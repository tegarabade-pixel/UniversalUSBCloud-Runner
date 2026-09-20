package main

import (
	"bytes"
	"crypto/aes"
	"crypto/cipher"
	"crypto/ecdh"
	"crypto/hmac"
	"crypto/rand"
	"crypto/sha256"
	"encoding/base64"
	"encoding/binary"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"hash/crc32"
	"io"
	"log"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/gorilla/websocket"
)

const (
	ver                   = 0x0111
	opReqImport           = 0x8003
	opRepImport           = 0x0003
	opReqList             = 0x8005
	opRepList             = 0x0005
	cmdSubmit             = 1
	cmdUnlink             = 2
	retSubmit             = 3
	retUnlink             = 4
	fReq                  = 1
	fResp                 = 2
	maxTransfer           = 8 * 1024 * 1024
	fCancel               = 3
	maxUrbInflightCap     = 32
	maxUrbWaitersCap      = 16
	maxUrbPayloadBytesCap = 32 * 1024 * 1024
	urbShortNotOK         = uint32(0x0001)
	urbZeroPacket         = uint32(0x0040)
)

var magic = []byte{'U', 'U', 'C', '4'}

type Iface struct {
	ID               int `json:"id"`
	AlternateSetting int `json:"alternateSetting"`
	Class            int `json:"class"`
	Subclass         int `json:"subclass"`
	Protocol         int `json:"protocol"`
}

type Device struct {
	Type                  string  `json:"type"`
	Generation            uint64  `json:"generation"`
	ConnectionEpoch       uint64  `json:"connectionEpoch"`
	TransportSession      string  `json:"transportSession"`
	LogicalSession        uint64  `json:"logicalSession"`
	ReconnectState        string  `json:"reconnectState"`
	Mode                  string  `json:"mode"`
	PreviousMode          string  `json:"previousMode"`
	FlashProtocol         string  `json:"flashProtocol"`
	FlashState            string  `json:"flashState"`
	FlashProfile          string  `json:"flashProfile"`
	FlashCapable          bool    `json:"flashCapable"`
	FlashConfidence       int     `json:"flashConfidence"`
	FlashConfidenceLabel  string  `json:"flashConfidenceLabel"`
	FlashRecoveryState    string  `json:"flashRecoveryState"`
	FlashOperationStage   string  `json:"flashOperationStage"`
	FlashOperationTarget  string  `json:"flashOperationTarget"`
	FlashOperationCRC32   string  `json:"flashOperationCrc32"`
	FlashIntegrityErrors  uint64  `json:"flashIntegrityErrors"`
	FlashGuardBlocks      uint64  `json:"flashGuardBlocks"`
	StrictOrder           bool    `json:"strictOrder"`
	RecommendedInflight   int     `json:"recommendedInflight"`
	RecommendedWaiters    int     `json:"recommendedWaiters"`
	RecommendedPayloadMiB int     `json:"recommendedPayloadMiB"`
	StateKey              string  `json:"stateKey"`
	BusID                 string  `json:"busid"`
	VendorID              int     `json:"vendorId"`
	ProductID             int     `json:"productId"`
	BCDDevice             int     `json:"bcdDevice"`
	DeviceClass           int     `json:"deviceClass"`
	DeviceSubclass        int     `json:"deviceSubclass"`
	DeviceProtocol        int     `json:"deviceProtocol"`
	ConfigValue           int     `json:"configValue"`
	NumConfigurations     int     `json:"numConfigurations"`
	Interfaces            []Iface `json:"interfaces"`
	Product               string  `json:"product"`
}

type response struct {
	status int32
	actual uint32
	data   []byte
}

type pendingTransfer struct {
	ch     chan response
	dir    uint8
	maxLen uint32
}

type txKey struct {
	session uint64
	id      uint64
	epoch   uint64
}

// transferTicket separates ordered submission from asynchronous completion.
// USB/IP submit order is preserved on the WebSocket while many transfers may remain outstanding.
type transferTicket struct {
	key txKey
	ch  chan response
}

type Bridge struct {
	signal string
	room   string

	wsMu    sync.RWMutex
	ws      *websocket.Conn
	writeMu sync.Mutex

	// Native desktop signaling is proxied only over localhost to the
	// Python WebRTC media/input host. Media itself never traverses this socket.
	desktopMu      sync.RWMutex
	desktopWS      *websocket.Conn
	desktopWriteMu sync.Mutex

	secureMu   sync.Mutex
	keyA2W     []byte
	keyW2A     []byte
	keyDesktop []byte
	serverPriv *ecdh.PrivateKey
	serverPub  []byte
	sendSeq    uint64
	recvSeq    uint64

	devMu            sync.RWMutex
	dev              *Device
	devKey           string
	remoteGeneration uint64
	devGen           atomic.Uint64
	changes          chan uint64

	pendMu           sync.Mutex
	pending          map[txKey]*pendingTransfer
	id               atomic.Uint64
	transportSession atomic.Uint64

	stop chan struct{}
}

func NewBridge(signal, room string) *Bridge {
	return &Bridge{
		signal:  signal,
		room:    room,
		pending: map[txKey]*pendingTransfer{},
		changes: make(chan uint64, 16),
		stop:    make(chan struct{}),
	}
}

func newTransportSessionID() uint64 {
	var raw [8]byte
	if _, e := rand.Read(raw[:]); e == nil {
		v := binary.BigEndian.Uint64(raw[:])
		if v != 0 {
			return v
		}
	}
	// Extremely unlikely fallback; uniqueness only needs to fence process/relay lifetimes.
	v := uint64(time.Now().UnixNano()) ^ uint64(os.Getpid())<<32
	if v == 0 {
		v = 1
	}
	return v
}

func (b *Bridge) rotateTransportSession() uint64 {
	next := newTransportSessionID()
	old := b.transportSession.Swap(next)
	b.failAllPending(-104)

	// A cached descriptor belongs to the old relay/transaction lifetime even when the
	// Android USB cable never moved. Hide it until Android sends a fresh descriptor
	// explicitly fenced by `next`; otherwise a new USB/IP import could submit against
	// the old connectionEpoch during the secure-handshake window.
	b.devMu.Lock()
	hadDevice := b.dev != nil || b.devKey != ""
	b.dev = nil
	b.devKey = ""
	// Android descriptor generations are monotonic only inside one transaction
	// lifetime. A fresh Runner transport session must not reject generation 1 from
	// a restarted Android service merely because the previous lifetime reached 27.
	b.remoteGeneration = 0
	b.devMu.Unlock()

	if (old != 0 && old != next) || hadDevice {
		// Force every USB/IP import/device list consumer to reopen against the new fence.
		b.publishChange()
	}
	log.Printf("USB TRANSACTION SESSION %016x (old=%016x) descriptorCacheCleared=%t", next, old, hadDevice)
	return next
}

func (b *Bridge) endpoint() (string, error) {
	u, e := url.Parse(b.signal)
	if e != nil {
		return "", e
	}
	q := u.Query()
	q.Set("room", b.room)
	q.Set("role", "windows")
	u.RawQuery = q.Encode()
	return u.String(), nil
}

func (b *Bridge) Run() {
	go func() {
		for {
			select {
			case <-b.stop:
				return
			default:
			}
			if e := b.runOnce(); e != nil {
				log.Printf("relay: %v", e)
			}
			select {
			case <-b.stop:
				return
			case <-time.After(750 * time.Millisecond):
			}
		}
	}()
}

func (b *Bridge) desktopConnected() bool {
	b.desktopMu.RLock()
	defer b.desktopMu.RUnlock()
	return b.desktopWS != nil
}

func (b *Bridge) desktopSendRaw(p []byte) error {
	b.desktopMu.RLock()
	ws := b.desktopWS
	b.desktopMu.RUnlock()
	if ws == nil {
		return errors.New("native desktop IPC offline")
	}
	b.desktopWriteMu.Lock()
	defer b.desktopWriteMu.Unlock()
	return ws.WriteMessage(websocket.TextMessage, p)
}

func (b *Bridge) RunDesktopProxy() {
	go func() {
		for {
			select {
			case <-b.stop:
				return
			default:
			}
			ws, _, e := websocket.DefaultDialer.Dial("ws://127.0.0.1:8765", nil)
			if e != nil {
				log.Printf("desktop IPC connect: %v", e)
				time.Sleep(350 * time.Millisecond)
				continue
			}
			b.desktopMu.Lock()
			b.desktopWS = ws
			b.desktopMu.Unlock()
			log.Printf("NATIVE DESKTOP IPC CONNECTED")
			// Re-advertise the encrypted desktop capability after IPC comes online.
			_ = b.sendText(b.helloPayload())
			// Desktop readiness is a level, not a one-shot edge. Android may still be
			// verifying OIDC when the first host-ready event arrives, so repeat a tiny
			// authenticated-session-gated liveness signal until IPC disconnects.
			readyPayload, _ := json.Marshal(map[string]any{"type": "desktop-state", "state": "host-ready", "desktopProtocol": 3, "turnMode": os.Getenv("UUC_ICE_MODE"), "iceProvider": os.Getenv("UUC_ICE_PROVIDER"), "turnRelayReady": os.Getenv("UUC_TURN_RELAY_READY") == "1", "turnProbe": os.Getenv("UUC_TURN_PROBE_RESULT")})
			_ = b.write(websocket.TextMessage, readyPayload)
			heartbeatStop := make(chan struct{})
			go func() {
				ticker := time.NewTicker(2 * time.Second)
				defer ticker.Stop()
				for {
					select {
					case <-heartbeatStop:
						return
					case <-ticker.C:
						_ = b.write(websocket.TextMessage, readyPayload)
					}
				}
			}()
			for {
				kind, p, e := ws.ReadMessage()
				if e != nil {
					break
				}
				if kind != websocket.TextMessage {
					continue
				}
				var g map[string]any
				if json.Unmarshal(p, &g) != nil {
					continue
				}
				typ, _ := g["type"].(string)
				if typ == "rtc-answer" || typ == "rtc-offer-ack" || typ == "rtc-ice" || typ == "desktop-state" || typ == "desktop-error" {
					_ = b.write(websocket.TextMessage, p)
				}
			}
			close(heartbeatStop)
			b.desktopMu.Lock()
			if b.desktopWS == ws {
				b.desktopWS = nil
			}
			b.desktopMu.Unlock()
			_ = ws.Close()
			log.Printf("NATIVE DESKTOP IPC DISCONNECTED")
			// Do not leave Android with a stale green Desktop Ready state.
			offline, _ := json.Marshal(map[string]any{"type": "desktop-state", "state": "host-offline", "desktopProtocol": 3, "turnMode": os.Getenv("UUC_ICE_MODE"), "iceProvider": os.Getenv("UUC_ICE_PROVIDER"), "turnRelayReady": os.Getenv("UUC_TURN_RELAY_READY") == "1", "turnProbe": os.Getenv("UUC_TURN_PROBE_RESULT")})
			_ = b.write(websocket.TextMessage, offline)
			time.Sleep(time.Second)
		}
	}()
}

var secureMagic = []byte{'U', 'U', 'E', '2'}

func hkdfSHA256(ikm, salt, info []byte, outLen int) []byte {
	extract := hmac.New(sha256.New, salt)
	extract.Write(ikm)
	prk := extract.Sum(nil)
	out := make([]byte, 0, outLen)
	var prev []byte
	counter := byte(1)
	for len(out) < outLen {
		expand := hmac.New(sha256.New, prk)
		expand.Write(prev)
		expand.Write(info)
		expand.Write([]byte{counter})
		prev = expand.Sum(nil)
		need := outLen - len(out)
		if need > len(prev) {
			need = len(prev)
		}
		out = append(out, prev[:need]...)
		counter++
	}
	return out
}

func secureNonce(prefix string, seq uint64) []byte {
	b := make([]byte, 12)
	copy(b[:4], []byte(prefix))
	binary.BigEndian.PutUint64(b[4:], seq)
	return b
}

func (b *Bridge) setAndroidPublic(encoded string) error {
	raw, e := base64.RawURLEncoding.DecodeString(encoded)
	if e != nil {
		return e
	}
	curve := ecdh.P256()
	peer, e := curve.NewPublicKey(raw)
	if e != nil {
		return e
	}
	priv, e := curve.GenerateKey(rand.Reader)
	if e != nil {
		return e
	}
	shared, e := priv.ECDH(peer)
	if e != nil {
		return e
	}
	clean := strings.ToUpper(strings.ReplaceAll(b.room, "-", ""))
	saltArr := sha256.Sum256([]byte(clean))
	salt := saltArr[:]
	b.secureMu.Lock()
	defer b.secureMu.Unlock()
	b.serverPriv = priv
	b.serverPub = priv.PublicKey().Bytes()
	b.keyA2W = hkdfSHA256(shared, salt, []byte("uuc-v2-a2w"), 32)
	b.keyW2A = hkdfSHA256(shared, salt, []byte("uuc-v2-w2a"), 32)
	b.keyDesktop = hkdfSHA256(shared, salt, []byte("uuc-v2-desktop"), 32)
	b.sendSeq = 0
	b.recvSeq = 0
	log.Printf("E2E READY")
	return nil
}

func (b *Bridge) secureReady() bool {
	b.secureMu.Lock()
	defer b.secureMu.Unlock()
	return len(b.keyA2W) == 32 && len(b.keyW2A) == 32 && len(b.keyDesktop) == 32 && len(b.serverPub) > 0
}

func (b *Bridge) encryptToAndroid(plain []byte) ([]byte, error) {
	b.secureMu.Lock()
	defer b.secureMu.Unlock()
	if len(b.keyW2A) != 32 {
		return nil, errors.New("secure session not ready")
	}
	b.sendSeq++
	seq := b.sendSeq
	header := make([]byte, 12)
	copy(header[:4], secureMagic)
	binary.BigEndian.PutUint64(header[4:], seq)
	block, e := aes.NewCipher(b.keyW2A)
	if e != nil {
		return nil, e
	}
	gcm, e := cipherNewGCM(block)
	if e != nil {
		return nil, e
	}
	sealed := gcm.Seal(nil, secureNonce("W2A0", seq), plain, header)
	return append(header, sealed...), nil
}

func (b *Bridge) decryptFromAndroid(packet []byte) ([]byte, error) {
	b.secureMu.Lock()
	defer b.secureMu.Unlock()
	if len(b.keyA2W) != 32 {
		return nil, errors.New("secure session not ready")
	}
	if len(packet) < 28 || !bytes.Equal(packet[:4], secureMagic) {
		return nil, errors.New("invalid secure packet")
	}
	seq := binary.BigEndian.Uint64(packet[4:12])
	if seq <= b.recvSeq {
		return nil, errors.New("replayed secure packet")
	}
	block, e := aes.NewCipher(b.keyA2W)
	if e != nil {
		return nil, e
	}
	gcm, e := cipherNewGCM(block)
	if e != nil {
		return nil, e
	}
	plain, e := gcm.Open(nil, secureNonce("A2W0", seq), packet[12:], packet[:12])
	if e != nil {
		return nil, e
	}
	b.recvSeq = seq
	return plain, nil
}

// Small wrapper keeps crypto/cipher out of the generated source's public surface.
func cipherNewGCM(block cipher.Block) (cipher.AEAD, error) { return cipher.NewGCM(block) }

func (b *Bridge) encryptedDesktopSecret() map[string]any {
	b.secureMu.Lock()
	defer b.secureMu.Unlock()
	if len(b.keyDesktop) != 32 || os.Getenv("DESKTOP_NATIVE_READY") != "1" {
		return nil
	}
	ice := []map[string]any{}
	if raw := strings.TrimSpace(os.Getenv("UUC_ICE_SERVERS_JSON")); raw != "" {
		var parsed []map[string]any
		if json.Unmarshal([]byte(raw), &parsed) == nil && len(parsed) > 0 {
			ice = parsed
		}
	}
	payload, _ := json.Marshal(map[string]any{
		"mode":            "webrtc",
		"desktopReady":    b.desktopConnected(),
		"desktopProtocol": 3,
		"turnMode":        os.Getenv("UUC_ICE_MODE"),
		"iceMode":         os.Getenv("UUC_ICE_MODE"),
		"iceProvider":     os.Getenv("UUC_ICE_PROVIDER"),
		"turnRelayReady":  os.Getenv("UUC_TURN_RELAY_READY") == "1",
		"turnProbe":       os.Getenv("UUC_TURN_PROBE_RESULT"),
		"iceServers":      ice,
	})
	block, e := aes.NewCipher(b.keyDesktop)
	if e != nil {
		return nil
	}
	gcm, e := cipher.NewGCM(block)
	if e != nil {
		return nil
	}
	nonce := make([]byte, gcm.NonceSize())
	if _, e = rand.Read(nonce); e != nil {
		return nil
	}
	sealed := gcm.Seal(nil, nonce, payload, []byte("uuc-v2-desktop"))
	return map[string]any{
		"nonce":      base64.RawURLEncoding.EncodeToString(nonce),
		"ciphertext": base64.RawURLEncoding.EncodeToString(sealed),
	}
}

func oidcAudience(room string, serverPublic []byte) string {
	clean := strings.ToUpper(strings.ReplaceAll(room, "-", ""))
	pub := base64.RawURLEncoding.EncodeToString(serverPublic)
	sum := sha256.Sum256([]byte(clean + "|" + pub))
	return fmt.Sprintf("uuc-%x", sum[:16])
}

func (b *Bridge) oidcToken() string {
	base := os.Getenv("ACTIONS_ID_TOKEN_REQUEST_URL")
	bearer := os.Getenv("ACTIONS_ID_TOKEN_REQUEST_TOKEN")
	if base == "" || bearer == "" {
		return ""
	}
	sep := "&"
	if !strings.Contains(base, "?") {
		sep = "?"
	}
	b.secureMu.Lock()
	serverPublic := append([]byte(nil), b.serverPub...)
	b.secureMu.Unlock()
	if len(serverPublic) == 0 {
		return ""
	}
	endpoint := base + sep + "audience=" + url.QueryEscape(oidcAudience(b.room, serverPublic))
	req, e := http.NewRequest(http.MethodGet, endpoint, nil)
	if e != nil {
		return ""
	}
	req.Header.Set("Authorization", "bearer "+bearer)
	client := &http.Client{Timeout: 10 * time.Second}
	resp, e := client.Do(req)
	if e != nil {
		return ""
	}
	defer resp.Body.Close()
	if resp.StatusCode < 200 || resp.StatusCode >= 300 {
		return ""
	}
	var out struct {
		Value string `json:"value"`
	}
	if json.NewDecoder(resp.Body).Decode(&out) != nil {
		return ""
	}
	return out.Value
}

func (b *Bridge) helloPayload() map[string]any {
	out := map[string]any{
		"type":                "hello",
		"role":                "windows",
		"protocol":            3,
		"oidcToken":           b.oidcToken(),
		"repository":          os.Getenv("GITHUB_REPOSITORY"),
		"actor":               os.Getenv("GITHUB_ACTOR"),
		"runId":               os.Getenv("GITHUB_RUN_ID"),
		"usbTransportSession": fmt.Sprintf("%016x", b.transportSession.Load()),
	}
	b.secureMu.Lock()
	if len(b.serverPub) > 0 {
		out["serverPublic"] = base64.RawURLEncoding.EncodeToString(b.serverPub)
	}
	b.secureMu.Unlock()
	if secret := b.encryptedDesktopSecret(); secret != nil {
		out["desktopSecret"] = secret
	}
	return out
}

func (b *Bridge) runOnce() error {
	ep, e := b.endpoint()
	if e != nil {
		return e
	}
	ws, _, e := websocket.DefaultDialer.Dial(ep, nil)
	if e != nil {
		return e
	}

	// A relay reconnect is a new transaction lifetime. Request IDs may restart/repeat,
	// therefore every binary USB frame is fenced by this independently random session ID.
	b.rotateTransportSession()

	b.wsMu.Lock()
	b.ws = ws
	b.wsMu.Unlock()

	// Keep the signaling control-plane connection self-healing. Media does not
	// traverse this websocket, but a dead TCP path must be detected quickly so
	// SDP/control can recover without the Android UI declaring the runner gone.
	_ = ws.SetReadDeadline(time.Now().Add(35 * time.Second))
	ws.SetPongHandler(func(string) error {
		return ws.SetReadDeadline(time.Now().Add(35 * time.Second))
	})
	defer func() {
		b.wsMu.Lock()
		if b.ws == ws {
			b.ws = nil
		}
		b.wsMu.Unlock()
		// USB/IP depends on this control-plane websocket. A lost relay must not leave
		// already-submitted flashing URBs blocked for the full 18-second ticket timeout.
		b.failAllPending(-104)
		ws.Close()
	}()

	log.Printf("RELAY CONNECTED")
	_ = b.sendText(b.helloPayload())

	helloStop := make(chan struct{})
	defer close(helloStop)

	go func() {
		ticker := time.NewTicker(10 * time.Second)
		defer ticker.Stop()

		for {
			select {
			case <-helloStop:
				return
			case <-ticker.C:
				// Protocol-level ping makes half-open websocket/TCP paths fail fast.
				b.writeMu.Lock()
				_ = ws.WriteControl(websocket.PingMessage, []byte("uuc"), time.Now().Add(2*time.Second))
				b.writeMu.Unlock()
				_ = b.sendText(map[string]any{
					"type":     "hello",
					"role":     "windows",
					"protocol": 2,
				})

				_ = b.sendText(map[string]any{
					"type":   "request-usb-state",
					"reason": "periodic",
				})
			}
		}
	}()

	for {
		kind, p, e := ws.ReadMessage()
		if e != nil {
			return e
		}
		if kind == websocket.TextMessage {
			b.handleText(p)
		}
		if kind == websocket.BinaryMessage {
			b.handleBinary(p)
		}
	}
}

func (b *Bridge) write(kind int, p []byte) error {
	b.wsMu.RLock()
	ws := b.ws
	b.wsMu.RUnlock()
	if ws == nil {
		return errors.New("relay offline")
	}
	b.writeMu.Lock()
	defer b.writeMu.Unlock()
	return ws.WriteMessage(kind, p)
}

func (b *Bridge) sendText(v any) error {
	p, e := json.Marshal(v)
	if e != nil {
		return e
	}
	return b.write(websocket.TextMessage, p)
}

func parseTransportSessionHex(raw string) uint64 {
	s := strings.TrimSpace(raw)
	s = strings.TrimPrefix(strings.TrimPrefix(s, "0x"), "0X")
	if s == "" || len(s) > 16 {
		return 0
	}
	v, e := strconv.ParseUint(s, 16, 64)
	if e != nil {
		return 0
	}
	return v
}

func deviceKey(d *Device) string {
	if d == nil {
		return ""
	}
	raw, _ := json.Marshal(d)
	return string(raw)
}

func (b *Bridge) publishChange() {
	g := b.devGen.Add(1)
	select {
	case b.changes <- g:
	default:
	}
	log.Printf("USB GENERATION %d", g)
}

func (b *Bridge) setDevice(d *Device) (accepted bool, changed bool) {
	key := deviceKey(d)

	b.devMu.Lock()
	defer b.devMu.Unlock()

	// Generation 0 is accepted for backward compatibility.
	// For the reliable v1.1.1 APK, stale generations are ignored.
	if d.Generation > 0 && b.remoteGeneration > 0 && d.Generation < b.remoteGeneration {
		return false, false
	}

	sameKey := key != "" && key == b.devKey
	sameGeneration := d.Generation > 0 && d.Generation == b.remoteGeneration

	if d.Generation > 0 {
		b.remoteGeneration = d.Generation
	}

	b.dev = d
	b.devKey = key

	// New generation must be treated as a physical lifetime transition
	// even when VID/PID/descriptors are identical.
	changed = !sameKey || !sameGeneration

	return true, changed
}

func (b *Bridge) clearDevice(incomingGeneration uint64) (accepted bool, changed bool) {
	b.devMu.Lock()
	defer b.devMu.Unlock()

	if incomingGeneration > 0 &&
		b.remoteGeneration > 0 &&
		incomingGeneration < b.remoteGeneration {
		return false, false
	}

	had := b.dev != nil || b.devKey != ""

	if incomingGeneration > 0 {
		b.remoteGeneration = incomingGeneration
	}

	b.dev = nil
	b.devKey = ""

	return true, had
}

func (b *Bridge) Generation() uint64     { return b.devGen.Load() }
func (b *Bridge) Changes() <-chan uint64 { return b.changes }

func (b *Bridge) handleText(p []byte) {
	var g map[string]any
	if json.Unmarshal(p, &g) != nil {
		log.Printf("ANDROID TEXT JSON decode failed: %q", string(p))
		return
	}

	typ, _ := g["type"].(string)

	if typ != "hello" && typ != "peer-joined" && typ != "peer-left" {
		log.Printf("ANDROID TEXT type=%q bytes=%d", typ, len(p))
	}

	if typ == "app-ping" {
		_ = b.sendText(map[string]any{"type": "app-pong", "time": g["time"]})
		return
	}

	if typ == "rtc-offer" || typ == "rtc-ice" || typ == "rtc-restart" || typ == "rtc-answer-replay" || typ == "rtc-answer-ack" || typ == "rtc-signal-resync" || typ == "desktop-control" {
		if !b.secureReady() {
			_ = b.sendText(map[string]any{"type": "desktop-error", "message": "secure desktop session not ready"})
			return
		}
		if e := b.desktopSendRaw(p); e != nil {
			_ = b.sendText(map[string]any{"type": "desktop-error", "message": e.Error()})
		}
		return
	}

	if typ == "usb-device" {
		var d Device
		if json.Unmarshal(p, &d) != nil {
			log.Printf("ANDROID usb-device JSON decode failed: %s", string(p))
			return
		}

		currentTx := b.transportSession.Load()
		descriptorTx := parseTransportSessionHex(d.TransportSession)
		if currentTx == 0 || descriptorTx == 0 || descriptorTx != currentTx {
			log.Printf("ANDROID USB DESCRIPTOR stale-session ignored descriptor=%016x current=%016x gen=%d", descriptorTx, currentTx, d.Generation)
			_ = b.sendText(map[string]any{
				"type": "usb-ack", "generation": d.Generation, "state": "stale-session",
			})
			return
		}

		if d.BusID == "" {
			d.BusID = "1-1"
		}

		old := b.Device()
		accepted, changed := b.setDevice(&d)

		if !accepted {
			log.Printf(
				"ANDROID USB STALE ignored androidGen=%d currentRemoteGen=%d",
				d.Generation, b.remoteGeneration,
			)
			_ = b.sendText(map[string]any{
				"type":       "usb-ack",
				"generation": d.Generation,
				"state":      "stale",
			})
			return
		}

		if changed {
			b.publishChange()
		}

		if old == nil {
			log.Printf(
				"ANDROID USB READY bridgeGen=%d androidGen=%d %04x:%04x %q",
				b.Generation(), d.Generation, d.VendorID, d.ProductID, d.Product,
			)
		} else if old.VendorID != d.VendorID ||
			old.ProductID != d.ProductID ||
			old.BCDDevice != d.BCDDevice ||
			old.Product != d.Product ||
			old.Generation != d.Generation {
			log.Printf(
				"ANDROID USB REENUM bridgeGen=%d androidGen=%d %04x:%04x -> %04x:%04x %q",
				b.Generation(), d.Generation,
				old.VendorID, old.ProductID,
				d.VendorID, d.ProductID, d.Product,
			)
		} else {
			log.Printf(
				"ANDROID USB REFRESH bridgeGen=%d androidGen=%d %04x:%04x %q",
				b.Generation(), d.Generation, d.VendorID, d.ProductID, d.Product,
			)
		}

		_ = b.sendText(map[string]any{
			"type":       "usb-ack",
			"generation": d.Generation,
			"state":      "present",
		})
		return
	}

	if typ == "usb-detach" {
		incomingGen := uint64(0)
		if v, ok := g["generation"].(float64); ok && v >= 0 {
			incomingGen = uint64(v)
		}
		rawTx, _ := g["transportSession"].(string)
		detachTx := parseTransportSessionHex(rawTx)
		currentTx := b.transportSession.Load()
		if currentTx == 0 || detachTx == 0 || detachTx != currentTx {
			log.Printf("ANDROID USB DETACH stale-session ignored detach=%016x current=%016x gen=%d", detachTx, currentTx, incomingGen)
			return
		}

		accepted, changed := b.clearDevice(incomingGen)

		if !accepted {
			log.Printf(
				"ANDROID USB DETACH stale ignored androidGen=%d",
				incomingGen,
			)
			return
		}

		if changed {
			b.publishChange()
		}

		log.Printf(
			"ANDROID USB DETACHED bridgeGen=%d androidGen=%d",
			b.Generation(), incomingGen,
		)

		_ = b.sendText(map[string]any{
			"type":       "usb-ack",
			"generation": incomingGen,
			"state":      "absent",
		})
		return
	}

	if typ == "hello" {
		if role, _ := g["role"].(string); role == "android" {
			log.Printf("ANDROID ONLINE")
			if pub, _ := g["ecdhPublic"].(string); pub != "" {
				if e := b.setAndroidPublic(pub); e != nil {
					log.Printf("E2E handshake failed: %v", e)
				}
			}

			_ = b.sendText(b.helloPayload())

			_ = b.sendText(map[string]any{
				"type":   "request-usb-state",
				"reason": "android-hello",
			})
		}
		return
	}

	if typ == "peer-left" {
		if role, _ := g["role"].(string); role == "android" {
			log.Printf("ANDROID PEER LEFT — fencing USB transaction lifetime")
			// The Runner relay socket can remain connected while Android's relay
			// socket disappears. Fail pending URBs immediately and rotate the USB
			// transaction session so a late binary frame from the departed peer
			// cannot complete work in the next Android lifetime.
			b.rotateTransportSession()
		}
		return
	}

	if typ == "peer-joined" {
		if role, _ := g["role"].(string); role == "android" {
			log.Printf("ANDROID PEER JOINED")

			_ = b.sendText(b.helloPayload())

			_ = b.sendText(map[string]any{
				"type":   "request-usb-state",
				"reason": "peer-joined",
			})
		}
		return
	}

	log.Printf("relay text: %s", strings.TrimSpace(string(p)))
}

func (b *Bridge) handleBinary(p []byte) {
	plain, e := b.decryptFromAndroid(p)
	if e != nil {
		log.Printf("E2E response decrypt: %v", e)
		return
	}
	p = plain
	// UUC4 RESP = magic(4), kind(1), transportSession(8), requestId(8), usbEpoch(8), status(4), actual(4), payloadCRC32(4), data.
	if len(p) < 41 || !bytes.Equal(p[:4], magic) || p[4] != fResp {
		return
	}
	r := bytes.NewReader(p[5:])
	var session uint64
	var id uint64
	var epoch uint64
	var st int32
	var actual uint32
	var payloadCRC uint32
	if binary.Read(r, binary.BigEndian, &session) != nil ||
		binary.Read(r, binary.BigEndian, &id) != nil ||
		binary.Read(r, binary.BigEndian, &epoch) != nil ||
		binary.Read(r, binary.BigEndian, &st) != nil ||
		binary.Read(r, binary.BigEndian, &actual) != nil ||
		binary.Read(r, binary.BigEndian, &payloadCRC) != nil {
		return
	}
	if session == 0 || session != b.transportSession.Load() {
		log.Printf("USB stale response ignored session=%016x current=%016x id=%d", session, b.transportSession.Load(), id)
		return
	}
	data, _ := io.ReadAll(r)
	key := txKey{session: session, id: id, epoch: epoch}
	b.pendMu.Lock()
	pt := b.pending[key]
	if pt == nil {
		b.pendMu.Unlock()
		return
	}
	malformed := actual > pt.maxLen
	if pt.dir == 1 {
		malformed = malformed || uint32(len(data)) != actual
	} else {
		malformed = malformed || len(data) != 0
	}
	crcMismatch := false
	if !malformed {
		expectedCRC := uint32(0)
		if len(data) > 0 {
			expectedCRC = crc32.ChecksumIEEE(data)
		}
		crcMismatch = expectedCRC != payloadCRC
	}
	delete(b.pending, key)
	b.pendMu.Unlock()
	if malformed {
		log.Printf("USB malformed response id=%d dir=%d actual=%d data=%d max=%d", id, pt.dir, actual, len(data), pt.maxLen)
		pt.ch <- response{status: -71}
		return
	}
	if crcMismatch {
		log.Printf("USB CRC mismatch response id=%d actual=%d got=%08x", id, actual, payloadCRC)
		pt.ch <- response{status: -84}
		return
	}
	if pt.dir == 0 {
		data = nil
	}
	pt.ch <- response{st, actual, data}
}

func (b *Bridge) failAllPending(status int32) {
	b.pendMu.Lock()
	pending := make([]*pendingTransfer, 0, len(b.pending))
	for key, ch := range b.pending {
		delete(b.pending, key)
		pending = append(pending, ch)
	}
	b.pendMu.Unlock()
	for _, pt := range pending {
		select {
		case pt.ch <- response{status: status}:
		default:
		}
	}
	if len(pending) > 0 {
		log.Printf("USB pending failed fast count=%d status=%d", len(pending), status)
	}
}

func (b *Bridge) Device() *Device {
	b.devMu.RLock()
	defer b.devMu.RUnlock()
	if b.dev == nil {
		return nil
	}
	d := *b.dev
	d.Interfaces = append([]Iface(nil), b.dev.Interfaces...)
	return &d
}

func (b *Bridge) sendCancel(key txKey) {
	if key.session == 0 || key.session != b.transportSession.Load() {
		return
	}
	buf := new(bytes.Buffer)
	buf.Write(magic)
	buf.WriteByte(fCancel)
	_ = binary.Write(buf, binary.BigEndian, key.session)
	_ = binary.Write(buf, binary.BigEndian, key.id)
	_ = binary.Write(buf, binary.BigEndian, key.epoch)
	encrypted, e := b.encryptToAndroid(buf.Bytes())
	if e != nil {
		return
	}
	_ = b.write(websocket.BinaryMessage, encrypted)
}

func (b *Bridge) StartTransfer(dir, ep uint8, setup [8]byte, payload []byte, n int) (*transferTicket, response) {
	if n < 0 || n > maxTransfer {
		return nil, response{status: -90}
	}
	if dir > 1 || ep > 15 {
		return nil, response{status: -71}
	}
	if dir == 0 && n > 0 && len(payload) < n {
		return nil, response{status: -71}
	}
	d := b.Device()
	if d == nil || d.ConnectionEpoch == 0 {
		return nil, response{status: -19}
	}
	session := b.transportSession.Load()
	if session == 0 {
		return nil, response{status: -107}
	}

	id := b.id.Add(1)
	key := txKey{session: session, id: id, epoch: d.ConnectionEpoch}
	ch := make(chan response, 1)
	b.pendMu.Lock()
	if _, exists := b.pending[key]; exists {
		b.pendMu.Unlock()
		return nil, response{status: -16}
	}
	b.pending[key] = &pendingTransfer{ch: ch, dir: dir, maxLen: uint32(n)}
	b.pendMu.Unlock()

	// UUC4 REQ = magic, kind, transportSession, requestId, usbEpoch, dir, ep, timeout, length, payloadCRC32, setup, payload.
	buf := new(bytes.Buffer)
	buf.Write(magic)
	buf.WriteByte(fReq)
	_ = binary.Write(buf, binary.BigEndian, key.session)
	_ = binary.Write(buf, binary.BigEndian, key.id)
	_ = binary.Write(buf, binary.BigEndian, key.epoch)
	buf.WriteByte(dir)
	buf.WriteByte(ep)
	_ = binary.Write(buf, binary.BigEndian, uint32(15000))
	_ = binary.Write(buf, binary.BigEndian, uint32(n))
	payloadCRC := uint32(0)
	if dir == 0 && n > 0 {
		payloadCRC = crc32.ChecksumIEEE(payload[:n])
	}
	_ = binary.Write(buf, binary.BigEndian, payloadCRC)
	buf.Write(setup[:])
	if dir == 0 && n > 0 {
		buf.Write(payload[:n])
	}

	encrypted, e := b.encryptToAndroid(buf.Bytes())
	if e != nil {
		b.pendMu.Lock()
		delete(b.pending, key)
		b.pendMu.Unlock()
		return nil, response{status: -107}
	}
	if e := b.write(websocket.BinaryMessage, encrypted); e != nil {
		b.pendMu.Lock()
		delete(b.pending, key)
		b.pendMu.Unlock()
		return nil, response{status: -107}
	}
	return &transferTicket{key: key, ch: ch}, response{}
}

func (b *Bridge) WaitTransfer(ticket *transferTicket, cancel <-chan struct{}) response {
	if ticket == nil {
		return response{status: -71}
	}
	timer := time.NewTimer(18 * time.Second)
	defer timer.Stop()
	select {
	case r := <-ticket.ch:
		return r
	case <-cancel:
		b.pendMu.Lock()
		delete(b.pending, ticket.key)
		b.pendMu.Unlock()
		b.sendCancel(ticket.key)
		return response{status: -104}
	case <-timer.C:
		b.pendMu.Lock()
		delete(b.pending, ticket.key)
		b.pendMu.Unlock()
		b.sendCancel(ticket.key)
		return response{status: -110}
	}
}

func (b *Bridge) Transfer(cancel <-chan struct{}, dir, ep uint8, setup [8]byte, payload []byte, n int) response {
	ticket, immediate := b.StartTransfer(dir, ep, setup, payload, n)
	if ticket == nil {
		return immediate
	}
	return b.WaitTransfer(ticket, cancel)
}

func fixed(s string, n int) []byte { o := make([]byte, n); copy(o, []byte(s)); return o }

func writeDev(w io.Writer, d *Device, ifs bool) error {
	w.Write(fixed("/virtual/android-usb/1-1", 256))
	bus := d.BusID
	if bus == "" {
		bus = "1-1"
	}
	w.Write(fixed(bus, 32))
	for _, v := range []any{uint32(1), uint32(1), uint32(3), uint16(d.VendorID), uint16(d.ProductID), uint16(d.BCDDevice)} {
		if e := binary.Write(w, binary.BigEndian, v); e != nil {
			return e
		}
	}
	w.Write([]byte{byte(d.DeviceClass), byte(d.DeviceSubclass), byte(d.DeviceProtocol),
		byte(d.ConfigValue), byte(d.NumConfigurations), byte(len(d.Interfaces))})
	if ifs {
		for _, i := range d.Interfaces {
			w.Write([]byte{byte(i.Class), byte(i.Subclass), byte(i.Protocol), 0})
		}
	}
	return nil
}

func full(c net.Conn, n int) ([]byte, error) {
	p := make([]byte, n)
	_, e := io.ReadFull(c, p)
	return p, e
}

type Server struct {
	b         *Bridge
	importsMu sync.Mutex
	imports   map[net.Conn]struct{}
}

func NewServer(b *Bridge) *Server {
	return &Server{b: b, imports: map[net.Conn]struct{}{}}
}

func (s *Server) addImport(c net.Conn) {
	s.importsMu.Lock()
	s.imports[c] = struct{}{}
	n := len(s.imports)
	s.importsMu.Unlock()
	log.Printf("USB/IP active imports=%d", n)
}

func (s *Server) delImport(c net.Conn) {
	s.importsMu.Lock()
	delete(s.imports, c)
	n := len(s.imports)
	s.importsMu.Unlock()
	log.Printf("USB/IP active imports=%d", n)
}

func (s *Server) closeImports(reason string) {
	s.importsMu.Lock()
	conns := make([]net.Conn, 0, len(s.imports))
	for c := range s.imports {
		conns = append(conns, c)
	}
	s.importsMu.Unlock()

	if len(conns) > 0 {
		log.Printf("USB/IP closing %d import(s): %s", len(conns), reason)
	}
	for _, c := range conns {
		_ = c.Close()
	}
}

func (s *Server) WatchDeviceChanges() {
	go func() {
		for g := range s.b.Changes() {
			s.closeImports(fmt.Sprintf("Android USB generation changed to %d", g))
		}
	}()
}

func (s *Server) Serve(addr string) error {
	ln, e := net.Listen("tcp", addr)
	if e != nil {
		return e
	}
	log.Printf("USB/IP server %s", addr)
	for {
		c, e := ln.Accept()
		if e != nil {
			return e
		}
		go s.conn(c)
	}
}

func (s *Server) conn(c net.Conn) {
	defer c.Close()
	c.SetDeadline(time.Now().Add(30 * time.Second))
	h, e := full(c, 8)
	if e != nil {
		return
	}
	op := binary.BigEndian.Uint16(h[2:4])

	if op == opReqList {
		s.list(c)
		return
	}

	if op == opReqImport {
		p, e := full(c, 32)
		if e != nil {
			return
		}
		bus := strings.TrimRight(string(p), "\x00")
		s.importDev(c, bus)
		return
	}
}

func (s *Server) list(c net.Conn) {
	d := s.b.Device()
	buf := new(bytes.Buffer)
	binary.Write(buf, binary.BigEndian, uint16(ver))
	binary.Write(buf, binary.BigEndian, uint16(opRepList))
	binary.Write(buf, binary.BigEndian, uint32(0))
	if d == nil {
		binary.Write(buf, binary.BigEndian, uint32(0))
		_ = writeAll(c, buf.Bytes())
		return
	}
	binary.Write(buf, binary.BigEndian, uint32(1))
	writeDev(buf, d, true)
	c.Write(buf.Bytes())
}

func clampInt(v, lo, hi int) int {
	if v < lo {
		return lo
	}
	if v > hi {
		return hi
	}
	return v
}

func pipelineLimits(d *Device) (int, int, int) {
	// Safe defaults. Phase 5 accepts aggressive protocol hints only when Android has a
	// high-confidence protocol fingerprint. This prevents an ordinary vendor-specific
	// interface from accidentally receiving Fastboot/EDL-style concurrency.
	inflight := 8
	waiters := 4
	payload := 8 * 1024 * 1024
	if d != nil && d.FlashConfidence >= 80 {
		if d.RecommendedInflight > 0 {
			inflight = clampInt(d.RecommendedInflight, 4, maxUrbInflightCap)
		}
		if d.RecommendedWaiters > 0 {
			waiters = clampInt(d.RecommendedWaiters, 2, maxUrbWaitersCap)
		}
		if waiters > inflight {
			waiters = inflight
		}
		if d.RecommendedPayloadMiB > 0 {
			payload = clampInt(d.RecommendedPayloadMiB, 8, maxUrbPayloadBytesCap/(1024*1024)) * 1024 * 1024
		}
	}
	return inflight, waiters, payload
}

func (s *Server) importDev(c net.Conn, bus string) {
	d := s.b.Device()
	buf := new(bytes.Buffer)
	binary.Write(buf, binary.BigEndian, uint16(ver))
	binary.Write(buf, binary.BigEndian, uint16(opRepImport))
	if d == nil || bus != d.BusID {
		binary.Write(buf, binary.BigEndian, uint32(1))
		_ = writeAll(c, buf.Bytes())
		return
	}
	binary.Write(buf, binary.BigEndian, uint32(0))
	writeDev(buf, d, false)
	if e := writeAll(c, buf.Bytes()); e != nil {
		return
	}
	c.SetDeadline(time.Time{})
	s.addImport(c)
	defer s.delImport(c)
	inflight, waiters, payloadLimit := pipelineLimits(d)
	log.Printf("USB/IP IMPORT %s gen=%d protocol=%s confidence=%d/%s recovery=%s operation=%s target=%s integrityErrors=%d guardBlocks=%d profile=%s pipeline=ordered inflight=%d waiters=%d payloadMiB=%d",
		bus, s.b.Generation(), d.FlashProtocol, d.FlashConfidence, d.FlashConfidenceLabel, d.FlashRecoveryState,
		d.FlashOperationStage, d.FlashOperationTarget, d.FlashIntegrityErrors, d.FlashGuardBlocks,
		d.FlashProfile, inflight, waiters, payloadLimit/(1024*1024))
	s.urbs(c, inflight, waiters, int64(payloadLimit))
}

func writeAll(w io.Writer, p []byte) error {
	for len(p) > 0 {
		n, err := w.Write(p)
		if n > 0 {
			p = p[n:]
		}
		if err != nil {
			return err
		}
		if n == 0 {
			return io.ErrShortWrite
		}
	}
	return nil
}

func applyUrbCompletionFlags(flags uint32, dir uint32, requested int, r response) response {
	// Linux URB_SHORT_NOT_OK applies to non-iso IN requests. A short successful
	// read is reported as -EREMOTEIO instead of silently looking successful.
	if flags&urbShortNotOK != 0 && dir == 1 && r.status == 0 && int(r.actual) < requested {
		r.status = -121 // -EREMOTEIO
	}
	return r
}

func (s *Server) urbs(c net.Conn, maxUrbInflight int, maxUrbWaiters int, maxUrbPayloadBytes int64) {
	type urbJob struct {
		seq         uint32
		dir         uint32
		ep          uint32
		flags       uint32
		setup       [8]byte
		payload     []byte
		n           int
		cancel      chan struct{}
		cancelOnce  sync.Once
		stateMu     sync.Mutex
		state       int // 0 active, 1 cancelled, 2 completion committed
		payloadCost int64
		ticket      *transferTicket
	}

	var wm sync.Mutex
	var jobsMu sync.Mutex
	jobsBySeq := map[uint32]*urbJob{}
	jobs := make(chan *urbJob, maxUrbInflight)
	slots := make(chan struct{}, maxUrbInflight)
	var payloadMu sync.Mutex
	var payloadBytes int64
	verboseUrb := os.Getenv("UUC_USB_VERBOSE_URB") == "1"
	var workerWG sync.WaitGroup

	cancelJob := func(j *urbJob) bool {
		if j == nil {
			return false
		}
		j.stateMu.Lock()
		defer j.stateMu.Unlock()
		if j.state != 0 {
			return false
		}
		j.state = 1
		j.cancelOnce.Do(func() { close(j.cancel) })
		return true
	}
	isCancelled := func(j *urbJob) bool {
		j.stateMu.Lock()
		defer j.stateMu.Unlock()
		return j.state == 1
	}
	beginCompletion := func(j *urbJob) bool {
		j.stateMu.Lock()
		defer j.stateMu.Unlock()
		if j.state != 0 {
			return false
		}
		j.state = 2
		return true
	}
	reservePayload := func(n int64) bool {
		if n <= 0 {
			return true
		}
		payloadMu.Lock()
		defer payloadMu.Unlock()
		if payloadBytes+n > maxUrbPayloadBytes {
			return false
		}
		payloadBytes += n
		return true
	}
	releasePayload := func(n int64) {
		if n <= 0 {
			return
		}
		payloadMu.Lock()
		payloadBytes -= n
		if payloadBytes < 0 {
			payloadBytes = 0
		}
		payloadMu.Unlock()
	}
	discardN := func(n int) error {
		if n <= 0 {
			return nil
		}
		_, e := io.CopyN(io.Discard, c, int64(n))
		return e
	}

	for worker := 0; worker < maxUrbWaiters; worker++ {
		workerWG.Add(1)
		go func(workerID int) {
			defer workerWG.Done()
			for j := range jobs {
				func() {
					defer func() {
						jobsMu.Lock()
						if jobsBySeq[j.seq] == j {
							delete(jobsBySeq, j.seq)
						}
						jobsMu.Unlock()
						releasePayload(j.payloadCost)
						<-slots
					}()

					if isCancelled(j) {
						return
					}

					r := s.b.WaitTransfer(j.ticket, j.cancel)
					if !beginCompletion(j) {
						// UNLINK won the race. Even if the Android response arrived at the
						// same instant, explicitly send CANCEL so Android records the host
						// outcome as uncertain rather than assuming semantic completion.
						s.b.sendCancel(j.ticket.key)
						return
					}
					r = applyUrbCompletionFlags(j.flags, j.dir, j.n, r)

					if j.ep == 0 || r.status != 0 || verboseUrb {
						if j.ep == 0 {
							preview := r.data
							if len(preview) > 32 {
								preview = preview[:32]
							}
							log.Printf("URB COMPLETE seq=%d ep=0 status=%d actual=%d data[0:%d]=% x",
								j.seq, r.status, r.actual, len(preview), preview)
						} else {
							log.Printf("URB COMPLETE seq=%d ep=%d status=%d actual=%d",
								j.seq, j.ep, r.status, r.actual)
						}
					}

					data := r.data
					if j.dir == 0 {
						data = nil
					}
					retSub(c, &wm, j.seq, r.status, r.actual, data)
				}()
			}
		}(worker)
	}

	defer func() {
		jobsMu.Lock()
		toCancel := make([]*urbJob, 0, len(jobsBySeq))
		for _, j := range jobsBySeq {
			toCancel = append(toCancel, j)
		}
		jobsMu.Unlock()
		for _, j := range toCancel {
			cancelJob(j)
		}
		close(jobs)
		// Keep the import socket alive until all waiter goroutines have observed cancellation.
		// This prevents writes racing with conn()'s deferred Close().
		workerWG.Wait()
	}()

	for {
		h, e := full(c, 48)
		if e != nil {
			log.Printf("USB/IP URB stream ended: %v", e)
			return
		}

		cmd := binary.BigEndian.Uint32(h[0:4])
		seq := binary.BigEndian.Uint32(h[4:8])
		devid := binary.BigEndian.Uint32(h[8:12])
		dir := binary.BigEndian.Uint32(h[12:16])
		ep := binary.BigEndian.Uint32(h[16:20])

		if cmd == cmdSubmit {
			flags := binary.BigEndian.Uint32(h[20:24])
			n := int(int32(binary.BigEndian.Uint32(h[24:28])))
			startFrame := int32(binary.BigEndian.Uint32(h[28:32]))
			packets := int32(binary.BigEndian.Uint32(h[32:36]))
			interval := int32(binary.BigEndian.Uint32(h[36:40]))
			var setup [8]byte
			copy(setup[:], h[40:48])

			if ep == 0 || verboseUrb {
				log.Printf("URB SUBMIT seq=%d devid=%08x dir=%d ep=%d len=%d flags=%08x start=%d packets=%d interval=%d setup=% x",
					seq, devid, dir, ep, n, flags, startFrame, packets, interval, setup)
			}

			if n < 0 || n > maxTransfer {
				// Length is part of the USB/IP stream framing. Once it is invalid we cannot
				// safely find the next header without trusting an unbounded byte count.
				log.Printf("URB FATAL seq=%d invalid length=%d; closing import", seq, n)
				retSub(c, &wm, seq, -90, 0, nil)
				return
			}

			// The USB/IP fields are 32-bit. Never cast malformed values to uint8,
			// because e.g. endpoint 256 would otherwise wrap to endpoint zero.
			if dir > 1 || ep > 15 {
				log.Printf("URB FATAL seq=%d invalid dir/ep dir=%d ep=%d", seq, dir, ep)
				retSub(c, &wm, seq, -71, 0, nil) // -EPROTO
				return
			}

			// Android's public UsbDeviceConnection API does not expose a reliable
			// bulk-OUT ZLP flag. Silently ignoring USBIP_URB_ZERO_PACKET can alter
			// protocol semantics, so fail closed while preserving the TCP framing.
			if flags&urbZeroPacket != 0 {
				if dir == 0 && n > 0 {
					if e := discardN(n); e != nil {
						return
					}
				}
				retSub(c, &wm, seq, -95, 0, nil) // -EOPNOTSUPP
				continue
			}

			// Isochronous USB/IP is intentionally unsupported. Consume stream bytes without retaining them.
			if packets > 0 {
				if dir == 0 && n > 0 {
					if e := discardN(n); e != nil {
						return
					}
				}
				if e := discardN(int(packets) * 16); e != nil {
					return
				}
				retSub(c, &wm, seq, -95, 0, nil)
				continue
			}

			// Reserve one bounded URB lifetime before retaining an OUT payload.
			select {
			case slots <- struct{}{}:
			default:
				if dir == 0 && n > 0 {
					if e := discardN(n); e != nil {
						return
					}
				}
				retSub(c, &wm, seq, -16, 0, nil)
				continue
			}

			payloadCost := int64(0)
			if dir == 0 {
				payloadCost = int64(n)
			}
			if !reservePayload(payloadCost) {
				<-slots
				if dir == 0 && n > 0 {
					if e := discardN(n); e != nil {
						return
					}
				}
				retSub(c, &wm, seq, -16, 0, nil)
				continue
			}

			var payload []byte
			if dir == 0 && n > 0 {
				payload, e = full(c, n)
				if e != nil {
					releasePayload(payloadCost)
					<-slots
					return
				}
			}

			// A duplicate active USB/IP sequence must never overwrite the old cancellation mapping.
			jobsMu.Lock()
			_, duplicateSeq := jobsBySeq[seq]
			jobsMu.Unlock()
			if duplicateSeq {
				releasePayload(payloadCost)
				<-slots
				retSub(c, &wm, seq, -16, 0, nil)
				continue
			}

			// IMPORTANT: submit to Android here, on the single USB/IP reader goroutine.
			// This preserves exact URB arrival order while completion workers wait in parallel.
			ticket, immediate := s.b.StartTransfer(uint8(dir), uint8(ep), setup, payload, n)
			if ticket == nil {
				releasePayload(payloadCost)
				<-slots
				retSub(c, &wm, seq, immediate.status, immediate.actual, immediate.data)
				continue
			}

			// StartTransfer has synchronously encrypted/written the frame, so the original
			// OUT payload no longer needs to be retained while waiting for completion.
			releasePayload(payloadCost)
			payloadCost = 0
			payload = nil

			j := &urbJob{
				seq: seq, dir: dir, ep: ep, flags: flags, setup: setup, payload: nil, n: n,
				cancel: make(chan struct{}), payloadCost: payloadCost, ticket: ticket,
			}
			jobsMu.Lock()
			jobsBySeq[seq] = j
			jobsMu.Unlock()
			jobs <- j
			continue
		}

		if cmd == cmdUnlink {
			target := binary.BigEndian.Uint32(h[20:24])
			jobsMu.Lock()
			j := jobsBySeq[target]
			jobsMu.Unlock()
			if cancelJob(j) {
				// Successful unlink: Linux USB/IP specifies -ECONNRESET and no
				// corresponding RET_SUBMIT for the cancelled URB.
				retUnlinkFn(c, &wm, seq, -104)
			} else {
				// Too late / already completed / unknown target: status 0.
				retUnlinkFn(c, &wm, seq, 0)
			}
			continue
		}

		log.Printf("USB/IP unknown command: 0x%08x seq=%d", cmd, seq)
		return
	}
}

func retSub(c net.Conn, m *sync.Mutex, seq uint32, st int32, actual uint32, data []byte) {
	b := new(bytes.Buffer)
	for _, v := range []any{uint32(retSubmit), seq, uint32(0), uint32(0), uint32(0), st, actual,
		uint32(0), uint32(0xffffffff), uint32(0), uint64(0)} {
		binary.Write(b, binary.BigEndian, v)
	}
	if data != nil {
		b.Write(data)
	}
	m.Lock()
	defer m.Unlock()
	if e := writeAll(c, b.Bytes()); e != nil {
		log.Printf("USB/IP RET_SUBMIT write failed: %v", e)
	}
}

func retUnlinkFn(c net.Conn, m *sync.Mutex, seq uint32, st int32) {
	b := new(bytes.Buffer)
	for _, v := range []any{uint32(retUnlink), seq, uint32(0), uint32(0), uint32(0), st} {
		binary.Write(b, binary.BigEndian, v)
	}
	b.Write(make([]byte, 24))
	m.Lock()
	defer m.Unlock()
	if e := writeAll(c, b.Bytes()); e != nil {
		log.Printf("USB/IP RET_UNLINK write failed: %v", e)
	}
}

func phase8Require(ok bool, name string) error {
	if ok {
		return nil
	}
	return fmt.Errorf("phase8 selftest failed: %s", name)
}

// runPhase8SelfTest is simulation-only: it never opens TCP USB/IP, relay WebSocket,
// or a physical USB device. It exercises the same in-memory session/generation/pending
// structures used at runtime so the official workflow can reject a broken Runner build.
func runPhase8SelfTest() error {
	b := NewBridge("ws://127.0.0.1/unused", "PHASE8TEST0001")
	s1 := b.rotateTransportSession()
	if e := phase8Require(s1 != 0, "session-nonzero"); e != nil {
		return e
	}

	d := &Device{
		Generation: 10, ConnectionEpoch: 7,
		TransportSession: fmt.Sprintf("%016x", s1),
		VendorID:         0x18d1, ProductID: 0x4ee0, Product: "phase8",
	}
	accepted, changed := b.setDevice(d)
	if e := phase8Require(accepted && changed && b.Device() != nil, "descriptor-install"); e != nil {
		return e
	}

	// Stale generations must never replace a newer descriptor.
	stale := *d
	stale.Generation = 9
	accepted, _ = b.setDevice(&stale)
	if e := phase8Require(!accepted && b.Device() != nil && b.Device().Generation == 10, "stale-generation-fence"); e != nil {
		return e
	}

	// Pending tickets must fail immediately on relay/session loss rather than waiting 18s.
	key := txKey{session: s1, id: 1, epoch: 7}
	ch := make(chan response, 1)
	b.pendMu.Lock()
	b.pending[key] = &pendingTransfer{ch: ch, dir: 0, maxLen: 64}
	b.pendMu.Unlock()
	b.failAllPending(-104)
	select {
	case r := <-ch:
		if e := phase8Require(r.status == -104, "pending-fail-fast-status"); e != nil {
			return e
		}
	case <-time.After(250 * time.Millisecond):
		return fmt.Errorf("phase8 selftest failed: pending-fail-fast-timeout")
	}
	b.pendMu.Lock()
	pendingLeft := len(b.pending)
	b.pendMu.Unlock()
	if e := phase8Require(pendingLeft == 0, "pending-map-drained"); e != nil {
		return e
	}

	// Relay lifetime rotation must clear the cached Android descriptor and produce a new fence.
	s2 := b.rotateTransportSession()
	if e := phase8Require(s2 != 0 && s2 != s1, "session-rotation"); e != nil {
		return e
	}
	if e := phase8Require(b.Device() == nil, "descriptor-cache-cleared"); e != nil {
		return e
	}
	if e := phase8Require(parseTransportSessionHex(fmt.Sprintf("%016x", s2)) == s2, "session-hex-roundtrip"); e != nil {
		return e
	}
	if e := phase8Require(parseTransportSessionHex("not-a-session") == 0, "invalid-session-rejected"); e != nil {
		return e
	}

	log.Printf("PHASE8 RUNNER SELFTEST PASS session1=%016x session2=%016x", s1, s2)
	return nil
}

func main() {
	signalURL := flag.String("signal", "", "relay URL")
	room := flag.String("room", "", "room")
	phase8SelfTest := flag.Bool("phase8-selftest", false, "run isolated Phase 8 stability self-test and exit")
	flag.Parse()
	if *phase8SelfTest {
		if e := runPhase8SelfTest(); e != nil {
			log.Fatal(e)
		}
		return
	}
	if *signalURL == "" || len(*room) < 12 {
		flag.Usage()
		os.Exit(2)
	}

	b := NewBridge(*signalURL, *room)
	b.RunDesktopProxy()
	b.Run()
	s := NewServer(b)
	s.WatchDeviceChanges()
	go func() {
		if e := s.Serve("127.0.0.1:3240"); e != nil {
			log.Fatal(e)
		}
	}()

	log.Printf("FULL RELAY AGENT READY")
	stop := make(chan os.Signal, 1)
	signal.Notify(stop, syscall.SIGINT, syscall.SIGTERM)
	<-stop
	close(b.stop)
}
