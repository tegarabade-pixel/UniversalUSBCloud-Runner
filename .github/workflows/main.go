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
	"io"
	"log"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/gorilla/websocket"
)

const (
	ver         = 0x0111
	opReqImport = 0x8003
	opRepImport = 0x0003
	opReqList   = 0x8005
	opRepList   = 0x0005
	cmdSubmit   = 1
	cmdUnlink   = 2
	retSubmit   = 3
	retUnlink   = 4
	fReq        = 1
	fResp       = 2
	maxTransfer = 8 * 1024 * 1024
)

var magic = []byte{'U', 'U', 'C', '2'}

type Iface struct {
	ID               int `json:"id"`
	AlternateSetting int `json:"alternateSetting"`
	Class            int `json:"class"`
	Subclass         int `json:"subclass"`
	Protocol         int `json:"protocol"`
}

type Device struct {
	Type              string  `json:"type"`
	Generation        uint64  `json:"generation"`
	StateKey          string  `json:"stateKey"`
	BusID             string  `json:"busid"`
	VendorID          int     `json:"vendorId"`
	ProductID         int     `json:"productId"`
	BCDDevice         int     `json:"bcdDevice"`
	DeviceClass       int     `json:"deviceClass"`
	DeviceSubclass    int     `json:"deviceSubclass"`
	DeviceProtocol    int     `json:"deviceProtocol"`
	ConfigValue       int     `json:"configValue"`
	NumConfigurations int     `json:"numConfigurations"`
	Interfaces        []Iface `json:"interfaces"`
	Product           string  `json:"product"`
}

type response struct {
	status int32
	actual uint32
	data   []byte
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

	pendMu  sync.Mutex
	pending map[uint64]chan response
	id      atomic.Uint64

	stop chan struct{}
}

func NewBridge(signal, room string) *Bridge {
	return &Bridge{
		signal:  signal,
		room:    room,
		pending: map[uint64]chan response{},
		changes: make(chan uint64, 16),
		stop:    make(chan struct{}),
	}
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
			case <-time.After(2 * time.Second):
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
				time.Sleep(time.Second)
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
				if typ == "rtc-answer" || typ == "rtc-ice" || typ == "desktop-state" || typ == "desktop-error" {
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
		"type":       "hello",
		"role":       "windows",
		"protocol":   3,
		"oidcToken":  b.oidcToken(),
		"repository": os.Getenv("GITHUB_REPOSITORY"),
		"actor":      os.Getenv("GITHUB_ACTOR"),
		"runId":      os.Getenv("GITHUB_RUN_ID"),
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

	b.wsMu.Lock()
	b.ws = ws
	b.wsMu.Unlock()
	defer func() {
		b.wsMu.Lock()
		if b.ws == ws {
			b.ws = nil
		}
		b.wsMu.Unlock()
		ws.Close()
	}()

	log.Printf("RELAY CONNECTED")
	_ = b.sendText(b.helloPayload())

	helloStop := make(chan struct{})
	defer close(helloStop)

	go func() {
		ticker := time.NewTicker(15 * time.Second)
		defer ticker.Stop()

		for {
			select {
			case <-helloStop:
				return
			case <-ticker.C:
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

	if typ == "rtc-offer" || typ == "rtc-ice" || typ == "rtc-restart" || typ == "desktop-control" {
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
	if len(p) < 21 || !bytes.Equal(p[:4], magic) || p[4] != fResp {
		return
	}
	r := bytes.NewReader(p[5:])
	var id uint64
	var st int32
	var actual uint32
	if binary.Read(r, binary.BigEndian, &id) != nil {
		return
	}
	if binary.Read(r, binary.BigEndian, &st) != nil {
		return
	}
	if binary.Read(r, binary.BigEndian, &actual) != nil {
		return
	}
	data, _ := io.ReadAll(r)
	if uint32(len(data)) > actual {
		data = data[:actual]
	}
	b.pendMu.Lock()
	ch := b.pending[id]
	delete(b.pending, id)
	b.pendMu.Unlock()
	if ch != nil {
		ch <- response{st, actual, data}
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

func (b *Bridge) Transfer(dir, ep uint8, setup [8]byte, payload []byte, n int) response {
	if n < 0 || n > maxTransfer {
		return response{status: -90}
	}
	id := b.id.Add(1)
	ch := make(chan response, 1)
	b.pendMu.Lock()
	b.pending[id] = ch
	b.pendMu.Unlock()

	buf := new(bytes.Buffer)
	buf.Write(magic)
	buf.WriteByte(fReq)
	binary.Write(buf, binary.BigEndian, id)
	buf.WriteByte(dir)
	buf.WriteByte(ep)
	binary.Write(buf, binary.BigEndian, uint32(30000))
	binary.Write(buf, binary.BigEndian, uint32(n))
	buf.Write(setup[:])
	if dir == 0 && n > 0 {
		if len(payload) < n {
			n = len(payload)
		}
		buf.Write(payload[:n])
	}

	encrypted, e := b.encryptToAndroid(buf.Bytes())
	if e != nil {
		b.pendMu.Lock()
		delete(b.pending, id)
		b.pendMu.Unlock()
		return response{status: -107}
	}
	if e := b.write(websocket.BinaryMessage, encrypted); e != nil {
		b.pendMu.Lock()
		delete(b.pending, id)
		b.pendMu.Unlock()
		return response{status: -107}
	}

	select {
	case r := <-ch:
		return r
	case <-time.After(35 * time.Second):
		b.pendMu.Lock()
		delete(b.pending, id)
		b.pendMu.Unlock()
		return response{status: -110}
	}
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
		c.Write(buf.Bytes())
		return
	}
	binary.Write(buf, binary.BigEndian, uint32(1))
	writeDev(buf, d, true)
	c.Write(buf.Bytes())
}

func (s *Server) importDev(c net.Conn, bus string) {
	d := s.b.Device()
	buf := new(bytes.Buffer)
	binary.Write(buf, binary.BigEndian, uint16(ver))
	binary.Write(buf, binary.BigEndian, uint16(opRepImport))
	if d == nil || bus != d.BusID {
		binary.Write(buf, binary.BigEndian, uint32(1))
		c.Write(buf.Bytes())
		return
	}
	binary.Write(buf, binary.BigEndian, uint32(0))
	writeDev(buf, d, false)
	if _, e := c.Write(buf.Bytes()); e != nil {
		return
	}
	c.SetDeadline(time.Time{})
	s.addImport(c)
	defer s.delImport(c)
	log.Printf("USB/IP IMPORT %s gen=%d", bus, s.b.Generation())
	s.urbs(c)
}

func (s *Server) urbs(c net.Conn) {
	var wm sync.Mutex
	var cm sync.Mutex
	cancelled := map[uint32]bool{}

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

			if ep == 0 {
				log.Printf(
					"URB SUBMIT seq=%d devid=%08x dir=%d ep=%d len=%d flags=%08x start=%d packets=%d interval=%d setup=% x",
					seq, devid, dir, ep, n, flags, startFrame, packets, interval, setup,
				)
			} else {
				log.Printf(
					"URB SUBMIT seq=%d dir=%d ep=%d len=%d flags=%08x",
					seq, dir, ep, n, flags,
				)
			}

			if n < 0 || n > maxTransfer {
				log.Printf("URB REJECT seq=%d invalid length=%d", seq, n)
				go retSub(c, &wm, seq, -90, 0, nil)
				continue
			}

			var payload []byte
			if dir == 0 && n > 0 {
				payload, e = full(c, n)
				if e != nil {
					return
				}
			}

			if packets > 0 {
				if _, e = full(c, int(packets)*16); e != nil {
					return
				}
				go retSub(c, &wm, seq, -95, 0, nil)
				continue
			}

			go func(seq, dir, ep uint32, setup [8]byte, payload []byte, n int) {
				r := s.b.Transfer(uint8(dir), uint8(ep), setup, payload, n)

				if ep == 0 {
					preview := r.data
					if len(preview) > 32 {
						preview = preview[:32]
					}
					log.Printf(
						"URB COMPLETE seq=%d ep=0 status=%d actual=%d data[0:%d]=% x",
						seq, r.status, r.actual, len(preview), preview,
					)
				} else {
					log.Printf(
						"URB COMPLETE seq=%d ep=%d status=%d actual=%d",
						seq, ep, r.status, r.actual,
					)
				}

				cm.Lock()
				x := cancelled[seq]
				delete(cancelled, seq)
				cm.Unlock()
				if x {
					return
				}
				data := r.data
				if dir == 0 {
					data = nil
				}
				retSub(c, &wm, seq, r.status, r.actual, data)
			}(seq, dir, ep, setup, payload, n)
			continue
		}

		if cmd == cmdUnlink {
			target := binary.BigEndian.Uint32(h[20:24])
			cm.Lock()
			cancelled[target] = true
			cm.Unlock()
			retUnlinkFn(c, &wm, seq, -104)
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
	c.Write(b.Bytes())
}

func retUnlinkFn(c net.Conn, m *sync.Mutex, seq uint32, st int32) {
	b := new(bytes.Buffer)
	for _, v := range []any{uint32(retUnlink), seq, uint32(0), uint32(0), uint32(0), st} {
		binary.Write(b, binary.BigEndian, v)
	}
	b.Write(make([]byte, 24))
	m.Lock()
	defer m.Unlock()
	c.Write(b.Bytes())
}

func main() {
	signalURL := flag.String("signal", "", "relay URL")
	room := flag.String("room", "", "room")
	flag.Parse()
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
