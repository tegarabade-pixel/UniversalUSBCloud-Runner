"""Universal USB Cloud v2.8.0 Remote Transport v3 native Windows desktop host.

Transport:
  aiortc WebRTC (DTLS-SRTP/SCTP)
Media:
  desktop -> H264/VP8 negotiated by WebRTC
  WASAPI loopback -> Opus when a render endpoint exists
Input:
  unordered/no-retry data channel: motion, wheel, touch move
  reliable data channel: buttons, keyboard, text

The host listens only on 127.0.0.1:8765 for signaling from the already
OIDC-authenticated UUC Go relay agent. It never opens an Internet-facing port.
"""
from __future__ import annotations

import asyncio
import ctypes
import fractions
import json
import logging
import os
import sys
import time
from ctypes import wintypes
from typing import Any, Optional

import av
import mss
import numpy as np
import websockets
from aiortc import (
    AudioStreamTrack,
    RTCConfiguration,
    RTCIceServer,
    RTCPeerConnection,
    RTCSessionDescription,
    RTCRtpSender,
    VideoStreamTrack,
)
from aiortc.sdp import candidate_from_sdp

try:
    import pyaudiowpatch as pyaudio
except Exception:
    pyaudio = None

LOG = logging.getLogger("uuc-desktop")
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")

HOST = "127.0.0.1"
PORT = int(os.environ.get("UUC_DESKTOP_IPC_PORT", "8765"))
TARGET_W = max(640, int(os.environ.get("UUC_DESKTOP_WIDTH", "1280")))
TARGET_H = max(360, int(os.environ.get("UUC_DESKTOP_HEIGHT", "720")))
TARGET_FPS = max(15, min(60, int(os.environ.get("UUC_DESKTOP_FPS", "30"))))

# ---------------------------------------------------------------------------
# Win32 input
# ---------------------------------------------------------------------------
if sys.platform != "win32":
    raise RuntimeError("uuc_webrtc_host.py is Windows-only")

user32 = ctypes.WinDLL("user32", use_last_error=True)

INPUT_MOUSE = 0
INPUT_KEYBOARD = 1
MOUSEEVENTF_MOVE = 0x0001
MOUSEEVENTF_LEFTDOWN = 0x0002
MOUSEEVENTF_LEFTUP = 0x0004
MOUSEEVENTF_RIGHTDOWN = 0x0008
MOUSEEVENTF_RIGHTUP = 0x0010
MOUSEEVENTF_MIDDLEDOWN = 0x0020
MOUSEEVENTF_MIDDLEUP = 0x0040
MOUSEEVENTF_XDOWN = 0x0080
MOUSEEVENTF_XUP = 0x0100
MOUSEEVENTF_WHEEL = 0x0800
MOUSEEVENTF_HWHEEL = 0x1000
MOUSEEVENTF_ABSOLUTE = 0x8000
KEYEVENTF_KEYUP = 0x0002
KEYEVENTF_UNICODE = 0x0004
XBUTTON1 = 0x0001
XBUTTON2 = 0x0002
WHEEL_DELTA = 120

SM_CXSCREEN = 0
SM_CYSCREEN = 1

ULONG_PTR = wintypes.WPARAM


class MOUSEINPUT(ctypes.Structure):
    _fields_ = [
        ("dx", wintypes.LONG), ("dy", wintypes.LONG), ("mouseData", wintypes.DWORD),
        ("dwFlags", wintypes.DWORD), ("time", wintypes.DWORD), ("dwExtraInfo", ULONG_PTR),
    ]


class KEYBDINPUT(ctypes.Structure):
    _fields_ = [
        ("wVk", wintypes.WORD), ("wScan", wintypes.WORD), ("dwFlags", wintypes.DWORD),
        ("time", wintypes.DWORD), ("dwExtraInfo", ULONG_PTR),
    ]


class HARDWAREINPUT(ctypes.Structure):
    _fields_ = [("uMsg", wintypes.DWORD), ("wParamL", wintypes.WORD), ("wParamH", wintypes.WORD)]


class INPUT_UNION(ctypes.Union):
    _fields_ = [("mi", MOUSEINPUT), ("ki", KEYBDINPUT), ("hi", HARDWAREINPUT)]


class INPUT(ctypes.Structure):
    _anonymous_ = ("u",)
    _fields_ = [("type", wintypes.DWORD), ("u", INPUT_UNION)]


def _send_input(inp: INPUT) -> bool:
    return user32.SendInput(1, ctypes.byref(inp), ctypes.sizeof(INPUT)) == 1


def mouse(flags: int, dx: int = 0, dy: int = 0, data: int = 0) -> None:
    inp = INPUT(type=INPUT_MOUSE)
    inp.mi = MOUSEINPUT(dx, dy, data & 0xFFFFFFFF, flags, 0, 0)
    _send_input(inp)


def key_vk(vk: int, down: bool) -> None:
    inp = INPUT(type=INPUT_KEYBOARD)
    inp.ki = KEYBDINPUT(vk & 0xFFFF, 0, 0 if down else KEYEVENTF_KEYUP, 0, 0)
    _send_input(inp)


def text_unicode(text: str) -> None:
    raw = text.encode("utf-16-le", errors="surrogatepass")
    for i in range(0, len(raw), 2):
        unit = raw[i] | (raw[i + 1] << 8)
        down = INPUT(type=INPUT_KEYBOARD)
        down.ki = KEYBDINPUT(0, unit, KEYEVENTF_UNICODE, 0, 0)
        up = INPUT(type=INPUT_KEYBOARD)
        up.ki = KEYBDINPUT(0, unit, KEYEVENTF_UNICODE | KEYEVENTF_KEYUP, 0, 0)
        _send_input(down)
        _send_input(up)


# Android KeyEvent keyCode -> Windows VK. Printable IME text takes the Unicode path.
ANDROID_VK: dict[int, int] = {
    4: 0x1B,  # BACK -> ESC when sent as a physical key
    19: 0x26, 20: 0x28, 21: 0x25, 22: 0x27,
    23: 0x0D, 61: 0x09, 62: 0x20, 66: 0x0D, 67: 0x08,
    92: 0x21, 93: 0x22, 122: 0x24, 123: 0x23, 112: 0x2E, 124: 0x2D,
    111: 0x1B,
    113: 0x11, 114: 0x11,  # CTRL
    57: 0x12, 58: 0x12,    # ALT
    59: 0x10, 60: 0x10,    # SHIFT
    117: 0x5B, 118: 0x5C,  # META / Win
    115: 0x14, 116: 0x91, 143: 0x90,  # caps/scroll/num lock
    120: 0x2C, 121: 0x91,             # print screen / break-ish fallback
    131: 0x70, 132: 0x71, 133: 0x72, 134: 0x73, 135: 0x74, 136: 0x75,
    137: 0x76, 138: 0x77, 139: 0x78, 140: 0x79, 141: 0x7A, 142: 0x7B,
}
for i in range(26):
    ANDROID_VK[29 + i] = 0x41 + i
for i in range(10):
    ANDROID_VK[7 + i] = 0x30 + i
ANDROID_VK.update({
    68: 0xC0, 69: 0xBD, 70: 0xBB, 71: 0xDB, 72: 0xDD, 73: 0xDC,
    74: 0xBA, 75: 0xDE, 76: 0xBC, 77: 0xBE, 78: 0xBF,
    144: 0x60, 145: 0x61, 146: 0x62, 147: 0x63, 148: 0x64,
    149: 0x65, 150: 0x66, 151: 0x67, 152: 0x68, 153: 0x69,
    154: 0x6F, 155: 0x6A, 156: 0x6D, 157: 0x6B, 158: 0x6E, 160: 0x0D,
})


# ---------------------------------------------------------------------------
# Native Direct Touch injection, with mouse fallback if the host forbids it.
# ---------------------------------------------------------------------------
PT_TOUCH = 0x00000002
POINTER_FLAG_NEW = 0x00000001
POINTER_FLAG_INRANGE = 0x00000002
POINTER_FLAG_INCONTACT = 0x00000004
POINTER_FLAG_FIRSTBUTTON = 0x00000010
POINTER_FLAG_DOWN = 0x00010000
POINTER_FLAG_UPDATE = 0x00020000
POINTER_FLAG_UP = 0x00040000
TOUCH_MASK_CONTACTAREA = 0x00000001
TOUCH_MASK_ORIENTATION = 0x00000002
TOUCH_MASK_PRESSURE = 0x00000004
TOUCH_FEEDBACK_DEFAULT = 0x1


class POINT(ctypes.Structure):
    _fields_ = [("x", wintypes.LONG), ("y", wintypes.LONG)]


class RECT(ctypes.Structure):
    _fields_ = [("left", wintypes.LONG), ("top", wintypes.LONG), ("right", wintypes.LONG), ("bottom", wintypes.LONG)]


class POINTER_INFO(ctypes.Structure):
    _fields_ = [
        ("pointerType", wintypes.DWORD), ("pointerId", wintypes.UINT), ("frameId", wintypes.UINT),
        ("pointerFlags", wintypes.DWORD), ("sourceDevice", wintypes.HANDLE), ("hwndTarget", wintypes.HWND),
        ("ptPixelLocation", POINT), ("ptHimetricLocation", POINT), ("ptPixelLocationRaw", POINT),
        ("ptHimetricLocationRaw", POINT), ("dwTime", wintypes.DWORD), ("historyCount", wintypes.UINT),
        ("InputData", ctypes.c_int32), ("dwKeyStates", wintypes.DWORD),
        ("PerformanceCount", ctypes.c_uint64), ("ButtonChangeType", wintypes.DWORD),
    ]


class POINTER_TOUCH_INFO(ctypes.Structure):
    _fields_ = [
        ("pointerInfo", POINTER_INFO), ("touchFlags", wintypes.DWORD), ("touchMask", wintypes.DWORD),
        ("rcContact", RECT), ("rcContactRaw", RECT), ("orientation", wintypes.UINT), ("pressure", wintypes.UINT),
    ]


_TOUCH_OK = False
try:
    user32.InitializeTouchInjection.argtypes = [wintypes.UINT, wintypes.DWORD]
    user32.InitializeTouchInjection.restype = wintypes.BOOL
    user32.InjectTouchInput.argtypes = [wintypes.UINT, ctypes.POINTER(POINTER_TOUCH_INFO)]
    user32.InjectTouchInput.restype = wintypes.BOOL
    _TOUCH_OK = bool(user32.InitializeTouchInjection(10, TOUCH_FEEDBACK_DEFAULT))
except Exception:
    _TOUCH_OK = False


def screen_size() -> tuple[int, int]:
    return max(1, user32.GetSystemMetrics(SM_CXSCREEN)), max(1, user32.GetSystemMetrics(SM_CYSCREEN))


def inject_touch(contacts: list[dict[str, Any]]) -> None:
    global _TOUCH_OK
    sw, sh = screen_size()
    if not contacts:
        return
    if not _TOUCH_OK:
        c = contacts[0]
        x = int(max(0.0, min(1.0, float(c.get("x", 0)))) * 65535)
        y = int(max(0.0, min(1.0, float(c.get("y", 0)))) * 65535)
        mouse(MOUSEEVENTF_MOVE | MOUSEEVENTF_ABSOLUTE, x, y)
        st = c.get("state")
        if st == "down": mouse(MOUSEEVENTF_LEFTDOWN)
        elif st == "up": mouse(MOUSEEVENTF_LEFTUP)
        return

    infos = (POINTER_TOUCH_INFO * len(contacts))()
    for i, c in enumerate(contacts):
        x = int(max(0.0, min(1.0, float(c.get("x", 0.0)))) * (sw - 1))
        y = int(max(0.0, min(1.0, float(c.get("y", 0.0)))) * (sh - 1))
        state = str(c.get("state", "move"))
        flags = POINTER_FLAG_INRANGE | POINTER_FLAG_INCONTACT | POINTER_FLAG_FIRSTBUTTON
        if state == "down": flags |= POINTER_FLAG_NEW | POINTER_FLAG_DOWN
        elif state == "up": flags = POINTER_FLAG_UP
        else: flags |= POINTER_FLAG_UPDATE
        p = POINTER_INFO()
        p.pointerType = PT_TOUCH
        p.pointerId = max(1, int(c.get("id", i + 1)))
        p.pointerFlags = flags
        p.ptPixelLocation = POINT(x, y)
        p.ptPixelLocationRaw = POINT(x, y)
        t = POINTER_TOUCH_INFO()
        t.pointerInfo = p
        t.touchFlags = 0
        t.touchMask = TOUCH_MASK_CONTACTAREA | TOUCH_MASK_ORIENTATION | TOUCH_MASK_PRESSURE
        size = max(0.0, min(1.0, float(c.get("size", 0.03))))
        radius = max(3, int(size * min(sw, sh) * 0.04))
        t.rcContact = RECT(x - radius, y - radius, x + radius, y + radius)
        t.rcContactRaw = t.rcContact
        t.orientation = 90
        t.pressure = int(max(0.0, min(1.0, float(c.get("pressure", 0.5)))) * 1024)
        infos[i] = t
    if not user32.InjectTouchInput(len(contacts), infos):
        LOG.warning("InjectTouchInput failed winerr=%s; falling back to mouse", ctypes.get_last_error())
        _TOUCH_OK = False
        inject_touch(contacts)


class InputInjector:
    def handle(self, obj: dict[str, Any]) -> None:
        typ = obj.get("type")
        sw, sh = screen_size()
        if typ == "mouse-relative":
            # Fractions of the Android viewport -> fractions of the remote desktop.
            dx = int(float(obj.get("dx", 0.0)) * sw * 1.35)
            dy = int(float(obj.get("dy", 0.0)) * sh * 1.35)
            mouse(MOUSEEVENTF_MOVE, dx, dy)
        elif typ == "mouse-absolute":
            x = int(max(0.0, min(1.0, float(obj.get("x", 0.0)))) * 65535)
            y = int(max(0.0, min(1.0, float(obj.get("y", 0.0)))) * 65535)
            mouse(MOUSEEVENTF_MOVE | MOUSEEVENTF_ABSOLUTE, x, y)
        elif typ == "mouse-button":
            self.button(str(obj.get("button", "left")), bool(obj.get("down", False)))
        elif typ == "click":
            button = str(obj.get("button", "left"))
            for _ in range(max(1, min(3, int(obj.get("count", 1))))):
                self.button(button, True); self.button(button, False)
        elif typ == "wheel":
            v = float(obj.get("v", 0.0))
            h = float(obj.get("h", 0.0))
            if "dy" in obj: v = float(obj.get("dy", 0.0)) * 8.0
            if abs(v) > 0.001: mouse(MOUSEEVENTF_WHEEL, data=int(v * WHEEL_DELTA))
            if abs(h) > 0.001: mouse(MOUSEEVENTF_HWHEEL, data=int(h * WHEEL_DELTA))
        elif typ == "key":
            keycode = int(obj.get("keyCode", -1))
            vk = ANDROID_VK.get(keycode)
            if vk is not None:
                key_vk(vk, str(obj.get("action", "down")) == "down")
        elif typ == "text":
            text_unicode(str(obj.get("text", "")))
        elif typ == "touch":
            contacts = obj.get("contacts")
            if isinstance(contacts, list): inject_touch(contacts)
        elif typ == "release-all":
            # Defensive reset when Android loses focus/reconnects, preventing stuck
            # Ctrl/Alt/Shift/Win or mouse buttons after a packet/session interruption.
            for vk in (0x10, 0x11, 0x12, 0x5B, 0x5C):
                key_vk(vk, False)
            mouse(MOUSEEVENTF_LEFTUP)
            mouse(MOUSEEVENTF_RIGHTUP)
            mouse(MOUSEEVENTF_MIDDLEUP)
            mouse(MOUSEEVENTF_XUP, data=XBUTTON1)
            mouse(MOUSEEVENTF_XUP, data=XBUTTON2)

    @staticmethod
    def button(name: str, down: bool) -> None:
        table = {
            "left": (MOUSEEVENTF_LEFTDOWN, MOUSEEVENTF_LEFTUP, 0),
            "right": (MOUSEEVENTF_RIGHTDOWN, MOUSEEVENTF_RIGHTUP, 0),
            "middle": (MOUSEEVENTF_MIDDLEDOWN, MOUSEEVENTF_MIDDLEUP, 0),
            "x1": (MOUSEEVENTF_XDOWN, MOUSEEVENTF_XUP, XBUTTON1),
            "x2": (MOUSEEVENTF_XDOWN, MOUSEEVENTF_XUP, XBUTTON2),
        }
        a, b, data = table.get(name, table["left"])
        mouse(a if down else b, data=data)


# ---------------------------------------------------------------------------
# Media tracks
# ---------------------------------------------------------------------------
class DesktopVideoTrack(VideoStreamTrack):
    """Latest-frame desktop capture with runtime quality profile changes.

    Lowering resolution/FPS is intentionally used instead of queueing frames. The
    goal is interactive latency: when the network is under pressure, send less
    work rather than building an ever-growing capture/encode queue.
    """
    def __init__(self) -> None:
        super().__init__()
        self.sct = None
        self.monitor = None
        self.capture_available = False
        self.capture_error = ""
        self._test_pattern = False
        try:
            self.sct = mss.mss()
            if len(self.sct.monitors) < 2:
                raise RuntimeError("No Windows desktop monitor available")
            self.monitor = self.sct.monitors[1]
            self.capture_available = True
            try:
                self.sct.with_cursor = True
            except Exception:
                pass
        except Exception as exc:
            self.capture_error = f"{type(exc).__name__}: {exc}"
            self._test_pattern = True
            LOG.warning("Desktop capture unavailable; diagnostic test pattern forced: %s", self.capture_error)
        self._start = time.monotonic()
        self._seq = 0
        self._profile = "balanced"
        self._width = TARGET_W
        self._height = TARGET_H
        self._fps = TARGET_FPS

    @property
    def profile(self) -> tuple[str, int, int, int]:
        return self._profile, self._width, self._height, self._fps

    def set_test_pattern(self, enabled: bool) -> bool:
        self._test_pattern = bool(enabled) or not self.capture_available
        LOG.info("diagnostic test_pattern=%s capture_available=%s", self._test_pattern, self.capture_available)
        return self._test_pattern

    def set_profile(self, profile: str, width: int, height: int, fps: int) -> tuple[str, int, int, int]:
        profile = (profile or "adaptive").strip().lower()[:32]
        # Never exceed operator configured maximums. Keep even dimensions for YUV420/H264.
        width = max(320, min(TARGET_W, int(width or TARGET_W))) // 2 * 2
        height = max(180, min(TARGET_H, int(height or TARGET_H))) // 2 * 2
        fps = max(10, min(TARGET_FPS, int(fps or TARGET_FPS)))
        self._profile, self._width, self._height, self._fps = profile, width, height, fps
        # Rebase pacing so a profile change cannot create a huge timing catch-up.
        self._start = time.monotonic()
        self._seq = 0
        LOG.info("capture profile=%s %dx%d@%dfps", profile, width, height, fps)
        return self.profile

    async def recv(self) -> av.VideoFrame:
        fps = max(10, self._fps)
        interval = 1.0 / fps
        target = self._start + self._seq * interval
        now = time.monotonic()
        if target > now:
            await asyncio.sleep(target - now)
        # If capture/encode stalled, skip old frame times. Never queue obsolete desktop frames.
        now = time.monotonic()
        if now - target > interval * 2:
            self._seq = int((now - self._start) / interval)
        self._seq += 1
        tw = self._width
        th = self._height
        if self._test_pattern or not self.capture_available or self.sct is None or self.monitor is None:
            # Network/codec/render isolation pattern. It keeps media alive even if
            # Windows desktop capture is the failing component.
            arr = np.zeros((th, tw, 3), dtype=np.uint8)
            colors = ((255,255,255),(0,255,255),(255,255,0),(0,255,0),(255,0,255),(0,0,255),(255,0,0))
            band = max(1, tw // len(colors))
            for i, color in enumerate(colors):
                arr[:, i*band:(i+1)*band, :] = color
            marker = int((self._seq * 9) % max(1, tw))
            arr[:, max(0, marker-4):min(tw, marker+4), :] = (255,255,255)
            frame = av.VideoFrame.from_ndarray(arr, format="bgr24")
            frame = frame.reformat(width=max(2, tw), height=max(2, th), format="yuv420p")
        else:
            shot = self.sct.grab(self.monitor)
            arr = np.asarray(shot, dtype=np.uint8)
            frame = av.VideoFrame.from_ndarray(arr, format="bgra")
            src_aspect = frame.width / max(1, frame.height)
            if abs((tw / th) - src_aspect) > 0.01:
                if tw / th > src_aspect:
                    tw = int(th * src_aspect) // 2 * 2
                else:
                    th = int(tw / src_aspect) // 2 * 2
            frame = frame.reformat(width=max(2, tw), height=max(2, th), format="yuv420p")
        frame.pts = int((time.monotonic() - self._start) * 90000)
        frame.time_base = fractions.Fraction(1, 90000)
        return frame


class LoopbackAudioTrack(AudioStreamTrack):
    SAMPLE_RATE = 48000
    SAMPLES = 960  # 20 ms

    def __init__(self) -> None:
        super().__init__()
        self.pa = None
        self.stream = None
        self.channels = 2
        self._pts = 0
        self.available = False
        if pyaudio is None:
            LOG.warning("PyAudioWPatch unavailable; audio fallback = silence")
            return
        try:
            self.pa = pyaudio.PyAudio()
            dev = self.pa.get_default_wasapi_loopback()
            self.channels = max(1, min(2, int(dev.get("maxInputChannels", 2))))
            rate = int(dev.get("defaultSampleRate", self.SAMPLE_RATE))
            self.SAMPLE_RATE = rate if rate > 0 else 48000
            self.SAMPLES = max(160, int(self.SAMPLE_RATE * 0.02))
            self.stream = self.pa.open(
                format=pyaudio.paInt16,
                channels=self.channels,
                rate=self.SAMPLE_RATE,
                input=True,
                input_device_index=int(dev["index"]),
                frames_per_buffer=self.SAMPLES,
            )
            self.available = True
            LOG.info("WASAPI loopback: %s rate=%s channels=%s", dev.get("name"), self.SAMPLE_RATE, self.channels)
        except Exception as exc:
            LOG.warning("WASAPI loopback unavailable: %s; audio fallback = silence", exc)
            self.close_audio()

    async def recv(self) -> av.AudioFrame:
        if self.available and self.stream is not None:
            try:
                data = await asyncio.to_thread(self.stream.read, self.SAMPLES, False)
            except Exception:
                data = bytes(self.SAMPLES * self.channels * 2)
        else:
            await asyncio.sleep(self.SAMPLES / self.SAMPLE_RATE)
            data = bytes(self.SAMPLES * self.channels * 2)
        layout = "mono" if self.channels == 1 else "stereo"
        frame = av.AudioFrame(format="s16", layout=layout, samples=self.SAMPLES)
        frame.planes[0].update(data[: frame.planes[0].buffer_size].ljust(frame.planes[0].buffer_size, b"\x00"))
        frame.sample_rate = self.SAMPLE_RATE
        frame.pts = self._pts
        frame.time_base = fractions.Fraction(1, self.SAMPLE_RATE)
        self._pts += self.SAMPLES
        return frame

    def close_audio(self) -> None:
        try:
            if self.stream is not None: self.stream.close()
        except Exception:
            pass
        try:
            if self.pa is not None: self.pa.terminate()
        except Exception:
            pass
        self.stream = None
        self.pa = None
        self.available = False

    def stop(self) -> None:
        self.close_audio()
        super().stop()


# ---------------------------------------------------------------------------
# WebRTC host / local signaling IPC
# ---------------------------------------------------------------------------
class DesktopHost:
    def __init__(self) -> None:
        self.pc: Optional[RTCPeerConnection] = None
        self.ws = None
        self.injector = InputInjector()
        self.pending_ice: list[dict[str, Any]] = []
        self.video: Optional[DesktopVideoTrack] = None
        self.audio: Optional[LoopbackAudioTrack] = None
        self.session_id: int = 0
        self.active_ice_provider = os.environ.get("UUC_ICE_PROVIDER", "none")
        self.active_ice_mode = os.environ.get("UUC_ICE_MODE", "direct-only")

    @staticmethod
    def _parse_ice_items(items: Any) -> list[RTCIceServer]:
        servers: list[RTCIceServer] = []
        if not isinstance(items, list):
            return servers
        for item in items[:8]:
            if not isinstance(item, dict):
                continue
            urls = item.get("urls", item.get("url", []))
            if isinstance(urls, str):
                urls = [urls]
            if not isinstance(urls, list):
                continue
            clean: list[str] = []
            for value in urls[:10]:
                u = str(value).strip()
                lower = u.lower()
                if lower.startswith(("stun:", "stuns:", "turn:", "turns:")) and len(u) <= 240:
                    clean.append(u)
            if not clean:
                continue
            servers.append(RTCIceServer(
                urls=clean,
                username=str(item.get("username", ""))[:256],
                credential=str(item.get("credential", ""))[:512],
            ))
        return servers

    def rtc_config(self, offered_ice: Any = None, offered_provider: str = "", offered_mode: str = "") -> RTCConfiguration:
        # The rtc-offer travels through the already verified/e2e signaling path.
        # v2.8.2 may attach the exact effective ICE list Android is using, which
        # avoids rebuilding Runner code just to swap diagnostic STUN endpoints.
        servers = self._parse_ice_items(offered_ice)
        if servers:
            self.active_ice_provider = (offered_provider or "android-session-ice")[:80]
            self.active_ice_mode = (offered_mode or "session-override")[:80]
        else:
            raw = os.environ.get("UUC_ICE_SERVERS_JSON", "").strip()
            if raw:
                try:
                    servers = self._parse_ice_items(json.loads(raw))
                except Exception as exc:
                    LOG.warning("UUC_ICE_SERVERS_JSON parse failed: %s", exc)
            self.active_ice_provider = os.environ.get("UUC_ICE_PROVIDER", "none")
            self.active_ice_mode = os.environ.get("UUC_ICE_MODE", "direct-only")

        schemes: list[str] = []
        for srv in servers:
            urls = srv.urls if isinstance(srv.urls, list) else [srv.urls]
            for u in urls:
                schemes.append(str(u).split(":", 1)[0].lower())
        LOG.info("ICE servers loaded provider=%s mode=%s count=%d stun=%d turn=%d sessionOverride=%s",
                 self.active_ice_provider, self.active_ice_mode, len(servers),
                 sum(1 for x in schemes if x.startswith("stun")),
                 sum(1 for x in schemes if x.startswith("turn")),
                 bool(offered_ice))
        return RTCConfiguration(iceServers=servers)

    async def close_pc(self) -> None:
        pc, self.pc = self.pc, None
        if pc is not None:
            try: await pc.close()
            except Exception: pass
        if self.video is not None:
            try: self.video.stop()
            except Exception: pass
            self.video = None
        if self.audio is not None:
            try: self.audio.stop()
            except Exception: pass
            self.audio = None
        self.pending_ice.clear()

    async def send(self, obj: dict[str, Any]) -> None:
        if self.ws is not None:
            await self.ws.send(json.dumps(obj, separators=(",", ":")))

    async def new_pc(self, session_id: int, offered_ice: Any = None, offered_provider: str = "", offered_mode: str = "") -> RTCPeerConnection:
        # Close the previous PC before switching session id so late callbacks from
        # the old PC are tagged with the old generation and ignored by Android.
        await self.close_pc()
        self.session_id = session_id
        pc_session = session_id
        pc = RTCPeerConnection(self.rtc_config(offered_ice, offered_provider, offered_mode))
        self.pc = pc
        self.video = DesktopVideoTrack()
        self.audio = LoopbackAudioTrack()
        video_sender = pc.addTrack(self.video)
        pc.addTrack(self.audio)

        # Prefer H.264 for Android hardware decode when both sides support it, but
        # retain the remaining codecs as negotiated fallbacks.
        try:
            caps = RTCRtpSender.getCapabilities("video").codecs
            preferred = [c for c in caps if c.mimeType.lower() == "video/h264"]
            preferred += [c for c in caps if c not in preferred]
            transceiver = next(t for t in pc.getTransceivers() if t.sender == video_sender)
            if preferred:
                transceiver.setCodecPreferences(preferred)
                LOG.info("video codec preference=%s", [c.mimeType for c in preferred])
        except Exception as exc:
            LOG.info("video codec preference fallback: %s", exc)

        @pc.on("datachannel")
        def on_datachannel(channel):
            LOG.info("datachannel open request label=%s", channel.label)
            @channel.on("message")
            def on_message(message):
                if pc_session != self.session_id:
                    return
                if not isinstance(message, str):
                    try: message = bytes(message).decode("utf-8", "replace")
                    except Exception: return
                try:
                    obj = json.loads(message)
                    if isinstance(obj, dict) and obj.get("type") == "desktop-control":
                        asyncio.create_task(self.apply_control(obj))
                    elif isinstance(obj, dict) and obj.get("type") == "diag-ping":
                        nonce = int(obj.get("nonce", 0) or 0)
                        channel.send(json.dumps({
                            "type": "diag-pong",
                            "nonce": nonce,
                            "sessionId": pc_session,
                            "captureAvailable": bool(self.video and self.video.capture_available),
                            "pattern": bool(self.video and self.video._test_pattern),
                        }, separators=(",", ":")))
                        LOG.info("diagnostic ping/pong channel=%s nonce=%s", channel.label, nonce)
                    elif isinstance(obj, dict) and obj.get("type") == "diag-control":
                        enabled = bool(obj.get("pattern", False))
                        applied = self.video.set_test_pattern(enabled) if self.video is not None else enabled
                        channel.send(json.dumps({
                            "type": "diag-ack",
                            "sessionId": pc_session,
                            "pattern": bool(applied),
                            "captureAvailable": bool(self.video and self.video.capture_available),
                        }, separators=(",", ":")))
                    else:
                        self.injector.handle(obj)
                except Exception as exc:
                    LOG.debug("datachannel decode failed: %s", exc)

            @channel.on("open")
            def on_open():
                LOG.info("diagnostic datachannel OPEN label=%s session=%s", channel.label, pc_session)
                asyncio.create_task(self.send({
                    "type": "desktop-state", "state": "diag-datachannel-open",
                    "desktopProtocol": 3, "sessionId": pc_session,
                    "channel": channel.label,
                    "captureAvailable": bool(self.video and self.video.capture_available),
                }))

            @channel.on("close")
            def on_close():
                LOG.info("diagnostic datachannel CLOSED label=%s session=%s", channel.label, pc_session)

        @pc.on("connectionstatechange")
        async def state_change():
            LOG.info("WebRTC connectionState=%s ice=%s gathering=%s",
                     pc.connectionState, pc.iceConnectionState, pc.iceGatheringState)
            await self.send({
                "type": "desktop-state",
                "state": pc.connectionState,
                "desktopProtocol": 3,
                "sessionId": pc_session,
                "iceState": pc.iceConnectionState,
                "iceGathering": pc.iceGatheringState,
                "turnMode": self.active_ice_mode, "iceProvider": self.active_ice_provider,
                "audioAvailable": bool(self.audio and self.audio.available),
            })

        @pc.on("iceconnectionstatechange")
        async def ice_state_change():
            LOG.info("WebRTC ICE state=%s gathering=%s", pc.iceConnectionState, pc.iceGatheringState)
            await self.send({
                "type": "desktop-state",
                "state": "ice-" + str(pc.iceConnectionState),
                "desktopProtocol": 3,
                "sessionId": pc_session,
                "iceState": pc.iceConnectionState,
                "iceGathering": pc.iceGatheringState,
                "turnMode": self.active_ice_mode, "iceProvider": self.active_ice_provider,
            })

        @pc.on("icegatheringstatechange")
        async def ice_gathering_change():
            LOG.info("WebRTC ICE gathering=%s", pc.iceGatheringState)

        return pc

    async def apply_control(self, obj: dict[str, Any]) -> None:
        if self.video is None:
            return
        profile = str(obj.get("profile", "adaptive"))
        presets = {
            "survival": (640, 360, 15),
            "low": (854, 480, 20),
            "balanced": (1280, 720, 30),
        }
        default = presets.get(profile.lower(), (TARGET_W, TARGET_H, TARGET_FPS))
        width = int(obj.get("width", default[0]) or default[0])
        height = int(obj.get("height", default[1]) or default[1])
        fps = int(obj.get("fps", default[2]) or default[2])
        applied = self.video.set_profile(profile, width, height, fps)
        await self.send({
            "type": "desktop-state",
            "state": "profile-applied",
            "desktopProtocol": 3,
            "sessionId": self.session_id,
            "profile": applied[0], "width": applied[1], "height": applied[2], "fps": applied[3],
            "reason": str(obj.get("reason", "adaptive"))[:80],
            "turnMode": self.active_ice_mode,
            "iceProvider": self.active_ice_provider,
        })

    async def add_remote_ice(self, ice: dict[str, Any]) -> None:
        if self.pc is None:
            self.pending_ice.append(ice)
            return
        cand_text = str(ice.get("candidate", ""))
        if not cand_text:
            await self.pc.addIceCandidate(None)
            return
        if cand_text.startswith("candidate:"):
            cand_text = cand_text.split(":", 1)[1]
        candidate = candidate_from_sdp(cand_text)
        candidate.sdpMid = ice.get("sdpMid")
        candidate.sdpMLineIndex = int(ice.get("sdpMLineIndex", 0))
        await self.pc.addIceCandidate(candidate)

    async def handle(self, obj: dict[str, Any]) -> None:
        typ = obj.get("type")
        sid = int(obj.get("sessionId", 0) or 0)
        if typ == "rtc-offer":
            offered_ice = obj.get("iceServers")
            offered_provider = str(obj.get("iceProvider", ""))
            offered_mode = str(obj.get("iceMode", ""))
            pc = await self.new_pc(sid, offered_ice, offered_provider, offered_mode)
            offer = RTCSessionDescription(sdp=str(obj.get("sdp", "")), type="offer")
            await pc.setRemoteDescription(offer)
            pending, self.pending_ice = self.pending_ice, []
            for ice in pending:
                await self.add_remote_ice(ice)
            answer = await pc.createAnswer()
            # aiortc gathers ICE here; pc.localDescription contains candidates.
            await pc.setLocalDescription(answer)
            types = sorted(set(parts[parts.index("typ") + 1]
                               for line in pc.localDescription.sdp.splitlines()
                               if line.startswith("a=candidate:") and " typ " in line
                               for parts in [line.split()] if "typ" in parts and parts.index("typ") + 1 < len(parts)))
            LOG.info("RTC answer local candidate types=%s", types)
            await self.send({"type": "rtc-answer", "desktopProtocol": 3, "sessionId": self.session_id, "sdp": pc.localDescription.sdp,
                             "candidateTypes": types, "turnMode": self.active_ice_mode, "iceProvider": self.active_ice_provider})
            await self.send({
                "type": "desktop-state", "state": "diag-answer-sent",
                "desktopProtocol": 3, "sessionId": self.session_id,
                "captureAvailable": bool(self.video and self.video.capture_available),
                "captureError": "" if not self.video else self.video.capture_error[:160],
                "pattern": bool(self.video and self.video._test_pattern),
                "candidateTypes": types,
                "turnMode": self.active_ice_mode,
                "iceProvider": self.active_ice_provider,
            })
            LOG.info("RTC answer sent (%d SDP bytes) capture=%s pattern=%s", len(pc.localDescription.sdp), bool(self.video and self.video.capture_available), bool(self.video and self.video._test_pattern))
        elif typ == "rtc-ice":
            if sid and self.session_id and sid != self.session_id:
                return
            ice = obj.get("ice")
            if isinstance(ice, dict): await self.add_remote_ice(ice)
        elif typ == "rtc-restart":
            if not sid or not self.session_id or sid >= self.session_id:
                await self.close_pc()
        elif typ == "desktop-control":
            if not sid or not self.session_id or sid == self.session_id:
                await self.apply_control(obj)

    async def client(self, ws) -> None:
        self.ws = ws
        LOG.info("Local relay agent connected to desktop IPC")
        await self.send({"type": "desktop-state", "state": "host-ready", "desktopProtocol": 3, "sessionId": self.session_id, "turnMode": self.active_ice_mode, "iceProvider": self.active_ice_provider})
        try:
            async for raw in ws:
                try:
                    obj = json.loads(raw)
                    await self.handle(obj)
                except Exception as exc:
                    LOG.exception("desktop signal failed")
                    await self.send({"type": "desktop-error", "message": f"{type(exc).__name__}: {exc}"})
        finally:
            self.ws = None
            await self.close_pc()
            LOG.info("Local relay agent disconnected from desktop IPC")


async def main() -> None:
    host = DesktopHost()
    async with websockets.serve(host.client, HOST, PORT, max_size=4 * 1024 * 1024, ping_interval=10, ping_timeout=20):
        LOG.info("UUC v2.8.1 diagnostic desktop IPC ready ws://%s:%d max=%dx%d@%dfps touch=%s", HOST, PORT, TARGET_W, TARGET_H, TARGET_FPS, _TOUCH_OK)
        await asyncio.Future()


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        pass
