"""Universal USB Cloud v2.10.11 CAPTURE-TRUTH native Windows desktop host.

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
kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
user32.GetProcessWindowStation.restype = wintypes.HANDLE
user32.GetThreadDesktop.restype = wintypes.HANDLE
kernel32.GetCurrentThreadId.restype = wintypes.DWORD
kernel32.WTSGetActiveConsoleSessionId.restype = wintypes.DWORD
kernel32.ProcessIdToSessionId.argtypes = [wintypes.DWORD, ctypes.POINTER(wintypes.DWORD)]
kernel32.ProcessIdToSessionId.restype = wintypes.BOOL

UOI_NAME = 2

def _user_object_name(handle) -> str:
    if not handle:
        return "?"
    needed = wintypes.DWORD(0)
    user32.GetUserObjectInformationW(handle, UOI_NAME, None, 0, ctypes.byref(needed))
    if needed.value <= 2:
        return "?"
    buf = ctypes.create_unicode_buffer(max(2, needed.value // ctypes.sizeof(ctypes.c_wchar) + 2))
    if not user32.GetUserObjectInformationW(handle, UOI_NAME, buf, ctypes.sizeof(buf), ctypes.byref(needed)):
        return "?"
    return buf.value or "?"

def _capture_session_context() -> dict[str, Any]:
    """Describe the Windows session/window-station/desktop seen by this host process.

    A successful MSS grab can still return an all-black framebuffer when the process
    lives in a non-interactive Windows session. Keep this context attached to media
    telemetry so Android can distinguish transport success from source-capture failure.
    """
    pid = os.getpid()
    sid = wintypes.DWORD(0xFFFFFFFF)
    try:
        ok = bool(kernel32.ProcessIdToSessionId(pid, ctypes.byref(sid)))
        process_session = int(sid.value) if ok else -1
    except Exception:
        process_session = -1
    try:
        active_console = int(kernel32.WTSGetActiveConsoleSessionId())
        if active_console == 0xFFFFFFFF:
            active_console = -1
    except Exception:
        active_console = -1
    try:
        winsta = _user_object_name(user32.GetProcessWindowStation())
    except Exception:
        winsta = "?"
    try:
        desktop = _user_object_name(user32.GetThreadDesktop(kernel32.GetCurrentThreadId()))
    except Exception:
        desktop = "?"
    return {
        "processSession": process_session,
        "activeConsoleSession": active_console,
        "windowStation": winsta[:96],
        "desktopName": desktop[:96],
    }

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
        self.capture_backend = "mss"
        self.monitor_index = -1
        self.monitor_switches = 0
        self.frame_luma = -1.0
        self.frame_std = -1.0
        self.dark_pixel_ratio = -1.0
        self.black_frames = 0
        self.sampled_frames = 0
        self.black_streak = 0
        self.black_frame_ratio = 0.0
        self.source_state = "UNKNOWN"
        self._last_monitor_probe = 0.0
        self._capture_context = _capture_session_context()
        try:
            self.sct = mss.mss()
            if len(self.sct.monitors) < 2:
                raise RuntimeError("No Windows desktop monitor available")
            try:
                self.sct.with_cursor = True
            except Exception:
                pass
            # Do not blindly assume monitors[1] is the useful output. GitHub/VM
            # environments may expose more than one output, including blank ones.
            self._select_best_monitor(initial=True)
            if self.monitor is None:
                raise RuntimeError("No capturable Windows desktop monitor")
            self.capture_available = True
            LOG.info(
                "capture context session=%s activeConsole=%s winsta=%s desktop=%s monitor=%s",
                self._capture_context.get("processSession"),
                self._capture_context.get("activeConsoleSession"),
                self._capture_context.get("windowStation"),
                self._capture_context.get("desktopName"),
                self.monitor_index,
            )
        except Exception as exc:
            self.capture_error = f"{type(exc).__name__}: {exc}"
            self._test_pattern = True
            self.source_state = "PATTERN"
            LOG.warning("Desktop capture unavailable; diagnostic test pattern forced: %s", self.capture_error)
        # Keep the RTP/media timeline and frame pacing timeline separate.
        # The media clock is created exactly once for this track and MUST remain
        # monotonic for the whole PeerConnection. Profile/FPS changes may rebase
        # pacing, but they must never rewind frame.pts / RTP timestamps.
        now = time.monotonic()
        self._media_start = now
        self._pace_start = now
        self._pace_seq = 0
        self._last_pts = -1
        self._last_pts_wall = now
        self.pts_backwards = 0
        self.pts_discontinuities = 0
        self.profile_changes = 0
        self._profile = "high"
        self._width = TARGET_W
        self._height = TARGET_H
        self._fps = TARGET_FPS
        self.frames_generated = 0
        self.capture_errors = 0
        self.last_capture_error = ""

    @staticmethod
    def _frame_health(arr: np.ndarray) -> tuple[float, float, float, bool]:
        """Cheap sampled luma/variance check used only to detect truly blank sources."""
        if arr is None or arr.size == 0:
            return 0.0, 0.0, 1.0, True
        h, w = arr.shape[:2]
        sy = max(1, h // 90)
        sx = max(1, w // 160)
        sample = arr[::sy, ::sx, :3].astype(np.float32, copy=False)
        # MSS is BGRA. Weighted BT.601-ish luma is enough for blank-frame detection.
        luma = sample[..., 0] * 0.114 + sample[..., 1] * 0.587 + sample[..., 2] * 0.299
        mean = float(np.mean(luma))
        std = float(np.std(luma))
        dark = float(np.mean(luma < 8.0))
        black = mean < 3.0 and std < 2.0 and dark > 0.995
        return mean, std, dark, black

    def _select_best_monitor(self, initial: bool = False) -> None:
        if self.sct is None:
            return
        best = None
        for idx, mon in enumerate(self.sct.monitors[1:], start=1):
            try:
                arr = np.asarray(self.sct.grab(mon), dtype=np.uint8)
                mean, std, dark, black = self._frame_health(arr)
                # Prefer content/variance over a uniformly bright or black output.
                score = (std * 4.0) + mean + (0.0 if black else 25.0)
                LOG.info(
                    "capture monitor probe index=%d size=%sx%s luma=%.2f std=%.2f dark=%.3f black=%s score=%.2f",
                    idx, getattr(mon, "width", mon.get("width", "?")) if hasattr(mon, "get") else getattr(mon, "width", "?"),
                    getattr(mon, "height", mon.get("height", "?")) if hasattr(mon, "get") else getattr(mon, "height", "?"),
                    mean, std, dark, black, score,
                )
                if best is None or score > best[0]:
                    best = (score, idx, mon, mean, std, dark, black)
            except Exception as exc:
                LOG.warning("capture monitor probe failed index=%d: %s", idx, exc)
        if best is None:
            return
        _, idx, mon, mean, std, dark, black = best
        old_index = self.monitor_index
        self.monitor = mon
        self.monitor_index = idx
        self.frame_luma, self.frame_std, self.dark_pixel_ratio = mean, std, dark
        self.source_state = "BLACK" if black else "LIVE"
        if old_index > 0 and old_index != idx:
            self.monitor_switches += 1
            LOG.warning("capture monitor switched %d -> %d after blank-source probe", old_index, idx)
        elif initial:
            LOG.info("capture monitor selected index=%d source=%s", idx, self.source_state)
        self._last_monitor_probe = time.monotonic()

    def _update_capture_health(self, arr: np.ndarray) -> None:
        mean, std, dark, black = self._frame_health(arr)
        self.frame_luma, self.frame_std, self.dark_pixel_ratio = mean, std, dark
        self.sampled_frames += 1
        if black:
            self.black_frames += 1
            self.black_streak += 1
            self.source_state = "BLACK"
        else:
            self.black_streak = 0
            self.source_state = "LIVE"
        self.black_frame_ratio = self.black_frames / max(1, self.sampled_frames)
        now = time.monotonic()
        # If the chosen output stays truly black, re-probe all outputs. This fixes
        # the common VM case where monitor #1 exists but a different output is live.
        if self.black_streak >= 10 and now - self._last_monitor_probe >= 5.0:
            self._select_best_monitor(initial=False)

    @property
    def profile(self) -> tuple[str, int, int, int]:
        return self._profile, self._width, self._height, self._fps

    def set_test_pattern(self, enabled: bool) -> bool:
        self._test_pattern = bool(enabled) or not self.capture_available
        if self._test_pattern:
            self.source_state = "PATTERN"
        LOG.info("diagnostic test_pattern=%s capture_available=%s source=%s", self._test_pattern, self.capture_available, self.source_state)
        return self._test_pattern

    def set_profile(self, profile: str, width: int, height: int, fps: int) -> tuple[str, int, int, int]:
        profile = (profile or "adaptive").strip().lower()[:32]
        # Never exceed operator configured maximums. Keep even dimensions for YUV420/H264.
        width = max(320, min(TARGET_W, int(width or TARGET_W))) // 2 * 2
        height = max(180, min(TARGET_H, int(height or TARGET_H))) // 2 * 2
        fps = max(10, min(TARGET_FPS, int(fps or TARGET_FPS)))
        previous = (self._profile, self._width, self._height, self._fps)
        self._profile, self._width, self._height, self._fps = profile, width, height, fps
        # Rebase ONLY the pacing schedule, and only when the requested profile
        # actually changes. Duplicate control messages must not perturb pacing.
        # Never touch _media_start: changing FPS/quality inside one PeerConnection
        # must not rewind RTP timestamps.
        if previous != self.profile:
            self._pace_start = time.monotonic()
            self._pace_seq = 0
            self.profile_changes += 1
        LOG.info(
            "capture profile=%s %dx%d@%dfps profileChanges=%d mediaClockMs=%d lastPts=%d",
            profile, width, height, fps, self.profile_changes,
            int((time.monotonic() - self._media_start) * 1000), self._last_pts,
        )
        return self.profile

    def _pattern_frame(self, tw: int, th: int) -> av.VideoFrame:
        arr = np.zeros((th, tw, 3), dtype=np.uint8)
        colors = ((255,255,255),(0,255,255),(255,255,0),(0,255,0),(255,0,255),(0,0,255),(255,0,0))
        band = max(1, tw // len(colors))
        for i, color in enumerate(colors):
            arr[:, i*band:(i+1)*band, :] = color
        marker = int((self._pace_seq * 9) % max(1, tw))
        arr[:, max(0, marker-4):min(tw, marker+4), :] = (255,255,255)
        frame = av.VideoFrame.from_ndarray(arr, format="bgr24")
        return frame.reformat(width=max(2, tw), height=max(2, th), format="yuv420p")

    def metrics(self) -> dict[str, Any]:
        return {
            "profile": self._profile, "width": self._width, "height": self._height, "fps": self._fps,
            "framesGenerated": self.frames_generated, "captureErrors": self.capture_errors,
            "captureAvailable": self.capture_available, "captureError": self.last_capture_error or self.capture_error,
            "mediaClockMs": int((time.monotonic() - self._media_start) * 1000),
            "lastPts": int(self._last_pts), "ptsBackwards": int(self.pts_backwards),
            "ptsDiscontinuities": int(self.pts_discontinuities), "profileChanges": int(self.profile_changes),
            "captureBackend": self.capture_backend, "monitorIndex": int(self.monitor_index),
            "monitorSwitches": int(self.monitor_switches), "frameLuma": round(float(self.frame_luma), 2),
            "frameStd": round(float(self.frame_std), 2), "darkPixelRatio": round(float(self.dark_pixel_ratio), 4),
            "blackFrames": int(self.black_frames), "sampledFrames": int(self.sampled_frames),
            "blackStreak": int(self.black_streak), "blackFrameRatio": round(float(self.black_frame_ratio), 4),
            "sourceState": self.source_state,
            **self._capture_context,
        }

    async def recv(self) -> av.VideoFrame:
        fps = max(10, self._fps)
        interval = 1.0 / fps
        target = self._pace_start + self._pace_seq * interval
        now = time.monotonic()
        if target > now:
            await asyncio.sleep(target - now)
        # If capture/encode stalled, skip old frame times. Never queue obsolete desktop frames.
        now = time.monotonic()
        if now - target > interval * 2:
            self._pace_seq = int((now - self._pace_start) / interval)
        self._pace_seq += 1
        tw = self._width
        th = self._height
        if self._test_pattern or not self.capture_available or self.sct is None or self.monitor is None:
            # Network/codec/render isolation pattern. It keeps media alive even if
            # Windows desktop capture is the failing component.
            self.source_state = "PATTERN"
            frame = self._pattern_frame(tw, th)
        else:
            try:
                shot = self.sct.grab(self.monitor)
                arr = np.asarray(shot, dtype=np.uint8)
                # Sample source truth at ~4-5 Hz; never run expensive diagnostics on
                # every frame. A renderer can be healthy while the source is black.
                if self.frames_generated % max(4, int(max(10, self._fps) / 5)) == 0:
                    self._update_capture_health(arr)
                frame = av.VideoFrame.from_ndarray(arr, format="bgra")
                src_aspect = frame.width / max(1, frame.height)
                if abs((tw / th) - src_aspect) > 0.01:
                    if tw / th > src_aspect:
                        tw = int(th * src_aspect) // 2 * 2
                    else:
                        th = int(tw / src_aspect) // 2 * 2
                frame = frame.reformat(width=max(2, tw), height=max(2, th), format="yuv420p")
            except Exception as exc:
                # A transient MSS failure must not kill the WebRTC video track. Send
                # one diagnostic frame and retry real capture on the next recv().
                self.capture_errors += 1
                self.last_capture_error = f"{type(exc).__name__}: {exc}"[:160]
                if self.capture_errors <= 3 or self.capture_errors % 30 == 0:
                    LOG.warning("desktop capture transient failure #%d: %s", self.capture_errors, self.last_capture_error)
                frame = self._pattern_frame(tw, th)
        # Continuous 90 kHz media clock. Guard against any accidental regression
        # even if platform timer granularity produces an equal timestamp.
        pts_now_wall = time.monotonic()
        computed_pts = int((pts_now_wall - self._media_start) * 90000)
        if self._last_pts >= 0 and computed_pts <= self._last_pts:
            self.pts_backwards += 1
            computed_pts = self._last_pts + 1
        if self._last_pts >= 0:
            delta_pts = computed_pts - self._last_pts
            # Flag only large forward jumps (>1s). FPS/profile changes are expected
            # and should never count as discontinuities because media time is continuous.
            if delta_pts > 90000:
                self.pts_discontinuities += 1
        self._last_pts = computed_pts
        self._last_pts_wall = pts_now_wall
        frame.pts = computed_pts
        frame.time_base = fractions.Fraction(1, 90000)
        self.frames_generated += 1
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
            try:
                dev = self.pa.get_default_wasapi_loopback()
            except Exception as default_exc:
                dev = None
                # GitHub-hosted Windows can expose WASAPI endpoints in an unusual
                # order. If the default lookup fails, probe every loopback-capable
                # device before falling back to silence.
                generator = getattr(self.pa, "get_loopback_device_info_generator", None)
                if callable(generator):
                    try:
                        for candidate in generator():
                            if int(candidate.get("maxInputChannels", 0) or 0) > 0:
                                dev = candidate
                                break
                    except Exception:
                        dev = None
                if dev is None:
                    raise default_exc
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
        self.active_relay_transport = "auto"
        self.offer_task: Optional[asyncio.Task] = None
        self.offer_generation = 0
        self.pending_ice_by_session: dict[int, list[dict[str, Any]]] = {}

    @staticmethod
    def _relay_rank(url: str, preference: str) -> int:
        """Put the requested TURN transport first for aiortc.

        aiortc/aioice intentionally consumes one TURN URI per PeerConnection.
        Android libwebrtc can try the whole list, so on recovery Android tells the
        host which transport to prioritize: UDP, TLS/443, TCP/80, or TCP/3478.
        """
        u = url.lower()
        pref = (preference or "auto").lower()
        if not u.startswith(("turn:", "turns:")):
            return 100
        if pref == "udp" and u.startswith("turn:") and "transport=udp" in u:
            return 0
        if pref == "tls443" and u.startswith("turns:") and ":443" in u and "transport=tcp" in u:
            return 0
        if pref == "tcp80" and u.startswith("turn:") and ":80" in u and "transport=tcp" in u:
            return 0
        if pref == "tcp3478" and u.startswith("turn:") and ":3478" in u and "transport=tcp" in u:
            return 0
        # AUTO prefers UDP for the lowest latency, then TLS/443 as the most
        # firewall-friendly path, then the remaining TCP options.
        if pref == "auto":
            if u.startswith("turn:") and "transport=udp" in u:
                return 0
            if u.startswith("turns:") and ":443" in u:
                return 1
            if u.startswith("turn:") and ":80" in u and "transport=tcp" in u:
                return 2
            if u.startswith("turn:") and "transport=tcp" in u:
                return 3
        return 20

    @classmethod
    def _parse_ice_items(cls, items: Any, relay_preference: str = "auto") -> list[RTCIceServer]:
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
            for value in urls[:12]:
                u = str(value).strip()
                lower = u.lower()
                if lower.startswith(("stun:", "stuns:", "turn:", "turns:")) and len(u) <= 240:
                    clean.append(u)
            if not clean:
                continue
            # Preserve STUN ordering, but put the requested TURN transport first
            # inside each TURN credential object. Python's sort is stable.
            if any(x.lower().startswith(("turn:", "turns:")) for x in clean):
                clean = sorted(clean, key=lambda x: cls._relay_rank(x, relay_preference))
            servers.append(RTCIceServer(
                urls=clean,
                username=str(item.get("username", ""))[:256],
                credential=str(item.get("credential", ""))[:512],
            ))
        return servers

    def rtc_config(self, offered_ice: Any = None, offered_provider: str = "", offered_mode: str = "", relay_preference: str = "auto") -> RTCConfiguration:
        # The rtc-offer travels through the already verified/e2e signaling path.
        # It carries the exact short-lived ICE list Android is using, so both ends
        # share credentials while the host is still free to rotate TURN transport.
        self.active_relay_transport = (relay_preference or "auto")[:32]
        servers = self._parse_ice_items(offered_ice, self.active_relay_transport)
        if servers:
            self.active_ice_provider = (offered_provider or "android-session-ice")[:80]
            self.active_ice_mode = (offered_mode or "session-override")[:80]
        else:
            raw = os.environ.get("UUC_ICE_SERVERS_JSON", "").strip()
            if raw:
                try:
                    servers = self._parse_ice_items(json.loads(raw), self.active_relay_transport)
                except Exception as exc:
                    LOG.warning("UUC_ICE_SERVERS_JSON parse failed: %s", exc)
            self.active_ice_provider = os.environ.get("UUC_ICE_PROVIDER", "none")
            self.active_ice_mode = os.environ.get("UUC_ICE_MODE", "direct-only")

        schemes: list[str] = []
        for srv in servers:
            urls = srv.urls if isinstance(srv.urls, list) else [srv.urls]
            for u in urls:
                schemes.append(str(u).split(":", 1)[0].lower())
        LOG.info("ICE servers loaded provider=%s mode=%s relayTransport=%s count=%d stun=%d turn=%d sessionOverride=%s",
                 self.active_ice_provider, self.active_ice_mode, self.active_relay_transport, len(servers),
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

    async def new_pc(self, session_id: int, offered_ice: Any = None, offered_provider: str = "", offered_mode: str = "", relay_preference: str = "auto") -> RTCPeerConnection:
        # Close the previous PC before switching session id so late callbacks from
        # the old PC are tagged with the old generation and ignored by Android.
        await self.close_pc()
        self.session_id = session_id
        pc_session = session_id
        pc = RTCPeerConnection(self.rtc_config(offered_ice, offered_provider, offered_mode, relay_preference))
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
                            "audioAvailable": bool(self.audio and self.audio.available),
                            "captureErrors": int(self.video.capture_errors if self.video else 0),
                            **(self.video.metrics() if self.video is not None else {}),
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
                if channel.label == "input-reliable":
                    asyncio.create_task(self.telemetry_loop(pc_session, channel))
                asyncio.create_task(self.send({
                    "type": "desktop-state", "state": "diag-datachannel-open",
                    "desktopProtocol": 3, "sessionId": pc_session,
                    "channel": channel.label,
                    "captureAvailable": bool(self.video and self.video.capture_available),
                    "audioAvailable": bool(self.audio and self.audio.available),
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
                "relayTransport": self.active_relay_transport,
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
                "relayTransport": self.active_relay_transport,
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
            "balanced": (960, 540, 30),
            "high": (1280, 720, 30),
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
            "mediaClockMs": int((time.monotonic() - self.video._media_start) * 1000),
            "lastPts": int(self.video._last_pts), "ptsBackwards": int(self.video.pts_backwards),
            "ptsDiscontinuities": int(self.video.pts_discontinuities),
            "profileChanges": int(self.video.profile_changes),
            "reason": str(obj.get("reason", "adaptive"))[:80],
            "turnMode": self.active_ice_mode,
            "iceProvider": self.active_ice_provider,
            "relayTransport": self.active_relay_transport,
        })

    async def telemetry_loop(self, pc_session: int, channel) -> None:
        """Send low-rate media telemetry over the already-open reliable SCTP channel."""
        last_at = time.monotonic()
        last_frames = self.video.frames_generated if self.video is not None else 0
        last_bytes = -1
        while pc_session == self.session_id and self.pc is not None and getattr(channel, "readyState", "") == "open":
            await asyncio.sleep(2.0)
            if pc_session != self.session_id or self.pc is None or getattr(channel, "readyState", "") != "open":
                break
            now = time.monotonic()
            dt = max(0.001, now - last_at)
            video = self.video
            metrics = video.metrics() if video is not None else {}
            frames = int(metrics.get("framesGenerated", 0) or 0)
            capture_fps = max(0.0, (frames - last_frames) / dt)
            send_kbps = -1
            frames_encoded = -1
            try:
                report = await self.pc.getStats()
                current_bytes = -1
                for stat in report.values():
                    if getattr(stat, "type", "") != "outbound-rtp":
                        continue
                    if str(getattr(stat, "kind", getattr(stat, "mediaType", ""))).lower() != "video":
                        continue
                    current_bytes = int(getattr(stat, "bytesSent", -1) or -1)
                    frames_encoded = int(getattr(stat, "framesEncoded", -1) or -1)
                    break
                if current_bytes >= 0 and last_bytes >= 0 and current_bytes >= last_bytes:
                    send_kbps = int(round(((current_bytes - last_bytes) * 8.0) / (dt * 1000.0)))
                if current_bytes >= 0:
                    last_bytes = current_bytes
            except Exception as exc:
                LOG.debug("host telemetry stats unavailable: %s", exc)
            payload = {
                "type": "host-telemetry", "sessionId": pc_session,
                "captureFps": round(capture_fps, 1), "sendKbps": send_kbps,
                "framesGenerated": frames, "framesEncoded": frames_encoded,
                "captureErrors": int(metrics.get("captureErrors", 0) or 0),
                "profile": metrics.get("profile", "?"),
                "width": int(metrics.get("width", 0) or 0), "height": int(metrics.get("height", 0) or 0),
                "targetFps": int(metrics.get("fps", 0) or 0),
                "mediaClockMs": int(metrics.get("mediaClockMs", 0) or 0),
                "lastPts": int(metrics.get("lastPts", -1) or -1),
                "ptsBackwards": int(metrics.get("ptsBackwards", 0) or 0),
                "ptsDiscontinuities": int(metrics.get("ptsDiscontinuities", 0) or 0),
                "profileChanges": int(metrics.get("profileChanges", 0) or 0),
                "captureBackend": metrics.get("captureBackend", "?"),
                "monitorIndex": int(metrics.get("monitorIndex", -1)),
                "monitorSwitches": int(metrics.get("monitorSwitches", 0) or 0),
                "frameLuma": float(metrics.get("frameLuma", -1.0)),
                "frameStd": float(metrics.get("frameStd", -1.0)),
                "darkPixelRatio": float(metrics.get("darkPixelRatio", -1.0)),
                "blackFrames": int(metrics.get("blackFrames", 0) or 0),
                "sampledFrames": int(metrics.get("sampledFrames", 0) or 0),
                "blackStreak": int(metrics.get("blackStreak", 0) or 0),
                "blackFrameRatio": float(metrics.get("blackFrameRatio", 0.0)),
                "sourceState": metrics.get("sourceState", "UNKNOWN"),
                "processSession": int(metrics.get("processSession", -1)),
                "activeConsoleSession": int(metrics.get("activeConsoleSession", -1)),
                "windowStation": metrics.get("windowStation", "?"),
                "desktopName": metrics.get("desktopName", "?"),
                "audioAvailable": bool(self.audio and self.audio.available),
            }
            try:
                channel.send(json.dumps(payload, separators=(",", ":")))
            except Exception:
                break
            last_at, last_frames = now, frames

    async def _cancel_offer_task(self) -> None:
        task, self.offer_task = self.offer_task, None
        if task is not None and not task.done():
            task.cancel()
            try:
                await task
            except asyncio.CancelledError:
                pass
            except Exception as exc:
                LOG.debug("previous offer task ended during cancel: %s", exc)

    async def add_remote_ice(self, sid: int, ice: dict[str, Any]) -> None:
        # ICE may beat the async offer task by a few milliseconds. Queue only
        # future/current-session candidates; stale candidates are discarded.
        if sid and self.session_id and sid < self.session_id:
            return
        if self.pc is None or (sid and sid != self.session_id):
            if sid:
                self.pending_ice_by_session.setdefault(sid, []).append(ice)
                # Keep the map bounded; session ids are monotonically increasing.
                for old_sid in sorted(self.pending_ice_by_session)[:-4]:
                    self.pending_ice_by_session.pop(old_sid, None)
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

    async def _handle_offer(self, obj: dict[str, Any], offer_generation: int) -> None:
        sid = int(obj.get("sessionId", 0) or 0)
        pc: Optional[RTCPeerConnection] = None
        try:
            offered_ice = obj.get("iceServers")
            offered_provider = str(obj.get("iceProvider", ""))
            offered_mode = str(obj.get("iceMode", ""))
            relay_preference = str(obj.get("relayTransport", "auto"))
            pc = await self.new_pc(sid, offered_ice, offered_provider, offered_mode, relay_preference)
            if offer_generation != self.offer_generation or self.pc is not pc:
                return
            offer = RTCSessionDescription(sdp=str(obj.get("sdp", "")), type="offer")
            await pc.setRemoteDescription(offer)
            if offer_generation != self.offer_generation or self.pc is not pc:
                return
            pending = self.pending_ice_by_session.pop(sid, [])
            for ice in pending:
                if offer_generation != self.offer_generation or self.pc is not pc:
                    return
                await self.add_remote_ice(sid, ice)
            answer = await pc.createAnswer()
            if offer_generation != self.offer_generation or self.pc is not pc:
                return
            # aiortc gathers ICE here. This is the slow section that used to block
            # the websocket receive loop and create a stale-answer backlog.
            await pc.setLocalDescription(answer)
            if offer_generation != self.offer_generation or self.pc is not pc:
                LOG.info("dropping superseded answer session=%s generation=%s", sid, offer_generation)
                return
            types = sorted(set(parts[parts.index("typ") + 1]
                               for line in pc.localDescription.sdp.splitlines()
                               if line.startswith("a=candidate:") and " typ " in line
                               for parts in [line.split()] if "typ" in parts and parts.index("typ") + 1 < len(parts)))
            LOG.info("RTC answer local candidate types=%s session=%s", types, sid)
            await self.send({"type": "rtc-answer", "desktopProtocol": 3, "sessionId": sid, "sdp": pc.localDescription.sdp,
                             "candidateTypes": types, "turnMode": self.active_ice_mode, "iceProvider": self.active_ice_provider,
                             "relayTransport": self.active_relay_transport})
            await self.send({
                "type": "desktop-state", "state": "diag-answer-sent",
                "desktopProtocol": 3, "sessionId": sid,
                "captureAvailable": bool(self.video and self.video.capture_available),
                "captureError": "" if not self.video else self.video.capture_error[:160],
                "pattern": bool(self.video and self.video._test_pattern),
                **(self.video.metrics() if self.video is not None else {}),
                "candidateTypes": types,
                "turnMode": self.active_ice_mode,
                "iceProvider": self.active_ice_provider,
                "relayTransport": self.active_relay_transport,
                "audioAvailable": bool(self.audio and self.audio.available),
            })
            LOG.info("RTC answer sent session=%s (%d SDP bytes) capture=%s pattern=%s", sid, len(pc.localDescription.sdp), bool(self.video and self.video.capture_available), bool(self.video and self.video._test_pattern))
        except asyncio.CancelledError:
            LOG.info("RTC offer superseded/cancelled session=%s generation=%s", sid, offer_generation)
            raise

    async def _start_latest_offer(self, obj: dict[str, Any]) -> None:
        sid = int(obj.get("sessionId", 0) or 0)
        self.offer_generation += 1
        generation = self.offer_generation
        await self._cancel_offer_task()
        LOG.info("latest-offer-wins start session=%s generation=%s", sid, generation)
        self.offer_task = asyncio.create_task(self._handle_offer(obj, generation))

    async def handle(self, obj: dict[str, Any]) -> None:
        typ = obj.get("type")
        sid = int(obj.get("sessionId", 0) or 0)
        if typ == "rtc-offer":
            await self._start_latest_offer(obj)
        elif typ == "rtc-ice":
            ice = obj.get("ice")
            if isinstance(ice, dict):
                await self.add_remote_ice(sid, ice)
        elif typ == "rtc-restart":
            # Restart must invalidate any answer still gathering for the old session.
            self.offer_generation += 1
            await self._cancel_offer_task()
            if not sid or not self.session_id or sid >= self.session_id:
                await self.close_pc()
        elif typ == "desktop-control":
            if not sid or not self.session_id or sid == self.session_id:
                await self.apply_control(obj)

    async def client(self, ws) -> None:
        self.ws = ws
        LOG.info("Local relay agent connected to desktop IPC")
        await self.send({"type": "desktop-state", "state": "host-ready", "desktopProtocol": 3, "sessionId": self.session_id, "turnMode": self.active_ice_mode, "iceProvider": self.active_ice_provider, "relayTransport": self.active_relay_transport})
        try:
            async for raw in ws:
                try:
                    obj = json.loads(raw)
                    await self.handle(obj)
                except Exception as exc:
                    LOG.exception("desktop signal failed")
                    await self.send({"type": "desktop-error", "message": f"{type(exc).__name__}: {exc}"})
        finally:
            self.offer_generation += 1
            await self._cancel_offer_task()
            self.ws = None
            await self.close_pc()
            LOG.info("Local relay agent disconnected from desktop IPC")


async def main() -> None:
    host = DesktopHost()
    async with websockets.serve(host.client, HOST, PORT, max_size=4 * 1024 * 1024, ping_interval=10, ping_timeout=20):
        LOG.info("UUC v2.10.11 CAPTURE-TRUTH desktop IPC ready ws://%s:%d max=%dx%d@%dfps touch=%s", HOST, PORT, TARGET_W, TARGET_H, TARGET_FPS, _TOUCH_OK)
        await asyncio.Future()


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        pass
