# -*- coding: utf-8 -*-
"""
스마트클립 (SmartClip) - Windows용 클립보드 기록 관리자 · 스마트공 시리즈
================================================================
CopyQ 방식: 복사할 때 클립보드에 들어 있는 "모든 형식"을 원본 바이트
그대로 저장했다가 그대로 복원합니다. 그래서 한글 표, 엑셀 셀 서식,
워드 스타일, 이미지, 파일 복사까지 원래대로 다시 붙여넣을 수 있습니다.

[사용법]
  실행하면 기록 창이 바로 뜨고, 트레이에도 아이콘이 표시됩니다.
  창을 닫으면(X) 종료되지 않고 트레이로 숨겨집니다.
  Ctrl+Shift+V      숨겨져 있을 때 마우스 옆에 기록 창 띄우기 (HOTKEY 설정에서 변경 가능)
  Enter / 더블클릭   서식 그대로 붙여넣기
  Shift+Enter       텍스트만 붙여넣기 (서식 제거)
  Ctrl+Enter        붙여넣지 않고 클립보드에만 넣기
  Alt+Enter         호환 모드(HTML/RTF)로 붙여넣기 - 한글에는 기본으로 이 방식 사용
  Ctrl+Shift+Enter  원본 형식 그대로 붙여넣기
  F2                저장된 형식 정보 보기
  Ctrl+P            상단에 고정 / 고정 해제
  Ctrl+N            메모 바로 추가 (가리기를 켜면 비밀번호 등도 ●●●로 감춤)
  Ctrl+E            메모 고치기
  Ctrl+H            선택 항목 가리기 / 풀기 (붙여넣기는 그대로)
                    설정 → 기록 → '가린 항목 비밀번호'를 정하면 보거나 풀 때 비밀번호를 물음
  Ctrl+↑ / Ctrl+↓   고정 항목 순서 바꾸기
  Ctrl+D, Delete    선택 항목 삭제
  Ctrl+T            항상 위에 표시 켜기/끄기
  Ctrl+K            창 유지(붙여넣어도 닫히지 않음) 켜기/끄기
  Esc               검색어 지우기 → 한 번 더 누르면 트레이로 숨기기 (창 닫기 X와 같음)
  Ctrl+F            찾기 칸으로 이동 (본문 전체 검색, 띄어쓰기로 여러 단어 AND 검색)
  Ctrl+Q            프로그램 종료
  글자 입력          기록 검색
  마우스 오른쪽 클릭  메뉴

[보안] (행정기관 PC 사용 고려)
  - 기록·메모는 외부로 보내지 않음. 인터넷은 '새 버전 확인'(깃허브에 최신 버전 번호만 물어봄)에만 쓰며
    설정 → 기록 → '새 버전 확인'을 끄면 인터넷을 전혀 쓰지 않음
  - 기록은 Windows DPAPI로 암호화 저장 → 같은 PC·같은 Windows 계정에서만 열림
  - 주민등록번호·카드번호가 든 내용은 기록하지 않음 (기본값)
  - 자동 삭제(1/7/30일), 종료 시 삭제, 전체 삭제
  - 관리자 권한·설치 없이 사용자 폴더에서만 동작

[트레이 아이콘]  작업표시줄 오른쪽 아이콘
  왼쪽 클릭 = 창 열기/숨기기,  오른쪽 클릭 = 메뉴(항상 위, 창 유지, 일시정지, 종료)

[실행]   python smart_clipboard.py   (추가 설치 필요 없음, Python 3.8 이상)
[exe 빌드]
  pip install pyinstaller
  pyinstaller --onefile --noconsole --name SmartClip smart_clipboard.py

기록 저장 위치: %APPDATA%\\SmartClip\\clips.db
"""

import os
import sys
import time
import pickle
import sqlite3
import hashlib
import hmac
import queue
import threading
import re
import json
import base64
import html as html_lib
import math
import struct
import zlib
import webbrowser

if sys.platform != "win32":
    print("이 프로그램은 Windows에서만 동작합니다.")
    sys.exit(1)

import ctypes
from ctypes import wintypes as wt
import tkinter as tk
from tkinter import messagebox

# ─────────────────────────────────────────────────────────────
# 설정
# ─────────────────────────────────────────────────────────────
APP_NAME = "스마트클립"
APP_VERSION = "1.1.4"          # 배포할 때 여기만 올리면 깃허브가 자동으로 빌드·릴리스 (태그 smartclipboard-v버전)

MOD_ALT, MOD_CONTROL, MOD_SHIFT, MOD_WIN, MOD_NOREPEAT = 0x1, 0x2, 0x4, 0x8, 0x4000
HOTKEY_MODS = MOD_CONTROL | MOD_SHIFT      # 단축키 조합
HOTKEY_VK = ord("V")                        # 단축키 글자
HOTKEY_TEXT = "Ctrl+Shift+V"
# 업무 프로그램과 단축키가 겹칠 때 고를 수 있는 조합 (오른쪽 클릭 메뉴 → 단축키)
HOTKEY_CHOICES = {
    "Ctrl+Shift+V": (MOD_CONTROL | MOD_SHIFT, ord("V")),
    "Ctrl+Alt+V": (MOD_CONTROL | MOD_ALT, ord("V")),
    "Ctrl+Shift+Z": (MOD_CONTROL | MOD_SHIFT, ord("Z")),
    "Ctrl+Shift+Q": (MOD_CONTROL | MOD_SHIFT, ord("Q")),
    "Alt+Shift+V": (MOD_ALT | MOD_SHIFT, ord("V")),
}
WM_SET_HOTKEY = 0x8000 + 2
WM_SHOW_MAIN = 0x8000 + 3         # 이미 실행 중일 때 두 번째 실행이 보내는 "창 보여 줘" 신호

# Windows 시작 시 자동 실행 (현재 사용자 레지스트리 - 관리자 권한 불필요)
RUN_KEY = r"Software\Microsoft\Windows\CurrentVersion\Run"
RUN_NAME = "SmartClip"


def launch_command(tray=False):
    """자동 실행에 등록할 명령줄 (exe면 exe, 스크립트면 pythonw + 스크립트)."""
    if getattr(sys, "frozen", False):
        cmd = '"%s"' % sys.executable
    else:
        exe = sys.executable
        if os.path.basename(exe).lower() == "python.exe":       # 콘솔 창이 뜨지 않는 쪽으로
            for name in ("pythonw.exe",):
                cand = os.path.join(os.path.dirname(exe), name)
                if os.path.exists(cand):
                    exe = cand
                    break
        script = globals().get("__file__") or sys.argv[0]
        cmd = '"%s" "%s"' % (exe, os.path.abspath(script))
    return cmd + (" --tray" if tray else "")


def set_autostart(enable, tray=True):
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY, 0, winreg.KEY_SET_VALUE) as k:
            if enable:
                winreg.SetValueEx(k, RUN_NAME, 0, winreg.REG_SZ, launch_command(tray))
            else:
                try:
                    winreg.DeleteValue(k, RUN_NAME)
                except FileNotFoundError:
                    pass
        return True
    except Exception:
        return False


def remove_old_startup_shortcuts():
    """예전 배치파일이 시작프로그램 폴더에 만든 바로가기 정리 (두 번 실행되지 않게)."""
    folder = os.path.join(os.environ.get("APPDATA", ""), r"Microsoft\Windows\Start Menu\Programs\Startup")
    for name in ("스마트클립.lnk", "스마트 클립보드.lnk", "SmartClip.lnk"):
        try:
            os.remove(os.path.join(folder, name))
        except OSError:
            pass

MAX_ITEMS = 300                     # 고정 안 된 항목 최대 개수
MAX_FORMAT_BYTES = 32 * 1024 * 1024  # 형식 1개 최대 크기 (32MB)
MAX_ITEM_BYTES = 80 * 1024 * 1024    # 항목 1개 전체 최대 크기 (80MB)
DATA_DIR = os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), "SmartClip")
SETTINGS_FILE = os.path.join(DATA_DIR, "settings.json")

# 아이콘 (clip_icon.ico 내장)
ICON_ICO_B64 = (
    "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"
    "8D+x5Svqc2BSTAAAAABJRU5ErkJggg=="
)
ICON_PNG_B64 = (
    "iVBORw0KGgoAAAANSUhEUgAAABoAAAAaCAYAAACpSkzOAAAERUlEQVR4XqVWa2gcVRT+zn3MZjaPrqEWk7YpKjGxpSKoFMWS"
    "ovgu+VGJxYhP0P70h4gUn7Uliv7zj9RfPmgFEa1FsChioYVSadqoIbVGBBGrTWnJw+zO7p25R+6d2bjR7G6wHyyzOztzHt/5"
    "zjmXAIABIn8B+ODWPMx8bylK8mzJ31suSDCFmkp/RsFk1yNfzXt7DCICU/ULfzQkDZ9/jogejxNeB2ZddWCdO67jkwiCakOh"
    "WCn8ykTv6Yuzr9OOUeN9ML8sMPq5jH5u/6SlQ29N5mKY2KbpwVlgtGgJkiK1JrKrtf4nW4uokiw8697QSkC2K5SnK1/mCuEg"
    "7tlkfCzF/QM7w0IwUrxYLoNIEyBAAmxjaCkw+ssFnP59BpIYpWLROwjzIRIr0Le6AzdevRJxYkFCOc8uSAtmk+/M5UrT5pX8"
    "8OFdxO/f0RrJyoTWYk3ZWBeRD5njCCrXhtkoxrPvHsGFOYtACww/uQNCSuzb+zbK5QSFNsKbj21GZ2sAE82BVEuaKWADTTCG"
    "z4U27FeVlkovG6w2xqZUkwBMEera7QjWbwdP/QH94Ra0RRH6r+vHtieecfxh4tuj+OHkOIKcBt/6BnR3D/j0x0gm9gE6D2Ir"
    "jPEFuKIoKv0qMRwSkVyoNVtAhVDrHwJaVyEoaBTn/0KpBIyfGsen7+yGlBLfnRiDqTi5xtCFtUBrF9SGYSSTBwAbpwGDIYWz"
    "bkPlJEyyVjVO7BJkDZgZHSs68cBTIxg79jV0AJw6ccbzcv3Nt8MYYONNA7isc5V/lhKz4GARLLGq2yMkfAM4mgYf3uk/deHo"
    "8M2SKXIJ1HdUBRGckBe1Sg1cFYQPqDEaOEo7qXLkJdhzJwHVCqfaxSAgLkFcvhHBwEiqtTpompFcdxtEZx8gA98ji+AySQyo"
    "rSu7XT+zBo7Sl2TPlmasLAvNqTu6C3ZqDFD5JagTQFxMqdv86iVS173JU0OeurQGDAb5GSLAiYFoX9M0q+bUXXU3FrVZQ/yv"
    "GmWqO/Ya7PnvQSpMxUASXJmD6tsG1T8EsJvcEhCNw2mqOrFyA0jnM9VlKzKOQCuu9E7TDrukPkpfVr2DTdgS9ZdiDZRbv/+N"
    "KIvQUeUGpEdt1C4zkc216vat/r9EdoJJWUJEDCsAsbBVrclsi5SyZljwQfDv+pGUWkssMzNFqlXRZMnwWa1lt198JASSIszo"
    "W1DX3J+t7iWiXAT2Qol/+gyuftBeOFb7xWen8kr/6C1E+wdeyBWC3X6VgwIiIo5LWVTpXmku63Q8kcq7leE8V9wqj2bMnvDB"
    "wy/6w8nkF8d1z3TpYK4Q3BnPGZg4q8EC/8tAdYKzhZYE1a5Rnql8M6XK960duqv8z3Fr7w06LrQ9DxKPxrHtEdRguTSAZbZK"
    "0W8gfKDOtuyhpw+V/XHLB117gDxwSzug+0wk8k5vTRvtX9BalBDqM3TvodmMEH+A/Bsa1MDuPkmoDAAAAABJRU5ErkJggg=="
)


def icon_file():
    """내장된 아이콘을 %APPDATA%\\SmartClip\\clip_icon.ico 로 저장하고 경로를 돌려줌."""
    path = os.path.join(DATA_DIR, "clip_icon.ico")
    try:
        data = base64.b64decode("".join(ICON_ICO_B64))
        if not os.path.exists(path) or os.path.getsize(path) != len(data):
            os.makedirs(DATA_DIR, exist_ok=True)
            with open(path, "wb") as f:
                f.write(data)
        return path
    except Exception:
        return None

# ─────────────────────────────────────────────────────────────
# Win32 API 정의
# ─────────────────────────────────────────────────────────────
user32 = ctypes.WinDLL("user32", use_last_error=True)
kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
gdi32 = ctypes.WinDLL("gdi32", use_last_error=True)
shell32 = ctypes.WinDLL("shell32", use_last_error=True)

LRESULT = ctypes.c_ssize_t
WNDPROC = ctypes.WINFUNCTYPE(LRESULT, wt.HWND, wt.UINT, wt.WPARAM, wt.LPARAM)

WM_NULL = 0x0000
WM_DESTROY = 0x0002
WM_LBUTTONUP = 0x0202
WM_LBUTTONDBLCLK = 0x0203
WM_RBUTTONUP = 0x0205
WM_APP = 0x8000
WM_TRAY = WM_APP + 1
WM_TIMER = 0x0113
WM_HOTKEY = 0x0312
WM_CLIPBOARDUPDATE = 0x031D
WS_POPUP = 0x80000000
WS_EX_TOOLWINDOW = 0x00000080
NIM_ADD, NIM_MODIFY, NIM_DELETE = 0, 1, 2
NIF_MESSAGE, NIF_ICON, NIF_TIP = 0x1, 0x2, 0x4
MF_STRING, MF_CHECKED, MF_SEPARATOR = 0x0, 0x8, 0x800
TPM_RIGHTBUTTON, TPM_RETURNCMD = 0x2, 0x100
IDI_APPLICATION = 32512
GMEM_MOVEABLE = 0x0002
GA_ROOT = 2
PROCESS_QUERY_LIMITED_INFORMATION = 0x1000
ERROR_ALREADY_EXISTS = 183

CF_TEXT, CF_BITMAP, CF_METAFILEPICT = 1, 2, 3
CF_OEMTEXT, CF_DIB, CF_PALETTE = 7, 8, 9
CF_UNICODETEXT, CF_ENHMETAFILE, CF_HDROP, CF_LOCALE, CF_DIBV5 = 13, 14, 15, 16, 17

# 저장하지 않는 표준 형식 (GDI 핸들이거나 다른 형식에서 자동 생성됨)
SKIP_STD = {CF_BITMAP, CF_METAFILEPICT, CF_PALETTE, 0x0080, 0x0082, 0x0083, 0x008E}

# 저장하지 않는 등록 형식 (원본 프로그램/세션에 묶인 정보라 복원하면 오히려 문제가 됨)
SKIP_NAMES = {
    "DataObject", "OlePrivateData", "Ole Private Data",
    "Ole Clipboard Persist On Flush",
    "Link", "Link Source", "Link Source Descriptor", "ObjectLink", "OwnerLink",
}

# 이 표시가 있으면 기록하지 않음 (비밀번호 관리자 등)
EXCLUDE_NAMES = {"ExcludeClipboardContentFromMonitorProcessing", "Clipboard Viewer Ignore"}


class WNDCLASSW(ctypes.Structure):
    _fields_ = [
        ("style", wt.UINT), ("lpfnWndProc", WNDPROC),
        ("cbClsExtra", ctypes.c_int), ("cbWndExtra", ctypes.c_int),
        ("hInstance", wt.HINSTANCE), ("hIcon", wt.HICON), ("hCursor", wt.HANDLE),
        ("hbrBackground", wt.HBRUSH), ("lpszMenuName", wt.LPCWSTR), ("lpszClassName", wt.LPCWSTR),
    ]


class NOTIFYICONDATAW(ctypes.Structure):
    _fields_ = [
        ("cbSize", wt.DWORD), ("hWnd", wt.HWND), ("uID", wt.UINT), ("uFlags", wt.UINT),
        ("uCallbackMessage", wt.UINT), ("hIcon", wt.HICON), ("szTip", wt.WCHAR * 128),
        ("dwState", wt.DWORD), ("dwStateMask", wt.DWORD), ("szInfo", wt.WCHAR * 256),
        ("uTimeoutOrVersion", wt.UINT), ("szInfoTitle", wt.WCHAR * 64),
        ("dwInfoFlags", wt.DWORD), ("guidItem", ctypes.c_byte * 16), ("hBalloonIcon", wt.HICON),
    ]


class KEYBDINPUT(ctypes.Structure):
    _fields_ = [("wVk", wt.WORD), ("wScan", wt.WORD), ("dwFlags", wt.DWORD),
                ("time", wt.DWORD), ("dwExtraInfo", ctypes.c_size_t)]


class MOUSEINPUT(ctypes.Structure):
    _fields_ = [("dx", wt.LONG), ("dy", wt.LONG), ("mouseData", wt.DWORD),
                ("dwFlags", wt.DWORD), ("time", wt.DWORD), ("dwExtraInfo", ctypes.c_size_t)]


class HARDWAREINPUT(ctypes.Structure):
    _fields_ = [("uMsg", wt.DWORD), ("wParamL", wt.WORD), ("wParamH", wt.WORD)]


class _INPUTUNION(ctypes.Union):
    _fields_ = [("mi", MOUSEINPUT), ("ki", KEYBDINPUT), ("hi", HARDWAREINPUT)]


class INPUT(ctypes.Structure):
    _fields_ = [("type", wt.DWORD), ("u", _INPUTUNION)]


def _proto(dll, name, restype, *argtypes):
    f = getattr(dll, name)
    f.restype = restype
    f.argtypes = argtypes
    return f


# user32
_proto(user32, "RegisterClassW", wt.ATOM, ctypes.POINTER(WNDCLASSW))
_proto(user32, "CreateWindowExW", wt.HWND, wt.DWORD, wt.LPCWSTR, wt.LPCWSTR, wt.DWORD,
       ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int,
       wt.HWND, wt.HMENU, wt.HINSTANCE, wt.LPVOID)
_proto(user32, "DefWindowProcW", LRESULT, wt.HWND, wt.UINT, wt.WPARAM, wt.LPARAM)
_proto(user32, "GetMessageW", wt.BOOL, ctypes.POINTER(wt.MSG), wt.HWND, wt.UINT, wt.UINT)
_proto(user32, "TranslateMessage", wt.BOOL, ctypes.POINTER(wt.MSG))
_proto(user32, "DispatchMessageW", LRESULT, ctypes.POINTER(wt.MSG))
_proto(user32, "AddClipboardFormatListener", wt.BOOL, wt.HWND)
_proto(user32, "RegisterHotKey", wt.BOOL, wt.HWND, ctypes.c_int, wt.UINT, wt.UINT)
_proto(user32, "UnregisterHotKey", wt.BOOL, wt.HWND, ctypes.c_int)
_proto(user32, "SetTimer", ctypes.c_size_t, wt.HWND, ctypes.c_size_t, wt.UINT, wt.LPVOID)
_proto(user32, "KillTimer", wt.BOOL, wt.HWND, ctypes.c_size_t)
_proto(user32, "OpenClipboard", wt.BOOL, wt.HWND)
_proto(user32, "CloseClipboard", wt.BOOL)
_proto(user32, "EmptyClipboard", wt.BOOL)
_proto(user32, "EnumClipboardFormats", wt.UINT, wt.UINT)
_proto(user32, "GetClipboardData", wt.HANDLE, wt.UINT)
_proto(user32, "SetClipboardData", wt.HANDLE, wt.UINT, wt.HANDLE)
_proto(user32, "GetClipboardFormatNameW", ctypes.c_int, wt.UINT, wt.LPWSTR, ctypes.c_int)
_proto(user32, "RegisterClipboardFormatW", wt.UINT, wt.LPCWSTR)
_proto(user32, "GetClipboardSequenceNumber", wt.DWORD)
_proto(user32, "GetClipboardOwner", wt.HWND)
_proto(user32, "GetWindowThreadProcessId", wt.DWORD, wt.HWND, ctypes.POINTER(wt.DWORD))
_proto(user32, "GetForegroundWindow", wt.HWND)
_proto(user32, "SetForegroundWindow", wt.BOOL, wt.HWND)
_proto(user32, "GetAncestor", wt.HWND, wt.HWND, wt.UINT)
_proto(user32, "SendInput", wt.UINT, wt.UINT, ctypes.POINTER(INPUT), ctypes.c_int)
_proto(user32, "GetCursorPos", wt.BOOL, ctypes.POINTER(wt.POINT))
_proto(user32, "IsWindow", wt.BOOL, wt.HWND)
_proto(user32, "IsWindowVisible", wt.BOOL, wt.HWND)
_proto(user32, "PostMessageW", wt.BOOL, wt.HWND, wt.UINT, wt.WPARAM, wt.LPARAM)
_proto(user32, "FindWindowW", wt.HWND, wt.LPCWSTR, wt.LPCWSTR)
_proto(user32, "RegisterWindowMessageW", wt.UINT, wt.LPCWSTR)
_proto(user32, "CreatePopupMenu", wt.HMENU)
_proto(user32, "AppendMenuW", wt.BOOL, wt.HMENU, wt.UINT, ctypes.c_size_t, wt.LPCWSTR)
_proto(user32, "TrackPopupMenu", wt.BOOL, wt.HMENU, wt.UINT, ctypes.c_int, ctypes.c_int,
       ctypes.c_int, wt.HWND, wt.LPVOID)
_proto(user32, "DestroyMenu", wt.BOOL, wt.HMENU)
_proto(user32, "LoadIconW", wt.HICON, wt.HINSTANCE, wt.LPVOID)
_proto(user32, "LoadImageW", wt.HANDLE, wt.HINSTANCE, wt.LPCWSTR, wt.UINT, ctypes.c_int, ctypes.c_int, wt.UINT)
_proto(user32, "GetSystemMetrics", ctypes.c_int, ctypes.c_int)
IMAGE_ICON, LR_LOADFROMFILE, SM_CXSMICON, SM_CYSMICON = 1, 0x10, 49, 50

# shell32 (트레이 아이콘)
_proto(shell32, "Shell_NotifyIconW", wt.BOOL, wt.DWORD, ctypes.POINTER(NOTIFYICONDATAW))
_proto(shell32, "ExtractIconW", wt.HICON, wt.HINSTANCE, wt.LPCWSTR, wt.UINT)

# kernel32
_proto(kernel32, "GetModuleHandleW", wt.HMODULE, wt.LPCWSTR)
_proto(kernel32, "GlobalAlloc", wt.HANDLE, wt.UINT, ctypes.c_size_t)
_proto(kernel32, "GlobalLock", wt.LPVOID, wt.HANDLE)
_proto(kernel32, "GlobalUnlock", wt.BOOL, wt.HANDLE)
_proto(kernel32, "GlobalSize", ctypes.c_size_t, wt.HANDLE)
_proto(kernel32, "GlobalFree", wt.HANDLE, wt.HANDLE)
_proto(kernel32, "OpenProcess", wt.HANDLE, wt.DWORD, wt.BOOL, wt.DWORD)
_proto(kernel32, "QueryFullProcessImageNameW", wt.BOOL, wt.HANDLE, wt.DWORD, wt.LPWSTR,
       ctypes.POINTER(wt.DWORD))
_proto(kernel32, "CloseHandle", wt.BOOL, wt.HANDLE)
_proto(kernel32, "CreateMutexW", wt.HANDLE, wt.LPVOID, wt.BOOL, wt.LPCWSTR)

# gdi32 (엑셀/워드가 넣는 그림 형식 EMF)
_proto(gdi32, "GetEnhMetaFileBits", wt.UINT, wt.HANDLE, wt.UINT, wt.LPVOID)
_proto(gdi32, "SetEnhMetaFileBits", wt.HANDLE, wt.UINT, ctypes.c_char_p)


# ─────────────────────────────────────────────────────────────
# 클립보드 읽기 / 쓰기
# ─────────────────────────────────────────────────────────────
def open_clipboard(hwnd, tries=25):
    for _ in range(tries):
        if user32.OpenClipboard(hwnd):
            return True
        time.sleep(0.02)
    return False


def fmt_key(fmt):
    """형식 번호 → 저장용 이름. 등록 형식은 이름으로(세션마다 번호가 달라지므로), 표준 형식은 #번호."""
    if fmt >= 0xC000:
        buf = ctypes.create_unicode_buffer(256)
        if user32.GetClipboardFormatNameW(fmt, buf, 256):
            return buf.value
    return "#%d" % fmt


def fmt_id(key):
    if key.startswith("#"):
        return int(key[1:])
    return user32.RegisterClipboardFormatW(key)


def _read_hglobal(h, limit):
    size = kernel32.GlobalSize(h)
    if size == 0 or size > limit:
        return None
    p = kernel32.GlobalLock(h)
    if not p:
        return None
    try:
        return ctypes.string_at(p, size)
    finally:
        kernel32.GlobalUnlock(h)


BIG_TEXT_CHARS = 200000      # 이보다 긴 글(대략 100쪽 이상)은 "큰 복사"로 보고 글자만 기록할 수 있음


def read_clipboard(hwnd, honor_flags=True, max_format=MAX_FORMAT_BYTES, big_chars=BIG_TEXT_CHARS):
    """현재 클립보드의 형식들을 읽어 (formats, note) 로 돌려줌. 기록하지 않을 때는 (None, None).

    note: None(정상) / "big"(큰 복사라 글자만 기록) / "partial"(크기 제한으로 일부 형식 제외)

    한글·엑셀은 큰 내용을 복사하면 HTML·RTF 같은 형식을 누가 요청할 때에야 만듭니다.
    여기서 그런 형식을 요청하면 원래 프로그램이 수백 쪽을 변환하느라 멈추고,
    그동안 클립보드가 잡혀 있어 붙여넣기도 안 됩니다. 그래서 글자(텍스트)를 먼저 읽어
    아주 긴 내용이면 다른 형식은 요청하지 않습니다.
    """
    if not open_clipboard(hwnd):
        return None, None
    try:
        fmts = []
        f = 0
        while True:
            f = user32.EnumClipboardFormats(f)
            if f == 0:
                break
            fmts.append((f, fmt_key(f)))

        names = {k for _, k in fmts}
        max_item = max(MAX_ITEM_BYTES, max_format * 3)
        if honor_flags and names & EXCLUDE_NAMES:
            return None, None
        if honor_flags and "CanIncludeInClipboardHistory" in names:
            fid = user32.RegisterClipboardFormatW("CanIncludeInClipboardHistory")
            h = user32.GetClipboardData(fid)
            if h:
                b = _read_hglobal(h, 64)
                if b and len(b) >= 4 and int.from_bytes(b[:4], "little") == 0:
                    return None, None

        # 1) 글자(텍스트)부터 읽어서 큰 복사인지 확인
        pre = {}
        if CF_UNICODETEXT in {f for f, _ in fmts}:
            h = user32.GetClipboardData(CF_UNICODETEXT)
            text = _read_hglobal(h, max(max_format, 64 * 1024 * 1024)) if h else None
            if text:
                pre["#13"] = text
                if big_chars and len(text) // 2 > big_chars:
                    out = [("#13", text)]
                    if CF_LOCALE in {f for f, _ in fmts}:
                        hl = user32.GetClipboardData(CF_LOCALE)
                        loc = _read_hglobal(hl, 64) if hl else None
                        if loc:
                            out.append(("#16", loc))
                    return out, "big"

        # 2) 나머지 형식을 원래 순서대로
        out, total, skipped = [], 0, 0
        for f, key in fmts:
            if key in pre:
                total += len(pre[key])
                out.append((key, pre[key]))
                continue
            if f in SKIP_STD or 0x0200 <= f <= 0x03FF or key in SKIP_NAMES:
                continue
            if key == "CanIncludeInClipboardHistory":
                continue
            try:
                h = user32.GetClipboardData(f)
                if not h:
                    continue
                if f == CF_ENHMETAFILE:
                    size = gdi32.GetEnhMetaFileBits(h, 0, None)
                    if not size or size > max_format:
                        skipped += 1
                        continue
                    buf = ctypes.create_string_buffer(size)
                    gdi32.GetEnhMetaFileBits(h, size, buf)
                    data = buf.raw
                else:
                    if kernel32.GlobalSize(h) > max_format:
                        skipped += 1
                        continue
                    data = _read_hglobal(h, max_format)
                if not data:
                    continue
                if total + len(data) > max_item:
                    skipped += 1
                    continue
                total += len(data)
                out.append((key, data))
            except Exception:
                continue
        if not out:
            return None, None
        return out, ("partial" if skipped else None)
    finally:
        user32.CloseClipboard()


def write_clipboard(hwnd, formats):
    """저장해 둔 형식들을 원래 순서대로 클립보드에 다시 넣음."""
    if not open_clipboard(hwnd):
        return False
    ok = 0
    try:
        user32.EmptyClipboard()
        for key, data in formats:
            if not data:
                continue
            fid = fmt_id(key)
            if not fid:
                continue
            if fid == CF_ENHMETAFILE:
                hemf = gdi32.SetEnhMetaFileBits(len(data), data)
                if hemf and user32.SetClipboardData(fid, hemf):
                    ok += 1
                continue
            h = kernel32.GlobalAlloc(GMEM_MOVEABLE, len(data))
            if not h:
                continue
            p = kernel32.GlobalLock(h)
            if not p:
                kernel32.GlobalFree(h)
                continue
            ctypes.memmove(p, data, len(data))
            kernel32.GlobalUnlock(h)
            if user32.SetClipboardData(fid, h):
                ok += 1
            else:
                kernel32.GlobalFree(h)
    finally:
        user32.CloseClipboard()
    return ok > 0


def exe_of_hwnd(hwnd):
    if not hwnd:
        return ""
    pid = wt.DWORD()
    user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
    if not pid.value:
        return ""
    h = kernel32.OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, False, pid.value)
    if not h:
        return ""
    try:
        buf = ctypes.create_unicode_buffer(1024)
        n = wt.DWORD(1024)
        if kernel32.QueryFullProcessImageNameW(h, 0, buf, ctypes.byref(n)):
            return os.path.basename(buf.value)
    finally:
        kernel32.CloseHandle(h)
    return ""


# ─────────────────────────────────────────────────────────────
# 키보드 입력 (Ctrl+V 보내기)
# ─────────────────────────────────────────────────────────────
VK_SHIFT, VK_CONTROL, VK_MENU, VK_LWIN, VK_RWIN = 0x10, 0x11, 0x12, 0x5B, 0x5C
KEYEVENTF_KEYUP = 0x0002


def _key(vk, up=False):
    i = INPUT()
    i.type = 1
    i.u.ki = KEYBDINPUT(vk, 0, KEYEVENTF_KEYUP if up else 0, 0, 0)
    return i


def send_ctrl_v():
    # 키보드 상태는 읽지 않고, Shift만 떼어 준 뒤 Ctrl+V 입력 (Shift+Enter로 고른 경우 대비)
    seq = [_key(VK_SHIFT, True), _key(VK_CONTROL), _key(ord("V")), _key(ord("V"), True), _key(VK_CONTROL, True)]
    arr = (INPUT * len(seq))(*seq)
    user32.SendInput(len(seq), arr, ctypes.sizeof(INPUT))


# ─────────────────────────────────────────────────────────────
# 보안: 암호화 저장, 개인정보 감지
# ─────────────────────────────────────────────────────────────
crypt32 = ctypes.WinDLL("crypt32", use_last_error=True)


class DATA_BLOB(ctypes.Structure):
    _fields_ = [("cbData", wt.DWORD), ("pbData", ctypes.POINTER(ctypes.c_char))]


_proto(crypt32, "CryptProtectData", wt.BOOL, ctypes.POINTER(DATA_BLOB), wt.LPCWSTR, ctypes.POINTER(DATA_BLOB),
       wt.LPVOID, wt.LPVOID, wt.DWORD, ctypes.POINTER(DATA_BLOB))
_proto(crypt32, "CryptUnprotectData", wt.BOOL, ctypes.POINTER(DATA_BLOB), wt.LPVOID, ctypes.POINTER(DATA_BLOB),
       wt.LPVOID, wt.LPVOID, wt.DWORD, ctypes.POINTER(DATA_BLOB))
_proto(kernel32, "LocalFree", wt.HANDLE, wt.HANDLE)

CRYPTPROTECT_UI_FORBIDDEN = 0x1
_ENTROPY = b"SmartClip-v1"


def _blob(data):
    buf = ctypes.create_string_buffer(data, len(data))
    return DATA_BLOB(len(data), ctypes.cast(buf, ctypes.POINTER(ctypes.c_char))), buf


def protect(data):
    """Windows DPAPI 암호화: 현재 Windows 사용자 계정으로만 풀 수 있음 (다른 계정·다른 PC에서는 못 읽음)."""
    src, _k1 = _blob(data)
    ent, _k2 = _blob(_ENTROPY)
    out = DATA_BLOB()
    if not crypt32.CryptProtectData(ctypes.byref(src), "SmartClip", ctypes.byref(ent), None, None,
                                    CRYPTPROTECT_UI_FORBIDDEN, ctypes.byref(out)):
        raise OSError("암호화 실패 (%d)" % ctypes.get_last_error())
    try:
        return ctypes.string_at(out.pbData, out.cbData)
    finally:
        kernel32.LocalFree(ctypes.cast(out.pbData, wt.HANDLE))


def unprotect(data):
    src, _k1 = _blob(data)
    ent, _k2 = _blob(_ENTROPY)
    out = DATA_BLOB()
    if not crypt32.CryptUnprotectData(ctypes.byref(src), None, ctypes.byref(ent), None, None,
                                      CRYPTPROTECT_UI_FORBIDDEN, ctypes.byref(out)):
        raise OSError("복호화 실패 (%d)" % ctypes.get_last_error())
    try:
        return ctypes.string_at(out.pbData, out.cbData)
    finally:
        kernel32.LocalFree(ctypes.cast(out.pbData, wt.HANDLE))


# 주민등록번호·외국인등록번호 (생년월일 형식이 맞는 것만)
_RRN = re.compile(r"(?<!\d)(\d{2})(0[1-9]|1[0-2])(0[1-9]|[12]\d|3[01])\s?[-–]?\s?([1-8])\d{6}(?!\d)")
# 카드번호 (4-4-4-4, 숫자 검증)
_CARD = re.compile(r"(?<!\d)(\d{4})[- ]?(\d{4})[- ]?(\d{4})[- ]?(\d{4})(?!\d)")


def _luhn(num):
    total = 0
    for i, ch in enumerate(reversed(num)):
        d = int(ch)
        if i % 2:
            d *= 2
            if d > 9:
                d -= 9
        total += d
    return total % 10 == 0


def find_pii(text):
    """주민등록번호/카드번호가 있으면 그 종류 이름을 돌려줌 (없으면 빈 문자열)."""
    if not text:
        return ""
    if _RRN.search(text):
        return "주민등록번호"
    for m in _CARD.finditer(text):
        if _luhn("".join(m.groups())):
            return "카드번호"
    return ""


# ─────────────────────────────────────────────────────────────
# 클립보드 감시 스레드
# ─────────────────────────────────────────────────────────────
class ClipListener(threading.Thread):
    def __init__(self, q):
        super().__init__(daemon=True)
        self.q = q
        self.hwnd = None
        self.hotkey_ok = False
        self.ready = threading.Event()
        self.ignore_seq = -1
        self.paused = False
        self.menu_state = {"topmost": False, "keep_open": False}   # 트레이 메뉴 체크 표시용
        # 기록 제한 (설정 창에서 변경)
        self.honor_flags = True             # 프로그램이 "기록 금지" 표시한 내용은 건너뜀
        self.max_format = MAX_FORMAT_BYTES  # 형식 하나 최대 크기
        self.debounce_ms = 120              # 연속 복사 신호를 모으는 간격
        self.big_text_only = True           # 아주 긴 내용은 글자만 기록 (원래 프로그램이 멈추지 않게)
        self._pending_hotkey = None
        self._proc = WNDPROC(self._wndproc)   # GC 방지용 참조
        self._nid = None
        self._msg_taskbar = 0

    def run(self):
        hinst = kernel32.GetModuleHandleW(None)
        wc = WNDCLASSW()
        wc.lpfnWndProc = self._proc
        wc.hInstance = hinst
        wc.lpszClassName = "SmartClipListenerWnd"
        user32.RegisterClassW(ctypes.byref(wc))
        # 트레이 메뉴를 띄우려면 메시지 전용 창이 아닌 "숨겨진 일반 창"이 필요함
        self.hwnd = user32.CreateWindowExW(WS_EX_TOOLWINDOW, "SmartClipListenerWnd", "SmartClip",
                                           WS_POPUP, 0, 0, 0, 0, None, None, hinst, None)
        user32.AddClipboardFormatListener(self.hwnd)
        mods, vk = HOTKEY_CHOICES.get(HOTKEY_TEXT, (HOTKEY_MODS, HOTKEY_VK))
        self.hotkey_ok = bool(user32.RegisterHotKey(self.hwnd, 1, mods | MOD_NOREPEAT, vk))
        self._msg_taskbar = user32.RegisterWindowMessageW("TaskbarCreated")
        self.add_tray()
        self.ready.set()

        msg = wt.MSG()
        while user32.GetMessageW(ctypes.byref(msg), None, 0, 0) > 0:
            user32.TranslateMessage(ctypes.byref(msg))
            user32.DispatchMessageW(ctypes.byref(msg))

    def _wndproc(self, hwnd, msg, wp, lp):
        try:
            if msg == WM_CLIPBOARDUPDATE:
                # 엑셀 등은 짧은 시간에 여러 번 갱신하므로 120ms 모았다가 한 번만 읽음
                user32.SetTimer(hwnd, 1, self.debounce_ms, None)
                return 0
            if msg == WM_TIMER and wp == 1:
                user32.KillTimer(hwnd, 1)
                self._capture()
                return 0
            if msg == WM_HOTKEY:
                self.q.put(("hotkey", user32.GetForegroundWindow()))
                return 0
            if msg == WM_SHOW_MAIN:
                self.q.put(("tray_cmd", 1))
                return 0
            if msg == WM_SET_HOTKEY and self._pending_hotkey:
                mods, vk = self._pending_hotkey
                self._pending_hotkey = None
                user32.UnregisterHotKey(hwnd, 1)
                self.hotkey_ok = bool(user32.RegisterHotKey(hwnd, 1, mods | MOD_NOREPEAT, vk))
                self.q.put(("hotkey_set", self.hotkey_ok))
                return 0
            if msg == WM_TRAY:
                ev = lp & 0xFFFF
                if ev in (WM_LBUTTONUP, WM_LBUTTONDBLCLK):
                    self.q.put(("tray_toggle",))
                elif ev == WM_RBUTTONUP:
                    self._tray_menu()
                return 0
            if self._msg_taskbar and msg == self._msg_taskbar:
                self.add_tray()      # 탐색기가 재시작되면 아이콘 다시 등록
                return 0
        except Exception as e:
            self.q.put(("error", str(e)))
        return user32.DefWindowProcW(hwnd, msg, wp, lp)

    # ── 트레이 아이콘 ──
    def add_tray(self):
        nid = NOTIFYICONDATAW()
        nid.cbSize = ctypes.sizeof(NOTIFYICONDATAW)
        nid.hWnd = self.hwnd
        nid.uID = 1
        nid.uFlags = NIF_MESSAGE | NIF_ICON | NIF_TIP
        nid.uCallbackMessage = WM_TRAY
        icon = None
        path = icon_file()
        if path:
            icon = user32.LoadImageW(None, path, IMAGE_ICON, user32.GetSystemMetrics(SM_CXSMICON),
                                     user32.GetSystemMetrics(SM_CYSMICON), LR_LOADFROMFILE)
        if not icon:
            icon = shell32.ExtractIconW(kernel32.GetModuleHandleW(None), sys.executable, 0)
        if not icon or icon == 1:
            icon = user32.LoadIconW(None, ctypes.c_void_p(IDI_APPLICATION))
        nid.hIcon = icon
        nid.szTip = "%s (%s)" % (APP_NAME, HOTKEY_TEXT)
        self._nid = nid
        shell32.Shell_NotifyIconW(NIM_ADD, ctypes.byref(nid))

    def set_tray_tip(self, text):
        if self._nid:
            self._nid.szTip = text[:127]
            self._nid.uFlags = NIF_TIP
            shell32.Shell_NotifyIconW(NIM_MODIFY, ctypes.byref(self._nid))

    def remove_tray(self):
        if self._nid:
            shell32.Shell_NotifyIconW(NIM_DELETE, ctypes.byref(self._nid))
            self._nid = None

    def _tray_menu(self):
        m = user32.CreatePopupMenu()
        chk = lambda on: MF_STRING | (MF_CHECKED if on else 0)
        user32.AppendMenuW(m, MF_STRING, 1, "기록 창 열기\t" + HOTKEY_TEXT)
        user32.AppendMenuW(m, MF_SEPARATOR, 0, None)
        user32.AppendMenuW(m, chk(self.menu_state["topmost"]), 2, "항상 위에 표시")
        user32.AppendMenuW(m, chk(self.menu_state["keep_open"]), 3, "창 유지 (붙여넣어도 닫지 않음)")
        user32.AppendMenuW(m, chk(self.paused), 4, "기록 일시정지")
        user32.AppendMenuW(m, MF_SEPARATOR, 0, None)
        user32.AppendMenuW(m, MF_STRING, 9, "종료")
        pt = wt.POINT()
        user32.GetCursorPos(ctypes.byref(pt))
        user32.SetForegroundWindow(self.hwnd)
        cmd = user32.TrackPopupMenu(m, TPM_RIGHTBUTTON | TPM_RETURNCMD, pt.x, pt.y, 0, self.hwnd, None)
        user32.PostMessageW(self.hwnd, WM_NULL, 0, 0)
        user32.DestroyMenu(m)
        if cmd:
            self.q.put(("tray_cmd", cmd))

    def _capture(self):
        if self.paused:
            return
        if user32.GetClipboardSequenceNumber() == self.ignore_seq:
            return   # 내가 넣은 내용이면 무시
        exe = exe_of_hwnd(user32.GetClipboardOwner())
        formats, note = read_clipboard(self.hwnd, self.honor_flags, self.max_format,
                                       BIG_TEXT_CHARS if self.big_text_only else 0)
        if formats:
            self.q.put(("clip", formats, exe, note))

    def set_hotkey(self, mods, vk):
        self._pending_hotkey = (mods, vk)
        user32.PostMessageW(self.hwnd, WM_SET_HOTKEY, 0, 0)


# ─────────────────────────────────────────────────────────────
# 내용 분석 (미리보기, 종류, 출처)
# ─────────────────────────────────────────────────────────────
SOURCE_NAMES = {
    "excel.exe": "엑셀", "winword.exe": "워드", "powerpnt.exe": "파워포인트",
    "hwp.exe": "한글", "hword.exe": "한워드", "hcell.exe": "한셀", "hshow.exe": "한쇼",
    "chrome.exe": "크롬", "msedge.exe": "엣지", "whale.exe": "웨일", "firefox.exe": "파이어폭스",
    "explorer.exe": "탐색기", "notepad.exe": "메모장", "outlook.exe": "아웃룩",
}


def source_label(exe):
    if not exe:
        return "직접"
    low = exe.lower()
    if low in SOURCE_NAMES:
        return SOURCE_NAMES[low]
    if low.startswith("hwp"):
        return "한글"
    return os.path.splitext(exe)[0]


def get_text(d):
    if "#13" in d:
        return d["#13"].decode("utf-16-le", "ignore").split("\x00", 1)[0]
    if "#1" in d:
        raw = d["#1"].split(b"\x00", 1)[0]
        try:
            return raw.decode("mbcs")
        except Exception:
            return raw.decode("cp949", "ignore")
    return ""


def parse_hdrop(b):
    try:
        off = int.from_bytes(b[0:4], "little")
        wide = int.from_bytes(b[16:20], "little")
        s = b[off:].decode("utf-16-le", "ignore") if wide else b[off:].decode("mbcs", "ignore")
        return [p for p in s.split("\x00") if p]
    except Exception:
        return []


def dib_size(b):
    try:
        w = int.from_bytes(b[4:8], "little", signed=True)
        h = int.from_bytes(b[8:12], "little", signed=True)
        return abs(w), abs(h)
    except Exception:
        return 0, 0


def html_to_text(raw):
    try:
        s = raw.decode("utf-8", "ignore")
        i = s.lower().find("<html")
        if i < 0:
            i = s.lower().find("<!--startfragment")
        s = s[max(i, 0):]
        s = re.sub(r"(?is)<(script|style)[^>]*>.*?</\1>", " ", s)
        s = re.sub(r"(?i)<br\s*/?>|</p>|</tr>|</div>", "\n", s)
        s = re.sub(r"(?i)</t[dh]>", "\t", s)
        s = re.sub(r"<[^>]+>", "", s)
        return html_lib.unescape(s)
    except Exception:
        return ""


def full_text(formats):
    """미리보기 창에 보여 줄 본문 전체."""
    d = dict(formats)
    text = get_text(d)
    if text.strip():
        return text
    if "HTML Format" in d:
        return html_to_text(d["HTML Format"]).strip()
    if "#15" in d:
        return "\n".join(parse_hdrop(d["#15"]))
    return ""


def analyze(formats, exe):
    d = dict(formats)
    text = get_text(d)
    html = d.get("HTML Format", b"")
    has_table = b"<table" in html.lower()
    lines = text.strip("\r\n").split("\n") if text else []
    tabbed = bool(text) and "\t" in text
    has_img = any(k in d for k in ("#8", "#17", "PNG", "#14"))

    if has_table or (tabbed and len(lines) >= 1 and exe.lower() in ("excel.exe", "hcell.exe")) \
            or (tabbed and len(lines) > 1):
        kind = "표"
    elif "#15" in d:
        kind = "파일"
    elif has_img and not text.strip():
        kind = "이미지"
    elif "Rich Text Format" in d or html or any("hwp" in k.lower() for k in d):
        kind = "서식"
    elif text:
        kind = "텍스트"
    else:
        kind = "기타"

    if kind == "표" and lines:
        cols = max(l.count("\t") + 1 for l in lines)
        first = " | ".join(c.strip() for c in lines[0].rstrip("\r").split("\t"))
        preview = "%d행×%d열 · %s" % (len(lines), cols, first)
    elif kind == "파일":
        files = parse_hdrop(d["#15"])
        names = [os.path.basename(p) or p for p in files]
        preview = ("%d개: " % len(names) if len(names) > 1 else "") + ", ".join(names)
    elif kind == "이미지":
        img = d.get("#8") or d.get("#17")
        w, h = dib_size(img) if img else (0, 0)
        preview = "그림 %d×%d" % (w, h) if w else "그림"
    else:
        preview = re.sub(r"\s+", " ", text).strip() or "(%d개 형식)" % len(d)

    preview = preview[:200]
    # 검색용 본문: 텍스트 전체 (+ 텍스트가 없으면 HTML에서 뽑은 글자, 파일 이름)
    body = text
    if not body.strip() and html:
        body = html_to_text(html)
    extra = [preview, source_label(exe), kind]
    if "#15" in d:
        extra += parse_hdrop(d["#15"])
    search = (body + "\n" + " ".join(extra)).lower()

    hasher = hashlib.sha1()
    key_parts = [k for k in ("#13", "#8", "#17", "PNG", "#15") if k in d]
    if key_parts:
        for k in key_parts:
            hasher.update(k.encode())
            hasher.update(d[k])
    else:
        for k, v in formats:
            hasher.update(k.encode())
            hasher.update(v)
    size = sum(len(v) for _, v in formats)
    return kind, preview, search, hasher.hexdigest(), size


# ─────────────────────────────────────────────────────────────
# 저장소 (SQLite)
# ─────────────────────────────────────────────────────────────
class Store:
    """기록 저장소 (SQLite).

    보안:
    - 내용(클립보드 원본, 미리보기, 검색용 본문)은 모두 Windows DPAPI로 암호화해 저장합니다.
      → 같은 PC의 같은 Windows 계정으로 로그인했을 때만 풀 수 있고,
        DB 파일을 복사해 가거나 다른 계정으로는 내용을 볼 수 없습니다.
    - 지운 기록이 파일에 남지 않도록 secure_delete를 켭니다.
    - 중복 확인용 해시도 비밀 키(HMAC)를 섞어 내용 추측이 불가능하게 합니다.
    """

    def __init__(self, folder):
        os.makedirs(folder, exist_ok=True)
        self.path = os.path.join(folder, "clips.db")
        self.db = sqlite3.connect(self.path)
        self.db.execute("PRAGMA secure_delete = ON")
        self.db.execute("""CREATE TABLE IF NOT EXISTS items(
            id INTEGER PRIMARY KEY AUTOINCREMENT, ts REAL, pinned INTEGER DEFAULT 0,
            source TEXT, kind TEXT, preview TEXT, search TEXT, keyhash TEXT,
            size INTEGER, data BLOB)""")
        self.db.execute("CREATE TABLE IF NOT EXISTS meta(k TEXT PRIMARY KEY, v BLOB)")
        self.db.execute("CREATE INDEX IF NOT EXISTS ix_key ON items(keyhash)")
        cols = [r[1] for r in self.db.execute("PRAGMA table_info(items)")]
        if "pin_order" not in cols:      # 이전 버전 DB 업그레이드
            self.db.execute("ALTER TABLE items ADD COLUMN pin_order REAL DEFAULT 0")
        if "enc" not in cols:
            self.db.execute("ALTER TABLE items ADD COLUMN enc INTEGER DEFAULT 0")
            self.db.execute("ALTER TABLE items ADD COLUMN meta BLOB")
        if "hidden" not in cols:         # 가리기(비밀번호 등) 표시
            self.db.execute("ALTER TABLE items ADD COLUMN hidden INTEGER DEFAULT 0")
        self.db.commit()
        self.max_items = MAX_ITEMS
        self.cache = {}                  # id → (preview, search) 복호화한 값 (메모리에만 보관)
        self.key = self._load_key()

        ver = self.db.execute("PRAGMA user_version").fetchone()[0]
        if ver < 3:
            self._encrypt_old_rows()     # 예전 버전에서 암호화 없이 저장된 기록을 암호화
            self.db.execute("PRAGMA user_version = 3")
            self.db.commit()
            self.db.execute("VACUUM")    # 암호화 전 내용이 파일에 남지 않게 정리

    # ── 암호화 도우미 ──
    def _load_key(self):
        row = self.db.execute("SELECT v FROM meta WHERE k='hkey'").fetchone()
        if row:
            try:
                return unprotect(row[0])
            except OSError:
                pass
        key = os.urandom(32)
        self.db.execute("INSERT OR REPLACE INTO meta(k, v) VALUES('hkey', ?)", (protect(key),))
        self.db.commit()
        return key

    def _hkey(self, keyhash):
        return hmac.new(self.key, keyhash.encode(), hashlib.sha256).hexdigest()

    def _seal(self, formats, preview, search):
        data = protect(pickle.dumps(formats, protocol=pickle.HIGHEST_PROTOCOL))
        meta = protect(pickle.dumps((preview, search), protocol=pickle.HIGHEST_PROTOCOL))
        return data, meta

    def _encrypt_old_rows(self):
        rows = self.db.execute("SELECT id, source, data FROM items WHERE enc=0 OR enc IS NULL").fetchall()
        for iid, source, data in rows:
            try:
                formats = pickle.loads(data)
                kind, preview, search, keyhash, _ = analyze(formats, source or "")
                d, m = self._seal(formats, preview, search)
                self.db.execute("UPDATE items SET kind=?, preview='', search='', keyhash=?, data=?, meta=?, enc=1 "
                                "WHERE id=?", (kind, self._hkey(keyhash), d, m, iid))
            except Exception:
                self.db.execute("DELETE FROM items WHERE id=?", (iid,))
        self.db.commit()

    def _meta(self, iid, enc, preview, search, meta):
        if not enc:
            return preview or "", search or ""
        if iid not in self.cache:
            try:
                self.cache[iid] = pickle.loads(unprotect(meta))
            except Exception:
                self.cache[iid] = None   # 다른 계정/PC에서 만든 기록 → 읽을 수 없음
        return self.cache[iid]

    # ── 조회 ──
    def file_size(self):
        try:
            return os.path.getsize(self.path)
        except OSError:
            return 0

    def list(self):
        # 고정 항목은 사용자가 정한 순서로 맨 위, 나머지는 최근 순
        cur = self.db.execute("SELECT id, ts, pinned, source, kind, size, keyhash, enc, preview, search, meta, "
                              "hidden FROM items ORDER BY pinned DESC, "
                              "CASE WHEN pinned=1 THEN pin_order END ASC, ts DESC")
        out = []
        for iid, ts, pinned, source, kind, size, kh, enc, preview, search, meta, hidden in cur.fetchall():
            pm = self._meta(iid, enc, preview, search, meta)
            if pm is None:
                continue
            out.append({"id": iid, "ts": ts, "pinned": pinned, "source": source, "kind": kind,
                        "preview": pm[0], "search": pm[1], "size": size, "keyhash": kh,
                        "hidden": bool(hidden), "title": pm[2] if len(pm) > 2 else ""})
        return out

    def formats(self, item_id):
        row = self.db.execute("SELECT data, enc FROM items WHERE id=?", (item_id,)).fetchone()
        if not row:
            return []
        data, enc = row
        try:
            return pickle.loads(unprotect(data) if enc else data)
        except Exception:
            return []

    # ── 추가/변경 ──
    def add(self, formats, source, kind, preview, search, keyhash, size):
        d, m = self._seal(formats, preview, search)
        hk = self._hkey(keyhash)
        row = self.db.execute("SELECT id FROM items WHERE keyhash=?", (hk,)).fetchone()
        if row:
            self.db.execute("UPDATE items SET ts=?, source=?, kind=?, preview='', search='', size=?, data=?, "
                            "meta=?, enc=1 WHERE id=?", (time.time(), source, kind, size, d, m, row[0]))
            self.cache[row[0]] = (preview, search)
        else:
            cur = self.db.execute("INSERT INTO items(ts, pinned, source, kind, preview, search, keyhash, size, "
                                  "data, meta, enc) VALUES(?,0,?,?,'','',?,?,?,?,1)",
                                  (time.time(), source, kind, hk, size, d, m))
            self.cache[cur.lastrowid] = (preview, search)
        self.trim()

    def trim(self):
        self.db.execute("DELETE FROM items WHERE pinned=0 AND id NOT IN "
                        "(SELECT id FROM items WHERE pinned=0 ORDER BY ts DESC LIMIT ?)", (self.max_items,))
        self.db.commit()

    def purge_older(self, days):
        """고정하지 않은 기록 중 days일 지난 것 삭제. 지운 개수를 돌려줌."""
        if not days:
            return 0
        cur = self.db.execute("DELETE FROM items WHERE pinned=0 AND ts < ?", (time.time() - days * 86400,))
        self.db.commit()
        return cur.rowcount

    def touch(self, item_id):
        self.db.execute("UPDATE items SET ts=? WHERE id=?", (time.time(), item_id))
        self.db.commit()

    def toggle_pin(self, item_id):
        row = self.db.execute("SELECT pinned FROM items WHERE id=?", (item_id,)).fetchone()
        if not row:
            return
        if row[0]:
            self.db.execute("UPDATE items SET pinned=0 WHERE id=?", (item_id,))
        else:
            # 새로 고정한 항목은 고정 목록의 맨 위로
            top = self.db.execute("SELECT MIN(pin_order) FROM items WHERE pinned=1").fetchone()[0]
            order = (top if top is not None else 0) - 1
            self.db.execute("UPDATE items SET pinned=1, pin_order=? WHERE id=?", (order, item_id))
        self.db.commit()

    def move_pin(self, item_id, direction):
        """고정 항목을 위(-1)/아래(+1)로 한 칸 이동."""
        rows = self.db.execute("SELECT id FROM items WHERE pinned=1 ORDER BY pin_order ASC, ts DESC").fetchall()
        ids = [r[0] for r in rows]
        if item_id not in ids:
            return False
        i = ids.index(item_id)
        j = i + direction
        if not 0 <= j < len(ids):
            return False
        ids[i], ids[j] = ids[j], ids[i]
        for n, iid in enumerate(ids):
            self.db.execute("UPDATE items SET pin_order=? WHERE id=?", (n, iid))
        self.db.commit()
        return True

    # ── 메모 · 가리기 ──
    @staticmethod
    def _memo_parts(text, title):
        formats = [("#13", (text + "\x00").encode("utf-16-le"))]
        first = re.sub(r"\s+", " ", text).strip()
        preview = (title or first or "(빈 메모)")[:200]
        search = (text + "\n" + title + " 메모").lower()
        return formats, preview, search

    def _seal_memo(self, formats, preview, search, title):
        data = protect(pickle.dumps(formats, protocol=pickle.HIGHEST_PROTOCOL))
        meta = protect(pickle.dumps((preview, search, title), protocol=pickle.HIGHEST_PROTOCOL))
        return data, meta

    def add_memo(self, text, title="", hidden=False):
        """직접 적은 메모 → 고정 목록 맨 위에 추가 (기록 개수 제한으로 지워지지 않음)"""
        formats, preview, search = self._memo_parts(text, title)
        d, m = self._seal_memo(formats, preview, search, title)
        top = self.db.execute("SELECT MIN(pin_order) FROM items WHERE pinned=1").fetchone()[0]
        order = (top if top is not None else 0) - 1
        cur = self.db.execute("INSERT INTO items(ts, pinned, pin_order, source, kind, preview, search, keyhash, "
                              "size, data, meta, enc, hidden) VALUES(?,1,?,'',?,'','',?,?,?,?,1,?)",
                              (time.time(), order, "메모", self._hkey("memo:" + os.urandom(16).hex()),
                               len(formats[0][1]), d, m, 1 if hidden else 0))
        self.db.commit()
        self.cache[cur.lastrowid] = (preview, search, title)
        return cur.lastrowid

    def update_memo(self, item_id, text, title="", hidden=False):
        formats, preview, search = self._memo_parts(text, title)
        d, m = self._seal_memo(formats, preview, search, title)
        self.db.execute("UPDATE items SET data=?, meta=?, size=?, hidden=?, enc=1 WHERE id=?",
                        (d, m, len(formats[0][1]), 1 if hidden else 0, item_id))
        self.db.commit()
        self.cache[item_id] = (preview, search, title)

    # ── 가린 항목 비밀번호 (PBKDF2 해시만 저장, 원래 비밀번호는 어디에도 남지 않음) ──
    PW_ROUNDS = 200000

    def _lock_rec(self):
        row = self.db.execute("SELECT v FROM meta WHERE k='lockpw'").fetchone()
        if not row:
            return None
        try:
            return pickle.loads(unprotect(row[0]))
        except Exception:
            return None

    def has_password(self):
        return self._lock_rec() is not None

    def set_password(self, pw):
        """pw가 None이면 비밀번호 없앰"""
        if pw is None:
            self.db.execute("DELETE FROM meta WHERE k='lockpw'")
        else:
            salt = os.urandom(16)
            h = hashlib.pbkdf2_hmac("sha256", pw.encode("utf-8"), salt, self.PW_ROUNDS)
            rec = protect(pickle.dumps({"salt": salt, "hash": h, "rounds": self.PW_ROUNDS}))
            self.db.execute("INSERT OR REPLACE INTO meta(k, v) VALUES('lockpw', ?)", (rec,))
        self.db.commit()

    def check_password(self, pw):
        rec = self._lock_rec()
        if rec is None:
            return True
        h = hashlib.pbkdf2_hmac("sha256", (pw or "").encode("utf-8"), rec["salt"], rec["rounds"])
        return hmac.compare_digest(h, rec["hash"])

    def delete_hidden(self):
        """비밀번호를 잊었을 때: 가린 항목을 모두 지우고 비밀번호도 없앰"""
        n = self.db.execute("DELETE FROM items WHERE hidden=1").rowcount
        self.db.execute("DELETE FROM meta WHERE k='lockpw'")
        self.db.commit()
        self.db.execute("VACUUM")
        self.cache.clear()
        return n

    def set_hidden(self, item_id, hidden):
        self.db.execute("UPDATE items SET hidden=? WHERE id=?", (1 if hidden else 0, item_id))
        self.db.commit()

    def delete(self, item_id):
        self.db.execute("DELETE FROM items WHERE id=?", (item_id,))
        self.db.commit()
        self.cache.pop(item_id, None)

    def clear_unpinned(self):
        self.db.execute("DELETE FROM items WHERE pinned=0")
        self.db.commit()
        self.db.execute("VACUUM")

    def clear_all(self):
        self.db.execute("DELETE FROM items")
        self.db.commit()
        self.db.execute("VACUUM")
        self.cache.clear()


# ─────────────────────────────────────────────────────────────
# 화면 (tkinter)
# ─────────────────────────────────────────────────────────────
from tkinter import ttk

# 아이콘 색상 기반 테마
C_ORANGE = "#FFD699"      # 머리 띠 (아이콘 주황을 연하게)
C_ORANGE_DK = "#F4B862"   # 테두리/마우스 올림
C_ORANGE_LT = "#FFEDD3"   # 구분 제목 줄
C_CREAM = "#FFF9EF"       # 고정 항목 배경
C_SELECT = "#FFE6BF"      # 선택 줄
C_BROWN = "#5C3D00"       # 클립 고리 색 (글자)
C_BROWN_LT = "#8A6A3A"    # 보조 글자
C_LINE = "#F2E2C8"        # 테두리
C_BG = "#FFFBF4"          # 창 바탕
C_WHITE = "#FFFFFF"
C_HILITE = "#FFD27F"      # 검색어 강조
C_STAR_ON = "#F29A12"     # 고정된 별 (진하게)
C_STAR_OFF = "#EADFCB"    # 고정 안 된 별 (희미하게)
C_STAR_HOVER = "#E3B66A"  # 별 위에 마우스

KIND_COLORS = {"표": "#2E7D32", "서식": "#1565C0", "이미지": "#8E44AD", "메모": "#00838F",
               "파일": "#B5651D", "텍스트": C_BROWN, "기타": "#888888"}
FONT = ("맑은 고딕", 10)
FONT_SMALL = ("맑은 고딕", 9)
FONT_BOLD = ("맑은 고딕", 10, "bold")
FONT_TITLE = ("맑은 고딕", 12, "bold")

LIMIT_CHOICES = (100, 300, 500, 1000, 3000)
SERIES_TEXT = "스마트공"
CONTACT_EMAIL = "smartgongmaster@gmail.com"   # 오류·개선 제안 받는 주소
GITHUB_REPO = "nunco-git/ezgong"              # 새 버전 확인 (깃허브 릴리스)
RELEASE_TAG_PREFIX = "smartclipboard-v"
DOWNLOAD_URL = "https://smartgong.kr/download/smart-clipboard"   # 항상 최신 버전 exe
UPDATE_CHECK_HOURS = 12


def ver_tuple(v):
    nums = re.findall(r"\d+", str(v))[:4]
    return tuple(int(n) for n in nums) + (0,) * (4 - len(nums))
SERIES_URL = "https://smartgong.kr"

# 작업표시줄/트레이 창은 붙여넣을 대상에서 제외
SHELL_CLASSES = {"Shell_TrayWnd", "Shell_SecondaryTrayWnd", "NotifyIconOverflowWindow",
                 "TopLevelWindowForOverflowXamlIsland", "Progman", "WorkerW"}

_proto(user32, "GetClassNameW", ctypes.c_int, wt.HWND, wt.LPWSTR, ctypes.c_int)


def window_class(hwnd):
    buf = ctypes.create_unicode_buffer(256)
    user32.GetClassNameW(hwnd, buf, 256)
    return buf.value


def is_own_window(hwnd):
    pid = wt.DWORD()
    user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
    return pid.value == os.getpid()


# 호환 모드: 어느 프로그램이나 읽을 수 있는 공통 형식만 사용 (프로그램 전용·OLE 형식 제외)
COMPAT_KEYS = {
    "HTML Format", "Rich Text Format", "PNG",
    "#13", "#1", "#7", "#16",      # 텍스트, 로캘
    "#8", "#17", "#14",            # 그림(DIB, DIBV5, EMF)
    "#15", "FileNameW", "FileName",  # 파일 복사
}
STD_FORMAT_NAMES = {
    "#1": "CF_TEXT (텍스트)", "#7": "CF_OEMTEXT (텍스트)", "#8": "CF_DIB (그림)",
    "#13": "CF_UNICODETEXT (텍스트)", "#14": "CF_ENHMETAFILE (그림 EMF)",
    "#15": "CF_HDROP (파일)", "#16": "CF_LOCALE (언어)", "#17": "CF_DIBV5 (그림)",
}


def compat_formats(formats):
    return [(k, v) for k, v in formats if k in COMPAT_KEYS]


def is_hwp_exe(exe):
    return (exe or "").lower().startswith("hwp")


def load_settings():
    try:
        with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def save_settings(data):
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception:
        pass


def human_size(n):
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            return ("%d %s" % (n, unit)) if unit == "B" else ("%.1f %s" % (n, unit))
        n /= 1024.0


def short_time(ts):
    lt = time.localtime(ts)
    now = time.localtime()
    if lt.tm_year == now.tm_year and lt.tm_yday == now.tm_yday:
        return time.strftime("%H:%M", lt)
    if lt.tm_year == now.tm_year:
        return time.strftime("%m/%d", lt)
    return time.strftime("%y/%m/%d", lt)


# 버튼 그림 (18px PNG, 이모지 대신 사용 - 어느 PC에서나 같게 보임)
ICONS = {
    "trash_b": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAACoUlEQVR4Xq2UMWhUQRCGv9l97y5n1IjBWIiiIohnJRqstBAECxuLqGgKsUhnoXY2XkCwsdBO7AIBhVeJFlZRUUQES08UFDEx0VOiJuZyufd2R97eGe5CSqd47LC73878M/PgP5l0coaGsMv+JIVizHlr2Og8agyumTK2+yhfq9XWvSTBA5qvu0Cddu4wg3GBV861TpYKMFfnyvgzrq+WRAApyMkycaGfm7FlX5aRIvQboezDe2AMOM8XgY8GIhVm04yRey+YzgOK8k9OG1qPFWUvyk4VekVRB7V/r+eRAb0IBxQWBObiiD5g+urVFkhzbZKExTOHqajhuDoei0FEKajHG4vksedrEZrWMLiUUbv7nLeqiAg+B1GutVK0yrFIuNS0XB9/yo/VtBjZT7ywhltGaAC3K5VwVwOoOtBWXngkyuUItp87RCmDUyq8F8cGBIsyRYMnVtjmlRtB3ieh0t50vZoFUa1Cwzt2qXINZViFCypcVMOJO69JRSggdN0NTrncishZfjuFzDOgEQ2B76L8Bn4Csyi/ho/SayT0TVfqATQ62gI1U942s5DvwUxxCLHmKRHSikVIabIjjsB4XnbK0hXekiGygqhQX01oVYwxLLb3ejrPLIPyMha3sOQcMyhl48NehoQx8AIeoakpezKXO0x2yvIPpHkZk4SmgylR9qhSQunDsxZhHdBnhRhld5bPnuVzpyyh/J0mQlGVeVVmVHgoyitVPgn0qPJGhc0GxKbEEHop2DJob3uiRXgBnBbLt11HOFtNiGqb8AMDmPl5pH+BB87zrr6FerurQ6GWQW/a3a0wub7Ehrk63z9MYIv9sDVX6SsUlWxND9GfBhNJgqtUgjTdoNGnhLG0EWP1BiURSit/Mwo+dThruL9Skr8ngBU8rKqx0QAAAABJRU5ErkJggg==",
    "trash_w": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAAB2UlEQVR4Xq2Uy0tVURjFf9u3VKgpORONINSR0MVx8+bNG/QPNGreJHDQzHF/QuJAFKqBA3EqohiI+Co0sgeVld4V6/Bt2ffqnbngcM49d++P9TobrgmpnCOpvfjdBTwBbgMCzoHXwCe42FdPKfm/1pBU02U8b7WjYiTJ907gFTAF/AMGgYmmjQfANtABfAGeppQOvb8jhhiWNQncBW6EnKOmQX7/APgJfAf6gENLzYzaU0rnkh4Cj4B34YN9qpeeAH+BGnCUUpo1kQufJJmq7y/DlqFWXkjqlPRB0pqHSGrz2mpAyDAWgGfAqKRe4DGwBfSH9H3gPTACzJhJJF3Pg0rYq1PgHvACmAPGgG5gOaW0JMmSKyYZzYy+xR93gN/AMVTvTqDy66skG258LgflqblUGyFzOgroSpihLz+7FmZnrJS2NNALz5zkrxZme72ZGj1XMcql/AN8jCJ601nE79hz9OMxYO8So+iB++COOBkvdmou3E3gVjxb3v2Qv1sOuio1p/MjmM0Dq8BOSFkHhqOgHup0G5G/fElu64mkAZfNUbuwce+WtChp0+uLz6uBUT5SrN0FdPTlsWLYM6t4G5+UfawSL6X5vDF85tgfXw3nVRjudW+aFf0HHCLbk4UJp+cAAAAASUVORK5CYII=",
    "trash_l": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAADAElEQVR4Xq2TT2hcVRTGv+/e92aSTJJJbTMujMWKUjIDgn+KKLgQEVy4cTFRsCsXlSy68A9V3GQGhCLtQhfS2l23zkp0IQjabkIpiKtEdCFiWmMSTZPWJpN5955P3psmZEqWXrjv3cc73++8853zgP9pcT/ny2bT7z4vTS2VYo9vJd49EIPJeZffLm8defmvxuJioZvpdAyA8vMAaP86N/vcibHR8vUQDCZhbKSElVt3P/rwwrWzBxVRgCSwNVNPR45UPy2l/sksxEzC4cS7erQiIbwnYtRNQL855xIS68F06oPP5/8UQJdfSGB8atwTbAB4VOBTBI4G06qAYoegVUAVic9IehzgtCxW8yStubkcATSbTd/pdOIns8+/WC77V3ey8IMzR0kleDMzX8QRZiB7aeJOhJ6tnrk4f0ESSSrJA+r11SLQqFcS594NWens+5eu/n2QF1+cejrdUPkzOHQFXGy1Wrm2D2os1gojnPgtqfdiGh45P/vCsMFel9OvNJsg6KNzN5B1r3jHowY7T0BzuJJ32txg1oDE541Wl4iPCfpYwkmApwW8Q+C1ty/9mDnHkhkHtMUXNev1fmuc2wyxONaiwzaFNUKbAm6RLEHaOHfyiYp3BKmB0vvUdrtQHyvh5+1uUPTuWQsWAaQCPYqNlGCG0cqxoZIHo64N2LK/tNuJS7wvpmHrIKNNckq5nQfIc2h/zB4ob+P4yEM7IdoypTro83chNxKQQTJH9mSa3skMnn4pBy3cs6UA5QnyNs60Oz0JNyBNkxoGVRU0CnBMYJVSCuF4LzMd/tf/UQzjPVsKs/cvAmUD7wSv5dT4DYHrBH4HMURhQcCDzoGxlqUAurvaPVCj0f+jIzTvHd84FP3KSu2lN7HYSVCfNKDm1td/4sNx8ussxF/Gl6e2dqc61+2BFhb6003j0qGJoYl/NrfXKmvfeUxOAGsZgJuoYDJUR8vJxp3e9zOdTpxrtXJrBkGt9tXYzsmyy7fv9obpOJxnvK9w2+nFSIev7rfkP9kNagWLG425AAAAAElFTkSuQmCC",
    "close_b": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAACHUlEQVR4XoWUT2sTQRjGf7s7mxBBJY2H6kHw2t76D7G1qeDBfIBKMRQPihc/xJLPIZ5KAhKPQpubaXIrIp7Ee4sUCR5UJNmdGXk3u+km2db3tJl583tnnufZhflyctby6v99AbhXwASQQi6HVUEJJAjmYdkBu7t42WEx0Vqcp8v4hQVaBcXSMGK/1edTtYrqdolScKOBebZF2XNoA4vG5Umzy5nsy/Tx8W7g4bDuK+5qQ6e+Ta3Z5URgOzuYCcTlqKjYiAw4ITeBUzl9DJGHpHFVuXSUSyUyDDTUmsecSE98Epcj32NDGwgNL1s93qb/nYiVLtS3WffgUGDaMAgdHodDvpUKHCuPtRiiedXq80Z0arfRMmhK9VSTBNYpKMp/R5w5cF70WdEWRtEYElRRjUS/OZDUBPaQFc/lvQP37NieX1bz+qDPwSxEai4vIqxsjEK+GsMAMMZgsQyHms+y9zEnZFOgjOhl0aTosxZpjIXfyuNW0acn15ZIyMnnchQ7B26DJCeJO0III/atyxfl0FUO5aybeWKL6PbFfRZGBQ4nFifuyKCsm1nYlP3y4/sHvD8lOqUCj0J9YbEIK5rIdVKY71EZaX6MLKvvepymYjuNBvanj3LgtrZEWsKWsTjVRMKpQ2qh5hyoXLNcl5sEwUWM4jw9r7K4t8myPM++lNm1vQfcqW+xlIh9+Rcg781Pa+YTkw+RpqsgWdhs3z9YtvZ/87Y5WwAAAABJRU5ErkJggg==",
    "close_w": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAABO0lEQVR4Xo2Uu0oEQRBFyydsqJGI/oCyIC77NxqJf+cniLmImIibCYKBiA8wE9Ej3VaNd3q6dSuaR8/pmntvl1lRwEL5rFZzrQMWW7AECMifMGA5QWowfQYsDTbzXVaBE+AGmDgsQxUMrAGnwDWw1XUYF8AIuOOnnoBpwKITh5z7mlS7ve5l4cQhPZgvTp0o5KgqgcCmBWzPu72QTo4dMtRJNUm/Bbz4h/fAZQXS6dfKR7i2D9wK4A04LE2IquXly1/OzOzZLN9jZu9mdjVPWFWnJGxo8gG5m1Sv6mbrl3J3FYsPgLFoptHoiy2RXy8szu74BqWbkbNfeZL1wApwVnNHjo3CHoHtVrJnkDWJsOkRCTcT7AH4BHbKZOfRAWxI7Adhi4MKbAqkPXb+GSOdJs0x4lo1Z5FOgnKzb/+gG36YFBBBAAAAAElFTkSuQmCC",
    "close_l": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAACgUlEQVR4XoWUu08UURTGz33N7IKAuDFBYkxsoeOxASGZJTHG/QOgs1DJmsXWKNJcphAf0ZYt0MrEQixNcG3MagIqMZbGHmKIIWoQYWbuw5xdhgz70JtMMWfO/O4533fuBWhcpEms2fp/npRAW8EsVAExpDXM84AjRErZAEtu8HxykiU3qxKttWR+ql+0nex6lnZY324QXbpd+vBJSo/7fkVVc6SkxPfN3eJ4N6dmGQj06H11cfbxx00LAPygVOg83cl0AMOuw8+EypYXiqP5Ob+yLj2PQy5nYoig9lVbSmRDZUA7pAsANgA3idvwfd88LI4PEmbLQtBMpMx2oEx+rrS2jjlYCUJch2aVshAoNT1bev8EJcB/D8WKAwvF0WGX0xXBaUYps620Pc9c89VG7K0r6JDSFiJlCjcXV5dQp6nlZY0bHVE91qQKY6ScdkX3zp9ok4Ddak+LgUgbCKMa5I30+MSBfg2gapuex/1KRd0vjAxwl70gQM4Cmg5kJ9L6+q3FtadJE+LVOC+5nMGPvB2+GA3bBMBoYy2ADZSBz63m60hrSYsFs69TDhva3YsUAdhLpXhHGJmfoTYX0ID6qg4rwmFLWlwT1gABcplROxZF+ocj6HE0AjXE+UoOZW0gAQgBsI+ujpywKbriOiyL7gTKFGYXV5cwJ+lmcjSO2I8vvd9esl/cKR9LOxP7oQala+5gCwjCCmKYK1hmL1DfiWGDN0rvNtAKitXM+7793S64BXJKa6NCZadjixGADwJRm2Df5INQbxEgGWtsR7UhKWtax8fkwcxwz72ZsX6M1R/KZExeOdd751q278DB1jdAs5Mfr7orpjkEk/4FScLq8/4CV2NXMRdNOqUAAAAASUVORK5CYII=",
    "pin_b": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAACBklEQVR4Xq2TP2gUQRTGf29m9zaXROGKRC0ERbG4wsLGRrNio7WwIGpAG1tTWnkeir2VIjYiSRNIJ+mUu2glYuV11qn8F3LE3M7uyMzd5faOjQHxg2WZffu+9733voH/BJngcWd7/TJHKobbmaUyjAvYQEFmefO6zecGqCbkw3hQJGrE6GYLExiWarPc39oBNShlc5iO4EeXa8C5ToKwOspWY4pavoJYWPvVpW0Mvd8pqXvSnN3tXToITy1IvY4t5o4ROalO1XKbjybjWRhQwaKwSKiJ0owPyxu8Wk1QzeaoLYdxRQO4/lHUpd+WFafS1c854xR/mVBTRiTfq2hilM057pI9ifSJRDGXxMxsbqKTBF1sbXJre7hxgXdRwKXUkCEoJUhu2Tq1Qa24rcJWPfzak5ijVbhjcyJruauE+dy1JGisJ0yxPA9CvvVS1lfe82loAz8jN2D3jiz3ajM8qUY0KiHHtEYr3Y+FATrUTE1HLB2e4hHwwn33NoCBj/prd/tc+9nlbJb55IoXI5wETvQMbcD0DGmaISKsuJxJG+yLxQUeLC54z+w7z5GiwtqdVF+lQ0Ad8/UtkbPBzascOn2e7U5nZMZJL5WiEffbvnWRx05REjM7+LFUWakh/wUHEon4+YzdqzIcSJRbQq3+PuiyK7KHhy0y71TFyzTjCvPsDIKl6v4AXt+ttlkF7ogAAAAASUVORK5CYII=",
    "pin_w": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAABS0lEQVR4Xq2TPU4DQQyFnxN+CkSJoAAJJAQSBR1X4Ax0wEVoqbhADkBJh6ihD1Qcgw4hQkI+5MWDZofd5fdJ0To7Xs/ze7b0T7C8DmBmBrAs6UjSXHZOxJdmdgf0zGzayAOY8QPg1Ku14DZy+q3N+C3OCtgDroER8BK/Z+AeOIycXqcqGauDYDQBxhEP2tg0VnVmknbiRtcmabnlbLz7kk2tUCR57/5+LZL9w1RoSdKCpD7UNarETXDHJI2C/np+FPGqpKcmt5JLyfYVSceS5iVtS3rNWHns43AGPEi6MrNhbQy+aXuJYS58ai0N1oWkXdcgG8YNSd7mjaSJpHFodp6Z8TWAk6BS24ISNbHD9mSvnzkD18uxCDwGm8r+XPTStY/dAaae6GyiUPpfGdM5R39B9768w2//xOA3jGazyf45Yl38uQnslytR4g3wfBMQcqHLMwAAAABJRU5ErkJggg==",
    "pin_l": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAACQ0lEQVR4Xq1Tv2tTYRQ99/vee2nTitpitIKgi0MKDoqU6hAXcVbIrggO6WCHCsXBJFiH1kkQ0sHFxcGCmwgukmLpIOLU9ycYrDZKSZu8H9+98iV9JWnTFsQDb7rfPZxzz3nAfwJ18whABMiz+xOnB9LuXWPES+YClkHXQRjE72cWV78Vi1DlMjiZO91EpWJOo1yNHU9Pj42mZzf+NKG0aj8xzDgxnELtl7kD4LLv5wlY2l3vvNpFla0qBXm3Xt9eDiITNppRZL8wNEF9M/BF6IUIKJvNSvdmD5GValU9qqx+aYWm4nmOBxFFIpTynFQQxiuziyuvl5byqlwu79qy2KOoA+ufiLKKYI8oQiC2MoguWsVra71q9hHZRyP1QQ3kFCDn7LIlISFiFgjkVKmQGzpbq+m3eehuaz2pdWOhMPkp5Tk3WmFs7Nm0ImIjm1uZmyf32rJoEyWxLxSuntHau8fMKRY80IoyhgUE0oAYIoqYZXFwwNkIW/JhpvL5a1KDdvxJ7CLuw7HRodnGVoggZlg7igSxYaRcRxNBe66eHk67+N5q3AZwJanBTo+q7QRs7D9+b1+KItYM8TpJ0AUA51uhWSZC3ApMFMZMLOqNne6twYGYn7r25PnU9c7ZD0HP0Pod9/O01i6b7wDZeGj941NS6rGnjh2vj0w0xn1/Zw70O/o+FIu5tu35wuScVfSykBtOguknrG8h/wVHEhGR2AMdRX4kEQtc17E/y+E4kKhUqhq7yuBXUWRuZX5mmjsN7qvuLzqHCjIDnUIGAAAAAElFTkSuQmCC",
    "lock_b": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAACgUlEQVR4Xp2Tu2sUURTGf2fuTCYPxUeR0kLYJliIhULcPCAQCwttUiQEBAULqxSCUZA1XXqxSOMrJoIB/wKFmAcIKiLC2lhoEZVskShrJrNz5165sxndrBsQbzfMOd/9ne98F/Y4pRJei1+yV33LHyXwpsCM9lMIhDPGsN8Kz+aWePXPQo5kagozVuRy6DMTBmAtWKC6zUxhiCtOzNU0iu4iGhlBLSyQjvXR3xnwItF8NoabFioiXNvXwWA14vrsMtN5bS7mt/LBs0waC1HKuServHM1FwZY3IopW5i82MuduwtUIQNxsLuIMrqxIgc9+GbgQ2GIEz/KhPE6qtJN1PaV6a52rlZjBgrLrJRHEDeB62smsvMrbIwXUR5UdnyIcurxIl88wWrDd7eMgfU//blHGeKlYQ6n20xoww0rrAH3drAFwWAZDBT9Fh6khtuzS7zNl+MEpFRCPi3SplOed7XT+zPGKMHzFYjU53eeGQNJim0PkCRlI4FTj5f46Pqz0LkRtmI6RTgexWjXmxpMkkJcI45qbOo0EzEiSJSQKMUh33LUTVIu7wi5E/hZXCIRfGuxnoeIUDEwpDTHgNe+wrMWN4ZyNSLUcv92PQPh97fxPURr3s+vsPrwJWva8jRQWVseRDH2z9Zb5cj5omopJgw4PV7kvC+8sR4Tsc4oMprm/DU/zMaCNFCEwBGxBG0+3cbtrSF7Lgp/JTvRSOjj4FPcjQI1nYVtuAaFNEFnTXUaN56Yhhzmo0nskYSwFbZxwG3Ird253xFy1quLotw1NkNSTs3CptPu6cFmgcxDNdrHyVBxS2uUdRGsExjqI9SttpjAR+mUuUfL3M97mz377/MLxfwPkIUn3owAAAAASUVORK5CYII=",
    "lock_w": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAABsElEQVR4Xq2UMWtVQRCFv40RoxgkFnaxELQStBdEEFRI4x+wtdXS0t7Sxj9ga2klWKVSULAXG20CGhGUqPGTc5l9XN+9r3Pgwb7ds7Nnzpy5sCLUteUjta3Czx4kSWvtj3oeuAlsAi9aa69WJZpEZ6LedRpPcj7H9p9Qj2RDvVo5Pqh31Fvqy9p7UJgBOxtJFB3U53XpUgeqG+p7dV/dLNxUmn6gbqkH6tsq47h6sh55VA+EcUpcsFofU2utCXwpwF4EB36MWH1K5cDXasbi/rAImyRRTwP36+IF9WGtU0KSXqtE99THrbU3vcO9pNCMBrtF/XCmYz1ii8Tn2KMkWRtMVyWcAC4Dv7NVDBIHwH4xC6uc/QK2gHMlRxu7N7VHj5SbdS7sAdeBi8BrIPgki8jB/Oz6LY9B/99fftda222tfQSejVgNhdRviMk8VeTFJLui3la3qwlhMWvE5UQB9jgEjgFngaPAmVHJC0f0xdhHoZrXkqADsr4BZHjThMEtxTb4qY+qE9+BU0vzszMzT7283k3Xy4j5bHyLHkBMGGCfo2g11qZ37Wk+KwtD/q/4CymbT3319LeGAAAAAElFTkSuQmCC",
    "lock_l": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAAC5klEQVR4XqVUzWsTQRR/b2Z30ySmtS3Wmwehl9aDeOmHUgtCi3iwl/RPaGlOFTSpomwjHlKLJ6E1JxHxYsCzB0WFSipVPAjxIhSRijRC82U2O7szT2bbhKa2J99pdt+b3/v93scAHGG2bbODLiLAo+KNwxy2DSydTqu7s0P9UdOYBIKY4uoVYn7jKKB/MmgmGuTezNBMLGxlo2FDMwFFBKWqm633TSQ0mI7ZD9oG9Dwe59O5nFxOjIxFwtY7IeR3IeUdBCoyxlI9sY7x32XnZnIln2nGNsHa6pADAAJAAlwgRdAQ4mpqJf80ubL+srdqXi7V3E0EXFi6MRqbzuWUjm0CtQ7Nn5m5C8c5yl9K0Vfn5OS5zkohVHG3+WCxz9ns/ZHp7gxfL9caF2sn8muDhThqBRqsrdioCa2u7dxPjHBkWNyrg9PMupwY/skYki9ZOZ0G9cbebt0PGGk2GuTBteEe5hvznpS3AGCLCB4HfgRkgIqIxiMhY0wRPKm7/sObj/Kfm81BDbJo2wjw1ooWvdddx6zRclUozpGFTA6IGGSRisCXClxPUixsYkOoHd/zhlLZD99s28ag2FpCZ8WNAMDZyh/hawZSKuUICTVHuLW6VxKeBCGk4ohYczzPNFk3R3ZaEx4sFHaBtImGQUDgIKKBRMQYQ45QREWXhFJnCOCjZXFGRAoBuJREElEc2n5AagIr02QopPySzK6/v51d3xKefGGZgTsYRK2YEbW6fuiKECAXrlSRkHl+aW5kSoDxqcOgeceVet04BrPebgcWU9depws6JUMmDzGCUwaQGQ4ZfdJXpJm05OBe/P45aggfoyHkRCABKFj0uutLYjjBSPU7rucHM7LLRstDUthS1DxghJgHQPVo2OzyfBWk1Tc6o9YVzgJQMPiuAETgej+IqZL+jg8MkKGT6KFKpdPVzOzwlBBy0fOlZhaIcIXUi0+IxANkRGWZnAtPPkuu5jf0XTzwEvyX/QUVUX25kzdykgAAAABJRU5ErkJggg==",
    "gear_b": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAADGklEQVR4XnWUTWhcVRTHf/e++96baQah9CNuVJDqIrpQiljFyVAE0ZWLMlpJYtVCdVO0SLVIZIiKWMWKGxeiSKVqdQRBdKO4GBKkLUhRaBYKLuxCAkpJYubj3S85r5k4I3oX713OPR//c87/HMX4UY0GSaeDB+KhBhUzYJuouJzu6Q59GNcZmqsRP3IvH1oNzPJuYrbC82nCM2JsPW8Vk5zc/iv63R+wm3ZbNmZUcPBOJrOcwwsdXhX5TJ0fNeySuw781G6XSP2j07xQDHj/7HlWJIgAkI9qtVC/fMN1xvDJRIW71ns8HRQrRnMsBO5QELXioofPCVCr8trGgHPecvCm+7i8sECUmphOBzdbZ75W4eW/+hRakWl9Fat1OPmbBJNoCLGUFbUq2UafF88s8or4KBEd2Yv5bRd6Z5cnEzjlIopIUAqTS/KqNMYHrNzThNQH5vt/8IYEaS9jRS0OizczzWWtUTiCIPCR9b7jPWCNyExm2DNwWK2giEy2lym2utZsUKtEpmOkHyNvpwm3+oBXmlUCD3y4yAVRnruXHargW6W5zYeyv0WiOBDArXq+N7ZLnuV8lhkmXADrcZUM0y/44KMlLhy9n3ythzr9HX/OTTOfaL72Ho/UMeEr59jQlhs2S3r1xC16lXVZlZ846e4mtFpI0muiEzdbPsrlMrVqpB4igxB5J024OcbS588+cPfHS1wZGszW+TRNeMj68t0pxQEVKSS1UWYzew/HspRTfYvNDan1XCTyUokEnsoMzcJhs4TUOr48s8SDwyBlc5tTpOvXo+iSCk+UdMVjjeZ2rfhCcpCIhS1RCDlAs9ycIuMWaLexWoZU2rhzg+O1nJNCNuGJIApSfIe3jmA9ZAaTJmSFpZjIOJHv4Ll2m0J8jI1IknJ2W86+bo/5ANcazSM+sp1I1Jp1H1lUkUsTFU70Cs47y8PDERnbAjK0MpBD4VydQ0/sJz6+v1wpjw3loiO6IwP/32vkyF7SKzcS0t95Nks5vjlzr+9Z5E2mMAv/MHprjYx17d9Lq7mP6jVQLfkEvfY5ev+32P4GI3ddfG4vIcQAAAAASUVORK5CYII=",
    "gear_w": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAABxElEQVR4Xo2Uu05VQRSG/+EcBIkWhuKUNLwADQ9AY0BN6Cgo5AlMKIBE6G3oaH0BaQg8hJqY2JgoPZ2XENAAci4f+TdrcPb2QPiTlT2ZvS7/mnVJKgAkSS1J/ZQSwLikiVA5SyldNHVK+wqhkM9toAW8Br4DP+Lsu9FsXNrUnAAdGxSKz0wr8Ly4d4BOjYC9AiPAFPA+jF4BS8BHoA/0gE/ARojxIWxsm+yoHZ63wsnfgoXRDSmRdbbCtp0ZjQJjUDFxdLOwgyYuoRJjE3gQktqujqRueD6S5MoNJJnpb0lvJZ1KWpY0nXUldVJKlzdVAx4BC8Ac8CWimdUvYLZ44EngMzAIcSu4GE+Bx3ZkhT9FDjml7WDplN1P1nVAw4Hs0LDt5Mh/DfUPJ3GsUnVlI0XDd/VmjNTmI7XDiOTH/gY8aXT+u2Bhx370FzepNRRXQzFXxm+yGEF2G//2S1uPgmm67fM3w5WckbRXGPSKlL669PGve5+GzH11r4bMI+K2z822A/wsRuQYOADehI7Hx2N1PSLl4A0Z2pcFjZU7h3bYSvCqiDWyHivEa2Qtoud3qa2Ra0qBIYvtoSSLcZ5SOr9tsV0BCQLP/MRuIA0AAAAASUVORK5CYII=",
    "gear_l": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAADhklEQVR4Xm1UXWhcVRCeOT/33t0kxk2apCAKiviQ9kEpxUSD+yb6pCDx9yFIoH+htVH7Y4zcXH/appJopVYbDO2bYhRBfNL6EJQ2VaQouI/1ofShVJPuxuzee/5GzmY3bIoDl3Pu8M3MmZlvBqBFiADjuCgAAL06HilGM+MDXf47N1KMGtA6xmNbbTd+CAAR/AHggdtKvfRXz/UjuYAfJCJMtfvg3pt3TV8oXGVzc79pj2u18dE3FO+NPtyXy/HRV5PFY15/Yu/g74jYgz6Es388u7BgAcDOHhiaqK3peZy/fKPpDP1lKo6x/eb3dyNjnxc6wsHlcu0VR3hDChy3lnYCAgnOrhhrv3IA0N0Rnbi1mi0R0fP/9jx+bSpJCONiUSSLi2Z6z+Bk9525d5YrqeIMA85ZvQSZMsafgeRCcAbWkdeprjuiYLmcvnXk00vveh/1F83t2iHSsIfVbHm35GzWGv9Scogo8lE9e8iUBWNJ+ywDyWWq7GSt99b7UAJIFkpa1AvcKN7x3QPXZMDQGuOk4MI5Wq3W9GcEUAHAl6KQ359mRjOGgEh9SVJSzc5hvK/Yngf9GGOUOoenQsm2a+OsYKycKfPk0bNLv3jwsbGd3SEEPyDDB61z4BwpxuEZa8CgwotsC1ZDIPoyFOJHRNyulDW5UPDMuHPeyan9T4SeTxMf//qPMTQpOEMicgAYhEJ8hwhf53M6WK9oQ4jqNFonF1HZH8uVGm6r9ro4BkYcK85jaJ1zDXhdxN+Uz9rJDGfGZAhwRgj+QKask5y9eHzv0Ok3PllcaQY6OUb760EQfZOMUu5pIlDVmlSbaD6975HxfChmq6nWUSik0u6Kc+5tRlAhxD1RyIdryuoo4DJT5tvDZy491Qwi6oQc7pddW+/BzFSk54lncppZLQV7KJDiG5+Cj1jLjEHwj/F5YSke7g+gHyBJSppNFYs8WSipVJcPdXWG055soeQyHwnpu5MqY5UyLtMWolCIKORBmhpV6AiP5ns6D3sKxMUi3zwiiF90tocDK5VsEgC2CoEvGEsFH58ztmod/UQEf3onlWp2mRw9tzEitw9tW5scPfjRz+tDO/boSFvAzxMQKG1ffv30xfNe/+GBoYm1NT3/ZuvQbrS+ZY2c3bVDFlbuc1e3XH8tF7BDjfqcrPYtzQD0iyajW202ye2LbWZ8INdcbP7eAP/vYvsP2CLY+OdUfb0AAAAASUVORK5CYII=",
    "search_b": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAACaElEQVR4XpWUz0uUQRzGPzPv+7qyWpRC2DmksCAMDTJ311j6BXYJFtRtEzx48z9I1u3Ypa516FJmZJ4Kioh0TU+FQZdSIqwIy/Ighqu778zErK2t+i7Rcxnemed9vs88850RBCCdRjKBXPiFmK3FTGRRAkwQtyISCZygxUrzJYhtP9lv0x2l0ROcdSV7jGZ+DZ6OZPlpnWYy6KBCm0KWNDSEuRRh0HPIVFeBMSAFrOZZXPcZuD/NgzTIDDvFikLW9ugoqjvCYF2Yqys5ZnzNDWH4YgTNrmQo5LE7lyd+9yUvSvxyZwIbbAZ9+RQHHMM7bXgb8ojfes5yiZiK0uxJxtd9FmtyHL75Gl+IreHL/scb4SpFZ7WHt+5zzYoMnCNkK9vxziRv1gqMhkM05mo4YkW2hy9LVY1hn9Jo1+OTJX3bhW+3W5dDxWK4QjLnCLTW1AWFLffXblgUMOdIpO9z3Ao0rOBagYWDiGwW3xjaCxqpHb5aflPTzr6ygYtUnPreKN/7OlhMRjhWXjUZobc/jkm2M2bn0zHc7a62nFpPlIthj7F8gbwyDGOYB1rCIS7kC3xQmhFleDYyzZR1a53uaMhSsyXbOOO4XA95NEkJvoK8z0OteV/lcUUplhWcHp7kVbnYls4uazbRG+NoyKPWV/y4Pc5sTzsnXYdHjmCv0iwpOG/FgnqqiKA7VZpLnqA1FWWprwNjx642WoqZpYsXIBAikdhoDXs69n6VtpGM0urAE0dSrzSrviZ6b4qZSkKBKIml2mgRLpMGPuYFnYeyfK5g6N/PTFeU5kSMhj/M/zK0ieLD9xdFkd+vhvaTksxmCwAAAABJRU5ErkJggg==",
    "search_w": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAABe0lEQVR4Xo2Tvy4EYRTF72VlS0IiSomI1r/VUIiCXqETjyAegILHkHgB0ag8BB3NaigUBKEgIbt+cib3kzEzO9mTTCbz3fnOPef+casAMGBmetzMMLOuu+vdP4DBHuSV5wnK+AfAlRmYNrMNMxsxszszu3D3Zyl1959aWfpJRMCBmAp4BLZEELarkewA+0FwBWwDq8Ae8B7na0FWtpkyAFPAN3AJDBcszwFvQBsYkvKSJAUiy25kTRaaUgo0I34c8bkqVWpxwriZqZD3YbXj7l21HmiYWTvio1UFElGaD/2o76UgaASBOtkxs5WIPwTR/7mKTqlbY5B15wmYL9RoJ2ydhS0pLCPXtc248AWcxCicx9ktcAhIme70JMvqBawDN4U5OgWO4kzda/VLJquzyg7MxKVl4DXINOWJrHp1qnYtZ70FvASZ3ou10x4N0AzpSZazmkgJZIqED2ChckDrkAosJcAncA1M1u5fL+Rsam0mQmV5ZfpBXkGy9QtAPML7F7wW2wAAAABJRU5ErkJggg==",
    "search_l": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAAC0UlEQVR4Xo1UW0gUURg+l5mddXdtdYtQewx72IIQNNtV8kFKA3spxteeWm9FL4UW1jhFm+6LSRfNpyAicKuXgiSiMKRNLIPALhJhRW1kWeJlZ2fOJc7ayO66Rt/LMOf85zv/953vHAhyQNMAAqAGlcQX4NdiD+/qGqEQAp6rdk0MqSrONbnWuA2YtUj8856mylJJlupkGRUwyqd/GYlhffDFD03TkK7rLNdGyB4URZxz0NMSPO1Q5CmvR7nolKWz+W7Hda+SN3muaWejIFmWvRqpjkTbjdEoDTcHTm3a4Doz8zsxQQm/wDj6DDAtkxHucjuldQuGWXv8UuyRXZ9OBzWgIR3oLBIKblZc+A1l/JVpOGs7Bh/O2YXnmwNlnjzp8aJBvhdSc2vo6nMCIcwwH5WE7qXM5Zg3ePJk2UySiCDpO1KvqKqKxffEQOzlokGiBW6ldB45tgmSbPNX9EKANjLKGMbSR1FU/C2fRKNROutLUE2rkTDkU7IEGWXAl9PsLcWeVIuMgymMESKE7BB+xYvmJUEQjy9AXR8hlMNqw2QIO8AXUa/6/RnShFAoHA+3VficSHktYQgTllXffvnZhL1zd3PVwYJ8+drcfPJO+0DsgNhAkGeYnX5q3S2V+71u5+0lg5iE8BsAgmkAebnXrexbMsh7SthNCumDjitjo9lkK4G0wxYOBfcoDtjrckp+CSNgEgqMJL1lUfrWpTg6LULnkpTtPtkfG08ny0i2CJuuA5Fc2Hs0uN3llD3UsGZa+56+ixyurpIguCthWGhR9jNJ2F5BZmcq+4oAceTitNL1rwT2UKDCoaBhh4x8psVmDdOs6xwcfy7UrCL6C6iqKlIBAJP+KBdd2jLCLYEKRUL3ZYzWW5QtcQJ3HesfnViLKCdssp62YLkM4RMG+AfLog1G0din3Cv+gaGh5WdGXJtIa0VR6laAVa/I/yH9BbBJ/gC1MVkUgFVjigAAAABJRU5ErkJggg==",
    "plus_b": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAABsklEQVR42sWTwWoUQRCGv66uXcU1gTnkZEQUD+JRRJK4ZBSfQGFAsurqC3jx4HFOvoAPoKK5yEKewdUQ8eQTGFw8KYgnZd1Md3mYybIOs4le9L90d/1/V1dVV3kOQZbhl5bwoxGR/w0H0Fvn+q0u96qzmyeWJmNe2q2XsizG1tE2T/pXuQBYluH/2NGUHLNgRlEEQowkB2rrkeQ5AkgOUggGOBzeIjEHSXZLLq/ddbW9zZIbq5wSzwdVPIHLz96w01BHA9AZo/UusXykQyeMcYXDnHCaShkcZ3trfBVFWp74PfLz5ZCPU49Zhh8MCLfXuaGO55NI21kZtoFzbrqPzqqIHaGtxMkeDze3eZymqJ7/UqZnxqJXOgq4KmEzCFUbqiAzdu/LCiVNNeLmGhePKQsTw4nDYuCkOZ6qRwrjgYf3ISJeiAbjF6952+iojjsrnIjKSBVfwMrmK97N02p9rgCSXeTbGaJ9ZnF/wnzB8Yr3QAAYDMp1LvZ7pL/KuV6Xyd0r7PW7XJt97K86m8hYhVbLo1H4cehgHsDZRpf7Asknz6PhkFBv2n+PNEXT9PdPacIvuT2IaxsKDukAAAAASUVORK5CYII=",
    "plus_w": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAABGUlEQVR42sWUTU7DMBCF3yRhxY/EmrJA4gYgcQ64AReABQfiOCxYcIVegB2iKar9seAZnBJouupIka15med5fiNLGwJogU47DyC8XgO3QJTcNiSN1xk/cVGkjtVs0n4oaSUpJB3/92M31omkBpAkTNJKysYbDEZE/kUERAVk5xbVOb3xvFbDgCgiAGaS9t0Fks4qonPgVVJjsmVEzAdz4vUGeAM+gJW/VF12qvJLYAHcubbrfLokHbmbv6Kp9sW5bwNi7bIv7VSRdirp0SQPkl4qaX1EPE2dpxNLAbjaxv62kpEtt8SB8VZSskFplKgAfPmaPS/ZMhURCRgQTJ3sXtKe9++TpVWdZQ/bHLi3O8/OpZ0/J92Uh+0TJCXaNjh2vpAAAAAASUVORK5CYII=",
    "plus_l": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAACAUlEQVR42sWTv2tTURTHv+fe+16jMYEMRap10MGho4o0VsjgX6Bws4ogahRdREWX1w5C/LUIFlwUHHPByT/AgBgyBBddi10qCtLJ9iXv3XMcXow1fW3c+t3uvd9z7udevkdjglrW6jk7rdvtVcaeSgACgMc3Fs43G9VLyNa0k1/lbUYRFAHSvFmbJcjb8v7w1dPG2RMApGWtzqsxu2KlcUlIpYOUKQEqu1lpnGQLKZd+Vo8z43MYGL3ZT8/FBzvvD307qddmeh4AlpbA24gEIPp7wADw5Do2RzcS4qywx2Mgso2oefn07FTRFL0X8ikJKXUU8O8CY3SS8EUR6YZkFMKU49j377/sfh11bFmr6875ZmPhwr6Q3vQTDgWiKMMkEKkhMoNEBACBfCHU3B+k9+4sd55HUc2YL3M/CAAUSTkwpsgCEGWgIoIkzV4SBEqN9ll0YDTiga/kfvajK2dOFaZQGogQexICHQH4tQm0GiR8m4BPmkSRJvaM+O6Lj53cRuN6dnX+sNe0GgZGbyQy/2D5Q3cn7z85stZqC2C9sqIq68d4RX0vKyQAAA1/YBhGDcADQN05n5ts55yvO+fXZnq+7pw3OpEsCpJuKfT1oW/iiPxRknBstAoKoTFEtPHfyR4fWgKkea16Symq/JoOHi4utj1RFsC9UxTVTBTVzCTfb2Ni0k0Yvmf9AAAAAElFTkSuQmCC",
    "pw_b": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAACYklEQVR42p2Ty2+NURTFf2t/537VlKTVCBOPFkHjMcDAow8NpkY3kbSmBkblH+jYyF8gBorEjZGBEO/qRMwMBElVyqBBEIn23vudsw2+S6om1Z2cwcnaa+999llLANUqWdc0xgriay+pViMyzsoKLI5xMAGMHGEozxhogtzRcsgSXgFvRJ5em+KxRvoZq2RcMv2TCA4OZWWB+79YcmhGzmvkKAuZ0faH0ALdqUvkJpQS0cHNCAApUQiQEUxQROrBRFtKNFzMCArKxhvyQHej4FuCOUSPiYonPjg0zehJTsJ5XThrzVhnZrjDx8YG+upNDtR/cqQt0hMTlwXvJibZCdzLAyLjWEcnu3Gi4NXEJLvkPKxkuLWeHGo1Yh640NXFp4bRN/+Zcw6bq33kOJMLDb7nTeZe/6CRnDc4LwB3cSgmFABc5U4lZpJzv0jMrupgTRbo9LXscec54t6CsXdTYrXDXeDVmYN0IzbGVE4ETqxWMa9ze77gbEX00s7NPGAGA7aKl+5cMTGQ4JScW9F4lHIGKhnCidb62VCrEckZaw/MKmPSxHCzAIfjVx/w5foUd3D6cYauTvHsxlPeIk6Wc5Sq9sX6cYfoNGKkiAmA/aMn6BgfJCD2SGw7Pcx6QIjDKYFAGu3HHZqCaZxuGd0t4S2W6LQ7SWKrQA7vgQWH7WpZLDgkQTCxIy0S218qN3pNJZYAMzYLiIkCgYOyfVtob6vQLyBkEDIsW3oMzCDLsNC6y8rckKHoXCxNe5TRYAynhJxlmra0jBeJh9eeMbF0FysNCWBwkDAEPP5P9m/OkycUvwBPxPx5JhrDUgAAAABJRU5ErkJggg==",
    "pw_w": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAABlUlEQVR42qWUsWpUURCGv7m5iRgNiotoE0STNIJprLQI4nP4BFbBBxAs4wvYCIKIpA8KERGNnQQrMRBh0QQLsdEu2b13P5u58bJsIOwOHO6ZM3Pn/DP/zAkAdQooGE8GEVGjjhvgSNQicnMHWAEi14n+z7UVEe9RV51cVkM9AE6NuPEQmEmEdd5epq3Kb6MfhirQA76ng8BloAP8AX4BV4Fp4CfQT30AfAMuABdRB2pXnVJPq+fUOfWp+jlruJEpLKqzaqV+UUNdVwdFQi8jogYeAL+B68B94Io6A3wE/ia6HrALbEeEwC0gyv8MGpneW2AfmAPOAzeAT8AbYBk4C2wCO2oHmAdsAtXZkBvAB+Aa8CjPVoDnwLPczwMvE13TMhWZ+17CejiC2letxnutfm3pT9KnXyRLw9JrUXxTPaOWmeaieilLcTt9oqG/D3ST8k5jbAXuJt0Lef4DOACWmhkNtR4ajWoEwuMascpAUQCPh24vR6xhW1svgLVmaO8Bd8cc2ncR8YIs2qTPSDSIykkCRUT1DyZ2Mswg9GPxAAAAAElFTkSuQmCC",
    "pw_l": "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAACu0lEQVR42qWTPYzVRRTFz7kz//cR2ARcPxMNeYtG3QANGnSNC4KhpXpUdib4QQMYYKV5oUA3UFi5SmFsrHixsjAQgwICAbWyMGqyYFATcAlLYpb33n/mHor/ArskJCinmZnMnXtnzvwuAeBIux2uLZ+2n/DftBbA8msjvrXbzeh0YHhAdTowAsCHb63b0GgU42XplMT7OUxSRWHq9cqT7x8+9x0n335pR7NefBSM0KLAapQWzxfuQUByodcvd0bSJsvsKNOdgOyCpD7JWjAyuWcIMrNIANk9EYAFi0aC5GQ0Q92zDwRcJJkgCeDjzXocvtFPs9l1mWDLAgvP+tOh0sxacnd3/zULD4Vgj1gMJgF/tWaeHA11f+HqzOAV9dFKZf6M5IU9U2efg3CsUQtM9NeW5cEqQBnAL7unzj5P4ni9CDIABBG3dru57Nmula2hf6yRR69fmX3XXSs67dEagFNzvXQ99Ozy308sHUj4TcCPBATh5ZSdNm9a5Slx0R3fOMOl+qNLhpq1sKzx8NBqWj4P4RgLX9OcGWyScBTAmQ+2vzhsZk+VyXWLodxtt60R0lez/bltQRyJKo40G4UZw3gJ/9nFz2kYp2OLyC/hxbcRYbxeD4SUq0TzT+sl2zFUa14yw6kYuPHGIIHS6/s+/uHqxKenvxb5KskNE1Onv997+OTvLm6+xYxVNNyRJKSsQUqeUnYIXHvovTVLOp31EeBqAE8feHPdYxVOHMvZIYI8tH1MLpSEpgUMGzk8D95twgVNQ3QSK0nQHX+Q6kF8BqxaLMrhJKKZPesuyJXubocQbAQAPHuSgGC2giRy9kQQLjAKOLi0WUzk7GCFdrw7UXVDgUWIC9e1IkQz4t+5cpIAcPCdsTeKyI2D5FzYSvfSvKmqRVOZdHzPJ2e+WOTFA6gqXv3I/9f+/SfSTR4XVCHjpCNeAAAAAElFTkSuQmCC",
}
_icon_cache = {}


def icon(name, color="b"):
    """내장 그림 → PhotoImage (b=갈색, w=흰색, l=연한 갈색)."""
    key = "%s_%s" % (name, color)
    if key not in _icon_cache:
        _icon_cache[key] = tk.PhotoImage(data=ICONS[key])
    return _icon_cache[key]


class Tooltip:
    """마우스를 올리면 잠시 뒤 설명이 뜨는 말풍선."""

    def __init__(self, widget, text):
        self.w, self.text = widget, text
        self.tip = None
        self.job = None
        widget.bind("<Enter>", self._schedule, add="+")
        widget.bind("<Leave>", self._hide, add="+")
        widget.bind("<ButtonPress>", self._hide, add="+")

    def _schedule(self, e=None):
        self._hide()
        self.job = self.w.after(450, self._show)

    def _show(self):
        self.job = None
        if self.tip or not self.text:
            return
        t = self.tip = tk.Toplevel(self.w)
        t.overrideredirect(True)
        t.attributes("-topmost", True)
        tk.Label(t, text=self.text, font=FONT_SMALL, bg=C_BROWN, fg="#FFF1D6", padx=8, pady=4,
                 justify="left").pack()
        t.update_idletasks()
        x = self.w.winfo_rootx()
        y = self.w.winfo_rooty() + self.w.winfo_height() + 4
        sw, sh = t.winfo_screenwidth(), t.winfo_screenheight()
        tw, th = t.winfo_width(), t.winfo_height()
        x = max(0, min(x, sw - tw - 4))
        if y + th > sh - 40:
            y = self.w.winfo_rooty() - th - 4
        t.geometry("+%d+%d" % (x, y))

    def _hide(self, e=None):
        if self.job:
            self.w.after_cancel(self.job)
            self.job = None
        if self.tip:
            self.tip.destroy()
            self.tip = None


class FlatButton(tk.Label):
    """아이콘 색상에 맞춘 납작한 버튼 (variable 을 주면 켜기/끄기 버튼, icon=그림 이름, tip=설명)."""

    def __init__(self, parent, text, command, bg=C_WHITE, fg=C_BROWN, hover=C_ORANGE_LT,
                 on_bg=C_BROWN, on_fg=C_WHITE, variable=None, icon_name=None, tip=None, **kw):
        super().__init__(parent, text=text, bg=bg, fg=fg, font=kw.pop("font", FONT_SMALL),
                         padx=kw.pop("padx", 8 if icon_name else 10), pady=kw.pop("pady", 3), cursor="hand2",
                         highlightthickness=1, highlightbackground=kw.pop("border", C_LINE), **kw)
        self._bg, self._fg, self._hover = bg, fg, hover
        self._on_bg, self._on_fg = on_bg, on_fg
        self.command = command
        self.variable = variable
        self.icon_name = icon_name
        if icon_name:
            self.config(image=icon(icon_name), compound="left" if text else "none")
        self.bind("<Enter>", lambda e: self._paint(True))
        self.bind("<Leave>", lambda e: self._paint(False))
        self.bind("<Button-1>", self._click)
        self._paint(False)
        if tip:
            Tooltip(self, tip)

    def set_text(self, text):
        self.config(text=text, compound=("left" if text else "none") if self.icon_name else "none")

    def _click(self, e):
        if self.variable is not None:
            self.variable.set(not self.variable.get())
        if self.command:
            self.command()
        self._paint(False)

    def _paint(self, hover):
        on = self.variable is not None and self.variable.get()
        if on:
            self.config(bg=self._on_bg, fg=self._on_fg)
        else:
            self.config(bg=self._hover if hover else self._bg, fg=self._fg)
        if self.icon_name:
            self.config(image=icon(self.icon_name, "w" if on else "b"))

    def refresh(self):
        self._paint(False)


import tkinter.font as tkfont
from tkinter import colorchooser, filedialog

try:                                    # 배경 이미지 크기 맞춤·흐리게 (없으면 PNG/GIF 원본 크기로만 표시)
    from PIL import Image, ImageTk
    HAS_PIL = True
except Exception:
    HAS_PIL = False

DEFAULT_THEME = {
    "bg_mode": "default",     # default / color / image
    "list_bg": C_WHITE,       # 목록·미리보기 배경색
    "head_bg": C_ORANGE,      # 머리 띠 색
    "bg_image": "",           # 배경 이미지 (설정 폴더에 복사본 저장)
    "bg_dim": 70,             # 배경 이미지를 흐리게 (0~90%) - 글자가 잘 보이게
    "fg": C_BROWN,            # 목록 글자 색
    "kind_colors": True,      # 종류(표·서식·이미지…)별 글자 색 구분
    "font_family": "맑은 고딕",
    "font_size": 10,
}


def white_overlay_png(w, h, alpha):
    """반투명 흰색 PNG (배경 이미지를 흐리게 덮는 용도, Pillow 불필요)."""
    row = b"\x00" + bytes((255, 255, 255, alpha)) * w
    raw = zlib.compress(row * h, 6)

    def chunk(tag, data):
        return struct.pack(">I", len(data)) + tag + data + struct.pack(">I", zlib.crc32(tag + data) & 0xFFFFFFFF)
    png = (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 6, 0, 0, 0))
           + chunk(b"IDAT", raw) + chunk(b"IEND", b""))
    return base64.b64encode(png).decode()


def best_fraction(scale, limit=12):
    """정수 확대(z)/축소(s)로 scale 이상이 되는 가장 가까운 비율."""
    best = None
    for s_ in range(1, limit + 1):
        z = max(1, math.ceil(scale * s_ - 1e-9))
        if z > limit:
            continue
        r = z / s_
        if best is None or r < best[0]:
            best = (r, z, s_)
    return best or (1.0, 1, 1)


class ClipList(tk.Frame):
    """배경 이미지를 깔 수 있는 목록 (캔버스에 화면에 보이는 줄만 그림)."""

    COLS = (("pin", "★", 30, "center"), ("src", "출처", 70, "center"), ("kind", "종류", 64, "center"),
            ("text", "내용", 0, "w"), ("time", "시간", 64, "center"))

    def __init__(self, parent, on_select, on_star=None, on_add=None, on_pw=None):
        super().__init__(parent, bg=C_LINE, padx=1, pady=1)
        self.on_select = on_select
        self.on_star = on_star
        self.on_add, self.on_pw = on_add, on_pw
        self._head_tip = None
        self.hover_star = None
        self.rows = []                  # [{"iid", "values", "kind", "pinned"}]
        self.pos = {}                   # iid → 줄 번호
        self.sel = None
        self.off = 0                    # 위로 스크롤한 픽셀
        self.display = [c[0] for c in self.COLS]
        self.bgimg = None
        self._fit_cache = {}
        self.theme = dict(DEFAULT_THEME)
        self.font = tkfont.Font(family="맑은 고딕", size=10)
        self.head_font = tkfont.Font(family="맑은 고딕", size=9, weight="bold")
        self.rh = 28

        self.head = tk.Canvas(self, height=28, bg=C_CREAM, highlightthickness=0, bd=0)
        self.c = tk.Canvas(self, bg=C_WHITE, highlightthickness=0, bd=0, takefocus=1, height=120, width=200)
        self.sb = ttk.Scrollbar(self, orient="vertical", command=self.yview, style="Clip.Vertical.TScrollbar")
        self.head.grid(row=0, column=0, columnspan=2, sticky="ew")
        self.c.grid(row=1, column=0, sticky="nsew")
        self.sb.grid(row=1, column=1, sticky="ns")
        self.rowconfigure(1, weight=1)
        self.columnconfigure(0, weight=1)

        self.c.bind("<Configure>", lambda e: self.draw())
        self.c.bind("<Button-1>", self._click)
        self.c.bind("<Motion>", self._motion)
        self.c.bind("<Leave>", lambda e: self._set_hover(None))
        self.c.bind("<MouseWheel>", lambda e: self.scroll_px(-int(e.delta / 120) * self.rh * 3))
        self.head.bind("<Configure>", lambda e: self.draw_head())

    # ── 모양 ──
    def set_theme(self, theme, bgimg, overlay=None):
        self.theme = theme
        self.bgimg = bgimg
        self.overlay = overlay
        self.font.configure(family=theme["font_family"], size=theme["font_size"])
        self.rh = self.font.metrics("linespace") + 12
        self._fit_cache.clear()
        self.draw_head()
        bg = theme["list_bg"] if theme["bg_mode"] != "default" else C_WHITE
        self.c.configure(bg=bg)
        self.draw()

    def set_columns(self, cols):
        self.display = list(cols)
        self._fit_cache.clear()
        self.draw_head()
        self.draw()

    def _layout(self, w):
        k = max(1.0, self.theme.get("font_size", 10) / 10.0)      # 글자가 커지면 칸도 넓게
        fixed = sum(int(c[2] * k) for c in self.COLS if c[0] in self.display and c[2])
        out, x = [], 0
        for cid, title, cw, anchor in self.COLS:
            if cid not in self.display:
                continue
            width = int(cw * k) or max(60, w - fixed)
            out.append((cid, title, x, width, anchor))
            x += width
        return out

    def _fit(self, text, width):
        key = (text, width)
        if key in self._fit_cache:
            return self._fit_cache[key]
        if self.font.measure(text) <= width:
            res = text
        else:
            lo, hi = 0, len(text)
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if self.font.measure(text[:mid] + "…") <= width:
                    lo = mid
                else:
                    hi = mid - 1
            res = text[:lo] + "…"
        if len(self._fit_cache) > 4000:
            self._fit_cache.clear()
        self._fit_cache[key] = res
        return res

    # ── 그리기 ──
    def draw_head(self):
        h = self.head
        h.delete("all")
        w = max(1, h.winfo_width() - self.sb.winfo_width())
        for cid, title, x, cw, anchor in self._layout(w):
            if anchor == "center":
                h.create_text(x + cw / 2, 14, text=title, font=self.head_font, fill=C_BROWN)
            else:
                h.create_text(x + 8, 14, text=title, font=self.head_font, fill=C_BROWN, anchor="w")
            if cid == "text":           # 내용 제목 옆: [+ 메모 추가] [PW 가리기]
                bx = x + 8 + self.head_font.measure(title) + 12
                for tag, name, cmd, tip in (("h_add", "plus", self.on_add, "메모 바로 추가 (Ctrl+N)"),
                                            ("h_pw", "pw", self.on_pw,
                                             "선택한 항목 가리기 / 풀기 (Ctrl+H)\n비밀번호 같은 내용을 ●●●로 감춤\n"
                                             "보거나 풀 때 물어볼 비밀번호는 설정 → 비밀번호")):
                    if cmd is None:
                        continue
                    h.create_rectangle(bx - 4, 3, bx + 22, 25, fill="", outline="", tags=(tag, tag + "_bg"))
                    h.create_image(bx + 9, 14, image=icon(name, "b"), tags=(tag,))
                    h.tag_bind(tag, "<Button-1>", lambda e, cmd=cmd, tag=tag: (self._head_hover(tag, None, e), cmd()))
                    h.tag_bind(tag, "<Enter>", lambda e, tag=tag, tip=tip: self._head_hover(tag, tip, e))
                    h.tag_bind(tag, "<Leave>", lambda e, tag=tag: self._head_hover(tag, None, e))
                    bx += 30

    def _head_hover(self, tag, tip, e):
        h = self.head
        h.itemconfigure(tag + "_bg", fill=C_ORANGE_DK if tip else "", outline="")
        h.configure(cursor="hand2" if tip else "")
        if self._head_tip is not None:
            try:
                self._head_tip.destroy()
            except tk.TclError:
                pass
            self._head_tip = None
        if tip:
            t = self._head_tip = tk.Toplevel(h)
            t.overrideredirect(True)
            t.attributes("-topmost", True)
            tk.Label(t, text=tip, font=FONT_SMALL, bg=C_BROWN, fg="#FFF1D6", padx=8, pady=4,
                     justify="left").pack()
            t.geometry("+%d+%d" % (e.x_root + 8, h.winfo_rooty() + h.winfo_height() + 4))

    def draw(self):
        c = self.c
        c.delete("all")
        w, h = c.winfo_width(), c.winfo_height()
        if w < 2:
            return
        if self.bgimg is not None:
            c.create_image(w // 2, h // 2, image=self.bgimg, anchor="center")
            if getattr(self, "overlay", None) is not None:
                c.create_image(0, 0, image=self.overlay, anchor="nw")
        th = self.theme
        has_img = self.bgimg is not None
        rh = self.rh
        total = len(self.rows) * rh
        self.off = max(0, min(self.off, max(0, total - h)))
        cols = self._layout(w)
        first = self.off // rh
        y = -(self.off % rh)
        line = C_LINE if not has_img else ""
        for i in range(first, min(len(self.rows), first + h // rh + 2)):
            r = self.rows[i]
            if r["iid"] == self.sel:
                c.create_rectangle(0, y, w, y + rh, fill=C_SELECT, outline="")
            elif r["pinned"]:
                if has_img:
                    c.create_rectangle(0, y + 3, 4, y + rh - 3, fill=C_ORANGE_DK, outline="")
                else:
                    c.create_rectangle(0, y, w, y + rh, fill=C_CREAM if th["bg_mode"] == "default"
                                       else _mix(th["list_bg"], C_ORANGE, 0.12), outline="")
            if line:
                c.create_line(0, y + rh - 1, w, y + rh - 1, fill=line)
            for cid, title, x, cw, anchor in cols:
                val = str(r["values"].get(cid, ""))
                if cid == "pin":
                    if r["pinned"]:
                        color = C_STAR_ON
                    elif r["iid"] == self.hover_star:
                        color = C_STAR_HOVER
                    else:
                        color = C_STAR_OFF
                    val = "★"
                elif cid in ("src", "time", "kind"):
                    color = _mix(th["fg"], "#FFFFFF", 0.35)
                elif th["kind_colors"]:
                    color = KIND_COLORS.get(r["kind"], th["fg"]) if r["kind"] != "텍스트" else th["fg"]
                else:
                    color = th["fg"]
                tx = 0
                if cid == "text" and r.get("hidden"):     # 가린 항목: PW 표시
                    c.create_image(x + 8 + 9, y + rh / 2, image=icon("pw", "b"))
                    tx = 24
                txt = val if cid == "pin" else self._fit(val, cw - 14 - tx)
                if tx:
                    c.create_text(x + 8 + tx, y + rh / 2, text=txt, font=self.font, fill=color, anchor="w")
                elif anchor == "center":
                    c.create_text(x + cw / 2, y + rh / 2, text=txt, font=self.font, fill=color)
                else:
                    c.create_text(x + 8, y + rh / 2, text=txt, font=self.font, fill=color, anchor="w")
            y += rh
        if not self.rows:
            c.create_text(w / 2, min(h / 2, 80), text="기록이 없습니다", font=self.font,
                          fill=_mix(th["fg"], "#FFFFFF", 0.5))
        if total > 0 and total > h:
            self.sb.set(self.off / total, min(1.0, (self.off + h) / total))
        else:
            self.sb.set(0, 1)

    # ── 데이터 / 선택 ──
    def set_rows(self, rows):
        self.rows = rows
        self.pos = {r["iid"]: i for i, r in enumerate(rows)}
        if self.sel not in self.pos:
            self.sel = None
        self.draw()

    def select(self, iid, notify=True):
        if iid not in self.pos:
            return
        self.sel = iid
        self.see(iid)
        self.draw()
        if notify:
            self.on_select()

    def selection(self):
        return (self.sel,) if self.sel else ()

    def see(self, iid):
        i = self.pos.get(iid)
        if i is None:
            return
        h = self.c.winfo_height()
        top, bottom = i * self.rh, (i + 1) * self.rh
        if top < self.off:
            self.off = top
        elif bottom > self.off + h:
            self.off = bottom - h

    def identify_row(self, y):
        i = int((y + self.off) // self.rh)
        return self.rows[i]["iid"] if 0 <= i < len(self.rows) else ""

    def _in_star(self, x):
        for cid, title, cx, cw, anchor in self._layout(self.c.winfo_width()):
            if cid == "pin":
                return cx <= x < cx + cw
        return False

    def _click(self, e):
        self.c.focus_set()
        iid = self.identify_row(e.y)
        if not iid:
            return
        if self._in_star(e.x) and self.on_star:
            self.sel = iid
            self.on_star(iid)          # 별을 누르면 고정 / 해제
            return
        self.select(iid)

    def _set_hover(self, iid):
        if iid != self.hover_star:
            self.hover_star = iid
            self.c.configure(cursor="hand2" if iid else "")
            self.draw()

    def _motion(self, e):
        iid = self.identify_row(e.y)
        self._set_hover(iid if iid and self._in_star(e.x) else None)

    # ── 스크롤 ──
    def scroll_px(self, d):
        self.off += d
        self.draw()

    def yview(self, *args):
        total = len(self.rows) * self.rh
        h = self.c.winfo_height()
        if not args:
            return
        if args[0] == "moveto":
            self.off = int(float(args[1]) * total)
        elif args[0] == "scroll":
            n = int(args[1])
            self.off += n * (self.rh if args[2] == "units" else max(self.rh, h - self.rh))
        self.draw()


def _mix(c1, c2, t):
    """두 색을 섞음 (t=0 → c1, t=1 → c2)."""
    try:
        a = [int(c1[i:i + 2], 16) for i in (1, 3, 5)]
        b = [int(c2[i:i + 2], 16) for i in (1, 3, 5)]
        return "#%02X%02X%02X" % tuple(int(x + (y - x) * t) for x, y in zip(a, b))
    except Exception:
        return c1


class SettingsDialog:
    """⚙ 설정 창: 기록 제한 / 화면(배경·글자)."""

    def __init__(self, app):
        self.app = app
        if getattr(app, "_settings_win", None) and app._settings_win.winfo_exists():
            app._settings_win.lift()
            app._settings_win.focus_force()
            return
        t = self.t = tk.Toplevel(app.root, bg=C_BG)
        app._settings_win = t
        app._settings_obj = self
        t.title("스마트클립 설정")
        t.transient(app.root)
        t.attributes("-topmost", bool(app.topmost_var.get()))
        t.resizable(False, False)
        t.protocol("WM_DELETE_WINDOW", self.close)
        try:
            t.iconbitmap(icon_file())
        except Exception:
            pass

        cf = tk.Frame(t, bg=C_CREAM, highlightthickness=1, highlightbackground=C_LINE)
        cf.pack(fill="x", padx=12, pady=(12, 0))
        tk.Label(cf, text="✉ 오류나 개선할 점은", font=FONT_SMALL, bg=C_CREAM, fg=C_BROWN).pack(
            side="left", padx=(10, 3), pady=6)
        ml = tk.Label(cf, text=CONTACT_EMAIL, font=(FONT_SMALL[0], FONT_SMALL[1], "bold", "underline"),
                      bg=C_CREAM, fg="#1565C0", cursor="hand2")
        ml.pack(side="left", pady=6)
        tk.Label(cf, text="으로 알려 주세요", font=FONT_SMALL, bg=C_CREAM, fg=C_BROWN).pack(side="left", padx=3, pady=6)

        def copy_mail(e=None):
            app.root.clipboard_clear()
            app.root.clipboard_append(CONTACT_EMAIL)
            app.toast("메일 주소를 복사했습니다 · 받는 사람 칸에 붙여넣어 보내 주세요")
        ml.bind("<Button-1>", copy_mail)
        Tooltip(ml, "누르면 주소를 복사합니다")

        nb = ttk.Notebook(t, style="Clip.TNotebook")
        nb.pack(fill="both", expand=True, padx=12, pady=(8, 6))
        p1 = tk.Frame(nb, bg=C_BG, padx=14, pady=12)
        p2 = tk.Frame(nb, bg=C_BG, padx=14, pady=12)
        p3 = tk.Frame(nb, bg=C_BG, padx=14, pady=12)
        nb.add(p1, text="  기록  ")
        nb.add(p3, text=" 비밀번호  ", image=icon("pw", "b"), compound="left")
        nb.add(p2, text="  화면  ")
        self._build_record(p1)
        self._build_lock(p3)
        self._build_look(p2)
        self.nb, self.lock_tab = nb, p3

        bar = tk.Frame(t, bg=C_BG)
        bar.pack(fill="x", padx=12, pady=(0, 12))
        FlatButton(bar, "닫기", self.close).pack(side="right")
        self._place_beside()

    def _place_beside(self):
        """설정 창을 스마트클립 창 바로 오른쪽에 (자리가 없으면 왼쪽에) 띄움."""
        t, r = self.t, self.app.root
        t.update_idletasks()
        tw, th = t.winfo_reqwidth(), t.winfo_reqheight()
        sw, sh = t.winfo_screenwidth(), t.winfo_screenheight()
        rx, ry, rw = r.winfo_rootx(), r.winfo_rooty(), r.winfo_width()
        x = rx + rw + 8
        if x + tw > sw:
            x = rx - tw - 8
        if x < 0:
            x = max(0, sw - tw - 8)
        y = max(0, min(ry - 30, sh - th - 50))
        t.geometry("+%d+%d" % (x, y))

    # 공통 도구
    def _section(self, parent, text):
        tk.Label(parent, text=text, font=FONT_BOLD, bg=C_BG, fg=C_BROWN, anchor="w").pack(fill="x", pady=(8, 2))

    def _check(self, parent, text, var, cmd, note=None):
        cb = tk.Checkbutton(parent, text=text, variable=var, command=cmd, font=FONT_SMALL, bg=C_BG, fg=C_BROWN,
                            activebackground=C_BG, selectcolor=C_WHITE, anchor="w", justify="left",
                            highlightthickness=0, bd=0, wraplength=420)
        cb.pack(fill="x")
        if note:
            tk.Label(parent, text=note, font=FONT_SMALL, bg=C_BG, fg="#B49B74", anchor="w",
                     justify="left", wraplength=400).pack(fill="x", padx=(24, 0))

    def _combo(self, parent, label, values, current, cmd, width=12):
        row = tk.Frame(parent, bg=C_BG)
        row.pack(fill="x", pady=2)
        tk.Label(row, text=label, font=FONT_SMALL, bg=C_BG, fg=C_BROWN, width=16, anchor="w").pack(side="left")
        var = tk.StringVar(value=current)
        cb = ttk.Combobox(row, textvariable=var, values=values, state="readonly", width=width, font=FONT_SMALL)
        cb.pack(side="left")
        cb.bind("<<ComboboxSelected>>", lambda e: cmd(var.get()))
        return var

    # ── 기록 탭 ──
    def _build_record(self, p):
        a = self.app
        self._section(p, "시작")
        self._check(p, "Windows 시작할 때 자동 실행", a.autostart_var, a._sync_autostart)
        self._check(p, "자동 실행할 때는 창 없이 트레이에서 시작", a.start_tray_var, a._sync_autostart)
        self._check(p, "새 버전 확인 (하루 두 번, 깃허브에 최신 버전 번호만 물어봄)", a.update_check_var,
                    lambda: (a._save(), a.check_update(force=True) if a.update_check_var.get() else a._show_update_btn()),
                    "끄면 이 프로그램은 인터넷을 전혀 쓰지 않습니다.")
        self._section(p, "기록 제한 (해제하면 더 많은 내용이 기록됩니다)")
        self._check(p, "주민등록번호·카드번호가 든 내용은 기록하지 않음", a.pii_var, a._apply_record_settings)
        self._check(p, "프로그램이 '기록 금지'로 표시한 내용은 기록하지 않음", a.honor_var, a._apply_record_settings,
                    "비밀번호 관리 프로그램 등이 복사할 때 붙이는 표시입니다. (Windows 기본 클립보드 기록도 따르는 규칙)")
        self._check(p, "빠르게 연달아 복사한 것도 모두 기록", a.fast_var, a._apply_record_settings,
                    "기본은 0.12초 안의 연속 신호를 하나로 모읍니다. 켜면 0.03초로 줄입니다.")
        self._check(p, "아주 긴 내용(약 100쪽 이상)은 글자만 기록", a.bigtext_var, a._apply_record_settings,
                    "수백 쪽을 복사하면 한글·엑셀이 서식(HTML·RTF)을 만드느라 멈추고 그동안 붙여넣기도 "
                    "안 됩니다. 켜 두면 글자만 바로 기록해서 원래 프로그램이 느려지지 않습니다.")
        sizes = ["32MB", "64MB", "128MB", "256MB"]
        self._combo(p, "형식 하나 최대 크기", sizes, "%dMB" % a.maxfmt_var.get(),
                    lambda v: (a.maxfmt_var.set(int(v[:-2])), a._apply_record_settings()))
        tk.Label(p, text="형식 = 복사한 내용을 HTML·RTF·텍스트 등 한 가지 방식으로 담은 데이터입니다. "
                         "파일 크기와 달리, 서식이 많은 문서는 파일보다 몇 배 커질 수 있습니다.",
                 font=FONT_SMALL, bg=C_BG, fg="#B49B74", justify="left", anchor="w",
                 wraplength=400).pack(fill="x", padx=(24, 0))

        self._section(p, "보관")
        self._combo(p, "보관 개수 (고정 제외)", ["%d개" % n for n in LIMIT_CHOICES], "%d개" % a.limit_var.get(),
                    lambda v: (a.limit_var.set(int(v[:-1])), a.on_limit_changed()))
        ret_names = {0: "사용 안 함", 1: "1일 지난 기록", 7: "7일 지난 기록", 30: "30일 지난 기록"}
        self._combo(p, "자동 삭제 (고정 제외)", list(ret_names.values()), ret_names.get(a.retention_var.get(), "사용 안 함"),
                    lambda v: (a.retention_var.set({n: k for k, n in ret_names.items()}[v]), a.on_retention()))
        self._check(p, "프로그램을 끌 때 고정 안 된 기록 삭제", a.clear_exit_var, a._save)

        self._section(p, "붙여넣기 · 단축키")
        self._check(p, "한글에는 자동으로 호환 모드(HTML/RTF)로 붙여넣기", a.hwp_compat_var, a._save)
        self._combo(p, "창 여는 단축키", list(HOTKEY_CHOICES), a.hotkey_var.get(),
                    lambda v: (a.hotkey_var.set(v), a.on_hotkey()))
        bar = tk.Frame(p, bg=C_BG)
        bar.pack(fill="x", pady=(12, 0))
        FlatButton(bar, "모든 기록 삭제 (고정 포함)…", a.wipe_all).pack(side="left")

    def _build_lock(self, p):
        a = self.app
        self._section(p, "가린 항목(PW) 비밀번호")
        tk.Label(p, text="메모나 기록을 가리면(Ctrl+H) 목록·미리보기에 ●●●로만 보입니다.\n"
                         "비밀번호를 정해 두면 가린 내용을 보거나 · 풀거나 · 고칠 때 비밀번호를 묻습니다.",
                 font=FONT_SMALL, bg=C_BG, fg="#B49B74", anchor="w", justify="left", wraplength=420).pack(fill="x", pady=(0, 6))
        self.pw_lbl = tk.Label(p, font=FONT_SMALL, bg=C_BG, fg=C_BROWN, anchor="w", justify="left", wraplength=420)
        self.pw_lbl.pack(fill="x")
        pwb = tk.Frame(p, bg=C_BG)
        pwb.pack(fill="x", pady=(4, 2))
        self.pw_set_btn = FlatButton(pwb, "비밀번호 정하기", a.set_password)
        self.pw_set_btn.pack(side="left")
        self.pw_clear_btn = FlatButton(pwb, "없애기", a.clear_password)
        self.pw_clear_btn.pack(side="left", padx=(6, 0))
        self.pw_forgot_btn = FlatButton(pwb, "잊어버렸어요…", a.forgot_password)
        self.pw_forgot_btn.pack(side="left", padx=(6, 0))
        self._check(p, "가린 항목을 붙여넣을 때도 비밀번호 묻기", a.pw_paste_var, a._save,
                    "끄면 보거나 풀 때만 묻고, 붙여넣기(Enter)는 바로 됩니다.")
        self.refresh_pw()
        tk.Label(p, text="· 한 번 넣으면 3분 동안(창을 숨기기 전까지) 다시 묻지 않습니다.\n"
                         "· 5번 틀리면 30초 동안 막힙니다.\n"
                         "· 비밀번호는 저장하지 않고 확인용 값만 암호화해 둡니다. 잊으면 되찾을 수 없으니\n"
                         "  '잊어버렸어요…'로 가린 항목만 지우고 새로 정하세요.",
                 font=FONT_SMALL, bg=C_BG, fg="#B49B74", anchor="w", justify="left").pack(fill="x", pady=(10, 0))

    def refresh_pw(self):
        has = self.app.store.has_password()
        self.pw_lbl.config(text="✔ 비밀번호를 정해 두었습니다." if has
                           else "비밀번호를 정하지 않았습니다 — 지금은 누구나 '잠깐 보기'로 가린 내용을 볼 수 있습니다.",
                           fg="#2E7D32" if has else "#C0392B")
        self.pw_set_btn.set_text("비밀번호 바꾸기" if has else "비밀번호 정하기")
        for b in (self.pw_clear_btn, self.pw_forgot_btn):
            if has:
                b.pack(side="left", padx=(6, 0))
            else:
                b.pack_forget()

    # ── 화면 탭 ──
    def _build_look(self, p):
        a = self.app
        th = a.theme
        self._section(p, "배경")
        self.mode_var = tk.StringVar(value=th["bg_mode"])
        for val, text in (("default", "기본"), ("color", "단색"), ("image", "이미지")):
            tk.Radiobutton(p, text=text, value=val, variable=self.mode_var, command=self._mode_changed,
                           font=FONT_SMALL, bg=C_BG, fg=C_BROWN, activebackground=C_BG, selectcolor=C_WHITE,
                           anchor="w", highlightthickness=0, bd=0).pack(fill="x")
        row = tk.Frame(p, bg=C_BG)
        row.pack(fill="x", pady=(4, 0))
        self.list_sw = self._swatch(row, "목록 배경색", "list_bg")
        self.head_sw = self._swatch(row, "머리 띠 색", "head_bg")

        row2 = tk.Frame(p, bg=C_BG)
        row2.pack(fill="x", pady=(6, 0))
        FlatButton(row2, "이미지 고르기…", self._pick_image).pack(side="left")
        self.img_lbl = tk.Label(row2, font=FONT_SMALL, bg=C_BG, fg="#B49B74", anchor="w")
        self.img_lbl.pack(side="left", padx=8)
        self._img_label()
        row3 = tk.Frame(p, bg=C_BG)
        row3.pack(fill="x", pady=(4, 0))
        tk.Label(row3, text="이미지 흐리게", font=FONT_SMALL, bg=C_BG, fg=C_BROWN, width=16,
                 anchor="w").pack(side="left")
        self.dim = tk.Scale(row3, from_=0, to=90, orient="horizontal", length=180, showvalue=True,
                            bg=C_BG, fg=C_BROWN, troughcolor=C_ORANGE_LT, highlightthickness=0, bd=0,
                            font=FONT_SMALL, command=lambda v: self._set("bg_dim", int(float(v)), later=True))
        self.dim.set(th["bg_dim"])
        self.dim.pack(side="left")

        self._section(p, "글자")
        row4 = tk.Frame(p, bg=C_BG)
        row4.pack(fill="x")
        self.fg_sw = self._swatch(row4, "글자 색", "fg")
        self.kind_var = tk.BooleanVar(value=th["kind_colors"])
        self._check(p, "종류별 색 구분 (표·서식·이미지·파일)", self.kind_var,
                    lambda: self._set("kind_colors", bool(self.kind_var.get())))
        fams = sorted({f for f in tkfont.families(a.root) if not f.startswith("@")})
        self._combo(p, "글꼴", fams, th["font_family"], lambda v: self._set("font_family", v), width=22)
        self._combo(p, "글자 크기", [str(n) for n in range(8, 21)], str(th["font_size"]),
                    lambda v: self._set("font_size", int(v)), width=6)

        bar = tk.Frame(p, bg=C_BG)
        bar.pack(fill="x", pady=(12, 0))
        FlatButton(bar, "화면 기본값으로", self._reset).pack(side="left")

    def _swatch(self, parent, label, key):
        tk.Label(parent, text=label, font=FONT_SMALL, bg=C_BG, fg=C_BROWN).pack(side="left", padx=(0, 4))
        sw = tk.Label(parent, text="      ", bg=self.app.theme[key], relief="solid", bd=1, cursor="hand2")
        sw.pack(side="left", padx=(0, 14))
        sw.bind("<Button-1>", lambda e: self._pick_color(key, sw, label))
        return sw

    def _pick_color(self, key, sw, label):
        cur = self.app.theme[key]
        res = colorchooser.askcolor(color=cur, title=label, parent=self.t)
        if res and res[1]:
            sw.config(bg=res[1])
            if key == "list_bg" and self.mode_var.get() == "default":
                self.mode_var.set("color")
                self.app.theme["bg_mode"] = "color"
            self._set(key, res[1].upper())

    def _pick_image(self):
        types = [("그림 파일", "*.png *.gif *.jpg *.jpeg *.bmp *.webp" if HAS_PIL else "*.png *.gif")]
        path = filedialog.askopenfilename(parent=self.t, title="배경 이미지 고르기", filetypes=types)
        if not path:
            return
        try:
            ext = os.path.splitext(path)[1].lower()
            dst = os.path.join(DATA_DIR, "background" + ext)
            for old in os.listdir(DATA_DIR):
                if old.startswith("background."):
                    os.remove(os.path.join(DATA_DIR, old))
            if not HAS_PIL and ext not in (".png", ".gif"):
                raise ValueError("이 버전은 PNG·GIF 그림만 쓸 수 있습니다.")
            with open(path, "rb") as fi, open(dst, "wb") as fo:
                fo.write(fi.read())
        except Exception as e:
            messagebox.showerror(APP_NAME, "이미지를 불러오지 못했습니다.\n%s\n\nPNG 파일로 저장해서 다시 골라 보세요." % e,
                                 parent=self.t)
            return
        self.mode_var.set("image")
        self.app.theme["bg_mode"] = "image"
        self._set("bg_image", dst)
        self._img_label()

    def _img_label(self):
        path = self.app.theme.get("bg_image")
        self.img_lbl.config(text=os.path.basename(path) if path and os.path.exists(path) else "(선택 안 함)")

    def _mode_changed(self):
        mode = self.mode_var.get()
        if mode == "image" and not (self.app.theme.get("bg_image") and os.path.exists(self.app.theme["bg_image"])):
            self._pick_image()
            if self.app.theme["bg_mode"] != "image":
                self.mode_var.set(self.app.theme["bg_mode"])
            return
        self._set("bg_mode", mode)

    def _set(self, key, val, later=False):
        self.app.theme[key] = val
        self.app.apply_theme(later=later)

    def _reset(self):
        keep = self.app.theme.get("bg_image", "")
        self.app.theme.clear()
        self.app.theme.update(DEFAULT_THEME)
        self.app.theme["bg_image"] = keep
        self.mode_var.set("default")
        self.kind_var.set(True)
        self.dim.set(DEFAULT_THEME["bg_dim"])
        for sw, key in ((self.list_sw, "list_bg"), (self.head_sw, "head_bg"), (self.fg_sw, "fg")):
            sw.config(bg=DEFAULT_THEME[key])
        self.app.apply_theme()
        self.close()
        SettingsDialog(self.app)

    def close(self):
        self.app._save()
        self.app._settings_obj = None
        self.t.destroy()


def ask_password(app, title, prompt, confirm=False, check=None):
    """비밀번호 입력 창. confirm=True면 두 번 입력해서 확인.
    check(pw) → True/False 를 주면 맞을 때까지 다시 묻고, 맞으면 비밀번호를, 취소하면 None을 돌려줌"""
    t = tk.Toplevel(app.root, bg=C_BG)
    t.title(title)
    t.transient(app.root)
    t.attributes("-topmost", True)
    t.resizable(False, False)
    try:
        t.iconbitmap(icon_file())
    except Exception:
        pass
    app.menu_open = True
    res = {"pw": None}
    f = tk.Frame(t, bg=C_BG, padx=16, pady=14)
    f.pack(fill="both")
    tk.Label(f, text=prompt, font=FONT, bg=C_BG, fg=C_BROWN, anchor="w", justify="left",
             wraplength=320).pack(fill="x")
    v1, v2 = tk.StringVar(), tk.StringVar()
    opts = dict(font=FONT, relief="solid", bd=1, bg=C_WHITE, fg=C_BROWN, insertbackground=C_BROWN,
                show="●", width=28)
    e1 = tk.Entry(f, textvariable=v1, **opts)
    e1.pack(fill="x", ipady=3, pady=(8, 0))
    e2 = None
    if confirm:
        tk.Label(f, text="한 번 더 입력", font=FONT_SMALL, bg=C_BG, fg=C_BROWN_LT, anchor="w").pack(fill="x", pady=(8, 0))
        e2 = tk.Entry(f, textvariable=v2, **opts)
        e2.pack(fill="x", ipady=3, pady=(2, 0))
    msg = tk.Label(f, text="", font=FONT_SMALL, bg=C_BG, fg="#C0392B", anchor="w")
    msg.pack(fill="x", pady=(6, 0))
    fails = {"n": 0}

    def ok(_=None):
        pw = v1.get()
        if confirm:
            if len(pw) < 4:
                msg.config(text="4자 이상으로 정해 주세요")
                return "break"
            if pw != v2.get():
                msg.config(text="두 번 입력한 비밀번호가 다릅니다")
                v2.set("")
                e2.focus_set()
                return "break"
        if check is not None and not check(pw):
            fails["n"] += 1
            v1.set("")
            if fails["n"] >= 5:
                msg.config(text="5번 틀렸습니다. 잠시 후 다시 시도해 주세요.")
                t.after(1500, close)
            else:
                msg.config(text="비밀번호가 맞지 않습니다 (%d/5)" % fails["n"])
            return "break"
        res["pw"] = pw
        close()
        return "break"

    def close(_=None):
        try:
            t.grab_release()
            t.destroy()
        except tk.TclError:
            pass

    bar = tk.Frame(t, bg=C_BG)
    bar.pack(fill="x", padx=16, pady=(0, 12))
    FlatButton(bar, "취소", close).pack(side="right")
    FlatButton(bar, "확인 (Enter)", ok).pack(side="right", padx=(0, 6))
    for e in (e1, e2):
        if e is not None:
            e.bind("<Return>", ok)
    t.bind("<Escape>", close)
    t.update_idletasks()
    r = app.root
    x = r.winfo_rootx() + max(0, (r.winfo_width() - t.winfo_reqwidth()) // 2)
    y = r.winfo_rooty() + 80
    t.geometry("+%d+%d" % (max(0, x), max(0, y)))
    e1.focus_force()
    try:
        t.grab_set()
    except tk.TclError:
        pass

    def front():            # 본 창이 뒤늦게 앞으로 나와도 비밀번호 창이 가려지지 않게
        try:
            t.attributes("-topmost", True)
            t.lift()
            if t.focus_get() is None:
                e1.focus_force()
        except tk.TclError:
            pass
    for ms in (60, 250, 600, 1200):
        t.after(ms, front)
    t.wait_window()
    app.menu_open = False
    try:
        app.root.focus_force()
    except tk.TclError:
        pass
    return res["pw"]


class MemoDialog:
    """메모 추가 / 고치기. 가리기를 켜면 목록·미리보기에 ●●●로 표시 (내용은 암호화되어 저장)"""

    def __init__(self, app, item=None):
        self.app, self.item = app, item
        old = getattr(app, "_memo_win", None)
        if old is not None and old.winfo_exists():
            old.destroy()
        t = self.t = tk.Toplevel(app.root, bg=C_BG)
        app._memo_win = t
        app.menu_open = True
        t.title("메모 고치기" if item else "메모 추가")
        t.transient(app.root)
        t.attributes("-topmost", True)
        t.resizable(True, True)
        t.protocol("WM_DELETE_WINDOW", self.close)
        try:
            t.iconbitmap(icon_file())
        except Exception:
            pass
        text, title, hidden = "", "", False
        if item:
            try:
                text = get_text(dict(app.store.formats(item["id"])))
            except Exception:
                text = ""
            title, hidden = item.get("title") or "", bool(item.get("hidden"))

        f = tk.Frame(t, bg=C_BG, padx=14, pady=12)
        f.pack(fill="both", expand=True)
        tk.Label(f, text="제목 (선택 · 가려도 목록에 보임)", font=FONT_SMALL, bg=C_BG, fg=C_BROWN_LT,
                 anchor="w").pack(fill="x")
        self.title_var = tk.StringVar(value=title)
        te = tk.Entry(f, textvariable=self.title_var, font=FONT, relief="solid", bd=1, bg=C_WHITE, fg=C_BROWN,
                      insertbackground=C_BROWN)
        te.pack(fill="x", ipady=3, pady=(2, 8))
        tk.Label(f, text="내용 (붙여넣기 할 글)", font=FONT_SMALL, bg=C_BG, fg=C_BROWN_LT,
                 anchor="w").pack(fill="x")
        self.body = tk.Text(f, font=FONT, wrap="word", relief="solid", bd=1, bg=C_WHITE, fg=C_BROWN,
                            insertbackground=C_BROWN, width=44, height=7, undo=True)
        self.body.pack(fill="both", expand=True, pady=(2, 8))
        self.body.insert("1.0", text)
        self.hidden_var = tk.BooleanVar(value=hidden)
        tk.Checkbutton(f, text=" 가리기 — 비밀번호 등 (목록·미리보기에 ●●●로 표시, 붙여넣기는 그대로)",
                       image=icon("pw", "b"), compound="left",
                       variable=self.hidden_var, bg=C_BG, fg=C_BROWN, activebackground=C_BG,
                       selectcolor=C_WHITE, font=FONT_SMALL, anchor="w").pack(fill="x")
        tk.Label(f, text="내용은 암호화되어 저장됩니다. 설정에서 비밀번호를 정하면 가린 내용을 볼 때 비밀번호를 묻습니다.",
                 font=FONT_SMALL, bg=C_BG, fg="#B49B74", anchor="w").pack(fill="x", pady=(2, 0))
        bar = tk.Frame(t, bg=C_BG)
        bar.pack(fill="x", padx=14, pady=(0, 12))
        FlatButton(bar, "취소", self.close).pack(side="right")
        FlatButton(bar, "저장 (Ctrl+Enter)", self.save).pack(side="right", padx=(0, 6))
        for w in (t, te, self.body):
            w.bind("<Control-Return>", lambda e: (self.save(), "break")[1])
        t.bind("<Escape>", lambda e: self.close())
        te.bind("<Return>", lambda e: (self.body.focus_set(), "break")[1])
        self._place()
        (self.body if item else te).focus_set()

    def _place(self):
        t, r = self.t, self.app.root
        t.update_idletasks()
        tw, th = t.winfo_reqwidth(), t.winfo_reqheight()
        sw, sh = t.winfo_screenwidth(), t.winfo_screenheight()
        x = r.winfo_rootx() + max(0, (r.winfo_width() - tw) // 2)
        y = r.winfo_rooty() + 60
        t.geometry("+%d+%d" % (max(0, min(x, sw - tw - 8)), max(0, min(y, sh - th - 50))))

    def save(self):
        text = self.body.get("1.0", "end-1c")
        title = self.title_var.get().strip()
        if not text.strip():
            self.app.toast("내용을 적어 주세요")
            self.body.focus_set()
            return
        if self.item:
            self.app.store.update_memo(self.item["id"], text, title, self.hidden_var.get())
            iid = self.item["id"]
        else:
            iid = self.app.store.add_memo(text, title, self.hidden_var.get())
            if self.app.search_var.get():
                self.app.search_var.set("")
        self.app.revealed = None
        self.close()
        self.app.reload(keep_id=iid)
        self.app.toast("메모를 저장했습니다 (★ 고정 목록 맨 위)" if not self.item else "메모를 고쳤습니다")

    def close(self):
        try:
            self.t.destroy()
        except tk.TclError:
            pass
        self.app.menu_open = False
        try:
            self.app.root.focus_force()
        except tk.TclError:
            pass


class App:
    def __init__(self):
        global HOTKEY_TEXT
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass

        self.root = tk.Tk()
        self.root.withdraw()

        self._mutex = kernel32.CreateMutexW(None, False, "SmartClip_SingleInstance")
        if ctypes.get_last_error() == ERROR_ALREADY_EXISTS:
            # 이미 실행 중이면 그 창을 앞으로 불러오고 조용히 끝냄
            other = user32.FindWindowW("SmartClipListenerWnd", None)
            if other and "--tray" not in sys.argv:
                user32.PostMessageW(other, WM_SHOW_MAIN, 0, 0)
            sys.exit(0)

        self.settings = load_settings()
        if self.settings.get("hotkey") in HOTKEY_CHOICES:
            HOTKEY_TEXT = self.settings["hotkey"]
        try:
            self.store = Store(DATA_DIR)
        except Exception as e:
            messagebox.showerror(APP_NAME, "기록 저장소를 열지 못했습니다.\n%s\n\n폴더: %s" % (e, DATA_DIR))
            sys.exit(1)
        self.store.max_items = int(self.settings.get("max_items", MAX_ITEMS))
        self.q = queue.Queue()
        self.listener = ClipListener(self.q)
        self.listener.start()
        self.listener.ready.wait(5)

        self.items = []
        self.order = []                     # 화면에 보이는 항목 id 순서 (구분 제목 제외)
        self.by_id = {}
        self.last_target = None             # 붙여넣을 대상 창 (마지막으로 쓰던 다른 프로그램)
        self.visible = False
        self.popup_mode = False             # 단축키로 잠깐 띄운 상태인지
        self._tray_notice_shown = False
        self.menu_open = False
        self.revealed = None           # 가린 항목 중 잠깐 보기 중인 것
        saved = self.settings.get("update_avail")
        self.update_info = saved if isinstance(saved, dict) and \
            ver_tuple(saved.get("version", "0")) > ver_tuple(APP_VERSION) else None
        self.unlocked_until = 0        # 비밀번호를 넣은 뒤 다시 묻지 않는 시각
        self.pw_block_until = 0        # 여러 번 틀렸을 때 잠시 막음
        self._tick = 0
        self._search_job = None
        self._own = (None, 0.0)             # 내가 클립보드에 넣은 내용 (다시 기록되지 않게)

        self.topmost_var = tk.BooleanVar(value=bool(self.settings.get("topmost", False)))
        self.keep_var = tk.BooleanVar(value=bool(self.settings.get("keep_open", False)))
        self.hwp_compat_var = tk.BooleanVar(value=bool(self.settings.get("hwp_compat", True)))
        self.pw_paste_var = tk.BooleanVar(value=bool(self.settings.get("pw_on_paste", False)))
        self.update_check_var = tk.BooleanVar(value=bool(self.settings.get("update_check", True)))
        self.limit_var = tk.IntVar(value=self.store.max_items)
        # 보안 설정
        self.pii_var = tk.BooleanVar(value=bool(self.settings.get("pii_skip", True)))
        self.retention_var = tk.IntVar(value=int(self.settings.get("retention_days", 0)))
        self.clear_exit_var = tk.BooleanVar(value=bool(self.settings.get("clear_on_exit", False)))
        self.hotkey_var = tk.StringVar(value=HOTKEY_TEXT)
        self.honor_var = tk.BooleanVar(value=bool(self.settings.get("honor_flags", True)))
        self.fast_var = tk.BooleanVar(value=bool(self.settings.get("fast_capture", False)))
        self.maxfmt_var = tk.IntVar(value=int(self.settings.get("max_format_mb", 32)))
        self.bigtext_var = tk.BooleanVar(value=bool(self.settings.get("big_text_only", True)))
        self.theme = dict(DEFAULT_THEME)
        self.theme.update({k: v for k, v in self.settings.get("theme", {}).items() if k in DEFAULT_THEME})
        self._bg_src = None              # 원본 배경 이미지 (PIL)
        self._bg_job = None
        self._apply_record_settings(save=False)
        self.autostart_var = tk.BooleanVar(value=bool(self.settings.get("autostart", True)))    # 기본: 켬
        self.start_tray_var = tk.BooleanVar(value=bool(self.settings.get("start_in_tray", True)))
        self._sync_autostart(save=False)

        self.store.purge_older(self.retention_var.get())
        self._build()
        self.apply_theme(later=True)
        self.apply_topmost()
        self._sync_tray_state()
        self.reload()

        if not self.listener.hotkey_ok:
            messagebox.showwarning(APP_NAME, "%s 단축키를 등록하지 못했습니다.\n"
                                   "다른 프로그램이 이미 쓰고 있을 수 있습니다.\n"
                                   "오른쪽 클릭 메뉴 → 보안·환경 설정 → 단축키에서 다른 조합을 고르세요.\n"
                                   "트레이 아이콘을 클릭해서도 창을 열 수 있습니다." % HOTKEY_TEXT)

        if "--tray" in sys.argv:
            pass                   # Windows 시작 시 자동 실행: 트레이에서 조용히 시작
        else:
            self.show(None)        # 실행하면 창을 바로 띄움 (트레이 아이콘도 함께 표시)
        self.root.after(50, self.poll)
        self._show_update_btn()
        self.root.after(5000, self.check_update)

    # ─────────────────────── 화면 구성 ───────────────────────
    def _build(self):
        r = self.root
        r.title("%s(%s)" % (APP_NAME, SERIES_TEXT))
        r.configure(bg=C_BG)
        path = icon_file()
        if path:
            try:
                r.iconbitmap(default=path)
            except tk.TclError:
                pass
        geo = self.settings.get("geometry")
        if geo:
            r.geometry(geo)
        else:
            sw, sh = r.winfo_screenwidth(), r.winfo_screenheight()
            r.geometry("700x600+%d+%d" % ((sw - 700) // 2, (sh - 600) // 3))
        r.minsize(300, 340)          # 좌우로 좁게 줄여 옆에 붙여 쓸 수 있게
        r.protocol("WM_DELETE_WINDOW", self.hide)

        self._style()

        # ── 머리 띠 (아이콘 주황색) ──
        head = tk.Frame(r, bg=C_ORANGE)
        head.pack(fill="x")
        title_row = tk.Frame(head, bg=C_ORANGE)
        self._head_widgets = [head, title_row]
        title_row.pack(fill="x", padx=12, pady=10)
        try:
            self._logo = tk.PhotoImage(data="".join(ICON_PNG_B64))
            logo = tk.Label(title_row, image=self._logo, bg=C_ORANGE)
            logo.pack(side="left", padx=(0, 8))
            self._head_widgets.append(logo)
        except tk.TclError:
            pass
        # 스마트클립(스마트공) - "(스마트공)"을 누르면 smartgong.kr 이 열림
        title_lbl = tk.Label(title_row, text=APP_NAME, font=FONT_TITLE, bg=C_ORANGE, fg=C_BROWN)
        title_lbl.pack(side="left")
        self._head_widgets.append(title_lbl)
        link_font = (FONT_TITLE[0], FONT_TITLE[1])
        self.link_lbl = tk.Label(title_row, text="(%s)" % SERIES_TEXT, font=link_font,
                                 bg=C_ORANGE, fg=C_BROWN_LT, cursor="hand2")
        self.link_lbl.pack(side="left", padx=(2, 0))
        self._head_widgets.append(self.link_lbl)
        self.link_lbl.bind("<Button-1>", lambda e: self.open_site())
        self.link_lbl.bind("<Enter>", lambda e: self.link_lbl.config(fg=C_BROWN, font=link_font + ("underline",)))
        self.link_lbl.bind("<Leave>", lambda e: self.link_lbl.config(fg=C_BROWN_LT, font=link_font))

        # 찾기 칸 (제목과 같은 줄)
        sbox = tk.Frame(title_row, bg=C_WHITE, highlightthickness=2, highlightbackground=C_ORANGE_DK,
                        highlightcolor=C_BROWN)
        sbox.pack(side="left", fill="x", expand=True, padx=(14, 0))
        tk.Label(sbox, image=icon("search", "l"), bg=C_WHITE).pack(side="left", padx=(7, 3))
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *_: self._search_later())
        self.entry = tk.Entry(sbox, textvariable=self.search_var, font=FONT, relief="flat", bd=0, width=6,
                              bg=C_WHITE, fg=C_BROWN, insertbackground=C_BROWN)
        self.entry.pack(side="left", fill="x", expand=True, ipady=4)
        Tooltip(self.entry, "복사한 내용 전체에서 찾기 (Ctrl+F)\n띄어쓰기로 여러 단어를 모두 포함한 항목 찾기")
        self.clear_btn = tk.Label(sbox, text="✕", bg=C_WHITE, fg=C_BROWN_LT, font=FONT_SMALL, cursor="hand2")
        self.clear_btn.pack(side="right", padx=7)
        self.clear_btn.bind("<Button-1>", lambda e: (self.search_var.set(""), self.entry.focus_set()))
        Tooltip(self.clear_btn, "찾는 글자 지우기 (Esc)")
        self.hint_lbl = tk.Label(sbox, text="본문 전체에서 찾기", bg=C_WHITE, fg="#C2A57A", font=FONT_SMALL)
        self.hint_lbl.pack(side="right")

        # ── 도구 모음 ──
        bar = tk.Frame(r, bg=C_BG)
        bar.pack(fill="x", padx=12, pady=(8, 6))
        self.pin_btn = FlatButton(bar, "★ 고정", self.toggle_pin,
                                  tip="선택한 항목을 맨 위에 고정 / 해제 (Ctrl+P)\n목록 왼쪽 ☆를 눌러도 됩니다")
        self.pin_btn.pack(side="left")
        FlatButton(bar, "▲", lambda: self.move_pin(-1), padx=7,
                   tip="고정 항목을 한 칸 위로 (Ctrl+↑)").pack(side="left", padx=(4, 0))
        FlatButton(bar, "▼", lambda: self.move_pin(1), padx=7,
                   tip="고정 항목을 한 칸 아래로 (Ctrl+↓)").pack(side="left", padx=(2, 0))
        self.del_btn = FlatButton(bar, "", self.delete, icon_name="close",
                                  tip="선택한 항목 삭제 (Delete)")
        self.del_btn.pack(side="left", padx=(8, 0))
        self.clear_btn2 = FlatButton(bar, "", self.clear_all, icon_name="trash",
                                     tip="최근 기록 모두 비우기\n(★ 고정 항목은 남습니다)")
        self.clear_btn2.pack(side="left", padx=(4, 0))
        self.set_btn = FlatButton(bar, "설정", self.open_settings, icon_name="gear",
                                  tip="설정 - 기록 제한, 자동 실행, 배경, 글자 (Ctrl+,)")
        self.set_btn.pack(side="right")
        self.btn_keep = FlatButton(bar, "창 유지", self.on_keep_changed, variable=self.keep_var, icon_name="lock",
                                   tip="창 유지 - 붙여넣거나 다른 곳을 눌러도 창을 닫지 않음 (Ctrl+K)")
        self.btn_keep.pack(side="right", padx=(0, 4))
        self.btn_top = FlatButton(bar, "항상 위", self.on_topmost_changed, variable=self.topmost_var,
                                  icon_name="pin", tip="항상 위 - 다른 프로그램 창보다 늘 위에 표시 (Ctrl+T)")
        self.btn_top.pack(side="right", padx=(0, 4))

        # ── 목록 + 미리보기 ──
        pw = tk.PanedWindow(r, orient="vertical", bg=C_BG, sashwidth=6, bd=0, sashrelief="flat")
        pw.pack(fill="both", expand=True, padx=12)

        self.tree = ClipList(pw, self._on_select, on_star=self._star_click,
                             on_add=lambda: self.add_memo(), on_pw=lambda: self.toggle_hidden())
        lf = self.tree
        pw.add(lf, minsize=150, stretch="always")

        pf = tk.Frame(pw, bg=C_LINE, padx=1, pady=1)
        pin_head = tk.Frame(pf, bg=C_CREAM)
        pin_head.pack(fill="x")
        self.info_lbl = tk.Label(pin_head, font=FONT_SMALL, bg=C_CREAM, fg=C_BROWN_LT, anchor="w")
        self.info_lbl.pack(side="left", fill="x", expand=True, padx=8, pady=3)
        self.match_lbl = tk.Label(pin_head, font=FONT_SMALL, bg=C_CREAM, fg=C_ORANGE_DK)
        self.match_lbl.pack(side="right", padx=8)
        self.preview = tk.Text(pf, font=FONT, wrap="word", relief="flat", bd=0, bg=C_WHITE, fg=C_BROWN,
                               padx=10, pady=8, height=7, cursor="arrow", tabs=("120",))
        psb = ttk.Scrollbar(pf, orient="vertical", command=self.preview.yview, style="Clip.Vertical.TScrollbar")
        self.preview.configure(yscrollcommand=psb.set)
        psb.pack(side="right", fill="y")
        self.preview.pack(fill="both", expand=True)
        self.preview.tag_configure("hit", background=C_HILITE, foreground=C_BROWN)
        self.preview.tag_configure("dim", foreground="#B49B74")
        self.preview.tag_configure("reveal", foreground="#1565C0", underline=True)
        self.preview.tag_bind("reveal", "<Button-1>", lambda e: self.reveal())
        self.preview.tag_bind("reveal", "<Enter>", lambda e: self.preview.config(cursor="hand2"))
        self.preview.tag_bind("reveal", "<Leave>", lambda e: self.preview.config(cursor="arrow"))
        self.preview.config(state="disabled")
        pw.add(pf, minsize=70, stretch="never")
        self.root.after(100, lambda: self._place_sash(pw))

        # ── 상태줄 ──
        foot = tk.Frame(r, bg=C_BG)
        foot.pack(fill="x", side="bottom", padx=12, pady=(6, 8), before=pw)   # 창이 작아도 상태줄은 항상 보이게
        self.count_lbl = tk.Label(foot, font=FONT_SMALL, bg=C_BG, fg=C_BROWN_LT)
        self.count_lbl.pack(side="right")
        self.keys_lbl = tk.Label(foot, font=FONT_SMALL, bg=C_BG, fg="#B49B74", anchor="w", width=1,
                                 text="Enter 붙여넣기 · Shift+Enter 텍스트만 · Ctrl+P 고정 · 오른쪽 클릭 메뉴")
        self.keys_lbl.pack(side="left", fill="x", expand=True, padx=(0, 8))
        self.upd_lbl = tk.Label(foot, text="⬆ 업데이트 필요", font=(FONT_SMALL[0], FONT_SMALL[1], "bold"),
                                bg="#E8590C", fg="white", padx=8, pady=1, cursor="hand2")
        self.upd_lbl.bind("<Button-1>", lambda e: self.show_update())
        self._layout = None
        r.bind("<Configure>", self._on_resize, add="+")
        # 오른쪽 아래 모서리: 끌어서 창 크기 조절
        self.grip = ttk.Sizegrip(r, style="Clip.TSizegrip")
        self.grip.place(relx=1.0, rely=1.0, anchor="se")
        self.grip.lift()
        Tooltip(self.grip, "끌어서 창 크기 조절")

        # ── 오른쪽 클릭 메뉴 ──
        mopt = dict(tearoff=0, font=FONT_SMALL, bg=C_WHITE, fg=C_BROWN, activebackground=C_SELECT,
                    activeforeground=C_BROWN, bd=1, relief="solid")
        self.menu = tk.Menu(r, **mopt)
        self.menu.add_command(label="붙여넣기  (Enter)", command=lambda: self.use())
        self.menu.add_command(label="텍스트만 붙여넣기  (Shift+Enter)", command=lambda: self.use(plain=True))
        self.menu.add_command(label="호환 모드로 붙여넣기 - HTML/RTF  (Alt+Enter)",
                              command=lambda: self.use(mode="compat"))
        self.menu.add_command(label="원본 형식 그대로 붙여넣기  (Ctrl+Shift+Enter)",
                              command=lambda: self.use(mode="raw"))
        self.menu.add_command(label="클립보드에만 넣기  (Ctrl+Enter)", command=lambda: self.use(paste=False))
        self.menu.add_separator()
        self.menu.add_command(label=" 메모 추가  (Ctrl+N)", command=self.add_memo, image=icon("plus", "b"),
                              compound="left")
        self.menu.add_command(label="메모 고치기  (Ctrl+E)", command=self.edit_memo)
        self.menu.add_command(label=" 가리기 / 풀기  (Ctrl+H)", command=self.toggle_hidden, image=icon("pw", "b"),
                              compound="left")
        self.menu.add_command(label=" 가린 항목 비밀번호…", command=self.open_lock_settings, image=icon("pw", "l"),
                              compound="left")
        self.menu.add_separator()
        self.menu.add_command(label="상단에 고정 / 고정 해제  (Ctrl+P)", command=self.toggle_pin)
        self.menu.add_command(label="고정 순서 위로  (Ctrl+↑)", command=lambda: self.move_pin(-1))
        self.menu.add_command(label="고정 순서 아래로  (Ctrl+↓)", command=lambda: self.move_pin(1))
        self.menu.add_command(label="삭제  (Delete)", command=self.delete)
        self.menu.add_command(label="전체 비우기 (고정 항목 제외)", command=self.clear_all)
        self.menu.add_separator()
        self.menu.add_checkbutton(label="항상 위에 표시  (Ctrl+T)", variable=self.topmost_var,
                                  command=self.on_topmost_changed)
        self.menu.add_checkbutton(label="창 유지  (Ctrl+K)", variable=self.keep_var,
                                  command=self.on_keep_changed)
        self.menu.add_checkbutton(label="한글에는 자동으로 호환 모드 사용", variable=self.hwp_compat_var,
                                  command=self._save)
        self.menu.add_separator()
        self.menu.add_command(label="⚙ 설정…  (Ctrl+,)", command=self.open_settings)
        self.menu.add_command(label="기록 일시정지 / 재개", command=self.toggle_pause)
        self.menu.add_command(label="형식 정보 보기  (F2)", command=self.show_formats)
        self.menu.add_separator()
        self.menu.add_command(label="프로그램 종료  (Ctrl+Q)", command=self.quit)

        # ── 단축키 ──
        keys = {
            "<Escape>": self.on_escape,
            "<Return>": lambda: self.use(),
            "<Shift-Return>": lambda: self.use(plain=True),
            "<Control-Return>": lambda: self.use(paste=False),
            "<Alt-Return>": lambda: self.use(mode="compat"),
            "<Control-Shift-Return>": lambda: self.use(mode="raw"),
            "<F2>": self.show_formats,
            "<Control-comma>": self.open_settings,
            "<Control-p>": self.toggle_pin, "<Control-P>": self.toggle_pin,
            "<Control-n>": self.add_memo, "<Control-N>": self.add_memo,
            "<Control-e>": self.edit_memo, "<Control-E>": self.edit_memo,
            "<Control-h>": self.toggle_hidden, "<Control-H>": self.toggle_hidden,
            "<Control-d>": self.delete, "<Control-D>": self.delete,
            "<Control-t>": self.flip_topmost, "<Control-T>": self.flip_topmost,
            "<Control-k>": self.flip_keep, "<Control-K>": self.flip_keep,
            "<Control-q>": self.quit, "<Control-Q>": self.quit,
            "<Control-f>": self.focus_search, "<Control-F>": self.focus_search,
            "<Control-Up>": lambda: self.move_pin(-1),
            "<Control-Down>": lambda: self.move_pin(1),
        }
        for seq, fn in keys.items():
            for w in (self.entry, self.tree.c, self.preview):
                w.bind(seq, lambda e, fn=fn: (fn(), "break")[1])
        self.tree.c.bind("<Delete>", lambda e: (self.delete(), "break")[1])
        self.entry.bind("<Delete>", self._entry_delete)
        for seq, d in (("<Down>", 1), ("<Up>", -1), ("<Next>", 10), ("<Prior>", -10)):
            self.entry.bind(seq, lambda e, d=d: self.move(d))
            self.tree.c.bind(seq, lambda e, d=d: self.move(d))
        self.tree.c.bind("<Double-Button-1>", self._on_double)
        self.tree.c.bind("<Button-3>", self.popup_menu)
        self.tree.c.bind("<Configure>", lambda e: (self.tree.draw(), self._render_bg_later()), add="+")
        r.bind("<FocusOut>", lambda e: r.after(200, self._check_focus))

    def _style(self):
        st = ttk.Style(self.root)
        try:
            st.theme_use("clam")
        except tk.TclError:
            pass
        st.configure("Clip.Treeview", background=C_WHITE, fieldbackground=C_WHITE, foreground=C_BROWN,
                     font=FONT, rowheight=28, borderwidth=0, relief="flat")
        st.map("Clip.Treeview", background=[("selected", C_SELECT)], foreground=[("selected", C_BROWN)])
        st.configure("Clip.Treeview.Heading", background=C_CREAM, foreground=C_BROWN, font=FONT_BOLD,
                     relief="flat", borderwidth=0, padding=(4, 5))
        st.map("Clip.Treeview.Heading", background=[("active", C_ORANGE_LT)])
        st.layout("Clip.Treeview", [("Treeview.treearea", {"sticky": "nswe"})])
        st.configure("Clip.Vertical.TScrollbar", background=C_ORANGE_LT, troughcolor=C_BG, bordercolor=C_BG,
                     arrowcolor=C_BROWN, lightcolor=C_ORANGE_LT, darkcolor=C_ORANGE_LT, gripcount=0)
        st.map("Clip.Vertical.TScrollbar", background=[("active", C_ORANGE)])
        st.configure("Clip.TNotebook", background=C_BG, borderwidth=0)
        st.configure("Clip.TSizegrip", background=C_BG)
        st.configure("Clip.TNotebook.Tab", background=C_ORANGE_LT, foreground=C_BROWN, padding=(12, 5),
                     font=FONT_SMALL)
        st.map("Clip.TNotebook.Tab", background=[("selected", C_WHITE)])

    def _place_sash(self, pw):
        try:
            h = pw.winfo_height()
            if h > 300:
                pw.sash_place(0, 0, int(h * 0.68))
        except tk.TclError:
            pass

    def _entry_delete(self, e):
        if not self.search_var.get():
            self.delete()
            return "break"
        return None

    def focus_search(self):
        self.entry.focus_set()
        self.entry.select_range(0, "end")

    # ─────────────────────── 목록 ───────────────────────
    def _search_later(self):
        if self._search_job:
            self.root.after_cancel(self._search_job)
        self._search_job = self.root.after(150, self.refresh)
        self._update_hint()

    def terms(self):
        return [t for t in self.search_var.get().lower().split() if t]

    def reload(self, keep_id=None):
        self.items = self.store.list()
        self.refresh(keep_id)

    def refresh(self, keep_id=None):
        self._search_job = None
        if keep_id is None:
            cur = self.current()
            keep_id = cur["id"] if cur else None
        terms = self.terms()
        view = [it for it in self.items if all(t in self._search_text(it) for t in terms)]
        pinned = [it for it in view if it["pinned"]]
        recent = [it for it in view if not it["pinned"]]

        # 고정 항목은 맨 위에만 한 번 (최근 기록에는 다시 나오지 않음), 구분 줄 없이
        self.order, self.by_id, rows = [], {}, []
        for it in pinned + recent:
            iid = str(it["id"])
            rows.append({"iid": iid, "kind": it["kind"], "pinned": bool(it["pinned"]),
                         "hidden": bool(it.get("hidden")), "values": {
                "pin": "★" if it["pinned"] else "", "src": source_label_cached(it["source"]),
                "kind": it["kind"], "text": self._list_text(it), "time": short_time(it["ts"])}})
            self.order.append(iid)
            self.by_id[iid] = it
        self.tree.set_rows(rows)

        total_pin = sum(1 for it in self.items if it["pinned"])
        recent_n = len(self.items) - total_pin
        txt = "기록 %d/%d · 고정 %d · %s" % (recent_n, self.store.max_items, total_pin,
                                             human_size(self.store.file_size()))
        if terms:
            txt = "찾음 %d개 · " % len(view) + txt
        if self.listener.paused:
            txt += " · ⏸ 일시정지"
        self.count_lbl.config(text=txt)

        target = str(keep_id) if keep_id is not None and str(keep_id) in self.by_id else None
        if target is None and self.order:
            target = self.order[0]
        if target:
            self._select_iid(target)
        else:
            self._show_preview(None)
            self._update_pin_button()

    # ── 가리기(비밀번호 등) ──
    HIDDEN_DOTS = "●●●●●●"

    def _list_text(self, it):
        if not it.get("hidden"):
            return it["preview"]
        title = it.get("title") or ""
        return "%s  %s" % (title, self.HIDDEN_DOTS) if title else self.HIDDEN_DOTS

    def _search_text(self, it):
        """가린 항목은 제목으로만 찾음 (내용은 검색에 걸리지 않게)"""
        if it.get("hidden"):
            return ((it.get("title") or "") + " " + it["kind"] + " 가림").lower()
        return it["search"] or ""

    UNLOCK_SEC = 180          # 비밀번호를 한 번 넣으면 3분 동안(창을 숨기기 전까지) 다시 묻지 않음

    def unlock(self, why="가린 내용을 보려면"):
        """가린 항목 비밀번호 확인. 비밀번호가 없거나 맞으면 True"""
        if not self.store.has_password():
            return True
        if time.time() < self.unlocked_until:
            return True
        if time.time() < self.pw_block_until:
            self.toast("비밀번호를 여러 번 틀렸습니다. 30초 뒤에 다시 시도해 주세요.")
            return False
        tries = {"n": 0}

        def check(pw):
            ok = self.store.check_password(pw)
            if not ok:
                tries["n"] += 1
            return ok
        pw = ask_password(self, "비밀번호 확인", "%s 비밀번호를 입력하세요." % why, check=check)
        if pw is None:
            if tries["n"] >= 5:
                self.pw_block_until = time.time() + 30
            return False
        self.unlocked_until = time.time() + self.UNLOCK_SEC
        return True

    def lock_now(self):
        self.unlocked_until = 0
        if self.revealed is not None:
            self.revealed = None
            try:
                self._show_preview(self.current())
            except Exception:
                pass

    def set_password(self):
        if self.store.has_password() and not self.unlock("비밀번호를 바꾸려면 지금"):
            return
        pw = ask_password(self, "가린 항목 비밀번호", "가린 항목(PW)을 보거나 풀 때 물어볼 비밀번호를 정하세요.\n"
                          "잊으면 되찾을 수 없습니다.", confirm=True)
        if pw is None:
            return
        self.store.set_password(pw)
        self.lock_now()
        self.toast("비밀번호를 정했습니다")
        self._refresh_pw_ui()

    def clear_password(self):
        if not self.store.has_password():
            return
        if not self.unlock("비밀번호를 없애려면 지금"):
            return
        self.store.set_password(None)
        self.toast("비밀번호를 없앴습니다")
        self._refresh_pw_ui()

    def forgot_password(self):
        self.menu_open = True
        n = sum(1 for it in self.items if it.get("hidden"))
        ok = messagebox.askyesno(APP_NAME, "비밀번호는 되찾을 수 없습니다.\n\n가린 항목 %d개를 모두 지우고 비밀번호를 없앨까요?\n"
                                 "(가리지 않은 기록은 그대로 남습니다)" % n, icon="warning", parent=self.root)
        self.menu_open = False
        if ok:
            self.store.delete_hidden()
            self.lock_now()
            self.reload()
            self.toast("가린 항목과 비밀번호를 지웠습니다")
            self._refresh_pw_ui()

    def _refresh_pw_ui(self):
        dlg = getattr(self, "_settings_obj", None)
        if dlg is not None:
            try:
                dlg.refresh_pw()
            except Exception:
                pass

    def toggle_hidden(self):
        it = self.current()
        if not it:
            return
        if it.get("hidden") and not self.unlock("가리기를 풀려면"):
            return
        self.store.set_hidden(it["id"], not it.get("hidden"))
        self.revealed = None
        self.reload(keep_id=it["id"])
        self.toast("가렸습니다 · 붙여넣기는 그대로 됩니다" if not it.get("hidden") else "가리기를 풀었습니다")

    def reveal(self):
        """가린 내용을 잠깐 보기 (다른 항목을 고르면 다시 가려짐)"""
        it = self.current()
        if it and it.get("hidden"):
            if self.revealed == it["id"]:
                self.revealed = None
            elif self.unlock():
                self.revealed = it["id"]
            self._show_preview(it)

    def add_memo(self):
        MemoDialog(self)

    def edit_memo(self):
        it = self.current()
        if not it:
            return
        if it["kind"] != "메모":
            self.toast("직접 적은 메모만 고칠 수 있습니다")
            return
        if it.get("hidden") and not self.unlock("가린 메모를 고치려면"):
            return
        MemoDialog(self, it)

    def _star_click(self, iid):
        it = self.by_id.get(iid)
        if it:
            self.store.toggle_pin(it["id"])
            self.reload(keep_id=it["id"])

    def _select_iid(self, iid):
        self.tree.select(iid)

    def move(self, d):
        if not self.order:
            return "break"
        cur = self.tree.selection()
        i = self.order.index(cur[0]) if cur and cur[0] in self.order else -1
        i = max(0, min(len(self.order) - 1, i + d))
        self._select_iid(self.order[i])
        return "break"

    def current(self):
        sel = self.tree.selection() if hasattr(self, "tree") else ()
        return self.by_id.get(sel[0]) if sel else None

    def _on_select(self, e=None):
        cur = self.current()
        if not cur or cur["id"] != getattr(self, "revealed", None):
            self.revealed = None
        self._show_preview(cur)
        self._update_pin_button()

    def _on_double(self, e):
        row = self.tree.identify_row(e.y)
        if row in self.by_id:
            self._select_iid(row)
            self.use()
        return "break"

    def _update_pin_button(self):
        it = self.current()
        if self._layout == "narrow":
            self.pin_btn.config(text="☆" if it and it["pinned"] else "★")
        else:
            self.pin_btn.config(text="☆ 해제" if it and it["pinned"] else "★ 고정")

    # ─────────────────────── 창 너비에 맞춰 배치 ───────────────────────
    def _on_resize(self, e):
        if e.widget is not self.root:
            return
        w = e.width
        layout = "wide" if w >= 600 else ("mid" if w >= 430 else "narrow")
        if layout == self._layout:
            return
        self._layout = layout
        if layout == "wide":
            self.tree.set_columns(("pin", "src", "kind", "text", "time"))
        elif layout == "mid":
            self.tree.set_columns(("pin", "src", "text", "time"))
        else:
            self.tree.set_columns(("pin", "text"))
        full = layout != "narrow"
        self.btn_top.set_text("항상 위" if full else "")
        self.btn_keep.set_text("창 유지" if full else "")
        self.set_btn.set_text("설정" if full else "")
        # 아주 좁으면 "스마트클립"만 표시
        if layout == "narrow":
            self.link_lbl.pack_forget()
            self.root.title(APP_NAME)
        else:
            self.link_lbl.pack(side="left", padx=(2, 0))
            self.root.title("%s(%s)" % (APP_NAME, SERIES_TEXT))
        self._update_pin_button()
        self._update_hint()

    def _update_hint(self):
        if self._layout == "wide" and not self.search_var.get():
            self.hint_lbl.pack(side="right")
        else:
            self.hint_lbl.pack_forget()

    def open_site(self):
        try:
            webbrowser.open(SERIES_URL)
        except Exception:
            self.toast("브라우저를 열 수 없습니다 · %s" % SERIES_URL)

    def _show_preview(self, it):
        p = self.preview
        p.config(state="normal")
        p.delete("1.0", "end")
        self.match_lbl.config(text="")
        if not it:
            self.info_lbl.config(text="")
            p.config(state="disabled")
            return
        self.info_lbl.config(text="%s · %s · %s · %s" % (
            source_label_cached(it["source"]), it["kind"], human_size(it["size"] or 0),
            time.strftime("%Y-%m-%d %H:%M", time.localtime(it["ts"]))))
        if it.get("hidden") and getattr(self, "revealed", None) != it["id"]:
            if it.get("title"):
                p.insert("end", it["title"] + "\n\n")
            p.image_create("end", image=icon("pw", "b"), padx=2)
            p.insert("end", " 가린 내용입니다.  ", "dim")
            p.insert("end", "👁 잠깐 보기", "reveal")
            p.insert("end", "  (Ctrl+H 가리기 풀기)\n\n붙여넣기(Enter)는 그대로 됩니다.", "dim")
            p.config(state="disabled")
            return
        try:
            body = full_text(self.store.formats(it["id"]))
        except Exception:
            body = ""
        if body:
            if len(body) > 200000:
                body = body[:200000] + "\n… (너무 길어 일부만 표시)"
            p.insert("1.0", body)
        else:
            p.insert("1.0", it["preview"] or "(미리볼 글자가 없습니다)", "dim")

        terms = self.terms()
        first, hits = None, 0
        for t in terms:
            start = "1.0"
            while True:
                pos = p.search(t, start, stopindex="end", nocase=True)
                if not pos:
                    break
                end = "%s+%dc" % (pos, len(t))
                p.tag_add("hit", pos, end)
                hits += 1
                first = first or pos
                start = end
        if terms:
            self.match_lbl.config(text="본문 일치 %d곳" % hits if hits else "")
        if first:
            p.see(first)
        p.config(state="disabled")

    # ─────────────────────── 창 표시 / 숨기기 ───────────────────────
    def my_hwnd(self):
        return user32.GetAncestor(self.root.winfo_id(), GA_ROOT)

    def _remember_target(self, hwnd):
        if hwnd and user32.IsWindow(hwnd) and not is_own_window(hwnd) \
                and window_class(hwnd) not in SHELL_CLASSES:
            self.last_target = hwnd

    def show(self, target=None, from_hotkey=False):
        """창 표시.
        - 실행할 때 / 트레이에서 열 때: 일반 창으로 열림 (다른 곳을 클릭해도 그대로 있음)
        - 숨겨진 상태에서 단축키로 열 때: 마우스 옆에 잠깐 뜨는 팝업 (붙여넣으면 다시 트레이로)
        """
        self._remember_target(target)
        if self.visible:
            if from_hotkey and self.popup_mode:
                self.hide()
                return
            if self.root.state() == "iconic":
                self.root.deiconify()
            self._bring_front()
            return

        self.popup_mode = from_hotkey and not self.keep_var.get()
        self.search_var.set("")
        self.reload()
        if self.popup_mode:
            self._place_near_cursor()
        else:
            geo = self.settings.get("geometry")
            if geo:
                self.root.geometry(geo)
        self.root.deiconify()
        self._bring_front()
        self.visible = True

    def _bring_front(self):
        self.root.deiconify()
        self.root.lift()
        self.root.focus_force()
        user32.SetForegroundWindow(self.my_hwnd())
        self.focus_search()

    def _place_near_cursor(self):
        pt = wt.POINT()
        user32.GetCursorPos(ctypes.byref(pt))
        self.root.update_idletasks()
        w, h = self.root.winfo_width(), self.root.winfo_height()
        if w < 100:
            w, h = 700, 600
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        x = min(max(pt.x - 40, 0), sw - w - 10)
        y = min(max(pt.y - 20, 0), sh - h - 60)
        self.root.geometry("+%d+%d" % (x, y))

    def _remember_geometry(self):
        if self.visible and not self.popup_mode and self.root.state() == "normal":
            self.settings["geometry"] = self.root.geometry()

    def on_escape(self):
        if self.search_var.get():
            self.search_var.set("")      # 먼저 검색어 지우기
        else:
            self.hide()

    def hide(self):
        first = self.visible and not self.popup_mode and not self._tray_notice_shown
        self._remember_geometry()
        self._save()
        self.visible = False
        self.popup_mode = False
        self.lock_now()                 # 창을 숨기면 다시 잠금
        self.root.withdraw()
        if first:
            self._tray_notice_shown = True
            self.toast("트레이 아이콘에서 계속 실행 중입니다 · %s 로 다시 열기" % HOTKEY_TEXT)

    def _check_focus(self):
        if not self.popup_mode or self.keep_var.get():
            return
        if self.visible and not self.menu_open and self.root.focus_get() is None:
            self.hide()

    def popup_menu(self, e):
        row = self.tree.identify_row(e.y)
        if row in self.by_id:
            self._select_iid(row)
        self.menu_open = True
        try:
            self.menu.tk_popup(e.x_root, e.y_root)
        finally:
            self.menu.grab_release()
            self.root.after(300, lambda: setattr(self, "menu_open", False))

    # ─────────────────────── 설정 ───────────────────────
    def apply_topmost(self):
        self.root.attributes("-topmost", bool(self.topmost_var.get()))

    def on_topmost_changed(self):
        self.apply_topmost()
        self.btn_top.refresh()
        self._save()
        self._sync_tray_state()

    def on_keep_changed(self):
        self.btn_keep.refresh()
        self._save()
        self._sync_tray_state()
        if self.keep_var.get() and not self.visible:
            self.show(None)

    def flip_topmost(self):
        self.topmost_var.set(not self.topmost_var.get())
        self.on_topmost_changed()

    def flip_keep(self):
        self.keep_var.set(not self.keep_var.get())
        self.on_keep_changed()

    def on_limit_changed(self):
        n = int(self.limit_var.get())
        recent_n = sum(1 for it in self.items if not it["pinned"])
        if recent_n > n:
            self.menu_open = True
            ok = messagebox.askyesno(APP_NAME, "보관 개수를 %d개로 줄이면 오래된 기록 %d개가 삭제됩니다.\n계속할까요?"
                                     % (n, recent_n - n), parent=self.root)
            self.menu_open = False
            if not ok:
                self.limit_var.set(self.store.max_items)
                return
        self.store.max_items = n
        self.store.trim()
        self._save()
        self.reload()

    def _sync_tray_state(self):
        self.listener.menu_state["topmost"] = bool(self.topmost_var.get())
        self.listener.menu_state["keep_open"] = bool(self.keep_var.get())

    def _save(self):
        self.settings["topmost"] = bool(self.topmost_var.get())
        self.settings["keep_open"] = bool(self.keep_var.get())
        self.settings["hwp_compat"] = bool(self.hwp_compat_var.get())
        self.settings["pw_on_paste"] = bool(self.pw_paste_var.get())
        self.settings["update_check"] = bool(self.update_check_var.get())
        self.settings["max_items"] = int(self.store.max_items)
        self.settings["pii_skip"] = bool(self.pii_var.get())
        self.settings["retention_days"] = int(self.retention_var.get())
        self.settings["clear_on_exit"] = bool(self.clear_exit_var.get())
        self.settings["hotkey"] = HOTKEY_TEXT
        self.settings.pop("exclude_apps", None)      # 이전 버전 설정 정리
        self.settings["honor_flags"] = bool(self.honor_var.get())
        self.settings["fast_capture"] = bool(self.fast_var.get())
        self.settings["max_format_mb"] = int(self.maxfmt_var.get())
        self.settings["big_text_only"] = bool(self.bigtext_var.get())
        self.settings["theme"] = dict(self.theme)
        self.settings["autostart"] = bool(self.autostart_var.get())
        self.settings["start_in_tray"] = bool(self.start_tray_var.get())
        save_settings(self.settings)

    # ─────────────────────── 설정 창 / 화면 테마 ───────────────────────
    def open_settings(self):
        SettingsDialog(self)

    def open_lock_settings(self):
        SettingsDialog(self)
        dlg = getattr(self, "_settings_obj", None)
        if dlg is not None:
            try:
                dlg.nb.select(dlg.lock_tab)
            except Exception:
                pass

    def _sync_autostart(self, save=True):
        """설정에 맞춰 레지스트리 자동 실행 등록/해제 (실행할 때마다 경로도 최신으로 맞춤)."""
        on = bool(self.autostart_var.get())
        remove_old_startup_shortcuts()
        ok = set_autostart(on, bool(self.start_tray_var.get()))
        if save:
            self._save()
            if not ok:
                self.toast("자동 실행 설정을 바꾸지 못했습니다 (보안 프로그램이 막았을 수 있음)")
            else:
                self.toast("Windows 시작 시 자동 실행: %s" % ("켬" if on else "끔"))

    def _apply_record_settings(self, save=True):
        self.listener.honor_flags = bool(self.honor_var.get())
        self.listener.debounce_ms = 30 if self.fast_var.get() else 120
        self.listener.max_format = int(self.maxfmt_var.get()) * 1024 * 1024
        self.listener.big_text_only = bool(self.bigtext_var.get())
        if save:
            self._save()

    def apply_theme(self, later=False):
        th = self.theme
        for w in self._head_widgets:
            try:
                w.config(bg=th["head_bg"])
            except tk.TclError:
                pass
        plain_bg = th["list_bg"] if th["bg_mode"] == "color" else C_WHITE
        self.preview.config(bg=plain_bg, fg=th["fg"], font=self.tree.font)
        if later:
            self._render_bg_later()
        else:
            self._render_bg()
        if not later:
            self._save()

    def _render_bg_later(self):
        if self._bg_job:
            self.root.after_cancel(self._bg_job)
        self._bg_job = self.root.after(150, self._render_bg)

    def _render_bg(self):
        """배경 이미지를 목록 크기에 꽉 차게 자르고, 글자가 잘 보이게 흐리게 처리."""
        self._bg_job = None
        th = self.theme
        img = overlay = None
        path = th.get("bg_image") or ""
        if th["bg_mode"] == "image" and path and os.path.exists(path):
            w, h = self.tree.c.winfo_width(), self.tree.c.winfo_height()
            if w > 2 and h > 2:
                try:
                    if HAS_PIL:
                        if not self._bg_src or self._bg_src[0] != path:
                            self._bg_src = (path, Image.open(path).convert("RGB"))
                        src = self._bg_src[1]
                        scale = max(w / src.width, h / src.height)
                        im = src.resize((max(w, int(src.width * scale + 0.5)), max(h, int(src.height * scale + 0.5))),
                                        Image.LANCZOS)
                        left, top = (im.width - w) // 2, (im.height - h) // 2
                        im = im.crop((left, top, left + w, top + h))
                        dim = max(0, min(90, int(th["bg_dim"]))) / 100.0
                        if dim:
                            im = Image.blend(im, Image.new("RGB", (w, h), "#FFFFFF"), dim)
                        img = ImageTk.PhotoImage(im, master=self.root)
                    else:
                        # Pillow 없음: Tk 기능만으로 꽉 차게 맞추고 반투명 흰색을 덮어 흐리게
                        if not self._bg_src or self._bg_src[0] != path:
                            self._bg_src = (path, tk.PhotoImage(file=path, master=self.root))
                        src = self._bg_src[1]
                        sw_, sh_ = src.width(), src.height()
                        _, z, s_ = best_fraction(max(w / sw_, h / sh_))
                        img = tk.PhotoImage(master=self.root)
                        img.tk.call(img, "copy", src, "-zoom", z, z, "-subsample", s_, s_)
                        dim = max(0, min(90, int(th["bg_dim"])))
                        if dim:
                            overlay = tk.PhotoImage(master=self.root, data=white_overlay_png(w, h, int(dim * 2.55)))
                except Exception as e:
                    self.toast("배경 이미지를 열 수 없습니다: %s" % e)
                    img = None
        self._bg_photo = (img, overlay)      # 참조 유지
        self.tree.set_theme(th, img, overlay)

    # ─────────────────────── 보안 설정 ───────────────────────
    def on_retention(self):
        self._save()
        n = self.store.purge_older(self.retention_var.get())
        self.reload()
        if n:
            self.toast("오래된 기록 %d개를 삭제했습니다" % n)

    def on_hotkey(self):
        name = self.hotkey_var.get()
        mods, vk = HOTKEY_CHOICES[name]
        self._hotkey_wanted = name
        self.listener.set_hotkey(mods, vk)

    def _hotkey_result(self, ok):
        global HOTKEY_TEXT
        name = getattr(self, "_hotkey_wanted", HOTKEY_TEXT)
        if ok:
            HOTKEY_TEXT = name
            self.listener.set_tray_tip("%s (%s)" % (APP_NAME, HOTKEY_TEXT))
            self._save()
            self.toast("창 여는 단축키: %s" % HOTKEY_TEXT)
        else:
            self.hotkey_var.set(HOTKEY_TEXT)
            mods, vk = HOTKEY_CHOICES.get(HOTKEY_TEXT, (HOTKEY_MODS, HOTKEY_VK))
            self.listener.set_hotkey(mods, vk)       # 원래 단축키로 되돌림
            self._hotkey_wanted = HOTKEY_TEXT
            self.menu_open = True
            messagebox.showwarning(APP_NAME, "%s 는 다른 프로그램이 이미 쓰고 있어 등록하지 못했습니다.\n"
                                   "다른 조합을 골라 주세요." % name, parent=self.root)
            self.menu_open = False

    def wipe_all(self):
        self.menu_open = True
        ok = messagebox.askyesno(APP_NAME, "고정 항목을 포함한 모든 기록을 지울까요?\n되돌릴 수 없습니다.",
                                 icon="warning", parent=self.root)
        self.menu_open = False
        if ok:
            self.store.clear_all()
            self.reload()
            self.toast("모든 기록을 삭제했습니다")

    # ─────────────────────── 동작 ───────────────────────
    def use(self, plain=False, paste=True, mode="auto"):
        """mode: auto(대상에 맞게) / raw(원본 그대로) / compat(호환 모드)"""
        it = self.current()
        if not it:
            return
        if it.get("hidden") and self.pw_paste_var.get() and not self.unlock("가린 항목을 붙여넣으려면"):
            return
        formats = self.store.formats(it["id"])
        target = self.last_target
        used_compat = False
        if plain:
            text = get_text(dict(formats)) or full_text(formats)
            if text:
                formats = [("#13", (text + "\x00").encode("utf-16-le"))]
        else:
            if mode == "auto" and paste and target and self.hwp_compat_var.get() \
                    and is_hwp_exe(exe_of_hwnd(target)):
                mode = "compat"
            if mode == "compat":
                compat = compat_formats(formats)
                if compat:
                    formats, used_compat = compat, True
        keep = not (self.popup_mode and not self.keep_var.get())
        if not keep:
            self.hide()
        # 내가 넣는 내용은 기록 순서를 바꾸지 않음 (맨 위로 올라오지 않게)
        self._own = (analyze(formats, "")[3], time.time())
        ok = write_clipboard(self.listener.hwnd, formats)
        self.listener.ignore_seq = user32.GetClipboardSequenceNumber()
        if not ok:
            messagebox.showerror(APP_NAME, "클립보드에 넣지 못했습니다. 잠시 후 다시 시도해 주세요.")
            return
        if paste and target and user32.IsWindow(target):
            self.root.after(40, lambda: self._paste_into(target))
        elif not paste:
            self.toast("클립보드에 넣었습니다" + (" (호환 모드)" if used_compat else ""))

    def _paste_into(self, target):
        user32.SetForegroundWindow(target)
        self.root.after(80, send_ctrl_v)

    def show_formats(self):
        """선택 항목에 저장된 클립보드 형식 목록 (문제 확인용)."""
        it = self.current()
        if not it:
            return
        formats = self.store.formats(it["id"])
        lines = ["출처: %s (%s)   종류: %s" % (source_label_cached(it["source"]), it["source"] or "?", it["kind"]),
                 "저장된 형식 %d개 (복사될 때의 순서):" % len(formats), ""]
        compat_names = {k for k, _ in compat_formats(formats)}
        for n, (k, v) in enumerate(formats, 1):
            mark = "  ◎" if k in compat_names else ""
            lines.append("%2d. %-40s %10s%s" % (n, STD_FORMAT_NAMES.get(k, k), "{:,} B".format(len(v)), mark))
        lines += ["", "◎ = 호환 모드에서 사용하는 형식"]
        report = "\n".join(lines)

        t = tk.Toplevel(self.root, bg=C_BG)
        t.title("형식 정보")
        t.attributes("-topmost", True)
        txt = tk.Text(t, font=("Consolas", 10), width=72, height=min(30, len(lines) + 2), wrap="none",
                      bg=C_WHITE, fg=C_BROWN, relief="flat", highlightthickness=1, highlightbackground=C_LINE)
        txt.insert("1.0", report)
        txt.config(state="disabled")
        txt.pack(fill="both", expand=True, padx=10, pady=(10, 6))

        def copy_report():
            self._own = (None, 0.0)
            write_clipboard(self.listener.hwnd, [("#13", (report + "\x00").encode("utf-16-le"))])
            self.listener.ignore_seq = user32.GetClipboardSequenceNumber()
            self.toast("형식 목록을 복사했습니다")

        bar = tk.Frame(t, bg=C_BG)
        bar.pack(fill="x", padx=10, pady=(0, 10))
        FlatButton(bar, "목록 복사", copy_report).pack(side="left")
        FlatButton(bar, "닫기", t.destroy).pack(side="right")

    # ── 새 버전 확인 ──
    def check_update(self, force=False):
        if not self.update_check_var.get():
            return
        if not force and time.time() - self.settings.get("update_checked", 0) < UPDATE_CHECK_HOURS * 3600 - 60:
            self.root.after(3600 * 1000, self.check_update)
            return
        q = self.q

        def work():
            import urllib.request
            try:
                req = urllib.request.Request("https://api.github.com/repos/%s/releases?per_page=30" % GITHUB_REPO,
                                             headers={"User-Agent": "SmartClip/%s" % APP_VERSION,
                                                      "Accept": "application/vnd.github+json"})
                with urllib.request.urlopen(req, timeout=10) as r:
                    rels = json.loads(r.read(2 * 1024 * 1024).decode("utf-8"))
                mine = [x for x in rels if isinstance(x, dict) and not x.get("draft") and not x.get("prerelease")
                        and str(x.get("tag_name", "")).startswith(RELEASE_TAG_PREFIX)]
                if not mine:
                    return
                rel = max(mine, key=lambda x: ver_tuple(str(x["tag_name"])[len(RELEASE_TAG_PREFIX):]))
                tag = str(rel["tag_name"])[len(RELEASE_TAG_PREFIX):]
                info = {"version": tag, "date": str(rel.get("published_at") or "")[:10]}
                q.put(("update", info if ver_tuple(tag) > ver_tuple(APP_VERSION) else None))
            except Exception:
                pass                    # 인터넷이 안 되면 조용히 넘어감
        threading.Thread(target=work, daemon=True).start()
        if not force:
            self.root.after(UPDATE_CHECK_HOURS * 3600 * 1000, self.check_update)

    def _show_update_btn(self):
        info = self.update_info
        show = bool(info) and self.update_check_var.get()
        try:
            if show:
                self.upd_lbl.config(text="⬆ 업데이트 필요 (v%s)" % info["version"])
                if not self.upd_lbl.winfo_ismapped():
                    self.upd_lbl.pack(side="left", padx=(0, 8), before=self.keys_lbl)
            else:
                self.upd_lbl.pack_forget()
        except tk.TclError:
            pass

    def show_update(self):
        info = self.update_info
        if not info:
            return
        self.menu_open = True
        ok = messagebox.askyesno(APP_NAME, "스마트클립 새 버전 v%s 이(가) 나왔습니다. (지금 v%s)\n\n"
                                 "내려받을까요?\n\n받은 SmartClip.exe 를 지금 쓰는 파일 자리에 바꿔 넣고, "
                                 "트레이 아이콘에서 끝내기 → 다시 실행하세요.\n(기록·메모·설정은 그대로 이어집니다)"
                                 % (info["version"], APP_VERSION), parent=self.root)
        self.menu_open = False
        if ok:
            webbrowser.open(DOWNLOAD_URL)

    def toggle_pin(self):
        it = self.current()
        if it:
            self.store.toggle_pin(it["id"])
            self.reload(keep_id=it["id"])

    def move_pin(self, direction):
        it = self.current()
        if not it:
            return
        if not it["pinned"]:
            self.toast("고정된 항목만 순서를 바꿀 수 있습니다 (Ctrl+P로 고정)")
            return
        if self.search_var.get():
            self.search_var.set("")
        if self.store.move_pin(it["id"], direction):
            self.reload(keep_id=it["id"])

    def delete(self):
        it = self.current()
        if not it:
            return
        iid = str(it["id"])
        i = self.order.index(iid) if iid in self.order else 0
        nxt = self.order[i + 1] if i + 1 < len(self.order) else (self.order[i - 1] if i > 0 else None)
        self.store.delete(it["id"])
        self.reload(keep_id=int(nxt) if nxt else None)

    def clear_all(self):
        self.menu_open = True
        n = sum(1 for it in self.items if not it["pinned"])
        if n and messagebox.askyesno(APP_NAME, "최근 기록 %d개를 모두 비울까요?\n(★ 상단 고정 항목은 남습니다)" % n,
                                     parent=self.root):
            self.store.clear_unpinned()
            self.reload()
            self.toast("최근 기록을 비웠습니다")
        self.menu_open = False

    def toggle_pause(self):
        self.listener.paused = not self.listener.paused
        paused = self.listener.paused
        self.listener.set_tray_tip("%s - %s" % (APP_NAME, "일시정지됨" if paused else HOTKEY_TEXT))
        self.toast("기록 일시정지" if paused else "기록 다시 시작")
        self.refresh()

    def quit(self):
        try:
            self._remember_geometry()
            self._save()
            self.listener.remove_tray()
            if self.clear_exit_var.get():
                self.store.clear_unpinned()
        finally:
            self.root.quit()
            self.root.destroy()
            os._exit(0)

    def toast(self, msg):
        t = tk.Toplevel(self.root)
        t.overrideredirect(True)
        t.attributes("-topmost", True)
        try:
            t.attributes("-alpha", 0.95)
        except tk.TclError:
            pass
        box = tk.Frame(t, bg=C_ORANGE, padx=2, pady=2)
        box.pack()
        tk.Label(box, text=msg, font=FONT, bg=C_BROWN, fg="#FFF1D6", padx=16, pady=10).pack()
        t.update_idletasks()
        sw, sh = t.winfo_screenwidth(), t.winfo_screenheight()
        t.geometry("+%d+%d" % (sw - t.winfo_width() - 24, sh - t.winfo_height() - 70))
        t.after(2500, t.destroy)

    # ─────────────────────── 감시 스레드 이벤트 처리 ───────────────────────
    def poll(self):
        try:
            while True:
                ev = self.q.get_nowait()
                kind = ev[0]
                if kind == "update":
                    self.settings["update_checked"] = time.time()
                    self.settings["update_avail"] = ev[1]
                    self.update_info = ev[1]
                    save_settings(self.settings)
                    self._show_update_btn()
                    continue
                if kind == "clip":
                    formats, exe = ev[1], ev[2]
                    k, preview, search, keyhash, size = analyze(formats, exe)
                    own_hash, own_t = self._own
                    if keyhash == own_hash and time.time() - own_t < 5:
                        continue        # 방금 내가 붙여넣은 내용 → 순서 그대로
                    if self.pii_var.get():
                        pii = find_pii(full_text(formats) or search)
                        if pii:
                            self.toast("%s가 들어 있어 기록하지 않았습니다" % pii)
                            continue
                    try:
                        self.store.add(formats, exe, k, preview, search, keyhash, size)
                    except MemoryError:
                        self.toast("내용이 너무 커서 기록하지 못했습니다")
                        continue
                    except Exception as e:
                        self.toast("기록 저장 실패: %s" % e)
                        continue
                    note = ev[3] if len(ev) > 3 else None
                    if note == "big":
                        self.toast("내용이 아주 길어서 글자만 기록했습니다 (서식 제외)")
                    elif note == "partial":
                        self.toast("일부 서식은 크기 제한을 넘어 빼고 기록했습니다 (설정 → 형식 최대 크기)")
                    self.items = self.store.list()
                    if self.visible:
                        self.refresh()
                elif kind == "hotkey_set":
                    self._hotkey_result(ev[1])
                elif kind == "hotkey":
                    self.show(ev[1], from_hotkey=True)
                elif kind == "tray_toggle":
                    if self.visible and self.root.state() != "iconic":
                        self.hide()
                    else:
                        self.visible = False
                        self.show(None)
                elif kind == "tray_cmd":
                    cmd = ev[1]
                    if cmd == 1:
                        self.show(None)
                    elif cmd == 2:
                        self.flip_topmost()
                    elif cmd == 3:
                        self.flip_keep()
                    elif cmd == 4:
                        self.toggle_pause()
                    elif cmd == 9:
                        self.quit()
        except queue.Empty:
            pass
        except Exception as e:
            print("오류:", e)

        # 0.3초마다 "지금 쓰고 있는 다른 프로그램"을 기억 (붙여넣을 곳)
        self._tick += 1
        if self._tick % 6 == 0:
            self._remember_target(user32.GetForegroundWindow())
        if self._tick % 72000 == 0 and self.retention_var.get():     # 1시간마다 자동 삭제 확인
            if self.store.purge_older(self.retention_var.get()):
                self.reload()
        self.root.after(50, self.poll)

    def run(self):
        self.root.mainloop()


_label_cache = {}


def source_label_cached(exe):
    if exe not in _label_cache:
        _label_cache[exe] = source_label(exe)
    return _label_cache[exe]


if __name__ == "__main__":
    App().run()
