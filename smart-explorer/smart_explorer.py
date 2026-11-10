# -*- coding: utf-8 -*-
"""
스마트탐색기 - 화면을 나눠 쓰는 멀티 탐색기 + 파일 이름·본문 검색기
지원: 한글(HWP, HWPX), 워드(DOCX), 엑셀(XLSX), 파워포인트(PPTX), PDF, 텍스트류
     구형 워드(DOC)·엑셀(XLS), 스캔 PDF(윈도우 내장 OCR)
     ODT·RTF·EML, 압축파일(ZIP·7Z·RAR·TAR·GZ — 안에 든 문서까지), 이미지(글자 인식)
화면 분할(가로×세로) 멀티 탐색기 — 폴더 둘러보기·복사·이동·이름 바꾸기·휴지통, 칸끼리 끌어다 놓기
탐색기와 같은 원래 모양 미리보기 + 자체 미리보기(PDF·그림·표·압축 목록)
필요 패키지: build_exe.bat 참고 (pypdfium2, winrt-Windows.Media.Ocr 등)
"""
import os
import sys
import re
import json
import time
import zlib
import html
import struct
import codecs
import queue
import sqlite3
import zipfile
import base64
import csv
import io
import gzip
import bz2
import lzma
import shutil
import tarfile
import tempfile
import logging
import threading
import subprocess
from datetime import datetime
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog

# --noconsole 빌드에서 stderr/stdout이 None이면 라이브러리 경고 출력 시 오류가 나므로 막아 둠
if sys.stderr is None:
    sys.stderr = open(os.devnull, "w")
if sys.stdout is None:
    sys.stdout = open(os.devnull, "w")

try:
    import pypdfium2 as pdfium
    import pypdfium2.raw as pdfium_c
except ImportError:
    pdfium = None
try:
    from pypdf import PdfReader
    logging.getLogger("pypdf").setLevel(logging.ERROR)
except ImportError:
    PdfReader = None
try:
    from PIL import Image, ImageOps
    Image.MAX_IMAGE_PIXELS = 300_000_000
except ImportError:
    Image = None
try:
    import py7zr
except ImportError:
    py7zr = None
try:
    import rarfile
except ImportError:
    rarfile = None

APP_NAME = "스마트탐색기"
APP_VERSION = "1.0.21"          # 배포할 때 여기만 올리고, 깃허브 태그는 v1.0.0 처럼 똑같이 붙임
DOWNLOAD_URL = "https://smartgong.kr/download/smart-explorer"   # 항상 최신 버전 exe
GITHUB_REPO = "nunco-git/ezgong"   # 새 버전 알림용 깃허브 저장소 "소유자/저장소이름". 비우면 확인 안 함
RELEASE_TAG_PREFIX = "smartexplorer-v"   # 한 저장소에 여러 프로그램을 올려도 섞이지 않게 태그 앞에 붙이는 이름
UPDATE_CHECK_HOURS = 3         # 새 버전 확인 간격 (켤 때·창을 띄울 때도 확인)
_LOCAL = os.environ.get("LOCALAPPDATA") or os.path.expanduser("~")
APP_DIR = os.path.join(_LOCAL, "SmartExplorer")
if not os.path.isdir(APP_DIR) and os.path.isdir(os.path.join(_LOCAL, "BodySearch")):
    try:                                       # 예전 '본문 검색기' 설정·캐시를 그대로 이어받음
        shutil.copytree(os.path.join(_LOCAL, "BodySearch"), APP_DIR, ignore=shutil.ignore_patterns("tmp"))
    except Exception:
        pass
os.makedirs(APP_DIR, exist_ok=True)

# ── 광고 칸 설정 ──
AD_FEED_URL = "https://smartgong.kr/ads/smart_explorer.json"   # 광고 목록(JSON) 주소. 비우면 받지 않음
AD_REFRESH_MIN = 30                        # 광고 목록을 다시 받는 간격(분)
AD_SIZE = (300, 250)                       # 광고 칸 크기(px) — 표준 '미디엄 렉탱글' 300×250. 이보다 줄이지 않음
AD_GAP = 6
AD_PANE_EXTRA = (260, 230)                 # 광고가 붙은 칸의 최소 크기 = 광고 크기 + 이만큼(미리보기·목록 자리)


# ── 설치 수 집계 ── (둘 중 하나만 써도 됨, 비우면 아무것도 보내지 않음)
FIREBASE_DB_URL = "https://smartexplorer-d569e-default-rtdb.asia-southeast1.firebasedatabase.app"   # 파이어베이스 Realtime Database 주소 (예: https://smartgong-xxxx-default-rtdb.asia-southeast1.firebasedatabase.app)
STATS_URL = ""     # 사용 집계 주소(예: 구글 Apps Script 웹 앱 주소). 비우면 아무것도 보내지 않음
                   # 보내는 것: 무작위 설치 번호, 프로그램 버전, 종류(install/daily) — 이름·PC 정보·파일 정보는 보내지 않음
AD_EMPTY_SIZE = (120, 100)                 # 아직 광고가 없을 때 칸 크기 (작게)


def ad_pixels(widget):
    """화면 배율(125%·150%)을 반영한 광고 칸 크기. 실제 광고가 있을 때만 300×250"""
    try:
        dpi = widget.winfo_fpixels("1i") / 96
    except Exception:
        dpi = 1.0
    size = AD_SIZE if (AD_MANAGER is not None and AD_MANAGER.ads) else AD_EMPTY_SIZE
    return int(size[0] * dpi), int(size[1] * dpi)
AD_MAX_IMAGE = 3 * 1024 * 1024             # 광고 그림 최대 크기
AD_PLACEHOLDER = ""                        # 받은 광고가 없을 때 보이는 글 (비워 둠)
AD_CONTACT_URL = ""                        # 빈 광고 칸을 눌렀을 때 열리는 주소 (비워 두면 아무 일 없음)
CACHE_DB = os.path.join(APP_DIR, "cache.db")
SETTINGS_FILE = os.path.join(APP_DIR, "settings.json")
MAX_FILE_SIZE = 100 * 1024 * 1024          # 100MB 넘는 문서는 건너뜀
MAX_ARCHIVE_SIZE = 4 * 1024 ** 3           # 압축 파일은 목록만 읽으므로 4GB까지
TMP_DIR = os.path.join(APP_DIR, "tmp")     # 압축 안 파일 미리보기용 임시 폴더
FONT = ("맑은 고딕", 10)


def fsz(n):
    """글꼴 크기: 기준(10) 대비 차이를 환경설정 글꼴 크기에 맞춰 늘리거나 줄임"""
    return max(6, FONT[1] + n - 10)

IMAGE_EXTS = (".jpg", ".jpeg", ".png", ".gif", ".bmp", ".webp", ".tif", ".tiff", ".ico", ".jfif")
ARCHIVE_EXTS = (".zip", ".7z", ".rar", ".tar", ".tgz", ".gz", ".bz2", ".xz", ".alz", ".egg")
SHEET_EXTS = (".xlsx", ".xlsm", ".xls", ".csv", ".tsv")
TYPE_GROUPS = [   # (이름, 확장자, 기본으로 켤지)
    ("한글", (".hwp", ".hwpx"), True),
    ("워드", (".docx", ".doc", ".odt", ".rtf"), True),
    ("엑셀", (".xlsx", ".xlsm", ".xls", ".ods"), True),
    ("파워포인트", (".pptx", ".odp"), True),
    ("PDF", (".pdf",), True),
    ("텍스트", (".txt", ".csv", ".tsv", ".md", ".log", ".html", ".htm", ".xml", ".json",
              ".ini", ".py", ".js", ".css", ".sql", ".eml"), True),
    ("압축파일", ARCHIVE_EXTS, True),
    ("이미지(글자 인식)", IMAGE_EXTS, False),
    ("기타 모든 파일(이름만)", ("*",), False),
]
KNOWN_EXTS = {e for _, ex, _ in TYPE_GROUPS for e in ex if e != "*"}
SKIP_DIRS = {"$recycle.bin", "system volume information", "node_modules", ".git",
             "__pycache__", ".svn", "$windows.~bt", "$windows.~ws"}


# ───────────────────────── 텍스트 추출 ─────────────────────────
TAG_RE = re.compile(r"<[^>]+>")
T_RE = re.compile(r"<(?:\w+:)?t(?:\s[^>]*)?>(.*?)</(?:\w+:)?t>", re.S)
PARA_END_RE = re.compile(r"</(?:\w+:)?(?:p|si)>")


def _num_key(name):
    nums = re.findall(r"\d+", name)
    return int(nums[-1]) if nums else 0


def _xml_runs(xml_bytes):
    """<x:t> 태그 안의 글자를 문단 단위로 모음 (HWPX/DOCX/PPTX/XLSX 공통)"""
    s = xml_bytes.decode("utf-8", "ignore")
    lines = []
    for chunk in PARA_END_RE.split(s):
        ts = T_RE.findall(chunk)
        if ts:
            lines.append(html.unescape("".join(TAG_RE.sub("", t) for t in ts)))
    return "\n".join(lines)


def _zip_text(path, member_re):
    with zipfile.ZipFile(path) as zf:
        names = sorted((n for n in zf.namelist() if re.fullmatch(member_re, n)), key=_num_key)
        return "\n".join(_xml_runs(zf.read(n)) for n in names)


def hwpx_text(path):
    text = _zip_text(path, r"Contents/section\d+\.xml")
    if not text.strip():
        with zipfile.ZipFile(path) as zf:
            if "Preview/PrvText.txt" in zf.namelist():
                text = zf.read("Preview/PrvText.txt").decode("utf-8", "ignore")
    return text


def docx_text(path):
    return _zip_text(path, r"word/(?:document|header\d*|footer\d*|footnotes|endnotes)\.xml")


def pptx_text(path):
    return _zip_text(path, r"ppt/(?:slides/slide\d+|notesSlides/notesSlide\d+)\.xml")


CELL_RE = re.compile(r"<c\b([^>]*?)(?:/>|>(.*?)</c>)", re.S)
V_RE = re.compile(r"<v>(.*?)</v>", re.S)


def xlsx_text(path):
    parts = []
    with zipfile.ZipFile(path) as zf:
        names = zf.namelist()
        if "xl/sharedStrings.xml" in names:
            parts.append(_xml_runs(zf.read("xl/sharedStrings.xml")))
        for n in sorted((n for n in names if re.fullmatch(r"xl/worksheets/sheet\d+\.xml", n)), key=_num_key):
            s = zf.read(n).decode("utf-8", "ignore")
            vals = []
            for attrs, inner in CELL_RE.findall(s):
                if 't="s"' in attrs:          # 공유 문자열은 위에서 이미 넣음
                    continue
                if 't="inlineStr"' in attrs:
                    vals.append("".join(TAG_RE.sub("", t) for t in T_RE.findall(inner)))
                else:
                    m = V_RE.search(inner)
                    if m:
                        vals.append(m.group(1))
            if vals:
                parts.append(html.unescape(" ".join(vals)))
    return "\n".join(parts)


def _hwp_para_text(b):
    """HWP 문단 텍스트(UTF-16LE)에서 제어문자를 걸러냄"""
    out = bytearray()
    n = len(b) // 2
    i = 0
    while i < n:
        c = b[2 * i] | (b[2 * i + 1] << 8)
        if c >= 32:
            out += b[2 * i:2 * i + 2]
            i += 1
        elif c in (0, 10, 13) or 24 <= c <= 31:      # 1글자짜리 제어문자
            if c in (10, 13):
                out += b"\n\x00"
            elif c >= 24:
                out += b" \x00"
            i += 1
        else:                                         # 인라인/확장 제어문자는 8글자 차지
            if c == 9:
                out += b"\t\x00"
            i += 8
    return out.decode("utf-16-le", "ignore").strip("\n")


def _hwp_records(data):
    out = []
    pos, n = 0, len(data)
    while pos + 4 <= n:
        h = struct.unpack_from("<I", data, pos)[0]
        pos += 4
        tag, size = h & 0x3FF, (h >> 20) & 0xFFF
        if size == 0xFFF:
            if pos + 4 > n:
                break
            size = struct.unpack_from("<I", data, pos)[0]
            pos += 4
        if tag == 67:                                 # HWPTAG_PARA_TEXT
            t = _hwp_para_text(data[pos:pos + size])
            if t:
                out.append(t)
        pos += size
    return "\n".join(out)


class OleFile:
    """구형 MS 오피스·HWP가 쓰는 OLE(복합 문서) 파일 읽기 — 외부 패키지 없이 동작"""
    END = 0xFFFFFFFA

    def __init__(self, path):
        with open(path, "rb") as f:
            self.d = d = f.read()
        if d[:8] != b"\xd0\xcf\x11\xe0\xa1\xb1\x1a\xe1":
            raise RuntimeError("OLE 형식이 아님")
        self.ss = 1 << struct.unpack_from("<H", d, 0x1E)[0]
        self.mss = 1 << struct.unpack_from("<H", d, 0x20)[0]
        n_fat, first_dir, _, cutoff, first_mini, n_mini, first_difat, n_difat = \
            struct.unpack_from("<IIIIIIII", d, 0x2C)
        self.cutoff = cutoff
        difat = [x for x in struct.unpack_from("<109I", d, 0x4C)]
        sid, per = first_difat, self.ss // 4 - 1
        for _ in range(n_difat):
            if sid >= self.END:
                break
            vals = struct.unpack_from(f"<{per + 1}I", d, self._off(sid))
            difat.extend(vals[:per])
            sid = vals[per]
        self.fat = []
        for s in difat[:n_fat]:
            if s < self.END:
                self.fat.extend(struct.unpack_from(f"<{self.ss // 4}I", d, self._off(s)))
        dirdata = self._read_chain(first_dir)
        self.entries = []
        for i in range(len(dirdata) // 128):
            e = dirdata[i * 128:(i + 1) * 128]
            nlen = struct.unpack_from("<H", e, 0x40)[0]
            name = e[:max(0, nlen - 2)].decode("utf-16-le", "ignore")
            typ = e[0x42]
            left, right, child = struct.unpack_from("<III", e, 0x44)
            start, size = struct.unpack_from("<II", e, 0x74)
            self.entries.append((name, typ, left, right, child, start, size))
        root = self.entries[0]
        self.ministream = self._read_chain(root[5])[:root[6]]
        self.minifat = []
        if n_mini:
            md = self._read_chain(first_mini)
            self.minifat = list(struct.unpack_from(f"<{len(md) // 4}I", md))
        self.paths = {}
        self._walk(root[4], ())

    def _off(self, sid):
        return (sid + 1) * self.ss

    def _chain(self, start, table):
        seen = set()
        while start < self.END and start < len(table) and start not in seen:
            seen.add(start)
            yield start
            start = table[start]

    def _read_chain(self, start):
        return b"".join(self.d[self._off(s):self._off(s) + self.ss] for s in self._chain(start, self.fat))

    def _walk(self, idx, prefix, depth=0):
        stack, seen = [idx], set()
        while stack:
            i = stack.pop()
            if i >= len(self.entries) or i in seen:
                continue
            seen.add(i)
            name, typ, left, right, child, start, size = self.entries[i]
            stack += [left, right]
            p = prefix + (name,)
            if typ == 2:
                self.paths[p] = i
            elif typ == 1 and depth < 20:
                self._walk(child, p, depth + 1)

    def exists(self, *path):
        return tuple(path) in self.paths

    def listdir(self):
        return list(self.paths)

    def read(self, *path):
        i = self.paths.get(tuple(path))
        if i is None:
            raise KeyError("/".join(path))
        _, _, _, _, _, start, size = self.entries[i]
        if size < self.cutoff:
            m = self.mss
            data = b"".join(self.ministream[s * m:(s + 1) * m] for s in self._chain(start, self.minifat))
        else:
            data = self._read_chain(start)
        return data[:size]


def hwp_text(path):
    ole = OleFile(path)
    header = ole.read("FileHeader")
    flags = struct.unpack_from("<I", header, 36)[0]
    compressed, encrypted, distributed = flags & 1, flags & 2, flags & 4
    texts = []
    if not encrypted and not distributed:
        sections = [p for p in ole.listdir() if len(p) == 2 and p[0] == "BodyText" and p[1].startswith("Section")]
        for p in sorted(sections, key=lambda p: _num_key(p[1])):
            data = ole.read(*p)
            if compressed:
                data = zlib.decompress(data, -15)
            texts.append(_hwp_records(data))
    text = "\n".join(texts)
    if not text.strip() and ole.exists("PrvText"):   # 배포용·암호 문서는 미리보기 텍스트로 대체
        text = ole.read("PrvText").decode("utf-16-le", "ignore")
    return text


def doc_text(path):
    """구형 워드(.doc, 97~2003): 조각 표(piece table)를 따라 본문을 꺼냄"""
    ole = OleFile(path)
    wd = ole.read("WordDocument")
    flags = struct.unpack_from("<H", wd, 0x0A)[0]
    if flags & 0x0100:
        raise RuntimeError("암호가 걸린 DOC")
    table = ole.read("1Table" if flags & 0x0200 else "0Table")
    fc_clx, lcb_clx = struct.unpack_from("<II", wd, 0x1A2)
    clx = table[fc_clx:fc_clx + lcb_clx]
    pos = 0
    while pos < len(clx) and clx[pos] == 1:                     # Prc(서식) 블록 건너뜀
        pos += 3 + struct.unpack_from("<H", clx, pos + 1)[0]
    if pos >= len(clx) or clx[pos] != 2:
        raise RuntimeError("DOC 본문 구조를 찾지 못함")
    lcb = struct.unpack_from("<I", clx, pos + 1)[0]
    plc = clx[pos + 5:pos + 5 + lcb]
    n = (lcb - 4) // 12
    cps = struct.unpack_from(f"<{n + 1}I", plc, 0)
    out = []
    for i in range(n):
        fc = struct.unpack_from("<I", plc, (n + 1) * 4 + i * 8 + 2)[0]
        cnt = cps[i + 1] - cps[i]
        if fc & 0x40000000:
            off = (fc & 0x3FFFFFFF) // 2
            out.append(wd[off:off + cnt].decode("cp1252", "ignore"))
        else:
            out.append(wd[fc:fc + cnt * 2].decode("utf-16-le", "ignore"))
    s = "".join(out)
    s = re.sub(r"\x13[^\x13\x14\x15]*\x14", "", s)              # 필드 코드 제거, 결과값만 남김
    s = s.replace("\r", "\n").replace("\x07", "\t").replace("\x0b", "\n").replace("\x0c", "\n")
    return re.sub(r"[\x00-\x08\x0e-\x1f]", "", s)


def _fmt_num(v):
    return str(int(v)) if v == int(v) and abs(v) < 1e15 else ("%.10g" % v)


def _rk(rk):
    if rk & 2:
        v = rk >> 2
        if v & 0x20000000:
            v -= 0x40000000
        v = float(v)
    else:
        v = struct.unpack("<d", struct.pack("<Q", (rk & 0xFFFFFFFC) << 32))[0]
    return v / 100 if rk & 1 else v


class _Seg:
    """CONTINUE 레코드로 나뉜 데이터를 이어 읽기"""
    def __init__(self, segs):
        self.segs, self.i, self.p = segs, 0, 0

    def _need(self):
        while self.i < len(self.segs) and self.p >= len(self.segs[self.i]):
            self.i += 1
            self.p = 0
        if self.i >= len(self.segs):
            raise EOFError

    def bytes(self, n):
        out = b""
        while n > 0:
            self._need()
            seg = self.segs[self.i]
            k = min(n, len(seg) - self.p)
            out += seg[self.p:self.p + k]
            self.p += k
            n -= k
        return out

    def u16(self):
        return struct.unpack("<H", self.bytes(2))[0]

    def string(self):
        cch = self.u16()
        flags = self.bytes(1)[0]
        runs = self.u16() if flags & 8 else 0
        ext = struct.unpack("<i", self.bytes(4))[0] if flags & 4 else 0
        high, chars = flags & 1, []
        while cch > 0:
            if self.i < len(self.segs) and self.p >= len(self.segs[self.i]):
                self._need()
                high = self.bytes(1)[0] & 1                  # CONTINUE 경계에서 압축 여부 다시 읽음
            self._need()
            avail = len(self.segs[self.i]) - self.p
            k = min(cch, avail // (2 if high else 1)) or cch
            raw = self.bytes(k * (2 if high else 1))
            chars.append(raw.decode("utf-16-le" if high else "latin-1", "ignore"))
            cch -= k
        self.bytes(runs * 4 + max(ext, 0))
        return "".join(chars)


def xls_text(path):
    """구형 엑셀(.xls, 97~2003)"""
    ole = OleFile(path)
    if ole.exists("Workbook"):
        wb = ole.read("Workbook")
    elif ole.exists("Book"):
        raise RuntimeError("Excel 95 이전 형식은 지원하지 않음")
    else:
        raise RuntimeError("XLS 통합문서를 찾지 못함")
    recs, pos = [], 0
    while pos + 4 <= len(wb):
        typ, ln = struct.unpack_from("<HH", wb, pos)
        recs.append((typ, wb[pos + 4:pos + 4 + ln]))
        pos += 4 + ln
    out = []
    i = 0
    while i < len(recs):
        typ, data = recs[i]
        if typ == 0x002F:
            raise RuntimeError("암호가 걸린 XLS")
        if typ == 0x00FC:                                   # SST(공유 문자열)
            segs = [data]
            while i + 1 < len(recs) and recs[i + 1][0] == 0x003C:
                i += 1
                segs.append(recs[i][1])
            r = _Seg(segs)
            r.bytes(4)
            total = struct.unpack("<I", r.bytes(4))[0]
            try:
                for _ in range(total):
                    out.append(r.string())
            except EOFError:
                pass
        elif typ == 0x0203 and len(data) >= 14:            # NUMBER
            out.append(_fmt_num(struct.unpack_from("<d", data, 6)[0]))
        elif typ == 0x027E and len(data) >= 10:            # RK
            out.append(_fmt_num(_rk(struct.unpack_from("<I", data, 6)[0])))
        elif typ == 0x00BD:                                # MULRK
            for k in range((len(data) - 6) // 6):
                out.append(_fmt_num(_rk(struct.unpack_from("<I", data, 4 + k * 6 + 2)[0])))
        elif typ in (0x0204, 0x0207):                      # LABEL, STRING(수식 결과)
            try:
                out.append(_Seg([data[6:] if typ == 0x0204 else data]).string())
            except Exception:
                pass
        i += 1
    return "\n".join(out)


# ───────────── 한글 입력(IME): 조합 중인 글자를 입력칸과 같은 글꼴·크기로 ─────────────
_ime = {}


def _ime_api():
    if "imm" not in _ime:
        import ctypes
        from ctypes import wintypes

        class LOGFONTW(ctypes.Structure):
            _fields_ = [("lfHeight", wintypes.LONG), ("lfWidth", wintypes.LONG),
                        ("lfEscapement", wintypes.LONG), ("lfOrientation", wintypes.LONG),
                        ("lfWeight", wintypes.LONG), ("lfItalic", wintypes.BYTE),
                        ("lfUnderline", wintypes.BYTE), ("lfStrikeOut", wintypes.BYTE),
                        ("lfCharSet", wintypes.BYTE), ("lfOutPrecision", wintypes.BYTE),
                        ("lfClipPrecision", wintypes.BYTE), ("lfQuality", wintypes.BYTE),
                        ("lfPitchAndFamily", wintypes.BYTE), ("lfFaceName", ctypes.c_wchar * 32)]
        u32, imm = ctypes.windll.user32, ctypes.windll.imm32
        u32.GetFocus.restype = ctypes.c_void_p
        imm.ImmGetContext.restype = ctypes.c_void_p
        imm.ImmGetContext.argtypes = [ctypes.c_void_p]
        imm.ImmReleaseContext.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        imm.ImmSetCompositionFontW.argtypes = [ctypes.c_void_p, ctypes.POINTER(LOGFONTW)]
        _ime.update(imm=imm, u32=u32, LOGFONTW=LOGFONTW, ctypes=ctypes)
    return _ime


def ime_match_font(widget):
    """한글을 조합하는 동안 뜨는 IME 조합 창의 글꼴·크기를 입력칸과 똑같이 맞춤.
    안 맞추면 윈도우 기본 글꼴로 크게 떴다가 글자가 완성돼야 칸에 들어가 어색함"""
    if sys.platform != "win32":
        return None
    try:
        from tkinter import font as tkfont
        api = _ime_api()
        hwnd = api["u32"].GetFocus()
        if not hwnd:
            return None
        try:
            spec = widget.cget("font")
        except tk.TclError:
            spec = ""
        act = tkfont.Font(root=widget, font=spec or "TkTextFont").actual()
        size = act["size"]
        px = -size if size < 0 else max(8, round(size * widget.winfo_fpixels("1i") / 72))
        himc = api["imm"].ImmGetContext(hwnd)
        if not himc:
            return None
        try:
            lf = api["LOGFONTW"]()
            lf.lfHeight = -px
            lf.lfWeight = 700 if act.get("weight") == "bold" else 400
            lf.lfCharSet = 129                      # HANGUL_CHARSET
            lf.lfQuality = 5                        # CLEARTYPE_QUALITY
            lf.lfFaceName = act["family"][:31]
            api["imm"].ImmSetCompositionFontW(himc, api["ctypes"].byref(lf))
        finally:
            api["imm"].ImmReleaseContext(hwnd, himc)
        return act["family"], px
    except Exception:
        return None


def install_ime_fix(root):
    """모든 입력칸에서 포커스를 받을 때 IME 조합 창 글꼴을 맞춤"""
    if sys.platform != "win32":
        return

    def on_focus(e):
        w = e.widget
        try:
            w.after_idle(lambda: ime_match_font(w))
        except (tk.TclError, AttributeError):
            pass
    for cls in ("TEntry", "Entry", "Text", "TSpinbox", "TCombobox", "Spinbox"):
        root.bind_class(cls, "<FocusIn>", on_focus, add="+")


# ───────────── PDF + 스캔 PDF 글자 인식(OCR, 윈도우 내장) ─────────────
class StopSearch(Exception):
    pass


_ocr = {"engine": None, "error": None, "tried": False, "no_korean": False}
_ocr_lock = threading.Lock()      # 여러 칸에서 동시에 검색해도 OCR은 한 번에 하나씩


def ocr_engine(recheck=False):
    if recheck:                          # 한국어 OCR을 막 설치했으면 다시 확인
        _ocr.update(engine=None, error=None, tried=False, no_korean=False)
    if not _ocr["tried"]:
        _ocr["tried"] = True
        try:
            from winrt.windows.media.ocr import OcrEngine
            from winrt.windows.globalization import Language
            eng = OcrEngine.try_create_from_language(Language("ko"))
            if eng is None:
                _ocr["no_korean"] = True           # 한국어 OCR 미설치 → 설치 안내 창
                _ocr["error"] = "윈도우 한국어 OCR이 설치되어 있지 않음"
                # 영어 OCR로 한글을 읽으면 엉뚱한 글자가 저장되므로, 한국어 OCR을 설치할 때까지 미룸
            if eng is None:
                raise RuntimeError("윈도우 한국어 OCR이 설치되어 있지 않음")
            _ocr["engine"] = eng
        except Exception as e:
            _ocr["error"] = f"OCR을 쓸 수 없음 ({e})"
    return _ocr["engine"]


def ocr_bgra(bgra, w, h):
    import asyncio
    from winrt.windows.graphics.imaging import SoftwareBitmap, BitmapPixelFormat, BitmapAlphaMode
    from winrt.windows.storage.streams import DataWriter, Buffer

    def make_buffer():
        try:
            dw = DataWriter()
            dw.write_bytes(bgra)
            return dw.detach_buffer()
        except TypeError:                   # winrt 버전에 따라 bytes를 바로 못 받을 때
            buf = Buffer(len(bgra))
            buf.length = len(bgra)
            memoryview(buf)[:] = bgra
            return buf

    async def run():
        bmp = SoftwareBitmap.create_copy_from_buffer(make_buffer(), BitmapPixelFormat.BGRA8,
                                                     w, h, BitmapAlphaMode.PREMULTIPLIED)
        res = await _ocr["engine"].recognize_async(bmp)
        return "\n".join(line.text for line in res.lines)
    with _ocr_lock:
        return asyncio.run(run())


def pdf_text(path, ocr=False, progress=None, stop=None):
    """반환: (텍스트, OCR이 필요했지만 못 한 쪽이 있는지)"""
    if pdfium is None:
        if PdfReader is None:
            raise RuntimeError("PDF 읽기 패키지(pypdfium2)가 없음")
        r = PdfReader(path)
        if r.is_encrypted:
            r.decrypt("")
        return "\n".join((p.extract_text() or "") for p in r.pages), False
    try:
        doc = pdfium.PdfDocument(path)
    except pdfium.PdfiumError as e:
        raise RuntimeError(f"PDF를 열 수 없음(암호 등): {e}")
    texts, pending = [], False
    try:
        n = len(doc)
        for i in range(n):
            page = doc[i]
            tp = page.get_textpage()
            t = tp.get_text_range()
            tp.close()
            if len(t.strip()) < 15:                         # 글자가 거의 없는 쪽 = 스캔 이미지로 판단
                if ocr and ocr_engine() is not None:
                    if stop is not None and stop.is_set():
                        raise StopSearch()
                    if progress:
                        progress(f"{path}  [글자 인식 {i + 1}/{n}쪽]")
                    w, h = page.get_size()
                    maxdim = getattr(_ocr["engine"], "max_image_dimension", 4000) or 4000
                    scale = max(0.5, min(2.5, (maxdim - 10) / max(w, h, 1)))
                    bmp = page.render(scale=scale, force_bitmap_format=pdfium_c.FPDFBitmap_BGRA,
                                      may_draw_forms=True)
                    bw, bh, stride = bmp.width, bmp.height, bmp.stride
                    raw = bytes(bmp.buffer)
                    if stride != bw * 4:
                        raw = b"".join(raw[r * stride:r * stride + bw * 4] for r in range(bh))
                    bmp.close()
                    t = ocr_bgra(raw, bw, bh)
                else:
                    pending = True
            page.close()
            texts.append(t)
    finally:
        doc.close()
    return "\n".join(texts), pending


def plain_text(path):
    with open(path, "rb") as f:
        b = f.read(20 * 1024 * 1024)
    if b.startswith(codecs.BOM_UTF16_LE) or b.startswith(codecs.BOM_UTF16_BE):
        s = b.decode("utf-16", "ignore")
    else:
        for enc in ("utf-8-sig", "cp949"):
            try:
                s = b.decode(enc)
                break
            except UnicodeDecodeError:
                continue
        else:
            s = b.decode("utf-8", "ignore")
    if path.lower().endswith((".html", ".htm", ".xml")):
        s = html.unescape(TAG_RE.sub(" ", s))
    return s


def odf_text(path):
    """오픈오피스·리브레오피스 문서(.odt .ods .odp)"""
    with zipfile.ZipFile(path) as zf:
        s = zf.read("content.xml").decode("utf-8", "ignore")
    s = re.sub(r"</text:(?:p|h)>|<text:line-break/>|</table:table-cell>", "\n", s)
    s = re.sub(r"<text:tab/>", "\t", s)
    s = re.sub(r'<text:s(?: text:c="(\d+)")?/>', lambda m: " " * int(m.group(1) or 1), s)
    return html.unescape(TAG_RE.sub("", s))


def rtf_text(path):
    with open(path, "rb") as f:
        raw = f.read(30 * 1024 * 1024).decode("latin-1")
    m = re.search(r"\\ansicpg(\d+)", raw)
    cp = "cp" + (m.group(1) if m else "949")
    try:
        codecs.lookup(cp)
    except LookupError:
        cp = "cp949"
    out, hexbuf, depth, skip_depth = [], bytearray(), 0, None

    def flush():
        if hexbuf:
            out.append(hexbuf.decode(cp, "ignore"))
            hexbuf.clear()
    tok = re.compile(r"\\'([0-9a-fA-F]{2})|\\u(-?\d+) ?\??|\\([a-zA-Z]+)(-?\d+)? ?|\\(.)|([{}])|([^\\{}\r\n]+)|[\r\n]+")
    for mt in tok.finditer(raw):
        hx, uni, word, _, sym, brace, txt = mt.groups()
        if brace == "{":
            depth += 1
            continue
        if brace == "}":
            flush()
            if skip_depth is not None and depth <= skip_depth:
                skip_depth = None
            depth -= 1
            continue
        if skip_depth is not None:
            continue
        if hx:
            hexbuf.append(int(hx, 16))
            continue
        flush()
        if uni:
            out.append(chr(int(uni) % 65536))
        elif word:
            if word in ("fonttbl", "colortbl", "stylesheet", "info", "pict", "object", "header", "footer"):
                skip_depth = depth
            elif word in ("par", "line", "row"):
                out.append("\n")
            elif word in ("tab", "cell"):
                out.append("\t")
        elif sym == "*":
            skip_depth = depth
        elif sym and sym in "\\{}":
            out.append(sym)
        elif txt:
            out.append(txt)
    flush()
    return "".join(out)


def eml_text(path):
    import email
    from email import policy
    with open(path, "rb") as f:
        msg = email.message_from_binary_file(f, policy=policy.default)
    out = [f"{k}: {msg.get(k, '')}" for k in ("From", "To", "Cc", "Subject", "Date") if msg.get(k)]
    for part in msg.walk():
        if part.get_content_maintype() == "multipart":
            continue
        fn = part.get_filename()
        if fn:
            out.append(f"[첨부] {fn}")
            continue
        if part.get_content_type() in ("text/plain", "text/html"):
            try:
                t = part.get_content()
            except Exception:
                t = (part.get_payload(decode=True) or b"").decode("cp949", "ignore")
            if part.get_content_type() == "text/html":
                t = html.unescape(TAG_RE.sub(" ", t))
            out.append(t)
    return "\n".join(out)


# ───────────── 표 형태로 읽기 (엑셀·CSV 미리보기용) ─────────────
GRID_ROWS, GRID_COLS = 1000, 60


def _col_index(ref):
    n = 0
    for ch in ref:
        if "A" <= ch <= "Z":
            n = n * 26 + ord(ch) - 64
        else:
            break
    return n - 1


def xlsx_sheets(path):
    """[(시트 이름, {(행, 열): 값})] — 시트마다 앞부분만"""
    with zipfile.ZipFile(path) as zf:
        names = set(zf.namelist())
        sst = []
        if "xl/sharedStrings.xml" in names:
            s = zf.read("xl/sharedStrings.xml").decode("utf-8", "ignore")
            for si in re.findall(r"<si>(.*?)</si>", s, re.S):
                sst.append(html.unescape("".join(TAG_RE.sub("", t) for t in T_RE.findall(si))))
        rels = {}
        if "xl/_rels/workbook.xml.rels" in names:
            r = zf.read("xl/_rels/workbook.xml.rels").decode("utf-8", "ignore")
            for rel in re.findall(r"<Relationship\b[^>]*>", r):
                i = re.search(r'Id="([^"]+)"', rel)
                t = re.search(r'Target="([^"]+)"', rel)
                if i and t:
                    tgt = t.group(1).lstrip("/")
                    rels[i.group(1)] = tgt if tgt.startswith("xl/") else "xl/" + tgt
        sheets = []
        wb = zf.read("xl/workbook.xml").decode("utf-8", "ignore") if "xl/workbook.xml" in names else ""
        for tag in re.findall(r"<sheet\b[^>]*>", wb):
            nm = re.search(r'name="([^"]*)"', tag)
            rid = re.search(r'r:id="([^"]+)"', tag) or re.search(r'\bid="([^"]+)"', tag)
            if nm and rid and rels.get(rid.group(1)) in names:
                sheets.append((html.unescape(nm.group(1)), rels[rid.group(1)]))
        if not sheets:
            sheets = [(os.path.basename(n), n) for n in sorted(names, key=_num_key)
                      if re.fullmatch(r"xl/worksheets/sheet\d+\.xml", n)]
        out = []
        for nm, member in sheets[:30]:
            s = zf.read(member).decode("utf-8", "ignore")
            cells = {}
            for attrs, inner in CELL_RE.findall(s):
                ref = re.search(r'\br="([A-Z]+)(\d+)"', attrs)
                if not ref or not inner:
                    continue
                row, col = int(ref.group(2)) - 1, _col_index(ref.group(1))
                if row >= GRID_ROWS:
                    break
                if col >= GRID_COLS:
                    continue
                t = re.search(r'\bt="(\w+)"', attrs)
                t = t.group(1) if t else "n"
                if t == "inlineStr":
                    val = "".join(TAG_RE.sub("", x) for x in T_RE.findall(inner))
                else:
                    v = V_RE.search(inner)
                    if not v:
                        continue
                    val = v.group(1)
                    if t == "s":
                        try:
                            val = sst[int(val)]
                        except (ValueError, IndexError):
                            pass
                    elif t == "b":
                        val = "TRUE" if val == "1" else "FALSE"
                    elif t == "n":
                        try:
                            val = _fmt_num(float(val))
                        except ValueError:
                            pass
                cells[(row, col)] = html.unescape(val)
            out.append((nm, cells))
        return out


def xls_sheets(path):
    ole = OleFile(path)
    if not ole.exists("Workbook"):
        raise RuntimeError("XLS 통합문서를 찾지 못함")
    wb = ole.read("Workbook")
    recs, pos = [], 0
    while pos + 4 <= len(wb):
        typ, ln = struct.unpack_from("<HH", wb, pos)
        recs.append((pos, typ, wb[pos + 4:pos + 4 + ln]))
        pos += 4 + ln
    sst, bounds = [], {}
    i = 0
    while i < len(recs):
        _, typ, data = recs[i]
        if typ == 0x002F:
            raise RuntimeError("암호가 걸린 XLS")
        if typ == 0x0085 and len(data) >= 8:              # BOUNDSHEET(시트 이름)
            off, dt = struct.unpack_from("<I", data, 0)[0], data[5]
            cch, flags = data[6], data[7]
            name = data[8:8 + cch * 2].decode("utf-16-le", "ignore") if flags & 1 else \
                data[8:8 + cch].decode("latin-1")
            if dt == 0:
                bounds[off] = name
        elif typ == 0x00FC:
            segs = [data]
            while i + 1 < len(recs) and recs[i + 1][1] == 0x003C:
                i += 1
                segs.append(recs[i][2])
            r = _Seg(segs)
            r.bytes(4)
            total = struct.unpack("<I", r.bytes(4))[0]
            try:
                for _ in range(total):
                    sst.append(r.string())
            except EOFError:
                pass
        i += 1
    out, cells, pending_formula = [], None, None
    for off, typ, data in recs:
        if typ == 0x0809:
            if off in bounds:
                cells = {}
                out.append((bounds[off], cells))
            else:
                cells = None
            continue
        if cells is None:
            continue
        if typ == 0x000A:
            cells = None
            continue
        try:
            if typ == 0x0207 and pending_formula:        # 바로 앞 수식의 문자열 결과
                cells[pending_formula] = _Seg([data]).string()
                pending_formula = None
                continue
            pending_formula = None
            if len(data) < 6:
                continue
            row, col = struct.unpack_from("<HH", data, 0)
            if row >= GRID_ROWS:
                continue
            if typ == 0x00BD:                            # MULRK
                for k in range((len(data) - 6) // 6):
                    c = col + k
                    if c < GRID_COLS:
                        cells[(row, c)] = _fmt_num(_rk(struct.unpack_from("<I", data, 4 + k * 6 + 2)[0]))
                continue
            if col >= GRID_COLS:
                continue
            if typ == 0x00FD:                            # LABELSST
                idx = struct.unpack_from("<I", data, 6)[0]
                cells[(row, col)] = sst[idx] if idx < len(sst) else ""
            elif typ == 0x0203:
                cells[(row, col)] = _fmt_num(struct.unpack_from("<d", data, 6)[0])
            elif typ == 0x027E:
                cells[(row, col)] = _fmt_num(_rk(struct.unpack_from("<I", data, 6)[0]))
            elif typ == 0x0204:
                cells[(row, col)] = _Seg([data[6:]]).string()
            elif typ == 0x0205:
                cells[(row, col)] = ("TRUE" if data[6] else "FALSE") if data[7] == 0 else "#오류"
            elif typ == 0x0006 and len(data) >= 14:      # FORMULA
                if data[12:14] == b"\xff\xff":
                    if data[6] == 0:
                        pending_formula = (row, col)
                    elif data[6] == 1:
                        cells[(row, col)] = "TRUE" if data[8] else "FALSE"
                else:
                    cells[(row, col)] = _fmt_num(struct.unpack_from("<d", data, 6)[0])
        except Exception:
            continue
    return out


def csv_sheets(path):
    text = plain_text(path)
    sample = text[:5000]
    delim = "\t" if path.lower().endswith(".tsv") or sample.count("\t") > sample.count(",") else ","
    cells = {}
    for r, row in enumerate(csv.reader(io.StringIO(text), delimiter=delim)):
        if r >= GRID_ROWS:
            break
        for c, v in enumerate(row[:GRID_COLS]):
            if v != "":
                cells[(r, c)] = v
    return [(os.path.basename(path), cells)]


def read_sheets(path):
    ext = os.path.splitext(path)[1].lower()
    if ext in (".xlsx", ".xlsm"):
        return xlsx_sheets(path)
    if ext == ".xls":
        return xls_sheets(path)
    return csv_sheets(path)


# ───────────── 문서 속 미리보기 그림(한글·오피스가 저장해 둔 첫 쪽 그림) ─────────────
def embedded_thumbnail(path):
    ext = os.path.splitext(path)[1].lower()
    try:
        if ext == ".hwp":
            ole = OleFile(path)
            return ole.read("PrvImage") if ole.exists("PrvImage") else None
        if zipfile.is_zipfile(path):
            with zipfile.ZipFile(path) as zf:
                names = zf.namelist()
                for n in ("Preview/PrvImage.png", "docProps/thumbnail.jpeg", "docProps/thumbnail.jpg",
                          "docProps/thumbnail.png", "Thumbnails/thumbnail.png"):
                    if n in names:
                        return zf.read(n)
    except Exception:
        return None
    return None


# ───────────── 이미지 (미리보기 + 글자 인식) ─────────────
def image_text(path, ocr=False, progress=None, stop=None):
    if not ocr or Image is None or ocr_engine() is None:
        return "", True                                   # 아직 글자 인식 안 함
    if stop is not None and stop.is_set():
        raise StopSearch()
    if progress:
        progress(f"{path}  [그림 글자 인식]")
    im = Image.open(path)
    im = ImageOps.exif_transpose(im)
    w, h = im.size
    if min(w, h) < 40:
        return "", False
    maxdim = getattr(_ocr["engine"], "max_image_dimension", 4000) or 4000
    scale = min(2.0 if max(w, h) < 1200 else 1.0, (maxdim - 10) / max(w, h))
    if scale != 1.0:
        im = im.resize((max(1, int(w * scale)), max(1, int(h * scale))))
    im = im.convert("RGBA")
    return ocr_bgra(im.tobytes("raw", "BGRA"), im.width, im.height), False


# ───────────── 압축 파일 (목록 보기 + 안에 든 문서까지 검색) ─────────────
ARCHIVE_INNER_LIMIT = 300 * 1024 * 1024     # 압축 안 문서를 읽을 때 풀어 볼 최대 크기
ARCHIVE_INNER_FILES = 300


def _zip_name(info):
    if info.flag_bits & 0x800:
        return info.filename
    try:
        raw = info.filename.encode("cp437")
    except UnicodeEncodeError:
        return info.filename
    for enc in ("utf-8", "cp949"):        # 맥에서 만든 압축은 UTF-8, 윈도우는 CP949
        try:
            return raw.decode(enc)
        except UnicodeDecodeError:
            continue
    return info.filename


def _single_name(path):
    base = os.path.basename(path)
    return os.path.splitext(base)[0] or base


def archive_kind(path):
    ext = os.path.splitext(path)[1].lower()
    if ext == ".zip" or (ext not in (".7z", ".rar") and zipfile.is_zipfile(path)):
        return "zip"
    if ext == ".7z":
        return "7z"
    if ext == ".rar":
        return "rar"
    if ext in (".tar", ".tgz", ".gz", ".bz2", ".xz"):
        try:
            if tarfile.is_tarfile(path):
                return "tar"
        except Exception:
            pass
        return {".gz": "gz", ".bz2": "bz2", ".xz": "xz"}.get(ext, "tar")
    return "other"


def archive_entries(path):
    """[{name, size, mtime, dir, enc}] 와 오류 메시지"""
    kind = archive_kind(path)
    out = []
    if kind == "zip":
        with zipfile.ZipFile(path) as zf:
            for i in zf.infolist():
                out.append({"name": _zip_name(i), "size": i.file_size, "dir": i.is_dir(),
                            "enc": bool(i.flag_bits & 1), "key": i.filename,
                            "mtime": "%04d-%02d-%02d %02d:%02d" % i.date_time[:5]})
    elif kind == "tar":
        with tarfile.open(path) as tf:
            for m in tf.getmembers():
                out.append({"name": m.name, "size": m.size, "dir": m.isdir(), "enc": False, "key": m.name,
                            "mtime": datetime.fromtimestamp(m.mtime).strftime("%Y-%m-%d %H:%M")})
    elif kind in ("gz", "bz2", "xz"):
        out.append({"name": _single_name(path), "size": 0, "dir": False, "enc": False, "key": "",
                    "mtime": ""})
    elif kind == "7z":
        if py7zr is None:
            raise RuntimeError("7z 목록을 보려면 py7zr 패키지가 필요함")
        with py7zr.SevenZipFile(path, "r") as z:
            for i in z.list():
                mt = getattr(i, "creationtime", None)
                out.append({"name": i.filename, "size": i.uncompressed or 0, "dir": i.is_directory,
                            "enc": False, "key": i.filename,
                            "mtime": mt.strftime("%Y-%m-%d %H:%M") if mt else ""})
    elif kind == "rar":
        if rarfile is None:
            raise RuntimeError("RAR 목록을 보려면 rarfile 패키지가 필요함")
        with rarfile.RarFile(path) as rf:
            for i in rf.infolist():
                out.append({"name": i.filename, "size": i.file_size, "dir": i.is_dir(),
                            "enc": bool(getattr(i, "needs_password", lambda: False)()), "key": i.filename,
                            "mtime": "%04d-%02d-%02d %02d:%02d" % tuple(i.date_time[:5]) if i.date_time else ""})
    else:
        raise RuntimeError("이 압축 형식(ALZ·EGG 등)은 목록을 읽을 수 없음 — 반디집 등으로 열어 주세요")
    return out


def _safe_target(dest, name):
    base = os.path.basename(name.replace("\\", "/")) or "file"
    base = re.sub(r'[<>:"|?*\x00-\x1f]', "_", base)
    return os.path.join(dest, base)


def archive_extract(path, entry, dest):
    """압축 안 파일 하나를 dest 폴더에 풀고 그 경로를 돌려줌"""
    os.makedirs(dest, exist_ok=True)
    target = _safe_target(dest, entry["name"])
    kind = archive_kind(path)
    if kind == "zip":
        with zipfile.ZipFile(path) as zf, zf.open(entry["key"]) as src, open(target, "wb") as dst:
            shutil.copyfileobj(src, dst)
    elif kind == "tar":
        with tarfile.open(path) as tf:
            src = tf.extractfile(entry["key"])
            if src is None:
                raise RuntimeError("파일이 아님")
            with open(target, "wb") as dst:
                shutil.copyfileobj(src, dst)
    elif kind in ("gz", "bz2", "xz"):
        opener = {"gz": gzip.open, "bz2": bz2.open, "xz": lzma.open}[kind]
        with opener(path, "rb") as src, open(target, "wb") as dst:
            shutil.copyfileobj(src, dst)
    elif kind == "7z":
        tmp = tempfile.mkdtemp(dir=dest)
        with py7zr.SevenZipFile(path, "r") as z:
            z.extract(path=tmp, targets=[entry["key"]])
        src = os.path.join(tmp, *entry["key"].replace("\\", "/").split("/"))
        shutil.move(src, target)
        shutil.rmtree(tmp, ignore_errors=True)
    elif kind == "rar":
        with rarfile.RarFile(path) as rf, rf.open(entry["key"]) as src, open(target, "wb") as dst:
            shutil.copyfileobj(src, dst)
    else:
        raise RuntimeError("풀 수 없는 형식")
    return target


def archive_text(path, ocr=False, progress=None, stop=None):
    """파일 목록 + 안에 든 문서들의 글자. '■ 파일이름' 줄로 구분"""
    entries = archive_entries(path)
    files = [e for e in entries if not e["dir"]]
    parts = ["■ (압축 파일 목록)\n" + "\n".join(e["name"] for e in files)]
    readable = [e for e in files if not e["enc"]
                and os.path.splitext(e["name"])[1].lower() in KNOWN_EXTS
                and os.path.splitext(e["name"])[1].lower() not in ARCHIVE_EXTS + IMAGE_EXTS
                and (e["size"] or 0) <= MAX_FILE_SIZE]
    total = sum(e["size"] or 0 for e in readable)
    if not readable or total > ARCHIVE_INNER_LIMIT:
        return "\n".join(parts), False
    os.makedirs(TMP_DIR, exist_ok=True)
    work = tempfile.mkdtemp(dir=TMP_DIR)
    try:
        for n, e in enumerate(readable[:ARCHIVE_INNER_FILES]):
            if stop is not None and stop.is_set():
                raise StopSearch()
            if progress and n % 5 == 0:
                progress(f"{path}  [압축 안 {n + 1}/{len(readable)}]")
            try:
                f = archive_extract(path, e, os.path.join(work, str(n)))
                t, _ = extract_text(f, nested=True)
                if t.strip():
                    parts.append(f"■ {e['name']}\n{t}")
            except StopSearch:
                raise
            except Exception:
                continue
    finally:
        shutil.rmtree(work, ignore_errors=True)
    return "\n".join(parts), False


def archive_section(text, pos):
    """압축 파일 글자에서 pos 위치가 속한 '■ 파일이름'"""
    k = text.rfind("■ ", 0, pos + 1)
    while k > 0 and text[k - 1] != "\n":
        k = text.rfind("■ ", 0, k)
    if k < 0:
        return ""
    return text[k + 2:text.find("\n", k) if text.find("\n", k) >= 0 else len(text)]


def generic_text(path):
    """모르는 형식: 앞부분이 글자처럼 보이면 텍스트로 읽음"""
    with open(path, "rb") as f:
        head = f.read(4096)
    if b"\x00" in head and not head.startswith((codecs.BOM_UTF16_LE, codecs.BOM_UTF16_BE)):
        return None
    return plain_text(path)


EXTRACTORS = {".hwp": hwp_text, ".hwpx": hwpx_text, ".docx": docx_text, ".doc": doc_text,
              ".xlsx": xlsx_text, ".xlsm": xlsx_text, ".xls": xls_text, ".pptx": pptx_text,
              ".odt": odf_text, ".ods": odf_text, ".odp": odf_text, ".rtf": rtf_text, ".eml": eml_text}


def extract_text(path, ocr=False, progress=None, stop=None, nested=False):
    """반환: (텍스트, OCR 대기 여부). nested=True면 압축 안 파일(다시 압축·그림은 안 읽음)"""
    ext = os.path.splitext(path)[1].lower()
    if ext == ".pdf":
        return pdf_text(path, ocr and not nested, progress, stop)
    if ext in IMAGE_EXTS:
        return ("", False) if nested else image_text(path, ocr, progress, stop)
    if ext in ARCHIVE_EXTS:
        return ("", False) if nested else archive_text(path, ocr, progress, stop)
    if ext in EXTRACTORS:
        return EXTRACTORS[ext](path), False
    t = generic_text(path)
    return (t or ""), False


# ───────────── 인터넷 연결 (파이썬 방식 → 안 되면 윈도우 방식) ─────────────
# 회사·기관 PC는 프록시(자동 구성 스크립트)나 보안 프로그램의 인증서 때문에 파이썬 방식(urllib)이
# "urlopen error"로 실패하는 일이 많음. 그때는 인터넷 익스플로러·엣지와 같은 윈도우 설정(WinINet)으로 다시 시도.
_WININET_ERRORS = {
    12002: "응답 시간 초과", 12007: "인터넷 주소를 찾지 못함(DNS)", 12029: "서버에 연결할 수 없음(방화벽·차단)",
    12030: "연결이 끊어짐", 12031: "연결이 초기화됨", 12037: "보안 인증서 날짜 문제", 12038: "보안 인증서 이름 문제",
    12044: "클라이언트 인증서 필요", 12045: "신뢰할 수 없는 보안 인증서", 12057: "인증서 해지 확인 실패",
    12157: "보안 연결(SSL) 실패", 12175: "보안 인증서 오류",
}


class NetHTTPError(Exception):
    def __init__(self, code):
        super().__init__(f"HTTP {code}")
        self.code = code


def _wininet_request(url, method, headers, data, limit, timeout):
    import ctypes
    from ctypes import wintypes
    from urllib.parse import urlsplit
    wi = ctypes.WinDLL("wininet", use_last_error=True)
    H = ctypes.c_void_p
    wi.InternetOpenW.restype = H
    wi.InternetOpenW.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, wintypes.LPCWSTR, wintypes.LPCWSTR, wintypes.DWORD]
    wi.InternetConnectW.restype = H
    wi.InternetConnectW.argtypes = [H, wintypes.LPCWSTR, wintypes.WORD, wintypes.LPCWSTR, wintypes.LPCWSTR,
                                    wintypes.DWORD, wintypes.DWORD, ctypes.c_size_t]
    wi.HttpOpenRequestW.restype = H
    wi.HttpOpenRequestW.argtypes = [H, wintypes.LPCWSTR, wintypes.LPCWSTR, wintypes.LPCWSTR, wintypes.LPCWSTR,
                                    ctypes.c_void_p, wintypes.DWORD, ctypes.c_size_t]
    wi.HttpSendRequestW.restype = wintypes.BOOL
    wi.HttpSendRequestW.argtypes = [H, wintypes.LPCWSTR, wintypes.DWORD, ctypes.c_void_p, wintypes.DWORD]
    wi.HttpQueryInfoW.restype = wintypes.BOOL
    wi.HttpQueryInfoW.argtypes = [H, wintypes.DWORD, ctypes.c_void_p, ctypes.POINTER(wintypes.DWORD),
                                  ctypes.POINTER(wintypes.DWORD)]
    wi.InternetReadFile.restype = wintypes.BOOL
    wi.InternetReadFile.argtypes = [H, ctypes.c_void_p, wintypes.DWORD, ctypes.POINTER(wintypes.DWORD)]
    wi.InternetSetOptionW.restype = wintypes.BOOL
    wi.InternetSetOptionW.argtypes = [H, wintypes.DWORD, ctypes.c_void_p, wintypes.DWORD]
    wi.InternetCloseHandle.argtypes = [H]

    def fail(what):
        code = ctypes.get_last_error()
        raise OSError(f"{what}: {_WININET_ERRORS.get(code, '윈도우 오류')} ({code})")

    headers = dict(headers or {})
    ua = headers.pop("User-Agent", "Mozilla/5.0")
    sp = urlsplit(url)
    https = sp.scheme == "https"
    path = (sp.path or "/") + ("?" + sp.query if sp.query else "")
    handles = []
    try:
        h = wi.InternetOpenW(ua, 0, None, None, 0)          # 0 = 윈도우 인터넷 설정(프록시 포함) 그대로
        if not h:
            fail("인터넷 시작 실패")
        handles.append(h)
        ms = wintypes.DWORD(int(timeout * 1000))
        for opt in (2, 5, 6):                               # 연결·보내기·받기 시간 제한
            wi.InternetSetOptionW(h, opt, ctypes.byref(ms), 4)
        c = wi.InternetConnectW(h, sp.hostname, sp.port or (443 if https else 80), None, None, 3, 0, 0)
        if not c:
            fail("연결 실패")
        handles.append(c)
        flags = 0x80000000 | 0x04000000 | 0x00000200 | (0x00800000 if https else 0)   # 새로 받기·캐시 안 씀·창 없음·SSL
        r = wi.HttpOpenRequestW(c, method, path, None, None, None, flags, 0)
        if not r:
            fail("요청 실패")
        handles.append(r)
        hdr = "".join(f"{k}: {v}\r\n" for k, v in headers.items())
        body = data or b""
        buf = ctypes.create_string_buffer(body, len(body)) if body else None
        if not wi.HttpSendRequestW(r, hdr or None, len(hdr), buf, len(body)):
            fail("보내기 실패")
        status, n = wintypes.DWORD(0), wintypes.DWORD(4)
        if wi.HttpQueryInfoW(r, 19 | 0x20000000, ctypes.byref(status), ctypes.byref(n), None) and status.value >= 400:
            raise NetHTTPError(status.value)
        out = bytearray()
        chunk = ctypes.create_string_buffer(65536)
        got = wintypes.DWORD(0)
        while len(out) <= limit:
            if not wi.InternetReadFile(r, chunk, 65536, ctypes.byref(got)):
                fail("받기 실패")
            if got.value == 0:
                break
            out += chunk.raw[:got.value]
        return bytes(out)
    finally:
        for x in reversed(handles):
            wi.InternetCloseHandle(x)


def net_request(url, method="GET", headers=None, data=None, limit=2 * 1024 * 1024, timeout=10):
    """인터넷에서 받기(또는 보내기) → 받은 내용(bytes). 서버가 오류(4xx·5xx)를 주면 NetHTTPError"""
    import urllib.request
    import urllib.error
    try:
        req = urllib.request.Request(url, data=data, method=method, headers=dict(headers or {}))
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.read(limit + 1)
    except urllib.error.HTTPError as e:
        raise NetHTTPError(e.code)
    except Exception as e1:
        if sys.platform != "win32":
            raise
        try:
            return _wininet_request(url, method, headers, data, limit, timeout)
        except NetHTTPError:
            raise
        except Exception as e2:
            raise OSError(f"{e2}  [기본 방식: {str(e1)[:80]}]")


def net_error_text(e):
    """사용자에게 보여 줄 짧은 설명"""
    if isinstance(e, NetHTTPError):
        if e.code == 403:
            return "확인 횟수 제한(잠시 뒤 다시 시도)"
        if e.code == 404:
            return "릴리스를 찾지 못함"
        return f"서버 오류 (HTTP {e.code})"
    return str(e)[:220]


# ───────────────────────── 캐시(한 번 읽은 파일은 다시 안 읽음) ─────────────────────────
class Cache:
    def __init__(self, path):
        self.con = sqlite3.connect(path, check_same_thread=False)
        self.con.execute("CREATE TABLE IF NOT EXISTS docs(path TEXT PRIMARY KEY, mtime REAL, "
                         "size INTEGER, text BLOB, err TEXT)")
        cols = [r[1] for r in self.con.execute("PRAGMA table_info(docs)")]
        if "pend" not in cols:   # 1 = 스캔 PDF인데 아직 글자 인식을 안 한 상태
            self.con.execute("ALTER TABLE docs ADD COLUMN pend INTEGER DEFAULT 0")
            self.con.commit()
        self.lock = threading.Lock()

    @staticmethod
    def key(path):
        """같은 파일은 대소문자·슬래시 모양이 달라도 같은 기록을 쓰게"""
        return os.path.normcase(os.path.abspath(path))

    def get(self, path, mtime, size, ocr=False):
        with self.lock:
            row = self.con.execute("SELECT mtime, size, text, err, pend FROM docs WHERE path=?",
                                   (self.key(path),)).fetchone()
        if row and row[0] == mtime and row[1] == size and not (ocr and row[4]):
            return zlib.decompress(row[2]).decode("utf-8", "ignore"), row[3]
        return None

    def get_any(self, path):
        with self.lock:
            row = self.con.execute("SELECT text FROM docs WHERE path=?", (self.key(path),)).fetchone()
        return zlib.decompress(row[0]).decode("utf-8", "ignore") if row else None

    def put(self, path, mtime, size, text, err, pend=False):
        blob = zlib.compress(text.encode("utf-8", "ignore"), 6)
        with self.lock:
            self.con.execute("INSERT OR REPLACE INTO docs(path, mtime, size, text, err, pend) VALUES(?,?,?,?,?,?)",
                             (self.key(path), mtime, size, blob, err, 1 if pend else 0))

    def fresh(self, path, mtime, size):
        """이미 최신 내용이 저장돼 있으면 True (색인할 때 다시 읽지 않으려고)"""
        with self.lock:
            row = self.con.execute("SELECT mtime, size, pend FROM docs WHERE path=?", (self.key(path),)).fetchone()
        return bool(row) and row[0] == mtime and row[1] == size and not row[2]

    def forget_missing(self, folder, seen):
        """folder 아래에서 이번에 보지 못한(지워진) 파일 기록을 지움"""
        prefix = self.key(folder).rstrip("\\/") + os.sep
        with self.lock:
            rows = self.con.execute("SELECT path FROM docs WHERE substr(path, 1, ?) = ?",
                                    (len(prefix), prefix)).fetchall()
            gone = [(p,) for (p,) in rows if p not in seen]
            if gone:
                self.con.executemany("DELETE FROM docs WHERE path=?", gone)
                self.con.commit()
        return len(gone)

    def sigs_many(self, keys):
        """여러 파일의 (수정시각, 크기, 글자인식 대기) — 내용은 꺼내지 않아 가벼움"""
        out = {}
        keys = list(keys)
        with self.lock:
            for i in range(0, len(keys), 400):
                part = keys[i:i + 400]
                q = "SELECT path, mtime, size, pend FROM docs WHERE path IN (%s)" % ",".join("?" * len(part))
                for path, mtime, size, pend in self.con.execute(q, part):
                    out[path] = (mtime, size, pend)
        return out

    def get_many(self, keys):
        """여러 파일 기록을 한 번에: {key: (mtime, size, text_blob, err, pend)}"""
        out = {}
        keys = list(keys)
        with self.lock:
            for i in range(0, len(keys), 400):
                part = keys[i:i + 400]
                q = "SELECT path, mtime, size, text, err, pend FROM docs WHERE path IN (%s)" % ",".join("?" * len(part))
                for path, mtime, size, text, err, pend in self.con.execute(q, part):
                    out[path] = (mtime, size, text, err, pend)
        return out

    def commit(self):
        with self.lock:
            self.con.commit()

    def clear(self):
        with self.lock:
            self.con.execute("DELETE FROM docs")
            self.con.commit()
            self.con.execute("VACUUM")

    def count(self):
        with self.lock:
            return self.con.execute("SELECT COUNT(*) FROM docs").fetchone()[0]

    def close(self):
        with self.lock:
            self.con.commit()
            self.con.close()


# ───────────────────────── 검색 ─────────────────────────
def parse_query(q):
    """띄어 쓴 단어는 모두 포함(AND), "따옴표"는 한 덩어리 구절"""
    return [a or b for a, b in re.findall(r'"([^"]+)"|(\S+)', q)]


def make_pattern(term, ignore_space):
    if ignore_space:   # '예산집행'으로 찾아도 '예산 집행', 줄바꿈된 '예산\n집행'까지 찾음
        chars = [c for c in term if not c.isspace()]
        pat = r"\s*".join(re.escape(c) for c in chars)
    else:
        pat = r"\s+".join(re.escape(w) for w in term.split())
    return re.compile(pat, re.IGNORECASE)


def make_snippet(text, a, b, width=45, lo=0, hi=None):
    hi = len(text) if hi is None else hi
    s, e = max(lo, a - width), min(hi, b + width)
    snip = re.sub(r"\s+", " ", text[s:e]).strip()
    return ("…" if s > lo else "") + snip + ("…" if e < hi else "")


def match_text(text, pats, archive=False):
    total, snippets = 0, []
    for p in pats:
        cnt = 0
        for m in p.finditer(text):
            if archive and text.startswith("■ ", text.rfind("\n", 0, m.start()) + 1):
                continue                          # '■ 파일이름' 구분 줄은 목록과 겹치므로 건너뜀
            cnt += 1
            if cnt <= 4 and len(snippets) < 10:
                if archive:                       # 압축 파일이면 어느 파일 안에서 찾았는지 앞에 붙임
                    lo = text.rfind("\n■ ", 0, m.start()) + 1
                    lo = text.find("\n", lo) + 1 if text.startswith("■ ", lo) and text.find("\n", lo) < m.start() else lo
                    hi = text.find("\n■ ", m.end())
                    snip = make_snippet(text, m.start(), m.end(), lo=lo, hi=hi if hi >= 0 else None)
                    sec = archive_section(text, m.start())
                    if sec and sec != "(압축 파일 목록)":
                        snip = f"[{sec}]  {snip}"
                    elif sec:
                        snip = "[파일 목록]  " + snip
                else:
                    snip = make_snippet(text, m.start(), m.end())
                if snip not in snippets:
                    snippets.append(snip)
        if cnt == 0:
            return 0, []
        total += cnt
    return total, snippets


def iter_files(root, recursive):
    if recursive:
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames if d.lower() not in SKIP_DIRS]
            for f in filenames:
                yield os.path.join(dirpath, f)
    else:
        try:
            for e in os.scandir(root):
                if e.is_file():
                    yield e.path
        except OSError:
            return


def iter_entries(root, recursive, dirs=False):
    """(경로, 이름, 수정시각, 크기) — 폴더 목록을 읽을 때 함께 오는 정보를 써서 파일마다 따로 묻지 않음
    (공유 폴더·네트워크 드라이브에서 특히 빠름). dirs=True면 폴더도 내보냄(크기 -1)"""
    stack = [root]
    while stack:
        d = stack.pop()
        try:
            with os.scandir(d) as it:
                subs = []
                for e in it:
                    try:
                        if e.is_dir(follow_symlinks=False):
                            if recursive and e.name.lower() not in SKIP_DIRS:
                                subs.append(e.path)
                            if dirs:
                                yield e.path, e.name, e.stat(follow_symlinks=False).st_mtime, -1
                            continue
                        if not e.is_file():
                            continue
                        st = e.stat()
                        yield e.path, e.name, st.st_mtime, st.st_size
                    except OSError:
                        continue
        except OSError:
            continue
        stack.extend(reversed(subs))


def name_worker(root, pats, recursive, out_q, stop):
    """파일명 검색: 문서 내용은 읽지 않고 파일·폴더 이름만 비교 (아주 빠름)"""
    scanned = found = 0
    last = time.time()
    for path, name, mtime, size in iter_entries(root, recursive, dirs=True):
        if stop.is_set():
            break
        scanned += 1
        if all(p.search(name) for p in pats):
            found += 1
            out_q.put(("hit", {
                "path": path, "name": name, "folder": os.path.dirname(path),
                "mtime": datetime.fromtimestamp(mtime).strftime("%Y-%m-%d %H:%M"),
                "count": 0, "snippets": [], "name_hit": True, "is_dir": size < 0}))
        if time.time() - last > 0.2:
            last = time.time()
            out_q.put(("progress", scanned, path))
    out_q.put(("done", scanned, 0, stop.is_set()))


def search_worker(root, pats, exts, recursive, name_search, out_q, stop, cache, ocr=False):
    scanned = errors = found = 0
    if ocr and ocr_engine() is None:      # OCR을 못 쓰는 PC면 알리고 일반 검색만
        out_q.put(("warn", _ocr["error"]))
        ocr = False
    last = time.time()
    batch = []

    def emit(path, name, mtime, count=0, snippets=(), name_hit=False):
        out_q.put(("hit", {
            "path": path, "name": name, "folder": os.path.dirname(path),
            "mtime": datetime.fromtimestamp(mtime).strftime("%Y-%m-%d %H:%M"),
            "count": count, "snippets": list(snippets), "name_hit": name_hit}))

    def flush():
        """모아 둔 파일들의 색인을 한 번에 꺼내 와서 찾기"""
        nonlocal scanned, errors, found, last
        if not batch:
            return False
        rows = cache.get_many(Cache.key(b[0]) for b in batch)
        for path, name, ext, mtime, size in batch:
            if stop.is_set():
                return True
            row = rows.get(Cache.key(path))
            if row and row[0] == mtime and row[1] == size and not (ocr and row[4]):
                try:
                    text, err = zlib.decompress(row[2]).decode("utf-8", "ignore"), row[3]
                except Exception:
                    text, err = "", "기록 손상"
            else:
                pend = False
                try:
                    text, pend = extract_text(path, ocr, lambda m: out_q.put(("progress", scanned, m)), stop)
                    err = ""
                except StopSearch:
                    return True                             # 중간에 멈춘 OCR 결과는 저장하지 않음
                except Exception as e:
                    text, err = "", str(e)[:200]
                cache.put(path, mtime, size, text, err, pend)
            scanned += 1
            if err:
                errors += 1
            count, snippets = match_text(text, pats, ext in ARCHIVE_EXTS)
            name_hit = name_search and all(p.search(name) for p in pats)
            if count or name_hit:
                found += 1
                emit(path, name, mtime, count, snippets, name_hit)
            if time.time() - last > 0.2:
                last = time.time()
                out_q.put(("progress", scanned, path))
                cache.commit()
        batch.clear()
        return False

    for path, name, mtime, size in iter_entries(root, recursive):
        if stop.is_set():
            break
        ext = os.path.splitext(name)[1].lower()
        if name.startswith("~$"):
            continue
        if ext not in exts:
            # '기타 모든 파일'은 내용은 읽지 않고 이름만 비교
            if "*" in exts and (ext not in KNOWN_EXTS) and all(p.search(name) for p in pats):
                found += 1
                emit(path, name, mtime, name_hit=True)
            continue
        if size > (MAX_ARCHIVE_SIZE if ext in ARCHIVE_EXTS else MAX_FILE_SIZE):
            continue
        batch.append((path, name, ext, mtime, size))
        if len(batch) >= 200 and flush():
            break
    else:
        flush()
    cache.commit()
    out_q.put(("done", scanned, errors, stop.is_set()))



# ───────────── 원래 모양 미리보기 (탐색기와 같은 윈도우 미리보기 처리기) ─────────────
SHELL_PREVIEW = False
if sys.platform == "win32":
    try:
        import ctypes
        from ctypes import wintypes
        import comtypes
        from comtypes import GUID, IUnknown, COMMETHOD

        class IPreviewHandler(IUnknown):
            _iid_ = GUID("{8895b1c6-b41f-4c1c-a562-0d564250836f}")
            _methods_ = [
                COMMETHOD([], ctypes.HRESULT, "SetWindow", (["in"], wintypes.HWND, "hwnd"),
                          (["in"], ctypes.POINTER(wintypes.RECT), "prc")),
                COMMETHOD([], ctypes.HRESULT, "SetRect", (["in"], ctypes.POINTER(wintypes.RECT), "prc")),
                COMMETHOD([], ctypes.HRESULT, "DoPreview"),
                COMMETHOD([], ctypes.HRESULT, "Unload"),
                COMMETHOD([], ctypes.HRESULT, "SetFocus"),
                COMMETHOD([], ctypes.HRESULT, "QueryFocus", (["out"], ctypes.POINTER(wintypes.HWND), "phwnd")),
                COMMETHOD([], ctypes.HRESULT, "TranslateAccelerator", (["in"], ctypes.c_void_p, "pmsg")),
            ]

        class IInitializeWithFile(IUnknown):
            _iid_ = GUID("{b7d14566-0509-4cce-a71f-0a554233bd9b}")
            _methods_ = [COMMETHOD([], ctypes.HRESULT, "Initialize", (["in"], wintypes.LPCWSTR, "pszFilePath"),
                                   (["in"], wintypes.DWORD, "grfMode"))]

        class IInitializeWithStream(IUnknown):
            _iid_ = GUID("{b824b49d-22ac-4161-ac8a-9916e8fa3f7f}")
            _methods_ = [COMMETHOD([], ctypes.HRESULT, "Initialize", (["in"], ctypes.c_void_p, "pstm"),
                                   (["in"], wintypes.DWORD, "grfMode"))]

        class IInitializeWithItem(IUnknown):
            _iid_ = GUID("{7f73be3f-fb79-493c-a6c7-7ee14e245841}")
            _methods_ = [COMMETHOD([], ctypes.HRESULT, "Initialize", (["in"], ctypes.c_void_p, "psi"),
                                   (["in"], wintypes.DWORD, "grfMode"))]

        IID_IShellItem = GUID("{43826d1e-e718-42ee-bc55-a1e261c37bfe}")
        _shlwapi = ctypes.windll.shlwapi
        _shell32 = ctypes.windll.shell32
        _shlwapi.AssocQueryStringW.argtypes = [wintypes.DWORD, wintypes.DWORD, wintypes.LPCWSTR, wintypes.LPCWSTR,
                                               wintypes.LPWSTR, ctypes.POINTER(wintypes.DWORD)]
        _shlwapi.AssocQueryStringW.restype = ctypes.c_long
        _shlwapi.SHCreateStreamOnFileEx.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD, wintypes.BOOL,
                                                    ctypes.c_void_p, ctypes.POINTER(ctypes.c_void_p)]
        _shlwapi.SHCreateStreamOnFileEx.restype = ctypes.c_long
        _shell32.SHCreateItemFromParsingName.argtypes = [wintypes.LPCWSTR, ctypes.c_void_p, ctypes.POINTER(GUID),
                                                         ctypes.POINTER(ctypes.c_void_p)]
        _shell32.SHCreateItemFromParsingName.restype = ctypes.c_long
        SHELL_PREVIEW = True
    except Exception:
        SHELL_PREVIEW = False

_clsid_cache = {}


def preview_clsid(ext):
    """이 확장자에 등록된 미리보기 처리기 찾기 (탐색기가 쓰는 것과 같음)"""
    if ext not in _clsid_cache:
        buf = ctypes.create_unicode_buffer(128)
        n = wintypes.DWORD(128)
        hr = _shlwapi.AssocQueryStringW(0x20, 16, ext, "{8895b1c6-b41f-4c1c-a562-0d564250836f}", buf, ctypes.byref(n))
        _clsid_cache[ext] = buf.value if hr == 0 and buf.value else None
    return _clsid_cache[ext]


ZOOMABLE_SHELL_EXTS = (".hwp", ".hwpx", ".hwt", ".hwtx")   # 처리기 미리보기를 키워 볼 수 있는 형식
PAGE_RATIO = 297 / 210                      # A4 세로 쪽 비율 (키울 때 처리기 창 높이 = 폭 × 이 비율)


class WheelHook:
    """처리기 창은 다른 프로그램(한글)이 그리는 창이라 마우스 휠이 이 프로그램으로 오지 않음.
    마우스 휠을 가로채서, 커서가 한글 미리보기 위에 있으면 스크롤(Ctrl+휠은 확대)로 바꿔 줌."""

    def __init__(self):
        self.panels = []
        self.rects = []                       # (화면 좌표 사각형, 미리보기) — 화면 스레드에서 갱신
        self.pending = []                     # (미리보기, 스크롤 칸 수, 확대 여부)
        self.hook = None
        self._proc = None

    def add(self, panel):
        self.panels.append(panel)
        if self.hook is None and sys.platform == "win32":
            self._install(panel)

    def _install(self, panel):
        """휠 가로채기는 따로 스레드에서 돌림 → 이 프로그램이 바쁠 때도 PC 전체 마우스가 느려지지 않음"""
        self.hook = "starting"
        threading.Thread(target=self._hook_thread, daemon=True).start()
        panel.after(100, self._tick)

    def _hook_thread(self):
        try:
            import ctypes
            from ctypes import wintypes
            u32 = ctypes.windll.user32
            k32 = ctypes.windll.kernel32

            class MSLL(ctypes.Structure):
                _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long), ("mouseData", wintypes.DWORD),
                            ("flags", wintypes.DWORD), ("time", wintypes.DWORD), ("extra", ctypes.c_void_p)]
            LRESULT = ctypes.c_ssize_t
            HOOKPROC = ctypes.WINFUNCTYPE(LRESULT, ctypes.c_int, wintypes.WPARAM, wintypes.LPARAM)
            u32.CallNextHookEx.argtypes = [ctypes.c_void_p, ctypes.c_int, wintypes.WPARAM, wintypes.LPARAM]
            u32.CallNextHookEx.restype = LRESULT
            u32.SetWindowsHookExW.argtypes = [ctypes.c_int, HOOKPROC, ctypes.c_void_p, wintypes.DWORD]
            u32.SetWindowsHookExW.restype = ctypes.c_void_p
            u32.UnhookWindowsHookEx.argtypes = [ctypes.c_void_p]
            k32.GetModuleHandleW.restype = ctypes.c_void_p

            def proc(code, wparam, lparam):
                try:
                    if code == 0 and wparam == 0x020A and self.rects:     # WM_MOUSEWHEEL
                        m = ctypes.cast(lparam, ctypes.POINTER(MSLL)).contents
                        for (x0, y0, x1, y1), p in self.rects:
                            if x0 <= m.x < x1 and y0 <= m.y < y1:
                                delta = ctypes.c_short((m.mouseData >> 16) & 0xFFFF).value
                                ctrl = bool(u32.GetKeyState(0x11) & 0x8000)
                                self.pending.append((p, delta, ctrl))
                                return 1                        # 한글 처리기로 보내지 않음
                except Exception:
                    pass
                return u32.CallNextHookEx(None, code, wparam, lparam)
            self._proc = HOOKPROC(proc)
            h = u32.SetWindowsHookExW(14, self._proc, k32.GetModuleHandleW(None), 0)   # WH_MOUSE_LL
            if not h:
                self.hook = None
                return
            self.hook = h
            self._thread_id = k32.GetCurrentThreadId()
            msg = wintypes.MSG()
            while u32.GetMessageW(ctypes.byref(msg), None, 0, 0) > 0:
                u32.TranslateMessage(ctypes.byref(msg))
                u32.DispatchMessageW(ctypes.byref(msg))
            u32.UnhookWindowsHookEx(h)
        except Exception:
            self.hook = None

    def _tick(self):
        """화면 스레드: 한글 미리보기 위치를 갱신하고, 쌓인 휠 동작을 처리"""
        rects, alive = [], []
        for p in self.panels:
            try:
                if not p.winfo_exists():
                    continue
                alive.append(p)
                if p.shell_zoomable and p.shell_frame.winfo_ismapped() and p.shell and p.shell.h is not None:
                    cv = p.shell_cv
                    x, y = cv.winfo_rootx(), cv.winfo_rooty()
                    rects.append(((x, y, x + cv.winfo_width(), y + cv.winfo_height()), p))
            except Exception:
                continue
        self.panels, self.rects = alive, rects
        pend, self.pending = self.pending, []
        for p, delta, ctrl in pend:
            try:
                if ctrl:
                    p.shell_zoom_step(1.1 if delta > 0 else 1 / 1.1)
                else:
                    p.shell_scroll(-3 if delta > 0 else 3)
            except Exception:
                pass
        if self.panels:
            try:
                self.panels[0].after(60, self._tick)
                return
            except Exception:
                pass
        self.hook_tick_stopped = True

    def remove_all(self):
        self.rects = []
        tid = getattr(self, "_thread_id", None)
        if tid and sys.platform == "win32":
            try:
                import ctypes
                ctypes.windll.user32.PostThreadMessageW(tid, 0x0012, 0, 0)   # WM_QUIT → 가로채기 끝
            except Exception:
                pass
        self.hook = None


WHEEL_HOOK = WheelHook()


class ShellPreview:
    def __init__(self, host):
        self.host = host
        self.h = None
        self.keep = None
        host.bind("<Configure>", self._resize)

    def _rect(self):
        return wintypes.RECT(0, 0, max(1, self.host.winfo_width()), max(1, self.host.winfo_height()))

    def _resize(self, e=None):
        if self.h is not None:
            try:
                self.h.SetRect(self._rect())
            except Exception:
                pass

    def _init(self, h, path):
        try:
            h.QueryInterface(IInitializeWithFile).Initialize(path, 0)
            return True
        except Exception:
            pass
        try:
            ini = h.QueryInterface(IInitializeWithStream)
            p = ctypes.c_void_p()
            if _shlwapi.SHCreateStreamOnFileEx(path, 0x40, 0, False, None, ctypes.byref(p)) == 0 and p.value:
                keep = ctypes.cast(p, ctypes.POINTER(IUnknown))
                ini.Initialize(p.value, 0)
                return keep
        except Exception:
            pass
        try:
            ini = h.QueryInterface(IInitializeWithItem)
            p = ctypes.c_void_p()
            if _shell32.SHCreateItemFromParsingName(path, None, ctypes.byref(IID_IShellItem), ctypes.byref(p)) == 0 and p.value:
                keep = ctypes.cast(p, ctypes.POINTER(IUnknown))
                ini.Initialize(p.value, 0)
                return keep
        except Exception:
            pass
        return None

    # 확장자별로 먼저 시도할 다른 처리기 (hwpx는 hwp용이 모든 쪽을 보여 주는 경우가 많음)
    BORROW = {".hwpx": ".hwp"}

    def show(self, path):
        self.unload()
        ext = os.path.splitext(path)[1].lower()
        tried = []
        for e in ([self.BORROW[ext]] if ext in self.BORROW else []) + [ext]:
            clsid = preview_clsid(e)
            if clsid and clsid not in tried:
                tried.append(clsid)
                if self._try(clsid, path):
                    return True
        return False

    def _try(self, clsid, path):
        h = None
        for ctx in (comtypes.CLSCTX_LOCAL_SERVER, comtypes.CLSCTX_INPROC_SERVER):
            try:
                h = comtypes.CoCreateInstance(GUID(clsid), interface=IPreviewHandler, clsctx=ctx)
                break
            except Exception:
                continue
        if h is None:
            return False
        try:
            keep = self._init(h, path)
            if keep is None:
                return False
            self.host.update_idletasks()
            h.SetWindow(self.host.winfo_id(), self._rect())
            h.DoPreview()
            self.h, self.keep = h, keep
            return True
        except Exception:
            try:
                h.Unload()
            except Exception:
                pass
            return False

    def unload(self):
        if self.h is not None:
            try:
                self.h.Unload()
            except Exception:
                pass
        self.h = None
        self.keep = None


# ───────────── 광고 칸 (미리보기 오른쪽) ─────────────
class AdManager:
    """광고 목록을 인터넷 주소(AD_FEED_URL)에서 받아 와 모든 광고 칸에 돌려 가며 보여 줌.
    받은 목록과 그림은 PC에 저장해 두어 인터넷이 끊겨도 마지막 광고를 보여 줌."""

    def __init__(self, root):
        self.root = root
        self.dir = os.path.join(APP_DIR, "ads")
        os.makedirs(self.dir, exist_ok=True)
        self.boxes = []
        self.ads = []
        self.on_change = None
        self.interval = 15
        self.index = 0
        self.q = queue.Queue()
        self._load_cache()
        self.root.after(1500, self.fetch)
        self.root.after(self.interval * 1000, self._tick)
        self.root.after(300, self._poll)

    # 목록 받기
    def _load_cache(self):
        try:
            with open(os.path.join(self.dir, "feed.json"), encoding="utf-8") as f:
                self._apply(json.load(f))
        except Exception:
            pass

    def fetch(self):
        if AD_FEED_URL:
            threading.Thread(target=self._fetch_worker, daemon=True).start()
        self.root.after(AD_REFRESH_MIN * 60 * 1000, self.fetch)

    def _fetch_worker(self):
        import hashlib
        try:
            feed = json.loads(net_request(AD_FEED_URL, headers={"User-Agent": f"SmartExplorer/{APP_VERSION}"},
                                          limit=512 * 1024, timeout=8).decode("utf-8-sig"))
            for ad in feed.get("ads", []):
                url = ad.get("image") or ""
                if not url.lower().startswith(("http://", "https://")):
                    continue
                ext = os.path.splitext(url.split("?")[0])[1].lower()
                ext = ext if ext in (".png", ".jpg", ".jpeg", ".gif", ".bmp", ".webp") else ".img"
                local = os.path.join(self.dir, hashlib.sha1(url.encode()).hexdigest()[:16] + ext)
                try:                                   # 그림 하나가 안 받아져도 나머지 광고는 계속
                    if not os.path.exists(local):
                        data = net_request(url, headers={"User-Agent": f"SmartExplorer/{APP_VERSION}"},
                                           limit=AD_MAX_IMAGE, timeout=10)
                        if len(data) > AD_MAX_IMAGE:
                            continue
                        with open(local + ".part", "wb") as f:
                            f.write(data)
                        os.replace(local + ".part", local)
                    ad["_local"] = local
                except Exception:
                    continue
            with open(os.path.join(self.dir, "feed.json.part"), "w", encoding="utf-8") as f:
                json.dump(feed, f, ensure_ascii=False)
            os.replace(os.path.join(self.dir, "feed.json.part"), os.path.join(self.dir, "feed.json"))
            self.q.put(feed)
        except Exception:
            pass                                       # 못 받으면 저장해 둔 광고를 계속 씀

    def _poll(self):
        try:
            while True:
                had = bool(self.ads)
                self._apply(self.q.get_nowait())
                self._show_all()
                if had != bool(self.ads) and self.on_change:
                    self.on_change()                   # 광고가 생기거나 없어지면 칸 크기를 다시 맞춤
        except queue.Empty:
            pass
        self.root.after(1000, self._poll)

    def _apply(self, feed):
        ads = []
        for ad in feed.get("ads", []):
            local = ad.get("_local")
            if local and not os.path.exists(local):
                local = None
            if not local and not ad.get("text"):
                continue
            ads.append({"image": local, "link": ad.get("link", ""), "text": ad.get("text", ""),
                        "bg": ad.get("bg", "#ffffff"), "fg": ad.get("fg", "#333333")})
        self.ads = ads
        try:
            self.interval = max(5, int(feed.get("interval", 15)))
        except (TypeError, ValueError):
            self.interval = 15

    # 돌려 보여 주기
    def current_for(self, box):
        if not self.ads:
            return {"image": None, "link": AD_CONTACT_URL, "text": AD_PLACEHOLDER, "bg": "#ffffff", "fg": "#999999",
                    "empty": True}
        return self.ads[(self.index + box.offset) % len(self.ads)]

    def _tick(self):
        if len(self.ads) > 1:
            self.index += 1
            self._show_all()
        self.root.after(self.interval * 1000, self._tick)

    def _show_all(self):
        for b in list(self.boxes):
            try:
                b.show(self.current_for(b))
            except tk.TclError:
                self.boxes.remove(b)

    def register(self, box):
        box.offset = len(self.boxes)                  # 칸마다 다른 광고가 보이도록 순서를 어긋나게
        self.boxes.append(box)
        box.show(self.current_for(box))

    def unregister(self, box):
        if box in self.boxes:
            self.boxes.remove(box)


AD_MANAGER = None


class AdBox(tk.Frame):
    def __init__(self, master):
        super().__init__(master, bg="#ffffff", highlightthickness=1, highlightbackground="#d8d8d8")
        self.offset = 0
        self.ad = None
        self.img = None
        self._job = None
        self.label = tk.Label(self, bg="#ffffff", cursor="hand2", wraplength=10, justify="center",
                              font=(FONT[0], fsz(9)))
        self.label.place(relx=0, rely=0, relwidth=1, relheight=1)
        self.tag = tk.Label(self, text="AD", bg="#e3e3e3", fg="#666", font=(FONT[0], fsz(7)))
        for w in (self, self.label):
            w.bind("<Button-1>", self._click)
        self.bind("<Configure>", self._resized)
        if AD_MANAGER is not None:
            AD_MANAGER.register(self)

    def destroy(self):
        if AD_MANAGER is not None:
            AD_MANAGER.unregister(self)
        super().destroy()

    def show(self, ad):
        self.ad = ad
        self._render()

    def _resized(self, e=None):
        if self._job:
            self.after_cancel(self._job)
        self._job = self.after(200, self._render)

    def _render(self):
        self._job = None
        ad = self.ad
        if not ad:
            return
        w, h = max(10, self.winfo_width() - 4), max(10, self.winfo_height() - 4)
        bg = ad.get("bg") or "#ffffff"
        self.configure(bg=bg)
        if ad.get("empty"):                            # 광고가 없으면 칸만 비워 둠 (글자·AD 표시 없음)
            self.img = None
            self.label.configure(image="", text="", bg=bg, cursor="arrow")
            self.tag.place_forget()
            return
        self.label.configure(cursor="hand2")
        self.tag.place(relx=1, x=-1, y=1, anchor="ne")
        if ad.get("image"):
            try:
                self.img, _ = make_photo(ad["image"], w, h, upscale=True)
                self.label.configure(image=self.img, text="", bg=bg)
                self.tag.lift()
                return
            except Exception:
                pass
        self.img = None
        self.label.configure(image="", text=ad.get("text", ""), bg=bg, fg=ad.get("fg") or "#333333",
                             wraplength=max(10, w - 6))
        self.tag.lift()

    def _click(self, e=None):
        link = (self.ad or {}).get("link") or ""
        if link.lower().startswith(("http://", "https://")):
            import webbrowser
            webbrowser.open(link)


def fmt_size(n):
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            return f"{n:,.0f} {unit}" if unit == "B" else f"{n:,.1f} {unit}"
        n /= 1024


def make_photo(src, max_w, max_h, upscale=False):
    """src: 파일 경로 또는 bytes → 크기에 맞춘 tk 그림 (PIL 없으면 PNG·GIF만)"""
    if Image is not None:
        from PIL import ImageTk
        im = Image.open(io.BytesIO(src) if isinstance(src, (bytes, bytearray)) else src)
        try:
            im.draft("RGB", (max_w, max_h))
        except Exception:
            pass
        im = ImageOps.exif_transpose(im)
        if im.mode not in ("RGB", "RGBA"):
            im = im.convert("RGBA" if "A" in im.mode or im.mode == "P" else "RGB")
        w, h = im.size
        scale = min(max_w / w, max_h / h)
        if scale < 1 or upscale:
            im = im.resize((max(1, int(w * scale)), max(1, int(h * scale))), Image.LANCZOS)
        return ImageTk.PhotoImage(im), (w, h)
    import base64
    data = src if isinstance(src, (bytes, bytearray)) else open(src, "rb").read()
    img = tk.PhotoImage(data=base64.b64encode(data))
    w, h = img.width(), img.height()
    k = max(1, -(-w // max_w), -(-h // max_h))
    return (img.subsample(k) if k > 1 else img), (w, h)


# ───────────── 암호 걸린 파일 미리보기 (PDF · 엑셀 · 워드 · 파워포인트) ─────────────
OOXML_EXTS = (".xlsx", ".xlsm", ".docx", ".pptx")
OLE_OFFICE_EXTS = (".xls", ".doc", ".ppt")
SESSION_PASSWORDS = {}          # 이번에 켠 동안만 기억 (디스크에 저장하지 않음)


def locked_kind(path, ext):
    """암호가 걸린 파일이면 'pdf' / 'office' / 'hwp', 아니면 None"""
    try:
        if ext == ".pdf" and pdfium is not None:
            try:
                pdfium.PdfDocument(path).close()
                return None
            except pdfium.PdfiumError as e:
                return "pdf" if getattr(e, "err_code", None) == 4 or "password" in str(e).lower() else None
        if ext in OOXML_EXTS + OLE_OFFICE_EXTS:
            with open(path, "rb") as f:
                head = f.read(8)
            if head != b"\xd0\xcf\x11\xe0\xa1\xb1\x1a\xe1":
                return None
            if ext in OOXML_EXTS:            # 암호 걸린 xlsx·docx는 압축(zip)이 아니라 OLE 상자 안에 들어 있음
                return "office"
            try:
                import msoffcrypto
                with open(path, "rb") as f:
                    return "office" if msoffcrypto.OfficeFile(f).is_encrypted() else None
            except Exception:
                return None
        if ext == ".hwp":
            header = OleFile(path).read("FileHeader")
            return "hwp" if struct.unpack_from("<I", header, 36)[0] & 2 else None
        if ext == ".hwpx":
            with zipfile.ZipFile(path) as zf:
                if "META-INF/manifest.xml" in zf.namelist() and \
                        b"encryption-data" in zf.read("META-INF/manifest.xml"):
                    return "hwp"
    except Exception:
        return None
    return None


def office_decrypt(path, password):
    """암호를 풀어 임시 폴더에 같은 이름으로 저장 → 그 경로 (암호가 틀리면 ValueError)"""
    try:
        import msoffcrypto
    except ImportError:
        raise RuntimeError("암호 해제 기능(msoffcrypto)이 없습니다")
    out = io.BytesIO()
    with open(path, "rb") as f:
        of = msoffcrypto.OfficeFile(f)
        try:
            of.load_key(password=password)
            of.decrypt(out)
        except Exception as e:
            raise ValueError(str(e))
    d = os.path.join(TMP_DIR, "unlocked", str(int(time.time() * 1000)))
    os.makedirs(d, exist_ok=True)
    dest = os.path.join(d, os.path.basename(path))
    with open(dest, "wb") as f:
        f.write(out.getvalue())
    return dest


class PreviewPanel(ttk.Frame):
    """원래 모양(윈도우 처리기) → 직접 그리기(PDF·그림·표·압축 목록·문서 첫 쪽 그림+글자) 순서로 보여 줌"""
    MAX_PDF_PAGES = 30
    MAX_INNER_PREVIEW = 80 * 1024 * 1024

    def __init__(self, master, nested=False, ad=False):
        super().__init__(master)
        self.nested = nested
        self.adbox = None
        self.side = None
        if not nested:
            # 미리보기는 body 안에만 그림. 광고를 켜면 body 오른쪽에 광고 띠가 생김
            self.body = ttk.Frame(self)
            self.body.place(relx=0, rely=0, relwidth=1, relheight=1)
            self.bind("<Configure>", lambda e: self._layout_ad(), add="+")
        else:
            self.body = self
        if ad:
            self.set_ad(True)
        # 탐색기 미리보기 처리기 자리: 스크롤 가능한 캔버스 안에 넣어서 한글 문서는 크게 키워 볼 수 있게
        self.shell_frame = ttk.Frame(self.body)
        self.shell_bar = ttk.Frame(self.shell_frame)
        self.shell_btns = {}
        for mode, label in (("width", "↔ 가로 맞춤"), ("height", "↕ 세로 맞춤")):
            b = ttk.Button(self.shell_bar, text=label, command=lambda m=mode: self.set_shell_fit(m))
            b.pack(side="left", padx=(0, 2))
            self.shell_btns[mode] = b
        ttk.Button(self.shell_bar, text="−", width=3, command=lambda: self.shell_zoom_step(1 / 1.2)).pack(side="left", padx=(6, 0))
        self.shell_zoom_var = tk.StringVar()
        ttk.Label(self.shell_bar, textvariable=self.shell_zoom_var, width=8, anchor="center").pack(side="left")
        ttk.Button(self.shell_bar, text="+", width=3, command=lambda: self.shell_zoom_step(1.2)).pack(side="left")
        ttk.Label(self.shell_bar, text="휠 = 스크롤 · Ctrl+휠 = 확대", foreground="#888").pack(side="right")
        sf = ttk.Frame(self.shell_frame)
        sf.pack(side="bottom", fill="both", expand=True)
        self.shell_cv = tk.Canvas(sf, bg="#e9e9e9", highlightthickness=0)
        self.shell_ys = ttk.Scrollbar(sf, orient="vertical", command=self.shell_cv.yview)
        self.shell_xs = ttk.Scrollbar(sf, orient="horizontal", command=self.shell_cv.xview)
        self.shell_cv.configure(yscrollcommand=self.shell_ys.set, xscrollcommand=self.shell_xs.set)
        self.shell_ys.pack(side="right", fill="y")
        self.shell_xs.pack(side="bottom", fill="x")
        self.shell_cv.pack(fill="both", expand=True)
        self.host = tk.Frame(self.shell_cv, bg="white")
        self.host_win = self.shell_cv.create_window(0, 0, window=self.host, anchor="nw")
        self.shell_cv.bind("<Configure>", lambda e: self._layout_shell())
        self.shell_zoomable = False
        self.shell_fit = "width"        # 한글 문서: width(가로 맞춤) · height(세로 맞춤) · custom
        self.shell_zoom = 1.0           # custom일 때 가로 맞춤 대비 배율
        self.shell = ShellPreview(self.host) if (SHELL_PREVIEW and not nested) else None
        if self.shell:
            WHEEL_HOOK.add(self)
        self.images = []
        self.current = None
        self.pats = []
        self.cache = None
        self._img_src = None
        self._fit_job = None

        # PDF·그림 (가로 맞춤 · 세로 맞춤 · 확대/축소)
        self.pic_frame = ttk.Frame(self.body)
        zb = ttk.Frame(self.pic_frame)
        zb.pack(fill="x", pady=(0, 2))
        self.fit_mode = "auto"          # auto(PDF=가로, 그림=전체) · width · height · custom
        self.zoom = 1.0                 # custom일 때 배율 (1.0 = 실제 크기)
        self._eff_zoom = 1.0            # 지금 화면에 보이는 배율
        self.fit_btns = {}
        for mode, label in (("width", "↔ 가로 맞춤"), ("height", "↕ 세로 맞춤")):
            b = ttk.Button(zb, text=label, command=lambda m=mode: self.set_fit(m))
            b.pack(side="left", padx=(0, 2))
            self.fit_btns[mode] = b
        ttk.Button(zb, text="−", width=3, command=lambda: self.zoom_step(1 / 1.25)).pack(side="left", padx=(6, 0))
        self.zoom_var = tk.StringVar(value="")
        zl = ttk.Label(zb, textvariable=self.zoom_var, width=6, anchor="center", cursor="hand2")
        zl.pack(side="left")
        zl.bind("<Button-1>", lambda e: self.set_zoom(1.0))
        ttk.Button(zb, text="+", width=3, command=lambda: self.zoom_step(1.25)).pack(side="left")
        self.page_info = ttk.Label(zb, foreground="#777")
        self.page_info.pack(side="right")
        cf = ttk.Frame(self.pic_frame)
        cf.pack(fill="both", expand=True)
        self.canvas = tk.Canvas(cf, bg="#e9e9e9", highlightthickness=0)
        cs = ttk.Scrollbar(cf, orient="vertical", command=self.canvas.yview)
        cx = ttk.Scrollbar(cf, orient="horizontal", command=self.canvas.xview)
        self.canvas.configure(yscrollcommand=cs.set, xscrollcommand=cx.set)
        cs.pack(side="right", fill="y")
        cx.pack(side="bottom", fill="x")
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<MouseWheel>", self._on_wheel)
        self.canvas.bind("<Shift-MouseWheel>", lambda e: self.canvas.xview_scroll(int(-e.delta / 120), "units"))
        self.canvas.bind("<Control-MouseWheel>", lambda e: self.zoom_step(1.15 if e.delta > 0 else 1 / 1.15))
        self.canvas.bind("<ButtonPress-1>", lambda e: self.canvas.scan_mark(e.x, e.y))
        self.canvas.bind("<B1-Motion>", lambda e: self.canvas.scan_dragto(e.x, e.y, gain=1))
        self.canvas.configure(cursor="fleur")
        self.canvas.bind("<Configure>", self._on_canvas_resize)
        self._pdf_path = None

        # 암호 입력
        self.lock_frame = ttk.Frame(self.body)
        lk = ttk.Frame(self.lock_frame)
        lk.place(relx=0.5, rely=0.4, anchor="center")
        ttk.Label(lk, text="🔒", font=(FONT[0], fsz(26))).pack()
        self.lock_title = ttk.Label(lk, text="", font=(FONT[0], fsz(11), "bold"), justify="center")
        self.lock_title.pack(pady=(2, 8))
        self.lock_row = ttk.Frame(lk)
        self.lock_row.pack()
        self.pw_var = tk.StringVar()
        self.pw_entry = ttk.Entry(self.lock_row, textvariable=self.pw_var, show="●", width=22, font=(FONT[0], fsz(11)))
        self.pw_entry.pack(side="left", ipady=1)
        self.pw_entry.bind("<Return>", lambda e: self._unlock())
        ttk.Button(self.lock_row, text="미리보기", style="Accent.TButton", command=self._unlock).pack(side="left", padx=(4, 0))
        self.lock_msg = ttk.Label(lk, text="", foreground="#888", justify="center")
        self.lock_msg.pack(pady=(8, 0))
        self._lock = None
        self._pdf_pw = None
        self._unlocked = []

        # 문서(첫 쪽 그림 + 글자)
        self.doc_frame = ttk.Frame(self.body)
        self.text = tk.Text(self.doc_frame, wrap="word", padx=10, pady=8, font=FONT, relief="flat")
        ts = ttk.Scrollbar(self.doc_frame, orient="vertical", command=self.text.yview)
        self.text.configure(yscrollcommand=ts.set)
        ts.pack(side="right", fill="y")
        self.text.pack(fill="both", expand=True)
        self.text.tag_configure("hl", background="#ffe066")
        self.text.tag_configure("note", foreground="#2a6fdb")
        self.text.tag_configure("info", foreground="#777")
        self.text.tag_configure("big", font=(FONT[0], fsz(12), "bold"))
        self.text.tag_configure("center", justify="center")

        # 표(엑셀·CSV)
        self.grid_frame = ttk.Frame(self.body)
        gb = ttk.Frame(self.grid_frame)
        gb.pack(fill="x", pady=(0, 2))
        self.sheet_var = tk.StringVar()
        self.sheet_cb = ttk.Combobox(gb, textvariable=self.sheet_var, state="readonly", width=24)
        self.sheet_cb.pack(side="left")
        self.sheet_cb.bind("<<ComboboxSelected>>", lambda e: self._fill_grid())
        self.grid_info = ttk.Label(gb, foreground="#777")
        self.grid_info.pack(side="left", padx=8)
        gf = ttk.Frame(self.grid_frame)
        gf.pack(fill="both", expand=True)
        self.grid = ttk.Treeview(gf, show="headings", selectmode="browse")
        gy = ttk.Scrollbar(gf, orient="vertical", command=self.grid.yview)
        gx = ttk.Scrollbar(gf, orient="horizontal", command=self.grid.xview)
        self.grid.configure(yscrollcommand=gy.set, xscrollcommand=gx.set)
        gy.pack(side="right", fill="y")
        gx.pack(side="bottom", fill="x")
        self.grid.pack(fill="both", expand=True)
        self.grid.tag_configure("hit", background="#fff3b0")
        self.sheets = []

        # 압축 파일 목록 (+ 고른 파일 미리보기)
        self.arc_frame = ttk.Frame(self.body)
        if not nested:
            ab = ttk.Frame(self.arc_frame)
            ab.pack(fill="x", pady=(0, 2))
            self.arc_info = ttk.Label(ab, foreground="#555")
            self.arc_info.pack(side="left")
            ttk.Button(ab, text="고른 파일 열기", command=self._arc_open).pack(side="right")
            ap = ttk.PanedWindow(self.arc_frame, orient="vertical")
            ap.pack(fill="both", expand=True)
            af = ttk.Frame(ap)
            self.arc_tree = ttk.Treeview(af, columns=("name", "size", "mtime"), show="headings", selectmode="browse")
            for c, t, w, anc, st in (("name", "압축 안 파일", 300, "w", True), ("size", "크기", 80, "e", False),
                                     ("mtime", "수정일", 120, "center", False)):
                self.arc_tree.heading(c, text=t)
                self.arc_tree.column(c, width=w, anchor=anc, stretch=st)
            asb = ttk.Scrollbar(af, orient="vertical", command=self.arc_tree.yview)
            self.arc_tree.configure(yscrollcommand=asb.set)
            asb.pack(side="right", fill="y")
            self.arc_tree.pack(fill="both", expand=True)
            self.arc_tree.tag_configure("hit", background="#fff3b0")
            self.arc_tree.tag_configure("dim", foreground="#999")
            self.arc_tree.bind("<<TreeviewSelect>>", lambda e: self._arc_schedule())
            self.arc_tree.bind("<Double-1>", lambda e: self._arc_open())
            ap.add(af, weight=1)
            self.inner = PreviewPanel(ap, nested=True)
            ap.add(self.inner, weight=2)
        self.arc_entries = {}
        self._arc_job = None

        self.msg = ttk.Label(self.body, text="파일을 선택하면 미리보기가 나옵니다.", anchor="center", foreground="#888")
        self._bg_job = None
        self.msg.bind("<Configure>", lambda e: self._bg_later())
        self._show(self.msg)

    # 광고 칸 (화면 맨 오른쪽 아래 칸에만 하나)
    def set_ad(self, on):
        if self.nested or bool(self.adbox) == bool(on):
            return
        if on:
            self.side = ttk.Frame(self)
            self.adbox = AdBox(self.side)
        else:
            self.adbox.destroy()
            self.side.destroy()
            self.adbox = self.side = None
        self._layout_ad()

    def _ad_size(self):
        return ad_pixels(self)                           # 최소 크기 유지 — 줄이지 않음

    def _layout_ad(self):
        if self.nested:
            return
        if not self.adbox:
            self.body.place(relx=0, rely=0, relwidth=1, relheight=1, width=0)
            return
        aw, ah = self._ad_size()
        self.body.place(relx=0, rely=0, relwidth=1, width=-(aw + AD_GAP), relheight=1)
        self.side.place(relx=1, x=-aw, rely=0, width=aw, relheight=1)
        self.adbox.place(relx=0, rely=1, y=-ah, relwidth=1, height=ah)

    # 공통
    def _show(self, w):
        for x in (self.shell_frame, self.pic_frame, self.doc_frame, self.grid_frame, self.arc_frame, self.msg,
                  self.lock_frame):
            if x is not w:
                x.pack_forget()
        w.pack(fill="both", expand=True)
        if w is self.msg:
            self.after_idle(self._msg_bg)

    def _bg_later(self):
        if self._bg_job:
            self.after_cancel(self._bg_job)
        self._bg_job = self.after(150, self._msg_bg)

    def _msg_bg(self, e=None):
        """미리보기가 비어 있을 때 환경설정의 배경 그림을 깔아 줌"""
        try:
            if not self.msg.winfo_ismapped():
                return
            img = background_photo(self.msg.winfo_width(), self.msg.winfo_height())
            self._bg_img = img
            self.msg.configure(image=img or "", compound="center")
        except tk.TclError:
            pass

    def _width(self):
        self.update_idletasks()
        return max(200, self.body.winfo_width() - 40)

    def clear(self):
        if self.shell:
            self.shell.unload()
        if not self.nested and self.current:
            self.inner.clear()
        self.current = None
        self.images = []
        self._img_src = None
        self._pdf_path = None
        self._pdf_pw = None
        self._lock = None
        for f in self._unlocked:                 # 암호를 푼 임시 파일은 바로 지움
            shutil.rmtree(os.path.dirname(f), ignore_errors=True)
        self._unlocked = []
        self.page_limit = self.MAX_PDF_PAGES
        self.canvas.delete("all")
        self.msg.configure(text="파일을 선택하면 미리보기가 나옵니다.")
        self._show(self.msg)

    def show(self, path, pats, cache=None, use_shell=True):
        if path == self.current:
            return
        self.clear()
        self.current, self.pats, self.cache = path, pats, cache
        if not os.path.exists(path):
            self.msg.configure(text="파일이 없습니다 (옮겨졌거나 지워짐).")
            return
        if os.path.isdir(path):
            try:
                items = list_folder(path)
                nd = sum(1 for h in items if h["is_dir"])
                names = "\n".join(("📁 " if h["is_dir"] else "    ") + h["name"]
                                  for h in sorted(items, key=lambda h: (not h["is_dir"], h["name"].lower()))[:40])
                more = "\n    …" if len(items) > 40 else ""
                self.msg.configure(text=f"📁 {os.path.basename(path) or path}\n폴더 {nd}개 · 파일 {len(items) - nd}개"
                                        f"\n\n{names}{more}", anchor="nw", justify="left")
            except OSError as e:
                self.msg.configure(text=f"폴더를 읽을 수 없습니다: {e}")
            return
        self.msg.configure(anchor="center", justify="center")
        ext = os.path.splitext(path)[1].lower()
        lock = locked_kind(path, ext)
        if lock:
            self._lock = (path, ext, lock, use_shell)
            pw = SESSION_PASSWORDS.get(os.path.normcase(path))
            if pw is None or not self._unlock(pw):
                self._ask_password()
            return
        self._dispatch(path, ext, use_shell)

    def _ask_password(self, wrong=False):
        path, ext, lock, _ = self._lock
        self.lock_title.configure(text=f"{os.path.basename(path)}\n암호가 걸린 파일입니다")
        if lock == "hwp":
            self.lock_row.pack_forget()
            self.lock_msg.configure(foreground="#888", text=(
                "한글(HWP·HWPX) 암호 문서는 암호 방식이 공개되어 있지 않아\n미리보기를 할 수 없습니다.\n"
                "더블클릭하면 한글 프로그램에서 암호를 넣고 열 수 있습니다."))
        else:
            self.lock_row.pack()
            self.lock_msg.configure(
                foreground="#b0412b" if wrong else "#888",
                text="암호가 맞지 않습니다. 다시 입력해 주세요." if wrong else
                "암호를 입력하면 미리 볼 수 있습니다.\n(입력한 암호는 프로그램을 끌 때까지만 기억합니다)")
            self.pw_var.set("")
            self.after_idle(self.pw_entry.focus_set)
        self._show(self.lock_frame)

    def _unlock(self, pw=None):
        """암호로 열어 보기. 성공하면 True"""
        if not self._lock:
            return False
        path, ext, lock, use_shell = self._lock
        typed = pw is None
        if typed:
            pw = self.pw_var.get()
            if not pw:
                return False
        try:
            if lock == "pdf":
                pdfium.PdfDocument(path, password=pw).close()
                self._pdf_pw = pw
                self._show(self.pic_frame)
                self._render_pdf(path)
            elif lock == "office":
                tmp = office_decrypt(path, pw)
                self._unlocked.append(tmp)
                self._dispatch(tmp, ext, use_shell)
            else:
                return False
        except (ValueError, pdfium.PdfiumError if pdfium else ValueError):
            if typed:
                self._ask_password(wrong=True)
            return False
        except Exception as e:
            self._render_doc(path, error=f"암호를 풀었지만 열 수 없습니다: {e}")
            return True
        SESSION_PASSWORDS[os.path.normcase(path)] = pw
        return True

    def _dispatch(self, path, ext, use_shell):
        if use_shell and self.shell and ext not in ARCHIVE_EXTS:
            self.shell_zoomable = ext in ZOOMABLE_SHELL_EXTS
            self._show(self.shell_frame)
            self._layout_shell(reset=True)
            self.update_idletasks()
            if self.shell.show(path):
                return
        self.shell_zoomable = False
        try:
            if ext == ".pdf" and pdfium is not None:
                self._show(self.pic_frame)
                self._render_pdf(path)
            elif ext in IMAGE_EXTS:
                self._show(self.pic_frame)
                self._render_image(path)
            elif ext in ARCHIVE_EXTS and not self.nested:
                self._show(self.arc_frame)
                self._render_archive(path)
            elif ext in SHEET_EXTS:
                self._show(self.grid_frame)
                self._render_sheets(path)
            else:
                self._render_doc(path)
        except Exception as e:
            self._render_doc(path, error=str(e))

    def _text_of(self, path):
        t = self.cache.get_any(path) if self.cache else None
        if t is None:
            try:
                t = extract_text(path, nested=self.nested)[0]
            except Exception as e:
                t = f"(글자를 읽을 수 없음: {e})"
        return t

    def _highlight(self, widget, start, text):
        first = None
        for p in self.pats:
            for m in p.finditer(text):
                a = f"{start}+{m.start()}c"
                widget.tag_add("hl", a, f"{start}+{m.end()}c")
                if first is None or widget.compare(a, "<", first):
                    first = a
        return first

    # 탐색기 처리기 미리보기 크게 보기 (한글 문서)
    def set_shell_fit(self, mode):
        self.shell_fit = mode
        self._layout_shell()

    def shell_zoom_step(self, factor):
        if not self.shell_zoomable:
            return
        cur = self.shell_zoom if self.shell_fit == "custom" else 1.0
        if self.shell_fit == "height":
            cw = max(100, self.shell_cv.winfo_width())
            ch = max(100, self.shell_cv.winfo_height())
            cur = min(1.0, ch / (cw * PAGE_RATIO))
        self.shell_fit = "custom"
        self.shell_zoom = max(0.3, min(4.0, cur * factor))
        self._layout_shell()

    def shell_scroll(self, units):
        self.shell_cv.yview_scroll(units, "units")

    def _layout_shell(self, reset=False):
        """처리기 창 크기 정하기. 한글은 쪽 비율(A4)대로 키워서 캔버스 안에서 스크롤"""
        cv = self.shell_cv
        cw, ch = max(50, cv.winfo_width()), max(50, cv.winfo_height())
        if not self.shell_zoomable:
            self.shell_bar.pack_forget()
            w, h = cw, ch
        else:
            if not self.shell_bar.winfo_ismapped():
                self.shell_bar.pack(side="top", fill="x", pady=(0, 2), before=cv.master)
            if self.shell_fit == "height":
                w, h = cw, ch
                self.shell_zoom_var.set("세로 맞춤")
            elif self.shell_fit == "custom":
                w = int(cw * self.shell_zoom)
                h = max(ch, int(w * PAGE_RATIO))
                self.shell_zoom_var.set(f"{self.shell_zoom * 100:.0f}%")
            else:
                w, h = cw, max(ch, int(cw * PAGE_RATIO))
                self.shell_zoom_var.set("가로 맞춤")
            for m, b in self.shell_btns.items():
                try:
                    b.state(["pressed"] if m == self.shell_fit else ["!pressed"])
                except Exception:
                    pass
        cv.itemconfigure(self.host_win, width=w, height=h)
        cv.configure(scrollregion=(0, 0, w, h))
        if reset:
            cv.xview_moveto(0)
            cv.yview_moveto(0)

    # 맞춤·확대
    def set_fit(self, mode):
        self.fit_mode = mode
        self._redraw()

    def set_zoom(self, z):
        self.fit_mode = "custom"
        self.zoom = max(0.1, min(8.0, z))
        self._redraw()

    def zoom_step(self, factor):
        self.set_zoom(self._eff_zoom * factor)

    def _on_wheel(self, e):
        self.canvas.yview_scroll(int(-e.delta / 120) * 3, "units")

    def _effective_mode(self):
        if self.fit_mode != "auto":
            return self.fit_mode
        return "width" if self._pdf_path else "page"

    def _calc_scale(self, w, h, unit=1.0):
        """w,h = 원본 크기, unit = 실제 크기(100%)일 때의 배율"""
        self.canvas.update_idletasks()
        cw = max(200, self.canvas.winfo_width()) - 24
        ch = max(150, self.canvas.winfo_height()) - 20
        mode = self._effective_mode()
        if mode == "width":
            sc = cw / max(w, 1)
        elif mode == "height":
            sc = ch / max(h, 1)
        elif mode == "page":
            sc = min(cw / max(w, 1), ch / max(h, 1), unit)      # 작은 그림은 키우지 않음
        else:
            sc = self.zoom * unit
        sc = max(0.02, min(sc, 6000 / max(w, h, 1)))          # 너무 큰 그림은 메모리 때문에 제한
        self._eff_zoom = sc / unit
        self.zoom_var.set(f"{self._eff_zoom * 100:.0f}%")
        for m, btn in self.fit_btns.items():
            try:
                btn.state(["pressed"] if mode == m else ["!pressed"])
            except Exception:
                pass
        return sc

    def _redraw(self):
        if self._pdf_path:
            self._draw_pdf()
        elif self._img_src:
            self._draw_image()

    def _on_canvas_resize(self, e=None):
        if not (self._pdf_path or self._img_src) or self._effective_mode() == "custom":
            return
        if self._fit_job:
            self.after_cancel(self._fit_job)
        self._fit_job = self.after(250, self._redraw)

    # PDF
    def _render_pdf(self, path):
        self._pdf_path = path
        self._draw_pdf(reset=True)

    def _draw_pdf(self, reset=False):
        self._fit_job = None
        path = self._pdf_path
        if not path:
            return
        yfrac = 0.0 if reset else self.canvas.yview()[0]
        doc = pdfium.PdfDocument(path, password=self._pdf_pw)
        try:
            n = len(doc)
            limit = getattr(self, "page_limit", self.MAX_PDF_PAGES)
            sizes = [doc[i].get_size() for i in range(min(n, limit))]
            pw = max(w for w, _ in sizes)
            ph = sizes[0][1]
            sc = self._calc_scale(pw, ph, unit=96 / 72)
            self.canvas.delete("all")
            self.images = []
            cw = max(200, self.canvas.winfo_width())
            maxw = int(pw * sc)
            y = 10
            for i in range(len(sizes)):
                page = doc[i]
                bmp = page.render(scale=sc, force_bitmap_format=pdfium_c.FPDFBitmap_BGR, rev_byteorder=True)
                w, h, stride = bmp.width, bmp.height, bmp.stride
                raw = bytes(bmp.buffer)
                if stride != w * 3:
                    raw = b"".join(raw[r * stride:r * stride + w * 3] for r in range(h))
                bmp.close()
                page.close()
                img = tk.PhotoImage(data=b"P6 %d %d 255\n" % (w, h) + raw)
                self.images.append(img)
                x = max(12, (cw - w) // 2)
                self.canvas.create_image(x, y, anchor="nw", image=img)
                y += h + 10
            if n > limit:
                more = self.canvas.create_text(12, y + 4, anchor="nw", fill="#2a6fdb", font=(FONT[0], fsz(10), "underline"),
                                               text=f"▼ 다음 {min(self.MAX_PDF_PAGES, n - limit)}쪽 더 보기  ({limit}/{n}쪽 표시 중)")
                self.canvas.tag_bind(more, "<Button-1>", lambda e: self._more_pages())
                self.canvas.tag_bind(more, "<Enter>", lambda e: self.canvas.configure(cursor="hand2"))
                self.canvas.tag_bind(more, "<Leave>", lambda e: self.canvas.configure(cursor="fleur"))
                y += 34
            self.page_info.configure(text=f"{n}쪽")
            self.canvas.configure(scrollregion=(0, 0, max(cw, maxw + 24), y))
            self.canvas.yview_moveto(yfrac)
            if reset:
                self.canvas.xview_moveto(0)
        finally:
            doc.close()

    def _more_pages(self):
        self.page_limit = getattr(self, "page_limit", self.MAX_PDF_PAGES) + self.MAX_PDF_PAGES
        self._draw_pdf()

    # 그림
    def _render_image(self, path):
        self._img_src = path
        self._draw_image()

    def _image_size(self, src):
        if Image is not None:
            with Image.open(src) as im:
                w, h = im.size
                try:
                    o = im.getexif().get(0x0112, 1)     # 세로로 찍은 사진은 가로세로를 바꿔서 계산
                    if o in (5, 6, 7, 8):
                        w, h = h, w
                except Exception:
                    pass
                return w, h
        img = tk.PhotoImage(file=src)
        return img.width(), img.height()

    def _draw_image(self):
        self._fit_job = None
        if self._img_src is None:
            return
        w, h = self._image_size(self._img_src)
        sc = self._calc_scale(w, h)
        img, _ = make_photo(self._img_src, max(1, int(w * sc)), max(1, int(h * sc)), upscale=sc > 1)
        self.images = [img]
        self.canvas.delete("all")
        cw = max(200, self.canvas.winfo_width())
        iw, ih = img.width(), img.height()
        self.canvas.create_image(max(12, (cw - iw) // 2), 10, anchor="nw", image=img)
        self.page_info.configure(text=f"{w:,} × {h:,} 픽셀 · {fmt_size(os.path.getsize(self._img_src))}")
        self.canvas.configure(scrollregion=(0, 0, max(cw, iw + 24), ih + 20))

    # 표
    def _render_sheets(self, path):
        self.sheets = read_sheets(path)
        if not self.sheets:
            raise RuntimeError("시트가 없음")
        names = [n for n, _ in self.sheets]
        self.sheet_cb.configure(values=names)
        best = 0
        if self.pats:                          # 검색어가 있는 시트를 먼저 보여 줌
            for i, (_, cells) in enumerate(self.sheets):
                if any(p.search(v) for v in cells.values() for p in self.pats):
                    best = i
                    break
        self.sheet_var.set(names[best])
        self._fill_grid()

    def _fill_grid(self):
        name = self.sheet_var.get()
        cells = next((c for n, c in self.sheets if n == name), {})
        g = self.grid
        g.delete(*g.get_children())
        nrows = max((r for r, _ in cells), default=-1) + 1
        ncols = max((c for _, c in cells), default=-1) + 1
        ncols = max(ncols, 1)
        cols = ["#"] + [self._col_name(c) for c in range(ncols)]
        g.configure(columns=cols)
        g.heading("#", text="")
        g.column("#", width=44, anchor="e", stretch=False)
        for c in range(ncols):
            nm = self._col_name(c)
            g.heading(nm, text=nm)
            g.column(nm, width=110, anchor="w", stretch=False)
        first_hit = None
        for r in range(nrows):
            vals = [cells.get((r, c), "") for c in range(ncols)]
            hit = bool(self.pats) and any(p.search(v) for v in vals if v for p in self.pats)
            iid = g.insert("", "end", values=[r + 1] + [v.replace("\n", " ")[:200] for v in vals],
                           tags=("hit",) if hit else ())
            if hit and first_hit is None:
                first_hit = iid
        if first_hit:
            g.see(first_hit)
        more = " (앞부분만 표시)" if nrows >= GRID_ROWS else ""
        self.grid_info.configure(text=f"{len(self.sheets)}개 시트 · {nrows:,}행{more} · 노란 줄 = 검색어 있음")

    @staticmethod
    def _col_name(c):
        s = ""
        c += 1
        while c:
            c, r = divmod(c - 1, 26)
            s = chr(65 + r) + s
        return s

    # 압축 파일
    def _render_archive(self, path):
        t = self.arc_tree
        t.delete(*t.get_children())
        self.arc_entries = {}
        self.inner.clear()
        try:
            entries = archive_entries(path)
        except Exception as e:
            self._render_doc(path, error=str(e))
            return
        text = self.cache.get_any(path) if self.cache else None
        hit_names = set()
        if text and self.pats:
            for p in self.pats:
                for m in p.finditer(text):
                    sec = archive_section(text, m.start())
                    if sec == "(압축 파일 목록)":
                        line_s = text.rfind("\n", 0, m.start()) + 1
                        line_e = text.find("\n", m.end())
                        hit_names.add(text[line_s:line_e if line_e >= 0 else len(text)])
                    elif sec:
                        hit_names.add(sec)
        files = [e for e in entries if not e["dir"]]
        total = sum(e["size"] or 0 for e in files)
        first = None
        for i, e in enumerate(sorted(files, key=lambda e: e["name"].lower())):
            iid = str(i)
            self.arc_entries[iid] = e
            tags = ("hit",) if e["name"] in hit_names else (("dim",) if e["enc"] else ())
            label = e["name"] + ("  🔒" if e["enc"] else "")
            t.insert("", "end", iid=iid, values=(label, fmt_size(e["size"]) if e["size"] else "", e["mtime"]),
                     tags=tags)
            if tags == ("hit",) and first is None:
                first = iid
        msg = f"파일 {len(files):,}개 · 풀면 {fmt_size(total)}"
        if hit_names:
            msg += f" · 검색어가 든 파일 {len(hit_names)}개(노란 줄)"
        self.arc_info.configure(text=msg)
        target = first or (t.get_children()[0] if t.get_children() else None)
        if target:
            t.selection_set(target)
            t.see(target)

    def _arc_schedule(self):
        if self._arc_job:
            self.after_cancel(self._arc_job)
        self._arc_job = self.after(250, self._arc_preview)

    def _arc_extract(self):
        sel = self.arc_tree.selection()
        e = self.arc_entries.get(sel[0]) if sel else None
        if not e:
            return None, None
        if e["enc"]:
            return e, "암호가 걸린 파일이라 미리 볼 수 없습니다."
        if (e["size"] or 0) > self.MAX_INNER_PREVIEW:
            return e, f"파일이 커서({fmt_size(e['size'])}) 미리보기를 건너뜁니다. '고른 파일 열기'를 누르세요."
        dest = os.path.join(TMP_DIR, "preview")
        shutil.rmtree(dest, ignore_errors=True)
        try:
            return archive_extract(self.current, e, os.path.join(dest, str(int(time.time() * 1000)))), None
        except Exception as ex:
            return e, f"풀 수 없음: {ex}"

    def _arc_preview(self):
        self._arc_job = None
        f, err = self._arc_extract()
        if f is None:
            return
        if err:
            self.inner.clear()
            self.inner.msg.configure(text=err)
            return
        self.inner.current = None
        self.inner.show(f, self.pats, None, use_shell=False)

    def _arc_open(self):
        sel = self.arc_tree.selection()
        e = self.arc_entries.get(sel[0]) if sel else None
        if not e:
            return
        if e["enc"]:
            messagebox.showinfo(APP_NAME, "암호가 걸린 파일입니다. 압축 프로그램으로 열어 주세요.")
            return
        try:
            f = archive_extract(self.current, e, os.path.join(TMP_DIR, "open", str(int(time.time() * 1000))))
            os.startfile(f)
        except Exception as ex:
            messagebox.showerror(APP_NAME, f"열 수 없습니다.\n{ex}")

    # 문서(첫 쪽 그림 + 글자) · 정보 카드
    def _render_doc(self, path, error=None):
        t = self.text
        t.configure(state="normal")
        t.delete("1.0", "end")
        self.images = []
        try:
            st = os.stat(path)
            info = f"{os.path.basename(path)}\n"
            t.insert("end", info, "big")
            t.insert("end", f"{fmt_size(st.st_size)} · 수정 {datetime.fromtimestamp(st.st_mtime):%Y-%m-%d %H:%M}"
                            f" · 만든 날 {datetime.fromtimestamp(st.st_ctime):%Y-%m-%d %H:%M}\n\n", "info")
        except OSError:
            pass
        if error:
            t.insert("end", f"※ {error}\n\n", "note")
        thumb = embedded_thumbnail(path)
        if thumb:
            try:
                w = self._width()
                img, _ = make_photo(thumb, min(w, 700), 900, upscale=True)
                self.images.append(img)
                t.image_create("end", image=img, padx=4, pady=4)
                t.insert("end", "\n(문서에 저장된 첫 쪽 미리보기 그림)\n\n", ("info",))
            except Exception:
                pass
        ext = os.path.splitext(path)[1].lower()
        text = "" if error and ext in ARCHIVE_EXTS else self._text_of(path)
        first = None
        if text.strip():
            if not thumb:
                t.insert("end", "※ 원래 모양 미리보기를 지원하지 않아 글자만 보여 줍니다.\n\n", "note")
            start = t.index("end-1c")
            shown = text[:300000]
            t.insert("end", shown)
            first = self._highlight(t, start, shown)
        elif not thumb and not error:
            kind = "그림" if ext in IMAGE_EXTS else ("소리·영상" if ext in (".mp3", ".mp4", ".wav", ".avi", ".mkv", ".mov", ".wmv", ".m4a") else "이")
            t.insert("end", f"{kind} 형식은 내용을 직접 보여 줄 수 없습니다.\n더블클릭하면 연결된 프로그램으로 열립니다.", "note")
        t.configure(state="disabled")
        self._show(self.doc_frame)
        if first:
            t.see(first)
        else:
            t.see("1.0")


# ───────────── 파일 다루기 (복사·이동·삭제는 윈도우 탐색기와 같은 방식) ─────────────
FO_MOVE, FO_COPY, FO_DELETE = 1, 2, 3
FOF_RENAMEONCOLLISION, FOF_ALLOWUNDO, FOF_NOCONFIRMMKDIR, FOF_WANTNUKEWARNING = 0x8, 0x40, 0x200, 0x4000
CF_HDROP = 15

if sys.platform == "win32":
    import ctypes
    from ctypes import wintypes as _wt

    class _SHFILEOPSTRUCTW(ctypes.Structure):
        if ctypes.sizeof(ctypes.c_void_p) == 4:
            _pack_ = 1                                # 32비트 윈도우에서는 1바이트 정렬
        _fields_ = [("hwnd", _wt.HWND), ("wFunc", _wt.UINT), ("pFrom", ctypes.c_void_p),
                    ("pTo", ctypes.c_void_p), ("fFlags", ctypes.c_ushort), ("fAnyOperationsAborted", _wt.BOOL),
                    ("hNameMappings", ctypes.c_void_p), ("lpszProgressTitle", _wt.LPCWSTR)]

    _k32 = ctypes.windll.kernel32
    _u32 = ctypes.windll.user32
    _sh32 = ctypes.windll.shell32
    _k32.GlobalAlloc.argtypes = [_wt.UINT, ctypes.c_size_t]
    _k32.GlobalAlloc.restype = ctypes.c_void_p
    _k32.GlobalLock.argtypes = [ctypes.c_void_p]
    _k32.GlobalLock.restype = ctypes.c_void_p
    _k32.GlobalUnlock.argtypes = [ctypes.c_void_p]
    _u32.SetClipboardData.argtypes = [_wt.UINT, ctypes.c_void_p]
    _u32.SetClipboardData.restype = ctypes.c_void_p
    _u32.GetClipboardData.argtypes = [_wt.UINT]
    _u32.GetClipboardData.restype = ctypes.c_void_p
    _u32.OpenClipboard.argtypes = [_wt.HWND]
    _u32.RegisterClipboardFormatW.argtypes = [_wt.LPCWSTR]
    _u32.RegisterClipboardFormatW.restype = _wt.UINT
    _sh32.DragQueryFileW.argtypes = [ctypes.c_void_p, _wt.UINT, _wt.LPWSTR, _wt.UINT]
    _sh32.DragQueryFileW.restype = _wt.UINT
    _sh32.SHFileOperationW.argtypes = [ctypes.POINTER(_SHFILEOPSTRUCTW)]


def _multi_sz(paths):
    s = "\0".join(os.path.normpath(p) for p in paths) + "\0\0"
    return (ctypes.c_wchar * len(s))(*s)


def shell_file_op(func, paths, dest=None, hwnd=0, rename_on_collision=False):
    """True = 끝까지 진행, False = 사용자가 취소. 충돌·확인 창은 윈도우가 띄움"""
    if not paths:
        return False
    if sys.platform != "win32":                       # (윈도우가 아닐 때 쓰는 간단한 대체 방식)
        for p in paths:
            if func == FO_DELETE:
                shutil.rmtree(p) if os.path.isdir(p) else os.remove(p)
                continue
            target = os.path.join(dest, os.path.basename(p))
            if os.path.exists(target):
                if not rename_on_collision:
                    raise FileExistsError(target)
                base, ext = os.path.splitext(os.path.basename(p))
                k = 2
                while os.path.exists(target):
                    target = os.path.join(dest, f"{base} ({k}){ext}")
                    k += 1
            if func == FO_MOVE:
                shutil.move(p, target)
            elif os.path.isdir(p):
                shutil.copytree(p, target)
            else:
                shutil.copy2(p, target)
        return True
    src = _multi_sz(paths)
    to = _multi_sz([dest]) if dest else None
    flags = FOF_ALLOWUNDO | FOF_NOCONFIRMMKDIR
    if func == FO_DELETE:
        flags |= FOF_WANTNUKEWARNING
    if rename_on_collision:
        flags |= FOF_RENAMEONCOLLISION
    op = _SHFILEOPSTRUCTW(hwnd or None, func, ctypes.addressof(src), ctypes.addressof(to) if to else None,
                          flags, False, None, None)
    rc = _sh32.SHFileOperationW(ctypes.byref(op))
    if rc not in (0, 0x4C7):                          # 0x4C7 = 사용자가 취소
        raise OSError(f"파일 작업 실패 (코드 {rc:#x})")
    return rc == 0 and not op.fAnyOperationsAborted


def clipboard_set_files(paths, cut, hwnd=0):
    """윈도우 클립보드에 파일을 올림 → 탐색기에서도 붙여넣기 가능"""
    if sys.platform != "win32" or not paths:
        return False
    data = ("\0".join(os.path.normpath(p) for p in paths) + "\0\0").encode("utf-16-le")
    header = struct.pack("<IiiII", 20, 0, 0, 0, 1)    # DROPFILES: 파일 목록 위치, 좌표, fNC, fWide
    blob = header + data
    if not _u32.OpenClipboard(hwnd or None):
        return False
    try:
        _u32.EmptyClipboard()
        h = _k32.GlobalAlloc(0x0042, len(blob))
        p = _k32.GlobalLock(h)
        ctypes.memmove(p, blob, len(blob))
        _k32.GlobalUnlock(h)
        _u32.SetClipboardData(CF_HDROP, h)
        eff = _k32.GlobalAlloc(0x0042, 4)
        p = _k32.GlobalLock(eff)
        ctypes.memmove(p, struct.pack("<I", 2 if cut else 5), 4)
        _k32.GlobalUnlock(eff)
        _u32.SetClipboardData(_u32.RegisterClipboardFormatW("Preferred DropEffect"), eff)
        return True
    finally:
        _u32.CloseClipboard()


def clipboard_get_files(hwnd=0):
    """윈도우 클립보드의 파일 목록과 잘라내기 여부 (탐색기에서 복사한 것 포함)"""
    if sys.platform != "win32" or not _u32.OpenClipboard(hwnd or None):
        return [], False
    try:
        h = _u32.GetClipboardData(CF_HDROP)
        if not h:
            return [], False
        n = _sh32.DragQueryFileW(h, 0xFFFFFFFF, None, 0)
        paths = []
        for i in range(n):
            ln = _sh32.DragQueryFileW(h, i, None, 0)
            buf = ctypes.create_unicode_buffer(ln + 1)
            _sh32.DragQueryFileW(h, i, buf, ln + 1)
            paths.append(buf.value)
        cut = False
        he = _u32.GetClipboardData(_u32.RegisterClipboardFormatW("Preferred DropEffect"))
        if he:
            p = _k32.GlobalLock(he)
            if p:
                cut = bool(ctypes.c_uint32.from_address(p).value & 2)
                _k32.GlobalUnlock(he)
        return paths, cut
    finally:
        _u32.CloseClipboard()


def clipboard_clear_files(hwnd=0):
    if sys.platform == "win32" and _u32.OpenClipboard(hwnd or None):
        _u32.EmptyClipboard()
        _u32.CloseClipboard()


def same_drive(a, b):
    return os.path.splitdrive(os.path.abspath(a))[0].lower() == os.path.splitdrive(os.path.abspath(b))[0].lower()


def is_inside(child, parent):
    c, p = os.path.normcase(os.path.abspath(child)), os.path.normcase(os.path.abspath(parent))
    return c == p or c.startswith(p.rstrip("\\/") + os.sep)


def list_folder(folder):
    """폴더 내용 (숨김·시스템 파일 제외)"""
    out = []
    with os.scandir(folder) as it:
        for e in it:
            try:
                st = e.stat()
            except OSError:
                continue
            if getattr(st, "st_file_attributes", 0) & 0x6:     # 숨김(2)·시스템(4)
                continue
            if e.name.startswith("~$"):
                continue
            is_dir = e.is_dir()
            out.append({"path": e.path, "name": e.name, "folder": folder, "is_dir": is_dir,
                        "size": -1 if is_dir else st.st_size, "count": 0, "snippets": [], "name_hit": False,
                        "mtime": datetime.fromtimestamp(st.st_mtime).strftime("%Y-%m-%d %H:%M"), "ts": st.st_mtime})
    return out


def type_name(h):
    if h.get("is_dir"):
        return "파일 폴더"
    ext = os.path.splitext(h["name"])[1]
    return (ext[1:].upper() + " 파일") if ext else "파일"


# ───────────── 이름 바꾸기 (한 개 · 여러 개 연번 · 첫 문장으로) ─────────────
BAD_NAME_RE = re.compile(r'[\\/:*?"<>|\x00-\x1f]')
RESERVED_NAMES = {"CON", "PRN", "AUX", "NUL"} | {f"COM{i}" for i in range(1, 10)} | {f"LPT{i}" for i in range(1, 10)}


def split_name(path, name=None):
    """(이름, 확장자). 폴더는 확장자 없음"""
    name = name or os.path.basename(path)
    if os.path.isdir(path):
        return name, ""
    base, ext = os.path.splitext(name)
    if not base:                                    # '.gitignore' 같은 이름
        return name, ""
    return base, ext


def clean_name(text, limit=60):
    """파일 이름으로 쓸 수 있게 다듬기 (못 쓰는 글자 빼기, 공백 정리, 길이 제한)"""
    t = BAD_NAME_RE.sub(" ", text or "")
    t = re.sub(r"\s+", " ", t).strip(" .")
    if len(t) > limit:
        cut = t[:limit]
        sp = cut.rfind(" ")
        t = (cut[:sp] if sp > limit * 0.6 else cut).strip(" .")
    if t.upper() in RESERVED_NAMES:
        t += "_"
    return t


def first_sentence(path, cache=None, limit=60):
    """문서 내용의 첫 문장(첫 줄). 글자가 없으면 빈 문자열"""
    if os.path.isdir(path):
        return ""
    text = cache.get_any(path) if cache else None
    if text is None:
        try:
            text = extract_text(path, nested=True)[0]
        except Exception:
            text = ""
    if os.path.splitext(path)[1].lower() in ARCHIVE_EXTS:
        return ""
    for line in (text or "").splitlines():
        line = line.strip()
        if len(re.sub(r"[\W_]+", "", line)) < 2:        # 기호·숫자 한 글자 줄은 건너뜀
            continue
        m = re.search(r"(.+?[.?!。])(\s|$)", line)       # 줄 안에서 첫 문장 끝까지
        s = m.group(1) if m and len(m.group(1)) >= 4 else line
        s = clean_name(s, limit)
        if s:
            return s
    return ""


def unique_target(folder, base, ext, taken):
    """같은 이름이 있으면 ' (2)', ' (3)'… 을 붙인 이름"""
    cand = base + ext
    k = 2
    while os.path.normcase(cand) in taken:
        cand = f"{base} ({k}){ext}"
        k += 1
    return cand


def do_renames(pairs):
    """[(원래 경로, 새 경로)] 한꺼번에 바꾸기. 서로 이름이 겹쳐도 되게 임시 이름을 거쳐 감.
    반환: (성공 수, 실패 메시지 목록)"""
    import uuid
    pairs = [(a, b) for a, b in pairs if os.path.normcase(a) != os.path.normcase(b) or a != b]
    temp = []
    errors = []
    for a, b in pairs:
        t = os.path.join(os.path.dirname(a), f".~ren_{uuid.uuid4().hex[:8]}")
        try:
            os.rename(a, t)
            temp.append((t, a, b))
        except OSError as e:
            errors.append(f"{os.path.basename(a)}: {e.strerror or e}")
    ok = 0
    for t, a, b in temp:
        try:
            if os.path.exists(b):
                raise FileExistsError("같은 이름이 이미 있음")
            os.rename(t, b)
            ok += 1
        except OSError as e:
            errors.append(f"{os.path.basename(a)}: {e.strerror or e}")
            try:
                os.rename(t, a)                     # 실패하면 원래 이름으로 되돌림
            except OSError:
                pass
    return ok, errors


class RenameDialog:
    """파일 하나 이름 바꾸기: 긴 입력칸, 확장자는 고정, '첫 문장으로' 버튼"""

    def __init__(self, pane, h):
        self.pane, self.h = pane, h
        self.result = None
        self.base, self.ext = split_name(h["path"], h["name"])
        w = self.win = tk.Toplevel(pane)
        w.title("이름 바꾸기")
        w.transient(pane.winfo_toplevel())
        w.resizable(True, False)
        f = ttk.Frame(w, padding=14)
        f.pack(fill="both", expand=True)
        ttk.Label(f, text=f"지금 이름:  {h['name']}", foreground="#777").pack(anchor="w")
        row = ttk.Frame(f)
        row.pack(fill="x", pady=(8, 4))
        self.var = tk.StringVar(value=self.base)
        width = max(50, min(110, len(self.base) + 12))
        self.entry = ttk.Entry(row, textvariable=self.var, width=width, font=(FONT[0], fsz(11)))
        self.entry.pack(side="left", fill="x", expand=True, ipady=2)
        if self.ext:
            ttk.Label(row, text=self.ext, font=(FONT[0], fsz(11), "bold"), foreground="#555").pack(side="left", padx=(4, 0))
        hint = "확장자(" + self.ext + ")는 바뀌지 않습니다." if self.ext else "폴더 이름"
        ttk.Label(f, text=hint, foreground="#888").pack(anchor="w")
        self.msg = ttk.Label(f, text="", foreground="#b0412b")
        self.msg.pack(anchor="w", pady=(4, 0))
        bf = ttk.Frame(f)
        bf.pack(fill="x", pady=(8, 0))
        if not h.get("is_dir"):
            ttk.Button(bf, text="📝 문서 첫 문장으로", command=self.use_first).pack(side="left")
        ttk.Button(bf, text="취소", command=w.destroy).pack(side="right")
        ttk.Button(bf, text="바꾸기", style="Accent.TButton", command=self.ok).pack(side="right", padx=4)
        w.bind("<Return>", lambda e: self.ok())
        w.bind("<Escape>", lambda e: w.destroy())
        center_on(w, pane.winfo_toplevel())
        self.entry.focus_set()
        self.entry.select_range(0, "end")
        self.entry.icursor("end")
        w.grab_set()

    def use_first(self):
        s = first_sentence(self.h["path"], self.pane.app.cache)
        if s:
            self.var.set(s)
            self.msg.configure(text="")
            self.entry.icursor("end")
        else:
            self.msg.configure(text="문서에서 글자를 찾지 못했습니다 (그림·스캔 문서 등).")

    def ok(self):
        base = self.var.get().strip()
        cleaned = clean_name(base, 200)
        if not cleaned:
            self.msg.configure(text="이름을 입력해 주세요.")
            return
        if BAD_NAME_RE.search(base):
            self.msg.configure(text='\\ / : * ? " < > | 는 이름에 쓸 수 없습니다.')
            return
        new = cleaned + self.ext
        path = self.h["path"]
        target = os.path.join(os.path.dirname(path), new)
        if new == self.h["name"]:
            self.win.destroy()
            return
        if os.path.exists(target) and os.path.normcase(target) != os.path.normcase(path):
            self.msg.configure(text="같은 이름이 이미 있습니다.")
            return
        self.result = target
        self.win.destroy()


class BatchRenameDialog:
    """여러 파일 이름 한꺼번에: 연번 / 각 문서 첫 문장 / 첫 문장 + 연번. 확장자는 그대로"""
    MODES = (("seq", "새 이름 + 연번"), ("first", "각 문서의 첫 문장"), ("first_seq", "첫 문장 + 연번"))

    def __init__(self, pane, items):
        self.pane, self.items = pane, items           # [(경로, 이름, 폴더 여부)] 목록 순서대로
        self.result = None
        self._firsts = {}
        w = self.win = tk.Toplevel(pane)
        w.title(f"이름 바꾸기 — {len(items)}개")
        w.transient(pane.winfo_toplevel())
        f = ttk.Frame(w, padding=14)
        f.pack(fill="both", expand=True)
        top = ttk.Frame(f)
        top.pack(fill="x")
        self.mode = tk.StringVar(value="seq")
        for i, (k, lb) in enumerate(self.MODES):
            ttk.Radiobutton(top, text=lb, value=k, variable=self.mode, command=self.refresh).grid(row=0, column=i, sticky="w", padx=(0, 14))
        opt = ttk.Frame(f)
        opt.pack(fill="x", pady=(10, 4))
        ttk.Label(opt, text="새 이름").grid(row=0, column=0, sticky="w")
        first_base = split_name(items[0][0], items[0][1])[0]
        self.base = tk.StringVar(value=re.sub(r"[\s_\-]*\(?\d+\)?$", "", first_base) or first_base)
        ttk.Entry(opt, textvariable=self.base, width=40).grid(row=0, column=1, columnspan=3, sticky="w", padx=4)
        ttk.Label(opt, text="시작 번호").grid(row=1, column=0, sticky="w", pady=(6, 0))
        self.start = tk.StringVar(value="1")
        ttk.Spinbox(opt, from_=0, to=99999, width=6, textvariable=self.start, command=self.refresh).grid(row=1, column=1, sticky="w", padx=4, pady=(6, 0))
        ttk.Label(opt, text="자릿수").grid(row=1, column=2, sticky="e", pady=(6, 0))
        self.digits = tk.StringVar(value=str(max(2, len(str(len(items))))))
        ttk.Spinbox(opt, from_=1, to=6, width=4, textvariable=self.digits, command=self.refresh).grid(row=1, column=3, sticky="w", padx=4, pady=(6, 0))
        ttk.Label(opt, text="번호 위치").grid(row=2, column=0, sticky="w", pady=(6, 0))
        self.pos = tk.StringVar(value="뒤")
        pf = ttk.Frame(opt)
        pf.grid(row=2, column=1, columnspan=3, sticky="w", padx=4, pady=(6, 0))
        for v in ("앞", "뒤"):
            ttk.Radiobutton(pf, text=v, value=v, variable=self.pos, command=self.refresh).pack(side="left", padx=(0, 8))
        ttk.Label(pf, text="   구분 글자").pack(side="left")
        self.sep = tk.StringVar(value="_")
        ttk.Combobox(pf, textvariable=self.sep, values=["_", "-", " ", ".", ""], width=4).pack(side="left", padx=4)
        for v in (self.base, self.start, self.digits, self.sep):
            v.trace_add("write", lambda *a: self.refresh())

        tf = ttk.Frame(f)
        tf.pack(fill="both", expand=True, pady=(8, 0))
        self.tree = ttk.Treeview(tf, columns=("old", "new"), show="headings", height=min(14, max(5, len(items))))
        self.tree.heading("old", text="지금 이름")
        self.tree.heading("new", text="바뀔 이름")
        self.tree.column("old", width=330)
        self.tree.column("new", width=380)
        sb = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.tree.pack(fill="both", expand=True)
        self.tree.tag_configure("warn", foreground="#b0412b")
        ttk.Label(f, text="확장자는 그대로 둡니다. 같은 이름이 생기면 끝에 (2), (3)을 붙입니다.  순서는 목록에 보이는 순서입니다.",
                  foreground="#888").pack(anchor="w", pady=(6, 0))
        self.msg = ttk.Label(f, text="", foreground="#b0412b")
        self.msg.pack(anchor="w")
        bf = ttk.Frame(f)
        bf.pack(fill="x", pady=(8, 0))
        ttk.Button(bf, text="취소", command=w.destroy).pack(side="right")
        ttk.Button(bf, text=f"{len(items)}개 바꾸기", style="Accent.TButton", command=self.ok).pack(side="right", padx=4)
        w.bind("<Escape>", lambda e: w.destroy())
        self.refresh()
        center_on(w, pane.winfo_toplevel())
        w.grab_set()

    def _first(self, path):
        if path not in self._firsts:
            self._firsts[path] = first_sentence(path, self.pane.app.cache, 50)
        return self._firsts[path]

    def plan(self):
        """[(원래 경로, 새 이름, 표시)]"""
        mode = self.mode.get()
        try:
            n0 = int(self.start.get())
        except ValueError:
            n0 = 1
        try:
            dg = max(1, min(6, int(self.digits.get())))
        except ValueError:
            dg = 2
        sep = self.sep.get()
        base = clean_name(self.base.get(), 120)
        out = []
        folder_taken = {}
        batch = {os.path.normcase(p) for p, _, _ in self.items}
        for i, (path, name, is_dir) in enumerate(self.items):
            old_base, ext = split_name(path, name)
            num = str(n0 + i).zfill(dg)
            if mode == "seq":
                core = base or old_base
                nb = f"{num}{sep}{core}" if self.pos.get() == "앞" else f"{core}{sep}{num}"
            else:
                fs = self._first(path) or old_base
                if mode == "first":
                    nb = fs
                else:
                    nb = f"{num}{sep}{fs}" if self.pos.get() == "앞" else f"{fs}{sep}{num}"
            nb = clean_name(nb, 150) or old_base
            folder = os.path.dirname(path)
            if folder not in folder_taken:              # 이 폴더에 이미 있는 이름(이번에 바꿀 파일은 빼고)
                try:
                    folder_taken[folder] = {os.path.normcase(x) for x in os.listdir(folder)
                                            if os.path.normcase(os.path.join(folder, x)) not in batch}
                except OSError:
                    folder_taken[folder] = set()
            taken = folder_taken[folder]
            new = unique_target(folder, nb, ext, taken)
            taken.add(os.path.normcase(new))
            out.append((path, new, new != nb + ext))
        return out

    def refresh(self):
        try:
            plan = self.plan()
        except Exception:
            return
        self.tree.delete(*self.tree.get_children())
        for (path, new, bumped), (_, name, _) in zip(plan, self.items):
            self.tree.insert("", "end", values=(name, new + ("   ⚠ 같은 이름 있음" if bumped else "")),
                             tags=("warn",) if bumped else ())

    def ok(self):
        plan = self.plan()
        self.result = [(p, os.path.join(os.path.dirname(p), new)) for p, new, _ in plan]
        self.win.destroy()


# ───────────────────────── 검색 칸(분할 화면 하나) ─────────────────────────
OPTION_LABELS = [("recursive", "하위 폴더 포함", True), ("name_search", "본문 검색 때 파일명도 함께", True),
                 ("ignore_space", "띄어쓰기 무시", True), ("ocr", "스캔 PDF 글자 인식", True),
                 ("shell_preview", "원래 모양 미리보기", True)]


# ───────────── 윈도우 탐색기와 끌어다 놓기 (OLE 드래그 앤 드롭) ─────────────
# 탐색기·바탕화면·다른 프로그램과 파일을 끌어서 주고받음. 끄는 동안 탐색기처럼 파일 그림과 '이동/복사' 표시가 따라다님.
OLE_DND = None
if sys.platform == "win32" and struct.calcsize("P") == 8:
    try:
        import ctypes
        from ctypes import wintypes as _wt

        class _OLE:
            DROPEFFECT_NONE, DROPEFFECT_COPY, DROPEFFECT_MOVE, DROPEFFECT_LINK = 0, 1, 2, 4
            MK_SHIFT, MK_CONTROL, MK_ALT = 0x4, 0x8, 0x20
            CF_HDROP, TYMED_HGLOBAL, DVASPECT_CONTENT = 15, 1, 1
            S_OK, E_NOINTERFACE, E_UNEXPECTED = 0, 0x80004002 - 2 ** 32, 0x8000FFFF - 2 ** 32

            class GUID(ctypes.Structure):
                _fields_ = [("a", ctypes.c_uint32), ("b", ctypes.c_uint16), ("c", ctypes.c_uint16),
                            ("d", ctypes.c_ubyte * 8)]

                @classmethod
                def of(cls, text):
                    g = cls()
                    ctypes.oledll.ole32.CLSIDFromString(ctypes.c_wchar_p(text), ctypes.byref(g))
                    return g

                def same(self, other):
                    return bytes(self) == bytes(other)

            class FORMATETC(ctypes.Structure):
                _fields_ = [("cfFormat", ctypes.c_ushort), ("ptd", ctypes.c_void_p), ("dwAspect", ctypes.c_ulong),
                            ("lindex", ctypes.c_long), ("tymed", ctypes.c_ulong)]

            class STGMEDIUM(ctypes.Structure):
                _fields_ = [("tymed", ctypes.c_ulong), ("hGlobal", ctypes.c_void_p), ("pUnk", ctypes.c_void_p)]

            class POINT(ctypes.Structure):
                _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]

        _O = _OLE
        _ole32 = ctypes.windll.ole32
        _shell32 = ctypes.windll.shell32
        _O.IID_IUnknown = _O.GUID.of("{00000000-0000-0000-C000-000000000046}")
        _O.IID_IDropTarget = _O.GUID.of("{00000122-0000-0000-C000-000000000046}")
        _O.IID_IDataObject = _O.GUID.of("{0000010e-0000-0000-C000-000000000046}")
        _O.IID_IDropTargetHelper = _O.GUID.of("{4657278B-411B-11D2-839A-00C04FD918D0}")
        _O.CLSID_DragDropHelper = _O.GUID.of("{4657278A-411B-11D2-839A-00C04FD918D0}")
        _O.BHID_DataObject = _O.GUID.of("{B8C0BD9F-ED24-455C-83E6-D5390C4FE8C4}")
        _shell32.SHParseDisplayName.argtypes = [ctypes.c_wchar_p, ctypes.c_void_p, ctypes.POINTER(ctypes.c_void_p),
                                                ctypes.c_ulong, ctypes.c_void_p]
        _shell32.SHCreateShellItemArrayFromIDLists.argtypes = [ctypes.c_uint, ctypes.POINTER(ctypes.c_void_p),
                                                               ctypes.POINTER(ctypes.c_void_p)]
        _shell32.SHDoDragDrop.argtypes = [_wt.HWND, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_ulong,
                                          ctypes.POINTER(ctypes.c_ulong)]
        _shell32.DragQueryFileW.argtypes = [ctypes.c_void_p, ctypes.c_uint, ctypes.c_wchar_p, ctypes.c_uint]
        _shell32.DragQueryFileW.restype = ctypes.c_uint
        _ole32.RegisterDragDrop.argtypes = [_wt.HWND, ctypes.c_void_p]
        _ole32.RevokeDragDrop.argtypes = [_wt.HWND]
        _ole32.ReleaseStgMedium.argtypes = [ctypes.c_void_p]
        _ole32.CoTaskMemFree.argtypes = [ctypes.c_void_p]
        _ole32.CoCreateInstance.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_ulong, ctypes.c_void_p,
                                            ctypes.POINTER(ctypes.c_void_p)]

        def _vcall(ptr, index, restype, argtypes, *args):
            """COM 객체(포인터)의 index번째 함수 부르기"""
            vtbl = ctypes.cast(ptr, ctypes.POINTER(ctypes.POINTER(ctypes.c_void_p)))[0]
            fn = ctypes.WINFUNCTYPE(restype, ctypes.c_void_p, *argtypes)(vtbl[index])
            return fn(ptr, *args)

        def _release(ptr):
            if ptr:
                _vcall(ptr, 2, ctypes.c_ulong, [])

        def _files_from_dataobject(pdo):
            """끌어 온 내용(IDataObject)에서 파일 경로 목록(CF_HDROP)을 꺼냄"""
            fe = _O.FORMATETC(_O.CF_HDROP, None, _O.DVASPECT_CONTENT, -1, _O.TYMED_HGLOBAL)
            st = _O.STGMEDIUM()
            hr = _vcall(pdo, 3, ctypes.HRESULT if False else ctypes.c_long,
                        [ctypes.POINTER(_O.FORMATETC), ctypes.POINTER(_O.STGMEDIUM)], ctypes.byref(fe), ctypes.byref(st))
            if hr != 0:
                return []
            out = []
            try:
                n = _shell32.DragQueryFileW(st.hGlobal, 0xFFFFFFFF, None, 0)
                for i in range(n):
                    ln = _shell32.DragQueryFileW(st.hGlobal, i, None, 0)
                    buf = ctypes.create_unicode_buffer(ln + 1)
                    _shell32.DragQueryFileW(st.hGlobal, i, buf, ln + 1)
                    out.append(buf.value)
            finally:
                _ole32.ReleaseStgMedium(ctypes.byref(st))
            return out

        _QI = ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.c_void_p, ctypes.POINTER(_O.GUID), ctypes.POINTER(ctypes.c_void_p))
        _AR = ctypes.WINFUNCTYPE(ctypes.c_ulong, ctypes.c_void_p)
        _DE = ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_ulong, ctypes.c_int64,
                                 ctypes.POINTER(ctypes.c_ulong))
        _DO = ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.c_void_p, ctypes.c_ulong, ctypes.c_int64,
                                 ctypes.POINTER(ctypes.c_ulong))
        _DL = ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.c_void_p)

        class _VTBL(ctypes.Structure):
            _fields_ = [("QueryInterface", _QI), ("AddRef", _AR), ("Release", _AR), ("DragEnter", _DE),
                        ("DragOver", _DO), ("DragLeave", _DL), ("Drop", _DE)]

        class _COMOBJ(ctypes.Structure):
            _fields_ = [("lpVtbl", ctypes.POINTER(_VTBL))]

        def _pt(v):
            """POINTL(값 전달, 64비트에서는 8바이트 한 덩어리) → (x, y)"""
            v &= 0xFFFFFFFFFFFFFFFF
            x, y = v & 0xFFFFFFFF, (v >> 32) & 0xFFFFFFFF
            return (x - 2 ** 32 if x >= 2 ** 31 else x, y - 2 ** 32 if y >= 2 ** 31 else y)

        class OleDropTarget:
            """창에 '여기에 파일을 놓을 수 있음'을 등록. handler(kind, paths, x, y, keys) → 효과(복사/이동/없음)"""

            def __init__(self, hwnd, handler):
                self.hwnd, self.handler = hwnd, handler
                self.paths = []
                self.helper = ctypes.c_void_p()
                try:          # 끄는 파일 그림을 이 창 위에서도 보여 주는 도우미
                    _ole32.CoCreateInstance(ctypes.byref(_O.CLSID_DragDropHelper), None, 1,
                                            ctypes.byref(_O.IID_IDropTargetHelper), ctypes.byref(self.helper))
                except OSError:
                    self.helper = ctypes.c_void_p()

                def qi(this, riid, ppv):
                    if riid[0].same(_O.IID_IUnknown) or riid[0].same(_O.IID_IDropTarget):
                        ppv[0] = this
                        return _O.S_OK
                    ppv[0] = None
                    return _O.E_NOINTERFACE

                def addref(this):
                    return 1

                def drag_enter(this, pdo, keys, pt, peff):
                    try:
                        self.paths = _files_from_dataobject(pdo)
                        x, y = _pt(pt)
                        peff[0] = self._effect(self.handler("enter", self.paths, x, y, keys), peff[0])
                        if self.helper:
                            p = _O.POINT(x, y)
                            _vcall(self.helper, 3, ctypes.c_long, [_wt.HWND, ctypes.c_void_p, ctypes.c_void_p,
                                                                   ctypes.c_ulong], self.hwnd, pdo, ctypes.byref(p), peff[0])
                    except Exception:
                        peff[0] = 0
                    return _O.S_OK

                def drag_over(this, keys, pt, peff):
                    try:
                        x, y = _pt(pt)
                        peff[0] = self._effect(self.handler("over", self.paths, x, y, keys), peff[0])
                        if self.helper:
                            p = _O.POINT(x, y)
                            _vcall(self.helper, 5, ctypes.c_long, [ctypes.c_void_p, ctypes.c_ulong],
                                   ctypes.byref(p), peff[0])
                    except Exception:
                        peff[0] = 0
                    return _O.S_OK

                def drag_leave(this):
                    try:
                        self.handler("leave", self.paths, 0, 0, 0)
                        if self.helper:
                            _vcall(self.helper, 4, ctypes.c_long, [])
                    except Exception:
                        pass
                    return _O.S_OK

                def drop(this, pdo, keys, pt, peff):
                    try:
                        x, y = _pt(pt)
                        paths = _files_from_dataobject(pdo) or self.paths
                        want = self._effect(self.handler("drop", paths, x, y, keys), peff[0])
                        if self.helper:
                            p = _O.POINT(x, y)
                            _vcall(self.helper, 6, ctypes.c_long, [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_ulong],
                                   pdo, ctypes.byref(p), want)
                        # 실제 옮기기는 이 프로그램이 함 → 보낸 쪽(탐색기)이 원본을 지우지 않게 '복사'로 알려 줌
                        peff[0] = _O.DROPEFFECT_COPY if want else 0
                    except Exception:
                        peff[0] = 0
                    return _O.S_OK

                self._fns = [_QI(qi), _AR(addref), _AR(addref), _DE(drag_enter), _DO(drag_over), _DL(drag_leave),
                             _DE(drop)]
                self._vtbl = _VTBL(*self._fns)
                self._obj = _COMOBJ(ctypes.pointer(self._vtbl))
                self.ok = _ole32.RegisterDragDrop(hwnd, ctypes.byref(self._obj)) == 0

            @staticmethod
            def _effect(want, allowed):
                return want if want and (want & allowed) else 0

            def revoke(self):
                if self.ok:
                    _ole32.RevokeDragDrop(self.hwnd)
                    self.ok = False
                _release(self.helper.value)
                self.helper = ctypes.c_void_p()

        def ole_drag_files(hwnd, paths):
            """파일들을 끌기 시작 (탐색기처럼 그림이 따라다님). 끝날 때까지 기다렸다가 결과 효과를 돌려줌"""
            pidls = []
            try:
                for p in paths:
                    pidl = ctypes.c_void_p()
                    if _shell32.SHParseDisplayName(os.path.abspath(p), None, ctypes.byref(pidl), 0, None) == 0:
                        pidls.append(pidl)
                if not pidls:
                    return 0
                arr = (ctypes.c_void_p * len(pidls))(*[x.value for x in pidls])
                psia = ctypes.c_void_p()
                if _shell32.SHCreateShellItemArrayFromIDLists(len(pidls), arr, ctypes.byref(psia)) != 0:
                    return 0
                pdo = ctypes.c_void_p()
                try:
                    hr = _vcall(psia.value, 3, ctypes.c_long, [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p,
                                                               ctypes.POINTER(ctypes.c_void_p)],
                                None, ctypes.byref(_O.BHID_DataObject), ctypes.byref(_O.IID_IDataObject),
                                ctypes.byref(pdo))
                    if hr != 0 or not pdo:
                        return 0
                    eff = ctypes.c_ulong(0)
                    _shell32.SHDoDragDrop(hwnd, pdo, None, _O.DROPEFFECT_COPY | _O.DROPEFFECT_MOVE | _O.DROPEFFECT_LINK,
                                          ctypes.byref(eff))
                    return eff.value
                finally:
                    _release(pdo.value)
                    _release(psia.value)
            finally:
                for x in pidls:
                    _ole32.CoTaskMemFree(x)


        # ── 윈도우 탐색기 오른쪽 클릭 메뉴 (속성·압축·보내기·연결 프로그램·백신 검사 등 그대로) ──
        _u32 = ctypes.windll.user32
        _O.IID_IContextMenu = _O.GUID.of("{000214E4-0000-0000-C000-000000000046}")
        _O.IID_IContextMenu2 = _O.GUID.of("{000214F4-0000-0000-C000-000000000046}")
        _O.IID_IContextMenu3 = _O.GUID.of("{BCFCE0A0-EC17-11D0-8D10-00A0C90F2719}")
        _O.IID_IShellItem = _O.GUID.of("{43826D1E-E718-42EE-BC55-A1E261C37BFE}")
        _O.IID_IShellFolder = _O.GUID.of("{000214E6-0000-0000-C000-000000000046}")
        _O.BHID_SFUIObject = _O.GUID.of("{3981E225-F559-11D3-8E3A-00C04F6837D5}")
        _O.BHID_SFObject = _O.GUID.of("{3981E224-F559-11D3-8E3A-00C04F6837D5}")
        _shell32.SHCreateItemFromIDList.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.POINTER(ctypes.c_void_p)]
        _u32.CreatePopupMenu.restype = ctypes.c_void_p
        _u32.DestroyMenu.argtypes = [ctypes.c_void_p]
        _u32.TrackPopupMenuEx.argtypes = [ctypes.c_void_p, ctypes.c_uint, ctypes.c_int, ctypes.c_int, _wt.HWND,
                                          ctypes.c_void_p]
        _u32.TrackPopupMenuEx.restype = ctypes.c_int
        _u32.DefWindowProcW.argtypes = [_wt.HWND, ctypes.c_uint, ctypes.c_size_t, ctypes.c_ssize_t]
        _u32.DefWindowProcW.restype = ctypes.c_ssize_t
        _u32.CreateWindowExW.argtypes = [ctypes.c_ulong, ctypes.c_wchar_p, ctypes.c_wchar_p, ctypes.c_ulong,
                                         ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, _wt.HWND,
                                         ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p]
        _u32.CreateWindowExW.restype = _wt.HWND
        _u32.SetForegroundWindow.argtypes = [_wt.HWND]
        _u32.PostMessageW.argtypes = [_wt.HWND, ctypes.c_uint, ctypes.c_size_t, ctypes.c_ssize_t]
        _WNDPROC = ctypes.WINFUNCTYPE(ctypes.c_ssize_t, _wt.HWND, ctypes.c_uint, ctypes.c_size_t, ctypes.c_ssize_t)

        class _WNDCLASSEXW(ctypes.Structure):
            _fields_ = [("cbSize", ctypes.c_uint), ("style", ctypes.c_uint), ("lpfnWndProc", _WNDPROC),
                        ("cbClsExtra", ctypes.c_int), ("cbWndExtra", ctypes.c_int), ("hInstance", ctypes.c_void_p),
                        ("hIcon", ctypes.c_void_p), ("hCursor", ctypes.c_void_p), ("hbrBackground", ctypes.c_void_p),
                        ("lpszMenuName", ctypes.c_wchar_p), ("lpszClassName", ctypes.c_wchar_p),
                        ("hIconSm", ctypes.c_void_p)]

        class _CMICEX(ctypes.Structure):
            _fields_ = [("cbSize", ctypes.c_ulong), ("fMask", ctypes.c_ulong), ("hwnd", _wt.HWND),
                        ("lpVerb", ctypes.c_void_p), ("lpParameters", ctypes.c_char_p),
                        ("lpDirectory", ctypes.c_char_p), ("nShow", ctypes.c_int), ("dwHotKey", ctypes.c_ulong),
                        ("hIcon", ctypes.c_void_p), ("lpTitle", ctypes.c_char_p), ("lpVerbW", ctypes.c_void_p),
                        ("lpParametersW", ctypes.c_wchar_p), ("lpDirectoryW", ctypes.c_wchar_p),
                        ("lpTitleW", ctypes.c_wchar_p), ("ptInvoke", _O.POINT)]

        _menu_state = {"cm2": None, "cm3": None, "hwnd": None}

        def _menu_wndproc(hwnd, msg, wp, lp):
            # 보내기·연결 프로그램 같은 하위 메뉴는 메뉴가 열릴 때 채워지므로 메시지를 넘겨 줌
            if msg in (0x0117, 0x002B, 0x002C, 0x0120):   # INITMENUPOPUP, DRAWITEM, MEASUREITEM, MENUCHAR
                try:
                    if _menu_state["cm3"]:
                        res = ctypes.c_ssize_t(0)
                        if _vcall(_menu_state["cm3"], 7, ctypes.c_long,
                                  [ctypes.c_uint, ctypes.c_size_t, ctypes.c_ssize_t, ctypes.POINTER(ctypes.c_ssize_t)],
                                  msg, wp, lp, ctypes.byref(res)) == 0:
                            return res.value
                    elif _menu_state["cm2"]:
                        if _vcall(_menu_state["cm2"], 6, ctypes.c_long, [ctypes.c_uint, ctypes.c_size_t,
                                                                          ctypes.c_ssize_t], msg, wp, lp) == 0:
                            return 0
                except Exception:
                    pass
            return _u32.DefWindowProcW(hwnd, msg, wp, lp)

        _menu_proc = _WNDPROC(_menu_wndproc)

        def _menu_owner():
            if _menu_state["hwnd"]:
                return _menu_state["hwnd"]
            wc = _WNDCLASSEXW()
            wc.cbSize = ctypes.sizeof(_WNDCLASSEXW)
            wc.lpfnWndProc = _menu_proc
            wc.hInstance = ctypes.windll.kernel32.GetModuleHandleW(None)
            wc.lpszClassName = "SmartExplorerShellMenu"
            ctypes.windll.user32.RegisterClassExW(ctypes.byref(wc))
            _menu_state["wc"] = wc
            _menu_state["hwnd"] = _u32.CreateWindowExW(0x80, "SmartExplorerShellMenu", "", 0x80000000,
                                                       0, 0, 0, 0, None, None, wc.hInstance, None)
            return _menu_state["hwnd"]

        def _pidl(path):
            pidl = ctypes.c_void_p()
            if _shell32.SHParseDisplayName(os.path.abspath(path), None, ctypes.byref(pidl), 0, None) != 0:
                return None
            return pidl

        def _context_menu_for(paths, background_dir):
            pcm = ctypes.c_void_p()
            if background_dir:              # 빈 곳: 그 폴더 자체의 메뉴 (새로 만들기 등)
                pidl = _pidl(background_dir)
                if not pidl:
                    return None
                psi, psf = ctypes.c_void_p(), ctypes.c_void_p()
                try:
                    if _shell32.SHCreateItemFromIDList(pidl, ctypes.byref(_O.IID_IShellItem), ctypes.byref(psi)) != 0:
                        return None
                    if _vcall(psi.value, 3, ctypes.c_long, [ctypes.c_void_p] * 3 + [ctypes.POINTER(ctypes.c_void_p)],
                              None, ctypes.byref(_O.BHID_SFObject), ctypes.byref(_O.IID_IShellFolder),
                              ctypes.byref(psf)) != 0:
                        return None
                    if _vcall(psf.value, 8, ctypes.c_long, [_wt.HWND, ctypes.c_void_p, ctypes.POINTER(ctypes.c_void_p)],
                              _menu_owner(), ctypes.byref(_O.IID_IContextMenu), ctypes.byref(pcm)) != 0:
                        return None
                    return pcm.value
                finally:
                    _release(psf.value)
                    _release(psi.value)
                    _ole32.CoTaskMemFree(pidl)
            pidls = [x for x in (_pidl(p) for p in paths) if x]
            try:
                if not pidls:
                    return None
                arr = (ctypes.c_void_p * len(pidls))(*[x.value for x in pidls])
                psia = ctypes.c_void_p()
                if _shell32.SHCreateShellItemArrayFromIDLists(len(pidls), arr, ctypes.byref(psia)) != 0:
                    return None
                try:
                    if _vcall(psia.value, 3, ctypes.c_long, [ctypes.c_void_p] * 3 + [ctypes.POINTER(ctypes.c_void_p)],
                              None, ctypes.byref(_O.BHID_SFUIObject), ctypes.byref(_O.IID_IContextMenu),
                              ctypes.byref(pcm)) != 0:
                        return None
                    return pcm.value
                finally:
                    _release(psia.value)
            finally:
                for x in pidls:
                    _ole32.CoTaskMemFree(x)

        def shell_menu(paths, x, y, background_dir=None, extended=False):
            """윈도우 탐색기의 오른쪽 클릭 메뉴를 그대로 띄우고, 고른 명령을 실행. 고른 명령이 있으면 True"""
            pcm = _context_menu_for(paths, background_dir)
            if not pcm:
                return False
            hmenu = _u32.CreatePopupMenu()
            cm2, cm3 = ctypes.c_void_p(), ctypes.c_void_p()
            try:
                flags = 0x0 | 0x4 | (0x100 if extended else 0)          # NORMAL | EXPLORE | (Shift: 확장 메뉴)
                if _vcall(pcm, 3, ctypes.c_long, [ctypes.c_void_p, ctypes.c_uint, ctypes.c_uint, ctypes.c_uint,
                                                  ctypes.c_uint], hmenu, 0, 1, 0x7FFF, flags) < 0:
                    return False
                _vcall(pcm, 0, ctypes.c_long, [ctypes.c_void_p, ctypes.POINTER(ctypes.c_void_p)],
                       ctypes.byref(_O.IID_IContextMenu3), ctypes.byref(cm3))
                if not cm3:
                    _vcall(pcm, 0, ctypes.c_long, [ctypes.c_void_p, ctypes.POINTER(ctypes.c_void_p)],
                           ctypes.byref(_O.IID_IContextMenu2), ctypes.byref(cm2))
                _menu_state["cm3"], _menu_state["cm2"] = cm3.value, cm2.value
                owner = _menu_owner()
                _u32.SetForegroundWindow(owner)
                cmd = _u32.TrackPopupMenuEx(hmenu, 0x0100 | 0x0002, int(x), int(y), owner, None)   # RETURNCMD|RIGHTBUTTON
                _u32.PostMessageW(owner, 0, 0, 0)
                if cmd <= 0:
                    return False
                ci = _CMICEX()
                ci.cbSize = ctypes.sizeof(_CMICEX)
                ci.fMask = 0x4000 | 0x20000000            # UNICODE | PTINVOKE
                ci.hwnd = owner
                ci.lpVerb = ci.lpVerbW = cmd - 1
                ci.nShow = 1
                ci.ptInvoke = _O.POINT(int(x), int(y))
                if background_dir:
                    ci.lpDirectoryW = background_dir
                _vcall(pcm, 4, ctypes.c_long, [ctypes.c_void_p], ctypes.byref(ci))
                return True
            finally:
                _menu_state["cm3"] = _menu_state["cm2"] = None
                _release(cm3.value)
                _release(cm2.value)
                _u32.DestroyMenu(hmenu)
                _release(pcm)

        _hr = _ole32.OleInitialize(None)
        if _hr in (0, 1):                     # S_OK / S_FALSE(이미 준비됨)
            OLE_DND = _OLE
            OLE_DND.DropTarget = OleDropTarget
            OLE_DND.drag_files = staticmethod(ole_drag_files)
            OLE_DND.shell_menu = staticmethod(shell_menu)
    except Exception:
        OLE_DND = None


class SearchPane(tk.Frame):
    """칸 하나 = 탐색기(둘러보기) + 본문 검색기. 검색어가 비어 있으면 폴더 내용을 보여 줌"""
    COLS = {
        "browse": (("name", "이름", 230, "w", True), ("count", "크기", 80, "e", False),
                   ("mtime", "수정한 날짜", 125, "center", False), ("folder", "종류", 100, "w", False)),
        "search": (("name", "파일명", 220, "w", True), ("count", "일치", 50, "center", False),
                   ("mtime", "수정일", 125, "center", False), ("folder", "위치", 260, "w", True)),
    }

    def __init__(self, master, app, state):
        super().__init__(master, highlightthickness=2, highlightbackground="#d0d0d0", highlightcolor="#d0d0d0")
        self.app = app
        self.q = queue.Queue()
        self.stop_event = threading.Event()
        self.worker = None
        self.hits = {}
        self.pats = []
        self.sort_state = {}
        self.browse_sort = ("mtime", True)      # 폴더 보기 정렬: 새 폴더를 열면 늘 '수정한 날짜 최신순'
        self.t0 = 0
        self.warn = ""
        self.preview_job = None
        self.mode = None
        self.cwd = None
        self.back_stack = []
        self._cwd_sig = None
        self._tick = 0
        self._drag = None
        self._build(state)
        start = state.get("cwd") or self.folder_var.get()
        if self.pinned_var.get() and not (start and os.path.isdir(start) and is_inside(start, self.folder_var.get())):
            start = self.folder_var.get()
        self.after_idle(lambda: self.navigate(start if os.path.isdir(start or "") else os.path.expanduser("~"),
                                              remember=False))
        self.after_id = self.after(100, self.poll)

    # ───────── 화면 ─────────
    def _build(self, st):
        inner = ttk.Frame(self, padding=(6, 6, 6, 4))
        inner.pack(fill="both", expand=True)

        r1 = ttk.Frame(inner)
        r1.pack(fill="x")
        self.back_btn = ttk.Button(r1, text="◀", width=3, command=self.go_back)
        self.back_btn.pack(side="left")
        self.up_btn = ttk.Button(r1, text="⬆", width=3, command=self.go_up)
        self.up_btn.pack(side="left", padx=(2, 4))
        self.folder_var = tk.StringVar(value=st.get("folder", os.path.join(os.path.expanduser("~"), "Documents")))
        self.folder_cb = ttk.Combobox(r1, textvariable=self.folder_var, values=self.app.s.get("recent", []))
        self.folder_cb.pack(side="left", fill="x", expand=True)
        self.folder_cb.bind("<Return>", lambda e: self.navigate(self.folder_var.get().strip().strip('"')))
        self.folder_cb.bind("<<ComboboxSelected>>", lambda e: self.navigate(self.folder_var.get()))
        # 고정했을 때 보여 줄 표시줄
        self.pin_text = tk.StringVar()
        self.pin_label = tk.Label(r1, textvariable=self.pin_text, anchor="w", bg="#fff4cc", fg="#5a4500",
                                  font=(FONT[0], fsz(10), "bold"), padx=6, relief="solid", borderwidth=1)
        self.pin_label.bind("<Double-1>", lambda e: self.navigate(self.folder_var.get()))
        self.browse_btn = ttk.Button(r1, text="폴더…", width=6, command=self.browse)
        self.browse_btn.pack(side="left", padx=(4, 0))
        self.hide_dirs = bool(st.get("hide_dirs", False))      # 목록에서 폴더 숨기기 (파일만 보기)
        self.dir_btn = ttk.Button(r1, text="", command=self.toggle_dirs)
        self.dir_btn.pack(side="left", padx=(2, 0))
        self._dir_btn_text()
        self.pinned_var = tk.BooleanVar(value=st.get("pinned", False))
        self.pin_btn = ttk.Checkbutton(r1, text="📌 고정", variable=self.pinned_var, style="Toolbutton",
                                       command=self.apply_pin)
        self.preview_hidden = st.get("preview_hidden", False)
        self.pv_btn = ttk.Button(r1, text="", command=self.toggle_preview)
        self.pv_btn.pack(side="left", padx=(2, 0))     # 미리보기 숨기기 → 📌 고정 순서
        self.pin_btn.pack(side="left", padx=(2, 0))
        self.after_idle(lambda: self.apply_pin(quiet=True))

        r2 = ttk.Frame(inner)
        r2.pack(fill="x", pady=(4, 4))
        self.query_var = tk.StringVar(value=st.get("query", ""))
        self.query_entry = ttk.Entry(r2, textvariable=self.query_var, font=(FONT[0], fsz(11)))
        self.query_entry.pack(side="left", fill="x", expand=True, ipady=1)
        self.search_mode = st.get("search_mode", "body")     # Enter = 마지막에 누른 검색 버튼
        self.query_entry.bind("<Return>", lambda e: self.start(self.search_mode))
        self.query_entry.bind("<Escape>", lambda e: self.clear_search())
        # 비어 있을 때 보이는 안내 글
        self.ph = tk.Label(self.query_entry, text="찾을 단어 입력 후 [파일명 검색] 또는 [본문 추가 검색]",
                           fg="#9a9a9a", bg="white", font=(FONT[0], fsz(10)), cursor="xterm")
        self.ph.bind("<Button-1>", lambda e: self.query_entry.focus_set())
        self.query_entry.bind("<FocusIn>", lambda e: self._placeholder(), add="+")
        self.query_entry.bind("<FocusOut>", lambda e: self._placeholder(), add="+")
        self.query_var.trace_add("write", lambda *a: self._placeholder())
        self.after_idle(self._placeholder)
        self.name_btn = ttk.Button(r2, text="🔍 파일명 검색", command=lambda: self.start("name"))
        self.name_btn.pack(side="left", padx=(4, 0))
        self.search_btn = ttk.Button(r2, text="📄 본문 추가 검색", style="Accent.TButton", command=lambda: self.start("body"))
        self.search_btn.pack(side="left", padx=(2, 0))
        self.stop_btn = ttk.Button(r2, text="중지", width=5, command=self.stop, state="disabled")
        self.stop_btn.pack(side="left", padx=(2, 0))
        self.clear_btn = ttk.Button(r2, text="✕", width=3, command=self.clear_search)
        self.clear_btn.pack(side="left", padx=(2, 0))

        types = st.get("types", {})
        opts = st.get("opts", {})
        self.type_vars = {lb: tk.BooleanVar(value=types.get(lb, d)) for lb, _, d in TYPE_GROUPS}
        self.opt_vars = {k: tk.BooleanVar(value=opts.get(k, d)) for k, _, d in OPTION_LABELS}
        mb = ttk.Menubutton(r2, text="옵션")
        menu = tk.Menu(mb, tearoff=0)
        menu.add_command(label="파일 종류", state="disabled")
        for lb, _, _ in TYPE_GROUPS:
            menu.add_checkbutton(label="   " + lb, variable=self.type_vars[lb])
        menu.add_separator()
        for k, lb, _ in OPTION_LABELS:
            menu.add_checkbutton(label=lb, variable=self.opt_vars[k],
                                 command=(self.refresh_preview if k == "shell_preview" else None))
        mb["menu"] = menu
        mb.pack(side="left", padx=(2, 0))
        # 상태 정보(폴더·파일 개수, 검색 진행)는 옵션 버튼 왼쪽에
        self.status_var = tk.StringVar(value="")
        self.status_lbl = ttk.Label(r2, textvariable=self.status_var, width=30, anchor="w", foreground="#555")
        self.status_lbl.pack(side="left", padx=(8, 4), before=mb)   # mb(옵션)는 이미 배치돼 있음
        self.opt_btn = mb
        self.progress = ttk.Progressbar(r2, mode="indeterminate", length=50)   # 검색 중에만 보임
        self.status_lbl.bind("<Enter>", self._status_tip)          # 글이 잘리면 마우스를 올려 전체 보기
        self.status_lbl.bind("<Leave>", lambda e: self._status_tip(hide=True))

        self._inner = inner
        self.side_preview = False          # True = 미리보기를 목록 오른쪽에 (칸이 1개일 때)
        self._sashes = {"bottom": st.get("sash"), "side": st.get("sash_side")}
        paned = ttk.PanedWindow(inner, orient="vertical")
        paned.pack(fill="both", expand=True)

        tf = ttk.Frame(inner)              # 경계창을 다시 만들 수 있게 경계창의 부모(inner) 아래에 만듦
        self.tree = ttk.Treeview(tf, columns=("name", "count", "mtime", "folder"), show="headings",
                                 selectmode="extended")
        ys = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=ys.set)
        ys.pack(side="right", fill="y")
        self.tree.pack(side="left", fill="both", expand=True)
        self.tree.tag_configure("dir", foreground=theme_dir_color())
        self.tree.tag_configure("drophl", background="#cce8ff")     # 끌어 놓을 폴더 표시
        t = self.tree
        t.bind("<<TreeviewSelect>>", self.on_select)
        t.bind("<Double-1>", lambda e: self.activate())
        t.bind("<Return>", lambda e: self.activate())
        t.bind("<BackSpace>", lambda e: self.go_up())
        t.bind("<Alt-Left>", lambda e: self.go_back())
        t.bind("<F5>", lambda e: self.refresh())
        t.bind("<F2>", lambda e: self.rename())
        t.bind("<Delete>", lambda e: self.delete())
        for k in ("c", "C"):
            t.bind(f"<Control-{k}>", lambda e: self.clip(cut=False))
        for k in ("x", "X"):
            t.bind(f"<Control-{k}>", lambda e: self.clip(cut=True))
        for k in ("v", "V"):
            t.bind(f"<Control-{k}>", lambda e: self.paste())
        for k in ("a", "A"):
            t.bind(f"<Control-{k}>", lambda e: (t.selection_set(t.get_children()), "break")[1])
        t.bind("<Control-Shift-N>", lambda e: self.new_folder())
        t.bind("<Control-Shift-n>", lambda e: self.new_folder())
        t.bind("<Button-3>", self.popup_menu)
        t.bind("<ButtonPress-1>", self._drag_press)
        t.bind("<B1-Motion>", self._drag_motion)
        t.bind("<ButtonRelease-1>", self._drag_release)
        paned.add(tf, weight=2)
        tf.lift(paned)
        self.tf = tf

        bf = ttk.Frame(inner)
        self.nb = ttk.Notebook(bf)
        self.nb.pack(fill="both", expand=True, pady=(4, 0))
        self.preview = PreviewPanel(self.nb)
        mf = ttk.Frame(self.nb)
        self.matches = tk.Text(mf, wrap="word", padx=10, pady=8, font=FONT, state="disabled", relief="flat")
        ms = ttk.Scrollbar(mf, orient="vertical", command=self.matches.yview)
        self.matches.configure(yscrollcommand=ms.set)
        ms.pack(side="right", fill="y")
        self.matches.pack(fill="both", expand=True)
        self.matches.tag_configure("title", font=(FONT[0], fsz(11), "bold"))
        self.matches.tag_configure("path", foreground="#666")
        self.matches.tag_configure("hl", background="#ffe066")
        self.matches.tag_configure("note", foreground="#2a6fdb")
        self.preview.fit_mode = st.get("fit", "auto")
        self.preview.zoom = st.get("zoom", 1.0)
        self.preview.shell_fit = st.get("shell_fit", "width")
        self.preview.shell_zoom = st.get("shell_zoom", 1.0)
        self.nb.add(self.preview, text="미리보기")
        self.nb.add(mf, text="일치한 문장")
        self.nb.select(st.get("tab", 0))
        self.nb.bind("<<NotebookTabChanged>>", lambda e: self.schedule_preview(50))
        paned.add(bf, weight=3)
        bf.lift(paned)
        self.bf = bf
        self.paned = paned
        self.after_idle(lambda: self.apply_preview_visible(save=False))
        self._bind_paned(paned)
        if st.get("sash"):                            # 목록/미리보기 경계 위치 복원
            self.after(300, lambda: self._set_sash(st["sash"]))


        self.menu = tk.Menu(self, tearoff=0)

    def _set_columns(self, mode):
        if self.mode == mode:
            return
        self.mode = mode
        for c, t, w, anchor, stretch in self.COLS[mode]:
            self.tree.heading(c, text=t, command=lambda c=c: self.sort_by(c))
            self.tree.column(c, width=w, minwidth=40, anchor=anchor, stretch=stretch)
        self.sort_state = {}
        if mode == "browse":
            col, rev = self.browse_sort
            self.sort_state[col] = not rev

    def get_state(self):
        try:
            tab = self.nb.index(self.nb.select())
        except Exception:
            tab = 0
        return {"folder": self.folder_var.get(), "query": self.query_var.get(), "tab": tab,
                "search_mode": self.search_mode,
                "pinned": self.pinned_var.get(), "cwd": self.cwd or "", "preview_hidden": self.preview_hidden,
                "hide_dirs": self.hide_dirs,
                "sash_side": (self._sash_pos() if self.side_preview else self._sashes.get("side")),
                "fit": self.preview.fit_mode, "zoom": self.preview.zoom,
                "sash": (self._sashes.get("bottom") if self.side_preview else self._sash_pos()),
                "shell_fit": self.preview.shell_fit, "shell_zoom": self.preview.shell_zoom,
                "types": {k: v.get() for k, v in self.type_vars.items()},
                "opts": {k: v.get() for k, v in self.opt_vars.items()}}

    def _status_tip(self, e=None, hide=False):
        tip = getattr(self, "_tip", None)
        if tip is not None:
            try:
                tip.destroy()
            except tk.TclError:
                pass
            self._tip = None
        text = self.status_var.get()
        if hide or len(text) <= 30:
            return
        t = self._tip = tk.Toplevel(self)
        t.wm_overrideredirect(True)
        t.attributes("-topmost", True)
        tk.Label(t, text=text, bg="#ffffe0", relief="solid", borderwidth=1, padx=6, pady=3,
                 font=(FONT[0], fsz(9))).pack()
        x, y = self.status_lbl.winfo_rootx(), self.status_lbl.winfo_rooty() + self.status_lbl.winfo_height() + 2
        t.geometry(f"+{x}+{y}")

    def _placeholder(self):
        try:
            show = not self.query_var.get() and self.focus_get() is not self.query_entry
        except Exception:
            show = not self.query_var.get()
        if show:
            self.ph.place(x=6, rely=0.5, anchor="w")
        else:
            self.ph.place_forget()

    def _bind_paned(self, paned):
        paned.bind("<ButtonRelease-1>", lambda e: self.after(10, self.clamp_sash), add="+")
        paned.bind("<Configure>", lambda e: self.after(10, self.clamp_sash), add="+")

    def _span(self):
        return self.paned.winfo_width() if self.side_preview else self.paned.winfo_height()

    def set_side_preview(self, side):
        """미리보기 위치: side=True 면 목록 오른쪽, False 면 목록 아래 (경계창을 새로 만들어 바꿈)"""
        side = bool(side)
        if side == self.side_preview:
            return
        key_old = "side" if self.side_preview else "bottom"
        cur = self._sash_pos()
        if cur:
            self._sashes[key_old] = cur
        old = self.paned
        try:
            for w in list(old.panes()):
                old.forget(w)
        except Exception:
            pass
        old.destroy()
        self.side_preview = side
        paned = ttk.PanedWindow(self._inner, orient="horizontal" if side else "vertical")
        paned.pack(fill="both", expand=True)
        paned.add(self.tf, weight=2)
        self.tf.lift(paned)
        self.paned = paned
        if not self.preview_hidden:
            paned.add(self.bf, weight=3)
        self.bf.lift(paned)
        self._bind_paned(paned)
        frac = self._sashes.get("side" if side else "bottom") or (0.45 if side else None)
        if frac:
            self.after(150, lambda: self._set_sash(frac))
        self.schedule_preview(80)

    def _sash_pos(self):
        try:
            h = self._span()
            return round(self.paned.sashpos(0) / h, 3) if h > 50 else None
        except Exception:
            return None

    def clamp_sash(self):
        """광고가 붙은 칸은 미리보기 높이가 광고보다 작아지지 않게 목록/미리보기 경계를 제한"""
        if not self.preview.adbox:
            return
        try:
            h = self._span()
            aw, ah = ad_pixels(self)
            need = (aw + 30) if self.side_preview else (ah + 45)   # 광고 + 탭 머리글·여백
            pos = self.paned.sashpos(0)
            if h > need + 60 and pos > h - need:
                self.paned.sashpos(0, h - need)
        except Exception:
            pass

    def _set_sash(self, frac):
        try:
            h = self._span()
            if h > 50 and 0.05 < frac < 0.95:
                self.paned.sashpos(0, int(h * frac))
        except Exception:
            pass

    def set_active(self, on):
        c = "#2a6fdb" if on else "#d0d0d0"
        self.configure(highlightbackground=c, highlightcolor=c)

    def destroy_pane(self):
        self.stop_event.set()
        try:
            self.after_cancel(self.after_id)
        except Exception:
            pass
        self.preview.clear()
        self.preview.set_ad(False)
        self.destroy()

    def hwnd(self):
        try:
            return int(self.winfo_toplevel().wm_frame(), 16)
        except Exception:
            return 0

    # ───────── 폴더 고정 ─────────
    def apply_pin(self, quiet=False):
        """폴더 고정: 켜면 이 칸의 기준 폴더가 바뀌지 않음 (하위 폴더 둘러보기는 됨, 검색은 늘 기준 폴더 전체)"""
        if self.pinned_var.get():
            folder = (self.cwd or self.folder_var.get()).strip().strip('"')
            if not os.path.isdir(folder):
                self.pinned_var.set(False)
                if not quiet:
                    messagebox.showwarning(APP_NAME, "있는 폴더만 고정할 수 있습니다.\n" + folder)
                return
            if not quiet:
                self.folder_var.set(os.path.normpath(folder))
            self.folder_cb.pack_forget()
            self.pin_label.pack(side="left", fill="x", expand=True, before=self.browse_btn, ipady=2)
            self.browse_btn.state(["disabled"])
            if not quiet:
                self.app.schedule_save()
                self.status_var.set("폴더를 고정했습니다. 검색은 늘 이 폴더 전체에서 합니다.")
                self.query_entry.focus_set()
        else:
            self.pin_label.pack_forget()
            self.folder_cb.pack(side="left", fill="x", expand=True, before=self.browse_btn)
            self.browse_btn.state(["!disabled"])
            if self.cwd:
                self.folder_var.set(self.cwd)
            if not quiet:
                self.app.schedule_save()
                self.status_var.set("폴더 고정을 풀었습니다.")
        self._update_location()

    def _update_location(self):
        root = self.folder_var.get()
        if self.pinned_var.get():
            rel = ""
            if self.cwd and is_inside(self.cwd, root) and os.path.normcase(self.cwd) != os.path.normcase(root):
                rel = "  ›  " + os.path.relpath(self.cwd, root).replace(os.sep, " › ")
            self.pin_text.set("📌 " + root + rel)
        at_root = self.cwd is None or os.path.dirname(self.cwd.rstrip("\\/")) == self.cwd.rstrip("\\/") or \
            (self.pinned_var.get() and os.path.normcase(os.path.abspath(self.cwd)) == os.path.normcase(os.path.abspath(root)))
        self.up_btn.state(["disabled" if at_root else "!disabled"])
        self.back_btn.state(["!disabled" if self.back_stack else "disabled"])

    def _dir_btn_text(self):
        self.dir_btn.configure(text="📁 폴더 보이기" if self.hide_dirs else "📁 폴더 숨기기")

    def toggle_dirs(self):
        """누르면 목록에서 폴더 숨기기 ↔ 다시 누르면 보이기"""
        self.hide_dirs = not self.hide_dirs
        self._dir_btn_text()
        if self.mode == "browse" and self.cwd:
            self.load_browse()
        try:
            self.app.schedule_save()
        except Exception:
            pass

    def browse(self):
        if self.pinned_var.get():
            return
        d = filedialog.askdirectory(initialdir=self.cwd or None, title="폴더 선택")
        if d:
            self.navigate(os.path.normpath(d))

    # ───────── 둘러보기(탐색기) ─────────
    def navigate(self, folder, remember=True, select=None):
        if not folder:
            return
        folder = os.path.normpath(os.path.expanduser(folder))
        if not os.path.isdir(folder):
            messagebox.showwarning(APP_NAME, "폴더를 찾을 수 없습니다.\n" + folder)
            if self.cwd and not self.pinned_var.get():
                self.folder_var.set(self.cwd)
            return
        if self.pinned_var.get() and not is_inside(folder, self.folder_var.get()):
            self.status_var.set("고정된 폴더 밖으로는 나갈 수 없습니다. 📌 고정을 풀어 주세요.")
            return
        if self.busy():
            self.stop()
        if remember and self.cwd and os.path.normcase(self.cwd) != os.path.normcase(folder):
            self.back_stack.append(self.cwd)
            del self.back_stack[:-50]
        prev = self.cwd
        self.cwd = folder
        if not self.pinned_var.get():
            self.folder_var.set(folder)
        if select is None and prev and is_inside(prev, folder) and os.path.normcase(prev) != os.path.normcase(folder):
            select = os.path.join(folder, os.path.relpath(prev, folder).split(os.sep)[0])   # 올라오면 나온 폴더 선택
        if os.path.normcase(prev or "") != os.path.normcase(folder):
            self.browse_sort = ("mtime", True)              # 다른 폴더로 가면 늘 수정한 날짜 최신순 + 맨 위
        self.load_browse(select=[select] if select else None, top=True)
        self.app.add_recent(folder)
        self.app.schedule_save()
        self._update_location()

    def go_up(self):
        if not self.cwd:
            return
        parent = os.path.dirname(self.cwd.rstrip("\\/"))
        if parent and parent != self.cwd.rstrip("\\/"):
            if self.pinned_var.get() and not is_inside(parent, self.folder_var.get()):
                return
            self.navigate(parent)
        return "break"

    def go_back(self):
        while self.back_stack:
            f = self.back_stack.pop()
            if os.path.isdir(f) and (not self.pinned_var.get() or is_inside(f, self.folder_var.get())):
                self.navigate(f, remember=False)
                break
        self._update_location()
        return "break"

    def _dir_sig(self, folder):
        try:
            st = os.stat(folder)
            return (st.st_mtime_ns, st.st_size)
        except OSError:
            return None

    def load_browse(self, select=None, top=False):
        """현재 폴더 내용을 목록에 채움. select = 선택해 둘 경로들, top = 맨 위로 스크롤"""
        self._set_columns("browse")
        keep = select if select is not None else ([] if top else self.selected_paths())
        y = 0 if (top or select is not None) else self.tree.yview()[0]
        self.tree.delete(*self.tree.get_children())
        self.hits.clear()
        self.pats = []
        try:
            items = list_folder(self.cwd)
        except OSError as e:
            self.status_var.set(f"폴더를 읽을 수 없습니다: {e}")
            return
        self._cwd_sig = self._dir_sig(self.cwd)
        nd = sum(1 for h in items if h["is_dir"])
        nf = len(items) - nd
        if self.hide_dirs:                               # 폴더 숨기기: 파일만
            items = [h for h in items if not h["is_dir"]]
        col, rev = self.browse_sort
        items.sort(key=lambda h: h["name"].lower())                      # 같은 값이면 이름순
        items.sort(key=self._sort_key(col, True), reverse=rev)
        items.sort(key=lambda h: not h["is_dir"])                       # 폴더는 늘 위에
        keep_n = {os.path.normcase(p) for p in (keep or [])}
        sel = []
        for i, h in enumerate(items):
            iid = str(i)
            self.hits[iid] = h
            self.tree.insert("", "end", iid=iid, tags=("dir",) if h["is_dir"] else (), values=(
                ("📁 " if h["is_dir"] else "") + h["name"], "" if h["is_dir"] else fmt_size(h["size"]),
                h["mtime"], type_name(h)))
            if os.path.normcase(h["path"]) in keep_n:
                sel.append(iid)
        if sel:
            self.tree.selection_set(sel)
            self.tree.focus(sel[0])
            self.tree.see(sel[0])
        else:
            self.tree.yview_moveto(y)
        self.status_var.set(f"폴더 {nd:,}개 숨김 · 파일 {nf:,}개" if self.hide_dirs and nd
                            else f"폴더 {nd:,}개 · 파일 {nf:,}개")
        if not sel:
            self.preview.clear()
            self._set_matches([])

    def refresh(self):
        if self.mode == "browse" and self.cwd:
            self.load_browse()
        return "break"

    def activate(self):
        """더블클릭·Enter: 폴더면 들어가고, 파일이면 열기"""
        h = self.current()
        if not h:
            return
        if h.get("is_dir"):
            self.navigate(h["path"])
        else:
            self.open_file()
        return "break"

    def clear_search(self):
        if self.busy():
            self.stop()
        self.query_var.set("")
        if self.cwd:
            self.load_browse(select=[])
        return "break"

    # ───────── 검색 ─────────
    def start(self, mode=None):
        if self.busy():
            return
        mode = mode or self.search_mode
        if mode != self.search_mode:
            self.search_mode = mode
            try:
                self.app.schedule_save()
            except Exception:
                pass
        if not parse_query(self.query_var.get()):
            self.clear_search()                       # 검색어가 비면 폴더 둘러보기로
            return
        folder = (self.folder_var.get() if self.pinned_var.get() else (self.cwd or self.folder_var.get()))
        folder = folder.strip().strip('"')
        if not os.path.isdir(folder):
            messagebox.showwarning(APP_NAME, "폴더를 찾을 수 없습니다.\n" + folder)
            return
        terms = parse_query(self.query_var.get())
        exts = set()
        for lb, ex, _ in TYPE_GROUPS:
            if self.type_vars[lb].get():
                exts.update(ex)
        if not exts and mode == "body":
            self.status_var.set("옵션에서 파일 종류를 하나 이상 선택하세요.")
            return
        o = {k: v.get() for k, v in self.opt_vars.items()}
        self.pats = [make_pattern(t, o["ignore_space"]) for t in terms]
        self._set_columns("search")
        self.tree.delete(*self.tree.get_children())
        self.hits.clear()
        self.preview.clear()
        self._set_matches([])
        folder = os.path.normpath(folder)
        self.stop_event = threading.Event()
        self.q = queue.Queue()
        self.warn = ""
        if mode == "name":
            self.worker = threading.Thread(target=name_worker, daemon=True, args=(
                folder, self.pats, o["recursive"], self.q, self.stop_event))
        else:
            self.worker = threading.Thread(target=search_worker, daemon=True, args=(
                folder, self.pats, exts, o["recursive"], o["name_search"], self.q, self.stop_event,
                self.app.cache, o["ocr"]))
        self.t0 = time.time()
        self.worker.start()
        self.search_btn.configure(state="disabled")
        self.name_btn.configure(state="disabled")
        self.stop_btn.configure(state="normal")
        self.progress.pack(side="left", padx=(0, 4), before=self.opt_btn)
        self.progress.start(12)
        self.status_var.set("검색 중…")

    def stop(self):
        self.stop_event.set()

    def busy(self):
        return bool(self.worker and self.worker.is_alive())

    def poll(self):
        try:
            for _ in range(300):
                msg = self.q.get_nowait()
                if msg[0] == "hit":
                    if self.mode == "search":
                        self.add_hit(msg[1])
                elif msg[0] == "warn":
                    self.warn = msg[1]
                elif msg[0] == "progress":
                    if self.mode == "search":
                        base, _, extra = msg[2].partition("  [")
                        cur = os.path.basename(base) + (f"  [{extra}" if extra else "")
                        self.status_var.set(f"검색 중… {msg[1]:,}개 확인 · {len(self.hits):,}개 찾음 · {cur}")
                elif msg[0] == "done":
                    _, scanned, errors, stopped = msg
                    self.progress.stop()
                    self.progress.pack_forget()
                    self.search_btn.configure(state="normal")
                    self.name_btn.configure(state="normal")
                    self.stop_btn.configure(state="disabled")
                    if self.mode == "search":
                        txt = f"{'중지됨' if stopped else '완료'}: {scanned:,}개 중 {len(self.hits):,}개 찾음 ({time.time() - self.t0:.1f}초) · Esc = 폴더로"
                        if errors:
                            txt += f" · 못 읽음 {errors:,}"
                        if self.warn:
                            txt += f" · {self.warn}"
                        self.status_var.set(txt)
                        if self.hits and not self.tree.selection():
                            first = self.tree.get_children()[0]
                            self.tree.selection_set(first)
                            self.tree.focus(first)
        except queue.Empty:
            pass
        # 둘러보기 중이면 폴더가 바뀌었는지 가끔 확인해서 자동으로 새로 고침
        self._tick += 1
        if self._tick % 15 == 0 and self.mode == "browse" and self.cwd and self._drag is None:
            sig = self._dir_sig(self.cwd)
            if sig is None and not os.path.isdir(self.cwd):
                parent = self.cwd
                while parent and not os.path.isdir(parent):
                    parent = os.path.dirname(parent.rstrip("\\/")) if os.path.dirname(parent.rstrip("\\/")) != parent else ""
                if parent:
                    self.navigate(parent, remember=False)
            elif sig != self._cwd_sig:
                self.load_browse()
        self.after_id = self.after(100, self.poll)

    def add_hit(self, h):
        iid = str(len(self.hits))
        h.setdefault("is_dir", False)
        self.hits[iid] = h
        self.tree.insert("", "end", iid=iid, values=(h["name"], h["count"] or ("폴더" if h["is_dir"] else "이름"),
                                                      h["mtime"], h["folder"]))

    def _sort_key(self, col, browse):
        def key(h):
            if col == "count":
                return h.get("size", 0) if browse else h["count"]
            if col == "folder":
                return type_name(h) if browse else h["folder"].lower()
            if col == "mtime":
                return h.get("ts", 0) or h["mtime"]
            return h["name"].lower()
        return key

    def sort_by(self, col):
        rev = self.sort_state.get(col, col in ("count", "mtime"))
        self.sort_state[col] = not rev
        browse = self.mode == "browse"
        if browse:
            self.browse_sort = (col, rev)          # 새로 고침해도 고른 정렬 유지
        k = self._sort_key(col, browse)
        items = sorted(self.tree.get_children(), key=lambda iid: k(self.hits[iid]), reverse=rev)
        if browse:                                     # 폴더는 늘 위에
            items = [i for i in items if self.hits[i]["is_dir"]] + [i for i in items if not self.hits[i]["is_dir"]]
        for i, iid in enumerate(items):
            self.tree.move(iid, "", i)

    # ───────── 선택·미리보기 ─────────
    def current(self):
        sel = self.tree.selection()
        return self.hits.get(sel[0]) if sel else None

    def selected_paths(self):
        return [self.hits[i]["path"] for i in self.tree.selection() if i in self.hits]

    def on_select(self, e=None):
        sel = self.tree.selection()
        h = self.current()
        if not h:
            return
        if len(sel) > 1:
            total = sum(max(self.hits[i].get("size", 0), 0) for i in sel if i in self.hits)
            self.status_var.set(f"{len(sel):,}개 선택" + (f" · {fmt_size(total)}" if total else ""))
        parts = [(h["name"] + "\n", "title", True), (h["path"] + "\n\n", "path", False)]
        if h.get("name_hit") and not h["snippets"]:
            parts.append(("파일 이름에서 일치했습니다.\n", "note", False))
        for s in h["snippets"]:
            parts.append((s + "\n\n", None, True))
        self._set_matches(parts)
        self.schedule_preview(250)       # 화살표로 빠르게 넘길 때 매번 열지 않도록 잠깐 기다림

    def _set_matches(self, parts):
        t = self.matches
        t.configure(state="normal")
        t.delete("1.0", "end")
        for text, tag, highlight in parts:
            start = t.index("end-1c")
            t.insert("end", text, tag)
            if highlight:
                for p in self.pats:
                    for m in p.finditer(text):
                        t.tag_add("hl", f"{start}+{m.start()}c", f"{start}+{m.end()}c")
        t.configure(state="disabled")

    def schedule_preview(self, delay):
        if self.preview_job:
            self.after_cancel(self.preview_job)
        self.preview_job = self.after(delay, self.load_preview)

    def set_ad_pane(self, on):
        """광고가 붙은 칸은 미리보기(광고 포함)를 숨길 수 없음"""
        self.is_ad_pane = on
        if on and self.preview_hidden:
            self.preview_hidden = False
            self.apply_preview_visible()
        try:
            self.pv_btn.state(["disabled"] if on else ["!disabled"])
        except Exception:
            pass

    def toggle_preview(self):
        if getattr(self, "is_ad_pane", False):
            return
        self.preview_hidden = not self.preview_hidden
        self.apply_preview_visible()

    def apply_preview_visible(self, save=True):
        """미리보기를 숨기면 목록(탐색기)만 칸 전체에 보임"""
        try:
            shown = str(self.bf) in self.paned.panes()
        except Exception:
            shown = True
        if self.preview_hidden:
            if shown:
                self.preview.clear()
                self.paned.forget(self.bf)
            self.pv_btn.configure(text="◧ 미리보기 보이기")
        else:
            if not shown:
                self.paned.add(self.bf, weight=3)
                self.schedule_preview(50)
            self.pv_btn.configure(text="◧ 미리보기 숨기기")
        if save:
            self.app.schedule_save()

    def load_preview(self):
        self.preview_job = None
        if self.preview_hidden:
            return
        h = self.current()
        try:
            visible = self.nb.index(self.nb.select()) == 0
        except Exception:
            visible = False
        if h and visible:
            self.preview.show(h["path"], self.pats, self.app.cache, self.opt_vars["shell_preview"].get())

    def refresh_preview(self):
        self.preview.clear()
        self.schedule_preview(50)

    # ───────── 오른쪽 클릭 메뉴 ─────────
    def popup_menu(self, e):
        iid = self.tree.identify_row(e.y)
        if iid and iid not in self.tree.selection():
            self.tree.selection_set(iid)
            self.tree.focus(iid)
        elif not iid:
            self.tree.selection_set(())
        has = bool(self.tree.selection())
        browse = self.mode == "browse"
        if (e.state & 0x1) and OLE_DND is not None and (has or browse):      # Shift+오른쪽 클릭: 윈도우 메뉴 바로
            self.windows_menu(e.x_root, e.y_root, extended=True)
            return "break"
        m = self.menu
        m.delete(0, "end")
        h = self.current()
        if OLE_DND is not None and (has or browse):
            m.add_command(label="Windows 메뉴 — 속성·압축·보내기·연결 프로그램 등  (Shift+오른쪽 클릭)",
                          command=lambda x=e.x_root, y=e.y_root: self.windows_menu(x, y))
            m.add_separator()
        if has:
            m.add_command(label="폴더 열기" if h.get("is_dir") else "열기", command=self.activate)
            if not h.get("is_dir"):
                m.add_command(label="전체 내용 보기", command=self.show_full)
            if not browse:
                m.add_command(label="이 칸에서 들어 있는 폴더로 이동", command=self.goto_containing)
            m.add_command(label="탐색기에서 보기", command=self.open_folder)
            m.add_separator()
            m.add_command(label="잘라내기  (Ctrl+X)", command=lambda: self.clip(cut=True))
            m.add_command(label="복사  (Ctrl+C)", command=lambda: self.clip(cut=False))
        if browse:
            m.add_command(label="붙여넣기  (Ctrl+V)", command=self.paste)
        if has:
            m.add_separator()
            m.add_command(label="이름 바꾸기  (F2)" if len(self.tree.selection()) == 1
                          else f"이름 한꺼번에 바꾸기 — 연번·첫 문장 ({len(self.tree.selection())}개)  (F2)",
                          command=self.rename)
            m.add_command(label="삭제 — 휴지통  (Del)", command=self.delete)
            m.add_command(label="경로 복사", command=self.copy_path)
        if browse:
            m.add_separator()
            m.add_command(label="새 폴더  (Ctrl+Shift+N)", command=self.new_folder)
            m.add_command(label="새로 고침  (F5)", command=self.refresh)
        m.tk_popup(e.x_root, e.y_root)

    def windows_menu(self, x, y, extended=False):
        """윈도우 탐색기 오른쪽 클릭 메뉴 그대로 (고른 파일 / 빈 곳이면 이 폴더의 메뉴)"""
        paths = self.selected_paths()
        bg = None if paths else (self.cwd if self.mode == "browse" else None)
        if not paths and not bg:
            return
        self.app.release_previews()
        try:
            done = OLE_DND.shell_menu(paths, x, y, background_dir=bg, extended=extended)
        except Exception as ex:
            messagebox.showerror(APP_NAME, f"Windows 메뉴를 열 수 없습니다.\n{ex}")
            return
        if done:                       # 지우기·압축·새로 만들기 등으로 폴더 내용이 바뀌었을 수 있음
            self.after(600, self.app.refresh_browsers)
            self.after(2500, self.app.refresh_browsers)

    # ───────── 파일 동작 ─────────
    def open_file(self):
        h = self.current()
        if h:
            try:
                os.startfile(h["path"])
            except Exception as e:
                messagebox.showerror(APP_NAME, f"파일을 열 수 없습니다.\n{e}")

    def open_folder(self):
        h = self.current()
        if h:
            subprocess.Popen(["explorer", "/select,", os.path.normpath(h["path"])])
        elif self.cwd:
            os.startfile(self.cwd)

    def goto_containing(self):
        h = self.current()
        if h:
            self.query_var.set("")
            self.navigate(os.path.dirname(h["path"]), select=h["path"])

    def copy_path(self):
        paths = self.selected_paths()
        if paths:
            self.clipboard_clear()
            self.clipboard_append("\n".join(paths))
            self.status_var.set("경로를 복사했습니다.")

    def clip(self, cut):
        paths = self.selected_paths()
        if not paths:
            return "break"
        self.app.file_clip = (paths, cut)
        try:
            clipboard_set_files(paths, cut, self.hwnd())
        except Exception:
            pass
        self.status_var.set(f"{len(paths)}개 {'잘라냄' if cut else '복사함'} — 붙여 넣을 칸에서 Ctrl+V")
        return "break"

    def paste(self):
        if self.mode != "browse" or not self.cwd:
            self.status_var.set("붙여넣기는 폴더를 둘러볼 때(검색어 비움) 할 수 있습니다.")
            return "break"
        try:
            paths, cut = clipboard_get_files(self.hwnd())
        except Exception:
            paths, cut = [], False
        if not paths and self.app.file_clip:
            paths, cut = self.app.file_clip
        paths = [p for p in paths if os.path.exists(p)]
        if not paths:
            self.status_var.set("붙여 넣을 파일이 없습니다.")
            return "break"
        if self.app.transfer(paths, self.cwd, move=cut, source=self):
            if cut:
                self.app.file_clip = None
                try:
                    clipboard_clear_files(self.hwnd())
                except Exception:
                    pass
        return "break"

    def rename(self):
        """F2: 하나면 이름 바꾸기 창, 여러 개면 연번·첫 문장 일괄 바꾸기"""
        sel = [i for i in self.tree.get_children() if i in self.tree.selection()]   # 목록에 보이는 순서
        if not sel:
            return "break"
        if len(sel) == 1:
            h = self.hits[sel[0]]
            dlg = RenameDialog(self, h)
            self.wait_window(dlg.win)
            if not dlg.result:
                return "break"
            pairs = [(h["path"], dlg.result)]
        else:
            items = [(self.hits[i]["path"], self.hits[i]["name"], self.hits[i].get("is_dir", False)) for i in sel]
            dlg = BatchRenameDialog(self, items)
            self.wait_window(dlg.win)
            if not dlg.result:
                return "break"
            pairs = dlg.result
        self.app.release_previews()
        ok, errors = do_renames(pairs)
        if errors:
            messagebox.showwarning(APP_NAME, f"{ok}개 바꿈, {len(errors)}개는 바꾸지 못했습니다.\n\n" + "\n".join(errors[:10]))
        new_paths = [b for a, b in pairs if os.path.exists(b)]
        if self.mode == "browse":
            self.load_browse(select=new_paths)
        else:
            mp = dict(pairs)
            for iid in sel:
                h = self.hits[iid]
                nb = mp.get(h["path"])
                if nb and os.path.exists(nb):
                    h.update(path=nb, name=os.path.basename(nb))
                    self.tree.item(iid, values=(h["name"], h["count"] or "이름", h["mtime"], h["folder"]))
        self.status_var.set(f"{ok}개 이름을 바꿨습니다.")
        self.app.refresh_browsers(except_pane=self)
        return "break"

    def delete(self):
        paths = self.selected_paths()
        if not paths:
            return "break"
        self.app.release_previews()
        try:
            if sys.platform != "win32" and not messagebox.askyesno(APP_NAME, f"{len(paths)}개를 지울까요?"):
                return "break"
            shell_file_op(FO_DELETE, paths, hwnd=self.hwnd())
        except Exception as e:
            messagebox.showerror(APP_NAME, f"지울 수 없습니다.\n{e}")
        if self.mode == "search":
            for iid in list(self.tree.selection()):
                if not os.path.exists(self.hits[iid]["path"]):
                    self.tree.delete(iid)
        self.app.refresh_browsers()
        return "break"

    def new_folder(self):
        if self.mode != "browse" or not self.cwd:
            return "break"
        name, k = "새 폴더", 2
        while os.path.exists(os.path.join(self.cwd, name)):
            name, k = f"새 폴더 ({k})", k + 1
        path = os.path.join(self.cwd, name)
        try:
            os.mkdir(path)
        except OSError as e:
            messagebox.showerror(APP_NAME, f"폴더를 만들 수 없습니다.\n{e}")
            return "break"
        self.load_browse(select=[path])
        self.app.refresh_browsers(except_pane=self)
        self.after(50, self.rename)
        return "break"

    # ───────── 끌어다 놓기 (칸끼리) ─────────
    def _drag_press(self, e):
        row = self.tree.identify_row(e.y)
        self._drag = None
        if not row or self.tree.identify_region(e.x, e.y) == "heading":
            return
        self._drag = {"x": e.x_root, "y": e.y_root, "active": False, "pending": None}
        # 여러 개 골라 둔 상태에서 그중 하나를 누르면 선택을 유지해야 끌 수 있음
        if row in self.tree.selection() and len(self.tree.selection()) > 1 and not (e.state & 0x5):
            self._drag["pending"] = row
            return "break"

    def _drag_motion(self, e):
        d = self._drag
        if not d:
            return
        if not d["active"]:
            if abs(e.x_root - d["x"]) + abs(e.y_root - d["y"]) < 10:
                return "break" if d["pending"] else None
            d["paths"] = self.selected_paths()
            if not d["paths"]:
                self._drag = None
                return
            d["active"] = True
            if OLE_DND is not None and self.app.ole_target is not None:
                # 탐색기처럼: 파일 그림이 따라다니고, 이 프로그램 칸·탐색기·바탕화면·다른 프로그램 어디에나 놓을 수 있음
                self._drag = None
                paths = d["paths"]
                self.app.release_previews()
                self.app.drag_source = self
                try:
                    OLE_DND.drag_files(int(self.winfo_toplevel().wm_frame(), 16), paths)
                except Exception:
                    pass
                finally:
                    self.app.drag_source = None
                self.after(300, lambda: self.app.refresh_browsers())
                return "break"
            self.winfo_toplevel().configure(cursor="hand2")
        target, dest = self.app.drop_target(e.x_root, e.y_root, d["paths"])
        if dest:
            op = "복사" if (e.state & 0x4) or not same_drive(d["paths"][0], dest) else "이동"
            if e.state & 0x1:
                op = "이동"
            self.app.set_hint(f"{len(d['paths'])}개 → {os.path.basename(dest) or dest} 로 {op}  (Ctrl=복사, Shift=이동)")
        else:
            self.app.set_hint("놓을 수 없는 곳")
        return "break"

    def _drag_release(self, e):
        d, self._drag = self._drag, None
        if not d:
            return
        if d["active"]:
            self.winfo_toplevel().configure(cursor="")
            self.app.set_hint("")
            target, dest = self.app.drop_target(e.x_root, e.y_root, d["paths"])
            if dest:
                if e.state & 0x4:
                    move = False
                elif e.state & 0x1:
                    move = True
                else:
                    move = same_drive(d["paths"][0], dest)    # 탐색기처럼: 같은 드라이브면 이동, 다르면 복사
                self.app.transfer(d["paths"], dest, move=move, source=self)
            return "break"
        if d["pending"]:
            self.tree.selection_set(d["pending"])
            self.tree.focus(d["pending"])

    # ───────── 전체 내용 창 ─────────
    def show_full(self):
        h = self.current()
        if not h or h.get("is_dir"):
            return
        text = self.app.cache.get_any(h["path"])
        if text is None:
            try:
                text = extract_text(h["path"])[0]
            except Exception as e:
                text = f"(읽을 수 없음: {e})"
        w = tk.Toplevel(self)
        w.title(h["name"])
        w.geometry("820x640")
        bar = ttk.Frame(w, padding=6)
        bar.pack(fill="x")
        info = tk.StringVar()
        ttk.Label(bar, textvariable=info).pack(side="left")
        tx = tk.Text(w, wrap="word", padx=12, pady=10, font=FONT)
        sc = ttk.Scrollbar(w, orient="vertical", command=tx.yview)
        tx.configure(yscrollcommand=sc.set)
        sc.pack(side="right", fill="y")
        tx.pack(fill="both", expand=True)
        tx.insert("1.0", text)
        tx.tag_configure("hl", background="#ffe066")
        tx.tag_configure("cur", background="#ff9f43")
        spots = []
        for p in self.pats:
            for m in p.finditer(text):
                a, b = f"1.0+{m.start()}c", f"1.0+{m.end()}c"
                tx.tag_add("hl", a, b)
                spots.append((m.start(), a, b))
        spots.sort()
        pos = {"i": -1}

        def go(step):
            if not spots:
                return
            pos["i"] = (pos["i"] + step) % len(spots)
            _, a, b = spots[pos["i"]]
            tx.tag_remove("cur", "1.0", "end")
            tx.tag_add("cur", a, b)
            tx.see(a)
            info.set(f"일치 {pos['i'] + 1} / {len(spots)}")
        ttk.Button(bar, text="▲ 이전", command=lambda: go(-1)).pack(side="right")
        ttk.Button(bar, text="▼ 다음", command=lambda: go(1)).pack(side="right", padx=4)
        w.bind("<F3>", lambda e: go(1))
        w.bind("<Shift-F3>", lambda e: go(-1))
        tx.configure(state="disabled")
        info.set(f"일치 {len(spots)}곳" if spots else "일치하는 곳 없음")
        go(1)


# ───────────────────────── 전체 창 ─────────────────────────
# ───────────────────────── 환경설정(글꼴·색상·배경 그림) ─────────────────────────
DEFAULT_THEME = {
    "font_family": "맑은 고딕", "font_size": 10,
    "text_color": "", "bg_color": "", "list_bg": "", "accent": "",   # 비어 있으면 윈도우 기본 모양
    "bg_image": "", "bg_mode": "fill", "bg_dim": True,
}
THEME_PRESETS = {
    "기본(윈도우)": {"text_color": "", "bg_color": "", "list_bg": "", "accent": ""},
    "밝은 회색": {"text_color": "#222222", "bg_color": "#eef0f3", "list_bg": "#ffffff", "accent": "#2a6fdb"},
    "따뜻한 베이지": {"text_color": "#3b2f20", "bg_color": "#f5ecdc", "list_bg": "#fffaf1", "accent": "#d07a1f"},
    "하늘색": {"text_color": "#16324f", "bg_color": "#e3f0fb", "list_bg": "#ffffff", "accent": "#2b7bd6"},
    "초록": {"text_color": "#1f3a26", "bg_color": "#e6f2e8", "list_bg": "#ffffff", "accent": "#2f9a52"},
    "어두운 테마": {"text_color": "#e6e6e6", "bg_color": "#2b2d31", "list_bg": "#1f2124", "accent": "#4c8dff"},
}
BG_MODES = {"fill": "꽉 채우기", "fit": "전체 보이기", "center": "가운데", "tile": "바둑판"}
THEME = dict(DEFAULT_THEME)


def _hex_to_rgb(c):
    c = c.lstrip("#")
    return tuple(int(c[i:i + 2], 16) for i in (0, 2, 4)) if len(c) == 6 else (255, 255, 255)


def _mix(c1, c2, t):
    a, b = _hex_to_rgb(c1), _hex_to_rgb(c2)
    return "#%02x%02x%02x" % tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))


def is_dark(c):
    if not c:
        return False
    r, g, b = _hex_to_rgb(c)
    return (0.299 * r + 0.587 * g + 0.114 * b) < 128


def custom_colors():
    return bool(THEME.get("bg_color") or THEME.get("text_color") or THEME.get("list_bg") or THEME.get("accent"))


def apply_style(root):
    """THEME 내용을 화면 전체 모양(ttk 스타일, 기본 글꼴, tk 위젯 기본 색)에 반영"""
    global FONT
    FONT = (THEME.get("font_family") or "맑은 고딕", int(THEME.get("font_size") or 10))
    root.option_clear()                       # 전에 지정한 색을 지우고 새로
    root.option_add("*Font", FONT)
    if not custom_colors():
        try:
            root.configure(bg="SystemButtonFace" if sys.platform == "win32" else "#d9d9d9")
        except tk.TclError:
            pass
    st = ttk.Style()
    if custom_colors():
        st.theme_use("clam")              # 색을 바꾸려면 색 지정이 되는 모양(clam)을 씀
    else:
        for theme in ("vista", "winnative", "clam"):
            if theme in st.theme_names():
                st.theme_use(theme)
                break
    st.configure(".", font=FONT)
    st.configure("Treeview", rowheight=int(FONT[1] * 2.4), font=FONT)
    st.configure("Treeview.Heading", font=(FONT[0], fsz(10), "bold"))
    st.configure("Accent.TButton", font=(FONT[0], fsz(10), "bold"))
    if not custom_colors():
        return
    fg = THEME.get("text_color") or "#222222"
    bg = THEME.get("bg_color") or "#f0f0f0"
    lb = THEME.get("list_bg") or "#ffffff"
    ac = THEME.get("accent") or "#2a6fdb"
    bg2 = _mix(bg, fg, 0.10)              # 버튼·머리글 바탕 (배경보다 살짝 진하게)
    hover = _mix(bg, ac, 0.25)
    border = _mix(bg, fg, 0.30)
    st.configure(".", background=bg, foreground=fg, fieldbackground=lb, bordercolor=border,
                 lightcolor=bg, darkcolor=border, troughcolor=_mix(bg, fg, 0.06),
                 selectbackground=ac, selectforeground="#ffffff", insertcolor=fg)
    st.map(".", foreground=[("disabled", _mix(fg, bg, 0.55))])
    for w in ("TFrame", "TLabel", "TCheckbutton", "TPanedwindow", "TNotebook", "TLabelframe", "TLabelframe.Label"):
        st.configure(w, background=bg, foreground=fg)
    st.configure("TButton", background=bg2, foreground=fg, padding=(8, 3))
    st.map("TButton", background=[("pressed", _mix(bg2, ac, 0.4)), ("active", hover)])
    st.configure("Toolbutton", background=bg2, foreground=fg)
    st.map("Toolbutton", background=[("selected", _mix(bg, ac, 0.45)), ("active", hover)])
    st.configure("Accent.TButton", background=ac, foreground="#ffffff")
    st.map("Accent.TButton", background=[("pressed", _mix(ac, "#000000", 0.2)), ("active", _mix(ac, "#ffffff", 0.15))],
           foreground=[("disabled", _mix("#ffffff", ac, 0.4))])
    st.configure("Menubutton", background=bg2, foreground=fg)
    st.configure("TMenubutton", background=bg2, foreground=fg)
    for w in ("TEntry", "TCombobox", "TSpinbox"):
        st.configure(w, fieldbackground=lb, foreground=fg, background=bg2, arrowcolor=fg)
    st.map("TCombobox", fieldbackground=[("readonly", lb)], foreground=[("readonly", fg)])
    st.configure("Treeview", background=lb, fieldbackground=lb, foreground=fg)
    st.map("Treeview", background=[("selected", ac)], foreground=[("selected", "#ffffff")])
    st.configure("Treeview.Heading", background=bg2, foreground=fg)
    st.map("Treeview.Heading", background=[("active", hover)])
    st.configure("TNotebook.Tab", background=bg2, foreground=fg, padding=(10, 3))
    st.map("TNotebook.Tab", background=[("selected", lb)])
    st.configure("Vertical.TScrollbar", background=bg2, arrowcolor=fg)
    st.configure("Horizontal.TScrollbar", background=bg2, arrowcolor=fg)
    st.configure("TProgressbar", background=ac)
    # tk 위젯(글 상자·메뉴 등) 기본 색
    root.configure(bg=bg)
    for pat, val in (("*Text.background", lb), ("*Text.foreground", fg), ("*Text.insertBackground", fg),
                     ("*Menu.background", lb), ("*Menu.foreground", fg),
                     ("*Menu.activeBackground", ac), ("*Menu.activeForeground", "#ffffff"),
                     ("*Toplevel.background", bg), ("*Listbox.background", lb), ("*Listbox.foreground", fg)):
        root.option_add(pat, val)


def theme_dir_color():
    return "#e8c26a" if is_dark(THEME.get("list_bg")) else "#7a5200"


_bg_cache = {}

# ───────────── 기본 배경 그림 (프로그램이 직접 그림 — 저작권 걱정 없음) ─────────────
BUILTIN_BGS = ["하늘", "노을", "숲", "바다", "밤하늘", "종이"]
BUILTIN_BG_DIR = os.path.join(APP_DIR, "backgrounds")


def _grad(size, stops, horizontal=False):
    """여러 색을 부드럽게 잇는 그라데이션. stops = [(위치 0~1, '#색'), ...]"""
    w, h = size
    n = w if horizontal else h
    line = Image.new("RGB", (n, 1) if horizontal else (1, n))
    px = line.load()
    for i in range(n):
        t = i / max(1, n - 1)
        for (t0, c0), (t1, c1) in zip(stops, stops[1:]):
            if t0 <= t <= t1:
                a, b = _hex_to_rgb(c0), _hex_to_rgb(c1)
                k = (t - t0) / max(1e-6, t1 - t0)
                col = tuple(int(a[j] + (b[j] - a[j]) * k) for j in range(3))
                break
        else:
            col = _hex_to_rgb(stops[-1][1])
        px[(i, 0) if horizontal else (0, i)] = col
    return line.resize((w, h))


def make_builtin_bg(name, size=(1600, 1000)):
    import random
    from PIL import ImageDraw, ImageFilter
    w, h = size
    rnd = random.Random(name)
    sc = w / 1600
    if name == "하늘":
        im = _grad(size, [(0, "#9ccbf5"), (0.65, "#dcefff"), (1, "#ffffff")])
        mask = Image.new("L", size, 0)                       # 구름: 모양(투명도)만 흐리게 해서 흰색을 얹음
        d = ImageDraw.Draw(mask)
        for _ in range(9):
            cx, cy = rnd.randint(0, w), rnd.randint(int(h * 0.1), int(h * 0.75))
            for _ in range(5):
                rx, ry = rnd.randint(60, 160) * sc, rnd.randint(30, 70) * sc
                ox, oy = rnd.randint(-120, 120) * sc, rnd.randint(-30, 30) * sc
                d.ellipse((cx + ox - rx, cy + oy - ry, cx + ox + rx, cy + oy + ry), fill=170)
        im.paste((255, 255, 255), (0, 0, w, h), mask.filter(ImageFilter.GaussianBlur(18 * sc)))
    elif name == "노을":
        im = _grad(size, [(0, "#ff9a76"), (0.45, "#ffc79a"), (0.8, "#ffe6cf"), (1, "#fff6ec")])
        mask = Image.new("L", size, 0)
        d = ImageDraw.Draw(mask)
        r = 170 * sc                                         # 해
        d.ellipse((w * 0.7 - r, h * 0.62 - r, w * 0.7 + r, h * 0.62 + r), fill=210)
        im.paste((255, 240, 200), (0, 0, w, h), mask.filter(ImageFilter.GaussianBlur(40 * sc)))
        d = ImageDraw.Draw(im)                               # 먼 산
        for k, col in ((0.78, "#e7a383"), (0.86, "#d98d70")):
            pts = [(0, h)] + [(x, h * k + 40 * sc * __import__("math").sin(x / (180 * sc) + k * 7)) for x in range(0, w + 20, 20)] + [(w, h)]
            d.polygon(pts, fill=col)
    elif name == "숲":
        im = _grad(size, [(0, "#d9efd6"), (0.6, "#a9d4a3"), (1, "#6fae6a")])
        mask = Image.new("L", size, 0)
        d = ImageDraw.Draw(mask)
        for _ in range(40):                                  # 빛망울
            r = rnd.randint(20, 90) * sc
            x, y = rnd.randint(0, w), rnd.randint(0, h)
            d.ellipse((x - r, y - r, x + r, y + r), fill=rnd.randint(40, 110))
        im.paste((255, 255, 225), (0, 0, w, h), mask.filter(ImageFilter.GaussianBlur(10 * sc)))
    elif name == "바다":
        import math
        im = _grad(size, [(0, "#bfe9f2"), (0.5, "#7fcfe0"), (1, "#3f9fbf")])
        d = ImageDraw.Draw(im)
        for i in range(14):                                  # 물결
            y0 = h * (0.35 + i * 0.05)
            amp, ph = (8 + i * 1.5) * sc, rnd.random() * 6
            pts = [(x, y0 + amp * math.sin(x / ((120 + i * 8) * sc) + ph)) for x in range(0, w + 10, 10)]
            d.line(pts, fill=(255, 255, 255), width=max(1, int(2 * sc)))
        im = Image.blend(im, _grad(size, [(0, "#bfe9f2"), (0.5, "#7fcfe0"), (1, "#3f9fbf")]), 0.55)
    elif name == "밤하늘":
        im = _grad(size, [(0, "#0b1430"), (0.6, "#1c2a55"), (1, "#3a3f6e")])
        d = ImageDraw.Draw(im)
        for _ in range(int(260 * sc * sc) + 40):             # 별
            x, y = rnd.randint(0, w), rnd.randint(0, int(h * 0.9))
            r = rnd.choice((0.6, 0.8, 1, 1, 1.4, 2)) * sc
            v = rnd.randint(170, 255)
            d.ellipse((x - r, y - r, x + r, y + r), fill=(v, v, min(255, v + 20)))
    else:                                                    # 종이
        im = Image.new("RGB", size, _hex_to_rgb("#f4ead7"))
        noise = Image.effect_noise(size, 28).convert("RGB")
        im = Image.blend(im, noise, 0.06)
        im = Image.blend(im, _grad(size, [(0, "#fbf5e9"), (1, "#eadcc1")]), 0.5)
    return im.convert("RGB")


try:
    from photo_walls import PHOTO_WALLS        # 기본 배경 사진 (퍼블릭 도메인)
except Exception:
    PHOTO_WALLS = []


def photo_bg_path(name):
    """기본 배경 사진을 꺼내 두고 그 경로를 돌려줌"""
    os.makedirs(BUILTIN_BG_DIR, exist_ok=True)
    i = [n for n, _, _ in PHOTO_WALLS].index(name)
    path = os.path.join(BUILTIN_BG_DIR, f"photo_{i + 1}.jpg")
    if not os.path.exists(path):
        with open(path + ".part", "wb") as f:
            f.write(base64.b64decode(PHOTO_WALLS[i][2]))
        os.replace(path + ".part", path)
    return path


def photo_thumb(name, size=(72, 45)):
    data = base64.b64decode(next(d for n, _, d in PHOTO_WALLS if n == name))
    im = Image.open(io.BytesIO(data))
    im.draft("RGB", (size[0] * 2, size[1] * 2))     # 큰 사진을 빨리 작게 읽기
    return im.convert("RGB").resize(size)


def builtin_bg_path(name):
    """기본 배경 그림 파일 경로 (처음 고를 때 한 번 그려서 저장)"""
    os.makedirs(BUILTIN_BG_DIR, exist_ok=True)
    path = os.path.join(BUILTIN_BG_DIR, f"bg_{BUILTIN_BGS.index(name) + 1}.png")
    if not os.path.exists(path):
        make_builtin_bg(name).save(path + ".part.png")
        os.replace(path + ".part.png", path)
    return path


def background_photo(w, h):
    """배경 그림을 (w, h) 크기에 맞춰 만든 tk 그림. 설정이 없거나 못 읽으면 None"""
    path = THEME.get("bg_image") or ""
    if not path or not os.path.exists(path) or w < 20 or h < 20:
        return None
    key = (path, os.path.getmtime(path), w, h, THEME.get("bg_mode"), THEME.get("bg_dim"), THEME.get("bg_color"))
    if key in _bg_cache:
        return _bg_cache[key]
    try:
        base = THEME.get("bg_color") or "#ffffff"
        if Image is None:                    # PIL이 없으면 PNG·GIF만, 크기 조절 없이
            import base64
            img = tk.PhotoImage(data=base64.b64encode(open(path, "rb").read()))
        else:
            from PIL import ImageTk
            src = ImageOps.exif_transpose(Image.open(path)).convert("RGB")
            iw, ih = src.size
            canvas = Image.new("RGB", (w, h), _hex_to_rgb(base))
            mode = THEME.get("bg_mode") or "fill"
            if mode == "fill":
                k = max(w / iw, h / ih)
                im = src.resize((max(1, int(iw * k)), max(1, int(ih * k))), Image.LANCZOS)
                canvas.paste(im, ((w - im.width) // 2, (h - im.height) // 2))
            elif mode == "fit":
                k = min(w / iw, h / ih)
                im = src.resize((max(1, int(iw * k)), max(1, int(ih * k))), Image.LANCZOS)
                canvas.paste(im, ((w - im.width) // 2, (h - im.height) // 2))
            elif mode == "tile":
                for y in range(0, h, ih):
                    for x in range(0, w, iw):
                        canvas.paste(src, (x, y))
            else:
                canvas.paste(src, ((w - iw) // 2, (h - ih) // 2))
            if THEME.get("bg_dim", True):    # 글씨가 잘 보이도록 흐리게
                canvas = Image.blend(canvas, Image.new("RGB", (w, h), _hex_to_rgb(base)), 0.45)
            img = ImageTk.PhotoImage(canvas)
        if len(_bg_cache) > 12:
            _bg_cache.clear()
        _bg_cache[key] = img
        return img
    except Exception:
        return None


class SettingsDialog:
    """⚙ 환경설정 창: 글꼴, 글자·배경·목록·강조 색, 배경 그림"""

    def refresh_shortcuts(self):
        """만들어 둔 바로가기는 버튼을 숨기고, 둘 다 있으면 바로가기 칸을 통째로 숨김"""
        desk, task = has_desktop_shortcut(), is_pinned_to_taskbar()
        for b in (self.sc_desk, self.sc_task, self.sc_note):
            b.pack_forget()
        if desk and task:
            self.sc_frame.pack_forget()
            return
        if not desk:
            self.sc_desk.pack(side="left")
        if not task:
            self.sc_task.pack(side="left", padx=(6, 0))
        self.sc_note.pack(side="left", padx=8)

    def make_desk(self):
        try:
            make_desktop_shortcut()
            self.sc_note.configure(text="바탕화면에 만들었습니다.")
        except Exception as e:
            messagebox.showerror(APP_NAME, f"바로가기를 만들 수 없습니다.\n{e}", parent=self.win)
        self.win.after(1500, self.refresh_shortcuts)

    def pin_task(self):
        try:
            make_start_menu_shortcut()          # 시작 메뉴에도 넣어 두면 검색·고정이 쉬움
        except Exception:
            pass
        messagebox.showinfo(APP_NAME,
                            "작업표시줄 고정은 Windows 보안 정책상 프로그램이 스스로 할 수 없어서, 한 번만 직접 해 주세요.\n\n"
                            "① 화면 아래 작업표시줄에 있는 스마트탐색기 아이콘을 마우스 오른쪽 클릭\n"
                            "② [작업 표시줄에 고정] 클릭\n\n"
                            "(시작 메뉴에도 '스마트탐색기'를 넣어 두었습니다. 시작 메뉴에서 오른쪽 클릭 → "
                            "[작업 표시줄에 고정]으로도 됩니다.)", parent=self.win)
        self.sc_note.configure(text="고정하면 이 칸은 저절로 사라집니다.")
        self._watch_pin(40)

    def _watch_pin(self, n):
        try:
            if not self.win.winfo_exists():
                return
        except tk.TclError:
            return
        if is_pinned_to_taskbar():
            self.sc_note.configure(text="작업표시줄에 고정됐습니다.")
            self.win.after(1500, self.refresh_shortcuts)
        elif n > 0:
            self.win.after(1500, lambda: self._watch_pin(n - 1))

    def __init__(self, app):
        self.app = app
        self.orig = dict(THEME)
        self.t = dict(THEME)
        w = self.win = tk.Toplevel(app.root)
        w.title("스마트탐색기 환경설정")
        w.transient(app.root)
        w.resizable(False, False)
        w.protocol("WM_DELETE_WINDOW", self.cancel)
        body = ttk.Frame(w, padding=14)
        body.pack(fill="both", expand=True)

        # 바로가기 (바탕화면·작업표시줄) — 만들고 나면 숨김
        self.sc_frame = ttk.LabelFrame(w, text=" 📌 바로가기 ", padding=(10, 6))
        self.sc_frame.pack(fill="x", padx=14, pady=(12, 0), before=body)
        self.sc_desk = ttk.Button(self.sc_frame, text="🖥 바탕화면에 바로가기 만들기", command=self.make_desk)
        self.sc_task = ttk.Button(self.sc_frame, text="📌 작업표시줄에 고정하기 …", command=self.pin_task)
        self.sc_note = ttk.Label(self.sc_frame, text="", foreground="#2a6fdb")
        self.refresh_shortcuts()

        # 알람·실행 설정 (자동 실행, 트레이, 단축키, 반복 알람)
        af = ttk.Frame(w, padding=(14, 12, 14, 0))
        af.pack(fill="x", before=body)
        ttk.Button(af, text="⏰ 알람·실행 설정 (반복 알람 · 자동 실행 · 트레이 · 단축키) …",
                   style="Accent.TButton", command=self.open_alarm).pack(fill="x")
        ttk.Button(af, text="🗂 색인 설정 (쉬는 동안 문서 내용 미리 읽어 두기) …",
                   command=self.open_index).pack(fill="x", pady=(4, 0))
        uf = ttk.Frame(af)
        uf.pack(fill="x", pady=(6, 0))
        ttk.Label(uf, text=f"버전 v{APP_VERSION}", foreground="#777").pack(side="left")
        self.upd_msg = ttk.Label(uf, text="", foreground="#2a6fdb")
        self.upd_msg.pack(side="left", padx=8)
        ttk.Button(uf, text="🔔 새 버전 확인", command=self.check_now).pack(side="right")

        # 미리 만든 색 조합
        ttk.Label(body, text="빠른 선택", font=(FONT[0], fsz(10), "bold")).grid(row=0, column=0, sticky="w")
        pf = ttk.Frame(body)
        pf.grid(row=0, column=1, columnspan=3, sticky="w", pady=(0, 8))
        for i, name in enumerate(THEME_PRESETS):
            ttk.Button(pf, text=name, command=lambda n=name: self.preset(n)).grid(row=i // 3, column=i % 3, padx=2, pady=2, sticky="ew")
        if Image is not None:                         # 배경 그림 빠른 선택 (작은 그림을 누르면 바로 골라짐)
            from PIL import ImageTk
            gf = ttk.Frame(pf)
            gf.grid(row=(len(THEME_PRESETS) + 2) // 3, column=0, columnspan=3, sticky="w", pady=(6, 0))
            ttk.Label(gf, text="배경 그림:").pack(side="left", padx=(2, 4))
            self._thumbs = []
            for name in BUILTIN_BGS:
                try:
                    th = ImageTk.PhotoImage(make_builtin_bg(name, (72, 45)))
                except Exception:
                    continue
                self._thumbs.append(th)
                b = tk.Label(gf, image=th, text=name, compound="top", cursor="hand2", font=(FONT[0], fsz(8)),
                             relief="solid", borderwidth=1, padx=1, pady=1)
                b.pack(side="left", padx=2)
                b.bind("<Button-1>", lambda e, n=name: self.builtin_bg(n))
            nb = tk.Label(gf, text="없음", width=6, height=3, cursor="hand2", relief="solid", borderwidth=1,
                          font=(FONT[0], fsz(8)))
            nb.pack(side="left", padx=2)
            nb.bind("<Button-1>", lambda e: (self.img_var.set(""), self._sync(), self.apply()))
            if PHOTO_WALLS:                           # 실제 풍경 사진
                ph = ttk.Frame(pf)
                ph.grid(row=(len(THEME_PRESETS) + 2) // 3 + 1, column=0, columnspan=3, sticky="w", pady=(4, 0))
                ttk.Label(ph, text="배경 사진:").grid(row=0, column=0, rowspan=2, sticky="n", padx=(2, 4), pady=(14, 0))
                for i, (name, _, _) in enumerate(PHOTO_WALLS):
                    try:
                        th = ImageTk.PhotoImage(photo_thumb(name))
                    except Exception:
                        continue
                    self._thumbs.append(th)
                    b = tk.Label(ph, image=th, text=name, compound="top", cursor="hand2", font=(FONT[0], fsz(8)),
                                 relief="solid", borderwidth=1, padx=1, pady=1)
                    b.grid(row=i // 5, column=1 + i % 5, padx=2, pady=2)
                    b.bind("<Button-1>", lambda e, n=name: self.builtin_bg(n, photo=True))

        # 글꼴
        ttk.Separator(body).grid(row=1, column=0, columnspan=4, sticky="ew", pady=6)
        ttk.Label(body, text="글꼴", font=(FONT[0], fsz(10), "bold")).grid(row=2, column=0, sticky="w")
        fams = self._families()
        self.fam_var = tk.StringVar(value=self.t["font_family"])
        cb = ttk.Combobox(body, textvariable=self.fam_var, values=fams, width=26)
        cb.grid(row=2, column=1, columnspan=2, sticky="w")
        cb.bind("<<ComboboxSelected>>", lambda e: self._sync())
        cb.bind("<KeyRelease>", lambda e: self._sync())
        ttk.Label(body, text="크기").grid(row=3, column=0, sticky="w", pady=(6, 0))
        self.size_var = tk.StringVar(value=str(self.t["font_size"]))
        sp = ttk.Spinbox(body, from_=8, to=20, width=5, textvariable=self.size_var, command=self._sync)
        sp.grid(row=3, column=1, sticky="w", pady=(6, 0))
        sp.bind("<KeyRelease>", lambda e: self._sync())

        # 색
        ttk.Separator(body).grid(row=4, column=0, columnspan=4, sticky="ew", pady=8)
        ttk.Label(body, text="색상", font=(FONT[0], fsz(10), "bold")).grid(row=5, column=0, sticky="w")
        self.swatches = {}
        for r, (key, label) in enumerate((("text_color", "글자색"), ("bg_color", "창 배경색"),
                                           ("list_bg", "목록·글 상자 배경"), ("accent", "강조색(선택 줄·검색 버튼)"))):
            ttk.Label(body, text=label).grid(row=6 + r, column=0, sticky="w", pady=2)
            sw = tk.Label(body, width=6, relief="solid", borderwidth=1, cursor="hand2")
            sw.grid(row=6 + r, column=1, sticky="w", pady=2)
            sw.bind("<Button-1>", lambda e, k=key: self.pick(k))
            ttk.Button(body, text="고르기…", command=lambda k=key: self.pick(k)).grid(row=6 + r, column=2, sticky="w", padx=4)
            ttk.Button(body, text="기본", command=lambda k=key: self.reset_color(k)).grid(row=6 + r, column=3, sticky="w")
            self.swatches[key] = sw

        # 배경 그림
        ttk.Separator(body).grid(row=10, column=0, columnspan=4, sticky="ew", pady=8)
        ttk.Label(body, text="배경 그림", font=(FONT[0], fsz(10), "bold")).grid(row=11, column=0, sticky="w")
        self.img_var = tk.StringVar(value=self.t.get("bg_image", ""))
        ttk.Entry(body, textvariable=self.img_var, width=30, state="readonly").grid(row=11, column=1, columnspan=2, sticky="w")
        bf = ttk.Frame(body)
        bf.grid(row=11, column=3, sticky="w")
        ttk.Button(bf, text="찾기…", command=self.pick_image).pack(side="left")
        ttk.Button(bf, text="지우기", command=lambda: (self.img_var.set(""), self._sync())).pack(side="left", padx=(2, 0))
        ttk.Label(body, text="보이는 방식").grid(row=12, column=0, sticky="w", pady=(6, 0))
        self.mode_var = tk.StringVar(value=BG_MODES.get(self.t.get("bg_mode", "fill"), "꽉 채우기"))
        mcb = ttk.Combobox(body, textvariable=self.mode_var, values=list(BG_MODES.values()), state="readonly", width=12)
        mcb.grid(row=12, column=1, sticky="w", pady=(6, 0))
        mcb.bind("<<ComboboxSelected>>", lambda e: self._sync())
        self.dim_var = tk.BooleanVar(value=self.t.get("bg_dim", True))
        ttk.Checkbutton(body, text="흐리게 (글씨가 잘 보이게)", variable=self.dim_var,
                        command=self._sync).grid(row=12, column=2, columnspan=2, sticky="w", pady=(6, 0))
        ttk.Label(body, text="배경 그림은 미리보기가 비어 있을 때(파일을 고르기 전) 보입니다. 위 '빠른 선택'에서 기본 그림을 고를 수 있습니다.",
                  foreground="#888").grid(row=13, column=0, columnspan=4, sticky="w", pady=(4, 0))

        # 미리보기
        ttk.Separator(body).grid(row=14, column=0, columnspan=4, sticky="ew", pady=8)
        self.sample = tk.Label(body, text="가나다라 ABC 123  —  미리보기", padx=10, pady=8, relief="solid", borderwidth=1)
        self.sample.grid(row=15, column=0, columnspan=4, sticky="ew")

        btns = ttk.Frame(w, padding=(14, 0, 14, 12))
        btns.pack(fill="x")
        ttk.Button(btns, text="처음 설정으로", command=self.defaults).pack(side="left")
        ttk.Button(btns, text="취소", command=self.cancel).pack(side="right")
        ttk.Button(btns, text="확인", style="Accent.TButton", command=self.ok).pack(side="right", padx=4)
        ttk.Button(btns, text="적용", command=self.apply).pack(side="right")
        self._refresh()
        center_on(w, app.root)
        w.grab_set()

    def check_now(self):
        self.upd_msg.configure(text="확인 중…")

        def done(msg):
            try:
                self.upd_msg.configure(text=msg)
                if self.app.update_info:
                    self.app.show_update()
            except tk.TclError:
                pass
        self.app.check_update(manual=True, done=done)

    def open_index(self):
        try:
            self.win.grab_release()
        except tk.TclError:
            pass
        dlg = IndexDialog(self.app, parent=self.win)
        self.win.wait_window(dlg.win)
        try:
            self.win.grab_set()
            self.win.lift()
        except tk.TclError:
            pass

    def open_alarm(self):
        try:
            self.win.grab_release()                   # 알람 창이 입력을 받을 수 있게
        except tk.TclError:
            pass
        dlg = AlarmDialog(self.app, parent=self.win)
        self.win.wait_window(dlg.win)
        try:
            self.win.grab_set()
            self.win.lift()
        except tk.TclError:
            pass

    @staticmethod
    def _families():
        from tkinter import font as tkfont
        fams = sorted({f for f in tkfont.families() if not f.startswith("@")})
        korean = [f for f in fams if any("가" <= ch <= "힣" for ch in f)]
        pref = [f for f in ("맑은 고딕", "Malgun Gothic", "나눔고딕", "NanumGothic", "굴림", "돋움", "바탕",
                            "Segoe UI", "Arial") if f in fams]
        seen, out = set(), []
        for f in pref + korean + fams:
            if f not in seen:
                seen.add(f)
                out.append(f)
        return out

    def _sync(self):
        self.t["font_family"] = self.fam_var.get().strip() or "맑은 고딕"
        try:
            self.t["font_size"] = max(8, min(20, int(self.size_var.get())))
        except ValueError:
            pass
        self.t["bg_image"] = self.img_var.get()
        self.t["bg_mode"] = next((k for k, v in BG_MODES.items() if v == self.mode_var.get()), "fill")
        self.t["bg_dim"] = self.dim_var.get()
        self._refresh()

    def _refresh(self):
        for key, sw in self.swatches.items():
            c = self.t.get(key) or ""
            sw.configure(bg=c or "#f0f0f0", text="" if c else "기본")
        fg = self.t.get("text_color") or "#222222"
        bg = self.t.get("list_bg") or "#ffffff"
        try:
            self.sample.configure(font=(self.t["font_family"], int(self.t["font_size"])), fg=fg, bg=bg)
        except tk.TclError:
            pass

    def preset(self, name):
        self.t.update(THEME_PRESETS[name])
        self._refresh()

    def pick(self, key):
        from tkinter import colorchooser
        c = colorchooser.askcolor(color=self.t.get(key) or None, parent=self.win, title="색 고르기")[1]
        if c:
            self.t[key] = c
            if key != "accent" and not self.t.get("accent"):
                self.t["accent"] = "#2a6fdb"
            self._refresh()

    def reset_color(self, key):
        self.t[key] = ""
        self._refresh()

    def builtin_bg(self, name, photo=False):
        try:
            self.img_var.set(photo_bg_path(name) if photo else builtin_bg_path(name))
        except Exception as e:
            messagebox.showerror(APP_NAME, f"배경 그림을 만들지 못했습니다.\n{e}", parent=self.win)
            return
        self._sync()
        self.apply()                                  # 고르면 바로 미리보기 칸에 보이게

    def pick_image(self):
        p = filedialog.askopenfilename(parent=self.win, title="배경 그림 고르기",
                                       filetypes=[("그림 파일", "*.png *.jpg *.jpeg *.bmp *.gif *.webp"), ("모든 파일", "*.*")])
        if p:
            self.img_var.set(os.path.normpath(p))
            self._sync()

    def defaults(self):
        self.t = dict(DEFAULT_THEME)
        self.fam_var.set(self.t["font_family"])
        self.size_var.set(str(self.t["font_size"]))
        self.img_var.set("")
        self.mode_var.set(BG_MODES["fill"])
        self.dim_var.set(True)
        self._refresh()

    def apply(self):
        self._sync()
        self.app.apply_theme(dict(self.t))
        try:
            self.win.lift()
            self.win.focus_set()
        except tk.TclError:
            pass

    def ok(self):
        self._sync()
        t = dict(self.t)
        self.win.grab_release()
        self.win.destroy()
        if t != THEME:
            self.app.apply_theme(t)

    def cancel(self):
        self.win.grab_release()
        self.win.destroy()
        if THEME != self.orig:                        # '적용'으로 바꿔 본 것을 되돌림
            self.app.apply_theme(self.orig)


# ───────────── 반복 알람 · 트레이 · 자동 실행 · 바로 실행 단축키 ─────────────
try:
    import pystray
except ImportError:
    pystray = None

INSTANCE_PORT = 48631                       # 프로그램이 이미 켜져 있는지 확인하는 내부 번호(이 PC 안에서만)
INSTANCE_REPLY = b"SMARTEXPLORER-OK"           # 진짜 스마트탐색기인지 확인하는 대답
RUN_KEY = r"Software\Microsoft\Windows\CurrentVersion\Run"
RUN_NAME = "SmartExplorer"
DEFAULT_ALARM = {
    "enabled": True,
    "mode": "schedule",          # schedule = 평일/휴일 일정, interval = 단순 반복
    "wd_start": "18:00",         # 평일: 이 시각부터
    "wd_end": "09:00",           # 평일: 이 시각까지 (시작보다 이르면 다음날 아침까지)
    "wd_every": 60,              # 평일: 몇 분마다
    "hd_every": 60,              # 휴일: 프로그램을 켠 순간부터 몇 분마다
    "every": 60, "unit": "분",   # 단순 반복 간격
    "message": "초과근무 체크시간입니다",
    "sound": True,
    "tts": True,                 # 알림 글을 음성으로 읽어주기 (기본 켜짐)
    "tts_repeat": 2,             # 음성 반복 횟수
    "song_on": False,            # 노래 파일 재생
    "song": "",                  # 노래 파일 경로
    "open_insarang": False,      # 알람이 울릴 때 인사랑도 함께 열기
    "open_record": True,         # 인사랑이 열리면 '초과근무기록' 버튼을 눌러 팝업까지 자동으로 띄우기 (시험 기능)
    "extra_holidays": "",        # 추가 휴일 (예: 2026-12-31, 2027-01-01)
}
# 관공서 공휴일 (대체·임시공휴일 포함). 토·일요일은 따로 넣지 않아도 휴일로 봄
HOLIDAYS_KR = {
    "2026-01-01", "2026-02-16", "2026-02-17", "2026-02-18", "2026-03-01", "2026-03-02", "2026-05-05",
    "2026-05-24", "2026-05-25", "2026-06-03", "2026-06-06", "2026-07-17", "2026-08-15", "2026-08-17",
    "2026-09-24", "2026-09-25", "2026-09-26", "2026-10-03", "2026-10-05", "2026-10-09", "2026-12-25",
}


def _parse_hm(text, default=(18, 0)):
    try:
        h, m = (int(x) for x in str(text).strip().split(":"))
        if 0 <= h < 24 and 0 <= m < 60:
            return h, m
    except (ValueError, TypeError):
        pass
    return default


HOLIDAY_FEED_URL = "https://smartgong.kr/ads/holidays_kr.json"   # 인터넷에서 받는 공휴일 목록 (임시공휴일 포함)
HOLIDAYS_ONLINE = set()          # 인터넷에서 받은 공휴일 (받기 전엔 비어 있음)
HOLIDAY_CACHE = os.path.join(APP_DIR, "holidays_cache.json")


def load_holiday_cache():
    """지난번에 받아 둔 공휴일 목록을 읽어 옴 (인터넷이 안 돼도 쓰도록)"""
    try:
        with open(HOLIDAY_CACHE, encoding="utf-8") as f:
            HOLIDAYS_ONLINE.update(x for x in json.load(f).get("dates", []) if re.fullmatch(r"\d{4}-\d{2}-\d{2}", str(x)))
    except Exception:
        pass


def fetch_online_holidays():
    """공휴일 목록을 받아 HOLIDAYS_ONLINE에 합치고, 새 날짜가 생겼으면 True"""
    raw = net_request(HOLIDAY_FEED_URL, headers={"User-Agent": f"SmartExplorer/{APP_VERSION}"}, limit=256 * 1024)
    dates = {str(x) for x in json.loads(raw.decode("utf-8")).get("dates", [])}
    dates = {x for x in dates if re.fullmatch(r"\d{4}-\d{2}-\d{2}", x)}
    if not dates:
        return False
    changed = not dates <= HOLIDAYS_ONLINE
    HOLIDAYS_ONLINE.update(dates)
    try:
        os.makedirs(APP_DIR, exist_ok=True)
        with open(HOLIDAY_CACHE, "w", encoding="utf-8") as f:
            json.dump({"dates": sorted(HOLIDAYS_ONLINE)}, f)
    except Exception:
        pass
    return changed


def is_holiday(d, alarm):
    extra = {x.strip() for x in re.split(r"[,\s]+", alarm.get("extra_holidays", "")) if x.strip()}
    key = d.strftime("%Y-%m-%d")
    return d.weekday() >= 5 or key in HOLIDAYS_KR or key in HOLIDAYS_ONLINE or key in extra


def next_alarm_time(alarm, after, anchor):
    """after(초) 이후 첫 알람 시각.
    평일: wd_start부터 wd_every분마다 그날 자정 전까지 / 휴일: anchor(켠 순간)부터 hd_every분마다"""
    from datetime import date, timedelta
    if alarm.get("mode") == "interval":
        n = max(1, int(alarm.get("every", 60) or 60))
        iv = n * (3600 if alarm.get("unit") == "시간" else 60)
        k = int((after - anchor) // iv) + 1 if after >= anchor else 1
        return anchor + k * iv
    today = datetime.fromtimestamp(after).date()
    for off in range(0, 10):
        d = today + timedelta(days=off)
        day_start = datetime(d.year, d.month, d.day).timestamp()
        day_end = day_start + 86400
        if is_holiday(d, alarm):
            iv = max(1, int(alarm.get("hd_every", 60) or 60)) * 60
            base = max(after, day_start - 1e-6)
            k = int((base - anchor) // iv) + 1 if base >= anchor else 1
            t = anchor + k * iv
            while t < day_start:
                t += iv
        else:
            # 평일: 시작 시각에 맞춰 간격마다. 끝 시각이 시작보다 이르면 '밤사이(다음날 아침까지)'
            iv = max(1, int(alarm.get("wd_every", 60) or 60)) * 60
            h, m = _parse_hm(alarm.get("wd_start", "18:00"))
            eh, em = _parse_hm(alarm.get("wd_end", "09:00"), (9, 0))
            start = day_start + h * 3600 + m * 60
            end = day_start + eh * 3600 + em * 60
            overnight = end <= start

            def allowed(x):   # 시작·끝 정각(예: 9시, 18시)에는 울리지 않음
                return (x < end or x > start) if overnight else (start < x < end)
            base = max(after, day_start - 1e-6)
            k = int((base - start) // iv) + 1
            t = start + k * iv
            while t < day_end and not allowed(t):
                t += iv
        if t > after and t < day_end:
            return t
    return None


def center_on(win, parent=None, w=None, h=None):
    """창을 프로그램 창(숨겨져 있으면 화면) 가운데에"""
    win.update_idletasks()
    w = w or win.winfo_reqwidth()
    h = h or win.winfo_reqheight()
    try:
        if parent is not None and parent.winfo_viewable():
            px, py, pw, ph = parent.winfo_rootx(), parent.winfo_rooty(), parent.winfo_width(), parent.winfo_height()
        else:
            raise tk.TclError
    except Exception:
        px, py, pw, ph = 0, 0, win.winfo_screenwidth(), win.winfo_screenheight()
    try:
        x = max(0, int(px + (pw - w) // 2))
        y = max(0, int(py + (ph - h) // 2))
        win.geometry(f"{int(w)}x{int(h)}+{x}+{y}")
    except Exception:
        pass
DEFAULT_HOTKEY = {"ctrl": True, "alt": False, "shift": True, "win": False, "key": "E", "enabled": True}   # Ctrl+Shift+E
OLD_DEFAULT_HOTKEY = {"ctrl": True, "alt": True, "shift": False, "win": False, "key": "E"}
HOTKEY_KEYS = [chr(c) for c in range(ord("A"), ord("Z") + 1)] + [str(d) for d in range(10)] + \
              [f"F{n}" for n in range(1, 13)] + ["Space"]


def launch_command(tray=True):
    """윈도우 시작 때 실행할 명령 (exe면 exe, 파이썬 파일이면 pythonw로)"""
    if getattr(sys, "frozen", False):
        cmd = f'"{sys.executable}"'
    else:
        py = sys.executable
        pyw = os.path.join(os.path.dirname(py), "pythonw.exe")
        cmd = f'"{pyw if os.path.exists(pyw) else py}" "{os.path.abspath(__file__)}"'
    return cmd + (" --tray" if tray else "")


def autostart_enabled():
    if sys.platform != "win32":
        return False
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY) as k:
            winreg.QueryValueEx(k, RUN_NAME)
            return True
    except OSError:
        return False


def set_autostart(on):
    if sys.platform != "win32":
        return False
    import winreg
    with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY, 0, winreg.KEY_SET_VALUE) as k:
        if on:
            winreg.SetValueEx(k, RUN_NAME, 0, winreg.REG_SZ, launch_command(tray=True))
        else:
            try:
                winreg.DeleteValue(k, RUN_NAME)
            except OSError:
                pass
    return True


SHORTCUT_NAME = "스마트탐색기.lnk"
EXE_NAME = "SmartExplorer.exe"


def desktop_dir():
    try:
        import ctypes
        buf = ctypes.create_unicode_buffer(260)
        if ctypes.windll.shell32.SHGetFolderPathW(None, 0x10, None, 0, buf) == 0 and buf.value:   # 바탕화면(원드라이브 포함)
            return buf.value
    except Exception:
        pass
    return os.path.join(os.path.expanduser("~"), "Desktop")


def has_desktop_shortcut():
    try:
        return os.path.exists(os.path.join(desktop_dir(), SHORTCUT_NAME))
    except Exception:
        return False


def is_pinned_to_taskbar():
    """작업표시줄에 고정돼 있는지 (고정한 바로가기들 중 이 프로그램을 가리키는 것이 있는지)"""
    d = os.path.join(os.environ.get("APPDATA", ""), r"Microsoft\Internet Explorer\Quick Launch\User Pinned\TaskBar")
    exe = os.path.basename(sys.executable if getattr(sys, "frozen", False) else EXE_NAME).lower()
    try:
        for n in os.listdir(d):
            if not n.lower().endswith(".lnk"):
                continue
            if os.path.splitext(n)[0] in ("스마트탐색기", "SmartExplorer"):
                return True
            with open(os.path.join(d, n), "rb") as f:
                data = f.read(65536).lower()
            if exe.encode("utf-16-le") in data or exe.encode("latin-1", "ignore") in data:
                return True
    except OSError:
        pass
    return False


def create_lnk(lnk_path, target, args="", workdir="", icon="", desc=""):
    """윈도우 바로가기(.lnk) 만들기 — PowerShell 없이 Windows 기능(IShellLink)을 직접 씀"""
    import ctypes
    ole32 = ctypes.windll.ole32

    class GUID(ctypes.Structure):
        _fields_ = [("a", ctypes.c_uint32), ("b", ctypes.c_uint16), ("c", ctypes.c_uint16), ("d", ctypes.c_ubyte * 8)]

    def guid(t):
        g = GUID()
        ole32.CLSIDFromString(ctypes.c_wchar_p(t), ctypes.byref(g))
        return g

    def vcall(ptr, i, argtypes, *a):
        vt = ctypes.cast(ptr, ctypes.POINTER(ctypes.POINTER(ctypes.c_void_p)))[0]
        return ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.c_void_p, *argtypes)(vt[i])(ptr, *a)

    ole32.CoInitialize(None)
    ole32.CoCreateInstance.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_ulong, ctypes.c_void_p,
                                       ctypes.POINTER(ctypes.c_void_p)]
    psl, ppf = ctypes.c_void_p(), ctypes.c_void_p()
    hr = ole32.CoCreateInstance(ctypes.byref(guid("{00021401-0000-0000-C000-000000000046}")), None, 1,
                                ctypes.byref(guid("{000214F9-0000-0000-C000-000000000046}")), ctypes.byref(psl))
    if hr != 0 or not psl:
        raise OSError(f"바로가기 기능을 쓸 수 없습니다 ({hr & 0xFFFFFFFF:#x})")
    W = ctypes.c_wchar_p
    try:
        vcall(psl.value, 20, [W], target)                     # SetPath
        vcall(psl.value, 11, [W], args or "")                 # SetArguments
        vcall(psl.value, 9, [W], workdir or "")               # SetWorkingDirectory
        vcall(psl.value, 7, [W], desc or "")                  # SetDescription
        vcall(psl.value, 17, [W, ctypes.c_int], icon or target, 0)   # SetIconLocation
        hr = vcall(psl.value, 0, [ctypes.c_void_p, ctypes.POINTER(ctypes.c_void_p)],
                   ctypes.byref(guid("{0000010B-0000-0000-C000-000000000046}")), ctypes.byref(ppf))
        if hr != 0 or not ppf:
            raise OSError("바로가기를 저장할 수 없습니다")
        hr = vcall(ppf.value, 6, [W, ctypes.c_int], lnk_path, 1)    # IPersistFile::Save
        if hr != 0:
            raise OSError(f"바로가기를 저장할 수 없습니다 ({hr & 0xFFFFFFFF:#x}): {lnk_path}")
    finally:
        for p in (ppf, psl):
            if p:
                vcall(p.value, 2, [])


def make_start_menu_shortcut():
    make_desktop_shortcut(os.path.join(os.environ.get("APPDATA", ""), r"Microsoft\Windows\Start Menu\Programs"))


def make_desktop_shortcut(folder=None):
    """바탕화면(또는 folder)에 '스마트탐색기' 바로가기 만들기"""
    if getattr(sys, "frozen", False):
        target, args, workdir = sys.executable, "", os.path.dirname(sys.executable)
    else:
        py = sys.executable
        pyw = os.path.join(os.path.dirname(py), "pythonw.exe")
        target = pyw if os.path.exists(pyw) else py
        args, workdir = f'"{os.path.abspath(__file__)}"', os.path.dirname(os.path.abspath(__file__))
    folder = folder or desktop_dir()
    os.makedirs(folder, exist_ok=True)
    create_lnk(os.path.join(folder, SHORTCUT_NAME), target, args, workdir, target, "스마트탐색기 (스마트공 시리즈)")


def hotkey_text(hk):
    parts = [n for k, n in (("ctrl", "Ctrl"), ("alt", "Alt"), ("shift", "Shift"), ("win", "Win")) if hk.get(k)]
    return "+".join(parts + [hk.get("key", "E")])


class SingleInstance:
    """두 번째로 실행하면 이미 켜진 프로그램을 앞으로 불러내고 스스로 끝남"""

    def __init__(self):
        import socket
        self.sock = None
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        try:
            s.bind(("127.0.0.1", INSTANCE_PORT))
            s.listen(5)
            self.sock = s
        except OSError:
            s.close()

    @property
    def first(self):
        return self.sock is not None

    def notify_existing(self, msg):
        """켜져 있는 스마트탐색기에 알림. 진짜 스마트탐색기가 대답하면 True
        (같은 번호를 다른 프로그램이 쓰고 있으면 False → 그냥 새로 실행)"""
        import socket
        try:
            with socket.create_connection(("127.0.0.1", INSTANCE_PORT), timeout=2) as c:
                c.settimeout(2)
                c.sendall(msg.encode())
                return c.recv(16) == INSTANCE_REPLY
        except OSError:
            return False

    def serve(self, q):
        def loop():
            while True:
                try:
                    c, _ = self.sock.accept()
                    with c:
                        data = c.recv(64).decode("utf-8", "ignore")
                        try:
                            c.sendall(INSTANCE_REPLY)
                        except OSError:
                            pass
                    q.put(("instance", data))
                except OSError:
                    break
        threading.Thread(target=loop, daemon=True).start()


class GlobalHotkey:
    """윈도우 어디서든 누르면 이 프로그램을 앞으로 불러오는 단축키"""
    MODS = {"alt": 0x1, "ctrl": 0x2, "shift": 0x4, "win": 0x8}

    def __init__(self, q):
        self.q = q
        self.tid = None
        self.error = ""

    @staticmethod
    def _vk(key):
        if key == "Space":
            return 0x20
        if len(key) == 1:
            return ord(key.upper())
        if key.startswith("F") and key[1:].isdigit():
            return 0x70 + int(key[1:]) - 1
        return 0

    def start(self, hk):
        self.stop()
        self.error = ""
        if sys.platform != "win32" or not hk.get("enabled", True):
            return
        mods = sum(v for k, v in self.MODS.items() if hk.get(k)) | 0x4000   # MOD_NOREPEAT
        vk = self._vk(hk.get("key", "E"))
        if not vk or mods == 0x4000:
            self.error = "Ctrl·Alt·Shift·Win 중 하나 이상과 함께 정해 주세요"
            return
        ready = threading.Event()

        def loop():
            import ctypes
            from ctypes import wintypes
            u32 = ctypes.windll.user32
            self.tid = ctypes.windll.kernel32.GetCurrentThreadId()
            if not u32.RegisterHotKey(None, 1, mods, vk):
                self.error = f"{hotkey_text(hk)} 는 다른 프로그램이 쓰고 있습니다"
                self.tid = None
                ready.set()
                return
            ready.set()
            msg = wintypes.MSG()
            while u32.GetMessageW(ctypes.byref(msg), None, 0, 0) > 0:
                if msg.message == 0x0312:                 # WM_HOTKEY
                    self.q.put(("show", None))
            u32.UnregisterHotKey(None, 1)
        threading.Thread(target=loop, daemon=True).start()
        ready.wait(2)

    def stop(self):
        if self.tid and sys.platform == "win32":
            import ctypes
            ctypes.windll.user32.PostThreadMessageW(self.tid, 0x0012, 0, 0)   # WM_QUIT
            time.sleep(0.05)
        self.tid = None


class TrayIcon:
    """작업 표시줄 오른쪽 알림 영역 아이콘: 열기 · 알람 켜기/끄기 · 끝내기"""

    def __init__(self, app):
        self.app = app
        self.icon = None
        if pystray is None or Image is None:
            return
        try:
            import base64
            img = Image.open(io.BytesIO(base64.b64decode(ICON_PNG_64)))
            q = app.bgq
            menu = pystray.Menu(
                pystray.MenuItem("스마트탐색기 열기", lambda: q.put(("show", None)), default=True),
                pystray.MenuItem("반복 알람", lambda: q.put(("alarm_toggle", None)),
                                 checked=lambda item: bool(app.alarm.get("enabled"))),
                pystray.MenuItem("알람·실행 설정…", lambda: q.put(("alarm_dialog", None))),
                pystray.Menu.SEPARATOR,
                pystray.MenuItem("끝내기", lambda: q.put(("quit", None))),
            )
            self.icon = pystray.Icon("SmartExplorer", img, APP_NAME, menu)
            self.icon.run_detached()
        except Exception:
            self.icon = None

    @property
    def ok(self):
        return self.icon is not None

    def notify(self, text, title=APP_NAME):
        if self.icon is not None:
            try:
                self.icon.notify(text, title)
            except Exception:
                pass

    def set_title(self, text):
        if self.icon is not None:
            try:
                self.icon.title = text[:120]
                self.icon.update_menu()
            except Exception:
                pass

    def stop(self):
        if self.icon is not None:
            try:
                self.icon.stop()
            except Exception:
                pass


INSARANG_URL = "https://chungnam.insarang.go.kr/nexin/index.html"
SSO_PROCS = ("passni.exe", "magicpass.exe")        # 행정포털(SSO) 로그인 프로그램


def running_process_names():
    """실행 중인 프로세스 이름(소문자) 집합. 알 수 없으면 None."""
    if sys.platform != "win32":
        return None
    try:
        import ctypes
        from ctypes import wintypes

        class PE(ctypes.Structure):
            _fields_ = [("dwSize", wintypes.DWORD), ("cntUsage", wintypes.DWORD),
                        ("th32ProcessID", wintypes.DWORD), ("th32DefaultHeapID", ctypes.c_size_t),
                        ("th32ModuleID", wintypes.DWORD), ("cntThreads", wintypes.DWORD),
                        ("th32ParentProcessID", wintypes.DWORD), ("pcPriClassBase", ctypes.c_long),
                        ("dwFlags", wintypes.DWORD), ("szExeFile", ctypes.c_wchar * 260)]
        k32 = ctypes.windll.kernel32
        k32.CreateToolhelp32Snapshot.restype = wintypes.HANDLE
        k32.CreateToolhelp32Snapshot.argtypes = [wintypes.DWORD, wintypes.DWORD]
        k32.Process32FirstW.argtypes = [wintypes.HANDLE, ctypes.POINTER(PE)]
        k32.Process32NextW.argtypes = [wintypes.HANDLE, ctypes.POINTER(PE)]
        k32.CloseHandle.argtypes = [wintypes.HANDLE]
        snap = k32.CreateToolhelp32Snapshot(0x2, 0)       # TH32CS_SNAPPROCESS
        if not snap or snap == wintypes.HANDLE(-1).value:
            return None
        names = set()
        try:
            pe = PE()
            pe.dwSize = ctypes.sizeof(PE)
            ok = k32.Process32FirstW(snap, ctypes.byref(pe))
            while ok:
                names.add(pe.szExeFile.lower())
                ok = k32.Process32NextW(snap, ctypes.byref(pe))
        finally:
            k32.CloseHandle(snap)
        return names
    except Exception:
        return None


def launch_insarang():
    """Edge로 인사랑을 엽니다(초과근무 알리미와 같은 microsoft-edge: 방식)."""
    if sys.platform == "win32":
        try:
            import ctypes
            ctypes.windll.shell32.ShellExecuteW.argtypes = [
                ctypes.c_void_p, ctypes.c_wchar_p, ctypes.c_wchar_p,
                ctypes.c_wchar_p, ctypes.c_wchar_p, ctypes.c_int]
            ctypes.windll.shell32.ShellExecuteW.restype = ctypes.c_void_p
            r = ctypes.windll.shell32.ShellExecuteW(None, "open", "microsoft-edge:" + INSARANG_URL, None, None, 1)
            if (r or 0) > 32:
                return True
        except Exception:
            pass
    try:
        import webbrowser
        return bool(webbrowser.open(INSARANG_URL))
    except Exception:
        return False


def open_insarang(parent=None, with_record=False, root=None, quiet=False):
    """🏢 인사랑 열기: 행정포털(SSO) 로그인 상태를 보고 Edge로 인사랑을 엽니다.
    with_record=True 이면 인사랑이 뜬 뒤 '초과근무기록' 버튼을 눌러 팝업까지 띄워 봅니다.
    quiet=True(알람 때 자동으로 열 때)는 물어보거나 오류창을 띄우지 않고, 안 될 것 같으면 그냥 건너뜁니다."""
    procs = running_process_names()
    if procs is not None and not any(p in procs for p in SSO_PROCS):
        if quiet:
            return False
        if not messagebox.askyesno(
                "인사랑",
                "행정포털(SSO) 로그인이 확인되지 않았습니다.\n"
                "먼저 행정포털에 로그인한 뒤 인사랑을 여는 것이 좋습니다.\n\n"
                "그래도 인사랑을 여시겠습니까?", parent=parent):
            return False
    if not launch_insarang():
        if not quiet:
            messagebox.showerror("인사랑", "인사랑을 열지 못했습니다.\nEdge 설치와 URL 연결을 확인해 주세요.", parent=parent)
        return False
    if with_record:
        host = root or parent

        def _report(msg):                                      # 안 됐으면 이유를 알려 줌 (성공이면 조용히)
            if msg != "ok" and host is not None:
                try:
                    host.after(0, lambda: messagebox.showinfo("인사랑", msg))
                except Exception:
                    pass
        InsarangRecordOpener.start(host, _report)
    return True


class InsarangRecordOpener:
    """인사랑 본창(Edge)에서 '초과근무기록' 버튼을 눌러 '초과근무기록관리 팝업'을 띄워 줍니다.
    화면 읽기 기능(Windows 접근성/UI Automation)으로 버튼을 찾고, 프로그램이 '누르기' 신호를 보냅니다.
    (마우스를 움직여 좌표를 클릭하지는 않습니다. 못 찾거나 후보가 여러 개면 아무것도 누르지 않고,
     입력·저장·퇴근확인 같은 동작은 하지 않습니다.)"""
    running = False
    WAIT_SEC = 90
    BTN_NAME = "초과근무기록"            # 본창의 버튼 (퇴근확인 버튼 바로 아래)
    ANCHOR_NAME = "퇴근확인"             # 위치를 가늠하는 기준 버튼 (누르지 않음)
    POPUP_NAME = "초과근무기록관리 팝업"   # 눌렀을 때 뜨는 팝업의 제목
    NAME_RE = re.compile(r"^\s*초과근무\s*기록\s*$")
    DEBUG_FILE = os.path.join(APP_DIR, "insarang_debug.txt")

    @classmethod
    def start(cls, root=None, on_result=None):
        if cls.running or sys.platform != "win32":
            return
        cls.running = True
        threading.Thread(target=cls._run, args=(root, on_result), daemon=True).start()

    @staticmethod
    def _windows(title_has=None):
        """보이는 Edge(Chrome_WidgetWin_1) 창의 (핸들, 제목). title_has=None 이면 전부"""
        import ctypes
        from ctypes import wintypes
        user32 = ctypes.windll.user32
        found = []
        cb_t = ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)

        def cb(hwnd, _):
            try:
                if user32.IsWindowVisible(hwnd):
                    cls = ctypes.create_unicode_buffer(128)
                    user32.GetClassNameW(hwnd, cls, 128)
                    if cls.value == "Chrome_WidgetWin_1":
                        n = user32.GetWindowTextLengthW(hwnd)
                        buf = ctypes.create_unicode_buffer(n + 1)
                        user32.GetWindowTextW(hwnd, buf, n + 1)
                        if title_has is None or title_has in buf.value:
                            found.append((hwnd, buf.value))
            except Exception:
                pass
            return True
        user32.EnumWindows(cb_t(cb), 0)
        return found

    @staticmethod
    def _ie_children(hwnd):
        """Edge 창 안의 'Internet Explorer_Server'(IE 모드 화면) 핸들"""
        import ctypes
        from ctypes import wintypes
        user32 = ctypes.windll.user32
        found = []
        cb_t = ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)

        def cb(h, _):
            try:
                cls = ctypes.create_unicode_buffer(64)
                user32.GetClassNameW(h, cls, 64)
                if cls.value == "Internet Explorer_Server":
                    found.append(h)
            except Exception:
                pass
            return True
        user32.EnumChildWindows(hwnd, cb_t(cb), 0)
        return found

    @staticmethod
    def _by_name(ui, U, root, name):
        """root 아래에서 이름이 정확히 name 인 요소들"""
        cond = ui.CreatePropertyCondition(U.UIA_NamePropertyId, name)
        arr = root.FindAll(U.TreeScope_Descendants, cond)
        return [arr.GetElement(i) for i in range(min(arr.Length, 200))]

    @classmethod
    def _scan(cls, ui, U, root, rx, limit=20000):
        """이름이 정규식 rx 에 맞는 요소들 (모든 요소를 훑음: 느리므로 마지막 수단)"""
        arr = root.FindAll(U.TreeScope_Descendants, ui.CreateTrueCondition())
        hits = []
        for i in range(min(arr.Length, limit)):
            try:
                el = arr.GetElement(i)
                if rx.match(el.CurrentName or ""):
                    hits.append(el)
            except Exception:
                pass
        return hits

    @staticmethod
    def _rect(el):
        r = el.CurrentBoundingRectangle
        return r.left, r.top, r.right, r.bottom

    @classmethod
    def _choose(cls, ui, U, root, hits):
        """후보 중 하나를 고른다. 하나뿐이면 그것, 여러 개면 '퇴근확인' 버튼 바로 아래에 있는 것."""
        if len(hits) == 1:
            return hits[0]
        try:
            anchors = cls._by_name(ui, U, root, cls.ANCHOR_NAME)
            best, best_d = None, None
            for a in anchors:
                al, at, ar, ab = cls._rect(a)
                for h in hits:
                    hl, ht, hr, hb = cls._rect(h)
                    overlap = min(ar, hr) - max(al, hl)
                    d = ht - ab
                    if overlap > 0 and -5 <= d < 400 and (best_d is None or d < best_d):
                        best, best_d = h, d
            return best
        except Exception:
            return None

    @classmethod
    def _press(cls, ui, U, el):
        """el(또는 위쪽 부모 몇 단계)에서 '누르기'가 되는 것을 눌러 본다. 눌렸으면 True"""
        walker = ui.ControlViewWalker
        cur = el
        for _ in range(4):
            if cur is None:
                break
            try:
                pt = cur.GetCurrentPattern(U.UIA_InvokePatternId)
                if pt:
                    pt.QueryInterface(U.IUIAutomationInvokePattern).Invoke()
                    return True
            except Exception:
                pass
            try:
                pt = cur.GetCurrentPattern(U.UIA_LegacyIAccessiblePatternId)
                if pt:
                    pt.QueryInterface(U.IUIAutomationLegacyIAccessiblePattern).DoDefaultAction()
                    return True
            except Exception:
                pass
            try:
                cur = walker.GetParentElement(cur)
            except Exception:
                cur = None
        return False

    @classmethod
    def _popup_open(cls, ui, U, handles):
        for h in handles:
            try:
                if cls._by_name(ui, U, ui.ElementFromHandle(h), cls.POPUP_NAME):
                    return True
            except Exception:
                pass
        return False

    @classmethod
    def _dump(cls, ui, U, note):
        """안 될 때 원인을 찾을 수 있게 화면 요소 정보를 파일로 남긴다 (개인정보는 담지 않고, 이름에 초과·퇴근·기록이 든 요소만)"""
        try:
            os.makedirs(APP_DIR, exist_ok=True)
            lines = ["[%s] %s v%s" % (time.strftime("%Y-%m-%d %H:%M:%S"), APP_NAME, APP_VERSION), note, "", "-- Edge 창 --"]
            wins = cls._windows()
            for hwnd, t in wins:
                lines.append("hwnd=%s  제목=%s" % (hwnd, t))
            kw = re.compile(r"초과|퇴근|기록|근무")
            for hwnd, t in wins:
                if "인사랑" not in t:
                    continue
                lines.append("")
                lines.append("-- 인사랑 창 %s: 이름에 초과/퇴근/기록/근무가 든 요소 --" % hwnd)
                try:
                    arr = ui.ElementFromHandle(hwnd).FindAll(U.TreeScope_Descendants, ui.CreateTrueCondition())
                    lines.append("전체 요소 수: %d" % arr.Length)
                    n = 0
                    for i in range(min(arr.Length, 20000)):
                        el = arr.GetElement(i)
                        nm = el.CurrentName or ""
                        if kw.search(nm):
                            lines.append("종류=%s 이름=%r 클래스=%r 위치=%s" % (
                                el.CurrentLocalizedControlType, nm[:60], el.CurrentClassName, cls._rect(el)))
                            n += 1
                            if n >= 60:
                                break
                except Exception as e:
                    lines.append("읽기 실패: %r" % (e,))
                for ie in cls._ie_children(hwnd):
                    lines.append("IE 모드 화면 핸들: %s" % ie)
            with open(cls.DEBUG_FILE, "w", encoding="utf-8") as f:
                f.write("\n".join(lines) + "\n")
            return cls.DEBUG_FILE
        except Exception:
            return None

    @classmethod
    def _run(cls, root, on_result):
        result = "시간 안에 인사랑 화면에서 '초과근무기록' 버튼을 찾지 못했습니다. 본창에서 직접 눌러 주세요."
        comtypes = None
        ui = U = None
        ok = False
        try:
            import comtypes
            import comtypes.client
            comtypes.CoInitialize()
            comtypes.client.GetModule("UIAutomationCore.dll")
            from comtypes.gen import UIAutomationClient as U
            ui = comtypes.CoCreateInstance(U.CUIAutomation._reg_clsid_, interface=U.IUIAutomation,
                                           clsctx=comtypes.CLSCTX_INPROC_SERVER)
            deadline = time.time() + cls.WAIT_SEC
            time.sleep(4)                                      # Edge가 뜰 시간
            attempt = 0
            while time.time() < deadline and not ok:
                attempt += 1
                wins = [h for h, _t in cls._windows("인사랑")]
                handles = []
                for w in wins:
                    handles += [w] + cls._ie_children(w)
                if handles and cls._popup_open(ui, U, handles):    # 이미 떠 있으면 또 누르지 않음
                    ok = True
                    break
                for h in handles:
                    try:
                        root_el = ui.ElementFromHandle(h)
                        hits = cls._by_name(ui, U, root_el, cls.BTN_NAME)
                        if not hits and attempt % 3 == 0:          # 이름이 조금 다르게 읽히는 경우를 대비
                            hits = cls._scan(ui, U, root_el, cls.NAME_RE)
                        if not hits:
                            continue
                        target = cls._choose(ui, U, root_el, hits)
                        if target is None:
                            result = "'초과근무기록' 버튼이 여러 개라 어느 것인지 알 수 없어 누르지 않았습니다. 본창에서 직접 눌러 주세요."
                            continue
                        if not cls._press(ui, U, target):
                            result = "'초과근무기록' 버튼을 찾았지만 눌러지지 않았습니다. 본창에서 직접 눌러 주세요."
                            continue
                        result = "'초과근무기록' 버튼은 눌렀지만 팝업이 뜬 것은 확인하지 못했습니다. 화면을 확인해 주세요."
                        t_end = time.time() + 10
                        while time.time() < t_end:
                            if cls._popup_open(ui, U, handles):
                                ok = True
                                break
                            time.sleep(1)
                        deadline = 0                           # 한 번 눌렀으면 다시 누르지 않고 마친다
                        break
                    except Exception:
                        continue
                if ok or deadline == 0:
                    break
                time.sleep(2.5)
        except Exception as e:
            result = "화면 읽기(접근성)를 시작하지 못했습니다. 본창에서 직접 눌러 주세요."
            result += "\n(%r)" % (e,)
        try:
            if not ok and ui is not None:
                path = cls._dump(ui, U, result)
                if path:
                    result += "\n\n원인 확인용 기록: " + path
        except Exception:
            pass
        finally:
            cls.running = False
            try:
                if comtypes is not None:
                    comtypes.CoUninitialize()
            except Exception:
                pass
        if on_result:
            try:
                on_result("ok" if ok else result)
            except Exception:
                pass


def alarm_extras(app, cfg, on_error=None, quiet_insarang=True):
    """알람이 울릴 때(또는 시험할 때) 소리 말고 하는 일: 음성·노래, 인사랑 자동 열기"""
    AlarmAudio.play(app, cfg.get("message", ""), cfg, on_error)
    if cfg.get("open_insarang"):
        app.root.after(1200, lambda: open_insarang(
            None, with_record=bool(cfg.get("open_record")), root=app.root, quiet=quiet_insarang))


class AlarmAudio:
    """알람이 울릴 때 ① 알림 글을 음성으로 읽고 ② 노래 파일을 (팝업을 닫을 때까지) 반복 재생"""
    ALIAS = "seralarm"
    current = None

    def __init__(self, root, text, tts, repeat, song, on_error=None):
        self.root = root
        self.text = (text or "").strip() or "알람입니다"
        self.left = max(1, min(9, int(repeat))) if tts else 0
        self.song = song or ""
        self.on_error = on_error
        self.voice = None
        self.ps = None
        self.mci = False
        self.wav = False
        self.song_tried = False
        self.alive = True
        self.job = None

    @classmethod
    def play(cls, app, message, cfg, on_error=None):
        """cfg: tts·tts_repeat·song_on·song 가 든 사전 (알람 설정)"""
        cls.halt()
        tts = bool(cfg.get("tts"))
        song = (cfg.get("song") or "").strip() if cfg.get("song_on") else ""
        if not tts and not song:
            return
        try:
            rep = int(cfg.get("tts_repeat", 2))
        except (TypeError, ValueError):
            rep = 2
        cls.current = cls(app.root, message, tts, rep, song, on_error)
        cls.current._tick()

    @classmethod
    def halt(cls):
        a, cls.current = cls.current, None
        if a is not None:
            a.stop()

    def _err(self, msg):
        if self.on_error:
            try:
                self.on_error(msg)
            except Exception:
                pass

    # --- 음성 ---
    def _speak(self):
        try:                                           # ① Windows 음성(SAPI)
            if self.voice is None:
                import comtypes.client
                try:
                    self.voice = comtypes.client.CreateObject("SAPI.SpVoice", dynamic=True)
                except TypeError:
                    self.voice = comtypes.client.CreateObject("SAPI.SpVoice")
            self.voice.Speak(self.text, 1)             # 1 = 비동기(읽는 동안 화면이 멈추지 않게)
            return True
        except Exception:
            self.voice = None
        try:                                           # ② 대체: PowerShell 음성 합성
            env = dict(os.environ, SE_TTS_TEXT=self.text)
            self.ps = subprocess.Popen(
                ["powershell", "-NoProfile", "-NonInteractive", "-Command",
                 "Add-Type -AssemblyName System.Speech;"
                 "(New-Object System.Speech.Synthesis.SpeechSynthesizer).Speak($env:SE_TTS_TEXT)"],
                env=env, creationflags=0x08000000)
            return True
        except Exception:
            self.ps = None
        self._err("음성 읽기를 시작하지 못했습니다. (Windows 음성 기능을 확인해 주세요)")
        return False

    def _speaking(self):
        if self.voice is not None:
            try:
                return not bool(self.voice.WaitUntilDone(0))
            except Exception:
                return False
        if self.ps is not None:
            return self.ps.poll() is None
        return False

    # --- 노래 (윈도우 MCI: mp3·wav·wma·m4a) ---
    def _mci(self, cmd):
        import ctypes
        buf = ctypes.create_unicode_buffer(256)
        err = ctypes.windll.winmm.mciSendStringW(cmd, buf, 255, 0)
        return err, buf.value

    def _song_start(self):
        self.song_tried = True
        path = self.song
        if not os.path.isfile(path):
            self._err("노래 파일을 찾을 수 없습니다:\n" + path)
            return
        names = [path]
        try:
            import ctypes
            b = ctypes.create_unicode_buffer(1024)
            if ctypes.windll.kernel32.GetShortPathNameW(path, b, 1024):
                names.append(b.value)
        except Exception:
            pass
        try:
            self._mci("close " + self.ALIAS)
            for q in names:
                for typ in ("", " type mpegvideo"):
                    if self._mci('open "%s"%s alias %s' % (q, typ, self.ALIAS))[0] == 0:
                        if self._mci("play " + self.ALIAS)[0] == 0:
                            self.mci = True
                            return
                        self._mci("close " + self.ALIAS)
        except Exception:
            pass
        if path.lower().endswith(".wav"):
            try:
                import winsound
                winsound.PlaySound(path, winsound.SND_FILENAME | winsound.SND_ASYNC | winsound.SND_LOOP)
                self.wav = True
                return
            except Exception:
                pass
        self._err("노래 파일을 재생하지 못했습니다. (mp3·wav·wma·m4a 파일인지 확인해 주세요)\n" + path)

    def _song_loop(self):
        if self.mci:
            err, mode = self._mci("status %s mode" % self.ALIAS)
            if err == 0 and mode == "stopped":         # 끝나면 처음부터 다시
                self._mci("seek %s to start" % self.ALIAS)
                self._mci("play " + self.ALIAS)

    def _tick(self):
        if not self.alive:
            return
        try:
            if self._speaking():
                pass
            elif self.left > 0:
                self.left -= 1
                if not self._speak():
                    self.left = 0
            elif self.song:
                if not self.song_tried:
                    self._song_start()
                else:
                    self._song_loop()
        except Exception:
            pass
        try:
            self.job = self.root.after(700, self._tick)
        except Exception:
            self.alive = False

    def stop(self):
        self.alive = False
        try:
            if self.job:
                self.root.after_cancel(self.job)
        except Exception:
            pass
        try:
            if self.voice is not None:
                self.voice.Speak("", 3)                # 읽던 것 중단
        except Exception:
            pass
        try:
            if self.ps is not None and self.ps.poll() is None:
                self.ps.terminate()
        except Exception:
            pass
        try:
            if self.mci:
                self._mci("stop " + self.ALIAS)
                self._mci("close " + self.ALIAS)
            if self.wav:
                import winsound
                winsound.PlaySound(None, winsound.SND_PURGE)
        except Exception:
            pass


def play_alarm_sound():
    if sys.platform == "win32":
        try:
            import winsound
            winsound.PlaySound("SystemNotification", winsound.SND_ALIAS | winsound.SND_ASYNC)
            return
        except Exception:
            pass
    try:
        tk._default_root.bell()
    except Exception:
        pass


class AlarmPopup:
    """알람 알림 창: 모니터 가운데, 큼직하게, 항상 위에"""

    def __init__(self, app, message):
        # 설정 창처럼 '다른 창을 못 누르게 잡고 있는 창'(grab)이 열려 있으면 알람 창 버튼이 눌리지 않음
        # → 알람 창이 잠시 넘겨받았다가 닫힐 때 돌려줌
        try:
            self.prev_grab = app.root.grab_current()
        except Exception:
            self.prev_grab = None
        if self.prev_grab is not None:
            try:
                self.prev_grab.grab_release()
            except tk.TclError:
                pass
        w = self.win = tk.Toplevel(app.root)
        w.title("스마트탐색기 알람")
        w.protocol("WM_DELETE_WINDOW", self.close)
        w.attributes("-topmost", True)
        w.resizable(False, False)
        bg = "#fff8e6"
        f = tk.Frame(w, bg=bg, padx=40, pady=30, highlightthickness=4, highlightbackground="#e8902f")
        f.pack(fill="both", expand=True)
        tk.Label(f, text=f"⏰ {datetime.now():%H:%M}", bg=bg, fg="#b4690e",
                 font=(FONT[0], fsz(26), "bold")).pack(anchor="w")
        tk.Label(f, text=message or "알람", bg=bg, fg="#3b2f20", wraplength=640, justify="left",
                 font=(FONT[0], fsz(22), "bold")).pack(anchor="w", pady=(14, 20))
        nxt = app.alarm_next
        tk.Label(f, text=(f"다음 알람: {datetime.fromtimestamp(nxt):%m월 %d일 %H:%M}" if nxt else ""), bg=bg,
                 fg="#8a8278", font=(FONT[0], fsz(14))).pack(anchor="w")
        bf = tk.Frame(f, bg=bg)
        bf.pack(fill="x", pady=(20, 0))
        st = ttk.Style()
        st.configure("Big.TButton", font=(FONT[0], fsz(14), "bold"), padding=(18, 8))
        st.configure("BigPlain.TButton", font=(FONT[0], fsz(13)), padding=(14, 8))
        ttk.Button(bf, text="확인", style="Big.TButton", command=self.close).pack(side="right")
        ttk.Button(bf, text="알람 끄기", style="BigPlain.TButton",
                   command=lambda: (app.set_alarm_enabled(False), self.close())).pack(side="right", padx=8)
        ttk.Button(bf, text="🏢 인사랑 열기", style="BigPlain.TButton",
                   command=lambda: self.close() if open_insarang(w, with_record=bool(app.alarm.get("open_record")), root=app.root) else None).pack(side="right", padx=(0, 8))
        w.bind("<Escape>", lambda e: self.close())
        w.bind("<Return>", lambda e: self.close())
        w.update_idletasks()
        ww = max(720, w.winfo_reqwidth())
        wh = max(340, w.winfo_reqheight())
        center_on(w, None, ww, wh)                     # 모니터 가운데
        if self.prev_grab is not None:
            try:
                w.grab_set()
            except tk.TclError:
                pass
        w.after(200, lambda: (w.lift(), w.focus_force()))

    def close(self):
        AlarmAudio.halt()                              # 읽던 음성·노래도 함께 멈춤
        try:
            self.win.grab_release()
        except tk.TclError:
            pass
        try:
            self.win.destroy()
        except tk.TclError:
            pass
        g = self.prev_grab
        if g is not None:
            try:
                if g.winfo_exists():
                    g.grab_set()              # 설정 창에 다시 넘겨줌
            except tk.TclError:
                pass


class AlarmDialog:
    """⏰ 알람·실행 설정 창"""

    def __init__(self, app, parent=None):
        self.app = app
        a, hk = dict(app.alarm), dict(app.hotkey)
        w = self.win = tk.Toplevel(parent or app.root)
        w.title("알람·실행 설정")
        w.transient(parent or app.root)
        w.resizable(False, False)
        b = ttk.Frame(w, padding=14)
        b.pack(fill="both", expand=True)
        bold = (FONT[0], fsz(10), "bold")

        ttk.Label(b, text="⏰ 알람", font=bold).grid(row=0, column=0, columnspan=4, sticky="w")
        self.en = tk.BooleanVar(value=a["enabled"])
        ttk.Checkbutton(b, text="알람 켜기", variable=self.en).grid(row=1, column=0, columnspan=4, sticky="w", pady=(4, 2))
        self.mode = tk.StringVar(value=a.get("mode", "schedule"))
        af = ttk.Frame(b)
        af.grid(row=2, column=0, columnspan=4, sticky="w")
        ttk.Radiobutton(af, text="평일·휴일 일정", value="schedule", variable=self.mode).grid(row=0, column=0, sticky="w")
        ttk.Label(af, text="   평일").grid(row=1, column=0, sticky="w", pady=2)
        self.wd_start = tk.StringVar(value=a.get("wd_start", "18:00"))
        ttk.Combobox(af, textvariable=self.wd_start, width=6,
                     values=[f"{h:02d}:00" for h in range(24)] + [f"{h:02d}:30" for h in range(24)]).grid(row=1, column=1, sticky="w")
        tf = ttk.Frame(af)
        tf.grid(row=1, column=2, columnspan=3, sticky="w")
        ttk.Label(tf, text="부터 다음날").pack(side="left", padx=(4, 4))
        self.wd_end = tk.StringVar(value=a.get("wd_end", "09:00"))
        ttk.Combobox(tf, textvariable=self.wd_end, width=6,
                     values=[f"{h:02d}:00" for h in range(24)] + [f"{h:02d}:30" for h in range(24)]).pack(side="left")
        ttk.Label(tf, text="까지").pack(side="left", padx=(4, 8))
        self.wd_every = tk.StringVar(value=str(a.get("wd_every", 60)))
        ttk.Spinbox(tf, from_=5, to=720, width=5, textvariable=self.wd_every).pack(side="left")
        ttk.Label(tf, text="분마다").pack(side="left", padx=4)
        ttk.Label(af, text="   휴일").grid(row=2, column=0, sticky="w", pady=2)
        ttk.Label(af, text="켠 순간부터").grid(row=2, column=1, columnspan=2, sticky="w")
        self.hd_every = tk.StringVar(value=str(a.get("hd_every", 60)))
        ttk.Spinbox(af, from_=5, to=720, width=5, textvariable=self.hd_every).grid(row=2, column=3, sticky="w")
        ttk.Label(af, text="분마다 (토·일·공휴일)").grid(row=2, column=4, sticky="w", padx=4)
        ttk.Label(af, text="   추가 휴일").grid(row=3, column=0, sticky="w", pady=2)
        self.extra = tk.StringVar(value=a.get("extra_holidays", ""))
        ttk.Entry(af, textvariable=self.extra, width=34).grid(row=3, column=1, columnspan=4, sticky="w")
        ttk.Label(af, text="      예: 2026-12-31, 2027-01-01 (공휴일·임시공휴일은 인터넷으로 자동 반영)",
                  foreground="#888").grid(row=4, column=0, columnspan=5, sticky="w")
        ttk.Radiobutton(af, text="단순 반복", value="interval", variable=self.mode).grid(row=5, column=0, sticky="w", pady=(6, 0))
        rf = ttk.Frame(af)
        rf.grid(row=5, column=1, columnspan=4, sticky="w", pady=(6, 0))
        ttk.Label(rf, text="켠 순간부터").pack(side="left")
        self.every = tk.StringVar(value=str(a.get("every", 60)))
        ttk.Spinbox(rf, from_=1, to=999, width=5, textvariable=self.every).pack(side="left", padx=4)
        self.unit = tk.StringVar(value=a.get("unit", "분"))
        ttk.Combobox(rf, textvariable=self.unit, values=["분", "시간"], state="readonly", width=5).pack(side="left")
        ttk.Label(rf, text="마다").pack(side="left", padx=4)
        ttk.Label(b, text="알림 글").grid(row=3, column=0, sticky="w", pady=(8, 0))
        self.msg = tk.StringVar(value=a["message"])
        ttk.Entry(b, textvariable=self.msg, width=40).grid(row=3, column=1, columnspan=3, sticky="w", pady=(8, 0))
        self.sound = tk.BooleanVar(value=a["sound"])
        ttk.Checkbutton(b, text="소리 내기", variable=self.sound).grid(row=4, column=1, columnspan=2, sticky="w", pady=(4, 0))
        ttk.Button(b, text="지금 시험해 보기", command=self.test).grid(row=4, column=3, sticky="e", pady=(4, 0))

        # 🔊 음성·노래로 알리기 (row 5)
        vf = ttk.LabelFrame(b, text=" 🔊 알림 방법 (음성·노래·인사랑) ", padding=(8, 4))
        vf.grid(row=5, column=0, columnspan=4, sticky="ew", pady=(8, 0))
        self.tts = tk.BooleanVar(value=a.get("tts", True))
        self.tts_rep = tk.StringVar(value=str(a.get("tts_repeat", 2)))
        self.song_on = tk.BooleanVar(value=a.get("song_on", False))
        self.song = tk.StringVar(value=a.get("song", ""))
        self.open_ins = tk.BooleanVar(value=a.get("open_insarang", False))
        self.open_rec = tk.BooleanVar(value=a.get("open_record", True))
        r1 = ttk.Frame(vf)
        r1.pack(fill="x")
        ttk.Checkbutton(r1, text="알림 글을 음성으로 읽어주기", variable=self.tts).pack(side="left")
        ttk.Label(r1, text="   반복").pack(side="left")
        ttk.Spinbox(r1, from_=1, to=9, width=3, textvariable=self.tts_rep).pack(side="left", padx=3)
        ttk.Label(r1, text="회").pack(side="left")
        r2 = ttk.Frame(vf)
        r2.pack(fill="x", pady=(4, 0))
        ttk.Checkbutton(r2, text="노래 파일 재생", variable=self.song_on).pack(side="left")
        ttk.Entry(r2, textvariable=self.song, width=30).pack(side="left", padx=(6, 4), fill="x", expand=True)
        ttk.Button(r2, text="찾기…", command=self.pick_song).pack(side="left")
        r3 = ttk.Frame(vf)
        r3.pack(fill="x", pady=(6, 0))
        ttk.Checkbutton(r3, text="🏢 알람이 울리면 인사랑도 함께 열기 (행정포털 로그인이 되어 있을 때)",
                        variable=self.open_ins).pack(anchor="w")
        ttk.Checkbutton(r3, text="   └ 인사랑이 열리면 '초과근무기록' 버튼을 눌러 팝업까지 띄우기 (🏢 인사랑 버튼에도 적용)",
                        variable=self.open_rec).pack(anchor="w")
        ttk.Label(vf, text="※ 팝업의 [확인]·[알람 끄기]를 누르면 음성과 노래가 멈춥니다. 노래는 끌 때까지 반복됩니다.\n"
                           "   mp3·wav·wma·m4a 파일을 쓸 수 있고, [지금 시험해 보기]로 미리 들어 볼 수 있습니다.",
                  foreground="#888").pack(fill="x", pady=(4, 0))

        ttk.Separator(b).grid(row=6, column=0, columnspan=4, sticky="ew", pady=10)
        ttk.Label(b, text="🚀 실행", font=bold).grid(row=7, column=0, columnspan=4, sticky="w")
        self.auto = tk.BooleanVar(value=autostart_enabled())
        ttk.Checkbutton(b, text="윈도우를 켜면 자동으로 실행 (트레이에 숨긴 채로 시작)", variable=self.auto).grid(
            row=8, column=0, columnspan=4, sticky="w", pady=(4, 0))
        self.tray = tk.BooleanVar(value=app.s.get("close_to_tray", True))
        txt = "닫기(X)를 누르면 끝내지 않고 트레이(시계 옆 아이콘)에 숨기기"
        cb = ttk.Checkbutton(b, text=txt, variable=self.tray)
        cb.grid(row=9, column=0, columnspan=4, sticky="w", pady=(2, 0))
        if not app.tray.ok:
            cb.state(["disabled"])
            ttk.Label(b, text="※ 트레이 기능을 쓰려면 pystray 패키지가 필요합니다", foreground="#b0412b").grid(
                row=10, column=0, columnspan=4, sticky="w")

        ttk.Separator(b).grid(row=11, column=0, columnspan=4, sticky="ew", pady=10)
        ttk.Label(b, text="⌨ 바로 실행 단축키 (어디서든 누르면 스마트탐색기가 앞으로 나옴)", font=bold).grid(
            row=12, column=0, columnspan=4, sticky="w")
        self.hk_en = tk.BooleanVar(value=hk.get("enabled", True))
        ttk.Checkbutton(b, text="사용", variable=self.hk_en).grid(row=13, column=0, sticky="w", pady=(4, 0))
        mf = ttk.Frame(b)
        mf.grid(row=13, column=1, columnspan=3, sticky="w", pady=(4, 0))
        self.mods = {}
        for k, n in (("ctrl", "Ctrl"), ("alt", "Alt"), ("shift", "Shift"), ("win", "Win")):
            self.mods[k] = tk.BooleanVar(value=hk.get(k, False))
            ttk.Checkbutton(mf, text=n, variable=self.mods[k]).pack(side="left", padx=(0, 4))
        ttk.Label(mf, text="+").pack(side="left", padx=4)
        self.key = tk.StringVar(value=hk.get("key", "E"))
        ttk.Combobox(mf, textvariable=self.key, values=HOTKEY_KEYS, state="readonly", width=6).pack(side="left")
        ttk.Button(b, text="바탕화면에 바로가기 만들기", command=self.shortcut).grid(
            row=14, column=0, columnspan=4, sticky="w", pady=(10, 0))

        self.status = ttk.Label(b, text="", foreground="#b0412b", wraplength=420)
        self.status.grid(row=15, column=0, columnspan=4, sticky="w", pady=(8, 0))
        bf = ttk.Frame(w, padding=(14, 0, 14, 12))
        bf.pack(fill="x")
        ttk.Button(bf, text="취소", command=w.destroy).pack(side="right")
        ttk.Button(bf, text="확인", style="Accent.TButton", command=self.ok).pack(side="right", padx=4)
        if app.hotkey_ctl.error:
            self.status.configure(text=app.hotkey_ctl.error)
        center_on(w, app.root)
        w.grab_set()

    def _alarm(self):
        def num(var, lo, hi, d):
            try:
                return max(lo, min(hi, int(var.get())))
            except ValueError:
                return d
        h, m = _parse_hm(self.wd_start.get())
        eh, em = _parse_hm(self.wd_end.get(), (9, 0))
        return {"enabled": self.en.get(), "mode": self.mode.get(),
                "wd_start": f"{h:02d}:{m:02d}", "wd_end": f"{eh:02d}:{em:02d}",
                "wd_every": num(self.wd_every, 5, 720, 60),
                "hd_every": num(self.hd_every, 5, 720, 60),
                "every": num(self.every, 1, 999, 60), "unit": self.unit.get() or "분",
                "message": self.msg.get().strip(), "sound": self.sound.get(),
                "tts": self.tts.get(), "tts_repeat": num(self.tts_rep, 1, 9, 2),
                "song_on": self.song_on.get(), "song": self.song.get().strip(),
                "open_insarang": self.open_ins.get(), "open_record": self.open_rec.get(),
                "extra_holidays": self.extra.get().strip()}

    def pick_song(self):
        p = filedialog.askopenfilename(
            parent=self.win, title="알람으로 쓸 노래 파일",
            filetypes=[("음악 파일", "*.mp3 *.wav *.wma *.m4a *.aac"), ("모든 파일", "*.*")])
        if p:
            self.song.set(os.path.normpath(p))
            self.song_on.set(True)

    def test(self):
        a = self._alarm()
        if a["sound"]:
            play_alarm_sound()
        AlarmPopup(self.app, a["message"])
        alarm_extras(self.app, a, lambda m: messagebox.showwarning(APP_NAME, m, parent=self.win),
                     quiet_insarang=False)

    def shortcut(self):
        try:
            make_desktop_shortcut()
            self.status.configure(text="바탕화면에 '스마트탐색기' 바로가기를 만들었습니다.", foreground="#2f7a3a")
        except Exception as e:
            self.status.configure(text=f"바로가기를 만들지 못했습니다: {e}", foreground="#b0412b")

    def ok(self):
        app = self.app
        hk = {k: v.get() for k, v in self.mods.items()}
        hk.update(key=self.key.get() or "E", enabled=self.hk_en.get())
        if hk["enabled"] and not any(hk[k] for k in self.MODS_KEYS):
            self.status.configure(text="단축키는 Ctrl·Alt·Shift·Win 중 하나 이상과 함께 정해 주세요.")
            return
        try:
            set_autostart(self.auto.get())
        except Exception as e:
            self.status.configure(text=f"자동 실행을 설정하지 못했습니다: {e}")
            return
        app.s["close_to_tray"] = self.tray.get()
        app.set_alarm(self._alarm())
        app.set_hotkey(hk)
        if app.hotkey_ctl.error:
            self.status.configure(text=app.hotkey_ctl.error + " — 다른 조합을 골라 주세요.")
            return
        self.win.destroy()

    MODS_KEYS = ("ctrl", "alt", "shift", "win")


# ───────────── 쉬는 동안 색인 (문서 내용을 미리 읽어 두기) ─────────────
DEFAULT_INDEX = {"enabled": True, "folders": [], "idle_min": 3, "every_hours": 2, "ocr": True, "on_start": True}
INDEX_SKIP_EXTS = set(IMAGE_EXTS)              # 글자 인식을 끄면 그림은 색인에서 뺌


def user_idle_seconds():
    """키보드·마우스를 마지막으로 쓴 뒤 지난 시간(초)"""
    if sys.platform != "win32":
        return 10 ** 9
    try:
        import ctypes
        from ctypes import wintypes

        class LASTINPUTINFO(ctypes.Structure):
            _fields_ = [("cbSize", wintypes.UINT), ("dwTime", wintypes.DWORD)]
        li = LASTINPUTINFO()
        li.cbSize = ctypes.sizeof(li)
        if not ctypes.windll.user32.GetLastInputInfo(ctypes.byref(li)):
            return 0
        return ((ctypes.windll.kernel32.GetTickCount() - li.dwTime) & 0xFFFFFFFF) / 1000.0
    except Exception:
        return 0


def default_index_folders():
    """바탕화면 · 문서 · 다운로드"""
    out = []
    if sys.platform == "win32":
        try:
            import ctypes
            for csidl in (0x10, 0x05):              # 바탕화면, 문서
                buf = ctypes.create_unicode_buffer(260)
                if ctypes.windll.shell32.SHGetFolderPathW(None, csidl, None, 0, buf) == 0:
                    out.append(buf.value)
        except Exception:
            pass
    home = os.path.expanduser("~")
    for name in ("Desktop", "Documents", "Downloads"):
        p = os.path.join(home, name)
        if os.path.isdir(p) and os.path.normcase(p) not in {os.path.normcase(x) for x in out}:
            out.append(p)
    return [p for p in out if os.path.isdir(p)]


class IdleIndexer:
    """PC를 쓰지 않는 동안 정해 둔 폴더의 문서 내용을 미리 읽어 저장해 둠.
    키보드·마우스를 만지면 바로 멈췄다가, 다시 쉬면 이어서 함. 검색할 때는 저장된 내용을 바로 씀."""

    def __init__(self, app):
        self.app = app
        if not app.s.get("index_ocr_v109"):          # 1.0.9부터 스캔 PDF·그림 글자 인식도 미리 색인 (한 번만 켜 줌)
            app.s["index"] = dict(app.s.get("index", {}), ocr=True)
            app.s["index_ocr_v109"] = True
        self.cfg = dict(DEFAULT_INDEX, **app.s.get("index", {}))
        self.state = "대기"          # 대기 · 색인 중 · 잠시 멈춤 · 완료
        self.done = 0
        self.total = 0
        self.read = 0                # 이번에 새로 읽은 문서 수
        self.last_finish = app.s.get("index_last", 0)
        self.force = threading.Event()
        self.stop_flag = threading.Event()
        self.thread = threading.Thread(target=self._loop, daemon=True)
        self.thread.start()

    def folders(self):
        """설정한 폴더 + 칸에 📌 고정해 둔 폴더 (중복·하위 폴더 정리)"""
        fs = list(self.cfg.get("folders") or []) or default_index_folders()
        fs += list(getattr(self.app, "pinned_folders", []))   # 화면 쪽에서 정리해 둔 목록 (스레드에서 화면을 직접 건드리지 않음)
        out = []
        for f in sorted({os.path.normpath(f) for f in fs if f and os.path.isdir(f)}, key=len):
            if not any(is_inside(f, o) for o in out):
                out.append(f)
        return out

    def run_now(self):
        self.force.set()

    def stop(self):
        self.stop_flag.set()
        self.force.set()

    def _busy(self):
        """사용자가 PC를 쓰고 있거나 검색 중이면 색인을 쉼"""
        if self.force_mode:
            return any(p.busy() for p in self.app.panes)
        if user_idle_seconds() < max(1, self.cfg.get("idle_min", 3)) * 60:
            return True
        return any(p.busy() for p in self.app.panes)

    def _wait_idle(self):
        while not self.stop_flag.is_set():
            if not self._busy():
                return True
            self.state = "잠시 멈춤"
            self.stop_flag.wait(5)
        return False

    def _loop(self):
        self.force_mode = False
        self.force.wait(4)                         # 화면이 뜬 뒤 잠깐만 기다렸다가 시작 ('지금 색인'이면 바로)
        # 프로그램을 켜면 바로 한 번 색인 (윈도우 시작 때 트레이로 자동 실행된 경우는 PC를 쉴 때까지 기다림)
        startup = bool(self.cfg.get("enabled", True) and self.cfg.get("on_start", True)) and "--tray" not in sys.argv
        while not self.stop_flag.is_set():
            due = time.time() - self.last_finish >= max(0.25, self.cfg.get("every_hours", 2)) * 3600
            if self.force.is_set() or startup or (self.cfg.get("enabled", True) and due and not self._busy()):
                self.force_mode = self.force.is_set() or startup
                startup = False
                self.force.clear()
                try:
                    self._pass()
                except Exception:
                    pass
                self.force_mode = False
            else:
                self.state = "대기" if self.state != "완료" else "완료"
                self.force.wait(30)

    def _pass(self):
        """1단계: 본문 글자를 빠르게 모두 읽어 둠 → 2단계: 스캔 PDF·그림을 글자 인식(OCR)"""
        cache = self.app.cache
        folders = self.folders()
        want_ocr = bool(self.cfg.get("ocr"))
        ocr = want_ocr and ocr_engine() is not None
        if want_ocr and _ocr["no_korean"]:
            self.app.bgq.put(("ocr_missing", None))   # 화면 쪽에서 설치 안내 창 (하루 한 번까지)
        skip = set() if ocr else INDEX_SKIP_EXTS
        self.phase = "본문"
        self.state, self.done, self.total, self.read = "목록 만드는 중", 0, 0, 0
        files = []
        seen = {f: set() for f in folders}
        for f in folders:
            for path, name, mtime, size in iter_entries(f, True):   # 목록과 함께 오는 크기·시각을 씀 (빠름)
                if self.stop_flag.is_set():
                    return
                seen[f].add(cache.key(path))          # 있는 파일은 모두 기억 (지워진 것만 정리하려고)
                ext = os.path.splitext(name)[1].lower()
                if ext in KNOWN_EXTS and ext not in skip and not name.startswith("~$") \
                        and size <= (MAX_ARCHIVE_SIZE if ext in ARCHIVE_EXTS else MAX_FILE_SIZE):
                    files.append((path, mtime, size))
        self.total = len(files)
        sigs = cache.sigs_many(cache.key(p) for p, _, _ in files)
        need_ocr = []

        def read_one(path, mtime, size, use_ocr):
            try:
                text, pend = extract_text(path, use_ocr, None, self.stop_flag)
                err = ""
            except StopSearch:
                return None
            except Exception as e:
                text, pend, err = "", False, str(e)[:200]
            cache.put(path, mtime, size, text, err, pend)
            self.read += 1
            if self.read % 20 == 0:
                cache.commit()
            time.sleep(0.01)                       # 다른 일에 양보
            return pend

        for i, (path, mtime, size) in enumerate(files):
            if not self._wait_idle():
                return
            self.state = "색인 중"
            self.done = i
            sig = sigs.get(cache.key(path))
            if sig and sig[0] == mtime and sig[1] == size:   # 내용이 그대로면 다시 읽지 않음
                pend = bool(sig[2])
            else:
                pend = read_one(path, mtime, size, False)   # 글자 인식은 뒤로 미루고 본문부터 빠르게
                if pend is None:
                    return
            if pend and ocr:
                need_ocr.append((path, mtime, size))
        cache.commit()
        if ocr and need_ocr:                       # 2단계: 스캔 PDF·그림 글자 인식
            self.phase = "글자 인식"
            self.done, self.total = 0, len(need_ocr)
            for i, (path, mtime, size) in enumerate(need_ocr):
                if not self._wait_idle():
                    return
                self.state = "색인 중"
                self.done = i
                if read_one(path, mtime, size, True) is None:
                    return
            cache.commit()
        for f in folders:                          # 지워진 파일 기록 정리
            cache.forget_missing(f, seen[f])
        self.phase = "본문"
        self.done = self.total
        self.state = "완료"
        self.last_finish = time.time()
        self.app.bgq.put(("index_done", self.last_finish))

    def summary(self):
        if self.state in ("색인 중", "잠시 멈춤") and self.total:
            pct = int(self.done * 100 / self.total)
            what = "글자 인식" if getattr(self, "phase", "본문") == "글자 인식" else "색인"
            return f"🗂 {what} {pct}%" + (" (쉬는 동안 이어서)" if self.state == "잠시 멈춤" else "")
        if self.state == "목록 만드는 중":
            return "🗂 색인 준비 중"
        if self.last_finish:
            mins = int((time.time() - self.last_finish) // 60)
            ago = "방금" if mins < 1 else (f"{mins}분 전" if mins < 60 else f"{mins // 60}시간 전")
            return f"🗂 색인 완료 · {ago}"
        return "🗂 색인 전" if self.cfg.get("enabled", True) else ""


OCR_CAPABILITY = "Language.OCR~~~ko-KR~0.0.1.0"


class OcrInstallDialog:
    """한국어 OCR(윈도우 기본 기능) 설치 안내"""

    def __init__(self, app):
        self.app = app
        w = self.win = tk.Toplevel(app.root)
        w.title("한국어 글자 인식(OCR) 설치 안내")
        w.transient(app.root)
        w.resizable(False, False)
        w.protocol("WM_DELETE_WINDOW", self.close)
        b = ttk.Frame(w, padding=16)
        b.pack(fill="both", expand=True)
        ttk.Label(b, text="🔤 이 PC에는 한국어 글자 인식(OCR)이 없습니다",
                  font=(FONT[0], fsz(12), "bold")).pack(anchor="w")
        ttk.Label(b, justify="left", text=(
            "스캔한 PDF나 사진 속 글자를 검색하려면 윈도우의 '한국어 OCR' 기능이 필요합니다.\n"
            "(무료, 윈도우에 들어 있는 기능이며 용량은 수 MB 정도입니다)\n\n"
            "[지금 설치]를 누르면 관리자 권한 확인 창이 뜹니다. '예'를 누르면 검은 창에서\n"
            "1~2분 정도 설치가 진행되고, 끝나면 스마트탐색기가 알아서 글자 인식을 시작합니다.\n\n"
            "※ 회사·기관 PC라서 관리자 권한이 없으면 전산 담당자에게 아래 명령 실행을 요청하세요.")
        ).pack(anchor="w", pady=(8, 4))
        cmd = ttk.Entry(b, width=70)
        cmd.insert(0, f"Add-WindowsCapability -Online -Name {OCR_CAPABILITY}")
        cmd.configure(state="readonly")
        cmd.pack(anchor="w", fill="x")
        ttk.Label(b, text="글자 인식 없이도 파일명·일반 문서 본문 검색은 그대로 됩니다.",
                  foreground="#777").pack(anchor="w", pady=(8, 0))
        self.msg = ttk.Label(b, text="", foreground="#2a6fdb")
        self.msg.pack(anchor="w", pady=(6, 0))
        bf = ttk.Frame(w, padding=(16, 0, 16, 14))
        bf.pack(fill="x")
        self.never = tk.BooleanVar(value=False)
        ttk.Checkbutton(bf, text="다시 보지 않기", variable=self.never).pack(side="left")
        ttk.Button(bf, text="닫기", command=self.close).pack(side="right")
        self.install_btn = ttk.Button(bf, text="지금 설치", style="Accent.TButton", command=self.install)
        self.install_btn.pack(side="right", padx=4)
        center_on(w, app.root)
        w.lift()
        w.focus_force()

    def install(self):
        script = (f"Write-Host '한국어 OCR 설치 중... (1~2분)'; "
                  f"Add-WindowsCapability -Online -Name {OCR_CAPABILITY}; "
                  f"Write-Host '끝났습니다. 이 창은 5초 뒤 닫힙니다.'; Start-Sleep 5")
        enc = base64.b64encode(script.encode("utf-16-le")).decode()
        try:
            import ctypes
            r = ctypes.windll.shell32.ShellExecuteW(None, "runas", "powershell.exe",
                                                    f"-NoProfile -ExecutionPolicy Bypass -EncodedCommand {enc}", None, 1)
        except Exception:
            r = 0
        if r <= 32:
            self.msg.configure(text="설치를 시작하지 못했습니다 (관리자 권한 거부). 위 명령을 전산 담당자에게 요청하세요.",
                               foreground="#b0412b")
            return
        self.install_btn.configure(state="disabled")
        self.msg.configure(text="설치 중입니다… 끝나면 자동으로 알려 드립니다.", foreground="#2a6fdb")
        self.tries = 0
        self.win.after(15000, self.check)

    def check(self):
        """설치가 끝났는지 15초마다 확인 (최대 20분)"""
        self.tries += 1
        ocr_engine(recheck=True)
        if not _ocr["no_korean"] and _ocr["engine"] is not None:
            try:
                self.msg.configure(text="✅ 설치 완료! 쉬는 동안 스캔 PDF·그림 글자 인식을 시작합니다.", foreground="#1f7a3a")
                self.install_btn.configure(state="disabled")
            except tk.TclError:
                pass
            self.app.indexer.run_now()
            return
        if self.tries < 80:
            self.app.root.after(15000, self.check)
        else:
            try:
                self.install_btn.configure(state="normal")
                self.msg.configure(text="아직 설치가 확인되지 않습니다. PC를 다시 시작한 뒤 확인해 주세요.", foreground="#b0412b")
            except tk.TclError:
                pass

    def close(self):
        if self.never.get():
            self.app.s["ocr_nag_off"] = True
            self.app.schedule_save()
        self.app._ocr_dlg = None
        self.win.destroy()


class IndexDialog:
    """🗂 색인 설정 창"""

    def __init__(self, app, parent=None):
        self.app = app
        ix = app.indexer
        c = dict(ix.cfg)
        w = self.win = tk.Toplevel(parent or app.root)
        w.title("색인 설정")
        w.transient(parent or app.root)
        b = ttk.Frame(w, padding=14)
        b.pack(fill="both", expand=True)
        bold = (FONT[0], fsz(10), "bold")
        ttk.Label(b, text="🗂 쉬는 동안 색인", font=bold).grid(row=0, column=0, columnspan=3, sticky="w")
        ttk.Label(b, text="PC를 쓰지 않는 동안 아래 폴더의 문서 내용을 미리 읽어 두면, 검색할 때 바로 찾습니다.\n"
                          "프로그램을 켜면 바로 한 번 시작하고, 이후에는 키보드·마우스를 만지면 곧바로 멈췄다가 다시 쉬면 이어서 합니다.",
                  foreground="#666").grid(row=1, column=0, columnspan=3, sticky="w", pady=(2, 8))
        self.en = tk.BooleanVar(value=c.get("enabled", True))
        ttk.Checkbutton(b, text="쉬는 동안 자동으로 색인", variable=self.en).grid(row=2, column=0, columnspan=3, sticky="w")
        rf = ttk.Frame(b)
        rf.grid(row=3, column=0, columnspan=3, sticky="w", pady=(4, 0))
        ttk.Label(rf, text="키보드·마우스를").pack(side="left")
        self.idle = tk.StringVar(value=str(c.get("idle_min", 3)))
        ttk.Spinbox(rf, from_=1, to=60, width=4, textvariable=self.idle).pack(side="left", padx=4)
        ttk.Label(rf, text="분 이상 안 쓰면 시작,").pack(side="left")
        self.every = tk.StringVar(value=str(c.get("every_hours", 2)))
        ttk.Spinbox(rf, from_=1, to=48, width=4, textvariable=self.every).pack(side="left", padx=4)
        ttk.Label(rf, text="시간마다 새로 바뀐 파일 확인").pack(side="left")
        self.ocr = tk.BooleanVar(value=c.get("ocr", True))
        of = ttk.Frame(b)
        of.grid(row=4, column=0, columnspan=3, sticky="w", pady=(4, 0))
        of1 = ttk.Frame(of)
        of1.pack(anchor="w")
        ttk.Checkbutton(of1, text="스캔 PDF·그림 글자도 미리 인식해서 색인 (본문을 다 읽은 뒤 천천히)", variable=self.ocr).pack(side="left")
        ocr_engine()
        if _ocr["no_korean"]:
            ttk.Button(of1, text="⚠ 한국어 OCR 설치…", command=lambda: app.ocr_missing(force=True)).pack(side="left", padx=(6, 0))
        self.on_start = tk.BooleanVar(value=c.get("on_start", True))
        ttk.Checkbutton(of, text="프로그램을 켜면 바로 색인 시작 (이후에는 PC를 쉬는 동안 자동으로 이어서)",
                        variable=self.on_start).pack(anchor="w", pady=(2, 0))

        ttk.Label(b, text="색인할 폴더", font=bold).grid(row=5, column=0, columnspan=3, sticky="w", pady=(10, 2))
        lf = ttk.Frame(b)
        lf.grid(row=6, column=0, columnspan=2, sticky="nsew")
        self.lb = tk.Listbox(lf, height=7, width=62, activestyle="none")
        self.lb.pack(side="left", fill="both", expand=True)
        sb = ttk.Scrollbar(lf, orient="vertical", command=self.lb.yview)
        sb.pack(side="right", fill="y")
        self.lb.configure(yscrollcommand=sb.set)
        for f in (c.get("folders") or default_index_folders()):
            self.lb.insert("end", f)
        bf = ttk.Frame(b)
        bf.grid(row=6, column=2, sticky="n", padx=(6, 0))
        ttk.Button(bf, text="추가…", command=self.add).pack(fill="x")
        ttk.Button(bf, text="빼기", command=self.remove).pack(fill="x", pady=(4, 0))
        ttk.Label(b, text="📌 고정해 둔 폴더는 자동으로 함께 색인합니다.", foreground="#888").grid(
            row=7, column=0, columnspan=3, sticky="w", pady=(4, 0))

        self.status = ttk.Label(b, text="", foreground="#2a6fdb")
        self.status.grid(row=8, column=0, columnspan=3, sticky="w", pady=(10, 0))
        btn = ttk.Frame(w, padding=(14, 0, 14, 12))
        btn.pack(fill="x")
        ttk.Button(btn, text="지금 색인 시작", command=self.now).pack(side="left")
        ttk.Button(btn, text="취소", command=w.destroy).pack(side="right")
        ttk.Button(btn, text="확인", style="Accent.TButton", command=self.ok).pack(side="right", padx=4)
        self._tick()
        center_on(w, parent or app.root)
        w.grab_set()

    def _tick(self):
        try:
            ix = self.app.indexer
            txt = ix.summary() or "색인 꺼짐"
            if ix.state in ("색인 중", "잠시 멈춤"):
                txt += f"  —  {ix.done:,} / {ix.total:,}개 확인, 새로 읽음 {ix.read:,}개"
            txt += f"   ·   저장된 문서 {self.app.cache.count():,}개"
            self.status.configure(text=txt)
            self.win.after(1000, self._tick)
        except tk.TclError:
            pass

    def add(self):
        d = filedialog.askdirectory(parent=self.win, title="색인할 폴더 고르기")
        if d:
            d = os.path.normpath(d)
            if d not in self.lb.get(0, "end"):
                self.lb.insert("end", d)

    def remove(self):
        for i in reversed(self.lb.curselection()):
            self.lb.delete(i)

    def _save(self):
        def num(v, lo, hi, d):
            try:
                return max(lo, min(hi, int(v.get())))
            except ValueError:
                return d
        cfg = {"enabled": self.en.get(), "folders": list(self.lb.get(0, "end")),
               "idle_min": num(self.idle, 1, 60, 3), "every_hours": num(self.every, 1, 48, 2), "ocr": self.ocr.get(),
               "on_start": self.on_start.get()}
        self.app.indexer.cfg = dict(DEFAULT_INDEX, **cfg)
        self.app.s["index"] = cfg
        self.app.schedule_save()

    def now(self):
        self._save()
        self.app.indexer.run_now()
        self.status.configure(text="색인을 시작합니다… (검색 중에는 잠시 멈춥니다)")

    def ok(self):
        self._save()
        self.win.destroy()


CONTACT_EMAIL = "smartgongmaster@gmail.com"   # 오류·개선 제안 받는 주소
INTRO_LINE = "파일명 + 본문 내용까지 검색  ·  PDF·엑셀·PPT·워드·이미지·압축파일 미리보기 (한글은 1쪽 미리보기)"
GUIDE = [
    ("스마트탐색기  v" + APP_VERSION, "화면을 여러 칸으로 나눠 쓰는 탐색기에, 파일 이름은 물론 문서 안의 내용까지 찾아 주는 검색 기능을 더한 프로그램입니다."),
    ("🔍 파일명 검색 · 📄 본문 추가 검색",
     "검색어 칸에 찾을 말을 넣고 버튼을 고르세요. Enter는 마지막에 누른 버튼과 같게 검색합니다.\n"
     "· [🔍 파일명 검색] 파일·폴더 이름만 찾습니다. 문서를 열지 않아 아주 빠릅니다.\n"
     "· [📄 본문 추가 검색] 파일 이름 + 문서 안의 내용까지 찾습니다.\n"
     "· 한글(HWP·HWPX), 워드, 엑셀, 파워포인트, PDF, 텍스트, 메일(EML), 압축파일 속 문서까지 내용으로 찾습니다.\n"
     "· 여러 단어를 띄어 쓰면 모두 들어 있는 파일, \"따옴표\"로 묶으면 그 구절 그대로 찾습니다.\n"
     "· '띄어쓰기 무시'가 켜져 있으면 '예산집행'으로 '예산 집행'도 찾습니다.\n"
     "· 옵션에서 스캔 PDF·이미지 글자 인식, 파일 종류 선택, 하위 폴더 포함 여부를 정할 수 있습니다.\n"
     "· 쉬는 동안 바탕화면·문서·다운로드(와 📌 고정 폴더)의 본문, 스캔 PDF·그림 글자까지 미리 읽어 두어(색인) 검색이 빠릅니다.\n"
     "· 검색어를 지우거나 Esc를 누르면 다시 폴더 보기로 돌아옵니다."),
    ("👁 미리보기",
     "· PDF, 엑셀, 파워포인트, 워드, 이미지, 압축파일 내용을 바로 볼 수 있습니다.\n"
     "· PDF·이미지는 가로 맞춤 / 세로 맞춤 / 확대·축소(Ctrl+휠).\n"
     "· 엑셀·CSV는 표로, 압축파일은 안의 파일 목록과 각 파일 미리보기로 보여 줍니다.\n"
     "· 한글(HWP·HWPX) 파일은 1쪽 미리보기를 지원합니다.\n"
     "· '일치한 문장' 탭에서 검색어가 들어 있는 부분만 모아 볼 수 있습니다."),
    ("📌 폴더 고정",
     "칸마다 자주 쓰는 폴더를 고정해 두면, 그 칸은 늘 그 폴더에서 검색합니다. 프로그램을 껐다 켜도 유지됩니다."),
    ("🪟 화면 분할",
     "위쪽에서 가로×세로 칸 수(최대 4×4)를 고르세요. 칸 사이 경계선이나 파란 손잡이를 끌어 크기를 조절하고, "
     "경계선을 더블클릭하면 같은 크기로 돌아갑니다."),
    ("◧ 미리보기 위치",
     "칸이 1개일 때는 미리보기가 목록 오른쪽에 나오고, 칸을 2개 이상으로 나누면 목록 아래로 옵니다.\n"
     "목록과 미리보기 사이 경계를 끌어 크기를 조절하면 오른쪽·아래 각각 따로 기억합니다."),
    ("🗂 쉬는 동안 색인",
     "PC를 몇 분 동안 쓰지 않으면 바탕화면·문서·다운로드와 📌 고정한 폴더의 문서 내용을 미리 읽어 둡니다. "
     "그러면 처음 검색할 때도 바로 찾습니다. 프로그램을 켜면 바로 한 번 시작하고(검색 중에는 잠시 멈춤), 그 뒤로는 PC를 쉬는 동안 자동으로 이어 가며 키보드·마우스를 만지면 곧바로 멈춥니다. "
     "[⚙ 환경설정] → [🗂 색인 설정]에서 폴더와 시간을 바꾸거나 '지금 색인 시작'을 누를 수 있습니다."),
    ("ℹ 사용 집계 안내",
     "프로그램 개선을 위해 하루 한 번, 이 PC에 설치된 프로그램을 구분하는 무작위 번호와 버전만 smartgong.kr 쪽으로 보냅니다. "
     "이름·PC 정보·파일 이름이나 내용은 보내지 않습니다."),
    ("⏰ 반복 알람 · 실행 설정",
     "· [⚙ 환경설정] → [⏰ 알람·실행 설정]에서 '1시간마다'처럼 간격과 알림 글을 정하면, 프로그램이 켜져 있는 동안 계속 반복해서 알려 줍니다.\n"
     "· 윈도우를 켜면 자동 실행(트레이에 숨긴 채 시작), 닫기(X)를 눌러도 트레이에서 계속 실행되게 할 수 있습니다.\n"
     "· 바로 실행 단축키(기본 Ctrl+Alt+E)를 누르면 어디서든 스마트탐색기가 앞으로 나옵니다.\n"
     "· 트레이 아이콘을 오른쪽 클릭하면 열기 · 알람 켜기/끄기 · 끝내기를 할 수 있습니다."),
    ("📁 탐색기 기능",
     "· 폴더 더블클릭으로 들어가기, ⬆ 또는 Backspace로 위로, ◀ 뒤로\n"
     "· 복사 Ctrl+C · 잘라내기 Ctrl+X · 붙여넣기 Ctrl+V (윈도우 탐색기와 서로 주고받기 가능)\n"
     "· 이름 바꾸기 F2 · 휴지통으로 삭제 Del · 새 폴더 Ctrl+Shift+N\n"
     "· 끌어서 옮기기 — 다른 칸은 물론 윈도우 탐색기·바탕화면·다른 프로그램과도 주고받습니다.\n"
     "   끄는 동안 탐색기처럼 파일 그림과 '이동/복사' 표시가 따라다니고, 놓을 폴더는 파랗게 표시됩니다.\n"
     "   같은 드라이브는 이동, 다른 드라이브는 복사 (Ctrl = 복사, Shift = 이동)\n"
     "· 오른쪽 클릭 → 맨 위 「Windows 메뉴」(또는 Shift+오른쪽 클릭): 속성·압축·보내기·연결 프로그램·바로 가기 만들기 등\n"
     "   윈도우 탐색기의 메뉴가 그대로 나옵니다. 빈 곳에서 열면 '새로 만들기' 메뉴도 쓸 수 있습니다."),
]
SMARTGONG_LOGO_PNG = "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"


def smartgong_logo(widget, height=26):
    """스마트공 로고 그림 (화면 배율에 맞춰 크기 조절). 못 만들면 None"""
    try:
        try:
            dpi = widget.winfo_fpixels("1i") / 96
        except Exception:
            dpi = 1.0
        h = max(16, int(height * dpi))
        if Image is not None:
            from PIL import ImageTk
            im = Image.open(io.BytesIO(base64.b64decode(SMARTGONG_LOGO_PNG))).convert("RGBA")
            w = max(1, round(im.width * h / im.height))
            return ImageTk.PhotoImage(im.resize((w, h), Image.LANCZOS))
        return tk.PhotoImage(data=SMARTGONG_LOGO_PNG)
    except Exception:
        return None


ICON_PNG_64 = "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"
ICON_PNG_32 = "iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAGCElEQVR42r2Xe2zWVxnHP8/5nV/fW1sKk0oZtJIigsXWMInTweLMCGYML0ixiQKSZds/mrm5OGOcpfMSLwszzmyJ4mVuQSkbE7OByXSuW5CZ4TTTZhHHsskwAwPSy/v2vZxzHv94S+nbvn2BsXmS88/vd855Lt/n+1xg0tLeXsNbvKbKkMk/pK8v9HcTfaLnwx8Nzq8NSqv6YHXywQsVNH5HrHHWcAzDE/YFfi19A+6srAkFtBcjfYTRX13VlbDxThub9yFAeJPMHrfZFcNfi1m9MbN14PBZJUS114j0hUL/1e8RYwbiSGbncs5N9dCleh4gnbLWBR0Ozl+T6Hnmee3vjkR7May/IsofyTyXTEVduZwviRC/JfgrpXQ6ivNj7sVkwazgswMFI32Ewkv165L1cVcu59yEcDFnUZy+Rcb/X9wSIc7mnEvW1y0bS/FxEdQABNV1oFrhsVIWQrHKLoErgBt7QwiJAKoqQa8DsOPyFhImzIPgiFd8DjNvJWiYYq1CcLjBB/HHD4JNl8/UXOGcfYoQVBQWTlKg7AlEIBSR9NuxHVtqPhkt2YB7aR/UzQL1M9lblhglwCYqnCzj3LDV70VQyoFNTmJ0JcNNUzuJa3aAsZXoTfG3lrK4I4+iZ46W35uirJ1OFgFfKB8UU0WB8bfTzUTt10+/XuV0NP8D5B/fDL407a+Z5jEUohhMPOXZarwKaPAEX5q4LgDBE3wR1IF6JDMPSTeXA1ikhgemZ+hpOlbIF1NmJBEjQ6c4efwV0vWNtLS+E0OEBo+YqCx4BphsLesA3JFHKf3lXiRuBPyEgqpKbC05yfDA06c4dPBp1OdRhZa2Dm64YwfLV16LqiI16GprExbM7Hbs4o9BNDmKFUUo5ofYfud2/usT3PylW2lfspSR0WEe37WLr2xdw/Yf/YYVq9YTvH8DCoxrbeZ2Yi7rqKhM3nuiOGbPfXdxIp/g/v5dNM6/HHKjYC3L3r+azJ138MOvbeP+/a9Sl0jOGEs1IChr7QZ/QfHQNyDRNPFNAKKYgYf+xCe33Ejj/Msp/ecENo4JY2OYVIlP33QzAwcOMHj4KVasWkcIvioQNSAoB1+0aC2JWe8AsWXXqxKZiOzIafJmIwva2gilApG1iAiRtVByNDTOomlOAydee7kmmc4LgcQZJD1vIiYE0OBJv205qYZm/v3qUUx8PSV3BoljgveYZJKR06cZHhplbktbRUxdPAT/eJjCoW8i4xCIRPjcKepX3cpV67byyAPfYc2GT5FpbobsKFEqBYl6Hv7+DmycoeuDa1ENM8k/PwR26SbMgtWVuUE9Wt/CxkXK80/u5Qs9PWy7/TbaFy9heGSY/bt/ycHf/4E4rmP3fV/lM7d8D5GIUCUXnCcRKdg0pqm9aouTjuHrP32SH3/r8/yg9y7EKN555re9i6Y5cxgZOsPen9xNcAW2dCbJDYFOUWLmWmDsRDWbnt3LyUWBhqZmbvvubs6cep3Xj71Cur6e1sXLGfzzU3z7lvVEUYF9D92Lv7KVbWvaGcu7GrUAhagOzZ2k9LeflyticFW2h+CQ4FBfIrgCTZfNY+l7r6R18XLUF+m44kN8+Z69iM2QSid57Lnj/Ox3R4ljU8EIC2BEQkUKtkncCzvxL++fVMelZs+pWt4iIGIIIdDR0MjtG5dx9+7DpBMR+549RktTio+sbsWPuXAOAsNrGLSCrXEazZ28gG6nauQgwOiQp2thhi9u6OCefS8CkEgYxYiienxSDJgDwA3TipGJL6kxjyxkxzxdi2bT29PJ8FiJZQsaoejFWDkAYLUXQ2PysfxQbjCdth2VbbnWbAcuaCYxQq7gaG3OIIgzETafLf4zFZX2qiKGjm6R635bMJbNzutwOhXFQdUp6lTVvxlbwOeLzhmj1qvmgkabZdOzY+zpNjJ5Lsw+ePXKupTZaeuiTlQhXKL5E24ozxK+5AezWX/TrC3P/PHsRHZuOB3/8Pfed9ct7Zy7Qb2s9V7bVDUSGe8rLq7/L5NCxEcx/xKRJ44N6yOLtg3k+/u7o02b9vgqo9P/YTyfIuN/WrL8lwst6mIAAAAASUVORK5CYII="


def set_window_icon(root):
    try:
        icons = [tk.PhotoImage(data=ICON_PNG_64), tk.PhotoImage(data=ICON_PNG_32)]
        root.iconphoto(True, *icons)
        root._icons = icons
    except Exception:
        pass
    if sys.platform == "win32":
        try:                                    # 작업 표시줄에 파이썬 아이콘 대신 이 프로그램 아이콘이 나오게
            import ctypes
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("SmartGong.SmartExplorer")
        except Exception:
            pass


def load_settings():
    try:
        with open(SETTINGS_FILE, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


class App:
    ole_target = None          # 끌어 온 파일 받는 곳 (윈도우)
    drag_source = None
    _drop_hl = None
    _ole_req = _ole_drop_req = _ole_state = None
    MAX_SPLIT = 4

    def __init__(self, root, instance=None):
        self.root = root
        self.s = load_settings()
        self.bgq = queue.Queue()                       # 트레이·단축키·두 번째 실행에서 온 요청
        install_ime_fix(root)                          # 한글 입력이 칸 안에서 같은 크기로 자연스럽게
        saved = self.s.get("alarm", {})
        self.alarm = dict(DEFAULT_ALARM, **saved) if "mode" in saved else dict(DEFAULT_ALARM)   # 예전 형식이면 새 기본값
        self.started = time.time()                    # 휴일 알람 기준: 프로그램을 켠 순간
        saved_hk = self.s.get("hotkey", {})
        if not self.s.get("hotkey_v2"):                  # 예전 기본값(Ctrl+Alt+E) 그대로였으면 새 기본값(Ctrl+Shift+E)으로
            self.s["hotkey_v2"] = True
            if all(saved_hk.get(k, v) == v for k, v in OLD_DEFAULT_HOTKEY.items()):
                saved_hk = dict(saved_hk, **{k: v for k, v in DEFAULT_HOTKEY.items() if k != "enabled"})
                self.s["hotkey"] = saved_hk
        self.hotkey = dict(DEFAULT_HOTKEY, **saved_hk)
        self.alarm_next = None
        root.title(f"{APP_NAME}  v{APP_VERSION}")
        root.geometry(self.s.get("geometry", "1200x780"))
        if True:                                          # 처음 켤 때도 늘 전체 화면
            try:
                root.state("zoomed")
            except tk.TclError:
                try:
                    root.attributes("-zoomed", True)
                except tk.TclError:
                    pass
        if not self.s.get("autostart_init"):           # 처음 한 번: 윈도우 시작 때 자동 실행 켜 둠
            self.s["autostart_init"] = True
            try:
                set_autostart(True)
            except Exception:
                pass
        self.cache = Cache(CACHE_DB)
        global AD_MANAGER
        AD_MANAGER = AdManager(root)
        AD_MANAGER.on_change = self.ads_changed
        self.update_minsize()
        shutil.rmtree(TMP_DIR, ignore_errors=True)        # 지난번 압축 미리보기 임시 파일 정리
        self.panes = []
        self.file_clip = None          # (경로 목록, 잘라내기 여부) — 윈도우 클립보드를 못 쓸 때 대비
        self.splitters = []
        self.junctions = []
        self._grid_shape = None
        self._save_job = None
        self.col_b, self.row_b = [0, 1], [0, 1]
        self.col_bs, self.row_bs = [[0, 1]], [[0, 1]]
        self.active = None
        self._style()
        self._build()
        self.apply_layout()
        self.pinned_folders = []
        self.indexer = IdleIndexer(self)
        root.protocol("WM_DELETE_WINDOW", self.close_window)
        self.tray = TrayIcon(self)
        self.hotkey_ctl = GlobalHotkey(self.bgq)
        self.hotkey_ctl.start(self.hotkey)
        if instance is not None and instance.first:
            instance.serve(self.bgq)
        load_holiday_cache()
        self._reset_alarm()
        threading.Thread(target=self._holiday_loop, daemon=True).start()
        root.after(500, self._bg_poll)
        root.after(30000, self._autosave)
        root.after(5000, self.send_stats)
        self.update_info = None                          # 새 버전 정보 (있으면)
        saved = self.s.get("update_avail")               # 지난번에 찾아 둔 새 버전 (12시간마다 확인하므로 기억)
        if isinstance(saved, dict) and self._ver_tuple(saved.get("version", "0")) > self._ver_tuple(APP_VERSION):
            self.update_info = saved
        root.after(8000, lambda: self.check_update(force=True))   # 켤 때마다 바로 확인
        root.after(30 * 60 * 1000, self._update_tick)
        root.after(300, self.setup_ole_drop)             # 탐색기·바탕화면에서 끌어 온 파일 받기
        root.bind_all("<FocusIn>", self._focus_in, add="+")
        root.bind_all("<Control-f>", self._focus_query)
        root.bind_all("<Control-F>", self._focus_query)
        if self.panes:
            self.set_active(self.panes[0])
            self.panes[0].query_entry.focus_set()

    def _style(self):
        THEME.clear()
        THEME.update(DEFAULT_THEME)
        THEME.update(self.s.get("theme", {}))
        apply_style(self.root)

    def apply_theme(self, t):
        """환경설정 반영: 저장하고 화면을 새 글꼴·색으로 다시 그림"""
        THEME.clear()
        THEME.update(DEFAULT_THEME)
        THEME.update(t)
        self.s["theme"] = dict(THEME)
        self.rebuild_ui()

    def rebuild_ui(self):
        if any(p.busy() for p in self.panes):
            for p in self.panes:
                p.stop()
        self.save_settings()                          # 칸 상태·경계 위치를 저장해 두었다가 그대로 다시 만듦
        active_i = self.panes.index(self.active) if self.active in self.panes else 0
        for p in self.panes:
            p.destroy_pane()
        self.panes, self.active = [], None
        for w in list(self.root.winfo_children()):
            if not isinstance(w, tk.Toplevel):
                w.destroy()
        self.splitters, self.junctions = [], []
        self._grid_shape = None
        apply_style(self.root)
        self._build()
        self.apply_layout()
        self.update_minsize()
        if self.panes:
            self.set_active(self.panes[min(active_i, len(self.panes) - 1)])

    def _build(self):
        bar = ttk.Frame(self.root, padding=(8, 6, 8, 2))
        bar.pack(fill="x")
        lay = self.s.get("layout", {})
        self.cols_var = tk.StringVar(value=str(lay.get("cols", 1)))
        self.rows_var = tk.StringVar(value=str(lay.get("rows", 1)))
        # 맨 앞: 프로그램 이름과 한 줄 소개
        ttk.Label(bar, text="스마트탐색기", foreground="#b4690e",
                  font=(FONT[0], fsz(11), "bold")).pack(side="left", padx=(0, 6))
        ttk.Label(bar, text=INTRO_LINE, foreground="#7a6a52", font=(FONT[0], fsz(9))).pack(side="left", padx=(0, 16))
        ttk.Label(bar, text="화면 분할   가로").pack(side="left")
        for i, var in enumerate((self.cols_var, self.rows_var)):
            if i == 1:
                ttk.Label(bar, text="칸  ×  세로").pack(side="left")
            sp = ttk.Spinbox(bar, from_=1, to=self.MAX_SPLIT, width=3, textvariable=var,
                             command=self.apply_layout, justify="center")
            sp.pack(side="left", padx=4)
            sp.bind("<Return>", lambda e: self.apply_layout())
            sp.bind("<FocusOut>", lambda e: self.apply_layout())
        ttk.Label(bar, text="칸").pack(side="left")
        for c, r in ((1, 1), (2, 1), (1, 2), (2, 2)):
            ttk.Button(bar, text=f"{c}×{r}", width=4,
                       command=lambda c=c, r=r: self.set_layout(c, r)).pack(side="left", padx=(6 if (c, r) == (1, 1) else 1, 0))
        self.SPLIT_MODES = {"rows": "줄마다 따로 (세로 경계)", "cols": "열마다 따로 (가로 경계)"}
        self.split_mode = lay.get("split_mode", "rows")
        self.split_var = tk.StringVar(value=self.SPLIT_MODES.get(self.split_mode, self.SPLIT_MODES["rows"]))
        ttk.Label(bar, text="   경계 조절").pack(side="left")
        sm = ttk.Combobox(bar, textvariable=self.split_var, state="readonly", width=20,
                          values=list(self.SPLIT_MODES.values()))
        sm.pack(side="left", padx=(4, 0))
        sm.bind("<<ComboboxSelected>>", lambda e: self.set_split_mode(
            next(k for k, v in self.SPLIT_MODES.items() if v == self.split_var.get())))
        self._logo = smartgong_logo(bar)
        if self._logo is not None:                     # 스마트공 로고 (누르면 smartgong.kr)
            series = ttk.Label(bar, image=self._logo, cursor="hand2")
        else:
            series = ttk.Label(bar, text="smartgong.kr", foreground="#2a6fdb", cursor="hand2",
                               font=(FONT[0], fsz(9), "underline"))
        series.pack(side="right", padx=(0, 0))         # 맨 오른쪽
        series.bind("<Button-1>", lambda e: __import__("webbrowser").open("https://smartgong.kr"))
        ttk.Button(bar, text="ⓘ 사용 안내", command=self.show_guide).pack(side="right", padx=(10, 10))
        ttk.Button(bar, text="⚙ 환경설정", command=lambda: SettingsDialog(self)).pack(side="right", padx=(0, 4))
        ttk.Button(bar, text="🏢 인사랑", command=lambda: open_insarang(self.root, with_record=bool(self.alarm.get("open_record")), root=self.root)).pack(side="right", padx=(0, 4))
        self.update_var = tk.StringVar(value="")
        self.update_slot = ttk.Frame(bar)                 # 새 버전이 있을 때만 [업데이트 필요] 버튼이 나타남
        self.update_slot.pack(side="right", padx=(0, 10))
        self.update_btn = tk.Button(self.update_slot, text="업데이트 필요", command=self.show_update,
                                    bg="#e8590c", fg="white", activebackground="#c44a07", activeforeground="white",
                                    relief="flat", bd=0, padx=10, pady=2, cursor="hand2",
                                    font=(FONT[0], fsz(10), "bold"))
        self.root.after_idle(self._show_update_badge)
        self.index_var = tk.StringVar(value="")
        il = ttk.Label(bar, textvariable=self.index_var, foreground="#2f7a3a", cursor="hand2", font=(FONT[0], fsz(9)))
        il.pack(side="right", padx=(0, 12))
        il.bind("<Button-1>", lambda e: IndexDialog(self))
        notes = []
        if pdfium is None and PdfReader is None:
            notes.append("PDF 패키지 없음")
        if not SHELL_PREVIEW and sys.platform == "win32":
            notes.append("원래 모양 미리보기 불가(comtypes 없음)")
        self.hint_var = tk.StringVar()
        ttk.Label(bar, textvariable=self.hint_var, foreground="#2a6fdb",
                  font=(FONT[0], fsz(10), "bold")).pack(side="left", padx=12)

        if notes:
            ttk.Label(bar, text="※ " + ", ".join(notes), foreground="#b0412b",
                      font=(FONT[0], fsz(9))).pack(side="right", padx=(0, 10))
        self.grid_frame = tk.Frame(self.root)          # 칸들은 place로 배치 (경계를 끌어 크기 조절)
        self.grid_frame.pack(fill="both", expand=True, padx=5, pady=(2, 5))
        self.grid_frame.bind("<Configure>", lambda e: self._on_grid_resize())

    def set_layout(self, cols, rows):
        self.cols_var.set(str(cols))
        self.rows_var.set(str(rows))
        self.apply_layout()

    def apply_layout(self):
        try:
            cols = max(1, min(self.MAX_SPLIT, int(self.cols_var.get())))
            rows = max(1, min(self.MAX_SPLIT, int(self.rows_var.get())))
        except ValueError:
            return
        self.cols_var.set(str(cols))
        self.rows_var.set(str(rows))
        n = cols * rows
        saved = self.s.setdefault("panes", [])
        while len(self.panes) > n:                       # 줄어든 칸은 설정을 기억해 두고 닫음
            i = len(self.panes) - 1
            p = self.panes.pop()
            self._remember(i, p)
            if p is self.active:
                self.active = None
            p.destroy_pane()
        while len(self.panes) < n:
            i = len(self.panes)
            st = saved[i] if i < len(saved) else (saved[0] if saved else {})
            if i >= len(saved) and saved:
                st = {k: v for k, v in st.items() if k not in ("query", "pinned")}
            self.panes.append(SearchPane(self.grid_frame, self, st))
        lay = self.s.get("layout", {})
        if (cols, rows) != self._grid_shape:          # 칸 수가 바뀌면 경계를 고르게, 같으면 저장해 둔 경계 사용
            first = self._grid_shape is None

            def ok(v, n):
                return isinstance(v, list) and len(v) == n + 1 and all(isinstance(x, (int, float)) for x in v)

            def ok2(v, m, n):
                return isinstance(v, list) and len(v) == m and all(ok(x, n) for x in v)
            even = lambda n: [i / n for i in range(n + 1)]
            self.row_b = lay["row_b"] if first and ok(lay.get("row_b"), rows) else even(rows)
            self.col_b = lay["col_b"] if first and ok(lay.get("col_b"), cols) else even(cols)
            self.col_bs = lay["col_bs"] if first and ok2(lay.get("col_bs"), rows, cols) else [even(cols) for _ in range(rows)]
            self.row_bs = lay["row_bs"] if first and ok2(lay.get("row_bs"), cols, rows) else [even(rows) for _ in range(cols)]
            self._grid_shape = (cols, rows)
        self._make_splitters(cols, rows)
        self.enforce_ad_cell()
        self.place_panes()
        side = n == 1 and self.s.get("side_preview_single", True)
        for p in self.panes:                            # 칸이 1개면 미리보기를 목록 오른쪽에
            try:
                p.set_side_preview(side)
            except Exception:
                pass
        for i, p in enumerate(self.panes):              # 광고는 맨 오른쪽 아래 칸 하나에만
            p.preview.set_ad(i == len(self.panes) - 1)
            p.set_ad_pane(i == len(self.panes) - 1)
            p.after(50, p.clamp_sash)
        self.schedule_save()
        if self.active is None and self.panes:
            self.set_active(self.panes[0])

    # ───────── 칸 경계 끌어서 크기 조절 ─────────
    SPLIT_W = 6

    def set_split_mode(self, mode):
        """rows = 가로줄마다 세로 경계를 따로 / cols = 세로줄마다 가로 경계를 따로"""
        self.split_mode = mode
        self.split_var.set(self.SPLIT_MODES[mode])
        self._make_splitters(*self._grid_shape)
        self.place_panes()
        self.schedule_save()

    def _bounds(self, kind, idx):
        """kind=col/row 경계 목록. 따로 움직이는 쪽은 idx(줄·열 번호)별 목록"""
        if kind == "col":
            return self.col_bs[idx] if self.split_mode == "rows" else self.col_b
        return self.row_bs[idx] if self.split_mode == "cols" else self.row_b

    def _make_splitters(self, cols, rows):
        for w in self.splitters + self.junctions:
            w.destroy()
        self.splitters, self.junctions = [], []

        def add(kind, k, idx):
            bar = tk.Frame(self.grid_frame, bg="#c9d3e3",
                           cursor="sb_h_double_arrow" if kind == "col" else "sb_v_double_arrow")
            bar.bind("<B1-Motion>", lambda e: self._drag_split(kind, k, idx, e))
            bar.bind("<ButtonRelease-1>", lambda e: self.schedule_save())
            bar.bind("<Double-1>", lambda e: self._even_split(kind, idx))
            bar.bind("<Enter>", lambda e: bar.configure(bg="#7fa3d9"))
            bar.bind("<Leave>", lambda e: bar.configure(bg="#c9d3e3"))
            bar._split = (kind, k, idx)
            self.splitters.append(bar)
        if self.split_mode == "rows":
            for k in range(1, rows):
                add("row", k, None)                   # 가로 경계: 화면 전체 폭
            for r in range(rows):
                for k in range(1, cols):
                    add("col", k, r)                  # 세로 경계: 줄마다 따로
        else:
            for k in range(1, cols):
                add("col", k, None)                   # 세로 경계: 화면 전체 높이
            for c in range(cols):
                for k in range(1, rows):
                    add("row", k, c)                  # 가로 경계: 열마다 따로
        # 경계가 만나는 점(손잡이): 끌면 가로·세로를 한꺼번에 조절
        major_n, minor_n = (rows, cols) if self.split_mode == "rows" else (cols, rows)
        for k in range(1, major_n):
            for j in range(1, minor_n):
                for side in (k - 1, k):
                    hd = tk.Frame(self.grid_frame, bg="#7fa3d9", cursor="fleur", width=14, height=14)
                    hd._junc = (k, j, side)
                    hd.bind("<ButtonPress-1>", lambda e, h=hd: self._junc_press(h))
                    hd.bind("<B1-Motion>", lambda e, h=hd: self._junc_drag(h, e))
                    hd.bind("<ButtonRelease-1>", lambda e: self.schedule_save())
                    self.junctions.append(hd)

    def _minor_bounds(self, side):
        return self.col_bs[side] if self.split_mode == "rows" else self.row_bs[side]

    def _junc_targets(self, k, j, side):
        """같은 위치에 겹친 위·아래(왼쪽·오른쪽) 경계는 함께 움직임"""
        other = side + 1 if side == k - 1 else side - 1
        a, b = self._minor_bounds(side), self._minor_bounds(other)
        return [side, other] if abs(a[j] - b[j]) < 0.004 else [side]

    def _junc_press(self, h):
        h._targets = self._junc_targets(*h._junc)

    def _junc_drag(self, h, e):
        k, j, side = h._junc
        g = self.grid_frame
        W, H = g.winfo_width(), g.winfo_height()
        if W < 50 or H < 50:
            return
        fx, fy = (e.x_root - g.winfo_rootx()) / W, (e.y_root - g.winfo_rooty()) / H
        if self.split_mode == "rows":
            self.row_b[k] = self._clamp("row", None, k, fy)
            for s_ in getattr(h, "_targets", [side]):
                self.col_bs[s_][j] = self._clamp("col", s_, j, fx)
        else:
            self.col_b[k] = self._clamp("col", None, k, fx)
            for s_ in getattr(h, "_targets", [side]):
                self.row_bs[s_][j] = self._clamp("row", s_, j, fy)
        self.place_panes()

    def _clamp(self, kind, idx, k, frac):
        """경계 위치 제한: 칸 최소 크기, 광고가 붙은 맨 오른쪽 아래 칸은 광고 + 여유만큼"""
        g = self.grid_frame
        size = g.winfo_width() if kind == "col" else g.winfo_height()
        if size < 50:
            return frac
        b = self._bounds(kind, idx)
        cols, rows = self._grid_shape
        lo = b[k - 1] + 160 / size
        hi = b[k + 1] - 160 / size
        aw, ah = ad_pixels(self.root)
        last = (cols - 1) if kind == "col" else (rows - 1)
        # 이 경계가 광고 칸의 왼쪽(위쪽) 경계이면 광고 칸이 충분히 넓게(높게) 남도록
        touches_ad = k == last and (
            idx is None or idx == ((rows - 1) if kind == "col" else (cols - 1)))
        if touches_ad:
            need = (aw + AD_PANE_EXTRA[0]) if kind == "col" else (ah + AD_PANE_EXTRA[1])
            hi = min(hi, 1 - need / size)
        if hi < lo:                                   # 창이 너무 작으면 광고 칸을 우선
            return max(b[k - 1] + 0.02, min(hi if touches_ad else lo, b[k + 1] - 0.02))
        return max(lo, min(hi, frac))

    def enforce_ad_cell(self):
        """창 크기가 바뀌어도 광고 칸이 최소 크기 아래로 줄지 않게 경계를 밀어 줌"""
        if not self._grid_shape:
            return
        cols, rows = self._grid_shape
        if cols > 1:
            idx = None if self.split_mode == "cols" else rows - 1
            b = self._bounds("col", idx)
            b[cols - 1] = self._clamp("col", idx, cols - 1, b[cols - 1])
        if rows > 1:
            idx = None if self.split_mode == "rows" else cols - 1
            b = self._bounds("row", idx)
            b[rows - 1] = self._clamp("row", idx, rows - 1, b[rows - 1])

    def _cell(self, r, c):
        cb = self._bounds("col", r)
        rb = self._bounds("row", c)
        return cb[c], cb[c + 1], rb[r], rb[r + 1]

    def place_panes(self):
        cols, rows = self._grid_shape
        h = self.SPLIT_W // 2
        for i, p in enumerate(self.panes):
            r, c = divmod(i, cols)
            x0, x1, y0, y1 = self._cell(r, c)
            lx = h if c > 0 else 0
            rx = h if c < cols - 1 else 0
            ty = h if r > 0 else 0
            by = h if r < rows - 1 else 0
            p.place(relx=x0, x=lx, rely=y0, y=ty, relwidth=x1 - x0, width=-(lx + rx),
                    relheight=y1 - y0, height=-(ty + by))
        for bar in self.splitters:
            kind, k, idx = bar._split
            if kind == "col":
                b = self._bounds("col", idx)
                if idx is None:
                    bar.place(relx=b[k], x=-h, rely=0, relheight=1, width=self.SPLIT_W)
                else:                                 # 그 줄 높이만큼만
                    rb = self.row_b
                    t = h if idx > 0 else 0
                    bt = h if idx < rows - 1 else 0
                    bar.place(relx=b[k], x=-h, rely=rb[idx], y=t, relheight=rb[idx + 1] - rb[idx],
                              height=-(t + bt), width=self.SPLIT_W)
            else:
                b = self._bounds("row", idx)
                if idx is None:
                    bar.place(rely=b[k], y=-h, relx=0, relwidth=1, height=self.SPLIT_W)
                else:                                 # 그 열 폭만큼만
                    cb = self.col_b
                    lft = h if idx > 0 else 0
                    rt = h if idx < cols - 1 else 0
                    bar.place(rely=b[k], y=-h, relx=cb[idx], x=lft, relwidth=cb[idx + 1] - cb[idx],
                              width=-(lft + rt), height=self.SPLIT_W)
            bar.lift()
        shown = set()
        for hd in self.junctions:
            k, j, side = hd._junc
            mb = self._minor_bounds(side)
            if self.split_mode == "rows":
                x, y = mb[j], self.row_b[k]
            else:
                x, y = self.col_b[k], mb[j]
            key = (round(x, 3), round(y, 3))
            if key in shown:                          # 위·아래 경계가 겹치면 손잡이 하나만
                hd.place_forget()
                continue
            shown.add(key)
            hd.place(relx=x, rely=y, x=-7, y=-7, width=14, height=14)
            hd.lift()

    def _drag_split(self, kind, k, idx, e):
        g = self.grid_frame
        b = self._bounds(kind, idx)
        if kind == "col":
            size, pos = g.winfo_width(), e.x_root - g.winfo_rootx()
        else:
            size, pos = g.winfo_height(), e.y_root - g.winfo_rooty()
        if size < 50:
            return
        b[k] = self._clamp(kind, idx, k, pos / size)
        self.place_panes()

    # ───────── 창 숨기기·보이기, 알람, 단축키 ─────────
    def close_window(self):
        """닫기(X): 설정에 따라 트레이로 숨기거나 끝냄"""
        if self.s.get("close_to_tray", True) and self.tray.ok:
            self.save_settings()
            self.root.withdraw()
            if not self.s.get("tray_tip_shown"):
                self.s["tray_tip_shown"] = True
                self.tray.notify("트레이(시계 옆 아이콘)에서 계속 실행됩니다. 끝내려면 아이콘을 오른쪽 클릭 → 끝내기.")
        else:
            self.quit_app()

    def quit_app(self):
        self.tray.stop()
        self.hotkey_ctl.stop()
        self.on_close()

    def show_window(self):
        r = self.root
        r.deiconify()
        r.update_idletasks()
        try:
            r.state("zoomed")                        # 늘 전체 화면으로 (트레이·단축키로 불러와도 제자리·제 크기)
        except tk.TclError:
            if r.state() == "iconic":
                r.state("normal")
        r.lift()
        r.attributes("-topmost", True)
        r.after(300, lambda: r.attributes("-topmost", False))
        r.focus_force()
        r.after(1500, lambda: self.check_update(within=3600))   # 트레이에서 불러올 때 1시간 넘었으면 다시 확인
        if self.active:
            self.active.query_entry.focus_set()

    def _reset_alarm(self):
        """알람 설정이 바뀌면 다음 알람 시각을 다시 계산"""
        if self.alarm.get("mode") == "interval":
            self.alarm_anchor = time.time()
        self.alarm_next = (next_alarm_time(self.alarm, time.time(), self._anchor())
                           if self.alarm.get("enabled") else None)
        self._tray_title()

    def _holiday_loop(self):
        """공휴일 목록을 켤 때 한 번, 그 뒤 12시간마다 인터넷에서 받아 옴 (실패하면 조용히 넘어감)"""
        time.sleep(8)
        while True:
            try:
                if fetch_online_holidays():
                    self.bgq.put(("holidays", None))
            except Exception:
                pass
            time.sleep(12 * 3600)

    def _anchor(self):
        if self.alarm.get("mode") == "interval":
            return getattr(self, "alarm_anchor", self.started)
        return self.started

    def _tray_title(self):
        if self.alarm_next:
            self.tray.set_title(f"{APP_NAME} · 다음 알람 {datetime.fromtimestamp(self.alarm_next):%m/%d %H:%M}")
        else:
            self.tray.set_title(APP_NAME)

    def set_alarm(self, a):
        self.alarm = dict(DEFAULT_ALARM, **a)
        self.s["alarm"] = self.alarm
        self._reset_alarm()
        self.schedule_save()

    def set_alarm_enabled(self, on):
        self.set_alarm(dict(self.alarm, enabled=on))

    def set_hotkey(self, hk):
        self.hotkey = dict(DEFAULT_HOTKEY, **hk)
        self.s["hotkey"] = self.hotkey
        self.hotkey_ctl.start(self.hotkey)
        self.schedule_save()

    def fire_alarm(self):
        if self.alarm.get("sound", True):
            play_alarm_sound()
        AlarmPopup(self, self.alarm.get("message", ""))
        alarm_extras(self, self.alarm)

    def ocr_missing(self, force=False):
        """한국어 OCR이 없는 PC: 색인할 때 설치 안내 창 (하루 한 번, '다시 보지 않기' 가능)"""
        if not force and (self.s.get("ocr_nag_off") or time.time() - self.s.get("ocr_nag_at", 0) < 20 * 3600):
            return
        if getattr(self, "_ocr_dlg", None):
            return
        self.s["ocr_nag_at"] = time.time()
        self.schedule_save()
        self._ocr_dlg = OcrInstallDialog(self)

    def _bg_poll(self):
        try:
            while True:
                kind, data = self.bgq.get_nowait()
                if kind == "show" or (kind == "instance" and data == "show"):
                    self.show_window()
                elif kind == "alarm_toggle":
                    self.set_alarm_enabled(not self.alarm.get("enabled"))
                    self.tray.notify("반복 알람을 켰습니다." if self.alarm.get("enabled") else "반복 알람을 껐습니다.")
                elif kind == "alarm_dialog":
                    self.show_window()
                    AlarmDialog(self)
                elif kind == "quit":
                    self.quit_app()
                    return
                elif kind == "update":
                    self.on_update(*data)
                elif kind == "ocr_missing":
                    self.ocr_missing()
                elif kind == "holidays":
                    self._reset_alarm()
                elif kind == "index_done":
                    self.s["index_last"] = data
                    self.schedule_save()
        except queue.Empty:
            pass
        # 색인 상태 표시, 고정 폴더 목록 갱신 (색인 스레드가 읽음)
        try:
            self.pinned_folders = [p.folder_var.get() for p in self.panes if p.pinned_var.get()]
            if hasattr(self, "indexer"):
                self.index_var.set(self.indexer.summary())
        except Exception:
            pass
        if self.alarm_next and time.time() >= self.alarm_next:
            # 절전 등으로 여러 번 놓쳤어도 한 번만 울리고 다음 시각부터 이어감
            self.alarm_next = next_alarm_time(self.alarm, time.time(), self._anchor())
            self._tray_title()
            self.fire_alarm()
        self.root.after(1000, self._bg_poll)

    # ───────── 설치 수 집계 (무작위 번호만 보냄) ─────────
    # ───────── 새 버전 알림 (깃허브 릴리스) ─────────
    @staticmethod
    def _ver_tuple(v):
        nums = re.findall(r"\d+", str(v))[:4]
        return tuple(int(n) for n in nums) + (0,) * (4 - len(nums))

    def _update_tick(self):
        """트레이에 늘 켜 두는 프로그램이라 30분마다 '확인할 때가 됐나' 살펴봄 (절전에서 깨어나도 이어짐)"""
        self.check_update()
        self.root.after(30 * 60 * 1000, self._update_tick)

    def check_update(self, manual=False, done=None, force=False, within=None):
        """깃허브의 최신 릴리스 버전을 확인. manual=True면 결과를 done(메시지)로 알려 줌"""
        if not GITHUB_REPO:
            if done:
                done("새 버전 확인 주소(GITHUB_REPO)가 설정돼 있지 않습니다.")
            return
        if not manual and not force:
            last = self.s.get("update_checked", 0)
            if time.time() - last < (within or UPDATE_CHECK_HOURS * 3600) - 60:
                return
        if getattr(self, "_upd_running", False) and not manual:
            return
        self._upd_running = True

        def work():
            msg = None
            try:
                rels = json.loads(net_request(f"https://api.github.com/repos/{GITHUB_REPO}/releases?per_page=100",
                                              headers={"User-Agent": f"SmartExplorer/{APP_VERSION}",
                                                       "Accept": "application/vnd.github+json"}).decode("utf-8"))
                # 이 프로그램 태그(smartexplorer-v1.2.3)가 붙은 정식 릴리스 중 가장 높은 버전
                mine = [x for x in rels if isinstance(x, dict) and not x.get("draft") and not x.get("prerelease")
                        and str(x.get("tag_name", "")).startswith(RELEASE_TAG_PREFIX)]
                if not mine:
                    raise RuntimeError("아직 올라온 릴리스가 없음")
                rel = max(mine, key=lambda x: self._ver_tuple(str(x["tag_name"])[len(RELEASE_TAG_PREFIX):]))
                tag = str(rel["tag_name"])[len(RELEASE_TAG_PREFIX):]
                url = str(rel.get("html_url", ""))
                if not url.startswith(f"https://github.com/{GITHUB_REPO}/releases/"):   # 엉뚱한 주소로 보내지 않게
                    url = f"https://github.com/{GITHUB_REPO}/releases/tag/{rel['tag_name']}"
                info = {"version": tag, "url": url, "notes": str(rel.get("body") or "")[:3000],
                        "date": str(rel.get("published_at") or "")[:10]}
                newer = self._ver_tuple(tag) > self._ver_tuple(APP_VERSION)
                msg = (f"새 버전 {tag}이(가) 있습니다." if newer else f"지금이 최신 버전입니다 (v{APP_VERSION}).")
                self.bgq.put(("update", (info if newer else None, manual)))
            except Exception as e:
                msg = f"새 버전을 확인하지 못했습니다: {net_error_text(e)}"
            self._upd_running = False
            if done:
                self.root.after(0, lambda: done(msg))
        threading.Thread(target=work, daemon=True).start()

    def on_update(self, info, manual):
        self.s["update_checked"] = time.time()
        self.s["update_avail"] = info
        self.schedule_save()
        self.update_info = info
        self._show_update_badge()
        if info and not manual and self.s.get("update_skip") != info["version"] \
                and self.s.get("update_notified") != info["version"]:
            self.s["update_notified"] = info["version"]
            self.tray.notify(f"새 버전 {info['version']}이(가) 나왔습니다. 위쪽 [업데이트 필요] 버튼을 눌러 주세요.")

    def _show_update_badge(self):
        try:
            info = self.update_info
            if info and self.s.get("update_skip") != info["version"]:
                self.update_var.set(f"업데이트 필요 (v{info['version']})")
                self.update_btn.configure(text=f"업데이트 필요 (v{info['version']})")
                if not self.update_btn.winfo_ismapped():
                    self.update_btn.pack()
            else:
                self.update_var.set("")
                self.update_btn.pack_forget()
        except Exception:
            pass

    def show_update(self):
        info = self.update_info
        if not info:
            return
        w = tk.Toplevel(self.root)
        w.title("새 버전 알림")
        w.transient(self.root)
        f = ttk.Frame(w, padding=16)
        f.pack(fill="both", expand=True)
        ttk.Label(f, text=f"🔔 스마트탐색기 새 버전 {info['version']}", font=(FONT[0], fsz(13), "bold")).pack(anchor="w")
        ttk.Label(f, text=f"지금 쓰는 버전: v{APP_VERSION}" + (f"   ·   나온 날: {info['date']}" if info.get("date") else ""),
                  foreground="#777").pack(anchor="w", pady=(2, 8))
        if info.get("notes"):
            tx = tk.Text(f, height=12, width=70, wrap="word", font=(FONT[0], fsz(10)), relief="solid", borderwidth=1)
            tx.insert("1.0", info["notes"])
            tx.configure(state="disabled")
            tx.pack(fill="both", expand=True)
        ttk.Label(f, text="① [새 버전 내려받기]로 받은 SmartExplorer.exe 를 지금 쓰는 파일 자리에 바꿔 넣고 다시 실행하세요.\n"
                          "    (설정·즐겨찾기는 그대로 이어집니다)\n"
                          "② smartgong.kr 또는 깃허브 공식 릴리스에서 받은 파일만 실행하세요.",
                  foreground="#b0412b", justify="left").pack(anchor="w", pady=(8, 0))
        bf = ttk.Frame(f)
        bf.pack(fill="x", pady=(10, 0))

        def skip():
            self.s["update_skip"] = info["version"]
            self.schedule_save()
            self._show_update_badge()
            w.destroy()
        ttk.Button(bf, text="나중에", command=w.destroy).pack(side="right")
        ttk.Button(bf, text="이 버전 건너뛰기", command=skip).pack(side="right", padx=4)
        ttk.Button(bf, text="깃허브에서 보기",
                   command=lambda: (__import__("webbrowser").open(info["url"]), w.destroy())).pack(side="right", padx=4)
        ttk.Button(bf, text="새 버전 내려받기", style="Accent.TButton",
                   command=lambda: (__import__("webbrowser").open(DOWNLOAD_URL), w.destroy())).pack(side="right")
        center_on(w, self.root)

    def send_stats(self):
        if not (STATS_URL or FIREBASE_DB_URL):
            return
        import uuid
        new = False
        if not self.s.get("install_id"):
            self.s["install_id"] = uuid.uuid4().hex     # 이 PC에 설치된 프로그램을 구분하는 무작위 번호
            new = True
        today = datetime.now().strftime("%Y-%m-%d")
        if not new and self.s.get("last_ping") == today:
            return                                       # 하루에 한 번만
        ev = "install" if new else "daily"
        iid = self.s["install_id"]

        def call(url, method="GET", body=None):
            data = json.dumps(body).encode("utf-8") if body is not None else None
            net_request(url, method, {"User-Agent": f"SmartExplorer/{APP_VERSION}",
                                      "Content-Type": "application/json"}, data, limit=1024)

        def work():
            import urllib.parse
            try:
                if FIREBASE_DB_URL:
                    # installs/<번호> : 버전·처음·마지막 사용 시각 → 설치 수 = 항목 수
                    # daily/<날짜>/<번호> : 그날 켠 PC → 하루 사용 PC 수
                    base = FIREBASE_DB_URL.rstrip("/")
                    rec = {"v": APP_VERSION, "last": {".sv": "timestamp"}}
                    if new:
                        rec["first"] = {".sv": "timestamp"}
                    call(f"{base}/installs/{iid}.json", "PATCH", rec)
                    call(f"{base}/daily/{today}/{iid}.json", "PUT", True)
                if STATS_URL:
                    q = urllib.parse.urlencode({"id": iid, "v": APP_VERSION, "ev": ev})
                    call(STATS_URL + ("&" if "?" in STATS_URL else "?") + q)
                self.root.after(0, lambda: (self.s.__setitem__("last_ping", today), self.schedule_save()))
            except Exception:
                pass                                     # 인터넷이 안 되면 다음에 다시
        threading.Thread(target=work, daemon=True).start()

    def update_minsize(self):
        aw, ah = ad_pixels(self.root)
        self.root.minsize(max(640, aw + AD_PANE_EXTRA[0] + 200), max(460, ah + AD_PANE_EXTRA[1] + 80))

    def ads_changed(self):
        self.update_minsize()
        for p in self.panes:
            p.preview._layout_ad()
            p.clamp_sash()
        self.enforce_ad_cell()
        self.place_panes()

    def _on_grid_resize(self):
        if self._grid_shape:
            self.enforce_ad_cell()
            self.place_panes()

    def _even_split(self, kind, idx):
        b = self._bounds(kind, idx)
        n = len(b) - 1
        b[:] = [i / n for i in range(n + 1)]
        self.enforce_ad_cell()
        self.place_panes()
        self.schedule_save()

    # ───────── 설정 저장 (바뀔 때마다 + 끌 때) ─────────
    def schedule_save(self):
        if self._save_job:
            try:
                self.root.after_cancel(self._save_job)
            except Exception:
                pass
        self._save_job = self.root.after(1500, self.save_settings)

    def save_settings(self):
        self._save_job = None
        try:
            for i, p in enumerate(self.panes):
                self._remember(i, p)
            rnd = lambda v: [round(x, 4) for x in v]
            self.s["layout"] = {"cols": self._grid_shape[0], "rows": self._grid_shape[1],
                                "split_mode": self.split_mode,
                                "col_b": rnd(self.col_b), "row_b": rnd(self.row_b),
                                "col_bs": [rnd(v) for v in self.col_bs], "row_bs": [rnd(v) for v in self.row_bs]}
            try:
                zoomed = self.root.state() == "zoomed"
            except Exception:
                zoomed = False
            if self.root.winfo_viewable() or not self.s.get("geometry"):
                self.s["zoomed"] = bool(zoomed) if isinstance(zoomed, bool) else False
            geo = self.root.geometry()
            if isinstance(geo, str) and not zoomed:
                self.s["geometry"] = geo
            data = json.dumps(self.s, ensure_ascii=False, indent=1)
            tmp = SETTINGS_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:   # 다 쓴 다음 바꿔치기 → 도중에 꺼져도 설정이 안 깨짐
                f.write(data)
            os.replace(tmp, SETTINGS_FILE)
            return True
        except Exception:
            return False

    def _autosave(self):
        self.save_settings()
        self.root.after(30000, self._autosave)

    def _remember(self, i, pane):
        saved = self.s.setdefault("panes", [])
        while len(saved) <= i:
            saved.append({})
        saved[i] = pane.get_state()

    def set_active(self, pane):
        if self.active is pane:
            return
        if self.active is not None:
            try:
                self.active.set_active(False)
            except tk.TclError:
                pass
        self.active = pane
        pane.set_active(len(self.panes) > 1)

    def _focus_in(self, e):
        w = e.widget
        while w is not None and not isinstance(w, SearchPane):
            w = getattr(w, "master", None)
        if w is not None and w in self.panes:
            self.set_active(w)

    def _focus_query(self, e=None):
        if self.active:
            self.active.query_entry.focus_set()
            self.active.query_entry.select_range(0, "end")
        return "break"

    def show_guide(self):
        w = tk.Toplevel(self.root)
        w.title("스마트탐색기 사용 안내")
        w.transient(self.root)
        center_on(w, self.root, 640, 560)
        tx = tk.Text(w, wrap="word", padx=18, pady=14, font=FONT, relief="flat", spacing1=2, spacing3=4)
        tx.pack(fill="both", expand=True)
        tx.tag_configure("h", font=(FONT[0], fsz(13), "bold"), foreground="#b4690e")
        tx.tag_configure("b", font=(FONT[0], fsz(10), "bold"))
        tx.tag_configure("contact", background="#fff8e6", lmargin1=8, lmargin2=8, rmargin=8,
                         spacing1=6, spacing3=6)
        tx.tag_configure("mail", foreground="#1565c0", underline=True, font=(FONT[0], fsz(10), "bold"))
        tx.tag_configure("key", foreground="#b4690e", font=(FONT[0], fsz(12), "bold"))

        def copy_mail(e=None):
            try:
                w.clipboard_clear()
                w.clipboard_append(CONTACT_EMAIL)
            except tk.TclError:
                pass
            messagebox.showinfo(APP_NAME, f"메일 주소를 복사했습니다.\n\n{CONTACT_EMAIL}\n\n"
                                          "메일 받는 사람 칸에 붙여넣어(Ctrl+V) 보내 주세요.", parent=w)
        tx.tag_bind("mail", "<Button-1>", copy_mail)
        tx.tag_bind("mail", "<Enter>", lambda e: tx.configure(cursor="hand2"))
        tx.tag_bind("mail", "<Leave>", lambda e: tx.configure(cursor=""))
        for i, (head, body) in enumerate(GUIDE):
            if i == 0:
                tx.insert("end", head + "\n", "h")
                tx.insert("end", body + "\n\n")
                hk = self.hotkey
                tx.insert("end", "⌨ 바로 실행 단축키  ", ("contact", "b"))
                tx.insert("end", hotkey_text(hk) if hk.get("enabled", True) else "꺼짐", ("contact", "key"))
                tx.insert("end", "\n어디서든 누르면 스마트탐색기가 바로 앞으로 나옵니다 (트레이에 숨어 있어도). "
                                 "바꾸기: ⚙ 환경설정 → 알람·실행 설정\n", "contact")
                tx.insert("end", "✉ 사용하다가 오류나 개선할 점이 있으면 ", "contact")
                tx.insert("end", CONTACT_EMAIL, ("contact", "mail"))
                tx.insert("end", " 으로 알려 주세요. (누르면 주소 복사)\n", "contact")
                tx.insert("end", "\n")
            else:
                tx.insert("end", head + "\n", "b")
                tx.insert("end", body + "\n\n")
        tx.configure(state="disabled")
        ttk.Button(w, text="닫기", command=w.destroy).pack(pady=8)

    # ───────── 칸끼리 파일 옮기기 ─────────
    def set_hint(self, text):
        self.hint_var.set(text)

    def pane_at(self, xr, yr):
        w = self.root.winfo_containing(xr, yr)
        while w is not None and not isinstance(w, SearchPane):
            w = getattr(w, "master", None)
        return w if w in self.panes else None

    def drop_target(self, xr, yr, paths):
        """끌어 놓는 위치 → (칸, 넣을 폴더). 폴더 줄 위면 그 폴더, 아니면 그 칸이 보고 있는 폴더"""
        pane = self.pane_at(xr, yr)
        if pane is None:
            return None, None
        dest = None
        try:
            row = pane.tree.identify_row(yr - pane.tree.winfo_rooty())
            if self.root.winfo_containing(xr, yr) is pane.tree:
                h = pane.hits.get(row)
                if h and h.get("is_dir") and h["path"] not in paths:
                    dest = h["path"]
        except Exception:
            pass
        if dest is None and pane.mode == "browse":
            dest = pane.cwd
        if not dest:
            return pane, None
        if all(os.path.normcase(os.path.dirname(p)) == os.path.normcase(dest) for p in paths):
            return pane, None                          # 원래 있던 폴더에 놓음 = 아무 일 없음
        if any(os.path.isdir(p) and is_inside(dest, p) for p in paths):
            return pane, None                          # 폴더를 자기 안으로 옮길 수 없음
        return pane, dest

    # ───────── 탐색기·바탕화면에서 끌어 온 파일 받기 ─────────
    def setup_ole_drop(self):
        self.ole_target = None
        self.drag_source = None
        self._drop_hl = None
        self._ole_req = self._ole_drop_req = self._ole_state = None
        if OLE_DND is None:
            return
        try:
            self.root.update_idletasks()
            hwnd = int(self.root.wm_frame(), 16)
            t = OLE_DND.DropTarget(hwnd, self._ole_drop_event)
            self.ole_target = t if t.ok else None
            if self.ole_target is not None:
                self.root.after(40, self._ole_poll)
        except Exception:
            self.ole_target = None

    def _drop_effect(self, paths, dest, keys):
        """탐색기와 같은 규칙: Ctrl=복사, Shift=이동, 그냥 놓으면 같은 드라이브는 이동·다른 드라이브는 복사"""
        if keys & OLE_DND.MK_CONTROL:
            return OLE_DND.DROPEFFECT_COPY
        if keys & OLE_DND.MK_SHIFT:
            return OLE_DND.DROPEFFECT_MOVE
        return OLE_DND.DROPEFFECT_MOVE if same_drive(paths[0], dest) else OLE_DND.DROPEFFECT_COPY

    def _set_drop_highlight(self, pane, row):
        old = self._drop_hl
        if old and old != (pane, row):
            try:
                op, orow = old
                if orow and op.tree.exists(orow):
                    tags = [t for t in op.tree.item(orow, "tags") if t != "drophl"]
                    op.tree.item(orow, tags=tags)
            except Exception:
                pass
        self._drop_hl = (pane, row) if pane is not None and row else None
        if self._drop_hl:
            try:
                tags = list(pane.tree.item(row, "tags"))
                if "drophl" not in tags:
                    pane.tree.item(row, tags=tags + ["drophl"])
            except Exception:
                pass

    def _ole_drop_event(self, kind, paths, x, y, keys):
        """끌어 놓기 알림 (윈도우가 부름).
        다른 프로그램(탐색기 등)에서 끌어 올 때는 tkinter가 이벤트를 처리하는 도중에 불리므로 여기서 화면(tk)을 만지면
        프로그램이 멈출 수 있음 → 요청만 적어 두고, 화면 일은 _ole_poll 이 이어서 함.
        이 프로그램에서 끌기 시작한 경우(drag_source)는 끄는 동안 tk 가 돌지 않으므로 바로 처리"""
        if self.drag_source is not None:
            return self._ole_apply(kind, paths, x, y, keys)
        self._ole_req = (kind, list(paths), x, y, keys)
        if kind == "drop":
            self._ole_drop_req = self._ole_req
        st = self._ole_state                    # 화면 쪽에서 마지막으로 계산해 둔 결과
        if kind == "leave" or not paths:
            return 0
        if st is None:
            return OLE_DND.DROPEFFECT_COPY      # 아직 계산 전: 일단 받을 수 있다고 표시
        eff = st[2]
        if eff and keys & OLE_DND.MK_CONTROL:
            eff = OLE_DND.DROPEFFECT_COPY
        elif eff and keys & OLE_DND.MK_SHIFT:
            eff = OLE_DND.DROPEFFECT_MOVE
        return eff

    def _ole_poll(self):
        """다른 프로그램에서 끌어 오는 동안 화면 표시(놓을 폴더 강조·안내 글)와, 놓았을 때 옮기기"""
        try:
            req, self._ole_req = self._ole_req, None
            if req is not None:
                kind, paths, x, y, keys = req
                if kind == "leave":
                    self._ole_state = None
                self._ole_apply("over" if kind == "drop" else kind, paths, x, y, keys, remember=True)
            drop, self._ole_drop_req = self._ole_drop_req, None
            if drop is not None:
                kind, paths, x, y, keys = drop
                self._ole_state = None
                self._ole_apply("drop", paths, x, y, keys)
        except Exception:
            pass
        self.root.after(40, self._ole_poll)

    def _ole_apply(self, kind, paths, x, y, keys, remember=False):
        if kind == "leave" or not paths:
            self._set_drop_highlight(None, None)
            self.set_hint("")
            return 0
        pane, dest = self.drop_target(x, y, paths)
        row = None
        if pane is not None and dest:
            try:
                r = pane.tree.identify_row(y - pane.tree.winfo_rooty())
                h = pane.hits.get(r)
                if h and h.get("is_dir") and os.path.normcase(h["path"]) == os.path.normcase(dest):
                    row = r
            except Exception:
                pass
        self._set_drop_highlight(pane, row)
        eff = self._drop_effect(paths, dest, keys) if dest else 0
        if remember:
            self._ole_state = (pane, dest, eff)
        if not dest:
            self.set_hint("여기에는 놓을 수 없습니다" if pane is not None else "")
            return 0
        op = "이동" if eff == OLE_DND.DROPEFFECT_MOVE else "복사"
        if kind != "drop":
            self.set_hint(f"{len(paths)}개 → {os.path.basename(dest.rstrip(os.sep)) or dest} 로 {op}  "
                          "(Ctrl=복사, Shift=이동)")
            return eff
        self._set_drop_highlight(None, None)
        self.set_hint("")
        src = self.drag_source
        # 끌어 놓기가 끝난 뒤에 옮김 (보낸 쪽이 기다리지 않게)
        self.root.after(10, lambda: self.transfer(list(paths), dest, move=(eff == OLE_DND.DROPEFFECT_MOVE),
                                                  source=src or pane))
        return eff

    def release_previews(self):
        """미리보기가 파일을 붙잡고 있으면 옮기거나 지울 수 없으므로 먼저 놓아 줌"""
        for p in self.panes:
            try:
                p.preview.clear()
            except Exception:
                pass

    def refresh_browsers(self, except_pane=None):
        for p in self.panes:
            if p is not except_pane and p.mode == "browse" and p.cwd:
                p.load_browse()

    def transfer(self, paths, dest, move, source=None):
        paths = [p for p in paths if os.path.exists(p)]
        if not paths or not os.path.isdir(dest):
            return False
        if any(os.path.isdir(p) and is_inside(dest, p) for p in paths):
            messagebox.showwarning(APP_NAME, "폴더를 자기 자신 안으로 옮기거나 복사할 수 없습니다.")
            return False
        same_folder = all(os.path.normcase(os.path.dirname(p)) == os.path.normcase(dest) for p in paths)
        if move and same_folder:
            return False
        self.release_previews()
        try:
            ok = shell_file_op(FO_MOVE if move else FO_COPY, paths, dest,
                               hwnd=source.hwnd() if source else 0, rename_on_collision=same_folder)
        except Exception as e:
            messagebox.showerror(APP_NAME, f"{'이동' if move else '복사'}하지 못했습니다.\n{e}")
            ok = False
        names = [os.path.join(dest, os.path.basename(p)) for p in paths]
        for p in self.panes:
            if p.mode == "browse" and p.cwd:
                p.load_browse(select=names if os.path.normcase(p.cwd) == os.path.normcase(dest) else None)
        if source is not None:
            source.status_var.set(f"{len(paths)}개 {'이동' if move else '복사'}{'함' if ok else ' — 일부 취소됨'} → {dest}")
        return ok

    def add_recent(self, folder):
        recent = [folder] + [f for f in self.s.get("recent", []) if f != folder]
        self.s["recent"] = recent[:15]
        for p in self.panes:
            p.folder_cb.configure(values=self.s["recent"])

    def clear_cache(self):
        if any(p.busy() for p in self.panes):
            messagebox.showinfo(APP_NAME, "모든 검색이 끝난 뒤에 비워 주세요.")
            return
        n = self.cache.count()
        if messagebox.askyesno(APP_NAME, f"저장해 둔 문서 내용 {n:,}건을 지울까요?\n(다음 검색은 파일을 다시 읽어서 느려집니다)"):
            self.cache.clear()

    def on_close(self):
        try:
            if self.ole_target is not None:
                self.ole_target.revoke()
        except Exception:
            pass
        try:
            self.indexer.stop()
            self.indexer.thread.join(timeout=3)
        except Exception:
            pass
        if self._save_job:
            try:
                self.root.after_cancel(self._save_job)
            except Exception:
                pass
        self.save_settings()
        workers = [p.worker for p in self.panes if p.busy()]
        for p in self.panes:
            p.stop_event.set()
            p.preview.clear()
        for w in workers:
            w.join(timeout=2)
        try:
            self.cache.close()
        except Exception:
            pass
        shutil.rmtree(os.path.join(TMP_DIR, "preview"), ignore_errors=True)
        WHEEL_HOOK.remove_all()
        self.root.destroy()


def main():
    if sys.platform == "win32":
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
    start_hidden = "--tray" in sys.argv
    instance = SingleInstance()
    if not instance.first:                             # 이미 켜져 있으면 그 창을 불러오고 끝냄
        if instance.notify_existing("tray" if start_hidden else "show"):
            return
        # 대답이 없으면 다른 프로그램이 같은 번호를 쓰는 것 → 그대로 실행 (하나만 실행 기능만 빠짐)
    root = tk.Tk()
    set_window_icon(root)
    app = App(root, instance)
    if start_hidden and app.tray.ok:                   # 윈도우 시작 때는 트레이에 숨긴 채로
        root.withdraw()
    root.mainloop()


if __name__ == "__main__":
    main()
