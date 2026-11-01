# -*- coding: utf-8 -*-
"""
반복 알람 (Windows)
- 지정한 시각/간격/요일에 맞춰 팝업창 + 알림음(또는 mp3/wav 파일) + 음성(TTS)으로 알려줍니다.
- 팝업: 살짝 움직이는 캐릭터 이미지(기본 내장, 원하는 이미지/GIF로 교체 가능),
        크기·위치·글꼴·글자색·배경색·배경이미지 설정 가능
- 창을 닫아도 시스템 트레이에 남아 계속 동작합니다.
- Windows 시작 시 자동 실행 설정 가능.

필요 패키지: pillow, pystray  (pip install pillow pystray)
"""
import sys
import os
import io
import json
import math
import re
import calendar
import time
import queue
import base64
import ctypes
import socket
import subprocess
import threading
import datetime
import hashlib
import secrets
import webbrowser
import http.server
import urllib.request
import urllib.parse
import urllib.error
import tkinter as tk
import tkinter.font as tkfont
from tkinter import ttk, messagebox, filedialog, colorchooser, simpledialog

try:
    import winsound
except ImportError:  # 비 Windows 환경(테스트용)
    winsound = None

try:
    from PIL import Image, ImageDraw, ImageFont, ImageSequence, ImageTk
    HAS_PIL = True
except Exception:
    HAS_PIL = False

try:
    import pystray
    HAS_TRAY = HAS_PIL
except Exception:
    HAS_TRAY = False

APP_NAME = "스마트 일정 알라미"
APP_VERSION = "1.1.0"          # 배포할 때 여기만 올리면 깃허브가 자동으로 빌드·릴리스 (태그 smartalarm-v버전)
DAY_NAMES = ["월", "화", "수", "목", "금", "토", "일"]  # datetime.weekday(): 월=0
LOCK_PORT = 47653
REPEAT_MS = 7000
SNOOZE_MIN = 5

CONFIG_DIR = os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), "RepeatAlarm")
CONFIG_PATH = os.path.join(CONFIG_DIR, "alarms.json")
BACKUP_DIR = os.path.join(CONFIG_DIR, "backup")

POS_CHOICES = ["가운데", "화면 위쪽 가운데", "왼쪽 위", "오른쪽 위", "왼쪽 아래", "오른쪽 아래", "직접 지정"]
PREFERRED_FONTS = [
    "한컴산뜻돋움", "한컴 산뜻돋움", "나눔스퀘어라운드 ExtraBold", "나눔스퀘어라운드 Bold", "나눔스퀘어라운드", "NanumSquareRound",
    "배달의민족 주아", "배달의민족 도현", "Jua", "HY견고딕", "HY엽서M", "휴먼둥근헤드라인", "휴먼엑스포",
    "나눔손글씨 펜", "나눔바른펜", "나눔고딕", "NanumGothic", "맑은 고딕", "Malgun Gothic",
]
AUTO_FONT_LABEL = "(자동 선택)"
# 기본 글꼴 우선순위: 한컴산뜻돋움 → 맑은 고딕 → 돋움체
DEFAULT_FONT_ORDER = ["한컴산뜻돋움", "한컴 산뜻돋움", "맑은 고딕", "Malgun Gothic", "돋움체", "DotumChe", "돋움", "Dotum"]

DEFAULT_STYLE = {
    "w": 400, "h": 300,
    "pos": "가운데", "x": 100, "y": 100,
    "font": "", "size": 22, "bold": True, "fg": "#4a2f00", "shadow": True,
    "bg": "#fff3bf", "bg_image": "",
    "use_img": True, "img": "", "anim": True,
    "sound": "",
    "font_files": [],
    "img_fit": "fit",
}

# 프로그램(메인 창) 꾸미기 기본값
DEFAULT_UI = {
    "font": "", "size": 12,
    "fg": "#212529", "bg": "#f1f3f5", "card": "#ffffff", "accent": "#f6a53f",
    "head_bg": "#fff3bf", "head_fg": "#4a2f00", "head_img": "", "head_mascot": True,
}
SG_URL = "https://www.smartgong.kr/"
NOTICE_EVERY_S = 6 * 3600           # 공지는 6시간마다 확인 (GitHub 페이지의 파일을 읽으므로 Firebase 한도와 무관)

# 초과근무 알람 기본값 (평일 업무시간 밖 + 휴일 전체)
DEFAULT_OT = {"enabled": True, "start": "09:00", "end": "18:00", "every": 60, "holiday": True,
              "text": "초과근무 시간입니다. 업무를 마무리하고 퇴근을 준비하세요."}

# 뽀모도로 기본값 (분)
DEFAULT_POMO = {"work": 25, "brk": 5, "long": 15, "every": 4, "auto": True}
POMO_NAMES = {"work": "일하는 시간", "brk": "휴식 시간", "long": "긴 휴식"}

# 달력(일정) 위젯 기본값
DEFAULT_CAL = {"show": False, "x": -1, "y": -1, "w": 640, "h": 520, "mode": "alpha", "alpha": 85,
               "hover": True, "lock": False, "bottom": False, "holidays": True, "lunar": True, "view": "month",
               "font": "", "fscale": 100, "fg": "", "bg": "", "head_bg": "", "head_fg": "", "accent": "",
               "img": "", "veil": 40}

FIT_LABELS = {
    "fit": "팝업 크기에 맞춤 (비율 유지)",
    "fill": "팝업 전체 꽉 채우기 (잘릴 수 있음)",
    "area": "글자 위쪽 영역에 맞춤",
}
FIT_CODES = {v: k for k, v in FIT_LABELS.items()}

# 프로그램 아이콘(달력+알람시계)
APPICON_B64 = (
    "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"
)


def app_icon_image(size):
    """프로그램 아이콘을 size×size RGBA 이미지로 (Pillow 필요)"""
    im = Image.open(io.BytesIO(base64.b64decode(APPICON_B64))).convert("RGBA")
    return im.resize((int(size), int(size)), _RES.LANCZOS)


# 스마트공 기본 아이콘(임시 이미지; 설정에서 내 이미지로 바꿀 수 있음)
SG_IMG_B64 = (
    "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"
    "SUVORK5CYII="
)

# 기본 팝업 이미지(내장, 투명 배경 PNG)
DEFAULT_IMG_B64 = (
    "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"
    "5sGhu+84/fB/+mIrOf1nsRrIj3/yH72xF80banHdyZ5nw0al7N5Kb/MPE8OI4elfozN6BCcFIQqOLgcPjlg5I7isR11XZB0ly2qm"
    "pIOZraHjuGL2Oqamppia30qcv4pmahc9PY0/+mE2Tj7B/j0i9XJ0PVneeOiR392w+7afs1xkyWm3fmtd/TMYaKmLa1y7dRtWuyic"
    "WWuqjRk8MUIsA1prouVJnbIoOw4CEQ2K82kxZS26kOCfuG5TfvFmFs+Xma0u+vaLGe21jQKUIXFpTIuDS1L/HF/fauN4HeKwDhBL"
    "GeVLwLkQ1qioqwKwRtpZC6BUQlUn9o9yFnASVVfhMjfWZhrDYeYsJ8UX5Ti7P6RnPcfVmYT2HSUovvGrIrXjCe7xhPy4JDZydkKw"
    "7o+1n/9N9j3WC9GqJogtErgAh2KTHz752o7k85GcyQ3LsnVbTpACP/ejZPM/yWS9hA9fhupRzPA49ehRQr1AqJcJg9MYbzhxaMDC"
    "0YgJk5xZWOD4kZrLrijwvlqd5EZqhBzrAyYr2bCp4PTxmqaRjg7PvP6phz76mvkbf2o/MPiztPurqjz+4H/ZHMtHbo+VXmUnvJnf"
    "puRzGfXcd+Kya6hO/w4sfQpLIGYVgmXxqOHYAZAwRRM90/MNu67MyPICOzmH3fh9hIlXUXSuxuTX4V2GYOhGizRfoo4fYWLLkMmB"
    "cOLRSMbc9qbsvxO4HzjxwsBBYybOWGxNhWebA9PzLsjxzUuCbTaO6dcBNC3KsbXs6s/QC/+cl83LMN4AU0KfmpJ+rUk8tmoVWdfj"
    "+xa4rvFpGlmTgNIYnzatYs/dgPXZ4YyXxyJuz799LrLqN7H2PcGsNc7HwVHlhe1xjKeo01jCBVl0S029ss9Ip4pa0Zl26tVJ9DWm"
    "/jqx/DzGbCPrvQombkfnJ8kZYMJxmtEppHmMzB9CJ/6QfnkP1SmDNj2OHegzM5MzMesxJiT1dQGVgLYZ2fScZ+NW4cRTAVW2nj70"
    "1e9e2XvnV1R1z5+dakCg/8Cm41/6b38hlM07MdqdmrDMb/XEzivpzP1F8H048WtM+2NUmcXnBlsaDh8oCXWPIutiitPsuCowt1UJ"
    "VWA0exndjT8C3atp9AhUJ7HVQer+I4TyQeryIVz5FWyhTPVyjkqXrMpmKf0NLD41cXan9qIGgSwNjKnB+7E5NglDFkmQwjfwK2XM"
    "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"
    "X1KSBpUEMT450wVBTIcjh/ss9SFK14sWX9v0yv/p4yQpAb1IVcB4sUydfuR335X70StihXUbtsv1t/89dPqV9MsBvslRawjdCepg"
    "cY0F15BpTrDLbJgZcPnlMLPJ47XGZ2B3G7o3Ozo72nf2sFA9HCj3BuKxiB15bBir86ZNvGkVcokR1UiI2rpUK0GSBSwhyYyrJNi4"
    "kUggJuvP9Z+Y/LGdT0EjaiBok+i7tN8S9byfoBf+xDYpiFGTY2JIn/SFgNIQCQRJ7trpEpNveRSofYQ4Ynqi5PKtOdu39MnMEvgM"
    "1ymptU7BqlEoethgYdSnzHaw8y0/S/eGd0ntgytMfWX/1D23H/jKf7hM9aVLdZ9ldU6c2nDle/64Np39XdfE/pnAwtHldIFBMNpB"
    "JNAMk41ip5snO14TkKiY8X09D1NDAOP7eNlHVQyJxuLIiVJeMLq/bKDlc69FwWqSupW8l7SVYkjuR5IlzrNJTeDxx4ghUGKcRbSD"
    "RfA+IDJNbufRaMmtYbC4h5NHH0ZNzeYrDL1NMcloaMDrEDIDriabGmIzTyhLXD5DGBVkk9NsuqaTsrOVg5QnHsL5Lt5ZSttHtaCp"
    "+lijrSezQ2zyD048a3PWOaePRWMgs566HkDdpIEzI6vGakbPBgFfFpVcbGdZjAGXkbkcZxyiKetr5AxqRtAMyDWkjcw+dwpS9BlW"
    "DOpguFSwdEzIoiN6f8J3rvr0DW/8G/vaKuCi3RVVtfd99P03hcGpNxvVuSbL2XXrT9Odvw07jHS9wTpD5jy5HyQ5FlFscBQo2zc4"
    "tu7KmczyJA+zAaZe0aN7uUEqJRwx9PcNWTowpF4K2GBx6pLf7jppB3men2/m377QHzj/eSZkSuhknm1bO+zY3qPIS6IfIiEDcnId"
    "MtMokk1QdcGHY2R0uflVP4AWV+CM67i6/PbDe+58DZC9LIOAGNPsuu0nH9LOxk825XBFtGDheKN+aHGS4ZxDYyBWwCgi1mB6QuPS"
    "hIZV0/Kz10o0M3bUciD1UarmfmpnCdFiycA0PE33Xs3LAhNSUsZz7qkYwHrwPlLhyIpJnCiWRBtVzq4Cxh/E461Qe4szoDaQdTZS"
    "FPMQhMwoy8e/Qrn4JFlh+f+z99/RlmXXeR/6m2utvfcJN1bOVZ270Y2cMwGCYBQpigIoUyJFM8gkZUt6Q9Szn2kPQrbpIenRpuQn"
    "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"
    "KLpB6KXVQIrW+Qg7LpysefKhCT0GBC1O9hZe88mdO29buRJAQUTUzB598nP/8s6QTr4n1gvleq22c99Irj+kUPdoVyuaqdFsTBht"
    "wPBCw2RdqUdK20ZIAU1d1mQ5wmfVaut0idgs9bZifOqCgGzi5Wds4DTzk+8YxVkhEcxXGaWkWRfFbUorC9bGTAKznFWYM4I46pAR"
    "OK4wioGwY0dgaWef3kKJW0rMLSSKwYDVJ5I99uiEOeuNzO/4dHXw1U882yGb+R/nH/7MP3/znb12+bvrNSkeumfFbt+5S0K/zZ0s"
    "Ey6btIvho2H+Glz/hzHpk+p/jjX/AUnn6fXmeOr+dZYfbhHx2trCgwu7X/fR/be/Z+XF4gv7Ir6quz/2v7/dc+HNzg96ZTVi5448"
    "PA2+j+mUZuoZr3vOncwwbMTwweOddbmVYJr3VRJD4waxXcbFEcIcV4DC/QEcGAmzctOLJNk6qqPNudjM6cg5wUidtLsjuAHrq2OO"
    "PbLO7gOB3qCH8y3mEyVw7b6KJ84PUbfE2JYI0mJKTwrteZtm5JoqDnBTh4lDNrkRCU8iBIPU4hph3vVA245nM2bXrpK5PX3mF1YY"
    "9CJFACtnlVaP4ZmSh+9fo60VoUDEMvt5s8GdZ4POHNNgOF2CZmRtqE/1d7/1N172XT9xj3PuIqLbSyYIYMb11//wuY0bf+8TKw/+"
    "9/dU2nttc3LqH/3cCre+7QD93WD2BFb/ChbPQrEfl+7BuWmnrtkHilyeujpnyeqQ3hyTk3Diy2vIekUK5bTp7b/nNW/+sd8Hhs+G"
    "XNq59/B0fflh9Tpm/aRDN8AtZRRQsbOl9BU42NUIFitSU9COjWYamQ6NZqo000hbC+0kMZm0xKnm+ZV2Bu2JTZ2TmoSEhCRHj3mc"
    "a2m1xlyPQhyhLRi7BvUjQt3DeSHRsknM8ZCcbVqVOW/050uqQUFZGWVfqKpAWBBCPyMjQmX4SvHFjEAA6BhLjgtnGtykLzE00zjn"
    "77nhFf/Tqed22O5u3J43nxxPP3auTPQ3jkzd0fkVbvqOXZl81yrRGUFkS4FPDfGBGBRNG9jkV9G0TrQvUfbO4M2zcr/y5FfWwRbM"
    "WbveW9jz+Vd/4B98xYk0V6uAZ4XVlHr2iVf3U7rBYpTBUqS3NE+zEVm50LB2QRltCM1ESbHC+x4pOny5sanXpW3nwGERvKfUFtc+"
    "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"
    "ijIQJZCcSJ2SDoIvmkl6q1//6uuBI+FbJLOhG/6dBjltpkeBT3NlP4q2OzDSNpTE8z48tuUnG3F+9xdCPXp71eqh8RkTsR6hF5HU"
    "B+rNLDt3ZRTxmp+8+PzcxIPmzSWzIS1ZS0hxnZF7N6hN0iF5HGYN4ovsb6wFElqkGAMOix5XZHSyWEQsAoGUEtpGytIDve61HSj4"
    "GcZuZta06dZkiNNcuVQV6+sTdJSIxYRYVcO3vvcvr26bB3wdzzIhIrWZHdv5/h88A3zyGX5n0z3Hq1n/c7xUVR7+zb91XRie/qOh"
    "KK+vZcFdd9v3sPvVH2Bf/xpYuJHa3U/z+C8hzTlUjNAp4TKDlmDbLElTh8mfGRjlrxcWc5GLUUmbxQoLI4zuo9Z/h999Hrf4PqI7"
    "jGpAmeJcQlKBmCKmmfGLz714084+NWf8kEEUSCKJ0FhJ4UoCJ2D6EJz9DxTtJ3AFmBR4a3BkJrCzvIeM2VDZNs/P7DmTjTS2cBlK"
    "1CYv/SagaUhavJmFA3+a8tYNbjjzFOvH7uXxh36e5tx9FG6es2eHHL4Oyn72HReXoXZZATiSYubwzLzKBSG2CYInWMHqycSxR5Xx"
    "sE/pXb4/FB2qaUgRPFDgfTZ6etpwRLIeGUFQy4HSm8OJuNQ0rQvVUfo7nsq9hW+9Yle6YeD0Dw2wBOtze9/7+fXzv3Ba/Oja1fXA"
    "8v0tmiZsjBRtCkzjJgLH+cwk9H0lhGwYX/Yd5cBRDRbxA4Ew7IguSvC9LP1M6HaadszfWauoe+AoqpJZj11moWY41yLqsFTlMpJI"
    "IRVpzTGuK2IdacaG1UaqjbZus2mNZtVCA7x3lGWBLz1zux2rx2vGMdIriklT7LgA84krqDS90LlPV1lMn0Msvor/f46X84V98ed/"
    "sPBaDmrnfH//q7n1HX8Vm7udZrjOpImUbj+D8BZoHsqY8+1P9DkWWnrRJpH8Yyb4QUurX0aXz1BMHqO/9P1o7zU0toA2FZaZtCAN"
    "IjWFRJJk9JqpB8tgCy+z2rjCI8xJjWsewIa/SRr+NjI9ScmY4EBcTTRHsjL7Dkt8fqtUslWqmGDS0ITdhOoQTVvT1CXFjlvZs+/V"
    "NAPh4Y/+Y+bTGtTGdNJQ9bfSRdW0yax2BRgBi90B7gRvHjetOHUq8eSTLU29hBdPKVO85LlhspjVAzp5bMwTrLclz2KzYbMw7WRd"
    "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"
)


# ================================================================ 로직
def hm_to_min(s):
    h, m = s.split(":")
    return int(h) * 60 + int(m)


def normalize_date(text):
    """'2026-10-8', '2026.10.08', '2026/10/8' 등을 '2026-10-08'로. 잘못되면 ValueError"""
    parts = [x for x in re.split(r"[-./\s]+", str(text).strip()) if x]
    if len(parts) != 3:
        raise ValueError("날짜 형식 오류")
    return datetime.date(int(parts[0]), int(parts[1]), int(parts[2])).isoformat()


def minutes_on_day(a):
    """그날 알람이 울릴 시각(자정부터 분 단위) 목록"""
    if a["mode"] in ("time", "date"):
        return [hm_to_min(a["time"])]
    s_, e_ = hm_to_min(a["start"]), hm_to_min(a["end"])
    return list(range(s_, e_ + 1, max(1, int(a["every"]))))


def day_ok(a, d):
    """알람 a가 날짜 d(datetime.date)에 해당하는지 (요일/날짜/적용 기간)"""
    if not a.get("enabled", True):
        return False
    iso = d.isoformat()
    if a["mode"] == "date":
        return a.get("date") == iso
    if d.weekday() not in a["days"]:
        return False
    f, t = a.get("from"), a.get("to")
    if f and iso < f:
        return False
    if t and iso > t:
        return False
    return True


def matches(a, dt):
    """알람 a가 dt(분 단위)에 울려야 하는지"""
    if not day_ok(a, dt.date()):
        return False
    m = dt.hour * 60 + dt.minute
    if a["mode"] in ("time", "date"):
        return m == hm_to_min(a["time"])
    s_, e_ = hm_to_min(a["start"]), hm_to_min(a["end"])
    return s_ <= m <= e_ and (m - s_) % max(1, int(a["every"])) == 0


def next_fire(alarms, snoozes, now, events=()):
    """(datetime, label) 또는 None  (앞으로 2년 이내)"""
    best = None
    today = now.date()
    nowmin = now.hour * 60 + now.minute
    for off in range(0, 731):
        d = today + datetime.timedelta(days=off)
        cands = []
        for a in alarms:
            if not day_ok(a, d):
                continue
            for mm in minutes_on_day(a):
                if off == 0 and mm <= nowmin:
                    continue
                cands.append((mm, a["label"]))
        for e in events:
            for mm, lab in event_fires(e, d):
                if off == 0 and mm <= nowmin:
                    continue
                cands.append((mm, lab))
        if cands:
            mm, lab = min(cands)
            best = (datetime.datetime.combine(d, datetime.time(mm // 60, mm % 60)), lab)
            break
    for s_ in snoozes:
        d = datetime.datetime.fromtimestamp(s_["at"])
        if best is None or d < best[0]:
            best = (d, s_["label"])
    return best


def describe_days(days):
    d = sorted(days)
    if d == list(range(7)):
        return "매일"
    if d == [0, 1, 2, 3, 4]:
        return "평일"
    if d == [5, 6]:
        return "주말"
    return "·".join(DAY_NAMES[i] for i in d)


def describe_alert(a):
    parts = []
    if a.get("beep", True):
        parts.append("파일" if a.get("sound") else "알림음")
    if a.get("tts", True):
        parts.append("음성")
    return "+".join(parts) if parts else "팝업만"


def describe_repeat(a):
    if a["mode"] == "date":
        return "날짜 지정(1회)"
    txt = describe_days(a["days"])
    f, t = a.get("from"), a.get("to")
    if f or t:
        short = lambda x: x[2:].replace("-", ".") if x else ""
        txt += f" ({short(f)}~{short(t)})"
    return txt


def alarm_state(a):
    if not a.get("enabled", True):
        return "꺼짐"
    today = datetime.date.today().isoformat()
    if a["mode"] == "date" and a.get("date", "") < today:
        return "지남"
    if a["mode"] != "date" and a.get("to") and a["to"] < today:
        return "기간종료"
    return "켜짐"


def norm_alarm(a):
    """예전 형식(alert 키)을 새 형식으로 변환하고 빠진 값을 채움"""
    if "tts" not in a:
        al = a.get("alert", "both")
        a["beep"] = al in ("both", "popup")
        a["tts"] = al in ("both", "voice")
    a.setdefault("beep", True)
    a.setdefault("img", "")
    a.setdefault("sound", "")
    a.setdefault("enabled", True)
    return a


def load_config():
    data = {}
    try:
        with open(CONFIG_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception:
        data = {}
    data["alarms"] = [norm_alarm(a) for a in data.get("alarms", [])]
    data.setdefault("rate", 0)
    data["style"] = dict(DEFAULT_STYLE)      # 팝업 모양은 고정(설정 기능 삭제): 저장돼 있던 값은 무시
    ui = dict(DEFAULT_UI)
    ui.update(data.get("ui", {}))
    if str(ui.get("accent", "")).lower() == "#f08c00":      # 예전 기본 주황 → 연한 주황으로
        ui["accent"] = DEFAULT_UI["accent"]
    data["ui"] = ui
    cal = dict(DEFAULT_CAL)
    cal.update(data.get("cal", {}))
    data["cal"] = cal
    ot = dict(DEFAULT_OT)
    if isinstance(data.get("ot"), dict):
        ot.update(data["ot"])
    data["ot"] = ot
    pm = dict(DEFAULT_POMO)
    if isinstance(data.get("pomo"), dict):
        pm.update(data["pomo"])
    for k_, lo_, hi_ in (("work", 1, 180), ("brk", 1, 60), ("long", 0, 120), ("every", 0, 12)):
        try:
            pm[k_] = max(lo_, min(hi_, int(pm[k_])))
        except Exception:
            pm[k_] = DEFAULT_POMO[k_]
    pm["auto"] = bool(pm.get("auto", True))
    data["pomo"] = pm
    data.setdefault("voice", "")
    data["events"] = [norm_event(e) for e in data.get("events", []) if isinstance(e, dict)]
    cl = data.get("cloud") if isinstance(data.get("cloud"), dict) else {}
    for k in ("conf", "user"):
        if not isinstance(cl.get(k), dict):
            cl[k] = {}
    data["cloud"] = cl
    data["tomb"] = [t for t in data.get("tomb", []) if isinstance(t, dict) and "id" in t]
    return data


def save_config(data):
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print("저장 실패:", e)


# ================================================================ 자동 실행
RUN_KEY = r"Software\Microsoft\Windows\CurrentVersion\Run"


def _autostart_cmd():
    if getattr(sys, "frozen", False):
        return f'"{sys.executable}" --minimized'
    exe = sys.executable
    if exe.lower().endswith("python.exe"):
        exe = exe[:-10] + "pythonw.exe"
    return f'"{exe}" "{os.path.abspath(__file__)}" --minimized'


def get_autostart():
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY) as k:
            winreg.QueryValueEx(k, "RepeatAlarm")
        return True
    except Exception:
        return False


def set_autostart(on):
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY, 0, winreg.KEY_SET_VALUE) as k:
            if on:
                winreg.SetValueEx(k, "RepeatAlarm", 0, winreg.REG_SZ, _autostart_cmd())
            else:
                try:
                    winreg.DeleteValue(k, "RepeatAlarm")
                except FileNotFoundError:
                    pass
        return True
    except Exception as e:
        messagebox.showerror(APP_NAME, f"자동 실행 설정에 실패했습니다.\n{e}")
        return False


# ================================================================ 음성 / 소리
class Speaker:
    """PowerShell의 System.Speech로 한국어 음성을 읽어줍니다(추가 설치 불필요)."""

    PS = (
        "Add-Type -AssemblyName System.Speech;"
        "$s=New-Object System.Speech.Synthesis.SpeechSynthesizer;"
        "$v=$s.GetInstalledVoices()|Where-Object{$_.Enabled -and $_.VoiceInfo.Culture.Name -eq 'ko-KR'}|Select-Object -First 1;"
        "if($v){$s.SelectVoice($v.VoiceInfo.Name)};"
        "$s.Rate=[int]$env:ALARM_RATE;"
        "$s.Speak($env:ALARM_TEXT)"
    )

    def __init__(self):
        self.proc = None

    def speak(self, text, rate=0):
        self.stop()
        if os.name != "nt":
            return
        env = os.environ.copy()
        env["ALARM_TEXT"] = text
        env["ALARM_RATE"] = str(int(rate))
        try:
            self.proc = subprocess.Popen(
                ["powershell", "-NoProfile", "-NonInteractive", "-Command", self.PS],
                env=env, creationflags=0x08000000,  # CREATE_NO_WINDOW
            )
        except Exception as e:
            print("음성 실행 실패:", e)

    def stop(self):
        if self.proc and self.proc.poll() is None:
            try:
                self.proc.terminate()
            except Exception:
                pass
        self.proc = None


class AudioPlayer:
    """Windows MCI로 mp3/wav/wma 파일을 재생(추가 설치 불필요)"""
    ALIAS = "ra_audio"

    def _mci(self, cmd):
        if os.name != "nt":
            return 1, ""
        buf = ctypes.create_unicode_buffer(256)
        err = ctypes.windll.winmm.mciSendStringW(cmd, buf, 255, 0)
        return err, buf.value

    def play(self, path):
        self.stop()
        p = path.replace('"', "")
        err, _ = self._mci(f'open "{p}" alias {self.ALIAS}')
        if err:
            err, _ = self._mci(f'open "{p}" type mpegvideo alias {self.ALIAS}')
        if err:
            return False
        err, _ = self._mci(f"play {self.ALIAS}")
        return not err

    def is_playing(self):
        _, mode = self._mci(f"status {self.ALIAS} mode")
        return mode == "playing"

    def stop(self):
        self._mci(f"stop {self.ALIAS}")
        self._mci(f"close {self.ALIAS}")


def beep(root=None):
    def run():
        if winsound:
            for _ in range(3):
                winsound.Beep(880, 180)
                time.sleep(0.08)
        elif root:
            root.bell()
    threading.Thread(target=run, daemon=True).start()


# ================================================================ 이미지 / 글꼴
_RES = getattr(Image, "Resampling", Image) if HAS_PIL else None
_DEFAULT_IMG = None


def default_image():
    global _DEFAULT_IMG
    if _DEFAULT_IMG is None:
        _DEFAULT_IMG = Image.open(io.BytesIO(base64.b64decode(DEFAULT_IMG_B64))).convert("RGBA")
    return _DEFAULT_IMG.copy()


def fit_image(im, max_w, max_h, max_scale=1.5):
    r = min(max_w / im.width, max_h / im.height, max_scale)
    size = (max(1, int(im.width * r)), max(1, int(im.height * r)))
    return im.resize(size, _RES.LANCZOS)


def cover_rgba(im, w, h):
    r = max(w / im.width, h / im.height)
    im = im.resize((max(1, int(im.width * r)), max(1, int(im.height * r))), _RES.LANCZOS)
    x, y = (im.width - w) // 2, (im.height - h) // 2
    return im.crop((x, y, x + w, y + h))


def build_frames(path, max_w, max_h, anim, mode="area"):
    """(PIL 프레임 목록, 프레임별 지연(ms), 프레임별 상하 이동(px))
    path: 내 이미지 경로(없거나 못 읽으면 내장 캐릭터)
    mode: fit  = 주어진 영역에 맞춤(비율 유지, 영역보다 작은 그림은 확대)
          fill = 영역을 꽉 채움(넘치는 부분은 잘림)
          area = 영역 안에 맞춤(확대 제한, 내장 캐릭터 기본)"""
    max_w, max_h = max(40, int(max_w)), max(40, int(max_h))
    im, custom = None, False
    if path and os.path.isfile(path):
        try:
            src = Image.open(path)
            if getattr(src, "is_animated", False) and src.n_frames > 1:   # 움직이는 GIF는 그대로 재생
                frames, delays = [], []
                for i, fr in enumerate(ImageSequence.Iterator(src)):
                    if i >= 150:
                        break
                    fr = fr.convert("RGBA")
                    frames.append(cover_rgba(fr, max_w, max_h) if mode == "fill" else fit_image(fr, max_w, max_h, 8))
                    delays.append(max(30, int(fr.info.get("duration", 100))))
                return frames, delays, [0] * len(frames)
            im, custom = src.convert("RGBA"), True
        except Exception:
            im, custom = None, False
    if im is None:
        im = default_image()
    if custom and mode == "fill":
        return [cover_rgba(im, max_w, max_h)], [1000], [0]
    if custom and mode == "fit" and not anim:
        return [fit_image(im, max_w, max_h, 8)], [1000], [0]
    if custom:
        k, cap = (0.96, 8) if mode == "fit" else (0.92, 4)
        base = fit_image(im, max_w * k, max_h * k, cap)
    else:
        base = fit_image(im, max_w * 0.92, max_h * 0.92)
    if not anim:
        return [base], [1000], [0]
    # 살짝 숨쉬듯 늘었다 줄고, 통통 튀며, 좌우로 갸우뚱
    frames, bobs = [], []
    n = 28
    bw, bh = base.size
    for i in range(n):
        t = 2 * math.pi * i / n
        u = (1 - math.cos(t)) / 2
        sx, sy = 1.01 - 0.025 * u, 0.985 + 0.05 * u
        f = base.resize((max(1, int(bw * sx)), max(1, int(bh * sy))), _RES.BICUBIC)
        if not custom:   # 내장 캐릭터만 갸우뚱, 내 사진은 기울이지 않음
            f = f.rotate(2.0 * math.sin(t), resample=_RES.BICUBIC, expand=True)
        frames.append(f)
        bobs.append(-7 * u if not custom else -3 * u)
    return frames, [50] * n, bobs


def cover_image(path, w, h):
    im = Image.open(path).convert("RGB")
    r = max(w / im.width, h / im.height)
    im = im.resize((max(1, int(im.width * r)), max(1, int(im.height * r))), _RES.LANCZOS)
    x, y = (im.width - w) // 2, (im.height - h) // 2
    return im.crop((x, y, x + w, y + h))


def pick_font(root):
    try:
        fams = set(tkfont.families(root))
    except Exception:
        fams = set()
    for n in DEFAULT_FONT_ORDER:      # 한컴산뜻돋움 → 맑은 고딕 → 돋움체
        if n in fams:
            return n
    return "돋움체"


def register_font(path):
    """폰트 파일(.ttf/.otf)을 이 프로그램에서만 쓰도록 임시 등록"""
    if os.name != "nt" or not os.path.isfile(path):
        return False
    try:
        return bool(ctypes.windll.gdi32.AddFontResourceExW(path, 0x10, 0))
    except Exception:
        return False


def font_file_name(path):
    try:
        return ImageFont.truetype(path, 20).getname()[0]
    except Exception:
        return ""


def luminance(hexcolor):
    try:
        h = hexcolor.lstrip("#")
        r, g, b = int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)
        return 0.299 * r + 0.587 * g + 0.114 * b
    except Exception:
        return 0


def compute_pos(style, w, h, sw, sh):
    p, m, taskbar = style.get("pos", "가운데"), 30, 60
    if p == "가운데":
        x, y = (sw - w) // 2, (sh - h) // 2
    elif p == "화면 위쪽 가운데":
        x, y = (sw - w) // 2, m
    elif p == "왼쪽 위":
        x, y = m, m
    elif p == "오른쪽 위":
        x, y = sw - w - m, m
    elif p == "왼쪽 아래":
        x, y = m, sh - h - m - taskbar
    elif p == "오른쪽 아래":
        x, y = sw - w - m, sh - h - m - taskbar
    else:
        try:
            x, y = int(style.get("x", 100)), int(style.get("y", 100))
        except (TypeError, ValueError):
            x, y = 100, 100
    return max(0, min(x, sw - w)), max(0, min(y, sh - h))


# ================================================================ 팝업 창
class PopupWindow:
    OFFS = [(-2, 0), (2, 0), (0, -2), (0, 2), (2, 2)]

    def __init__(self, root, style, text, img_path="", on_snooze=None, on_dismiss=None, on_stop=None,
                 on_next=None):
        self.root, self.s = root, style
        self.on_next = on_next
        self.sig = (bool(on_snooze), bool(on_stop), bool(on_next))
        self.on_stop = on_stop
        self.on_dismiss, self.on_snooze = on_dismiss, on_snooze
        self.img_path = img_path
        self.anim_job = None
        self.img_id = None
        self.photos, self.delays, self.bobs = [], [], []
        self.fi = 0
        self.img_x = self.img_y = 0

        sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
        W = min(max(320, int(style["w"])), sw)
        H = min(max(240, int(style["h"])), sh)
        self.W, self.H = W, H

        win = self.win = tk.Toplevel(root)
        win.title("알람")
        win.resizable(False, False)
        win.attributes("-topmost", True)
        win.protocol("WM_DELETE_WINDOW", self.dismiss)
        cv = self.cv = tk.Canvas(win, width=W, height=H, highlightthickness=0, bg=style["bg"])
        cv.pack()

        self.bg_photo = None
        if HAS_PIL and style.get("bg_image") and os.path.isfile(style["bg_image"]):
            try:
                self.bg_photo = ImageTk.PhotoImage(cover_image(style["bg_image"], W, H))
                cv.create_image(0, 0, image=self.bg_photo, anchor="nw")
            except Exception:
                self.bg_photo = None

        fam = style.get("font") or pick_font(root)
        self.font = (fam, int(style["size"]), "bold" if style.get("bold") else "normal")
        fg = style["fg"]
        self.shadow_ids = []
        if style.get("shadow"):
            sc = "#000000" if luminance(fg) > 140 else "#ffffff"
            for _ in self.OFFS:
                self.shadow_ids.append(cv.create_text(0, 0, text=text, width=W - 40, anchor="n",
                                                      justify="center", font=self.font, fill=sc))
        self.text_id = cv.create_text(W / 2, 0, text=text, width=W - 40, anchor="n",
                                      justify="center", font=self.font, fill=fg)

        bfont = (fam, 12, "bold")
        if on_stop:
            bf = (fam, 10, "bold")
            bar = tk.Frame(cv, bg=style["bg"])
            specs = []
            if on_snooze:
                specs.append((f"{SNOOZE_MIN}분 후", "#e9ecef", "#212529", "#ced4da", self.snooze))
            specs.append(("확인", "#f6a53f", "white", "#e8890c", self.dismiss))
            if on_next:
                specs.append(("다음 시각 설정", "#1c7ed6", "white", "#1864ab", self.ask_next))
            specs.append(("오늘은 팝업 중지", "#868e96", "white", "#495057", self.stop_ot))
            btns = [tk.Button(bar, text=t, font=bf, relief="flat", bg=bg_, fg=fg_, padx=8,
                              activebackground=ab, activeforeground=fg_, command=cmd)
                    for t, bg_, fg_, ab, cmd in specs]
            for b in btns:
                b.pack(side="left", padx=3)
            bar.update_idletasks()
            if bar.winfo_reqwidth() > W - 16:       # 폭이 모자라면 두 줄로
                for b in btns:
                    b.pack_forget()
                for i, b in enumerate(btns):
                    b.grid(row=i // 2, column=i % 2, padx=3, pady=2, sticky="we")
                cv.create_window(W / 2, H - 8, window=bar, anchor="s")
            else:
                cv.create_window(W / 2, H - 30, window=bar)
        elif on_snooze:
            b1 = tk.Button(cv, text=f"{SNOOZE_MIN}분 후 다시", font=bfont, width=12, relief="flat",
                           bg="#e9ecef", activebackground="#ced4da", command=self.snooze)
            b2 = tk.Button(cv, text="확인", font=bfont, width=12, relief="flat", bg="#f6a53f", fg="white",
                           activebackground="#e8890c", activeforeground="white", command=self.dismiss)
            cv.create_window(W / 2 - 80, H - 30, window=b1)
            cv.create_window(W / 2 + 80, H - 30, window=b2)
        else:
            b2 = tk.Button(cv, text="닫기", font=bfont, width=14, relief="flat", bg="#f6a53f", fg="white",
                           activebackground="#e8890c", activeforeground="white", command=self.dismiss)
            cv.create_window(W / 2, H - 30, window=b2)

        self.layout()
        x, y = compute_pos(style, W, H, sw, sh)
        win.geometry(f"{W}x{H}+{x}+{y}")
        win.lift()
        try:
            win.focus_force()
        except Exception:
            pass

    # ---- 배치
    def layout(self):
        cv, W, H = self.cv, self.W, self.H
        bb = cv.bbox(self.text_id)
        th = (bb[3] - bb[1]) if bb else 0
        ty = max(H - 62 - th - 8, 70)
        cv.coords(self.text_id, W / 2, ty)
        for sid, (dx, dy) in zip(self.shadow_ids, self.OFFS):
            cv.coords(sid, W / 2 + dx, ty + dy)
        self.build_anim(W - 40, max(50, ty - 8 - 12), ty - 8)

    def build_anim(self, max_w, max_h, bottom):
        self.stop_anim()
        if self.img_id is not None:
            self.cv.delete(self.img_id)
            self.img_id = None
        if not HAS_PIL or not self.s.get("use_img", True):
            return
        path = self.img_path or self.s.get("img", "")
        custom = bool(path) and os.path.isfile(path)
        mode = self.s.get("img_fit", "fit") if custom else "area"
        if mode == "area":      # 글자 위쪽 영역, 바닥 기준
            box, anchor, self.img_x, self.img_y = (max_w, max_h), "s", self.W / 2, bottom
        else:                   # 팝업 전체 크기에 맞춤
            box, anchor, self.img_x, self.img_y = (self.W, self.H), "center", self.W / 2, self.H / 2
        try:
            frames, self.delays, self.bobs = build_frames(
                path if custom else "", box[0], box[1], self.s.get("anim", True), mode)
            self.photos = [ImageTk.PhotoImage(f) for f in frames]
        except Exception:
            return
        self.fi = 0
        self.img_id = self.cv.create_image(self.img_x, self.img_y, image=self.photos[0], anchor=anchor)
        ref = self.shadow_ids[0] if self.shadow_ids else self.text_id
        self.cv.tag_lower(self.img_id, ref)      # 글자 바로 아래(배경 위)에 둠
        if len(self.photos) > 1:
            self.anim_job = self.win.after(self.delays[0], self.step)

    def step(self):
        try:
            self.fi = (self.fi + 1) % len(self.photos)
            self.cv.itemconfig(self.img_id, image=self.photos[self.fi])
            self.cv.coords(self.img_id, self.img_x, self.img_y + self.bobs[self.fi])
            self.anim_job = self.win.after(self.delays[self.fi], self.step)
        except tk.TclError:
            self.anim_job = None

    def stop_anim(self):
        if self.anim_job is not None:
            try:
                self.win.after_cancel(self.anim_job)
            except Exception:
                pass
            self.anim_job = None

    # ---- 제어
    def alive(self):
        try:
            return bool(self.win.winfo_exists())
        except Exception:
            return False

    def stop_ot(self):
        self.close()
        if self.on_stop:
            self.on_stop()

    def ask_next(self):
        if self.on_next:
            self.on_next(self.win)

    def update_text(self, text):
        self.cv.itemconfig(self.text_id, text=text)
        for sid in self.shadow_ids:
            self.cv.itemconfig(sid, text=text)
        self.layout()
        self.win.lift()

    def lift(self):
        self.win.lift()

    def close(self):
        self.stop_anim()
        if self.alive():
            self.win.destroy()

    def dismiss(self):
        self.close()
        if self.on_dismiss:
            self.on_dismiss()

    def snooze(self):
        self.close()
        if self.on_snooze:
            self.on_snooze()


# ================================================================ 공통 위젯
def darker(hexcolor, k=0.85):
    try:
        h = hexcolor.lstrip("#")
        r, g, b = (int(h[i:i + 2], 16) for i in (0, 2, 4))
        return "#%02x%02x%02x" % (int(r * k), int(g * k), int(b * k))
    except Exception:
        return hexcolor


class ScrollFrame(ttk.Frame):
    """내용이 창보다 길면 세로 스크롤이 되는 프레임 (내용은 .inner 에 넣음)"""

    def __init__(self, parent, bg, frame_style="TFrame", height=None, fit_width=False, hscroll=False):
        super().__init__(parent, style=frame_style)
        self.fit_width = fit_width
        self.hscroll = hscroll
        self.hsb = None
        self.cv = tk.Canvas(self, highlightthickness=0, bd=0, bg=bg)
        if height:
            self.cv.configure(height=height)
        self.vsb = ttk.Scrollbar(self, orient="vertical", command=self.cv.yview)
        self.cv.configure(yscrollcommand=self.vsb.set)
        if hscroll:
            self.hsb = ttk.Scrollbar(self, orient="horizontal", command=self.cv.xview)
            self.cv.configure(xscrollcommand=self.hsb.set)
        self.vsb.pack(side="right", fill="y")
        self.cv.pack(side="left", fill="both", expand=True)
        self.inner = ttk.Frame(self.cv, style=frame_style)
        self.win_id = self.cv.create_window((0, 0), window=self.inner, anchor="nw")
        self.inner.bind("<Configure>", self._on_inner)
        self.cv.bind("<Configure>", self._on_cv)
        self._hshown = False
        self.cv.bind_all("<MouseWheel>", self._wheel, add="+")

    def _on_cv(self, e):
        self._fit_inner(e.width)

    def _fit_inner(self, cw=None):
        """가로 스크롤을 쓰는 경우: 내용이 창보다 넓으면 내용 너비를 유지하고 가로 스크롤바를 보인다"""
        cw = cw or self.cv.winfo_width()
        need = self.inner.winfo_reqwidth() if self.hscroll else 0
        self.cv.itemconfigure(self.win_id, width=max(cw, need))
        if self.hscroll and self.hsb is not None:
            show = need > cw + 1
            if show and not self._hshown:
                self.hsb.pack(side="bottom", fill="x", before=self.cv)
                self._hshown = True
            elif not show and self._hshown:
                self.hsb.pack_forget()
                self._hshown = False
                self.cv.xview_moveto(0)
        self.cv.configure(scrollregion=self.cv.bbox("all"))

    def _on_inner(self, _e):
        if self.hscroll:
            self._fit_inner()
        self.cv.configure(scrollregion=self.cv.bbox("all"))
        if self.fit_width:
            self.cv.configure(width=self.inner.winfo_reqwidth())

    def _wheel(self, e):
        try:
            w = self.cv.winfo_containing(e.x_root, e.y_root)
            if w is None or w.winfo_class() in ("Treeview", "Listbox", "TCombobox", "TSpinbox"):
                return
            p = w
            while p is not None and p is not self:
                p = p.master
            if p is None:
                return
            if e.state & 0x1 and self._hshown:        # Shift + 휠 = 가로 이동
                self.cv.xview_scroll(int(-e.delta / 120) * 3, "units")
                return
            if self.inner.winfo_reqheight() <= self.cv.winfo_height():
                return
            self.cv.yview_scroll(int(-e.delta / 120), "units")
        except tk.TclError:
            pass


# ================================================================ 꾸미기 설정창 (팝업 / 프로그램 화면)
class StyleDialog:
    def __init__(self, app):
        self.app = app
        s = dict(DEFAULT_STYLE)
        s.update(app.cfg["style"])
        u = dict(DEFAULT_UI)
        u.update(app.cfg["ui"])
        self.font_files = list(s.get("font_files", []))
        self.preview = None
        self.var, self.cbtn = {}, {}
        self.cb_fonts = []

        d = self.win = tk.Toplevel(app.root)
        d.title("꾸미기 설정")
        d.transient(app.root)
        d.configure(bg=app.theme["card"])
        sw, sh = d.winfo_screenwidth(), d.winfo_screenheight()

        for k, v in s.items():
            if k != "font_files":
                self.var["p_" + k] = self._mk(v)
        for k, v in u.items():
            self.var["u_" + k] = self._mk(v)
        self.v_fit = tk.StringVar(value=FIT_LABELS.get(s.get("img_fit", "fit"), FIT_LABELS["fit"]))
        for key in ("p_font", "u_font"):
            if not self.var[key].get():
                self.var[key].set(AUTO_FONT_LABEL)

        self.nb = nb = ttk.Notebook(d)
        nb.pack(fill="both", expand=True, padx=8, pady=(8, 0))
        h = max(300, min(620, sh - 260))
        sf2 = ScrollFrame(nb, app.theme["card"], height=h, fit_width=True)
        nb.add(sf2, text="  프로그램 화면  ")
        self._build_ui_tab(sf2.inner)
        self.refresh_fonts()

        f = ttk.Frame(d)
        f.pack(fill="x", padx=10, pady=10)
        ttk.Button(f, text="기본값으로", command=self.reset).pack(side="left")
        ttk.Button(f, text="닫기", command=self.close).pack(side="right")
        ttk.Button(f, text="저장 · 적용", style="Accent.TButton", command=self.save).pack(side="right", padx=6)

        d.protocol("WM_DELETE_WINDOW", self.close)
        d.update_idletasks()
        w = min(d.winfo_reqwidth() + 4, sw - 40)
        hh = min(d.winfo_reqheight() + 4, sh - 80)
        d.geometry(f"{w}x{hh}+{max(0, (sw - w) // 2)}+{max(0, (sh - hh) // 3)}")

    # ---- 변수/행 도우미
    @staticmethod
    def _mk(v):
        if isinstance(v, bool):
            return tk.BooleanVar(value=v)
        if isinstance(v, int):
            return tk.IntVar(value=v)
        return tk.StringVar(value=v)

    def _lf(self, parent, title):
        f = ttk.LabelFrame(parent, text=" " + title + " ", padding=8)
        f.pack(fill="x", padx=10, pady=6)
        return f

    def _color(self, parent, r, label, key, col=0):
        ttk.Label(parent, text=label).grid(row=r, column=col, sticky="w", padx=6, pady=4)
        b = tk.Button(parent, width=8, relief="groove", bg=self.var[key].get(), command=lambda k=key: self.pick(k))
        b.grid(row=r, column=col + 1, sticky="w")
        self.cbtn[key] = b

    def _file(self, parent, r, label, key, kind, clear="지움"):
        var = self.var[key]
        ttk.Label(parent, text=label).grid(row=r, column=0, sticky="w", padx=6, pady=4)
        ttk.Entry(parent, textvariable=var, width=36).grid(row=r, column=1, columnspan=3, sticky="we")
        ttk.Button(parent, text="선택", command=lambda: self.browse(var, kind)).grid(row=r, column=4, padx=3)
        ttk.Button(parent, text=clear, command=lambda: var.set("")).grid(row=r, column=5, padx=3)

    def _font_row(self, parent, key_font, key_size, row):
        ttk.Label(parent, text="글꼴").grid(row=row, column=0, sticky="w", padx=6, pady=4)
        cb = ttk.Combobox(parent, textvariable=self.var[key_font], width=28)
        cb.grid(row=row, column=1, columnspan=3, sticky="w")
        self.cb_fonts.append(cb)
        ttk.Button(parent, text="글꼴 파일 불러오기", command=lambda k=key_font: self.load_font_file(k)).grid(
            row=row, column=4, columnspan=2, padx=3)
        ttk.Label(parent, text="크기").grid(row=row + 1, column=0, sticky="w", padx=6, pady=4)
        ttk.Spinbox(parent, from_=9, to=90, width=5, textvariable=self.var[key_size]).grid(row=row + 1, column=1, sticky="w")

    # ---- 탭: 팝업
    def _build_popup_tab(self, p):
        v = self.var
        f = self._lf(p, "크기 · 위치")
        ttk.Label(f, text="너비").grid(row=0, column=0, padx=6, pady=4)
        ttk.Spinbox(f, from_=320, to=2400, increment=20, width=6, textvariable=v["p_w"]).grid(row=0, column=1)
        ttk.Label(f, text="높이").grid(row=0, column=2, padx=6)
        ttk.Spinbox(f, from_=240, to=1400, increment=20, width=6, textvariable=v["p_h"]).grid(row=0, column=3)
        ttk.Label(f, text="위치").grid(row=1, column=0, padx=6, pady=4)
        cb = ttk.Combobox(f, textvariable=v["p_pos"], values=POS_CHOICES, state="readonly", width=16)
        cb.grid(row=1, column=1, columnspan=2, sticky="w")
        ttk.Label(f, text="X").grid(row=1, column=3, sticky="e")
        self.sp_x = ttk.Spinbox(f, from_=0, to=5000, increment=10, width=6, textvariable=v["p_x"])
        self.sp_x.grid(row=1, column=4)
        ttk.Label(f, text="Y").grid(row=1, column=5, sticky="e")
        self.sp_y = ttk.Spinbox(f, from_=0, to=3000, increment=10, width=6, textvariable=v["p_y"])
        self.sp_y.grid(row=1, column=6, padx=(0, 6))
        cb.bind("<<ComboboxSelected>>", lambda e: self.toggle_xy())

        f = self._lf(p, "글꼴 · 글자색")
        self._font_row(f, "p_font", "p_size", 0)
        ttk.Checkbutton(f, text="굵게", variable=v["p_bold"]).grid(row=1, column=2)
        ttk.Checkbutton(f, text="글자 테두리(가독성)", variable=v["p_shadow"]).grid(row=1, column=3, columnspan=3, sticky="w")
        self._color(f, 2, "글자색", "p_fg")

        f = self._lf(p, "배경")
        self._color(f, 0, "배경색", "p_bg")
        self._file(f, 1, "배경 이미지", "p_bg_image", "img")

        f = self._lf(p, "팝업 이미지 (기본: 내장 캐릭터)")
        ttk.Checkbutton(f, text="이미지 표시", variable=v["p_use_img"]).grid(row=0, column=0, padx=6, pady=4)
        ttk.Checkbutton(f, text="살짝 움직이기 (GIF는 그대로 재생)", variable=v["p_anim"]).grid(
            row=0, column=1, columnspan=4, sticky="w")
        self._file(f, 1, "내 이미지", "p_img", "img", "기본으로")
        ttk.Label(f, text="내 이미지 맞춤").grid(row=2, column=0, sticky="w", padx=6, pady=4)
        ttk.Combobox(f, textvariable=self.v_fit, values=list(FIT_LABELS.values()), state="readonly",
                     width=32).grid(row=2, column=1, columnspan=4, sticky="w")

        f = self._lf(p, "알림 소리 파일 (비우면 기본 알림음)")
        self._file(f, 0, "mp3/wav 등", "p_sound", "audio")
        ttk.Button(f, text="▶ 재생", command=self.play_sound).grid(row=1, column=1, pady=4, sticky="w")
        ttk.Button(f, text="■ 정지", command=self.app.player.stop).grid(row=1, column=2, pady=4, sticky="w")

    # ---- 탭: 프로그램 화면
    def _build_ui_tab(self, p):
        v = self.var
        f = self._lf(p, "글꼴 · 글자 크기")
        self._font_row(f, "u_font", "u_size", 0)
        ttk.Label(f, text="※ '(자동 선택)'은 한컴산뜻돋움 → 맑은 고딕 → 돋움체 순서로 설치된 글꼴을 씁니다.\n※ 글자 크기를 키우면 버튼·표·입력칸도 함께 커집니다.",
                  foreground="#868e96", justify="left").grid(row=2, column=0, columnspan=6, sticky="w", padx=6)

        f = self._lf(p, "색상")
        self._color(f, 0, "글자색", "u_fg")
        self._color(f, 0, "포인트색(선택·버튼)", "u_accent", col=2)
        self._color(f, 1, "창 배경색", "u_bg")
        self._color(f, 1, "패널 배경색", "u_card", col=2)

        f = self._lf(p, "상단 시계 영역")
        self._color(f, 0, "배경색", "u_head_bg")
        self._color(f, 0, "글자색", "u_head_fg", col=2)
        self._file(f, 1, "배경 이미지", "u_head_img", "img")
        ttk.Checkbutton(f, text="캐릭터 표시", variable=v["u_head_mascot"]).grid(row=2, column=1, sticky="w")

    # ---- 동작
    def toggle_xy(self):
        st = "normal" if self.var["p_pos"].get() == "직접 지정" else "disabled"
        self.sp_x.config(state=st)
        self.sp_y.config(state=st)

    def refresh_fonts(self):
        try:
            fams = sorted({f for f in tkfont.families(self.win) if not f.startswith("@")})
        except Exception:
            fams = []
        top = [f for f in PREFERRED_FONTS if f in fams]
        vals = [AUTO_FONT_LABEL] + top + [f for f in fams if f not in top]
        for cb in self.cb_fonts:
            cb["values"] = vals

    def pick(self, key):
        c = colorchooser.askcolor(color=self.var[key].get(), parent=self.win)[1]
        if c:
            self.var[key].set(c)
            self.cbtn[key].config(bg=c)

    def browse(self, var, kind):
        if kind == "img":
            ft = [("이미지", "*.png *.jpg *.jpeg *.gif *.bmp *.webp"), ("모든 파일", "*.*")]
        else:
            ft = [("오디오", "*.mp3 *.wav *.wma *.mid"), ("모든 파일", "*.*")]
        p = filedialog.askopenfilename(parent=self.win, filetypes=ft)
        if p:
            var.set(p)

    def load_font_file(self, key):
        p = filedialog.askopenfilename(parent=self.win, title="글꼴 파일 선택",
                                       filetypes=[("글꼴", "*.ttf *.otf *.ttc"), ("모든 파일", "*.*")])
        if not p:
            return
        if not register_font(p):
            messagebox.showwarning(APP_NAME, "글꼴을 불러오지 못했습니다.", parent=self.win)
            return
        name = font_file_name(p)
        if p not in self.font_files:
            self.font_files.append(p)
        self.refresh_fonts()
        if name:
            self.var[key].set(name)
        else:
            messagebox.showinfo(APP_NAME, "글꼴은 등록했지만 이름을 알 수 없습니다.\n목록에서 직접 선택하세요.", parent=self.win)

    def play_sound(self):
        p = self.var["p_sound"].get().strip()
        if not p or not os.path.isfile(p):
            messagebox.showinfo(APP_NAME, "소리 파일을 먼저 선택하세요.", parent=self.win)
            return
        if not self.app.player.play(p):
            messagebox.showwarning(APP_NAME, "이 파일은 재생할 수 없습니다.", parent=self.win)

    def _num(self, key, lo, hi, default):
        try:
            return max(lo, min(hi, int(self.var[key].get())))
        except (tk.TclError, ValueError):
            return default

    def _font_val(self, key):
        f = self.var[key].get().strip()
        return "" if f in ("", AUTO_FONT_LABEL) else f

    def collect_popup(self):
        g = lambda k: self.var["p_" + k].get()
        return {
            "w": self._num("p_w", 320, 2400, 400), "h": self._num("p_h", 240, 1400, 300),
            "pos": g("pos"), "x": self._num("p_x", 0, 5000, 100), "y": self._num("p_y", 0, 3000, 100),
            "font": self._font_val("p_font"), "size": self._num("p_size", 9, 90, 22),
            "bold": g("bold"), "fg": g("fg"), "shadow": g("shadow"), "bg": g("bg"),
            "bg_image": g("bg_image").strip(), "use_img": g("use_img"), "img": g("img").strip(),
            "anim": g("anim"), "img_fit": FIT_CODES.get(self.v_fit.get(), "fit"),
            "sound": g("sound").strip(), "font_files": list(self.font_files),
        }

    def collect_ui(self):
        g = lambda k: self.var["u_" + k].get()
        return {
            "font": self._font_val("u_font"), "size": self._num("u_size", 9, 40, 12),
            "fg": g("fg"), "bg": g("bg"), "card": g("card"), "accent": g("accent"),
            "head_bg": g("head_bg"), "head_fg": g("head_fg"), "head_img": g("head_img").strip(),
            "head_mascot": g("head_mascot"),
        }

    def do_preview(self):
        if self.preview and self.preview.alive():
            self.preview.close()
        st = self.collect_popup()
        self.preview = PopupWindow(self.app.root, st, "회의 시작 10분 전입니다.\n(미리보기)", st["img"])

    def reset(self):
        if not messagebox.askyesno(APP_NAME, "프로그램 화면 설정을 기본값으로 되돌릴까요?", parent=self.win):
            return
        src, prefix = DEFAULT_UI, "u_"
        for k, val in src.items():
            if k == "font_files" or (prefix + k) not in self.var:
                continue
            self.var[prefix + k].set(AUTO_FONT_LABEL if k == "font" else val)
            if prefix + k in self.cbtn:
                self.cbtn[prefix + k].config(bg=val)

    def save(self):
        ui = self.collect_ui()
        if ui["head_img"] and not os.path.isfile(ui["head_img"]):
            messagebox.showwarning(APP_NAME, f"상단 배경 이미지를 찾을 수 없습니다.\n{ui['head_img']}", parent=self.win)
            return
        self.app.cfg["ui"] = ui
        save_config(self.app.cfg)
        self.app.apply_ui()
        self.win.lift()
        messagebox.showinfo(APP_NAME, "저장했습니다.\n프로그램 화면에 바로 적용됩니다.", parent=self.win)

    def close(self):
        if self.preview and self.preview.alive():
            self.preview.close()
        self.app.player.stop()
        self.app.style_dlg = None
        self.win.destroy()


# ================================================================ 날짜 선택(달력)
class DatePicker:
    HEAD = ["일", "월", "화", "수", "목", "금", "토"]

    def __init__(self, app, parent, current, on_pick):
        self.app, self.on_pick = app, on_pick
        try:
            cur = datetime.date.fromisoformat(normalize_date(current))
        except Exception:
            cur = None
        base = cur or datetime.date.today()
        self.sel, self.y, self.m = cur, base.year, base.month
        th = app.theme
        w = self.win = tk.Toplevel(parent)
        w.title("날짜 선택")
        w.transient(parent)
        w.resizable(False, False)
        w.configure(bg=th["card"])
        top = ttk.Frame(w)
        top.pack(fill="x", padx=10, pady=(10, 4))
        ttk.Button(top, text="◀", width=3, command=lambda: self.move(-1)).pack(side="left")
        self.lbl = ttk.Label(top, anchor="center", font=app.f_bold)
        self.lbl.pack(side="left", fill="x", expand=True)
        ttk.Button(top, text="▶", width=3, command=lambda: self.move(1)).pack(side="left")
        self.gf = ttk.Frame(w)
        self.gf.pack(padx=10, pady=4)
        bot = ttk.Frame(w)
        bot.pack(fill="x", padx=10, pady=(4, 10))
        ttk.Button(bot, text="오늘", command=lambda: self.pick(datetime.date.today())).pack(side="left")
        ttk.Button(bot, text="닫기", command=w.destroy).pack(side="right")
        self.draw()
        w.update_idletasks()
        sw, sh = w.winfo_screenwidth(), w.winfo_screenheight()
        x = max(0, min(parent.winfo_pointerx() - 60, sw - w.winfo_reqwidth() - 10))
        y = max(0, min(parent.winfo_pointery() + 10, sh - w.winfo_reqheight() - 50))
        w.geometry(f"+{x}+{y}")
        try:
            w.grab_set()
        except tk.TclError:
            pass

    def move(self, delta):
        m = self.m - 1 + delta
        self.y += m // 12
        self.m = m % 12 + 1
        self.draw()

    def draw(self):
        for c in self.gf.winfo_children():
            c.destroy()
        th, fam, size = self.app.theme, self.app.ui_family, self.app.ui_size
        self.lbl.config(text=f"{self.y}년 {self.m}월")
        for c, h in enumerate(self.HEAD):
            color = "#e03131" if c == 0 else "#1c7ed6" if c == 6 else th["fg"]
            tk.Label(self.gf, text=h, bg=th["card"], fg=color, font=(fam, size, "bold")).grid(row=0, column=c, pady=2)
        today = datetime.date.today()
        for r, week in enumerate(calendar.Calendar(firstweekday=6).monthdayscalendar(self.y, self.m), start=1):
            for c, day in enumerate(week):
                if not day:
                    continue
                d = datetime.date(self.y, self.m, day)
                bg, fg = ("#f1f3f5", "#e03131" if c == 0 else "#1c7ed6" if c == 6 else th["fg"])
                if d == today:
                    bg = "#fff3bf"
                if d == self.sel:
                    bg, fg = th["accent"], "#ffffff"
                tk.Button(self.gf, text=str(day), width=4, relief="flat", bg=bg, fg=fg, font=(fam, size),
                          activebackground=darker(bg, 0.9), command=lambda dd=d: self.pick(dd)
                          ).grid(row=r, column=c, padx=1, pady=1)

    def pick(self, d):
        self.on_pick(d.isoformat())
        self.win.destroy()


# ================================================================ 일정 / 달력 위젯
# 공휴일: 인사혁신처 월력요항 기준(2026~2027). '근로자의 날'은 관공서 공휴일이 아니라서 넣지 않았습니다.
# 이 표에 없는 날(2028년 이후, 임시공휴일 등)은 일정에서 "휴일로 표시"를 체크해 직접 추가할 수 있습니다.
HOLIDAYS = {
    "2026-01-01": "신정", "2026-02-16": "설날 연휴", "2026-02-17": "설날", "2026-02-18": "설날 연휴",
    "2026-03-01": "삼일절", "2026-03-02": "대체공휴일", "2026-05-05": "어린이날",
    "2026-05-24": "부처님오신날", "2026-05-25": "대체공휴일", "2026-06-03": "지방선거",
    "2026-06-06": "현충일", "2026-07-17": "제헌절", "2026-08-15": "광복절", "2026-08-17": "대체공휴일",
    "2026-09-24": "추석 연휴", "2026-09-25": "추석", "2026-09-26": "추석 연휴",
    "2026-10-03": "개천절", "2026-10-05": "대체공휴일", "2026-10-09": "한글날", "2026-12-25": "성탄절",
    "2027-01-01": "신정", "2027-02-06": "설날 연휴", "2027-02-07": "설날", "2027-02-08": "설날 연휴",
    "2027-02-09": "대체공휴일", "2027-03-01": "삼일절", "2027-05-05": "어린이날", "2027-05-13": "부처님오신날",
    "2027-06-06": "현충일", "2027-07-17": "제헌절", "2027-07-19": "대체공휴일", "2027-08-15": "광복절",
    "2027-08-16": "대체공휴일", "2027-09-14": "추석 연휴", "2027-09-15": "추석", "2027-09-16": "추석 연휴",
    "2027-10-03": "개천절", "2027-10-04": "대체공휴일", "2027-10-09": "한글날", "2027-10-11": "대체공휴일",
    "2027-12-25": "성탄절", "2027-12-27": "대체공휴일",
}

EVENT_COLORS = [("주황", "#f6a53f"), ("파랑", "#1c7ed6"), ("초록", "#2f9e44"),
                ("빨강", "#e03131"), ("보라", "#7048e8"), ("회색", "#868e96")]
EVENT_ALARMS = [("알람 없음", None), ("정시", 0), ("5분 전", 5), ("10분 전", 10),
                ("30분 전", 30), ("1시간 전", 60), ("1일 전", 1440)]
EVENT_REPEATS = [("반복 없음", "none"), ("매월", "monthly"), ("매년", "yearly")]
EVENT_KINDS = ["", "회의", "출장", "교육", "행사", "점검", "보고", "휴가", "민원", "기타"]
KEY_COLOR = "#010203"          # '배경만 투명' 방식에서 투명 처리되는 색


def _iso(s):
    return datetime.date.fromisoformat(s)


# ---- 기념일: (규칙, 이름, 분류)  규칙 = ("md",월,일) | ("nth",월,요일(0=월),몇째(-1=마지막)) | ("lunar",음력월,음력일)
# 24절기 양력일 (2023~2050, 천문 계산, 한국 표준시): 해마다 [YY + 24개 날짜(2자리)] — 소한부터 동지까지
TERMS_RAW = "23052004190621052006210621072308230823082408220722 24062004190520041905200521062207220722082307220721 25052003180520042005210521072207230723082307220721 26052004190520052005210621072307230723082307220722 27052004190621052006210621072308230823082408220722 28062004190520041905200521062207220722082307220621 29052003180520042005210521072207230723082307220721 30052004180520052005210521072307230723082307220722 31052004190621052006210621072308230823082308220722 32062004190520041905200521062207220722082307220621 33052003180520042005210521072207230723082307220721 34052004180520052005210521072307230723082307220722 35052004190621052006210621072308230823082307220722 36062004190520041905200521062207220722082307220621 37052003180520042005210521072207230723082307220721 38052004180520052005210521072307230723082307220722 39052004190621052006210621072308230823082307220722 40062004190520041905200521062207220722082307220621 41052003180520042005210521072207230723082307220721 42052004180520052005210521072307230723082307220722 43052004190621052005210621072307230823082307220722 44062004190520041905200521062207220722082307220621 45052003180520042005200521072207230722082307220721 46052004180520042005210521072307230723082307220722 47052004190621052005210621072307230823082307220722 48062004190520041905200521062207220722072307220621 49052003180520042005200521072207230722082307220721 50052004180520042005210521072207230723082307220722"
TERM_NAMES = "소한 대한 입춘 우수 경칩 춘분 청명 곡우 입하 소만 망종 하지 소서 대서 입추 처서 백로 추분 한로 상강 입동 소설 대설 동지".split()
_TERMS = {}


def term_days(y):
    """해당 연도의 24절기 날짜 리스트(없으면 None)"""
    if not _TERMS:
        for tok in TERMS_RAW.split():
            _TERMS[2000 + int(tok[:2])] = [int(tok[2 + 2 * i:4 + 2 * i]) for i in range(24)]
    return _TERMS.get(y)


def term_name(d):
    t = term_days(d.year)
    if t:
        i = d.month * 2 - 2
        for j in (i, i + 1):
            if t[j] == d.day:
                return TERM_NAMES[j]
    return ""


def bok_name(d):
    """초복·중복·말복 이름(해당 날이 아니면 ''). 하지 후 3·4번째 경일=초복·중복, 입추 후 첫 경일=말복"""
    if d.month not in (6, 7, 8):
        return ""
    t = term_days(d.year)
    if not t or ((d.toordinal() - 730120 + 4) % 10) != 6:     # 경일(庚日)이 아니면 아님
        return ""
    ha, ip = datetime.date(d.year, 6, t[11]), datetime.date(d.year, 8, t[14])
    if d >= ip:
        return "말복" if all(((ip + datetime.timedelta(k)).toordinal() - 730120 + 4) % 10 != 6 for k in range((d - ip).days)) else ""
    if d < ha:
        return ""
    n = sum(1 for k in range((d - ha).days + 1) if ((ha + datetime.timedelta(k)).toordinal() - 730120 + 4) % 10 == 6)
    return {3: "초복", 4: "중복"}.get(n, "")


ANNIV_CATS = {"gov": ("행정·법정기념일", "#2f9e44"), "wel": ("복지·보건·가정", "#1098ad"),
              "pri": ("민간 기념일(데이)", "#d6336c"), "sea": ("명절·세시풍속(음력)", "#7048e8"),
              "term": ("24절기", "#5c940d"), "bok": ("초복·중복·말복", "#e8590c")}
ANNIVS = [
    # 행정·법정
    (("md", 2, 28), "2·28민주운동 기념일", "gov"), (("md", 3, 8), "여성의 날", "gov"),
    (("md", 3, 15), "3·15의거 기념일", "gov"), (("md", 3, 22), "물의 날", "gov"),
    (("nth", 3, 4, 4), "서해수호의 날", "gov"), (("md", 4, 3), "제주4·3 추념일", "gov"),
    (("md", 4, 5), "식목일", "gov"), (("md", 4, 11), "임시정부수립 기념일", "gov"),
    (("md", 4, 19), "4·19혁명 기념일", "gov"), (("md", 4, 21), "과학의 날", "gov"),
    (("md", 4, 22), "지구의 날", "gov"), (("md", 4, 25), "법의 날", "gov"),
    (("md", 4, 28), "충무공 이순신 탄신일", "gov"), (("md", 5, 1), "근로자의 날", "gov"),
    (("md", 5, 10), "유권자의 날", "gov"), (("md", 5, 18), "5·18민주화운동 기념일", "gov"),
    (("md", 5, 19), "발명의 날", "gov"), (("md", 5, 25), "방재의 날", "gov"),
    (("md", 5, 31), "바다의 날", "gov"), (("md", 6, 5), "환경의 날", "gov"),
    (("md", 6, 9), "기록의 날", "gov"), (("md", 6, 10), "6·10민주항쟁 기념일", "gov"),
    (("md", 6, 25), "6·25전쟁일", "gov"), (("nth", 7, 2, 2), "정보보호의 날", "gov"),
    (("md", 8, 14), "일본군위안부 기림의 날", "gov"), (("md", 10, 1), "국군의 날", "gov"),
    (("md", 10, 21), "경찰의 날", "gov"), (("md", 10, 25), "독도의 날", "gov"),
    (("md", 10, 29), "지방자치의 날", "gov"), (("md", 11, 3), "학생독립운동 기념일", "gov"),
    (("md", 11, 9), "소방의 날", "gov"), (("md", 11, 11), "농업인의 날", "gov"),
    (("md", 11, 17), "순국선열의 날", "gov"), (("md", 12, 10), "인권의 날", "gov"),
    # 복지·보건·가정
    (("md", 4, 2), "자폐인식의 날", "wel"), (("md", 4, 7), "보건의 날", "wel"),
    (("md", 4, 20), "장애인의 날", "wel"), (("md", 5, 8), "어버이날", "wel"),
    (("md", 5, 11), "입양의 날", "wel"), (("md", 5, 15), "스승의 날", "wel"),
    (("nth", 5, 0, 3), "성년의 날", "wel"), (("md", 5, 21), "부부의 날", "wel"),
    (("md", 9, 7), "사회복지의 날", "wel"), (("md", 9, 10), "자살예방의 날", "wel"),
    (("nth", 9, 5, 3), "청년의 날", "wel"), (("md", 9, 21), "치매극복의 날", "wel"),
    (("md", 10, 2), "노인의 날", "wel"), (("md", 11, 19), "아동학대예방의 날", "wel"),
    (("md", 12, 5), "자원봉사자의 날", "wel"),
    # 민간
    (("md", 2, 14), "밸런타인데이", "pri"), (("md", 3, 3), "삼겹살데이", "pri"),
    (("md", 3, 14), "화이트데이", "pri"), (("md", 4, 14), "블랙데이", "pri"),
    (("md", 5, 14), "로즈데이", "pri"), (("md", 6, 14), "키스데이", "pri"),
    (("md", 7, 14), "실버데이", "pri"), (("md", 9, 14), "포토데이", "pri"),
    (("md", 10, 14), "와인데이", "pri"), (("md", 11, 11), "빼빼로데이", "pri"),
    (("md", 12, 24), "크리스마스 이브", "pri"), (("md", 12, 31), "송년(제야)", "pri"),
    # 음력 명절·세시
    (("lunar", 1, 15), "정월대보름", "sea"), (("lunar", 5, 5), "단오", "sea"),
    (("lunar", 6, 15), "유두", "sea"), (("lunar", 7, 7), "칠석", "sea"),
    (("lunar", 7, 15), "백중", "sea"), (("lunar", 9, 9), "중양절", "sea"),
]
_ANNIV_CACHE = {}

# 날짜 이름 → 간단한 설명 (일정 창에 표시)
DESC = {
    "신정": "양력 1월 1일, 새해 첫날.", "설날": "음력 1월 1일. 한 해를 시작하는 가장 큰 명절로 차례와 세배를 한다.",
    "삼일절": "1919년 3·1운동을 기념하는 국경일.", "대체공휴일": "공휴일이 주말·다른 공휴일과 겹칠 때 그 다음 평일을 쉬는 날.",
    "어린이날": "어린이의 인격을 존중하고 행복을 도모하는 날(5/5).", "부처님오신날": "음력 4월 8일, 석가모니 탄신을 기리는 날.",
    "지방선거": "전국동시지방선거일.", "현충일": "나라를 위해 희생한 순국선열·전몰장병을 추모하는 날(6/6).",
    "제헌절": "1948년 대한민국 헌법 제정·공포를 기념하는 날(7/17).", "광복절": "1945년 광복과 1948년 정부 수립을 기념하는 국경일(8/15).",
    "추석": "음력 8월 15일, 한 해 농사에 감사하며 차례를 지내는 큰 명절.", "개천절": "단군이 나라를 연 것을 기념하는 국경일(10/3).",
    "한글날": "훈민정음 반포를 기념하는 국경일(10/9).", "성탄절": "예수 그리스도의 탄생을 기념하는 날(12/25).",
    # 행정·법정
    "2·28민주운동 기념일": "1960년 2월 28일 대구 학생들이 부정선거 독재에 맞선 민주화운동을 기리는 날.",
    "여성의 날": "여성의 권리와 양성평등을 기념하는 세계 여성의 날(유엔 지정).",
    "3·15의거 기념일": "1960년 3·15 부정선거에 항거해 마산에서 일어난 의거를 기리는 날.",
    "물의 날": "물의 소중함을 알리는 유엔 지정 세계 물의 날.",
    "서해수호의 날": "제2연평해전·천안함 피격·연평도 포격 희생 장병을 기리는 날(3월 넷째 금요일).",
    "제주4·3 추념일": "제주4·3 사건 희생자와 유족을 추모하는 국가기념일.",
    "식목일": "나무를 심고 산림을 가꾸는 날(공휴일은 아님).",
    "임시정부수립 기념일": "1919년 4월 11일 대한민국임시정부 수립을 기념하는 날.",
    "4·19혁명 기념일": "1960년 4·19혁명의 민주 이념을 계승하는 날.",
    "과학의 날": "과학기술 진흥과 국민의 과학 의식을 높이기 위한 날.",
    "지구의 날": "환경 보호 실천을 다짐하는 날(1970년 시작).",
    "법의 날": "법의 존엄성과 준법정신을 높이기 위한 날.",
    "충무공 이순신 탄신일": "1545년 4월 28일 태어난 충무공 이순신 장군을 기리는 날.",
    "근로자의 날": "노동자의 노고와 권익을 기리는 날. 관공서는 정상 근무.",
    "유권자의 날": "선거의 중요성과 유권자의 권리·책임을 알리는 날.",
    "5·18민주화운동 기념일": "1980년 5·18 광주민주화운동을 기리는 국가기념일.",
    "발명의 날": "발명 의욕을 북돋우고 지식재산 의식을 높이기 위한 날.",
    "방재의 날": "재난 예방과 방재 의식을 높이기 위한 날.",
    "바다의 날": "해양의 중요성과 해양산업 발전을 기리는 날.",
    "환경의 날": "유엔이 정한 세계 환경의 날, 환경 보전 의식을 높이는 날.",
    "기록의 날": "세계 기록의 날. 기록물 관리의 중요성을 알리는 날(6/9).",
    "6·10민주항쟁 기념일": "1987년 6월 민주항쟁의 정신을 기리는 날.",
    "6·25전쟁일": "1950년 6월 25일 발발한 6·25전쟁을 기억하는 날.",
    "정보보호의 날": "정보보호 의식을 높이기 위한 날(7월 둘째 수요일).",
    "일본군위안부 기림의 날": "일본군 위안부 피해자를 기리고 인권 의식을 높이는 날.",
    "국군의 날": "국군의 위훈을 기리고 사기를 높이는 날(10/1).",
    "경찰의 날": "경찰의 노고를 격려하고 사기를 높이는 날.",
    "독도의 날": "독도가 우리 영토임을 알리는 날(10/25).",
    "지방자치의 날": "지방자치의 의미를 되새기고 주민 참여를 높이는 날.",
    "학생독립운동 기념일": "1929년 광주학생항일운동을 기리는 날.",
    "소방의 날": "119 숫자에 맞춘 소방의 날, 화재 예방과 소방관 노고를 기림.",
    "농업인의 날": "농업의 소중함을 알리는 날(11/11, 흙 土 = 十一).",
    "순국선열의 날": "1905년 을사늑약 체결을 기억하며 순국선열을 기리는 날.",
    "인권의 날": "1948년 세계인권선언을 기념하는 날.",
    # 복지·보건·가정
    "자폐인식의 날": "세계 자폐인의 날. 자폐성 장애에 대한 이해를 높이는 날.",
    "보건의 날": "세계보건기구(WHO) 창설을 기념하는 세계 보건의 날.",
    "장애인의 날": "장애인의 복지 증진과 인식 개선을 위한 법정기념일.",
    "어버이날": "부모님의 은혜에 감사하는 날(5/8). 카네이션을 단다.",
    "입양의 날": "입양을 장려하고 입양 가족을 격려하는 날(5/11).",
    "스승의 날": "스승의 은혜에 감사하는 날(5/15).",
    "성년의 날": "만 19세가 된 청년에게 성년의 책임을 일깨우는 날(5월 셋째 월요일).",
    "부부의 날": "부부 사랑을 다지는 날(5/21, 둘이 하나가 된다는 뜻).",
    "사회복지의 날": "사회복지의 중요성을 알리고 종사자를 격려하는 날(9/7).",
    "자살예방의 날": "세계 자살예방의 날. 생명 존중 문화를 만드는 날.",
    "청년의 날": "청년의 사회 참여와 권익을 기리는 날(9월 셋째 토요일).",
    "치매극복의 날": "세계 알츠하이머의 날. 치매 극복 의지를 다지는 날(9/21).",
    "노인의 날": "노인을 공경하고 복지를 증진하는 날(10/2).",
    "아동학대예방의 날": "아동학대 예방과 아동 권리를 알리는 날(11/19).",
    "자원봉사자의 날": "자원봉사자의 헌신을 기리는 날(12/5).",
    # 민간
    "밸런타인데이": "2월 14일, 연인·지인에게 초콜릿을 주며 마음을 전하는 날.",
    "삼겹살데이": "3월 3일(三三), 삼겹살을 먹는 날로 알려진 민간 기념일.",
    "화이트데이": "3월 14일, 밸런타인데이에 선물 받은 답례로 사탕을 주는 날.",
    "블랙데이": "4월 14일, 애인이 없는 사람이 짜장면을 먹는다는 민간 기념일.",
    "로즈데이": "5월 14일, 장미를 주고받는 날.", "키스데이": "6월 14일, 연인 사이의 기념일.",
    "실버데이": "7월 14일, 은제품을 선물하는 날.", "포토데이": "9월 14일, 사진을 찍어 간직하는 날.",
    "와인데이": "10월 14일, 와인을 나누는 날.", "빼빼로데이": "11월 11일, 빼빼로를 주고받는 날.",
    "크리스마스 이브": "12월 24일, 성탄절 전날.", "송년(제야)": "12월 31일, 한 해를 마무리하는 날.",
    # 음력 명절
    "정월대보름": "음력 1월 15일. 달맞이, 부럼 깨기, 오곡밥·나물을 먹는 날.",
    "단오": "음력 5월 5일. 창포물에 머리를 감고 씨름·그네뛰기를 하던 날.",
    "유두": "음력 6월 15일. 흐르는 물에 머리를 감아 액을 씻던 날.",
    "칠석": "음력 7월 7일. 견우와 직녀가 만난다는 날.",
    "백중": "음력 7월 15일. 농사일을 쉬고 음식을 나누던 날.",
    "중양절": "음력 9월 9일. 국화전을 먹고 높은 곳에 오르던 날.",
    # 24절기
    "소한": "작은 추위. 겨울 추위가 본격적으로 시작되는 때.", "대한": "큰 추위. 겨울의 마지막 절기.",
    "입춘": "봄이 시작되는 절기. 새해 복을 비는 입춘첩을 붙인다.", "우수": "눈이 녹아 비가 되는 때. 봄기운이 돈다.",
    "경칩": "겨울잠 자던 개구리가 깨어난다는 절기.", "춘분": "낮과 밤의 길이가 같아지는 봄의 한가운데.",
    "청명": "하늘이 맑고 밝아지는 때. 봄 농사 준비를 시작.", "곡우": "봄비가 내려 곡식을 기름지게 하는 때.",
    "입하": "여름이 시작되는 절기.", "소만": "만물이 자라 점차 가득 차는 때.",
    "망종": "곡식 씨 뿌리기에 알맞은 때. 보리를 베고 모내기를 한다.", "하지": "1년 중 낮이 가장 긴 날.",
    "소서": "작은 더위. 장마가 시작되는 무렵.", "대서": "큰 더위. 1년 중 가장 더운 때.",
    "입추": "가을이 시작되는 절기.", "처서": "더위가 물러가는 때. 아침저녁으로 선선해진다.",
    "백로": "풀잎에 흰 이슬이 맺히기 시작하는 때.", "추분": "낮과 밤의 길이가 같아지는 가을의 한가운데.",
    "한로": "찬 이슬이 맺히는 때. 단풍이 짙어진다.", "상강": "서리가 내리기 시작하는 때.",
    "입동": "겨울이 시작되는 절기. 김장을 준비한다.", "소설": "첫눈이 내리기 시작한다는 작은 눈의 절기.",
    "대설": "눈이 많이 내린다는 절기.", "동지": "1년 중 밤이 가장 긴 날. 팥죽을 먹는 풍습이 있다.",
    "초복": "삼복(초복·중복·말복)의 시작. 삼계탕 등으로 더위를 이겨내는 풍습.",
    "중복": "삼복 더위의 한가운데. 보양식을 먹는 풍습.", "말복": "삼복의 마지막 날. 더위가 꺾이기 시작하는 때.",
}


def _nth_weekday(y, m, wd, n):
    if n > 0:
        d = datetime.date(y, m, 1)
        d += datetime.timedelta((wd - d.weekday()) % 7 + 7 * (n - 1))
        return d
    last = datetime.date(y, m, calendar.monthrange(y, m)[1])
    return last - datetime.timedelta((last.weekday() - wd) % 7)


def anniv_list(d):
    """날짜 d의 기념일 [(이름, 분류코드)]"""
    key = d.toordinal()
    if key in _ANNIV_CACHE:
        return _ANNIV_CACHE[key]
    out, lun = [], None
    for rule, name, cat in ANNIVS:
        k = rule[0]
        if k == "md":
            ok = (d.month, d.day) == (rule[1], rule[2])
        elif k == "nth":
            ok = d.month == rule[1] and _nth_weekday(d.year, rule[1], rule[2], rule[3]) == d
        else:
            if lun is None:
                lun = lunar_of(d) or ()
            ok = bool(lun) and lun[2] is False and (lun[0], lun[1]) == (rule[1], rule[2])
        if ok and name != HOLIDAYS.get(d.isoformat()):
            out.append((name, cat))
    tn = term_name(d)
    if tn:
        out.append((tn, "term"))
    bn = bok_name(d)
    if bn:
        out.append((bn, "bok"))
    if len(_ANNIV_CACHE) > 4000:
        _ANNIV_CACHE.clear()
    _ANNIV_CACHE[key] = out
    return out


def norm_event(e):
    e.setdefault("id", int(time.time() * 1000))
    e.setdefault("title", "")
    e.setdefault("date", datetime.date.today().isoformat())
    e.setdefault("end", "")
    e.setdefault("time", "")
    e.setdefault("repeat", "none")
    e.setdefault("alarm", None)
    e.setdefault("color", 0)
    e.setdefault("memo", "")
    e.setdefault("holiday", False)
    e.setdefault("kind", "")
    e.setdefault("dept", "")
    e.setdefault("team", "")
    e.setdefault("upd", 0)
    return e


def event_starts(e, d):
    """일정 e가 날짜 d에 시작하는지 (반복 포함)"""
    try:
        s = _iso(e["date"])
    except Exception:
        return False
    if d < s:
        return False
    r = e.get("repeat", "none")
    if r == "monthly":
        return d.day == s.day
    if r == "yearly":
        return (d.month, d.day) == (s.month, s.day)
    return d == s


def event_on(e, d):
    """날짜 d의 달력 칸에 일정 e를 표시할지 (여러 날 일정 포함)"""
    if event_starts(e, d):
        return True
    if e.get("repeat", "none") == "none" and e.get("end"):
        try:
            return _iso(e["date"]) <= d <= _iso(e["end"])
        except Exception:
            return False
    return False


def alarm_text(off):
    for t, v in EVENT_ALARMS:
        if v == off:
            return t
    return ""


def event_fires(e, d):
    """날짜 d에 울릴 (자정부터 분, 알림 문구) 목록"""
    off = e.get("alarm")
    if off is None or not e.get("title"):
        return []
    base = hm_to_min(e.get("time") or "09:00")
    out = []
    for k in (0, 1):
        occ = d + datetime.timedelta(days=k)
        if event_starts(e, occ):
            fire = datetime.datetime.combine(occ, datetime.time(base // 60, base % 60)) \
                - datetime.timedelta(minutes=off)
            if fire.date() == d:
                lab = e["title"] if off == 0 else f'{e["title"]} ({alarm_text(off)})'
                out.append((fire.hour * 60 + fire.minute, lab))
    return out


def day_events(events, d):
    """날짜 d에 표시할 일정(시간 없는 것 먼저, 그다음 시간순)"""
    lst = [e for e in events if event_on(e, d)]
    lst.sort(key=lambda e: (e.get("time") or "", e.get("id", 0)))
    return lst


def holiday_name(app_events, d):
    """공휴일 이름(없으면 ''). 사용자가 '휴일로 표시'한 일정 제목도 포함"""
    iso = d.isoformat()
    if iso in HOLIDAYS:
        return HOLIDAYS[iso]
    for e in app_events:
        if e.get("holiday") and event_on(e, d):
            return e.get("title", "") or "휴일"
    return ""


# 음력 변환표 (2023~2049 음력해): 양력 설날(yymmdd) + 윤달(16진, 0=없음) + 달별 일수(0=29일, 1=30일)
LUNAR_RAW = "23012220101010110101 2402100010010110110 25012961010010101110 2602170101001010111 2702070010100100111 28012750110100100110 2902130110110010011 3002030010110101010 31012331010101101010 3202110100101101101 330131b0100101011101 3402190010010101110 3502080101001001101 36012861101001001101 3702150110100100101 3802040110101010010 39012451101101010100 4002120101101101010 4102010100101101101 42012220100101011011 4302100010010011011 44013071010010010111 4502170101001001011 4602060101100100101 47012651011010100101 4802140011011010100 4902020101011011010"
_LUNAR = []


def lunar_of(d):
    """양력 date → (음력월, 음력일, 윤달여부). 표 범위(2023~2049) 밖이면 None"""
    if not _LUNAR:
        for tok in LUNAR_RAW.split():
            st = datetime.date(2000 + int(tok[0:2]), int(tok[2:4]), int(tok[4:6]))
            _LUNAR.append((st, int(tok[6], 16), tok[7:]))
    lo = None
    for ent in _LUNAR:
        if ent[0] <= d:
            lo = ent
        else:
            break
    if lo is None:
        return None
    st, leapm, lens = lo
    off = (d - st).days
    mnum, i = 1, 0
    for i, ch in enumerate(lens):
        n = 30 if ch == "1" else 29
        is_leap = leapm and i == leapm      # 윤달은 leapm번째 달 바로 뒤
        if off < n:
            return (mnum, off + 1, bool(is_leap))
        off -= n
        if not (leapm and i == leapm - 1):
            mnum += 1
        else:
            pass
    return None


def lunar_text(d, short=False):
    r = lunar_of(d)
    if not r:
        return ""
    m, day, leap = r
    if short and day != 1:
        return str(day)
    return f"{'윤' if leap else ''}{m}.{day}"


def ot_session(app_events, dt, ot):
    """초과근무 구간이면 구간 키(문자열), 아니면 ''.
    휴일(주말·공휴일·'휴일로 표시'한 일정) = 하루 종일, 평일 = 업무시간(start~end) 밖"""
    d = dt.date()
    is_hol = d.weekday() >= 5 or bool(holiday_name(app_events, d))
    if is_hol:
        return d.isoformat() + "H" if ot.get("holiday", True) else ""
    m = dt.hour * 60 + dt.minute
    try:
        s_, e_ = hm_to_min(ot["start"]), hm_to_min(ot["end"])
    except Exception:
        s_, e_ = 540, 1080
    if m < s_:
        return d.isoformat() + "A"
    if m >= e_:
        return d.isoformat() + "P"
    return ""


def _mix(c1, c2, t):
    a = [int(c1[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(c2[i:i + 2], 16) for i in (1, 3, 5)]
    return "#%02x%02x%02x" % tuple(int(a[i] * (1 - t) + b[i] * t) for i in range(3))


def _lum(c):
    try:
        r, g, b = [int(c[i:i + 2], 16) for i in (1, 3, 5)]
        return 0.299 * r + 0.587 * g + 0.114 * b
    except Exception:
        return 0


class CalendarWidget:
    """바탕화면에 두는 월간 달력. 테두리 없는 창 하나를 Canvas로 그린다."""
    MIN_W, MIN_H = 540, 360

    def __init__(self, app):
        self.app = app
        t = datetime.date.today()
        self.y, self.m = t.year, t.month
        self.win = self.cv = None
        self.hits = []
        self.fonts = {}
        self.press = None
        self.last_day = t
        self.cur_alpha = None
        self.redraw_job = None
        self.settings_dlg = None
        self.bg_cache = None
        self.bg_photo = None
        self.view = "month"
        self.full = False
        self.pre_geo = None
        self.cursor = ""

    def _persist(self):
        """설정 저장 + (웹에 보낼 보기 설정이 바뀌었으면) 클라우드 동기화 예약"""
        save_config(self.app.cfg)
        try:
            cl = self.app.cloud
            if cl.ready() and json.dumps(cal_prefs_doc(self.app), sort_keys=True) != cl.prefs_sent:
                cl.request_sync(2)
        except Exception:
            pass

    @property
    def cal(self):
        return self.app.cfg["cal"]

    def alive(self):
        try:
            return self.win is not None and bool(self.win.winfo_exists())
        except tk.TclError:
            return False

    # ---------- 열기 / 닫기
    def show(self):
        try:
            self.app.cloud.touch()
        except Exception:
            pass
        if self.alive():
            self.win.deiconify()
            self.win.lift()
            return
        c = self.cal
        w = self.win = tk.Toplevel(self.app.root)
        w.overrideredirect(True)
        sw, sh = w.winfo_screenwidth(), w.winfo_screenheight()
        W = max(self.MIN_W, min(int(c["w"]), sw))
        H = max(self.MIN_H, min(int(c["h"]), sh))
        x, y = int(c["x"]), int(c["y"])
        if x < 0 or y < 0:
            x, y = max(0, sw - W - 30), 60
        x = max(-W + 100, min(x, sw - 100))
        y = max(0, min(y, sh - 60))
        w.geometry(f"{W}x{H}+{x}+{y}")
        self.cv = tk.Canvas(w, highlightthickness=0, bd=0)
        self.cv.pack(fill="both", expand=True)
        self.cv.bind("<Configure>", self._on_configure)
        self.cv.bind("<ButtonPress-1>", self._press)
        self.cv.bind("<B1-Motion>", self._motion)
        self.cv.bind("<ButtonRelease-1>", self._release)
        self.cv.bind("<Motion>", self._hover_cursor)
        self.full = False
        self.view = "year" if c.get("view") == "year" else "month"
        self.cv.bind("<MouseWheel>", lambda e: self.shift(-1 if e.delta > 0 else 1))
        self.cv.bind("<Button-4>", lambda e: self.shift(-1))
        self.cv.bind("<Button-5>", lambda e: self.shift(1))
        self.apply_trans()
        self.redraw()
        self.cal["show"] = True
        self._persist()
        self._keep()

    def hide(self):
        if self.alive():
            self.win.destroy()
        self.win = self.cv = None
        self.cal["show"] = False
        self._persist()

    def toggle(self):
        if self.alive():
            self.hide()
        else:
            self.show()

    # ---------- 투명도 / 맨 뒤 유지
    def apply_trans(self):
        if not self.alive():
            return
        c = self.cal
        key = c["mode"] == "key"
        try:
            self.win.attributes("-transparentcolor", KEY_COLOR if key else "")
        except tk.TclError:
            pass
        self.cur_alpha = None
        self._set_alpha(1.0 if key else c["alpha"] / 100.0)
        self.fonts = {}
        self.bg_cache = None
        self.redraw()

    def _set_alpha(self, a):
        a = max(0.2, min(1.0, a))
        if self.cur_alpha == a:
            return
        try:
            self.win.attributes("-alpha", a)
            self.cur_alpha = a
        except tk.TclError:
            pass

    def _to_bottom(self):
        try:
            u = ctypes.windll.user32
            hwnd = u.GetParent(self.win.winfo_id()) or self.win.winfo_id()
            u.SetWindowPos(hwnd, 1, 0, 0, 0, 0, 0x0001 | 0x0002 | 0x0010)   # HWND_BOTTOM, 크기·위치·활성화 유지
        except Exception:
            pass

    def _keep(self):
        if not self.alive():
            return
        c = self.cal
        if c.get("bottom"):
            self._to_bottom()
        if c["mode"] == "alpha":
            if c.get("hover"):
                try:
                    px, py = self.win.winfo_pointerx(), self.win.winfo_pointery()
                    inside = (self.win.winfo_rootx() <= px < self.win.winfo_rootx() + self.win.winfo_width()
                              and self.win.winfo_rooty() <= py < self.win.winfo_rooty() + self.win.winfo_height())
                except tk.TclError:
                    inside = False
                self._set_alpha(1.0 if inside else c["alpha"] / 100.0)
            else:
                self._set_alpha(c["alpha"] / 100.0)
        today = datetime.date.today()
        if today != self.last_day:          # 자정이 지나면 '오늘' 표시 갱신
            self.last_day = today
            self.redraw()
        self.win.after(250, self._keep)

    def refresh_theme(self):
        self.fonts = {}
        self.redraw()

    # ---------- 이동 / 크기 / 클릭
    def shift(self, delta):
        if self.view == "year":
            self.y += delta
            self.redraw()
            return
        m = self.m - 1 + delta
        self.y += m // 12
        self.m = m % 12 + 1
        self.redraw()

    def goto_today(self):
        t = datetime.date.today()
        self.y, self.m = t.year, t.month
        self.redraw()

    def evs_on(self, d):
        c = self.cal
        fk, fd, ft = c.get("f_kind", ""), c.get("f_dept", ""), c.get("f_team", "")
        out = day_events(self.app.events, d)
        if fk:
            out = [e for e in out if e.get("kind") == fk]
        if fd:
            out = [e for e in out if e.get("dept") == fd]
        if ft:
            out = [e for e in out if e.get("team") == ft]
        return out

    def filter_menu(self, which, x_root, y_root):
        key = {"fk": "f_kind", "fd": "f_dept", "ft": "f_team"}[which]
        evs = self.app.events
        if which == "fk":
            vals = [k_ for k_ in EVENT_KINDS if k_] + sorted({e.get("kind") for e in evs if e.get("kind")} - set(EVENT_KINDS))
        else:
            fld = "dept" if which == "fd" else "team"
            vals = sorted({e.get(fld) for e in evs if e.get(fld)})
        m = tk.Menu(self.win, tearoff=0)
        cur = self.cal.get(key, "")

        def pick(v):
            self.cal[key] = v
            self._persist()
            self.redraw()
        m.add_command(label=("● " if not cur else "   ") + "(전체)", command=lambda: pick(""))
        for v in vals:
            m.add_command(label=("● " if v == cur else "   ") + v, command=lambda v=v: pick(v))
        if not vals:
            m.add_command(label="   (등록된 항목이 없습니다)", state="disabled")
        try:
            m.tk_popup(x_root, y_root)
        finally:
            m.grab_release()

    def _hit_at(self, x, y):
        for (x0, y0, x1, y1, kind, data) in reversed(self.hits):
            if x0 <= x <= x1 and y0 <= y <= y1:
                return kind, data
        return None, None

    def _edge_zone(self, x, y):
        if self.cal.get("lock") or self.full or not self.alive():
            return ""
        W, H = self.cv.winfo_width(), self.cv.winfo_height()
        z = ""
        if y < 4:
            z += "n"
        elif y > H - 7:
            z += "s"
        if x < 6:
            z += "w"
        elif x > W - 7:
            z += "e"
        return z

    _CURSORS_NT = {"e": "size_we", "w": "size_we", "n": "size_ns", "s": "size_ns",
                   "se": "size_nw_se", "nw": "size_nw_se", "ne": "size_ne_sw", "sw": "size_ne_sw"}
    _CURSORS_X = {"e": "sb_h_double_arrow", "w": "sb_h_double_arrow", "n": "sb_v_double_arrow",
                  "s": "sb_v_double_arrow", "se": "bottom_right_corner", "nw": "top_left_corner",
                  "ne": "top_right_corner", "sw": "bottom_left_corner"}

    def _hover_cursor(self, ev):
        if self.press:
            return
        z = self._edge_zone(ev.x, ev.y)
        cur = (self._CURSORS_NT if os.name == "nt" else self._CURSORS_X).get(z, "")
        if cur != self.cursor:
            try:
                self.cv.config(cursor=cur)
                self.cursor = cur
            except tk.TclError:
                pass

    def toggle_full(self):
        if not self.alive():
            return
        if self.full:
            g = self.pre_geo or (100, 60, self.MIN_W, self.MIN_H)
            self.win.geometry(f"{g[2]}x{g[3]}+{g[0]}+{g[1]}")
            self.full = False
        else:
            self.win.update_idletasks()
            self.pre_geo = (self.win.winfo_x(), self.win.winfo_y(), self.win.winfo_width(), self.win.winfo_height())
            sw, sh = self.win.winfo_screenwidth(), self.win.winfo_screenheight()
            self.win.geometry(f"{sw}x{sh}+0+0")
            self.full = True
            self.win.lift()
        self.redraw()

    def set_view(self, v):
        self.view = v
        self.cal["view"] = v
        self._persist()
        self.redraw()

    def _press(self, ev):
        z = self._edge_zone(ev.x, ev.y)
        if z:
            self.press = {"kind": "edge", "data": z, "rx": ev.x_root, "ry": ev.y_root, "moved": False,
                          "x": self.win.winfo_x(), "y": self.win.winfo_y(),
                          "w": self.win.winfo_width(), "h": self.win.winfo_height()}
            return
        kind, data = self._hit_at(ev.x, ev.y)
        self.press = {"kind": kind, "data": data, "rx": ev.x_root, "ry": ev.y_root, "moved": False,
                      "x": self.win.winfo_x(), "y": self.win.winfo_y(),
                      "w": self.win.winfo_width(), "h": self.win.winfo_height()}

    def _motion(self, ev):
        p = self.press
        if not p:
            return
        dx, dy = ev.x_root - p["rx"], ev.y_root - p["ry"]
        if abs(dx) + abs(dy) > 4:
            p["moved"] = True
        if not p["moved"] or self.cal.get("lock"):
            return
        if p["kind"] == "edge":
            z, nw, nh, nx, ny = p["data"], p["w"], p["h"], p["x"], p["y"]
            if "e" in z:
                nw = max(self.MIN_W, p["w"] + dx)
            if "s" in z:
                nh = max(self.MIN_H, p["h"] + dy)
            if "w" in z:
                nw = max(self.MIN_W, p["w"] - dx)
                nx = p["x"] + p["w"] - nw
            if "n" in z:
                nh = max(self.MIN_H, p["h"] - dy)
                ny = p["y"] + p["h"] - nh
            self.win.geometry(f"{nw}x{nh}+{nx}+{ny}")
        elif p["kind"] == "drag":
            if self.full:
                return
            self.win.geometry(f'+{p["x"] + dx}+{p["y"] + dy}')
        elif p["kind"] == "grip":
            nw, nh = max(self.MIN_W, p["w"] + dx), max(self.MIN_H, p["h"] + dy)
            self.win.geometry(f'{nw}x{nh}')

    def _release(self, ev):
        p, self.press = self.press, None
        if not p:
            return
        if p["moved"]:
            if not self.cal.get("lock") and not self.full and p["kind"] in ("drag", "grip", "edge"):
                self.win.update_idletasks()
                self.cal.update(x=self.win.winfo_x(), y=self.win.winfo_y(),
                                w=self.win.winfo_width(), h=self.win.winfo_height())
                self._persist()
            return
        k, d = p["kind"], p["data"]
        if k == "prev":
            self.shift(-1)
        elif k == "next":
            self.shift(1)
        elif k == "today":
            self.goto_today()
        elif k == "gear":
            self.open_settings()
        elif k == "full":
            self.toggle_full()
        elif k == "lunar":
            self.cal["lunar"] = not self.cal.get("lunar", True)
            self._persist()
            self.redraw()
        elif k in ("fk", "fd", "ft"):
            self.filter_menu(k, ev.x_root, ev.y_root)
        elif k == "pomo_go":
            self.app.pomo_toggle()
        elif k == "pomo_skip":
            self.app.pomo_skip()
        elif k == "pomo_reset":
            self.app.pomo_reset()
        elif k == "pomo_set":
            self.app.open_pomo_settings()
        elif k == "view":
            self.set_view("month" if self.view == "year" else "year")
        elif k == "ymonth":
            self.y, self.m = d
            self.set_view("month")
        elif k == "yday":
            self.app.open_events(d)
        elif k == "close":
            self.hide()
        elif k == "day":
            self.app.open_events(d)
        elif k == "event":
            self.app.open_events(d[1], d[0])

    def pomo_update(self, txt, n, ratio):
        """매초: 뽀모도로 글자·진행 막대만 갱신 (달력 전체를 다시 그리지 않음)"""
        cv = self.cv
        if cv is None or not getattr(self, "_pomo_geo", None):
            return
        try:
            cv.itemconfigure("pomo_t", text=txt)
            cv.itemconfigure("pomo_c", text=f"오늘 {n}회")
            x0, y0, x1, y1 = self._pomo_geo
            cv.coords("pomo_p", 0, y0, x1 * ratio, y1)
        except tk.TclError:
            pass

    def _on_configure(self, _e=None):
        if self.redraw_job:
            try:
                self.win.after_cancel(self.redraw_job)
            except tk.TclError:
                pass
        self.redraw_job = self.win.after(30, self.redraw)

    # ---------- 그리기
    def font(self, px, bold=False):
        key = (px, bold)
        if key not in self.fonts:
            self.fonts[key] = tkfont.Font(root=self.win, family=self.cal.get("font") or self.app.ui_family, size=-px,
                                          weight="bold" if bold else "normal")
        return self.fonts[key]

    def _fit(self, text, font, maxw):
        if maxw <= 0:
            return ""
        if font.measure(text) <= maxw:
            return text
        while text and font.measure(text + "…") > maxw:
            text = text[:-1]
        return text + "…" if text else ""

    def _txt(self, x, y, text, font, color, anchor="nw", shadow=False):
        cv = self.cv
        if shadow:
            sc = "#ffffff" if _lum(color) < 140 else "#000000"
            for ox, oy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
                cv.create_text(x + ox, y + oy, text=text, font=font, fill=sc, anchor=anchor)
        return cv.create_text(x, y, text=text, font=font, fill=color, anchor=anchor)

    def _draw_bg_image(self, W, H):
        path = self.cal.get("img", "")
        if not (path and HAS_PIL and os.path.isfile(path)):
            return False
        veil = max(0, min(90, int(self.cal.get("veil", 40))))
        ck = (path, W, H, veil)
        if not self.bg_cache or self.bg_cache[0] != ck:
            try:
                im = Image.open(path).convert("RGBA")
                im = cover_rgba(im, W, H)
                if veil:
                    im = Image.alpha_composite(im, Image.new("RGBA", im.size, (255, 255, 255, int(255 * veil / 100))))
                self.bg_cache = (ck, ImageTk.PhotoImage(im))
            except Exception:
                self.bg_cache = None
                return False
        self.bg_photo = self.bg_cache[1]
        self.cv.create_image(0, 0, image=self.bg_photo, anchor="nw")
        return True

    def redraw(self):
        self.redraw_job = None
        if not self.alive():
            return
        cv, app, c = self.cv, self.app, self.cal
        th = dict(app.theme)
        if c.get("bg"):
            th["card"], th["bg"] = c["bg"], _mix(c["bg"], "#808080", 0.1)
        for k_ in ("fg", "head_bg", "head_fg", "accent"):
            if c.get(k_):
                th[k_] = c[k_]
        key = c["mode"] == "key"
        W, H = cv.winfo_width(), cv.winfo_height()
        if W < 60 or H < 60:
            return
        cv.delete("all")
        self.hits = []
        cv.configure(bg=KEY_COLOR if key else th["card"])
        has_img = self._draw_bg_image(W, H)
        shade = key or has_img          # 투명/그림 위에서는 글자에 테두리를 둬서 읽기 쉽게
        sc = max(0.6, min(1.8, c.get("fscale", 100) / 100.0))
        fg, acc = th["fg"], th["accent"]
        grid = "#ced4da" if not key else _mix(fg, "#ffffff", 0.35)
        RED, BLUE, DIM = "#e03131", "#1c7ed6", "#adb5bd"

        tb = max(42, int(app.ui_size * 3.5))
        hfont = self.font(max(18, int(tb * 0.58)), True)
        bfont = self.font(max(11, int(tb * 0.36)))
        cv.create_rectangle(0, 0, W, tb, fill=th["head_bg"], outline=th["head_bg"])
        self.hits.append((0, 0, W, tb, "drag", None))

        def button(x0, x1, text, kind):
            cv.create_rectangle(x0, 5, x1, tb - 5, fill=_mix(th["head_bg"], "#ffffff", 0.45), outline=acc)
            cv.create_text((x0 + x1) / 2, tb / 2, text=text, font=bfont, fill=th["head_fg"])
            self.hits.append((x0, 5, x1, tb - 5, kind, None))

        bw = tb - 4
        button(6, 6 + bw, "◀", "prev")
        button(10 + bw, 10 + 2 * bw, "▶", "next")
        rx = W - 6
        vtxt = "월간" if self.view == "year" else "연간"
        for text, kind, wid in (("✕", "close", bw), ("❐" if self.full else "⛶", "full", bw), ("⚙", "gear", bw),
                                (vtxt, "view", int(bw * 1.5)), ("오늘", "today", int(bw * 1.5))):
            button(rx - wid, rx, text, kind)
            rx -= wid + 4
        ttl = f"{self.y}년" if self.view == "year" else f"{self.y}년 {self.m}월"
        cv.create_text((14 + 2 * bw + rx) / 2, tb / 2, text=ttl, font=hfont, fill=th["head_fg"])
        # ---- 둘째 줄: 음력 체크 + 유형/부서/팀 선택
        fr = max(32, int(tb * 0.8))
        cv.create_rectangle(0, tb, W, tb + fr, fill=_mix(th["head_bg"], "#ffffff", 0.35), outline=th["head_bg"])
        self.hits.append((0, tb, W, tb + fr, "drag", None))
        sfont = self.font(max(13, int(fr * 0.46)))
        bx = 8
        on = self.cal.get("lunar", True)
        cb = fr * 0.5
        cv.create_rectangle(bx, tb + fr / 2 - cb / 2, bx + cb, tb + fr / 2 + cb / 2, fill="#ffffff", outline=acc, width=2)
        if on:
            cv.create_text(bx + cb / 2, tb + fr / 2, text="✔", font=self.font(int(cb * 0.85), True), fill=acc)
        cv.create_text(bx + cb + 5, tb + fr / 2, text="음력", font=sfont, fill=th["head_fg"], anchor="w")
        lw_ = bx + cb + 5 + sfont.measure("음력") + 6
        self.hits.append((bx - 2, tb, lw_, tb + fr, "lunar", None))
        fx = lw_ + 10
        for lab, key_, hk in (("유형", "f_kind", "fk"), ("부서", "f_dept", "fd"), ("팀", "f_team", "ft")):
            v = self.cal.get(key_, "")
            txt = f"{lab}: {v or '전체'} ▾"
            wd = sfont.measure(txt) + 18
            if fx + wd > W - 6:
                break
            cv.create_rectangle(fx, tb + 4, fx + wd, tb + fr - 4, fill=acc if v else _mix(th["head_bg"], "#ffffff", 0.7),
                                outline=acc)
            cv.create_text(fx + wd / 2, tb + fr / 2, text=txt, font=sfont, fill="#ffffff" if v else th["head_fg"])
            self.hits.append((fx, tb + 4, fx + wd, tb + fr - 4, hk, None))
            fx += wd + 6
        # 우측: 프로그램 아이콘 + 이름 (자리가 있을 때만)
        try:
            isz = int(fr - 8)
            nfont = self.font(max(12, int(fr * 0.42)), True)
            nw = nfont.measure(APP_NAME)
            if fx + isz + 10 + nw + 12 <= W - 6:
                self._nm_icon = ImageTk.PhotoImage(app_icon_image(isz))
                cv.create_image(W - 8 - nw - 6, tb + fr / 2, image=self._nm_icon, anchor="e")
                cv.create_text(W - 8, tb + fr / 2, text=APP_NAME, font=nfont, fill=th["head_fg"], anchor="e")
            elif fx + isz + 12 <= W - 6:
                self._nm_icon = ImageTk.PhotoImage(app_icon_image(isz))
                cv.create_image(W - 8, tb + fr / 2, image=self._nm_icon, anchor="e")
        except Exception:
            pass
        # ---- 셋째 줄: 뽀모도로 (줄은 달력 테마 색, 제목만 노란 표지. 시간 + 설정/초기화/건너뛰기/시작이 한 줄에 모두 보이도록 글자 크기를 맞춤)
        pr = max(30, int(fr * 0.95))
        py0 = tb + fr
        pbg, pline, ptxt = _mix(th["head_bg"], "#ffffff", 0.6), th["head_bg"], th["head_fg"]
        cv.create_rectangle(0, py0, W, py0 + pr, fill=pbg, outline=pline)
        self.hits.append((0, py0, W, py0 + pr, "drag", None))
        pm = app.pomo
        txt, cnt = app.pomo_text()
        pcol = {"work": "#e67700", "brk": "#2f9e44", "long": "#1c7ed6"}[pm["phase"]]
        labs = [("설정", "pomo_set"), ("초기화", "pomo_reset"), ("건너뛰기", "pomo_skip"),
                ("일시정지" if pm["run"] else "시작", "pomo_go")]
        wide = max(f"{nm}  88:88  (멈춤)" for nm in POMO_NAMES.values())
        pb_, sb_ = max(13, int(pr * 0.46)), max(12, int(pr * 0.44))
        while True:
            pfont, sm_ = self.font(pb_, True), self.font(sb_)
            need = 10 + pfont.measure(wide) + 12 + sum(sm_.measure(l) + 16 + 4 for l, _k in labs)
            if need <= W or sb_ <= 9:
                break
            pb_, sb_ = max(10, pb_ - 1), sb_ - 1
        tx0 = 10
        tfont = self.font(sb_, True)
        if need + tfont.measure("뽀모도로") + 30 <= W:       # 제목만 노란 표지로 (줄 배경은 그대로)
            tw_ = tfont.measure("뽀모도로") + 16
            cv.create_rectangle(8, py0 + 5, 8 + tw_, py0 + pr - 6, fill="#ffe066", outline="#f08c00")
            cv.create_text(8 + tw_ / 2, py0 + pr / 2 - 1, text="뽀모도로", font=tfont, fill="#5f3b00")
            tx0 = 8 + tw_ + 10
        self._pomo_txt = cv.create_text(tx0, py0 + pr / 2 - 1, text=txt, font=pfont, fill=pcol, anchor="w", tags=("pomo_t",))
        bx1 = W - 6
        for lab, kind in reversed(labs):          # 오른쪽부터 [시작][건너뛰기][초기화][설정] 순으로 배치
            bw2 = sm_.measure(lab) + 16
            cv.create_rectangle(bx1 - bw2, py0 + 4, bx1, py0 + pr - 5, fill="#ffffff" if kind != "pomo_go" else pcol,
                                outline=pcol, width=2 if kind == "pomo_go" else 1)
            cv.create_text(bx1 - bw2 / 2, py0 + pr / 2 - 1, text=lab, font=sm_,
                           fill="#ffffff" if kind == "pomo_go" else ptxt)
            self.hits.append((bx1 - bw2, py0 + 4, bx1, py0 + pr - 4, kind, None))
            bx1 -= bw2 + 4
        self._pomo_cnt = cv.create_text(tx0 + pfont.measure(wide) + 4, py0 + pr / 2 - 1,
                                        text=f"오늘 {cnt}회", font=sm_, fill=ptxt, anchor="w", tags=("pomo_c",))
        if bx1 - 4 < cv.bbox(self._pomo_cnt)[2]:
            cv.delete(self._pomo_cnt)
        self._pomo_geo = (0, py0 + pr - 4, W, py0 + pr)
        cv.create_rectangle(0, py0 + pr - 4, W, py0 + pr, fill=_mix(pbg, "#808080", 0.15), outline="")
        cv.create_rectangle(0, py0 + pr - 4, W * app.pomo_ratio(), py0 + pr, fill=pcol, outline="", tags=("pomo_p",))
        tb = py0 + pr          # 이후 달력 본문은 이 아래에서 시작
        if self.view == "year":
            self._draw_year(th, W, H, tb, sc, key, has_img, shade, grid)
            self._finish(W, H, acc)
            return

        weeks = calendar.Calendar(firstweekday=6).monthdatescalendar(self.y, self.m)
        rows = len(weeks)
        gy0 = tb
        gh = H - gy0 - 12
        cw = W / 7.0
        wk_h = max(20, int(gh / (rows + 1) * 0.55))
        ch = (gh - wk_h) / rows
        dn = max(10, min(40, int(min(ch * 0.2, 26) * sc)))
        ev = max(9, min(30, int(min(dn * 0.82, 20 * sc))))
        fd, fdb = self.font(dn), self.font(dn, True)
        fe, fs = self.font(ev), self.font(max(9, ev - 1))

        for i, name in enumerate(("일", "월", "화", "수", "목", "금", "토")):
            x0 = i * cw
            col = RED if i == 0 else BLUE if i == 6 else fg
            if not shade:
                cv.create_rectangle(x0, gy0, x0 + cw, gy0 + wk_h, fill=th["bg"], outline=grid)
            elif has_img and not key:
                cv.create_rectangle(x0, gy0, x0 + cw, gy0 + wk_h, outline=grid)
            self._txt(x0 + cw / 2, gy0 + wk_h / 2, name, fdb, col, "center", shade)
        gy0 += wk_h

        today = datetime.date.today()
        for r, week in enumerate(weeks):
            for ci, d in enumerate(week):
                x0, y0 = ci * cw, gy0 + r * ch
                x1, y1 = x0 + cw, y0 + ch
                inm = d.month == self.m
                hname = holiday_name(app.events, d) if c.get("holidays", True) else ""
                if key:
                    cv.create_rectangle(x0, y0, x1, y1, outline=grid, fill="")
                    cv.create_rectangle(x0 + 1, y0 + 1, x1 - 1, y0 + dn + 9,
                                        fill=th["card"] if inm else th["bg"], outline="")
                elif has_img:
                    cv.create_rectangle(x0, y0, x1, y1, outline=grid, fill="")
                else:
                    cv.create_rectangle(x0, y0, x1, y1, outline=grid, fill=th["card"] if inm else th["bg"])
                self.hits.append((x0, y0, x1, y1, "day", d))
                col = RED if (ci == 0 or hname) else BLUE if ci == 6 else fg
                if not inm:
                    col = _mix(col, "#ffffff", 0.55) if not shade else DIM
                nx, ny = x0 + 6, y0 + 4
                if d == today:
                    wnum = fdb.measure(str(d.day))
                    cv.create_oval(nx - 4, ny - 2, nx + wnum + 4, ny + dn + 6, fill=acc, outline=acc)
                    self._txt(nx, ny, str(d.day), fdb, "#ffffff")
                else:
                    self._txt(nx, ny, str(d.day), fd, col, "nw", shade and inm)
                    wnum = fd.measure(str(d.day))
                lw = 0
                if c.get("lunar", True) and cw > 64:
                    lt = lunar_text(d, short=cw < 100)
                    if lt:
                        lcol = _mix(fg, "#ffffff", 0.45) if inm else DIM
                        self._txt(x1 - 5, ny + 3, lt, fs, lcol, "ne", shade and inm)
                        lw = fs.measure(lt) + 8
                if hname and cw > 80:
                    t = self._fit(hname, fs, x1 - (nx + wnum + 10) - 4 - lw)
                    if t:
                        self._txt(nx + wnum + 10, ny + 2, t, fs, RED if inm else _mix(RED, "#ffffff", 0.55),
                                  "nw", shade and inm)
                evs = self.evs_on(d)
                ystart = y0 + dn + 12
                an = [(n_, cat) for n_, cat in anniv_list(d) if c.get("anniv", {}).get(cat, True)]
                if an and (y1 - ystart) > (ev + 6) * 2 + fs.metrics("linespace") + 4 and cw > 70:
                    txt_ = " · ".join(n_ for n_, _ in an)
                    acol = ANNIV_CATS[an[0][1]][1]
                    self._txt(x0 + 6, ystart - 2, self._fit(txt_, fs, cw - 12), fs, acol if inm else DIM, "nw", shade and inm)
                    ystart += fs.metrics("linespace") + 1
                chip_h = ev + 6
                room = int((y1 - 3 - ystart) / (chip_h + 2))
                if room <= 0 or not evs:
                    continue
                shown = evs if len(evs) <= room else evs[:max(room - 1, 0)]
                yy = ystart
                for e in shown:
                    colr = EVENT_COLORS[e.get("color", 0) % len(EVENT_COLORS)][1]
                    label = (e["time"] + " " if e.get("time") else "") + (f'[{e["kind"]}] ' if e.get("kind") else "") + e.get("title", "")
                    cv.create_rectangle(x0 + 3, yy, x1 - 3, yy + chip_h, fill=colr, outline=colr)
                    cv.create_text(x0 + 7, yy + chip_h / 2, text=self._fit(label, fe, cw - 14), font=fe,
                                   fill="#ffffff", anchor="w")
                    self.hits.append((x0 + 3, yy, x1 - 3, yy + chip_h, "event", (e["id"], d)))
                    yy += chip_h + 2
                if len(evs) > len(shown):
                    more = f"+{len(evs) - len(shown)}개 더"
                    cv.create_rectangle(x0 + 3, yy, x1 - 3, yy + chip_h, fill=th["card"], outline=grid)
                    cv.create_text(x0 + 7, yy + chip_h / 2, text=more, font=fs, fill=fg, anchor="w")

        self._finish(W, H, acc)

    def _finish(self, W, H, acc):
        cv = self.cv
        if not self.full:           # 우측 하단 크기 조절 손잡이
            cv.create_polygon(W - 2, H - 16, W - 2, H - 2, W - 16, H - 2, fill=acc, outline=acc)
            self.hits.append((W - 20, H - 20, W, H, "grip", None))
        cv.create_rectangle(1, 1, W - 1, H - 1, outline=acc, width=2)

    def _draw_year(self, th, W, H, tb, sc, key, has_img, shade, grid):
        cv, app, c = self.cv, self.app, self.cal
        fg, acc = th["fg"], th["accent"]
        RED, BLUE, DIM = "#e03131", "#1c7ed6", "#adb5bd"
        area_h = H - tb - 10
        best = None
        for cols, rows in ((4, 3), (3, 4), (6, 2), (2, 6)):
            a = (W / cols) / (area_h / rows)
            sc_ = abs(math.log(a / 1.05))
            if best is None or sc_ < best[0]:
                best = (sc_, cols, rows)
        _, cols, rows = best
        mw, mh = W / cols, area_h / rows
        today = datetime.date.today()
        tfs = max(11, min(26, int(min(mh * 0.1, mw * 0.11) * sc)))
        ft = self.font(tfs, True)
        for mi in range(12):
            r_, c_ = divmod(mi, cols)
            x0, y0 = c_ * mw + 5, tb + 5 + r_ * mh
            x1, y1 = x0 + mw - 10, y0 + mh - 8
            mon = mi + 1
            if not shade:
                cv.create_rectangle(x0, y0, x1, y1, fill=th["card"], outline=grid)
            else:
                cv.create_rectangle(x0, y0, x1, y1, outline=grid)
            is_now = (self.y == today.year and mon == today.month)
            title_h = tfs + 10
            self._txt(x0 + 8, y0 + 4, f"{mon}월", ft, acc if is_now else fg, "nw", shade)
            self.hits.append((x0, y0, x1, y0 + title_h, "ymonth", (self.y, mon)))
            cw_ = (x1 - x0 - 8) / 7.0
            dfs = max(8, min(22, int(min(cw_ * 0.55, (y1 - y0 - title_h) / 8.5) * sc)))
            fd, fdb = self.font(dfs), self.font(dfs, True)
            dow_h = dfs + 6
            for i, nm in enumerate("일월화수목금토"):
                self._txt(x0 + 4 + i * cw_ + cw_ / 2, y0 + title_h + dow_h / 2, nm, fd,
                          RED if i == 0 else BLUE if i == 6 else _mix(fg, "#ffffff", 0.35), "center", shade)
            weeks = calendar.Calendar(firstweekday=6).monthdatescalendar(self.y, mon)
            rh = (y1 - y0 - title_h - dow_h - 4) / 6.0
            for wi, week in enumerate(weeks):
                for ci, d in enumerate(week):
                    if d.month != mon:
                        continue
                    cx = x0 + 4 + ci * cw_ + cw_ / 2
                    cy = y0 + title_h + dow_h + wi * rh + rh / 2
                    hname = holiday_name(app.events, d) if c.get("holidays", True) else ""
                    col = RED if (ci == 0 or hname) else BLUE if ci == 6 else fg
                    if d == today:
                        rr = min(cw_, rh) * 0.5
                        cv.create_oval(cx - rr, cy - rr, cx + rr, cy + rr, fill=acc, outline=acc)
                        cv.create_text(cx, cy, text=str(d.day), font=fdb, fill="#ffffff")
                    else:
                        self._txt(cx, cy, str(d.day), fd, col, "center", shade)
                    if self.evs_on(d):
                        cv.create_oval(cx - 2, cy + dfs * 0.62, cx + 2, cy + dfs * 0.62 + 4, fill=acc, outline=acc)
                    self.hits.append((cx - cw_ / 2, cy - rh / 2, cx + cw_ / 2, cy + rh / 2, "yday", d))

    # ---------- 설정
    def open_settings(self):
        if not self.alive():
            self.show()
        if self.settings_dlg is not None:
            try:
                if self.settings_dlg.winfo_exists():
                    self.settings_dlg.lift()
                    return
            except tk.TclError:
                pass
        app, c = self.app, self.cal
        d = self.settings_dlg = tk.Toplevel(app.root)
        d.title("달력 위젯 설정")
        d.configure(bg=app.theme["bg"])
        d.resizable(False, False)
        v_mode = tk.StringVar(value=c["mode"])
        v_alpha = tk.IntVar(value=int(c["alpha"]))
        v_hover = tk.BooleanVar(value=c.get("hover", True))
        v_lock = tk.BooleanVar(value=c.get("lock", False))
        v_bottom = tk.BooleanVar(value=c.get("bottom", False))
        v_hol = tk.BooleanVar(value=c.get("holidays", True))
        v_lun = tk.BooleanVar(value=c.get("lunar", True))
        an_cfg = c.setdefault("anniv", {})
        v_an = {k_: tk.BooleanVar(value=an_cfg.get(k_, True)) for k_ in ANNIV_CATS}
        v_fk = tk.StringVar(value=c.get("f_kind", "") or "(전체)")
        v_fd = tk.StringVar(value=c.get("f_dept", "") or "(전체)")
        v_ft = tk.StringVar(value=c.get("f_team", "") or "(전체)")
        SAME = "(프로그램 글꼴과 같게)"
        v_font = tk.StringVar(value=c.get("font") or SAME)
        v_fscale = tk.IntVar(value=int(c.get("fscale", 100)))
        v_veil = tk.IntVar(value=int(c.get("veil", 40)))
        v_img = tk.StringVar(value=c.get("img", ""))

        def apply(*_):
            c.update(mode=v_mode.get(), alpha=int(v_alpha.get()), hover=v_hover.get(), lock=v_lock.get(),
                     bottom=v_bottom.get(), holidays=v_hol.get(), lunar=v_lun.get(),
                     f_kind="" if v_fk.get() == "(전체)" else v_fk.get(), f_dept="" if v_fd.get() == "(전체)" else v_fd.get(),
                     f_team="" if v_ft.get() == "(전체)" else v_ft.get(),
                     anniv={k_: v.get() for k_, v in v_an.items()},
                     font="" if v_font.get() == SAME else v_font.get(), fscale=int(v_fscale.get()),
                     veil=int(v_veil.get()), img=v_img.get().strip())
            self._persist()
            self.apply_trans()

        _sh = d.winfo_screenheight()
        ttk.Button(d, text="닫기", command=d.destroy).pack(side="bottom", anchor="e", padx=12, pady=8)
        sfr = ScrollFrame(d, app.theme["bg"], height=max(300, min(780, _sh - 170)), fit_width=True)
        sfr.pack(side="top", fill="both", expand=True)
        f = ttk.Frame(sfr.inner, padding=14)
        f.pack(fill="both", expand=True)
        ttk.Label(f, text="투명 방식", style="TLabel").grid(row=0, column=0, sticky="w")
        ttk.Radiobutton(f, text="전체 반투명 (글씨도 함께 흐려짐)", value="alpha", variable=v_mode,
                        command=apply).grid(row=1, column=0, columnspan=2, sticky="w", padx=10)
        ttk.Radiobutton(f, text="배경만 투명 (글씨·일정은 선명)", value="key", variable=v_mode,
                        command=apply).grid(row=2, column=0, columnspan=2, sticky="w", padx=10)
        ttk.Label(f, text="불투명도(%)  ← 작을수록 아이콘이 잘 보임").grid(row=3, column=0, sticky="w", pady=(10, 0))
        tk.Scale(f, from_=20, to=100, orient="horizontal", length=240, variable=v_alpha, command=apply,
                 bg=app.theme["bg"], fg=app.theme["fg"], troughcolor="#ced4da", highlightthickness=0, bd=0,
                 font=(app.ui_family, app.ui_size)).grid(row=4, column=0, columnspan=2, sticky="w")
        for r, (txt, var) in enumerate((
                ("마우스를 올리면 선명하게 (전체 반투명일 때)", v_hover),
                ("위치·크기 고정 (실수로 옮기지 않게)", v_lock),
                ("항상 다른 창 뒤에 두기", v_bottom),
                ("공휴일 표시", v_hol),
                ("음력 표시 (월간 달력 칸에 작게)", v_lun)), start=5):
            ttk.Checkbutton(f, text=txt, variable=var, command=apply).grid(row=r, column=0, columnspan=2,
                                                                            sticky="w", pady=(6 if r == 5 else 2, 0))
        af_ = ttk.LabelFrame(f, text=" 기념일 표시 / 일정 필터 ", padding=8)
        af_.grid(row=10, column=0, columnspan=2, sticky="we", pady=(10, 0))
        for i_, (k_, (nm_, col_)) in enumerate(ANNIV_CATS.items()):
            ttk.Checkbutton(af_, text=nm_, variable=v_an[k_], command=apply).grid(row=i_ // 2, column=i_ % 2, sticky="w", padx=4)
        ttk.Label(af_, text="유형만").grid(row=3, column=0, sticky="e", pady=(6, 0))
        cbk = ttk.Combobox(af_, textvariable=v_fk, values=["(전체)"] + [k_ for k_ in EVENT_KINDS if k_], state="readonly", width=10)
        cbk.grid(row=3, column=1, sticky="w", pady=(6, 0))
        cbk.bind("<<ComboboxSelected>>", apply)
        ttk.Label(af_, text="부서만").grid(row=4, column=0, sticky="e", pady=(4, 0))
        cbd = ttk.Combobox(af_, textvariable=v_fd, state="readonly", width=14,
                           values=["(전체)"] + sorted({e_.get("dept") for e_ in app.events if e_.get("dept")}))
        cbd.grid(row=4, column=1, sticky="w", pady=(4, 0))
        cbd.bind("<<ComboboxSelected>>", apply)
        ttk.Label(af_, text="팀만").grid(row=5, column=0, sticky="e", pady=(4, 0))
        cbt = ttk.Combobox(af_, textvariable=v_ft, state="readonly", width=14,
                           values=["(전체)"] + sorted({e_.get("team") for e_ in app.events if e_.get("team")}))
        cbt.grid(row=5, column=1, sticky="w", pady=(4, 0))
        cbt.bind("<<ComboboxSelected>>", apply)
        ttk.Label(af_, text="※ 달력 위쪽 줄에서도 바로 고를 수 있습니다.", foreground="#868e96").grid(
            row=6, column=0, columnspan=2, sticky="w", pady=(4, 0))
        look = ttk.LabelFrame(f, text=" 달력 모양 ", padding=8)
        look.grid(row=11, column=0, columnspan=2, sticky="we", pady=(12, 0))
        ttk.Label(look, text="글꼴").grid(row=0, column=0, sticky="w")
        try:
            fams = sorted({x for x in tkfont.families(app.root) if not x.startswith("@")})
        except Exception:
            fams = []
        cb = ttk.Combobox(look, textvariable=v_font, values=[SAME] + fams, state="readonly", width=26)
        cb.grid(row=0, column=1, sticky="w", padx=6)
        cb.bind("<<ComboboxSelected>>", apply)
        ttk.Label(look, text="글자 크기(%)").grid(row=1, column=0, sticky="w", pady=(6, 0))
        tk.Scale(look, from_=70, to=160, orient="horizontal", length=200, variable=v_fscale, command=apply,
                 bg=app.theme["bg"], fg=app.theme["fg"], troughcolor="#ced4da", highlightthickness=0, bd=0,
                 font=(app.ui_family, app.ui_size)).grid(row=1, column=1, sticky="w", padx=6)
        cr = ttk.Frame(look)
        cr.grid(row=2, column=0, columnspan=2, sticky="w", pady=(6, 0))

        def pick_color(key_, label):
            cur = c.get(key_) or {"fg": app.theme["fg"], "bg": app.theme["card"], "head_bg": app.theme["head_bg"],
                                  "head_fg": app.theme["head_fg"], "accent": app.theme["accent"]}[key_]
            r_ = colorchooser.askcolor(color=cur, parent=d, title=label)
            if r_ and r_[1]:
                c[key_] = r_[1]
                apply()

        for key_, label in (("fg", "글자색"), ("bg", "배경색"), ("head_bg", "제목줄색"),
                            ("head_fg", "제목줄 글자색"), ("accent", "강조색")):
            ttk.Button(cr, text=label, command=lambda k=key_, l=label: pick_color(k, l)).pack(side="left", padx=(0, 4))

        def reset_colors():
            for k_ in ("fg", "bg", "head_bg", "head_fg", "accent"):
                c[k_] = ""
            apply()
        ttk.Button(cr, text="색 초기화", command=reset_colors).pack(side="left", padx=(8, 0))
        ttk.Label(look, text="배경 이미지").grid(row=3, column=0, sticky="w", pady=(8, 0))
        ir = ttk.Frame(look)
        ir.grid(row=3, column=1, sticky="we", padx=6, pady=(8, 0))
        ttk.Entry(ir, textvariable=v_img, width=22).pack(side="left")

        def browse_img():
            pth = filedialog.askopenfilename(parent=d, title="달력 배경 이미지",
                                             filetypes=[("이미지", "*.png *.jpg *.jpeg *.bmp *.gif *.webp"), ("모든 파일", "*.*")])
            if pth:
                v_img.set(pth)
                apply()
        ttk.Button(ir, text="선택", command=browse_img).pack(side="left", padx=3)
        ttk.Button(ir, text="지움", command=lambda: (v_img.set(""), apply())).pack(side="left")
        ttk.Label(look, text="이미지 흐리게(%)").grid(row=4, column=0, sticky="w")
        tk.Scale(look, from_=0, to=90, orient="horizontal", length=200, variable=v_veil, command=apply,
                 bg=app.theme["bg"], fg=app.theme["fg"], troughcolor="#ced4da", highlightthickness=0, bd=0,
                 font=(app.ui_family, app.ui_size)).grid(row=4, column=1, sticky="w", padx=6)

        ttk.Label(f, text="※ '배경만 투명'에서는 칸의 빈 곳을 누르면 뒤의 바탕화면 아이콘이 눌립니다.\n"
                          "   날짜 숫자나 일정 막대를 눌러 주세요.\n"
                          "※ 제목줄을 끌어 옮기고, 가장자리·모서리를 끌어 크기를 바꿉니다.\n"
                          "   ⛶ 버튼 = 전체 화면(다시 누르면 복귀), 연간/월간 버튼 = 보기 전환.",
                  foreground="#868e96", justify="left").grid(row=12, column=0, columnspan=2, sticky="w", pady=(10, 0))
        ttk.Button(f, text="닫기", command=d.destroy).grid(row=13, column=1, sticky="e", pady=(10, 0))
        d.update_idletasks()
        sw, sh = d.winfo_screenwidth(), d.winfo_screenheight()
        d.geometry(f"+{max(0, min(self.win.winfo_x() + 40, sw - d.winfo_reqwidth() - 10))}"
                   f"+{max(0, min(self.win.winfo_y() + 50, sh - d.winfo_reqheight() - 60))}")


class EventDialog:
    """하루의 일정 목록 + 추가/수정/삭제 창"""

    def __init__(self, app, d, select_id=None):
        self.app, self.d = app, d
        old = getattr(app, "ev_dlg", None)
        if old is not None:
            try:
                old.win.destroy()
            except Exception:
                pass
        app.ev_dlg = self
        th = app.theme
        w = self.win = tk.Toplevel(app.root)
        w.configure(bg=th["bg"])
        w.resizable(False, False)
        self.ids = []
        self.cur = None
        self.unlocked = set()        # 이 창에서 '잠금 해제'한 일정 번호
        self.v_title = tk.StringVar()
        self.v_date = tk.StringVar()
        self.v_end = tk.StringVar()
        self.v_timeon = tk.BooleanVar(value=False)
        self.v_h, self.v_m = tk.StringVar(value="09"), tk.StringVar(value="00")
        self.v_rep = tk.StringVar(value="none")
        self.v_alarm = tk.StringVar(value=EVENT_ALARMS[0][0])
        self.v_color = tk.StringVar(value=EVENT_COLORS[0][0])
        self.v_memo = tk.StringVar()
        self.v_hol = tk.BooleanVar(value=False)
        self.v_kind, self.v_dept, self.v_team = tk.StringVar(), tk.StringVar(), tk.StringVar()

        f = ttk.Frame(w, padding=12)
        f.pack(fill="both", expand=True)
        self.lbl = ttk.Label(f, font=app.f_bold)
        self.lbl.pack(anchor="w")
        self.lbl_hol = ttk.Label(f, foreground="#e03131")
        self.lbl_hol.pack(anchor="w")
        self.lbl_lock = ttk.Label(f, foreground="#e03131")
        self.lbl_an = ttk.Label(f, foreground="#495057", wraplength=520, justify="left")
        self.lbl_an.pack(anchor="w")
        lf = ttk.Frame(f)
        lf.pack(fill="x", pady=(6, 8))
        self.lb = tk.Listbox(lf, height=5, activestyle="none", exportselection=False,
                             font=(app.ui_family, app.ui_size), bg=th["card"], fg=th["fg"],
                             selectbackground=th["accent"], selectforeground="#ffffff",
                             relief="solid", bd=1, highlightthickness=0)
        self.lb.pack(side="left", fill="x", expand=True)
        sb = ttk.Scrollbar(lf, command=self.lb.yview)
        sb.pack(side="left", fill="y")
        self.lb.config(yscrollcommand=sb.set)
        self.lb.bind("<<ListboxSelect>>", self.on_select)

        self.lbl_lock.pack(anchor="w")
        form = ttk.LabelFrame(f, text=" 일정 추가 / 수정 ", padding=10)
        form.pack(fill="x")
        form.columnconfigure(1, weight=1)
        r = 0
        ttk.Label(form, text="제목").grid(row=r, column=0, sticky="w")
        ttk.Entry(form, textvariable=self.v_title, width=34).grid(row=r, column=1, columnspan=2, sticky="we", pady=2)
        r += 1
        ttk.Label(form, text="날짜").grid(row=r, column=0, sticky="w")
        df = ttk.Frame(form)
        df.grid(row=r, column=1, columnspan=2, sticky="w", pady=2)
        ttk.Entry(df, textvariable=self.v_date, width=12).pack(side="left")
        ttk.Button(df, text="달력", command=lambda: self.pick(self.v_date)).pack(side="left", padx=4)
        ttk.Label(df, text="  끝나는 날(선택)").pack(side="left")
        ttk.Entry(df, textvariable=self.v_end, width=12).pack(side="left", padx=4)
        ttk.Button(df, text="달력", command=lambda: self.pick(self.v_end)).pack(side="left")
        r += 1
        ttk.Label(form, text="시간").grid(row=r, column=0, sticky="w")
        tf = ttk.Frame(form)
        tf.grid(row=r, column=1, columnspan=2, sticky="w", pady=2)
        ttk.Checkbutton(tf, text="시간 지정", variable=self.v_timeon).pack(side="left")
        app._hm(tf, self.v_h, self.v_m)
        r += 1
        ttk.Label(form, text="반복").grid(row=r, column=0, sticky="w")
        rf = ttk.Frame(form)
        rf.grid(row=r, column=1, columnspan=2, sticky="w", pady=2)
        for t, v in EVENT_REPEATS:
            ttk.Radiobutton(rf, text=t, value=v, variable=self.v_rep).pack(side="left", padx=(0, 10))
        r += 1
        ttk.Label(form, text="알람").grid(row=r, column=0, sticky="w")
        af = ttk.Frame(form)
        af.grid(row=r, column=1, columnspan=2, sticky="w", pady=2)
        ttk.Combobox(af, textvariable=self.v_alarm, values=[t for t, _ in EVENT_ALARMS], state="readonly",
                     width=10).pack(side="left")
        ttk.Label(af, text="  색").pack(side="left")
        ttk.Combobox(af, textvariable=self.v_color, values=[t for t, _ in EVENT_COLORS], state="readonly",
                     width=6).pack(side="left", padx=4)
        r += 1
        ttk.Label(form, text="분류").grid(row=r, column=0, sticky="w")
        kf = ttk.Frame(form)
        kf.grid(row=r, column=1, columnspan=2, sticky="w", pady=2)
        ttk.Label(kf, text="유형").pack(side="left")
        ttk.Combobox(kf, textvariable=self.v_kind, values=EVENT_KINDS, width=7).pack(side="left", padx=(3, 8))
        ttk.Label(kf, text="부서").pack(side="left")
        self.cb_dept = ttk.Combobox(kf, textvariable=self.v_dept, width=11)
        self.cb_dept.pack(side="left", padx=(3, 8))
        ttk.Label(kf, text="팀").pack(side="left")
        self.cb_team = ttk.Combobox(kf, textvariable=self.v_team, width=11)
        self.cb_team.pack(side="left", padx=3)
        self.refresh_hist()
        r += 1
        ttk.Label(form, text="메모").grid(row=r, column=0, sticky="w")
        ttk.Entry(form, textvariable=self.v_memo).grid(row=r, column=1, columnspan=2, sticky="we", pady=2)
        r += 1
        ttk.Checkbutton(form, text="휴일로 표시 (날짜를 빨간색으로)", variable=self.v_hol).grid(
            row=r, column=1, columnspan=2, sticky="w", pady=(2, 0))
        r += 1
        ttk.Label(form, text="※ 알람은 시간을 지정하지 않으면 오전 9시 기준입니다.", foreground="#868e96").grid(
            row=r, column=0, columnspan=3, sticky="w")

        bf = ttk.Frame(f)
        bf.pack(fill="x", pady=(10, 0))
        ttk.Button(bf, text="＋ 새 일정 추가", style="Accent.TButton", command=self.add).pack(side="left")
        ttk.Button(bf, text="선택 일정 수정 저장", command=self.update).pack(side="left", padx=6)
        ttk.Button(bf, text="삭제", command=self.delete).pack(side="left")
        self.btn_unlock = ttk.Button(bf, text="잠금 해제", command=self.unlock)
        ttk.Button(bf, text="닫기", command=w.destroy).pack(side="right")

        self.set_day(d, select_id)
        w.update_idletasks()
        sw, sh = w.winfo_screenwidth(), w.winfo_screenheight()
        x = max(0, min(w.winfo_pointerx() - 40, sw - w.winfo_reqwidth() - 10))
        y = max(0, min(w.winfo_pointery() - 40, sh - w.winfo_reqheight() - 50))
        w.geometry(f"+{x}+{y}")
        w.lift()
        w.focus_force()

    def refresh_hist(self):
        evs = self.app.events
        self.cb_dept["values"] = sorted({e.get("dept", "") for e in evs if e.get("dept")})
        self.cb_team["values"] = sorted({e.get("team", "") for e in evs if e.get("team")})

    def pick(self, var):
        DatePicker(self.app, self.win, var.get(), lambda iso: var.set(iso))

    def set_day(self, d, select_id=None):
        self.d = d
        self.win.title(f"일정 - {d.year}년 {d.month}월 {d.day}일")
        self.lbl.config(text=f"{d.year}년 {d.month}월 {d.day}일 ({DAY_NAMES[d.weekday()]})")
        h = holiday_name(self.app.events, d)
        self.lbl_hol.config(text=("● " + h + ("  — " + DESC[h.replace(" 연휴", "")] if h.replace(" 연휴", "") in DESC else "")) if h else "")
        self.lbl_an.config(text="\n".join(f"※ {n} — {DESC[n]}" if n in DESC else f"※ {n}" for n, _c in anniv_list(d)))
        self.fill_list(select_id)
        if self.cur is None:
            self.clear_form()

    def fill_list(self, select_id=None):
        self.lb.delete(0, "end")
        evs = day_events(self.app.events, self.d)
        self.ids = [e["id"] for e in evs]
        for e in evs:
            rep = {"monthly": " [매월]", "yearly": " [매년]"}.get(e.get("repeat"), "")
            al = " ⏰" if e.get("alarm") is not None else ""
            kd = f'[{e["kind"]}] ' if e.get("kind") else ""
            org = " ({})".format("/".join(x for x in (e.get("dept"), e.get("team")) if x)) if (e.get("dept") or e.get("team")) else ""
            lk = "[잠금] " if self.is_locked(e) else ""
            self.lb.insert("end", f'{lk}{e.get("time") or "종일"}  {kd}{e["title"]}{org}{rep}{al}')
        self.cur = None
        self.show_lock(None)
        if select_id in self.ids:
            i = self.ids.index(select_id)
            self.lb.selection_set(i)
            self.on_select()

    def clear_form(self):
        self.v_title.set("")
        self.v_date.set(self.d.isoformat())
        self.v_end.set("")
        self.v_timeon.set(False)
        self.v_h.set("09"); self.v_m.set("00")
        self.v_rep.set("none")
        self.v_alarm.set(EVENT_ALARMS[0][0])
        self.v_color.set(EVENT_COLORS[0][0])
        self.v_memo.set("")
        self.v_hol.set(False)
        self.v_kind.set("")
        self.v_dept.set(getattr(self.app, "last_dept", ""))
        self.v_team.set(getattr(self.app, "last_team", ""))

    def find(self, eid):
        for e in self.app.events:
            if e["id"] == eid:
                return e
        return None

    def is_locked(self, e):
        return event_hard_locked(e) or (event_locked(e) and e["id"] not in self.unlocked)

    def show_lock(self, e):
        if e is not None and event_hard_locked(e):
            self.lbl_lock.config(text=f"끝난 지 {LOCK_HARD_DAYS}일이 지난 일정은 기록으로 보관되며 수정·삭제할 수 없습니다.")
            self.btn_unlock.pack_forget()
        elif e is not None and self.is_locked(e):
            self.lbl_lock.config(text=f"지난 일정은 잠겨 있어 수정·삭제할 수 없습니다. ({LOCK_HARD_DAYS}일 안의 일정만 '잠금 해제'로 고칠 수 있음)")
            self.btn_unlock.pack(side="left", padx=6)
        else:
            self.lbl_lock.config(text="")
            self.btn_unlock.pack_forget()

    def unlock(self):
        e = self.find(self.cur) if self.cur is not None else None
        if e is None or event_hard_locked(e):
            return
        if messagebox.askyesno(APP_NAME, "지난 일정은 기록으로 보관 중입니다.\n정말 잠금을 풀고 고칠까요?", parent=self.win):
            self.unlocked.add(e["id"])
            self.fill_list(e["id"])
            self.show_lock(e)

    def on_select(self, _e=None):
        sel = self.lb.curselection()
        if not sel:
            return
        e = self.find(self.ids[sel[0]])
        if not e:
            return
        self.cur = e["id"]
        self.show_lock(e)
        self.v_title.set(e["title"])
        self.v_date.set(e["date"])
        self.v_end.set(e.get("end", ""))
        self.v_timeon.set(bool(e.get("time")))
        if e.get("time"):
            self.v_h.set(e["time"][:2]); self.v_m.set(e["time"][3:])
        self.v_rep.set(e.get("repeat", "none"))
        self.v_alarm.set(alarm_text(e.get("alarm")) or EVENT_ALARMS[0][0])
        self.v_color.set(EVENT_COLORS[e.get("color", 0) % len(EVENT_COLORS)][0])
        self.v_memo.set(e.get("memo", ""))
        self.v_hol.set(bool(e.get("holiday")))
        self.v_kind.set(e.get("kind", ""))
        self.v_dept.set(e.get("dept", ""))
        self.v_team.set(e.get("team", ""))

    def read(self):
        title = self.v_title.get().strip()
        if not title:
            messagebox.showwarning(APP_NAME, "일정 제목을 입력하세요.", parent=self.win)
            return None
        try:
            date = normalize_date(self.v_date.get())
            end = normalize_date(self.v_end.get()) if self.v_end.get().strip() else ""
            tm = f"{int(self.v_h.get()):02d}:{int(self.v_m.get()):02d}" if self.v_timeon.get() else ""
            if tm and (int(tm[:2]) > 23 or int(tm[3:]) > 59):
                raise ValueError
        except ValueError:
            messagebox.showwarning(APP_NAME, "날짜(예: 2026-10-08)와 시각을 확인하세요.", parent=self.win)
            return None
        if end and end < date:
            messagebox.showwarning(APP_NAME, "끝나는 날이 시작 날짜보다 빠릅니다.", parent=self.win)
            return None
        alarm = dict(EVENT_ALARMS).get(self.v_alarm.get())
        color = [t for t, _ in EVENT_COLORS].index(self.v_color.get()) if self.v_color.get() in \
            [t for t, _ in EVENT_COLORS] else 0
        return {"title": title, "date": date, "end": end, "time": tm, "repeat": self.v_rep.get(),
                "alarm": alarm, "color": color, "memo": self.v_memo.get().strip(), "holiday": self.v_hol.get(),
                "kind": self.v_kind.get().strip(), "dept": self.v_dept.get().strip(), "team": self.v_team.get().strip()}

    def after_change(self, date_iso, select_id=None):
        e = self.find(select_id) if select_id else None
        if e:       # 다음 일정 입력 때 부서·팀을 미리 채워 둠
            self.app.last_dept, self.app.last_team = e.get("dept", ""), e.get("team", "")
        self.app.save_events()
        self.refresh_hist()
        self.set_day(datetime.date.fromisoformat(date_iso), select_id)

    def add(self):
        data = self.read()
        if data:
            e = norm_event(dict(data, id=int(time.time() * 1000), upd=int(time.time() * 1000)))
            self.app.events.append(e)
            self.unlocked.add(e["id"])     # 방금 입력한 일정은 이 창에서 바로 고칠 수 있음
            self.after_change(e["date"], e["id"])

    def update(self):
        if self.cur is None or not self.find(self.cur):
            messagebox.showinfo(APP_NAME, "수정할 일정을 목록에서 선택하세요.", parent=self.win)
            return
        if self.is_locked(self.find(self.cur)):
            messagebox.showinfo(APP_NAME, ("끝난 지 7일이 지난 일정은 수정할 수 없습니다." if event_hard_locked(self.find(self.cur))
                                           else "지난 일정은 잠겨 있어 수정할 수 없습니다. 고치려면 '잠금 해제'를 누르세요."), parent=self.win)
            return
        data = self.read()
        if data:
            e = self.find(self.cur)
            e.update(data)
            e["upd"] = int(time.time() * 1000)
            self.after_change(e["date"], e["id"])

    def delete(self):
        if self.cur is None or not self.find(self.cur):
            messagebox.showinfo(APP_NAME, "삭제할 일정을 목록에서 선택하세요.", parent=self.win)
            return
        if self.is_locked(self.find(self.cur)):
            messagebox.showinfo(APP_NAME, ("끝난 지 7일이 지난 일정은 삭제할 수 없습니다." if event_hard_locked(self.find(self.cur))
                                           else "지난 일정은 잠겨 있어 삭제할 수 없습니다. 지우려면 '잠금 해제'를 누르세요."), parent=self.win)
            return
        if messagebox.askyesno(APP_NAME, "선택한 일정을 삭제할까요?", parent=self.win):
            if self.app.cloud.logged_in():
                self.app.tomb.append({"id": self.cur, "upd": int(time.time() * 1000)})
            self.app.events[:] = [e for e in self.app.events if e["id"] != self.cur]
            self.cur = None
            self.app.save_events()
            self.set_day(self.d)
            self.clear_form()


# ================================================================ 클라우드(구글 로그인 + Firestore) 동기화·공유
# 배포 전에 관리자가 아래 4개 값을 채워서 exe를 만들면, 직원은 '구글 로그인'만 하면 됩니다.
# (비워 두면 프로그램의 '☁ 구글 로그인·공유 설정' 창에서 직접 입력할 수 있습니다.)
DEFAULT_CLOUD = {
    "apiKey": "AIzaSyDZS8cacPdO-c3BdaXH5jNgHFdJtFCeTo8",   # Firebase 웹 API 키
    "projectId": "planneralarm-6271e",   # Firebase 프로젝트 ID
    "loginUrl": "https://nunco-git.github.io/planneralarm/",   # 로그인 페이지(웹 조회 페이지) 주소
}
SYNC_EVERY_S = 900      # 평소 15분마다 '바뀐 일정이 있나' 확인 (확인 1번 = 읽기 1건)
SYNC_SLOW_S = 1800      # 1시간 동안 변화가 없으면 30분 간격으로 늦춤
SYNC_FULL_DAYS = 7      # 전체 읽기(점검)는 일주일에 한 번


class CloudError(Exception):
    code = 0


# ---------- Firestore 값 변환
def _fs_val(v):
    if v is None:
        return {"nullValue": None}
    if isinstance(v, bool):
        return {"booleanValue": v}
    if isinstance(v, int):
        return {"integerValue": str(v)}
    if isinstance(v, float):
        return {"doubleValue": v}
    return {"stringValue": str(v)}


def _fs_doc(d):
    return {"fields": {k: _fs_val(v) for k, v in d.items()}}


def _fs_py(v):
    if "stringValue" in v:
        return v["stringValue"]
    if "integerValue" in v:
        return int(v["integerValue"])
    if "booleanValue" in v:
        return v["booleanValue"]
    if "doubleValue" in v:
        return v["doubleValue"]
    return None


def _fs_from(doc):
    return {k: _fs_py(v) for k, v in doc.get("fields", {}).items()}


class FirebaseREST:
    """Firebase 인증 토큰 + Firestore REST (표준 라이브러리만 사용)"""

    def __init__(self, conf, user):
        self.conf, self.user = conf, user
        self.id_token, self.exp = None, 0

    def _http(self, method, url, body=None, form=None, token=None, timeout=20):
        data, headers = None, {}
        if form is not None:
            data = urllib.parse.urlencode(form).encode()
            headers["Content-Type"] = "application/x-www-form-urlencoded"
        elif body is not None:
            data = json.dumps(body).encode("utf-8")
            headers["Content-Type"] = "application/json"
        if token:
            headers["Authorization"] = "Bearer " + token
        req = urllib.request.Request(url, data=data, headers=headers, method=method)
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                raw = r.read().decode("utf-8")
                return json.loads(raw) if raw else {}
        except urllib.error.HTTPError as e:
            raw = e.read().decode("utf-8", "replace")
            try:
                j = json.loads(raw)
                er = j.get("error", raw)
                msg = er.get("message", str(er)) if isinstance(er, dict) else f'{er} {j.get("error_description", "")}'
            except Exception:
                msg = raw[:200]
            ex = CloudError(f"{e.code}: {msg}")
            ex.code = e.code
            raise ex
        except (urllib.error.URLError, OSError) as e:
            raise CloudError("네트워크 연결 실패: " + str(getattr(e, "reason", e)))

    def token(self):
        if self.id_token and time.time() < self.exp - 120:
            return self.id_token
        j = self._http("POST", "https://securetoken.googleapis.com/v1/token?key=" +
                       urllib.parse.quote(self.conf["apiKey"]),
                       form={"grant_type": "refresh_token", "refresh_token": self.user.get("refresh", "")})
        self.id_token = j["id_token"]
        self.exp = time.time() + int(j.get("expires_in", 3600))
        if j.get("refresh_token"):
            self.user["refresh"] = j["refresh_token"]
        return self.id_token

    def _base(self):
        return f'https://firestore.googleapis.com/v1/projects/{urllib.parse.quote(self.conf["projectId"])}/databases/(default)/documents'

    def _path(self, path):
        return "/".join(urllib.parse.quote(p, safe="") for p in path.split("/"))

    def get(self, path):
        try:
            return _fs_from(self._http("GET", self._base() + "/" + self._path(path), token=self.token()))
        except CloudError as e:
            if e.code == 404:
                return None
            raise

    def set(self, path, data):
        self._http("PATCH", self._base() + "/" + self._path(path), body=_fs_doc(data), token=self.token())

    def delete(self, path):
        try:
            self._http("DELETE", self._base() + "/" + self._path(path), token=self.token())
        except CloudError as e:
            if e.code != 404:
                raise

    def get_raw(self, path):
        """문서 원본(updateTime 포함). 없으면 None"""
        try:
            return self._http("GET", self._base() + "/" + self._path(path), token=self.token())
        except CloudError as e:
            if e.code == 404:
                return None
            raise

    def commit(self, writes):
        """여러 쓰기를 한 번에(전부 성공하거나 전부 실패)"""
        return self._http("POST", self._base() + ":commit", body={"writes": writes}, token=self.token())

    def doc_name(self, path):
        return f'projects/{self.conf["projectId"]}/databases/(default)/documents/' + path

    def query(self, collection, wheres=(), parent="", gt=None, ge=None):
        sq = {"from": [{"collectionId": collection}]}
        flt = [{"fieldFilter": {"field": {"fieldPath": f}, "op": "EQUAL", "value": _fs_val(v)}} for f, v in wheres]
        if gt:      # (필드, 값): 값보다 큰 문서만 읽기 → 읽기 횟수 절약
            flt.append({"fieldFilter": {"field": {"fieldPath": gt[0]}, "op": "GREATER_THAN", "value": _fs_val(gt[1])}})
        if ge:      # (필드, 값): 값 이상인 문서만
            flt.append({"fieldFilter": {"field": {"fieldPath": ge[0]}, "op": "GREATER_THAN_OR_EQUAL", "value": _fs_val(ge[1])}})
        if flt:
            sq["where"] = flt[0] if len(flt) == 1 else {"compositeFilter": {"op": "AND", "filters": flt}}
        url = self._base() + ("/" + self._path(parent) if parent else "") + ":runQuery"
        j = self._http("POST", url, token=self.token(), body={"structuredQuery": sq})
        out = []
        for item in j if isinstance(j, list) else []:
            d = item.get("document")
            if d:
                row = _fs_from(d)
                row["_id"] = urllib.parse.unquote(d["name"].rsplit("/", 1)[-1])
                out.append(row)
        return out


def open_small_window(url, w=440, h=620):
    """Edge/Chrome를 '앱 창'(주소창 없는 작은 창)으로 열기. 없으면 기본 브라우저."""
    if os.name == "nt":
        cands = []
        for env in ("ProgramFiles(x86)", "ProgramFiles", "LOCALAPPDATA"):
            base = os.environ.get(env)
            if base:
                cands += [os.path.join(base, r"Microsoft\Edge\Application\msedge.exe"),
                          os.path.join(base, r"Google\Chrome\Application\chrome.exe")]
        try:
            root = tk._default_root
            sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
        except Exception:
            sw, sh = 1920, 1080
        pos = f"{max(0, (sw - w) // 2)},{max(0, (sh - h) // 3)}"
        for exe in cands:
            if os.path.isfile(exe):
                try:
                    subprocess.Popen([exe, f"--app={url}", f"--window-size={w},{h}", f"--window-position={pos}"])
                    return
                except Exception:
                    pass
    webbrowser.open(url)


def web_login(conf, timeout_s=180, open_browser=None):
    """브라우저에서 웹 페이지로 구글 로그인 → 이 PC(127.0.0.1)로 로그인 정보가 되돌아옴. user dict 반환"""
    open_browser = open_browser or open_small_window
    state = secrets.token_urlsafe(24)
    result = {}

    class Handler(http.server.BaseHTTPRequestHandler):
        def do_GET(self):
            q = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            ok = q.get("state", [""])[0] == state and q.get("refresh", [""])[0] and q.get("uid", [""])[0]
            if ok:
                result.update(uid=q["uid"][0], refresh=q["refresh"][0], email=q.get("email", [""])[0],
                              name=q.get("name", [""])[0] or q.get("email", [""])[0])
            msg = "로그인이 완료되었습니다" if ok else "잘못된 요청입니다"
            icon = "✅" if ok else "⚠️"
            sub = "스마트 일정 알라미로 돌아가세요.<br>이 창은 잠시 후 저절로 닫힙니다." if ok else "다시 시도해 주세요."
            body = ("<html><head><meta charset='utf-8'><meta name='viewport' content='width=device-width,initial-scale=1'></head>"
                    "<body style=\"margin:0;min-height:100vh;display:flex;align-items:center;justify-content:center;"
                    "font-family:'Malgun Gothic',sans-serif;background:linear-gradient(160deg,#fff3bf,#ffe066 45%,#ffa94d)\">"
                    "<div style='background:#fff;border-radius:20px;padding:34px 30px;text-align:center;max-width:340px;"
                    "box-shadow:0 14px 40px rgba(120,70,0,.22)'>"
                    f"<div style='font-size:52px'>{icon}</div><h2 style='margin:8px 0'>{msg}</h2>"
                    f"<p style='color:#868e96;font-size:14px'>{sub}</p></div>"
                    "<script>setTimeout(function(){window.close()},1800)</script></body></html>")
            self.send_response(200 if ok else 400)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.end_headers()
            self.wfile.write(body.encode("utf-8"))

        def log_message(self, *a):
            pass

    srv = http.server.HTTPServer(("127.0.0.1", 0), Handler)
    srv.timeout = 1
    base = conf["loginUrl"]
    url = base + ("&" if "?" in base else "?") + urllib.parse.urlencode({"desktop": srv.server_address[1], "state": state})
    open_browser(url)
    end = time.time() + timeout_s
    try:
        while not result and time.time() < end:
            srv.handle_request()
    finally:
        srv.server_close()
    if not result:
        raise CloudError("로그인 시간이 지났습니다. 다시 시도하세요.")
    return dict(result)


# ---------- 일정 <-> 클라우드 문서  (users/<내uid>/events/<일정번호>)
SYNC_PAST_DAYS = 7      # 끝난 지 이 일수가 지난 '반복 없는' 일정은 클라우드와 동기화하지 않음(읽기·저장 절약)


def event_last(e):
    """일정의 마지막 날짜(ISO). 반복 일정은 끝이 없으므로 아주 먼 날짜"""
    if e.get("repeat", "none") != "none":
        return "9999-12-31"
    return e.get("end") or e.get("date") or "9999-12-31"


def event_locked(e):
    """어제까지 끝난 (반복 없는) 일정은 잠가서 비망록처럼 보관: 수정·삭제 불가"""
    if e.get("repeat", "none") != "none":
        return False
    last = e.get("end") or e.get("date") or ""
    return bool(last) and last < datetime.date.today().isoformat()


LOCK_HARD_DAYS = 7      # 끝난 지 이 일수가 지난 일정은 '잠금 해제'도 안 되는 완전 잠금(수정·삭제 불가)


def event_hard_locked(e):
    if e.get("repeat", "none") != "none":
        return False
    last = e.get("end") or e.get("date") or ""
    return bool(last) and last < (datetime.date.today() - datetime.timedelta(days=LOCK_HARD_DAYS)).isoformat()


def event_sync_keep():
    return (datetime.date.today() - datetime.timedelta(days=SYNC_PAST_DAYS)).isoformat()


def event_to_doc(e):
    return {"last": event_last(e), "id": int(e["id"]), "title": e.get("title", ""), "date": e.get("date", ""), "end": e.get("end", ""),
            "time": e.get("time", ""), "repeat": e.get("repeat", "none"), "alarm": e.get("alarm"),
            "color": int(e.get("color", 0)), "memo": e.get("memo", ""), "holiday": bool(e.get("holiday")),
            "kind": e.get("kind", ""), "dept": e.get("dept", ""), "team": e.get("team", ""),
            "upd": int(e.get("upd", 0)), "deleted": False}


def doc_to_event(d):
    return {"id": int(d["id"]), "title": d.get("title", ""), "date": d.get("date", ""), "end": d.get("end", ""),
            "time": d.get("time", ""), "repeat": d.get("repeat", "none"), "alarm": d.get("alarm"),
            "color": int(d.get("color") or 0), "memo": d.get("memo", ""), "holiday": bool(d.get("holiday")),
            "kind": d.get("kind") or "", "dept": d.get("dept") or "", "team": d.get("team") or "",
            "upd": int(d.get("upd") or 0)}


def cal_prefs_doc(app):
    """PC 달력 보기 설정 → 웹 페이지로 보낼 문서 (users/<uid>/prefs/cal)"""
    c, th = app.cfg["cal"], app.theme
    d = {"lunar": bool(c.get("lunar", True)), "view": c.get("view", "month"), "holidays": bool(c.get("holidays", True)),
         "f_kind": c.get("f_kind", ""), "f_dept": c.get("f_dept", ""), "f_team": c.get("f_team", ""),
         "c_fg": c.get("fg") or th["fg"], "c_card": c.get("bg") or th["card"], "c_head_bg": c.get("head_bg") or th["head_bg"],
         "c_head_fg": c.get("head_fg") or th["head_fg"], "c_accent": c.get("accent") or th["accent"]}
    an = c.get("anniv", {})
    for k in ANNIV_CATS:
        d["an_" + k] = bool(an.get(k, True))
    return d


# ---------- 동기화 전 백업 (웹/클라우드가 잘못 바뀌어도 PC의 일정을 되살릴 수 있게)
BACKUP_PAST_DAYS = 0         # 0 = 지난 일정까지 전부 백업. (숫자를 넣으면 그 일수 전부터의 일정만). 백업 파일은 지우지 않고 계속 보관
BACKUP_DAILY = True          # 하루에 한 번(그날 첫 동기화 직전)만 백업


def list_backups():
    try:
        names = [n for n in os.listdir(BACKUP_DIR) if n.startswith("일정백업_") and n.endswith(".json")]
    except OSError:
        return []
    return sorted(names, reverse=True)


def make_backup(events, tomb, alarms=None, reason="", daily=False):
    """일정·알람을 backup 폴더에 날짜·시각이 붙은 JSON 으로 저장. 만든 파일 경로(없으면 '')"""
    try:
        os.makedirs(BACKUP_DIR, exist_ok=True)
        last = list_backups()
        if daily and any(n.startswith(f"일정백업_{datetime.date.today():%Y%m%d}_") for n in last):
            return ""                # 오늘 이미 백업했음
        frm = (datetime.date.today() - datetime.timedelta(days=BACKUP_PAST_DAYS)).isoformat() if BACKUP_PAST_DAYS else ""
        if frm:
            events = [e for e in events if event_last(e) >= frm]
        if not events and not tomb:
            return ""
        name = f"일정백업_{datetime.datetime.now():%Y%m%d_%H%M%S}.json"
        path = os.path.join(BACKUP_DIR, name)
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump({"saved": datetime.datetime.now().isoformat(timespec="seconds"), "reason": reason, "from": frm,
                       "events": events, "tomb": tomb, "alarms": alarms or []}, f, ensure_ascii=False, indent=1)
        os.replace(tmp, path)
        return path
    except Exception as ex:
        print("백업 실패:", ex)
        return ""


def sync_events(fb, snap, since=0, push_only=False, push_mark=0):
    """클라우드와 내 일정을 맞춤. 변경 내용을 담은 dict를 돌려줌(앱 목록은 건드리지 않음)"""
    uid = snap["uid"]
    base = f"users/{uid}/events"
    now = int(time.time() * 1000)
    out = {"updates": {}, "adds": [], "deletes": [], "stamped": {}, "tomb_done": [], "pushed": 0, "prefs_done": None}
    # since>0 이면 '그 이후 바뀐 문서'만 읽는다(시계 오차 대비 10분 여유). 0이면 전체 읽기.
    cut = max(0, since - 600000) if since else 0
    mx = since
    if push_only:
        # 읽기 없이 '내가 바꾼 것'만 올린다 (읽기 0건). 내려받기는 하지 않는다.
        keep = event_sync_keep()
        pm = push_mark
        if snap.get("prefs") is not None:
            fb.set(f"users/{uid}/prefs/cal", dict(snap["prefs"], upd=now))
            out["prefs_done"] = json.dumps(snap["prefs"], sort_keys=True)
        for t in snap["tomb"]:
            fb.set(f'{base}/{t["id"]}', {"id": int(t["id"]), "title": "", "deleted": True, "last": "9999-12-31", "upd": int(t["upd"])})
            out["tomb_done"].append(t["id"])
            pm = max(pm, int(t["upd"]))
        for e in snap["events"]:
            lu = int(e.get("upd", 0))
            if event_last(e) < keep or (lu and lu <= push_mark):
                continue
            if not lu:
                lu = now
                out["stamped"][e["id"]] = lu
            fb.set(f'{base}/{e["id"]}', event_to_doc(dict(e, upd=lu)))
            pm = max(pm, lu)
            out["pushed"] += 1
        out["since_new"] = since
        out["push_new"] = pm
        out["web"] = False
        return out
    if snap.get("prefs") is not None:
        fb.set(f"users/{uid}/prefs/cal", dict(snap["prefs"], upd=int(time.time() * 1000)))
        out["prefs_done"] = json.dumps(snap["prefs"], sort_keys=True)
    for t in snap["tomb"]:
        fb.set(f'{base}/{t["id"]}', {"id": int(t["id"]), "title": "", "deleted": True, "last": "9999-12-31", "upd": int(t["upd"])})
        out["tomb_done"].append(t["id"])
        mx = max(mx, int(t["upd"]))
    tomb_ids = {t["id"] for t in snap["tomb"]}
    remote = {}
    keep = event_sync_keep()
    for d in fb.query("events", parent=f"users/{uid}", gt=("upd", cut) if cut else None,
                      ge=None if cut else ("last", keep)):
        try:
            remote[int(d.get("id") or d["_id"])] = d
            mx = max(mx, int(d.get("upd") or 0))
        except (TypeError, ValueError):
            pass
    local_ids = set()
    for e in snap["events"]:
        eid, lu = e["id"], int(e.get("upd", 0))
        local_ids.add(eid)
        if event_last(e) < keep:
            continue                # 지난 일정은 동기화하지 않음
        r = remote.get(eid)
        if r is None:
            if cut and lu and lu <= cut:
                continue            # 바뀐 적 없는 일정(이미 올라가 있음)
            if not lu:
                lu = now
                out["stamped"][eid] = lu
            fb.set(f"{base}/{eid}", event_to_doc(dict(e, upd=lu)))
            mx = max(mx, lu)
            out["pushed"] += 1
            continue
        ru = int(r.get("upd") or 0)
        if lu > ru:
            fb.set(f"{base}/{eid}", event_to_doc(e))
            mx = max(mx, lu)
            out["pushed"] += 1
        elif ru > lu:
            if r.get("deleted"):
                out["deletes"].append(eid)
            else:
                out["updates"][eid] = doc_to_event(r)
    for eid, r in remote.items():
        if eid not in local_ids and eid not in tomb_ids and not r.get("deleted"):
            ne = doc_to_event(r)
            if event_last(ne) >= keep:
                out["adds"].append(ne)
    out["since_new"] = mx
    out["push_new"] = mx
    out["web"] = any(r.get("src") == "web" for r in remote.values())
    return out


class CloudSync:
    def __init__(self, app):
        self.app = app
        self.busy = self.pending = False
        self.prefs_sent = ""
        self.status = ""
        self.listeners = []
        self.since, self.since_uid, self.full_at = 0, "", 0.0
        self.idle, self.last_sync = 0, 0.0
        self.force_read = False
        self.last_appr_check = 0.0

    @property
    def c(self):
        return self.app.cfg["cloud"]

    def conf(self):
        d = dict(DEFAULT_CLOUD)
        d.update({k: v.strip() for k, v in self.c.get("conf", {}).items() if isinstance(v, str) and v.strip()})
        return d

    def configured(self):
        c = self.conf()
        return all(c.get(k) for k in ("apiKey", "projectId", "loginUrl"))

    def logged_in(self):
        u = self.c.get("user", {})
        return bool(u.get("uid") and u.get("refresh"))

    def approved(self):
        """관리자가 승인한 계정인가 (승인 전에는 동기화하지 않음)"""
        return bool(self.c.get("approved"))

    def ready(self):
        return self.configured() and self.logged_in() and self.approved()

    APPR_TEXT = {"none": "아직 사용 신청을 하지 않았습니다.", "pending": "승인 대기 중입니다. 관리자가 승인하면 사용할 수 있습니다.",
                 "approved": "승인되었습니다.", "revoked": "사용이 중지된 계정입니다. 관리자에게 문의하세요.",
                 "": "승인 상태를 확인하지 못했습니다."}

    def approval_text(self):
        if not self.logged_in():
            return ""
        return self.APPR_TEXT.get(self.c.get("approval", ""), self.APPR_TEXT[""])

    def check_approval(self, done=None):
        """승인 상태 확인 (읽기 1건)"""
        if not (self.configured() and self.logged_in()):
            return
        self.last_appr_check = time.time()
        uid = self.c["user"]["uid"]

        def fin(res, err):
            if err:
                self.set_status(f"승인 상태 확인 실패: {err}")
            else:
                st = str(res.get("status", "none")) if res else "none"
                was = self.approved()
                self.c["approval"] = st
                self.c["approved"] = (st == "approved")
                save_config(self.app.cfg)
                self.set_status(self.approval_text())
                if self.approved() and not was:
                    self.request_sync(0)
            if done:
                done()
        self.run_bg(lambda: self.fb().get(f"approvals/{uid}"), fin)

    def request_approval(self, agency, dept, pname, done=None):
        """사용 신청서(승인 대기)를 올림"""
        if not (self.configured() and self.logged_in()):
            return
        u = self.c["user"]

        def work():
            fb = self.fb()
            if fb.get(f"approvals/{u['uid']}"):
                return "exists"
            info = {"uid": u["uid"], "email": u.get("email", "")[:100], "name": u.get("name", "")[:100],
                    "agency": agency[:50], "dept": dept[:50], "pname": pname[:50], "requested": int(time.time() * 1000)}
            try:    # 선착순 자동 승인: 카운터 +1 과 승인 문서 생성을 한 번에 (자리가 없거나 실패하면 아래 '승인 대기'로)
                raw = fb.get_raw("meta/autoApprove")
                if raw and raw.get("updateTime"):
                    c = _fs_from(raw)
                    n, lim = int(c.get("n") or 0), int(c.get("limit") or 0)
                    if n < lim:
                        fb.commit([
                            {"update": {"name": fb.doc_name("meta/autoApprove"), **_fs_doc({"n": n + 1, "limit": lim})},
                             "updateMask": {"fieldPaths": ["n", "limit"]},
                             "currentDocument": {"updateTime": raw["updateTime"]}},
                            {"update": {"name": fb.doc_name("approvals/" + urllib.parse.quote(u["uid"], safe="")),
                                        **_fs_doc(dict(info, status="approved"))},
                             "currentDocument": {"exists": False}}])
                        return "auto"
            except CloudError:
                pass
            fb.set(f"approvals/{u['uid']}", dict(info, status="pending"))
            return "ok"

        def fin(res, err):
            if err:
                self.set_status(f"신청하지 못했습니다: {err}")
            else:
                self.check_approval(done)
                return
            if done:
                done()
        self.run_bg(work, fin)

    def fb(self):
        return FirebaseREST(self.conf(), self.c["user"])

    def set_status(self, text):
        self.status = text
        for cb in list(self.listeners):
            try:
                cb()
            except Exception:
                pass

    def run_bg(self, fn, done=None):
        def work():
            try:
                r, err = fn(), None
            except Exception as ex:
                r, err = None, ex
            if done:
                self.app.cmdq.put(("call", lambda: done(r, err)))
        threading.Thread(target=work, daemon=True).start()

    def login(self, done):
        if not self.configured():
            done(None, CloudError("연결 정보(API 키·프로젝트 ID·로그인 페이지 주소)를 먼저 입력하세요."))
            return
        conf = self.conf()

        def fin(res, err):
            if not err:
                self.c["user"] = res
                self.c["approval"], self.c["approved"] = "", False
                save_config(self.app.cfg)
                self.check_approval()
            done(res, err)
        self.run_bg(lambda: web_login(conf), fin)

    def logout(self):
        self.c["user"] = {}
        self.c["approval"], self.c["approved"] = "", False
        self.prefs_sent = ""
        save_config(self.app.cfg)
        self.set_status("로그아웃했습니다.")

    def read_enabled(self):
        """클라우드에서 '내려받기(읽기)'를 하는 사용자인가: 웹 입력 이력이 있거나 사용자가 켠 경우"""
        return bool(self.c.get("webuse") or self.c.get("autopoll"))

    def touch(self):
        """달력/창을 열 때: (읽기 사용자만) 마지막 동기화가 2분 넘었으면 한 번 확인(읽기 1건)"""
        if self.ready() and self.read_enabled() and time.time() - self.last_sync > 120:
            self.idle = 0
            self.request_sync(1)

    def interval(self):
        return SYNC_EVERY_S if self.idle < 4 else SYNC_SLOW_S

    def want_poll(self):
        """주기적 확인이 필요한가? 웹/다른 PC에서 입력한 이력이 있거나 사용자가 켠 경우에만(밤 시간 제외)"""
        if not (self.c.get("webuse") or self.c.get("autopoll")):
            return False
        return 6 <= datetime.datetime.now().hour < 22

    def request_sync(self, delay=0):
        if not self.ready() or self.pending:
            return
        self.pending = True
        self.app.root.after(int(delay * 1000), self._start)

    def _start(self):
        self.pending = False
        if not self.ready():
            return
        if self.busy:
            self.request_sync(3)
            return
        app, u = self.app, self.c["user"]
        snap = {"uid": u["uid"], "events": [dict(e) for e in app.events], "tomb": [dict(t) for t in app.tomb]}
        pd = cal_prefs_doc(app)
        snap["prefs"] = pd if json.dumps(pd, sort_keys=True) != self.prefs_sent else None
        # 처음/계정이 바뀐 때/일주일에 한 번만 전체를 읽고, 그 외에는 바뀐 일정만 읽는다.
        # 마지막 동기화 시점은 설정 파일에 저장해 두어, 프로그램을 다시 켜도 전체를 읽지 않는다.
        sv = self.c.get("since") if isinstance(self.c.get("since"), dict) else {}
        if sv.get("uid") == u["uid"]:
            self.since, self.full_at = int(sv.get("t", 0)), float(sv.get("full", 0))
        else:
            self.since, self.full_at = 0, 0.0
        if self.read_enabled() and time.time() - self.full_at > SYNC_FULL_DAYS * 86400:
            self.since = 0
        # 읽기를 쓰지 않는 사용자는 '올리기만' 한다. 처음 로그인(since=0)이거나 [지금 동기화]를 누른 경우에만 읽는다.
        push_only = bool(self.since) and not self.read_enabled() and not self.force_read
        self.force_read = False
        self.push_only = push_only
        push_mark = int(sv.get("push", sv.get("t", 0))) if sv.get("uid") == u["uid"] else 0
        since = self.since
        # 동기화 전에 PC의 일정을 백업 (받아오는 동기화는 더 자주)
        make_backup(snap["events"], snap["tomb"], app.alarms, "동기화 전", daily=BACKUP_DAILY)
        self.busy = True
        self.set_status("저장 중…" if push_only else "동기화 중…")
        self.run_bg(lambda: sync_events(self.fb(), snap, since, push_only, push_mark), self._finish)

    def _finish(self, res, err):
        self.busy = False
        if err:
            self.set_status(f"동기화 실패: {err}")
            el = str(err).lower()
            if "403" in el or "permission" in el:
                self.c["approved"] = False            # 승인이 중지되었거나 아직 승인 전: 상태를 다시 확인
                save_config(self.app.cfg)
                self.check_approval()
                return
            if "429" in el or "quota" in el or "resource_exhausted" in el:
                self.app.set_local_notice("오늘 클라우드 사용 한도를 넘어 일정 동기화가 잠시 멈췄습니다. "
                                          "일정 등록·알람은 PC에서 정상 동작하며, 한도가 초기화되면(한국시간 오후 4~5시경) 자동으로 이어집니다.")
            return
        self.app.set_local_notice("")
        app = self.app
        if res.get("prefs_done"):
            self.prefs_sent = res["prefs_done"]
        old = self.c.get("since") if isinstance(self.c.get("since"), dict) else {}
        uid_ = self.c.get("user", {}).get("uid", "")
        if getattr(self, "push_only", False):
            self.c["since"] = {"uid": uid_, "t": self.since, "full": self.full_at,
                               "push": max(int(res.get("push_new", 0)), int(old.get("push", old.get("t", 0))))}
        else:
            if not self.since:
                self.full_at = time.time()
            self.since = max(self.since, res.get("since_new", 0)) or int(time.time() * 1000)
            self.c["since"] = {"uid": uid_, "t": self.since, "full": self.full_at,
                               "push": max(int(res.get("push_new", 0)), self.since)}
        self.last_sync = time.time()
        if res.get("web"):
            self.c["webuse"] = True         # 웹에서 입력한 일정이 확인되면 이후부터 주기적 확인을 켠다
        changed = res["pushed"] or res["adds"] or res["updates"] or res["deletes"]
        self.idle = 0 if changed else self.idle + 1
        by = {e["id"]: e for e in app.events}
        for eid, f in res["updates"].items():
            if eid in by and not event_locked(by[eid]):      # 잠긴 지난 일정은 웹에서 바뀌어도 PC에 반영하지 않음
                by[eid].update(f)
        for f in res["adds"]:
            if f["id"] not in by:
                app.events.append(norm_event(f))
        if res["deletes"]:
            gone = {i for i in res["deletes"] if not (i in by and event_locked(by[i]))}
            app.events[:] = [e for e in app.events if e["id"] not in gone]
        for eid, upd in res["stamped"].items():
            if eid in by and not by[eid].get("upd"):
                by[eid]["upd"] = upd
        app.tomb[:] = [t for t in app.tomb if t["id"] not in res["tomb_done"]]
        app.cfg["events"], app.cfg["tomb"] = app.events, app.tomb
        save_config(app.cfg)
        if app.cal.alive():
            app.cal.redraw()
        app.update_next()
        self.set_status(f'동기화 완료 {datetime.datetime.now():%H:%M} · 올린 일정 {res["pushed"]}건 · '
                        f'받아온 일정 {len(res["adds"]) + len(res["updates"])}건')

    def periodic(self):
        if self.configured() and self.logged_in() and not self.approved():
            if time.time() - self.last_appr_check > 3000:       # 승인 전에는 1시간에 한 번만 확인(읽기 1건)
                self.check_approval()
        elif self.want_poll():
            self.request_sync(0)
        self.app.root.after(int(self.interval() * 1000), self.periodic)


def app_font_name(app):
    return getattr(app, "ui_family", "TkDefaultFont")


class CloudDialog:
    """☁ 구글 로그인 설정 창"""

    def __init__(self, app):
        self.app, self.cl = app, app.cloud
        old = getattr(app, "cloud_dlg", None)
        if old is not None:
            try:
                old.win.destroy()
            except Exception:
                pass
        app.cloud_dlg = self
        w = self.win = tk.Toplevel(app.root)
        w.title("구글 로그인 · 내 일정 동기화")
        w.configure(bg=app.theme["bg"])
        w.resizable(False, False)
        f = ttk.Frame(w, padding=12)
        f.pack(fill="both", expand=True)
        conf = self.cl.c.setdefault("conf", {})
        self.v_conf = {k: tk.StringVar(value=conf.get(k, "")) for k in DEFAULT_CLOUD}
        if not all(DEFAULT_CLOUD.values()):
            cf = ttk.LabelFrame(f, text=" 연결 정보 (관리자가 안내한 값) ", padding=8)
            cf.pack(fill="x")
            cf.columnconfigure(1, weight=1)
            for i, (k, lab) in enumerate((("apiKey", "Firebase API 키"), ("projectId", "프로젝트 ID"),
                                          ("loginUrl", "로그인 페이지 주소"))):
                ttk.Label(cf, text=lab).grid(row=i, column=0, sticky="w", pady=1)
                ttk.Entry(cf, textvariable=self.v_conf[k], width=46).grid(row=i, column=1, sticky="we", padx=6, pady=1)
            ttk.Button(cf, text="저장", command=self.save_conf).grid(row=3, column=1, sticky="e", pady=(4, 0))
        lf = ttk.LabelFrame(f, text=" 로그인 ", padding=8)
        lf.pack(fill="x", pady=(8, 0))
        self.lbl_user = ttk.Label(lf, text="")
        self.lbl_user.pack(side="left")
        self.btn_in = ttk.Button(lf, text="구글 로그인", style="Accent.TButton", command=self.login)
        self.btn_in.pack(side="right")
        self.btn_out = ttk.Button(lf, text="로그아웃", command=self.logout)
        self.btn_out.pack(side="right", padx=6)
        af = ttk.LabelFrame(f, text=" 사용 승인 ", padding=8)
        af.pack(fill="x", pady=(8, 0))
        self.lbl_appr = ttk.Label(af, text="", wraplength=360, justify="left")
        self.lbl_appr.pack(side="left")
        self.btn_chk = ttk.Button(af, text="승인 상태 확인", command=self.check_appr)
        self.btn_chk.pack(side="right")
        self.btn_req = ttk.Button(af, text="사용 신청", style="Accent.TButton", command=self.req_appr)
        self.btn_req.pack(side="right", padx=6)
        nb_ = tk.Label(f, text="📌  PC에서 저장한 일정은 smartgong.kr 초기화면 좌측 상단 '앱 목록'에서 조회할 수 있습니다.",
                       bg="#fff3bf", fg="#4a2f00", anchor="w", justify="left", padx=10, pady=8, wraplength=520,
                       font=(app_font_name(self.app), self.app.ui_size, "bold"))
        nb_.pack(fill="x", pady=(8, 0))
        ttk.Label(f, text="※ 로그인하면 이 PC의 일정이 내 구글 계정 칸에 저장되고, 웹 페이지에서 같은 계정으로 조회할 수 있습니다.\n"
                          "   다른 사람에게는 보이지 않습니다. (로그인 창은 브라우저에서 열립니다.)", foreground="#868e96", justify="left").pack(anchor="w", pady=(8, 0))
        self.v_poll = tk.BooleanVar(value=bool(self.cl.c.get("autopoll")))

        def set_poll():
            self.cl.c["autopoll"] = bool(self.v_poll.get())
            save_config(self.app.cfg)
        ttk.Checkbutton(f, text="웹·다른 PC에서 입력한 일정도 자동으로 받기 (켜면 낮 시간 15~30분마다 확인)",
                        variable=self.v_poll, command=set_poll).pack(anchor="w", pady=(8, 0))
        ttk.Label(f, text="   꺼 두어도 웹에서 입력한 일정이 한 번 확인되면 자동으로 켜집니다. 꺼진 동안에는 프로그램을 켤 때·창을 열 때·'지금 동기화'를 누를 때 받아 옵니다.",
                  foreground="#868e96", wraplength=520, justify="left").pack(anchor="w")
        sf = ttk.Frame(f)
        sf.pack(fill="x", pady=(8, 0))
        ttk.Button(sf, text="지금 동기화", command=self.sync_now).pack(side="left")
        ttk.Button(sf, text="닫기", command=w.destroy).pack(side="right")
        ttk.Button(sf, text="백업에서 복원", command=self.restore_backup).pack(side="left", padx=(8, 0))
        ttk.Button(sf, text="백업 폴더 열기", command=self.open_backup_dir).pack(side="left", padx=(8, 0))
        ttk.Label(f, text=f"※ 동기화하기 전에 이 PC의 일정을 자동으로 백업합니다 (하루 한 번, 지난 일정까지 전부 · 백업 파일은 지우지 않고 보관). 웹이 잘못 바뀌어도 '백업에서 복원'으로 되돌릴 수 있습니다.",
                  foreground="#868e96", wraplength=520, justify="left").pack(anchor="w", pady=(6, 0))
        self.lbl_stat = ttk.Label(f, text="", foreground="#868e96", wraplength=520, justify="left")
        self.lbl_stat.pack(anchor="w", pady=(6, 0))
        self.cl.listeners.append(self.refresh)
        w.bind("<Destroy>", lambda e: self.cl.listeners.remove(self.refresh)
               if e.widget is w and self.refresh in self.cl.listeners else None)
        self.refresh()
        w.update_idletasks()
        sw, sh = w.winfo_screenwidth(), w.winfo_screenheight()
        w.geometry(f"+{max(0, (sw - w.winfo_reqwidth()) // 2)}+{max(0, min((sh - w.winfo_reqheight()) // 3, sh - w.winfo_reqheight() - 60))}")

    def check_appr(self):
        self.cl.set_status("승인 상태를 확인하는 중…")
        self.cl.check_approval()

    def req_appr(self):
        if not self.cl.logged_in():
            messagebox.showinfo("사용 신청", "먼저 구글 로그인을 하세요.", parent=self.win)
            return
        d = tk.Toplevel(self.win)
        d.title("사용 신청")
        d.resizable(False, False)
        d.transient(self.win)
        f = ttk.Frame(d, padding=14)
        f.pack(fill="both", expand=True)
        ttk.Label(f, text="관리자가 승인할 때 확인합니다. 모두 입력해 주세요.").grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 8))
        vs = {k: tk.StringVar() for k in ("agency", "dept", "pname")}
        ents = []
        for i, (k, lab) in enumerate((("agency", "기관"), ("dept", "부서"), ("pname", "이름"))):
            ttk.Label(f, text=lab).grid(row=i + 1, column=0, sticky="w", pady=3)
            e = ttk.Entry(f, textvariable=vs[k], width=28)
            e.grid(row=i + 1, column=1, padx=(10, 0), pady=3)
            ents.append(e)

        def send():
            vals = {k: v.get().strip() for k, v in vs.items()}
            if not all(vals.values()):
                messagebox.showwarning("사용 신청", "기관, 부서, 이름을 모두 입력하세요.", parent=d)
                return
            d.destroy()
            self.cl.set_status("신청하는 중…")
            self.cl.request_approval(vals["agency"], vals["dept"], vals["pname"])
        bf = ttk.Frame(f)
        bf.grid(row=4, column=0, columnspan=2, sticky="e", pady=(10, 0))
        ttk.Button(bf, text="신청", style="Accent.TButton", command=send).pack(side="left", padx=4)
        ttk.Button(bf, text="취소", command=d.destroy).pack(side="left", padx=4)
        d.bind("<Return>", lambda e: send())
        d.update_idletasks()
        d.geometry(f"+{self.win.winfo_x() + 40}+{self.win.winfo_y() + 60}")
        ents[0].focus_set()

    def open_backup_dir(self):
        try:
            os.makedirs(BACKUP_DIR, exist_ok=True)
            os.startfile(BACKUP_DIR)
        except Exception:
            webbrowser.open(BACKUP_DIR)

    def restore_backup(self):
        app = self.app
        os.makedirs(BACKUP_DIR, exist_ok=True)
        path = filedialog.askopenfilename(parent=self.win, title="복원할 백업 파일 선택", initialdir=BACKUP_DIR,
                                          filetypes=[("일정 백업", "*.json")])
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                d = json.load(f)
            evs = [norm_event(e) for e in d.get("events", []) if isinstance(e, dict) and "id" in e]
        except Exception as ex:
            messagebox.showerror("복원", f"백업 파일을 읽을 수 없습니다.\n{ex}", parent=self.win)
            return
        if not messagebox.askyesno("복원", f"백업의 일정 {len(evs)}건으로 되돌릴까요?\n"
                                          f"(백업 시각: {d.get('saved', '?')})\n\n"
                                          "지금 일정은 따로 백업해 두고, 복원한 내용은 클라우드(웹)에도 다시 올립니다.", parent=self.win):
            return
        make_backup(app.events, app.tomb, app.alarms, "복원 직전")
        now = int(time.time() * 1000)
        for e in evs:
            e["upd"] = now          # 클라우드에 있는 값보다 새것으로 만들어 웹까지 덮어쓰게 함
        frm = str(d.get("from") or "")
        ids = {e["id"] for e in evs}
        kept = [e for e in app.events if e["id"] not in ids and bool(frm) and event_last(e) < frm]   # 백업 범위 밖(오래된) 일정은 그대로 둠
        app.events[:] = kept + evs
        app.tomb[:] = []
        app.cfg["events"], app.cfg["tomb"] = app.events, app.tomb
        save_config(app.cfg)
        if app.cal.alive():
            app.cal.redraw()
        app.update_next()
        self.cl.c["since"] = {}      # 다음 동기화는 전체 확인
        self.cl.request_sync(0)
        self.cl.set_status(f"일정 {len(evs)}건을 복원했습니다. 클라우드에도 반영합니다.")

    def sync_now(self):
        if self.cl.logged_in() and not self.cl.approved():
            self.cl.set_status("승인 후에 동기화할 수 있습니다. " + self.cl.approval_text())
            return
        self.cl.force_read = True       # 이 버튼은 클라우드에서 최신 일정도 내려받는다(읽기)
        self.cl.request_sync(0)

    def alive(self):
        try:
            return bool(self.win.winfo_exists())
        except tk.TclError:
            return False

    def save_conf(self):
        self.cl.c["conf"] = {k: v.get().strip() for k, v in self.v_conf.items()}
        save_config(self.app.cfg)
        self.cl.set_status("연결 정보를 저장했습니다.")

    def refresh(self):
        if not self.alive():
            return
        u = self.cl.c.get("user", {})
        li = self.cl.logged_in()
        self.lbl_user.config(text=f'{u.get("name", "")} ({u.get("email", "")})' if li else "로그인하지 않았습니다.")
        ap = self.cl.c.get("approval", "")
        self.lbl_appr.config(text=self.cl.approval_text() if li else "로그인한 뒤 사용 신청을 할 수 있습니다.")
        self.btn_req.state(["!disabled"] if (li and ap in ("none", "")) else ["disabled"])
        self.btn_chk.state(["!disabled"] if li else ["disabled"])
        self.btn_in.state(["disabled"] if li else ["!disabled"])
        self.btn_out.state(["!disabled"] if li else ["disabled"])
        self.lbl_stat.config(text=self.cl.status)

    def login(self):
        if not self.cl.configured():
            self.save_conf()
        if not self.cl.configured():
            messagebox.showinfo(APP_NAME, "연결 정보 3개를 모두 입력하세요.", parent=self.win)
            return
        self.cl.set_status("브라우저가 열립니다. 구글 계정으로 로그인하세요…")

        def done(r, e):
            if e:
                messagebox.showwarning(APP_NAME, str(e), parent=self.win if self.alive() else None)
                self.cl.set_status(f"로그인 실패: {e}")
            else:
                self.cl.set_status("로그인했습니다.")
                messagebox.showinfo(APP_NAME, "로그인했습니다.\n\nPC에서 저장한 일정은 smartgong.kr 초기화면 좌측 상단 '앱 목록'에서 조회할 수 있습니다.",
                                    parent=self.win if self.alive() else None)
            self.refresh()
        self.cl.login(done)

    def logout(self):
        if messagebox.askyesno(APP_NAME, "로그아웃할까요?\n(이 PC의 일정은 그대로 남습니다.)", parent=self.win):
            self.cl.logout()
            self.refresh()


# ================================================================ 앱
class App:
    def __init__(self, start_hidden=False):
        self.cfg = load_config()
        self.alarms = self.cfg["alarms"]
        self.events = self.cfg["events"]
        self.tomb = self.cfg["tomb"]
        self.cloud_dlg = None
        self.ev_dlg = None
        for p in self.cfg["style"].get("font_files", []):
            register_font(p)
        self.snoozes = []        # 알람 항목 + "at"
        self.active = []         # 현재 울리는 항목
        self.popup = None
        self.style_dlg = None
        self.repeat_job = None
        self.turn_tts = False
        self.speaker = Speaker()
        self.player = AudioPlayer()
        self.ot_stopped = ""                      # 오늘은 팝업 중지를 누른 날짜
        self.ot_next = time.time() + int(self.cfg["ot"].get("every", 60)) * 60
        self.ot_last = None                       # 초과근무 알람을 마지막으로 울린 (날짜, 분)
        self.ot_anchor = None                     # 팝업에서 지정한 다음 알림 시각 (날짜, 분)
        self.cmdq = queue.Queue()
        self.notice = self.cfg.get("notice") if isinstance(self.cfg.get("notice"), dict) else {}
        self.local_notice = ""
        self.tray = None
        self.last_min = int(time.time() // 60)
        self.ui_widgets = []
        self.pomo_dlg = None
        self.pomo = {"phase": "work", "run": False, "left": self.cfg["pomo"]["work"] * 60, "end": 0, "done": 0}
        self.hd_vals = {"clock": "", "date": "", "next": ""}
        self.hd_ids = {}
        self.hd_photo = self.hd_mascot = None

        self.root = tk.Tk()
        self.root.title(APP_NAME)
        try:
            self._win_icon = ImageTk.PhotoImage(app_icon_image(64))
            self.root.iconphoto(True, self._win_icon)
        except Exception:
            pass
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        self.root.geometry(f"{min(1000, sw - 40)}x{min(860, sh - 90)}+20+20")
        self.root.minsize(380, 360)
        self.root.protocol("WM_DELETE_WINDOW", self.hide_window)
        self._init_vars()
        self.pomo_var = tk.StringVar(master=self.root)
        self.pomo_btn_var = tk.StringVar(master=self.root, value="시작")
        self.cal = CalendarWidget(self)
        self.cloud = CloudSync(self)
        self.apply_ui()
        self.fit_window()
        self._start_tray()
        if self.cfg["cal"].get("show"):
            self.root.after(400, self.cal.show)

        if start_hidden and self.tray:
            self.root.withdraw()

        self.root.after(1000, self.tick)
        self.root.after(200, self.poll_cmds)
        self.root.after(4000, self.cloud.periodic)
        self.root.after(6000, self.fetch_notice)

    # ---------- 입력 변수 (화면을 다시 만들어도 값 유지)
    def _init_vars(self):
        self.var_label = tk.StringVar()
        self.var_mode = tk.StringVar(value="정시")
        self.var_beep = tk.BooleanVar(value=True)
        self.var_tts = tk.BooleanVar(value=True)
        self.t_h, self.t_m = tk.StringVar(value="09"), tk.StringVar(value="00")
        self.s_h, self.s_m = tk.StringVar(value="09"), tk.StringVar(value="00")
        self.e_h, self.e_m = tk.StringVar(value="18"), tk.StringVar(value="00")
        self.v_every = tk.StringVar(value="60")
        self.day_vars = [tk.BooleanVar(value=i < 5) for i in range(7)]
        self.var_date = tk.StringVar(value=datetime.date.today().isoformat())
        self.var_from, self.var_to = tk.StringVar(), tk.StringVar()
        self.var_img = tk.StringVar()
        self.var_sound = tk.StringVar()
        self.var_rate = tk.IntVar(value=int(self.cfg.get("rate", 0)))
        self.var_auto = tk.BooleanVar(value=get_autostart())

    # ---------- 테마(글꼴/색) 적용
    def apply_ui(self):
        u = dict(DEFAULT_UI)
        u.update(self.cfg.get("ui", {}))
        self.theme = u
        fam = u["font"] or pick_font(self.root)
        size = max(9, min(40, int(u["size"])))
        self.ui_family, self.ui_size = fam, size
        for n in ("TkDefaultFont", "TkTextFont", "TkMenuFont", "TkHeadingFont", "TkCaptionFont",
                  "TkSmallCaptionFont", "TkIconFont", "TkTooltipFont"):
            try:
                tkfont.nametofont(n).configure(family=fam, size=size)
            except tk.TclError:
                pass
        self.f_bold = tkfont.Font(root=self.root, family=fam, size=size, weight="bold")
        self.f_clock = tkfont.Font(root=self.root, family=fam, size=int(size * 2.6), weight="bold")
        self.f_name = tkfont.Font(root=self.root, family=fam, size=int(size * 1.7), weight="bold")
        self.f_small = tkfont.Font(root=self.root, family=fam, size=max(8, int(size * 0.85)))
        self.f_norm = tkfont.Font(root=self.root, family=fam, size=size)
        self._style_ttk()
        self.root.configure(bg=u["bg"])
        for w in self.ui_widgets:
            try:
                w.destroy()
            except tk.TclError:
                pass
        self.ui_widgets = []
        self._build_ui()
        self.refresh_list()
        if getattr(self, "cal", None):
            self.cal.refresh_theme()

    def _style_ttk(self):
        u, fam, size = self.theme, self.ui_family, self.ui_size
        st = ttk.Style(self.root)
        try:
            st.theme_use("clam")
        except tk.TclError:
            pass
        bg, card, fg, acc = u["bg"], u["card"], u["fg"], u["accent"]
        btn, btn_act, line = "#e9ecef", "#dee2e6", "#ced4da"
        st.configure(".", background=card, foreground=fg, font=(fam, size), bordercolor=line)
        st.configure("Win.TFrame", background=bg)
        st.configure("Win.TLabel", background=bg, foreground=fg)
        st.configure("TLabelframe", background=card, bordercolor=line)
        st.configure("TLabelframe.Label", background=card, foreground=fg, font=(fam, size, "bold"))
        st.configure("TNotebook", background=card, bordercolor=line, tabmargins=(2, 4, 2, 0))
        st.configure("TNotebook.Tab", padding=(18, 7), font=(fam, size, "bold"),
                     background="#dee2e6", foreground="#495057")
        st.map("TNotebook.Tab", background=[("selected", acc)], foreground=[("selected", "#ffffff")],
               padding=[("selected", (18, 7))], expand=[("selected", (0, 0, 0, 0))])
        st.configure("TButton", background=btn, foreground=fg, padding=(10, 5), relief="flat", borderwidth=1)
        st.map("TButton", background=[("active", btn_act), ("pressed", btn_act)])
        st.configure("Accent.TButton", background=acc, foreground="#ffffff", padding=(14, 6),
                     font=(fam, size, "bold"))
        st.configure("Title.TLabel", background=acc, foreground="#ffffff", padding=(14, 6), font=(fam, size, "bold"))
        st.configure("Box.TFrame", background=card, relief="solid", borderwidth=1, bordercolor=line)
        st.map("Accent.TButton", background=[("active", darker(acc)), ("pressed", darker(acc, 0.7))],
               foreground=[("active", "#ffffff")])
        st.configure("TCheckbutton", background=card, foreground=fg)
        st.map("TCheckbutton", background=[("active", card)])
        st.configure("TRadiobutton", background=card, foreground=fg)
        st.map("TRadiobutton", background=[("active", card)])
        self._apply_check_style(st, size, acc)
        for w in ("TEntry", "TCombobox", "TSpinbox"):
            st.configure(w, fieldbackground="#ffffff", foreground="#212529", padding=4)
        st.map("TCombobox", fieldbackground=[("readonly", "#ffffff")], foreground=[("readonly", "#212529")])
        st.configure("Treeview", background="#ffffff", fieldbackground="#ffffff", foreground="#212529",
                     rowheight=int(size * 2.4), font=(fam, size), borderwidth=0)
        st.map("Treeview", background=[("selected", acc)], foreground=[("selected", "#ffffff")])
        st.configure("Treeview.Heading", background=btn, foreground=fg, font=(fam, size, "bold"), padding=5)
        st.configure("TScrollbar", background=btn, troughcolor=bg, bordercolor=line, arrowcolor=fg)
        st.configure("TSizegrip", background=bg)
        self.root.option_add("*TCombobox*Listbox.font", (fam, size))

    def _apply_check_style(self, st, size, acc):
        """체크박스 표시를 X 대신 체크(✓) 모양으로 교체"""
        if not HAS_PIL:
            return
        try:
            px = max(16, int(size * 1.55))
            S = 4
            big = px * S

            def box(checked):
                im = Image.new("RGBA", (big, big), (0, 0, 0, 0))
                d = ImageDraw.Draw(im)
                d.rounded_rectangle((S, S, big - S - 1, big - S - 1), radius=int(big * 0.18),
                                    fill=acc if checked else "#ffffff",
                                    outline=acc if checked else "#868e96", width=int(S * 1.5))
                if checked:
                    d.line([(big * 0.23, big * 0.53), (big * 0.42, big * 0.72), (big * 0.79, big * 0.29)],
                           fill="#ffffff", width=int(big * 0.13), joint="curve")
                return ImageTk.PhotoImage(im.resize((px, px), _RES.LANCZOS))

            self._chk_imgs = (box(False), box(True))
            self._elem_n = getattr(self, "_elem_n", 0) + 1
            name = f"chkmark{self._elem_n}"
            st.element_create(name, "image", self._chk_imgs[0], ("selected", self._chk_imgs[1]), sticky="")
            st.layout("TCheckbutton", [("Checkbutton.padding", {"sticky": "nswe", "children": [
                (name, {"side": "left", "sticky": ""}),
                ("Checkbutton.focus", {"side": "left", "sticky": "w", "children": [
                    ("Checkbutton.label", {"sticky": "nswe"})]})]})])

            def radio(checked):   # 라디오 버튼도 같은 크기로
                im = Image.new("RGBA", (big, big), (0, 0, 0, 0))
                d = ImageDraw.Draw(im)
                d.ellipse((S, S, big - S - 1, big - S - 1), fill="#ffffff",
                          outline=acc if checked else "#868e96", width=int(S * 1.5))
                if checked:
                    m = int(big * 0.29)
                    d.ellipse((m, m, big - m - 1, big - m - 1), fill=acc)
                return ImageTk.PhotoImage(im.resize((px, px), _RES.LANCZOS))

            self._rad_imgs = (radio(False), radio(True))
            rname = f"radmark{self._elem_n}"
            st.element_create(rname, "image", self._rad_imgs[0], ("selected", self._rad_imgs[1]), sticky="")
            st.layout("TRadiobutton", [("Radiobutton.padding", {"sticky": "nswe", "children": [
                (rname, {"side": "left", "sticky": ""}),
                ("Radiobutton.focus", {"side": "left", "sticky": "w", "children": [
                    ("Radiobutton.label", {"sticky": "nswe"})]})]})])
        except Exception as e:
            print("체크 표시 스타일 적용 실패:", e)

    # ---------- 상단 시계 영역
    def _build_header(self):
        u = self.theme
        lh = lambda f: f.metrics("linespace")
        h = int(lh(self.f_clock) + lh(self.f_norm) + lh(self.f_bold) + 26)
        cv = tk.Canvas(self.root, height=h, highlightthickness=0, bd=0, bg=u["head_bg"])
        cv.pack(side="top", fill="x")
        cv.bind("<Configure>", lambda e: self.draw_header(e.width))
        self.hd, self.hd_h = cv, h
        self.hd_ids = {}
        self.ui_widgets.append(cv)

    def draw_header(self, w):
        u, cv, h = self.theme, self.hd, self.hd_h
        cv.delete("all")
        self.hd_photo = self.hd_mascot = None
        has_img = False
        if HAS_PIL and u.get("head_img") and os.path.isfile(u["head_img"]):
            try:
                self.hd_photo = ImageTk.PhotoImage(cover_image(u["head_img"], max(1, w), h))
                cv.create_image(0, 0, image=self.hd_photo, anchor="nw")
                has_img = True
            except Exception:
                self.hd_photo = None
        mw = 0
        if HAS_PIL and u.get("head_mascot", True):
            try:
                im = fit_image(default_image(), 300, h - 10, 1.0)
                self.hd_mascot = ImageTk.PhotoImage(im)
                cv.create_image(14, h / 2, image=self.hd_mascot, anchor="w")
                mw = im.width + 28
            except Exception:
                self.hd_mascot = None
        iw = 0
        self.hd_sg = None
        if HAS_PIL:
            try:
                src = Image.open(io.BytesIO(base64.b64decode(SG_IMG_B64))).convert("RGBA")
                im = fit_image(src, 300, h - 10, 9)
                self.hd_sg = ImageTk.PhotoImage(im)
                cv.create_image(w - 14, h / 2, image=self.hd_sg, anchor="e", tags=("sg",))
                cv.tag_bind("sg", "<Button-1>", lambda e: self.open_sg())
                cv.tag_bind("sg", "<Enter>", lambda e: cv.config(cursor="hand2"))
                cv.tag_bind("sg", "<Leave>", lambda e: cv.config(cursor=""))
                iw = im.width + 28
            except Exception:
                self.hd_sg = None
        fg = u["head_fg"]
        sc = "#000000" if luminance(fg) > 140 else "#ffffff"
        # 로고(마스코트) 오른쪽: 프로그램 아이콘 + 이름
        nb = 0
        self.hd_appicon = None
        if HAS_PIL:
            try:
                isz = max(32, min(76, h - 22))
                tw = self.f_name.measure(APP_NAME)
                clk = self.f_clock.measure("00:00:00") + 40
                room = w - mw - iw - clk
                show_name = room >= isz + 12 + tw
                if show_name or room >= isz + 8:
                    self.hd_appicon = ImageTk.PhotoImage(app_icon_image(isz))
                    cv.create_image(mw, h / 2, image=self.hd_appicon, anchor="w")
                    nb = isz + 8
                    if show_name:
                        tx = mw + isz + 12
                        if has_img:
                            for dx, dy in ((-2, 0), (2, 0), (0, -2), (0, 2)):
                                cv.create_text(tx + dx, h / 2 + dy, text=APP_NAME, font=self.f_name, fill=sc, anchor="w")
                        cv.create_text(tx, h / 2, text=APP_NAME, font=self.f_name, fill=fg, anchor="w")
                        nb = isz + 12 + tw + 8
            except Exception:
                self.hd_appicon = None
                nb = 0
        # 가운데 '광고 창': 로고·이름 오른쪽부터 스마트공 아이콘 왼쪽까지. 지금은 비워 두고(점선 틀만),
        # 공지/안내가 있을 때만 그 안에 글을 보여 준다. (나중에 광고 배너가 여기에 연결된다)
        self.hd_ids = {}
        self.ad_box = None
        x0, x1 = mw + nb + 12, w - iw + 4
        x1 = min(x1, x0 + int(w * 0.30))   # 전체 가로의 30%
        y0, y1 = 8, h - 8
        if x1 - x0 >= 80:
            self.ad_box = (x0, y0, x1, y1)
            items = self.notice_items()
            if not items:
                cv.create_rectangle(x0, y0, x1, y1, outline="", fill="", tags=("adslot",))
            else:
                warn = any(lv == "warn" for lv, _ in items)
                bgc, bdc, tcol = ("#fff0f0", "#e03131", "#a61e1e") if warn else ("#fff9db", u["accent"], "#4a2f00")
                cv.create_rectangle(x0, y0, x1, y1, fill=bgc, outline="", width=0, tags=("notice",))
                fnt = self.f_small
                maxw, lines, cur = (x1 - x0) - 22, [], ""
                full = "  ".join(t for _, t in items)
                for chn in full:
                    if fnt.measure(cur + chn) > maxw:
                        lines.append(cur)
                        cur = chn
                        if len(lines) == 3:
                            break
                    else:
                        cur += chn
                if len(lines) < 3 and cur:
                    lines.append(cur)
                if len(lines) == 3 and len("".join(lines)) < len(full):
                    lines[2] = lines[2][:-1] + "…"
                cv.create_text(x0 + 11, h / 2, text="\n".join(lines), font=fnt, fill=tcol, anchor="w", tags=("notice",))
                cv.tag_bind("notice", "<Button-1>", lambda e: self.show_notice())
                cv.tag_bind("notice", "<Enter>", lambda e: cv.config(cursor="hand2"))
                cv.tag_bind("notice", "<Leave>", lambda e: cv.config(cursor=""))

    def open_sg(self):
        webbrowser.open(SG_URL)

    # ---------- 공지 (헤더 시계 오른쪽)
    def notice_items(self):
        """[(수준, 글)] 목록: 한도 초과 같은 PC 안내 → 관리자 공지 → 새 버전 안내 순"""
        out = []
        if self.local_notice:
            out.append(("warn", self.local_notice))
        n = self.notice if isinstance(self.notice, dict) else {}
        if str(n.get("text", "")).strip():
            out.append((n.get("level") if n.get("level") in ("info", "warn") else "info", str(n["text"]).strip()[:300]))
        return out

    def notice_link(self):
        n = self.notice if isinstance(self.notice, dict) else {}
        for k in ("link",):
            u = str(n.get(k, "")).strip()
            if u.startswith("https://"):
                return u
        return ""

    def redraw_header(self):
        try:
            self.draw_header(self.hd.winfo_width())
        except Exception:
            pass

    def set_local_notice(self, text):
        if text != self.local_notice:
            self.local_notice = text
            self.redraw_header()

    def fetch_notice(self):
        """공지 파일(notice.json)을 읽어 온다. 실패하면 조용히 넘어가고 저장해 둔 공지를 계속 보여 준다."""
        try:
            base = self.cloud.conf().get("loginUrl", "")
        except Exception:
            base = ""
        if base.startswith("https://"):
            url = urllib.parse.urljoin(base, "notice.json")

            def work():
                try:
                    req = urllib.request.Request(url, headers={"Cache-Control": "no-cache"})
                    with urllib.request.urlopen(req, timeout=8) as r:
                        d = json.loads(r.read().decode("utf-8"))
                    if isinstance(d, dict):
                        self.cmdq.put(("call", lambda: self._apply_notice(d)))
                except Exception:
                    pass
            threading.Thread(target=work, daemon=True).start()
        self.root.after(NOTICE_EVERY_S * 1000, self.fetch_notice)

    def _apply_notice(self, d):
        keep = {k: d.get(k, "") for k in ("id", "text", "level", "link")}
        if keep != self.notice:
            self.notice = keep
            self.cfg["notice"] = keep
            save_config(self.cfg)
            self.redraw_header()

    def show_notice(self):
        items = self.notice_items()
        if not items:
            return
        link = self.notice_link()
        text = "\n\n".join(t for _, t in items)
        if link:
            if messagebox.askyesno(APP_NAME, text + "\n\n링크를 열까요?", parent=self.root):
                webbrowser.open(link)
        else:
            messagebox.showinfo(APP_NAME, text, parent=self.root)

    def hd_set(self, key, text):
        self.hd_vals[key] = text
        for i in self.hd_ids.get(key, []):
            try:
                self.hd.itemconfig(i, text=text)
            except tk.TclError:
                pass

    # ---------- UI
    def _build_ui(self):
        r, u = self.root, self.theme
        fam, size = self.ui_family, self.ui_size
        k = size / 10.0

        self._build_header()

        bottom = ttk.Frame(r, style="Win.TFrame")
        bottom.pack(side="bottom", fill="x")
        ttk.Label(bottom, text="※ 창을 닫아도 트레이에서 계속 동작합니다. 완전히 끄려면 트레이 아이콘 → 종료.",
                  style="Win.TLabel").pack(side="left", padx=12, pady=4)
        ttk.Sizegrip(bottom).pack(side="right", anchor="se")      # 우측 하단 크기 조절
        self.ui_widgets.append(bottom)

        sf = ScrollFrame(r, u["bg"], "Win.TFrame", hscroll=True)
        sf.pack(fill="both", expand=True)
        self.ui_widgets.append(sf)
        self.sf, self.bottom_bar = sf, bottom
        body = sf.inner

        # 뽀모도로
        # 한 줄: [🍅 뽀모도로(강조색 바탕·흰 글씨)]  일하는 시간 25:00 · 오늘 0회 완료 ........ [시작][건너뛰기][초기화][설정]
        pf = ttk.Frame(body, style="Box.TFrame", padding=(8, 6))
        pf.pack(fill="x", padx=12, pady=(10, 0))
        ttk.Label(pf, text="🍅 뽀모도로", style="Title.TLabel").pack(side="left", padx=(0, 12))
        ttk.Label(pf, textvariable=self.pomo_var, font=self.f_bold).pack(side="left")
        ttk.Button(pf, textvariable=self.pomo_btn_var, width=8, command=self.pomo_toggle).pack(side="left", padx=(16, 4))
        for text, cmd in (("건너뛰기", self.pomo_skip), ("초기화", self.pomo_reset), ("설정", self.open_pomo_settings)):
            ttk.Button(pf, text=text, width=8, command=cmd).pack(side="left", padx=(0, 4))
        self.pomo_refresh()

        # 알람 목록
        mid = ttk.Frame(body, style="Win.TFrame")
        mid.pack(fill="x", padx=12, pady=(10, 0))
        cols = ("time", "label", "repeat", "alert", "state")
        self.tree = ttk.Treeview(mid, columns=cols, show="headings", height=5, selectmode="browse")
        for c, t, w in (("time", "시각/날짜", 200), ("label", "이름", 240), ("repeat", "반복", 200),
                        ("alert", "방식", 100), ("state", "상태", 90)):
            self.tree.heading(c, text=t)
            self.tree.column(c, width=int(w * k), anchor="w")
        sb = ttk.Scrollbar(mid, command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="x", expand=True)
        sb.pack(side="right", fill="y")
        self.tree.bind("<<TreeviewSelect>>", self.on_select)

        btns = ttk.Frame(body, style="Win.TFrame")
        btns.pack(fill="x", padx=12, pady=8)
        for text, cmd in (("켜기/끄기", self.toggle_sel), ("테스트", self.test_sel), ("삭제", self.delete_sel)):
            ttk.Button(btns, text=text, command=cmd).pack(side="left", padx=(0, 6))

        # 알람 추가/수정
        form = ttk.LabelFrame(body, text=" 알람 추가 / 수정 ", padding=10)
        form.pack(fill="x", padx=12, pady=6)
        form.columnconfigure(1, weight=1)

        ttk.Label(form, text="이름(읽어줄 문구)").grid(row=0, column=0, sticky="w")
        ttk.Entry(form, textvariable=self.var_label).grid(row=0, column=1, columnspan=3, sticky="we", pady=3)

        ttk.Label(form, text="반복 방식").grid(row=1, column=0, sticky="w")
        rm = ttk.Frame(form)
        rm.grid(row=1, column=1, columnspan=3, sticky="w", pady=3)
        for txt, val in (("정시 (정해진 시각)", "정시"), ("간격 (N분마다)", "간격"), ("날짜 지정 (특정일 1회)", "날짜")):
            ttk.Radiobutton(rm, text=txt, value=val, variable=self.var_mode,
                            command=self.switch_mode).pack(side="left", padx=(0, 14))

        self.holder = ttk.Frame(form)
        self.holder.grid(row=2, column=0, columnspan=4, sticky="w", pady=4)
        self.f_time = ttk.Frame(self.holder)
        ttk.Label(self.f_time, text="시각").pack(side="left")
        self._hm(self.f_time, self.t_h, self.t_m)

        self.f_int = ttk.Frame(self.holder)
        ttk.Label(self.f_int, text="시작").pack(side="left")
        self._hm(self.f_int, self.s_h, self.s_m)
        ttk.Label(self.f_int, text="   종료").pack(side="left")
        self._hm(self.f_int, self.e_h, self.e_m)
        ttk.Label(self.f_int, text="   간격(분)").pack(side="left")
        ttk.Spinbox(self.f_int, from_=1, to=720, width=5, textvariable=self.v_every).pack(side="left", padx=6)

        self.f_date = ttk.Frame(self.holder)
        ttk.Label(self.f_date, text="날짜").pack(side="left")
        ttk.Entry(self.f_date, textvariable=self.var_date, width=12).pack(side="left", padx=6)
        ttk.Button(self.f_date, text="달력", command=lambda: self.pick_date(self.var_date)).pack(side="left")
        ttk.Label(self.f_date, text="     시각").pack(side="left")
        self._hm(self.f_date, self.t_h, self.t_m)

        self.dayf = ttk.Frame(form)
        self.dayf.grid(row=3, column=0, columnspan=4, sticky="w", pady=3)
        ttk.Label(self.dayf, text="요일").pack(side="left", padx=(0, 6))
        for i, n in enumerate(DAY_NAMES):
            ttk.Checkbutton(self.dayf, text=n, variable=self.day_vars[i]).pack(side="left", padx=2)
        for text, days in (("매일", range(7)), ("평일", range(5)), ("주말", (5, 6))):
            ttk.Button(self.dayf, text=text, width=5, command=lambda d=days: self.set_days(d)).pack(
                side="left", padx=(10 if text == "매일" else 2, 0))

        self.f_period = ttk.Frame(form)
        self.f_period.grid(row=4, column=0, columnspan=4, sticky="w", pady=3)
        ttk.Label(self.f_period, text="적용 기간(선택)").pack(side="left")
        ttk.Entry(self.f_period, textvariable=self.var_from, width=12).pack(side="left", padx=(8, 2))
        ttk.Button(self.f_period, text="달력", command=lambda: self.pick_date(self.var_from)).pack(side="left")
        ttk.Label(self.f_period, text="  ~  ").pack(side="left")
        ttk.Entry(self.f_period, textvariable=self.var_to, width=12).pack(side="left", padx=(0, 2))
        ttk.Button(self.f_period, text="달력", command=lambda: self.pick_date(self.var_to)).pack(side="left")
        ttk.Button(self.f_period, text="기간 지움",
                   command=lambda: (self.var_from.set(""), self.var_to.set(""))).pack(side="left", padx=8)
        ttk.Label(self.f_period, text="(비우면 계속 반복)", foreground="#868e96").pack(side="left")
        self.switch_mode()

        ttk.Label(form, text="이 알람의 이미지").grid(row=5, column=0, sticky="w", pady=(8, 0))
        rf = ttk.Frame(form)
        rf.grid(row=5, column=1, columnspan=3, sticky="we", pady=(8, 0))
        ttk.Entry(rf, textvariable=self.var_img).pack(side="left", fill="x", expand=True)
        ttk.Button(rf, text="선택", command=lambda: self.browse(self.var_img, "img")).pack(side="left", padx=3)
        ttk.Button(rf, text="지움", command=lambda: self.var_img.set("")).pack(side="left")
        ttk.Label(form, text="이 알람의 소리파일").grid(row=6, column=0, sticky="w", pady=(3, 0))
        sf2 = ttk.Frame(form)
        sf2.grid(row=6, column=1, columnspan=3, sticky="we", pady=(3, 0))
        ttk.Entry(sf2, textvariable=self.var_sound).pack(side="left", fill="x", expand=True)
        ttk.Button(sf2, text="선택", command=lambda: self.browse(self.var_sound, "audio")).pack(side="left", padx=3)
        ttk.Button(sf2, text="지움", command=lambda: self.var_sound.set("")).pack(side="left")
        ttk.Button(sf2, text="▶", width=3, command=self.play_form_sound).pack(side="left", padx=(6, 2))
        ttk.Button(sf2, text="■", width=3, command=self.player.stop).pack(side="left")
        ttk.Label(form, text="※ 비워두면 '꾸미기 설정'에서 정한 이미지/소리를 사용합니다.",
                  foreground="#868e96").grid(row=7, column=0, columnspan=4, sticky="w", pady=(2, 0))

        ttk.Label(form, text="알림 방식").grid(row=8, column=0, sticky="w", pady=(6, 0))
        af = ttk.Frame(form)
        af.grid(row=8, column=1, columnspan=3, sticky="w", pady=(6, 0))
        ttk.Checkbutton(af, text="알림음/소리파일", variable=self.var_beep).pack(side="left")
        ttk.Checkbutton(af, text="음성으로 읽기", variable=self.var_tts).pack(side="left", padx=14)

        fb = ttk.Frame(form)
        fb.grid(row=9, column=0, columnspan=4, sticky="w", pady=(10, 0))
        ttk.Button(fb, text="＋ 새 알람 등록", style="Accent.TButton", command=self.add_alarm).pack(side="left")
        ttk.Button(fb, text="선택한 알람 수정 저장", command=self.update_alarm).pack(side="left", padx=8)

        # 설정
        st = ttk.LabelFrame(body, text=" 설정 ", padding=10)
        st.pack(fill="x", padx=12, pady=(8, 4), before=mid)
        ttk.Label(st, text="음성 속도").pack(side="left")
        tk.Scale(st, from_=-5, to=5, orient="horizontal", length=int(130 * k), variable=self.var_rate,
                 bg=u["card"], fg=u["fg"], troughcolor="#ced4da", highlightthickness=0, bd=0,
                 font=(fam, size)).pack(side="left", padx=6)
        ttk.Button(st, text="음성 테스트", command=self.test_voice).pack(side="left", padx=4)
        ttk.Button(st, text="🎨 꾸미기 설정", style="Accent.TButton", command=self.open_style).pack(side="left", padx=10)
        ttk.Checkbutton(st, text="Windows 시작 시 자동 실행", variable=self.var_auto,
                        command=self.on_autostart).pack(side="left", padx=6)

        ot = self.cfg["ot"]
        of = ttk.LabelFrame(body, text=" 초과근무 알람 ", padding=10)
        of.pack(fill="x", padx=12, pady=(0, 4), before=mid)
        self.v_ot_on = tk.BooleanVar(value=ot["enabled"])
        self.v_ot_hol = tk.BooleanVar(value=ot["holiday"])
        self.v_ot_every = tk.StringVar(value=str(ot["every"]))
        self.v_ot_sh, self.v_ot_sm = tk.StringVar(value=ot["start"][:2]), tk.StringVar(value=ot["start"][3:])
        self.v_ot_eh, self.v_ot_em = tk.StringVar(value=ot["end"][:2]), tk.StringVar(value=ot["end"][3:])
        self.v_ot_text = tk.StringVar(value=ot["text"])
        ttk.Checkbutton(of, text="사용", variable=self.v_ot_on, command=self.save_ot).pack(side="left")
        ttk.Label(of, text="  업무시간").pack(side="left")
        self._hm(of, self.v_ot_sh, self.v_ot_sm)
        ttk.Label(of, text="~").pack(side="left", padx=2)
        self._hm(of, self.v_ot_eh, self.v_ot_em)
        ttk.Label(of, text="  이후 · 알림 간격").pack(side="left")
        ttk.Spinbox(of, from_=5, to=480, increment=5, width=4, textvariable=self.v_ot_every).pack(side="left", padx=(4, 0))
        ttk.Label(of, text="분").pack(side="left", padx=(2, 6))
        ttk.Checkbutton(of, text="휴일(주말·공휴일) 하루 종일", variable=self.v_ot_hol, command=self.save_ot).pack(side="left", padx=6)
        ttk.Button(of, text="적용", command=self.save_ot).pack(side="left", padx=4)
        ttk.Button(of, text="테스트", command=self.test_ot).pack(side="left")
        of2 = ttk.Frame(body, style="Win.TFrame")
        of2.pack(fill="x", padx=12, pady=(0, 4), before=mid)
        ttk.Label(of2, text="초과근무 알림 문구", style="Win.TLabel").pack(side="left")
        ttk.Entry(of2, textvariable=self.v_ot_text, width=44).pack(side="left", padx=6)
        ttk.Label(of2, text="※ '오늘은 팝업 중지' = 오늘 하루 알림 중지",
                  style="Win.TLabel").pack(side="left")

        cf = ttk.LabelFrame(body, text=" 달력(일정) 위젯 ", padding=10)
        cf.pack(fill="x", padx=12, pady=(0, 6), before=mid)
        ttk.Button(cf, text="📅 달력 켜기/끄기", style="Accent.TButton", command=self.toggle_cal).pack(side="left")
        ttk.Button(cf, text="⚙ 투명도·고정 설정", command=lambda: self.cal.open_settings()).pack(side="left", padx=8)
        ttk.Button(cf, text="＋ 오늘 일정 추가", command=lambda: self.open_events(datetime.date.today())).pack(side="left")
        ttk.Button(cf, text="☁ 구글 로그인(웹 조회)", style="Accent.TButton",
                   command=lambda: CloudDialog(self)).pack(side="left", padx=8)

    # ---------- 뽀모도로
    def pomo_minutes(self, phase):
        c = self.cfg["pomo"]
        return int(c["work"] if phase == "work" else c["long"] if phase == "long" else c["brk"])

    def pomo_left(self):
        pm = self.pomo
        return max(0, int(round(pm["end"] - time.time()))) if pm["run"] else int(pm["left"])

    def pomo_text(self):
        pm = self.pomo
        sec = self.pomo_left()
        st = "" if pm["run"] else ("  (멈춤)" if pm["left"] < self.pomo_minutes(pm["phase"]) * 60 else "")
        return f'{POMO_NAMES[pm["phase"]]}  {sec // 60:02d}:{sec % 60:02d}{st}', pm["done"]

    def pomo_ratio(self):
        tot = max(1, self.pomo_minutes(self.pomo["phase"]) * 60)
        return max(0.0, min(1.0, 1 - self.pomo_left() / tot))

    def pomo_refresh(self, full=False):
        txt, n = self.pomo_text()
        try:
            self.pomo_var.set(f"{txt}   ·   오늘 {n}회 완료")
            self.pomo_btn_var.set("일시정지" if self.pomo["run"] else "시작")
        except Exception:
            pass
        try:
            if self.cal.alive():
                if full:
                    self.cal.redraw()
                else:
                    self.cal.pomo_update(txt, n, self.pomo_ratio())
        except Exception:
            pass

    def pomo_toggle(self):
        pm = self.pomo
        if pm["run"]:
            pm["left"] = max(1, self.pomo_left())
            pm["run"] = False
        else:
            pm["end"] = time.time() + pm["left"]
            pm["run"] = True
        self.pomo_refresh(True)

    def pomo_reset(self):
        self.pomo.update(phase="work", run=False, left=self.pomo_minutes("work") * 60, done=0)
        self.pomo_refresh(True)

    def pomo_next_phase(self, alarm):
        pm, c = self.pomo, self.cfg["pomo"]
        if pm["phase"] == "work":
            pm["done"] += 1
            long_ = c["every"] > 0 and c["long"] > 0 and pm["done"] % c["every"] == 0
            nxt = "long" if long_ else "brk"
            msg = f'일하는 시간이 끝났습니다. {self.pomo_minutes(nxt)}분 동안 쉬세요.'
        else:
            nxt = "work"
            msg = f'휴식이 끝났습니다. 다시 {self.pomo_minutes("work")}분 집중해 볼까요?'
        keep_run = pm["run"] if not alarm else bool(c["auto"])
        pm["phase"] = nxt
        pm["left"] = self.pomo_minutes(nxt) * 60
        pm["run"] = keep_run
        pm["end"] = time.time() + pm["left"]
        if alarm:
            self.fire([{"label": msg, "beep": True, "tts": True, "pomo": True}])
        self.pomo_refresh(True)

    def pomo_skip(self):
        self.pomo_next_phase(False)

    def pomo_tick(self):
        pm = self.pomo
        if pm["run"]:
            if time.time() >= pm["end"]:
                self.pomo_next_phase(True)
            else:
                self.pomo_refresh(False)

    def open_pomo_settings(self):
        if self.pomo_dlg is not None:
            try:
                if self.pomo_dlg.winfo_exists():
                    self.pomo_dlg.lift()
                    return
            except tk.TclError:
                pass
        c = self.cfg["pomo"]
        d = self.pomo_dlg = tk.Toplevel(self.root)
        d.title("뽀모도로 설정")
        d.resizable(False, False)
        d.transient(self.root)
        f = ttk.Frame(d, padding=14)
        f.pack(fill="both", expand=True)
        vs = {k: tk.IntVar(value=c[k]) for k in ("work", "brk", "long", "every")}
        va = tk.BooleanVar(value=c["auto"])
        rows = (("일하는 시간 (분)", "work", 1, 180), ("휴식 시간 (분)", "brk", 1, 60),
                ("긴 휴식 (분, 0=사용 안 함)", "long", 0, 120), ("긴 휴식 주기 (몇 번 일한 뒤, 0=없음)", "every", 0, 12))
        for i, (t, k, lo, hi) in enumerate(rows):
            ttk.Label(f, text=t).grid(row=i, column=0, sticky="w", pady=4)
            ttk.Spinbox(f, from_=lo, to=hi, width=6, textvariable=vs[k]).grid(row=i, column=1, padx=(12, 0), pady=4)
        ttk.Checkbutton(f, text="시간이 끝나면 다음 단계를 자동으로 이어서 시작", variable=va).grid(
            row=4, column=0, columnspan=2, sticky="w", pady=(6, 2))
        ttk.Label(f, text="기본: 25분 일하고 5분 쉬기", foreground="#868e96").grid(row=5, column=0, columnspan=2, sticky="w")

        def save():
            nc = {}
            for k, lo, hi in (("work", 1, 180), ("brk", 1, 60), ("long", 0, 120), ("every", 0, 12)):
                try:
                    nc[k] = max(lo, min(hi, int(vs[k].get())))
                except Exception:
                    nc[k] = DEFAULT_POMO[k]
            nc["auto"] = bool(va.get())
            self.cfg["pomo"] = nc
            save_config(self.cfg)
            pm = self.pomo
            if not pm["run"]:
                pm["left"] = self.pomo_minutes(pm["phase"]) * 60
            self.pomo_refresh(True)
            d.destroy()

        def default():
            for k in vs:
                vs[k].set(DEFAULT_POMO[k])
            va.set(DEFAULT_POMO["auto"])

        bf = ttk.Frame(f)
        bf.grid(row=6, column=0, columnspan=2, sticky="e", pady=(12, 0))
        ttk.Button(bf, text="기본값으로", command=default).pack(side="left", padx=4)
        ttk.Button(bf, text="저장", command=save).pack(side="left", padx=4)
        ttk.Button(bf, text="닫기", command=d.destroy).pack(side="left", padx=4)
        d.update_idletasks()
        d.geometry(f"+{self.root.winfo_x() + 60}+{self.root.winfo_y() + 80}")

    def fit_window(self):
        """내용이 다 보이도록 창 크기를 맞춤 (화면보다 크면 화면에 맞추고 스크롤)"""
        try:
            self.root.update_idletasks()
            sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
            need_h = self.hd_h + self.sf.inner.winfo_reqheight() + self.bottom_bar.winfo_reqheight() + 8
            need_w = self.sf.inner.winfo_reqwidth() + 40
            w = max(900, min(need_w, sw - 40))
            h = max(480, min(need_h, sh - 90))
            self.root.geometry(f"{w}x{h}+20+20")
        except tk.TclError:
            pass

    # ---------- 달력/일정
    def toggle_cal(self):
        self.cal.toggle()

    def open_events(self, d, select_id=None):
        EventDialog(self, d, select_id)

    def save_events(self):
        self.cfg["events"] = self.events
        self.cfg["tomb"] = self.tomb
        save_config(self.cfg)
        if self.cal.alive():
            self.cal.redraw()
        self.update_next()
        self.cloud.idle = 0
        self.cloud.request_sync(3)

    def event_hits(self, dt):
        out, m = [], dt.hour * 60 + dt.minute
        for e in self.events:
            for mm, lab in event_fires(e, dt.date()):
                if mm == m:
                    out.append({"label": lab, "beep": True, "tts": True, "img": "", "sound": ""})
        return out

    def _hm(self, parent, vh, vm):
        ttk.Spinbox(parent, from_=0, to=23, width=3, textvariable=vh, format="%02.0f", wrap=True).pack(side="left", padx=(6, 0))
        ttk.Label(parent, text=":").pack(side="left")
        ttk.Spinbox(parent, from_=0, to=59, width=3, textvariable=vm, format="%02.0f", wrap=True).pack(side="left")

    def switch_mode(self):
        mode = self.var_mode.get()
        for f in (self.f_time, self.f_int, self.f_date):
            f.pack_forget()
        {"정시": self.f_time, "간격": self.f_int, "날짜": self.f_date}.get(mode, self.f_time).pack()
        for f in (self.dayf, self.f_period):      # 날짜 지정은 요일/기간이 필요 없음
            if mode == "날짜":
                f.grid_remove()
            else:
                f.grid()

    def pick_date(self, var):
        DatePicker(self, self.root, var.get(), lambda iso: var.set(iso))

    def set_days(self, days):
        days = set(days)
        for i, v in enumerate(self.day_vars):
            v.set(i in days)

    def on_autostart(self):
        if not set_autostart(self.var_auto.get()):
            self.var_auto.set(not self.var_auto.get())

    def browse(self, var, kind):
        if kind == "img":
            ft = [("이미지", "*.png *.jpg *.jpeg *.gif *.bmp *.webp"), ("모든 파일", "*.*")]
        else:
            ft = [("오디오", "*.mp3 *.wav *.wma *.mid"), ("모든 파일", "*.*")]
        p = filedialog.askopenfilename(parent=self.root, filetypes=ft)
        if p:
            var.set(p)

    def play_form_sound(self):
        p = self.var_sound.get().strip() or self.cfg["style"].get("sound", "")
        if not p or not os.path.isfile(p):
            messagebox.showinfo(APP_NAME, "재생할 소리 파일을 선택하세요.")
            return
        if not self.player.play(p):
            messagebox.showwarning(APP_NAME, "이 파일은 재생할 수 없습니다.")

    def open_style(self):
        if self.style_dlg:
            self.style_dlg.win.lift()
            return
        self.style_dlg = StyleDialog(self)
        self.style_dlg.refresh_fonts()

    # ---------- 알람 CRUD
    def read_form(self):
        label = self.var_label.get().strip()
        if not label:
            messagebox.showwarning(APP_NAME, "알람 이름을 입력하세요.")
            return None
        mode = self.var_mode.get()
        days = [i for i, v in enumerate(self.day_vars) if v.get()]
        if mode != "날짜" and not days:
            messagebox.showwarning(APP_NAME, "반복 요일을 선택하세요.")
            return None
        img, snd = self.var_img.get().strip(), self.var_sound.get().strip()
        for p, nm in ((img, "이미지"), (snd, "소리 파일")):
            if p and not os.path.isfile(p):
                messagebox.showwarning(APP_NAME, f"{nm} 파일을 찾을 수 없습니다.\n{p}")
                return None
        try:
            a = {"id": int(time.time() * 1000), "label": label, "enabled": True,
                 "days": days if mode != "날짜" else list(range(7)),
                 "beep": self.var_beep.get(), "tts": self.var_tts.get(), "img": img, "sound": snd}
            if mode == "정시":
                a["mode"] = "time"
                a["time"] = f"{int(self.t_h.get()):02d}:{int(self.t_m.get()):02d}"
            elif mode == "간격":
                a["mode"] = "interval"
                a["start"] = f"{int(self.s_h.get()):02d}:{int(self.s_m.get()):02d}"
                a["end"] = f"{int(self.e_h.get()):02d}:{int(self.e_m.get()):02d}"
                a["every"] = max(1, int(self.v_every.get()))
                if hm_to_min(a["end"]) < hm_to_min(a["start"]):
                    messagebox.showwarning(APP_NAME, "종료 시각이 시작 시각보다 빠릅니다.")
                    return None
            else:
                a["mode"] = "date"
                a["date"] = normalize_date(self.var_date.get())
                a["time"] = f"{int(self.t_h.get()):02d}:{int(self.t_m.get()):02d}"
                when = datetime.datetime.combine(datetime.date.fromisoformat(a["date"]),
                                                 datetime.time(*map(int, a["time"].split(":"))))
                if when < datetime.datetime.now() and not messagebox.askyesno(
                        APP_NAME, "이미 지난 날짜/시각입니다.\n그래도 등록할까요?"):
                    return None
            if mode != "날짜":
                f, t = self.var_from.get().strip(), self.var_to.get().strip()
                if f:
                    a["from"] = normalize_date(f)
                if t:
                    a["to"] = normalize_date(t)
                if f and t and a["to"] < a["from"]:
                    messagebox.showwarning(APP_NAME, "적용 기간의 끝 날짜가 시작 날짜보다 빠릅니다.")
                    return None
        except ValueError:
            messagebox.showwarning(APP_NAME, "날짜(예: 2026-10-08)와 시각·간격 값을 확인하세요.")
            return None
        return a

    def add_alarm(self):
        a = self.read_form()
        if a:
            self.alarms.append(a)
            self.var_label.set("")
            self.persist()

    def update_alarm(self):
        idx = self.sel_index()
        if idx is None:
            messagebox.showinfo(APP_NAME, "수정할 알람을 목록에서 선택하세요.")
            return
        a = self.read_form()
        if a:
            a["id"] = self.alarms[idx]["id"]
            a["enabled"] = self.alarms[idx].get("enabled", True)
            self.alarms[idx] = a
            self.persist()
            self.tree.selection_set(str(idx))

    def sel_index(self):
        s = self.tree.selection()
        return int(s[0]) if s else None

    def toggle_sel(self):
        i = self.sel_index()
        if i is not None:
            self.alarms[i]["enabled"] = not self.alarms[i].get("enabled", True)
            self.persist()
            self.tree.selection_set(str(i))

    def delete_sel(self):
        i = self.sel_index()
        if i is not None and messagebox.askyesno(APP_NAME, "선택한 알람을 삭제할까요?"):
            del self.alarms[i]
            self.persist()

    def test_sel(self):
        i = self.sel_index()
        if i is None:
            messagebox.showinfo(APP_NAME, "테스트할 알람을 선택하세요.")
            return
        self.fire([self.alarms[i]])

    # ---------- 초과근무 / 음성
    def save_ot(self):
        try:
            sh, sm = int(self.v_ot_sh.get()), int(self.v_ot_sm.get())
            eh, em = int(self.v_ot_eh.get()), int(self.v_ot_em.get())
            ev = max(5, min(480, int(self.v_ot_every.get())))
            if not (0 <= sh < 24 and 0 <= eh < 24 and 0 <= sm < 60 and 0 <= em < 60):
                raise ValueError
        except ValueError:
            messagebox.showwarning(APP_NAME, "초과근무 시간·간격을 숫자로 올바르게 입력하세요.")
            return
        self.cfg["ot"] = {"enabled": self.v_ot_on.get(), "start": f"{sh:02d}:{sm:02d}", "end": f"{eh:02d}:{em:02d}",
                          "every": ev, "holiday": self.v_ot_hol.get(),
                          "text": self.v_ot_text.get().strip() or DEFAULT_OT["text"]}
        self.v_ot_every.set(str(ev))
        self.ot_next = time.time() + ev * 60
        self.ot_stopped = ""
        save_config(self.cfg)

    def ot_item(self):
        return {"label": self.cfg["ot"]["text"], "beep": True, "tts": True, "img": "", "sound": "", "ot": True}

    def test_ot(self):
        self.fire([self.ot_item()])

    def ot_stop(self):
        """'오늘은 팝업 중지': 오늘 하루는 초과근무 알림을 더 띄우지 않음"""
        self.ot_stopped = datetime.date.today().isoformat()
        self.active = [a for a in self.active if not a.get("ot")]
        self.close_popup()
        if self.active:
            self.show_popup()
            self.alarm_cycle()

    def ot_check(self, now):
        ot = self.cfg["ot"]
        if not ot.get("enabled"):
            return
        every = max(1, int(ot.get("every", 60)))
        key = ot_session(self.events, now, ot)
        today = now.date()
        m = now.hour * 60 + now.minute
        # 팝업에서 지정한 시각: 지정한 날은 그 시각부터, 다음 날은 같은 분(예: 매시 40분)에 맞춰 울림.
        # 메모리에만 두므로 프로그램(컴퓨터)을 끄면 사라지고, 다음 날이 지나도 사라짐
        anc = first = None
        if self.ot_anchor:
            ad, am = self.ot_anchor
            if today == ad:
                anc = first = am
            elif today == ad + datetime.timedelta(days=1):
                anc = am % every
            elif today > ad:
                self.ot_anchor = None
        if anc is not None or (key and not key.endswith("H")):
            # 시계 기준으로 울림: 평일은 매시 정각(간격 60분), 팝업에서 시각을 지정했으면 그 시각부터 간격마다
            # 절전 등으로 시각을 놓쳤으면 2분 안까지는 늦게라도 한 번 울림
            base = anc or 0
            if m < base:
                return
            slot = m - (m - base) % every
            if m - slot > 2 or self.ot_last == (today, slot):
                return
            self.ot_last = (today, slot)
            if not key and slot != first:    # 직접 지정한 첫 시각은 업무시간이라도 울림
                return
        else:
            # 휴일: 프로그램 실행 시점부터 간격마다
            ts = time.time()
            if ts < self.ot_next:
                return
            self.ot_next = ts + every * 60
            if not key:
                return
        if today.isoformat() == self.ot_stopped:
            return
        if any(a.get("ot") for a in self.active):
            return
        self.fire([self.ot_item()])

    def ot_ask_next(self, parent):
        """초과근무 팝업의 '다음 시각 설정': 다음에 뜰 시각을 직접 정하고, 그 뒤로는 간격마다 울림"""
        every = max(1, int(self.cfg["ot"].get("every", 60)))
        now = datetime.datetime.now()
        sug = now + datetime.timedelta(minutes=every)
        d = tk.Toplevel(parent)
        d.title("다음 초과근무 알림 시각")
        d.resizable(False, False)
        d.attributes("-topmost", True)
        d.transient(parent)
        f = ttk.Frame(d, padding=14)
        f.pack(fill="both", expand=True)
        ttk.Label(f, text="다음 팝업을 띄울 시각").grid(row=0, column=0, columnspan=4, sticky="w")
        vh, vm = tk.StringVar(value=f"{sug.hour:02d}"), tk.StringVar(value=f"{sug.minute:02d}")
        ttk.Spinbox(f, from_=0, to=23, width=4, textvariable=vh, format="%02.0f", wrap=True).grid(row=1, column=0, pady=6)
        ttk.Label(f, text=":").grid(row=1, column=1)
        ttk.Spinbox(f, from_=0, to=59, width=4, textvariable=vm, format="%02.0f", wrap=True).grid(row=1, column=2, pady=6)
        info = ttk.Label(f, foreground="#868e96")
        info.grid(row=2, column=0, columnspan=4, sticky="w")

        def target():
            try:
                h, mi = int(vh.get()), int(vm.get())
                if not (0 <= h < 24 and 0 <= mi < 60):
                    return None
            except ValueError:
                return None
            t = now.replace(hour=h, minute=mi, second=0, microsecond=0)
            if t <= datetime.datetime.now():
                t += datetime.timedelta(days=1)
            return t

        def show(*_):
            t = target()
            if t is None:
                info.config(text="시각을 올바르게 입력하세요.")
            else:
                day = "오늘" if t.date() == datetime.date.today() else "내일"
                info.config(text=f"{day} {t:%H:%M}에 뜨고, 그 뒤로 {every}분마다 뜹니다.\n"
                                 f"이 설정은 다음 날까지 유지되며, 컴퓨터(프로그램)를 끄면 원래대로 돌아갑니다.")
        vh.trace_add("write", show)
        vm.trace_add("write", show)
        show()

        def ok():
            t = target()
            if t is None:
                return
            today = datetime.date.today()
            self.ot_anchor = (t.date(), t.hour * 60 + t.minute)
            self.ot_last = None
            # 내일로 넘어가면 오늘 남은 알림은 멈추고, 오늘이면 중지 표시를 풀어 지정 시각에 뜨게 함
            self.ot_stopped = today.isoformat() if t.date() != today else ""
            d.destroy()
            self.active = [a for a in self.active if not a.get("ot")]
            self.close_popup()
            if self.active:
                self.show_popup()
                self.alarm_cycle()

        bf = ttk.Frame(f)
        bf.grid(row=3, column=0, columnspan=4, sticky="e", pady=(10, 0))
        ttk.Button(bf, text="설정", style="Accent.TButton", command=ok).pack(side="left", padx=4)
        ttk.Button(bf, text="취소", command=d.destroy).pack(side="left")
        d.bind("<Return>", lambda e: ok())
        d.update_idletasks()
        sw, sh = d.winfo_screenwidth(), d.winfo_screenheight()
        d.geometry(f"+{(sw - d.winfo_reqwidth()) // 2}+{(sh - d.winfo_reqheight()) // 2}")
        d.lift()
        d.focus_force()

    def test_voice(self):
        self.speaker.speak("알람 음성 테스트입니다.", self.var_rate.get())

    def on_select(self, _e=None):
        i = self.sel_index()
        if i is None:
            return
        a = self.alarms[i]
        self.var_label.set(a["label"])
        self.var_beep.set(a.get("beep", True))
        self.var_tts.set(a.get("tts", True))
        self.var_img.set(a.get("img", ""))
        self.var_sound.set(a.get("sound", ""))
        self.set_days(a["days"])
        self.var_from.set(a.get("from", ""))
        self.var_to.set(a.get("to", ""))
        if a["mode"] in ("time", "date"):
            self.var_mode.set("정시" if a["mode"] == "time" else "날짜")
            self.t_h.set(a["time"][:2]); self.t_m.set(a["time"][3:])
            if a["mode"] == "date":
                self.var_date.set(a["date"])
        else:
            self.var_mode.set("간격")
            self.s_h.set(a["start"][:2]); self.s_m.set(a["start"][3:])
            self.e_h.set(a["end"][:2]); self.e_m.set(a["end"][3:])
            self.v_every.set(str(a["every"]))
        self.switch_mode()

    def persist(self):
        self.cfg["alarms"] = self.alarms
        self.cfg["rate"] = self.var_rate.get()
        save_config(self.cfg)
        self.refresh_list()

    def refresh_list(self):
        self.tree.delete(*self.tree.get_children())
        for i, a in enumerate(self.alarms):
            if a["mode"] == "time":
                t = a["time"]
            elif a["mode"] == "date":
                t = f'{a["date"]} {a["time"]}'
            else:
                t = f'{a["start"]}~{a["end"]} / {a["every"]}분'
            self.tree.insert("", "end", iid=str(i), values=(
                t, a["label"], describe_repeat(a), describe_alert(a), alarm_state(a)))
        self.update_next()

    def update_next(self):
        n = next_fire(self.alarms, self.snoozes, datetime.datetime.now(), self.events)
        if n:
            d, lab = n
            ymd = f"{d.month}/{d.day}" if d.year == datetime.date.today().year else f"{d.year}/{d.month}/{d.day}"
            self.hd_set("next", f"다음 알람  {ymd}({DAY_NAMES[d.weekday()]}) {d:%H:%M} · {lab}")
        else:
            self.hd_set("next", "예정된 알람 없음")

    # ---------- 시계/스케줄러
    def tick(self):
        try:
            now = datetime.datetime.now()
            self.hd_set("clock", now.strftime("%H:%M:%S"))
            self.hd_set("date", f"{now.year}년 {now.month}월 {now.day}일 ({DAY_NAMES[now.weekday()]})")
            cur = int(time.time() // 60)
            if cur > self.last_min:
                # 절전/지연으로 놓친 분은 최대 3분까지만 보충
                hits = []
                for m in range(max(self.last_min + 1, cur - 2), cur + 1):
                    dt = datetime.datetime.fromtimestamp(m * 60)
                    for a in self.alarms:
                        if matches(a, dt) and a not in hits:
                            hits.append(a)
                    for h in self.event_hits(dt):
                        if h not in hits:
                            hits.append(h)
                self.last_min = cur
                if hits:
                    self.fire(hits)
                self.update_next()
            self.ot_check(now)
            self.pomo_tick()
            ts = time.time()
            due = [s for s in self.snoozes if s["at"] <= ts]
            if due:
                self.snoozes = [s for s in self.snoozes if s["at"] > ts]
                self.fire(due)
        finally:
            self.root.after(1000, self.tick)

    # ---------- 알람 울리기
    def fire(self, items):
        for a in items:
            if not any(x["label"] == a["label"] for x in self.active):
                self.active.append({"label": a["label"], "beep": a.get("beep", True), "tts": a.get("tts", True),
                                    "img": a.get("img", ""), "sound": a.get("sound", ""),
                                    "ot": bool(a.get("ot")), "pomo": bool(a.get("pomo"))})
        self.show_popup()
        if self.repeat_job:
            self.root.after_cancel(self.repeat_job)
            self.repeat_job = None
        self.turn_tts = False
        self.alarm_cycle()

    def alarm_cycle(self):
        if not self.active:
            return
        first = self.active[0]
        sound = first.get("sound") or self.cfg["style"].get("sound", "")
        want_beep = any(a["beep"] for a in self.active)
        tts_text = ". ".join(a["label"] for a in self.active if a["tts"])
        rate = self.var_rate.get()
        if want_beep and sound and os.path.isfile(sound):
            # 소리 파일: 끝까지 재생 → 끝나면 음성 → 다시 파일 … 순서로 반복
            if not self.player.is_playing():
                if tts_text and self.turn_tts:
                    self.turn_tts = False
                    self.speaker.speak(tts_text, rate)
                else:
                    self.turn_tts = True
                    if not self.player.play(sound):
                        beep(self.root)
        else:
            if want_beep:
                beep(self.root)
            if tts_text:
                self.root.after(900 if want_beep else 0, lambda t=tts_text: self.speaker.speak(t, rate))
        self.repeat_job = self.root.after(REPEAT_MS, self.alarm_cycle)

    def show_popup(self):
        text = "\n".join(a["label"] for a in self.active)
        has_ot = any(a.get("ot") for a in self.active)
        has_norm = any(not a.get("ot") and not a.get("pomo") for a in self.active)
        sig = (has_norm, has_ot, has_ot)
        if self.popup and self.popup.alive():
            if getattr(self.popup, "sig", None) == sig:
                self.popup.update_text(text)
                return
            self.popup.close()
        img = next((a.get("img", "") for a in self.active if a.get("img")), "")
        self.popup = PopupWindow(self.root, self.cfg["style"], text, img,
                                 on_snooze=self.snooze if has_norm else None, on_dismiss=self.dismiss,
                                 on_stop=self.ot_stop if has_ot else None,
                                 on_next=self.ot_ask_next if has_ot else None)

    def close_popup(self):
        if self.repeat_job:
            self.root.after_cancel(self.repeat_job)
            self.repeat_job = None
        self.speaker.stop()
        self.player.stop()
        if self.popup:
            self.popup.close()
        self.popup = None

    def dismiss(self):
        self.active = []
        self.close_popup()

    def snooze(self):
        at = time.time() + SNOOZE_MIN * 60
        for a in self.active:
            if not a.get("ot") and not a.get("pomo"):
                self.snoozes.append(dict(a, at=at))
        self.active = []
        self.close_popup()
        self.update_next()

    # ---------- 트레이
    def _tray_image(self):
        try:
            return app_icon_image(64)
        except Exception:
            img = Image.new("RGBA", (64, 64), (0, 0, 0, 0))
            d = ImageDraw.Draw(img)
            d.ellipse((4, 4, 60, 60), fill=(240, 140, 0, 255))
            d.ellipse((12, 12, 52, 52), fill=(255, 255, 255, 255))
            d.line((32, 32, 32, 18), fill=(33, 37, 41, 255), width=4)
            d.line((32, 32, 42, 36), fill=(33, 37, 41, 255), width=4)
            return img

    def _start_tray(self):
        if not HAS_TRAY:
            return
        menu = pystray.Menu(
            pystray.MenuItem("열기", lambda: self.cmdq.put("show"), default=True),
            pystray.MenuItem("달력 보이기/숨기기", lambda: self.cmdq.put("cal")),
            pystray.MenuItem("종료", lambda: self.cmdq.put("quit")),
        )
        self.tray = pystray.Icon("RepeatAlarm", self._tray_image(), APP_NAME, menu)
        self.tray.run_detached()

    def poll_cmds(self):
        try:
            while True:
                c = self.cmdq.get_nowait()
                if c == "show":
                    self.cloud.touch()
                    self.root.deiconify()
                    self.root.lift()
                    self.root.focus_force()
                elif c == "cal":
                    self.cal.toggle()
                elif isinstance(c, tuple) and c[0] == "call":
                    try:
                        c[1]()
                    except Exception as ex:
                        print("콜백 오류:", ex)
                elif c == "quit":
                    self.quit()
                    return
        except queue.Empty:
            pass
        self.root.after(200, self.poll_cmds)

    def hide_window(self):
        if self.tray:
            self.root.withdraw()
        else:
            self.root.iconify()

    def quit(self):
        self.cfg["rate"] = self.var_rate.get()
        save_config(self.cfg)
        self.speaker.stop()
        self.player.stop()
        if self.tray:
            try:
                self.tray.stop()
            except Exception:
                pass
        self.root.destroy()

    def run(self):
        self.root.mainloop()


def main():
    try:  # 고해상도 화면에서 글자 흐림 방지
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass

    lock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        lock.bind(("127.0.0.1", LOCK_PORT))
    except OSError:
        r = tk.Tk()
        r.withdraw()
        messagebox.showinfo(APP_NAME, "이미 실행 중입니다. 트레이 아이콘을 확인하세요.")
        return

    if not HAS_PIL:
        r = tk.Tk()
        r.withdraw()
        messagebox.showwarning(APP_NAME, "Pillow가 없어 이미지가 표시되지 않습니다.\n"
                                         "명령 프롬프트에서  py -m pip install pillow pystray  를 실행하세요.")
        r.destroy()

    App(start_hidden="--minimized" in sys.argv).run()


if __name__ == "__main__":
    main()
