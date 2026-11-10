"""구글 공개 달력(대한민국 공휴일)에서 공휴일·임시공휴일을 받아 ads/holidays_kr.json 으로 저장.
스마트탐색기가 이 파일을 받아 알람 날짜 계산에 씀. API 키 불필요."""
import json, re, sys, urllib.request
from datetime import date, timedelta

ICS = ("https://calendar.google.com/calendar/ical/"
       "ko.south_korea%23holiday%40group.v.calendar.google.com/public/basic.ics")
OUT = "ads/holidays_kr.json"


def main():
    req = urllib.request.Request(ICS, headers={"User-Agent": "Mozilla/5.0"})
    text = urllib.request.urlopen(req, timeout=60).read().decode("utf-8", "replace")
    text = re.sub(r"\r?\n[ \t]", "", text)           # 접힌 줄 이어 붙이기
    dates = set()
    for ev in text.split("BEGIN:VEVENT")[1:]:
        ev = ev.split("END:VEVENT")[0]
        m = re.search(r"DTSTART[^:\n]*:(\d{8})", ev)
        if not m:
            continue
        desc = (re.search(r"DESCRIPTION:(.*)", ev) or [None, ""])[1]
        if "공휴일" not in desc and "Public holiday" not in desc:   # 기념일(어버이날 등)은 제외
            continue
        s = m.group(1)
        start = date(int(s[:4]), int(s[4:6]), int(s[6:]))
        e = re.search(r"DTEND[^:\n]*:(\d{8})", ev)
        end = date(int(e.group(1)[:4]), int(e.group(1)[4:6]), int(e.group(1)[6:])) if e else start + timedelta(days=1)
        d = start
        while d < end:                               # 여러 날짜 일정도 하루씩 풀기
            dates.add(d.isoformat())
            d += timedelta(days=1)
    if len(dates) < 5:
        sys.exit(f"공휴일이 너무 적게 읽혔습니다({len(dates)}건). 달력 형식이 바뀌었는지 확인하세요.")
    json.dump({"updated": date.today().isoformat(), "dates": sorted(dates)},
              open(OUT, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    print(f"{len(dates)}건 저장")


main()
