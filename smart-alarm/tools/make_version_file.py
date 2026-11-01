"""alarm_app.py 의 APP_VERSION 을 읽어 PyInstaller용 버전 정보 파일(alarm_version.txt)을 만듦.
exe 파일 속성 → 자세히 탭에 버전·제품 이름·제작자가 나오게 함.

사용:  python tools/make_version_file.py            → alarm_version.txt 생성, 버전 출력
       python tools/make_version_file.py --check smartalarm-v1.2.0  → 태그와 APP_VERSION이 다르면 실패
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "alarm_app.py")


def app_version():
    with open(SRC, encoding="utf-8") as f:
        m = re.search(r'^APP_VERSION\s*=\s*"([^"]+)"', f.read(), re.M)
    if not m:
        sys.exit("APP_VERSION 을 찾지 못했습니다")
    return m.group(1)


def main():
    ver = app_version()
    if len(sys.argv) >= 3 and sys.argv[1] == "--check":
        tag = sys.argv[2]
        for pre in ("smartalarm-v", "v", "V"):     # 태그 앞 이름 떼기
            if tag.startswith(pre):
                tag = tag[len(pre):]
                break
        if tag != ver:
            sys.exit(f"태그 v{tag} 와 코드의 APP_VERSION {ver} 가 다릅니다. 둘을 맞춰 주세요.")
    nums = [int(n) for n in re.findall(r"\d+", ver)[:4]]
    nums += [0] * (4 - len(nums))
    t = tuple(nums)
    text = f"""# UTF-8
VSVersionInfo(
  ffi=FixedFileInfo(filevers={t}, prodvers={t}, mask=0x3f, flags=0x0, OS=0x40004,
                    fileType=0x1, subtype=0x0, date=(0, 0)),
  kids=[
    StringFileInfo([
      StringTable('041204B0', [
        StringStruct('CompanyName', '스마트공 (smartgong.kr)'),
        StringStruct('FileDescription', '스마트 일정 알라미 - 반복 알람·바탕화면 달력·일정 관리'),
        StringStruct('FileVersion', '{ver}'),
        StringStruct('InternalName', 'RepeatAlarm'),
        StringStruct('LegalCopyright', '© 스마트공'),
        StringStruct('OriginalFilename', 'RepeatAlarm.exe'),
        StringStruct('ProductName', '스마트 일정 알라미'),
        StringStruct('ProductVersion', '{ver}')])
    ]),
    VarFileInfo([VarStruct('Translation', [0x0412, 1200])])
  ]
)
"""
    with open(os.path.join(ROOT, "alarm_version.txt"), "w", encoding="utf-8") as f:
        f.write(text)
    print(ver)


if __name__ == "__main__":
    main()
