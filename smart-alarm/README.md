# 스마트 일정 알라미 (RepeatAlarm)

> 저장소 `nunco-git/ezgong` 의 `smart-alarm/` 폴더 · 스마트공 시리즈 (https://smartgong.kr)

정해진 시각·간격·날짜에 팝업과 소리, 음성으로 알려 주는 Windows 알람 프로그램.
바탕화면 달력(일정), 초과근무 알림, 뽀모도로, 구글 로그인 일정 동기화를 함께 제공합니다.

## 내려받기

- **바로 받기 (항상 최신 버전):** https://smartgong.kr/download/smart-alarm
- 설명·SHA-256이 있는 릴리스 페이지: https://smartgong.kr/download/smart-alarm/info

**위 주소나 깃허브 공식 릴리스가 아닌 곳에서 받은 파일은 실행하지 마세요.**

### ⚠ 처음 실행할 때 "Windows의 PC 보호" 창이 뜨면

1. 파란 창에서 **추가 정보** → **실행** 을 누릅니다.
2. **실행** 버튼이 없으면: `RepeatAlarm.exe` 오른쪽 클릭 → **속성** → **차단 해제** 체크 → **확인** 후 다시 실행합니다.
3. 브라우저가 다운로드를 막으면: 크롬 **⋮ → 유지**, 엣지 **… → 유지 → 추가 정보 → 그래도 유지**.

### 받은 파일이 진짜인지 확인

- PowerShell: `Get-FileHash RepeatAlarm.exe` → 릴리스 설명의 SHA-256 값과 같아야 합니다.
- 깃허브 CLI: `gh attestation verify RepeatAlarm.exe --repo nunco-git/ezgong`

## 새 버전 배포 방법 (관리자용)

1. `alarm_app.py` 위쪽 `APP_VERSION` 을 올립니다 (예: `1.1.0` → `1.2.0`).
2. 커밋해서 `main` 에 올리면 깃허브 Actions가 자동으로
   빌드 → SHA-256 기록 → 빌드 출처 증명 → 릴리스(`smartalarm-v1.2.0`) 게시 →
   홈페이지 고정 주소 갱신까지 합니다. 버전을 안 올리면 릴리스를 새로 만들지 않습니다.
   예전 주소(`releases/download/planalarm/RepeatAlarm.exe`)의 파일도 새 버전으로 바꿔 둡니다.
3. 릴리스 설명에 바뀐 점을 적어 둡니다.

## 내 PC에서 빌드

`build.bat` 실행 → 같은 폴더에 `RepeatAlarm.exe`
