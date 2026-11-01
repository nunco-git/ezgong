# 스마트클립 (SmartClip)

> 저장소 `nunco-git/ezgong` 의 `smart-clipboard/` 폴더 · 스마트공 시리즈 (https://smartgong.kr)

한글·엑셀·워드의 표와 서식을 그대로 다시 붙여넣는 Windows 클립보드 기록 관리자.
인터넷·네트워크 기능이 없고, 기록은 Windows DPAPI로 암호화해 이 PC·이 계정에만 저장합니다.

## 내려받기

- **바로 받기 (항상 최신 버전):** https://smartgong.kr/download/smart-clipboard
- 설명·SHA-256이 있는 릴리스 페이지: https://smartgong.kr/download/smart-clipboard/info

**위 주소나 깃허브 공식 릴리스가 아닌 곳에서 받은 파일은 실행하지 마세요.**

### ⚠ 처음 실행할 때 "Windows의 PC 보호" 창이 뜨면

1. 파란 창에서 **추가 정보** → **실행** 을 누릅니다.
2. **실행** 버튼이 없으면: `SmartClip.exe` 오른쪽 클릭 → **속성** → **차단 해제** 체크 → **확인** 후 다시 실행합니다.
3. 브라우저가 다운로드를 막으면: 크롬 **⋮ → 유지**, 엣지 **… → 유지 → 추가 정보 → 그래도 유지**.

### 받은 파일이 진짜인지 확인

- PowerShell: `Get-FileHash SmartClip.exe` → 릴리스 설명의 SHA-256 값과 같아야 합니다.
- 깃허브 CLI: `gh attestation verify SmartClip.exe --repo nunco-git/ezgong`

## 새 버전 배포 방법 (관리자용)

1. `smart_clipboard.py` 위쪽 `APP_VERSION` 을 올립니다 (예: `1.0.0` → `1.1.0`).
2. 커밋해서 `main` 에 올리면 깃허브 Actions가 자동으로
   빌드 → SHA-256 기록 → 빌드 출처 증명 → 릴리스(`smartclipboard-v1.1.0`) 게시 →
   홈페이지 고정 주소 갱신까지 합니다. 버전을 안 올리면 릴리스를 새로 만들지 않습니다.
3. 릴리스 설명에 바뀐 점을 적어 둡니다.

## 내 PC에서 빌드

`build_smartclip.bat` 실행 → 같은 폴더에 `SmartClip.exe`
