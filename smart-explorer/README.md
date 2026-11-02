# 스마트탐색기 (SmartExplorer)

> 저장소 `nunco-git/ezgong` 의 `smart-explorer/` 폴더

화면을 여러 칸으로 나눠 쓰는 탐색기 + 파일명·본문 내용 검색 (스마트공 시리즈, https://smartgong.kr)

## 오류 · 개선 제안

사용하다가 오류나 개선할 점이 있으면 **smartgongmaster@gmail.com** 으로 알려 주세요.

## 내려받기

- **바로 받기 (항상 최신 버전):** https://smartgong.kr/download/smart-explorer
- 설명·SHA-256이 있는 릴리스 페이지: https://smartgong.kr/download/smart-explorer/info

> **무료 프로그램입니다.** 창 오른쪽이나 왼쪽 하단에 광고가 표시될 수 있습니다.
> 설치 없이 실행하는 프로그램이라, 지우려면 **`SmartExplorer.exe` 파일을 삭제**하면 됩니다. (설정은 `%LOCALAPPDATA%\SmartExplorer` 폴더에 있으며 함께 지워도 됩니다)

**위 주소나 깃허브 공식 릴리스가 아닌 곳에서 받은 파일은 실행하지 마세요.**

### ⚠ 처음 실행할 때 "Windows의 PC 보호" 창이 뜨면

새로 나온 프로그램이라 윈도우가 아직 몰라서 뜨는 안내입니다. 아래처럼 실행하세요.

1. 파란 창에서 **추가 정보** → **실행** 을 누릅니다.
2. **실행** 버튼이 없으면: 받은 `SmartExplorer.exe` 를 오른쪽 클릭 → **속성** → 아래쪽 **차단 해제** 체크 → **확인** 후 다시 실행합니다.
3. 브라우저가 다운로드를 막으면: 크롬은 다운로드 목록 **⋮ → 유지**, 엣지는 **… → 유지 → 추가 정보 → 그래도 유지**.

※ "스마트 앱 컨트롤에 의해 차단됨"이 뜨거나 기관 보안 정책으로 막히면 위 방법으로는 실행되지 않습니다. 이때는 전산 담당자에게 문의해 주세요.
※ 반드시 **smartgong.kr** 또는 이 깃허브 페이지에서 받은 파일만 실행하세요.

### 받은 파일이 진짜인지 확인

- PowerShell: `Get-FileHash SmartExplorer.exe` → 릴리스 설명의 SHA-256 값과 같아야 합니다.
- 깃허브 CLI: `gh attestation verify SmartExplorer.exe --repo nunco-git/ezgong`

## 새 버전 배포 방법 (관리자용)

1. `smart_explorer.py` 맨 위 `APP_VERSION` 을 올립니다 (예: `1.0.0` → `1.1.0`).
2. 커밋해서 `main` 에 올리면 끝입니다. 깃허브 Actions가 자동으로
   빌드 → SHA-256 기록 → 빌드 출처 증명 → 릴리스(`smartexplorer-v1.1.0`) 게시까지 합니다.
   - 버전을 안 올리고 고친 것만 올리면 릴리스를 새로 만들지 않습니다.
   - Actions 탭에서 `smart-explorer-release` 를 직접 실행하거나, 태그 `smartexplorer-v1.1.0` 을 올려도 됩니다.
3. 릴리스 설명에 바뀐 점을 적어 두면, 설치된 프로그램의 **새 버전 알림** 창에 그대로 보입니다.

## 처음 한 번 해 둘 것

- 저장소 **Settings → General → Releases → Immutable releases** 켜기 (게시한 파일 바꿔치기 방지)
- 저장소 **Settings → Branches** 에서 `main` 보호 규칙 (강제 푸시·삭제 금지)
- 깃허브 계정 2단계 인증 / 패스키

## 내 PC에서 빌드

`build_exe.bat` 실행 → `dist\SmartExplorer.exe` (빌드 전용 가상환경 `.venv-build` 를 자동으로 만듦)
