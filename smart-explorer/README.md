# 스마트탐색기 (SmartExplorer)

> 저장소 `nunco-git/ezgong` 의 `smart-explorer/` 폴더

화면을 여러 칸으로 나눠 쓰는 탐색기 + 파일명·본문 내용 검색 (스마트공 시리즈, https://smartgong.kr)

## 내려받기

[Releases](https://github.com/nunco-git/ezgong/releases) 에서 **스마트탐색기** 릴리스의 `SmartExplorer.exe` 를 받으세요. **다른 곳에서 받은 파일은 실행하지 마세요.**

### 받은 파일이 진짜인지 확인

- PowerShell: `Get-FileHash SmartExplorer.exe` → 릴리스 설명의 SHA-256 값과 같아야 합니다.
- 깃허브 CLI: `gh attestation verify SmartExplorer.exe --repo nunco-git/ezgong`

## 새 버전 배포 방법 (관리자용)

1. `smart_explorer.py` 맨 위 `APP_VERSION` 을 올립니다 (예: `1.0.0` → `1.1.0`).
2. 커밋·푸시한 뒤 같은 번호로 태그를 올립니다. (한 저장소에 여러 프로그램이 있어도 섞이지 않게 `smartexplorer-v` 를 앞에 붙임)
   ```
   git tag smartexplorer-v1.1.0
   git push origin smartexplorer-v1.1.0
   ```
3. 깃허브 Actions가 자동으로 빌드 → SHA-256 기록 → 빌드 출처 증명 → 릴리스 게시까지 합니다.
   태그와 `APP_VERSION` 이 다르면 빌드가 멈춥니다.
4. 릴리스 설명에 바뀐 점을 적어 두면, 설치된 프로그램의 **새 버전 알림** 창에 그대로 보입니다.

## 처음 한 번 해 둘 것

- 저장소 **Settings → General → Releases → Immutable releases** 켜기 (게시한 파일 바꿔치기 방지)
- 저장소 **Settings → Branches** 에서 `main` 보호 규칙 (강제 푸시·삭제 금지)
- 깃허브 계정 2단계 인증 / 패스키

## 내 PC에서 빌드

`build_exe.bat` 실행 → `dist\SmartExplorer.exe` (빌드 전용 가상환경 `.venv-build` 를 자동으로 만듦)
