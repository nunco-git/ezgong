@echo off
chcp 65001 >nul
setlocal
cd /d "%~dp0"

echo [1/4] 빌드 전용 가상환경 준비 (.venv-build)
if not exist .venv-build\Scripts\python.exe (
    python -m venv .venv-build || goto :err
)
set PY=.venv-build\Scripts\python.exe
%PY% -m pip install --upgrade pip >nul
if exist requirements-lock.txt (
    %PY% -m pip install -r requirements-lock.txt || goto :err
) else (
    %PY% -m pip install -r requirements-build.txt || goto :err
)

echo [2/4] 버전 정보 파일 만들기
for /f %%v in ('%PY% tools\make_version_file.py') do set VER=%%v
if "%VER%"=="" goto :err
echo     버전: %VER%

echo [3/4] exe 만들기
%PY% -m PyInstaller --noconfirm --clean --onefile --noconsole --name SmartExplorer ^
  --icon smart_explorer.ico --version-file version_info.txt ^
  --collect-all pypdfium2 --collect-all pypdfium2_raw --collect-all winrt ^
  --collect-submodules comtypes --hidden-import pystray._win32 ^
  --exclude-module numpy --exclude-module pandas --exclude-module matplotlib --exclude-module scipy ^
  --exclude-module PyQt5 --exclude-module PyQt6 --exclude-module PySide6 --exclude-module IPython ^
  --exclude-module pytest --exclude-module pydoc_data ^
  smart_explorer.py || goto :err

echo [4/4] SHA-256 값
certutil -hashfile dist\SmartExplorer.exe SHA256
echo.
echo 완료: dist\SmartExplorer.exe  (v%VER%)
pause
exit /b 0

:err
echo.
echo 빌드에 실패했습니다. 위 메시지를 확인해 주세요.
pause
exit /b 1
