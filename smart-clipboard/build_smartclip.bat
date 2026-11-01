@echo off
chcp 65001 > nul
setlocal
cd /d "%~dp0"
title 스마트클립 exe 만들기

REM 내 PC에서 직접 만들 때 쓰는 파일입니다. (배포용은 깃허브가 자동으로 만듦)
REM 같은 폴더에 smart_clipboard.py, clip_icon.ico, tools\make_version_file.py 가 있어야 합니다.

set "PY=python"
where py >nul 2>nul && set "PY=py"

echo [1/4] PyInstaller, Pillow 설치 확인 중...
%PY% -m pip install --upgrade pyinstaller pillow --quiet
if errorlevel 1 goto :fail

echo [2/4] 버전 정보 파일 만들기
for /f %%v in ('%PY% tools\make_version_file.py') do set VER=%%v
if "%VER%"=="" goto :fail
echo     버전: %VER%

taskkill /f /im SmartClip.exe >nul 2>nul

echo [3/4] SmartClip.exe 만드는 중... (1~2분)
%PY% -m PyInstaller --onefile --noconsole --noupx --clean --noconfirm --name SmartClip ^
  --icon clip_icon.ico --version-file smartclip_version.txt smart_clipboard.py
if errorlevel 1 goto :fail

echo [4/4] 정리 중...
copy /y "dist\SmartClip.exe" "SmartClip.exe" >nul
rmdir /s /q build >nul 2>nul
rmdir /s /q dist >nul 2>nul
del /q SmartClip.spec >nul 2>nul
if not exist "SmartClip.exe" goto :fail

echo.
echo 완료: %cd%\SmartClip.exe  (v%VER%)
certutil -hashfile SmartClip.exe SHA256
echo  - 이 파일 하나만 원하는 곳에 두고 실행하면 됩니다. (행정기관 PC에도 그대로 복사)
echo  - 처음 실행하면 Windows 시작 시 자동 실행이 등록됩니다. (설정에서 끌 수 있음)
goto :end

:fail
echo.
echo [오류] exe를 만들지 못했습니다.
echo  "Permission denied"가 보이면 백신이 만들던 exe를 격리한 것입니다.
echo  백신의 격리 목록에서 파일 이름과 탐지명을 확인해 주세요.

:end
echo.
pause
endlocal
