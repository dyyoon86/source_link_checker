@echo off
setlocal
cd /d "%~dp0"
echo [build] javac version:
javac -version
if %errorlevel% neq 0 (
  echo [build] javac not found. Check JDK install / PATH.
  pause
  exit /b 1
)
if not exist classes mkdir classes
echo [build] compiling (target Java 1.8)...
javac -source 1.8 -target 1.8 -encoding UTF-8 -cp "lib\*" -d classes src\SourceLinkChecker.java
if %errorlevel% neq 0 (
  echo.
  echo [build] FAILED - see errors above.
  pause
  exit /b 1
)
echo [build] OK  -^> classes\
echo.
echo Now run: run-test.bat  or  run-prod.bat
pause
