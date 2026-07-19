@echo off
setlocal
cd /d "%~dp0"

rem usage:  run.bat          -> config.json
rem         run.bat test     -> config-test.json
rem         run.bat prod     -> config-prod.json
set CFG=config.json
if not "%~1"=="" set CFG=config-%~1.json

if not exist "classes\SourceLinkChecker.class" (
  echo [run] classes not found. Run build.bat first.
  pause
  exit /b 1
)
if not exist "%CFG%" (
  echo [run] config file not found: %CFG%
  pause
  exit /b 1
)
echo [run] config = %CFG%
java -version
echo.
java -cp "classes;lib\*" SourceLinkChecker "%CFG%"
echo.
echo [run] stopped. (if [ERROR] appears above, that is the cause)
pause
