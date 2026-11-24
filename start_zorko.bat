@echo off
chcp 65001 >nul
cd /d "%~dp0"
where py >nul 2>nul
if %errorlevel%==0 (
  py -3 zorko.py
) else (
  python zorko.py
)
echo.
echo Zorko остановлен. Если выше написана ошибка про Python, установите Python 3 с python.org.
pause
