@echo off
chcp 65001 >nul
cd /d "%~dp0"
echo Запуск Telegram-бота...
python main.py
if errorlevel 1 (
    echo.
    echo Бот завершился с ошибкой. Смотри logs\bot.log
    pause
)
