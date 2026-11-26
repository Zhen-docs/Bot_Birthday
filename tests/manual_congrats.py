"""Ручная проверка поздравления с ДР — без polling, без запуска бота.

Вызывает настоящую daily_birthdays_job из main.py и отправляет сообщение
в тот же чат, что и бот. Ничего не планирует и не опрашивает Telegram,
поэтому с работающим ботом не конфликтует.

Запуск (из корня проекта bot_stable):
    python tests/manual_congrats.py

Сообщение уйдёт по-настоящему и само не удалится.

Файл намеренно назван без префикса test_ — это не автотест, а ручной скрипт,
и unittest его не подхватывает.
"""

import asyncio
import sys
from pathlib import Path

# Запуск из любой папки: main.py лежит на уровень выше.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import main as bot  # noqa: E402
from telegram import Bot  # noqa: E402


async def run() -> int:
    today = bot.today_local()
    people = bot.birthdays_on(today)

    chat_id = bot.settings.group_chat_id
    print(f"Сегодня: {today.isoformat()} ({bot.settings.timezone_name})")
    print(f"Чат:     {chat_id}")
    print(f"Найдено ДР: {len(people)}")

    if not people:
        print()
        print("Сегодня дней рождения нет — поздравлять нечего.")
        print("Добавьте запись с сегодняшней датой в data/birthdays.json")
        print("или через /add_birthday в чате, потом запустите снова.")
        return 1

    for item in people:
        print(f"  - {item['name']} ({item['day']:02d}.{item['month']:02d})")

    names = ", ".join(item["name"] for item in people)
    print()
    print("Текст, который отправится:")
    print(f"  🎉 Сегодня день рождения у: {names}! Поздравляем 🥳")
    print()

    telegram_bot = Bot(token=bot.settings.bot_token)
    try:
        # Ровно тот же код, что выполняется по расписанию в 09:00.
        context = type("Ctx", (), {"bot": telegram_bot})()
        await bot.daily_birthdays_job(context)
    finally:
        await telegram_bot.shutdown()

    print("Готово. Проверьте чат.")
    return 0


if __name__ == "__main__":
    sys.exit(asyncio.run(run()))
