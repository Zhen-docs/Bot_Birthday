"""Telegram-бот для группового чата.

Функционал:
  * дни рождения участников (просмотр + админское редактирование);
  * погода: на время сходки и по запросу /weather на выбранную дату и время
    (Open-Meteo, без ключа);
  * сходки: публикация официального сообщения и напоминание за 2 часа;
  * упоминание всех участников из birthdays.json в напоминании о сходке;
  * личный кабинет владельца (ADMIN_USER_ID): правка дней рождения, локаций,
    сходки и фото — только в личных сообщениях, в группе всё как обычно.

Все данные хранятся в локальных JSON-файлах, БД не используется.
"""

from __future__ import annotations

import argparse
import asyncio
import calendar as pycalendar
import html
import json
import logging
import os
import re
import sys
import tempfile
import threading
import time
import uuid
import warnings
from datetime import date, datetime, timedelta
from datetime import time as dt_time
from functools import wraps
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Awaitable, Callable, Iterable

import pytz
import requests
from dotenv import load_dotenv
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

from telegram import (
    BotCommand,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Update,
)
from telegram.constants import ChatType, ParseMode
from telegram.error import BadRequest, Conflict, NetworkError, RetryAfter, TelegramError
from telegram.ext import (
    Application,
    ApplicationHandlerStop,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    ConversationHandler,
    MessageHandler,
    filters,
)

# ---------------------------------------------------------------------------
# Пути и базовые константы
# ---------------------------------------------------------------------------

BASE_DIR = Path(__file__).resolve().parent
CONFIG_DIR = BASE_DIR / "config"
DATA_DIR = BASE_DIR / "data"
PHOTOS_DIR = CONFIG_DIR / "photos"
# Фото, загруженные через бота, живут в data/: на Bothost эта папка
# сохраняется между деплоями из Git, а config/ перезаписывается.
UPLOADED_PHOTOS_DIR = DATA_DIR / "photos"
LOGS_DIR = BASE_DIR / "logs"

LOCATIONS_FILE = CONFIG_DIR / "locations.json"
BIRTHDAYS_FILE = DATA_DIR / "birthdays.json"
MEETUP_FILE = DATA_DIR / "meetup.json"
STATE_FILE = DATA_DIR / "state.json"

WEATHER_URL = "https://api.open-meteo.com/v1/forecast"
WEATHER_TIMEOUT = (5, 10)

# Open-Meteo отдаёт почасовой прогноз примерно на две недели вперёд.
MAX_FORECAST_DAYS = 15

JOB_BIRTHDAYS = "daily_birthdays"
JOB_MEETUP_REMINDER = "meetup_reminder"
JOB_MEETUP_POLL_CLOSE = "meetup_poll_close"
JOB_LOG_NEXT_RUNS = "log_next_runs"
JOB_NET_WATCHDOG = "net_watchdog"
JOB_BIRTHDAYS_RETRY = "daily_birthdays_retry"

# Сколько раз пробуем дослать поздравления, если в 09:00 не было сети.
MAX_BIRTHDAY_RETRIES = 90  # ~90 минут попыток

POLL_QUESTION = "Ты идёшь?"
POLL_OPTIONS = ["Приеду", "Не смогу", "Пока не знаю"]

MONTHS_NOMINATIVE = [
    "Январь", "Февраль", "Март", "Апрель", "Май", "Июнь",
    "Июль", "Август", "Сентябрь", "Октябрь", "Ноябрь", "Декабрь",
]
MONTHS_GENITIVE = [
    "января", "февраля", "марта", "апреля", "мая", "июня",
    "июля", "августа", "сентября", "октября", "ноября", "декабря",
]
WEEKDAYS = [
    "Понедельник", "Вторник", "Среда", "Четверг", "Пятница", "Суббота", "Воскресенье",
]
WEEKDAYS_SHORT = ["Пн", "Вт", "Ср", "Чт", "Пт", "Сб", "Вс"]

PRIVATE_ONLY_REPLY = "Я работаю только в группах"

logger = logging.getLogger("group_bot")

# ConversationHandler'ы работают в режиме per_chat: предупреждение PTB ожидаемо.
try:
    from telegram.warnings import PTBUserWarning

    warnings.filterwarnings("ignore", category=PTBUserWarning, message=r".*per_message=False.*")
except Exception:  # pragma: no cover
    pass

# ---------------------------------------------------------------------------
# Настройки
# ---------------------------------------------------------------------------


def _make_timezone(name: str):
    """Возвращает корректный tzinfo: zoneinfo, а при его отсутствии — pytz."""
    try:
        from zoneinfo import ZoneInfo

        return ZoneInfo(name)
    except Exception:  # pragma: no cover - зависит от окружения
        try:
            return pytz.timezone(name)
        except Exception:
            logger.warning("Неизвестный часовой пояс %r, использую Europe/Moscow", name)
            from zoneinfo import ZoneInfo

            return ZoneInfo("Europe/Moscow")


class Settings:
    """Конфигурация, прочитанная из .env."""

    def __init__(self) -> None:
        load_dotenv(BASE_DIR / ".env", override=False)
        self.bot_token: str = (os.getenv("BOT_TOKEN") or "").strip()
        self.group_chat_id: int | str | None = self._parse_chat_id(
            (os.getenv("GROUP_CHAT_ID") or "").strip()
        )
        self.timezone_name: str = (os.getenv("TIMEZONE") or "Europe/Moscow").strip()
        self.timezone = _make_timezone(self.timezone_name)
        self.daily_hour: int = self._parse_int(os.getenv("DAILY_HOUR"), 9, 0, 23)
        self.daily_minute: int = self._parse_int(os.getenv("DAILY_MINUTE"), 0, 0, 59)
        self.log_level: str = (os.getenv("LOG_LEVEL") or "INFO").strip().upper()
        self.delete_service_messages: bool = self._parse_bool(
            os.getenv("DELETE_SERVICE_MESSAGES"), True
        )
        # Владелец бота: в личных сообщениях ему доступна админ-панель.
        self.admin_user_id: int | None = self._parse_optional_int(
            (os.getenv("ADMIN_USER_ID") or "").strip()
        )

    @staticmethod
    def _parse_bool(raw: str | None, default: bool) -> bool:
        if raw is None or not str(raw).strip():
            return default
        return str(raw).strip().lower() in {"1", "true", "yes", "y", "on", "да"}

    @staticmethod
    def _parse_optional_int(raw: str) -> int | None:
        if not raw:
            return None
        try:
            return int(raw.strip().lstrip("@"))
        except ValueError:
            logger.warning("ADMIN_USER_ID должен быть числом, получено %r", raw)
            return None

    @staticmethod
    def _parse_chat_id(raw: str) -> int | str | None:
        if not raw:
            return None
        try:
            return int(raw)
        except ValueError:
            return raw  # @username канала/группы

    @staticmethod
    def _parse_int(raw: str | None, default: int, low: int, high: int) -> int:
        try:
            value = int(str(raw).strip())
        except (TypeError, ValueError):
            return default
        return value if low <= value <= high else default

    def time_of_day(self) -> dt_time:
        """Время ежедневных задач с корректным tzinfo (pytz требует localize)."""
        tzinfo = self.timezone
        if isinstance(tzinfo, pytz.BaseTzInfo):  # pragma: no cover - fallback-ветка
            tzinfo = datetime.now(tzinfo).tzinfo
        return dt_time(hour=self.daily_hour, minute=self.daily_minute, tzinfo=tzinfo)


settings = Settings()


def now_local() -> datetime:
    return datetime.now(settings.timezone)


def today_local() -> date:
    return now_local().date()


# ---------------------------------------------------------------------------
# Работа с JSON-файлами
# ---------------------------------------------------------------------------

_file_lock = threading.RLock()


def _ensure_dirs() -> None:
    for path in (CONFIG_DIR, DATA_DIR, PHOTOS_DIR, UPLOADED_PHOTOS_DIR, LOGS_DIR):
        path.mkdir(parents=True, exist_ok=True)


def read_json(path: Path, default: Any) -> Any:
    """Читает JSON; при отсутствии/повреждении файла возвращает default.

    utf-8-sig — чтобы файлы, сохранённые Блокнотом/Excel с BOM, тоже читались.
    """
    with _file_lock:
        try:
            with path.open("r", encoding="utf-8-sig") as fh:
                return json.load(fh)
        except FileNotFoundError:
            write_json(path, default)
            return json.loads(json.dumps(default))
        except (json.JSONDecodeError, OSError) as exc:
            logger.error("Не удалось прочитать %s: %s", path, exc)
            broken = path.with_suffix(path.suffix + ".broken")
            try:
                path.replace(broken)
                logger.error("Повреждённый файл сохранён как %s", broken)
            except OSError:
                pass
            write_json(path, default)
            return json.loads(json.dumps(default))


def write_json(path: Path, data: Any) -> None:
    """Атомарная запись JSON (tmp + os.replace)."""
    with _file_lock:
        path.parent.mkdir(parents=True, exist_ok=True)
        fd, tmp_name = tempfile.mkstemp(dir=str(path.parent), suffix=".tmp")
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as fh:
                json.dump(data, fh, ensure_ascii=False, indent=2)
                fh.write("\n")
            os.replace(tmp_name, path)
        except Exception:
            try:
                os.unlink(tmp_name)
            except OSError:
                pass
            raise


# ---------------------------------------------------------------------------
# Дни рождения
# ---------------------------------------------------------------------------


def _coerce_int(value: Any) -> int | None:
    """Аккуратно приводит к int: 5, "5", " 5 " -> 5; 1.5, "1.5", True -> None."""
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value) if value.is_integer() else None
    if isinstance(value, str):
        text = value.strip()
        if not text:
            return None
        try:
            return int(text)
        except ValueError:
            return None
    return None


def _normalize_birthday(item: Any) -> dict | None:
    if not isinstance(item, dict):
        return None
    name = str(item.get("name") or "").strip()
    day = _coerce_int(item.get("day"))
    month = _coerce_int(item.get("month"))
    if not name or day is None or month is None:
        return None
    if not (1 <= day <= 31) or not (1 <= month <= 12):
        return None
    return {
        "id": str(item.get("id") or uuid.uuid4()),
        "name": name,
        "day": day,
        "month": month,
    }


def load_birthdays() -> list[dict]:
    raw = read_json(BIRTHDAYS_FILE, [])
    if not isinstance(raw, list):
        logger.warning("%s должен содержать массив — файл будет перезаписан", BIRTHDAYS_FILE)
        raw = []
        write_json(BIRTHDAYS_FILE, raw)
    result: list[dict] = []
    for item in raw:
        normalized = _normalize_birthday(item)
        if normalized is not None:
            result.append(normalized)
    return result


def save_birthdays(items: Iterable[dict]) -> None:
    write_json(BIRTHDAYS_FILE, list(items))


def add_birthday(name: str, day: int, month: int) -> dict:
    items = load_birthdays()
    record = {"id": str(uuid.uuid4()), "name": name, "day": day, "month": month}
    items.append(record)
    save_birthdays(items)
    return record


def delete_birthdays_by_name(name: str) -> list[dict]:
    target = name.strip().casefold()
    items = load_birthdays()
    removed = [item for item in items if item["name"].casefold() == target]
    if removed:
        save_birthdays([item for item in items if item["name"].casefold() != target])
    return removed


def delete_birthday_by_id(record_id: str) -> dict | None:
    """Удаляет ровно одну запись по id (нужно для панели владельца)."""
    items = load_birthdays()
    removed = next((item for item in items if item["id"] == record_id), None)
    if removed is None:
        return None
    save_birthdays([item for item in items if item["id"] != record_id])
    return removed


def _plural_days(count: int) -> str:
    if count % 10 == 1 and count % 100 != 11:
        return "день"
    if 2 <= count % 10 <= 4 and not 12 <= count % 100 <= 14:
        return "дня"
    return "дней"


def _next_occurrence(item: dict, today: date) -> date | None:
    """Ближайшее наступление даты (0 = сегодня). 29 февраля ищется вперёд."""
    for year in (today.year, today.year + 1, today.year + 2):
        try:
            candidate = date(year, item["month"], item["day"])
        except ValueError:
            continue
        if candidate >= today:
            return candidate
    return None


def _relative_label(days: int) -> str:
    """Подпись «сколько ждать». Для далёких дат — пусто, чтобы не шуметь."""
    if days == 0:
        return "🎉 сегодня"
    if days == 1:
        return "завтра"
    if days <= 30:
        return f"через {days} {_plural_days(days)}"
    return ""


def format_birthdays(items: list[dict]) -> str:
    if not items:
        return (
            "📋 Список дней рождения пуст.\n\n"
            "Администратор может добавить запись командой /add_birthday"
        )
    today = today_local()
    ordered = sorted(
        items,
        key=lambda i: (
            _next_occurrence(i, today) or date(9999, 12, 31),
            i["name"].casefold(),
        ),
    )

    lines = [f"🎂 <b>Дни рождения</b> · {len(items)}", ""]
    current_header = None

    for item in ordered:
        occurrence = _next_occurrence(item, today)
        if occurrence is None:
            header = MONTHS_NOMINATIVE[item["month"] - 1]
            weekday = ""
            relative = ""
        else:
            header = MONTHS_NOMINATIVE[item["month"] - 1]
            if occurrence.year != today.year:
                header = f"{header} {occurrence.year}"
            weekday = WEEKDAYS_SHORT[occurrence.weekday()]
            relative = _relative_label((occurrence - today).days)

        if header != current_header:
            # Воздух перед новым месяцем.
            if current_header is not None:
                lines.append("")
            current_header = header
            lines.append(f"<b>{header}</b>")
        elif lines:
            # Между записями одного месяца — пустая строка: перенос длинного имени
            # остаётся плотным, а новая дата визуально отделена.
            lines.append("")

        date_part = f"{item['day']:02d}.{item['month']:02d}"
        if weekday:
            date_part = f"{date_part} {weekday}"
        row = f"<b>{date_part}</b> — {html.escape(item['name'])}"
        if relative:
            row = f"{row} · {relative}"
        lines.append(row)

    return "\n".join(lines)


def birthdays_on(day: date) -> list[dict]:
    return sorted(
        (item for item in load_birthdays() if item["day"] == day.day and item["month"] == day.month),
        key=lambda i: i["name"].casefold(),
    )


# ---------------------------------------------------------------------------
# Упоминание всех участников
#
# В birthdays.json имя хранится в формате «Имя username»: «Никита Nekit_098».
# Для упоминания берём последнее слово и ставим перед ним «@»: «@Nekit_098».
# Если username нет (одно имя) — оставляем имя как есть, чтобы человек всё
# равно попал в общий список.
# ---------------------------------------------------------------------------


def mention_for_name(name: str) -> str:
    parts = str(name or "").split()
    if not parts:
        return ""
    if len(parts) >= 2:
        # «Никита Nekit_098» -> «@Nekit_098»; лишний «@» в файле не мешает.
        username = parts[-1].lstrip("@")
        if username:
            return f"@{username}"
    return parts[0]


def build_mentions_text(items: Iterable[dict] | None = None) -> str:
    """Одно сообщение со всеми упоминаниями из birthdays.json."""
    records = load_birthdays() if items is None else list(items)
    seen: set[str] = set()
    mentions: list[str] = []
    for item in records:
        mention = mention_for_name(item.get("name", ""))
        key = mention.casefold()
        if not mention or key in seen:
            continue
        seen.add(key)
        mentions.append(mention)
    return " ".join(mentions)


# ---------------------------------------------------------------------------
# Погода (Open-Meteo, без ключа)
# ---------------------------------------------------------------------------

_http = requests.Session()
_http.headers.update(
    {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) group-bot/1.0",
        "Accept": "*/*",
    }
)
_retry = Retry(
    total=2,
    backoff_factor=0.5,
    status_forcelist=(500, 502, 503, 504),
    allowed_methods=("GET",),
)
_http.mount("https://", HTTPAdapter(max_retries=_retry))
_http.mount("http://", HTTPAdapter(max_retries=_retry))

WEATHER_CODES = {
    0: "ясно",
    1: "малооблачно",
    2: "облачно",
    3: "пасмурно",
    45: "туман",
    48: "изморозь",
    51: "морось",
    53: "морось",
    55: "сильная морось",
    61: "небольшой дождь",
    63: "дождь",
    65: "сильный дождь",
    66: "ледяной дождь",
    67: "ледяной дождь",
    71: "небольшой снег",
    73: "снег",
    75: "сильный снег",
    77: "снежная крупа",
    80: "ливень",
    81: "ливень",
    82: "сильный ливень",
    85: "снегопад",
    86: "сильный снегопад",
    95: "гроза",
    96: "гроза с градом",
    99: "гроза с градом",
}


def parse_coords(raw: str) -> tuple[float, float] | None:
    """'55.585639, 37.722646' -> (55.585639, 37.722646)."""
    parts = [part.strip() for part in str(raw or "").replace(";", ",").split(",")]
    if len(parts) != 2:
        return None
    try:
        lat, lon = float(parts[0]), float(parts[1])
    except ValueError:
        return None
    if not (-90 <= lat <= 90 and -180 <= lon <= 180):
        return None
    return lat, lon


def _fetch_weather_hour(
    location: dict, target_dt: datetime, fields: str
) -> dict[str, Any] | None:
    """Почасовые значения Open-Meteo на конкретный час. None — данных нет."""
    coords = parse_coords(location.get("coords", ""))
    if coords is None:
        return None
    lat, lon = coords
    day = target_dt.strftime("%Y-%m-%d")
    params = {
        "latitude": f"{lat:.6f}",
        "longitude": f"{lon:.6f}",
        "hourly": fields,
        "timezone": settings.timezone_name,
        "start_date": day,
        "end_date": day,
    }
    try:
        response = _http.get(WEATHER_URL, params=params, timeout=WEATHER_TIMEOUT)
        response.raise_for_status()
        data = response.json()
    except (requests.RequestException, ValueError) as exc:
        logger.warning("Погода недоступна: %s", exc)
        return None

    hourly = data.get("hourly") or {}
    times = hourly.get("time") or []
    target = target_dt.strftime("%Y-%m-%dT%H:00")
    if target not in times:
        logger.info("Погода: нет данных на %s", target)
        return None
    index = times.index(target)

    values: dict[str, Any] = {}
    for key in fields.split(","):
        series = hourly.get(key) or []
        values[key] = series[index] if index < len(series) else None
    return values


def _format_temperature(value: Any) -> str | None:
    if not isinstance(value, (int, float)):
        return None
    rounded = round(value)
    return "0°" if rounded == 0 else f"{rounded:+d}°"


def build_weather_text(location: dict, meetup_dt: datetime) -> str | None:
    """Короткая сводка погоды на час сходки. None — данных нет."""
    values = _fetch_weather_hour(
        location, meetup_dt, "temperature_2m,precipitation_probability,weather_code"
    )
    if values is None:
        return None
    temperature = _format_temperature(values.get("temperature_2m"))
    if temperature is None:
        return None

    parts = [temperature]
    code = values.get("weather_code")
    if isinstance(code, (int, float)):
        description = WEATHER_CODES.get(int(code))
        if description:
            parts.append(description)
    chance = values.get("precipitation_probability")
    if isinstance(chance, (int, float)) and chance >= 30:
        parts.append(f"осадки {chance:.0f}%")
    return f"🌤 Погода на {meetup_dt.strftime('%H:%M')}: {', '.join(parts)}"


def build_weather_report(location: dict, target_dt: datetime) -> str:
    """Подробная сводка для команды /weather. Всегда возвращает текст."""
    name = location.get("name") or "локация"
    if parse_coords(location.get("coords", "")) is None:
        return (
            f"⚠️ У локации «{html.escape(name)}» не заданы координаты — "
            "прогноз недоступен."
        )

    today = today_local()
    if target_dt.date() < today:
        return "⚠️ Прогноз есть только на будущее. Выбери другую дату."
    if target_dt.date() > today + timedelta(days=MAX_FORECAST_DAYS):
        return f"⚠️ Прогноз доступен не дальше чем на {MAX_FORECAST_DAYS} дней вперёд."

    values = _fetch_weather_hour(
        location,
        target_dt,
        "temperature_2m,apparent_temperature,precipitation_probability,"
        "precipitation,weather_code,wind_speed_10m",
    )
    if values is None:
        return "⚠️ Не удалось получить прогноз погоды. Попробуй позже."

    lines = [
        f"🌤 <b>Погода</b> · {html.escape(name)}",
        f"📅 {WEEKDAYS[target_dt.weekday()]}, {target_dt.strftime('%d.%m.%Y')} "
        f"· {target_dt.strftime('%H:%M')}",
    ]

    temperature = _format_temperature(values.get("temperature_2m"))
    feels = _format_temperature(values.get("apparent_temperature"))
    if temperature:
        line = f"🌡 Температура: {temperature}"
        if feels:
            line = f"{line} (ощущается как {feels})"
        lines.append(line)

    code = values.get("weather_code")
    if isinstance(code, (int, float)):
        description = WEATHER_CODES.get(int(code))
        if description:
            lines.append(f"☁️ {description}")

    chance = values.get("precipitation_probability")
    amount = values.get("precipitation")
    if isinstance(chance, (int, float)):
        line = f"💧 Осадки: {chance:.0f}%"
        if isinstance(amount, (int, float)) and amount > 0:
            line = f"{line} ({amount:.1f} мм)"
        lines.append(line)

    wind = values.get("wind_speed_10m")
    if isinstance(wind, (int, float)):
        lines.append(f"💨 Ветер: {wind:.0f} км/ч")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Локации и сходки
# ---------------------------------------------------------------------------


def load_locations() -> list[dict]:
    raw = read_json(LOCATIONS_FILE, [])
    locations: list[dict] = []
    if not isinstance(raw, list):
        logger.error("%s должен содержать массив локаций", LOCATIONS_FILE)
        return locations
    for item in raw:
        if not isinstance(item, dict):
            continue
        loc_id = str(item.get("id") or "").strip()
        name = str(item.get("name") or "").strip()
        if not loc_id or not name:
            continue
        locations.append(
            {
                "id": loc_id,
                "name": name,
                "time": str(item.get("time") or "").strip(),
                "address": str(item.get("address") or "").strip(),
                "coords": str(item.get("coords") or "").strip(),
                "link": str(item.get("link") or "").strip(),
                "note": str(item.get("note") or "").strip(),
                "photo": str(item.get("photo") or "").strip(),
            }
        )
    return locations


def coords_to_link(coords: str) -> str:
    """'55.585639, 37.722646' -> ссылка на точку в Яндекс.Картах (резерв для link)."""
    parts = [part.strip() for part in str(coords or "").replace(";", ",").split(",")]
    if len(parts) != 2:
        return ""
    try:
        lat, lon = float(parts[0]), float(parts[1])
    except ValueError:
        return ""
    if not (-90 <= lat <= 90 and -180 <= lon <= 180):
        return ""
    return f"https://yandex.ru/maps/?ll={lon:.6f}%2C{lat:.6f}&z=17&pt={lon:.6f}%2C{lat:.6f}"


def location_link(location: dict) -> str:
    """Ссылка на карту: приоритет — явный link, иначе координаты."""
    return location.get("link") or coords_to_link(location.get("coords", ""))


def find_location(location_id: str) -> dict | None:
    for location in load_locations():
        if location["id"] == location_id:
            return location
    return None


def save_locations(items: list[dict]) -> None:
    write_json(LOCATIONS_FILE, list(items))


def upsert_location(record: dict) -> None:
    """Добавляет локацию или заменяет существующую с тем же id."""
    items = load_locations()
    for index, item in enumerate(items):
        if item["id"] == record["id"]:
            items[index] = record
            break
    else:
        items.append(record)
    save_locations(items)


def delete_location_by_id(location_id: str) -> dict | None:
    items = load_locations()
    removed = next((item for item in items if item["id"] == location_id), None)
    if removed is None:
        return None
    save_locations([item for item in items if item["id"] != location_id])
    return removed


# ---------------------------------------------------------------------------
# Файлы фотографий (config/photos и data/photos)
#
# config/photos — фото из репозитория; data/photos — загруженные через бота.
# На Bothost config/ перезаписывается при деплое, а data/ сохраняется.
# ---------------------------------------------------------------------------

PHOTO_EXTENSIONS = {".jpg", ".jpeg", ".png", ".webp", ".gif"}

_BAD_NAME_CHARS = re.compile(r'[\\/:*?"<>|\x00-\x1f]+')


def list_photo_files() -> list[Path]:
    """Все фото из обеих папок; при совпадении имён первым идёт config/photos."""
    files: list[Path] = []
    seen: set[str] = set()
    for directory in (PHOTOS_DIR, UPLOADED_PHOTOS_DIR):
        if not directory.is_dir():
            continue
        for path in sorted(directory.iterdir(), key=lambda p: p.name.casefold()):
            if not path.is_file() or path.suffix.lower() not in PHOTO_EXTENSIONS:
                continue
            key = path.name.casefold()
            if key in seen:
                continue
            seen.add(key)
            files.append(path)
    return sorted(files, key=lambda path: path.name.casefold())


def find_photo_file(file_name: str) -> Path | None:
    """Файл по имени (без учёта регистра) среди обеих папок."""
    wanted = Path(str(file_name or "")).name.casefold()
    if not wanted:
        return None
    for path in list_photo_files():
        if path.name.casefold() == wanted:
            return path
    return None


def photo_reference(path: Path) -> str:
    """Путь для locations.json: относительно папки бота (config/photos/x.jpg)."""
    try:
        return path.relative_to(BASE_DIR).as_posix()
    except ValueError:
        return path.as_posix()


def safe_photo_name(raw: str) -> str:
    """Имя файла без расширения: пробелы -> «_», запрещённые символы убираем."""
    text = _BAD_NAME_CHARS.sub("", str(raw or "").strip()).strip(". ")
    text = re.sub(r"\s+", "_", text)
    return text[:64]


def photo_reference_from_name(raw: str) -> str:
    """«vegas», «vegas.jpg» или «config/photos/vegas.jpg» -> ссылка для локации.

    Понимает имена без расширения и не зависит от регистра. Пустая строка —
    файл не найден.
    """
    name = Path(str(raw or "").strip().replace("\\", "/")).name
    if not name:
        return ""
    files = list_photo_files()
    exact = next((p for p in files if p.name == name), None)
    if exact is not None:
        return photo_reference(exact)
    wanted = name.casefold()
    same_name = next((p for p in files if p.name.casefold() == wanted), None)
    if same_name is not None:
        return photo_reference(same_name)
    stem = Path(name).stem.casefold()
    same_stem = next((p for p in files if p.stem.casefold() == stem), None)
    if same_stem is not None:
        return photo_reference(same_stem)
    return ""


def photos_using(file_name: str) -> list[str]:
    """Названия локаций, которые ссылаются на этот файл."""
    target = Path(file_name).name.casefold()
    names: list[str] = []
    for location in load_locations():
        if Path(location.get("photo") or "").name.casefold() == target:
            names.append(location["name"])
    return names


def parse_location_time(raw: str) -> dt_time | None:
    value = (raw or "").strip()
    for fmt in ("%H:%M", "%H.%M", "%H"):
        try:
            return datetime.strptime(value, fmt).time()
        except ValueError:
            continue
    return None


def resolve_photo_path(location: dict) -> Path | None:
    raw = location.get("photo") or ""
    if not raw:
        return None
    path = Path(raw)
    if not path.is_absolute():
        path = BASE_DIR / path
    if path.is_file():
        return path
    # Linux различает регистр: ссылка DNB.jpg и файл dnb.jpg — разные пути.
    parent = path.parent
    if parent.is_dir():
        wanted = path.name.casefold()
        for candidate in parent.iterdir():
            if candidate.is_file() and candidate.name.casefold() == wanted:
                return candidate
    logger.warning("Фото локации не найдено: %s", path)
    return None


def build_meetup_message(location: dict, meetup_date: date, time_text: str) -> str:
    weekday = WEEKDAYS[meetup_date.weekday()]
    address = location.get("address") or "—"
    link = location_link(location)
    place_line = f"📍 Место: {location['name']}"
    map_line = f"🗺 {address}"
    if link:
        map_line = f"{map_line} — {link}"
    note = location.get("note") or ""
    lines = [
        "📢 <b>ОФИЦИАЛЬНОЕ СООБЩЕНИЕ</b>",
        "",
        f"📅 Дата: {meetup_date.strftime('%d.%m.%Y')} ({weekday})",
        f"🕐 Время: {time_text or '—'}",
        place_line,
        map_line,
    ]
    if note:
        lines.append(f"📝 {note}")
    return "\n".join(lines)


def load_meetup() -> dict | None:
    raw = read_json(MEETUP_FILE, None)
    if not isinstance(raw, dict) or not raw:
        return None
    return raw


def save_meetup(payload: dict) -> None:
    write_json(MEETUP_FILE, payload)


def clear_meetup() -> None:
    write_json(MEETUP_FILE, None)


# ---------------------------------------------------------------------------
# Вспомогательные функции Telegram
# ---------------------------------------------------------------------------


async def send_text(
    bot,
    chat_id: int | str,
    text: str,
    **kwargs: Any,
):
    """send_message с фолбэком на plain-text при ошибке разметки."""
    parse_mode = kwargs.pop("parse_mode", ParseMode.HTML)
    try:
        return await bot.send_message(chat_id=chat_id, text=text, parse_mode=parse_mode, **kwargs)
    except BadRequest as exc:
        if parse_mode and ("parse" in str(exc).lower() or "entit" in str(exc).lower()):
            logger.warning("Разметка отклонена Telegram, отправляю как текст: %s", exc)
            return await bot.send_message(chat_id=chat_id, text=text, **kwargs)
        raise


def _is_reply_target_missing(exc: BadRequest) -> bool:
    """Telegram не нашёл сообщение, на которое отвечаем (его уже удалили)."""
    text = str(exc).lower()
    return "replied" in text and "not found" in text


def _is_parse_error(exc: BadRequest) -> bool:
    text = str(exc).lower()
    return "parse" in text or "entit" in text


async def reply_text(update: Update, text: str, **kwargs: Any):
    """Ответ на сообщение с фолбэками: без reply, если оно удалено, и без разметки."""
    message = update.effective_message
    if message is None:
        return None
    parse_mode = kwargs.pop("parse_mode", ParseMode.HTML)

    async def _send(mode: str | None, use_reply: bool):
        if use_reply:
            if mode:
                return await message.reply_text(text, parse_mode=mode, **kwargs)
            return await message.reply_text(text, **kwargs)
        bot = message.get_bot()
        if mode:
            return await bot.send_message(
                chat_id=message.chat_id, text=text, parse_mode=mode, **kwargs
            )
        return await bot.send_message(chat_id=message.chat_id, text=text, **kwargs)

    try:
        return await _send(parse_mode, True)
    except BadRequest as exc:
        if _is_reply_target_missing(exc):
            # Сообщение пользователя уже удалено — отвечаем просто в чат.
            logger.info("Исходное сообщение удалено, отправляю без reply: %s", exc)
            return await _send(parse_mode, False)
        if parse_mode and _is_parse_error(exc):
            logger.warning("Разметка отклонена Telegram, отправляю как текст: %s", exc)
            try:
                return await _send(None, True)
            except BadRequest as inner:
                if _is_reply_target_missing(inner):
                    return await _send(None, False)
                raise
        raise


# ---------------------------------------------------------------------------
# Удаление служебных сообщений
#
# Любая команда/диалог помечает свои сообщения (команду пользователя, подсказки,
# клавиатуры, ответы об ошибках) и в конце удаляет их, оставляя только итог.
# ---------------------------------------------------------------------------

SERVICE_MSG_KEY = "service_msg_ids"

# Ключи, которые относятся к незавершённому диалогу (не трогаем service_msg_ids).
FLOW_KEYS = (
    "bd_name",
    "bd_day",
    "meetup_location",
    "meetup_time",
    "meetup_date",
    "weather_location",
    "weather_date",
    "weather_time",
)


def _clear_flow(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Сбрасывает данные диалога, сохраняя список сообщений на удаление."""
    for key in FLOW_KEYS:
        context.user_data.pop(key, None)


def _reset_service_messages(context: ContextTypes.DEFAULT_TYPE) -> None:
    context.user_data[SERVICE_MSG_KEY] = []


def _track_message(context: ContextTypes.DEFAULT_TYPE, message_id: Any) -> None:
    """Запоминает сообщение, которое нужно удалить по завершении команды."""
    if not settings.delete_service_messages:
        return
    if not isinstance(message_id, int):
        return
    ids = context.user_data.setdefault(SERVICE_MSG_KEY, [])
    if message_id not in ids:
        ids.append(message_id)


def _track_incoming(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Помечает на удаление сообщение пользователя (саму команду или ответ)."""
    message = update.effective_message
    _track_message(context, getattr(message, "message_id", None))


async def reply_tracked(
    update: Update, context: ContextTypes.DEFAULT_TYPE, text: str, **kwargs: Any
):
    """reply_text, который помечает и входящее сообщение, и свой ответ."""
    _track_incoming(update, context)
    message = await reply_text(update, text, **kwargs)
    _track_message(context, getattr(message, "message_id", None))
    return message


async def send_tracked(
    context: ContextTypes.DEFAULT_TYPE, chat_id: int | str, text: str, **kwargs: Any
):
    """send_text, который помечает своё сообщение на удаление."""
    message = await send_text(context.bot, chat_id, text, **kwargs)
    _track_message(context, getattr(message, "message_id", None))
    return message


async def delete_service_messages(
    context: ContextTypes.DEFAULT_TYPE, chat_id: int | str | None
) -> int:
    """Удаляет все помеченные сообщения. Ошибки не критичны."""
    message_ids = context.user_data.pop(SERVICE_MSG_KEY, []) or []
    if not message_ids or chat_id is None or context.bot is None:
        return 0
    deleted = 0
    for message_id in message_ids:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=message_id)
            deleted += 1
        except TelegramError as exc:
            # Бот не админ, сообщение уже удалено или старше 48 часов.
            logger.info("Не удалось удалить сообщение %s: %s", message_id, exc)
    logger.info("Удалено служебных сообщений: %s из %s", deleted, len(message_ids))
    return deleted


def _member_status(member: Any) -> str:
    status = getattr(member, "status", None)
    value = getattr(status, "value", None)
    if value is None:
        value = status if isinstance(status, str) else str(status or "")
    return str(value).strip().lower()
ADMIN_STATUSES = {"creator", "owner", "administrator"}


async def is_chat_admin(bot, chat_id: int | str, user_id: int) -> bool:
    try:
        member = await bot.get_chat_member(chat_id=chat_id, user_id=user_id)
    except TelegramError as exc:
        logger.warning("get_chat_member(%s, %s) не удался: %s", chat_id, user_id, exc)
        return False
    return _member_status(member) in ADMIN_STATUSES


async def ensure_group(update: Update) -> bool:
    chat = update.effective_chat
    if chat is None:
        return False
    if chat.type == ChatType.PRIVATE:
        if is_admin_user(update.effective_user):
            await reply_text(update, "ℹ️ В личке доступна админ-панель: /start")
        else:
            await reply_text(update, PRIVATE_ONLY_REPLY)
        return False
    return True


async def ensure_admin(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    if not await ensure_group(update):
        return False
    chat = update.effective_chat
    user = update.effective_user
    if chat is None or user is None:
        return False
    if await is_chat_admin(context.bot, chat.id, user.id):
        return True
    await reply_text(
        update,
        "⛔ Команда доступна только администраторам чата.",
    )
    return False


def admin_only(
    func: Callable[[Update, ContextTypes.DEFAULT_TYPE], Awaitable[Any]],
) -> Callable[[Update, ContextTypes.DEFAULT_TYPE], Awaitable[Any]]:
    @wraps(func)
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not await ensure_admin(update, context):
            return ConversationHandler.END
        return await func(update, context)

    return wrapper


def remember_group_chat(update: Update) -> None:
    """Запоминает чат, где бот используется (фолбэк для GROUP_CHAT_ID)."""
    chat = update.effective_chat
    if chat is None or chat.type == ChatType.PRIVATE:
        return
    try:
        state = read_json(STATE_FILE, {})
        if not isinstance(state, dict):
            state = {}
        if state.get("last_group_chat_id") != chat.id:
            state["last_group_chat_id"] = chat.id
            state["last_group_chat_title"] = chat.title or chat.username or ""
            write_json(STATE_FILE, state)
            logger.info(
                "Активный групповой чат: %s (%s)", chat.id, chat.title or chat.username or "—"
            )
    except OSError as exc:  # pragma: no cover
        logger.warning("Не удалось сохранить state.json: %s", exc)


def target_chat_id(context: ContextTypes.DEFAULT_TYPE) -> int | str | None:
    if settings.group_chat_id is not None:
        return settings.group_chat_id
    state = read_json(STATE_FILE, {})
    if isinstance(state, dict):
        value = state.get("last_group_chat_id")
        if isinstance(value, int):
            return value
    logger.warning("GROUP_CHAT_ID не задан и чат ещё не известен — пропускаю отправку")
    return None


# ---------------------------------------------------------------------------
# Общие команды
# ---------------------------------------------------------------------------


def build_help_text() -> str:
    return "\n".join(
        [
            "🤖 <b>Команды бота</b>",
            "",
            "<b>Дни рождения</b>",
            "/birthdays — список дней рождения по месяцам",
            "/add_birthday — добавить запись (админ)",
            "/del_birthday &lt;имя&gt; — удалить запись (админ)",
            "",
            "<b>Сходки</b>",
            "/meetup — опубликовать сходку",
            "/cancel_meetup — отменить запланированную сходку",
            "",
            "<b>Погода</b>",
            "/weather — прогноз на локацию, дату и время",
            "",
            "<b>Прочее</b>",
            "/cancel — прервать текущий диалог",
            "",
            f"🕘 Ежедневная сводка: {settings.daily_hour:02d}:{settings.daily_minute:02d} "
            f"({settings.timezone_name})",
        ]
    )


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat = update.effective_chat
    if chat is not None and chat.type == ChatType.PRIVATE:
        # В личку попадает только владелец: остальных отсекает private_chat_guard.
        await admin_panel(update, context)
        return
    if not await ensure_group(update):
        return
    remember_group_chat(update)
    await reply_text(update, build_help_text())


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await cmd_start(update, context)


async def cmd_chatid(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat = update.effective_chat
    if chat is None:
        return
    if chat.type == ChatType.PRIVATE:
        await reply_text(update, PRIVATE_ONLY_REPLY)
        return
    remember_group_chat(update)
    await reply_text(update, f"🆔 ID этого чата: <code>{chat.id}</code>")


async def private_chat_guard(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """В личных сообщениях бот работает только с владельцем (админ-панель)."""
    if update.effective_chat is None:
        return
    if is_admin_user(update.effective_user):
        return  # владельцу в личке доступна админ-панель
    await reply_text(update, PRIVATE_ONLY_REPLY)
    # Не даём остальным обработчикам продублировать ответ в личке.
    raise ApplicationHandlerStop


# ---------------------------------------------------------------------------
# Дни рождения: /birthdays
# ---------------------------------------------------------------------------


async def cmd_birthdays(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await ensure_group(update):
        return
    remember_group_chat(update)
    _reset_service_messages(context)
    _track_incoming(update, context)
    await reply_text(update, format_birthdays(load_birthdays()))
    await delete_service_messages(context, update.effective_chat.id)


# ---------------------------------------------------------------------------
# Дни рождения: /add_birthday (диалог)
# ---------------------------------------------------------------------------

ADD_NAME, ADD_DAY, ADD_MONTH = range(3)


def _max_day(month: int) -> int:
    return pycalendar.monthrange(2024, month)[1]  # 2024 — високосный, 29 февраля разрешено


@admin_only
async def add_birthday_entry(update: Update, context: ContextTypes.DEFAULT_TYPE):
    _clear_flow(context)
    _reset_service_messages(context)
    remember_group_chat(update)
    await reply_tracked(
        update,
        context,
        "➕ <b>Новый день рождения</b>\n\n"
        "Шаг 1/3 — напиши имя и username через пробел:\n"
        "Прервать: /cancel",
    )
    return ADD_NAME


@admin_only
async def add_birthday_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message = update.effective_message
    raw = (message.text or "").strip() if message else ""
    _track_incoming(update, context)
    if not raw:
        await reply_tracked(update, context, "Имя не может быть пустым. Напиши имя или /cancel.")
        return ADD_NAME
    if len(raw) > 64:
        await reply_tracked(
            update, context, "Слишком длинное имя (максимум 64 символа). Попробуй ещё раз."
        )
        return ADD_NAME
    context.user_data["bd_name"] = raw
    await reply_tracked(
        update,
        context,
        f"Шаг 2/3 — день рождения <b>{html.escape(raw)}</b>: день (1–31).",
    )
    return ADD_DAY


@admin_only
async def add_birthday_day(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw = (update.effective_message.text or "").strip() if update.effective_message else ""
    _track_incoming(update, context)
    try:
        day = int(raw)
    except ValueError:
        await reply_tracked(update, context, "Нужно число от 1 до 31. Попробуй ещё раз.")
        return ADD_DAY
    if not 1 <= day <= 31:
        await reply_tracked(update, context, "День должен быть от 1 до 31. Попробуй ещё раз.")
        return ADD_DAY
    context.user_data["bd_day"] = day
    await reply_tracked(update, context, "Шаг 3/3 — месяц (1–12).")
    return ADD_MONTH


@admin_only
async def add_birthday_month(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw = (update.effective_message.text or "").strip() if update.effective_message else ""
    _track_incoming(update, context)
    try:
        month = int(raw)
    except ValueError:
        await reply_tracked(update, context, "Нужно число от 1 до 12. Попробуй ещё раз.")
        return ADD_MONTH
    if not 1 <= month <= 12:
        await reply_tracked(update, context, "Месяц должен быть от 1 до 12. Попробуй ещё раз.")
        return ADD_MONTH

    day = int(context.user_data.get("bd_day", 0))
    name = str(context.user_data.get("bd_name", "")).strip()
    if not name or not 1 <= day <= 31:
        _clear_flow(context)
        await reply_tracked(
            update, context, "Диалог сброшен. Начни заново: /add_birthday"
        )
        await delete_service_messages(context, update.effective_chat.id)
        return ConversationHandler.END

    if day > _max_day(month):
        await reply_tracked(
            update,
            context,
            f"В {MONTHS_GENITIVE[month - 1]} нет {day}-го числа. Введи месяц ещё раз (1–12).",
        )
        return ADD_MONTH

    record = add_birthday(name, day, month)
    _clear_flow(context)
    duplicate_hint = ""
    same_name = [
        item
        for item in load_birthdays()
        if item["name"].casefold() == name.casefold() and item["id"] != record["id"]
    ]
    if same_name:
        duplicate_hint = (
            f"\n\n⚠️ В списке уже есть запись с именем «{html.escape(name)}» "
            f"(всего {len(same_name)}). Если это дубль — удали командой /del_birthday {html.escape(name)}"
        )
    # Итоговое сообщение не помечаем: оно остаётся в чате.
    await reply_text(
        update,
        "✅ Записано: "
        f"<b>{html.escape(record['name'])}</b> — {record['day']:02d} "
        f"{MONTHS_GENITIVE[record['month'] - 1]}{duplicate_hint}",
    )
    await delete_service_messages(context, update.effective_chat.id)
    return ConversationHandler.END


# ---------------------------------------------------------------------------
# Дни рождения: /del_birthday
# ---------------------------------------------------------------------------

DEL_NAME = 10


@admin_only
async def del_birthday_entry(update: Update, context: ContextTypes.DEFAULT_TYPE):
    _reset_service_messages(context)
    args = context.args or []
    name = " ".join(args).strip()
    if name:
        _track_incoming(update, context)
        await _perform_delete(update, context, name)
        return ConversationHandler.END
    await reply_tracked(
        update,
        context,
        "🗑 <b>Удаление дня рождения</b>\n\n"
        "Напиши имя, которое нужно удалить (регистр не важен).\n"
        "Прервать: /cancel",
    )
    return DEL_NAME


@admin_only
async def del_birthday_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    name = (update.effective_message.text or "").strip() if update.effective_message else ""
    _track_incoming(update, context)
    if not name:
        await reply_tracked(update, context, "Имя не может быть пустым. Напиши имя или /cancel.")
        return DEL_NAME
    await _perform_delete(update, context, name)
    return ConversationHandler.END


async def _perform_delete(
    update: Update, context: ContextTypes.DEFAULT_TYPE, name: str
) -> None:
    removed = delete_birthdays_by_name(name)
    if not removed:
        # Итог не помечаем: пользователь должен увидеть, что запись не найдена.
        await reply_text(
            update,
            f"🤷 Запись с именем «{html.escape(name)}» не найдена. "
            "Список: /birthdays",
        )
        await delete_service_messages(context, update.effective_chat.id)
        return
    names = ", ".join(html.escape(item["name"]) for item in removed)
    await reply_text(update, f"✅ Удалено записей: {len(removed)} ({names}).")
    await delete_service_messages(context, update.effective_chat.id)


# ---------------------------------------------------------------------------
# Сходки: /meetup
# ---------------------------------------------------------------------------

LOCATION, TIME, MANUAL_TIME, MEETUP_DATE, MANUAL_DATE = range(20, 25)

MEETUP_CALLBACK_CANCEL = "meetup:cancel"


def locations_keyboard() -> InlineKeyboardMarkup:
    rows: list[list[InlineKeyboardButton]] = []
    for location in load_locations():
        title = location["name"]
        if location.get("time"):
            title = f"{title} ({location['time']})"
        rows.append(
            [InlineKeyboardButton(title[:60], callback_data=f"meetup:loc:{location['id']}")]
        )
    rows.append([InlineKeyboardButton("❌ Отмена", callback_data=MEETUP_CALLBACK_CANCEL)])
    return InlineKeyboardMarkup(rows)


def dates_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("Сегодня", callback_data="meetup:date:0"),
                InlineKeyboardButton("Завтра", callback_data="meetup:date:1"),
                InlineKeyboardButton("Послезавтра", callback_data="meetup:date:2"),
            ],
            [
                InlineKeyboardButton("Ввести вручную", callback_data="meetup:date:manual"),
            ],
            [InlineKeyboardButton("❌ Отмена", callback_data=MEETUP_CALLBACK_CANCEL)],
        ]
    )


async def meetup_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    remember_group_chat(update)
    _clear_flow(context)
    _reset_service_messages(context)

    locations = load_locations()
    if not locations:
        await reply_text(
            update,
            "⚠️ Локации не настроены: добавь их в config/locations.json.",
        )
        return ConversationHandler.END

    message = update.effective_message
    _track_message(context, getattr(message, "message_id", None))

    prompt = await reply_text(
        update,
        "📢 <b>Создание сходки</b>\n\nШаг 1/3 — выбери локацию:",
        reply_markup=locations_keyboard(),
    )
    _track_message(context, getattr(prompt, "message_id", None))
    return LOCATION


def times_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("20:00", callback_data="meetup:time:20:00"),
                InlineKeyboardButton("21:00", callback_data="meetup:time:21:00"),
                InlineKeyboardButton("22:00", callback_data="meetup:time:22:00"),
            ],
            [InlineKeyboardButton("Своё время", callback_data="meetup:time:manual")],
            [InlineKeyboardButton("❌ Отмена", callback_data=MEETUP_CALLBACK_CANCEL)],
        ]
    )


async def _callback_group_ok(query) -> bool:
    """Кнопки диалогов доступны всем участникам группы, но не в личке."""
    chat = query.message.chat if query.message else None
    if chat is None:
        return False
    if chat.type == ChatType.PRIVATE:
        await query.answer(PRIVATE_ONLY_REPLY, show_alert=True)
        return False
    return True


async def meetup_location_chosen(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if query is None:
        return ConversationHandler.END
    await query.answer()
    if not await _callback_group_ok(query):
        return ConversationHandler.END

    location_id = (query.data or "").split(":", 2)[-1]
    location = find_location(location_id)
    if location is None:
        await query.answer("Локация не найдена", show_alert=True)
        return ConversationHandler.END

    context.user_data["meetup_location"] = location["id"]
    _track_message(context, getattr(query.message, "message_id", None))
    try:
        await query.edit_message_text(
            f"📍 Локация: <b>{html.escape(location['name'])}</b>",
            parse_mode=ParseMode.HTML,
        )
    except BadRequest as exc:
        logger.info("Не удалось отредактировать сообщение с локацией: %s", exc)

    prompt = await send_text(
        context.bot,
        query.message.chat_id,
        "🕐 Шаг 2/3 — выбери время сходки:",
        reply_markup=times_keyboard(),
    )
    _track_message(context, getattr(prompt, "message_id", None))
    return TIME


async def meetup_time_chosen(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if query is None:
        return ConversationHandler.END
    await query.answer()
    if not await _callback_group_ok(query):
        return ConversationHandler.END

    if "meetup_location" not in context.user_data:
        await query.answer("Сессия устарела, запусти /meetup заново", show_alert=True)
        return ConversationHandler.END

    value = (query.data or "").split(":", 2)[-1]
    _track_message(context, getattr(query.message, "message_id", None))

    if value == "manual":
        prompt = await send_text(
            context.bot,
            query.message.chat_id,
            "Введи время в формате <b>ЧЧ:ММ</b> (например: 21:30).\n"
            "Прервать: /cancel",
        )
        _track_message(context, getattr(prompt, "message_id", None))
        return MANUAL_TIME

    parsed = parse_location_time(value)
    if parsed is None:
        await query.answer("Некорректное время", show_alert=True)
        return TIME

    context.user_data["meetup_time"] = parsed.strftime("%H:%M")
    prompt = await send_text(
        context.bot,
        query.message.chat_id,
        f"🕐 Время: <b>{parsed.strftime('%H:%M')}</b>\n\nШаг 3/3 — выбери дату сходки:",
        reply_markup=dates_keyboard(),
    )
    _track_message(context, getattr(prompt, "message_id", None))
    return MEETUP_DATE


async def meetup_manual_time(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message = update.effective_message
    raw = (message.text or "").strip() if message else ""
    _track_message(context, getattr(message, "message_id", None))

    parsed = parse_location_time(raw)
    if parsed is None:
        prompt = await reply_text(
            update,
            "❌ Не понял время. Нужен формат ЧЧ:ММ, например 21:30.\n"
            "Попробуй ещё раз или /cancel.",
        )
        _track_message(context, getattr(prompt, "message_id", None))
        return MANUAL_TIME

    context.user_data["meetup_time"] = parsed.strftime("%H:%M")
    prompt = await reply_text(
        update,
        f"🕐 Время: <b>{parsed.strftime('%H:%M')}</b>\n\nШаг 3/3 — выбери дату сходки:",
        reply_markup=dates_keyboard(),
    )
    _track_message(context, getattr(prompt, "message_id", None))
    return MEETUP_DATE


async def meetup_date_chosen(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if query is None:
        return ConversationHandler.END
    await query.answer()
    if not await _callback_group_ok(query):
        return ConversationHandler.END

    if "meetup_location" not in context.user_data:
        await query.answer("Сессия устарела, запусти /meetup заново", show_alert=True)
        return ConversationHandler.END
    if "meetup_time" not in context.user_data:
        await query.answer("Сначала выбери время, запусти /meetup заново", show_alert=True)
        return ConversationHandler.END

    value = (query.data or "").split(":", 2)[-1]
    _track_message(context, getattr(query.message, "message_id", None))
    if value == "manual":
        prompt = await send_text(
            context.bot,
            query.message.chat_id,
            "Введи дату в формате <b>ДД.ММ.ГГГГ</b> (например: 25.12.2026).\n"
            "Прервать: /cancel",
        )
        _track_message(context, getattr(prompt, "message_id", None))
        return MANUAL_DATE

    try:
        offset = int(value)
    except ValueError:
        await query.answer("Некорректная дата", show_alert=True)
        return ConversationHandler.END

    target = today_local() + timedelta(days=offset)
    return await _finalize_meetup(update, context, target, chat_id=query.message.chat_id)


async def meetup_manual_date(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message = update.effective_message
    raw = (message.text or "").strip() if message else ""
    _track_message(context, getattr(message, "message_id", None))
    try:
        target = datetime.strptime(raw, "%d.%m.%Y").date()
    except ValueError:
        prompt = await reply_text(
            update,
            "❌ Не получилось разобрать дату. Нужен формат ДД.ММ.ГГГГ, например 25.12.2026.\n"
            "Попробуй ещё раз или /cancel.",
        )
        _track_message(context, getattr(prompt, "message_id", None))
        return MANUAL_DATE
    return await _finalize_meetup(update, context, target, chat_id=update.effective_chat.id)


async def _finalize_meetup(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    meetup_date: date,
    chat_id: int | str,
):
    location_id = str(context.user_data.get("meetup_location") or "")
    location = find_location(location_id)
    if location is None:
        context.user_data.clear()
        await reply_text(update, "⚠️ Локация не найдена. Запусти /meetup заново.")
        return ConversationHandler.END

    time_text = str(context.user_data.get("meetup_time") or "").strip()
    time_value = parse_location_time(time_text) or parse_location_time(
        location.get("time") or ""
    )
    if time_value is None:
        _clear_flow(context)
        await reply_text(update, "⚠️ Не удалось определить время сходки. Запусти /meetup заново.")
        return ConversationHandler.END
    time_text = time_value.strftime("%H:%M")

    meetup_dt = datetime.combine(meetup_date, time_value).replace(tzinfo=settings.timezone)
    now = now_local()
    if meetup_dt <= now:
        prompt = await reply_text(
            update,
            "⏳ Это время уже прошло. Выбери другую дату:",
            reply_markup=dates_keyboard(),
        )
        _track_message(context, getattr(prompt, "message_id", None))
        return MEETUP_DATE

    text = build_meetup_message(location, meetup_date, time_text)
    photo_path = resolve_photo_path(location)
    sent = None
    if photo_path is not None:
        try:
            with photo_path.open("rb") as photo_file:
                sent = await context.bot.send_photo(
                    chat_id=chat_id,
                    photo=photo_file,
                    caption=text,
                    parse_mode=ParseMode.HTML,
                )
        except (TelegramError, OSError) as exc:
            logger.warning("send_photo не удался (%s), отправляю текстом: %s", photo_path, exc)
            sent = None
    if sent is None:
        sent = await send_text(context.bot, chat_id, text)

    # Закрепляем анонс с уведомлением всем участникам.
    message_id = getattr(sent, "message_id", None)
    if message_id is not None:
        try:
            await context.bot.pin_chat_message(
                chat_id=chat_id,
                message_id=message_id,
                disable_notification=False,
            )
            logger.info("Анонс закреплён (%s)", message_id)
        except TelegramError as exc:
            logger.warning("Не удалось закрепить анонс: %s", exc)

    # Порядок в чате: анонс -> погода -> опрос -> упоминания.
    weather_text = await asyncio.to_thread(build_weather_text, location, meetup_dt)
    if weather_text:
        try:
            await context.bot.send_message(chat_id=chat_id, text=weather_text)
        except TelegramError as exc:
            logger.error("Не удалось отправить погоду: %s", exc)

    # Публичный опрос: видно, кто как ответил, без мультивыбора и без "правильного" ответа.
    poll_message_id = None
    try:
        poll_message = await context.bot.send_poll(
            chat_id=chat_id,
            question=POLL_QUESTION,
            options=POLL_OPTIONS,
            is_anonymous=False,
            allows_multiple_answers=False,
            type="regular",
        )
        poll_message_id = getattr(poll_message, "message_id", None)
        logger.info("Опрос отправлен (%s)", poll_message_id)
    except TelegramError as exc:
        logger.error("Не удалось отправить опрос: %s", exc)

    # Закрываем опрос в момент сходки.
    if poll_message_id is not None and context.job_queue is not None:
        for job in context.job_queue.get_jobs_by_name(JOB_MEETUP_POLL_CLOSE):
            job.schedule_removal()
        context.job_queue.run_once(
            meetup_poll_close_job,
            when=meetup_dt,
            name=JOB_MEETUP_POLL_CLOSE,
            chat_id=chat_id,
            data={"chat_id": chat_id, "poll_message_id": poll_message_id},
        )

    # Пересоздаём напоминание: прежнее снимаем.
    for job in _reminder_jobs(context):
        job.schedule_removal()

    reminder_at = meetup_dt - timedelta(hours=2)
    reminder_info = "напоминание не требуется — до сходки меньше двух часов"
    if reminder_at > now and context.job_queue is not None:
        context.job_queue.run_once(
            meetup_reminder_job,
            when=reminder_at,
            name=JOB_MEETUP_REMINDER,
            chat_id=chat_id,
            data={
                "name": location["name"],
                "time": time_text,
                "chat_id": chat_id,
            },
        )
        reminder_info = f"напоминание в {reminder_at.strftime('%d.%m.%Y %H:%M')} (МСК)"

    save_meetup(
        {
            "location_id": location["id"],
            "name": location["name"],
            "time": time_text,
            "chat_id": chat_id,
            "date": meetup_date.isoformat(),
            "meetup_at": meetup_dt.isoformat(),
            "reminder_at": reminder_at.isoformat(),
            "message_id": getattr(sent, "message_id", None),
            "poll_message_id": poll_message_id,
            "created_by": update.effective_user.id if update.effective_user else None,
            "created_at": now.isoformat(),
        }
    )
    _clear_flow(context)

    # Чистим служебную переписку диалога: в чате остаётся только анонс.
    await delete_service_messages(context, chat_id)
    logger.info(
        "Сходка опубликована: %s, %s %s (%s)",
        location["name"],
        meetup_date.isoformat(),
        time_text,
        reminder_info,
    )
    return ConversationHandler.END


async def meetup_poll_close_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Закрывает опрос к началу сходки."""
    data = context.job.data if context.job else None
    if not isinstance(data, dict):
        return
    chat_id = data.get("chat_id")
    poll_message_id = data.get("poll_message_id")
    if chat_id is None or poll_message_id is None:
        return
    try:
        await context.bot.stop_poll(chat_id=chat_id, message_id=poll_message_id)
        logger.info("Опрос закрыт (%s)", poll_message_id)
    except TelegramError as exc:
        logger.info("Не удалось закрыть опрос: %s", exc)


async def meetup_reminder_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    data = context.job.data if context.job else None
    if not isinstance(data, dict):
        logger.warning("Напоминание без данных — пропускаю")
        return
    chat_id = data.get("chat_id") or target_chat_id(context)
    if chat_id is None:
        return
    text = (
        "⏰ Через 2 часа сходка!\n"
        f"📍 {data.get('name', '')}, {data.get('time', '')}"
    )
    mentions = build_mentions_text()
    if mentions:
        text = f"{text}\n\n{mentions}"
    try:
        await context.bot.send_message(chat_id=chat_id, text=text)
    except TelegramError as exc:
        logger.error("Не удалось отправить напоминание: %s", exc)
    clear_meetup()


async def cmd_cancel_meetup(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await ensure_group(update):
        return
    _reset_service_messages(context)
    _track_incoming(update, context)
    removed = 0
    for job in _reminder_jobs(context):
        job.schedule_removal()
        removed += 1
    current = load_meetup()
    clear_meetup()

    # Открепляем анонс и закрываем опрос, если они были.
    if isinstance(current, dict) and current.get("message_id"):
        try:
            await context.bot.unpin_chat_message(
                chat_id=current.get("chat_id") or update.effective_chat.id,
                message_id=current["message_id"],
            )
        except TelegramError as exc:
            logger.info("Не удалось открепить анонс: %s", exc)

    for job in context.job_queue.get_jobs_by_name(JOB_MEETUP_POLL_CLOSE):
        job.schedule_removal()

    if isinstance(current, dict) and current.get("poll_message_id"):
        try:
            await context.bot.stop_poll(
                chat_id=current.get("chat_id") or update.effective_chat.id,
                message_id=current["poll_message_id"],
            )
        except TelegramError as exc:
            logger.info("Не удалось закрыть опрос: %s", exc)

    if not current and removed == 0:
        await reply_text(update, "🤷 Активной сходки нет — отменять нечего.")
        await delete_service_messages(context, update.effective_chat.id)
        return
    name = current.get("name") if isinstance(current, dict) else None
    await reply_text(
        update,
        "✅ Сходка отменена"
        + (f": {html.escape(str(name))}" if name else "")
        + ".\nНапоминание снято.",
    )
    await delete_service_messages(context, update.effective_chat.id)


def _reminder_jobs(context: ContextTypes.DEFAULT_TYPE) -> list:
    """Активные задачи-напоминания (устойчиво к отсутствию JobQueue)."""
    if context.job_queue is None:
        logger.warning("JobQueue недоступен: установи python-telegram-bot[job-queue]")
        return []
    return list(context.job_queue.get_jobs_by_name(JOB_MEETUP_REMINDER))


async def meetup_buttons_hint(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Подсказка, если в диалоге сходки пишут текст вместо нажатия кнопки."""
    _track_incoming(update, context)
    prompt = await reply_text(
        update,
        "Пожалуйста, выбери вариант кнопкой ниже или прерви диалог командой /cancel.",
    )
    _track_message(context, getattr(prompt, "message_id", None))
    if "meetup_location" not in context.user_data:
        return LOCATION
    if "meetup_time" not in context.user_data:
        return TIME
    return MEETUP_DATE


async def cancel_conversation(update: Update, context: ContextTypes.DEFAULT_TYPE):
    _track_incoming(update, context)
    _clear_flow(context)
    await delete_service_messages(context, update.effective_chat.id)
    return ConversationHandler.END


async def callback_cancel_meetup_flow(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if query is None:
        return ConversationHandler.END
    await query.answer()
    chat_id = query.message.chat_id if query.message else None
    _clear_flow(context)
    try:
        await query.edit_message_text("❌ Создание сходки отменено.")
    except BadRequest as exc:
        logger.info("Не удалось отредактировать сообщение при отмене: %s", exc)
    await delete_service_messages(context, chat_id)
    return ConversationHandler.END


# ---------------------------------------------------------------------------
# Погода: /weather
#
# Локация (координаты берутся из config/locations.json) -> дата -> время.
# Итог — одно сообщение с прогнозом, оно остаётся в чате.
# ---------------------------------------------------------------------------

W_LOCATION, W_DATE, W_TIME, W_MANUAL_DATE, W_MANUAL_TIME = range(30, 35)

WEATHER_CALLBACK_CANCEL = "weather:cancel"


def weather_locations_keyboard() -> InlineKeyboardMarkup:
    rows: list[list[InlineKeyboardButton]] = []
    for location in load_locations():
        title = location["name"]
        if location.get("time"):
            title = f"{title} ({location['time']})"
        rows.append(
            [InlineKeyboardButton(title[:60], callback_data=f"weather:loc:{location['id']}")]
        )
    rows.append([InlineKeyboardButton("❌ Отмена", callback_data=WEATHER_CALLBACK_CANCEL)])
    return InlineKeyboardMarkup(rows)


def weather_dates_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("Сегодня", callback_data="weather:date:0"),
                InlineKeyboardButton("Завтра", callback_data="weather:date:1"),
                InlineKeyboardButton("Послезавтра", callback_data="weather:date:2"),
            ],
            [InlineKeyboardButton("Ввести вручную", callback_data="weather:date:manual")],
            [InlineKeyboardButton("❌ Отмена", callback_data=WEATHER_CALLBACK_CANCEL)],
        ]
    )


def weather_times_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("09:00", callback_data="weather:time:09:00"),
                InlineKeyboardButton("12:00", callback_data="weather:time:12:00"),
                InlineKeyboardButton("15:00", callback_data="weather:time:15:00"),
            ],
            [
                InlineKeyboardButton("18:00", callback_data="weather:time:18:00"),
                InlineKeyboardButton("21:00", callback_data="weather:time:21:00"),
                InlineKeyboardButton("23:00", callback_data="weather:time:23:00"),
            ],
            [InlineKeyboardButton("Своё время", callback_data="weather:time:manual")],
            [InlineKeyboardButton("❌ Отмена", callback_data=WEATHER_CALLBACK_CANCEL)],
        ]
    )


def _weather_date_limits() -> tuple[date, date]:
    today = today_local()
    return today, today + timedelta(days=MAX_FORECAST_DAYS)


async def weather_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await ensure_group(update):
        return ConversationHandler.END
    remember_group_chat(update)
    _clear_flow(context)
    _reset_service_messages(context)

    locations = load_locations()
    if not locations:
        await reply_text(
            update,
            "⚠️ Локации не настроены: добавь их в config/locations.json.",
        )
        return ConversationHandler.END

    message = update.effective_message
    _track_message(context, getattr(message, "message_id", None))
    prompt = await reply_text(
        update,
        "🌤 <b>Погода</b>\n\nШаг 1/3 — выбери локацию:",
        reply_markup=weather_locations_keyboard(),
    )
    _track_message(context, getattr(prompt, "message_id", None))
    return W_LOCATION


async def weather_location_chosen(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if query is None:
        return ConversationHandler.END
    await query.answer()
    if not await _callback_group_ok(query):
        return ConversationHandler.END

    location_id = (query.data or "").split(":", 2)[-1]
    location = find_location(location_id)
    if location is None:
        await query.answer("Локация не найдена", show_alert=True)
        return ConversationHandler.END

    context.user_data["weather_location"] = location["id"]
    _track_message(context, getattr(query.message, "message_id", None))
    try:
        await query.edit_message_text(
            f"📍 Локация: <b>{html.escape(location['name'])}</b>",
            parse_mode=ParseMode.HTML,
        )
    except BadRequest as exc:
        logger.info("Не удалось отредактировать сообщение с локацией: %s", exc)

    prompt = await send_text(
        context.bot,
        query.message.chat_id,
        "📅 Шаг 2/3 — выбери дату:",
        reply_markup=weather_dates_keyboard(),
    )
    _track_message(context, getattr(prompt, "message_id", None))
    return W_DATE


async def weather_date_chosen(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if query is None:
        return ConversationHandler.END
    await query.answer()
    if not await _callback_group_ok(query):
        return ConversationHandler.END

    if "weather_location" not in context.user_data:
        await query.answer("Сессия устарела, запусти /weather заново", show_alert=True)
        return ConversationHandler.END

    value = (query.data or "").split(":", 2)[-1]
    _track_message(context, getattr(query.message, "message_id", None))

    if value == "manual":
        prompt = await send_text(
            context.bot,
            query.message.chat_id,
            "Введи дату в формате <b>ДД.ММ.ГГГГ</b> (например: 25.12.2026).\n"
            "Прервать: /cancel",
        )
        _track_message(context, getattr(prompt, "message_id", None))
        return W_MANUAL_DATE

    try:
        offset = int(value)
    except ValueError:
        await query.answer("Некорректная дата", show_alert=True)
        return W_DATE

    target = today_local() + timedelta(days=offset)
    context.user_data["weather_date"] = target.isoformat()
    prompt = await send_text(
        context.bot,
        query.message.chat_id,
        f"📅 Дата: <b>{target.strftime('%d.%m.%Y')}</b>\n\n"
        "🕐 Шаг 3/3 — выбери время:",
        reply_markup=weather_times_keyboard(),
    )
    _track_message(context, getattr(prompt, "message_id", None))
    return W_TIME


async def weather_manual_date(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message = update.effective_message
    raw = (message.text or "").strip() if message else ""
    _track_message(context, getattr(message, "message_id", None))
    try:
        target = datetime.strptime(raw, "%d.%m.%Y").date()
    except ValueError:
        prompt = await reply_text(
            update,
            "❌ Не получилось разобрать дату. Нужен формат ДД.ММ.ГГГГ, например 25.12.2026.\n"
            "Попробуй ещё раз или /cancel.",
        )
        _track_message(context, getattr(prompt, "message_id", None))
        return W_MANUAL_DATE

    first, last = _weather_date_limits()
    if target < first or target > last:
        prompt = await reply_text(
            update,
            f"❌ Прогноз доступен с {first.strftime('%d.%m.%Y')} "
            f"по {last.strftime('%d.%m.%Y')}. Введи другую дату или /cancel.",
        )
        _track_message(context, getattr(prompt, "message_id", None))
        return W_MANUAL_DATE

    context.user_data["weather_date"] = target.isoformat()
    prompt = await reply_text(
        update,
        f"📅 Дата: <b>{target.strftime('%d.%m.%Y')}</b>\n\n"
        "🕐 Шаг 3/3 — выбери время:",
        reply_markup=weather_times_keyboard(),
    )
    _track_message(context, getattr(prompt, "message_id", None))
    return W_TIME


async def weather_time_chosen(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if query is None:
        return ConversationHandler.END
    await query.answer()
    if not await _callback_group_ok(query):
        return ConversationHandler.END

    if "weather_location" not in context.user_data:
        await query.answer("Сессия устарела, запусти /weather заново", show_alert=True)
        return ConversationHandler.END
    if "weather_date" not in context.user_data:
        await query.answer("Сначала выбери дату, запусти /weather заново", show_alert=True)
        return ConversationHandler.END

    value = (query.data or "").split(":", 2)[-1]
    _track_message(context, getattr(query.message, "message_id", None))

    if value == "manual":
        prompt = await send_text(
            context.bot,
            query.message.chat_id,
            "Введи время в формате <b>ЧЧ:ММ</b> (например: 21:30).\n"
            "Прервать: /cancel",
        )
        _track_message(context, getattr(prompt, "message_id", None))
        return W_MANUAL_TIME

    parsed = parse_location_time(value)
    if parsed is None:
        await query.answer("Некорректное время", show_alert=True)
        return W_TIME

    context.user_data["weather_time"] = parsed.strftime("%H:%M")
    return await _finalize_weather(update, context, chat_id=query.message.chat_id)


async def weather_manual_time(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message = update.effective_message
    raw = (message.text or "").strip() if message else ""
    _track_message(context, getattr(message, "message_id", None))

    parsed = parse_location_time(raw)
    if parsed is None:
        prompt = await reply_text(
            update,
            "❌ Не понял время. Нужен формат ЧЧ:ММ, например 21:30.\n"
            "Попробуй ещё раз или /cancel.",
        )
        _track_message(context, getattr(prompt, "message_id", None))
        return W_MANUAL_TIME

    context.user_data["weather_time"] = parsed.strftime("%H:%M")
    return await _finalize_weather(update, context, chat_id=update.effective_chat.id)


async def _finalize_weather(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    chat_id: int | str,
):
    location = find_location(str(context.user_data.get("weather_location") or ""))
    if location is None:
        _clear_flow(context)
        await reply_text(update, "⚠️ Локация не найдена. Запусти /weather заново.")
        return ConversationHandler.END

    try:
        target_date = date.fromisoformat(str(context.user_data.get("weather_date") or ""))
    except ValueError:
        _clear_flow(context)
        await reply_text(update, "⚠️ Дата потерялась. Запусти /weather заново.")
        return ConversationHandler.END

    time_value = parse_location_time(str(context.user_data.get("weather_time") or ""))
    if time_value is None:
        _clear_flow(context)
        await reply_text(update, "⚠️ Не удалось определить время. Запусти /weather заново.")
        return ConversationHandler.END

    target_dt = datetime.combine(target_date, time_value).replace(tzinfo=settings.timezone)
    report = await asyncio.to_thread(build_weather_report, location, target_dt)
    await send_text(context.bot, chat_id, report)

    _clear_flow(context)
    # Итог (прогноз) остаётся в чате, служебная переписка удаляется.
    await delete_service_messages(context, chat_id)
    logger.info(
        "Погода по запросу: %s, %s %s",
        location["name"],
        target_date.isoformat(),
        target_dt.strftime("%H:%M"),
    )
    return ConversationHandler.END


async def weather_buttons_hint(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Подсказка, если в диалоге погоды пишут текст вместо нажатия кнопки."""
    _track_incoming(update, context)
    prompt = await reply_text(
        update,
        "Пожалуйста, выбери вариант кнопкой ниже или прерви диалог командой /cancel.",
    )
    _track_message(context, getattr(prompt, "message_id", None))
    if "weather_location" not in context.user_data:
        return W_LOCATION
    if "weather_date" not in context.user_data:
        return W_DATE
    return W_TIME


async def callback_cancel_weather_flow(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if query is None:
        return ConversationHandler.END
    await query.answer()
    chat_id = query.message.chat_id if query.message else None
    _clear_flow(context)
    try:
        await query.edit_message_text("❌ Выбор погоды отменён.")
    except BadRequest as exc:
        logger.info("Не удалось отредактировать сообщение при отмене: %s", exc)
    await delete_service_messages(context, chat_id)
    return ConversationHandler.END


# ---------------------------------------------------------------------------
# Личный кабинет владельца (только в личных сообщениях)
#
# В группе бот работает как раньше. Правка файлов (birthdays.json,
# locations.json, meetup.json) и папки config/photos доступна только владельцу
# в личке: его id задаётся переменной окружения ADMIN_USER_ID.
# ---------------------------------------------------------------------------

P_PANEL = 100
P_BD_NAME, P_BD_DAY, P_BD_MONTH = range(101, 104)
P_LOC_ID, P_LOC_NAME, P_LOC_TIME, P_LOC_ADDRESS = range(110, 114)
P_LOC_COORDS, P_LOC_LINK, P_LOC_NOTE, P_LOC_PHOTO = range(114, 118)
P_PHOTO_WAIT = 120
P_MT_DATE, P_MT_TIME = 121, 122

ADMIN_PREFIX = "adm:"


def is_admin_user(user) -> bool:
    """Владелец бота (ADMIN_USER_ID). Без него личка закрыта для всех."""
    if user is None or settings.admin_user_id is None:
        return False
    try:
        return int(getattr(user, "id", 0) or 0) == settings.admin_user_id
    except (TypeError, ValueError):
        return False


def _text_of(update: Update) -> str:
    message = update.effective_message
    return (message.text or "").strip() if message is not None else ""


def _clip(text: str, limit: int = 3800) -> str:
    return text if len(text) <= limit else f"{text[:limit - 20].rstrip()}\n…(сокращено)"


async def _admin_render(query, text: str, keyboard=None) -> None:
    """Обновляет сообщение панели на месте (без мусора в переписке)."""
    try:
        await query.edit_message_text(
            text=_clip(text), parse_mode=ParseMode.HTML, reply_markup=keyboard
        )
    except BadRequest as exc:
        logger.info("Админ-панель: сообщение не обновлено (%s)", exc)


def _back(callback: str, label: str = "⬅️ Назад") -> InlineKeyboardButton:
    return InlineKeyboardButton(label, callback_data=f"{ADMIN_PREFIX}{callback}")


def _meetup_status() -> str:
    current = load_meetup()
    if not isinstance(current, dict) or not current:
        return "не запланирована"
    return (
        f"{current.get('name') or '—'}, {current.get('date') or '—'} "
        f"{current.get('time') or ''}"
    ).strip()


def admin_panel_text() -> str:
    return "\n".join(
        [
            "🛠 <b>Админ-панель</b>",
            "",
            "Правки применяются к файлам бота сразу. В группе всё как обычно.",
            "",
            f"🎂 Дней рождения: {len(load_birthdays())}",
            f"📍 Локаций: {len(load_locations())}",
            f"🖼 Фото: {len(list_photo_files())}",
            f"📢 Сходка: {html.escape(_meetup_status())}",
        ]
    )


def admin_panel_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("🎂 Дни рождения", callback_data=f"{ADMIN_PREFIX}bd:menu")],
            [InlineKeyboardButton("📍 Локации", callback_data=f"{ADMIN_PREFIX}loc:menu")],
            [InlineKeyboardButton("🖼 Фото", callback_data=f"{ADMIN_PREFIX}ph:menu")],
            [InlineKeyboardButton("📢 Сходка", callback_data=f"{ADMIN_PREFIX}mt:menu")],
            [InlineKeyboardButton("🔄 Обновить", callback_data=f"{ADMIN_PREFIX}root")],
        ]
    )


def _bd_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("📋 Список", callback_data=f"{ADMIN_PREFIX}bd:list")],
            [InlineKeyboardButton("➕ Добавить", callback_data=f"{ADMIN_PREFIX}bd:add")],
            [InlineKeyboardButton("🗑 Удалить", callback_data=f"{ADMIN_PREFIX}bd:del")],
            [_back("root")],
        ]
    )


def _loc_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("📋 Список", callback_data=f"{ADMIN_PREFIX}loc:list")],
            [InlineKeyboardButton("➕ Добавить", callback_data=f"{ADMIN_PREFIX}loc:add")],
            [InlineKeyboardButton("🗑 Удалить", callback_data=f"{ADMIN_PREFIX}loc:del")],
            [
                InlineKeyboardButton(
                    "🖼 Привязать фото", callback_data=f"{ADMIN_PREFIX}loc:photo"
                )
            ],
            [_back("root")],
        ]
    )


def _photo_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("📋 Список", callback_data=f"{ADMIN_PREFIX}ph:list")],
            [InlineKeyboardButton("⬆️ Загрузить", callback_data=f"{ADMIN_PREFIX}ph:up")],
            [InlineKeyboardButton("🗑 Удалить", callback_data=f"{ADMIN_PREFIX}ph:del")],
            [_back("root")],
        ]
    )


def _meetup_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("📋 Показать", callback_data=f"{ADMIN_PREFIX}mt:show")],
            [
                InlineKeyboardButton(
                    "✏️ Изменить дату/время", callback_data=f"{ADMIN_PREFIX}mt:edit"
                )
            ],
            [InlineKeyboardButton("🧹 Очистить", callback_data=f"{ADMIN_PREFIX}mt:clear")],
            [_back("root")],
        ]
    )


def _locations_text() -> str:
    locations = load_locations()
    if not locations:
        return "📍 Локаций пока нет."
    lines = [f"📍 <b>Локации</b> · {len(locations)}", ""]
    for location in locations:
        lines.append(
            f"<b>{html.escape(location['name'])}</b> · "
            f"<code>{html.escape(location['id'])}</code>"
        )
        if location.get("time"):
            lines.append(f"🕐 {html.escape(location['time'])}")
        if location.get("address"):
            lines.append(f"🗺 {html.escape(location['address'])}")
        if location.get("coords"):
            lines.append(f"🧭 {html.escape(location['coords'])}")
        if location.get("link"):
            lines.append(f"🔗 {html.escape(location['link'])}")
        if location.get("note"):
            lines.append(f"📝 {html.escape(location['note'])}")
        lines.append(f"🖼 {html.escape(location.get('photo') or '—')}")
        lines.append("")
    return "\n".join(lines).rstrip()


def _photos_text() -> str:
    files = list_photo_files()
    if not files:
        return "🖼 Пока нет файлов ни в config/photos, ни в data/photos."
    lines = [f"🖼 <b>Фото</b> · {len(files)}", ""]
    for path in files:
        size_kb = path.stat().st_size / 1024
        used = photos_using(path.name)
        tail = f" · {', '.join(html.escape(name) for name in used)}" if used else " · не привязано"
        folder = "data" if path.parent == UPLOADED_PHOTOS_DIR else "config"
        lines.append(
            f"• <code>{html.escape(path.name)}</code> — {size_kb:.0f} КБ "
            f"[{folder}]{tail}"
        )
    return "\n".join(lines)


def _picker(items, prefix: str, label) -> list:
    """Список кнопок по индексам (индекс — безопаснее длинного id в callback)."""
    return [
        [
            InlineKeyboardButton(
                label(item, index)[:60], callback_data=f"{ADMIN_PREFIX}{prefix}{index}"
            )
        ]
        for index, item in enumerate(items[:40])
    ]


# --- вход в панель ---------------------------------------------------------


async def admin_panel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    for key in list(context.user_data):
        if key.startswith("adm_"):
            context.user_data.pop(key, None)
    message = update.effective_message
    if message is not None:
        await message.reply_text(
            admin_panel_text(),
            parse_mode=ParseMode.HTML,
            reply_markup=admin_panel_keyboard(),
        )
    return P_PANEL


async def admin_panel_hint(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message = update.effective_message
    if message is not None:
        await message.reply_text(
            "Выбери раздел кнопкой ниже. Обновить панель: /start",
            reply_markup=admin_panel_keyboard(),
        )
    return P_PANEL


async def admin_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    for key in list(context.user_data):
        if key.startswith("adm_"):
            context.user_data.pop(key, None)
    await admin_panel(update, context)
    return P_PANEL


# --- маршрутизация кнопок --------------------------------------------------


async def admin_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if query is None:
        return ConversationHandler.END
    chat = query.message.chat if query.message else None
    if chat is None or chat.type != ChatType.PRIVATE:
        await query.answer("Панель доступна только в личных сообщениях", show_alert=True)
        return ConversationHandler.END
    if not is_admin_user(query.from_user):
        await query.answer("Доступ только для владельца бота", show_alert=True)
        return ConversationHandler.END
    await query.answer()

    parts = (query.data or "").split(":")
    section = parts[1] if len(parts) > 1 else "root"
    action = parts[2] if len(parts) > 2 else "menu"
    arg = parts[3] if len(parts) > 3 else ""

    if section == "root":
        await _admin_render(query, admin_panel_text(), admin_panel_keyboard())
        return P_PANEL
    if section == "bd":
        return await _admin_birthdays(query, context, action, arg)
    if section == "loc":
        return await _admin_locations(query, context, action, arg)
    if section == "ph":
        return await _admin_photos(query, context, action, arg)
    if section == "mt":
        return await _admin_meetup(query, context, action, arg)
    await _admin_render(query, admin_panel_text(), admin_panel_keyboard())
    return P_PANEL


# --- дни рождения ----------------------------------------------------------


async def _admin_birthdays(query, context, action: str, arg: str):
    if action == "list":
        await _admin_render(query, format_birthdays(load_birthdays()), _bd_keyboard())
        return P_PANEL

    if action == "add":
        context.user_data["adm_bd"] = {}
        await _admin_render(
            query,
            "➕ <b>Новый день рождения</b>\n\n"
            "Шаг 1/3 — имя и username через пробел "
            "(например <code>Никита Nekit_098</code>).\n\n/cancel — отменить",
            None,
        )
        return P_BD_NAME

    if action == "del":
        items = load_birthdays()
        if not items:
            await _admin_render(query, "Список пуст — удалять нечего.", _bd_keyboard())
            return P_PANEL
        context.user_data["adm_bd_del"] = [item["id"] for item in items]
        rows = _picker(
            items, "bd:delok:", lambda item, index: f"{item['day']:02d}.{item['month']:02d} — {item['name']}"
        )
        rows.append([_back("bd:menu")])
        await _admin_render(query, "🗑 Выбери запись для удаления:", InlineKeyboardMarkup(rows))
        return P_PANEL

    if action == "delok":
        removed = None
        ids = context.user_data.get("adm_bd_del") or []
        try:
            index = int(arg)
        except ValueError:
            index = -1
        if 0 <= index < len(ids):
            removed = delete_birthday_by_id(ids[index])
        if removed is None:
            await _admin_render(query, "⚠️ Запись не найдена. Открой список заново.", _bd_keyboard())
            return P_PANEL
        await _admin_render(
            query,
            f"✅ Удалено: <b>{html.escape(removed['name'])}</b> "
            f"({removed['day']:02d}.{removed['month']:02d})",
            _bd_keyboard(),
        )
        return P_PANEL

    await _admin_render(query, "🎂 <b>Дни рождения</b>\n\nЧто сделать?", _bd_keyboard())
    return P_PANEL


async def admin_bd_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw = _text_of(update)
    if not raw:
        await reply_text(update, "Имя не может быть пустым. Напиши имя или /cancel.")
        return P_BD_NAME
    if len(raw) > 64:
        await reply_text(update, "Слишком длинное имя (максимум 64 символа).")
        return P_BD_NAME
    context.user_data["adm_bd"] = {"name": raw}
    await reply_text(update, f"Шаг 2/3 — день (1–31) для <b>{html.escape(raw)}</b>.")
    return P_BD_DAY


async def admin_bd_day(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw = _text_of(update)
    try:
        day = int(raw)
    except ValueError:
        await reply_text(update, "Нужно число от 1 до 31.")
        return P_BD_DAY
    if not 1 <= day <= 31:
        await reply_text(update, "День должен быть от 1 до 31.")
        return P_BD_DAY
    context.user_data.setdefault("adm_bd", {})["day"] = day
    await reply_text(update, "Шаг 3/3 — месяц (1–12).")
    return P_BD_MONTH


async def admin_bd_month(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw = _text_of(update)
    try:
        month = int(raw)
    except ValueError:
        await reply_text(update, "Нужно число от 1 до 12.")
        return P_BD_MONTH
    if not 1 <= month <= 12:
        await reply_text(update, "Месяц должен быть от 1 до 12.")
        return P_BD_MONTH

    data = context.user_data.get("adm_bd") or {}
    name = str(data.get("name") or "")
    day = int(data.get("day") or 0)
    if not name or not day:
        await reply_text(update, "⚠️ Диалог сбился, начни заново: /start")
        return P_PANEL
    if day > _max_day(month):
        await reply_text(
            update,
            f"В {MONTHS_GENITIVE[month - 1]} нет {day}-го числа. Введи месяц ещё раз (1–12).",
        )
        return P_BD_MONTH

    record = add_birthday(name, day, month)
    context.user_data.pop("adm_bd", None)
    await reply_text(
        update,
        f"✅ Записано: <b>{html.escape(record['name'])}</b> — {record['day']:02d} "
        f"{MONTHS_GENITIVE[record['month'] - 1]}",
        reply_markup=_bd_keyboard(),
    )
    return P_PANEL


# --- локации ---------------------------------------------------------------

LOC_FIELDS = ("id", "name", "time", "address", "coords", "link", "note", "photo")
LOC_STATES = {
    "id": P_LOC_ID,
    "name": P_LOC_NAME,
    "time": P_LOC_TIME,
    "address": P_LOC_ADDRESS,
    "coords": P_LOC_COORDS,
    "link": P_LOC_LINK,
    "note": P_LOC_NOTE,
    "photo": P_LOC_PHOTO,
}
LOC_PROMPTS = {
    "id": "Шаг 1/8 — id локации: латиница, цифры, «_», «-» (например <code>vegas</code>).",
    "name": "Шаг 2/8 — название локации (попадёт в анонс).",
    "time": "Шаг 3/8 — время сбора «ЧЧ:ММ» (например <code>21:00</code>) или «-».",
    "address": "Шаг 4/8 — адрес или «-».",
    "coords": "Шаг 5/8 — координаты «широта, долгота» (например <code>55.585639, 37.722646</code>) или «-».",
    "link": "Шаг 6/8 — ссылка на карту или «-».",
    "note": "Шаг 7/8 — примечание, где собираемся, или «-».",
    "photo": "Шаг 8/8 — имя фото из config/photos (например <code>vegas</code>) или «-».",
}


async def _admin_locations(query, context, action: str, arg: str):
    if action == "list":
        await _admin_render(query, _locations_text(), _loc_keyboard())
        return P_PANEL

    if action == "add":
        context.user_data["adm_loc"] = {}
        context.user_data["adm_loc_field"] = "id"
        await _admin_render(
            query, f"➕ <b>Новая локация</b>\n\n{LOC_PROMPTS['id']}\n\n/cancel — отменить", None
        )
        return P_LOC_ID

    if action == "del":
        locations = load_locations()
        if not locations:
            await _admin_render(query, "📍 Локаций нет — удалять нечего.", _loc_keyboard())
            return P_PANEL
        context.user_data["adm_loc_del"] = [item["id"] for item in locations]
        rows = _picker(
            locations, "loc:delok:", lambda item, index: f"{item['name']} ({item['id']})"
        )
        rows.append([_back("loc:menu")])
        await _admin_render(query, "🗑 Какую локацию удалить?", InlineKeyboardMarkup(rows))
        return P_PANEL

    if action == "delok":
        ids = context.user_data.get("adm_loc_del") or []
        try:
            index = int(arg)
        except ValueError:
            index = -1
        removed = delete_location_by_id(ids[index]) if 0 <= index < len(ids) else None
        if removed is None:
            await _admin_render(query, "⚠️ Локация не найдена.", _loc_keyboard())
            return P_PANEL
        await _admin_render(
            query, f"✅ Удалена локация: <b>{html.escape(removed['name'])}</b>", _loc_keyboard()
        )
        return P_PANEL

    if action == "photo":
        locations = load_locations()
        if not locations:
            await _admin_render(query, "📍 Сначала добавь локацию.", _loc_keyboard())
            return P_PANEL
        context.user_data["adm_loc_del"] = [item["id"] for item in locations]
        rows = _picker(locations, "loc:photoloc:", lambda item, index: item["name"])
        rows.append([_back("loc:menu")])
        await _admin_render(query, "🖼 К какой локации привязать фото?", InlineKeyboardMarkup(rows))
        return P_PANEL

    if action == "photoloc":
        photos = list_photo_files()
        if not photos:
            await _admin_render(
                query, "🖼 В config/photos нет файлов — сначала загрузи фото.", _loc_keyboard()
            )
            return P_PANEL
        ids = context.user_data.get("adm_loc_del") or []
        try:
            index = int(arg)
        except ValueError:
            index = -1
        if not 0 <= index < len(ids):
            await _admin_render(query, "⚠️ Локация не найдена.", _loc_keyboard())
            return P_PANEL
        context.user_data["adm_photo_pick"] = [p.name for p in photos]
        rows = _picker(photos, f"loc:setphoto:{index}:", lambda p, i: p.name)
        rows.append([_back("loc:menu")])
        await _admin_render(query, "🖼 Выбери файл:", InlineKeyboardMarkup(rows))
        return P_PANEL

    if action == "setphoto":
        ids = context.user_data.get("adm_loc_del") or []
        names = context.user_data.get("adm_photo_pick") or []
        sub = (query.data or "").split(":")
        # adm:loc:setphoto:<locIndex>:<photoIndex>
        try:
            loc_index = int(sub[3])
            photo_index = int(sub[4])
        except (IndexError, ValueError):
            loc_index = photo_index = -1
        location = find_location(ids[loc_index]) if 0 <= loc_index < len(ids) else None
        if location is None or not 0 <= photo_index < len(names):
            await _admin_render(query, "⚠️ Не удалось применить фото.", _loc_keyboard())
            return P_PANEL
        reference = photo_reference_from_name(names[photo_index])
        if not reference:
            await _admin_render(query, "⚠️ Файл не найден.", _loc_keyboard())
            return P_PANEL
        location["photo"] = reference
        upsert_location(location)
        await _admin_render(
            query,
            f"✅ Локация <b>{html.escape(location['name'])}</b> теперь с фото "
            f"<code>{html.escape(reference)}</code>",
            _loc_keyboard(),
        )
        return P_PANEL

    if action == "cancel":
        await _admin_render(query, admin_panel_text(), admin_panel_keyboard())
        return P_PANEL

    await _admin_render(query, "📍 <b>Локации</b>\n\nЧто сделать?", _loc_keyboard())
    return P_PANEL


async def admin_loc_field(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Один шаг мастера локации: какое поле — задаёт adm_loc_field."""
    field = str(context.user_data.get("adm_loc_field") or "")
    if field not in LOC_FIELDS:
        await reply_text(update, "⚠️ Мастер сбился, открой панель заново: /start")
        return P_PANEL

    raw = _text_of(update)
    skipped = raw in ("", "-", "—", "нет")

    if field == "id":
        loc_id = re.sub(r"\s+", "_", raw)
        if not re.fullmatch(r"[\w\-]{1,32}", loc_id or ""):
            await reply_text(update, "ID: латиница, цифры, «_» и «-» (до 32 символов). Ещё раз.")
            return LOC_STATES[field]
        if find_location(loc_id) is not None:
            await reply_text(update, f"Локация с id «{html.escape(loc_id)}» уже есть. Другой id.")
            return LOC_STATES[field]
        value = loc_id
    elif field == "name":
        if not raw:
            await reply_text(update, "Название не может быть пустым. Ещё раз.")
            return LOC_STATES[field]
        value = raw[:80]
    elif field == "time":
        if skipped:
            value = ""
        else:
            parsed = parse_location_time(raw)
            if parsed is None:
                await reply_text(update, "Время в формате ЧЧ:ММ, например 21:00. Или «-».")
                return LOC_STATES[field]
            value = parsed.strftime("%H:%M")
    elif field == "coords":
        if skipped:
            value = ""
        else:
            coords = parse_coords(raw)
            if coords is None:
                await reply_text(
                    update, "Координаты «широта, долгота», например 55.585639, 37.722646. Или «-»."
                )
                return LOC_STATES[field]
            value = f"{coords[0]:.6f}, {coords[1]:.6f}"
    elif field == "photo":
        if skipped:
            value = ""
        else:
            reference = photo_reference_from_name(raw)
            if not reference:
                listing = ", ".join(p.name for p in list_photo_files()[:10]) or "папка пуста"
                await reply_text(
                    update,
                    f"Файл «{html.escape(raw)}» не найден в config/photos.\n"
                    f"Есть: {html.escape(listing)}\n\n"
                    "Напиши имя файла ещё раз, отправь «-» или /cancel.",
                )
                return LOC_STATES[field]
            value = reference
    else:
        value = "" if skipped else raw[:200]

    data = context.user_data.setdefault("adm_loc", {})
    data[field] = value

    next_index = LOC_FIELDS.index(field) + 1
    if next_index >= len(LOC_FIELDS):
        record = {
            "id": data.get("id", ""),
            "name": data.get("name", ""),
            "time": data.get("time", ""),
            "address": data.get("address", ""),
            "coords": data.get("coords", ""),
            "link": data.get("link", ""),
            "note": data.get("note", ""),
            "photo": data.get("photo", ""),
        }
        upsert_location(record)
        context.user_data.pop("adm_loc", None)
        context.user_data.pop("adm_loc_field", None)
        await reply_text(
            update,
            f"✅ Локация сохранена: <b>{html.escape(record['name'])}</b> "
            f"(<code>{html.escape(record['id'])}</code>)",
            reply_markup=_loc_keyboard(),
        )
        return P_PANEL

    next_field = LOC_FIELDS[next_index]
    context.user_data["adm_loc_field"] = next_field
    await reply_text(update, LOC_PROMPTS[next_field])
    return LOC_STATES[next_field]


# --- фото ------------------------------------------------------------------


def _used_marker(file_name: str) -> str:
    used = photos_using(file_name)
    return f"привязано к: {', '.join(used)}" if used else "не привязано"


async def _admin_photos(query, context, action: str, arg: str):
    if action == "list":
        await _admin_render(query, _photos_text(), _photo_keyboard())
        return P_PANEL

    if action == "up":
        context.user_data.pop("adm_photo_name", None)
        await _admin_render(
            query,
            "⬆️ <b>Загрузка фото</b>\n\n"
            "Отправь фото (или файл-картинку).\n\n"
            "Имя файла можно задать двумя способами:\n"
            "• подписью к фото — она станет именем;\n"
            "• сначала напиши имя, потом отправь фото.\n\n"
            "Именно это имя потом указывается у локации.\n\n/cancel — отменить",
            InlineKeyboardMarkup([[_back("ph:menu")]]),
        )
        return P_PHOTO_WAIT

    if action == "del":
        files = list_photo_files()
        if not files:
            await _admin_render(query, "🖼 Файлов нет — удалять нечего.", _photo_keyboard())
            return P_PANEL
        context.user_data["adm_photo_pick"] = [p.name for p in files]
        rows = _picker(files, "ph:delok:", lambda p, i: p.name)
        rows.append([_back("ph:menu")])
        await _admin_render(query, "🗑 Какой файл удалить?", InlineKeyboardMarkup(rows))
        return P_PANEL

    if action == "delok":
        names = context.user_data.get("adm_photo_pick") or []
        try:
            index = int(arg)
        except ValueError:
            index = -1
        if not 0 <= index < len(names):
            await _admin_render(query, "⚠️ Файл не найден.", _photo_keyboard())
            return P_PANEL
        target = find_photo_file(names[index])
        if target is None:
            await _admin_render(query, "⚠️ Файл уже удалён.", _photo_keyboard())
            return P_PANEL
        try:
            target.unlink()
        except OSError as exc:
            await _admin_render(
                query, f"⚠️ Не удалось удалить: {html.escape(str(exc))}", _photo_keyboard()
            )
            return P_PANEL
        await _admin_render(query, f"✅ Удалён файл <code>{html.escape(names[index])}</code>", _photo_keyboard())
        return P_PANEL

    await _admin_render(query, "🖼 <b>Фото</b>\n\nЧто сделать?", _photo_keyboard())
    return P_PANEL


async def admin_photo_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Фото или имя для него в режиме загрузки."""
    message = update.effective_message
    if message is None:
        return P_PHOTO_WAIT

    has_photo = bool(message.photo) or (
        message.document is not None
        and (
            (message.document.mime_type or "").lower().startswith("image/")
            or Path(message.document.file_name or "").suffix.lower() in PHOTO_EXTENSIONS
        )
    )

    if not has_photo:
        name = safe_photo_name(_text_of(update))
        if not name:
            await reply_text(
                update, "Напиши имя файла (буквы, цифры, «_», «-») или отправь фото с подписью."
            )
            return P_PHOTO_WAIT
        context.user_data["adm_photo_name"] = name
        await reply_text(
            update,
            f"Имя: <code>{html.escape(name)}</code>. Теперь отправь фото "
            f"(или напиши другое имя).",
        )
        return P_PHOTO_WAIT

    caption = safe_photo_name(message.caption or "")
    name = caption or str(context.user_data.get("adm_photo_name") or "")
    if not name:
        context.user_data["adm_photo_name"] = ""
        await reply_text(
            update,
            "🖼 Фото получено, но имени нет.\n"
            "Напиши имя файла (например <code>vegas</code>) — сохраню с ним, "
            "или отправь фото с подписью.",
        )
        return P_PHOTO_WAIT

    saved = await _save_uploaded_photo(update, context, name)
    if saved is None:
        await reply_text(update, "⚠️ Не удалось сохранить файл. Попробуй ещё раз или /cancel.")
        return P_PHOTO_WAIT

    context.user_data.pop("adm_photo_name", None)
    file_name = Path(saved).name
    await reply_text(
        update,
        f"✅ Фото сохранено: <code>{html.escape(saved)}</code>\n"
        f"Имя для локации: <code>{html.escape(file_name)}</code>\n\n"
        "Привязать к локации: 📍 Локации → 🖼 Привязать фото",
        reply_markup=_photo_keyboard(),
    )
    return P_PANEL


async def _save_uploaded_photo(
    update: Update, context: ContextTypes.DEFAULT_TYPE, name: str
) -> str | None:
    message = update.effective_message
    if message is None:
        return None
    file = None
    suffix = ".jpg"
    try:
        if message.photo:
            file = await message.photo[-1].get_file()
        elif message.document is not None:
            file = await message.document.get_file()
            candidate = Path(message.document.file_name or "").suffix.lower()
            if candidate in PHOTO_EXTENSIONS:
                suffix = candidate
        if file is None:
            return None
        safe = safe_photo_name(name)
        if not safe:
            return None
        # Новые фото — в data/photos: переживают деплой из Git.
        UPLOADED_PHOTOS_DIR.mkdir(parents=True, exist_ok=True)
        target = UPLOADED_PHOTOS_DIR / f"{safe}{suffix}"
        await file.download_to_drive(custom_path=str(target))
    except (TelegramError, OSError) as exc:
        logger.error("Не удалось сохранить фото %r: %s", name, exc)
        return None
    logger.info("Фото сохранено: %s", target)
    return photo_reference(target)


# --- сходка ----------------------------------------------------------------


async def _admin_meetup(query, context, action: str, arg: str):
    if action == "show":
        current = load_meetup()
        body = (
            json.dumps(current, ensure_ascii=False, indent=2)
            if isinstance(current, dict) and current
            else "Сходка не запланирована."
        )
        await _admin_render(query, f"📢 <b>meetup.json</b>\n\n<pre>{html.escape(body)}</pre>", _meetup_keyboard())
        return P_PANEL

    if action == "edit":
        current = load_meetup()
        if not isinstance(current, dict) or not current:
            await _admin_render(
                query,
                "📢 Активной сходки нет — сначала опубликуй её командой /meetup в группе.",
                _meetup_keyboard(),
            )
            return P_PANEL
        context.user_data["adm_mt"] = {}
        await _admin_render(
            query,
            "✏️ <b>Изменение сходки</b>\n\nНовая дата в формате <b>ДД.ММ.ГГГГ</b>.\n\n"
            "/cancel — отменить",
            None,
        )
        return P_MT_DATE

    if action == "clear":
        current = load_meetup()
        if not isinstance(current, dict) or not current:
            await _admin_render(query, "📢 Активной сходки нет.", _meetup_keyboard())
            return P_PANEL
        keyboard = InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton(
                        "✅ Да, очистить", callback_data=f"{ADMIN_PREFIX}mt:clearyes"
                    )
                ],
                [_back("mt:menu")],
            ]
        )
        await _admin_render(
            query,
            "🧹 Очистить файл meetup.json?\n\n"
            "Это только состояние бота: анонс, опрос и напоминание в группе "
            "сами не удалятся — для этого /cancel_meetup.",
            keyboard,
        )
        return P_PANEL

    if action == "clearyes":
        clear_meetup()
        await _admin_render(query, "✅ meetup.json очищен.", _meetup_keyboard())
        return P_PANEL

    await _admin_render(query, "📢 <b>Сходка</b>\n\nЧто сделать?", _meetup_keyboard())
    return P_PANEL


async def admin_mt_date(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw = _text_of(update)
    try:
        target = datetime.strptime(raw, "%d.%m.%Y").date()
    except ValueError:
        await reply_text(update, "❌ Формат ДД.ММ.ГГГГ, например 25.12.2026. Или /cancel.")
        return P_MT_DATE
    context.user_data["adm_mt"] = {"date": target}
    await reply_text(
        update,
        f"📅 Дата: <b>{target.strftime('%d.%m.%Y')}</b>\n\nВремя в формате <b>ЧЧ:ММ</b>.",
    )
    return P_MT_TIME


async def admin_mt_time(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw = _text_of(update)
    parsed = parse_location_time(raw)
    if parsed is None:
        await reply_text(update, "❌ Формат ЧЧ:ММ, например 21:30. Или /cancel.")
        return P_MT_TIME

    data = context.user_data.get("adm_mt") or {}
    target = data.get("date")
    if not isinstance(target, date):
        await reply_text(update, "⚠️ Дата потерялась, открой панель заново: /start")
        return P_PANEL

    current = load_meetup()
    if not isinstance(current, dict) or not current:
        await reply_text(update, "⚠️ meetup.json пуст — открыть панель: /start")
        return P_PANEL

    meetup_dt = datetime.combine(target, parsed).replace(tzinfo=settings.timezone)
    if meetup_dt <= now_local():
        await reply_text(update, "⏳ Это время уже прошло. Введи время ещё раз или /cancel.")
        return P_MT_TIME

    payload = dict(current)
    payload.update(
        {
            "date": target.isoformat(),
            "time": parsed.strftime("%H:%M"),
            "meetup_at": meetup_dt.isoformat(),
            "reminder_at": (meetup_dt - timedelta(hours=2)).isoformat(),
        }
    )
    save_meetup(payload)
    context.user_data.pop("adm_mt", None)
    info = reschedule_meetup_jobs(context, payload, meetup_dt)
    await reply_text(
        update,
        f"✅ Сходка обновлена: <b>{target.strftime('%d.%m.%Y')} "
        f"{parsed.strftime('%H:%M')}</b>\n{info}",
        reply_markup=_meetup_keyboard(),
    )
    return P_PANEL


def reschedule_meetup_jobs(
    context: ContextTypes.DEFAULT_TYPE, payload: dict, meetup_dt: datetime
) -> str:
    """Пересоздаёт закрытие опроса и напоминание после правки даты/времени."""
    job_queue = context.job_queue
    if job_queue is None:
        return "⚠️ JobQueue недоступен — задачи в группе не пересозданы."
    chat_id = payload.get("chat_id")
    for job in list(job_queue.get_jobs_by_name(JOB_MEETUP_REMINDER)):
        job.schedule_removal()
    for job in list(job_queue.get_jobs_by_name(JOB_MEETUP_POLL_CLOSE)):
        job.schedule_removal()

    notes: list[str] = []
    poll_message_id = payload.get("poll_message_id")
    if poll_message_id is not None:
        job_queue.run_once(
            meetup_poll_close_job,
            when=meetup_dt,
            name=JOB_MEETUP_POLL_CLOSE,
            chat_id=chat_id,
            data={"chat_id": chat_id, "poll_message_id": poll_message_id},
        )
        notes.append(f"опрос закроется в {meetup_dt.strftime('%d.%m %H:%M')}")

    reminder_at = meetup_dt - timedelta(hours=2)
    if reminder_at > now_local():
        job_queue.run_once(
            meetup_reminder_job,
            when=reminder_at,
            name=JOB_MEETUP_REMINDER,
            chat_id=chat_id,
            data={
                "name": payload.get("name", ""),
                "time": payload.get("time", ""),
                "chat_id": chat_id,
            },
        )
        notes.append(f"напоминание в {reminder_at.strftime('%d.%m %H:%M')}")
    else:
        notes.append("напоминание не нужно — до сходки меньше двух часов")
    return "🔔 " + ", ".join(notes)


# --- сборка диалога --------------------------------------------------------


def build_admin_conversation() -> ConversationHandler:
    private = filters.ChatType.PRIVATE
    states: dict[int, list] = {
        P_PANEL: [
            CallbackQueryHandler(admin_callback, pattern=r"^adm:"),
            MessageHandler(filters.PHOTO | filters.Document.IMAGE, admin_photo_input),
            MessageHandler(filters.TEXT & ~filters.COMMAND, admin_panel_hint),
        ],
        P_BD_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND, admin_bd_name)],
        P_BD_DAY: [MessageHandler(filters.TEXT & ~filters.COMMAND, admin_bd_day)],
        P_BD_MONTH: [MessageHandler(filters.TEXT & ~filters.COMMAND, admin_bd_month)],
        P_PHOTO_WAIT: [
            CallbackQueryHandler(admin_callback, pattern=r"^adm:"),
            MessageHandler(filters.PHOTO | filters.Document.IMAGE, admin_photo_input),
            MessageHandler(filters.TEXT & ~filters.COMMAND, admin_photo_input),
        ],
        P_MT_DATE: [MessageHandler(filters.TEXT & ~filters.COMMAND, admin_mt_date)],
        P_MT_TIME: [MessageHandler(filters.TEXT & ~filters.COMMAND, admin_mt_time)],
    }
    for state in LOC_STATES.values():
        states[state] = [
            CallbackQueryHandler(admin_callback, pattern=r"^adm:"),
            MessageHandler(filters.TEXT & ~filters.COMMAND, admin_loc_field),
        ]
    return ConversationHandler(
        entry_points=[
            CommandHandler("start", admin_panel, filters=private),
            CommandHandler("admin", admin_panel, filters=private),
            CallbackQueryHandler(admin_callback, pattern=r"^adm:"),
        ],
        states=states,
        fallbacks=[
            CommandHandler("cancel", admin_cancel),
            CommandHandler("start", admin_panel, filters=private),
        ],
        allow_reentry=True,
        conversation_timeout=900,
        name="admin_conv",
    )


# ---------------------------------------------------------------------------
# Ежедневные задачи
# ---------------------------------------------------------------------------


async def daily_birthdays_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = target_chat_id(context)
    if chat_id is None:
        return
    today = today_local()
    people = birthdays_on(today)
    if not people:
        logger.info("ДР на %s: нет", today.isoformat())
        return
    names = ", ".join(item["name"] for item in people)
    text = f"🎉 Сегодня день рождения у: {names}! Поздравляем 🥳"
    await _send_birthdays(context, chat_id, text, names, attempt=1)


async def _send_birthdays(
    context: ContextTypes.DEFAULT_TYPE, chat_id, text: str, names: str, attempt: int
) -> None:
    try:
        await context.bot.send_message(chat_id=chat_id, text=text)
    except TelegramError as exc:
        if not _is_network_failure(exc) or attempt >= MAX_BIRTHDAY_RETRIES:
            logger.error("Не удалось отправить поздравления: %s", exc)
            return
        delay = min(300, 60 * attempt)
        logger.warning(
            "Поздравления не ушли (попытка %s из %s): %s. Повтор через %s с",
            attempt, MAX_BIRTHDAY_RETRIES, exc, delay,
        )
        if context.job_queue is not None:
            context.job_queue.run_once(
                _birthdays_retry_job,
                when=delay,
                name=JOB_BIRTHDAYS_RETRY,
                data={
                    "chat_id": chat_id,
                    "text": text,
                    "names": names,
                    "attempt": attempt + 1,
                },
            )
        return
    logger.info("ДР отправлены: %s", names)


async def _birthdays_retry_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    data = context.job.data if context.job is not None else None
    if not isinstance(data, dict):
        return
    await _send_birthdays(
        context,
        data.get("chat_id"),
        data.get("text"),
        data.get("names"),
        attempt=int(data.get("attempt", 2)),
    )


async def restore_meetup_reminder(application: Application) -> None:
    """После рестарта восстанавливает напоминание о будущей сходке."""
    current = load_meetup()
    if not isinstance(current, dict) or not current:
        return
    try:
        meetup_dt = datetime.fromisoformat(str(current.get("meetup_at")))
    except (TypeError, ValueError):
        clear_meetup()
        return
    if meetup_dt.tzinfo is None:
        meetup_dt = meetup_dt.replace(tzinfo=settings.timezone)
    now = now_local()
    if meetup_dt <= now:
        logger.info("Сходка в прошлом — состояние очищено")
        clear_meetup()
        return

    chat_id = current.get("chat_id") or target_chat_id(None)  # type: ignore[arg-type]

    # Опрос закрываем в момент сходки — независимо от напоминания.
    poll_message_id = current.get("poll_message_id")
    if poll_message_id is not None and application.job_queue is not None:
        application.job_queue.run_once(
            meetup_poll_close_job,
            when=meetup_dt,
            name=JOB_MEETUP_POLL_CLOSE,
            chat_id=chat_id,
            data={"chat_id": chat_id, "poll_message_id": poll_message_id},
        )
        logger.info("Закрытие опроса восстановлено на %s", meetup_dt.isoformat())

    reminder_at = meetup_dt - timedelta(hours=2)
    if reminder_at <= now:
        logger.info("До сходки меньше двух часов — напоминание не восстанавливаю")
        return

    application.job_queue.run_once(
        meetup_reminder_job,
        when=reminder_at,
        name=JOB_MEETUP_REMINDER,
        chat_id=chat_id,
        data={
            "name": current.get("name", ""),
            "time": current.get("time", ""),
            "chat_id": chat_id,
        },
    )
    logger.info("Напоминание восстановлено на %s", reminder_at.isoformat())


# ---------------------------------------------------------------------------
# Состояние связи с Telegram
#
# Пока связь есть — сторож молчит и запросов не делает. Как только polling
# сообщает о сетевой ошибке, включается проверка: раз в 15 секунд сторож
# дёргает get_me, пока не получится, и пишет, что связь вернулась.
# ---------------------------------------------------------------------------

_net_down_since: datetime | None = None
_net_errors = 0


def _is_network_failure(exc: BaseException) -> bool:
    """True только для настоящих сетевых сбоев (обрыв, таймаут, DNS).

    В PTB 22 BadRequest наследуется от NetworkError, поэтому одной проверки
    isinstance(exc, NetworkError) мало: «chat not found» или битая разметка
    сетевым сбоем не являются, и повторять их бессмысленно.
    """
    return isinstance(exc, NetworkError) and not isinstance(
        exc, (BadRequest, Conflict, RetryAfter)
    )


def _mark_net_down(error: BaseException) -> None:
    """Фиксирует потерю связи: пишет в лог один раз, дальше — редко."""
    global _net_down_since, _net_errors
    _net_errors += 1
    if _net_down_since is None:
        _net_down_since = now_local()
        logger.warning(
            "❌ Связь с Telegram потеряна в %s: %s",
            _net_down_since.strftime("%H:%M:%S"),
            error,
        )
    elif _net_errors % 20 == 0:
        logger.warning(
            "❌ Связи всё ещё нет: %s с, ошибок %s: %s",
            int((now_local() - _net_down_since).total_seconds()),
            _net_errors,
            error,
        )


def _mark_net_up() -> None:
    """Пишет, что связь восстановилась, и сбрасывает состояние."""
    global _net_down_since, _net_errors
    if _net_down_since is None:
        return
    down_for = int((now_local() - _net_down_since).total_seconds())
    logger.info("✅ Связь с Telegram восстановлена (простой %s с)", down_for)
    _net_down_since = None
    _net_errors = 0


async def net_watchdog_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Проверяет связь, только когда она уже помечена как потерянная."""
    if _net_down_since is None:
        return
    try:
        await context.bot.get_me()
    except TelegramError:
        return  # всё ещё нет — сообщение уже было
    _mark_net_up()


async def _log_next_runs_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Логирует ближайшие запуски задач.

    Вызывается одноразовой задачей, т.е. уже после того, как JobQueue стартовал
    в Application.start(). Раньше это делалось прямо из post_init и всегда
    печатало None: до старта планировщика у задачи нет next_run_time.
    """
    job_queue = context.job_queue
    if job_queue is None:
        return
    try:
        pending = job_queue.jobs
        pending = pending() if callable(pending) else list(pending)
    except Exception:  # pragma: no cover - защита от смены API
        return
    for job in pending:
        if job.name in (JOB_LOG_NEXT_RUNS, JOB_NET_WATCHDOG):
            continue
        next_run = getattr(job, "next_t", None) or getattr(job, "next_run_time", None)
        logger.info("Задача %r, следующий запуск: %s", job.name, next_run)


async def post_init(application: Application) -> None:
    time_of_day = settings.time_of_day()
    application.job_queue.run_daily(
        daily_birthdays_job,
        time=time_of_day,
        name=JOB_BIRTHDAYS,
    )
    logger.info(
        "Ежедневные задачи запланированы на %02d:%02d (%s)",
        settings.daily_hour,
        settings.daily_minute,
        settings.timezone_name,
    )
    # Планировщик стартует позже (в Application.start()), поэтому логируем
    # расписание из задачи, а не прямо здесь.
    application.job_queue.run_once(
        _log_next_runs_job, when=5, name=JOB_LOG_NEXT_RUNS
    )

    application.job_queue.run_repeating(
        net_watchdog_job, interval=15, first=15, name=JOB_NET_WATCHDOG
    )

    await restore_meetup_reminder(application)

    commands = [
        BotCommand("help", "Список команд"),
        BotCommand("birthdays", "Дни рождения"),
        BotCommand("add_birthday", "Добавить день рождения (админ)"),
        BotCommand("del_birthday", "Удалить день рождения (админ)"),
        BotCommand("meetup", "Создать сходку"),
        BotCommand("cancel_meetup", "Отменить сходку"),
        BotCommand("weather", "Погода на локации"),
    ]
    try:
        await application.bot.set_my_commands(commands)
    except TelegramError as exc:
        logger.warning("Не удалось обновить список команд: %s", exc)


async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    error = context.error

    # Сетевые сбои приходят из polling'а, а не из обработчиков: PTB сам
    # повторяет запрос (max_retries=-1), поэтому это шум, а не поломка.
    if _is_network_failure(error):
        _mark_net_down(error)
        return

    if isinstance(error, RetryAfter):
        logger.info("Флуд-контроль: повтор через %s с", error.retry_after)
        return

    # Не сетевой сбой, а ошибка конфигурации: с этим токеном работает ещё одна
    # копия бота. Telegram отдаёт сообщения только одному getUpdates.
    if isinstance(error, Conflict):
        logger.error(
            "Конфликт экземпляров: этот токен уже опрашивает другой запущенный бот. "
            "Остановите лишние копии — пока их две, сообщения теряются у обеих."
        )
        return

    logger.error("Ошибка при обработке обновления: %s", error, exc_info=error)
    if isinstance(update, Update) and update.effective_chat is not None:
        try:
            await context.bot.send_message(
                update.effective_chat.id,
                "⚠️ Произошла ошибка при обработке запроса. Попробуй ещё раз чуть позже.",
            )
        except TelegramError:
            pass


# ---------------------------------------------------------------------------
# Сборка приложения
# ---------------------------------------------------------------------------


def build_conversations() -> list[ConversationHandler]:
    add_conv = ConversationHandler(
        entry_points=[CommandHandler("add_birthday", add_birthday_entry)],
        states={
            ADD_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_birthday_name)],
            ADD_DAY: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_birthday_day)],
            ADD_MONTH: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_birthday_month)],
        },
        fallbacks=[CommandHandler("cancel", cancel_conversation)],
        allow_reentry=True,
        conversation_timeout=300,
        name="add_birthday_conv",
    )

    del_conv = ConversationHandler(
        entry_points=[CommandHandler("del_birthday", del_birthday_entry)],
        states={
            DEL_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND, del_birthday_name)],
        },
        fallbacks=[CommandHandler("cancel", cancel_conversation)],
        allow_reentry=True,
        conversation_timeout=300,
        name="del_birthday_conv",
    )

    meetup_conv = ConversationHandler(
        entry_points=[CommandHandler("meetup", meetup_start)],
        states={
            LOCATION: [
                CallbackQueryHandler(meetup_location_chosen, pattern=r"^meetup:loc:"),
                CallbackQueryHandler(callback_cancel_meetup_flow, pattern=r"^meetup:cancel$"),
                MessageHandler(filters.TEXT & ~filters.COMMAND, meetup_buttons_hint),
            ],
            MEETUP_DATE: [
                CallbackQueryHandler(meetup_date_chosen, pattern=r"^meetup:date:"),
                CallbackQueryHandler(callback_cancel_meetup_flow, pattern=r"^meetup:cancel$"),
                MessageHandler(filters.TEXT & ~filters.COMMAND, meetup_buttons_hint),
            ],
            TIME: [
                CallbackQueryHandler(meetup_time_chosen, pattern=r"^meetup:time:"),
                CallbackQueryHandler(callback_cancel_meetup_flow, pattern=r"^meetup:cancel$"),
                MessageHandler(filters.TEXT & ~filters.COMMAND, meetup_buttons_hint),
            ],
            MANUAL_TIME: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, meetup_manual_time),
            ],
            MANUAL_DATE: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, meetup_manual_date),
            ],
        },
        fallbacks=[CommandHandler("cancel", cancel_conversation)],
        allow_reentry=True,
        conversation_timeout=600,
        name="meetup_conv",
    )

    weather_conv = ConversationHandler(
        entry_points=[CommandHandler("weather", weather_start)],
        states={
            W_LOCATION: [
                CallbackQueryHandler(weather_location_chosen, pattern=r"^weather:loc:"),
                CallbackQueryHandler(callback_cancel_weather_flow, pattern=r"^weather:cancel$"),
                MessageHandler(filters.TEXT & ~filters.COMMAND, weather_buttons_hint),
            ],
            W_DATE: [
                CallbackQueryHandler(weather_date_chosen, pattern=r"^weather:date:"),
                CallbackQueryHandler(callback_cancel_weather_flow, pattern=r"^weather:cancel$"),
                MessageHandler(filters.TEXT & ~filters.COMMAND, weather_buttons_hint),
            ],
            W_TIME: [
                CallbackQueryHandler(weather_time_chosen, pattern=r"^weather:time:"),
                CallbackQueryHandler(callback_cancel_weather_flow, pattern=r"^weather:cancel$"),
                MessageHandler(filters.TEXT & ~filters.COMMAND, weather_buttons_hint),
            ],
            W_MANUAL_DATE: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, weather_manual_date),
            ],
            W_MANUAL_TIME: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, weather_manual_time),
            ],
        },
        fallbacks=[CommandHandler("cancel", cancel_conversation)],
        allow_reentry=True,
        conversation_timeout=600,
        name="weather_conv",
    )
    return [add_conv, del_conv, meetup_conv, weather_conv]


def build_application() -> Application:
    if not settings.bot_token:
        raise SystemExit(
            "BOT_TOKEN не задан. Укажи его в .env (BOT_TOKEN=123456:ABC-DEF...)."
        )

    application = (
        Application.builder()
        .token(settings.bot_token)
        .concurrent_updates(True)
        .post_init(post_init)
        .build()
    )

    application.add_handler(
        MessageHandler(filters.ChatType.PRIVATE, private_chat_guard), group=-1
    )

    # Панель владельца — раньше остальных: /start в личке уходит в неё.
    application.add_handler(build_admin_conversation())

    for conversation in build_conversations():
        application.add_handler(conversation)

    application.add_handler(CommandHandler("start", cmd_start))
    application.add_handler(CommandHandler("help", cmd_help))
    application.add_handler(CommandHandler("birthdays", cmd_birthdays))
    application.add_handler(CommandHandler("cancel_meetup", cmd_cancel_meetup))
    application.add_handler(CommandHandler("chatid", cmd_chatid))

    application.add_error_handler(error_handler)
    return application


# ---------------------------------------------------------------------------
# Самопроверка (python main.py --check)
# ---------------------------------------------------------------------------


async def run_check() -> int:
    problems: list[str] = []
    print("1. Конфигурация")
    print(f"   TOKEN: {'задан' if settings.bot_token else 'НЕ ЗАДАН'}")
    print(f"   GROUP_CHAT_ID: {settings.group_chat_id!r}")
    print(f"   TIMEZONE: {settings.timezone_name} -> {now_local().isoformat()}")
    if not settings.bot_token:
        problems.append("BOT_TOKEN пуст")

    print("2. Файлы")
    for path in (LOCATIONS_FILE, BIRTHDAYS_FILE):
        ok = path.exists()
        print(f"   {path.relative_to(BASE_DIR)}: {'OK' if ok else 'НЕТ'}")
        if not ok:
            problems.append(f"нет файла {path}")
    print(f"   config/photos/: {'OK' if PHOTOS_DIR.is_dir() else 'НЕТ'}")
    print(f"   локаций: {len(load_locations())}, ДР: {len(load_birthdays())}")

    print("   локации:")
    for location in load_locations():
        link = location_link(location)
        photo = resolve_photo_path(location)
        print(
            f"     • {location['name']} — {location.get('time') or '—'} "
            f"| {location.get('address') or '—'} "
            f"| карта: {'OK' if link else 'НЕТ'} "
            f"| фото: {photo.name if photo else 'нет'}"
        )
        if location.get("photo") and photo is None:
            print(f"       (положи файл: {location['photo']})")

    print("3. Telegram API")
    if settings.bot_token:
        try:
            response = requests.get(
                f"https://api.telegram.org/bot{settings.bot_token}/getMe", timeout=20
            ).json()
            if response.get("ok"):
                user = response["result"]
                print(f"   @{user.get('username')} ({user.get('first_name')}) — OK")
            else:
                problems.append(f"getMe: {response.get('description')}")
                print(f"   ОШИБКА: {response.get('description')}")
        except requests.RequestException as exc:
            problems.append(f"getMe: {exc}")
            print(f"   ОШИБКА сети: {exc}")

    print("4. Погода")
    location = (load_locations() or [None])[0]
    if location:
        sample_dt = (now_local() + timedelta(hours=3)).replace(minute=0, second=0, microsecond=0)
        weather = await asyncio.to_thread(build_weather_text, location, sample_dt)
        print(f"   {location['name']}: {weather or 'нет данных'}")
    else:
        print("   нет локаций")

    print("5. Форматирование")
    print("   /birthdays:")
    for line in format_birthdays(load_birthdays()).splitlines():
        print(f"     {line}")
    print("   упоминания (одно сообщение):")
    print(f"     {build_mentions_text() or '—'}")

    print()
    if problems:
        print("ПРОБЛЕМЫ: " + "; ".join(problems))
        return 1
    print("ВСЕ ПРОВЕРКИ ПРОЙДЕНЫ")
    return 0


def setup_logging() -> None:
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")  # type: ignore[union-attr]
        except (AttributeError, OSError):  # pragma: no cover
            pass

    level = getattr(logging, settings.log_level, logging.INFO)
    LOGS_DIR.mkdir(parents=True, exist_ok=True)
    formatter = logging.Formatter(
        fmt="%(asctime)s %(levelname)-8s %(name)s: %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
    )
    root = logging.getLogger()
    root.setLevel(level)
    for handler in list(root.handlers):
        root.removeHandler(handler)

    stream = logging.StreamHandler(stream=sys.stdout)
    stream.setFormatter(formatter)
    root.addHandler(stream)

    file_handler = RotatingFileHandler(
        LOGS_DIR / "bot.log", maxBytes=2_000_000, backupCount=5, encoding="utf-8"
    )
    file_handler.setFormatter(formatter)
    root.addHandler(file_handler)

    logging.getLogger("httpx").setLevel(logging.WARNING)
    logging.getLogger("telegram").setLevel(logging.INFO)
    logging.getLogger("apscheduler").setLevel(logging.WARNING)


def main() -> int:
    _ensure_dirs()
    setup_logging()

    parser = argparse.ArgumentParser(description="Telegram-бот группового чата")
    parser.add_argument(
        "--check",
        action="store_true",
        help="выполнить самопроверку конфигурации и API без запуска polling",
    )
    args = parser.parse_args()

    if args.check:
        return asyncio.run(run_check())

    logger.info("Запуск бота (часовой пояс: %s)", settings.timezone_name)
    application = build_application()
    logger.info("Polling started")
    application.run_polling(
        allowed_updates=Update.ALL_TYPES,
        drop_pending_updates=False,
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        logger.info("Остановлено пользователем")
        sys.exit(0)
