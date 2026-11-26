"""Компактные тесты бота. Запуск: python -m unittest tests.test_bot

Проверяем только то, что ломается молча: права, диалог сходки, напоминание,
удаление служебных сообщений и порядок списка ДР. Сеть и Telegram подменяются.
"""

from __future__ import annotations

import asyncio
import tempfile
import unittest
from datetime import date, datetime, timedelta
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import AsyncMock, MagicMock, patch

import main as bot
from telegram.constants import ChatType


# ---------------------------------------------------------------------------
# Заглушки Telegram
# ---------------------------------------------------------------------------


class FakeChat:
    def __init__(self, chat_id=-1001, chat_type=ChatType.GROUP):
        self.id = chat_id
        self.type = chat_type
        self.title = "Тест"
        self.username = None


class FakeUser:
    def __init__(self, user_id=42):
        self.id = user_id
        self.username = "tester"


class FakeMessage:
    _counter = 0

    def __init__(self, chat, text="", bot=None):
        self.chat = chat
        self.chat_id = chat.id
        self.text = text
        self.replies = []
        self.bot = bot
        # Вложения: нужны админ-панели при загрузке фото.
        self.photo = []
        self.document = None
        self.caption = None
        FakeMessage._counter += 1
        self.message_id = 1000 + FakeMessage._counter

    def get_bot(self):
        return self.bot

    async def reply_text(self, text, **kwargs):
        self.replies.append(text)
        FakeMessage._counter += 1
        return SimpleNamespace(message_id=1000 + FakeMessage._counter)


class FakeUpdate:
    def __init__(self, chat=None, user=None, text="", callback_query=None, bot=None):
        self.effective_chat = chat or FakeChat()
        self.effective_user = user or FakeUser()
        self.effective_message = FakeMessage(self.effective_chat, text, bot=bot)
        self.callback_query = callback_query


class FakeJob:
    def __init__(self, name, when=None, data=None, chat_id=None):
        self.name = name
        self.when = when
        self.data = data
        self.chat_id = chat_id
        self.removed = False

    def schedule_removal(self):
        self.removed = True


class FakeJobQueue:
    def __init__(self):
        self.once = []
        self.daily = []

    def get_jobs_by_name(self, name):
        return [j for j in self.once if j.name == name and not j.removed]

    def run_once(self, callback, when, name=None, data=None, chat_id=None, **kwargs):
        job = FakeJob(name, when=when, data=data, chat_id=chat_id)
        job.callback = callback
        self.once.append(job)
        return job

    def run_daily(self, callback, time, name=None, **kwargs):
        job = FakeJob(name)
        job.time = time
        self.daily.append(job)
        return job

    def run_repeating(self, callback, interval, first=None, name=None, **kwargs):
        job = FakeJob(name)
        job.interval = interval
        job.first = first
        self.once.append(job)
        return job


class FakeBot:
    def __init__(self, status="administrator", delete_fails=False):
        self.status = status
        self.sent = []
        self.photos = []
        self.deleted = []
        self.pinned = []
        self.unpinned = []
        self.polls = []
        self.stopped = []
        self.delete_fails = delete_fails
        self._next_id = 5000

    async def get_chat_member(self, chat_id, user_id):
        return SimpleNamespace(status=self.status)

    async def send_message(self, chat_id, text, **kwargs):
        self.sent.append((chat_id, text))
        self._next_id += 1
        return SimpleNamespace(message_id=self._next_id)

    async def send_photo(self, chat_id, photo, caption=None, **kwargs):
        self.photos.append((chat_id, caption))
        self._next_id += 1
        return SimpleNamespace(message_id=self._next_id)

    async def delete_message(self, chat_id, message_id):
        if self.delete_fails:
            from telegram.error import BadRequest

            raise BadRequest("Message can't be deleted")
        self.deleted.append((chat_id, message_id))
        return True

    async def pin_chat_message(self, chat_id, message_id, **kwargs):
        self.pinned.append((chat_id, message_id))
        return True

    async def unpin_chat_message(self, chat_id, message_id=None, **kwargs):
        self.unpinned.append((chat_id, message_id))
        return True

    async def send_poll(self, chat_id, question, options, **kwargs):
        self.polls.append(
            {"chat_id": chat_id, "question": question, "options": list(options), **kwargs}
        )
        self._next_id += 1
        return SimpleNamespace(message_id=self._next_id)

    async def stop_poll(self, chat_id, message_id, **kwargs):
        self.stopped.append((chat_id, message_id))
        return True


class FakeContext:
    def __init__(self, args=None, status="administrator"):
        self.user_data = {}
        self.bot = FakeBot(status=status)
        self.job_queue = FakeJobQueue()
        self.args = args or []


class BotTestCase(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)
        self.birthdays = self.tmp / "birthdays.json"
        self.meetup = self.tmp / "meetup.json"
        self.state = self.tmp / "state.json"
        self.locations = self.tmp / "locations.json"

        bot.write_json(self.birthdays, [])
        bot.write_json(
            self.locations,
            [
                {
                    "id": "park",
                    "name": "Парк",
                    "time": "21:00",
                    "address": "адрес",
                    "coords": "55.737364, 37.815451",
                    "link": "https://yandex.ru/maps/1",
                    "note": "Сбор у входа",
                    "photo": "",
                }
            ],
        )

        self._patches = [
            patch.object(bot, "BIRTHDAYS_FILE", self.birthdays),
            patch.object(bot, "MEETUP_FILE", self.meetup),
            patch.object(bot, "STATE_FILE", self.state),
            patch.object(bot, "LOCATIONS_FILE", self.locations),
        ]
        for p in self._patches:
            p.start()

    def tearDown(self):
        for p in self._patches:
            p.stop()
        self._tmp.cleanup()

    def run_async(self, coro):
        return asyncio.run(coro)

    # helpers -------------------------------------------------------------
    def callback(self, data, bot=None):
        query = MagicMock()
        query.data = data
        query.message = SimpleNamespace(chat_id=-1, chat=FakeChat(-1))
        query.from_user = FakeUser()
        query.answer = AsyncMock()
        query.edit_message_text = AsyncMock()
        return FakeUpdate(FakeChat(-1), callback_query=query, bot=bot)

    def choose_location(self, context):
        return self.run_async(
            bot.meetup_location_chosen(self.callback("meetup:loc:park", context.bot), context)
        )

    def choose_time(self, context, value="21:00"):
        return self.run_async(
            bot.meetup_time_chosen(self.callback(f"meetup:time:{value}", context.bot), context)
        )


# ---------------------------------------------------------------------------
# Хранилище и список
# ---------------------------------------------------------------------------


class TestBirthdays(BotTestCase):
    def test_add_and_delete(self):
        bot.add_birthday("Анна", 5, 3)
        self.assertEqual(len(bot.load_birthdays()), 1)
        self.assertEqual(bot.delete_birthdays_by_name("анна")[0]["name"], "Анна")
        self.assertEqual(bot.load_birthdays(), [])

    def test_corrupted_file_recovered(self):
        self.birthdays.write_text("{мусор", encoding="utf-8")
        self.assertEqual(bot.load_birthdays(), [])
        self.assertTrue(list(self.tmp.glob("birthdays.json.broken")))

    def test_sorted_by_nearest(self):
        today = bot.today_local()
        future = today + timedelta(days=10)
        bot.add_birthday("Далёкий", future.day, future.month)
        bot.add_birthday("Скоро", today.day, today.month)
        text = bot.format_birthdays(bot.load_birthdays())
        self.assertLess(text.index("Скоро"), text.index("Далёкий"))
        self.assertIn("🎉 сегодня", text)
        self.assertIn("через 10 дней", text)


# ---------------------------------------------------------------------------
# Упоминания из birthdays.json
# ---------------------------------------------------------------------------


class TestMentions(BotTestCase):
    def test_mention_from_full_name(self):
        self.assertEqual(bot.mention_for_name("Никита Nekit_098"), "@Nekit_098")
        self.assertEqual(bot.mention_for_name("  Кирилл   rfasc "), "@rfasc")
        self.assertEqual(bot.mention_for_name("Евгений"), "Евгений")
        self.assertEqual(bot.mention_for_name("Анна @anna"), "@anna")
        self.assertEqual(bot.mention_for_name(""), "")

    def test_all_birthdays_in_one_message(self):
        bot.add_birthday("Никита Nekit_098", 31, 8)
        bot.add_birthday("Евгений cartonhq", 2, 1)
        bot.add_birthday("Евгений", 18, 1)
        self.assertEqual(
            bot.build_mentions_text(),
            "@Nekit_098 @cartonhq Евгений",
        )

    def test_empty_list_gives_empty_text(self):
        self.assertEqual(bot.build_mentions_text(), "")


# ---------------------------------------------------------------------------
# Права
# ---------------------------------------------------------------------------


class TestPermissions(BotTestCase):
    def test_private_chat_blocked(self):
        update = FakeUpdate(FakeChat(1, ChatType.PRIVATE))
        with self.assertRaises(bot.ApplicationHandlerStop):
            self.run_async(bot.private_chat_guard(update, FakeContext()))
        self.assertEqual(update.effective_message.replies, [bot.PRIVATE_ONLY_REPLY])

    def test_non_admin_can_create_meetup(self):
        update = FakeUpdate(FakeChat(-1))
        result = self.run_async(bot.meetup_start(update, FakeContext(status="member")))
        self.assertEqual(result, bot.LOCATION)
        self.assertNotIn("только администраторам", update.effective_message.replies[-1])

    def test_non_admin_can_cancel_meetup(self):
        context = FakeContext(status="member")
        update = FakeUpdate(FakeChat(-1), text="/cancel_meetup", bot=context.bot)
        self.run_async(bot.cmd_cancel_meetup(update, context))
        self.assertIn("Активной сходки нет", update.effective_message.replies[-1])


# ---------------------------------------------------------------------------
# Сходка: локация -> время -> дата
# ---------------------------------------------------------------------------


class TestMeetup(BotTestCase):
    def setUp(self):
        super().setUp()
        patch.object(
            bot, "build_weather_text", return_value="🌤 Погода на 21:00: 0°, пасмурно"
        ).start()
        self.addCleanup(patch.stopall)

    def test_wizards_ask_location_then_time_then_date(self):
        context = FakeContext()
        self.choose_location(context)
        self.assertEqual(context.user_data["meetup_location"], "park")
        self.assertEqual(self.choose_time(context), bot.MEETUP_DATE)
        self.assertEqual(context.user_data["meetup_time"], "21:00")

    def test_time_keyboard(self):
        texts = [b.text for row in bot.times_keyboard().inline_keyboard for b in row]
        self.assertEqual(texts, ["20:00", "21:00", "22:00", "Своё время", "❌ Отмена"])

    def test_manual_time(self):
        context = FakeContext()
        self.choose_location(context)
        update = FakeUpdate(FakeChat(-1), text="19:45", bot=context.bot)
        self.assertEqual(
            self.run_async(bot.meetup_manual_time(update, context)), bot.MEETUP_DATE
        )
        self.assertEqual(context.user_data["meetup_time"], "19:45")

    def test_bad_manual_time_reprompts(self):
        context = FakeContext()
        self.choose_location(context)
        update = FakeUpdate(FakeChat(-1), text="вечером", bot=context.bot)
        self.assertEqual(
            self.run_async(bot.meetup_manual_time(update, context)), bot.MANUAL_TIME
        )

    def test_publish_pins_and_sends_mentions_and_weather(self):
        bot.add_birthday("Никита Nekit_098", 31, 8)
        bot.add_birthday("Кирилл rfasc", 29, 4)
        context = FakeContext()
        self.choose_location(context)
        self.choose_time(context)
        self.run_async(
            bot.meetup_date_chosen(self.callback("meetup:date:1", context.bot), context)
        )

        texts = [t for _, t in context.bot.sent]
        announcement = next(t for t in texts if "ОФИЦИАЛЬНОЕ СООБЩЕНИЕ" in t)
        self.assertIn("🕐 Время: 21:00", announcement)

        # Отдельного сообщения с упоминаниями после анонса больше нет.
        self.assertNotIn("@Nekit_098 @rfasc", texts)
        self.assertEqual(texts[-1], "🌤 Погода на 21:00: 0°, пасмурно")
        self.assertTrue(context.bot.pinned, "анонс должен быть закреплён")
        self.assertEqual(context.bot.pinned[0][0], -1)

        # Опрос публичный, без мультивыбора, без правильного ответа.
        self.assertEqual(len(context.bot.polls), 1)
        poll = context.bot.polls[0]
        self.assertEqual(poll["question"], "Ты идёшь?")
        self.assertEqual(poll["options"], ["Приеду", "Не смогу", "Пока не знаю"])
        self.assertFalse(poll["is_anonymous"])
        self.assertFalse(poll["allows_multiple_answers"])
        self.assertEqual(poll["type"], "regular")
        self.assertNotIn("correct_option_id", poll)

        # Опрос закрывается в момент сходки.
        close_jobs = [j for j in context.job_queue.once if j.name == bot.JOB_MEETUP_POLL_CLOSE]
        self.assertEqual(len(close_jobs), 1)
        self.assertEqual(close_jobs[0].when.hour, 21)

        saved = bot.load_meetup()
        self.assertEqual(saved["time"], "21:00")
        self.assertEqual(saved["date"], (bot.today_local() + timedelta(days=1)).isoformat())

    def test_reminder_two_hours_before(self):
        context = FakeContext()
        self.choose_location(context)
        self.choose_time(context)
        target = bot.today_local() + timedelta(days=3)
        self.run_async(bot._finalize_meetup(FakeUpdate(FakeChat(-1)), context, target, chat_id=-1))

        jobs = [j for j in context.job_queue.once if j.name == bot.JOB_MEETUP_REMINDER]
        self.assertEqual(len(jobs), 1)
        job = jobs[0]
        self.assertEqual(job.when.hour, 19)  # 21:00 минус 2 часа
        self.assertEqual(job.data["time"], "21:00")

    def test_reminder_text_says_two_hours(self):
        bot.add_birthday("Никита Nekit_098", 31, 8)
        context = FakeContext()
        context.job_queue.get_jobs_by_name = lambda name: []
        job = FakeJob(bot.JOB_MEETUP_REMINDER, data={"name": "Парк", "time": "21:00", "chat_id": -1})
        context.job = job
        self.run_async(bot.meetup_reminder_job(context))
        self.assertIn("Через 2 часа сходка", context.bot.sent[0][1])
        self.assertIn("@Nekit_098", context.bot.sent[0][1])

    def test_cancel_unpins(self):
        context = FakeContext()
        self.choose_location(context)
        self.choose_time(context)
        self.run_async(
            bot._finalize_meetup(
                FakeUpdate(FakeChat(-1)), context, bot.today_local() + timedelta(days=2), chat_id=-1
            )
        )
        self.run_async(bot.cmd_cancel_meetup(FakeUpdate(FakeChat(-1)), context))
        self.assertTrue(context.bot.unpinned)
        self.assertTrue(context.bot.stopped, "опрос должен закрыться при отмене")
        self.assertIsNone(bot.load_meetup())

    def test_past_date_reprompts_without_publishing(self):
        context = FakeContext()
        self.choose_location(context)
        self.choose_time(context)
        result = self.run_async(
            bot._finalize_meetup(
                FakeUpdate(FakeChat(-1)), context, bot.today_local() - timedelta(days=1), chat_id=-1
            )
        )
        self.assertEqual(result, bot.MEETUP_DATE)
        # Анонс не публикуется: в чат ушли только подсказки диалога.
        self.assertFalse(any("ОФИЦИАЛЬНОЕ" in t for _, t in context.bot.sent))
        self.assertFalse(context.bot.pinned)


# ---------------------------------------------------------------------------
# Удаление служебных сообщений
# ---------------------------------------------------------------------------


class TestCleanup(BotTestCase):
    def test_add_birthday_deletes_command_and_prompts(self):
        context = FakeContext()
        entry = FakeUpdate(FakeChat(-1), text="/add_birthday", bot=context.bot)
        command_id = entry.effective_message.message_id
        self.run_async(bot.add_birthday_entry(entry, context))
        self.run_async(bot.add_birthday_name(FakeUpdate(FakeChat(-1), text="Анна", bot=context.bot), context))
        self.run_async(bot.add_birthday_day(FakeUpdate(FakeChat(-1), text="5", bot=context.bot), context))
        self.run_async(bot.add_birthday_month(FakeUpdate(FakeChat(-1), text="3", bot=context.bot), context))

        deleted = [mid for _, mid in context.bot.deleted]
        self.assertIn(command_id, deleted)
        self.assertGreaterEqual(len(deleted), 7)
        self.assertEqual(bot.load_birthdays()[0]["name"], "Анна")

    def test_delete_survives_missing_rights(self):
        bot.add_birthday("Анна", 5, 3)
        context = FakeContext()
        context.bot.delete_fails = True
        update = FakeUpdate(FakeChat(-1), text="/birthdays", bot=context.bot)
        self.run_async(bot.cmd_birthdays(update, context))
        self.assertIn("Дни рождения", update.effective_message.replies[-1])


# ---------------------------------------------------------------------------
# Погода и сборка приложения
# ---------------------------------------------------------------------------


class TestWeather(BotTestCase):
    def test_parse_coords(self):
        self.assertEqual(bot.parse_coords("55.7, 37.8"), (55.7, 37.8))
        self.assertIsNone(bot.parse_coords(""))
        self.assertIsNone(bot.parse_coords("999, 0"))

    def test_no_coords_returns_none(self):
        location = {"coords": ""}
        self.assertIsNone(bot.build_weather_text(location, bot.now_local()))


class TestWeatherRequest(BotTestCase):
    """Команда /weather: локация -> дата -> время -> одно сообщение."""

    LOCATION = {
        "id": "park",
        "name": "Парк",
        "time": "21:00",
        "address": "адрес",
        "coords": "55.737364, 37.815451",
        "link": "",
        "note": "",
        "photo": "",
    }

    def weather_callback(self, data, bot_):
        query = MagicMock()
        query.data = data
        query.message = SimpleNamespace(chat_id=-1, chat=FakeChat(-1))
        query.from_user = FakeUser()
        query.answer = AsyncMock()
        query.edit_message_text = AsyncMock()
        return FakeUpdate(FakeChat(-1), callback_query=query, bot=bot_)

    def choose(self, context, data):
        handler = {
            "loc": bot.weather_location_chosen,
            "date": bot.weather_date_chosen,
            "time": bot.weather_time_chosen,
        }[data.split(":")[1]]
        return self.run_async(handler(self.weather_callback(data, context.bot), context))

    def test_wizard_asks_location_date_time_and_sends_report(self):
        report = "🌤 <b>Погода</b> · Парк\n📅 Среда, 25.11.2026 · 21:00\n🌡 Температура: -3°"
        with patch.object(bot, "build_weather_report", return_value=report):
            context = FakeContext()
            start = FakeUpdate(FakeChat(-1), text="/weather", bot=context.bot)
            self.assertEqual(self.run_async(bot.weather_start(start, context)), bot.W_LOCATION)

            self.assertEqual(self.choose(context, "weather:loc:park"), bot.W_DATE)
            self.assertEqual(context.user_data["weather_location"], "park")

            self.assertEqual(self.choose(context, "weather:date:1"), bot.W_TIME)
            self.assertEqual(
                context.user_data["weather_date"],
                (bot.today_local() + timedelta(days=1)).isoformat(),
            )

            self.assertEqual(self.choose(context, "weather:time:21:00"), bot.ConversationHandler.END)

        self.assertEqual(context.bot.sent[-1], (-1, report))
        self.assertNotIn("weather_time", context.user_data)
        # Служебная переписка удалена, прогноз остался.
        self.assertTrue(context.bot.deleted)

    def test_manual_date_outside_forecast_window_reprompts(self):
        context = FakeContext()
        context.user_data["weather_location"] = "park"
        far = (bot.today_local() + timedelta(days=bot.MAX_FORECAST_DAYS + 5)).strftime("%d.%m.%Y")
        update = FakeUpdate(FakeChat(-1), text=far, bot=context.bot)
        self.assertEqual(self.run_async(bot.weather_manual_date(update, context)), bot.W_MANUAL_DATE)
        self.assertIn("Прогноз доступен", update.effective_message.replies[-1])

    def test_report_contains_details(self):
        values = {
            "temperature_2m": -3.4,
            "apparent_temperature": -7.0,
            "precipitation_probability": 40,
            "precipitation": 0.4,
            "weather_code": 71,
            "wind_speed_10m": 12.3,
        }
        # Дата считается от сегодняшнего дня: иначе тест «стареет» и падает.
        tomorrow = bot.today_local() + timedelta(days=1)
        target = datetime(
            tomorrow.year, tomorrow.month, tomorrow.day, 21, 0, tzinfo=bot.settings.timezone
        )
        with patch.object(bot, "_fetch_weather_hour", return_value=values):
            text = bot.build_weather_report(self.LOCATION, target)
        self.assertIn("Парк", text)
        self.assertIn(tomorrow.strftime("%d.%m.%Y"), text)
        self.assertIn("21:00", text)
        self.assertIn("-3°", text)
        self.assertIn("ощущается как -7°", text)
        self.assertIn("небольшой снег", text)
        self.assertIn("Осадки: 40%", text)
        self.assertIn("Ветер: 12 км/ч", text)

    def test_report_handles_missing_coords_and_network(self):
        target = bot.now_local()
        self.assertIn(
            "не заданы координаты",
            bot.build_weather_report({"name": "Парк", "coords": ""}, target),
        )
        with patch.object(bot, "_fetch_weather_hour", return_value=None):
            self.assertIn("Не удалось получить прогноз", bot.build_weather_report(self.LOCATION, target))


class TestWiring(BotTestCase):
    def test_handlers_registered(self):
        app = bot.build_application()
        commands = set()
        for group in app.handlers.values():
            for handler in group:
                commands.update(getattr(handler, "commands", ()) or ())
                for entry in getattr(handler, "entry_points", ()) or ():
                    commands.update(getattr(entry, "commands", ()) or ())
        for expected in (
            "birthdays",
            "add_birthday",
            "del_birthday",
            "meetup",
            "cancel_meetup",
            "weather",
        ):
            self.assertIn(expected, commands)
        self.assertNotIn("all", commands)
        self.assertNotIn("calendar", commands)
        # /chatid работает, но в меню и в справке не показывается.
        self.assertIn("chatid", commands)
        self.assertNotIn("/chatid", bot.build_help_text())

    def test_only_birthdays_job_daily(self):
        context = FakeContext()
        app = SimpleNamespace(job_queue=context.job_queue, bot=AsyncMock())
        with patch.object(bot, "restore_meetup_reminder", AsyncMock()):
            self.run_async(bot.post_init(app))
        self.assertEqual([j.name for j in context.job_queue.daily], [bot.JOB_BIRTHDAYS])


class TestAdminPanel(BotTestCase):
    """Админ-панель владельца в личных сообщениях."""

    OWNER = 757255226

    def setUp(self):
        super().setUp()
        self.photos = self.tmp / "photos"
        self.photos.mkdir(exist_ok=True)
        (self.photos / "vegas.jpg").write_bytes(b"\xff\xd8fake")
        # Фото из бота пишутся в data/photos, а не в config/photos.
        self.uploads = self.tmp / "uploads"
        self._patches.append(patch.object(bot, "PHOTOS_DIR", self.photos))
        self._patches.append(patch.object(bot, "UPLOADED_PHOTOS_DIR", self.uploads))
        self._patches.append(patch.object(bot, "BASE_DIR", self.tmp))
        self._patches.append(patch.object(bot.settings, "admin_user_id", self.OWNER))
        for p in self._patches[-4:]:
            p.start()

    def owner_update(self, text="", **kwargs):
        return FakeUpdate(
            FakeChat(self.OWNER, ChatType.PRIVATE),
            FakeUser(self.OWNER),
            text=text,
            **kwargs,
        )

    def admin_callback(self, data, context, user_id=None):
        chat = FakeChat(self.OWNER, ChatType.PRIVATE)
        query = MagicMock()
        query.data = data
        query.message = SimpleNamespace(chat_id=self.OWNER, chat=chat)
        query.from_user = FakeUser(user_id or self.OWNER)
        query.answer = AsyncMock()
        query.edit_message_text = AsyncMock()
        return FakeUpdate(
            FakeChat(self.OWNER, ChatType.PRIVATE),
            FakeUser(user_id or self.OWNER),
            callback_query=query,
            bot=context.bot,
        )

    def press(self, data, context, user_id=None):
        """Нажатие кнопки админ-панели: возвращает состояние диалога."""
        update = self.admin_callback(data, context, user_id=user_id)
        return self.run_async(bot.admin_callback(update, context))

    def test_owner_passes_private_guard_others_blocked(self):
        self.run_async(bot.private_chat_guard(self.owner_update(), FakeContext()))
        with self.assertRaises(bot.ApplicationHandlerStop):
            self.run_async(
                bot.private_chat_guard(
                    FakeUpdate(FakeChat(1, ChatType.PRIVATE), FakeUser(42)), FakeContext()
                )
            )

    def test_panel_opens_in_private_chat(self):
        context = FakeContext()
        update = self.owner_update()
        self.assertEqual(self.run_async(bot.admin_panel(update, context)), bot.P_PANEL)
        self.assertIn("Админ-панель", update.effective_message.replies[-1])

    def test_start_in_group_still_shows_help(self):
        context = FakeContext()
        update = FakeUpdate(FakeChat(-1, ChatType.GROUP), text="/start", bot=context.bot)
        self.run_async(bot.cmd_start(update, context))
        reply = update.effective_message.replies[-1]
        self.assertIn("Команды бота", reply)
        self.assertNotIn("Админ-панель", reply)

    def test_add_birthday_flow(self):
        context = FakeContext()
        self.press("adm:bd:add", context)
        self.assertEqual(
            self.run_async(bot.admin_bd_name(self.owner_update("Анна anna"), context)),
            bot.P_BD_DAY,
        )
        self.assertEqual(
            self.run_async(bot.admin_bd_day(self.owner_update("5"), context)), bot.P_BD_MONTH
        )
        self.run_async(bot.admin_bd_month(self.owner_update("3"), context))
        items = bot.load_birthdays()
        self.assertEqual([(i["name"], i["day"], i["month"]) for i in items], [("Анна anna", 5, 3)])

    def test_location_wizard_saves_all_fields(self):
        context = FakeContext()
        self.press("adm:loc:add", context)
        answers = ["vegas", "ТРЦ", "21:00", "адрес", "55.1, 37.2", "https://map", "заметка", "vegas"]
        state = None
        for value in answers:
            state = self.run_async(bot.admin_loc_field(self.owner_update(value), context))
        self.assertEqual(state, bot.P_PANEL)
        location = next(item for item in bot.load_locations() if item["id"] == "vegas")
        self.assertEqual(location["name"], "ТРЦ")
        self.assertEqual(location["time"], "21:00")
        self.assertEqual(location["coords"], "55.100000, 37.200000")
        self.assertEqual(location["photo"], "photos/vegas.jpg")
        self.assertIsNotNone(bot.resolve_photo_path(location))

    def test_duplicate_location_id_rejected(self):
        bot.upsert_location({"id": "vegas", "name": "Старая"})
        context = FakeContext()
        self.press("adm:loc:add", context)
        self.assertEqual(
            self.run_async(bot.admin_loc_field(self.owner_update("vegas"), context)), bot.P_LOC_ID
        )
        same_id = [item for item in bot.load_locations() if item["id"] == "vegas"]
        self.assertEqual(len(same_id), 1)
        self.assertEqual(same_id[0]["name"], "Старая")

    def test_photo_upload_uses_caption_as_name(self):
        context = FakeContext()
        self.press("adm:ph:up", context)

        upload = AsyncMock()

        async def save(custom_path=None, **kwargs):
            Path(custom_path).write_bytes(b"\xff\xd8photo")

        upload.download_to_drive = save
        photo = SimpleNamespace(get_file=AsyncMock(return_value=upload))
        update = self.owner_update("")
        update.effective_message.photo = [photo]
        update.effective_message.caption = "massage"
        self.assertEqual(
            self.run_async(bot.admin_photo_input(update, context)), bot.P_PANEL
        )
        # Загруженное фото уходит в data/photos, чтобы пережить деплой из Git.
        self.assertTrue((self.uploads / "massage.jpg").is_file())
        self.assertFalse((self.photos / "massage.jpg").exists())

    def test_photo_from_name_then_file(self):
        context = FakeContext()
        self.press("adm:ph:up", context)
        update = self.owner_update("kuskovo")
        self.assertEqual(
            self.run_async(bot.admin_photo_input(update, context)), bot.P_PHOTO_WAIT
        )
        self.assertEqual(context.user_data.get("adm_photo_name"), "kuskovo")

        upload = AsyncMock()

        async def save(custom_path=None, **kwargs):
            Path(custom_path).write_bytes(b"\xff\xd8photo")

        upload.download_to_drive = save
        photo_update = self.owner_update("")
        photo_update.effective_message.photo = [
            SimpleNamespace(get_file=AsyncMock(return_value=upload))
        ]
        self.assertEqual(
            self.run_async(bot.admin_photo_input(photo_update, context)), bot.P_PANEL
        )
        self.assertTrue((self.uploads / "kuskovo.jpg").is_file())

    def test_list_sees_both_photo_folders(self):
        self.uploads.mkdir(exist_ok=True)
        (self.uploads / "new.jpg").write_bytes(b"\xff\xd8new")
        names = [path.name for path in bot.list_photo_files()]
        self.assertIn("vegas.jpg", names)  # из config/photos
        self.assertIn("new.jpg", names)  # из data/photos

    def test_photo_without_name_asks_for_it(self):
        context = FakeContext()
        self.press("adm:ph:up", context)
        update = self.owner_update("")
        update.effective_message.photo = [SimpleNamespace(get_file=AsyncMock())]
        update.effective_message.caption = ""
        self.assertEqual(
            self.run_async(bot.admin_photo_input(update, context)), bot.P_PHOTO_WAIT
        )
        self.assertIn("имени нет", update.effective_message.replies[-1])

    def test_photo_delete_removes_file(self):
        context = FakeContext()
        self.press("adm:ph:del", context)
        names = context.user_data.get("adm_photo_pick") or []
        self.assertIn("vegas.jpg", names)
        self.press(f"adm:ph:delok:{names.index('vegas.jpg')}", context)
        self.assertFalse((self.photos / "vegas.jpg").exists())

    def test_meetup_edit_reschedules_jobs(self):
        future = bot.today_local() + timedelta(days=4)
        bot.save_meetup(
            {
                "location_id": "park",
                "name": "Парк",
                "time": "21:00",
                "chat_id": -1,
                "date": future.isoformat(),
                "meetup_at": f"{future.isoformat()}T21:00:00+03:00",
                "message_id": 1,
                "poll_message_id": 2,
            }
        )
        context = FakeContext()
        self.press("adm:mt:edit", context)
        new_date = bot.today_local() + timedelta(days=6)
        self.assertEqual(
            self.run_async(bot.admin_mt_date(self.owner_update(new_date.strftime("%d.%m.%Y")), context)),
            bot.P_MT_TIME,
        )
        self.assertEqual(
            self.run_async(bot.admin_mt_time(self.owner_update("19:15"), context)), bot.P_PANEL
        )
        saved = bot.load_meetup()
        self.assertEqual(saved["time"], "19:15")
        self.assertTrue(saved["meetup_at"].startswith(f"{new_date.isoformat()}T19:15"))
        self.assertEqual(len(context.job_queue.get_jobs_by_name(bot.JOB_MEETUP_REMINDER)), 1)
        self.assertEqual(len(context.job_queue.get_jobs_by_name(bot.JOB_MEETUP_POLL_CLOSE)), 1)

    def test_stranger_callback_rejected(self):
        context = FakeContext()
        update = self.admin_callback("adm:root", context, user_id=42)
        self.assertEqual(
            self.run_async(bot.admin_callback(update, context)), bot.ConversationHandler.END
        )
        update.callback_query.answer.assert_awaited_with(
            "Доступ только для владельца бота", show_alert=True
        )

    def test_callback_from_group_rejected(self):
        context = FakeContext()
        chat = FakeChat(-1, ChatType.GROUP)
        query = MagicMock()
        query.data = "adm:root"
        query.message = SimpleNamespace(chat_id=-1, chat=chat)
        query.from_user = FakeUser(self.OWNER)
        query.answer = AsyncMock()
        query.edit_message_text = AsyncMock()
        update = FakeUpdate(chat, FakeUser(self.OWNER), callback_query=query, bot=context.bot)
        self.assertEqual(
            self.run_async(bot.admin_callback(update, context)), bot.ConversationHandler.END
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
