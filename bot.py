#!/usr/bin/env python3
"""Svitlo-bot: Telegram-сповіщення про графіки відключень світла для кількох адрес.

Що робить:
  * вранці надсилає графік на день для всіх адрес;
  * повідомляє, коли з'явився графік на завтра або змінився чинний;
  * нагадує за N хвилин до відключення (і, за бажанням, до увімкнення);
  * відповідає на команди /now, /today, /tomorrow.

Запуск:
  python3 bot.py                 постійна робота (сервер, VPS, Docker)
  python3 bot.py --once          одна перевірка і вихід (cron, GitHub Actions)
  python3 bot.py --dry-run --once   надрукувати повідомлення, нічого не надсилати

Потрібен лише Python 3.9+, сторонні бібліотеки не використовуються.
Дані: https://github.com/Baskerville42/outage-data-ua (знімки сайтів ДТЕК).
"""
from __future__ import annotations

import argparse
import html
import json
import logging
import math
import os
import sys
import time
import urllib.error
import urllib.request
from datetime import date, datetime, time as dtime, timedelta, timezone, tzinfo

log = logging.getLogger("svitlo")

DEFAULT_DATA_URL = (
    "https://raw.githubusercontent.com/Baskerville42/outage-data-ua/main/data/{region}.json"
)
DEFAULTS = {
    "remind_before_off_min": 30,   # за скільки хвилин попереджати про відключення (0 = вимкнено)
    "remind_before_on_min": 0,     # за скільки хвилин попереджати про увімкнення (0 = вимкнено)
    "digest_time": "07:00",        # коли надсилати графік на день (null = не надсилати)
    "quiet_hours": ["23:00", "07:00"],  # у цей час повідомлення приходять без звуку (null = завжди зі звуком)
    "poll_seconds": 300,           # як часто перевіряти графік
    "stale_hours": 3,              # попередити, якщо джерело не оновлюється довше
    "data_url": DEFAULT_DATA_URL,
}

# Статус години на сайті ДТЕК -> дві півгодини: 1 = світло є, 0 = немає, ? = можливе відключення
STATUS_TO_SLOTS = {
    "yes": "11", "no": "00", "first": "01", "second": "10",
    "maybe": "??", "mfirst": "?1", "msecond": "1?",
}
ON, OFF, MAYBE = "1", "0", "?"
WEEKDAYS = ["пн", "вт", "ср", "чт", "пт", "сб", "нд"]
HALF_HOUR = timedelta(minutes=30)


# --------------------------------------------------------------------------- час

class _KyivFallback(tzinfo):
    """Київський час за правилами ЄС — на випадок, коли в системі немає бази tzdata (Windows)."""

    @staticmethod
    def _last_sunday(year: int, month: int) -> datetime:
        d = datetime(year, month + 1, 1) - timedelta(days=1)
        return d - timedelta(days=(d.weekday() + 1) % 7)

    def _is_dst_utc(self, utc_naive: datetime) -> bool:
        start = self._last_sunday(utc_naive.year, 3).replace(hour=1)
        end = self._last_sunday(utc_naive.year, 10).replace(hour=1)
        return start <= utc_naive < end

    def utcoffset(self, dt):
        return timedelta(hours=3 if self._is_dst_utc(dt.replace(tzinfo=None) - timedelta(hours=2)) else 2)

    def dst(self, dt):
        return self.utcoffset(dt) - timedelta(hours=2)

    def tzname(self, dt):
        return "EEST" if self.dst(dt) else "EET"

    def fromutc(self, dt):
        naive = dt.replace(tzinfo=None)
        return (naive + timedelta(hours=3 if self._is_dst_utc(naive) else 2)).replace(tzinfo=self)


def _kyiv_tz() -> tzinfo:
    try:
        from zoneinfo import ZoneInfo
        for name in ("Europe/Kyiv", "Europe/Kiev"):
            try:
                return ZoneInfo(name)
            except Exception:
                continue
    except ImportError:
        pass
    return _KyivFallback()


KYIV = _kyiv_tz()


def now_kyiv() -> datetime:
    return datetime.now(timezone.utc).astimezone(KYIV)


def parse_hhmm(value: str) -> dtime:
    h, m = str(value).strip().split(":")
    return dtime(int(h), int(m))


# ----------------------------------------------------------------- конфігурація

class ConfigError(Exception):
    pass


def normalize_group(value) -> str:
    """'2.1', 'GPV2.1', 'Черга 2.1' -> 'GPV2.1'."""
    digits = "".join(ch for ch in str(value).replace(",", ".") if ch.isdigit() or ch == ".")
    if not digits or "." not in digits:
        raise ConfigError(f"Незрозуміла черга: {value!r}. Очікується щось на кшталт \"2.1\".")
    return "GPV" + digits


def load_config(path: str) -> dict:
    raw = os.environ.get("BOT_CONFIG")
    if raw:
        try:
            cfg = json.loads(raw)
        except json.JSONDecodeError as e:
            raise ConfigError(f"BOT_CONFIG містить некоректний JSON: {e}") from None
    else:
        try:
            with open(path, encoding="utf-8") as f:
                cfg = json.load(f)
        except FileNotFoundError:
            raise ConfigError(f"Не знайдено файл налаштувань {path}") from None
        except json.JSONDecodeError as e:
            raise ConfigError(f"{path}: некоректний JSON: {e}") from None

    cfg = {**DEFAULTS, **cfg}
    cfg["telegram_token"] = os.environ.get("TELEGRAM_BOT_TOKEN") or cfg.get("telegram_token") or ""
    if cfg["telegram_token"].startswith("ВСТАВТЕ"):
        cfg["telegram_token"] = ""
    env_chats = os.environ.get("TELEGRAM_CHAT_IDS")
    chats = env_chats.replace(";", ",").split(",") if env_chats else cfg.get("chat_ids") or []
    try:
        cfg["chat_ids"] = [int(str(c).strip()) for c in chats if str(c).strip()]
    except ValueError:
        raise ConfigError("chat_ids мають бути числами, наприклад [123456789]") from None

    addresses = cfg.get("addresses") or []
    if not addresses:
        raise ConfigError("У налаштуваннях немає жодної адреси (addresses).")
    targets: dict = {}
    for a in addresses:
        try:
            name, region = str(a["name"]).strip(), str(a["region"]).strip()
            group = normalize_group(a["group"])
        except KeyError as e:
            raise ConfigError(f"В адресі бракує поля {e}: {a}") from None
        # кілька адрес з однією чергою зливаються в одну ціль, щоб не дублювати повідомлення
        t = targets.setdefault((region, group), {"region": region, "group": group, "names": []})
        t["names"].append(name)
    cfg["targets"] = [
        {**t, "key": f"{t['region']}:{t['group']}", "name": " / ".join(t["names"])}
        for t in targets.values()
    ]
    for field in ("digest_time",):
        if cfg.get(field):
            cfg[field] = parse_hhmm(cfg[field])
    if cfg.get("quiet_hours"):
        cfg["quiet_hours"] = [parse_hhmm(x) for x in cfg["quiet_hours"]]
    return cfg


# --------------------------------------------------------------- стан між запусками

def load_state(path: str) -> dict:
    try:
        with open(path, encoding="utf-8") as f:
            state = json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        state = {}
    state.setdefault("schedules", {})
    state.setdefault("reminded", [])
    state.setdefault("source", {})
    return state


def save_state(path: str, state: dict) -> None:
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=1)
    os.replace(tmp, path)


# ------------------------------------------------------------------------- дані

def parse_day(hours: dict) -> str:
    """{'1': 'yes', ... '24': 'no'} -> рядок із 48 символів (півгодини від 00:00)."""
    return "".join(STATUS_TO_SLOTS.get(hours.get(str(h)), MAYBE * 2) for h in range(1, 25))


def fetch_region(url_template: str, region: str) -> dict:
    url = url_template.format(region=region)
    req = urllib.request.Request(url, headers={"User-Agent": "svitlo-bot/1.0"})
    with urllib.request.urlopen(req, timeout=25) as resp:
        raw = json.loads(resp.read().decode("utf-8"))
    fact = raw.get("fact") or {}
    days = {}
    for ts, groups in (fact.get("data") or {}).items():
        try:
            day = datetime.fromtimestamp(int(ts), KYIV).date()
        except (ValueError, OverflowError):
            continue
        days[day] = {g: parse_day(h) for g, h in groups.items() if isinstance(h, dict)}
    updated = None
    try:
        updated = datetime.fromisoformat(str(raw.get("lastUpdated")).replace("Z", "+00:00"))
    except ValueError:
        pass
    return {"days": days, "last_updated": updated, "update_text": fact.get("update")}


# ------------------------------------------------------------- робота з графіком

def timeline(sched: dict, days: list) -> list:
    """[(початок півгодини, стан)] для послідовних днів; зупиняється на першому дні без графіка."""
    out = []
    for d in days:
        slots = sched.get(d.isoformat())
        if not slots:
            if out:
                break
            continue
        base = datetime.combine(d, dtime())
        out += [(base + HALF_HOUR * i, ch) for i, ch in enumerate(slots)]
    return out


def runs(tl: list) -> list:
    """Зливає сусідні півгодини з однаковим станом у відрізки.

    prev/next — стан перед і після відрізка, None означає «графік невідомий».
    """
    out = []
    for start, ch in tl:
        if out and out[-1]["state"] == ch:
            out[-1]["end"] = start + HALF_HOUR
        else:
            out.append({"start": start, "end": start + HALF_HOUR, "state": ch, "prev": None, "next": None})
    for i, r in enumerate(out):
        if i:
            r["prev"] = out[i - 1]["state"]
        if i + 1 < len(out):
            r["next"] = out[i + 1]["state"]
    return out


def fmt_dur(delta: timedelta) -> str:
    minutes = int(delta.total_seconds() // 60)
    h, m = divmod(minutes, 60)
    return " ".join(p for p in (f"{h} год" if h else "", f"{m} хв" if m or not h else "") if p)


def fmt_clock(moment: datetime, day: date | None = None) -> str:
    if day is not None and moment == datetime.combine(day + timedelta(days=1), dtime()):
        return "24:00"
    return moment.strftime("%H:%M")


def fmt_range(r: dict, day: date | None = None) -> str:
    return f"{fmt_clock(r['start'])}–{fmt_clock(r['end'], day)}"


def fmt_date(d: date, today: date) -> str:
    label = {0: "сьогодні", 1: "завтра"}.get((d - today).days)
    text = f"{WEEKDAYS[d.weekday()]} {d.strftime('%d.%m')}"
    return f"{label}, {text}" if label else text


def group_label(group: str) -> str:
    return "черга " + group.replace("GPV", "")


def target_title(t: dict) -> str:
    return f"🏠 <b>{html.escape(t['name'])}</b> · {group_label(t['group'])}"


def day_lines(slots: str | None, d: date) -> list:
    if not slots:
        return ["⏳ графік ще не опубліковано"]
    outages = [r for r in runs(timeline({d.isoformat(): slots}, [d])) if r["state"] != ON]
    if not outages:
        return ["✅ відключень не заплановано"]
    lines = []
    for r in outages:
        if r["state"] == OFF:
            lines.append(f"🔴 {fmt_range(r, d)} · {fmt_dur(r['end'] - r['start'])}")
        else:
            lines.append(f"🟡 {fmt_range(r, d)} · можливе відключення")
    total = sum((r["end"] - r["start"] for r in outages if r["state"] == OFF), timedelta())
    if total and len([r for r in outages if r["state"] == OFF]) > 1:
        lines.append(f"Разом без світла: {fmt_dur(total)}")
    return lines


def day_block(t: dict, slots: str | None, d: date) -> str:
    return "\n".join([target_title(t)] + day_lines(slots, d))


def short_day(slots: str, d: date) -> str:
    outages = [r for r in runs(timeline({d.isoformat(): slots}, [d])) if r["state"] != ON]
    if not outages:
        return "без відключень"
    return ", ".join(fmt_range(r, d) + ("?" if r["state"] == MAYBE else "") for r in outages)


def day_message(cfg: dict, state: dict, d: date, today: date, header: str | None = None) -> str:
    head = header or f"📅 <b>Графік на {fmt_date(d, today)}</b>"
    blocks = [day_block(t, state["schedules"].get(t["key"], {}).get(d.isoformat()), d) for t in cfg["targets"]]
    return "\n\n".join([head] + blocks)


def now_message(cfg: dict, state: dict, now: datetime) -> str:
    today = now.date()
    blocks = []
    for t in cfg["targets"]:
        sched = state["schedules"].get(t["key"], {})
        rs = runs(timeline(sched, [today, today + timedelta(days=1)]))
        cur = next((r for r in rs if r["start"] <= now < r["end"]), None)
        if cur is None:
            line = "⏳ графік на зараз невідомий"
        else:
            known_end = cur["next"] is not None
            until = f"до {fmt_clock(cur['end'])}" if known_end else "до кінця опублікованого графіка"
            if cur["state"] == ON:
                line = f"🟢 за графіком світло є {until}"
                if known_end:
                    line += f" (ще {fmt_dur(cur['end'] - now)})"
            elif cur["state"] == OFF:
                line = f"🔴 за графіком світла немає {until}"
                if known_end:
                    line += f" (ще {fmt_dur(cur['end'] - now)})"
            else:
                line = f"🟡 можливе відключення {until}"
        blocks.append(f"{target_title(t)}\n{line}")
    return "\n\n".join([f"🕐 <b>Зараз, {now.strftime('%H:%M')}</b>"] + blocks)


# --------------------------------------------------------------------- Telegram

class Telegram:
    def __init__(self, token: str, chat_ids: list, dry_run: bool = False):
        self.token, self.chat_ids, self.dry_run = token, chat_ids, dry_run
        self.base = os.environ.get("TELEGRAM_API_BASE", "https://api.telegram.org").rstrip("/")

    def call(self, method: str, payload: dict, timeout: int = 30):
        req = urllib.request.Request(
            f"{self.base}/bot{self.token}/{method}",
            data=json.dumps(payload).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        for attempt in (1, 2):
            try:
                with urllib.request.urlopen(req, timeout=timeout) as resp:
                    return json.loads(resp.read().decode("utf-8")).get("result")
            except urllib.error.HTTPError as e:
                body = {}
                try:
                    body = json.loads(e.read().decode("utf-8"))
                except Exception:
                    pass
                wait = (body.get("parameters") or {}).get("retry_after")
                if e.code == 429 and wait and attempt == 1:
                    time.sleep(min(int(wait) + 1, 30))
                    continue
                raise RuntimeError(f"Telegram {method}: {e.code} {body.get('description', '')}".strip()) from None
            except (urllib.error.URLError, TimeoutError, OSError) as e:
                # текст помилки не містить адресу запиту, тож токен у журнал не потрапляє
                raise RuntimeError(f"Telegram {method}: {getattr(e, 'reason', e)}") from None

    def send_to(self, chat_id: int, text: str, silent: bool = False) -> bool:
        if self.dry_run:
            print(f"--- повідомлення{' (без звуку)' if silent else ''} ---\n{text}\n")
            return True
        try:
            self.call("sendMessage", {
                "chat_id": chat_id, "text": text, "parse_mode": "HTML",
                "disable_notification": silent, "disable_web_page_preview": True,
            })
            return True
        except RuntimeError as e:
            log.warning("%s", e)
            return False

    def send(self, text: str, silent: bool = False) -> bool:
        """Надсилає всім отримувачам; True, якщо дійшло хоча б одному."""
        if self.dry_run:
            return self.send_to(0, text, silent)
        return any([self.send_to(c, text, silent) for c in self.chat_ids])


HELP = (
    "💡 <b>Бот графіків відключень</b>\n\n"
    "/now — що зараз за графіком\n"
    "/today — графік на сьогодні\n"
    "/tomorrow — графік на завтра\n"
    "/id — показати chat_id цього чату\n\n"
    "Сам надсилаю графік на день, зміни графіка та нагадування перед відключенням."
)
COMMANDS = [
    {"command": "now", "description": "Що зараз за графіком"},
    {"command": "today", "description": "Графік на сьогодні"},
    {"command": "tomorrow", "description": "Графік на завтра"},
]


def handle_updates(cfg: dict, state: dict, tg: Telegram, now: datetime, timeout: int) -> bool:
    """Відповідає на команди. Повертає True, якщо стан змінився."""
    payload = {"timeout": timeout, "allowed_updates": ["message"]}
    if state.get("tg_offset"):
        payload["offset"] = state["tg_offset"]
    updates = tg.call("getUpdates", payload, timeout=timeout + 15) or []
    today = now.date()
    for u in updates:
        state["tg_offset"] = u["update_id"] + 1
        msg = u.get("message") or {}
        text = (msg.get("text") or "").strip()
        chat_id = (msg.get("chat") or {}).get("id")
        if chat_id is None or not text.startswith("/"):
            continue
        cmd = text.split()[0].split("@")[0].lower()
        if chat_id not in cfg["chat_ids"]:
            if cmd in ("/start", "/id"):
                tg.send_to(chat_id, (
                    f"Ваш chat_id: <code>{chat_id}</code>\n\n"
                    "Щоб отримувати сповіщення, додайте це число до <code>chat_ids</code> "
                    "у налаштуваннях бота і перезапустіть його."
                ))
            continue
        if cmd in ("/start", "/help"):
            tg.send_to(chat_id, HELP)
        elif cmd == "/id":
            tg.send_to(chat_id, f"chat_id: <code>{chat_id}</code>")
        elif cmd == "/now":
            tg.send_to(chat_id, now_message(cfg, state, now))
        elif cmd == "/today":
            tg.send_to(chat_id, day_message(cfg, state, today, today))
        elif cmd == "/tomorrow":
            tg.send_to(chat_id, day_message(cfg, state, today + timedelta(days=1), today))
    return bool(updates)


# --------------------------------------------------------------- основна перевірка

def is_quiet(cfg: dict, now: datetime) -> bool:
    q = cfg.get("quiet_hours")
    if not q:
        return False
    start, end, t = q[0], q[1], now.time()
    return start <= t < end if start <= end else (t >= start or t < end)


def check(cfg: dict, state: dict, tg: Telegram, now_aware: datetime, fetch=fetch_region) -> None:
    now = now_aware.replace(tzinfo=None)          # графік живе в київському «настінному» часі
    today, tomorrow = now.date(), now.date() + timedelta(days=1)
    silent = is_quiet(cfg, now)
    first_run = not state.get("initialized")
    schedules = state["schedules"]

    # 1. свіжі дані з джерела
    data = {}
    for region in sorted({t["region"] for t in cfg["targets"]}):
        src = state["source"].setdefault(region, {})
        try:
            data[region] = fetch(cfg["data_url"], region)
            if data[region]["last_updated"]:
                src["last_updated"] = data[region]["last_updated"].astimezone(timezone.utc).isoformat()
        except Exception as e:  # мережа, 404, зіпсований JSON — працюємо далі зі збереженим графіком
            log.warning("не вдалося отримати дані регіону %s: %s", region, e)
        src.setdefault("last_updated", now_aware.astimezone(timezone.utc).isoformat())

    # 2. порівняння з тим, що вже відомо
    changes: dict = {}
    for t in cfg["targets"]:
        stored = schedules.setdefault(t["key"], {})
        days = (data.get(t["region"]) or {}).get("days", {})
        for d in (today, tomorrow):
            new = (days.get(d) or {}).get(t["group"])
            if new is None:
                continue
            old = stored.get(d.isoformat())
            if first_run:
                stored[d.isoformat()] = new
            elif old is None:
                changes.setdefault(("new", d), []).append((t, old, new))
            else:
                # зміни в годинах, що вже минули, нікому не цікаві
                cut = int((now - datetime.combine(today, dtime())) / HALF_HOUR) if d == today else 0
                if old[cut:] == new[cut:]:
                    stored[d.isoformat()] = new
                else:
                    changes.setdefault(("changed", d), []).append((t, old, new))

    # 3. перший запуск: привітання і все, що відомо
    if first_run:
        parts = ["✅ <b>Бот запущено.</b> Стежу за адресами нижче.", day_message(cfg, state, today, today)]
        if any(tomorrow.isoformat() in schedules.get(t["key"], {}) for t in cfg["targets"]):
            parts.append(day_message(cfg, state, tomorrow, today))
        if tg.send("\n\n".join(parts), silent):
            state["initialized"] = True
            state["digest_date"] = today.isoformat()
        first_run = not state.get("initialized")

    # 4. новий або змінений графік
    for (kind, d), items in sorted(changes.items(), key=lambda kv: (kv[0][1], kv[0][0])):
        if kind == "new":
            head = f"🗓 <b>З'явився графік на {fmt_date(d, today)}</b>"
        else:
            head = f"🔄 <b>Графік змінено — {fmt_date(d, today)}</b>"
        blocks = []
        for t, old, new in items:
            block = day_block(t, new, d)
            if old:
                block += f"\nБуло: {short_day(old, d)}"
            blocks.append(block)
        if tg.send("\n\n".join([head] + blocks), silent):
            for t, _old, new in items:
                schedules[t["key"]][d.isoformat()] = new

    # 5. графік на день
    digest_time = cfg.get("digest_time")
    if digest_time and not first_run and state.get("digest_date") != today.isoformat():
        due = datetime.combine(today, digest_time)
        if due <= now < due + timedelta(hours=12):
            if tg.send(day_message(cfg, state, today, today), silent):
                state["digest_date"] = today.isoformat()
        elif now >= due + timedelta(hours=12):
            state["digest_date"] = today.isoformat()

    # 6. нагадування
    off_min, on_min = int(cfg["remind_before_off_min"] or 0), int(cfg["remind_before_on_min"] or 0)
    if not first_run:
        for t in cfg["targets"]:
            name = f"<b>{html.escape(t['name'])}</b>"
            for r in runs(timeline(schedules.get(t["key"], {}), [today, tomorrow])):
                left = r["start"] - now
                if off_min and r["state"] != ON and r["prev"] == ON and timedelta(0) < left <= timedelta(minutes=off_min):
                    key = f"{t['key']}|off|{r['start'].isoformat()}"
                    if key not in state["reminded"]:
                        mins = math.ceil(left.total_seconds() / 60)
                        span = fmt_range(r) if r["next"] is not None else f"з {fmt_clock(r['start'])}, щонайменше до {fmt_clock(r['end'], r['start'].date())}"
                        if r["state"] == OFF:
                            text = f"⚠️ {name}: через {mins} хв відключення\n🔴 {span} · {fmt_dur(r['end'] - r['start'])}"
                        else:
                            text = f"🟡 {name}: через {mins} хв можливе відключення\n{span}"
                        if tg.send(text, silent):
                            state["reminded"].append(key)
                left = r["end"] - now
                if on_min and r["state"] == OFF and r["next"] == ON and timedelta(0) < left <= timedelta(minutes=on_min):
                    key = f"{t['key']}|on|{r['end'].isoformat()}"
                    if key not in state["reminded"]:
                        mins = math.ceil(left.total_seconds() / 60)
                        if tg.send(f"💡 {name}: за графіком світло увімкнуть через {mins} хв, о {fmt_clock(r['end'])}", silent):
                            state["reminded"].append(key)

    # 7. джерело перестало оновлюватися
    now_utc = now_aware.astimezone(timezone.utc)
    stale = []
    for region in sorted({t["region"] for t in cfg["targets"]}):
        src = state["source"][region]
        try:
            age = now_utc - datetime.fromisoformat(src["last_updated"])
        except (KeyError, ValueError):
            continue
        if age <= timedelta(hours=float(cfg["stale_hours"])):
            src["warned"] = False
        elif not src.get("warned"):
            stale.append((region, age))
    if stale and not first_run:
        names = ", ".join(html.escape(t["name"]) for t in cfg["targets"] if t["region"] in dict(stale))
        if tg.send(f"❗ Дані про графік не оновлюються вже {fmt_dur(max(a for _, a in stale))} ({names}). "
                   "Графік у боті може бути застарілим — перевірте на сайті ДТЕК.", silent):
            for region, _age in stale:
                state["source"][region]["warned"] = True

    # 8. прибирання старого
    keep_from = (today - timedelta(days=1)).isoformat()
    for stored in schedules.values():
        for k in [k for k in stored if k < keep_from]:
            del stored[k]
    limit = (now - timedelta(days=1)).isoformat()
    state["reminded"] = [k for k in state["reminded"] if k.rsplit("|", 1)[-1] >= limit]


# ------------------------------------------------------------------------ запуск

def main(argv=None) -> int:
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(description="Сповіщення про графіки відключень світла")
    ap.add_argument("--config", default=os.path.join(here, "config.json"))
    ap.add_argument("--state", default=os.path.join(here, "state.json"))
    ap.add_argument("--once", action="store_true", help="одна перевірка і вихід (для cron / GitHub Actions)")
    ap.add_argument("--dry-run", action="store_true", help="друкувати повідомлення замість надсилання")
    ap.add_argument("--now", help="підставити час для перевірки, напр. 2026-10-08T14:35")
    args = ap.parse_args(argv)
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")

    try:
        cfg = load_config(args.config)
    except ConfigError as e:
        print(f"Помилка налаштувань: {e}", file=sys.stderr)
        return 2
    if not args.dry_run and not cfg["telegram_token"]:
        print("Помилка налаштувань: не вказано токен бота (telegram_token або TELEGRAM_BOT_TOKEN).", file=sys.stderr)
        return 2

    tg = Telegram(cfg["telegram_token"], cfg["chat_ids"], dry_run=args.dry_run)
    state = load_state(args.state)

    def clock() -> datetime:
        return datetime.fromisoformat(args.now).replace(tzinfo=KYIV) if args.now else now_kyiv()

    def do_check() -> None:
        if not cfg["chat_ids"] and not args.dry_run:
            log.warning("chat_ids порожній: надішліть боту /start, щоб дізнатися свій chat_id")
            return
        try:
            check(cfg, state, tg, clock())
        except Exception:
            log.exception("перевірка графіка завершилася помилкою")

    def do_updates(timeout: int) -> None:
        if args.dry_run:
            return
        if handle_updates(cfg, state, tg, clock().replace(tzinfo=None), timeout):
            save_state(args.state, state)

    if args.once:
        try:
            do_updates(0)
        except RuntimeError as e:
            log.warning("%s", e)
        do_check()
        save_state(args.state, state)
        log.info("перевірку завершено")
        return 0

    log.info("бот запущено: адрес — %d, отримувачів — %d", len(cfg["targets"]), len(cfg["chat_ids"]))
    if not args.dry_run:
        try:
            tg.call("setMyCommands", {"commands": COMMANDS})
        except RuntimeError as e:
            log.warning("%s", e)
    last_check = None
    while True:
        if last_check is None or time.monotonic() - last_check >= cfg["poll_seconds"]:
            do_check()
            save_state(args.state, state)
            last_check = time.monotonic()
        try:
            if args.dry_run:
                time.sleep(min(cfg["poll_seconds"], 30))
            else:
                do_updates(25)   # довге опитування заодно слугує паузою між перевірками
        except RuntimeError as e:
            log.warning("%s", e)
            time.sleep(15)
        except KeyboardInterrupt:
            return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(0)
