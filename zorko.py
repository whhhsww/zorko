#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Zorko: ищет заведения, которым нужен сайт, по открытым данным OpenStreetMap.

Запуск: python zorko.py  (или двойной щелчок по start_zorko.bat)
Окно программы откроется в браузере по адресу http://127.0.0.1:8765
Нужен только Python 3.8 и новее, сторонние пакеты не используются.

Как Zorko решает, есть ли у заведения сайт:
  1. смотрит адрес сайта в карте (его там часто нет, даже если сайт существует);
  2. ищет сайт сам: по домену из почты, по такому же заведению рядом,
     по Wikidata и подбором домена из названия;
  3. найденный сайт проверяет и показывает его проблемы.
"""
import csv
import datetime
import hashlib
import html as html_lib
import io
import ipaddress
import json
import math
import os
import queue
import re
import socket
import sqlite3
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HOST = "127.0.0.1"
PORT = int(os.environ.get("ZORKO_PORT", "8765"))
BASE = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.environ.get("ZORKO_DB", os.path.join(BASE, "zorko.db"))
UA = "Zorko/0.3 (desktop lead finder; data from OpenStreetMap)"
NOMINATIM = "https://nominatim.openstreetmap.org/search"
WIKIDATA = "https://www.wikidata.org/wiki/Special:EntityData/%s.json"
# Только зеркала с данными по всему миру. Региональные (например overpass.osm.ch,
# где есть одна Швейцария) сюда добавлять нельзя: по другим странам они молча вернут пусто.
OVERPASS = [
    "https://overpass-api.de/api/interpreter",
    "https://overpass.kumi.systems/api/interpreter",
    "https://overpass.private.coffee/api/interpreter",
]
OVERPASS_NEXT = [0]        # зеркало, которое ответило в прошлый раз: с него и начинаем
MAX_CELLS = 400            # больше квадратов за один поиск не делаем
MAX_SIDE_KM = 150          # защита от поиска по целой области или стране
MAX_CITIES = 5             # городов за один поиск
MAX_SPLITS = 3             # на сколько уровней можно делить город, если запрос не прошёл
WORKERS = max(1, min(24, int(os.environ.get("ZORKO_WORKERS", "12"))))  # сколько сайтов проверяем разом
INSTAGRAM_PAUSE = 1.3      # секунд между обращениями к Instagram, чтобы он нас не закрыл
INSTAGRAM_LIMIT = 300      # для скольких заведений за раз ищем аккаунт в Instagram
BROWSER_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36")
# Украинские города в латинице пишут и так, и так: для подбора имени аккаунта нужны оба варианта.
CITY_ALIASES = {"kyev": "kyiv", "kiev": "kyiv", "lvov": "lviv", "kharkov": "kharkiv",
                "kharkyv": "kharkiv", "odessa": "odesa", "odesa": "odessa", "dnepr": "dnipro",
                "nykolaev": "mykolaiv", "nikolaev": "mykolaiv", "chernyhov": "chernihiv",
                "vynnytsa": "vinnytsia", "vinnitsa": "vinnytsia", "zaporozhe": "zaporizhzhia",
                "rovno": "rivne", "ternopol": "ternopil", "lutsk": "lutsk", "uzhhorod": "uzhgorod"}
PAUSE_BETWEEN_CELLS = 1.0  # секунд, чтобы не перегружать бесплатный сервер карт
HEDGE_SECONDS = 25         # сколько ждём молчащее зеркало, прежде чем спросить соседнее
NO_MAP = ("Серверы карт не отвечают. Чаще всего это значит, что после большого поиска "
          "они на время ограничили ваш адрес, либо мешает VPN. Подождите 10–15 минут, "
          "выключите VPN и попробуйте снова. Кнопка «Проверить связь» покажет, какие серверы живы.")
DUPLICATE_METERS = 60      # одно и то же название ближе этого расстояния считаем дублем

CATEGORIES = [
    ("food", "Кафе, рестораны, пекарни", [
        '["amenity"~"^(cafe|restaurant|fast_food|bar|pub|ice_cream|food_court|biergarten)$"]',
        '["shop"~"^(bakery|pastry|confectionery|coffee|tea|deli|butcher|greengrocer|alcohol|beverages|seafood|cheese|chocolate)$"]']),
    ("beauty", "Красота и барбершопы", [
        '["shop"~"^(hairdresser|beauty|cosmetics|massage|tattoo|nails|perfumery)$"]',
        '["leisure"="sauna"]', '["amenity"="spa"]']),
    ("auto", "Авто: сервис, мойка, шины", [
        '["shop"~"^(car_repair|tyres|car_parts|car|motorcycle|bicycle)$"]',
        '["amenity"~"^(car_wash|driving_school)$"]']),
    ("med", "Медицина и ветеринары", [
        '["amenity"~"^(dentist|clinic|doctors|veterinary|pharmacy)$"]',
        '["healthcare"~"^(dentist|clinic|doctor|physiotherapist|laboratory|optometrist)$"]',
        '["shop"~"^(optician|hearing_aids|medical_supply)$"]']),
    ("stay", "Гостиницы и аренда", [
        '["tourism"~"^(hotel|guest_house|hostel|motel|apartment|chalet)$"]']),
    ("sport", "Спорт и фитнес", [
        '["leisure"~"^(fitness_centre|sports_centre|dance|horse_riding|bowling_alley|climbing)$"]',
        '["shop"~"^(sports|bicycle|fishing|outdoor)$"]']),
    ("edu", "Курсы, школы, садики", [
        '["amenity"~"^(language_school|music_school|prep_school|kindergarten|college|childcare)$"]',
        '["office"="educational_institution"]']),
    ("service", "Услуги и ремонт", [
        '["shop"~"^(laundry|dry_cleaning|shoe_repair|locksmith|photo|travel_agency|florist|funeral_directors|tailor|jewelry|watches|copyshop|printing|pet_grooming|storage_rental|rental)$"]',
        '["craft"]', '["amenity"="veterinary_pharmacy"]']),
    ("office", "Офисы и агентства", [
        '["office"~"^(estate_agent|lawyer|accountant|insurance|advertising_agency|it|architect|company|employment_agency|travel_agent|notary|financial)$"]']),
    ("shops", "Магазины (всё остальное)", ['["shop"]']),
]
KIND_RU = {
    "cafe": "кафе", "restaurant": "ресторан", "fast_food": "фастфуд", "bar": "бар", "pub": "паб",
    "biergarten": "пивная", "ice_cream": "мороженое", "food_court": "фуд-корт", "bakery": "пекарня",
    "pastry": "кондитерская", "confectionery": "кондитерская", "coffee": "кофе", "tea": "чай",
    "deli": "деликатесы", "butcher": "мясная лавка", "greengrocer": "овощи и фрукты",
    "alcohol": "алкоголь", "beverages": "напитки", "seafood": "рыба и морепродукты", "cheese": "сыры",
    "chocolate": "шоколад", "hairdresser": "парикмахерская", "beauty": "салон красоты",
    "cosmetics": "косметика", "massage": "массаж", "tattoo": "тату-салон", "nails": "ногтевая студия",
    "perfumery": "парфюмерия", "sauna": "сауна", "spa": "спа", "car_repair": "автосервис",
    "tyres": "шиномонтаж", "car_parts": "автозапчасти", "car": "автосалон", "motorcycle": "мотосалон",
    "bicycle": "велосипеды", "car_wash": "автомойка", "driving_school": "автошкола",
    "dentist": "стоматология", "clinic": "клиника", "doctors": "врач", "veterinary": "ветклиника",
    "pharmacy": "аптека", "physiotherapist": "физиотерапия", "laboratory": "лаборатория",
    "optometrist": "оптометрист", "optician": "оптика", "hearing_aids": "слуховые аппараты",
    "medical_supply": "медтехника", "hotel": "гостиница", "guest_house": "гостевой дом",
    "hostel": "хостел", "motel": "мотель", "apartment": "апартаменты", "chalet": "домик",
    "fitness_centre": "фитнес", "sports_centre": "спорткомплекс", "dance": "танцы",
    "horse_riding": "конный клуб", "bowling_alley": "боулинг", "climbing": "скалодром",
    "sports": "спорттовары", "fishing": "рыбалка", "outdoor": "туризм",
    "language_school": "языковая школа", "music_school": "музыкальная школа",
    "prep_school": "курсы", "kindergarten": "детский сад", "college": "колледж",
    "childcare": "детский центр", "educational_institution": "учебный центр",
    "laundry": "прачечная", "dry_cleaning": "химчистка", "shoe_repair": "ремонт обуви",
    "locksmith": "ключи и замки", "photo": "фотостудия", "travel_agency": "турагентство",
    "florist": "цветы", "funeral_directors": "ритуальные услуги", "tailor": "ателье",
    "jewelry": "ювелирный", "watches": "часы", "copyshop": "копицентр", "printing": "типография",
    "pet_grooming": "груминг", "storage_rental": "склады", "rental": "прокат",
    "estate_agent": "недвижимость", "lawyer": "юрист", "accountant": "бухгалтер",
    "insurance": "страхование", "advertising_agency": "реклама", "it": "IT-компания",
    "architect": "архитектор", "company": "компания", "employment_agency": "кадровое агентство",
    "travel_agent": "турагент", "notary": "нотариус", "financial": "финансы",
}
STATUSES = [("new", "Новый"), ("written", "Написал"), ("replied", "Ответил"), ("refused", "Отказ")]
SITE_STATES = {"none": "нет сайта", "social": "только соцсеть", "found": "сайт нашёлся", "site": "есть сайт"}
SOCIAL_HOSTS = ("instagram.com", "facebook.com", "fb.com", "fb.me", "t.me", "telegram.me", "vk.com",
                "tiktok.com", "linktr.ee", "taplink.cc", "youtube.com", "wa.me", "ok.ru", "pinterest.com",
                "x.com", "twitter.com", "linkedin.com")
FREE_MAIL = ("gmail.com", "googlemail.com", "ukr.net", "meta.ua", "i.ua", "mail.ru", "inbox.ru",
             "list.ru", "bk.ru", "yandex.ru", "yandex.ua", "ya.ru", "outlook.com", "hotmail.com",
             "live.com", "yahoo.com", "icloud.com", "me.com", "proton.me", "protonmail.com",
             "bigmir.net", "rambler.ru", "qip.ru", "email.ua", "3g.ua")
BUILDERS = {
    "Tilda": ("tildacdn", "tilda.ws", "tilda.cc"),
    "Wix": ("wixstatic.com", "wix.com", "_wixcssimports"),
    "uCoz": ("ucoz.",),
    "Weebly": ("weebly.com",),
    "Squarespace": ("squarespace",),
    "Google Sites": ("sites.google.com",),
    "Nethouse": ("nethouse.",),
    "WordPress": ("/wp-content/", "wp-includes"),
    "Joomla": ("/media/jui/", "joomla"),
}
PARKED = ("domain is for sale", "this domain", "купить домен", "домен продается", "домен продається",
          "parked", "buy this domain", "domain for sale", "срок регистрации домена",
          "website coming soon", "сайт в разработке", "under construction")
# Слова, по которым домен не угадать: в названии они есть почти у всех.
STOP_WORDS = {
    "кафе", "кофейня", "кавярня", "кав'ярня", "кофе", "кава", "ресторан", "ресторация",
    "ресторація", "бар", "паб", "пекарня", "кондитерская", "кондитерська", "пиццерия", "піцерія",
    "піца", "пицца", "суши", "суші", "бистро", "бістро", "столовая", "їдальня", "лавка", "бутик",
    "салон", "краси", "красоты", "барбершоп", "перукарня", "парикмахерская", "студия", "студія",
    "магазин", "маркет", "крамниця", "готель", "гостиница", "отель", "хостел", "аптека", "оптика",
    "клиника", "клініка", "стоматология", "стоматологія", "медцентр", "центр", "сервис", "сервіс",
    "авто", "автосервис", "автосервіс", "автомойка", "автомийка", "шиномонтаж", "мойка", "мийка",
    "фитнес", "фітнес", "клуб", "спа", "студио", "ателье", "ательє", "тов", "фоп", "пп",
    "мебель", "меблі", "продукты", "продукти", "цветы", "квіти", "сто", "груп", "груп­па", "group",
    "the", "cafe", "coffee", "bar", "pub", "restaurant", "pizza", "sushi", "shop", "store",
    "market", "hotel", "hostel", "salon", "studio", "club", "beauty", "barbershop", "fitness",
    "service", "auto", "and", "для", "дом", "дім",
}
TRANSLIT = {
    "а": "a", "б": "b", "в": "v", "г": "h", "ґ": "g", "д": "d", "е": "e", "є": "ie", "ё": "e",
    "ж": "zh", "з": "z", "и": "y", "і": "i", "ї": "i", "й": "i", "к": "k", "л": "l", "м": "m",
    "н": "n", "о": "o", "п": "p", "р": "r", "с": "s", "т": "t", "у": "u", "ф": "f", "х": "kh",
    "ц": "ts", "ч": "ch", "ш": "sh", "щ": "shch", "ъ": "", "ы": "y", "ь": "", "э": "e",
    "ю": "iu", "я": "ia",
}

DB_LOCK = threading.Lock()
JOB_LOCK = threading.Lock()
JOB = {"running": False, "kind": "", "done": 0, "total": 0, "found": 0, "added": 0,
       "msg": "", "error": "", "stop": False, "token": 0, "started": 0.0}
REV = [0]  # растёт при каждом изменении базы, чтобы окно знало, когда перечитать список


# ---------- база ----------

def db():
    con = sqlite3.connect(DB_PATH, timeout=30)
    con.row_factory = sqlite3.Row
    return con


COLUMNS = [
    ("name", "TEXT"), ("kind", "TEXT"), ("lat", "REAL"), ("lon", "REAL"), ("address", "TEXT"),
    ("city", "TEXT"), ("phone", "TEXT"), ("email", "TEXT"), ("website", "TEXT"), ("socials", "TEXT"),
    ("hours", "TEXT"), ("chain", "INTEGER DEFAULT 0"), ("site_state", "TEXT"),
    ("issues", "TEXT DEFAULT '[]'"), ("checked_at", "TEXT"), ("score", "INTEGER DEFAULT 0"),
    ("status", "TEXT DEFAULT 'new'"), ("note", "TEXT DEFAULT ''"), ("found_at", "TEXT"),
    # добавлено в версии 0.3
    ("found_site", "TEXT DEFAULT ''"), ("found_how", "TEXT DEFAULT ''"), ("searched_at", "TEXT"),
    ("wikidata", "TEXT DEFAULT ''"), ("cc", "TEXT DEFAULT ''"), ("hidden", "INTEGER DEFAULT 0"),
    ("instagram", "TEXT DEFAULT ''"), ("insta_at", "TEXT"),
    ("hidden_why", "TEXT DEFAULT ''"),
]


def init_db():
    """Создаёт базу, а в старой базе добавляет новые столбцы, не трогая найденное."""
    with DB_LOCK, db() as con:
        con.execute("CREATE TABLE IF NOT EXISTS places(id TEXT PRIMARY KEY)")
        con.execute("CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT)")
        have = {r["name"] for r in con.execute("PRAGMA table_info(places)")}
        for col, decl in COLUMNS:
            if col not in have:
                con.execute("ALTER TABLE places ADD COLUMN %s %s" % (col, decl))
        con.execute("CREATE INDEX IF NOT EXISTS places_state ON places(site_state)")


def get_settings():
    with db() as con:
        return {r["key"]: r["value"] for r in con.execute("SELECT key, value FROM settings")}


def bump():
    REV[0] += 1


# ---------- сеть ----------

def http_get(url, data=None, timeout=60):
    req = urllib.request.Request(url, data=data, headers={"User-Agent": UA, "Accept-Language": "ru,uk,en"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read()


def geocode(city):
    """Город -> (название, код страны, юг, север, запад, восток)."""
    qs = urllib.parse.urlencode({"q": city, "format": "jsonv2", "limit": 5,
                                 "accept-language": "uk,ru,en", "addressdetails": 1})
    items = json.loads(http_get(NOMINATIM + "?" + qs, timeout=30).decode("utf-8"))
    if not items:
        raise ValueError("Город «%s» не найден. Проверьте написание." % city)
    good = ("city", "town", "village", "hamlet", "municipality", "administrative", "suburb", "borough")
    item = next((i for i in items if i.get("type") in good or i.get("addresstype") in good), items[0])
    s, n, w, e = [float(x) for x in item["boundingbox"]]
    side = max((n - s) * 111.0, (e - w) * 111.0 * math.cos(math.radians((s + n) / 2)))
    if side > MAX_SIDE_KM:
        raise ValueError("«%s» — слишком большая область (%d км). Укажите город или район." % (city, side))
    cc = ((item.get("address") or {}).get("country_code") or "").lower()
    return item.get("display_name", city).split(",")[0].strip(), cc, s, n, w, e


def make_cells(s, n, w, e, km):
    """Режет область на квадраты примерно km x km, ближние к центру идут первыми."""
    km = max(0.5, float(km))
    while True:
        lat_step = km / 111.0
        lon_step = km / (111.0 * max(0.2, math.cos(math.radians((s + n) / 2))))
        rows = max(1, math.ceil((n - s) / lat_step))
        cols = max(1, math.ceil((e - w) / lon_step))
        if rows * cols <= MAX_CELLS:
            break
        km *= 1.25
    cells = []
    for i in range(rows):
        for j in range(cols):
            cells.append((s + i * lat_step, w + j * lon_step,
                          min(n, s + (i + 1) * lat_step), min(e, w + (j + 1) * lon_step)))
    cy, cx = (s + n) / 2, (w + e) / 2
    cells.sort(key=lambda c: ((c[0] + c[2]) / 2 - cy) ** 2 + ((c[1] + c[3]) / 2 - cx) ** 2)
    return cells


def overpass(filters, s, w, n, e, alive=lambda: True, attempts=2, timeout=120, server_timeout=180,
             hedge=None):
    """Один запрос к серверу карт. Если зеркало молчит дольше hedge секунд, параллельно
    спрашиваем соседнее и берём тот ответ, который придёт первым: так одно зависшее
    зеркало больше не держит весь поиск."""
    hedge = HEDGE_SECONDS if hedge is None else hedge
    parts = "".join("nwr%s(%.6f,%.6f,%.6f,%.6f);" % (f, s, w, n, e) for f in filters)
    query = "[out:json][timeout:%d];(" % server_timeout + parts + ");out center tags;"
    body = urllib.parse.urlencode({"data": query}).encode("utf-8")
    tries = max(1, min(attempts, len(OVERPASS)))
    answers = queue.Queue()
    state = {"started": 0, "last_start": 0.0}

    def ask(index):
        try:
            answers.put(("ok", index, http_get(OVERPASS[index], data=body, timeout=timeout)))
        except Exception as err:
            answers.put(("err", index, err))

    def start_next():
        index = (OVERPASS_NEXT[0] + state["started"]) % len(OVERPASS)
        state["started"] += 1
        state["last_start"] = time.time()
        threading.Thread(target=ask, args=(index,), daemon=True).start()

    start_next()
    failed, last = 0, None
    while failed < tries:
        if not alive():
            raise RuntimeError("stopped")
        try:
            kind, index, payload = answers.get(timeout=0.5)
        except queue.Empty:
            if state["started"] < tries and time.time() - state["last_start"] > hedge:
                start_next()
            continue
        if kind == "ok":
            try:
                elements = json.loads(payload.decode("utf-8")).get("elements", [])
                OVERPASS_NEXT[0] = index  # это зеркало работает, с него и начнём в следующий раз
                return elements
            except ValueError as err:
                last, failed = err, failed + 1
        else:
            last, failed = payload, failed + 1
            if state["started"] < tries:
                start_next()
    raise RuntimeError("сервер карт не ответил: %s" % last)


def split_box(box):
    """Делит участок на четыре части."""
    s, w, n, e = box
    ms, mw = (s + n) / 2, (w + e) / 2
    return [(s, w, ms, mw), (s, mw, ms, e), (ms, w, n, mw), (ms, mw, n, e)]


def ping_servers(token=None):
    """Проверяет связь с сервером городов и со всеми зеркалами карты."""
    lines = []
    ok = False
    try:
        http_get(NOMINATIM + "?q=Lviv&format=jsonv2&limit=1", timeout=15)
        lines.append("поиск городов: отвечает")
    except Exception:
        lines.append("поиск городов: НЕ отвечает")
    INSTA_OFF[0] = ""
    try:
        got = instagram_name("instagram")
        lines.append("Instagram: %s" % ("профили читаются" if got else "страницы профилей не читаются"))
    except Exception:
        lines.append("Instagram: не отвечает")
    for index, url in enumerate(OVERPASS):
        host = urllib.parse.urlparse(url).hostname
        if token is not None:
            setj(token, msg="Проверяю %s" % host, done=index)
        start = time.time()
        try:
            overpass(['["amenity"="cafe"]'], 49.838, 24.028, 49.842, 24.034,
                     attempts=1, timeout=15, server_timeout=15)
            lines.append("%s: отвечает (%.0f с)" % (host, time.time() - start))
            ok = True
        except Exception:
            lines.append("%s: не отвечает" % host)
        if token is not None and not alive(token):
            return lines, ok
    return lines, ok


# ---------- разбор заведений ----------

def normalize_url(url):
    url = (url or "").strip()
    if url and not re.match(r"^https?://", url, re.I):
        url = "http://" + url
    return url


def host_of(url):
    return (urllib.parse.urlparse(normalize_url(url)).hostname or "").lower()


def is_social(url):
    host = host_of(url)
    return any(host == h or host.endswith("." + h) for h in SOCIAL_HOSTS)


def site_state(website):
    if not website:
        return "none"
    return "social" if is_social(website) else "site"


def normalize_name(name):
    """«Кофейня "Зерно"» и «кофейня зерно» -> один и тот же ключ."""
    return re.sub(r"[^0-9a-zа-яёіїєґ]+", "", (name or "").lower())


def meters(lat1, lon1, lat2, lon2):
    dy = (lat1 - lat2) * 111000.0
    dx = (lon1 - lon2) * 111000.0 * math.cos(math.radians((lat1 + lat2) / 2))
    return math.hypot(dx, dy)


def score_place(p):
    """Приоритет 0-100: выше те, кому сайт нужнее и с кем есть как связаться."""
    state = p.get("site_state") or "none"
    issues = p.get("issues") or []
    if isinstance(issues, str):
        issues = json.loads(issues or "[]")
    phone, email = p.get("phone"), p.get("email")
    socials = p.get("socials")
    if state == "none":
        score = 60
    elif state == "social":
        score = 45
    elif state == "found":
        score = 18 + min(12, 6 * len(issues))  # сайт есть, но мы его нашли сами
    else:
        score = 10 + min(25, 8 * len(issues))
    online = bool(email or socials or p.get("instagram") or state == "social")
    score += 25 if phone else 0
    score += 10 if online else 0
    score += 5 if p.get("address") else 0
    if not (phone or online):
        score -= 15  # написать некуда
    if p.get("chain"):
        score -= 40  # сетевым заведениям сайт делает головной офис
    return max(0, min(100, score))


def parse_element(el):
    tags = el.get("tags") or {}
    name = tags.get("name") or tags.get("name:ru") or tags.get("name:uk") or tags.get("name:en")
    lat = el.get("lat", (el.get("center") or {}).get("lat"))
    lon = el.get("lon", (el.get("center") or {}).get("lon"))
    if not name or lat is None or lon is None:
        return None
    kind = next((tags[k] for k in ("amenity", "shop", "tourism", "leisure", "healthcare", "office", "craft")
                 if tags.get(k)), "")
    street = " ".join(x for x in (tags.get("addr:street"), tags.get("addr:housenumber")) if x)
    website = ""
    for key in ("website", "contact:website", "url", "contact:url", "website:menu", "operator:website",
                "brand:website", "contact:webpage"):
        if tags.get(key):
            website = tags[key].split(";")[0].strip()
            break
    socials = []
    for key in ("instagram", "facebook", "telegram", "viber", "whatsapp", "vk", "tiktok", "youtube"):
        val = tags.get("contact:" + key) or tags.get(key)
        if val:
            socials.append("%s: %s" % (key, val.split(";")[0].strip()))
    phone = ""
    for key in ("phone", "contact:phone", "contact:mobile", "mobile", "phone:mobile"):
        if tags.get(key):
            phone = tags[key].strip()
            break
    email = (tags.get("email") or tags.get("contact:email") or "").split(";")[0].strip()
    insta = (tags.get("contact:instagram") or tags.get("instagram") or "").strip()
    qid = (tags.get("wikidata") or tags.get("brand:wikidata") or "").strip()
    return {
        "id": "%s/%s" % (el.get("type"), el.get("id")),
        "name": name.strip()[:160], "kind": KIND_RU.get(kind, kind), "lat": lat, "lon": lon,
        "address": street, "city": tags.get("addr:city", ""), "phone": phone, "email": email,
        "website": website, "socials": "; ".join(socials), "hours": tags.get("opening_hours", ""),
        "chain": 1 if (tags.get("brand") or tags.get("brand:wikidata")) else 0,
        "site_state": site_state(website),
        "instagram": instagram_handle(insta),
        "wikidata": qid if re.match(r"^Q\d+$", qid) else "",
    }


def save_places(elements, city, cc):
    """Сохраняет найденное. Статусы, заметки и найденные сайты у известных заведений не трогает."""
    added = 0
    now = datetime.datetime.now().isoformat(timespec="seconds")
    with DB_LOCK, db() as con:
        for el in elements:
            p = parse_element(el)
            if not p:
                continue
            p["city"] = p["city"] or city
            p["cc"] = cc
            old = con.execute("SELECT issues, website, found_site FROM places WHERE id=?", (p["id"],)).fetchone()
            if old is None:
                # дубль: то же название в пределах 150 метров (точка и здание отмечены дважды)
                dup = None
                for row in con.execute(
                        "SELECT id, name, lat, lon FROM places WHERE lat BETWEEN ? AND ? AND lon BETWEEN ? AND ?",
                        (p["lat"] - 0.003, p["lat"] + 0.003, p["lon"] - 0.005, p["lon"] + 0.005)):
                    if normalize_name(row["name"]) == normalize_name(p["name"]) and \
                            meters(p["lat"], p["lon"], row["lat"], row["lon"]) < DUPLICATE_METERS:
                        dup = row["id"]
                        break
                p["issues"] = "[]"
                p["score"] = score_place(p)
                p["hidden"] = 1 if dup else 0
                p["hidden_why"] = "дубль" if dup else ""
                added += 0 if dup else 1
                con.execute("""INSERT INTO places(id,name,kind,lat,lon,address,city,cc,phone,email,website,
                    socials,hours,chain,site_state,wikidata,instagram,issues,score,status,note,found_at,hidden,hidden_why)
                    VALUES(:id,:name,:kind,:lat,:lon,:address,:city,:cc,:phone,:email,:website,:socials,:hours,
                    :chain,:site_state,:wikidata,:instagram,:issues,:score,'new','',:found_at,:hidden,:hidden_why)""",
                            dict(p, found_at=now))
            else:
                if old["website"] != p["website"]:
                    con.execute("UPDATE places SET issues='[]', checked_at=NULL WHERE id=?", (p["id"],))
                    p["issues"] = []
                else:
                    p["issues"] = json.loads(old["issues"] or "[]")
                if not p["website"] and old["found_site"]:
                    p["site_state"] = "found"  # сайт, который мы нашли сами, остаётся
                p["score"] = score_place(p)
                con.execute("""UPDATE places SET name=:name,kind=:kind,lat=:lat,lon=:lon,address=:address,
                    city=:city,cc=:cc,phone=:phone,email=:email,website=:website,socials=:socials,hours=:hours,
                    chain=:chain,site_state=:site_state,wikidata=:wikidata,score=:score,
                    instagram=CASE WHEN :instagram<>'' THEN :instagram ELSE instagram END WHERE id=:id""",
                            dict(p, issues=json.dumps(p["issues"], ensure_ascii=False)))
    bump()
    return added


def mark_chains():
    """Если одно и то же название встречается 3+ раза, это сеть: сайт ей делает головной офис."""
    with DB_LOCK, db() as con:
        counts = {}
        for row in con.execute("SELECT id, name FROM places"):
            counts.setdefault(normalize_name(row["name"]), []).append(row["id"])
        for key, ids in counts.items():
            if len(ids) >= 3 and key:
                con.executemany("UPDATE places SET chain=1 WHERE id=? AND chain=0", [(i,) for i in ids])
    bump()


# ---------- открываем сайты ----------

def host_is_public(host):
    """True: обычный адрес в интернете. False: локальный адрес. None: домена не существует."""
    try:
        infos = socket.getaddrinfo(host, None)
    except (socket.gaierror, UnicodeError, OSError):
        return None
    for info in infos:
        ip = ipaddress.ip_address(info[4][0].split("%")[0])
        if ip.is_private or ip.is_loopback or ip.is_link_local or ip.is_reserved or ip.is_multicast:
            return False
    return True


class SafeRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        host = urllib.parse.urlparse(newurl).hostname or ""
        if host_is_public(host) is not True:
            raise urllib.error.URLError("redirect to non-public host")
        return super().redirect_request(req, fp, code, msg, headers, newurl)


def fetch_page(url, timeout=12):
    opener = urllib.request.build_opener(SafeRedirect)
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (compatible; Zorko/0.3)",
                                               "Accept-Language": "ru,uk,en"})
    with opener.open(req, timeout=timeout) as resp:
        raw = resp.read(400000)
        charset = resp.headers.get_content_charset() or "utf-8"
        try:
            html = raw.decode(charset, errors="ignore")
        except LookupError:
            html = raw.decode("utf-8", errors="ignore")
        return html, resp.geturl()


def page_text(html):
    text = re.sub(r"(?is)<(script|style|noscript)[^>]*>.*?</\1>", " ", html)
    return re.sub(r"\s+", " ", re.sub(r"(?s)<[^>]+>", " ", text)).strip().lower()


def open_domain(domain, timeout=8):
    """Пробует открыть домен. Возвращает (html, адрес) или (None, None)."""
    if host_is_public(domain) is not True:
        return None, None
    for scheme in ("https://", "http://"):
        try:
            return fetch_page(scheme + domain, timeout=timeout)
        except Exception:
            continue
    return None, None


def name_tokens(name):
    return [t for t in re.split(r"[^0-9a-zа-яёіїєґ]+", (name or "").lower())
            if len(t) > 3 and t not in STOP_WORDS]


def page_matches(html, name, phone):
    """Правда ли, что эта страница про это заведение."""
    text = page_text(html)
    if len(text) < 120 or any(w in text for w in PARKED):
        return ""
    digits = re.sub(r"\D", "", phone or "")
    if len(digits) >= 7 and digits[-7:] in re.sub(r"\D", "", text):
        return "телефон совпал"
    for token in name_tokens(name):
        if token in text:
            return "название совпало"
    return ""


TRANSLIT_ALT = dict(TRANSLIT, **{"я": "ya", "ю": "yu", "є": "ye", "ї": "yi", "и": "i",
                                 "й": "y", "г": "g", "х": "h"})


def translit(word, table=None):
    table = table or TRANSLIT
    return "".join(table.get(ch, ch if ch.isalnum() and ch.isascii() else "") for ch in word.lower())


def guess_domains(name, cc):
    """Домены, которые стоит попробовать для такого названия."""
    tokens = name_tokens(name) or [t for t in re.split(r"[^0-9a-zа-яёіїєґ]+", (name or "").lower()) if t]
    bases = []
    for token in tokens[:3]:
        word = translit(token)
        if 3 <= len(word) <= 24 and word not in bases:
            bases.append(word)
    if len(tokens) > 1:
        joined = translit(tokens[0]) + translit(tokens[1])
        if 5 <= len(joined) <= 24 and joined not in bases:
            bases.append(joined)
    tlds = {"ua": ["com.ua", "ua", "in.ua"], "pl": ["pl", "com.pl"], "ru": ["ru"],
            "de": ["de"], "cz": ["cz"], "sk": ["sk"], "ro": ["ro"], "md": ["md"]}.get(cc, [cc] if cc else [])
    out = []
    for tld in tlds + ["com"]:  # сначала домены своей страны, они вероятнее
        for base in bases:
            domain = base + "." + tld
            if tld and domain not in out:
                out.append(domain)
    return out[:8]


INSTA_LOCK = threading.Lock()
INSTA_LAST = [0.0]
INSTA_OFF = [""]  # если Instagram нас закрыл, пишем сюда причину и больше не стучимся


def instagram_handle(value):
    """Из «@kava_lviv» или ссылки делает просто kava_lviv."""
    v = (value or "").strip().split(";")[0].strip().strip("@")
    if "instagram.com" in v.lower():
        v = urllib.parse.urlparse(normalize_url(v)).path.strip("/").split("/")[0]
    v = v.strip().strip("@")
    return v if re.match(r"^[A-Za-z0-9._]{2,30}$", v) else ""


def instagram_name(handle):
    """Имя аккаунта, если такой профиль открыт. Читаем только заголовок страницы —
    ровно то, что видит обычный браузер, когда вы открываете профиль."""
    if INSTA_OFF[0] or not re.match(r"^[A-Za-z0-9._]{2,30}$", handle or ""):
        return ""
    with INSTA_LOCK:  # не чаще одного обращения в секунду с небольшим
        delay = INSTAGRAM_PAUSE - (time.time() - INSTA_LAST[0])
        if delay > 0:
            time.sleep(delay)
        INSTA_LAST[0] = time.time()
    req = urllib.request.Request(
        "https://www.instagram.com/%s/" % handle,
        headers={"User-Agent": BROWSER_UA, "Accept-Language": "uk,ru;q=0.9,en;q=0.8",
                 "Accept": "text/html,application/xhtml+xml"})
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            raw = resp.read(400000).decode("utf-8", errors="ignore")
    except urllib.error.HTTPError as err:
        if err.code in (401, 403, 429):
            INSTA_OFF[0] = "Instagram перестал отвечать на запросы с этого компьютера (ошибка %d)." % err.code
        return ""
    except Exception:
        return ""
    title = html_lib.unescape((re.search(r"<title[^>]*>([^<]{0,160})</title>", raw) or ["", ""])[1]).strip()
    if "(@" not in title:
        return ""  # профиля нет, либо Instagram показал общую страницу
    name, _, tail = title.partition("(@")
    if tail.split(")")[0].strip().lower() != handle.lower():
        return ""  # нас перебросило на другой профиль
    return name.strip() or handle


def same_business(name, display):
    """Правда ли, что аккаунт принадлежит этому заведению."""
    a, b = set(name_tokens(name)), set(name_tokens(display))
    if a & b:
        return True
    squeeze = lambda t: translit(re.sub(r"[^0-9a-zа-яёіїєґ]+", "", (t or "").lower()))
    x, y = squeeze(name), squeeze(display)
    return bool(x) and len(x) >= 4 and (x in y or y in x)


def guess_handles(name, city):
    """Какие имена аккаунтов стоит попробовать для такого названия."""
    raw = [t for t in re.split(r"[^0-9a-zа-яёіїєґ]+", (name or "").lower()) if len(t) > 2]
    tokens = name_tokens(name) or raw
    if not tokens:
        return []
    variants = []
    for table in (TRANSLIT, TRANSLIT_ALT):
        first = translit(tokens[0], table)[:28]
        if first and first not in variants:
            variants.append(first)
    if len(tokens) > 1:
        pair = ("".join(translit(t) for t in tokens[:2]))[:28]
        if pair not in variants:
            variants.append(pair)
    whole = "".join(translit(t) for t in raw)[:28]
    if len(raw) > len(tokens) and whole and whole not in variants:
        variants.append(whole)

    city_tokens = name_tokens(city) or [t for t in re.split(r"[^0-9a-zа-яёіїєґ]+", (city or "").lower()) if t]
    city_names = []
    if city_tokens:
        base = translit(city_tokens[0])[:20]
        for option in (CITY_ALIASES.get(base), base):  # местное написание чаще
            if option and option not in city_names:
                city_names.append(option)

    out = []
    for handle in variants + ["%s.%s" % (variants[0], c) for c in city_names] + \
                  ["%s_%s" % (variants[0], c) for c in city_names]:
        if handle and 3 <= len(handle) <= 30 and handle not in out:
            out.append(handle)
    return out[:4]


def find_instagram(p):
    """Ищет аккаунт заведения в Instagram. Возвращает (имя аккаунта, подпись аккаунта)."""
    for handle in guess_handles(p["name"], p["city"]):
        if INSTA_OFF[0]:
            return "", ""
        display = instagram_name(handle)
        if display and same_business(p["name"], display):
            return handle, display
    return "", ""


def wikidata_site(qid):
    if not re.match(r"^Q\d+$", qid or ""):
        return ""
    try:
        data = json.loads(http_get(WIKIDATA % qid, timeout=20).decode("utf-8"))
        claims = data["entities"][qid]["claims"].get("P856") or []
        return claims[0]["mainsnak"]["datavalue"]["value"]
    except Exception:
        return ""


def find_site(place, known_names):
    """Ищет сайт заведения, которого нет в карте. Возвращает (адрес, как нашли)."""
    name, phone = place["name"], place["phone"]

    # 1. Такое же заведение в базе, у которого сайт уже известен (сеть, второй вход, филиал).
    twin = known_names.get(normalize_name(name))
    if twin:
        return twin, "такое же название в базе"

    # 2. Домен из почты: info@zerno-cafe.com означает сайт zerno-cafe.com.
    email = (place["email"] or "").strip()
    if "@" in email:
        domain = email.split("@")[-1].lower().strip(" .,;")
        if domain and domain not in FREE_MAIL and "." in domain:
            html, final = open_domain(domain)
            if html and (page_matches(html, name, phone) or len(page_text(html)) > 400):
                return final, "домен из почты"

    # 3. Wikidata: у известных заведений там записан официальный сайт.
    if place["wikidata"]:
        site = wikidata_site(place["wikidata"])
        if site:
            return site, "Wikidata"

    # 4. Подбор домена из названия, с проверкой, что страница про это заведение.
    for domain in guess_domains(name, place["cc"]):
        html, final = open_domain(domain)
        if html:
            why = page_matches(html, name, phone)
            if why:
                return final, "подобран домен, " + why
    return "", ""


def check_site(website):
    """Возвращает список проблем сайта простыми словами."""
    url = normalize_url(website)
    host = urllib.parse.urlparse(url).hostname or ""
    public = host_is_public(host) if host else None
    if public is None:
        return ["сайт не открывается"]
    if public is False:
        return ["адрес сайта некорректный"]
    rest = url.split("://", 1)[1]
    issues = []
    try:
        html, final = fetch_page("https://" + rest)
        if final.lower().startswith("http://"):
            issues.append("нет HTTPS")
    except Exception:
        try:
            html, final = fetch_page("http://" + rest)
            issues.append("нет HTTPS")
        except Exception:
            return ["сайт не открывается"]
    low = html.lower()
    text = page_text(html)
    if is_social(final):
        return issues + ["сайт ведёт в соцсеть"]
    if any(w in text for w in PARKED):
        return issues + ["домен есть, сайта нет"]
    if len(text) < 200:
        issues.append("на странице почти нет текста")
    if not re.search(r"<meta[^>]+name\s*=\s*[\"']?viewport", low):
        issues.append("нет мобильной версии")
    for builder, marks in BUILDERS.items():
        if any(m in low or m in final.lower() for m in marks):
            issues.append("сайт на конструкторе (%s)" % builder)
            break
    years = []
    for m in re.finditer(r"(?:©|&copy;|\(c\)|copyright)[^<]{0,40}?((?:19|20)\d{2})(?:\s*[-–—]\s*((?:19|20)\d{2}))?", low):
        years.append(int(m.group(2) or m.group(1)))
    if years and max(years) <= datetime.date.today().year - 2:
        issues.append("в подвале %d год" % max(years))
    return issues


# ---------- фоновые задачи ----------

def start_job(kind, target, *args):
    with JOB_LOCK:
        if JOB["running"]:
            raise ValueError("Уже идёт другая задача. Дождитесь её или нажмите «Остановить».")
        token = JOB["token"] + 1
        JOB.update(running=True, kind=kind, done=0, total=0, found=0, added=0, msg="Запускаю", error="",
                   stop=False, token=token, started=time.time())
    threading.Thread(target=_job_wrapper, args=(token, target) + args, daemon=True).start()


def stop_job():
    """Останавливает сразу: фоновый поток сам заметит это и тихо завершится."""
    with JOB_LOCK:
        if JOB["running"]:
            JOB.update(running=False, stop=True, msg="Остановлено")


def alive(token):
    return JOB["token"] == token and JOB["running"] and not JOB["stop"]


def setj(token, **values):
    """Меняет состояние задачи, только если она всё ещё текущая и не остановлена."""
    if JOB["token"] == token and not JOB["stop"]:
        JOB.update(values)


def pause(token, seconds):
    end = time.time() + seconds
    while time.time() < end and alive(token):
        time.sleep(0.1)


def _job_wrapper(token, target, *args):
    try:
        target(token, *args)
    except Exception as err:  # показываем причину в окне, а не роняем программу
        setj(token, error=str(err))
    finally:
        setj(token, running=False)


def run_scan(token, cities, cat_keys, cell_km=0):
    filters, seen = [], set()
    for key, _title, flt in CATEGORIES:
        if key in cat_keys:
            for f in flt:
                if f not in seen:
                    seen.add(f)
                    filters.append(f)
    if not filters:
        raise ValueError("Выберите хотя бы одну категорию.")

    # Сначала просим весь город одним запросом: так сервер карт нагружается в десятки раз
    # меньше и реже нас ограничивает. Если запрос не прошёл, делим участок на четыре части.
    tasks = []
    for i, city in enumerate(cities):
        setj(token, msg="Ищу на карте: %s" % city)
        name, cc, s, n, w, e = geocode(city)
        tasks.append([name, cc, (s, w, n, e), 0])
        if i + 1 < len(cities):
            pause(token, 1.2)  # правила бесплатного поиска городов: не чаще раза в секунду
        if not alive(token):
            return
    setj(token, total=len(tasks))

    failed = in_row = found = added = 0
    i = 0
    while i < len(tasks):
        if not alive(token):
            return
        name, cc, box, depth = tasks[i]
        setj(token, msg="%s: участок %d из %d" % (name, i + 1, len(tasks)))
        try:
            elements = overpass(filters, box[0], box[1], box[2], box[3], alive=lambda: alive(token),
                                timeout=120 if depth == 0 else 80, hedge=None if depth == 0 else 12)
            if not elements and depth == 0 and len(OVERPASS) > 1:
                # пусто на целый город подозрительно: спрашиваем другое зеркало
                OVERPASS_NEXT[0] = (OVERPASS_NEXT[0] + 1) % len(OVERPASS)
                try:
                    elements = overpass(filters, box[0], box[1], box[2], box[3],
                                        alive=lambda: alive(token), attempts=1, timeout=80)
                except RuntimeError:
                    pass
            if not alive(token):
                return
            found += len(elements)
            added += save_places(elements, name, cc)
            setj(token, found=found, added=added)
            in_row = 0
        except RuntimeError as err:
            if not alive(token) or "stopped" in str(err):
                return
            if depth < MAX_SPLITS and len(tasks) < MAX_CELLS:
                for part in split_box(box):  # участок великоват или сервер занят: берём по частям
                    tasks.append([name, cc, part, depth + 1])
                setj(token, total=len(tasks), msg="%s: участок великоват, делю на части" % name)
            else:
                failed += 1
            in_row += 1
            if (found == 0 and in_row >= 3) or failed >= 8:
                raise RuntimeError(NO_MAP)
        i += 1
        setj(token, done=i)
        pause(token, PAUSE_BETWEEN_CELLS)
    mark_chains()
    msg = "Готово. Новых заведений: %d" % added
    if failed:
        msg += ", не получилось участков: %d" % failed
    setj(token, msg=msg)


def run_ping(token):
    setj(token, total=len(OVERPASS))
    lines, ok = ping_servers(token)
    if not alive(token):
        return
    setj(token, done=len(OVERPASS),
         msg=" · ".join(lines) + ("" if ok else ". " + NO_MAP))


def run_parallel(token, items, work, report, workers=WORKERS):
    """Выполняет work(item) в несколько потоков. «Остановить» срабатывает сразу."""
    pending = list(reversed(items))  # забираем с конца, значит начинаем с самых приоритетных
    lock = threading.Lock()
    counter = {"done": 0}

    def worker():
        while alive(token):
            with lock:
                if not pending:
                    return
                item = pending.pop()
            try:
                work(item)
            except Exception:
                pass  # одно упавшее заведение не должно останавливать всю проверку
            with lock:
                counter["done"] += 1
                done = counter["done"]
            report(done, item)

    threads = [threading.Thread(target=worker, daemon=True) for _ in range(workers)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    return counter["done"]


def run_check(token, deep, insta=False):
    """Ищет сайты у тех, у кого их нет в карте, и проверяет все известные сайты."""
    with db() as con:
        known = {}
        for row in con.execute("SELECT name, website, found_site FROM places "
                               "WHERE (website<>'' OR found_site<>'') AND hidden=0"):
            site = row["website"] or row["found_site"]
            if site and not is_social(site):
                known.setdefault(normalize_name(row["name"]), site)
        where = "site_state='none' AND hidden=0" + ("" if deep else " AND searched_at IS NULL")
        to_find = [dict(r) for r in con.execute("SELECT * FROM places WHERE " + where + " ORDER BY score DESC")]
        where2 = "site_state IN ('site','found') AND hidden=0" + ("" if deep else " AND checked_at IS NULL")
        waiting = con.execute("SELECT COUNT(*) n FROM places WHERE " + where2).fetchone()["n"]

    if not to_find and not waiting:
        setj(token, msg="Проверять нечего: сначала найдите заведения, или всё уже проверено. "
                        "Чтобы пройти всё заново, включите «проверить всё заново».")
        return

    # Одинаковые названия — одно и то же заведение или сеть: ищем сайт один раз на название.
    groups = {}
    for p in to_find:
        groups.setdefault(normalize_name(p["name"]), []).append(p)
    leaders = sorted((g[0] for g in groups.values()), key=lambda p: -p["score"])
    rest = [p for g in groups.values() for p in g[1:]]

    total = len(to_find) + waiting
    setj(token, total=total)
    counts = {"found": 0}
    guard = threading.Lock()
    now = lambda: datetime.datetime.now().isoformat(timespec="seconds")

    def remember(p, site, how):
        state = "social" if is_social(site) else "found"
        with DB_LOCK, db() as con:
            con.execute("UPDATE places SET found_site=?, found_how=?, site_state=?, searched_at=?, "
                        "issues='[]', checked_at=NULL, score=? WHERE id=?",
                        (site, how, state, now(), score_place(dict(p, site_state=state, issues=[])), p["id"]))
        with guard:
            counts["found"] += 1

    def search_one(p):
        if not alive(token):
            return
        site, how = find_site(p, known)
        if not alive(token):
            return
        if site:
            known.setdefault(normalize_name(p["name"]), site)
            remember(p, site, how)
        else:
            with DB_LOCK, db() as con:
                con.execute("UPDATE places SET searched_at=? WHERE id=?", (now(), p["id"]))
        bump()

    def report_find(done, item):
        setj(token, done=done, found=counts["found"],
             msg="Ищу сайт: %s (%d из %d)" % (item["name"][:38], done, total))

    run_parallel(token, leaders, search_one, report_find)
    if not alive(token):
        return

    # Остальным заведениям с тем же названием сайт уже известен, сеть для этого не нужна.
    for p in rest:
        site = known.get(normalize_name(p["name"]))
        if site:
            remember(p, site, "такое же название в базе")
        else:
            with DB_LOCK, db() as con:
                con.execute("UPDATE places SET searched_at=? WHERE id=?", (now(), p["id"]))
    bump()
    done_find = len(to_find)
    setj(token, done=done_find, found=counts["found"])

    # Поиск аккаунтов в Instagram: идёт по одному запросу в секунду, поэтому
    # берём только самые приоритетные заведения.
    counts["insta"] = 0
    if insta and alive(token):
        with db() as con:
            where3 = "site_state='none' AND hidden=0 AND instagram=''" + ("" if deep else " AND insta_at IS NULL")
            to_insta = [dict(r) for r in con.execute(
                "SELECT * FROM places WHERE " + where3 + " ORDER BY score DESC LIMIT ?", (INSTAGRAM_LIMIT,))]
        setj(token, total=done_find + len(to_insta))
        for number, place in enumerate(to_insta):
            if not alive(token) or INSTA_OFF[0]:
                break
            setj(token, msg="Ищу в Instagram: %s (%d из %d)" % (place["name"][:34], number + 1, len(to_insta)))
            handle, _display = find_instagram(place)
            if not alive(token):
                return
            with DB_LOCK, db() as con:
                con.execute("UPDATE places SET instagram=?, insta_at=?, score=? WHERE id=?",
                            (handle, now(), score_place(dict(place, instagram=handle)), place["id"]))
            if handle:
                counts["insta"] += 1
            bump()
            done_find += 1
            setj(token, done=done_find, found=counts["found"])

    # Сайты, которые только что нашлись, проверяем в этом же заходе.
    with db() as con:
        to_check = [dict(r) for r in con.execute("SELECT id, website, found_site FROM places WHERE " + where2)]
    total = done_find + len(to_check)
    setj(token, total=total)
    counts["bad"] = 0

    def check_one(p):
        if not alive(token):
            return
        issues = check_site(p["website"] or p["found_site"])
        if not alive(token):
            return
        with DB_LOCK, db() as con:
            row = con.execute("SELECT * FROM places WHERE id=?", (p["id"],)).fetchone()
            if row:
                con.execute("UPDATE places SET issues=?, checked_at=?, score=? WHERE id=?",
                            (json.dumps(issues, ensure_ascii=False), now(),
                             score_place(dict(row, issues=issues)), p["id"]))
        if issues:
            with guard:
                counts["bad"] += 1
        bump()

    def report_check(done, item):
        setj(token, done=done_find + done, msg="Проверяю сайты: %d из %d" % (done, len(to_check)))

    run_parallel(token, to_check, check_one, report_check)
    if not alive(token):
        return
    message = ("Готово. Нашли сайтов: %d (столько заведений ушло из списка). Проверено сайтов: %d, с проблемами: %d."
               % (counts["found"], len(to_check), counts["bad"]))
    if insta:
        message += " Аккаунтов в Instagram нашлось: %d." % counts["insta"]
        if INSTA_OFF[0]:
            message += " " + INSTA_OFF[0] + " Попробуйте через час."
    setj(token, done=total, msg=message)


# ---------- черновик сообщения и выгрузка ----------

# Что полезного будет на сайте — своё для каждого вида заведений.
BENEFITS = [
    (("пекарня", "кондитерская", "шоколад", "мороженое", "мясная лавка", "сыры", "деликатесы", "овощи"),
     {"ru": ("ассортимент и цены", "предзаказ и доставка", "фото витрины"),
      "ua": ("асортимент і ціни", "передзамовлення і доставка", "фото вітрини")}),
    (("кафе", "ресторан", "фастфуд", "бар", "паб", "пивная", "кофе", "чай", "фуд-корт"),
     {"ru": ("меню с ценами и фото", "бронь столика", "доставка и самовывоз"),
      "ua": ("меню з цінами і фото", "бронь столика", "доставка і самовивіз")}),
    (("парикмахерская", "салон красоты", "барбершоп", "ногтевая студия", "массаж", "тату",
      "косметика", "спа", "сауна", "груминг", "парфюмерия"),
     {"ru": ("онлайн-запись", "прайс на услуги", "фото работ"),
      "ua": ("онлайн-запис", "прайс на послуги", "фото робіт")}),
    (("автосервис", "шиномонтаж", "автомойка", "автозапчасти", "автосалон", "автошкола",
      "мотосалон", "велосипеды"),
     {"ru": ("список услуг с ценами", "запись на удобное время", "как к вам доехать"),
      "ua": ("перелік послуг з цінами", "запис на зручний час", "як до вас доїхати")}),
    (("стоматология", "клиника", "врач", "ветклиника", "аптека", "лаборатория", "оптика",
      "физиотерапия", "медтехника"),
     {"ru": ("услуги и цены", "запись к нужному специалисту", "отзывы пациентов"),
      "ua": ("послуги і ціни", "запис до потрібного спеціаліста", "відгуки пацієнтів")}),
    (("гостиница", "хостел", "гостевой дом", "апартаменты", "мотель", "домик"),
     {"ru": ("номера и цены", "бронь напрямую, без комиссии посредникам", "фото и условия"),
      "ua": ("номери і ціни", "бронь напряму, без комісії посередникам", "фото і умови")}),
    (("фитнес", "спорткомплекс", "танцы", "боулинг", "скалодром", "конный клуб", "спорттовары"),
     {"ru": ("расписание занятий", "цены на абонементы", "запись на пробное"),
      "ua": ("розклад занять", "ціни на абонементи", "запис на пробне")}),
    (("детский сад", "языковая школа", "музыкальная школа", "курсы", "колледж", "детский центр",
      "учебный центр"),
     {"ru": ("программы и цены", "расписание", "запись на пробное занятие"),
      "ua": ("програми і ціни", "розклад", "запис на пробне заняття")}),
    (("цветы", "ателье", "ювелирный", "часы", "фотостудия", "прачечная", "химчистка", "ремонт",
      "типография", "копицентр", "прокат", "турагентство", "ключи"),
     {"ru": ("услуги и цены", "примеры работ", "заказ прямо со страницы"),
      "ua": ("послуги і ціни", "приклади робіт", "замовлення прямо зі сторінки")}),
]
# Как вид заведения называется по-украински: это попадает в текст письма.
KIND_UA = {
    "кафе": "кав'ярня", "ресторан": "ресторан", "фастфуд": "фастфуд", "бар": "бар", "паб": "паб",
    "пивная": "пивна", "мороженое": "морозиво", "фуд-корт": "фуд-корт", "пекарня": "пекарня",
    "кондитерская": "кондитерська", "кофе": "кава", "чай": "чай", "деликатесы": "делікатеси",
    "мясная лавка": "м'ясна лавка", "овощи и фрукты": "овочі і фрукти", "алкоголь": "алкоголь",
    "напитки": "напої", "рыба и морепродукты": "риба і морепродукти", "сыры": "сири",
    "шоколад": "шоколад", "парикмахерская": "перукарня", "салон красоты": "салон краси",
    "косметика": "косметика", "массаж": "масаж", "тату-салон": "тату-салон",
    "ногтевая студия": "нігтьова студія", "парфюмерия": "парфумерія", "сауна": "сауна", "спа": "спа",
    "автосервис": "автосервіс", "шиномонтаж": "шиномонтаж", "автозапчасти": "автозапчастини",
    "автосалон": "автосалон", "мотосалон": "мотосалон", "велосипеды": "велосипеди",
    "автомойка": "автомийка", "автошкола": "автошкола", "стоматология": "стоматологія",
    "клиника": "клініка", "врач": "лікар", "ветклиника": "ветклініка", "аптека": "аптека",
    "физиотерапия": "фізіотерапія", "лаборатория": "лабораторія", "оптометрист": "оптометрист",
    "оптика": "оптика", "слуховые аппараты": "слухові апарати", "медтехника": "медтехніка",
    "гостиница": "готель", "гостевой дом": "гостьовий будинок", "хостел": "хостел", "мотель": "мотель",
    "апартаменты": "апартаменти", "домик": "будиночок", "фитнес": "фітнес-клуб",
    "спорткомплекс": "спорткомплекс", "танцы": "танці", "конный клуб": "кінний клуб",
    "боулинг": "боулінг", "скалодром": "скеледром", "спорттовары": "спорттовари",
    "рыбалка": "рибалка", "туризм": "туризм", "языковая школа": "мовна школа",
    "музыкальная школа": "музична школа", "курсы": "курси", "детский сад": "дитячий садок",
    "колледж": "коледж", "детский центр": "дитячий центр", "учебный центр": "навчальний центр",
    "прачечная": "пральня", "химчистка": "хімчистка", "ремонт обуви": "ремонт взуття",
    "ключи и замки": "ключі та замки", "фотостудия": "фотостудія", "турагентство": "турагенція",
    "цветы": "квіти", "ритуальные услуги": "ритуальні послуги", "ателье": "ательє",
    "ювелирный": "ювелірний магазин", "часы": "годинники", "копицентр": "копіцентр",
    "типография": "друкарня", "груминг": "грумінг", "склады": "склади", "прокат": "прокат",
    "недвижимость": "нерухомість", "юрист": "юрист", "бухгалтер": "бухгалтер",
    "страхование": "страхування", "реклама": "реклама", "IT-компания": "IT-компанія",
    "архитектор": "архітектор", "компания": "компанія", "кадровое агентство": "кадрова агенція",
    "турагент": "турагент", "нотариус": "нотаріус", "финансы": "фінанси",
}
# Города, записанные в карте по-русски, в украинском письме пишем по-украински.
CITY_UA = {
    "киев": "Київ", "львов": "Львів", "харьков": "Харків", "одесса": "Одеса", "днепр": "Дніпро",
    "запорожье": "Запоріжжя", "николаев": "Миколаїв", "винница": "Вінниця", "чернигов": "Чернігів",
    "черкассы": "Черкаси", "сумы": "Суми", "ровно": "Рівне", "хмельницкий": "Хмельницький",
    "черновцы": "Чернівці", "тернополь": "Тернопіль", "ивано-франковск": "Івано-Франківськ",
    "луцк": "Луцьк", "кропивницкий": "Кропивницький", "мариуполь": "Маріуполь",
    "кривой рог": "Кривий Ріг", "белая церковь": "Біла Церква", "бровары": "Бровари",
    "ирпень": "Ірпінь", "дрогобыч": "Дрогобич", "трускавец": "Трускавець", "борисполь": "Бориспіль",
    "вишневое": "Вишневе", "каменец-подольский": "Кам'янець-Подільський", "умань": "Умань",
    "житомир": "Житомир", "полтава": "Полтава", "херсон": "Херсон", "ужгород": "Ужгород",
}
DEFAULT_BENEFIT = {"ru": ("услуги и цены", "часы работы и контакты", "как вас найти"),
                   "ua": ("послуги і ціни", "години роботи і контакти", "як вас знайти")}
ISSUE_WORDS = {
    "нет HTTPS": {"ru": "браузер помечает его как небезопасный: нет сертификата",
                  "ua": "браузер позначає його як небезпечний: немає сертифіката"},
    "нет мобильной версии": {"ru": "с телефона им пользоваться неудобно, а с телефона заходит больше половины людей",
                             "ua": "з телефона ним користуватися незручно, а з телефона заходить більше половини людей"},
    "сайт не открывается": {"ru": "он сейчас вообще не открывается", "ua": "він зараз взагалі не відкривається"},
    "домен есть, сайта нет": {"ru": "домен есть, а страницы на нём нет", "ua": "домен є, а сторінки на ньому немає"},
    "сайт ведёт в соцсеть": {"ru": "адрес ведёт в соцсеть, а не на сайт", "ua": "адреса веде в соцмережу, а не на сайт"},
    "на странице почти нет текста": {"ru": "на странице почти нет информации о вас",
                                     "ua": "на сторінці майже немає інформації про вас"},
    "адрес сайта некорректный": {"ru": "адрес сайта в справочниках записан с ошибкой",
                                 "ua": "адреса сайту в довідниках записана з помилкою"},
}


def benefits_for(kind, lang):
    for keys, texts in BENEFITS:
        if any(k in (kind or "") for k in keys):
            return texts[lang]
    return DEFAULT_BENEFIT[lang]


def issue_words(issues, lang):
    """Переводит находку проверки в живую фразу."""
    for issue in issues:
        if issue in ISSUE_WORDS:
            return ISSUE_WORDS[issue][lang]
        year = re.search(r"в подвале (\d{4}) год", issue)
        if year:
            return ({"ru": "последнее обновление на нём датировано %s годом",
                     "ua": "останнє оновлення на ньому датоване %s роком"}[lang]) % year.group(1)
        builder = re.search(r"конструкторе \(([^)]+)\)", issue)
        if builder:
            return ({"ru": "он собран на конструкторе %s, и его легко обогнать",
                     "ua": "він зібраний на конструкторі %s, і його легко обігнати"}[lang]) % builder.group(1)
    return {"ru": "есть что улучшить", "ua": "є що покращити"}[lang]


def contact_line(p):
    return " · ".join(x for x in (p["phone"], p["email"], p["socials"]) if x)


def draft_variants(p, settings):
    """Собирает три разных текста под конкретное заведение: короткий, письмо и разговор."""
    lang = settings.get("lang") if settings.get("lang") in ("ru", "ua") else "ua"
    seed = int(hashlib.md5(p["id"].encode("utf-8")).hexdigest()[:8], 16)
    pick = lambda options, salt=0: options[(seed + salt) % len(options)]

    name = re.sub(r'["«»„“”]', "", p["name"]).strip() or p["name"]
    city, kind = (p["city"] or ""), (p["kind"] or "")
    issues = json.loads(p["issues"] or "[]")
    site = (p["website"] or p["found_site"] or "").replace("https://", "").replace("http://", "").rstrip("/")
    has_site = p["site_state"] in ("site", "found")
    me = (settings.get("my_name") or "").strip()
    offer = (settings.get("offer") or "").strip()
    b1, b2, b3 = benefits_for(kind, lang)
    where = (" на " + p["address"]) if p["address"] else ""
    in_city = (" в городе " + city) if city else ""
    in_city_ua = (" у місті " + city) if city else ""

    if lang == "ua":
        kind = KIND_UA.get(kind, kind) or "заклад"
        city = CITY_UA.get(city.lower(), city)
        in_city_ua = (" у місті " + city) if city else ""
        greet = pick(["Вітаю!", "Доброго дня!", "Добрий день!"])
        if p["site_state"] == "none":
            intro = pick([
                "Шукав %s%s і натрапив на «%s»%s — але сайту у вас не знайшов." % (kind, in_city_ua, name, where),
                "Знайшов «%s» на карті%s%s, а ось сайту у вас немає." % (name, in_city_ua, where),
                "Побачив «%s» серед закладів%s — сайту не знайшов." % (name, in_city_ua)], 1)
        elif p["site_state"] == "social":
            intro = pick([
                "Знайшов «%s» — у вас є сторінка в соцмережі, але власного сайту немає." % name,
                "Бачу «%s» у соцмережах, а сайту у вас немає." % name,
                "У «%s» є соцмережа, але немає сайту, на який можна послатися." % name], 1)
        elif issues:
            intro = "Подивився ваш сайт (%s) — %s." % (site, issue_words(issues, lang))
        else:
            intro = "Подивився ваш сайт (%s): він робочий, але кілька речей на ньому можна зробити зручніше." % site
        if has_site:
            why = pick([
                "Сайт — перше, що бачить людина перед тим, як до вас прийти, і саме по ньому вирішує, чи йти.",
                "Тим, хто дивиться з телефона, важливо одразу побачити ціни, фото і як дістатися.",
                "Невеликі правки на сайті зазвичай дають більше дзвінків, ніж реклама."], 2)
            what = "Можу переробити його так, щоб одразу було видно головне: %s, %s, %s." % (b1, b2, b3)
        else:
            why = pick([
                "Коли людина шукає «%s %s» у Google чи на картах, вона обирає з тих, у кого видно ціни і фото." % (kind, city),
                "Більшість людей спершу гуглять заклад, і без сайту вас просто не бачать.",
                "Соцмережі показують не всім, а сайт працює на вас цілодобово."], 2)
            what = "Зроблю просту сторінку, де буде головне: %s, %s, %s." % (b1, b2, b3)
        who = ("Я %s." % offer) if offer else "Я роблю сайти для місцевого бізнесу."
        cta = pick([
            "Якщо цікаво, покажу, як це може виглядати саме у вас — безкоштовно.",
            "Хочете, зберу приклад для «%s» і надішлю подивитися?" % name,
            "Можу надіслати приклад під ваш заклад, без оплати і зобов'язань."], 3)
        sign = ("\n\n— %s" % me) if me else ""
        subject = "Сайт для «%s»" % name
        second = ("Подивився ваш сайт — %s." % issue_words(issues, lang)) if has_site else \
                 "Знайшов вас на карті%s. Підкажіть, сайт у вас є?" % in_city_ua
        third = ("Якщо коротко: людям з телефона важко швидко знайти те, за чим вони прийшли: %s." % b1) if has_site else \
                "Якщо немає: зараз тим, хто шукає вас у Google, ніде подивитися головне: %s." % b1
        call = ("Розмова з «%s»\n\n1. Доброго дня! Мене звати%s. %s\n2. %s\n3. %s\n"
                "4. Пропозиція: безкоштовно зберу приклад сторінки саме для вас, подивитеся і вирішите.\n"
                "5. Запитати: на який номер або пошту надіслати приклад?") % (
                    name, (" " + me) if me else "", who, second, third)
        titles = ("Коротко: Telegram, Viber, Instagram", "Лист на пошту", "Що сказати по телефону")
    else:
        kind = kind or "заведение"
        greet = pick(["Здравствуйте!", "Добрый день!", "Доброго дня!"])
        if p["site_state"] == "none":
            intro = pick([
                "Искал %s%s и наткнулся на «%s»%s — но сайта у вас не нашёл." % (kind, in_city, name, where),
                "Нашёл «%s» на карте%s%s, а вот сайта у вас нет." % (name, in_city, where),
                "Увидел «%s» среди заведений%s — сайта не нашёл." % (name, in_city)], 1)
        elif p["site_state"] == "social":
            intro = pick([
                "Нашёл «%s» — у вас есть страница в соцсети, но своего сайта нет." % name,
                "Вижу «%s» в соцсетях, а сайта у вас нет." % name,
                "У «%s» есть соцсеть, но нет сайта, на который можно сослаться." % name], 1)
        elif issues:
            intro = "Посмотрел ваш сайт (%s) — %s." % (site, issue_words(issues, lang))
        else:
            intro = "Посмотрел ваш сайт (%s): он рабочий, но пару вещей на нём можно сделать удобнее." % site
        if has_site:
            why = pick([
                "Сайт — первое, что видит человек перед тем, как к вам прийти, и по нему решает, идти ли вообще.",
                "Тем, кто смотрит с телефона, важно сразу увидеть цены, фото и как добраться.",
                "Небольшие правки на сайте обычно дают больше звонков, чем реклама."], 2)
            what = "Могу переделать его так, чтобы сразу было видно главное: %s, %s, %s." % (b1, b2, b3)
        else:
            why = pick([
                "Когда человек ищет «%s %s» в Google или на картах, он выбирает из тех, у кого видно цены и фото." % (kind, city),
                "Большинство людей сначала гуглят заведение, и без сайта вас просто не видят.",
                "Соцсети показывают не всем, а сайт работает на вас круглосуточно."], 2)
            what = "Сделаю простую страницу, где будет главное: %s, %s, %s." % (b1, b2, b3)
        who = ("Я %s." % offer) if offer else "Я делаю сайты для местного бизнеса."
        cta = pick([
            "Если интересно, покажу, как это может выглядеть именно у вас — бесплатно.",
            "Хотите, соберу пример для «%s» и пришлю посмотреть?" % name,
            "Могу прислать пример под ваше заведение, без оплаты и обязательств."], 3)
        sign = ("\n\n— %s" % me) if me else ""
        subject = "Сайт для «%s»" % name
        second = ("Посмотрел ваш сайт — %s." % issue_words(issues, lang)) if has_site else \
                 "Нашёл вас на карте%s. Подскажите, сайт у вас есть?" % in_city
        third = ("Если коротко: людям с телефона сложно быстро найти то, за чем они пришли: %s." % b1) if has_site else \
                "Если нет: сейчас тем, кто ищет вас в Google, негде посмотреть главное: %s." % b1
        call = ("Разговор с «%s»\n\n1. Добрый день! Меня зовут%s. %s\n2. %s\n3. %s\n"
                "4. Предложение: бесплатно соберу пример страницы именно для вас, посмотрите и решите.\n"
                "5. Спросить: на какой номер или почту прислать пример?") % (
                    name, (" " + me) if me else "", who, second, third)
        titles = ("Коротко: Telegram, Viber, Instagram", "Письмо на почту", "Что сказать по телефону")

    short = "%s %s %s %s" % (greet, intro, what, cta)
    letter = "%s\n\n%s %s\n\n%s %s\n\n%s%s" % (greet, intro, why, who, what, cta, sign)
    return {
        "name": p["name"],
        "contact": contact_line(p),
        "variants": [
            {"key": "short", "title": titles[0], "text": short},
            {"key": "mail", "title": titles[1], "text": "Тема: %s\n\n%s" % (subject, letter)},
            {"key": "call", "title": titles[2], "text": call},
        ],
    }


def csv_cell(value):
    """Не даём Excel принять текст из карты за формулу."""
    text = "" if value is None else str(value)
    if text[:1] in ("=", "@", "\t") or (text[:1] in ("+", "-") and not re.match(r"^[+\-][\d\s()\-]+$", text)):
        return "'" + text
    return text


def export_csv(ids=None):
    status_ru = dict(STATUSES)
    out = io.StringIO()
    writer = csv.writer(out, delimiter=";")
    writer.writerow(["Приоритет", "Название", "Категория", "Адрес", "Город", "Телефон", "Email", "Соцсети",
                     "Сайт", "Откуда сайт", "Состояние", "Проблемы сайта", "Статус", "Заметка",
                     "Часы работы", "На карте"])
    with db() as con:
        rows = con.execute("SELECT * FROM places ORDER BY score DESC, name")
        for p in rows:
            if ids is not None and p["id"] not in ids:
                continue
            writer.writerow([csv_cell(v) for v in (
                p["score"], p["name"], p["kind"], p["address"], p["city"], p["phone"], p["email"], p["socials"],
                p["website"] or p["found_site"], p["found_how"] or ("из карты" if p["website"] else ""),
                SITE_STATES.get(p["site_state"], ""), "; ".join(json.loads(p["issues"] or "[]")),
                status_ru.get(p["status"], p["status"]), p["note"], p["hours"],
                "https://www.openstreetmap.org/" + p["id"])])
    return out.getvalue().encode("utf-8-sig")


def save_csv_file(ids=None):
    """Кладёт выгрузку рядом с программой и открывает эту папку."""
    data = export_csv(ids)
    rows = max(0, data.decode("utf-8-sig").strip().count("\n"))
    path = os.path.join(BASE, "zorko_export.csv")
    try:
        with open(path, "wb") as f:
            f.write(data)
    except PermissionError:  # прежний файл открыт в Excel
        path = os.path.join(BASE, "zorko_export_%s.csv" % datetime.datetime.now().strftime("%H%M%S"))
        with open(path, "wb") as f:
            f.write(data)
    if hasattr(os, "startfile") and "--no-browser" not in sys.argv:
        try:
            os.startfile(BASE)
        except OSError:
            pass
    return path, rows


# ---------- веб-сервер ----------

class Handler(BaseHTTPRequestHandler):
    server_version = "Zorko"

    def log_message(self, *args):
        pass

    def reply(self, code, body, ctype="application/json; charset=utf-8", extra=None):
        if isinstance(body, (dict, list)):
            body = json.dumps(body, ensure_ascii=False).encode("utf-8")
        elif isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        for key, value in (extra or {}).items():
            self.send_header(key, value)
        self.end_headers()
        self.wfile.write(body)

    def local_only(self):
        host = (self.headers.get("Host") or "").rsplit(":", 1)[0]
        if host not in ("127.0.0.1", "localhost"):
            self.reply(403, {"error": "forbidden"})
            return False
        return True

    def do_GET(self):
        if not self.local_only():
            return
        url = urllib.parse.urlparse(self.path)
        query = urllib.parse.parse_qs(url.query)
        if url.path == "/":
            self.reply(200, PAGE, "text/html; charset=utf-8")
        elif url.path == "/favicon.ico":
            self.reply(204, b"", "image/x-icon")
        elif url.path == "/api/state":
            job = dict(JOB)
            job["eta"] = 0
            if job["running"] and job["done"]:
                job["eta"] = int((time.time() - job["started"]) / job["done"] * (job["total"] - job["done"]))
            with db() as con:
                stats = {r["site_state"]: r["n"] for r in con.execute(
                    "SELECT site_state, COUNT(*) n FROM places WHERE hidden=0 GROUP BY site_state")}
                stats["hidden"] = con.execute("SELECT COUNT(*) n FROM places WHERE hidden=1").fetchone()["n"]
            self.reply(200, {"job": job, "rev": REV[0], "stats": stats, "settings": get_settings(),
                             "categories": [[c[0], c[1]] for c in CATEGORIES], "statuses": STATUSES})
        elif url.path == "/api/places":
            with db() as con:
                rows = [dict(r) for r in con.execute("SELECT * FROM places")]
            for r in rows:
                r["issues"] = json.loads(r["issues"] or "[]")
                r["site"] = r["website"] or r["found_site"] or ""
            self.reply(200, {"rev": REV[0], "places": rows})
        elif url.path == "/api/draft":
            with db() as con:
                p = con.execute("SELECT * FROM places WHERE id=?", (query.get("id", [""])[0],)).fetchone()
            if not p:
                self.reply(404, {"error": "Заведение не найдено."})
            else:
                self.reply(200, draft_variants(p, get_settings()))
        elif url.path == "/api/export.csv":
            self.reply(200, export_csv(), "text/csv; charset=utf-8",
                       {"Content-Disposition": 'attachment; filename="zorko.csv"'})
        else:
            self.reply(404, {"error": "not found"})

    def do_POST(self):
        if not self.local_only():
            return
        if self.headers.get("X-Zorko") != "1":  # запросы принимаются только от окна самой программы
            self.reply(403, {"error": "forbidden"})
            return
        try:
            length = min(int(self.headers.get("Content-Length") or 0), 2000000)
            data = json.loads(self.rfile.read(length).decode("utf-8") or "{}")
            path = urllib.parse.urlparse(self.path).path
            extra = {}
            if path == "/api/scan":
                cities = [c.strip() for c in str(data.get("cities", "")).split(",") if c.strip()]
                if not cities:
                    raise ValueError("Введите город.")
                if len(cities) > MAX_CITIES:
                    raise ValueError("За один раз можно искать не больше %d городов." % MAX_CITIES)
                cats = [str(c) for c in (data.get("cats") or [])]
                start_job("scan", run_scan, cities, cats, float(data.get("cell_km") or 5))
            elif path == "/api/check":
                start_job("check", run_check, bool(data.get("deep")), bool(data.get("insta")))
            elif path == "/api/ping":
                start_job("ping", run_ping)
            elif path == "/api/stop":
                stop_job()
            elif path == "/api/place":
                status = str(data.get("status", "new"))
                if status not in dict(STATUSES):
                    raise ValueError("Неизвестный статус.")
                with DB_LOCK, db() as con:
                    con.execute("UPDATE places SET status=?, note=? WHERE id=?",
                                (status, str(data.get("note", ""))[:2000], str(data.get("id", ""))))
                bump()
            elif path == "/api/mark-site":
                place_id = str(data.get("id", ""))
                site = normalize_url(str(data.get("site", "")).strip())[:400]
                if site and not re.match(r"^https?://[^\s/]+\.[^\s/]+", site):
                    raise ValueError("Не похоже на адрес сайта. Пример: example.com")
                with DB_LOCK, db() as con:
                    row = con.execute("SELECT * FROM places WHERE id=?", (place_id,)).fetchone()
                    if not row:
                        raise ValueError("Заведение не найдено.")
                    state = "social" if (site and is_social(site)) else ("found" if site else row["site_state"])
                    con.execute("UPDATE places SET found_site=?, found_how=?, site_state=?, searched_at=?, "
                                "issues='[]', checked_at=NULL, score=? WHERE id=?",
                                (site, "нашли вручную" if site else "", state,
                                 datetime.datetime.now().isoformat(timespec="seconds"),
                                 score_place(dict(row, site_state=state, issues=[])), place_id))
                bump()
            elif path == "/api/hide":
                ids = [str(i) for i in (data.get("ids") or [])][:5000]
                hide = 1 if data.get("hide", True) else 0
                why = "скрыто вручную" if hide else ""
                with DB_LOCK, db() as con:
                    con.executemany("UPDATE places SET hidden=?, hidden_why=? WHERE id=?",
                                    [(hide, why, i) for i in ids])
                bump()
            elif path == "/api/settings":
                with DB_LOCK, db() as con:
                    for key in ("my_name", "offer", "ui", "lang"):
                        if key in data:
                            con.execute("INSERT INTO settings(key, value) VALUES(?, ?) "
                                        "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                                        (key, str(data[key])[:4000]))
            elif path == "/api/export-file":
                ids = data.get("ids")
                extra["path"], extra["rows"] = save_csv_file(
                    set(str(i) for i in ids) if isinstance(ids, list) else None)
            elif path == "/api/clear":
                if JOB["running"]:
                    raise ValueError("Сначала остановите текущую задачу.")
                with DB_LOCK, db() as con:
                    con.execute("DELETE FROM places")
                bump()
            else:
                self.reply(404, {"error": "not found"})
                return
            self.reply(200, dict({"ok": True, "rev": REV[0]}, **extra))
        except ValueError as err:
            self.reply(400, {"error": str(err)})
        except Exception as err:
            self.reply(500, {"error": "Ошибка программы: %s" % err})


PAGE = r"""<!doctype html>
<html lang="ru">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Zorko</title>
<style>
:root{--bg:#000;--card:#0b0b0c;--ink:#f5f5f7;--mute:#a1a1a6;--line:#27272b;--acc:#f5f5f7;--acc-ink:#000;--good:#7ee0a1;--warn:#ffcf70;--bad:#ff8f8f}
*{box-sizing:border-box}
html{color-scheme:dark}
body{margin:0;background:var(--bg);color:var(--ink);font:16px/1.5 "Segoe UI",system-ui,sans-serif;
  background-image:radial-gradient(rgba(255,255,255,.1) 1px,transparent 1.2px);background-size:22px 22px}
main{max-width:1500px;margin:0 auto;padding:20px 16px 56px;display:flex;flex-direction:column;gap:16px}
header{display:flex;flex-wrap:wrap;align-items:center;justify-content:space-between;gap:12px}
.brand{display:flex;align-items:center;gap:10px;font-size:22px;font-weight:700}
.panel{background:var(--card);border:1px solid var(--line);border-radius:16px;padding:16px}
.row{display:flex;flex-wrap:wrap;gap:12px;align-items:end}
label{display:flex;flex-direction:column;gap:4px;font-size:13px;color:var(--mute)}
input,select,textarea,button{font:inherit;color:var(--ink);background:#000;border:1px solid var(--line);border-radius:10px;padding:9px 12px;min-height:42px}
input:focus-visible,select:focus-visible,textarea:focus-visible,button:focus-visible,a:focus-visible{outline:2px solid var(--acc);outline-offset:2px}
button{cursor:pointer}
button:hover{border-color:var(--acc)}
button.main{background:var(--acc);color:var(--acc-ink);border-color:var(--acc);font-weight:700}
button:disabled{opacity:.45;cursor:default}
.grow{flex:1 1 220px}
.check{flex-direction:row;align-items:center;gap:8px;min-height:42px;font-size:15px;color:var(--ink);padding:0 10px;border:1px solid var(--line);border-radius:10px;cursor:pointer}
.check input{min-height:0;padding:0;width:17px;height:17px}
.check:hover{border-color:var(--acc)}
.cats{display:flex;flex-wrap:wrap;gap:8px;margin-top:12px}
.bar{height:8px;border-radius:8px;background:var(--line);overflow:hidden}
.bar i{display:block;height:100%;width:0;background:var(--acc);transition:width .4s}
.muted{color:var(--mute);font-size:14px}
.err{color:var(--bad)}
.wrap{overflow-x:auto}
table{width:100%;border-collapse:collapse;min-width:1060px}
th{font-size:13px;color:var(--mute);text-align:left;font-weight:500;padding:8px 10px;border-bottom:1px solid var(--line);white-space:nowrap}
td{padding:10px;border-bottom:1px solid var(--line);vertical-align:top}
tr.dim td{opacity:.55}
tr.pick{cursor:pointer}
tr.pick:hover td{background:#141416}
.score{display:inline-block;min-width:38px;text-align:center;padding:3px 6px;border-radius:8px;border:1px solid var(--line);font-variant-numeric:tabular-nums;font-weight:700}
.score.hi{background:var(--acc);color:var(--acc-ink);border-color:var(--acc)}
.tag{display:inline-block;margin:0 4px 4px 0;padding:2px 8px;border-radius:999px;border:1px solid var(--line);font-size:13px}
.tag.none{background:var(--acc);color:var(--acc-ink);border-color:var(--acc)}
.tag.bad{border-color:var(--warn);color:var(--warn)}
.tag.ok{border-color:var(--good);color:var(--good)}
a{color:var(--ink)}
td input{width:100%;min-width:150px;min-height:36px;padding:6px 8px}
td select,td button,td a.mini{min-height:36px;padding:6px 8px}
a.mini{display:inline-block;border:1px solid var(--line);border-radius:10px;text-decoration:none;text-align:center}
a.mini:hover{border-color:var(--acc)}
dialog{background:var(--card);color:var(--ink);border:1px solid var(--line);border-radius:16px;padding:20px;width:min(640px,92vw)}
dialog::backdrop{background:rgba(0,0,0,.7)}
textarea{width:100%;min-height:220px;resize:vertical}
footer{color:var(--mute);font-size:13px}
#toast{position:fixed;right:16px;bottom:16px;max-width:min(560px,90vw);padding:12px 16px;background:var(--acc);color:var(--acc-ink);border-radius:12px;font-weight:600;opacity:0;pointer-events:none;transition:opacity .2s;overflow-wrap:anywhere}
#toast.on{opacity:1}
.more{display:flex;justify-content:center;padding-top:12px}
</style>
</head>
<body>
<main>
<header>
  <div class="brand">
    <svg width="30" height="30" viewBox="0 0 32 32" aria-hidden="true" fill="currentColor"><circle cx="9" cy="5" r="2.7"/><circle cx="16.5" cy="5" r="2.7"/><circle cx="24" cy="5" r="2.7"/><circle cx="24" cy="10.5" r="2.7"/><circle cx="16.5" cy="16" r="2.7"/><circle cx="9" cy="21.5" r="2.7"/><circle cx="9" cy="27" r="2.7"/><circle cx="16.5" cy="27" r="2.7"/><circle cx="24" cy="27" r="2.7"/></svg>
    Zorko
  </div>
  <div class="muted" id="stats">Заведений в базе: 0</div>
</header>

<section class="panel" aria-label="Поиск заведений">
  <form class="row" id="scan-form">
    <label class="grow">Город, можно несколько через запятую<input id="city" placeholder="Львов, Дрогобыч" required></label>
    <button class="main" id="scan-btn" type="submit">Найти заведения</button>
    <button id="check-btn" type="button" title="Для тех, у кого сайт не указан в карте, Zorko попробует найти сайт сам, а найденные сайты проверит">Искать и проверять сайты</button>
    <button id="stop-btn" type="button" disabled>Остановить</button>
    <button id="ping-btn" type="button" title="Покажет, отвечают ли серверы карт вашему компьютеру">Проверить связь</button>
  </form>
  <div class="cats" id="cats" role="group" aria-label="Категории заведений"></div>
  <div class="row" style="margin-top:12px">
    <label class="check"><input id="deep" type="checkbox"> Проверить всё заново, даже проверенное</label>
    <label class="check" title="Zorko подберёт имя аккаунта по названию и проверит, есть ли такой профиль. Ссылку из описания профиля Instagram отдаёт только в браузере, поэтому её смотрите сами по ссылке в строке."><input id="insta" type="checkbox"> Искать аккаунты в Instagram (медленно, до 300 заведений за раз)</label>
  </div>
  <div style="margin-top:14px;display:flex;flex-direction:column;gap:6px">
    <div class="bar" role="progressbar" aria-label="Ход задачи" aria-valuemin="0" aria-valuemax="100" id="bar"><i></i></div>
    <div class="muted" id="job-msg">Выберите категории, введите город и нажмите «Найти заведения».</div>
  </div>
</section>

<section class="panel" aria-label="Ваши данные для черновиков">
  <div class="row">
    <label class="grow">Ваше имя, для черновика сообщения<input id="my-name" placeholder="Например: Андрей"></label>
    <label class="grow" style="flex-grow:3">Что вы предлагаете<input id="offer" placeholder="делаю сайты для местного бизнеса"></label>
    <label>Язык сообщений<select id="lang"><option value="ua">Українська</option><option value="ru">Русский</option></select></label>
  </div>
  <div class="muted" style="margin-top:8px">Текст собирается под каждое заведение отдельно: по его виду, городу и тому, что нашлось у его сайта.</div>
</section>

<section class="panel" aria-label="Заведения">
  <div class="row" style="margin-bottom:12px">
    <label>Сайт<select id="f-site">
      <option value="lead">Кому нужен сайт</option>
      <option value="none">Сайта нет совсем</option>
      <option value="social">Только соцсеть</option>
      <option value="bad">Сайт с проблемами</option>
      <option value="found">Сайт нашёлся сам</option>
      <option value="site">Сайт есть в карте</option>
      <option value="all">Все</option>
    </select></label>
    <label>Город<select id="f-city"><option value="">Все города</option></select></label>
    <label>Статус<select id="f-status"><option value="">Любой</option></select></label>
    <label>Сортировка<select id="f-sort">
      <option value="score">По приоритету</option>
      <option value="name">По названию</option>
      <option value="city">По городу</option>
      <option value="new">Сначала новые</option>
    </select></label>
    <label class="grow">Поиск по названию и адресу<input id="f-text" type="search"></label>
    <label>Контакты<select id="f-contact"><option value="">Любые</option><option value="any">Есть хоть какой-то</option><option value="phone">Есть телефон</option><option value="insta">Есть Instagram</option></select></label>
    <label class="check"><input id="f-chain" type="checkbox" checked> Скрыть сети</label>
    <label class="check"><input id="f-hidden" type="checkbox"> Показать скрытые</label>
  </div>
  <div class="row" style="margin-bottom:12px">
    <button type="button" id="csv-btn">Сохранить в CSV</button>
    <button type="button" id="clear-btn">Очистить базу</button>
    <span class="muted" id="count" style="align-self:center"></span>
  </div>
  <div class="wrap">
    <table>
      <thead><tr><th>Приоритет</th><th>Заведение</th><th>Контакты</th><th>Сайт</th><th>Статус</th><th>Заметка</th><th>Действия</th></tr></thead>
      <tbody id="rows"></tbody>
    </table>
  </div>
  <div class="more"><button type="button" id="more-btn" hidden>Показать ещё</button></div>
</section>

<footer>Данные карты © участники OpenStreetMap. Zorko ничего никому не отправляет: писать заведениям решаете и пишете вы сами.</footer>
</main>

<dialog id="draft-dlg" aria-labelledby="draft-title">
  <h2 id="draft-title" style="margin:0 0 4px;font-size:20px">Черновик сообщения</h2>
  <div class="muted" id="draft-contact"></div>
  <div class="row" id="draft-links" style="margin:10px 0 12px;gap:8px"></div>
  <div class="row" id="draft-tabs" role="group" aria-label="Вид сообщения" style="margin-bottom:12px"></div>
  <textarea id="draft-text" aria-label="Текст черновика"></textarea>
  <div class="row" style="margin-top:12px;justify-content:flex-end">
    <span class="muted" id="copy-msg" style="margin-right:auto"></span>
    <button type="button" id="copy-btn" class="main">Скопировать</button>
    <button type="button" id="close-btn">Закрыть</button>
  </div>
</dialog>

<dialog id="site-dlg" aria-labelledby="site-title">
  <h2 id="site-title" style="margin:0 0 12px;font-size:20px">У них есть сайт</h2>
  <p class="muted" id="site-hint" style="margin:0 0 12px">Нашли сайт в описании профиля или в поиске? Впишите его: заведение уйдёт из списка, а адрес останется в базе и в выгрузке.</p>
  <label>Адрес сайта<input id="site-input" type="text" placeholder="example.com" style="width:100%"></label>
  <p class="err" id="site-msg" style="margin:10px 0 0" hidden></p>
  <div class="row" style="margin-top:12px;justify-content:flex-end">
    <button type="button" id="site-save" class="main">Сохранить</button>
    <button type="button" id="site-cancel">Отмена</button>
  </div>
</dialog>

<dialog id="clear-dlg" aria-labelledby="clear-title">
  <h2 id="clear-title" style="margin:0 0 12px;font-size:20px">Очистить базу?</h2>
  <p class="muted">Будут удалены все найденные заведения вместе со статусами, заметками и найденными сайтами. Вернуть их нельзя.</p>
  <div class="row" style="margin-top:12px;justify-content:flex-end">
    <button type="button" id="clear-yes" class="main">Удалить всё</button>
    <button type="button" id="clear-no">Отмена</button>
  </div>
</dialog>
<div id="toast" role="status" aria-live="polite"></div>

<script>
const $ = (s) => document.querySelector(s);
const PAGE_SIZE = 200;
function el(tag, props, ...kids) {
  const n = document.createElement(tag);
  for (const k in (props || {})) {
    if (k === 'class') n.className = props[k];
    else if (k === 'text') n.textContent = props[k];
    else if (k.startsWith('on')) n.addEventListener(k.slice(2), props[k]);
    else if (props[k] !== null && props[k] !== undefined) n.setAttribute(k, props[k]);
  }
  for (const c of kids) if (c != null) n.append(c);
  return n;
}
async function api(path, body) {
  const opt = body ? { method: 'POST', headers: { 'Content-Type': 'application/json', 'X-Zorko': '1' }, body: JSON.stringify(body) } : {};
  const r = await fetch(path, opt);
  const j = await r.json();
  if (!r.ok) throw new Error(j.error || ('Ошибка ' + r.status));
  return j;
}
let places = [], rev = -1, statuses = [], cats = [], ready = false, shown = PAGE_SIZE, toastTimer = 0;

function toast(text) {
  const n = $('#toast'); n.textContent = text; n.classList.add('on');
  clearTimeout(toastTimer); toastTimer = setTimeout(() => n.classList.remove('on'), 4500);
}
function showError(e) { const m = $('#job-msg'); m.className = 'err'; m.textContent = e.message || String(e); toast(m.textContent); }

function uiState() {
  return {
    cats: [...document.querySelectorAll('[data-cat]')].filter((c) => c.checked).map((c) => c.dataset.cat),
    city: $('#city').value, site: $('#f-site').value, sort: $('#f-sort').value,
    contact: $('#f-contact').value, chain: $('#f-chain').checked
  };
}
function saveUi() { api('/api/settings', { ui: JSON.stringify(uiState()) }).catch(() => {}); }

function visible() {
  const site = $('#f-site').value, st = $('#f-status').value, city = $('#f-city').value;
  const text = $('#f-text').value.trim().toLowerCase(), hideChains = $('#f-chain').checked;
  const contact = $('#f-contact').value, withHidden = $('#f-hidden').checked;
  const list = places.filter((p) => {
    if (p.hidden && !withHidden) return false;
    if (hideChains && p.chain) return false;
    if (contact === 'phone' && !p.phone) return false;
    if (contact === 'any' && !(p.phone || p.email || p.socials || p.instagram)) return false;
    if (contact === 'insta' && !(p.instagram || /instagram/i.test(p.socials || ''))) return false;
    if (st && p.status !== st) return false;
    if (city && p.city !== city) return false;
    if (site === 'lead' && !(p.site_state === 'none' || p.site_state === 'social')) return false;
    if (site === 'none' && p.site_state !== 'none') return false;
    if (site === 'social' && p.site_state !== 'social') return false;
    if (site === 'found' && p.site_state !== 'found') return false;
    if (site === 'site' && p.site_state !== 'site') return false;
    if (site === 'bad' && !p.issues.length) return false;
    if (text && !((p.name + ' ' + p.address + ' ' + p.city).toLowerCase().includes(text))) return false;
    return true;
  });
  const sort = $('#f-sort').value;
  const by = {
    score: (a, b) => b.score - a.score || a.name.localeCompare(b.name, 'ru'),
    name: (a, b) => a.name.localeCompare(b.name, 'ru'),
    city: (a, b) => (a.city || '').localeCompare(b.city || '', 'ru') || b.score - a.score,
    new: (a, b) => String(b.found_at || '').localeCompare(String(a.found_at || '')) || b.score - a.score
  };
  return list.sort(by[sort] || by.score);
}
function safeLink(url) {
  const u = /^https?:\/\//i.test(url) ? url : 'http://' + url;
  try { const p = new URL(u); return (p.protocol === 'http:' || p.protocol === 'https:') ? p.href : null; } catch (e) { return null; }
}
const NET = {
  instagram: ['Instagram', 'https://instagram.com/'], facebook: ['Facebook', 'https://facebook.com/'],
  telegram: ['Telegram', 'https://t.me/'], tiktok: ['TikTok', 'https://tiktok.com/@'],
  vk: ['VK', 'https://vk.com/'], youtube: ['YouTube', 'https://youtube.com/']
};
function handleOf(value) {
  const v = String(value || '').trim().replace(/^@/, '');
  if (!v) return null;
  if (/^https?:\/\//i.test(v)) {
    const u = safeLink(v);
    return u ? { url: u, name: '' } : null;
  }
  return { url: '', name: v.replace(/^.*\//, '') };
}
function digitsOf(value) {
  return String(value || '').split(/[;,]/)[0].replace(/\D/g, '');
}
// Ссылки, по которым можно написать заведению в один клик.
function linksFor(p) {
  const out = [], seen = new Set();
  const add = (title, url) => { if (url && !seen.has(title)) { seen.add(title); out.push({ title, url }); } };
  for (const part of String(p.socials || '').split(';')) {
    const text = part.trim(); if (!text) continue;
    const i = text.indexOf(':'); if (i < 0) continue;
    const key = text.slice(0, i).trim().toLowerCase(), value = text.slice(i + 1).trim();
    if (key === 'whatsapp') { const d = digitsOf(value); if (d.length >= 9) add('WhatsApp', 'https://wa.me/' + d); continue; }
    if (key === 'viber') { const d = digitsOf(value); if (d.length >= 9) add('Viber', 'viber://chat?number=%2B' + d); continue; }
    const h = handleOf(value); if (!h) continue;
    const net = NET[key];
    if (net) add(net[0], h.url || (net[1] + h.name));
    else if (h.url) add(key, h.url);
  }
  if (p.site) {
    const host = (p.site.match(/^(?:https?:\/\/)?([^\/]+)/i) || [])[1] || '';
    for (const key in NET) if (host.toLowerCase().includes(key)) add(NET[key][0], safeLink(p.site));
  }
  if (p.instagram) add('Instagram', 'https://instagram.com/' + p.instagram);
  const d = digitsOf(p.phone);
  if (d.length >= 9) { add('Telegram', 'https://t.me/+' + d); add('Viber', 'viber://chat?number=%2B' + d); add('WhatsApp', 'https://wa.me/' + d); add('Позвонить', 'tel:+' + d); }
  if (p.email) add('Почта', 'mailto:' + p.email);
  return out;
}
function linkRow(p, cls) {
  const box = el('div', { style: 'display:flex;flex-wrap:wrap;gap:6px;margin-top:6px' });
  for (const l of linksFor(p)) box.append(el('a', { class: cls || 'mini', href: l.url, target: '_blank', rel: 'noopener noreferrer', text: l.title }));
  return box.childNodes.length ? box : null;
}
function siteCell(p) {
  const td = el('td');
  if (p.site_state === 'none') td.append(el('span', { class: 'tag none', text: p.searched_at ? 'сайта нет, искали' : 'сайта нет в карте' }));
  else if (p.site_state === 'social') td.append(el('span', { class: 'tag none', text: 'только соцсеть' }));
  else if (p.site_state === 'found') td.append(el('span', { class: 'tag', text: 'сайт нашёлся: ' + (p.found_how || '') }));
  else if (!p.checked_at) td.append(el('span', { class: 'tag', text: 'сайт не проверен' }));
  else if (!p.issues.length) td.append(el('span', { class: 'tag ok', text: 'проблем не найдено' }));
  for (const i of p.issues) td.append(el('span', { class: 'tag bad', text: i }));
  const href = p.site && safeLink(p.site);
  if (href) td.append(el('div', null, el('a', { href, target: '_blank', rel: 'noopener noreferrer', text: p.site.replace(/^https?:\/\//i, '').slice(0, 44) })));
  if (p.instagram && p.site_state === 'none') td.append(el('div', null, el('a', { href: 'https://instagram.com/' + p.instagram, target: '_blank', rel: 'noopener noreferrer', text: 'Instagram: @' + p.instagram })));
  if (p.hidden) td.append(el('div', { class: 'muted', text: p.hidden_why || 'скрыто' }));
  return td;
}
function save(p) { api('/api/place', { id: p.id, status: p.status, note: p.note }).then((j) => { rev = j.rev; toast('Сохранено'); }).catch(showError); }
async function hide(ids, on) {
  try { const j = await api('/api/hide', { ids, hide: on }); rev = j.rev; for (const p of places) if (ids.includes(p.id)) p.hidden = on ? 1 : 0; render(); toast(on ? 'Скрыто' : 'Возвращено'); }
  catch (e) { showError(e); }
}
function render() {
  const list = visible(), body = $('#rows');
  body.replaceChildren();
  for (const p of list.slice(0, shown)) {
    const sel = el('select', { 'aria-label': 'Статус: ' + p.name, onchange: (e) => { p.status = e.target.value; save(p); } });
    for (const [v, t] of statuses) { const o = el('option', { value: v, text: t }); if (v === p.status) o.selected = true; sel.append(o); }
    const note = el('input', { value: p.note || '', 'aria-label': 'Заметка: ' + p.name, placeholder: 'заметка', onchange: (e) => { p.note = e.target.value; save(p); } });
    const contacts = el('td');
    for (const c of [p.phone, p.email, p.socials]) if (c) contacts.append(el('div', { text: c }));
    if (!contacts.childNodes.length) contacts.append(el('span', { class: 'muted', text: 'контактов на карте нет' }));
    const links = linkRow(p);
    if (links) contacts.append(links);
    const q = encodeURIComponent(p.name + ' ' + (p.city || '') + ' ' + (p.address || ''));
    const row = el('tr', {
      class: (p.hidden ? 'dim ' : '') + 'pick',
      title: 'Нажмите на строку, чтобы собрать текст для этого заведения',
      onclick: (e) => { if (!e.target.closest('a, button, select, input, textarea')) openDraft(p); }
    },
      el('td', null, el('span', { class: 'score' + (p.score >= 70 ? ' hi' : ''), text: String(p.score) })),
      el('td', null,
        el('div', { text: p.name, style: 'font-weight:700;text-decoration:underline;text-underline-offset:3px' }),
        el('div', { class: 'muted', text: [p.kind, p.address, p.city].filter(Boolean).join(' · ') }),
        p.chain ? el('span', { class: 'tag', text: 'сеть' }) : null),
      contacts, siteCell(p), el('td', null, sel), el('td', null, note),
      el('td', null, el('div', { style: 'display:flex;flex-direction:column;gap:6px;min-width:146px' },
        el('a', { class: 'mini', href: 'https://www.google.com/search?q=' + q, target: '_blank', rel: 'noopener noreferrer', text: 'Найти в Google' }),
        el('a', { class: 'mini', href: 'https://www.openstreetmap.org/' + encodeURI(p.id), target: '_blank', rel: 'noopener noreferrer', text: 'На карте' }),
        el('button', { type: 'button', text: 'У них есть сайт', onclick: () => askSite(p) }),
        el('button', { type: 'button', text: p.hidden ? 'Вернуть' : 'Скрыть', onclick: () => hide([p.id], !p.hidden) }))));
    body.append(row);
  }
  $('#count').textContent = 'Показано ' + Math.min(list.length, shown) + ' из ' + list.length;
  $('#more-btn').hidden = list.length <= shown;
}
let draftPick = 'short';
async function openDraft(p) {
  try {
    const j = await api('/api/draft?id=' + encodeURIComponent(p.id));
    const tabs = $('#draft-tabs');
    tabs.replaceChildren();
    const show = (v) => {
      draftPick = v.key; $('#draft-text').value = v.text; $('#copy-msg').textContent = '';
      for (const b of tabs.children) {
        const on = b.dataset.key === v.key;
        b.classList.toggle('main', on); b.setAttribute('aria-pressed', String(on));
      }
    };
    for (const v of j.variants) tabs.append(el('button', { type: 'button', 'data-key': v.key, text: v.title, onclick: () => show(v) }));
    show(j.variants.find((v) => v.key === draftPick) || j.variants[0]);
    $('#draft-title').textContent = 'Черновик для «' + j.name + '»';
    $('#draft-contact').textContent = j.contact ? ('Куда писать: ' + j.contact) : 'Контактов в карте нет: ищите через «Найти в Google»';
    const box = $('#draft-links');
    box.replaceChildren();
    for (const l of linksFor(p)) box.append(el('a', { class: 'mini', style: 'padding:9px 14px', href: l.url, target: '_blank', rel: 'noopener noreferrer', text: l.title }));
    if (!box.childNodes.length) box.append(el('a', { class: 'mini', style: 'padding:9px 14px', href: 'https://www.google.com/search?q=' + encodeURIComponent(p.name + ' ' + (p.city || '')), target: '_blank', rel: 'noopener noreferrer', text: 'Найти в Google' }));
    $('#draft-dlg').showModal();
  } catch (e) { showError(e); }
}
async function loadPlaces() {
  const j = await api('/api/places'); places = j.places; rev = j.rev;
  const sel = $('#f-city'), cur = sel.value, cities = [...new Set(places.map((p) => p.city).filter(Boolean))].sort();
  sel.replaceChildren(el('option', { value: '', text: 'Все города' }));
  for (const c of cities) sel.append(el('option', { value: c, text: c }));
  sel.value = cities.includes(cur) ? cur : '';
  render();
}
function minutes(sec) { return sec < 90 ? 'меньше двух минут' : 'примерно ' + Math.round(sec / 60) + ' мин'; }
function buildCats(list, saved) {
  const box = $('#cats');
  box.replaceChildren();
  for (const [key, title] of list) {
    const input = el('input', { type: 'checkbox', 'data-cat': key, onchange: saveUi });
    if (saved ? saved.includes(key) : key === 'food') input.checked = true;
    box.append(el('label', { class: 'check' }, input, el('span', { text: title })));
  }
  box.append(el('label', { class: 'check' }, el('input', {
    type: 'checkbox', onchange: (e) => { for (const c of document.querySelectorAll('[data-cat]')) c.checked = e.target.checked; saveUi(); }
  }), el('span', { text: 'Выбрать все' })));
}
async function refresh() {
  const s = await api('/api/state');
  if (!ready) {
    ready = true; statuses = s.statuses; cats = s.categories;
    let saved = null;
    try { saved = JSON.parse(s.settings.ui || 'null'); } catch (e) {}
    buildCats(cats, saved && saved.cats);
    for (const [v, t] of s.statuses) $('#f-status').append(el('option', { value: v, text: t }));
    $('#my-name').value = s.settings.my_name || ''; $('#offer').value = s.settings.offer || '';
    $('#lang').value = s.settings.lang === 'ru' ? 'ru' : 'ua';
    if (saved) {
      $('#city').value = saved.city || '';
      $('#f-site').value = saved.site || 'lead'; $('#f-sort').value = saved.sort || 'score';
      $('#f-contact').value = saved.contact || ''; $('#f-chain').checked = saved.chain !== false;
    }
  }
  const j = s.job, pct = j.total ? Math.round(100 * j.done / j.total) : 0;
  $('#bar').firstElementChild.style.width = pct + '%';
  $('#bar').setAttribute('aria-valuenow', String(pct));
  const msg = $('#job-msg');
  let text = j.error || j.msg || '';
  if (!j.error && j.kind === 'ping' && !j.running && j.msg) { msg.className = 'muted'; msg.textContent = j.msg; }
  if (!j.error && j.running && j.kind === 'scan') text += '. Найдено на карте: ' + j.found + ', новых: ' + j.added;
  if (!j.error && j.running && j.kind === 'check' && j.found) text += '. Сайтов нашлось: ' + j.found;
  if (!j.error && j.running && j.eta) text += '. Осталось ' + minutes(j.eta);
  if (!j.error && !j.running && j.msg === 'Остановлено' && j.total) text += ' на ' + j.done + ' из ' + j.total + '. Найденное сохранено.';
  msg.className = j.error ? 'err' : 'muted';
  if (text) msg.textContent = text;
  $('#scan-btn').disabled = $('#check-btn').disabled = $('#clear-btn').disabled = $('#ping-btn').disabled = j.running;
  $('#stop-btn').disabled = !j.running;
  const st = s.stats, total = (st.none || 0) + (st.social || 0) + (st.site || 0) + (st.found || 0);
  $('#stats').textContent = 'В базе: ' + total + ' · без сайта: ' + (st.none || 0) + ' · только соцсеть: ' +
    (st.social || 0) + ' · сайт нашёлся: ' + (st.found || 0) + ' · сайт в карте: ' + (st.site || 0) +
    (st.hidden ? ' · скрыто: ' + st.hidden : '');
  const editing = document.activeElement && document.activeElement.closest('#rows');
  if (s.rev !== rev && !editing) await loadPlaces();
}
async function tick() {
  try { await refresh(); }
  catch (e) { $('#job-msg').className = 'err'; $('#job-msg').textContent = 'Нет связи с программой. Проверьте, что чёрное окно Zorko не закрыто.'; }
  setTimeout(tick, 1000);
}
async function act(fn) { try { await fn(); await refresh(); } catch (e) { showError(e); } }
$('#scan-form').addEventListener('submit', (e) => {
  e.preventDefault();
  act(async () => {
    const chosen = [...document.querySelectorAll('[data-cat]')].filter((c) => c.checked).map((c) => c.dataset.cat);
    if (!chosen.length) throw new Error('Выберите хотя бы одну категорию.');
    await api('/api/scan', { cities: $('#city').value, cats: chosen });
    saveUi(); $('#f-site').value = 'lead'; toast('Поиск запущен');
  });
});
$('#check-btn').addEventListener('click', () => act(async () => {
  await api('/api/check', { deep: $('#deep').checked, insta: $('#insta').checked });
  toast('Ищу сайты и проверяю их. Это самая долгая часть, можно остановить в любой момент.');
}));
$('#stop-btn').addEventListener('click', () => act(async () => { await api('/api/stop', {}); toast('Остановлено'); }));
$('#ping-btn').addEventListener('click', () => act(async () => { await api('/api/ping', {}); toast('Проверяю связь с серверами карт'); }));
$('#csv-btn').addEventListener('click', () => act(async () => {
  const ids = visible().map((p) => p.id);
  if (!ids.length) throw new Error('Показывать нечего: измените фильтры.');
  const j = await api('/api/export-file', { ids });
  toast('Сохранено строк: ' + j.rows + '. Файл: ' + j.path);
}));
let sitePlace = null;
function askSite(p) {
  sitePlace = p;
  $('#site-msg').hidden = true;
  $('#site-input').value = p.site || '';
  $('#site-title').textContent = 'Сайт для «' + p.name + '»';
  $('#site-dlg').showModal();
  $('#site-input').focus();
}
$('#site-cancel').addEventListener('click', () => $('#site-dlg').close());
$('#site-save').addEventListener('click', async () => {
  const value = $('#site-input').value.trim(), msg = $('#site-msg');
  if (!value) { msg.hidden = false; msg.textContent = 'Впишите адрес сайта или нажмите «Отмена».'; return; }
  try {
    const j = await api('/api/mark-site', { id: sitePlace.id, site: value });
    rev = j.rev; $('#site-dlg').close(); await loadPlaces();
    toast('Записано: у «' + sitePlace.name + '» есть сайт');
  } catch (e) { msg.hidden = false; msg.textContent = e.message; }
});
$('#site-input').addEventListener('keydown', (e) => { if (e.key === 'Enter') { e.preventDefault(); $('#site-save').click(); } });
$('#clear-btn').addEventListener('click', () => $('#clear-dlg').showModal());
$('#clear-no').addEventListener('click', () => $('#clear-dlg').close());
$('#clear-yes').addEventListener('click', () => act(async () => { await api('/api/clear', {}); $('#clear-dlg').close(); toast('База очищена'); }));
$('#more-btn').addEventListener('click', () => { shown += PAGE_SIZE; render(); });
for (const id of ['#f-site', '#f-status', '#f-chain', '#f-city', '#f-sort', '#f-contact', '#f-hidden']) {
  $(id).addEventListener('change', () => { shown = PAGE_SIZE; render(); saveUi(); });
}
$('#f-text').addEventListener('input', () => { shown = PAGE_SIZE; render(); });
$('#city').addEventListener('change', saveUi);
$('#my-name').addEventListener('change', (e) => act(async () => { await api('/api/settings', { my_name: e.target.value }); toast('Сохранено'); }));
$('#offer').addEventListener('change', (e) => act(async () => { await api('/api/settings', { offer: e.target.value }); toast('Сохранено'); }));
$('#lang').addEventListener('change', (e) => act(async () => { await api('/api/settings', { lang: e.target.value }); toast('Язык сообщений сохранён'); }));
$('#close-btn').addEventListener('click', () => $('#draft-dlg').close());
$('#copy-btn').addEventListener('click', async () => {
  const t = $('#draft-text');
  try { await navigator.clipboard.writeText(t.value); $('#copy-msg').textContent = 'Скопировано'; toast('Скопировано'); }
  catch (e) { t.select(); $('#copy-msg').textContent = 'Нажмите Ctrl+C, чтобы скопировать'; }
});
tick();
</script>
</body>
</html>
"""


def main():
    init_db()
    try:
        server = ThreadingHTTPServer((HOST, PORT), Handler)
    except OSError:
        print("Порт %d занят. Возможно, Zorko уже запущен: откройте http://%s:%d" % (PORT, HOST, PORT))
        webbrowser.open("http://%s:%d" % (HOST, PORT))
        return 1
    url = "http://%s:%d" % (HOST, PORT)
    print("Zorko запущен: %s" % url)
    print("Не закрывайте это окно, пока работаете. Чтобы выйти, нажмите Ctrl+C или закройте окно.")
    if "--no-browser" not in sys.argv:
        threading.Timer(0.8, webbrowser.open, args=(url,)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
