import os
import re
import sqlite3
import time
import hashlib
import json
import threading
import uuid
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone, timedelta
from functools import wraps
from html import escape
from urllib.parse import urlparse, urljoin
from html.parser import HTMLParser

import requests
from flask import Flask, jsonify, redirect, render_template_string, request, session, url_for

app = Flask(__name__)
app.secret_key = os.getenv("SECRET_KEY", "change-this-in-render")

SERPAPI_KEY = os.getenv("SERPAPI_KEY", "").strip()
APP_USERNAME = os.getenv("APP_USERNAME", "flowforgeweb")
APP_PASSWORD = os.getenv("APP_PASSWORD", "").strip()
DB_PATH = os.getenv("LEADS_DB_PATH", "/tmp/flowforge_leads.db")
SEEN_TTL_DAYS = int(os.getenv("SEEN_TTL_DAYS", "120"))
SERPAPI_NO_CACHE = os.getenv("SERPAPI_NO_CACHE", "false").lower() in {"1", "true", "yes", "on"}
REQUEST_TIMEOUT = int(os.getenv("REQUEST_TIMEOUT", "12"))
SEARCH_WORKERS = max(1, min(int(os.getenv("SEARCH_WORKERS", "3")), 5))
SEARCH_CACHE_SECONDS = 3600
JOB_STALE_SECONDS = 180
JOB_CONTEXT = threading.local()

QUALITY_FILTER_VERSION = "independent-rendered-v1"
RENDER_LOCK = threading.Lock()

MAX_MAP_PAGES = max(1, min(int(os.getenv("MAX_MAP_PAGES", "5")), 6))

ALLOWED_STATES = {
    "Kentucky", "Ohio", "Indiana", "Illinois", "Missouri", "Tennessee", "Virginia", "West Virginia"
}

BUSINESS_CATEGORIES = [
    ("landscaper", "Landscaping"),
    ("lawn care service", "Lawn Care"),
    ("roofing contractor", "Roofing"),
    ("restaurant", "Restaurant"),
    ("auto detailing", "Auto Detailing"),
    ("pressure washing service", "Pressure Washing"),
    ("plumber", "Plumbing"),
    ("hvac contractor", "HVAC"),
    ("electrician", "Electrician"),
    ("cleaning service", "Cleaning Service"),
    ("barber shop", "Barber Shop"),
    ("hair salon", "Hair Salon"),
    ("tree service", "Tree Service"),
    ("concrete contractor", "Concrete Contractor"),
    ("painting contractor", "Painting Contractor"),
    ("handyman", "Handyman"),
    ("moving company", "Moving Company"),
    ("pest control service", "Pest Control"),
    ("fence contractor", "Fence Contractor"),
    ("remodeling contractor", "Remodeling Contractor"),
    ("general contractor", "General Contractor"),
    ("flooring contractor", "Flooring Contractor"),
    ("junk removal service", "Junk Removal"),
    ("car wash", "Car Wash"),
    ("mechanic", "Auto Repair / Mechanic"),
]

SEARCH_PROFILES = {
    # candidate_target is the number of PRE-SCREENED businesses to fully verify.
    # Raw Maps rows rejected as chains, established/strong sites, inactive, duplicates,
    # or previously rejected do not consume one of these slots.
    5: {"map_pages": 3, "candidate_target": 15, "candidate_cap": 15, "label": "5 businesses · light request use"},
    10: {"map_pages": 4, "candidate_target": 30, "candidate_cap": 30, "label": "10 businesses · balanced request use"},
    15: {"map_pages": 5, "candidate_target": 45, "candidate_cap": 45, "label": "15 businesses · higher request use"},
}

DIRECTORY_OR_SOCIAL_DOMAINS = {
    "facebook.com", "m.facebook.com", "instagram.com", "linkedin.com", "yelp.com", "yellowpages.com",
    "mapquest.com", "tripadvisor.com", "bbb.org", "chamberofcommerce.com", "angi.com", "thumbtack.com",
    "nextdoor.com", "alignable.com", "foursquare.com", "bizapedia.com", "dnb.com", "manta.com",
    "google.com", "maps.google.com", "bing.com", "x.com", "twitter.com", "tiktok.com", "youtube.com"
}

SOCIAL_DOMAINS = {"facebook.com", "m.facebook.com", "instagram.com", "linkedin.com", "x.com", "twitter.com", "tiktok.com"}

GENERIC_NAME_WORDS = {
    "the", "and", "of", "llc", "inc", "company", "co", "services", "service", "business", "group",
    "restaurant", "cafe", "shop", "store", "center", "centre", "solutions"
}

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124 Safari/537.36"
    )
}


def now_iso():
    return datetime.now(timezone.utc).isoformat()


def db_connect():
    folder = os.path.dirname(DB_PATH)
    if folder:
        os.makedirs(folder, exist_ok=True)
    conn = sqlite3.connect(DB_PATH, timeout=30)
    conn.row_factory = sqlite3.Row
    return conn


def init_db():
    with db_connect() as conn:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS seen_businesses (
                signature TEXT PRIMARY KEY,
                name TEXT,
                address TEXT,
                phone TEXT,
                classification TEXT,
                checked_at TEXT NOT NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS qualified_leads (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                signature TEXT,
                name TEXT,
                address TEXT,
                phone TEXT,
                website TEXT,
                classification TEXT,
                tier TEXT,
                confidence INTEGER,
                improvement_score INTEGER,
                active_score INTEGER,
                reasons TEXT,
                best_sales_angle TEXT,
                sales_script TEXT,
                created_at TEXT NOT NULL
            )
            """
        )
        columns = {row[1] for row in conn.execute("PRAGMA table_info(qualified_leads)").fetchall()}
        if "tier" not in columns:
            conn.execute("ALTER TABLE qualified_leads ADD COLUMN tier TEXT")
        if "best_sales_angle" not in columns:
            conn.execute("ALTER TABLE qualified_leads ADD COLUMN best_sales_angle TEXT")
        if "sales_script" not in columns:
            conn.execute("ALTER TABLE qualified_leads ADD COLUMN sales_script TEXT")
        conn.execute("""CREATE TABLE IF NOT EXISTS search_cache (
            cache_key TEXT PRIMARY KEY, response_json TEXT NOT NULL, expires_at REAL NOT NULL
        )""")
        conn.execute("""CREATE TABLE IF NOT EXISTS search_jobs (
            id TEXT PRIMARY KEY, status TEXT NOT NULL, payload_json TEXT NOT NULL,
            heartbeat REAL NOT NULL, created_at REAL NOT NULL
        )""")
        conn.commit()


init_db()


def normalize_space(value):
    return re.sub(r"\s+", " ", (value or "").strip())


def digits(value):
    return re.sub(r"\D", "", value or "")


def business_signature(name, address, phone):
    raw = "|".join([
        QUALITY_FILTER_VERSION,
        re.sub(r"[^a-z0-9]", "", (name or "").lower()),
        re.sub(r"[^a-z0-9]", "", (address or "").lower()),
        digits(phone)[-10:],
    ])
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def seen_recently(signature):
    """Skip only durable outcomes. Temporary/uncertain failures must stay retryable."""
    cutoff = datetime.now(timezone.utc) - timedelta(days=SEEN_TTL_DAYS)
    durable = {
        "REJECT", "REJECT_CHAIN", "REJECT_INACTIVE", "REJECT_GOOD_WEBSITE",
        "NO_WEBSITE", "WEAK_WEBSITE",
    }
    with db_connect() as conn:
        row = conn.execute(
            "SELECT classification, checked_at FROM seen_businesses WHERE signature = ?", (signature,)
        ).fetchone()
    if not row or row["classification"] not in durable:
        return False
    try:
        checked = datetime.fromisoformat(row["checked_at"])
        return checked >= cutoff
    except Exception:
        return False


def mark_seen(signature, name, address, phone, classification="REJECT"):
    with db_connect() as conn:
        conn.execute(
            """
            INSERT INTO seen_businesses(signature, name, address, phone, classification, checked_at)
            VALUES (?, ?, ?, ?, ?, ?)
            ON CONFLICT(signature) DO UPDATE SET
                name=excluded.name,
                address=excluded.address,
                phone=excluded.phone,
                classification=excluded.classification,
                checked_at=excluded.checked_at
            """,
            (signature, name, address, phone, classification, now_iso()),
        )
        conn.commit()


def save_lead(lead):
    with db_connect() as conn:
        conn.execute(
            """
            INSERT INTO qualified_leads(
                signature, name, address, phone, website, classification, tier,
                confidence, improvement_score, active_score, reasons,
                best_sales_angle, sales_script, created_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                lead["signature"], lead["name"], lead["address"], lead["phone"], lead.get("website", ""),
                lead["classification"], lead.get("tier", "C"), lead["confidence"], lead.get("improvement_score", 0),
                lead["active_score"], " | ".join(lead.get("reasons", [])),
                lead.get("best_sales_angle", ""), lead.get("sales_script", ""), now_iso(),
            ),
        )
        conn.commit()


def login_required(fn):
    @wraps(fn)
    def wrapped(*args, **kwargs):
        if not session.get("logged_in"):
            return redirect(url_for("login", next=request.path))
        return fn(*args, **kwargs)
    return wrapped


class SearchProviderError(RuntimeError):
    pass


def job_update(job_id, payload=None, status=None):
    with db_connect() as conn:
        if payload is None:
            conn.execute("UPDATE search_jobs SET heartbeat=? WHERE id=? AND status='running'",
                         (time.time(), job_id))
        else:
            conn.execute("UPDATE search_jobs SET payload_json=?, status=?, heartbeat=? WHERE id=? AND status='running'",
                         (json.dumps(payload), status or "running", time.time(), job_id))
        conn.commit()


def get_job(job_id):
    with db_connect() as conn:
        row = conn.execute("SELECT * FROM search_jobs WHERE id=?", (job_id,)).fetchone()
    if not row:
        return None
    result = json.loads(row["payload_json"])
    result.update({"job_id": row["id"], "status": row["status"]})
    return result


def check_job_alive():
    job_id = getattr(JOB_CONTEXT, "job_id", None)
    if job_id:
        state = get_job(job_id)
        if not state or state["status"] != "running":
            raise SearchProviderError("This search was interrupted. Start a new search when ready.")
        job_update(job_id)


def serpapi(params):
    if not SERPAPI_KEY:
        raise SearchProviderError("SERPAPI_KEY is not configured in Render.")
    check_job_alive()
    cache_key = hashlib.sha256(json.dumps(params, sort_keys=True).encode()).hexdigest()
    if not SERPAPI_NO_CACHE:
        with db_connect() as conn:
            cached = conn.execute("SELECT response_json FROM search_cache WHERE cache_key=? AND expires_at>?",
                                  (cache_key, time.time())).fetchone()
        if cached:
            return json.loads(cached["response_json"])
    payload = dict(params)
    payload["api_key"] = SERPAPI_KEY
    payload["output"] = "json"
    if SERPAPI_NO_CACHE:
        payload["no_cache"] = "true"

    last_error = None
    for attempt in range(2):
        try:
            resp = requests.get("https://serpapi.com/search", params=payload, timeout=REQUEST_TIMEOUT + 8)
            last_error = None
            break
        except requests.RequestException as exc:
            last_error = exc
            if attempt == 0:
                time.sleep(0.65)
                check_job_alive()
    if last_error is not None:
        raise SearchProviderError("Search provider did not respond after a retry. This business was skipped; the scan can continue.") from None
    if resp.status_code >= 400:
        raise SearchProviderError(f"Search provider returned HTTP {resp.status_code}. Check your SerpApi quota/account.")
    try:
        data = resp.json()
    except ValueError:
        raise SearchProviderError("Search provider returned an unreadable response.") from None
    if data.get("error"):
        message = str(data["error"]).replace(SERPAPI_KEY, "[redacted]")
        raise SearchProviderError(message)
    if not SERPAPI_NO_CACHE:
        with db_connect() as conn:
            conn.execute("DELETE FROM search_cache WHERE expires_at<=?", (time.time(),))
            conn.execute("INSERT OR REPLACE INTO search_cache VALUES (?,?,?)",
                         (cache_key, json.dumps(data), time.time() + SEARCH_CACHE_SECONDS))
            conn.commit()
    return data


def google_search(query, location=None, num=10):
    params = {"engine": "google", "q": query, "num": num, "hl": "en", "gl": "us"}
    if location:
        params["location"] = location
    return serpapi(params)


def maps_search(query, location, requested_pages=None):
    all_results = []
    page_limit = MAX_MAP_PAGES if requested_pages is None else max(1, min(int(requested_pages), MAX_MAP_PAGES))
    for page in range(page_limit):
        params = {
            "engine": "google_maps",
            "type": "search",
            "q": query,
            "location": location,
            "z": "13",
            "hl": "en",
            "start": page * 20,
        }
        data = serpapi(params)
        rows = data.get("local_results") or []
        if not rows:
            break
        all_results.extend(rows)
        if len(rows) < 20:
            break
    return all_results


def hostname(url):
    if not url:
        return ""
    try:
        candidate = url if "://" in url else "https://" + url
        host = urlparse(candidate).hostname or ""
        return host.lower().removeprefix("www.")
    except Exception:
        return ""


def is_directory_or_social(url):
    host = hostname(url)
    return any(host == d or host.endswith("." + d) for d in DIRECTORY_OR_SOCIAL_DOMAINS)


def is_social(url):
    host = hostname(url)
    return any(host == d or host.endswith("." + d) for d in SOCIAL_DOMAINS)


def name_tokens(name):
    toks = re.findall(r"[a-z0-9]+", (name or "").lower())
    return {t for t in toks if len(t) >= 3 and t not in GENERIC_NAME_WORDS}


def likely_owned_website(url, title, business_name):
    if not url or is_directory_or_social(url):
        return False
    b_tokens = name_tokens(business_name)
    if not b_tokens:
        return True
    host_text = hostname(url).replace("-", " ").replace("_", " ")
    title_text = (title or "").lower()
    overlap = sum(1 for t in b_tokens if t in host_text or t in title_text)
    return overlap >= max(1, round(len(b_tokens) * 0.45))


def extract_map_website(row):
    direct = row.get("website") or ""
    if direct and not is_directory_or_social(direct):
        return direct
    links = row.get("links") or {}
    if isinstance(links, dict):
        for key in ("website", "menu", "order"):
            value = links.get(key)
            if isinstance(value, str) and value and not is_directory_or_social(value):
                return value
    return ""


def active_score(row, web_signal=False, social_signal=False, recent_activity=False):
    open_state = str(row.get("open_state") or "").lower()
    if "permanently closed" in open_state or "closed permanently" in open_state:
        return 0, ["Google Maps marks the business permanently closed"]

    score = 30
    reasons = ["Current Google Maps listing found"]

    if row.get("phone"):
        score += 18
        reasons.append("Public phone number present")
    if row.get("address"):
        score += 8
    if row.get("hours") or row.get("operating_hours"):
        score += 12
        reasons.append("Business hours are listed")

    reviews = row.get("reviews") or 0
    try:
        reviews = int(reviews)
    except Exception:
        reviews = 0
    if reviews >= 1:
        score += 8
        reasons.append("Has customer reviews")
    if reviews >= 10:
        score += 7
    if reviews >= 50:
        score += 5

    if row.get("rating"):
        score += 3
    if open_state and "open" in open_state:
        score += 4
    if web_signal:
        score += 5
        reasons.append("Current web search presence found")
    if social_signal:
        score += 5
        reasons.append("Social/business-profile presence found")
    if recent_activity:
        score += 8
        reasons.append("Recent online activity signal found")

    return min(score, 100), reasons


def organic_rows(data):
    return data.get("organic_results") or []


def _presence_from_searches(name, searches):
    owned_site = ""
    owned_title = ""
    social_found = False
    directory_found = False
    recent_activity = False
    total_organic = 0
    chain_reasons = []
    current_year = str(datetime.now().year)
    for _, data in searches:
        for item in organic_rows(data):
            total_organic += 1
            link = item.get("link") or ""
            title = item.get("title") or ""
            snippet = str(item.get("snippet") or "")
            date_text = str(item.get("date") or "")
            recency_text = f"{title} {snippet} {date_text}".lower()
            if name_tokens(name) & name_tokens(title) and chain_text_signal(f"{title} {snippet}"):
                chain_reasons.append("Search result describes this brand as a chain, franchise, or multi-location business")
            if current_year in recency_text or re.search(r"\b(?:today|yesterday|\d+\s+(?:day|days|week|weeks|month|months)\s+ago)\b", recency_text):
                recent_activity = True
            if is_social(link):
                social_found = True
            elif is_directory_or_social(link):
                directory_found = True
            elif not owned_site and likely_owned_website(link, title, name):
                owned_site = link
                owned_title = title
    return {
        "owned_site": owned_site, "owned_title": owned_title, "social_found": social_found,
        "directory_found": directory_found, "recent_activity": recent_activity,
        "web_signal": total_organic > 0, "queries_checked": len(searches), "chain_reasons": chain_reasons,
    }


def search_business_presence(name, city, state, phone=""):
    """Credit-aware verification: one search first; use a second only if no owned site is found."""
    location = f"{city}, {state}, United States"
    searches = []
    primary = f'"{name}" "{city}" {state}'
    searches.append((primary, google_search(primary, location=location, num=10)))
    result = _presence_from_searches(name, searches)
    if result["owned_site"]:
        return result
    secondary = f'"{name}" "{city}" website'
    searches.append((secondary, google_search(secondary, location=location, num=10)))
    return _presence_from_searches(name, searches)



def map_recent_activity_signal(row):
    """Best-effort recent activity clue from Maps result fields without another request."""
    text = " ".join(str(v) for v in row.values() if v is not None).lower()
    current_year = str(datetime.now().year)
    if current_year in text:
        return True
    return bool(re.search(
        r"\b(?:today|yesterday|\d+\s+(?:day|days|week|weeks|month|months)\s+ago)\b",
        text
    ))

# Name/domain matches plus live ownership evidence; this list is a first-pass exclusion, not the whole filter.
CHAIN_NAMES = {
    "mcdonalds", "burger king", "wendys", "taco bell", "kfc", "kentucky fried chicken", "subway",
    "chipotle", "qdoba", "chick fil a", "raising canes", "zaxbys", "bojangles", "popeyes", "arbys",
    "sonic drive in", "dairy queen", "five guys", "shake shack", "whataburger", "culvers", "freddys",
    "white castle", "cook out", "jack in the box", "hardees", "carls jr", "in n out burger",
    "dominos", "pizza hut", "papa johns", "little caesars", "marcos pizza", "hungry howies",
    "blaze pizza", "mod pizza", "jets pizza", "donatos", "mellow mushroom", "snappy tomato pizza",
    "panera bread", "jimmy johns", "jersey mikes", "firehouse subs", "potbelly", "penn station",
    "mcalisters deli", "jasons deli", "schlotzskys", "panda express", "pei wei", "pf changs",
    "olive garden", "longhorn steakhouse", "texas roadhouse", "outback steakhouse", "cheddars scratch kitchen",
    "applebees", "chilis", "tgi fridays", "red lobster", "red robin", "buffalo wild wings",
    "wingstop", "hooters", "twin peaks", "dave and busters", "cracker barrel", "ihop", "dennys",
    "waffle house", "first watch", "bob evans", "golden corral", "ruths chris", "the cheesecake factory",
    "starbucks", "dunkin", "tim hortons", "dutch bros", "7 brew", "tropical smoothie cafe",
    "smoothie king", "jamba", "crumbl", "nothing bundt cakes", "baskin robbins", "cold stone",
    "insomnia cookies", "krispy kreme", "nazs halal", "nazs halal food", "roosters", "drakes",
    "tonys of bowling green", "tonys of lexington", "tonys of cincinnati", "tonys steak and seafood",
    "great clips", "supercuts", "sport clips", "fantastic sams", "massage envy", "hand and stone",
    "planet fitness", "anytime fitness", "orangetheory", "snap fitness", "jiffy lube", "valvoline",
    "midas", "meineke", "firestone", "goodyear", "aamco", "take 5 oil change", "safelite",
    "mr handyman", "mr rooter", "molly maid", "merry maids", "servpro", "servicemaster",
    "roto rooter", "one hour heating", "benjamin franklin plumbing", "mister sparky", "trugreen",
    "lawn doctor", "the grounds guys", "mosquito joe", "the maids", "two men and a truck",
    "college hunks", "1 800 got junk", "budget blinds", "ace hardware", "the ups store",
    "7 eleven", "circle k", "dollar general", "dollar tree", "family dollar", "walmart", "target",
    "kroger", "walgreens", "cvs", "autozone", "oreilly auto parts", "advance auto parts", "pep boys",
}
CHAIN_DOMAINS = {
    "nazshalal.com", "nazshalalfranchising.com", "mcdonalds.com", "burgerking.com", "wendys.com",
    "tacobell.com", "kfc.com", "subway.com", "chipotle.com", "chick-fil-a.com", "dominos.com",
    "pizzahut.com", "papajohns.com", "starbucks.com", "dunkindonuts.com", "greatclips.com",
    "servpro.com", "trugreen.com", "planetfitness.com", "valvoline.com", "jiffylube.com",
    "tonysofcincinnati.com",
}


def normalized_brand(value):
    return re.sub(r"\s+", " ", re.sub(r"[^a-z0-9 ]", "", (value or "").lower().replace("&", " and "))).strip()


def known_chain(name, website=""):
    brand = normalized_brand(name)
    for chain in CHAIN_NAMES:
        if brand == chain or brand.startswith(chain + " "):
            return True
    host = hostname(website)
    return any(host == d or host.endswith("." + d) for d in CHAIN_DOMAINS)


def chain_text_signal(text):
    return bool(re.search(
        r"\b(?:restaurant chain|national chain|regional chain|franchise opportunities|franchis(?:ing|ees?)|"
        r"become a franchise|our franchise|over \d+ locations|more than \d+ locations|"
        r"\d+ (?:restaurant |store |business )?locations|locations nationwide|multiple locations)\b",
        text or "", re.I))


class SiteDocument(HTMLParser):
    def __init__(self, html, base):
        super().__init__(convert_charrefs=True)
        self.base = base
        self.skip = 0
        self.text = []
        self.links = []
        self.styles = []
        self.viewport = False
        self.feed(html)
    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag in {"script", "style", "noscript"}:
            self.skip += 1
        if tag == "a" and a.get("href"):
            self.links.append(urljoin(self.base, a["href"]))
        if tag == "link" and "stylesheet" in a.get("rel", "").lower() and a.get("href"):
            self.styles.append(urljoin(self.base, a["href"]))
        if tag == "meta" and a.get("name", "").lower() == "viewport":
            self.viewport = True
    def handle_endtag(self, tag):
        if tag in {"script", "style", "noscript"} and self.skip:
            self.skip -= 1
    def handle_data(self, data):
        if not self.skip:
            self.text.append(data)


def homepage_url(url):
    if "://" in (url or "") and not re.match(r"^https?://", url or "", re.I):
        return ""
    candidate = url if re.match(r"^https?://", url or "", re.I) else "https://" + (url or "")
    u = urlparse(candidate)
    if u.scheme not in {"http", "https"} or not u.hostname or u.username or u.password:
        return ""
    if u.hostname.lower() in {"localhost", "127.0.0.1", "::1"}:
        return ""
    path = "/"
    # Preserve tenant roots rather than auditing another business on a shared host.
    if u.hostname.lower().endswith("wixsite.com"):
        segment = u.path.strip("/").split("/")[0]
        if not segment:
            return ""
        path = "/" + segment + "/"
    return f"{u.scheme}://{u.netloc}{path}"


def fetch_site_document(url):
    check_job_alive()
    response = requests.get(url, headers=HEADERS, timeout=REQUEST_TIMEOUT, allow_redirects=True)
    if response.status_code >= 400 or "text/html" not in response.headers.get("Content-Type", "").lower():
        raise ValueError("Website could not be reliably evaluated")
    html = response.text[:1_500_000]
    doc = SiteDocument(html, response.url)
    text = normalize_space(" ".join(doc.text))
    if re.search(r"verify (?:you are|you're) human|checking your browser|access denied|just a moment|captcha", text, re.I):
        raise ValueError("Website presented an access challenge")
    return response.url, html, doc, text


def ownership_check(url, doc, text, html):
    if known_chain("", url) or chain_text_signal(text):
        return "chain", "Official website indicates a chain, franchise, or multi-location brand"
    # Location and franchise pages are verified instead of treating the mere word 'location' as a chain.
    franchise_links = [u for u in doc.links if re.search(r"franchis", u, re.I)]
    if franchise_links:
        return "chain", "Official website links to a franchise program"
    location_links = list(dict.fromkeys(u for u in doc.links if hostname(u) == hostname(url) and re.search(r"/(?:locations|our-locations|stores|find-a-location)(?:[/#?_-]|$)", urlparse(u).path, re.I)))
    if location_links:
        for link in location_links[:1]:
            try:
                _, page, location_doc, location_text = fetch_site_document(link)
            except (requests.RequestException, ValueError):
                return "uncertain", "Could not verify whether this brand has multiple locations"
            if chain_text_signal(location_text):
                return "chain", "Official location directory indicates multiple locations"
            addresses = set(re.findall(r'"streetAddress"\s*:\s*"([^"]+)"', page, re.I))
            # Explicit store/location-detail links, not menu categories or map links.
            locations = {u.rstrip("/") for u in location_doc.links if hostname(u)==hostname(url) and re.search(r"/(?:locations?|stores)/[^/?#]+", urlparse(u).path, re.I)}
            if len(addresses) >= 2 or len(locations) >= 2:
                return "chain", "Official website lists at least two distinct business locations"
            return "uncertain", "Location directory could not establish a single independent business"
    addresses = set(re.findall(r'"streetAddress"\s*:\s*"([^"]+)"', html, re.I))
    if len(addresses) >= 2:
        return "chain", "Official structured business data lists multiple addresses"
    return "not_detected", "No chain/franchise evidence detected in the checks performed"


def quick_site_prescreen(url):
    """Zero-SerpApi, conservative pre-screen. Reject only clearly strong/established sites or chains."""
    target = homepage_url(url)
    if not target:
        return "keep", ""
    if known_chain("", target):
        return "chain", "Known chain/franchise domain"
    try:
        r = requests.get(target, headers=HEADERS, timeout=min(REQUEST_TIMEOUT, 6), allow_redirects=True)
        if r.status_code >= 400 or "text/html" not in r.headers.get("Content-Type", "").lower():
            return "keep", ""
        html = r.text[:900000]
        doc = SiteDocument(html, r.url)
        text = normalize_space(" ".join(doc.text))
        if known_chain("", r.url) or chain_text_signal(text):
            return "chain", "Website indicates a chain/franchise or multi-location brand"
        if any(re.search(r"franchis", u, re.I) for u in doc.links):
            return "chain", "Website links to franchise information"
        addresses = set(re.findall(r'"streetAddress"\s*:\s*"([^"]+)"', html, re.I))
        if len(addresses) >= 2:
            return "chain", "Website lists multiple business addresses"

        # Clear modern-site evidence only. Borderline sites continue to the full visual audit.
        score = 0
        img_count = len(re.findall(r"<img\b", html, re.I))
        heading_count = len(re.findall(r"<h[1-3]\b", html, re.I))
        internal_links = sum(1 for u in doc.links if hostname(u) == hostname(r.url))
        if doc.viewport:
            score += 1
        if len(doc.styles) >= 2 or re.search(r"@media|display\s*:\s*(?:grid|flex)|bootstrap|tailwind", html, re.I):
            score += 1
        if img_count >= 4 and heading_count >= 2:
            score += 1
        if internal_links >= 8 and len(text) >= 700:
            score += 1
        if re.search(r"order (?:online|now)|reservations?|book (?:now|a table)|view menu|request (?:a )?quote|schedule", text, re.I):
            score += 1
        if re.search(r"testimonial|reviews?|gallery|our work|portfolio", text, re.I):
            score += 1
        if score >= 5:
            return "strong", "Website already shows clear modern design/content/conversion signals"
    except requests.RequestException:
        pass
    except Exception:
        pass
    return "keep", ""


RENDER_METRICS_JS = r"""({deviceWidth}) => {
 const width=innerWidth,height=innerHeight,scale=Math.min(1,deviceWidth/innerWidth);
 const visible=e=>{const r=e.getBoundingClientRect(),s=getComputedStyle(e);return r.width>0&&r.height>0&&s.display!=='none'&&s.visibility!=='hidden'&&Number(s.opacity)!==0&&r.bottom>0&&r.top<height};
 const texts=[...document.querySelectorAll('p,li,h1,h2,h3,a,button,label')].filter(e=>visible(e)&&e.textContent.trim().length>=15);
 const small=texts.filter(e=>parseFloat(getComputedStyle(e).fontSize)*scale<11).length;
 const clipped=texts.filter(e=>{const r=e.getBoundingClientRect(),s=getComputedStyle(e);return (r.left< -15||r.right>width+30)&&s.position!=='absolute'&&s.position!=='fixed'&&s.transform==='none'}).length;
 const images=[...document.images].filter(e=>visible(e)&&e.width>=80&&e.height>=50);
 const broken=images.filter(e=>e.complete&&e.naturalWidth===0).length;
 const bodyStyle=getComputedStyle(document.body);
 const oldMarkup=!!document.querySelector('frameset,marquee,font');
 const fixedLayouts=[...document.querySelectorAll('table,main,#wrapper,#container')].filter(e=>{const r=e.getBoundingClientRect();return visible(e)&&r.width>deviceWidth*1.25}).length;
 return {width, text_count:texts.length, tiny_text_count:small, clipped_text_count:clipped, visible_images:images.length, broken_images:broken,
         overflow_ratio:document.documentElement.scrollWidth/width, fixed_layouts:fixedLayouts, old_markup:oldMarkup,
         body_font:bodyStyle.fontFamily, body_text:document.body.innerText.slice(0,100000), stylesheets:document.styleSheets.length,
         headings:document.querySelectorAll('h1,h2,h3').length, links:document.querySelectorAll('a[href]').length};
}"""


def rendered_site_check(url):
    """Inspect actual computed styles/layout after external CSS and JavaScript load, on two viewports."""
    try:
        from playwright.sync_api import sync_playwright
    except ImportError:
        return None, "Visual checker unavailable: install the updated requirements and Chromium"
    reports = {}
    try:
        with RENDER_LOCK, sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-dev-shm-usage"])
            try:
                for label, viewport in [("desktop", {"width":1440,"height":1000}), ("mobile", {"width":390,"height":844})]:
                    check_job_alive()
                    context = browser.new_context(viewport=viewport, device_scale_factor=1, is_mobile=label=="mobile", has_touch=label=="mobile")
                    page = context.new_page()
                    page.set_default_timeout(15000)
                    blocked_assets = []
                    page.on("response", lambda response: blocked_assets.append(response.url) if response.status in {401,403,429} and response.request.resource_type in {"document","stylesheet","image","script"} and hostname(response.url)==hostname(url) else None)
                    response = page.goto(url, wait_until="load", timeout=20000)
                    if response is None or response.status >= 400:
                        return None, "Website did not load reliably in the visual checker"
                    try:
                        page.evaluate("() => Promise.race([document.fonts.ready, new Promise(r => setTimeout(r, 2000))])")
                    except Exception:
                        pass
                    page.wait_for_timeout(700)
                    metrics = page.evaluate(RENDER_METRICS_JS, {"deviceWidth":viewport["width"]})
                    if blocked_assets or re.search(r"verify (?:you are|you're) human|checking your browser|access denied|just a moment|captcha", metrics["body_text"], re.I):
                        return None, "Website blocked rendering; visual quality is uncertain"
                    if len(normalize_space(metrics["body_text"])) < 120:
                        return None, "Too little rendered content to verify website quality"
                    reports[label] = metrics
                    context.close()
            finally:
                browser.close()
    except Exception:
        # A missing browser, bot block or network failure must never become a 'weak website'.
        return None, "Website could not be visually verified; excluded from weak-site leads"
    return reports, ""


def visual_weakness_score(reports, text, doc):
    desktop, mobile = reports["desktop"], reports["mobile"]
    score, reasons, families = 0, [], set()
    if mobile["overflow_ratio"] >= 1.25 and mobile["clipped_text_count"] >= 3 and mobile["fixed_layouts"] >= 1:
        score += 40;families.add("layout")
        reasons.append("Rendered mobile layout is substantially wider than the screen and clips multiple text blocks")
    if mobile["tiny_text_count"] >= 6 and mobile["tiny_text_count"] >= max(1,mobile["text_count"])*0.4:
        score += 35;families.add("readability")
        reasons.append("At least 40% of visible mobile text blocks render below 11px and are difficult to read")
    if desktop["visible_images"] >= 2 and desktop["broken_images"] >= 2 and desktop["broken_images"] >= desktop["visible_images"]*0.5:
        score += 35;families.add("broken_imagery")
        reasons.append("At least half of the visible desktop images render broken")
    if mobile["old_markup"] and mobile["fixed_layouts"] and not doc.viewport:
        score += 30;families.add("legacy_nonresponsive")
        reasons.append("Rendered fixed-width legacy layout has no mobile viewport configuration")
    # Conversion gaps can strengthen real visual defects; they cannot qualify a polished site by themselves.
    functional = re.search(r"book (?:a table|a seat|now)|reservations?|order (?:now|online)|view menu|menus?", text, re.I)
    if not functional and not re.search(r"contact|quote|schedule|call", text, re.I):
        score += 8;reasons.append("No clear customer contact, ordering, booking or menu path found")
    qualified = len(families) >= 2 and score >= 65
    return min(score,100) if qualified else min(score,64), reasons, qualified


def website_improvement_score(url):
    """Conservative homepage audit: real rendered defects are required, never missing HTML tokens."""
    target = homepage_url(url)
    if not target:
        return None, ["Could not identify the business homepage"], {"uncertain":True}
    key = hashlib.sha256((QUALITY_FILTER_VERSION+"|website|"+target).encode()).hexdigest()
    if not SERPAPI_NO_CACHE:
        with db_connect() as conn:
            hit = conn.execute("SELECT response_json FROM search_cache WHERE cache_key=? AND expires_at>?",(key,time.time())).fetchone()
        if hit:
            return tuple(json.loads(hit["response_json"]))
    details = {"homepage_url":target, "visual_verified":False, "filter_version":QUALITY_FILTER_VERSION}
    if known_chain("", target):
        details["chain"] = True
        details["ownership_status"] = "chain"
        return 0,["Known chain/franchise website"],details
    try:
        final, html, doc, text = fetch_site_document(target)
        details["final_url"] = final
        ownership, reason = ownership_check(final,doc,text,html)
        details["ownership_status"] = ownership
        if ownership == "chain":
            details["chain"] = True
            outcome = (0,[reason],details)
        elif ownership == "uncertain":
            details["uncertain"] = True
            return None,[reason],details
        else:
            # Read linked styles rather than assuming the homepage contains CSS declarations.
            def css_read(link):
                try:
                    r=requests.get(link,headers=HEADERS,timeout=min(REQUEST_TIMEOUT,8))
                    return r.text[:250000] if r.status_code==200 else ""
                except requests.RequestException:
                    return ""
            with ThreadPoolExecutor(max_workers=SEARCH_WORKERS) as pool:
                css = "\n".join(pool.map(css_read, list(dict.fromkeys(doc.styles))[:3]))
            details["external_stylesheets"] = len(doc.styles)
            details["responsive_css_detected"] = bool(re.search(r"@media|display\s*:\s*(?:grid|flex)",css,re.I))
            # Functional features are positive evidence, not proof of visual polish.
            details["booking_ordering_detected"] = bool(re.search(r"book (?:a table|a seat|now)|reservations?|order (?:now|online)|opentable|toasttab|doordash|ubereats|tpgo",text+" "+" ".join(doc.links),re.I))
            reports, error = rendered_site_check(final)
            if reports is None:
                details["uncertain"] = True
                return None,[error],details
            score,reasons,qualified = visual_weakness_score(reports,text,doc)
            details.update({"visual_verified":True,"visually_weak":qualified,"desktop":{k:v for k,v in reports['desktop'].items() if k!='body_text'},"mobile":{k:v for k,v in reports['mobile'].items() if k!='body_text'}})
            outcome=(score,reasons,details)
    except (requests.RequestException,ValueError):
        details["uncertain"] = True
        return None,["Homepage could not be reliably evaluated"],details
    if not SERPAPI_NO_CACHE:
        with db_connect() as conn:
            conn.execute("INSERT OR REPLACE INTO search_cache VALUES (?,?,?)",(key,json.dumps(outcome),time.time()+SEARCH_CACHE_SECONDS));conn.commit()
    return outcome


def best_sales_angle(classification, reasons):
    """Return the best call angle and matching wording from the FlowForgeWeb call script."""
    joined = " ".join(reasons or []).lower()

    if classification == "NO_WEBSITE":
        return (
            "NO WEBSITE FOUND — strongest angle",
            "I couldn’t find a dedicated website for your business, even though you’re active online. "
            "We could build you a professional site that gives customers one place to see your services, "
            "contact you, and learn more about the business."
        )

    if any(x in joined for x in ["responsive mobile viewport", "mobile", "media quer"]):
        return (
            "MOBILE / RESPONSIVE ISSUES",
            "The current website could be easier to use on phones. Since a lot of customers search from mobile, "
            "we could make it cleaner, faster, and much easier to navigate."
        )

    if any(x in joined for x in ["call-to-action", "conversion path", "contact/quote form", "tap-to-call", "email link"]):
        return (
            "WEAK CALL-TO-ACTION / CONTACT FLOW",
            "It isn’t very easy for a customer to immediately call, request a quote, book, or contact you from the website. "
            "We could make that path much clearer so the site does a better job turning visitors into customers."
        )

    if any(x in joined for x in ["services/menu", "services", "menu information"]):
        return (
            "SERVICES / MENU ARE HARD TO FIND",
            "I noticed your services or menu aren’t presented as clearly as they could be. "
            "We could redesign that so customers immediately understand what you offer and how to take the next step."
        )

    if any(x in joined for x in ["trust signal", "review", "proof-of-work", "testimonial", "portfolio"]):
        return (
            "WEAK TRUST / REVIEWS / PORTFOLIO",
            "The site could do more to show customer reviews, past work, photos, or other trust signals. "
            "We could make those much more visible so new customers feel more confident reaching out."
        )

    if any(x in joined for x in ["stale", "very little useful business content", "thin", "missing or weak page title"]):
        return (
            "STALE OR THIN WEBSITE",
            "The website looks like it may not have been updated in a while and doesn’t show much about the business. "
            "We could give it a fresher look and make it much more useful to potential customers."
        )

    if any(x in joined for x in [
        "visual structure", "outdated", "legacy html", "table-based", "modern visual-design",
        "under-designed", "no meaningful imagery", "no clear navigation"
    ]):
        return (
            "OUTDATED / UNDER-DESIGNED WEBSITE",
            "I found your current website, and there looks to be a strong opportunity to modernize the design "
            "and make the business look more polished online."
        )

    return (
        "GENERAL FALLBACK — only when no single issue stands out",
        "I found your business while researching local companies and saw a few areas where your online presence could be improved. "
        "We’d be happy to show you a free sample rather than just trying to explain it over the phone."
    )


def full_call_script(business_name, angle_script):
    return (
        f"Hi, could I speak with the owner or manager? My name is [Your Name], and I’m with FlowForgeWeb. "
        f"We build custom websites for local businesses. I came across {business_name} and noticed: {angle_script} "
        "We’d be happy to put together a free sample showing what an improved website could look like for your business. "
        "If you like it, we can talk about next steps — no obligation. What’s the best email or phone number to send it to?"
    )

def lead_tier(classification, confidence, improvement_score, active_score):
    # Tier A: strongest/easiest pitch — active business with no owned website.
    if classification == "NO_WEBSITE" and confidence >= 95 and active_score >= 60:
        return "A"
    # Tier B: active business with a clearly poor website and strong improvement case.
    if classification == "WEAK_WEBSITE" and improvement_score >= 80 and confidence >= 85 and active_score >= 60:
        return "B"
    # Tier C: still qualified, but the improvement case is less overwhelming.
    return "C"


def evaluate_business(row, city, state):
    name = normalize_space(row.get("title") or row.get("name") or "")
    address = normalize_space(row.get("address") or "")
    phone = normalize_space(row.get("phone") or "")
    if not name:
        return None

    sig = business_signature(name, address, phone)
    if seen_recently(sig):
        return {"skip": "seen", "signature": sig}

    if known_chain(name, extract_map_website(row)):
        mark_seen(sig, name, address, phone, "REJECT_CHAIN")
        return {"skip":"chain", "signature":sig}

    # This is an upper bound: even all possible web/social/recency bonuses cannot rescue it.
    maximum_active, _ = active_score(row, web_signal=True, social_signal=True, recent_activity=True)
    if maximum_active < 60:
        mark_seen(sig, name, address, phone, "REJECT_INACTIVE")
        return {"skip": "inactive", "signature": sig}

    map_site = extract_map_website(row)
    map_site_assessment = None
    if map_site:
        map_site_assessment = website_improvement_score(map_site)
        improvement, _, details = map_site_assessment
        if details.get("chain"):
            mark_seen(sig,name,address,phone,"REJECT_CHAIN")
            return {"skip":"chain","signature":sig}
        if details.get("uncertain") or improvement is None:
            return {"skip": "uncertain", "signature": sig}
        if improvement < 65:
            mark_seen(sig, name, address, phone, "REJECT_GOOD_WEBSITE")
            return {"skip": "good_website", "signature": sig}

    if map_site:
        # Maps already gave us the owned site; avoid paid Google verification searches.
        presence = {"owned_site": map_site, "social_found": False, "directory_found": False,
                    "recent_activity": False, "web_signal": True, "queries_checked": 0, "chain_reasons": []}
    else:
        presence = search_business_presence(name, city, state, phone)
    site = map_site or presence["owned_site"]
    if presence.get("chain_reasons") or known_chain(name,site):
        mark_seen(sig,name,address,phone,"REJECT_CHAIN")
        return {"skip":"chain","signature":sig}

    recent_activity = presence.get("recent_activity", False) or map_recent_activity_signal(row)
    active, active_reasons = active_score(
        row,
        web_signal=presence["web_signal"] or bool(map_site),
        social_signal=presence["social_found"],
        recent_activity=recent_activity,
    )

    if active < 60:
        mark_seen(sig, name, address, phone, "REJECT_INACTIVE")
        return {"skip": "inactive", "signature": sig}

    reasons = list(active_reasons)

    if not site:
        confidence = 80
        confidence += 5  # Maps checked
        confidence += min(10, presence["queries_checked"] * 5)
        if presence["social_found"]:
            confidence += 2
            reasons.append("Social profile found, but no owned website found")
        if presence["directory_found"]:
            confidence += 2
            reasons.append("Directory listings found, but no owned website found")
        confidence = min(confidence, 99)

        if confidence >= 95:
            reasons.insert(0, "No owned website found after Maps + web + social/directory checks")
            angle_title, angle_script = best_sales_angle("NO_WEBSITE", reasons)
            lead = {
                "signature": sig,
                "name": name,
                "address": address,
                "phone": phone,
                "website": "",
                "classification": "NO_WEBSITE",
                "tier": lead_tier("NO_WEBSITE", confidence, 100, active),
                "confidence": confidence,
                "improvement_score": 100,
                "active_score": active,
                "reasons": reasons,
                "best_sales_angle": angle_title,
                "sales_angle_script": angle_script,
                "sales_script": full_call_script(name, angle_script),
                "maps_rating": row.get("rating"),
                "maps_reviews": row.get("reviews"),
            }
            mark_seen(sig, name, address, phone, "NO_WEBSITE")
            save_lead(lead)
            return lead

        return {"skip": "uncertain", "signature": sig}

    improvement, weak_reasons, site_details = map_site_assessment or website_improvement_score(site)
    if site_details.get("chain"):
        mark_seen(sig,name,address,phone,"REJECT_CHAIN")
        return {"skip":"chain","signature":sig}
    if site_details.get("uncertain") or improvement is None:
        return {"skip": "uncertain", "signature": sig}

    if improvement >= 65 and site_details.get("visual_verified") and site_details.get("visually_weak"):
        confidence = min(99, 70 + round(improvement * 0.25) + (5 if active >= 75 else 0))
        reasons.insert(0, f"Homepage rendered on desktop and mobile; confirmed visual weakness score is {improvement}/100")
        reasons.extend(weak_reasons)
        angle_title, angle_script = best_sales_angle("WEAK_WEBSITE", reasons)
        lead = {
            "signature": sig,
            "name": name,
            "address": address,
            "phone": phone,
            "website": site_details.get("final_url") or site_details.get("homepage_url") or site,
            "classification": "WEAK_WEBSITE",
            "tier": lead_tier("WEAK_WEBSITE", confidence, improvement, active),
            "confidence": confidence,
            "improvement_score": improvement,
            "active_score": active,
            "reasons": reasons,
            "best_sales_angle": angle_title,
            "sales_angle_script": angle_script,
            "sales_script": full_call_script(name, angle_script),
            "site_details": site_details,
            "maps_rating": row.get("rating"),
            "maps_reviews": row.get("reviews"),
        }
        mark_seen(sig, name, address, phone, "WEAK_WEBSITE")
        save_lead(lead)
        return lead

    mark_seen(sig, name, address, phone, "REJECT_GOOD_WEBSITE")
    return {"skip": "good_website", "signature": sig}


LOGIN_TEMPLATE = """
<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>FlowForge Leads Login</title>
<style>
body{font-family:Arial,sans-serif;background:#0b0f14;color:#f5f7fa;display:grid;place-items:center;min-height:100vh;margin:0}
.card{width:min(420px,90vw);background:#141a22;border:1px solid #273241;border-radius:18px;padding:28px;box-shadow:0 20px 50px #0008}
input,button{width:100%;box-sizing:border-box;padding:13px;border-radius:10px;border:1px solid #334155;margin-top:10px;background:#0f1720;color:white}
button{background:#fff;color:#111;font-weight:800;cursor:pointer}.err{color:#ff8c8c}</style></head><body>
<div class="card"><h1>FlowForge Leads</h1><p>Private business lead finder</p>
{% if error %}<p class="err">{{ error }}</p>{% endif %}
<form method="post"><input name="username" placeholder="Username" required><input name="password" type="password" placeholder="Password" required><button>Log in</button></form></div>
</body></html>
"""

APP_TEMPLATE = """
<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>FlowForge Lead Finder</title>
<style>
:root{--bg:#081018;--panel:#111c27;--border:#26384a;--text:#f6f8fb;--muted:#9fb1c3;--good:#8ef0b2;--warn:#ffd479;--blue:#8dc7ff}
*{box-sizing:border-box}body{font-family:Inter,Arial,sans-serif;background:var(--bg);color:var(--text);margin:0}.wrap{max-width:1180px;margin:0 auto;padding:28px}
.top{display:flex;justify-content:space-between;gap:20px;align-items:center}.panel{background:var(--panel);border:1px solid var(--border);border-radius:18px;padding:20px;margin-top:18px}
.grid{display:grid;grid-template-columns:2fr 1fr 1fr 1fr;gap:10px}input,select,button{padding:12px;border-radius:10px;border:1px solid #35506a;background:#0a141e;color:white;width:100%}
button{background:white;color:#0a1118;font-weight:800;cursor:pointer}.secondary{background:#17243a;color:#d7e9ff}.won{background:#163b27;color:#9cf3bb}.lost{background:#402329;color:#ffb4bb}.remove{background:#271b20;color:#ffc3c8}
small,.muted{color:var(--muted)}a{color:var(--blue)}.lead{border-top:1px solid var(--border);padding:18px 0}.lead:first-child{border-top:0}
.badge{display:inline-block;padding:5px 9px;border-radius:999px;background:#173427;color:var(--good);font-weight:800;font-size:12px}.weak{background:#3a3018;color:var(--warn)}
.tier{display:inline-block;padding:5px 9px;border-radius:999px;background:#17243a;color:#b9d7ff;font-weight:900;font-size:12px;margin-right:6px}.tierA{background:#153b26;color:#91f1b7}.tierB{background:#3a3018;color:#ffd479}.tierC{background:#2d293d;color:#cabdff}
.stats{display:flex;gap:12px;flex-wrap:wrap}.stat{background:#0b151f;border:1px solid var(--border);padding:10px 12px;border-radius:12px}.reason{margin:5px 0;color:#d8e0e8}
.angle{margin:14px 0;padding:14px;border:1px solid #35506a;background:#0a141e;border-radius:12px}.script{margin-top:8px;color:#dbe8f3;line-height:1.55}
.actions{display:flex;gap:10px;flex-wrap:wrap;margin-top:12px}.actions button{width:auto}
.pipeline-card{border-top:1px solid var(--border);padding:18px 0}.pipeline-card:first-child{border-top:0}.pipeline-head{display:flex;justify-content:space-between;gap:12px;align-items:flex-start}
.status-pill{font-size:12px;font-weight:900;border-radius:999px;padding:6px 10px;background:#17243a;color:#b9d7ff}
.range-wrap{margin:15px 0}.range-wrap input[type=range]{padding:0;border:0;background:transparent}.range-labels{display:grid;grid-template-columns:repeat(6,1fr);font-size:10px;color:var(--muted);gap:4px;text-align:center;margin-top:5px}
.pipeline-grid{display:grid;grid-template-columns:1.2fr 1fr;gap:12px}.remember{border-left:3px solid #ffd479;padding-left:10px}
@media(max-width:800px){.grid,.pipeline-grid{grid-template-columns:1fr}.top,.pipeline-head{align-items:flex-start;flex-direction:column}.range-labels{font-size:8px}.actions button{width:100%}}
</style></head><body><div class="wrap">
<div class="top"><div><h1>FlowForge Lead Finder</h1><p class="muted">Independent businesses only · new leads first · no-site or visually verified weak-site only</p></div><a href="/logout">Log out</a></div>
<div class="panel"><form id="searchForm"><div class="grid">
<select name="category" required><option value="">Business category</option>{% for value,label in categories %}<option value="{{value}}">{{label}}</option>{% endfor %}</select>
<input name="city" placeholder="City" required>
<select name="state" required><option value="">State</option>{% for s in states %}<option>{{s}}</option>{% endfor %}</select>
<select name="limit" required><option value="5">5 businesses · light requests</option><option value="10" selected>10 businesses · balanced</option><option value="15">15 businesses · deeper search</option></select>
</div><p class="muted" style="margin:10px 0 0">Larger batches search more Maps results and verify more candidates, so they use more SerpApi requests. Chains are excluded. Weak sites require verified desktop/mobile layout problems; uncertain sites are skipped.</p><button style="margin-top:10px">Find new qualified leads</button></form><p id="status" class="muted"></p></div>
<div id="results" class="panel" style="display:none"></div>
<div class="panel"><h2 style="margin-top:0">Lead Pipeline</h2><p class="muted">Click “Add to pipeline” on a qualified business. Status changes save automatically in this browser.</p><p class="muted remember"><b>Render Free:</b> this browser copy survives Render restarts on this device. Render Free itself does not permanently preserve the app’s local SQLite file.</p><div id="pipeline"></div></div>
</div><script>
const form=document.getElementById('searchForm'),statusEl=document.getElementById('status'),results=document.getElementById('results'),pipelineEl=document.getElementById('pipeline');
const PIPELINE_KEY='flowforge_pipeline_v2';
const REJECT_KEY='flowforge_rejected_businesses_v1';
const STAGES=['Called','Owner Reached','Sample Requested','Sample Sent','Follow-Up','Decision'];
function esc(v){return String(v??'').replace(/[&<>\"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','\"':'&quot;',"'":'&#39;'}[c]));}
function loadPipeline(){try{return JSON.parse(localStorage.getItem(PIPELINE_KEY)||'[]')}catch(_){return []}}
function loadRejects(){try{return JSON.parse(localStorage.getItem(REJECT_KEY)||'{}')}catch(_){return {}}}
function mergeRejects(rows){if(!Array.isArray(rows)||!rows.length)return;const saved=loadRejects();for(const x of rows){if(x&&x.signature)saved[x.signature]=x}const entries=Object.entries(saved).sort((a,b)=>String(b[1]?.saved_at||'').localeCompare(String(a[1]?.saved_at||''))).slice(0,2500);localStorage.setItem(REJECT_KEY,JSON.stringify(Object.fromEntries(entries)))}
function rejectedSignatures(){return Object.keys(loadRejects())}
function savePipeline(items){localStorage.setItem(PIPELINE_KEY,JSON.stringify(items));renderPipeline()}
function statusText(x){if(x.outcome==='won')return'Closed Won';if(x.outcome==='lost')return'Closed Lost';return STAGES[Math.max(0,Math.min(5,Number(x.stage||0)))]}
function addToPipeline(x){let items=loadPipeline();if(!items.some(z=>z.signature===x.signature)){items.unshift({...x,stage:0,outcome:'',added_at:new Date().toISOString()});savePipeline(items)}document.getElementById('pipeline').scrollIntoView({behavior:'smooth'})}
function setStage(sig,val){let items=loadPipeline(),x=items.find(z=>z.signature===sig);if(!x)return;x.stage=Number(val);x.outcome='';x.updated_at=new Date().toISOString();savePipeline(items)}
function setOutcome(sig,outcome){let items=loadPipeline(),x=items.find(z=>z.signature===sig);if(!x)return;x.outcome=outcome;x.updated_at=new Date().toISOString();savePipeline(items)}
function removePipeline(sig){savePipeline(loadPipeline().filter(z=>z.signature!==sig))}
function renderPipeline(){const items=loadPipeline();if(!items.length){pipelineEl.innerHTML='<p class="muted">No businesses added yet.</p>';return}pipelineEl.innerHTML=items.map(x=>`<div class="pipeline-card"><div class="pipeline-head"><div><b>${esc(x.name)}</b><div class="muted">${esc(x.phone||'')} ${x.address?'· '+esc(x.address):''}</div></div><span class="status-pill">${esc(statusText(x))}</span></div><div class="pipeline-grid"><div><div class="angle"><strong>Best sales angle: ${esc(x.best_sales_angle||'General')}</strong><div class="script">${esc(x.sales_angle_script||'')}</div></div><div class="range-wrap"><input type="range" min="0" max="5" step="1" value="${Number(x.stage||0)}" oninput="setStage('${esc(x.signature)}',this.value)"><div class="range-labels">${STAGES.map(s=>`<span>${esc(s)}</span>`).join('')}</div></div></div><div><b>Call wording</b><div class="script">${esc(x.sales_script||'')}</div><div class="actions"><button class="won" onclick="setOutcome('${esc(x.signature)}','won')">Closed Won</button><button class="lost" onclick="setOutcome('${esc(x.signature)}','lost')">Closed Lost</button><button class="remove" onclick="removePipeline('${esc(x.signature)}')">Remove</button></div></div></div></div>`).join('')}
function renderSearchResults(d){let html=`<div class="stats"><div class="stat"><b>${d.leads.length}</b><br><small>Qualified leads</small></div><div class="stat"><b>${d.tier_a}</b><br><small>Tier A</small></div><div class="stat"><b>${d.tier_b}</b><br><small>Tier B</small></div><div class="stat"><b>${d.tier_c}</b><br><small>Tier C</small></div><div class="stat"><b>${d.no_website}</b><br><small>No website</small></div><div class="stat"><b>${d.weak_website}</b><br><small>Weak website</small></div></div>`;if(!d.leads.length)html+=d.status==='error'?`<p class="muted">The search stopped before any leads could be verified.</p>`:`<p class="muted">No businesses met the strict filters in this batch. Try another nearby city/category or search again later.</p>`;d.leads.forEach((x,i)=>{const cls=x.classification==='WEAK_WEBSITE'?'badge weak':'badge',tierCls='tier tier'+esc(x.tier||'C');html+=`<div class="lead"><div><span class="${tierCls}">TIER ${esc(x.tier||'C')}</span><span class="${cls}">${esc(x.classification)}</span> <b>${esc(x.name)}</b></div><p>${esc(x.address)} ${x.phone?'· '+esc(x.phone):''}</p>${x.website?`<p><a target="_blank" rel="noopener" href="${esc(x.website)}">${esc(x.website)}</a></p>`:''}<p><b>Confidence:</b> ${x.confidence}% · <b>Active score:</b> ${x.active_score}/100${x.classification==='WEAK_WEBSITE'?` · <b>Improvement:</b> ${x.improvement_score}/100`:''}</p><div class="angle"><strong>BEST SALES ANGLE: ${esc(x.best_sales_angle)}</strong><div class="script">${esc(x.sales_angle_script)}</div><div class="script" style="margin-top:10px"><b>Full wording:</b> ${esc(x.sales_script)}</div></div>${x.reasons.slice(0,7).map(z=>`<div class="reason">• ${esc(z)}</div>`).join('')}<div class="actions"><button class="secondary" id="add-${i}">Add to lead pipeline ↓</button></div></div>`});results.innerHTML=html;results.style.display='block';d.leads.forEach((x,i)=>{const b=document.getElementById(`add-${i}`);if(b)b.onclick=()=>addToPipeline(x)})}
const searchButton=form.querySelector('button');
const SEARCH_JOB_KEY='flowforge_active_search_v1';
let monitoring=false;
function setSearching(on){searchButton.disabled=on;searchButton.textContent=on?'Search in progress…':'Find new qualified leads'}
async function readJSON(r){const type=r.headers.get('content-type')||'';if(!type.includes('application/json'))throw new Error('Server did not return a search response. Your search may still be running; refresh to reconnect.');return r.json()}
async function monitorSearch(jobId){
 if(monitoring)return;
 monitoring=true;setSearching(true);sessionStorage.setItem(SEARCH_JOB_KEY,jobId);
 let failures=0,lastResults='';
 try{
  while(true){
   let d;
   try{const r=await fetch('/api/search/'+encodeURIComponent(jobId),{cache:'no-store'});d=await readJSON(r);if(!r.ok){sessionStorage.removeItem(SEARCH_JOB_KEY);throw new Error(d.error||'Search unavailable')}failures=0}
   catch(err){if(!sessionStorage.getItem(SEARCH_JOB_KEY)||++failures>=5)throw err;statusEl.textContent='Reconnecting to your existing search…';await new Promise(resolve=>setTimeout(resolve,2000));continue}
   statusEl.textContent=d.message||'Searching and verifying businesses…';
   mergeRejects(d.reject_memory);
   const resultSignature=JSON.stringify(d.leads||[]);
   if(d.leads?.length&&resultSignature!==lastResults){renderSearchResults(d);lastResults=resultSignature}
   if(d.status==='done'||d.status==='error'){
    sessionStorage.removeItem(SEARCH_JOB_KEY);renderSearchResults(d);
    statusEl.textContent=d.status==='error'?'Error: '+d.error:`${d.request_profile} · candidate pool ${d.candidate_pool||0}/${d.candidate_target||d.candidate_cap||0} · verified ${d.checked} · skipped ${d.skipped_seen} already-seen · skipped ${d.skipped_chain||0} chains · returned ${d.leads.length}/${d.requested_limit} qualified active leads.`;
    break;
   }
   await new Promise(resolve=>setTimeout(resolve,1500));
  }
 }catch(err){statusEl.textContent='Error: '+err.message+(sessionStorage.getItem(SEARCH_JOB_KEY)?' Refresh to reconnect; do not start another search.':'')}
 finally{monitoring=false;setSearching(false)}
}
form.addEventListener('submit',async(e)=>{
 e.preventDefault();if(monitoring)return;
 const savedJob=sessionStorage.getItem(SEARCH_JOB_KEY);if(savedJob){await monitorSearch(savedJob);return}
 results.style.display='none';statusEl.textContent='Starting search…';setSearching(true);
 try{const payload=Object.fromEntries(new FormData(form));payload.rejected_signatures=rejectedSignatures();const r=await fetch('/api/search',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(payload)});const d=await readJSON(r);if(!r.ok)throw new Error(d.error||'Search failed');await monitorSearch(d.job_id)}
 catch(err){statusEl.textContent='Error: '+err.message}
 finally{if(!monitoring)setSearching(false)}
});
const savedSearch=sessionStorage.getItem(SEARCH_JOB_KEY);if(savedSearch)monitorSearch(savedSearch);
renderPipeline();
</script></body></html>
"""

@app.route("/login", methods=["GET", "POST"])
def login():
    error = None
    if request.method == "POST":
        if not APP_PASSWORD:
            error = "APP_PASSWORD is not configured in Render."
        elif request.form.get("username") == APP_USERNAME and request.form.get("password") == APP_PASSWORD:
            session["logged_in"] = True
            return redirect(request.args.get("next") or url_for("home"))
        else:
            error = "Invalid username or password."
    return render_template_string(LOGIN_TEMPLATE, error=error)


@app.route("/logout")
def logout():
    session.clear()
    return redirect(url_for("login"))


@app.route("/")
@login_required
def home():
    return render_template_string(APP_TEMPLATE, states=sorted(ALLOWED_STATES), categories=BUSINESS_CATEGORIES)


@app.route("/health")
def health():
    return jsonify({"ok": True, "serpapi_configured": bool(SERPAPI_KEY), "db_path": DB_PATH})


def search_result(query, limit, profile, leads, checked=0, skipped_seen=0,
                  skipped_inactive=0, skipped_good=0, skipped_uncertain=0, skipped_chain=0,
                  raw_found=0, prescreened=0, candidate_pool=0, prescreen_rejected=0,
                  provider_errors=0, reject_memory=None):
    tier_rank = {"A": 0, "B": 1, "C": 2}
    leads = sorted(leads, key=lambda x: (tier_rank.get(x.get("tier", "C"), 9), -x["confidence"], -x["improvement_score"], -x["active_score"]))
    qualified_total = len(leads)
    leads = leads[:limit]
    return {
        "query": query,
        "requested_limit": limit,
        "request_profile": profile["label"],
        "map_pages_requested": profile["map_pages"],
        "candidate_cap": profile["candidate_target"],
        "candidate_target": profile["candidate_target"],
        "checked": checked,
        "skipped_seen": skipped_seen,
        "skipped_inactive": skipped_inactive,
        "skipped_good_website": skipped_good,
        "skipped_uncertain": skipped_uncertain,
        "skipped_chain": skipped_chain,
        "raw_found": raw_found,
        "prescreened": prescreened,
        "candidate_pool": candidate_pool,
        "prescreen_rejected": prescreen_rejected,
        "provider_errors": provider_errors,
        "qualified_total": qualified_total,
        "reject_memory": list((reject_memory or {}).values())[-600:],
        "tier_a": sum(1 for x in leads if x.get("tier") == "A"),
        "tier_b": sum(1 for x in leads if x.get("tier") == "B"),
        "tier_c": sum(1 for x in leads if x.get("tier") == "C"),
        "no_website": sum(1 for x in leads if x["classification"] == "NO_WEBSITE"),
        "weak_website": sum(1 for x in leads if x["classification"] == "WEAK_WEBSITE"),
        "leads": leads,
    }


def run_search_job(job_id, category, city, state, limit, client_rejected=None):
    JOB_CONTEXT.job_id = job_id
    profile = SEARCH_PROFILES[limit]
    query = f"{category} in {city}, {state}"
    location = f"{city}, {state}, United States"
    leads = []
    candidates = []
    client_rejected = set(client_rejected or [])
    reject_memory = {}
    counts = dict(checked=0, skipped_seen=0, skipped_inactive=0, skipped_good=0, skipped_uncertain=0, skipped_chain=0,
                  raw_found=0, prescreened=0, candidate_pool=0, prescreen_rejected=0, provider_errors=0)

    def remember_reject(sig, row, classification):
        if classification not in {"REJECT_CHAIN", "REJECT_INACTIVE", "REJECT_GOOD_WEBSITE"}:
            return
        reject_memory[sig] = {
            "signature": sig, "classification": classification,
            "name": normalize_space(row.get("title") or row.get("name") or ""),
            "address": normalize_space(row.get("address") or ""),
            "phone": normalize_space(row.get("phone") or ""),
            "saved_at": now_iso(),
        }
        client_rejected.add(sig)

    def publish(message, status="running", error=None):
        payload = search_result(query, limit, profile, leads, reject_memory=reject_memory, **counts)
        payload["message"] = message
        if error:
            payload["error"] = error
        job_update(job_id, payload, status)

    def prescreen_one(row):
        name = normalize_space(row.get("title") or row.get("name") or "")
        address = normalize_space(row.get("address") or "")
        phone = normalize_space(row.get("phone") or "")
        sig = business_signature(name, address, phone)
        if not name:
            return "skip", "uncertain", sig, ""
        if sig in client_rejected or seen_recently(sig):
            return "skip", "seen", sig, ""
        site = extract_map_website(row)
        if known_chain(name, site):
            return "reject", "chain", sig, "REJECT_CHAIN"
        maximum_active, _ = active_score(row, web_signal=True, social_signal=True, recent_activity=True)
        if maximum_active < 60:
            return "reject", "inactive", sig, "REJECT_INACTIVE"
        if site:
            verdict, _reason = quick_site_prescreen(site)
            if verdict == "chain":
                return "reject", "chain", sig, "REJECT_CHAIN"
            if verdict == "strong":
                return "reject", "good_website", sig, "REJECT_GOOD_WEBSITE"
        return "keep", "", sig, ""

    try:
        target = profile["candidate_target"]
        publish(f"Searching Google Maps and building a {target}-business candidate pool…")
        seen_raw = set()
        max_pages = min(profile["map_pages"], MAX_MAP_PAGES)
        for page in range(max_pages):
            check_job_alive()
            if len(candidates) >= target:
                break
            params = {"engine": "google_maps", "type": "search", "q": query, "location": location, "z": "13", "hl": "en", "start": page * 20}
            try:
                data = serpapi(params)
            except SearchProviderError as exc:
                if page == 0 and not candidates:
                    raise
                counts["provider_errors"] += 1
                publish(f"A Maps page did not respond. Continuing with {len(candidates)}/{target} pre-screened candidates…")
                break
            rows = data.get("local_results") or []
            if not rows:
                break
            fresh_rows = []
            for row in rows:
                raw_key = (normalize_space(row.get("title") or row.get("name") or "").lower(), normalize_space(row.get("address") or "").lower(), digits(row.get("phone") or "")[-10:])
                if raw_key in seen_raw:
                    continue
                seen_raw.add(raw_key)
                fresh_rows.append(row)
            counts["raw_found"] += len(fresh_rows)
            publish(f"Found {counts['raw_found']} Maps listings · pre-screening obvious chains, strong sites, and prior rejects…")

            # Fast zero-credit checks can overlap; results remain in Maps order.
            outcomes = [None] * len(fresh_rows)
            with ThreadPoolExecutor(max_workers=SEARCH_WORKERS) as pool:
                futs = {pool.submit(prescreen_one, row): i for i, row in enumerate(fresh_rows)}
                for fut in as_completed(futs):
                    i = futs[fut]
                    try:
                        outcomes[i] = fut.result()
                    except Exception:
                        outcomes[i] = ("keep", "", business_signature(normalize_space(fresh_rows[i].get("title") or fresh_rows[i].get("name") or ""), normalize_space(fresh_rows[i].get("address") or ""), normalize_space(fresh_rows[i].get("phone") or "")), "")

            for row, outcome in zip(fresh_rows, outcomes):
                if len(candidates) >= target:
                    break
                action, reason, sig, classification = outcome
                counts["prescreened"] += 1
                if action == "keep":
                    # Hard second gate: rejected/seen businesses cannot enter the full scan.
                    if sig in client_rejected or seen_recently(sig):
                        counts["skipped_seen"] += 1
                        counts["prescreen_rejected"] += 1
                        continue
                    candidates.append(row)
                    counts["candidate_pool"] = len(candidates)
                else:
                    counts["prescreen_rejected"] += 1
                    if reason == "seen":
                        counts["skipped_seen"] += 1
                    elif reason == "chain":
                        counts["skipped_chain"] += 1
                    elif reason == "inactive":
                        counts["skipped_inactive"] += 1
                    elif reason == "good_website":
                        counts["skipped_good"] += 1
                    else:
                        counts["skipped_uncertain"] += 1
                    if classification:
                        name = normalize_space(row.get("title") or row.get("name") or "")
                        address = normalize_space(row.get("address") or "")
                        phone = normalize_space(row.get("phone") or "")
                        mark_seen(sig, name, address, phone, classification)
                        remember_reject(sig, row, classification)
                publish(f"Pre-screened {counts['prescreened']} listings · rejected {counts['prescreen_rejected']} · candidate pool {len(candidates)}/{target}.")

            if len(rows) < 20:
                break

        counts["candidate_pool"] = len(candidates)
        publish(f"Candidate pool ready: {len(candidates)}/{target}. Starting full verification…")

        for idx, row in enumerate(candidates, 1):
            check_job_alive()
            name = normalize_space(row.get("title") or row.get("name") or "")
            address = normalize_space(row.get("address") or "")
            phone = normalize_space(row.get("phone") or "")
            sig = business_signature(name, address, phone)
            # Hard third gate before any expensive work.
            if sig in client_rejected or seen_recently(sig):
                counts["skipped_seen"] += 1
                continue
            counts["checked"] += 1
            publish(f"Verifying candidate {idx}/{len(candidates)}: {name} · {len(leads)} qualified so far…")
            try:
                result = evaluate_business(row, city, state)
            except SearchProviderError:
                # A single verification/provider failure never kills the 30-candidate scan.
                counts["provider_errors"] += 1
                counts["skipped_uncertain"] += 1
                publish(f"Candidate {idx}/{len(candidates)} could not be verified. Skipping it and continuing…")
                continue
            except Exception:
                counts["skipped_uncertain"] += 1
                publish(f"Candidate {idx}/{len(candidates)} had a temporary verification problem. Continuing…")
                continue
            if result:
                skip = result.get("skip")
                if skip:
                    field = {"seen":"skipped_seen", "inactive":"skipped_inactive", "good_website":"skipped_good", "chain":"skipped_chain"}.get(skip, "skipped_uncertain")
                    counts[field] += 1
                    classification = {"inactive":"REJECT_INACTIVE", "good_website":"REJECT_GOOD_WEBSITE", "chain":"REJECT_CHAIN"}.get(skip)
                    if classification:
                        remember_reject(sig, row, classification)
                else:
                    leads.append(result)
            publish(f"Verified {counts['checked']}/{len(candidates)} candidates · found {len(leads)}/{limit} qualified leads.")

        publish(f"Search complete · verified all {len(candidates)} candidates · {len(leads)} qualified, showing the best {min(limit, len(leads))}.", "done")
    except SearchProviderError as exc:
        publish("Search stopped before a usable Maps pool could be built. Any verified results are shown below.", "error", str(exc))
    except Exception:
        publish("Search stopped. Any verified results are shown below.", "error", "The search could not finish. Check Render logs and try again later.")
        app.logger.exception("Lead search %s failed", job_id)
    finally:
        JOB_CONTEXT.job_id = None


def expire_stale_jobs(conn):
    rows = conn.execute("SELECT id,payload_json FROM search_jobs WHERE status='running' AND heartbeat<?",
                        (time.time() - JOB_STALE_SECONDS,)).fetchall()
    for row in rows:
        payload = json.loads(row["payload_json"])
        payload.update({"message": "Search interrupted.", "error": "The search stopped responding, possibly after a server restart. Any completed results are retained."})
        conn.execute("UPDATE search_jobs SET status='error',payload_json=? WHERE id=? AND status='running'",
                     (json.dumps(payload), row["id"]))


@app.route("/api/search", methods=["POST"])
@login_required
def api_search():
    args = request.get_json(silent=True) or request.form
    category = normalize_space(args.get("category"))
    city = normalize_space(args.get("city"))
    state = normalize_space(args.get("state"))
    try:
        requested_limit = int(args.get("limit", "10"))
    except (ValueError, TypeError):
        requested_limit = 10
    if requested_limit not in SEARCH_PROFILES:
        requested_limit = 10
    if category not in {v for v, _ in BUSINESS_CATEGORIES} or not city or state not in ALLOWED_STATES:
        return jsonify({"error": "Choose a category, city, state, and a batch size of 5, 10, or 15."}), 400
    if not SERPAPI_KEY:
        return jsonify({"error": "SERPAPI_KEY is missing from Render environment variables."}), 500
    job_id = uuid.uuid4().hex
    profile = SEARCH_PROFILES[requested_limit]
    client_rejected = args.get("rejected_signatures") or []
    if not isinstance(client_rejected, list):
        client_rejected = []
    client_rejected = [str(x) for x in client_rejected[:2500] if isinstance(x, str) and len(x) == 64]
    payload = search_result(f"{category} in {city}, {state}", requested_limit, profile, [])
    payload["message"] = "Starting search…"
    with db_connect() as conn:
        # Serialize admission across HTTP threads/workers so repeated clicks cannot duplicate paid work.
        conn.execute("BEGIN IMMEDIATE")
        expire_stale_jobs(conn)
        active = conn.execute("SELECT id FROM search_jobs WHERE status='running' LIMIT 1").fetchone()
        if active:
            conn.commit()
            return jsonify({"job_id": active["id"], "status": "running", "reused": True}), 202
        conn.execute("DELETE FROM search_jobs WHERE status!='running' AND created_at<?", (time.time() - 86400,))
        conn.execute("INSERT INTO search_jobs VALUES (?,?,?,?,?)",
                     (job_id, "running", json.dumps(payload), time.time(), time.time()))
        conn.commit()
    try:
        threading.Thread(target=run_search_job, args=(job_id, category, city, state, requested_limit, client_rejected), daemon=True).start()
    except Exception:
        payload["error"] = "Could not start the search. Please try again."
        job_update(job_id, payload, "error")
        return jsonify({"error": payload["error"]}), 500
    return jsonify({"job_id": job_id, "status": "running"}), 202


@app.route("/api/search/<job_id>")
@login_required
def search_status(job_id):
    with db_connect() as conn:
        expire_stale_jobs(conn)
        conn.commit()
    payload = get_job(job_id)
    if not payload:
        return jsonify({"error": "This search is no longer available, possibly after a server restart. Start a new search when ready."}), 404
    return jsonify(payload)


@app.route("/api/history")
@login_required
def api_history():
    with db_connect() as conn:
        rows = conn.execute(
            "SELECT * FROM qualified_leads ORDER BY id DESC LIMIT 250"
        ).fetchall()
    return jsonify([dict(r) for r in rows])


@app.route("/api/reset-seen", methods=["POST"])
@login_required
def reset_seen():
    with db_connect() as conn:
        conn.execute("DELETE FROM seen_businesses")
        conn.commit()
    return jsonify({"ok": True, "message": "Seen-business history cleared."})


if __name__ == "__main__":
    port = int(os.getenv("PORT", "5000"))
    app.run(host="0.0.0.0", port=port, debug=False)
