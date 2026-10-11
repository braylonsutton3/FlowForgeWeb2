import os
import re
import sqlite3
import time
import hashlib
from datetime import datetime, timezone, timedelta
from functools import wraps
from html import escape
from urllib.parse import urlparse

import requests
from flask import Flask, jsonify, redirect, render_template_string, request, session, url_for

app = Flask(__name__)
app.secret_key = os.getenv("SECRET_KEY", "change-this-in-render")

SERPAPI_KEY = os.getenv("SERPAPI_KEY", "").strip()
APP_USERNAME = os.getenv("APP_USERNAME", "flowforgeweb")
APP_PASSWORD = os.getenv("APP_PASSWORD", "").strip()
DB_PATH = os.getenv("LEADS_DB_PATH", "/tmp/flowforge_leads.db")
SEEN_TTL_DAYS = int(os.getenv("SEEN_TTL_DAYS", "120"))
SERPAPI_NO_CACHE = os.getenv("SERPAPI_NO_CACHE", "true").lower() in {"1", "true", "yes", "on"}
REQUEST_TIMEOUT = int(os.getenv("REQUEST_TIMEOUT", "12"))
MAX_MAP_PAGES = max(1, min(int(os.getenv("MAX_MAP_PAGES", "3")), 6))

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
    5: {"map_pages": 1, "candidate_cap": 15, "label": "5 businesses · light request use"},
    10: {"map_pages": 2, "candidate_cap": 30, "label": "10 businesses · balanced request use"},
    15: {"map_pages": 3, "candidate_cap": 45, "label": "15 businesses · higher request use"},
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
    conn = sqlite3.connect(DB_PATH)
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
                created_at TEXT NOT NULL
            )
            """
        )
        columns = {row[1] for row in conn.execute("PRAGMA table_info(qualified_leads)").fetchall()}
        if "tier" not in columns:
            conn.execute("ALTER TABLE qualified_leads ADD COLUMN tier TEXT")
        conn.commit()


init_db()


def normalize_space(value):
    return re.sub(r"\s+", " ", (value or "").strip())


def digits(value):
    return re.sub(r"\D", "", value or "")


def business_signature(name, address, phone):
    raw = "|".join([
        re.sub(r"[^a-z0-9]", "", (name or "").lower()),
        re.sub(r"[^a-z0-9]", "", (address or "").lower()),
        digits(phone)[-10:],
    ])
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def seen_recently(signature):
    cutoff = datetime.now(timezone.utc) - timedelta(days=SEEN_TTL_DAYS)
    with db_connect() as conn:
        row = conn.execute(
            "SELECT checked_at FROM seen_businesses WHERE signature = ?", (signature,)
        ).fetchone()
    if not row:
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
                confidence, improvement_score, active_score, reasons, created_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                lead["signature"], lead["name"], lead["address"], lead["phone"], lead.get("website", ""),
                lead["classification"], lead.get("tier", "C"), lead["confidence"], lead.get("improvement_score", 0),
                lead["active_score"], " | ".join(lead.get("reasons", [])), now_iso(),
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


def serpapi(params):
    if not SERPAPI_KEY:
        raise RuntimeError("SERPAPI_KEY is not configured in Render.")
    payload = dict(params)
    payload["api_key"] = SERPAPI_KEY
    payload["output"] = "json"
    if SERPAPI_NO_CACHE:
        payload["no_cache"] = "true"
    resp = requests.get("https://serpapi.com/search", params=payload, timeout=REQUEST_TIMEOUT + 8)
    resp.raise_for_status()
    data = resp.json()
    if data.get("error"):
        raise RuntimeError(data["error"])
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


def active_score(row, web_signal=False, social_signal=False):
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

    return min(score, 100), reasons


def organic_rows(data):
    return data.get("organic_results") or []


def search_business_presence(name, city, state, phone=""):
    location = f"{city}, {state}, United States"
    queries = [
        f'"{name}" "{city}" {state}',
        f'"{name}" "{city}" website',
        f'"{name}" "{city}" Facebook',
        f'"{name}" "{city}" Yelp',
    ]
    if phone:
        queries.append(f'"{phone}" "{name}"')

    searches = []
    for q in queries:
        try:
            searches.append((q, google_search(q, location=location, num=10)))
        except Exception:
            searches.append((q, {}))

    owned_site = ""
    owned_title = ""
    social_found = False
    directory_found = False
    total_organic = 0

    for _, data in searches:
        for item in organic_rows(data):
            total_organic += 1
            link = item.get("link") or ""
            title = item.get("title") or ""
            if is_social(link):
                social_found = True
            elif is_directory_or_social(link):
                directory_found = True
            elif not owned_site and likely_owned_website(link, title, name):
                owned_site = link
                owned_title = title

    return {
        "owned_site": owned_site,
        "owned_title": owned_title,
        "social_found": social_found,
        "directory_found": directory_found,
        "web_signal": total_organic > 0,
        "queries_checked": len(searches),
    }


def website_improvement_score(url):
    """Score how convincingly FlowForge could improve the business website.

    The score intentionally combines technical checks with visual/UX proxies that can
    be inferred from the public HTML/CSS without relying on a browser screenshot.
    """
    reasons = []
    score = 0
    details = {}
    target = url if re.match(r"^https?://", url or "", re.I) else "https://" + (url or "")

    if target.lower().startswith("http://"):
        score += 12
        reasons.append("Website is not using HTTPS")

    try:
        start = time.monotonic()
        resp = requests.get(target, headers=HEADERS, timeout=REQUEST_TIMEOUT, allow_redirects=True)
        elapsed = time.monotonic() - start
        html = resp.text[:1_500_000]
        lower = html.lower()
        details["status_code"] = resp.status_code
        details["load_seconds"] = round(elapsed, 2)
        details["final_url"] = resp.url

        if resp.status_code >= 400:
            score += 35
            reasons.append(f"Website returns HTTP {resp.status_code}")

        if not resp.url.lower().startswith("https://"):
            score += 10
            reasons.append("Final website URL is not HTTPS")

        if "name=\"viewport\"" not in lower and "name='viewport'" not in lower:
            score += 18
            reasons.append("No responsive mobile viewport detected")

        legacy_hits = sum(token in lower for token in ["<font", "<frameset", "<marquee", "<center>"])
        if legacy_hits:
            score += min(18, 8 + legacy_hits * 4)
            reasons.append("Legacy HTML patterns suggest an outdated site")

        if "<table" in lower and not any(x in lower for x in ["display:grid", "display: grid", "display:flex", "display: flex"]):
            score += 7
            reasons.append("Page appears to rely on older table-based layout patterns")

        # --- Visual / UX quality proxies ---
        modern_layout = any(x in lower for x in ["display:grid", "display: grid", "display:flex", "display: flex"])
        media_queries = "@media" in lower
        css_variables = "var(--" in lower or ":root" in lower
        font_service = any(x in lower for x in ["fonts.googleapis.com", "use.typekit.net", "fonts.bunny.net"])
        has_hero = any(x in lower for x in ["hero", "banner", "masthead", "jumbotron"])
        section_count = len(re.findall(r"<section\b", lower))
        image_count = len(re.findall(r"<img\b", lower))
        button_count = len(re.findall(r"<(?:button)\b", lower)) + len(re.findall(r"class=[\"'][^\"']*(?:btn|button|cta)[^\"']*[\"']", lower))
        heading_count = len(re.findall(r"<h[1-3]\b", lower))
        details.update({
            "modern_layout": modern_layout,
            "media_queries": media_queries,
            "section_count": section_count,
            "image_count": image_count,
            "button_count": button_count,
            "heading_count": heading_count,
        })

        visual_deficits = 0
        if not modern_layout:
            visual_deficits += 1
        if not media_queries:
            visual_deficits += 1
        if not css_variables and not font_service:
            visual_deficits += 1
        if not has_hero:
            visual_deficits += 1
        if section_count < 2:
            visual_deficits += 1
        if image_count < 2:
            visual_deficits += 1
        if heading_count < 2:
            visual_deficits += 1

        if visual_deficits >= 6:
            score += 20
            reasons.append("Very weak visual structure compared with a modern local-business site")
        elif visual_deficits >= 4:
            score += 14
            reasons.append("Visual structure appears dated or under-designed")
        elif visual_deficits >= 3:
            score += 8
            reasons.append("Several modern visual-design signals are missing")

        if "<nav" not in lower and "menu" not in lower:
            score += 7
            reasons.append("No clear navigation structure detected")

        cta_terms = [
            "contact us", "get a quote", "request a quote", "free quote", "book now", "schedule",
            "call now", "order now", "get started", "request service", "reserve", "view menu"
        ]
        cta_hits = sum(term in lower for term in cta_terms)
        if not cta_hits and button_count == 0:
            score += 14
            reasons.append("No strong customer call-to-action detected")
        elif cta_hits <= 1 and button_count <= 1:
            score += 7
            reasons.append("Customer conversion path is weak or easy to miss")

        if "<form" not in lower:
            score += 8
            reasons.append("No contact/quote form detected")

        if "tel:" not in lower and "mailto:" not in lower:
            score += 8
            reasons.append("No tap-to-call or email link detected")

        # Useful local-business trust / conversion elements.
        trust_terms = ["testimonial", "review", "licensed", "insured", "years of experience", "our work", "gallery", "portfolio"]
        service_terms = ["services", "menu", "what we do", "our services", "pricing", "service area"]
        if not any(t in lower for t in trust_terms):
            score += 5
            reasons.append("Few visible trust signals, reviews, or proof-of-work elements detected")
        if not any(t in lower for t in service_terms):
            score += 6
            reasons.append("Services/menu information is not clearly surfaced")

        # Weak page hierarchy / readability proxies.
        if "<h1" not in lower:
            score += 5
            reasons.append("No clear primary page heading detected")
        if image_count == 0:
            score += 8
            reasons.append("No meaningful imagery detected on the landing page")

        text = re.sub(r"<script.*?</script>|<style.*?</style>", " ", lower, flags=re.S)
        text = re.sub(r"<[^>]+>", " ", text)
        text = normalize_space(text)
        if len(text) < 700:
            score += 8
            reasons.append("Very little useful business content detected")

        if elapsed > 4.5:
            score += 12
            reasons.append(f"Slow response ({elapsed:.1f}s)")
        elif elapsed > 3.0:
            score += 7
            reasons.append(f"Slower response ({elapsed:.1f}s)")

        current_year = datetime.now().year
        years = [int(y) for y in re.findall(r"(?:19|20)\d{2}", text)]
        if years:
            newest = max(years)
            if newest <= current_year - 4:
                score += 10
                reasons.append(f"Visible content appears stale (newest detected year: {newest})")

        title_match = re.search(r"<title[^>]*>(.*?)</title>", html, re.I | re.S)
        title = normalize_space(re.sub(r"<[^>]+>", "", title_match.group(1))) if title_match else ""
        details["title"] = title
        if not title or len(title) < 5:
            score += 5
            reasons.append("Missing or weak page title")

        # Basic marketing metadata is another useful proxy for site quality.
        if "property=\"og:" not in lower and "property='og:" not in lower:
            score += 3
        if "name=\"description\"" not in lower and "name='description'" not in lower:
            score += 4
            reasons.append("Missing basic search/social marketing metadata")

    except requests.RequestException as exc:
        score = 90
        reasons.append("Website could not be reliably reached")
        details["error"] = str(exc)

    return min(score, 100), reasons, details


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

    map_site = extract_map_website(row)
    presence = search_business_presence(name, city, state, phone)
    site = map_site or presence["owned_site"]

    active, active_reasons = active_score(
        row,
        web_signal=presence["web_signal"],
        social_signal=presence["social_found"],
    )

    if active < 60:
        mark_seen(sig, name, address, phone, "REJECT_INACTIVE")
        return {"skip": "inactive", "signature": sig}

    reasons = list(active_reasons)

    if not site:
        confidence = 80
        confidence += 5  # Maps checked
        confidence += min(10, presence["queries_checked"] * 2)
        if presence["social_found"]:
            confidence += 2
            reasons.append("Social profile found, but no owned website found")
        if presence["directory_found"]:
            confidence += 2
            reasons.append("Directory listings found, but no owned website found")
        confidence = min(confidence, 99)

        if confidence >= 95:
            reasons.insert(0, "No owned website found after Maps + web + social/directory checks")
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
                "maps_rating": row.get("rating"),
                "maps_reviews": row.get("reviews"),
            }
            mark_seen(sig, name, address, phone, "NO_WEBSITE")
            save_lead(lead)
            return lead

        mark_seen(sig, name, address, phone, "REJECT_UNCERTAIN")
        return {"skip": "uncertain", "signature": sig}

    improvement, weak_reasons, site_details = website_improvement_score(site)
    if improvement >= 65:
        confidence = min(99, 70 + round(improvement * 0.25) + (5 if active >= 75 else 0))
        reasons.insert(0, f"Owned website found, but objective weakness score is {improvement}/100")
        reasons.extend(weak_reasons)
        lead = {
            "signature": sig,
            "name": name,
            "address": address,
            "phone": phone,
            "website": site,
            "classification": "WEAK_WEBSITE",
            "tier": lead_tier("WEAK_WEBSITE", confidence, improvement, active),
            "confidence": confidence,
            "improvement_score": improvement,
            "active_score": active,
            "reasons": reasons,
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
:root{--bg:#081018;--panel:#111c27;--border:#26384a;--text:#f6f8fb;--muted:#9fb1c3;--good:#8ef0b2;--warn:#ffd479}
*{box-sizing:border-box}body{font-family:Inter,Arial,sans-serif;background:var(--bg);color:var(--text);margin:0}.wrap{max-width:1180px;margin:0 auto;padding:28px}
.top{display:flex;justify-content:space-between;gap:20px;align-items:center}.panel{background:var(--panel);border:1px solid var(--border);border-radius:18px;padding:20px;margin-top:18px}
.grid{display:grid;grid-template-columns:2fr 1fr 1fr 1fr;gap:10px}input,select,button{padding:12px;border-radius:10px;border:1px solid #35506a;background:#0a141e;color:white;width:100%}button{background:white;color:#0a1118;font-weight:800;cursor:pointer}
small,.muted{color:var(--muted)}.lead{border-top:1px solid var(--border);padding:18px 0}.lead:first-child{border-top:0}.badge{display:inline-block;padding:5px 9px;border-radius:999px;background:#173427;color:var(--good);font-weight:800;font-size:12px}.weak{background:#3a3018;color:var(--warn)}.tier{display:inline-block;padding:5px 9px;border-radius:999px;background:#17243a;color:#b9d7ff;font-weight:900;font-size:12px;margin-right:6px}.tierA{background:#153b26;color:#91f1b7}.tierB{background:#3a3018;color:#ffd479}.tierC{background:#2d293d;color:#cabdff}
a{color:#8dc7ff}.stats{display:flex;gap:12px;flex-wrap:wrap}.stat{background:#0b151f;border:1px solid var(--border);padding:10px 12px;border-radius:12px}.reason{margin:5px 0;color:#d8e0e8}
@media(max-width:800px){.grid{grid-template-columns:1fr}.top{align-items:flex-start;flex-direction:column}}
</style></head><body><div class="wrap">
<div class="top"><div><h1>FlowForge Lead Finder</h1><p class="muted">Active businesses only · new leads first · no-site or confidently weak-site only</p></div><a href="/logout">Log out</a></div>
<div class="panel"><form id="searchForm"><div class="grid">
<select name="category" required><option value="">Business category</option>{% for value,label in categories %}<option value="{{value}}">{{label}}</option>{% endfor %}</select>
<input name="city" placeholder="City" required>
<select name="state" required><option value="">State</option>{% for s in states %}<option>{{s}}</option>{% endfor %}</select>
<select name="limit" required><option value="5">5 businesses · light requests</option><option value="10" selected>10 businesses · balanced</option><option value="15">15 businesses · deeper search</option></select>
</div><p class="muted" style="margin:10px 0 0">Larger batches search more Maps results and verify more candidates, so they use more SerpApi requests. Every returned business still gets the same strict website checks.</p><button style="margin-top:10px">Find new qualified leads</button></form><p id="status" class="muted"></p></div>
<div id="results" class="panel" style="display:none"></div>
</div><script>
const form=document.getElementById('searchForm'), statusEl=document.getElementById('status'), results=document.getElementById('results');
function esc(v){return String(v??'').replace(/[&<>\"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','\"':'&quot;',"'":'&#39;'}[c]));}
form.addEventListener('submit',async(e)=>{e.preventDefault();results.style.display='none';statusEl.textContent='Searching and verifying businesses…';
 const params=new URLSearchParams(new FormData(form));
 try{const r=await fetch('/api/search?'+params.toString()); const d=await r.json(); if(!r.ok) throw new Error(d.error||'Search failed');
 statusEl.textContent=`${d.request_profile} · checked ${d.checked} new businesses · skipped ${d.skipped_seen} already-seen · returned ${d.leads.length}/${d.requested_limit} qualified active leads.`;
 let html=`<div class="stats"><div class="stat"><b>${d.leads.length}</b><br><small>Qualified leads</small></div><div class="stat"><b>${d.tier_a}</b><br><small>Tier A</small></div><div class="stat"><b>${d.tier_b}</b><br><small>Tier B</small></div><div class="stat"><b>${d.tier_c}</b><br><small>Tier C</small></div><div class="stat"><b>${d.no_website}</b><br><small>No website</small></div><div class="stat"><b>${d.weak_website}</b><br><small>Weak website</small></div></div>`;
 if(!d.leads.length) html+=`<p class="muted">No businesses met the strict filters in this batch. Try another nearby city/category or search again later.</p>`;
 for(const x of d.leads){const cls=x.classification==='WEAK_WEBSITE'?'badge weak':'badge'; const tierCls='tier tier'+esc(x.tier||'C'); html+=`<div class="lead"><div><span class="${tierCls}">TIER ${esc(x.tier||'C')}</span><span class="${cls}">${esc(x.classification)}</span> <b>${esc(x.name)}</b></div><p>${esc(x.address)} ${x.phone?'· '+esc(x.phone):''}</p>${x.website?`<p><a target="_blank" rel="noopener" href="${esc(x.website)}">${esc(x.website)}</a></p>`:''}<p><b>Confidence:</b> ${x.confidence}% · <b>Active score:</b> ${x.active_score}/100${x.classification==='WEAK_WEBSITE'?` · <b>Improvement:</b> ${x.improvement_score}/100`:''}</p>${x.reasons.slice(0,7).map(z=>`<div class="reason">• ${esc(z)}</div>`).join('')}</div>`}
 results.innerHTML=html;results.style.display='block';
 }catch(err){statusEl.textContent='Error: '+err.message;}});
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


@app.route("/api/search")
@login_required
def api_search():
    category = normalize_space(request.args.get("category"))
    city = normalize_space(request.args.get("city"))
    state = normalize_space(request.args.get("state"))
    try:
        requested_limit = int(request.args.get("limit", "10"))
    except ValueError:
        requested_limit = 10
    if requested_limit not in SEARCH_PROFILES:
        requested_limit = 10
    limit = requested_limit
    profile = SEARCH_PROFILES[requested_limit]

    allowed_category_values = {value for value, _ in BUSINESS_CATEGORIES}
    if category not in allowed_category_values or not city or state not in ALLOWED_STATES:
        return jsonify({"error": "Choose a category, city, state, and a batch size of 5, 10, or 15."}), 400
    if not SERPAPI_KEY:
        return jsonify({"error": "SERPAPI_KEY is missing from Render environment variables."}), 500

    location = f"{city}, {state}, United States"
    query = f"{category} in {city}, {state}"

    try:
        rows = maps_search(query, location, requested_pages=profile["map_pages"])
    except Exception as exc:
        return jsonify({"error": f"Maps search failed: {exc}"}), 502

    leads = []
    checked = 0
    skipped_seen = 0
    skipped_inactive = 0
    skipped_good = 0
    skipped_uncertain = 0
    candidates_considered = 0

    for row in rows:
        if len(leads) >= limit or candidates_considered >= profile["candidate_cap"]:
            break
        name = normalize_space(row.get("title") or row.get("name") or "")
        sig = business_signature(name, normalize_space(row.get("address") or ""), normalize_space(row.get("phone") or ""))
        if seen_recently(sig):
            skipped_seen += 1
            continue

        candidates_considered += 1
        checked += 1
        try:
            result = evaluate_business(row, city, state)
        except Exception:
            mark_seen(sig, name, normalize_space(row.get("address") or ""), normalize_space(row.get("phone") or ""), "ERROR")
            skipped_uncertain += 1
            continue

        if not result:
            continue
        if result.get("skip"):
            if result["skip"] == "seen": skipped_seen += 1
            elif result["skip"] == "inactive": skipped_inactive += 1
            elif result["skip"] == "good_website": skipped_good += 1
            else: skipped_uncertain += 1
            continue
        leads.append(result)

    tier_rank = {"A": 0, "B": 1, "C": 2}
    leads.sort(key=lambda x: (tier_rank.get(x.get("tier", "C"), 9), -x["confidence"], -x["improvement_score"], -x["active_score"]))

    return jsonify({
        "query": query,
        "requested_limit": limit,
        "request_profile": profile["label"],
        "map_pages_requested": profile["map_pages"],
        "candidate_cap": profile["candidate_cap"],
        "checked": checked,
        "skipped_seen": skipped_seen,
        "skipped_inactive": skipped_inactive,
        "skipped_good_website": skipped_good,
        "skipped_uncertain": skipped_uncertain,
        "tier_a": sum(1 for x in leads if x.get("tier") == "A"),
        "tier_b": sum(1 for x in leads if x.get("tier") == "B"),
        "tier_c": sum(1 for x in leads if x.get("tier") == "C"),
        "no_website": sum(1 for x in leads if x["classification"] == "NO_WEBSITE"),
        "weak_website": sum(1 for x in leads if x["classification"] == "WEAK_WEBSITE"),
        "leads": leads,
    })


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
