"""
Wimbledon debenture ticket tracker: WDH + Dowgate scrapers, SQLite history, CSV export.

Captures every dated listing the sources publish (any year), so you can compare seasons.
Rows reflect listed prices and availability on the scraped pages - not a private ledger of
every completed resale; use official AELTC/Dowgate channels for regulated debenture trades.
Dowgate debenture bullets set includes_next_series_rights when the page text distinguishes
'plus rights for the next series' vs 'no rights for the next series'; WDH day tickets leave it blank.

ENHANCED VERSION (2026-04):
- Listing fingerprinting via listing_hash for tracking same ticket across scrapes
- Price change detection (previous_price_gbp, price_direction)
- Sold inference via disappeared flag when listings vanish
- Hours-since-first-seen for velocity analysis
"""

from __future__ import annotations

import hashlib
import json
import logging
import os
import re
import sqlite3
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import pandas as pd
import requests
from bs4 import BeautifulSoup
from dateutil import parser as date_parser

# --- toggles ---
ENABLE_TELEGRAM = False

# Include all session years the sites list (sanity bounds only; not limited to 2026–2028).
EVENT_YEAR_MIN = 1990
EVENT_YEAR_MAX = 2120

DB_PATH = Path(__file__).resolve().parent / "wimbledon_debentures.db"
CSV_PATH = Path(__file__).resolve().parent / "wimbledon_analysis.csv"
SNAPSHOT_CSV_PATH = Path(__file__).resolve().parent / "wimbledon_daily_snapshots.csv"
LOG_PATH = Path(__file__).resolve().parent / "logs.txt"

WDH_BASE = "https://www.wimbledondebentureholders.com"
WDH_URLS = (
    f"{WDH_BASE}/buy-wimbledon-tickets",
    f"{WDH_BASE}/events",
)
DOWGATE_WIMBLEDON_URL = "https://dowgatecapital.co.uk/services/wimbledon-debentures/"

HTTP_TIMEOUT = 45
USER_AGENT = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
)

SESSION = requests.Session()
SESSION.trust_env = False  # ignore HTTP(S)_PROXY so launchd/cron isn't broken by bad proxy env
SESSION.headers.update({"User-Agent": USER_AGENT})


def _setup_logging() -> None:
    LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s %(message)s",
        handlers=[
            logging.FileHandler(LOG_PATH, encoding="utf-8"),
            logging.StreamHandler(),
        ],
    )


def log_exception(source: str, exc: BaseException) -> None:
    logging.error("[%s] %s: %s", source, type(exc).__name__, exc)


@dataclass
class Listing:
    match_day: int
    court: str
    round_name: str
    gender: str
    price_gbp: int | None
    is_sold: bool
    seat_level: int | None
    orientation: str
    source_url: str
    broker_commission_pct: float | None = None
    estimated_net_yield_gbp: int | None = None
    gangway: int | None = None
    row: str | None = None
    proximity_to_royal_box: bool | None = None
    days_to_match: int | None = None
    draw_announced: bool | None = None
    # Dowgate only: True = includes next-series subscription rights; False = explicitly no; None = unknown / N/A (e.g. WDH).
    includes_next_series_rights: bool | None = None
    # NEW: Listing tracking fields
    listing_hash: str = ""
    previous_price_gbp: int | None = None
    first_price_gbp: int | None = None
    price_direction: str | None = None  # "up", "down", "same", None (new listing)
    hours_since_first_seen: float | None = None


def _compute_listing_hash(L: Listing) -> str:
    """
    Generate a stable hash to identify the same listing across scrapes.
    Uses: match_day, court, round_name, seat details, source.
    Price is NOT included so we can track price changes.
    """
    key_parts = [
        str(L.match_day),
        L.court.lower().strip(),
        L.round_name.lower().strip(),
        str(L.seat_level or ""),
        str(L.gangway or ""),
        (L.row or "").upper(),
        L.orientation.lower().strip(),
        L.source_url,
    ]
    key = "|".join(key_parts)
    return hashlib.sha256(key.encode("utf-8")).hexdigest()[:16]


def _norm_seat_level(val: str | None) -> int | None:
    if not val:
        return None
    m = re.search(r"\b(200|300)\b", val)
    if m:
        return int(m.group(1))
    return None


def _infer_gender(round_name: str) -> str:
    r = round_name.lower()
    if "men" in r and "women" not in r:
        return "Men"
    if "ladies" in r or "women" in r:
        return "Women"
    if "mixed" in r:
        return "Mixed"
    if "doubles" in r:
        return "Doubles"
    return "Various"


def _parse_price_display(text: str) -> int | None:
    m = re.search(r"£\s*([\d,]+)", text.replace("\xa3", "£"))
    if not m:
        return None
    return int(m.group(1).replace(",", ""))


def _date_to_match_day(dt: datetime) -> int:
    """Encode session date as YYYYMMDD for stable Int analytics."""
    return dt.year * 10000 + dt.month * 100 + dt.day


def _match_day_to_date(match_day: int) -> datetime | None:
    if match_day <= 0:
        return None
    s = str(match_day)
    if len(s) != 8:
        return None
    try:
        return datetime.strptime(s, "%Y%m%d")
    except ValueError:
        return None


def _derive_days_to_match(match_day: int, scrape_ts: str) -> int | None:
    md = _match_day_to_date(match_day)
    if not md:
        return None
    try:
        scrape_dt = datetime.strptime(scrape_ts, "%Y-%m-%dT%H:%M:%SZ")
    except ValueError:
        return None
    return (md.date() - scrape_dt.date()).days


def _derive_draw_announced(match_day: int, scrape_ts: str) -> bool | None:
    """
    Optional configuration for demand-regime analysis.
    Set WIMBLEDON_DRAW_ANNOUNCED_DATE (YYYY-MM-DD) to populate this signal.
    """
    md = _match_day_to_date(match_day)
    if not md:
        return None
    draw_date_raw = os.environ.get("WIMBLEDON_DRAW_ANNOUNCED_DATE", "").strip()
    if not draw_date_raw:
        return None
    try:
        draw_date = datetime.strptime(draw_date_raw, "%Y-%m-%d").date()
        scrape_date = datetime.strptime(scrape_ts, "%Y-%m-%dT%H:%M:%SZ").date()
    except ValueError:
        return None
    return scrape_date >= draw_date


def _derive_commission_pct(source_url: str) -> float | None:
    """
    Commission varies by broker and contract terms.
    Keep defaults conservative (unknown -> None) and allow env overrides.
    """
    source = source_url.lower()
    if "greenandpurple.com" in source or "greenandpurple" in source:
        return 0.18  # 15% commission + VAT on commission (effective ~18%).
    if "wimbledondebentureholders.com" in source:
        env_pct = os.environ.get("WDH_COMMISSION_PCT", "").strip()
        try:
            return float(env_pct) if env_pct else None
        except ValueError:
            return None
    if "dowgatecapital.co.uk" in source:
        env_pct = os.environ.get("DOWGATE_COMMISSION_PCT", "").strip()
        try:
            return float(env_pct) if env_pct else None
        except ValueError:
            return None
    return None


def _derive_estimated_net_yield(price_gbp: int | None, commission_pct: float | None) -> int | None:
    if price_gbp is None or commission_pct is None:
        return None
    return int(round(price_gbp * (1.0 - commission_pct)))


def _parse_gangway_and_row(text: str) -> tuple[int | None, str | None]:
    low = text.lower()
    g = re.search(r"\bgangway\s*(\d{2,3})\b", low)
    r = re.search(r"\brow\s*([a-z]{1,2})\b", low)
    gangway = int(g.group(1)) if g else None
    row = r.group(1).upper() if r else None
    return gangway, row


def _derive_proximity_to_royal_box(gangway: int | None) -> bool | None:
    if gangway is None:
        return None
    return gangway in {201, 212}


def _enrich_listing_metrics(L: Listing, scrape_ts: str) -> Listing:
    commission_pct = L.broker_commission_pct
    if commission_pct is None:
        commission_pct = _derive_commission_pct(L.source_url)
    L.broker_commission_pct = commission_pct
    L.estimated_net_yield_gbp = _derive_estimated_net_yield(L.price_gbp, commission_pct)
    L.days_to_match = _derive_days_to_match(L.match_day, scrape_ts)
    L.draw_announced = _derive_draw_announced(L.match_day, scrape_ts)
    if L.proximity_to_royal_box is None:
        L.proximity_to_royal_box = _derive_proximity_to_royal_box(L.gangway)
    return L


def _event_year_in_range(dt: datetime) -> bool:
    return EVENT_YEAR_MIN <= dt.year <= EVENT_YEAR_MAX


def _infer_next_series_rights(text: str) -> bool | None:
    """Parse Dowgate copy: 'no rights for the next series' vs 'plus rights for the next series'."""
    low = text.lower()
    if "no rights" in low and ("next" in low or "series" in low):
        return False
    if "plus rights" in low and "next" in low:
        return True
    if "rights for the next series" in low:
        return True
    return None


def _rights_sql(v: bool | None) -> int | None:
    if v is None:
        return None
    return 1 if v else 0


def _wdh_listing_sold(ev: Any, pair_price: int | None) -> bool:
    """Best-effort: sold / unavailable vs still listed (public page only)."""
    blob = (ev.get_text(" ", strip=True) if ev else "").lower()
    if "sold out" in blob or "sold-out" in blob:
        return True
    if "unavailable" in blob:
        return True
    if ev and ev.select_one('input[type="submit"][value="Buy"]') is None:
        if pair_price is None and "£" not in blob:
            return True
    return False


def scrape_wdh() -> list[Listing]:
    out: list[Listing] = []
    for url in WDH_URLS:
        try:
            r = SESSION.get(url, timeout=HTTP_TIMEOUT)
            r.raise_for_status()
        except Exception as e:
            log_exception(f"WDH fetch {url}", e)
            continue

        try:
            soup = BeautifulSoup(r.text, "lxml")
            for script in soup.find_all("script", type="application/ld+json"):
                raw = script.string or ""
                if not raw.strip():
                    continue
                try:
                    data = json.loads(raw)
                except json.JSONDecodeError:
                    continue
                if data.get("@type") != "SportsEvent":
                    continue
                start = data.get("startDate")
                if not start:
                    continue
                try:
                    dt = date_parser.parse(start)
                except (ValueError, TypeError):
                    continue
                if not _event_year_in_range(dt):
                    continue
                offers = data.get("offers") or {}
                price_raw = offers.get("price")
                price_gbp: int | None
                try:
                    price_gbp = int(float(price_raw)) if price_raw is not None else None
                except (ValueError, TypeError):
                    price_gbp = None
                desc = (data.get("description") or data.get("name") or "").lower()
                court = "Centre Court" if "centre" in desc else (
                    "No. 1 Court" if "no. 1" in desc or "no.1" in desc else "Unknown"
                )
                round_name = data.get("name") or ""
                if " - " in round_name:
                    round_name = round_name.split(" - ", 1)[-1].strip()
                avail = (offers.get("availability") or "").lower()
                is_sold = "soldout" in avail or "outofstock" in avail.replace(" ", "")
                listing = Listing(
                    match_day=_date_to_match_day(dt),
                    court=court,
                    round_name=round_name or "Unknown",
                    gender=_infer_gender(round_name),
                    price_gbp=price_gbp,
                    is_sold=is_sold,
                    seat_level=None,
                    orientation="unspecified",
                    source_url=url,
                    includes_next_series_rights=None,
                )
                out.append(listing)

            for ev in soup.select("div.mod.event"):
                h2 = ev.select_one("h2.bd")
                if not h2:
                    continue
                date_text = h2.get_text(strip=True)
                try:
                    dt = date_parser.parse(date_text, dayfirst=True)
                except (ValueError, TypeError):
                    continue
                if not _event_year_in_range(dt):
                    continue
                court_el = ev.select_one(".event-bd div")
                court = "Unknown"
                round_name = ""
                if court_el:
                    lines = [x.strip() for x in court_el.get_text("\n").split("\n") if x.strip()]
                    if lines:
                        court = lines[0]
                    sd = court_el.select_one(".secondary-detail")
                    if sd:
                        round_name = sd.get_text(strip=True)
                price_el = ev.select_one(".event-price")
                pair_price = _parse_price_display(price_el.get_text()) if price_el else None
                sel = ev.select_one("select.line-item-quantity")
                per_ticket: int | None = None
                if sel and sel.has_attr("data-event_sale_price"):
                    try:
                        per_ticket = int(float(sel["data-event_sale_price"]))
                    except (ValueError, TypeError):
                        per_ticket = None
                price_gbp = per_ticket if per_ticket is not None else (
                    (pair_price // 2) if pair_price is not None else None
                )
                is_sold = _wdh_listing_sold(ev, pair_price)
                ev_blob = ev.get_text(" ", strip=True)
                gangway, row = _parse_gangway_and_row(ev_blob)
                out.append(
                    Listing(
                        match_day=_date_to_match_day(dt),
                        court=court,
                        round_name=round_name or "Unknown",
                        gender=_infer_gender(round_name),
                        price_gbp=price_gbp,
                        is_sold=is_sold,
                        seat_level=_norm_seat_level(ev.get_text(" ", strip=True)),
                        orientation="unspecified",
                        source_url=url,
                        gangway=gangway,
                        row=row,
                        proximity_to_royal_box=_derive_proximity_to_royal_box(gangway),
                        includes_next_series_rights=None,
                    )
                )
        except Exception as e:
            log_exception(f"WDH parse {url}", e)

    # De-dupe identical listings from overlapping URLs
    seen: set[tuple[Any, ...]] = set()
    unique: list[Listing] = []
    for L in out:
        key = (
            L.match_day,
            L.court,
            L.round_name,
            L.price_gbp,
            L.seat_level,
            L.orientation,
            L.source_url,
            L.includes_next_series_rights,
        )
        if key in seen:
            continue
        seen.add(key)
        unique.append(L)
    return unique


def _parse_gbp_near(text: str) -> int | None:
    m = re.search(r"£\s*([\d,]+)", text.replace("\xa3", "£"))
    return int(m.group(1).replace(",", "")) if m else None


def scrape_dowgate() -> list[Listing]:
    out: list[Listing] = []
    try:
        r = SESSION.get(DOWGATE_WIMBLEDON_URL, timeout=HTTP_TIMEOUT)
        r.raise_for_status()
    except Exception as e:
        log_exception("Dowgate fetch", e)
        return out

    try:
        soup = BeautifulSoup(r.text, "lxml")
        text = soup.get_text("\n", strip=True)
        global_gbp = _parse_gbp_near(text)

        def row_for_line(line: str, y0: int, y1: int) -> Listing:
            low = line.lower()
            bits: list[str] = []
            if "centre" in low and "court" in low:
                bits.append("Centre Court")
            if "no.1" in low.replace(" ", "") or "no. 1" in low:
                bits.append("No.1 Court")
            court = ", ".join(bits) if bits else f"Debenture series {y0}-{y1}"
            rights = _infer_next_series_rights(line) if line.strip() else None
            label = f"AELTC debenture {y0}-{y1} (Dowgate weekly auction)"
            line_gbp = _parse_gbp_near(line)
            return Listing(
                match_day=0,
                court=court,
                round_name=label,
                gender="Various",
                price_gbp=line_gbp if line_gbp is not None else global_gbp,
                is_sold=False,
                seat_level=None,
                orientation="institutional",
                source_url=DOWGATE_WIMBLEDON_URL,
                includes_next_series_rights=rights,
            )

        seen_range: set[tuple[int, int]] = set()
        for li in soup.find_all("li"):
            line = li.get_text(" ", strip=True)
            rm = re.search(r"\b(20\d{2})\s*[-–]\s*(20\d{2})\b", line)
            if not rm:
                continue
            y0, y1 = int(rm.group(1)), int(rm.group(2))
            if y1 < y0:
                continue
            if (y0, y1) in seen_range:
                continue
            seen_range.add((y0, y1))
            out.append(row_for_line(line, y0, y1))

        if not out:
            for m in re.finditer(r"\b(20\d{2})\s*[-–]\s*(20\d{2})\b", text):
                y0, y1 = int(m.group(1)), int(m.group(2))
                if y1 < y0 or (y0, y1) in seen_range:
                    continue
                seen_range.add((y0, y1))
                out.append(row_for_line("", y0, y1))

        if not out:
            logging.info("Dowgate: no year-range text found; storing one summary row.")
            out.append(
                Listing(
                    match_day=0,
                    court="Debenture (see source)",
                    round_name="AELTC debenture issue / weekly auction (Dowgate)",
                    gender="Various",
                    price_gbp=global_gbp,
                    is_sold=False,
                    seat_level=None,
                    orientation="institutional",
                    source_url=DOWGATE_WIMBLEDON_URL,
                    includes_next_series_rights=None,
                )
            )
    except Exception as e:
        log_exception("Dowgate parse", e)
    return out


def init_db(conn: sqlite3.Connection) -> None:
    # Master log: one row per unique listing (by listing_hash), tracks lifecycle
    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS wimbledon_master_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            listing_hash TEXT NOT NULL UNIQUE,
            scrape_date TEXT NOT NULL,
            match_day INTEGER NOT NULL,
            court TEXT NOT NULL,
            "round" TEXT NOT NULL,
            gender TEXT NOT NULL,
            price_gbp INTEGER,
            previous_price_gbp INTEGER,
            first_price_gbp INTEGER,
            price_direction TEXT,
            is_sold INTEGER NOT NULL,
            seat_level INTEGER,
            orientation TEXT NOT NULL,
            source_url TEXT NOT NULL,
            includes_next_series_rights INTEGER,
            broker_commission_pct REAL,
            estimated_net_yield_gbp INTEGER,
            gangway INTEGER,
            row TEXT,
            proximity_to_royal_box INTEGER,
            days_to_match INTEGER,
            draw_announced INTEGER,
            hours_since_first_seen REAL,
            first_seen TEXT NOT NULL,
            last_seen TEXT NOT NULL,
            disappeared INTEGER DEFAULT 0
        )
        """
    )
    # Create index on listing_hash for fast lookups
    conn.execute(
        "CREATE INDEX IF NOT EXISTS idx_listing_hash ON wimbledon_master_log (listing_hash)"
    )
    conn.execute(
        "CREATE INDEX IF NOT EXISTS idx_wim_lookup ON wimbledon_master_log "
        "(match_day, court, \"round\", gender, price_gbp, seat_level, orientation, "
        "includes_next_series_rights)"
    )

    # Daily snapshots: every scrape creates new rows for time-series analysis
    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS daily_snapshots (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            snapshot_date TEXT NOT NULL,
            scrape_ts TEXT NOT NULL,
            listing_hash TEXT NOT NULL,
            match_day INTEGER NOT NULL,
            court TEXT NOT NULL,
            "round" TEXT NOT NULL,
            gender TEXT NOT NULL,
            price_gbp INTEGER,
            previous_price_gbp INTEGER,
            first_price_gbp INTEGER,
            price_direction TEXT,
            is_sold INTEGER NOT NULL,
            seat_level INTEGER,
            orientation TEXT NOT NULL,
            source_url TEXT NOT NULL,
            includes_next_series_rights INTEGER,
            broker_commission_pct REAL,
            estimated_net_yield_gbp INTEGER,
            gangway INTEGER,
            row TEXT,
            proximity_to_royal_box INTEGER,
            days_to_match INTEGER,
            draw_announced INTEGER,
            hours_since_first_seen REAL
        )
        """
    )
    conn.execute(
        "CREATE INDEX IF NOT EXISTS idx_snapshot_hash ON daily_snapshots (listing_hash)"
    )
    conn.execute(
        "CREATE INDEX IF NOT EXISTS idx_snapshot_date ON daily_snapshots (snapshot_date)"
    )
    conn.commit()


def upsert_listings(conn: sqlite3.Connection, listings: list[Listing], scrape_ts: str) -> tuple[int, int, int]:
    """
    Upsert listings using listing_hash as the unique key.
    Tracks price changes and calculates hours_since_first_seen.
    Returns (inserted, updated, price_changed) counts.
    """
    inserted = 0
    updated = 0
    price_changed_count = 0
    cur = conn.cursor()

    # Parse scrape timestamp for hours calculation
    try:
        scrape_dt = datetime.strptime(scrape_ts, "%Y-%m-%dT%H:%M:%SZ")
    except ValueError:
        scrape_dt = datetime.now(timezone.utc)

    for L in listings:
        L = _enrich_listing_metrics(L, scrape_ts)
        L.listing_hash = _compute_listing_hash(L)
        rs = _rights_sql(L.includes_next_series_rights)
        is_sold_int = 1 if L.is_sold else 0

        # Look up existing listing by hash
        cur.execute(
            """
            SELECT id, price_gbp, first_price_gbp, first_seen FROM wimbledon_master_log
            WHERE listing_hash = ?
            """,
            (L.listing_hash,),
        )
        row = cur.fetchone()

        if row:
            existing_id, old_price, first_price, first_seen_str = row

            # Calculate price direction
            price_direction = None
            previous_price = old_price
            if old_price is not None and L.price_gbp is not None:
                if L.price_gbp > old_price:
                    price_direction = "up"
                    price_changed_count += 1
                elif L.price_gbp < old_price:
                    price_direction = "down"
                    price_changed_count += 1
                else:
                    price_direction = "same"

            # Calculate hours since first seen
            hours_since_first = None
            if first_seen_str:
                try:
                    first_dt = datetime.strptime(first_seen_str, "%Y-%m-%dT%H:%M:%SZ")
                    hours_since_first = (scrape_dt - first_dt).total_seconds() / 3600
                except ValueError:
                    pass

            cur.execute(
                """
                UPDATE wimbledon_master_log
                SET last_seen = ?, scrape_date = ?, price_gbp = ?, previous_price_gbp = ?,
                    price_direction = ?, is_sold = ?, source_url = ?,
                    includes_next_series_rights = ?, broker_commission_pct = ?,
                    estimated_net_yield_gbp = ?, gangway = ?, "row" = ?,
                    proximity_to_royal_box = ?, days_to_match = ?, draw_announced = ?,
                    hours_since_first_seen = ?, disappeared = 0
                WHERE id = ?
                """,
                (
                    scrape_ts,
                    scrape_ts,
                    L.price_gbp,
                    previous_price,
                    price_direction,
                    is_sold_int,
                    L.source_url,
                    rs,
                    L.broker_commission_pct,
                    L.estimated_net_yield_gbp,
                    L.gangway,
                    L.row,
                    1 if L.proximity_to_royal_box is True else 0 if L.proximity_to_royal_box is False else None,
                    L.days_to_match,
                    1 if L.draw_announced is True else 0 if L.draw_announced is False else None,
                    hours_since_first,
                    existing_id,
                ),
            )
            updated += 1
        else:
            # New listing
            cur.execute(
                """
                INSERT INTO wimbledon_master_log (
                    listing_hash, scrape_date, match_day, court, "round", gender,
                    price_gbp, previous_price_gbp, first_price_gbp, price_direction,
                    is_sold, seat_level, orientation, source_url,
                    includes_next_series_rights, broker_commission_pct,
                    estimated_net_yield_gbp, gangway, "row", proximity_to_royal_box,
                    days_to_match, draw_announced, hours_since_first_seen, first_seen, last_seen
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    L.listing_hash,
                    scrape_ts,
                    L.match_day,
                    L.court,
                    L.round_name,
                    L.gender,
                    L.price_gbp,
                    None,  # previous_price_gbp
                    L.price_gbp,  # first_price_gbp
                    None,  # price_direction (new listing)
                    is_sold_int,
                    L.seat_level,
                    L.orientation,
                    L.source_url,
                    rs,
                    L.broker_commission_pct,
                    L.estimated_net_yield_gbp,
                    L.gangway,
                    L.row,
                    1 if L.proximity_to_royal_box is True else 0 if L.proximity_to_royal_box is False else None,
                    L.days_to_match,
                    1 if L.draw_announced is True else 0 if L.draw_announced is False else None,
                    0.0,  # hours_since_first_seen
                    scrape_ts,
                    scrape_ts,
                ),
            )
            inserted += 1

    conn.commit()
    return inserted, updated, price_changed_count


def mark_disappeared_listings(conn: sqlite3.Connection, current_hashes: set[str], scrape_ts: str) -> int:
    """
    Mark listings as disappeared (likely sold) if they were seen before but not in current scrape.
    Returns count of newly disappeared listings.
    """
    cur = conn.cursor()
    cur.execute(
        """
        SELECT listing_hash FROM wimbledon_master_log
        WHERE disappeared = 0 AND listing_hash NOT IN ({})
        """.format(
            ",".join("?" * len(current_hashes)) if current_hashes else "SELECT NULL WHERE 1=0"
        ),
        tuple(current_hashes) if current_hashes else (),
    )
    disappeared_hashes = [row[0] for row in cur.fetchall()]

    if disappeared_hashes:
        cur.executemany(
            """
            UPDATE wimbledon_master_log
            SET disappeared = 1, last_seen = ?
            WHERE listing_hash = ? AND disappeared = 0
            """,
            [(scrape_ts, h) for h in disappeared_hashes],
        )
        conn.commit()

    return len(disappeared_hashes)


def record_daily_snapshots(conn: sqlite3.Connection, listings: list[Listing], scrape_ts: str) -> None:
    """Append one row per listing for this scrape_ts into daily_snapshots."""
    snapshot_date = scrape_ts.split("T", 1)[0]
    cur = conn.cursor()
    rows = []

    try:
        scrape_dt = datetime.strptime(scrape_ts, "%Y-%m-%dT%H:%M:%SZ")
    except ValueError:
        scrape_dt = datetime.now(timezone.utc)

    for L in listings:
        L = _enrich_listing_metrics(L, scrape_ts)
        L.listing_hash = _compute_listing_hash(L)
        rs = _rights_sql(L.includes_next_series_rights)

        # Look up first_seen for hours calculation
        hours_since_first = L.hours_since_first_seen
        if hours_since_first is None:
            cur.execute(
                "SELECT first_seen FROM wimbledon_master_log WHERE listing_hash = ?",
                (L.listing_hash,),
            )
            row = cur.fetchone()
            if row and row[0]:
                try:
                    first_dt = datetime.strptime(row[0], "%Y-%m-%dT%H:%M:%SZ")
                    hours_since_first = (scrape_dt - first_dt).total_seconds() / 3600
                except ValueError:
                    hours_since_first = 0.0

        rows.append(
            (
                snapshot_date,
                scrape_ts,
                L.listing_hash,
                L.match_day,
                L.court,
                L.round_name,
                L.gender,
                L.price_gbp,
                L.previous_price_gbp,
                L.first_price_gbp,
                L.price_direction,
                1 if L.is_sold else 0,
                L.seat_level,
                L.orientation,
                L.source_url,
                rs,
                L.broker_commission_pct,
                L.estimated_net_yield_gbp,
                L.gangway,
                L.row,
                1 if L.proximity_to_royal_box is True else 0 if L.proximity_to_royal_box is False else None,
                L.days_to_match,
                1 if L.draw_announced is True else 0 if L.draw_announced is False else None,
                hours_since_first,
            )
        )
    cur.executemany(
        """
        INSERT INTO daily_snapshots (
            snapshot_date, scrape_ts, listing_hash, match_day, court, "round", gender,
            price_gbp, previous_price_gbp, first_price_gbp, price_direction,
            is_sold, seat_level, orientation, source_url,
            includes_next_series_rights, broker_commission_pct,
            estimated_net_yield_gbp, gangway, "row", proximity_to_royal_box,
            days_to_match, draw_announced, hours_since_first_seen
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        rows,
    )
    conn.commit()


def export_to_excel(
    db_path: Path = DB_PATH,
    out_path: Path = CSV_PATH,
    snapshot_out_path: Path = SNAPSHOT_CSV_PATH,
) -> None:
    """Export master_log and daily_snapshots to CSV for analysis workflow."""
    conn = sqlite3.connect(db_path)
    try:
        df = pd.read_sql_query(
            "SELECT * FROM wimbledon_master_log ORDER BY last_seen DESC, id DESC",
            conn,
        )
        df_snap = pd.read_sql_query(
            "SELECT * FROM daily_snapshots ORDER BY scrape_ts DESC, id DESC",
            conn,
        )
    finally:
        conn.close()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    df.to_csv(out_path, index=False)
    df_snap.to_csv(snapshot_out_path, index=False)


def notify_telegram(message: str) -> None:
    if not ENABLE_TELEGRAM:
        return
    token = os.environ.get("TELEGRAM_BOT_TOKEN", "")
    chat_id = os.environ.get("TELEGRAM_CHAT_ID", "")
    if not token or not chat_id:
        logging.warning("Telegram enabled but TELEGRAM_BOT_TOKEN or TELEGRAM_CHAT_ID missing.")
        return
    try:
        url = f"https://api.telegram.org/bot{token}/sendMessage"
        SESSION.post(
            url,
            json={"chat_id": chat_id, "text": message[:4000]},
            timeout=30,
        )
    except Exception as e:
        log_exception("Telegram", e)


def main() -> None:
    _setup_logging()
    scrape_ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    conn = sqlite3.connect(DB_PATH)
    try:
        init_db(conn)
        all_rows: list[Listing] = []
        for fn in (scrape_wdh, scrape_dowgate):
            try:
                all_rows.extend(fn())
            except Exception as e:
                log_exception(fn.__name__, e)

        # Compute hashes for all current listings
        current_hashes: set[str] = set()
        for L in all_rows:
            L.listing_hash = _compute_listing_hash(L)
            current_hashes.add(L.listing_hash)

        # Record snapshots first (before upsert so we can look up first_seen)
        record_daily_snapshots(conn, all_rows, scrape_ts)

        # Upsert listings with price tracking
        ins, upd, price_changes = upsert_listings(conn, all_rows, scrape_ts)
        logging.info("Upsert complete: inserted=%s updated=%s price_changes=%s", ins, upd, price_changes)

        # Mark disappeared listings (likely sold)
        disappeared = mark_disappeared_listings(conn, current_hashes, scrape_ts)
        if disappeared > 0:
            logging.info("Marked %s listings as disappeared (likely sold)", disappeared)

        export_to_excel()
        logging.info("Wrote %s", CSV_PATH)

        if ENABLE_TELEGRAM:
            notify_telegram(
                f"Wimbledon scrape {scrape_ts}: {len(all_rows)} listings parsed, "
                f"{ins} new, {upd} updated, {price_changes} price changes, {disappeared} disappeared."
            )
    finally:
        conn.close()


if __name__ == "__main__":
    main()
