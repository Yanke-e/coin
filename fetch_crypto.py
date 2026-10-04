#!/usr/bin/env python3
"""
fetch_crypto.py - Crypto Intelligence Terminal engine (v2).

Modes (python fetch_crypto.py --mode <mode>):
  full        Market data + use-case ranking + news intersection + coin profiles
              (backing / liquidity / developer data) + setup scoring. Writes
              crypto_data.json, then evaluates and emails alerts.
  alerts      Lightweight hourly pass: market data + news + scoring, emails alerts.
              Does not rewrite crypto_data.json (keeps git history small).
  spikelab    Studies past spikes (Quant, Shiba, XPIN, Avalanche) and measures
              what the market looked like BEFORE each one. Writes spike_lab.json.
  test-email  Sends a sample alert so you can confirm SMTP works.

Environment (set as GitHub Actions secrets):
  SMTP_USER           Gmail address that sends the alerts
  SMTP_APP_PASSWORD   Gmail app password (16 chars, needs 2-Step Verification)
  ALERT_EMAIL_TO      where alerts go (falls back to SMTP_USER)
  COINGECKO_API_KEY   optional CoinGecko demo key (fewer rate-limit errors)
  DASHBOARD_URL       optional dashboard URL used in emails
  BAN_TOP10           set to 0 to include BTC/ETH/SOL/... (default: banned)
"""

import argparse
import hashlib
import html
import json
import math
import os
import re
import smtplib
import ssl
import statistics
import sys
import time
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage
from email.utils import parsedate_to_datetime
from urllib.parse import quote_plus

import requests

# --------------------------------------------------------------------------- #
# Configuration
# --------------------------------------------------------------------------- #

DATA_FILE = os.environ.get("CRYPTO_OUTPUT", "crypto_data.json")
STATE_FILE = os.environ.get("CRYPTO_STATE", "alerts_state.json")
SPIKE_FILE = os.environ.get("CRYPTO_SPIKE_OUTPUT", "spike_lab.json")

CG_BASE = "https://api.coingecko.com/api/v3"
CG_MARKETS_URL = CG_BASE + "/coins/markets"
CG_PAGES = int(os.environ.get("CG_PAGES", "8"))   # 8 x 250 = top 2000 by market cap in full mode
CG_VOLUME_PAGES = 3               # plus the 750 highest-volume coins (catches small caps)
CG_PER_PAGE = 250
CG_DELAY = 3.0                    # polite pause between CoinGecko calls

# Noise floors only (there is NO upper market-cap limit).
MIN_MARKET_CAP = 2_000_000
MIN_VOLUME_24H = 50_000
MAX_PRICE_USD = float(os.environ.get("MAX_PRICE_USD", "15"))   # coins already above this are skipped

# Zero-cancel hunt: coins whose price has many leading zeros (0.0000123 has 4)
HUNT_MIN_ZEROS = 2
HUNT_MIN_KEEP = 35          # minimum hunt score to appear in the hunt view
HUNT_ALERT_SCORE = 75
MAX_HUNT = 500              # cap on hunt candidates stored in crypto_data.json
MAX_NON_HUNT = 400          # cap on ordinary assets stored

# DEX discovery (GeckoTerminal for discovery, DexScreener for pair data)
GT_BASE = "https://api.geckoterminal.com/api/v2"
GT_NETWORKS = [("eth", "ethereum"), ("bsc", "bsc"), ("solana", "solana"),
               ("base", "base"), ("arbitrum", "arbitrum"), ("polygon_pos", "polygon")]
DEX_MIN_LIQUIDITY = 25_000
DEX_MIN_MCAP = 100_000
DEX_MAX_MCAP = 3_000_000_000
DEX_BATCH = 30
DEX_BUDGET_S = 9 * 60
DEX_MAJOR_SYMBOLS = {"WETH", "ETH", "WBNB", "BNB", "USDC", "USDT", "DAI", "SOL", "WSOL", "WBTC",
                     "CBBTC", "BTC", "USDE", "FDUSD", "WMATIC", "POL", "USDS", "PYUSD"}
SECURITY_MAX_PER_RUN = 150          # EVM tokens are scanned in batches, so this is cheap
SOLANA_SCAN_MAX = 40
BLOCK_SELL_TAX = 20.0               # hide tokens whose sell tax is at least this (percent)
BLOCK_BUY_TAX = 25.0
SITE_SUMMARY_MAX = 25
CG_PLATFORM_TO_CHAIN = {"ethereum": "ethereum", "binance-smart-chain": "bsc", "base": "base",
                        "arbitrum-one": "arbitrum", "polygon-pos": "polygon", "solana": "solana"}
SECURITY_REFRESH_DAYS = 3
CG_PLATFORMS = {"ethereum": "ethereum", "bsc": "binance-smart-chain", "solana": "solana",
                "base": "base", "arbitrum": "arbitrum-one", "polygon": "polygon-pos"}
GOPLUS_CHAIN_IDS = {"ethereum": "1", "bsc": "56", "base": "8453", "arbitrum": "42161", "polygon": "137"}

BAN_TOP10 = os.environ.get("BAN_TOP10", "1") != "0"
BANNED_IDS = {"bitcoin", "ethereum", "solana", "binancecoin", "ripple",
              "cardano", "dogecoin", "tron", "tether", "usd-coin"}
BANNED_SYMBOLS = {"BTC", "ETH", "SOL", "BNB", "XRP", "ADA", "DOGE", "TRX", "USDT", "USDC"}

# Always tracked (bypass floors/filters) and always get a dedicated news query.
WATCHLIST = ["quant-network", "avalanche-2", "shiba-inu"]

DERIVATIVE_NAME_RE = re.compile(r"wrapped|staked|bridged|restaked|stablecoin|\busd|usd\b", re.I)

SCARCE_MAX = 800_000_000          # <= 800M circulating = Scarce tier, above = Ecosystem tier
ECOSYSTEM_MIN_TURNOVER = 0.10
ECOSYSTEM_MIN_ADOPTION_HITS = 2
ECOSYSTEM_COMBO_TURNOVER = 0.05
ECOSYSTEM_MIN_MCAP = 50_000_000

MOMENTUM_HIGH = 0.15
MOMENTUM_ELEVATED = 0.08
FDV_WARN_RATIO = 2.0
FDV_CRITICAL_RATIO = 5.0

# Use-case ranking: first = highest priority. Re-order this list to change the ranking.
USE_CASES = [
    ("institutional", "Institutional & RWA"),
    ("payments", "Payments & settlement"),
    ("interop", "Interoperability & oracles"),
    ("l1", "Layer-1 & scaling"),
    ("defi", "DeFi"),
    ("ai_depin", "AI & DePIN"),
    ("gaming", "Gaming & metaverse"),
    ("privacy", "Privacy"),
    ("meme", "Meme & community"),
    ("other", "Other"),
]
UC_RANK = {k: i for i, (k, _) in enumerate(USE_CASES)}
UC_LABEL = dict(USE_CASES)

# CoinGecko category id -> use case (best effort; unknown ids are skipped harmlessly).
CATEGORY_USE_CASES = {
    "real-world-assets-rwa": "institutional",
    "payment-solutions": "payments",
    "interoperability": "interop",
    "oracle": "interop",
    "layer-1": "l1",
    "decentralized-finance-defi": "defi",
    "artificial-intelligence": "ai_depin",
    "depin": "ai_depin",
    "gaming": "gaming",
    "privacy-coins": "privacy",
    "meme-token": "meme",
}
UC_OVERRIDES = {
    "quant-network": "institutional", "stellar": "institutional",
    "hedera-hashgraph": "institutional", "xdc-network": "institutional",
    "xdce-crowd-sale": "institutional", "algorand": "institutional",
    "flare-networks": "institutional", "casper-network": "institutional",
    "ondo-finance": "institutional", "canton-network": "institutional",
    "centrifuge": "institutional", "plume": "institutional",
    "chainlink": "interop", "wormhole": "interop",
    "avalanche-2": "l1", "shiba-inu": "meme",
}
UC_KEYWORDS = {
    "institutional": re.compile(r"real.?world|\brwa\b|tokeni[sz]|treasur|institution|cbdc|enterprise", re.I),
    "payments": re.compile(r"payment|remittance|settlement", re.I),
    "interop": re.compile(r"interoperab|cross.?chain|bridge|oracle|messaging", re.I),
    "l1": re.compile(r"layer.?1|\bl1\b|layer.?2|\bl2\b|smart contract platform|rollup", re.I),
    "defi": re.compile(r"defi|decentrali[sz]ed finance|\bdex\b|lending|yield|liquid staking|derivatives", re.I),
    "ai_depin": re.compile(r"\bai\b|artificial|depin|compute|physical infrastructure", re.I),
    "gaming": re.compile(r"gaming|metaverse|\bnft|play.to.earn", re.I),
    "privacy": re.compile(r"privacy", re.I),
    "meme": re.compile(r"meme|\bdog|\binu\b|pepe|\bcat\b", re.I),
}

# Profile enrichment (backing / liquidity / developer data) budget per full run.
ENRICH_MAX_PER_RUN = 45
ENRICH_REFRESH_DAYS = 14
ENRICH_DELAY = 4.0
TIER1_EXCHANGES = ["binance", "coinbase", "kraken", "okx", "bybit", "bitget",
                   "kucoin", "upbit", "gate", "bitstamp", "gemini", "htx"]

# News
NEWS_MAX_AGE_DAYS = 30
NEWS_PER_ASSET = 8
WIRE_MAX_ITEMS = 40
SUMMARY_MAX_CHARS = 280

# Alerts
ALERT_NEWS_MIN_STRENGTH = 5.0
ALERT_NEWS_MAJOR_STRENGTH = 6.0
ALERT_NEWS_MAX_AGE_H = 72
ALERT_MAX_PER_EMAIL = 20
ALERT_MARKET_MIN_MCAP = 10_000_000
ALERT_MARKET_MIN_VOLUME = 300_000
SETUP_ALERT_SCORE = 70

HTTP_TIMEOUT = 30
T0 = time.time()
CATEGORY_BUDGET_S = 5 * 60     # stop category pulls after 5 minutes of run time
ENRICH_BUDGET_S = 12 * 60      # stop profile enrichment after 12 minutes of run time
USER_AGENT = "Mozilla/5.0 (compatible; CryptoIntelTerminal/2.0) Python-requests"

AMBIGUOUS_SYMBOLS = {
    "THE", "FOR", "ALL", "NOT", "ONE", "CAT", "NEW", "BIG", "WAR", "FUN", "AND",
    "ARE", "ACT", "OPEN", "LIVE", "TOKEN", "COIN", "BANK", "SEC", "ETF", "CEO",
    "NFT", "DAO", "API", "DEX", "CEX", "TVL", "IPO", "USD", "EUR", "GBP", "AI",
}
ALIASES = {
    "quant-network": ["Quant", "Overledger", "QNT"],
    "chainlink": ["Chainlink", "CCIP", "LINK"],
    "stellar": ["Stellar", "XLM"],
    "hedera-hashgraph": ["Hedera", "HBAR"],
    "algorand": ["Algorand", "ALGO"],
    "avalanche-2": ["Avalanche", "AVAX"],
    "ondo-finance": ["Ondo", "Ondo Finance", "OUSG"],
    "polygon-ecosystem-token": ["Polygon", "POL"],
    "wormhole": ["Wormhole"],
    "xdc-network": ["XDC Network", "XDC"],
    "flare-networks": ["Flare Network", "Flare Networks", "FLR"],
    "casper-network": ["Casper Network", "CSPR"],
    "mantra": ["MANTRA", "OM"],
    "injective-protocol": ["Injective", "INJ"],
    "centrifuge": ["Centrifuge", "CFG"],
    "plume": ["Plume Network", "Plume"],
    "canton-network": ["Canton Network", "Canton"],
    "shiba-inu": ["Shiba Inu", "SHIB"],
    "the-open-network": ["Toncoin", "TON"],
    "near": ["NEAR Protocol", "NEAR"],
    "aptos": ["Aptos", "APT"],
    "polkadot": ["Polkadot", "DOT"],
    "cosmos": ["Cosmos Hub", "ATOM"],
    "vechain": ["VeChain", "VET"],
    "ethena": ["Ethena", "ENA"],
    "arbitrum": ["Arbitrum", "ARB"],
}

RSS_FEEDS = [
    ("Ledger Insights", "https://www.ledgerinsights.com/feed/"),
    ("CryptoSlate", "https://cryptoslate.com/feed/"),
    ("CoinDesk", "https://www.coindesk.com/arc/outboundfeeds/rss/"),
    ("The Block", "https://www.theblock.co/rss.xml"),
    ("Cointelegraph", "https://cointelegraph.com/rss"),
    ("Decrypt", "https://decrypt.co/feed"),
]
GOOGLE_NEWS_QUERIES = [
    "tokenized deposits bank pilot",
    "bank consortium blockchain pilot",
    "The Clearing House tokenized deposit",
    "UK Finance tokenised sterling deposit",
    "real world assets tokenization bank",
    "institutional blockchain adoption bank stablecoin settlement",
    "central bank blockchain interoperability pilot",
    "Binance will list new token",
    "Coinbase adds to roadmap listing",
    "Upbit Bithumb new KRW listing crypto",
    "Robinhood lists new crypto",
]

# Spike Lab cases. Dates bound the window searched for the biggest run.
SPIKE_CASES = [
    {"label": "Quant (QNT), 2026 institutional breakout", "kind": "utility", "cg": "quant-network",
     "binance": "QNTUSDT", "from": "2026-05-01", "to": None},
    {"label": "Shiba Inu (SHIB), 2021 mania", "kind": "meme", "cg": "shiba-inu",
     "binance": "SHIBUSDT", "from": "2021-05-10", "to": "2021-12-31"},
    {"label": "Shiba Inu (SHIB), 2023-24 revival (Shibarium era)", "kind": "meme_utility", "cg": "shiba-inu",
     "binance": "SHIBUSDT", "from": "2023-10-01", "to": "2024-04-30"},
    {"label": "Dogecoin (DOGE), 2020-21 run", "kind": "meme", "cg": "dogecoin",
     "binance": "DOGEUSDT", "from": "2020-11-01", "to": "2021-05-31"},
    {"label": "PEPE, late-2023 to 2024 run", "kind": "meme", "cg": "pepe",
     "binance": "PEPEUSDT", "from": "2023-10-01", "to": "2024-04-30"},
    {"label": "Bonk (BONK), late-2023 run (Solana ecosystem)", "kind": "meme_utility", "cg": "bonk",
     "binance": "BONKUSDT", "from": "2023-10-01", "to": "2024-04-30"},
    {"label": "Floki (FLOKI), 2023-24 run", "kind": "meme_utility", "cg": "floki",
     "binance": "FLOKIUSDT", "from": "2023-09-01", "to": "2024-04-30"},
    {"label": "JasmyCoin (JASMY), 2023-24 run (IoT data)", "kind": "utility", "cg": "jasmycoin",
     "binance": "JASMYUSDT", "from": "2023-09-01", "to": "2024-04-30"},
    {"label": "eCash (XEC), late-2021 run", "kind": "utility", "cg": "ecash",
     "binance": "XECUSDT", "from": "2021-09-01", "to": "2022-01-31"},
    {"label": "XPIN Network (XPIN), late 2025 (DePIN)", "kind": "utility", "cg_search": "XPIN Network",
     "binance": None, "from": "2025-09-01", "to": "2025-12-31"},
    {"label": "Avalanche (AVAX), 2026 tokenization move", "kind": "utility", "cg": "avalanche-2",
     "binance": "AVAXUSDT", "from": "2026-01-01", "to": None},
]
BINANCE_KLINES = "https://data-api.binance.vision/api/v3/klines"

# --------------------------------------------------------------------------- #
# Generic helpers
# --------------------------------------------------------------------------- #

def log(msg):
    print(msg, flush=True)


def to_float(value, default=None):
    try:
        if value is None:
            return default
        f = float(value)
        if math.isnan(f) or math.isinf(f):
            return default
        return f
    except (TypeError, ValueError):
        return default


def clamp(x, lo, hi):
    return max(lo, min(hi, x))


def clean_text(raw):
    if not raw:
        return ""
    text = html.unescape(re.sub(r"<[^>]+>", " ", raw))
    return re.sub(r"\s+", " ", text).strip()


def load_json(path, default):
    try:
        with open(path, "r", encoding="utf-8") as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return default


def save_json(path, obj, indent=None):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        if indent:
            json.dump(obj, fh, ensure_ascii=False, indent=indent)
        else:
            json.dump(obj, fh, ensure_ascii=False, separators=(",", ":"))
    os.replace(tmp, path)


def http_get(url, params=None, headers=None, retries=4):
    hdrs = {"User-Agent": USER_AGENT, "Accept": "*/*"}
    if headers:
        hdrs.update(headers)
    delay = 6
    last_err = None
    for attempt in range(1, retries + 1):
        try:
            resp = requests.get(url, params=params, headers=hdrs, timeout=HTTP_TIMEOUT)
            if resp.status_code == 404:
                raise RuntimeError(f"404 not found: {url}")
            if resp.status_code == 429:
                try:
                    wait = int(resp.headers.get("Retry-After", delay))
                except ValueError:
                    wait = delay
                wait = max(wait, delay)
                log(f"  rate limited, sleeping {wait}s (attempt {attempt}/{retries})")
                time.sleep(wait)
                delay *= 2
                last_err = "429 rate limited"
                continue
            resp.raise_for_status()
            return resp
        except requests.RequestException as exc:
            last_err = exc
            if attempt < retries:
                time.sleep(delay)
                delay *= 2
    raise RuntimeError(f"GET {url} failed: {last_err}")


def parse_date(raw):
    if not raw:
        return None
    if isinstance(raw, datetime):
        return raw if raw.tzinfo else raw.replace(tzinfo=timezone.utc)
    raw = str(raw).strip()
    try:
        dt = parsedate_to_datetime(raw)
        return (dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)).astimezone(timezone.utc)
    except (TypeError, ValueError, IndexError):
        pass
    try:
        dt = datetime.fromisoformat(raw.replace("Z", "+00:00"))
        return (dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)).astimezone(timezone.utc)
    except ValueError:
        return None


def cg_headers():
    key = os.environ.get("COINGECKO_API_KEY", "").strip()
    return {"x-cg-demo-api-key": key} if key else {}


def fmt_usd(n):
    if n is None:
        return "n/a"
    a = abs(n)
    if a >= 1e12:
        return f"${n / 1e12:.2f}T"
    if a >= 1e9:
        return f"${n / 1e9:.2f}B"
    if a >= 1e6:
        return f"${n / 1e6:.2f}M"
    if a >= 1e3:
        return f"${n / 1e3:.1f}K"
    return f"${n:.2f}"


def fmt_price(n):
    if n is None:
        return "n/a"
    if n >= 1000:
        return f"${n:,.2f}"
    if n >= 1:
        return f"${n:.2f}"
    if n >= 0.01:
        return f"${n:.4f}"
    return f"${n:.6f}"


def fmt_pct(n):
    return "n/a" if n is None else f"{n:+.1f}%"


# --------------------------------------------------------------------------- #
# Market data
# --------------------------------------------------------------------------- #

MARKET_PARAMS = {
    "vs_currency": "usd", "order": "market_cap_desc", "per_page": CG_PER_PAGE,
    "sparkline": "true", "price_change_percentage": "1h,24h,7d",
}


def fetch_markets(headers, pages=None, order="market_cap_desc"):
    rows = {}
    pages = pages or CG_PAGES
    for page in range(1, pages + 1):
        log(f"[markets] {order} page {page}/{pages}")
        try:
            data = http_get(CG_MARKETS_URL, params={**MARKET_PARAMS, "order": order, "page": page},
                            headers=headers).json()
        except Exception as exc:
            log(f"  ! page {page} failed: {exc}")
            break
        if not isinstance(data, list) or not data:
            break
        for c in data:
            if c.get("id"):
                rows[c["id"]] = c
        if page < pages:
            time.sleep(CG_DELAY)
    return rows


def fetch_by_ids(ids, headers):
    out = {}
    ids = [i for i in ids if not str(i).startswith("dex-")]
    for i in range(0, len(ids), 200):
        chunk = ids[i:i + 200]
        try:
            params = {k: v for k, v in MARKET_PARAMS.items() if k != "order"}
            params.update({"ids": ",".join(chunk), "page": 1})
            data = http_get(CG_MARKETS_URL, params=params, headers=headers, retries=2).json()
            for c in data if isinstance(data, list) else []:
                if c.get("id"):
                    out[c["id"]] = c
        except Exception as exc:
            log(f"  ! id lookup failed: {exc}")
        time.sleep(CG_DELAY)
    return out


def fetch_trending_ids(headers):
    try:
        d = http_get(f"{CG_BASE}/search/trending", headers=headers, retries=2).json()
        ids = [((c or {}).get("item") or {}).get("id") for c in (d.get("coins") or [])]
        ids = [i for i in ids if i]
        log(f"[trending] {len(ids)} trending coins")
        return ids
    except Exception as exc:
        log(f"[trending] skipped ({exc})")
        return []


# --------------------------------------------------------------------------- #
# DEX discovery: tokens that never reach CoinGecko's top lists
# --------------------------------------------------------------------------- #

def gt_discover():
    """GeckoTerminal trending + highest-volume pools per chain -> {chain: [token addresses]}."""
    found = {}
    for net, chain in GT_NETWORKS:
        for path in ("trending_pools", "pools"):
            if time.time() - T0 > DEX_BUDGET_S:
                return found
            params = {"page": 1}
            if path == "pools":
                params["sort"] = "h24_volume_usd_desc"
            try:
                d = http_get(f"{GT_BASE}/networks/{net}/{path}", params=params,
                             headers={"Accept": "application/json;version=20230302"}, retries=2).json()
            except Exception as exc:
                log(f"[dex] {net}/{path}: skipped ({exc})")
                time.sleep(2.5)
                continue
            lst = found.setdefault(chain, [])
            for pool in d.get("data") or []:
                tok = (((pool.get("relationships") or {}).get("base_token") or {}).get("data") or {})
                tid = tok.get("id") or ""
                if "_" in tid:
                    addr = tid.split("_", 1)[1]
                    if addr and addr not in lst:
                        lst.append(addr)
            time.sleep(2.5)
    return found


def ds_fetch(chain, addrs):
    out = []
    for i in range(0, len(addrs), DEX_BATCH):
        chunk = addrs[i:i + DEX_BATCH]
        try:
            data = http_get(f"https://api.dexscreener.com/tokens/v1/{chain}/{','.join(chunk)}", retries=2).json()
            if isinstance(data, list):
                out.extend(data)
        except Exception as exc:
            log(f"[dex] dexscreener {chain} batch failed ({exc})")
        time.sleep(0.4)
    return out


def pairs_to_rows(pairs, wanted):
    """Turn DexScreener pairs into CoinGecko-shaped rows (only pairs where our token is the BASE)."""
    groups = {}
    for p in pairs:
        chain = p.get("chainId")
        base = p.get("baseToken") or {}
        addr = base.get("address")
        if not chain or not addr or addr.lower() not in wanted.get(chain, set()):
            continue
        groups.setdefault((chain, addr), []).append(p)
    rows = {}
    for (chain, addr), ps in groups.items():
        def liq_of(x):
            return to_float((x.get("liquidity") or {}).get("usd"), 0.0)
        best = max(ps, key=liq_of)
        price = to_float(best.get("priceUsd"))
        if not price or price <= 0:
            continue
        liq = sum(liq_of(x) for x in ps)
        vol = sum(to_float((x.get("volume") or {}).get("h24"), 0.0) for x in ps)
        fdv = to_float(best.get("fdv"))
        mcap = to_float(best.get("marketCap"))
        basis = "market cap" if mcap else "fdv"
        mcap = mcap or fdv
        if not mcap:
            continue
        created_ms = min((x.get("pairCreatedAt") for x in ps if x.get("pairCreatedAt")), default=None)
        created = datetime.fromtimestamp(created_ms / 1000, timezone.utc).isoformat() if created_ms else None
        tx = (best.get("txns") or {}).get("h24") or {}
        pc = best.get("priceChange") or {}
        base = best.get("baseToken") or {}
        sym = (base.get("symbol") or "").upper()
        rid = f"dex-{chain}-{addr}"
        rows[rid] = {
            "id": rid, "symbol": sym, "name": base.get("name") or sym,
            "image": (best.get("info") or {}).get("imageUrl") or "",
            "current_price": price, "market_cap": mcap, "total_volume": vol,
            "circulating_supply": mcap / price, "fully_diluted_valuation": fdv,
            "price_change_percentage_1h_in_currency": to_float(pc.get("h1")),
            "price_change_percentage_24h_in_currency": to_float(pc.get("h24")),
            "_dex": {
                "chain": chain, "address": addr, "pair": best.get("pairAddress"),
                "url": best.get("url") or "", "dex": best.get("dexId"),
                "liquidity_usd": liq, "pair_created_at": created,
                "buys_24h": tx.get("buys"), "sells_24h": tx.get("sells"), "mcap_basis": basis,
                "websites": [w.get("url") for w in ((best.get("info") or {}).get("websites") or []) if w.get("url")][:2],
                "socials": [x.get("type") for x in ((best.get("info") or {}).get("socials") or []) if x.get("type")][:6],
            },
        }
    return rows


def discover_dex(prev_by_id):
    wanted_list = {}
    for chain, addrs in gt_discover().items():
        wanted_list.setdefault(chain, []).extend(addrs)
    for a in prev_by_id.values():          # keep refreshing tokens found on earlier runs
        d = a.get("dex") or {}
        if d.get("chain") and d.get("address"):
            lst = wanted_list.setdefault(d["chain"], [])
            if d["address"] not in lst:
                lst.append(d["address"])
    pairs = []
    for chain, addrs in wanted_list.items():
        if time.time() - T0 > DEX_BUDGET_S:
            log("[dex] time budget reached; skipping remaining chains")
            break
        pairs.extend(ds_fetch(chain, addrs))
    wanted = {c: {x.lower() for x in addrs} for c, addrs in wanted_list.items()}
    rows = pairs_to_rows(pairs, wanted)
    log(f"[dex] {sum(len(v) for v in wanted_list.values())} tokens queried, {len(rows)} priced")
    return rows


def fetch_category_rows(headers, rows):
    """Pull use-case categories; merge their rows into the pool; return id -> {category ids}."""
    members = {}
    for cat_id in CATEGORY_USE_CASES:
        if time.time() - T0 > CATEGORY_BUDGET_S:
            log("[category] time budget reached; skipping remaining categories")
            break
        try:
            data = http_get(CG_MARKETS_URL, params={**MARKET_PARAMS, "category": cat_id, "page": 1},
                            headers=headers, retries=2).json()
        except Exception as exc:
            log(f"[category] {cat_id}: skipped ({exc})")
            time.sleep(CG_DELAY)
            continue
        n = 0
        for c in data if isinstance(data, list) else []:
            if c.get("id"):
                rows.setdefault(c["id"], c)
                members.setdefault(c["id"], set()).add(cat_id)
                n += 1
        log(f"[category] {cat_id}: {n} coins")
        time.sleep(CG_DELAY)
    return members


def looks_like_stablecoin(coin):
    price = to_float(coin.get("current_price"))
    if price is None:
        return False
    c24 = abs(to_float(coin.get("price_change_percentage_24h_in_currency"), 0.0))
    c7 = abs(to_float(coin.get("price_change_percentage_7d_in_currency"), 0.0))
    return 0.97 <= price <= 1.03 and c24 < 1.0 and c7 < 2.0


def assign_use_case(coin_id, name, cat_ids, profile_categories):
    keys = set()
    for cid in cat_ids or []:
        if cid in CATEGORY_USE_CASES:
            keys.add(CATEGORY_USE_CASES[cid])
    if coin_id in UC_OVERRIDES:
        keys.add(UC_OVERRIDES[coin_id])
    blob = f"{name} " + " ".join(profile_categories or [])
    if not keys:
        for key, rx in UC_KEYWORDS.items():
            if rx.search(blob):
                keys.add(key)
    if not keys:
        keys.add("other")
    return min(keys, key=lambda k: UC_RANK[k])


def build_asset(coin, watch=False):
    coin_id = coin.get("id") or ""
    symbol = (coin.get("symbol") or "").upper()
    name = coin.get("name") or ""
    price = to_float(coin.get("current_price"))
    mcap = to_float(coin.get("market_cap"))
    volume = to_float(coin.get("total_volume"), 0.0)
    circ = to_float(coin.get("circulating_supply"))
    if not circ and mcap and price:
        circ = mcap / price
    if price is None or not mcap or mcap <= 0 or not circ or circ <= 0:
        return None

    dex = coin.get("_dex")
    if not watch:
        if BAN_TOP10 and (coin_id in BANNED_IDS or symbol in BANNED_SYMBOLS):
            return None
        if DERIVATIVE_NAME_RE.search(name):
            return None
        if price > MAX_PRICE_USD:                     # already expensive: skip
            return None
        if dex:
            if (symbol in DEX_MAJOR_SYMBOLS or (dex.get("liquidity_usd") or 0) < DEX_MIN_LIQUIDITY
                    or mcap < DEX_MIN_MCAP or mcap > DEX_MAX_MCAP or volume < MIN_VOLUME_24H):
                return None
        else:
            if looks_like_stablecoin(coin) or mcap < MIN_MARKET_CAP or volume < MIN_VOLUME_24H:
                return None

    total_supply = to_float(coin.get("total_supply"))
    max_supply = to_float(coin.get("max_supply"))
    fdv = to_float(coin.get("fully_diluted_valuation"))
    if not fdv:
        basis = max_supply or total_supply
        fdv = price * basis if basis else None
    fdv_ratio = (fdv / mcap) if fdv else None
    if fdv_ratio is None:
        dilution = "UNKNOWN"
    elif fdv_ratio >= FDV_CRITICAL_RATIO:
        dilution = "CRITICAL"
    elif fdv_ratio >= FDV_WARN_RATIO:
        dilution = "WARNING"
    else:
        dilution = "OK"

    turnover = volume / mcap
    momentum = "HIGH" if turnover >= MOMENTUM_HIGH else "ELEVATED" if turnover >= MOMENTUM_ELEVATED else "NORMAL"

    ath = to_float(coin.get("ath"))
    ath_change = to_float(coin.get("ath_change_percentage"))
    if ath_change is None and ath:
        ath_change = (price / ath - 1.0) * 100.0

    # 7-day sparkline analytics (compression / position in range)
    sp = [x for x in ((coin.get("sparkline_in_7d") or {}).get("price") or []) if isinstance(x, (int, float))]
    range_7d = pos_in_range = None
    spark = []
    if len(sp) >= 24:
        lo, hi = min(sp), max(sp)
        if lo > 0:
            range_7d = (hi / lo - 1.0) * 100.0
        if hi > lo:
            pos_in_range = clamp((price - lo) / (hi - lo), 0.0, 1.0)
        step = max(1, len(sp) // 42)
        spark = [float(f"{x:.6g}") for x in sp[::step]]

    return {
        "id": coin_id, "name": name, "symbol": symbol, "logo": coin.get("image") or "",
        "rank": coin.get("market_cap_rank"), "watchlist": bool(watch),
        "price": price, "market_cap": mcap, "volume_24h": volume,
        "circulating_supply": circ, "total_supply": total_supply, "max_supply": max_supply,
        "circulating_pct_of_max": (circ / max_supply * 100.0) if max_supply else None,
        "fdv": fdv, "fdv_ratio": fdv_ratio, "dilution_alert": dilution,
        "turnover_ratio": turnover, "momentum": momentum,
        "tier": "scarce" if circ <= SCARCE_MAX else "ecosystem",
        "ath": ath, "ath_date": coin.get("ath_date"),
        "atl": to_float(coin.get("atl")), "atl_date": coin.get("atl_date"),
        "ath_change_pct": ath_change,
        "atl_change_pct": to_float(coin.get("atl_change_percentage")),
        "change_1h": to_float(coin.get("price_change_percentage_1h_in_currency")),
        "change_24h": to_float(coin.get("price_change_percentage_24h_in_currency")),
        "change_7d": to_float(coin.get("price_change_percentage_7d_in_currency")),
        "range_7d_pct": range_7d, "pos_in_range": pos_in_range, "spark": spark,
        "vol_ratio": None,
        "venue": "dex" if dex else "cg", "dex": dex, "security": None, "security_checked_at": None,
        "zeros": 0, "hunt": None, "utility": None, "meme": False, "meme_utility": False,
        "overlooked": None, "history": None, "liquidity": None, "launch": None,
        "site_summary": None, "pending_scan": False,
        "use_case": "other", "use_case_label": UC_LABEL["other"], "use_case_rank": UC_RANK["other"],
        "category_ids": [], "profile": None, "profile_fetched_at": None,
        "news": [], "news_hits": 0, "adoption_hits": 0, "backing_strong": False,
        "stage": "Neutral", "stage_note": "", "setup_score": 0.0, "drivers": [],
    }


# --------------------------------------------------------------------------- #
# Coin profiles: backing, liquidity, developer and community signals
# --------------------------------------------------------------------------- #

PROFILE_PARAMS = {"localization": "false", "tickers": "true", "market_data": "false",
                  "community_data": "true", "developer_data": "true", "sparkline": "false"}


def fetch_profile(coin_id, headers):
    d = http_get(f"{CG_BASE}/coins/{coin_id}", params=PROFILE_PARAMS, headers=headers, retries=3).json()
    return parse_profile(d)


def fetch_profile_by_contract(chain, address, headers):
    """Many DEX tokens are also listed on CoinGecko: look them up by contract address."""
    platform = CG_PLATFORMS.get(chain)
    if not platform:
        return None
    d = http_get(f"{CG_BASE}/coins/{platform}/contract/{address}", params=PROFILE_PARAMS,
                 headers=headers, retries=2).json()
    if not isinstance(d, dict) or not d.get("id"):
        return None
    prof = parse_profile(d)
    prof["cg_id"] = d["id"]
    return prof


def parse_profile(d):
    links = d.get("links") or {}
    dev = d.get("developer_data") or {}
    com = d.get("community_data") or {}

    tickers = [t for t in (d.get("tickers") or []) if not t.get("is_stale") and not t.get("is_anomaly")]
    by_ex = {}
    for t in tickers:
        name = (t.get("market") or {}).get("name") or "?"
        vol = to_float((t.get("converted_volume") or {}).get("usd"), 0.0)
        cur = by_ex.setdefault(name, {"name": name, "volume_usd": 0.0, "trust": t.get("trust_score")})
        cur["volume_usd"] += vol
    exchanges = sorted(by_ex.values(), key=lambda e: e["volume_usd"], reverse=True)
    tier1 = [e["name"] for e in exchanges if any(x in e["name"].lower() for x in TIER1_EXCHANGES)]

    homepage = next((u for u in (links.get("homepage") or []) if u), "")
    whitepaper = links.get("whitepaper") or ""
    github = [u for u in ((links.get("repos_url") or {}).get("github") or []) if u][:2]
    platforms = {k: v for k, v in (d.get("platforms") or {}).items() if k and v}

    return {
        "description": clean_text((d.get("description") or {}).get("en"))[:700],
        "categories": [c for c in (d.get("categories") or []) if c][:8],
        "genesis_date": d.get("genesis_date"),
        "hashing_algorithm": d.get("hashing_algorithm"),
        "homepage": homepage, "whitepaper": whitepaper,
        "twitter": links.get("twitter_screen_name") or "",
        "subreddit": links.get("subreddit_url") or "",
        "github": github,
        "platforms": dict(list(platforms.items())[:4]),
        "sentiment_up_pct": to_float(d.get("sentiment_votes_up_percentage")),
        "watchlist_users": d.get("watchlist_portfolio_users"),
        "median_spread_pct": (statistics.median(sp) if (sp := [x for x in (to_float(t.get("bid_ask_spread_percentage")) for t in tickers) if x is not None]) else None),
        "exchange_count": len(exchanges),
        "top_exchanges": [{"name": e["name"], "volume_usd": round(e["volume_usd"]), "trust": e["trust"]}
                          for e in exchanges[:6]],
        "tier1_listings": len(tier1), "tier1_names": tier1[:8],
        "developer": {
            "stars": dev.get("stars"), "forks": dev.get("forks"),
            "commit_count_4_weeks": dev.get("commit_count_4_weeks"),
            "pull_requests_merged": dev.get("pull_requests_merged"),
            "closed_issues": dev.get("closed_issues"), "total_issues": dev.get("total_issues"),
        },
        "community": {
            "twitter_followers": com.get("twitter_followers"),
            "reddit_subscribers": com.get("reddit_subscribers"),
            "telegram_users": com.get("telegram_channel_user_count"),
        },
    }


def enrich_profiles(assets, headers, now):
    ranked = sorted(assets, key=lambda a: (not a["watchlist"],
                                           -max(a["setup_score"], (a.get("hunt") or {}).get("score", 0))))
    stale_before = now - timedelta(days=ENRICH_REFRESH_DAYS)
    todo = []
    for a in ranked:
        if a["venue"] == "dex" and not (a.get("hunt") and (a.get("dex") or {}).get("chain") in CG_PLATFORMS):
            continue
        fetched = parse_date(a.get("profile_fetched_at"))
        if not a.get("profile") or not fetched or fetched < stale_before:
            todo.append(a)
        if len(todo) >= ENRICH_MAX_PER_RUN:
            break
    fails = 0
    done = 0
    for a in todo:
        if time.time() - T0 > ENRICH_BUDGET_S:
            log("[profile] time budget reached; remaining coins will be enriched next run")
            break
        try:
            if a["venue"] == "dex":
                try:
                    prof = fetch_profile_by_contract(a["dex"]["chain"], a["dex"]["address"], headers)
                except RuntimeError as exc:
                    if "404" not in str(exc):
                        raise
                    prof = None                       # not listed on CoinGecko
                a["profile"] = prof or {"unlisted": True}
            else:
                a["profile"] = fetch_profile(a["id"], headers)
            a["profile_fetched_at"] = now.isoformat()
            done += 1
            fails = 0
        except Exception as exc:
            fails += 1
            log(f"[profile] {a['id']}: failed ({exc})")
            if fails >= 3:
                log("[profile] too many consecutive failures; stopping enrichment for this run")
                break
        time.sleep(ENRICH_DELAY)
    log(f"[profile] enriched {done}/{len(todo)} queued coins")


# --------------------------------------------------------------------------- #
# News scraping and adoption-signal strength
# --------------------------------------------------------------------------- #

TIER1_INST_RE = re.compile(
    r"\b(jpmorgan|j\.p\. morgan|jpm coin|hsbc|citi|citigroup|swift|dtcc|euroclear|blackrock|"
    r"franklin templeton|fidelity|visa|mastercard|goldman sachs|morgan stanley|bny|state street|"
    r"deutsche bank|santander|bnp paribas|standard chartered|barclays|lloyds|natwest|ubs|"
    r"soci[eé]t[eé] g[eé]n[eé]rale|the clearing house|clearing house|uk finance|central bank|"
    r"federal reserve|bank of england|ecb|nasdaq|cme|nyse)\b", re.I)
GENERIC_INST_RE = re.compile(
    r"\b(bank|banks|banking|consortium|asset manager|custod\w+|institution\w*|financial institutions?)\b", re.I)
ACTION_STRONG_RE = re.compile(
    r"\b(launch\w*|goes live|went live|now live|deploy\w*|partnership|partners?|selected|integrat\w+|"
    r"adopt\w*|rolls? out|rolled out|settle\w*|mainnet|go live)\b", re.I)
ACTION_MED_RE = re.compile(
    r"\b(pilot|trial|proof[- ]of[- ]concept|poc|sandbox|tokeni[sz]ed|tokeni[sz]ation|rwa|"
    r"real[- ]world assets?|testing|explor\w+)\b", re.I)
TAG_PATTERNS = [
    ("TOKENIZED DEPOSIT", re.compile(r"tokeni[sz]ed (bank )?deposits?|deposit tokens?|tokeni[sz]ed sterling", re.I)),
    ("RWA", re.compile(r"\brwa\b|real[- ]world assets?|tokeni[sz]ed (treasur\w+|bonds?|funds?|securities|assets?|equit\w+)", re.I)),
    ("BANK PILOT", re.compile(
        r"(bank|banks|consortium|clearing house|uk finance).{0,80}(pilot|trial|proof[- ]of[- ]concept|sandbox)"
        r"|(pilot|trial|sandbox).{0,80}(bank|banks|consortium)", re.I | re.S)),
    ("CONSORTIUM", re.compile(r"consortium|clearing house|uk finance", re.I)),
    ("CBDC", re.compile(r"\bcbdc\b|central bank digital", re.I)),
]


EXCHANGE_TIER1_RE = re.compile(r"\b(binance|coinbase|upbit|bithumb|robinhood|kraken|okx|bybit)\b", re.I)
LISTING_ACTION_RE = re.compile(
    r"\b(will list|to list|lists|listing|listed|adds? support|roadmap|spot trading|perpetual contract|futures contract)\b", re.I)


def classify_news(text):
    """Return (adoption, tags, inst_weight, action_weight, bonus)."""
    tags = [n for n, rx in TAG_PATTERNS if rx.search(text)]
    inst = 3.0 if TIER1_INST_RE.search(text) else 2.0 if GENERIC_INST_RE.search(text) else 0.0
    act = 2.0 if ACTION_STRONG_RE.search(text) else 1.5 if ACTION_MED_RE.search(text) else 0.0
    if EXCHANGE_TIER1_RE.search(text) and LISTING_ACTION_RE.search(text):
        tags.append("LISTING")                      # major-exchange listing: historically the biggest small-cap catalyst
        inst, act = max(inst, 3.0), max(act, 2.0)
    adoption = bool(tags) or (inst > 0 and act > 0)
    bonus = 0.5 if any(t in ("TOKENIZED DEPOSIT", "CBDC", "RWA", "LISTING") for t in tags) else 0.0
    if adoption and not tags:
        tags = ["INSTITUTIONAL"]
    return adoption, (tags if adoption else []), inst, act, bonus


def parse_feed(content, default_source):
    items = []
    try:
        root = ET.fromstring(content)
    except ET.ParseError:
        root = ET.fromstring(re.sub(rb"[\x00-\x08\x0b\x0c\x0e-\x1f]", b"", content))

    def local(tag):
        return tag.split("}", 1)[-1] if "}" in tag else tag

    for node in root.iter():
        if local(node.tag) not in ("item", "entry"):
            continue
        fields, href = {}, None
        for child in node:
            ct = local(child.tag)
            if ct == "link":
                if child.get("href") and child.get("rel") in (None, "alternate"):
                    href = child.get("href")
                elif child.text and child.text.strip():
                    fields.setdefault("link", child.text.strip())
            elif ct in ("title", "description", "summary", "pubDate", "published", "updated",
                        "source", "encoded", "content"):
                fields.setdefault(ct, (child.text or "").strip())
        link = href or fields.get("link")
        title = clean_text(fields.get("title"))
        if not title or not link:
            continue
        summary = clean_text(fields.get("description") or fields.get("summary")
                             or fields.get("encoded") or fields.get("content"))
        items.append({
            "title": title, "url": link, "summary": summary[:SUMMARY_MAX_CHARS],
            "published": parse_date(fields.get("pubDate") or fields.get("published") or fields.get("updated")),
            "source": clean_text(fields.get("source")) or default_source,
        })
    return items


def google_news_url(q):
    return f"https://news.google.com/rss/search?q={quote_plus(q + ' when:30d')}&hl=en-US&gl=US&ceid=US:en"


def fetch_news(extra_queries):
    sources = list(RSS_FEEDS)
    for q in GOOGLE_NEWS_QUERIES:
        sources.append((f"Wire query: {q}", google_news_url(q)))
    for q in extra_queries:
        sources.append((f"Watchlist: {q}", google_news_url(q)))

    cutoff = datetime.now(timezone.utc) - timedelta(days=NEWS_MAX_AGE_DAYS)
    seen, news, status = set(), [], []
    for label, url in sources:
        try:
            raw = parse_feed(http_get(url, retries=2).content, label)
        except Exception as exc:
            log(f"[news] {label}: FAILED ({exc})")
            status.append({"feed": label, "ok": False, "items": 0})
            continue
        kept = 0
        for it in raw:
            if it["published"] and it["published"] < cutoff:
                continue
            key = re.sub(r"[^a-z0-9]+", " ", it["title"].lower()).strip()
            if key in seen or it["url"] in seen:
                continue
            seen.add(key)
            seen.add(it["url"])
            adoption, tags, inst, act, bonus = classify_news(f"{it['title']} {it['summary']}")
            news.append({
                "title": it["title"], "url": it["url"], "source": it["source"],
                "summary": it["summary"],
                "published": it["published"].isoformat() if it["published"] else None,
                "adoption": adoption, "tags": tags, "inst": inst, "act": act, "bonus": bonus,
            })
            kept += 1
        log(f"[news] {label}: {kept} new items")
        status.append({"feed": label, "ok": True, "items": kept})
        time.sleep(0.5)
    return news, status


def build_matchers(asset):
    name_clean = re.sub(r"\s*\(.*?\)", "", asset["name"]).strip()
    terms = {name_clean, *ALIASES.get(asset["id"], [])}
    if asset.get("venue") == "dex":                 # DEX tokens often have generic names: be strict
        terms = {name_clean} if len(name_clean) >= 7 else set()
    regs = []
    for term in terms:
        if len(term) < 3:
            continue
        flags = re.I if (len(term) >= 7 or " " in term) else 0
        regs.append(re.compile(r"(?<![A-Za-z0-9])" + re.escape(term) + r"(?![A-Za-z0-9])", flags))
    sym = asset["symbol"]
    if len(sym) >= (4 if asset.get("venue") == "dex" else 3) and sym not in AMBIGUOUS_SYMBOLS and sym.isalnum():
        regs.append(re.compile(r"(?<![A-Za-z0-9])\$?" + re.escape(sym) + r"(?![A-Za-z0-9])"))
    return regs


def intersect_news(assets, news):
    matchers = {a["id"]: build_matchers(a) for a in assets}
    by_id = {a["id"]: a for a in assets}
    wire = []
    for item in news:
        blob = f"{item['title']} {item['summary']}"
        matched = []
        for a in assets:
            regs = matchers[a["id"]]
            if not any(rx.search(blob) for rx in regs):
                continue
            title_hit = any(rx.search(item["title"]) for rx in regs)
            strength = 0.0
            if item["adoption"]:
                strength = item["inst"] + item["act"] + item["bonus"] + (1.0 if title_hit else 0.0)
            a["news"].append({**item, "strength": round(strength, 1), "title_hit": title_hit})
            matched.append(a["id"])
        if item["adoption"]:
            wire.append({**item, "matched": [by_id[i]["symbol"] for i in matched][:8]})

    epoch = datetime(1970, 1, 1, tzinfo=timezone.utc).isoformat()
    for a in assets:
        items = a["news"]
        items.sort(key=lambda n: (n["strength"], n["published"] or epoch), reverse=True)
        a["news_hits"] = len(items)
        a["adoption_hits"] = sum(1 for n in items if n["adoption"])
        a["news"] = items[:NEWS_PER_ASSET]
    wire.sort(key=lambda n: n["published"] or epoch, reverse=True)
    return wire[:WIRE_MAX_ITEMS]


# --------------------------------------------------------------------------- #
# Stage + setup score (what the market looked like before past spikes)
# --------------------------------------------------------------------------- #

def classify_stage(a):
    c7 = a["change_7d"] or 0.0
    c24 = a["change_24h"] or 0.0
    t = a["turnover_ratio"]
    rng = a["range_7d_pct"]
    if c7 >= 40:
        return "Extended", "Already up 40%+ this week; the early window has probably passed."
    if c24 >= 10 and t >= 0.15:
        return "Ignition", "Price breaking out on heavy turnover right now."
    if t >= 0.08 and abs(c24) < 6 and (rng is None or rng <= 25):
        return "Accumulating", "Volume is building while price stays contained."
    if rng is not None and rng <= 12 and t < 0.08:
        return "Dormant base", "Tight multi-day range on quiet volume (a coiled base)."
    return "Neutral", "No clear setup pattern."


def score_asset(a):
    drivers = []

    def add(key, label, pts, mx, note):
        drivers.append({"key": key, "label": label, "pts": round(pts, 1), "max": mx, "note": note})

    strong = [n for n in a["news"] if n["adoption"] and n["strength"] >= ALERT_NEWS_MIN_STRENGTH]
    other = max(0, a["adoption_hits"] - len(strong))
    add("catalyst", "Institutional catalyst", min(30, 12 * len(strong) + 6 * other), 30,
        f"{len(strong)} strong and {other} other adoption headlines in the last {NEWS_MAX_AGE_DAYS} days")

    acc = clamp(a["turnover_ratio"] / 0.25, 0, 1) * 15
    vr = a.get("vol_ratio")
    if vr:
        acc += clamp((vr - 1) / 3, 0, 1) * 10
        note = f"Turnover {a['turnover_ratio'] * 100:.1f}%, volume {vr:.1f}x its recent baseline"
    else:
        note = f"Turnover {a['turnover_ratio'] * 100:.1f}%, volume baseline still building"
    add("accumulation", "Accumulation", acc, 25, note)

    rng = a["range_7d_pct"]
    base = 0 if rng is None else 12 if rng <= 8 else 9 if rng <= 15 else 5 if rng <= 25 else 0
    add("base", "Tight base", base, 12, "7-day range n/a" if rng is None else f"7-day range {rng:.1f}%")

    dd = a["ath_change_pct"]
    under = 0 if dd is None or dd > -10 else clamp(abs(dd) / 90, 0, 1) * 10
    add("undervalued", "Discount to all-time high", under, 10, "n/a" if dd is None else f"{dd:.0f}% from ATH")

    scarce = (6 if a["circulating_supply"] <= 300e6 else 3) if a["tier"] == "scarce" else 0
    add("scarcity", "Scarcity", scarce, 6, f"{a['circulating_supply'] / 1e6:.0f}M circulating")

    c24, c1 = a["change_24h"] or 0.0, a["change_1h"] or 0.0
    ign = clamp(c24, 0, 20) / 20 * 6 + clamp(c1, 0, 5) / 5 * 4
    if a["turnover_ratio"] < MOMENTUM_ELEVATED:
        ign *= 0.4
    add("ignition", "Breakout momentum", ign, 10, f"1h {c1:+.1f}%, 24h {c24:+.1f}%")

    p = a.get("profile") or {}
    q, qn = 0.0, []
    if p:
        t1 = p.get("tier1_listings") or 0
        q += 3 if t1 >= 3 else 1.5 if t1 >= 1 else 0
        qn.append(f"{t1} major exchanges")
        commits = (p.get("developer") or {}).get("commit_count_4_weeks")
        q += 2 if commits and commits >= 20 else 1 if commits and commits >= 5 else 0
        if commits is not None:
            qn.append(f"{commits} commits/4w")
        tw = (p.get("community") or {}).get("twitter_followers")
        q += 2 if tw and tw >= 50000 else 1 if tw and tw >= 10000 else 0
    add("quality", "Backing quality", q, 7, ", ".join(qn) if qn else "profile pending")

    score = sum(d["pts"] for d in drivers)
    if a["dilution_alert"] == "CRITICAL":
        score -= 15
        add("dilution", "Dilution risk", -15, 0, f"FDV is {a['fdv_ratio']:.1f}x market cap")
    elif a["dilution_alert"] == "WARNING":
        score -= 8
        add("dilution", "Dilution risk", -8, 0, f"FDV is {a['fdv_ratio']:.1f}x market cap")
    stage, note = classify_stage(a)
    if stage == "Extended" and (a["change_7d"] or 0) >= 60:
        score -= 10
        add("extended", "Chasing risk", -10, 0, "Up 60%+ in 7 days")
    a["stage"], a["stage_note"] = stage, note
    a["drivers"] = drivers
    a["setup_score"] = round(clamp(score, 0, 100), 1)
    analyse_liquidity(a)
    detect_meme(a)
    analyse_utility(a)
    analyse_hunt(a)
    analyse_overlooked(a)
    a["meme_utility"] = bool(a["meme"] and (a.get("utility") or {}).get("score", 0) >= 40)


# --------------------------------------------------------------------------- #
# Use case / utility: does the coin actually DO something?
# --------------------------------------------------------------------------- #

UTIL_DOMAIN_POINTS = {"institutional": 35, "payments": 32, "interop": 32, "l1": 28, "defi": 26,
                      "ai_depin": 24, "gaming": 18, "privacy": 18, "other": 8, "meme": 0}
UTIL_DOMAIN_TEXT = {
    "institutional": "Bank and real-world-asset infrastructure",
    "payments": "Payments and settlement", "interop": "Cross-chain connectivity and data oracles",
    "l1": "Base-layer blockchain or scaling network", "defi": "Decentralized finance",
    "ai_depin": "AI and physical-infrastructure networks", "gaming": "Gaming and metaverse",
    "privacy": "Privacy technology", "other": "Use not clearly classified",
    "meme": "Meme / community coin with no stated function",
}


def analyse_utility(a):
    prof = a.get("profile") or {}
    dex = a.get("dex") or {}
    key = a["use_case"]
    evidence = []

    domain = UTIL_DOMAIN_POINTS.get(key, 8)
    cats = prof.get("categories") or []
    if cats:
        evidence.append("Categories: " + ", ".join(cats[:4]))

    doc = 0
    if prof.get("homepage") or dex.get("websites"):
        doc += 6
        evidence.append("Has a website")
    if prof.get("whitepaper"):
        doc += 4
        evidence.append("Whitepaper published")
    if prof.get("github"):
        doc += 6
        evidence.append("Public code repository")
    desc = prof.get("description") or ((a.get("site_summary") or {}).get("text") or "")
    if not prof.get("description") and desc:
        evidence.append("Description taken from the project's own website")
    if len(desc) > 150:
        doc += 4
    if prof.get("twitter") or dex.get("socials"):
        doc += 2
    doc = min(20, doc)

    dev = prof.get("developer") or {}
    commits = dev.get("commit_count_4_weeks")
    devpts = 15 if commits and commits >= 20 else 9 if commits and commits >= 5 else 4 if commits else 0
    if commits:
        evidence.append(f"{commits} developer commits in the last 4 weeks")

    strong = sum(1 for n in a["news"] if n["adoption"] and n["strength"] >= ALERT_NEWS_MIN_STRENGTH)
    other = max(0, a["adoption_hits"] - strong)
    adopt = min(20, 10 * strong + 5 * other)
    if strong or other:
        evidence.append(f"{strong + other} institutional adoption headline(s) in the last {NEWS_MAX_AGE_DAYS} days")

    t1 = prof.get("tier1_listings") or 0
    ex_count = prof.get("exchange_count") or 0
    market = 10 if t1 >= 3 else 6 if t1 >= 1 else 3 if ex_count >= 5 else 0
    if t1:
        evidence.append(f"Listed on {t1} major exchange(s)")

    score = domain + doc + devpts + adopt + market
    if key == "meme" and not (strong or other):
        score = min(score, 25)
    score = int(clamp(score, 0, 100))
    if key == "meme" and not (strong or other):
        verdict = "Meme / no stated use"
    elif score >= 65:
        verdict = "Strong use case"
    elif score >= 40:
        verdict = "Some utility"
    elif score >= 20:
        verdict = "Weak or unclear use case"
    else:
        verdict = "No clear use case"

    summary = desc[:260].rsplit(" ", 1)[0] + ("..." if len(desc) > 260 else "") if desc else ""
    if not summary:
        summary = ("No project description could be found automatically. Open the token's website and "
                   "read what it actually does before buying." if a["venue"] == "dex" else "")
    a["utility"] = {
        "score": score, "label": verdict, "domain": UTIL_DOMAIN_TEXT.get(key, ""),
        "summary": summary, "evidence": evidence[:8],
        "homepage": prof.get("homepage") or (dex.get("websites") or [""])[0],
        "whitepaper": prof.get("whitepaper") or "",
        "github": (prof.get("github") or [""])[0],
        "documented": bool(prof.get("homepage") or dex.get("websites")),
    }


# --------------------------------------------------------------------------- #
# Zero-cancel hunt: cheap-looking coins with room to run, graded for rug-pull risk
# --------------------------------------------------------------------------- #

def zero_count(price):
    """Leading zeros after the decimal point: 0.0000123 -> 4, 0.0042 -> 2, 0.5 -> 0."""
    if not price or price <= 0 or price >= 1:
        return 0
    return max(0, -int(math.floor(math.log10(price))) - 1)


def contract_of(a):
    d = a.get("dex") or {}
    if d.get("chain") and d.get("address"):
        return d["chain"], d["address"]
    plats = (a.get("profile") or {}).get("platforms") or {}
    for cgp, chain in CG_PLATFORM_TO_CHAIN.items():
        if plats.get(cgp):
            return chain, plats[cgp]
    return None


def needs_scan(a):
    """DEX tokens must pass a scan to be shown. Listed coins are scanned when they look risky."""
    if a["venue"] == "dex":
        return True
    prof = a.get("profile") or {}
    return bool(a.get("hunt") and (prof.get("tier1_listings") or 0) == 0 and contract_of(a))


HARD_SOLANA_RE = re.compile(r"freeze authority|honeypot|rug|copycat|blacklist", re.I)


def security_verdict(sec):
    """Fail-closed rules. Returns (verdict, block_reasons, caution_reasons)."""
    block, caution = [], []
    if sec.get("source") == "GoPlus":
        if sec.get("honeypot"):
            block.append("Honeypot: sells are blocked")
        if sec.get("cannot_sell_all"):
            block.append("Holders cannot sell all their tokens")
        if (sec.get("sell_tax_pct") or 0) >= BLOCK_SELL_TAX:
            block.append(f"Sell tax {sec['sell_tax_pct']}%")
        if (sec.get("buy_tax_pct") or 0) >= BLOCK_BUY_TAX:
            block.append(f"Buy tax {sec['buy_tax_pct']}%")
        if sec.get("owner_change_balance"):
            block.append("Owner can change holder balances")
        if sec.get("selfdestruct"):
            block.append("Contract can self-destruct")
        for key, msg in (("mintable", "Owner can mint more supply"), ("hidden_owner", "Hidden owner"),
                         ("transfer_pausable", "Owner can pause transfers"),
                         ("slippage_modifiable", "Owner can change taxes at will"),
                         ("can_take_back_ownership", "Ownership can be taken back")):
            if sec.get(key):
                caution.append(msg)
        if sec.get("open_source") is False:
            caution.append("Contract source is not verified")
        for key, label in (("sell_tax_pct", "Sell tax"), ("buy_tax_pct", "Buy tax")):
            if 5 <= (sec.get(key) or 0) < 20:
                caution.append(f"{label} {sec[key]}%")
    else:
        for name in sec.get("danger") or []:
            (block if HARD_SOLANA_RE.search(str(name)) else caution).append(f"Scan danger: {name}")
        for name in (sec.get("warn") or [])[:3]:
            caution.append(f"Scan warning: {name}")
    verdict = "fail" if block else "caution" if caution else "pass"
    return verdict, block, caution


def parse_goplus(info):
    def flag(k):
        v = info.get(k)
        return None if v in (None, "") else str(v) == "1"

    def pct_of(k):
        v = to_float(info.get(k))
        return None if v is None else round(v * 100, 1)

    holders = to_float(info.get("holder_count"))
    hl = info.get("holders") or []
    top10 = round(sum(to_float(h.get("percent"), 0.0) for h in hl[:10]) * 100, 1) if hl else None
    lp = info.get("lp_holders") or []
    lp_locked = (round(sum(to_float(x.get("percent"), 0.0) for x in lp if str(x.get("is_locked")) == "1") * 100, 1)
                 if lp else None)
    return {"source": "GoPlus", "honeypot": flag("is_honeypot"),
            "buy_tax_pct": pct_of("buy_tax"), "sell_tax_pct": pct_of("sell_tax"),
            "mintable": flag("is_mintable"), "hidden_owner": flag("hidden_owner"),
            "open_source": flag("is_open_source"), "cannot_sell_all": flag("cannot_sell_all"),
            "owner_change_balance": flag("owner_change_balance"), "selfdestruct": flag("selfdestruct"),
            "transfer_pausable": flag("transfer_pausable"), "slippage_modifiable": flag("slippage_modifiable"),
            "can_take_back_ownership": flag("can_take_back_ownership"),
            "holders": int(holders) if holders else None, "top10_pct": top10, "lp_locked_pct": lp_locked,
            "creator_pct": pct_of("creator_percent")}


def goplus_scan(chain, addrs):
    out = {}
    cid = GOPLUS_CHAIN_IDS.get(chain)
    if not cid:
        return out
    for i in range(0, len(addrs), 30):
        chunk = addrs[i:i + 30]
        try:
            r = http_get(f"https://api.gopluslabs.io/api/v1/token_security/{cid}",
                         params={"contract_addresses": ",".join(chunk)}, retries=2).json()
        except Exception as exc:
            log(f"[security] goplus {chain} batch failed ({exc})")
            continue
        res = r.get("result") or {}
        for addr in chunk:
            info = res.get(addr.lower())
            if info:
                out[addr.lower()] = parse_goplus(info)
        time.sleep(1.5)
    return out


def rugcheck_scan(addr):
    try:
        r = http_get(f"https://api.rugcheck.xyz/v1/tokens/{addr}/report/summary", retries=2).json()
    except Exception as exc:
        log(f"[security] rugcheck failed ({exc})")
        return None
    risks = r.get("risks")
    if not isinstance(risks, list):
        return None
    lvl = lambda x: str(x.get("level") or "").lower()
    return {"source": "RugCheck",
            "danger": [x.get("name") for x in risks if lvl(x) == "danger"][:6],
            "warn": [x.get("name") for x in risks if lvl(x) == "warn"][:6]}


def scan_security_batch(assets, now):
    stale = now - timedelta(days=SECURITY_REFRESH_DAYS)

    def due(a):
        return not a.get("security") or (parse_date(a.get("security_checked_at")) or stale) <= stale

    cands = [a for a in assets if needs_scan(a) and contract_of(a) and due(a)]
    cands.sort(key=lambda a: (-((a.get("hunt") or {}).get("score", 0)), -a["volume_24h"]))
    by_chain = {}
    for a in cands[:SECURITY_MAX_PER_RUN]:
        chain, addr = contract_of(a)
        by_chain.setdefault(chain, []).append((a, addr))
    done = 0

    def finish(a, sec):
        sec["verdict"], sec["block"], sec["caution"] = security_verdict(sec)
        a["security"], a["security_checked_at"] = sec, now.isoformat()

    for chain, items in by_chain.items():
        if time.time() - T0 > ENRICH_BUDGET_S + 120:
            break
        if chain in GOPLUS_CHAIN_IDS:
            res = goplus_scan(chain, [addr for _, addr in items])
            for a, addr in items:
                if res.get(addr.lower()):
                    finish(a, res[addr.lower()])
                    done += 1
        elif chain == "solana":
            for a, addr in items[:SOLANA_SCAN_MAX]:
                sec = rugcheck_scan(addr)
                if sec:
                    finish(a, sec)
                    done += 1
                time.sleep(1.0)
    log(f"[security] scanned {done}/{len(cands)} tokens due for a scan")


# ---- liquidity, launch date, website summary ----

def analyse_liquidity(a):
    d = a.get("dex") or {}
    prof = a.get("profile") or {}
    mcap, vol = a["market_cap"], a["volume_24h"]
    if d.get("liquidity_usd") is not None:
        liq = d["liquidity_usd"]
        grade = ("Deep" if liq >= 1e6 else "Good" if liq >= 2.5e5 else "Okay" if liq >= 1e5
                 else "Thin" if liq >= 5e4 else "Very thin")
        q = max(liq, 1.0) / 2                       # constant-product estimate: half the pool is quote currency
        a["liquidity"] = {
            "kind": "DEX pool", "usd": liq, "grade": grade,
            "pct_of_mcap": round(liq / mcap * 100, 2) if mcap else None,
            "impact_1k_pct": round(1000 / (q + 1000) * 100, 2), "impact_10k_pct": round(10000 / (q + 10000) * 100, 2),
            "note": "Slippage is an estimate for standard pools; concentrated-liquidity pools can differ.",
        }
        return
    t1 = prof.get("tier1_listings") or 0
    spread = prof.get("median_spread_pct")
    grades = ["Thin", "Okay", "Good", "Deep"]
    idx = 3 if (t1 >= 2 and vol >= 5e6) else 2 if (t1 >= 1 or vol >= 2e6) else 1 if vol >= 5e5 else 0
    if spread is not None and spread > 2:
        idx = max(0, idx - 1)
    a["liquidity"] = {"kind": "Exchange order books", "usd": None, "grade": grades[idx], "spread_pct": spread,
                      "exchange_count": prof.get("exchange_count"), "volume_usd": vol,
                      "note": "Order-book depth is not published for free; this grade uses volume, spreads and listings."}


def analyse_launch(a, now):
    prof = a.get("profile") or {}
    d = a.get("dex") or {}
    h = a.get("history") or {}
    date, src = parse_date(prof.get("genesis_date")), "Project launch date"
    if not date and d.get("pair_created_at"):
        date, src = parse_date(d["pair_created_at"]), "First DEX trading pair created"
    if not date and h.get("days_of_data") and h["days_of_data"] < 360:
        date, src = now - timedelta(days=h["days_of_data"]), "First price on CoinGecko (approximate)"
    if date:
        a["launch"] = {"date": date.isoformat(), "age_days": max(0, (now - date).days), "source": src}
    else:
        older = (h.get("days_of_data") or 0) >= 360
        a["launch"] = {"date": None, "age_days": None,
                       "source": "Older than about a year (exact date not in the free data)" if older else "Not available"}


def fetch_site_summary(url):
    if not str(url).lower().startswith("https://"):
        return None
    try:
        r = requests.get(url, headers={"User-Agent": USER_AGENT}, timeout=8, stream=True)
        if r.status_code != 200:
            return None
        raw = b""
        for chunk in r.iter_content(8192):
            raw += chunk
            if len(raw) > 150_000:
                break
        r.close()
        text = raw.decode("utf-8", errors="ignore")
    except Exception:
        return None

    def meta(*names):
        for n in names:
            pat1 = r'<meta[^>]+(?:name|property)=["\']%s["\'][^>]*content=["\']([^"\']+)["\']' % re.escape(n)
            pat2 = r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+(?:name|property)=["\']%s["\']' % re.escape(n)
            m = re.search(pat1, text, re.I) or re.search(pat2, text, re.I)
            if m:
                return clean_text(m.group(1))
        return ""

    desc = meta("description", "og:description", "twitter:description")
    m = re.search(r"<title[^>]*>(.*?)</title>", text, re.I | re.S)
    title = clean_text(m.group(1)) if m else ""
    return (desc or title)[:300] or None


def enrich_site_summaries(assets, now):
    stale = now - timedelta(days=14)
    done = 0
    for a in assets:
        if done >= SITE_SUMMARY_MAX or time.time() - T0 > ENRICH_BUDGET_S + 120:
            break
        d = a.get("dex") or {}
        sites = d.get("websites") or []
        has_desc = bool((a.get("profile") or {}).get("description"))
        old = a.get("site_summary") or {}
        if a["venue"] != "dex" or not sites or has_desc:
            continue
        if old and (parse_date(old.get("fetched_at")) or stale) > stale:
            continue
        text = fetch_site_summary(sites[0])
        a["site_summary"] = {"text": text or "", "url": sites[0], "fetched_at": now.isoformat()}
        done += 1
    log(f"[site] read {done} project websites")


def detect_meme(a):
    prof = a.get("profile") or {}
    cats = " ".join(prof.get("categories") or [])
    a["meme"] = bool("meme-token" in (a.get("category_ids") or []) or re.search(r"meme", cats, re.I)
                     or a["use_case"] == "meme" or UC_KEYWORDS["meme"].search(a["name"]))


def analyse_overlooked(a):
    """Substance without attention: real use case + active builders + a small crowd + small cap."""
    prof = a.get("profile") or {}
    u = a.get("utility") or {}
    a["overlooked"] = None
    if not prof or prof.get("unlisted") or a["market_cap"] > 5e8 or a["volume_24h"] < 1.5e5:
        return
    tw = (prof.get("community") or {}).get("twitter_followers")
    wl = prof.get("watchlist_users")
    rank = a.get("rank")
    commits = (prof.get("developer") or {}).get("commit_count_4_weeks")
    reasons, att = [], 0
    if tw is not None:
        att += 15 if tw < 20000 else 10 if tw < 75000 else 5 if tw < 200000 else 0
        if tw < 75000:
            reasons.append(f"Small social following ({tw:,} followers on X)")
    if wl is not None:
        att += 10 if wl < 5000 else 6 if wl < 25000 else 2 if wl < 100000 else 0
        if wl < 25000:
            reasons.append(f"Few people are watching it ({wl:,} watchlists)")
    if rank:
        att += 5 if rank > 500 else 3 if rank > 250 else 0
    subs = 0
    if commits:
        subs += 10 if commits >= 20 else 5
        reasons.append(f"Developers are shipping ({commits} commits in 4 weeks)")
    if a["adoption_hits"] > 0:
        subs += 10
        reasons.append(f"{a['adoption_hits']} institutional or listing headline(s) recently")
    score = u.get("score", 0) * 0.45 + min(30, att) + min(20, subs)
    if u.get("score", 0) >= 50:
        reasons.insert(0, f"Real use case: {u.get('domain', '')} (utility {u.get('score')}/100)")
    if score >= 55 and u.get("score", 0) >= 50 and att >= 8:
        a["overlooked"] = {"score": int(score), "reasons": reasons[:6]}


def analyse_hunt(a):
    zeros = zero_count(a["price"])
    a["zeros"] = zeros
    if zeros < HUNT_MIN_ZEROS:
        a["hunt"] = None
        return
    now = datetime.now(timezone.utc)
    price, mcap = a["price"], a["market_cap"]
    dex = a.get("dex") or {}
    prof = a.get("profile") or {}
    sec = a.get("security") or {}
    liq = dex.get("liquidity_usd")
    vol, t = a["volume_24h"], a["turnover_ratio"]
    c24, c1 = a["change_24h"] or 0.0, a["change_1h"] or 0.0
    drivers = []

    def add(label, pts, mx, note):
        drivers.append({"label": label, "pts": round(pts, 1), "max": mx, "note": note})

    cap100 = mcap * 100
    room = (25 if mcap <= 5e6 else 21 if mcap <= 2e7 else 17 if mcap <= 5e7 else 11 if mcap <= 1.5e8
            else 6 if mcap <= 3e8 else 2 if mcap <= 1e9 else 0)
    feas = ("100x plausible" if cap100 <= 5e9 else "100x is a stretch" if cap100 <= 3e10
            else "10x possible, 100x unlikely" if mcap * 10 <= 3e10 else "limited room")
    add("Room to run", room, 25, f"Market cap {fmt_usd(mcap)}; 100x would mean {fmt_usd(cap100)}")

    interest = clamp(t / 0.3, 0, 1) * 12 + (4 if vol >= 1e6 else 2 if vol >= 2.5e5 else 0)
    if a.get("vol_ratio"):
        interest += clamp((a["vol_ratio"] - 1) / 3, 0, 1) * 4
    add("Buying interest", interest, 20, f"Turnover {t * 100:.1f}%, volume {fmt_usd(vol)}")

    if liq is not None:
        trad = 15 if liq >= 1e6 else 11 if liq >= 2.5e5 else 7 if liq >= 1e5 else 4 if liq >= 5e4 else 1
        tnote = f"Liquidity {fmt_usd(liq)} on {dex.get('chain', 'dex')}"
    else:
        trad = 15 if vol >= 2e6 else 11 if vol >= 5e5 else 7 if vol >= 1.5e5 else 3
        tnote = f"Listed venues, volume {fmt_usd(vol)}"
    if (prof.get("tier1_listings") or 0) >= 1:
        trad = min(15, trad + 3)
        tnote += f", {prof['tier1_listings']} major exchanges"
    add("Tradability", trad, 15, tnote)

    strong = sum(1 for n in a["news"] if n["adoption"] and n["strength"] >= ALERT_NEWS_MIN_STRENGTH)
    other = max(0, a["adoption_hits"] - strong)
    cat = min(15, 8 * strong + 4 * other + 2 * min(a["news_hits"], 3))
    add("Catalyst", cat, 15, f"{strong} strong, {other} other adoption headlines, {a['news_hits']} mentions")

    rng, dd = a["range_7d_pct"], a["ath_change_pct"]
    base = (5 if rng is not None and rng <= 12 else 2 if rng is not None and rng <= 25 else 0)
    base += 5 if dd is not None and dd <= -80 else 3 if dd is not None and dd <= -60 else 0
    add("Base and discount", base, 10, f"7d range {'n/a' if rng is None else f'{rng:.0f}%'}, {'n/a' if dd is None else f'{dd:.0f}%'} from ATH")

    ign = clamp(c24, 0, 40) / 40 * 6 + clamp(c1, 0, 8) / 8 * 4
    if t < MOMENTUM_ELEVATED:
        ign *= 0.4
    add("Breakout momentum", ign, 10, f"1h {c1:+.1f}%, 24h {c24:+.1f}%")

    fr = a.get("fdv_ratio")
    sup = 2 if fr is None else 5 if fr <= 1.5 else 3 if fr <= 3 else 0
    add("Supply sanity", sup, 5, "FDV n/a" if fr is None else f"FDV is {fr:.1f}x market cap")

    util = (a.get("utility") or {}).get("score", 0)
    util_pts = util * 0.15
    add("Real use case", util_pts, 15, f"{(a.get('utility') or {}).get('label', 'n/a')} (utility {util}/100)")

    # ---- risk grading ----
    pts, why = 0, []

    def risk(p, msg):
        nonlocal pts
        pts += p
        why.append(msg)

    age_days = None
    if dex:
        if liq is not None:
            if liq < 5e4:
                risk(3, f"Thin liquidity ({fmt_usd(liq)}): hard to exit")
            elif liq < 1.5e5:
                risk(2, f"Low liquidity ({fmt_usd(liq)})")
            elif liq < 5e5:
                risk(1, f"Modest liquidity ({fmt_usd(liq)})")
        created = parse_date(dex.get("pair_created_at"))
        if created:
            age_days = max(0, (now - created).days)
            if age_days < 7:
                risk(3, f"Trading pair is only {age_days} days old")
            elif age_days < 30:
                risk(2, f"Trading pair is under a month old ({age_days} days)")
            elif age_days < 90:
                risk(1, f"Trading pair is under 3 months old")
        risk(1, "Trades only on decentralized exchanges")
        buys, sells = dex.get("buys_24h") or 0, dex.get("sells_24h")
        if buys >= 20 and sells == 0:
            risk(3, "Buys but zero sells in 24h (possible honeypot)")
        if liq and vol / liq > 30:
            risk(1, "Volume is 30x+ liquidity (possible wash trading)")
        if not sec:
            risk(1, "No automated security scan available: check it yourself before buying")
    if t > 3:
        risk(1, "Daily volume is over 3x market cap")
    if c24 >= 300:
        risk(2, "Already up 300%+ today")
    if sec:
        for msg in sec.get("block") or []:
            risk(10, "Security scan: " + msg)
        for msg in (sec.get("caution") or [])[:4]:
            risk(1, msg)
        if sec.get("holders") is not None and sec["holders"] < 100:
            risk(2, f"Only {sec['holders']} holders")
        if (sec.get("top10_pct") or 0) > 60:
            risk(1, f"Top 10 wallets hold {sec['top10_pct']}% of supply (includes pools)")
        if sec.get("lp_locked_pct") is not None and sec["lp_locked_pct"] < 50:
            risk(1, f"Only {sec['lp_locked_pct']}% of liquidity is locked")
    if (prof.get("tier1_listings") or 0) >= 1:
        pts -= 2
        why.append("Listed on major exchanges (lowers risk)")
    if mcap >= 2e7:
        pts -= 1
    gd = parse_date(prof.get("genesis_date"))
    if gd and (now - gd).days > 365:
        pts -= 1
    level = "EXTREME" if pts >= 7 else "HIGH" if pts >= 4 else "MEDIUM" if pts >= 2 else "LOW"

    score = (trad + room + interest + cat + base + ign + sup + util_pts) / 115 * 100
    score -= {"EXTREME": 25, "HIGH": 12, "MEDIUM": 4, "LOW": 0}[level]
    a["hunt"] = {
        "zeros": zeros, "target_10x": price * 10, "target_100x": price * 100,
        "cap_10x": mcap * 10, "cap_100x": cap100, "feasibility": feas,
        "score": round(clamp(score, 0, 100), 1), "risk": level, "risk_reasons": why[:8],
        "drivers": drivers, "liquidity_usd": liq, "age_days": age_days,
    }


def ecosystem_backing_ok(a):
    if a["watchlist"]:
        return True
    if a["market_cap"] < ECOSYSTEM_MIN_MCAP:
        return False
    return (a["turnover_ratio"] >= ECOSYSTEM_MIN_TURNOVER
            or a["adoption_hits"] >= ECOSYSTEM_MIN_ADOPTION_HITS
            or (a["adoption_hits"] >= 1 and a["turnover_ratio"] >= ECOSYSTEM_COMBO_TURNOVER))


# --------------------------------------------------------------------------- #
# Alerts + email
# --------------------------------------------------------------------------- #

def dashboard_url():
    url = os.environ.get("DASHBOARD_URL", "").strip()
    if url:
        return url if url.endswith("/") else url + "/"
    repo = os.environ.get("GITHUB_REPOSITORY", "")
    if "/" in repo:
        owner, name = repo.split("/", 1)
        return f"https://{owner.lower()}.github.io/{name}/"
    return ""


def news_key(asset_id, title):
    norm = re.sub(r"[^a-z0-9]+", " ", title.lower()).strip()
    return hashlib.sha1(f"{asset_id}|{norm}".encode()).hexdigest()[:16]


def evaluate_alerts(assets, state, now):
    alerts = []
    seen = state.setdefault("sent_news", {})
    last = state.setdefault("last_alert", {})

    def cooled(key, hours):
        t = parse_date(last.get(key))
        return t is None or now - t > timedelta(hours=hours)

    for a in assets:
        for n in a["news"]:
            if not n["adoption"] or n["strength"] < ALERT_NEWS_MIN_STRENGTH:
                continue
            pub = parse_date(n["published"])
            if not pub or now - pub > timedelta(hours=ALERT_NEWS_MAX_AGE_H):
                continue
            key = news_key(a["id"], n["title"])
            if key in seen:
                continue
            alerts.append({
                "kind": "news", "type": "news", "key": key, "asset": a,
                "severity": "MAJOR" if n["strength"] >= ALERT_NEWS_MAJOR_STRENGTH else "NOTABLE",
                "news": n, "why": [("Major-exchange listing headline" if "LISTING" in (n.get("tags") or [])
                                    else "Institutional adoption headline") + f" (strength {n['strength']:.1f})",
                                   "Listing pumps are usually front-loaded: check price before chasing"
                                   if "LISTING" in (n.get("tags") or []) else "Verify the source before acting"],
                "priority": 100 + n["strength"] * 10 + a["setup_score"] / 10,
            })

        h = a.get("hunt")
        if (a["market_cap"] < (300_000 if h else ALERT_MARKET_MIN_MCAP)
                or a["volume_24h"] < (100_000 if h else ALERT_MARKET_MIN_VOLUME)):
            continue
        c24, c1, t, vr = a["change_24h"] or 0.0, a["change_1h"] or 0.0, a["turnover_ratio"], a.get("vol_ratio")
        market = []
        if vr and vr >= 3 and t >= 0.10 and abs(c24) < 8:
            market.append(("accumulation", 48, "Stealth accumulation",
                           [f"24h volume is {vr:.1f}x its baseline while price moved only {c24:+.1f}%",
                            f"Turnover {t * 100:.1f}% of market cap"]))
        if (c24 >= 15 and t >= 0.20) or (c1 >= 8 and t >= 0.15):
            market.append(("ignition", 12, "Breakout ignition",
                           [f"Price {c1:+.1f}% (1h) and {c24:+.1f}% (24h) on {t * 100:.1f}% turnover"]))
        if a["setup_score"] >= SETUP_ALERT_SCORE and a["stage"] in ("Dormant base", "Accumulating", "Ignition"):
            market.append(("setup", 48, "High-conviction setup",
                           [f"Setup score {a['setup_score']:.0f}/100, stage: {a['stage']}"]
                           + [f"{d['label']}: {d['note']}" for d in a["drivers"] if d["pts"] >= 0.5 * d["max"] > 0][:3]))
        if h and h["score"] >= HUNT_ALERT_SCORE and h["risk"] in ("LOW", "MEDIUM"):
            market.append(("zerohunt", 72, "Zero-cancel candidate",
                           [f"Hunt score {h['score']:.0f}/100, {h['zeros']} zeros, risk {h['risk']}",
                            f"100x would be {fmt_price(h['target_100x'])} ({h['feasibility']})"]
                           + [f"{d['label']}: {d['note']}" for d in h["drivers"] if d["pts"] >= 0.6 * d["max"] > 0][:2]
                           + ([f"History match {a['history']['match']['score']}%: looks like {a['history']['match']['analog']} before its run"]
                              if (a.get("history") or {}).get("match") and a["history"]["match"]["score"] >= 75 else [])))
        if h and h["risk"] in ("LOW", "MEDIUM") and c24 >= 30 and t >= 0.3:
            market.append(("zeroignite", 12, "Micro-cap ignition",
                           [f"Up {c24:+.1f}% in 24h on {t * 100:.1f}% turnover, risk {h['risk']}"]))
        for typ, cool_h, label, why in market:
            ck = f"{a['id']}:{typ}"
            if cooled(ck, cool_h):
                alerts.append({
                    "kind": "market", "type": typ, "key": ck, "asset": a, "severity": "WATCH",
                    "label": label, "why": why, "news": None,
                    "priority": 50 + a["setup_score"] + (10 if typ == "ignition" else 0),
                })
    alerts.sort(key=lambda x: x["priority"], reverse=True)
    return alerts[:ALERT_MAX_PER_EMAIL]


def build_email(alerts, armed=False):
    base = dashboard_url()
    majors = sum(1 for x in alerts if x["severity"] == "MAJOR")
    syms = ", ".join(dict.fromkeys(x["asset"]["symbol"] for x in alerts))[:80]
    if armed:
        subject = f"[Crypto Intel] Alerts armed ({len(alerts)} current flags)"
    else:
        subject = f"[Crypto Intel] {majors} major, {len(alerts) - majors} other: {syms}"

    intro = ("Alerts are now armed. These conditions already existed, so you will only be emailed about NEW events from here on."
             if armed else "New signals from your terminal:")
    text_parts, html_parts = [intro, ""], [f"<p style='margin:0 0 14px'>{html.escape(intro)}</p>"]
    for x in alerts:
        a, n = x["asset"], x["news"]
        title = (n["title"] if n else x.get("label", x["type"]))
        link = f"{base}#coin={a['id']}" if base else ""
        meta = (f"{fmt_price(a['price'])} | 24h {fmt_pct(a['change_24h'])} | mcap {fmt_usd(a['market_cap'])} | "
                f"turnover {a['turnover_ratio'] * 100:.1f}% | stage {a['stage']} | setup {a['setup_score']:.0f}/100 | "
                f"{a['use_case_label']}")
        u = a.get("utility")
        if u:
            meta += f" | use case: {u['label']} ({u['domain']})"
        h = a.get("hunt")
        if h:
            meta += (f" | {h['zeros']} zeros, 10x {fmt_price(h['target_10x'])}, 100x {fmt_price(h['target_100x'])}, "
                     f"hunt {h['score']:.0f}/100, RISK {h['risk']}")
        text_parts += [f"[{x['severity']}] {a['name']} ({a['symbol']}): {title}", f"  {meta}"]
        text_parts += [f"  - {w}" for w in x["why"]]
        if n:
            text_parts.append(f"  Source: {n['source']} - {n['url']}")
        if link:
            text_parts.append(f"  Dashboard: {link}")
        text_parts.append("")

        color = {"MAJOR": "#e11d48", "NOTABLE": "#d97706", "WATCH": "#0891b2"}.get(x["severity"], "#475569")
        html_parts.append(
            f"<div style='border:1px solid #cbd5e1;border-left:4px solid {color};border-radius:6px;padding:12px;margin:0 0 12px'>"
            f"<div style='font-size:12px;font-weight:700;color:{color}'>{x['severity']}</div>"
            f"<div style='font-size:16px;font-weight:700;margin:2px 0'>{html.escape(a['name'])} ({html.escape(a['symbol'])})</div>"
            f"<div style='font-size:14px;margin:2px 0 6px'>{html.escape(title)}</div>"
            f"<div style='font-size:12px;color:#475569'>{html.escape(meta)}</div>"
            + "".join(f"<div style='font-size:13px;margin-top:4px'>&bull; {html.escape(w)}</div>" for w in x["why"])
            + (f"<div style='margin-top:8px'><a href='{html.escape(n['url'])}' style='color:#0369a1'>VERIFY SOURCE WIRE ({html.escape(n['source'])})</a></div>" if n else "")
            + (f"<div style='margin-top:4px'><a href='{html.escape(link)}' style='color:#0369a1'>Open coin in dashboard</a></div>" if link else "")
            + "</div>")
    foot = ("Automated screen of public data; headline matching can be wrong. Verify the source and do your own research. "
            "Not financial advice.")
    text_parts.append(foot)
    html_parts.append(f"<p style='font-size:12px;color:#64748b'>{foot}</p>")
    body_html = ("<div style='font-family:-apple-system,Segoe UI,Roboto,Arial,sans-serif;max-width:640px'>"
                 + "".join(html_parts) + "</div>")
    return subject, "\n".join(text_parts), body_html


def email_configured():
    return bool(os.environ.get("SMTP_USER") and os.environ.get("SMTP_APP_PASSWORD"))


def send_email(subject, text, body_html):
    user = os.environ.get("SMTP_USER", "").strip()
    pw = os.environ.get("SMTP_APP_PASSWORD", "").replace(" ", "")
    to = os.environ.get("ALERT_EMAIL_TO", "").strip() or user
    if not user or not pw:
        log("[email] SMTP_USER / SMTP_APP_PASSWORD not set; email skipped")
        return False
    msg = EmailMessage()
    msg["Subject"], msg["From"], msg["To"] = subject, user, to
    msg.set_content(text)
    msg.add_alternative(body_html, subtype="html")
    try:
        with smtplib.SMTP_SSL("smtp.gmail.com", 465, context=ssl.create_default_context(), timeout=30) as s:
            s.login(user, pw)
            s.send_message(msg)
        log(f"[email] sent: {subject}")
        return True
    except Exception as exc:
        log(f"[email] FAILED: {exc}")
        return False


def run_alerts(assets, state, now):
    """Evaluate, email, and record alert state. Returns number of alerts emailed."""
    if not email_configured():
        log("[alerts] email not configured; alert engine idle (set SMTP_USER and SMTP_APP_PASSWORD)")
        return 0
    armed = not state.get("initialized")
    alerts = evaluate_alerts(assets, state, now)
    log(f"[alerts] {len(alerts)} candidate alerts (first run: {armed})")
    if not alerts and not armed:
        return 0
    if armed and not alerts:
        subject, text, body = (
            "[Crypto Intel] Alerts armed",
            "Alerts are armed. You will be emailed when institutional adoption news or unusual volume appears.",
            "<p>Alerts are armed. You will be emailed when institutional adoption news or unusual volume appears.</p>")
    else:
        subject, text, body = build_email(alerts, armed=armed)
    if not send_email(subject, text, body):
        return 0  # leave state untouched so the same alerts retry next run

    iso = now.isoformat()
    for x in alerts:
        if x["kind"] == "news":
            state["sent_news"][x["key"]] = iso
        else:
            state["last_alert"][x["key"]] = iso
        state.setdefault("history", []).append({
            "t": iso, "kind": x["kind"], "id": x["asset"]["id"], "symbol": x["asset"]["symbol"],
            "name": x["asset"]["name"], "severity": x["severity"],
            "title": (x["news"]["title"] if x["news"] else x.get("label", x["type"])),
            "url": (x["news"]["url"] if x["news"] else ""),
        })
    state["initialized"] = True
    return len(alerts)


def prune_state(state, now, touch=False):
    cut = now - timedelta(days=14)
    state["sent_news"] = {k: v for k, v in state.get("sent_news", {}).items()
                          if (parse_date(v) or now) > cut}
    cut2 = now - timedelta(days=7)
    state["last_alert"] = {k: v for k, v in state.get("last_alert", {}).items()
                           if (parse_date(v) or now) > cut2}
    state["history"] = state.get("history", [])[-60:]
    if touch:
        state["updated"] = now.isoformat()


# --------------------------------------------------------------------------- #
# Pipeline
# --------------------------------------------------------------------------- #

def pipeline(mode):
    now = datetime.now(timezone.utc)
    headers = cg_headers()
    prev = load_json(DATA_FILE, {})
    prev_by_id = {a["id"]: a for a in prev.get("assets", []) if isinstance(a, dict) and a.get("id")}
    state = load_json(STATE_FILE, {})
    log(f"== Crypto Intelligence Terminal: mode={mode} ==")

    # ---- 1. universe: CoinGecko (deep), trending, categories, DEX discovery --------------
    rows = fetch_markets(headers, pages=CG_PAGES if mode == "full" else min(CG_PAGES, 5))
    if not rows:
        log("FATAL: no market data returned (CoinGecko unreachable or rate limited).")
        return 1
    if mode == "full":
        for k, v in fetch_markets(headers, pages=CG_VOLUME_PAGES, order="volume_desc").items():
            rows.setdefault(k, v)
        need = [i for i in fetch_trending_ids(headers) if i not in rows]
        if need:
            rows.update(fetch_by_ids(need, headers))
        cat_members = fetch_category_rows(headers, rows)
    else:
        cat_members = {i: set(a.get("category_ids") or []) for i, a in prev_by_id.items()}
        missing = [i for i in prev_by_id if i not in rows and not i.startswith("dex-")]
        if missing:
            rows.update(fetch_by_ids(missing, headers))
    missing_watch = [i for i in WATCHLIST if i not in rows]
    if missing_watch:
        rows.update(fetch_by_ids(missing_watch, headers))
    cg_count = len(rows)
    rows.update(discover_dex(prev_by_id))
    log(f"[markets] {cg_count} CoinGecko coins + {len(rows) - cg_count} DEX tokens in pool")

    assets = []
    for cid, coin in rows.items():
        a = build_asset(coin, watch=cid in WATCHLIST)
        if not a:
            continue
        old = prev_by_id.get(cid) or {}
        a["category_ids"] = sorted(cat_members.get(cid, set()))
        a["profile"], a["profile_fetched_at"] = old.get("profile"), old.get("profile_fetched_at")
        a["security"], a["security_checked_at"] = old.get("security"), old.get("security_checked_at")
        a["history"] = old.get("history")
        a["site_summary"] = old.get("site_summary")
        pcats = (a["profile"] or {}).get("categories")
        a["use_case"] = assign_use_case(cid, a["name"], a["category_ids"], pcats)
        a["use_case_label"], a["use_case_rank"] = UC_LABEL[a["use_case"]], UC_RANK[a["use_case"]]
        assets.append(a)
    log(f"[filter] {len(assets)} assets pass the filters (price under ${MAX_PRICE_USD:g}, no market-cap ceiling)")

    # ---- 2. news ----------------------------------------------------------------------------
    news, feed_status = fetch_news([f"{a['name']} crypto" for a in assets if a["watchlist"]])
    log(f"[news] {len(news)} unique headlines")
    wire = intersect_news(assets, news)

    # ---- 3. volume baseline + scoring --------------------------------------------------------
    ema = state.setdefault("vol_ema", {})
    for a in assets:
        base = ema.get(a["id"])
        a["vol_ratio"] = round(a["volume_24h"] / base, 2) if base and base > 0 else None
        if mode == "full":
            ema[a["id"]] = a["volume_24h"] if not base else 0.8 * base + 0.2 * a["volume_24h"]
    for a in assets:
        score_asset(a)

    hidden = {"unsafe": 0, "pending": 0}

    def finalize():
        keep = []
        hidden["unsafe"] = hidden["pending"] = 0
        for a in assets:
            analyse_launch(a, now)
            sec = a.get("security")
            if sec and "verdict" not in sec:
                sec["verdict"], sec["block"], sec["caution"] = security_verdict(sec)
            if sec and sec.get("verdict") == "fail" and not a["watchlist"]:
                hidden["unsafe"] += 1              # honeypot / unsellable / punishing tax: never shown
                continue
            a["pending_scan"] = bool(a["venue"] == "dex" and not sec)
            if a["pending_scan"] and not a["watchlist"]:
                hidden["pending"] += 1             # DEX tokens are hidden until a scan has passed
                continue
            h = a.get("hunt")
            if h and h["risk"] == "EXTREME" and not a["watchlist"]:
                continue                         # clear rug/honeypot signals: never shown
            if a["watchlist"] or (h and h["score"] >= HUNT_MIN_KEEP):
                a["backing_strong"] = True
                keep.append(a)
                continue
            a["backing_strong"] = ecosystem_backing_ok(a) if a["tier"] == "ecosystem" else True
            if a["backing_strong"]:
                keep.append(a)
        hunts = sorted((a for a in keep if a.get("hunt")), key=lambda a: -a["hunt"]["score"])
        others = sorted((a for a in keep if not a.get("hunt")), key=lambda a: -a["setup_score"])
        chosen = {a["id"]: a for a in hunts[:MAX_HUNT] + others[:MAX_NON_HUNT] + [a for a in keep if a["watchlist"]]}
        out = list(chosen.values())
        out.sort(key=lambda x: (x["use_case_rank"], -x["setup_score"]))
        return out

    def write_data(final):
        uc_counts = {k: 0 for k, _ in USE_CASES}
        for a in final:
            uc_counts[a["use_case"]] += 1
        hunts = [a for a in final if a.get("hunt") and a["hunt"]["score"] >= HUNT_MIN_KEEP]
        payload = {
            "generated_at": now.isoformat(),
            "parameters": {
                "min_market_cap": MIN_MARKET_CAP, "min_volume_24h": MIN_VOLUME_24H,
                "max_market_cap": None, "max_price_usd": MAX_PRICE_USD, "banned_top10": BAN_TOP10,
                "scarce_max": SCARCE_MAX, "fdv_warn_ratio": FDV_WARN_RATIO,
                "fdv_critical_ratio": FDV_CRITICAL_RATIO, "news_window_days": NEWS_MAX_AGE_DAYS,
                "alert_news_min_strength": ALERT_NEWS_MIN_STRENGTH, "hunt_min_zeros": HUNT_MIN_ZEROS,
                "hunt_min_keep": HUNT_MIN_KEEP,
            },
            "use_cases": [{"key": k, "label": l, "rank": UC_RANK[k], "count": uc_counts[k]} for k, l in USE_CASES],
            "stats": {
                "assets": len(final),
                "scarce": sum(1 for a in final if a["tier"] == "scarce"),
                "ecosystem": sum(1 for a in final if a["tier"] == "ecosystem"),
                "high_momentum": sum(1 for a in final if a["momentum"] == "HIGH"),
                "dilution_alerts": sum(1 for a in final if a["dilution_alert"] in ("WARNING", "CRITICAL")),
                "with_adoption_news": sum(1 for a in final if a["adoption_hits"] > 0),
                "early_setups": sum(1 for a in final if a["stage"] in ("Dormant base", "Accumulating")),
                "hunt_candidates": len(hunts),
                "overlooked": sum(1 for a in final if a.get("overlooked")),
                "meme_with_use_case": sum(1 for a in final if a.get("meme_utility")),
                "hunt_low_medium_risk": sum(1 for a in hunts if a["hunt"]["risk"] in ("LOW", "MEDIUM")),
                "dex_tokens": sum(1 for a in final if a["venue"] == "dex"),
                "hidden_unsafe": hidden["unsafe"], "hidden_pending_scan": hidden["pending"],
                "headlines_scanned": len(news), "adoption_headlines": len(wire),
            },
            "feeds": feed_status,
            "adoption_wire": wire,
            "alert_log": list(reversed(state.get("history", [])))[:40],
            "assets": final,
        }
        save_json(DATA_FILE, payload)
        log(f"[done] wrote {DATA_FILE}: {payload['stats']}")

    update_history(assets, headers, now, fetch=False)     # re-match cached fingerprints (cheap)
    final = finalize()
    if mode == "full":
        write_data(final)          # write immediately so slow enrichment can never lose the data
        enrich_profiles(assets, headers, now)
        enrich_site_summaries(assets, now)
        scan_security_batch(assets, now)
        for a in assets:     # fresh profiles carry real categories: re-classify the use case
            a["use_case"] = assign_use_case(a["id"], a["name"], a["category_ids"],
                                            (a["profile"] or {}).get("categories"))
            a["use_case_label"], a["use_case_rank"] = UC_LABEL[a["use_case"]], UC_RANK[a["use_case"]]
        for a in assets:
            score_asset(a)
        update_history(assets, headers, now, fetch=True)
        final = finalize()
        write_data(final)
        ids = {a["id"] for a in final}
        state["vol_ema"] = {k: v for k, v in ema.items() if k in ids}   # keep the state file small

    sent = run_alerts(final, state, now)
    prune_state(state, now, touch=(mode == "full" or sent > 0))
    save_json(STATE_FILE, state, indent=1)
    log(f"== finished: {sent} alert(s) emailed ==")
    return 0


# --------------------------------------------------------------------------- #
# Spike Lab: what did the market look like BEFORE past runs?
# --------------------------------------------------------------------------- #

def fetch_binance_history(symbol):
    start = int(datetime(2017, 8, 1, tzinfo=timezone.utc).timestamp() * 1000)
    out, cur = [], start
    for _ in range(8):
        data = http_get(BINANCE_KLINES, params={"symbol": symbol, "interval": "1d",
                                                "startTime": cur, "limit": 1000}, retries=2).json()
        if not isinstance(data, list) or not data:
            break
        out.extend(data)
        if len(data) < 1000:
            break
        cur = int(data[-1][0]) + 86_400_000
    return [{"t": int(k[0]), "o": float(k[1]), "h": float(k[2]), "l": float(k[3]),
             "c": float(k[4]), "qv": float(k[7])} for k in out]


def fetch_cg_history(cg_id, headers):
    d = http_get(f"{CG_BASE}/coins/{cg_id}/market_chart",
                 params={"vs_currency": "usd", "days": 365, "interval": "daily"},
                 headers=headers, retries=3).json()
    prices, vols = d.get("prices") or [], d.get("total_volumes") or []
    out = []
    for i, p in enumerate(prices):
        if p[1] is None:
            continue
        v = vols[i][1] if i < len(vols) and vols[i][1] is not None else 0.0
        out.append({"t": int(p[0]), "o": p[1], "h": p[1], "l": p[1], "c": p[1], "qv": float(v)})
    return out


def resolve_cg_id(query, headers):
    d = http_get(f"{CG_BASE}/search", params={"query": query}, headers=headers, retries=2).json()
    coins = d.get("coins") or []
    return coins[0]["id"] if coins else None


def mean(xs):
    xs = list(xs)
    return sum(xs) / len(xs) if xs else 0.0


def fingerprint(c, i):
    if i < 70:
        return None
    win = c[i - 30:i + 1]
    hi, lo = max(x["h"] for x in win), min(x["l"] for x in win)
    v7, v60 = mean(x["qv"] for x in c[i - 6:i + 1]), mean(x["qv"] for x in c[i - 66:i - 6])
    ath = max(x["h"] for x in c[:i + 1])
    rets = [math.log(c[k]["c"] / c[k - 1]["c"]) for k in range(i - 29, i + 1)
            if c[k - 1]["c"] > 0 and c[k]["c"] > 0]
    return {
        "range_30d_pct": (hi / lo - 1) * 100 if lo > 0 else None,
        "vol_exp": v7 / v60 if v60 > 0 else None,
        "drawdown_pct": (c[i]["c"] / ath - 1) * 100 if ath > 0 else None,
        "volatility": statistics.pstdev(rets) if len(rets) > 5 else None,
        "ret_30d_pct": (c[i]["c"] / c[i - 30]["c"] - 1) * 100 if c[i - 30]["c"] > 0 else None,
        "breakout_20d": c[i]["c"] > max(x["h"] for x in c[i - 20:i]),
    }


CONDITIONS = [
    ("tight_base", "Tight 30-day base (range under 35%)",
     lambda f: f["range_30d_pct"] is not None and f["range_30d_pct"] <= 35),
    ("volume_building", "Volume building (7-day average 1.3x+ the prior 60 days)",
     lambda f: f["vol_exp"] is not None and f["vol_exp"] >= 1.3),
    ("beaten_down", "Beaten down (50%+ below its prior high)",
     lambda f: f["drawdown_pct"] is not None and f["drawdown_pct"] <= -50),
    ("calm_volatility", "Calm volatility (typical daily move under 4%)",
     lambda f: f["volatility"] is not None and f["volatility"] < 0.04),
    ("flat_prior_month", "Flat prior month (-15% to +15%)",
     lambda f: f["ret_30d_pct"] is not None and -15 <= f["ret_30d_pct"] <= 15),
]


def day(t):
    return datetime.fromtimestamp(t / 1000, timezone.utc).strftime("%Y-%m-%d")


def find_spike(c, t0, t1, min_gain=40.0):
    best = None
    for i in range(70, len(c) - 5):
        t = c[i]["t"]
        if t < t0 or (t1 and t > t1):
            continue
        fwd = c[i + 1:i + 31]
        pk = max(fwd, key=lambda x: x["h"])
        gain = (pk["h"] / c[i]["c"] - 1) * 100 if c[i]["c"] > 0 else 0
        if gain >= min_gain and (best is None or gain > best[0]):
            best = (gain, i, pk)
    return best


def analyse_case(case, candles):
    t0 = int(parse_date(case["from"]).timestamp() * 1000)
    t1 = int(parse_date(case["to"]).timestamp() * 1000) if case.get("to") else None
    spike = find_spike(candles, t0, t1)
    if not spike:
        return {"label": case["label"], "spike": None,
                "note": "No run of +40% within 30 days was found in this window."}, None
    gain, i, pk = spike
    base = candles[i]
    ign = None
    for j in range(i + 1, min(i + 31, len(candles))):
        move = (candles[j]["c"] / candles[j - 1]["c"] - 1) * 100
        prior_v = mean(x["qv"] for x in candles[max(0, j - 20):j])
        vmult = candles[j]["qv"] / prior_v if prior_v > 0 else None
        if move >= 6 or (vmult and vmult >= 2 and move >= 3):
            ign = {"date": day(candles[j]["t"]), "day_move_pct": round(move, 1),
                   "volume_multiple": round(vmult, 1) if vmult else None,
                   "days_after_base": j - i, "close": candles[j]["c"]}
            span = pk["h"] - base["c"]
            ign["move_left_pct"] = round((pk["h"] - candles[j]["c"]) / span * 100, 0) if span > 0 else None
            break
    fp = fingerprint(candles, i)
    flags = {k: bool(fn(fp)) for k, _, fn in CONDITIONS} if fp else {}
    return {
        "label": case["label"], "kind": case.get("kind"),
        "spike": {
            "base_date": day(base["t"]), "base_price": base["c"],
            "peak_date": day(pk["t"]), "peak_price": pk["h"],
            "gain_pct": round(gain, 0), "days_to_peak": int((pk["t"] - base["t"]) / 86_400_000),
            "ignition": ign, "fingerprint": fp, "flags": flags,
        },
    }, fp


def spikelab():
    headers = cg_headers()
    cases_out, fps, base_hits, base_days = [], [], {k: 0 for k, _, _ in CONDITIONS}, 0
    for case in SPIKE_CASES:
        candles, source = [], None
        try:
            if case.get("binance"):
                candles, source = fetch_binance_history(case["binance"]), "Binance daily candles"
        except Exception as exc:
            log(f"[spike] {case['label']}: binance failed ({exc})")
        if len(candles) < 120:
            try:
                cg_id = case.get("cg") or resolve_cg_id(case.get("cg_search", ""), headers)
                if cg_id:
                    candles, source = fetch_cg_history(cg_id, headers), f"CoinGecko daily ({cg_id}), 365-day limit"
                time.sleep(CG_DELAY)
            except Exception as exc:
                log(f"[spike] {case['label']}: coingecko failed ({exc})")
        if len(candles) < 120:
            cases_out.append({"label": case["label"], "spike": None,
                              "note": "Not enough price history could be fetched for this coin."})
            continue
        res, fp = analyse_case(case, candles)
        res["source"] = source
        cases_out.append(res)
        if fp:
            fps.append(res["spike"]["flags"])
        for i in range(70, len(candles)):
            f = fingerprint(candles, i)
            if f:
                base_days += 1
                for k, _, fn in CONDITIONS:
                    base_hits[k] += 1 if fn(f) else 0
        log(f"[spike] {case['label']}: {'spike found' if res['spike'] else 'no spike'}")

    n = len(fps)
    summary = []
    for k, label, _ in CONDITIONS:
        hit = sum(1 for f in fps if f.get(k))
        base_rate = (base_hits[k] / base_days * 100) if base_days else None
        lift = ((hit / n * 100) / base_rate) if n and base_rate else None
        summary.append({"key": k, "label": label, "spikes_hit": hit, "spikes_total": n,
                        "base_rate_pct": round(base_rate, 1) if base_rate is not None else None,
                        "lift": round(lift, 2) if lift is not None else None})
    lefts = [c["spike"]["ignition"]["move_left_pct"] for c in cases_out
             if c.get("spike") and c["spike"].get("ignition") and c["spike"]["ignition"].get("move_left_pct") is not None]
    out = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "cases": cases_out, "conditions": summary,
        "median_move_left_after_ignition_pct": round(statistics.median(lefts), 0) if lefts else None,
        "notes": [
            "Sample is tiny and hand-picked (survivorship bias): treat lift as a hint, not a forecast.",
            "'Base rate' is how often the same condition appeared on ordinary days for the same coins.",
            "A condition only matters if spikes show it far more often than ordinary days (lift well above 1).",
        ],
    }
    save_json(SPIKE_FILE, out, indent=1)
    log(f"[done] wrote {SPIKE_FILE}")
    return 0


# --------------------------------------------------------------------------- #
# Entry point
# --------------------------------------------------------------------------- #

# --------------------------------------------------------------------------- #
# History match: does this coin look like past coins did BEFORE they ran?
# --------------------------------------------------------------------------- #

HISTORY_MAX_PER_RUN = 25
HISTORY_REFRESH_DAYS = 3
GT_NET_BY_CHAIN = {chain: net for net, chain in GT_NETWORKS}


def load_library():
    lab = load_json(SPIKE_FILE, {})
    lib = []
    for c in lab.get("cases") or []:
        sp = c.get("spike")
        if sp and sp.get("fingerprint"):
            lib.append({"label": c["label"], "kind": c.get("kind"), "gain_pct": sp.get("gain_pct"),
                        "fp": sp["fingerprint"]})
    return lib, lab.get("conditions") or []


def fetch_dex_history(a):
    d = a.get("dex") or {}
    net, pair = GT_NET_BY_CHAIN.get(d.get("chain")), d.get("pair")
    if not net or not pair:
        return []
    r = http_get(f"{GT_BASE}/networks/{net}/pools/{pair}/ohlcv/day",
                 params={"aggregate": 1, "limit": 150, "currency": "usd"},
                 headers={"Accept": "application/json;version=20230302"}, retries=2).json()
    lst = (((r.get("data") or {}).get("attributes") or {}).get("ohlcv_list")) or []
    out = [{"t": int(x[0]) * 1000, "o": float(x[1]), "h": float(x[2]), "l": float(x[3]),
            "c": float(x[4]), "qv": float(x[5] or 0)} for x in lst if len(x) >= 6]
    out.sort(key=lambda c: c["t"])
    return out


def match_history(fp, library, conditions):
    """Similarity (0-100) of a live fingerprint to the pre-spike fingerprints of past runs."""
    def feat(f):
        return {
            "range": math.log10(1 + max(f.get("range_30d_pct") or 0, 0) / 100),
            "vol": math.log2(max(f.get("vol_exp") or 1e-6, 1e-6)),
            "dd": (f.get("drawdown_pct") or 0) / 40,
            "volat": (f.get("volatility") or 0) / 0.03,
            "ret": (f.get("ret_30d_pct") or 0) / 30,
        }
    tol = {"range": 0.35, "vol": 1.0, "dd": 1.0, "volat": 1.0, "ret": 1.0}
    live = feat(fp)
    best = None
    for case in library:
        past = feat(case["fp"])
        dist = sum(min(1.0, abs(live[k] - past[k]) / tol[k]) for k in tol) / len(tol)
        score = round(100 * (1 - dist))
        if best is None or score > best["score"]:
            best = {"score": score, "analog": case["label"], "kind": case.get("kind"), "analog_gain_pct": case.get("gain_pct")}
    lift = {c["key"]: c.get("lift") for c in conditions}
    met = [{"label": label, "met": bool(fn(fp)), "lift": lift.get(key)} for key, label, fn in CONDITIONS]
    if best:
        best["conditions"] = met
        best["conditions_met"] = sum(1 for m in met if m["met"])
    return best


def update_history(assets, headers, now, fetch=True):
    library, conditions = load_library()
    stale = now - timedelta(days=HISTORY_REFRESH_DAYS)
    if fetch:
        cands = [a for a in assets if a.get("hunt") or a["watchlist"]]
        cands.sort(key=lambda a: -((a.get("hunt") or {}).get("score", 0)))
        todo = [a for a in cands if not a.get("history")
                or (parse_date(a["history"].get("checked_at")) or stale) <= stale][:HISTORY_MAX_PER_RUN]
        for a in todo:
            if time.time() - T0 > ENRICH_BUDGET_S + 120:
                break
            try:
                candles = fetch_dex_history(a) if a["venue"] == "dex" else fetch_cg_history(a["id"], headers)
            except Exception as exc:
                log(f"[history] {a['symbol']}: failed ({exc})")
                candles = []
            fp = fingerprint(candles, len(candles) - 1) if len(candles) >= 72 else None
            a["history"] = {"checked_at": now.isoformat(), "fingerprint": fp, "too_new": fp is None,
                            "days_of_data": len(candles)}
            time.sleep(2.5 if a["venue"] == "dex" else CG_DELAY)
        log(f"[history] fetched daily history for {len(todo)} candidates")
    matched = 0
    for a in assets:
        h = a.get("history") or {}
        if h.get("fingerprint") and library:
            h["match"] = match_history(h["fingerprint"], library, conditions)
            matched += 1
    log(f"[history] matched {matched} assets against {len(library)} past runs")


def test_email():
    a = build_asset({"id": "quant-network", "symbol": "qnt", "name": "Quant", "image": "",
                     "current_price": 98.0, "market_cap": 1.4e9, "total_volume": 2.1e8,
                     "circulating_supply": 14.5e6, "total_supply": 14.6e6, "max_supply": 14.6e6,
                     "fully_diluted_valuation": 1.43e9, "ath": 427, "atl": 0.2,
                     "ath_change_percentage": -77, "price_change_percentage_24h_in_currency": 38.0,
                     "price_change_percentage_1h_in_currency": 6.0, "price_change_percentage_7d_in_currency": 41.0},
                    watch=True)
    a["use_case_label"] = UC_LABEL["institutional"]
    score_asset(a)
    item = {"title": "SAMPLE: The Clearing House selects Quant for tokenized deposit initiative",
            "url": "https://example.com/sample", "source": "Sample Wire", "strength": 6.0}
    alert = {"kind": "news", "type": "news", "key": "sample", "asset": a, "severity": "MAJOR",
             "news": item, "why": ["This is a test email to confirm alerts reach you."], "priority": 1}
    subject, text, body = build_email([alert])
    return 0 if send_email("[TEST] " + subject, text, body) else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", default=os.environ.get("CRYPTO_MODE", "full"),
                    choices=["full", "alerts", "spikelab", "test-email"])
    args = ap.parse_args()
    if args.mode == "spikelab":
        return spikelab()
    if args.mode == "test-email":
        return test_email()
    return pipeline(args.mode)


if __name__ == "__main__":
    sys.exit(main())
