#!/usr/bin/env python3
"""
edge_study.py - What do coins have in common BEFORE a 10-20% move?

Pulls ~90 days of 15-minute candles for the most liquid USDT pairs (Binance public
market-data endpoint, no key needed), then measures, at every 15-minute decision point:

  * which measurable conditions separate "a +10/15/20% move is still ahead within 24h"
    from ordinary moments (AUC: 0.5 = no information, 1.0 = perfect), and
  * whether a simple combined rule would have made money with a +15% target and a stop,
    after fees, tested OUT OF SAMPLE (rules are learned on the first 60% of the time
    range and judged on the last 40%).

Writes edge_study.json. Run it from the GitHub workflow (mode: edgestudy) or locally:
    pip install numpy requests && python edge_study.py

Environment: STUDY_DAYS (default 90), STUDY_TOP_N (default 150), STUDY_FEE (round-trip, default 0.002)
"""

import json
import math
import os
import sys
import time
from datetime import datetime, timezone

import numpy as np
import requests
from numpy.lib.stride_tricks import sliding_window_view

BASE = "https://data-api.binance.vision"
DAYS = int(os.environ.get("STUDY_DAYS", "90"))
TOP_N = int(os.environ.get("STUDY_TOP_N", "150"))
FEE = float(os.environ.get("STUDY_FEE", "0.002"))      # round-trip trading cost assumption
OUT = os.environ.get("STUDY_OUTPUT", "edge_study.json")

CANDLE_MIN = 15
PER_DAY = 24 * 60 // CANDLE_MIN       # 96
H = PER_DAY                           # look-ahead horizon: 24 hours
LB24, LB7D = PER_DAY, 7 * PER_DAY     # 96, 672
WARM = LB7D                           # rows before this lack a full 7-day history
TARGETS = (0.10, 0.15, 0.20)
TP = 0.15
STOPS = (0.05, 0.07, 0.10)
MAIN_STOP = 0.07
TRAIN_FRACTION = 0.6
COOLDOWN = H                          # no new signal on the same coin for 24h

STABLES = {"USDC", "FDUSD", "TUSD", "USDP", "DAI", "USDE", "EUR", "EURI", "AEUR", "BUSD", "PAXG", "XUSD", "USD1"}


def log(m):
    print(m, flush=True)


# --------------------------------------------------------------------------- #
# Data
# --------------------------------------------------------------------------- #

def get(url, params=None, tries=4):
    delay = 3
    for _ in range(tries):
        try:
            r = requests.get(url, params=params, timeout=25)
            if r.status_code in (418, 429):
                time.sleep(delay)
                delay *= 2
                continue
            r.raise_for_status()
            return r.json()
        except requests.RequestException:
            time.sleep(delay)
            delay *= 2
    return None


def universe():
    data = get(f"{BASE}/api/v3/ticker/24hr")
    if not isinstance(data, list):
        return []
    rows = []
    for d in data:
        sym = d.get("symbol", "")
        if not sym.endswith("USDT"):
            continue
        base = sym[:-4]
        if base in STABLES or any(base.endswith(x) for x in ("UP", "DOWN", "BULL", "BEAR")) and len(base) > 4:
            continue
        try:
            rows.append((sym, float(d.get("quoteVolume", 0))))
        except ValueError:
            continue
    rows.sort(key=lambda x: -x[1])
    return [s for s, _ in rows[:TOP_N]]


def klines(sym, start_ms):
    out, cur = [], start_ms
    while True:
        data = get(f"{BASE}/api/v3/klines", {"symbol": sym, "interval": "15m", "startTime": cur, "limit": 1000})
        if not isinstance(data, list) or not data:
            break
        out.extend(data)
        if len(data) < 1000:
            break
        cur = int(data[-1][0]) + CANDLE_MIN * 60 * 1000
        time.sleep(0.05)
    if not out:
        return None
    a = np.array([[float(x[0]), float(x[1]), float(x[2]), float(x[3]), float(x[4]), float(x[5]),
                   float(x[7]), float(x[9])] for x in out])
    return {"t": a[:, 0].astype("int64"), "o": a[:, 1], "h": a[:, 2], "l": a[:, 3], "c": a[:, 4],
            "v": a[:, 5], "qv": a[:, 6], "tb": a[:, 7]}


# --------------------------------------------------------------------------- #
# Features and labels (every feature at row i uses only data up to candle i)
# --------------------------------------------------------------------------- #

FEATURES = [
    ("ret_1h", "Price change, last hour"),
    ("ret_4h", "Price change, last 4 hours"),
    ("ret_24h", "Price change, last 24 hours"),
    ("vol_surge_1", "Volume of the latest 15 min vs the 24h average"),
    ("vol_surge_4", "Volume of the last hour vs the 24h average"),
    ("taker_buy_4", "Share of last hour's volume that was aggressive buying"),
    ("squeeze", "24h range vs its own 7-day average (low = coiled)"),
    ("breakout", "New 24-hour high (1 = yes)"),
    ("near_high", "Distance below the 24-hour high"),
    ("rel_btc_4h", "4h move minus Bitcoin's 4h move"),
    ("btc_24h", "Bitcoin's 24h move"),
    ("dd_7d", "Distance below the 7-day high"),
    ("hour", "UTC hour of day"),
]


def features_and_labels(c, btc):
    n = len(c["c"])
    cl, h, l, qv, v, tb = c["c"], c["h"], c["l"], c["qv"], c["v"], c["tb"]
    nan = np.full(n, np.nan)

    def lag_ret(k):
        r = nan.copy()
        r[k:] = cl[k:] / cl[:-k] - 1
        return r

    f = {"ret_1h": lag_ret(4), "ret_4h": lag_ret(16), "ret_24h": lag_ret(LB24)}

    cs = np.concatenate([[0.0], np.cumsum(qv)])
    mean_prev = nan.copy()
    idx = np.arange(LB24, n)
    mean_prev[idx] = (cs[idx] - cs[idx - LB24]) / LB24
    with np.errstate(divide="ignore", invalid="ignore"):
        f["vol_surge_1"] = qv / mean_prev
        q4 = nan.copy()
        q4[3:] = (cs[4:] - cs[:-4]) / 4
        f["vol_surge_4"] = q4 / mean_prev
        v4 = nan.copy()
        cv, ctb = np.concatenate([[0.0], np.cumsum(v)]), np.concatenate([[0.0], np.cumsum(tb)])
        v4[3:] = (cv[4:] - cv[:-4])
        t4 = nan.copy()
        t4[3:] = (ctb[4:] - ctb[:-4])
        f["taker_buy_4"] = t4 / v4

    wh = sliding_window_view(h, LB24).max(axis=1)      # wh[k] = max h[k..k+95]
    wl = sliding_window_view(l, LB24).min(axis=1)
    maxh_prev, minl_prev = nan.copy(), nan.copy()
    maxh_prev[LB24:] = wh[:n - LB24]
    minl_prev[LB24:] = wl[:n - LB24]
    rng = nan.copy()
    rng[LB24:] = (maxh_prev[LB24:] - minl_prev[LB24:]) / cl[LB24 - 1:n - 1]
    rcs = np.concatenate([[0.0], np.cumsum(np.nan_to_num(rng))])
    avg7 = nan.copy()
    j = np.arange(LB7D, n)
    avg7[j] = (rcs[j] - rcs[j - (LB7D - LB24)]) / (LB7D - LB24)
    with np.errstate(divide="ignore", invalid="ignore"):
        f["squeeze"] = rng / avg7
        f["near_high"] = cl / maxh_prev - 1
    f["breakout"] = np.where(np.isnan(maxh_prev), np.nan, (cl > maxh_prev).astype(float))
    wh7 = sliding_window_view(h, LB7D).max(axis=1)
    max7 = nan.copy()
    max7[LB7D:] = wh7[:n - LB7D]
    f["dd_7d"] = cl / max7 - 1

    # Bitcoin context, aligned on time
    pos = np.searchsorted(btc["t"], c["t"])
    pos = np.clip(pos, 0, len(btc["t"]) - 1)
    ok = btc["t"][pos] == c["t"]
    for key, k in (("rel_btc_4h", 16), ("btc_24h", LB24)):
        br = np.full(len(btc["c"]), np.nan)
        br[k:] = btc["c"][k:] / btc["c"][:-k] - 1
        x = np.where(ok, br[pos], np.nan)
        f[key] = (f["ret_4h"] - x) if key == "rel_btc_4h" else x
    f["hour"] = ((c["t"] // 3_600_000) % 24 + 1) % 24 + 0.0   # hour at candle close

    # labels
    m = n - H
    entry = cl[:m]
    wh_f = sliding_window_view(h[1:], H)[:m]
    wl_f = sliding_window_view(l[1:], H)[:m]
    fwd_gain = wh_f.max(axis=1) / entry - 1
    labels = {"fwd_gain": fwd_gain, "fwd_dd": wl_f.min(axis=1) / entry - 1}
    tp_hit = wh_f >= (entry * (1 + TP))[:, None]
    tp_any = tp_hit.any(axis=1)
    tp_idx = np.where(tp_any, tp_hit.argmax(axis=1), H)
    timeout_ret = cl[H:H + m] / entry - 1
    for s in STOPS:
        sl_hit = wl_f <= (entry * (1 - s))[:, None]
        sl_any = sl_hit.any(axis=1)
        sl_idx = np.where(sl_any, sl_hit.argmax(axis=1), H)
        win = tp_any & (tp_idx < sl_idx)
        loss = sl_any & ~win
        ret = np.where(win, TP, np.where(loss, -s, timeout_ret)) - FEE
        labels[f"win_{int(s * 100)}"] = win
        labels[f"ret_{int(s * 100)}"] = ret
    return f, labels, m


# --------------------------------------------------------------------------- #
# Analysis
# --------------------------------------------------------------------------- #

def rank_avg(x):
    _, inv, counts = np.unique(x, return_inverse=True, return_counts=True)
    cum = np.cumsum(counts)
    return (cum - (counts - 1) / 2)[inv]


def auc(pos, neg):
    if len(pos) < 50 or len(neg) < 50:
        return None
    x = np.concatenate([pos, neg])
    r = rank_avg(x)
    return float((r[:len(pos)].sum() - len(pos) * (len(pos) + 1) / 2) / (len(pos) * len(neg)))


def build_conditions(F):
    g = lambda k: F[k]
    with np.errstate(invalid="ignore"):
        return {
            "volume last hour 2x+ the 24h average": g("vol_surge_4") >= 2,
            "volume last hour 3x+ the 24h average": g("vol_surge_4") >= 3,
            "volume last hour 5x+ the 24h average": g("vol_surge_4") >= 5,
            "latest 15 min volume 4x+": g("vol_surge_1") >= 4,
            "buyers aggressive (taker buy share 58%+)": g("taker_buy_4") >= 0.58,
            "buyers very aggressive (taker buy share 65%+)": g("taker_buy_4") >= 0.65,
            "up 1% to 4% in the last hour": (g("ret_1h") >= 0.01) & (g("ret_1h") <= 0.04),
            "up 2% to 6% in the last 4 hours": (g("ret_4h") >= 0.02) & (g("ret_4h") <= 0.06),
            "not extended (24h change under 8%)": g("ret_24h") < 0.08,
            "coiled (24h range under 60% of its 7-day norm)": g("squeeze") <= 0.6,
            "making a new 24h high": g("breakout") == 1,
            "within 1.5% of the 24h high": g("near_high") >= -0.015,
            "outperforming Bitcoin by 2%+ (4h)": g("rel_btc_4h") >= 0.02,
            "Bitcoin not falling (24h >= 0)": g("btc_24h") >= 0,
            "20%+ below the 7-day high": g("dd_7d") <= -0.20,
        }


def cooled(rows, sym, t, mask):
    """Apply a per-coin cooldown to the signals in `mask`; return indices of trades taken."""
    idx = np.flatnonzero(mask)
    order = idx[np.lexsort((t[idx], sym[idx]))]
    taken, last_sym, last_t = [], -1, -1
    gap = COOLDOWN * CANDLE_MIN * 60 * 1000
    for i in order:
        if sym[i] != last_sym or t[i] - last_t >= gap:
            taken.append(i)
            last_sym, last_t = sym[i], t[i]
    return np.array(taken, dtype=int)


def trade_stats(taken, R, win, t):
    if len(taken) == 0:
        return {"trades": 0}
    r = R[taken]
    order = np.argsort(t[taken])
    pnl = np.cumsum(50.0 * r[order])
    dd = float(np.max(np.maximum.accumulate(pnl) - pnl)) if len(pnl) else 0.0
    span_days = max(1.0, (t[taken].max() - t[taken].min()) / 86_400_000)
    gains, losses = r[r > 0].sum(), -r[r < 0].sum()
    return {"trades": int(len(taken)), "win_rate_pct": round(100 * float(win[taken].mean()), 1),
            "avg_net_return_pct": round(100 * float(r.mean()), 2),
            "profit_factor": round(float(gains / losses), 2) if losses > 0 else None,
            "trades_per_day": round(len(taken) / span_days, 2),
            "pnl_usd_on_50_per_trade": round(float(pnl[-1]), 2), "max_drawdown_usd": round(dd, 2)}


def analyse(data, btc):
    cols = {k: [] for k, _ in FEATURES}
    lab = {}
    sym_ids, times = [], []
    for si, (name, c) in enumerate(data.items()):
        if len(c["c"]) < WARM + H + 200:
            continue
        f, labels, m = features_and_labels(c, btc)
        sl = slice(WARM, m)
        for k, _ in FEATURES:
            cols[k].append(f[k][sl])
        for k, v in labels.items():
            lab.setdefault(k, []).append(v[sl])
        sym_ids.append(np.full(m - WARM, si))
        times.append(c["t"][WARM:m])
    if not sym_ids:
        return None
    F = {k: np.concatenate(v) for k, v in cols.items()}
    L = {k: np.concatenate(v) for k, v in lab.items()}
    sym, t = np.concatenate(sym_ids), np.concatenate(times)
    valid = np.ones(len(t), bool)
    for k, _ in FEATURES:
        valid &= ~np.isnan(F[k])
    for k in F:
        F[k] = F[k][valid]
    for k in L:
        L[k] = L[k][valid]
    sym, t = sym[valid], t[valid]
    n = len(t)
    cut = np.quantile(t, TRAIN_FRACTION)
    train, test = t <= cut, t > cut
    log(f"[study] {n:,} decision points across {len(set(sym.tolist()))} coins; train {train.sum():,}, test {test.sum():,}")

    result = {"decision_points": int(n), "coins": int(len(set(sym.tolist()))),
              "train_until": datetime.fromtimestamp(cut / 1000, timezone.utc).isoformat()}

    # --- base rates ---
    base = {}
    for X in TARGETS:
        hit = L["fwd_gain"] >= X
        base[f"+{int(X * 100)}% within 24h (any stop)"] = {"all_pct": round(100 * float(hit.mean()), 2),
                                                           "test_pct": round(100 * float(hit[test].mean()), 2)}
    for s in STOPS:
        k = f"win_{int(s * 100)}"
        base[f"+15% before -{int(s * 100)}% (stop)"] = {"all_pct": round(100 * float(L[k].mean()), 2),
                                                        "test_pct": round(100 * float(L[k][test].mean()), 2),
                                                        "breakeven_win_rate_pct": round(100 * (s + FEE) / (TP + s), 1)}
    result["base_rates"] = base

    # --- traits: AUC per feature per target (what movers have in common) ---
    traits = []
    rng = np.random.default_rng(7)
    for k, label in FEATURES:
        row = {"feature": k, "meaning": label}
        for X in TARGETS:
            hit = L["fwd_gain"] >= X
            pos = F[k][hit]
            negi = np.flatnonzero(~hit)
            neg = F[k][rng.choice(negi, size=min(len(negi), 200_000), replace=False)]
            a = auc(pos, neg)
            row[f"auc_{int(X * 100)}"] = None if a is None else round(a, 3)
            if X == 0.15 and len(pos):
                row["median_when_move_follows"] = round(float(np.median(pos)), 4)
                row["median_otherwise"] = round(float(np.median(neg)), 4)
        traits.append(row)
    traits.sort(key=lambda r: -abs((r.get("auc_15") or 0.5) - 0.5))
    result["traits"] = traits

    # --- single conditions: lift on train and test ---
    conds = build_conditions(F)
    key = f"win_{int(MAIN_STOP * 100)}"
    rk = f"ret_{int(MAIN_STOP * 100)}"
    base_tr, base_te = L[key][train].mean(), L[key][test].mean()
    single = []
    for name, m in conds.items():
        a, b = m & train, m & test
        if a.sum() < 300 or b.sum() < 100:
            continue
        single.append({"condition": name, "train_n": int(a.sum()), "train_win_pct": round(100 * float(L[key][a].mean()), 2),
                       "train_lift": round(float(L[key][a].mean() / base_tr), 2) if base_tr else None,
                       "test_n": int(b.sum()), "test_win_pct": round(100 * float(L[key][b].mean()), 2),
                       "test_lift": round(float(L[key][b].mean() / base_te), 2) if base_te else None,
                       "test_avg_net_return_pct": round(100 * float(L[rk][b].mean()), 2)})
    single.sort(key=lambda r: -(r["test_lift"] or 0))
    result["single_conditions"] = single

    # --- greedy rule built on TRAIN only, judged on TEST ---
    chosen, cur = [], train.copy()
    for _ in range(4):
        best = None
        for name, m in conds.items():
            if name in chosen:
                continue
            mm = cur & m
            if mm.sum() < 800:
                continue
            e = float(L[rk][mm].mean())
            if best is None or e > best[0]:
                best = (e, name, mm)
        if best is None or best[0] <= float(L[rk][cur].mean()) + 0.0005:
            break
        chosen.append(best[1])
        cur = best[2]
    rule_mask = np.ones(n, bool)
    for name in chosen:
        rule_mask &= conds[name]
    random_taken = cooled(None, sym, t, test & (rng.random(n) < 0.02))
    train_taken = cooled(None, sym, t, rule_mask & train)
    test_taken = cooled(None, sym, t, rule_mask & test)
    result["rule"] = {
        "conditions": chosen, "stop_pct": int(MAIN_STOP * 100), "target_pct": int(TP * 100), "fee_assumed_round_trip_pct": FEE * 100,
        "train": trade_stats(train_taken, L[rk], L[key], t),
        "test_out_of_sample": trade_stats(test_taken, L[rk], L[key], t),
        "random_entries_test_for_comparison": trade_stats(random_taken, L[rk], L[key], t),
    }
    # how late would the signal be? (what had already happened when winning signals fired)
    wins = test_taken[L[key][test_taken]] if len(test_taken) else np.array([], dtype=int)
    if len(wins):
        result["rule"]["median_move_already_made_when_signal_fires_pct"] = {
            "last_hour": round(100 * float(np.median(F["ret_1h"][wins])), 2),
            "last_4h": round(100 * float(np.median(F["ret_4h"][wins])), 2)}
    result["notes"] = [
        "AUC 0.5 = the feature tells you nothing; 0.6 is weak, 0.7 useful, 0.8+ strong.",
        "A rule only counts if the OUT-OF-SAMPLE trades are profitable after fees; the training results are always flattering.",
        "Candle data cannot show the order of events inside one 15-minute candle: if a stop and a target both fall in one candle, the stop is assumed first.",
        "Fees are a flat assumption, and real slippage on thin coins is worse. The study covers only liquid Binance USDT pairs.",
    ]
    return result


def main():
    syms = universe()
    if not syms:
        log("FATAL: could not fetch the coin list (is data-api.binance.vision reachable?)")
        return 1
    start = int((time.time() - DAYS * 86400) * 1000)
    btc = klines("BTCUSDT", start)
    if btc is None:
        log("FATAL: no Bitcoin data")
        return 1
    data = {}
    for i, s in enumerate(syms):
        if s == "BTCUSDT":
            continue
        k = klines(s, start)
        if k is not None:
            data[s] = k
        if (i + 1) % 25 == 0:
            log(f"[study] downloaded {i + 1}/{len(syms)}")
    res = analyse(data, btc)
    if not res:
        log("FATAL: not enough data to analyse")
        return 1
    res["generated_at"] = datetime.now(timezone.utc).isoformat()
    res["params"] = {"days": DAYS, "coins_requested": TOP_N, "candle_minutes": CANDLE_MIN, "horizon_hours": 24}
    with open(OUT, "w", encoding="utf-8") as fh:
        json.dump(res, fh, indent=1)
    log("[study] top traits (AUC for a +15% move within 24h):")
    for r in res["traits"][:6]:
        log(f"   {r['feature']:14} auc15={r.get('auc_15')}  ({r['meaning']})")
    log(f"[study] rule: {res['rule']['conditions']}")
    log(f"[study] out-of-sample: {res['rule']['test_out_of_sample']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
