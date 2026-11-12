# -*- coding: utf-8 -*-
"""
KRYPTO-BOTEN  (papperstrading - inga riktiga pengar)
=====================================================
Kör:   python bot.py            -> live papperstrading dygnet runt
       python bot.py backtest 14 -> testa på de senaste 14 dagarnas data direkt
       python bot.py demo        -> snabbtest med påhittad data (ingen internet)

Boten:
  * hämtar riktiga priser från Binance (gratis, ingen nyckel behövs)
  * kör 5 strategier samtidigt på flera kryptovalutor (inkl. memecoins)
  * varje strategi kan gå LÅNG (tjäna på uppgång) och KORT (tjäna på nedgång)
  * "låtsashandlar" med 10 000 USDT inkl. avgifter, slippage och funding
  * lär sig:  1) lägger mer pengar på strategier/mynt som går bra och mindre på dåliga
              2) testar nya inställningar var 6:e timme och byter om de är klart bättre
  * skriver rapport.html (öppna i webbläsaren, uppdateras automatiskt)

Bara Pythons standardbibliotek används - inget extra behöver installeras.
"""

import json
import math
import re
import os
import random
import sys
import time
import itertools
import urllib.request
import urllib.error
import urllib.parse
import webbrowser
from datetime import datetime

# ----------------------------------------------------------------------------
# INSTÄLLNINGAR  (ändra gärna här)
# ----------------------------------------------------------------------------
SYMBOLS = ["BTCUSDT", "ETHUSDT", "SOLUSDT", "BNBUSDT", "XRPUSDT", "DOGEUSDT",
           "ADAUSDT", "AVAXUSDT", "LINKUSDT", "SUIUSDT",
           "PEPEUSDT", "WIFUSDT", "BONKUSDT", "SHIBUSDT", "FLOKIUSDT"]   # sista fem = memecoins (mycket mer svängiga)
TIMEFRAME = "1h"           # ljusens längd i live-läget: "5m", "15m" eller "1h" (se jämförelsen)
START_CAPITAL = 10_000.0   # låtsaspengar i USDT
FEE = 0.0005               # 0,05 % per köp och per sälj (Binance Futures, taker). Spot = 0.001
SLIPPAGE = 0.0005          # 0,05 % sämre pris än det vi ser
BASE_POSITION_PCT = 0.08   # varje trade = 8 % av kapitalet x "förtroende"
MAX_OPEN_POSITIONS = 12
TARGET_DAILY_VOL = 0.03    # mynt som svänger mer än 3 %/dag får mindre insats (memecoins), lugnare mynt mer
MIN_TRADE_USDT = 10.0
POLL_SECONDS = 20          # hur ofta live-boten kollar priser
SIGNAL_WINDOW = 500        # antal ljus som strategierna räknar på
LEARN_K = 40.0             # hur hårt resultat påverkar förtroendet
MULT_MIN, MULT_MAX = 0.25, 2.5
SWITCH_MARGIN = 0.25       # ny inställning måste vara så här mycket bättre för att bytas in
ENABLE_SHORT = True        # False = bara köp (spot). True = kan även tjäna på nedgångar (som futures, 1x)
SHORT_FUNDING_8H = 0.0001  # kostnad för korta positioner (0,01 % per 8 timmar, typiskt för futures)
REGIME_SYMBOL = "BTCUSDT"  # BTC-filtret: långa bara när BTC går upp, korta bara när BTC går ner
STATE_VERSION = 3
ACTIVE_SCORE = 0.5         # en strategi får bara handla om den visat klar vinst i senaste testet

# Inställningar per tidsram: hur mycket historik den lär sig av och hur ofta
TIMEFRAMES = {
    "5m":  {"ms": 5 * 60 * 1000,       "opt_window": 2016, "reopt_hours": 12,  "days": 45},   # lär sig på 7 dygn
    "15m": {"ms": 15 * 60 * 1000,      "opt_window": 1344, "reopt_hours": 24,  "days": 90},   # 14 dygn
    "1h":  {"ms": 60 * 60 * 1000,      "opt_window": 1440, "reopt_hours": 72,  "days": 240},  # 60 dygn
    "4h":  {"ms": 4 * 60 * 60 * 1000,  "opt_window": 540,  "reopt_hours": 168, "days": 450},  # 90 dygn
    "1d":  {"ms": 24 * 60 * 60 * 1000, "opt_window": 365,  "reopt_hours": 720, "days": 2000}, # används av trendmodellen
}
COMPARE_TIMEFRAMES = ["15m", "1h", "4h"]   # 5m är bortplockad: avgifterna äter upp allt


def set_timeframe(tf):
    global INTERVAL, BAR_MS, OPT_WINDOW, REOPT_HOURS, REGIME_N, SIGNAL_WINDOW
    cfg = TIMEFRAMES[tf]
    INTERVAL, BAR_MS = tf, cfg["ms"]
    OPT_WINDOW, REOPT_HOURS = cfg["opt_window"], cfg["reopt_hours"]
    REGIME_N = max(24, int(24 * 3600 * 1000 / BAR_MS))   # BTC jämförs med sitt dygnssnitt
    SIGNAL_WINDOW = max(500, int(57 * 86400000 / BAR_MS))  # räcker för trendens längsta jämförelse (56 dygn)

HERE = os.path.dirname(os.path.abspath(__file__))
STATE_FILE = os.path.join(HERE, "state.json")
SETTINGS_FILE = os.path.join(HERE, "installningar.json")   # skrivs av jämförelsen
try:
    with open(SETTINGS_FILE, encoding="utf-8") as _f:
        _saved = json.load(_f).get("timeframe")
    if _saved in TIMEFRAMES:
        TIMEFRAME = _saved
except Exception:
    pass
set_timeframe(TIMEFRAME)
REPORT_FILE = os.path.join(HERE, "rapport.html")
TRADES_CSV = os.path.join(HERE, "trades.csv")

BASE_URLS = ["https://data-api.binance.vision", "https://api.binance.com", "https://api1.binance.com"]

try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass


def log(msg):
    print(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] {msg}", flush=True)


def fmt_ts(ms):
    return datetime.fromtimestamp(ms / 1000).strftime("%Y-%m-%d %H:%M")


# ----------------------------------------------------------------------------
# DATA
# ----------------------------------------------------------------------------
class Bars:
    """Ljusstakar som listor: t (öppningstid ms), o, h, l, c, v"""
    __slots__ = ("t", "o", "h", "l", "c", "v")

    def __init__(self):
        self.t, self.o, self.h, self.l, self.c, self.v = [], [], [], [], [], []

    def __len__(self):
        return len(self.c)

    def append(self, t, o, h, l, c, v):
        self.t.append(t); self.o.append(o); self.h.append(h)
        self.l.append(l); self.c.append(c); self.v.append(v)

    def inverted(self):
        """Spegelvända priser (1/pris). Används för att hitta lägen att gå kort."""
        n = Bars()
        n.t, n.v = self.t, self.v
        n.o = [1.0 / x for x in self.o]
        n.c = [1.0 / x for x in self.c]
        n.h = [1.0 / x for x in self.l]
        n.l = [1.0 / x for x in self.h]
        return n

    def slice(self, a, b):
        n = Bars()
        n.t, n.o, n.h, n.l, n.c, n.v = (self.t[a:b], self.o[a:b], self.h[a:b],
                                        self.l[a:b], self.c[a:b], self.v[a:b])
        return n


def http_json(path, rounds=5):
    """Hämtar JSON från Binance. Om internet hackar försöker den igen några gånger
    (väntar 5, 10, 20, 40 sek) innan den ger upp."""
    last_err = None
    for r_i in range(rounds):
        for base in BASE_URLS:
            try:
                req = urllib.request.Request(base + path, headers={"User-Agent": "paper-bot/1.0"})
                with urllib.request.urlopen(req, timeout=15) as r:
                    return json.loads(r.read().decode())
            except urllib.error.HTTPError as e:
                last_err = e
                if e.code == 400:   # fel mynt-namn e.d. - ingen idé att försöka igen
                    raise RuntimeError(f"Binance svarade 400 (finns myntet?): {e}")
            except Exception as e:  # prova nästa adress
                last_err = e
        if r_i < rounds - 1:
            wait = 5 * (2 ** r_i)
            log(f"  Internet/Binance svarar inte ({last_err}) - försöker igen om {wait} s")
            time.sleep(wait)
    raise RuntimeError(f"Kunde inte hämta data från Binance: {last_err}")


COINBASE_GRAN = {"5m": 300, "15m": 900, "1h": 3600, "1d": 86400}
_BINANCE_DOWN = {"until": 0}


def fetch_klines_coinbase(symbol, limit=1000, start_ms=None):
    """Reservkälla om Binance är blockerat (t.ex. på amerikanska molnservrar)."""
    gran = COINBASE_GRAN.get(INTERVAL)
    if not gran or not symbol.endswith("USDT"):
        raise RuntimeError("Coinbase saknar denna tidsram")
    prod = symbol[:-4] + "-USD"
    step = gran * 1000
    now = int(time.time() * 1000)
    start = start_ms if start_ms is not None else now - limit * step
    rows = {}
    while start < now and len(rows) < limit:
        end = min(now, start + 300 * step)
        url = (f"https://api.exchange.coinbase.com/products/{prod}/candles?granularity={gran}"
               f"&start={datetime.utcfromtimestamp(start / 1000).isoformat()}Z&end={datetime.utcfromtimestamp(end / 1000).isoformat()}Z")
        req = urllib.request.Request(url, headers={"User-Agent": "paper-bot/1.0"})
        with urllib.request.urlopen(req, timeout=15) as r:
            data = json.loads(r.read().decode())
        if isinstance(data, dict):
            raise RuntimeError(f"Coinbase: {data.get('message')}")
        for t, lo, hi, op, cl, vol in data:
            rows[int(t) * 1000] = (float(op), float(hi), float(lo), float(cl), float(vol))
        start = end
        time.sleep(0.15)
    b = Bars()
    for t in sorted(rows)[:limit]:
        b.append(t, *rows[t])
    return b


def fetch_klines(symbol, limit=1000, start_ms=None):
    if time.time() < _BINANCE_DOWN["until"]:
        return fetch_klines_coinbase(symbol, limit, start_ms)
    path = f"/api/v3/klines?symbol={symbol}&interval={INTERVAL}&limit={limit}"
    if start_ms is not None:
        path += f"&startTime={int(start_ms)}"
    try:
        raw = http_json(path, rounds=2 if os.environ.get("GITHUB_ACTIONS") else 5)
    except RuntimeError as e:
        if "400" in str(e):
            raise
        log(f"  Binance svarar inte ({e}) - använder Coinbase som reserv")
        _BINANCE_DOWN["until"] = time.time() + 3600
        return fetch_klines_coinbase(symbol, limit, start_ms)
    b = Bars()
    for k in raw:
        b.append(int(k[0]), float(k[1]), float(k[2]), float(k[3]), float(k[4]), float(k[5]))
    return b


def fetch_history(symbol, days):
    """Hämtar historik och sparar den i mappen data_cache, så nästa test bara
    behöver ladda ner de senaste ljusen (går mycket snabbare)."""
    need = int(days * 24 * 3600 * 1000 / BAR_MS)
    start_wanted = int(time.time() * 1000) - need * BAR_MS
    cache_dir = os.path.join(HERE, "data_cache")
    cache_file = os.path.join(cache_dir, f"{symbol}_{INTERVAL}.json")
    cached = Bars()
    try:
        with open(cache_file, encoding="utf-8") as f:
            for row in json.load(f):
                cached.append(*row)
    except Exception:
        pass
    if len(cached) and cached.t[0] <= start_wanted + BAR_MS:
        start = cached.t[-1] + BAR_MS
        out = cached
    else:
        start = start_wanted
        out = Bars()
    out = _download_from(symbol, start, out)
    try:
        os.makedirs(cache_dir, exist_ok=True)
        rows = [[out.t[i], out.o[i], out.h[i], out.l[i], out.c[i], out.v[i]] for i in range(len(out))]
        with open(cache_file + ".tmp", "w", encoding="utf-8") as f:
            json.dump(rows, f)
        os.replace(cache_file + ".tmp", cache_file)
    except Exception:
        pass
    i0 = 0
    while i0 < len(out) and out.t[i0] < start_wanted:
        i0 += 1
    return out.slice(i0, len(out))


def _download_from(symbol, start, out):
    while True:
        chunk = fetch_klines(symbol, 1000, start)
        if len(chunk) == 0:
            break
        for i in range(len(chunk)):
            out.append(chunk.t[i], chunk.o[i], chunk.h[i], chunk.l[i], chunk.c[i], chunk.v[i])
        start = chunk.t[-1] + BAR_MS
        if len(chunk) < 1000:
            break
        time.sleep(0.2)
    # släng sista (ej stängda) ljuset
    now = int(time.time() * 1000)
    if len(out) and out.t[-1] + BAR_MS > now:
        out = out.slice(0, len(out) - 1)
    return out


def fake_history(symbol, n_bars, seed):
    """Påhittad prisdata för test utan internet (slumpvandring med trender)."""
    rnd = random.Random(seed)
    price = {"BTCUSDT": 60000, "ETHUSDT": 3000, "SOLUSDT": 150}.get(symbol, 1.0 + rnd.random() * 100)
    t = (int(time.time() * 1000) // BAR_MS - n_bars) * BAR_MS
    b = Bars()
    drift = 0.0
    for _ in range(n_bars):
        if rnd.random() < 0.01:
            drift = rnd.gauss(0, 0.0006)
        o = price
        moves = [rnd.gauss(drift / 4, 0.0018) for _ in range(4)]
        path = [o]
        for m in moves:
            path.append(path[-1] * (1 + m))
        c = path[-1]
        h = max(path) * (1 + abs(rnd.gauss(0, 0.0007)))
        l = min(path) * (1 - abs(rnd.gauss(0, 0.0007)))
        b.append(t, o, h, l, c, 1.0)
        price = c
        t += BAR_MS
    return b


# ----------------------------------------------------------------------------
# INDIKATORER  (räknar bara på historik -> inget fusk med framtida data)
# ----------------------------------------------------------------------------
def ema(vals, n):
    out = [0.0] * len(vals)
    if not vals:
        return out
    k = 2.0 / (n + 1)
    e = vals[0]
    for i, v in enumerate(vals):
        e = v * k + e * (1 - k) if i else v
        out[i] = e
    return out


def sma_std(vals, n):
    m = [None] * len(vals)
    s = [None] * len(vals)
    acc = acc2 = 0.0
    for i, v in enumerate(vals):
        acc += v; acc2 += v * v
        if i >= n:
            old = vals[i - n]
            acc -= old; acc2 -= old * old
        if i >= n - 1:
            mean = acc / n
            var = max(acc2 / n - mean * mean, 0.0)
            m[i] = mean
            s[i] = math.sqrt(var)
    return m, s


def rsi(vals, n):
    out = [50.0] * len(vals)
    if len(vals) <= n:
        return out
    gain = loss = 0.0
    for i in range(1, n + 1):
        d = vals[i] - vals[i - 1]
        gain += max(d, 0); loss += max(-d, 0)
    gain /= n; loss /= n
    for i in range(n + 1, len(vals)):
        d = vals[i] - vals[i - 1]
        gain = (gain * (n - 1) + max(d, 0)) / n
        loss = (loss * (n - 1) + max(-d, 0)) / n
        out[i] = 100.0 if loss == 0 else 100 - 100 / (1 + gain / loss)
    return out


def rolling_prev_max(vals, n):
    out = [None] * len(vals)
    for i in range(n, len(vals)):
        out[i] = max(vals[i - n:i])
    return out


def rolling_prev_min(vals, n):
    out = [None] * len(vals)
    for i in range(n, len(vals)):
        out[i] = min(vals[i - n:i])
    return out


# ----------------------------------------------------------------------------
# STRATEGIER  -> lista med 1 (köp), -1 (sälj), 0 (inget) per ljus
# ----------------------------------------------------------------------------
def sig_trend(b, p):
    c = b.c
    f, s = ema(c, p["fast"]), ema(c, p["slow"])
    sig = [0] * len(c)
    for i in range(max(p["slow"], 2), len(c)):
        if f[i] > s[i] and f[i - 1] <= s[i - 1]:
            sig[i] = 1
        elif f[i] < s[i] and f[i - 1] >= s[i - 1]:
            sig[i] = -1
    return sig


def sig_meanrev(b, p):
    c = b.c
    mid, sd = sma_std(c, p["n"])
    r = rsi(c, p["rsi_n"])
    sig = [0] * len(c)
    for i in range(p["n"], len(c)):
        if c[i] < mid[i] - p["k"] * sd[i] and r[i] < p["rsi_low"]:
            sig[i] = 1
        elif c[i] > mid[i] or r[i] > p["rsi_exit"]:
            sig[i] = -1
    return sig


def sig_breakout(b, p):
    c = b.c
    hh = rolling_prev_max(b.h, p["n"])
    ll = rolling_prev_min(b.l, p["m"])
    sig = [0] * len(c)
    for i in range(max(p["n"], p["m"]), len(c)):
        if c[i] > hh[i]:
            sig[i] = 1
        elif c[i] < ll[i]:
            sig[i] = -1
    return sig


def sig_macd(b, p):
    c = b.c
    ef, es = ema(c, p["fast"]), ema(c, p["slow"])
    macd = [a - z for a, z in zip(ef, es)]
    sl = ema(macd, p["sig"])
    tr = ema(c, p["trend_n"])
    sig = [0] * len(c)
    for i in range(max(p["slow"], p["trend_n"] // 2, 2), len(c)):
        h0, h1 = macd[i] - sl[i], macd[i - 1] - sl[i - 1]
        if h0 > 0 >= h1 and c[i] > tr[i]:
            sig[i] = 1
        elif h0 < 0 <= h1:
            sig[i] = -1
    return sig


def sig_momentum(b, p):
    c = b.c
    tr = ema(c, p["trend_n"])
    n = p["n"]
    sig = [0] * len(c)
    for i in range(max(n, p["trend_n"] // 2), len(c)):
        roc = c[i] / c[i - n] - 1
        if roc > p["thr"] and c[i] > tr[i]:
            sig[i] = 1
        elif roc < 0:
            sig[i] = -1
    return sig




TSMOM_SETS = [(3, 7, 14), (7, 14, 28), (14, 28, 56)]


def sig_tsmom(b, p):
    """Trendföljning enligt forskningen (time-series momentum): titta på avkastningen
    över tre perioder (t.ex. 1, 2 och 4 veckor). Köp när minst 'need' av dem är plus,
    sälj när färre än 'exit' är plus."""
    c = b.c
    per_day = max(1, int(86400000 / BAR_MS))
    looks = [d * per_day for d in TSMOM_SETS[p["set"]]]
    sig = [0] * len(c)
    for i in range(looks[-1], len(c)):
        ups = sum(1 for L in looks if c[i] > c[i - L])
        if ups >= p["need"]:
            sig[i] = 1
        elif ups < p["exit"]:
            sig[i] = -1
    return sig


RISK_GRID = {"sl": [0.015, 0.025, 0.04, 0.06], "tp": [0.02, 0.04, 0.07, 0.12],
             "trail": [0, 0.015, 0.03], "regime": [0, 1]}

STRATEGIES = {
    "trend": {
        "namn": "Trendföljning (EMA-kors)",
        "fn": sig_trend,
        "grid": {"fast": [5, 8, 12, 20], "slow": [26, 50, 100, 150], **RISK_GRID},
        "start": {"fast": 12, "slow": 50, "sl": 0.025, "tp": 0.04, "trail": 0, "regime": 1},
        "valid": lambda p: p["fast"] < p["slow"],
    },
    "meanrev": {
        "namn": "Studs tillbaka (Bollinger + RSI)",
        "fn": sig_meanrev,
        "grid": {"n": [20, 30, 50], "k": [1.5, 2.0, 2.5], "rsi_n": [7, 14],
                 "rsi_low": [25, 30, 35], "rsi_exit": [55, 65, 75], **RISK_GRID},
        "start": {"n": 20, "k": 2.0, "rsi_n": 14, "rsi_low": 30, "rsi_exit": 65, "sl": 0.025, "tp": 0.04, "trail": 0, "regime": 0},
        "valid": lambda p: True,
    },
    "breakout": {
        "namn": "Utbrott (Donchian)",
        "fn": sig_breakout,
        "grid": {"n": [24, 48, 96, 144], "m": [12, 24, 48], **RISK_GRID},
        "start": {"n": 48, "m": 24, "sl": 0.025, "tp": 0.04, "trail": 0, "regime": 1},
        "valid": lambda p: True,
    },
    "macd": {
        "namn": "MACD med trendfilter",
        "fn": sig_macd,
        "grid": {"fast": [8, 12], "slow": [21, 26, 34], "sig": [7, 9], "trend_n": [50, 100, 200], **RISK_GRID},
        "start": {"fast": 12, "slow": 26, "sig": 9, "trend_n": 100, "sl": 0.025, "tp": 0.04, "trail": 0, "regime": 1},
        "valid": lambda p: p["fast"] < p["slow"],
    },
    "tsmom": {
        "namn": "Trend på veckosikt (forskningsbaserad)",
        "fn": sig_tsmom,
        "grid": {"set": [0, 1, 2], "need": [2, 3], "exit": [1, 2],
                 "sl": [0.04, 0.06, 0.1, 0.15], "tp": [0.07, 0.12, 0.25, 0.5], "trail": [0, 0.03, 0.06, 0.1], "regime": [0, 1]},
        "start": {"set": 1, "need": 3, "exit": 2, "sl": 0.1, "tp": 0.5, "trail": 0.06, "regime": 0},
        "valid": lambda p: p["exit"] <= p["need"],
    },
    "momentum": {
        "namn": "Momentum (ROC + trend)",
        "fn": sig_momentum,
        "grid": {"n": [6, 12, 24, 48], "thr": [0.005, 0.01, 0.02], "trend_n": [50, 100, 200], **RISK_GRID},
        "start": {"n": 12, "thr": 0.01, "trend_n": 100, "sl": 0.025, "tp": 0.04, "trail": 0, "regime": 1},
        "valid": lambda p: True,
    },
}

STRATEGIES["rotation"] = {
    "namn": "Rotation (starkaste vs svagaste mynten)",
    "fn": None, "cross": True,
    "grid": {"look_h": [24, 72, 168, 336, 720], "hold_h": [8, 24, 72, 168], "k": [1, 2, 3], "abs": [0, 1], "dir": [1, -1],
             "sl": [0.04, 0.08, 0.15], "tp": [0.1, 0.3], "trail": [0, 0.05], "regime": [0, 1]},
    "start": {"look_h": 72, "hold_h": 24, "k": 2, "abs": 1, "dir": 1, "sl": 0.08, "tp": 0.3, "trail": 0, "regime": 0},
    "valid": lambda p: True,
}


def rotation_signals(bars_by_sym, p, side):
    """Vid varje ombalansering: rangordna mynten efter hur mycket de stigit senaste
    look_h timmarna. Lång-sidan köper de k starkaste, kort-sidan blankar de k svagaste.
    dir=-1 vänder på det (köp de som fallit mest = "studs tillbaka", forskningen visar att
    det ofta funkar på ~1 månads sikt).
    Alla andra positioner stängs. Mellan ombalanseringar: 0 (behåll)."""
    look = max(1, int(p["look_h"] * 3.6e6 / BAR_MS))
    hold = max(1, int(p["hold_h"] * 3.6e6 / BAR_MS))
    rets = {}
    for sym, b in bars_by_sym.items():
        r = {}
        for i in range(look, len(b)):
            r[b.t[i]] = b.c[i] / b.c[i - look] - 1
        rets[sym] = r
    out = {}
    for sym, b in bars_by_sym.items():
        out[sym] = [0] * len(b)
    times = set()
    for b in bars_by_sym.values():
        times.update(b.t)
    pos_of = {sym: {t: i for i, t in enumerate(b.t)} for sym, b in bars_by_sym.items()}
    for t in times:
        if (t // BAR_MS) % hold != 0:
            continue
        ranked = sorted(((rets[s].get(t) * p.get("dir", 1), s) for s in bars_by_sym if rets[s].get(t) is not None))
        if len(ranked) < 2 * p["k"] + 1:
            continue
        if side == "long":
            pick = [s for r, s in ranked[-p["k"]:] if not p["abs"] or r > 0]
        else:
            pick = [s for r, s in ranked[:p["k"]] if not p["abs"] or r < 0]
        for r, s in ranked:
            i = pos_of[s].get(t)
            if i is not None:
                out[s][i] = 1 if s in pick else -1
    return out


# Varje strategi körs som två "agenter": en som går lång och en som går kort.
SIDES = ["long", "short"] if ENABLE_SHORT else ["long"]
AGENTS = [f"{s}:{side}" for s in STRATEGIES for side in SIDES]
SIDE_TXT = {"long": "Lång", "short": "Kort"}


def agent_parts(agent):
    s, side = agent.split(":")
    return s, side


def agent_name(agent):
    s, side = agent_parts(agent)
    return f"{STRATEGIES[s]['namn']} - {SIDE_TXT[side]}"


def describe_params(p):
    parts = []
    for k, v in p.items():
        if k == "sl":
            parts.append(f"stopp {v * 100:.1f}%")
        elif k == "tp":
            parts.append(f"vinstmål {v * 100:.1f}%")
        elif k == "trail":
            parts.append(f"släpande stopp {v * 100:.1f}%" if v else "släpande stopp av")
        elif k == "regime":
            parts.append("BTC-filter " + ("på" if v else "av"))
        else:
            parts.append(f"{k}={v}")
    return ", ".join(parts)


def is_cross(agent):
    return STRATEGIES[agent_parts(agent)[0]].get("cross", False)


def all_signals(windows, params):
    """windows = {sym: (bars, inv_bars)} -> {sym: {agent: [signaler]}}"""
    out = {sym: {} for sym in windows}
    for ag in AGENTS:
        p = params[ag]
        if is_cross(ag):
            rs = rotation_signals({s: w[0] for s, w in windows.items()}, p, agent_parts(ag)[1])
            for sym in windows:
                out[sym][ag] = rs[sym]
        else:
            for sym, (w, wi) in windows.items():
                out[sym][ag] = agent_signals(ag, w, wi, p)
    return out


def agent_signals(agent, b, inv, p):
    """Lång: strategin på vanliga priser. Kort: samma strategi på spegelvända priser
    (1/pris), så ett 'köp' där betyder att priset ser ut att falla här."""
    s, side = agent_parts(agent)
    return STRATEGIES[s]["fn"](b if side == "long" else inv, p)


def regime_allows(side, use_regime, r):
    if not use_regime or r == 0:
        return True
    return (r > 0) if side == "long" else (r < 0)


# ----------------------------------------------------------------------------
# PRISBERÄKNING FÖR LÅNG/KORT (samma formel i snabbtest och i kontot)
# ----------------------------------------------------------------------------
def entry_price(p, side):
    return p * (1 + SLIPPAGE) if side == "long" else p * (1 - SLIPPAGE)


def exit_price(p, side):
    return p * (1 - SLIPPAGE) if side == "long" else p * (1 + SLIPPAGE)


def stop_take(e, side, sl, tp):
    if side == "long":
        return e * (1 - sl), e * (1 + tp)
    return e * (1 + sl), e * (1 - tp)


def trade_value(cost, e, x, side, hours=0.0):
    """Vad en insats 'cost' är värd vid stängning till pris x (efter båda avgifterna)."""
    notional = cost * (1 - FEE)
    qty = notional / e
    if side == "long":
        gross = qty * x
    else:
        gross = notional + qty * (e - x)
        gross -= notional * SHORT_FUNDING_8H * hours / 8.0
    return gross - qty * x * FEE


def mark_value(cost, e, price, side):
    notional = cost * (1 - FEE)
    qty = notional / e
    return qty * price if side == "long" else notional + qty * (e - price)


# ----------------------------------------------------------------------------
# SNABBSIMULERING (används när boten lär sig nya inställningar)
# ----------------------------------------------------------------------------
def trail_stop(stop, side, high, low, trail):
    """Släpande stopp: flyttar stoppet efter när priset går åt rätt håll."""
    if not trail:
        return stop
    if side == "long":
        return max(stop, high * (1 - trail))
    return min(stop, low * (1 + trail))


def simulate(b, sig, p, side, regime):
    sl, tp, use_reg, tr = p["sl"], p["tp"], p.get("regime", 0), p.get("trail", 0)
    rets = []
    pos = None  # (entry, stop, take, j)
    n = len(b)
    for j in range(1, n):
        s = sig[j - 1]
        if pos is not None and s == -1:
            x = exit_price(b.o[j], side)
            rets.append(trade_value(1.0, pos[0], x, side, (j - pos[3]) * BAR_MS / 3.6e6) - 1)
            pos = None
        elif pos is None and s == 1 and regime_allows(side, use_reg, regime[j - 1]):
            e = entry_price(b.o[j], side)
            st, tk = stop_take(e, side, sl, tp)
            pos = [e, st, tk, j]
        if pos is not None:
            x = None
            if side == "long":
                if b.l[j] <= pos[1]:
                    x = pos[1]
                elif b.h[j] >= pos[2]:
                    x = pos[2]
            else:
                if b.h[j] >= pos[1]:
                    x = pos[1]
                elif b.l[j] <= pos[2]:
                    x = pos[2]
            if x is not None:
                x = exit_price(x, side)
                rets.append(trade_value(1.0, pos[0], x, side, (j - pos[3]) * BAR_MS / 3.6e6) - 1)
                pos = None
            else:
                pos[1] = trail_stop(pos[1], side, b.h[j], b.l[j], tr)
    return rets


def score_returns(rets):
    n = len(rets)
    if n < 4:
        return -5.0 + n * 0.1  # för få trades = inget vi kan lita på
    mean = sum(rets) / n
    var = sum((r - mean) ** 2 for r in rets) / (n - 1)
    return mean / (math.sqrt(var) + 0.003) * math.sqrt(n)


def neighbours(params, grid, rnd, count):
    """Små förändringar av nuvarande inställningar ("mutationer")."""
    out = []
    keys = list(grid.keys())
    for _ in range(count):
        p = dict(params)
        k = rnd.choice(keys)
        opts = grid[k]
        if p.get(k) in opts:
            idx = opts.index(p[k]) + rnd.choice([-1, 1])
            p[k] = opts[max(0, min(len(opts) - 1, idx))]
        else:
            p[k] = rnd.choice(opts)
        out.append(p)
    return out


_COMBO_CACHE = {}


def all_combos(strat):
    if strat not in _COMBO_CACHE:
        st = STRATEGIES[strat]
        keys = list(st["grid"].keys())
        combos = [dict(zip(keys, v)) for v in itertools.product(*[st["grid"][k] for k in keys])]
        _COMBO_CACHE[strat] = [p for p in combos if st["valid"](p)]
    return _COMBO_CACHE[strat]


def optimize_agent(agent, window, incumbent, rnd, n_random=8, n_mut=5):
    """window = {sym: (bars, inv_bars, regime_list)}"""
    strat, side = agent_parts(agent)
    st = STRATEGIES[strat]
    cands = [incumbent] + rnd.sample(all_combos(strat), min(n_random, len(all_combos(strat))))
    cands += [p for p in neighbours(incumbent, st["grid"], rnd, n_mut) if st["valid"](p)]
    seen, uniq = set(), []
    for p in cands:
        key = tuple(sorted(p.items()))
        if key not in seen:
            seen.add(key)
            uniq.append(p)
    best_p, best_s, inc_s = incumbent, None, None
    for p in uniq:
        rets = []
        if st.get("cross"):
            rs = rotation_signals({s: v[0] for s, v in window.items()}, p, side)
        for sym, (b, inv, reg) in window.items():
            if len(b) < 200:
                continue
            sg = rs[sym] if st.get("cross") else agent_signals(agent, b, inv, p)
            rets += simulate(b, sg, p, side, reg)
        s = score_returns(rets)
        if p is incumbent:
            inc_s = s
        if best_s is None or s > best_s:
            best_p, best_s = p, s
    if inc_s is None:
        inc_s = best_s
    if best_p is not incumbent and best_s > inc_s + SWITCH_MARGIN:
        return best_p, inc_s, best_s, True
    return incumbent, inc_s, inc_s, False


def daily_vol(b, days=14):
    """Hur mycket myntet svänger per dygn (standardavvikelse), senaste ~2 veckorna."""
    per_day = max(1, int(86400000 / BAR_MS))
    n = min(len(b) - 1, days * per_day)
    if n < 10:
        return TARGET_DAILY_VOL
    rets = [b.c[i] / b.c[i - 1] - 1 for i in range(len(b) - n, len(b))]
    m = sum(rets) / n
    var = sum((r - m) ** 2 for r in rets) / n
    return max(1e-4, math.sqrt(var * per_day))


def regime_for(bars, btc):
    """+1 när BTC är över sitt dygnssnitt, -1 under, 0 okänt. Linjerad mot bars.t"""
    if btc is None or len(btc) == 0:
        return [0] * len(bars)
    e = ema(btc.c, REGIME_N)
    m = {}
    for i, t in enumerate(btc.t):
        m[t] = 0 if i < REGIME_N // 2 else (1 if btc.c[i] > e[i] else -1)
    return [m.get(t, 0) for t in bars.t]


# ----------------------------------------------------------------------------
# PAPPERSKONTO + LÄRANDE
# ----------------------------------------------------------------------------
class Engine:
    def __init__(self, state=None):
        if state and state.get("version") == STATE_VERSION:
            self.s = state
        else:
            self.s = {
                "version": STATE_VERSION,
                "start_ms": None, "cash": START_CAPITAL, "positions": [], "trades": [],
                "equity": [], "params": {a: dict(STRATEGIES[agent_parts(a)[0]]["start"]) for a in AGENTS},
                "scores": {}, "strat_scores": {}, "learning_log": [], "start_prices": {},
                "last_bar": {}, "last_reopt_ms": 0, "next_id": 1, "low_flags": {},
                "paused": {a: True for a in AGENTS}, "timeframe": INTERVAL,
            }
        self.prices = {}
        self.vols = {}

    # --- förtroende per agent+mynt (lärs av riktiga papperstrades) ---
    def multiplier(self, agent, sym=None):
        combo = self.s["scores"].get(f"{agent}|{sym}", 0.0) if sym else 0.0
        whole = self.s["strat_scores"].get(agent, 0.0)
        m = math.exp(LEARN_K * (0.5 * combo + 0.5 * whole))
        return max(MULT_MIN, min(MULT_MAX, m))

    def learn_from_trade(self, t, ts):
        a, sym = t["agent"], t["symbol"]
        key = f"{a}|{sym}"
        old = self.multiplier(a, sym)
        self.s["scores"][key] = 0.7 * self.s["scores"].get(key, 0.0) + 0.3 * t["ret"]
        self.s["strat_scores"][a] = 0.85 * self.s["strat_scores"].get(a, 0.0) + 0.15 * t["ret"]
        new = self.multiplier(a, sym)
        state = "låg" if new < 0.5 else ("hög" if new > 1.8 else "normal")
        if state != self.s["low_flags"].get(key, "normal"):
            self.s["low_flags"][key] = state
            namn = agent_name(a)
            if state == "låg":
                msg = f"{namn} på {sym} har gått dåligt -> minskar insatsen (x{old:.2f} -> x{new:.2f})"
            elif state == "hög":
                msg = f"{namn} på {sym} går bra -> ökar insatsen (x{old:.2f} -> x{new:.2f})"
            else:
                msg = f"{namn} på {sym} tillbaka till normal insats (x{new:.2f})"
            self.add_log(ts, msg)

    def add_log(self, ts, msg):
        self.s["learning_log"].append({"ts": ts, "msg": msg})
        self.s["learning_log"] = self.s["learning_log"][-400:]

    # --- konto ---
    def equity(self):
        e = self.s["cash"]
        for p in self.s["positions"]:
            e += mark_value(p["cost"], p["entry"], self.prices.get(p["symbol"], p["entry"]), p["side"])
        return e

    def open_pos(self, agent, sym, price, ts):
        strat, side = agent_parts(agent)
        if self.s["paused"].get(agent):
            return
        if len(self.s["positions"]) >= MAX_OPEN_POSITIONS:
            return
        for p in self.s["positions"]:
            if p["symbol"] == sym and (p["agent"] == agent or p["side"] != side):
                return  # en per agent+mynt, och aldrig lång och kort samtidigt i samma mynt
        par = self.s["params"][agent]
        vol_adj = max(0.3, min(2.0, TARGET_DAILY_VOL / self.vols.get(sym, TARGET_DAILY_VOL)))
        size = min(self.equity() * BASE_POSITION_PCT * self.multiplier(agent, sym) * vol_adj, self.s["cash"])
        if size < MIN_TRADE_USDT:
            return
        e = entry_price(price, side)
        st, tk = stop_take(e, side, par["sl"], par["tp"])
        self.s["cash"] -= size
        self.s["positions"].append({"id": self.s["next_id"], "agent": agent, "side": side, "symbol": sym,
                                    "entry": e, "cost": size, "stop": st, "take": tk, "ts": ts})
        self.s["next_id"] += 1

    def close_pos(self, pos, price, ts, reason):
        x = exit_price(price, pos["side"])
        hours = max(0.0, (ts - pos["ts"]) / 3.6e6)
        value = trade_value(pos["cost"], pos["entry"], x, pos["side"], hours)
        self.s["cash"] += value
        self.s["positions"].remove(pos)
        t = {"agent": pos["agent"], "side": pos["side"], "symbol": pos["symbol"], "entry": pos["entry"],
             "exit": x, "cost": pos["cost"], "pnl": value - pos["cost"], "ret": value / pos["cost"] - 1,
             "entry_ts": pos["ts"], "exit_ts": ts, "reason": reason}
        self.s["trades"].append(t)
        self.learn_from_trade(t, ts)
        return t

    def apply_signals(self, sym, sigs, price, ts, regime):
        """sigs = {agent: 1/-1/0} från senaste stängda ljuset; handlar till price."""
        self.prices[sym] = price
        for agent, s in sigs.items():
            if s == -1:
                for p in [p for p in self.s["positions"] if p["agent"] == agent and p["symbol"] == sym]:
                    self.close_pos(p, price, ts, "signal")
        for agent, s in sigs.items():
            if s == 1:
                side = agent_parts(agent)[1]
                if regime_allows(side, self.s["params"][agent].get("regime", 0), regime):
                    self.open_pos(agent, sym, price, ts)

    def check_exits(self, sym, high, low, ts):
        for p in [p for p in self.s["positions"] if p["symbol"] == sym]:
            moved = p.get("moved", False)
            why = "släpande stopp" if moved else "stopp"
            if p["side"] == "long":
                if low <= p["stop"]:
                    self.close_pos(p, p["stop"], ts, why); continue
                if high >= p["take"]:
                    self.close_pos(p, p["take"], ts, "vinstmål"); continue
            else:
                if high >= p["stop"]:
                    self.close_pos(p, p["stop"], ts, why); continue
                if low <= p["take"]:
                    self.close_pos(p, p["take"], ts, "vinstmål"); continue
            tr = self.s["params"].get(p["agent"], {}).get("trail", 0)
            ns = trail_stop(p["stop"], p["side"], high, low, tr)
            if ns != p["stop"]:
                p["stop"], p["moved"] = ns, True

    def record_equity(self, ts):
        eq = self.s["equity"]
        eq.append([ts, round(self.equity(), 2)])
        if len(eq) > 4000:  # gles ut gammal historik
            self.s["equity"] = eq[:2000:2] + eq[2000:]

    def reoptimize(self, window, ts, rnd):
        """window = {sym: (bars, inv, regime)} med de senaste OPT_WINDOW ljusen."""
        changed = 0
        for agent in AGENTS:
            inc = self.s["params"][agent]
            newp, old_s, new_s, switched = optimize_agent(agent, window, inc, rnd)
            paused = new_s < ACTIVE_SCORE
            if paused != self.s["paused"].get(agent, False):
                self.s["paused"][agent] = paused
                self.add_log(ts, f"{agent_name(agent)}: " + (
                    f"PAUSAD - inte tillräckligt lönsam just nu (poäng {new_s:.2f})" if paused else
                    f"AKTIV - visar vinst i testet (poäng {new_s:.2f})"))
            if switched:
                changed += 1
                self.s["params"][agent] = newp
                self.add_log(ts, f"{agent_name(agent)}: nya inställningar ({describe_params(newp)}) "
                                 f"- poäng {old_s:.2f} -> {new_s:.2f}")
        if changed == 0:
            self.add_log(ts, "Testade nya inställningar - de nuvarande är fortfarande bäst")
        self.s["last_reopt_ms"] = ts

    # --- statistik ---
    def stats(self):
        tr = self.s["trades"]
        n = len(tr)
        eq_now = self.equity()
        res = {"equity": eq_now, "pnl": eq_now - START_CAPITAL, "ret": eq_now / START_CAPITAL - 1,
               "n": n, "wins": sum(1 for t in tr if t["pnl"] > 0), "open": len(self.s["positions"])}
        res["winrate"] = res["wins"] / n if n else 0
        res["avg_pnl"] = sum(t["pnl"] for t in tr) / n if n else 0
        res["avg_ret"] = sum(t["ret"] for t in tr) / n if n else 0
        res["best"] = max(tr, key=lambda t: t["ret"]) if n else None
        res["worst"] = min(tr, key=lambda t: t["ret"]) if n else None
        gw = sum(t["pnl"] for t in tr if t["pnl"] > 0)
        gl = -sum(t["pnl"] for t in tr if t["pnl"] < 0)
        res["profit_factor"] = gw / gl if gl > 0 else (float("inf") if gw > 0 else 0)
        peak, mdd = START_CAPITAL, 0.0
        for _, e in self.s["equity"]:
            peak = max(peak, e)
            mdd = max(mdd, (peak - e) / peak)
        res["max_dd"] = mdd
        sp = self.s["start_prices"]
        bh = [self.prices[k] / sp[k] - 1 for k in sp if k in self.prices and sp[k]]
        res["buyhold"] = sum(bh) / len(bh) if bh else 0
        res["per_agent"], res["per_symbol"], res["per_side"] = {}, {}, {}
        for t in tr:
            for key, d in ((t["agent"], res["per_agent"]), (t["symbol"], res["per_symbol"]), (t["side"], res["per_side"])):
                x = d.setdefault(key, {"n": 0, "w": 0, "pnl": 0.0, "ret": 0.0})
                x["n"] += 1; x["w"] += t["pnl"] > 0; x["pnl"] += t["pnl"]; x["ret"] += t["ret"]
        return res


# ----------------------------------------------------------------------------
# RAPPORT (HTML)
# ----------------------------------------------------------------------------
def money(x):
    return f"{x:,.2f}".replace(",", " ")


def pct(x):
    return f"{x * 100:+.2f}%"


def cls(x):
    return "pos" if x > 0 else ("neg" if x < 0 else "")


def equity_svg(points):
    if len(points) < 2:
        return "<p class='muted'>Kurvan dyker upp när boten har kört en stund.</p>"
    W, H, P = 900, 260, 40
    xs = [p[0] for p in points]; ys = [p[1] for p in points]
    x0, x1 = min(xs), max(xs)
    y0, y1 = min(min(ys), START_CAPITAL), max(max(ys), START_CAPITAL)
    if y1 - y0 < 1:
        y0 -= 1; y1 += 1
    pad = (y1 - y0) * 0.08
    y0 -= pad; y1 += pad

    def X(v): return P + (v - x0) / max(x1 - x0, 1) * (W - 2 * P)
    def Y(v): return H - P + 10 - (v - y0) / (y1 - y0) * (H - 2 * P)
    path = " ".join(f"{'M' if i == 0 else 'L'}{X(a):.1f},{Y(b):.1f}" for i, (a, b) in enumerate(points))
    base = Y(START_CAPITAL)
    color = "#3fb68b" if ys[-1] >= START_CAPITAL else "#e5534b"
    return f"""<svg viewBox="0 0 {W} {H}" width="100%" preserveAspectRatio="none">
<line x1="{P}" y1="{base:.1f}" x2="{W - P}" y2="{base:.1f}" stroke="#555" stroke-dasharray="4 4"/>
<text x="{P}" y="{base - 6:.1f}" fill="#888" font-size="11">Start {money(START_CAPITAL)}</text>
<path d="{path}" fill="none" stroke="{color}" stroke-width="2"/>
<text x="{P}" y="{H - 6}" fill="#888" font-size="11">{fmt_ts(x0)}</text>
<text x="{W - P}" y="{H - 6}" fill="#888" font-size="11" text-anchor="end">{fmt_ts(x1)}</text>
<text x="{W - P}" y="{Y(ys[-1]) - 8:.1f}" fill="{color}" font-size="12" text-anchor="end">{money(ys[-1])}</text>
</svg>"""


def side_badge(side):
    return f"<span class='badge {side}'>{SIDE_TXT[side]}</span>"


def render_report(engine, path, title, subtitle, refresh=True):
    st = engine.stats()
    s = engine.s
    best, worst = st["best"], st["worst"]

    def trade_txt(t):
        if not t:
            return "-"
        return (f"<span class='{cls(t['ret'])}'>{pct(t['ret'])}</span> ({money(t['pnl'])} USDT)<br>"
                f"<small>{t['symbol']} · {agent_name(t['agent'])}</small>")

    def side_txt(side):
        d = st["per_side"].get(side, {"n": 0, "w": 0, "pnl": 0.0})
        return (f"<span class='{cls(d['pnl'])}'>{money(d['pnl'])} USDT</span>",
                f"<small>{d['n']} trades, {(d['w'] / d['n'] * 100 if d['n'] else 0):.0f}% vinster</small>")

    cards = [
        ("Kapital nu", f"{money(st['equity'])} USDT", ""),
        ("Resultat", f"<span class='{cls(st['pnl'])}'>{money(st['pnl'])} USDT ({pct(st['ret'])})</span>", ""),
        ("Om du bara köpt och hållit", f"<span class='{cls(st['buyhold'])}'>{pct(st['buyhold'])}</span>", "<small>samma mynt, lika mycket i varje</small>"),
        ("Antal trades", f"{st['n']}", f"<small>{st['open']} öppna just nu</small>"),
        ("Vinstandel", f"{st['winrate'] * 100:.1f}%", f"<small>{st['wins']} vinster / {st['n'] - st['wins']} förluster</small>"),
        ("Snitt per trade", f"<span class='{cls(st['avg_ret'])}'>{pct(st['avg_ret'])}</span>", f"<small>{money(st['avg_pnl'])} USDT</small>"),
        ("Bästa trade", trade_txt(best), ""),
        ("Sämsta trade", trade_txt(worst), ""),
        ("Största nedgång", f"<span class='neg'>{st['max_dd'] * 100:.2f}%</span>", "<small>från toppen</small>"),
        ("Vinstfaktor", "∞" if st["profit_factor"] == float("inf") else f"{st['profit_factor']:.2f}", "<small>&gt;1 = tjänar mer än förlorar</small>"),
        ("Långa (tjänar på uppgång)", *side_txt("long")),
    ]
    if ENABLE_SHORT:
        cards.append(("Korta (tjänar på nedgång)", *side_txt("short")))
    card_html = "".join(f"<div class='card'><div class='lbl'>{a}</div><div class='val'>{b}</div>{c}</div>" for a, b, c in cards)

    rows = ""
    for agent in AGENTS:
        strat, side = agent_parts(agent)
        d = st["per_agent"].get(agent, {"n": 0, "w": 0, "pnl": 0.0, "ret": 0.0})
        avg = d["ret"] / d["n"] if d["n"] else 0
        status = ("<span class=neg>Pausad</span>" if s["paused"].get(agent)
                  else f"x{engine.multiplier(agent):.2f}")
        rows += (f"<tr><td>{STRATEGIES[strat]['namn']}</td><td>{side_badge(side)}</td><td>{d['n']}</td>"
                 f"<td>{(d['w'] / d['n'] * 100 if d['n'] else 0):.0f}%</td>"
                 f"<td class='{cls(avg)}'>{pct(avg)}</td><td class='{cls(d['pnl'])}'>{money(d['pnl'])}</td>"
                 f"<td>{status}</td><td><small>{describe_params(s['params'][agent])}</small></td></tr>")

    symrows = ""
    for sym in SYMBOLS:
        d = st["per_symbol"].get(sym, {"n": 0, "w": 0, "pnl": 0.0})
        pr = engine.prices.get(sym)
        symrows += (f"<tr><td>{sym}</td><td>{d['n']}</td><td>{(d['w'] / d['n'] * 100 if d['n'] else 0):.0f}%</td>"
                    f"<td class='{cls(d['pnl'])}'>{money(d['pnl'])}</td><td>{f'{pr:.6g}' if pr else '-'}</td></tr>")

    posrows = ""
    for p in s["positions"]:
        cur = engine.prices.get(p["symbol"], p["entry"])
        r = trade_value(p["cost"], p["entry"], exit_price(cur, p["side"]), p["side"]) / p["cost"] - 1
        posrows += (f"<tr><td>{p['symbol']}</td><td>{side_badge(p['side'])}</td><td>{STRATEGIES[agent_parts(p['agent'])[0]]['namn']}</td>"
                    f"<td>{money(p['cost'])}</td><td>{p['entry']:.6g}</td><td>{cur:.6g}</td><td class='{cls(r)}'>{pct(r)}</td>"
                    f"<td>{p['stop']:.6g} / {p['take']:.6g}</td><td>{fmt_ts(p['ts'])}</td></tr>")
    if not posrows:
        posrows = "<tr><td colspan='9' class='muted'>Inga öppna positioner</td></tr>"

    trrows = ""
    for t in reversed(s["trades"][-50:]):
        trrows += (f"<tr><td>{fmt_ts(t['exit_ts'])}</td><td>{t['symbol']}</td><td>{side_badge(t['side'])}</td>"
                   f"<td>{STRATEGIES[agent_parts(t['agent'])[0]]['namn']}</td>"
                   f"<td class='{cls(t['ret'])}'>{pct(t['ret'])}</td><td class='{cls(t['pnl'])}'>{money(t['pnl'])}</td>"
                   f"<td>{t['reason']}</td></tr>")
    if not trrows:
        trrows = "<tr><td colspan='7' class='muted'>Inga avslutade trades än - boten väntar på bra lägen</td></tr>"

    logrows = "".join(f"<li><span class='muted'>{fmt_ts(l['ts'])}</span> {l['msg']}</li>" for l in reversed(s["learning_log"][-50:]))
    if not logrows:
        logrows = "<li class='muted'>Inget lärt än</li>"

    meta = "<meta http-equiv='refresh' content='60'>" if refresh else ""
    html = f"""<!DOCTYPE html><html lang="sv"><head><meta charset="utf-8">{meta}
<meta name="viewport" content="width=device-width,initial-scale=1"><title>{title}</title>
<style>
body{{background:#0f1115;color:#e6e6e6;font-family:Segoe UI,system-ui,sans-serif;margin:0;padding:24px;}}
h1{{margin:0 0 4px;font-size:24px}} h2{{font-size:17px;margin:28px 0 10px;color:#cfcfcf}}
.muted{{color:#888}} small{{color:#999}}
.grid{{display:grid;grid-template-columns:repeat(auto-fill,minmax(190px,1fr));gap:12px;margin-top:18px}}
.card{{background:#181b22;border:1px solid #262a33;border-radius:10px;padding:14px}}
.lbl{{color:#999;font-size:12px;text-transform:uppercase;letter-spacing:.04em}} .val{{font-size:19px;margin:6px 0 2px}}
.pos{{color:#3fb68b}} .neg{{color:#e5534b}}
.badge{{font-size:11px;padding:2px 7px;border-radius:9px}} .badge.long{{background:#173b2e;color:#5fd3a5}} .badge.short{{background:#40201f;color:#f08a84}}
.box{{background:#181b22;border:1px solid #262a33;border-radius:10px;padding:14px;overflow-x:auto}}
table{{border-collapse:collapse;width:100%;font-size:13px}} td,th{{padding:7px 9px;border-bottom:1px solid #262a33;text-align:left}}
th{{color:#999;font-weight:500}} ul{{margin:0;padding-left:18px;font-size:13px;line-height:1.7}}
.warn{{background:#2a2310;border:1px solid #5a4a1a;color:#e8c96a;padding:10px 14px;border-radius:8px;margin-top:14px;font-size:13px}}
</style></head><body>
<h1>{title}</h1><div class="muted">{subtitle}</div>
<div class="warn">Tidsram: {INTERVAL}-ljus. Papperstrading - inga riktiga pengar. Avgifter ({FEE * 100:.2f}%), slippage och finansieringskostnad för korta positioner är inräknade. Ingen hävstång. Tidigare resultat garanterar inget om framtiden.</div>
<div class="grid">{card_html}</div>
<h2>Kapital över tid</h2><div class="box">{equity_svg(s['equity'])}</div>
<h2>Strategier</h2><div class="box"><table><tr><th>Strategi</th><th>Sida</th><th>Trades</th><th>Vinst%</th><th>Snitt</th><th>Resultat USDT</th><th>Förtroende</th><th>Inställningar just nu</th></tr>{rows}</table></div>
<h2>Mynt</h2><div class="box"><table><tr><th>Mynt</th><th>Trades</th><th>Vinst%</th><th>Resultat USDT</th><th>Pris nu</th></tr>{symrows}</table></div>
<h2>Öppna positioner</h2><div class="box"><table><tr><th>Mynt</th><th>Sida</th><th>Strategi</th><th>Insats</th><th>In</th><th>Nu</th><th>Resultat</th><th>Stopp / mål</th><th>Sedan</th></tr>{posrows}</table></div>
<h2>Vad boten har lärt sig</h2><div class="box"><ul>{logrows}</ul></div>
<h2>Senaste trades</h2><div class="box"><table><tr><th>Stängd</th><th>Mynt</th><th>Sida</th><th>Strategi</th><th>Resultat</th><th>USDT</th><th>Varför</th></tr>{trrows}</table></div>
<p class="muted" style="margin-top:24px">Uppdaterad {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}</p>
</body></html>"""
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(html)
    os.replace(tmp, path)


def write_trades_csv(engine, path):
    with open(path, "w", encoding="utf-8") as f:
        f.write("stangd;oppnad;mynt;sida;strategi;in;ut;insats_usdt;resultat_usdt;resultat_procent;anledning\n")
        for t in engine.s["trades"]:
            f.write(f"{fmt_ts(t['exit_ts'])};{fmt_ts(t['entry_ts'])};{t['symbol']};{SIDE_TXT[t['side']]};"
                    f"{agent_parts(t['agent'])[0]};{t['entry']:.8g};{t['exit']:.8g};{t['cost']:.2f};"
                    f"{t['pnl']:.2f};{t['ret'] * 100:.3f};{t['reason']}\n")


def print_summary(engine, header):
    st = engine.stats()
    log(f"{header} | Kapital {money(st['equity'])} USDT ({pct(st['ret'])}) | Trades {st['n']} | "
        f"Vinst% {st['winrate'] * 100:.0f} | Öppna {st['open']} | Köp&håll {pct(st['buyhold'])}")


# ----------------------------------------------------------------------------
# BACKTEST  (samma motor + samma lärande, körs bara snabbare på historik)
# ----------------------------------------------------------------------------
def run_backtest(days=None, fake=False, tf=None, open_report=True):
    if tf:
        set_timeframe(tf)
    days = days or TIMEFRAMES[INTERVAL]["days"]
    report_path = os.path.join(HERE, f"backtest_rapport_{INTERVAL}.html")
    log(f"Backtest {INTERVAL}-ljus: hämtar {days:g} dagars prishistorik för {len(SYMBOLS)} mynt från Binance...")
    data = {}
    for i, sym in enumerate(SYMBOLS):
        if fake:
            data[sym] = fake_history(sym, int(days * 86400000 / BAR_MS), seed=i + 1)
        else:
            try:
                data[sym] = fetch_history(sym, days)
                log(f"  {sym}: {len(data[sym])} ljus")
            except Exception as e:
                log(f"  {sym}: kunde inte hämtas ({e}) - hoppar över")
    data = {k: v for k, v in data.items() if len(v) > OPT_WINDOW + 50}
    if not data:
        log("Ingen data - avbryter. Kolla internetanslutningen.")
        return None
    log("Kör testet (boten lär sig under tiden)...")

    btc = data.get(REGIME_SYMBOL)
    inv = {sym: b.inverted() for sym, b in data.items()}
    reg = {sym: regime_for(b, btc) for sym, b in data.items()}
    master = max(data.values(), key=len)
    idx = {sym: {t: i for i, t in enumerate(b.t)} for sym, b in data.items()}
    eng = Engine()
    rnd = random.Random(42)
    reopt_bars = int(REOPT_HOURS * 3600 * 1000 / BAR_MS)

    start_j = OPT_WINDOW
    eng.s["start_ms"] = master.t[start_j]
    for sym, b in data.items():
        i = idx[sym].get(master.t[start_j])
        if i is not None:
            eng.s["start_prices"][sym] = b.o[i]

    sigcache = {}
    seg_end_t = None
    total = len(master) - start_j
    for j in range(start_j, len(master)):
        t = master.t[j]
        if seg_end_t is None or t >= seg_end_t:
            window = {}
            for sym, b in data.items():
                i = idx[sym].get(t)
                if i is not None and i >= 200:
                    a = max(0, i - OPT_WINDOW)
                    window[sym] = (b.slice(a, i), inv[sym].slice(a, i), reg[sym][a:i])
            eng.reoptimize(window, t, rnd)
            seg_end_t = t + reopt_bars * BAR_MS
            sigcache, wins, starts = {}, {}, {}
            for sym, b in data.items():
                i = idx[sym].get(t)
                if i is None:
                    continue
                a = max(0, i - SIGNAL_WINDOW)
                e = min(len(b), i + reopt_bars + 1)
                wins[sym] = (b.slice(a, e), inv[sym].slice(a, e))
                starts[sym] = a
                eng.vols[sym] = daily_vol(b.slice(max(0, i - SIGNAL_WINDOW), i))
            sg = all_signals(wins, eng.s["params"])
            sigcache = {sym: (starts[sym], sg[sym]) for sym in wins}
        for sym, b in data.items():
            i = idx[sym].get(t)
            if i is None or i == 0 or sym not in sigcache:
                continue
            a, sigs = sigcache[sym]
            k = i - 1 - a
            if k < 0:
                continue
            eng.apply_signals(sym, {ag: sigs[ag][k] for ag in sigs}, b.o[i], t, reg[sym][i - 1])
            eng.check_exits(sym, b.h[i], b.l[i], t)
            eng.prices[sym] = b.c[i]
        eng.record_equity(t)
        done = j - start_j + 1
        if done % 2000 == 0:
            print_summary(eng, f"Backtest {done * 100 // total}%")

    print_summary(eng, f"BACKTEST {INTERVAL} KLAR")
    first, last = master.t[start_j], master.t[-1]
    learn_days = OPT_WINDOW * BAR_MS / 86400000
    render_report(eng, report_path, f"Backtest {INTERVAL} - krypto-boten",
                  f"Simulerad handel {fmt_ts(first)} till {fmt_ts(last)} (de första ~{learn_days:.0f} dygnen användes bara för att lära sig)",
                  refresh=False)
    log(f"Rapport sparad: {report_path}")
    if open_report:
        open_in_browser(report_path)
    eng.first_last = (first, last)
    return eng


def run_compare(fake=False):
    """Kör backtest på alla tidsramar och visar vilken som håller bäst."""
    results = []
    for tf in COMPARE_TIMEFRAMES:
        t0 = time.time()
        eng = run_backtest(fake=fake, tf=tf, open_report=False)
        if eng is None:
            continue
        st = eng.stats()
        results.append((tf, st, eng.first_last, time.time() - t0))
    rows = ""
    for tf, st, (a, b), secs in results:
        pf = "∞" if st["profit_factor"] == float("inf") else f"{st['profit_factor']:.2f}"
        rows += (f"<tr><td><a href='backtest_rapport_{tf}.html'>{tf}</a></td><td>{fmt_ts(a)[:10]} – {fmt_ts(b)[:10]}</td>"
                 f"<td class='{cls(st['ret'])}'>{pct(st['ret'])}</td><td class='{cls(st['buyhold'])}'>{pct(st['buyhold'])}</td>"
                 f"<td>{st['n']}</td><td>{st['winrate'] * 100:.0f}%</td><td>{pf}</td><td class='neg'>{st['max_dd'] * 100:.1f}%</td></tr>")
        log(f"{tf:>4}: resultat {pct(st['ret'])} | köp&håll {pct(st['buyhold'])} | {st['n']} trades | "
            f"vinstfaktor {pf} | största nedgång {st['max_dd'] * 100:.1f}%")
    html = f"""<!DOCTYPE html><html lang="sv"><head><meta charset="utf-8"><title>Jämförelse tidsramar</title>
<style>body{{background:#0f1115;color:#e6e6e6;font-family:Segoe UI,system-ui,sans-serif;padding:24px}}
table{{border-collapse:collapse;width:100%;font-size:14px;background:#181b22}} td,th{{padding:9px;border-bottom:1px solid #262a33;text-align:left}}
th{{color:#999;font-weight:500}} a{{color:#7cb7ff}} .pos{{color:#3fb68b}} .neg{{color:#e5534b}} .muted{{color:#888}}</style></head><body>
<h1>Vilken tidsram funkar bäst?</h1>
<p class="muted">Samma bot och samma lärande, olika ljuslängd. Klicka på en tidsram för hela rapporten.
Bra tecken: plus, slår köp-och-håll, vinstfaktor över 1,2, liten nedgång och många trades.</p>
<table><tr><th>Tidsram</th><th>Handlade period</th><th>Resultat</th><th>Köp &amp; håll</th><th>Trades</th><th>Vinst%</th><th>Vinstfaktor</th><th>Största nedgång</th></tr>{rows}</table>
<p class="muted">Skapad {datetime.now().strftime('%Y-%m-%d %H:%M')}</p></body></html>"""
    # välj bästa tidsram för live: måste gå plus, slå köp&håll och ha vinstfaktor > 1,2
    ok = [(st["ret"], tf) for tf, st, _, _ in results
          if st["ret"] > 0 and st["ret"] > st["buyhold"] and st["profit_factor"] > 1.2 and st["n"] >= 30]
    if ok:
        best = max(ok)[1]
        verdict = (f"<p class='pos'><b>Bäst: {best}.</b> Live-läget (1_STARTA_BOTEN) använder nu {best}-ljus.</p>")
        try:
            with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
                json.dump({"timeframe": best, "valt": datetime.now().isoformat()}, f)
        except Exception:
            pass
        log(f"BÄST: {best} - live-läget använder nu den tidsramen.")
    else:
        verdict = ("<p class='neg'><b>Ingen tidsram klarade kraven</b> (plus, slår köp-och-håll, vinstfaktor över 1,2, minst 30 trades). "
                   "Kör inte med riktiga pengar. Papperstrading går bra för att se mer.</p>")
        log("Ingen tidsram klarade kraven än - använd bara papperspengar.")
    html = html.replace("<p class=\"muted\">Skapad", verdict + "<p class=\"muted\">Skapad")
    path = os.path.join(HERE, "jamforelse.html")
    with open(path, "w", encoding="utf-8") as f:
        f.write(html)
    log(f"Jämförelse sparad: {path}")
    open_in_browser(path)


# ----------------------------------------------------------------------------
# LIVE PAPPERSTRADING
# ----------------------------------------------------------------------------
def keep_awake():
    """Hindrar Windows från att somna medan boten kör (skärmen får släckas)."""
    if os.name == "nt":
        try:
            import ctypes
            ctypes.windll.kernel32.SetThreadExecutionState(0x80000000 | 0x00000001)
            log("Datorn hålls vaken så länge boten kör.")
        except Exception:
            pass


def open_in_browser(path):
    if os.environ.get("BOT_NO_BROWSER"):
        return
    try:
        webbrowser.open("file:///" + path.replace("\\", "/"))
    except Exception:
        pass


def load_state():
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE, encoding="utf-8") as f:
                st = json.load(f)
            if st.get("version") == STATE_VERSION and st.get("timeframe") == INTERVAL:
                return st
            if st.get("version") == STATE_VERSION:
                log(f"Sparfilen gäller en annan tidsram ({st.get('timeframe')}) - startar om på {INTERVAL}")
                return None
            log("Gammal sparfil från en äldre version - startar om från noll")
        except Exception as e:
            log(f"Kunde inte läsa state.json ({e}) - startar om från noll")
    return None


def save_state(engine):
    tmp = STATE_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(engine.s, f)
    os.replace(tmp, STATE_FILE)


def run_live():
    keep_awake()
    state = load_state()
    eng = Engine(state)
    rnd = random.Random()
    if state:
        log(f"Fortsätter där boten slutade (startade {fmt_ts(eng.s['start_ms'])}, {len(eng.s['trades'])} trades hittills)")
    else:
        log(f"Ny start med {money(START_CAPITAL)} låtsas-USDT")
    log(f"Rapport: {REPORT_FILE}  (öppnas i webbläsaren)")
    log("Stäng fönstret eller tryck Ctrl+C för att stoppa. Allt sparas och fortsätter vid nästa start.")

    last_summary = 0
    errors = 0
    opened = False
    fetch_err = {}
    live_hist = {}
    while True:
        loop_start = time.time()
        now = int(loop_start * 1000)
        try:
            closed_by_sym = {}
            for sym in SYMBOLS:
                try:
                    h = live_hist.get(sym)
                    if h is None or now >= h.t[-1] + 2 * BAR_MS:   # nytt stängt ljus finns
                        need_days = max(SIGNAL_WINDOW, OPT_WINDOW) * BAR_MS / 86400000 + 2
                        h = fetch_history(sym, need_days)
                        live_hist[sym] = h
                    b = fetch_klines(sym, 2)
                except Exception as e:
                    if time.time() - fetch_err.get(sym, 0) > 3600:
                        log(f"  {sym}: kunde inte hämtas just nu ({e}) - hoppar över tills vidare")
                        fetch_err[sym] = time.time()
                    continue
                if len(h) < 300 or len(b) == 0:
                    continue
                closed_by_sym[sym] = h
                eng.vols[sym] = daily_vol(h)
                eng.prices[sym] = b.c[-1]
                if sym not in eng.s["start_prices"]:
                    eng.s["start_prices"][sym] = b.c[-1]
            if eng.s["start_ms"] is None:
                eng.s["start_ms"] = now
            btc = closed_by_sym.get(REGIME_SYMBOL)
            invs = {sym: b.inverted() for sym, b in closed_by_sym.items()}
            regs = {sym: regime_for(b, btc) for sym, b in closed_by_sym.items()}

            if now - eng.s["last_reopt_ms"] >= REOPT_HOURS * 3600 * 1000 and closed_by_sym:
                log("Lär sig: testar nya inställningar på de senaste dygnens data...")
                n_before = len(eng.s["learning_log"])
                window = {}
                for sym, h in closed_by_sym.items():
                    w = h.slice(max(0, len(h) - OPT_WINDOW), len(h))
                    window[sym] = (w, w.inverted(), regime_for(w, closed_by_sym.get(REGIME_SYMBOL)))
                eng.reoptimize(window, now, rnd)
                for l in eng.s["learning_log"][n_before:]:
                    log("  " + l["msg"])

            wins = {}
            for sym, closed in closed_by_sym.items():
                a = max(0, len(closed) - SIGNAL_WINDOW)
                wins[sym] = (closed.slice(a, len(closed)), invs[sym].slice(a, len(closed)))
            live_sigs = all_signals(wins, eng.s["params"])
            for sym, closed in closed_by_sym.items():
                last_t = closed.t[-1]
                if eng.s["last_bar"].get(sym) != last_t:
                    sigs = {ag: live_sigs[sym][ag][-1] for ag in AGENTS}
                    before = len(eng.s["trades"])
                    before_ids = {p["id"] for p in eng.s["positions"]}
                    first_time = sym not in eng.s["last_bar"]
                    eng.s["last_bar"][sym] = last_t
                    if not first_time:  # handla inte på gammal signal direkt vid start
                        eng.apply_signals(sym, sigs, eng.prices[sym], now, regs[sym][-1])
                    for t in eng.s["trades"][before:]:
                        log(f"  STÄNGD {SIDE_TXT[t['side']]:4} {sym} ({agent_parts(t['agent'])[0]}) {pct(t['ret'])}  {money(t['pnl'])} USDT")
                    for p in eng.s["positions"]:
                        if p["id"] not in before_ids:
                            log(f"  ÖPPNAD {SIDE_TXT[p['side']]:4} {sym} ({agent_parts(p['agent'])[0]}) för {money(p['cost'])} USDT @ {p['entry']:.6g}")
                before = len(eng.s["trades"])
                eng.check_exits(sym, eng.prices[sym], eng.prices[sym], now)
                for t in eng.s["trades"][before:]:
                    log(f"  STÄNGD {SIDE_TXT[t['side']]:4} {sym} ({agent_parts(t['agent'])[0]}, {t['reason']}) {pct(t['ret'])}  {money(t['pnl'])} USDT")

            eng.record_equity(now)
            save_state(eng)
            render_report(eng, REPORT_FILE, "Krypto-boten - live papperstrading",
                          f"Igång sedan {fmt_ts(eng.s['start_ms'])} · uppdateras automatiskt varje minut")
            write_trades_csv(eng, TRADES_CSV)
            if not opened:
                open_in_browser(REPORT_FILE)
                opened = True
            if time.time() - last_summary > 300:
                print_summary(eng, "Status")
                last_summary = time.time()
            errors = 0
        except KeyboardInterrupt:
            raise
        except Exception as e:
            errors += 1
            log(f"Problem ({e}). Försöker igen strax...")
            time.sleep(min(300, 15 * errors))
        time.sleep(max(1, POLL_SECONDS - (time.time() - loop_start)))


# ----------------------------------------------------------------------------
# ============================================================================
# ENKEL TRENDMODELL (fasta regler från forskningen - ingen omjustering)
# ============================================================================
# Varje dag: för varje mynt räknas hur många av perioderna 7/14/28/56 dagar som
# gått upp. Signal = andel upp minus andel ner (-1 .. +1). Insats styrs av hur
# mycket myntet svänger. Handlar bara när målvikten ändrats tydligt.
TREND_LOOKBACKS = [7, 14, 28, 56]
TREND_VOL_TARGET = 0.005     # varje mynt får svänga ~0,5 % av kapitalet per dag vid full signal
TREND_MAX_W = 0.25           # max 25 % av kapitalet i ett mynt
TREND_MAX_GROSS = 1.0        # aldrig mer än 100 % totalt (ingen hävstång)
TREND_MIN_TRADE = 0.03       # handla bara om vikten ändras mer än 3 procentenheter
TREND_STATE_FILE = os.path.join(HERE, "trend_state.json")
TREND_REPORT = os.path.join(HERE, "trend_rapport.html")


def trend_signal(c, i):
    L = TREND_LOOKBACKS
    if i < L[-1]:
        return None
    ups = sum(1 for d in L if c[i] > c[i - d])
    return (2 * ups - len(L)) / len(L)


def trend_vol(c, i, n=30):
    if i < n + 1:
        return None
    r = [c[k] / c[k - 1] - 1 for k in range(i - n + 1, i + 1)]
    m = sum(r) / n
    return max(1e-4, math.sqrt(sum((x - m) ** 2 for x in r) / n))


def trend_targets(data, idx, t, mode):
    """Målvikter per mynt vid dagens stängning t. mode: 'long' eller 'longshort'."""
    raw = {}
    for sym, b in data.items():
        i = idx[sym].get(t)
        if i is None:
            continue
        s = trend_signal(b.c, i)
        v = trend_vol(b.c, i)
        if s is None or v is None:
            continue
        if mode == "long":
            s = max(0.0, s)
        raw[sym] = max(-TREND_MAX_W, min(TREND_MAX_W, s * TREND_VOL_TARGET / v))
    gross = sum(abs(w) for w in raw.values())
    if gross > TREND_MAX_GROSS:
        raw = {k: w * TREND_MAX_GROSS / gross for k, w in raw.items()}
    return raw


def trend_simulate(data, mode, start_t=None):
    """Simulerar portföljen dag för dag. Returnerar dict med kurva, trades och statistik."""
    master = max(data.values(), key=len)
    idx = {s: {t: i for i, t in enumerate(b.t)} for s, b in data.items()}
    eq = START_CAPITAL
    w = {}            # nuvarande vikter
    curve, trades, costs = [], 0, 0.0
    cost_rate = FEE + SLIPPAGE
    funding_day = SHORT_FUNDING_8H * 3 * BAR_MS / 86400000   # per ljus
    for j in range(1, len(master)):
        t_prev, t = master.t[j - 1], master.t[j]
        if start_t and t < start_t:
            continue
        # 1) avkastning under dagen j för vikterna vi höll
        pnl = 0.0
        for sym, wt in w.items():
            b = data[sym]
            i = idx[sym].get(t)
            if i is None or i == 0:
                continue
            r = b.c[i] / b.c[i - 1] - 1
            pnl += wt * r
            if wt < 0:
                pnl -= abs(wt) * funding_day
        eq *= (1 + pnl)
        # 2) nya målvikter från dagens stängning, handla till stängningskurs + kostnad
        tgt = trend_targets(data, idx, t, mode)
        for sym in set(w) | set(tgt):
            new, old = tgt.get(sym, 0.0), w.get(sym, 0.0)
            # vikten har drivit med priset under dagen - räkna det som gammal vikt (förenkling)
            if abs(new - old) > TREND_MIN_TRADE or (new == 0 and old != 0):
                c = abs(new - old) * cost_rate * eq
                eq -= c
                costs += c
                trades += 1
                w[sym] = new
        w = {k: v for k, v in w.items() if v != 0}
        curve.append([t, eq])
    return {"curve": curve, "trades": trades, "costs": costs, "weights": w}


def curve_stats(curve):
    if len(curve) < 2:
        return {}
    e0, e1 = START_CAPITAL, curve[-1][1]
    days = (curve[-1][0] - curve[0][0]) / 86400000
    rets = [curve[i][1] / curve[i - 1][1] - 1 for i in range(1, len(curve))]
    m = sum(rets) / len(rets)
    sd = math.sqrt(sum((r - m) ** 2 for r in rets) / len(rets)) or 1e-9
    peak, mdd = e0, 0.0
    for _, e in curve:
        peak = max(peak, e)
        mdd = max(mdd, (peak - e) / peak)
    cagr = (e1 / e0) ** (365 / max(days, 1)) - 1 if e1 > 0 else -1
    return {"ret": e1 / e0 - 1, "cagr": cagr, "sharpe": m / sd * math.sqrt(365), "mdd": mdd, "end": e1}


def year_returns(curve):
    out, start = {}, None
    for t, e in curve:
        y = datetime.fromtimestamp(t / 1000).year
        if y not in out:
            out[y] = [start if start else START_CAPITAL, e]
        out[y][1] = e
        start = e
    return {y: v[1] / v[0] - 1 for y, v in out.items()}


def buyhold_curve(data, start_t):
    """Lika mycket i varje mynt som finns, ombalanseras varje dag (för rättvis jämförelse)."""
    master = max(data.values(), key=len)
    idx = {s: {t: i for i, t in enumerate(b.t)} for s, b in data.items()}
    eq, curve = START_CAPITAL, []
    for j in range(1, len(master)):
        t = master.t[j]
        if t < start_t:
            continue
        rs = []
        for sym, b in data.items():
            i = idx[sym].get(t)
            if i and i > 0:
                rs.append(b.c[i] / b.c[i - 1] - 1)
        if rs:
            eq *= 1 + sum(rs) / len(rs)
        curve.append([t, eq])
    return curve


def multi_svg(series):
    """series = [(namn, färg, kurva)] -> SVG med logaritmisk skala."""
    allp = [p for _, _, c in series for p in c]
    if len(allp) < 2:
        return ""
    W, H, P = 900, 300, 50
    x0, x1 = min(p[0] for p in allp), max(p[0] for p in allp)
    ys = [math.log(max(p[1], 1)) for p in allp]
    y0, y1 = min(ys), max(ys)
    if y1 - y0 < 0.01:
        y1 += 0.01

    def X(v): return P + (v - x0) / max(1, x1 - x0) * (W - 2 * P)
    def Y(v): return H - P + 10 - (math.log(max(v, 1)) - y0) / (y1 - y0) * (H - 2 * P)
    out = [f'<svg viewBox="0 0 {W} {H}" width="100%">']
    base = Y(START_CAPITAL)
    out.append(f'<line x1="{P}" y1="{base:.1f}" x2="{W - P}" y2="{base:.1f}" stroke="#555" stroke-dasharray="4 4"/>')
    for k, (name, col, c) in enumerate(series):
        step = max(1, len(c) // 900)
        pts = c[::step] + [c[-1]]
        d = " ".join(f"{'M' if i == 0 else 'L'}{X(a):.1f},{Y(b):.1f}" for i, (a, b) in enumerate(pts))
        out.append(f'<path d="{d}" fill="none" stroke="{col}" stroke-width="2"/>')
        out.append(f'<text x="{P + 10}" y="{20 + 16 * k}" fill="{col}" font-size="13">{name}: {money(c[-1][1])}</text>')
    out.append(f'<text x="{P}" y="{H - 8}" fill="#888" font-size="11">{fmt_ts(x0)[:10]}</text>')
    out.append(f'<text x="{W - P}" y="{H - 8}" fill="#888" font-size="11" text-anchor="end">{fmt_ts(x1)[:10]}</text>')
    out.append("</svg>")
    return "".join(out)


def run_trend_backtest(years=5.5, fake=False):
    global TREND_LOOKBACKS, TREND_MIN_TRADE, TREND_VOL_TARGET
    set_timeframe("1d")
    days = years * 365
    log(f"Trendmodell: hämtar {days:.0f} dagars dagsdata för {len(SYMBOLS)} mynt...")
    data = {}
    for i, sym in enumerate(SYMBOLS):
        try:
            data[sym] = fake_history(sym, int(days), seed=i + 1) if fake else fetch_history(sym, days)
            log(f"  {sym}: {len(data[sym])} dagar")
        except Exception as e:
            log(f"  {sym}: kunde inte hämtas ({e}) - hoppar över")
    data = {k: v for k, v in data.items() if len(v) > 80}
    if REGIME_SYMBOL not in data:
        log("Fick ingen BTC-data - avbryter. Kolla internet.")
        return
    start_t = data[REGIME_SYMBOL].t[TREND_LOOKBACKS[-1] + 31]
    res = {m: trend_simulate(data, m, start_t) for m in ("long", "longshort")}
    bh = buyhold_curve(data, start_t)
    stats = {"long": curve_stats(res["long"]["curve"]), "longshort": curve_stats(res["longshort"]["curve"]),
             "bh": curve_stats(bh)}
    yrs = {"long": year_returns(res["long"]["curve"]), "longshort": year_returns(res["longshort"]["curve"]),
           "bh": year_returns(bh)}
    names = {"long": "Trend, bara lång", "longshort": "Trend, lång + kort", "bh": "Köp & håll (lika i alla)"}
    for k in ("long", "longshort", "bh"):
        s = stats[k]
        log(f"{names[k]:26}: {pct(s['ret'])} totalt | {pct(s['cagr'])}/år | Sharpe {s['sharpe']:.2f} | "
            f"största nedgång {s['mdd'] * 100:.0f}%")

    def cell(x):
        return f"<td class='{cls(x)}'>{pct(x)}</td>"
    # känslighetstest: samma idé, lite andra regler. Bra modell = de flesta varianter går bra.
    orig = (TREND_LOOKBACKS, TREND_MIN_TRADE, TREND_VOL_TARGET)
    variants = [("Perioder 5/10/20/40 dagar", [5, 10, 20, 40], orig[1], orig[2]),
                ("Perioder 10/20/40/80 dagar", [10, 20, 40, 80], orig[1], orig[2]),
                ("Perioder 14/28/56/112 dagar", [14, 28, 56, 112], orig[1], orig[2]),
                ("Färre affärer (min 6 %-enheter)", orig[0], 0.06, orig[2]),
                ("Mindre insats (hälften)", orig[0], orig[1], orig[2] / 2),
                ("Större insats (dubbel)", orig[0], orig[1], orig[2] * 2)]
    vrows = ""
    for name, lb, mt, vt in variants:
        TREND_LOOKBACKS, TREND_MIN_TRADE, TREND_VOL_TARGET = lb, mt, vt
        st_ = curve_stats(trend_simulate(data, "long", start_t)["curve"])
        vrows += (f"<tr><td>{name}</td>{cell(st_['ret'])}{cell(st_['cagr'])}<td>{st_['sharpe']:.2f}</td>"
                  f"<td class='neg'>{st_['mdd'] * 100:.0f}%</td></tr>")
        log(f"  Variant {name:32}: {pct(st_['ret'])} | Sharpe {st_['sharpe']:.2f} | nedgång {st_['mdd'] * 100:.0f}%")
    TREND_LOOKBACKS, TREND_MIN_TRADE, TREND_VOL_TARGET = orig
    rows = ""
    for k in ("long", "longshort", "bh"):
        s = stats[k]
        tr = res[k]["trades"] if k in res else "-"
        cost = money(res[k]["costs"]) if k in res else "-"
        rows += (f"<tr><td>{names[k]}</td>{cell(s['ret'])}{cell(s['cagr'])}<td>{s['sharpe']:.2f}</td>"
                 f"<td class='neg'>{s['mdd'] * 100:.0f}%</td><td>{tr}</td><td>{cost}</td></tr>")
    all_years = sorted(set().union(*[set(v) for v in yrs.values()]))
    yrows = "".join(f"<tr><td>{y}</td>" + "".join(cell(yrs[k].get(y, 0)) for k in ("long", "longshort", "bh")) + "</tr>"
                    for y in all_years)
    w = res["longshort"]["weights"]
    wl = res["long"]["weights"]
    wrows = "".join(f"<tr><td>{s}</td><td class='{cls(wl.get(s, 0))}'>{wl.get(s, 0) * 100:.1f}%</td>"
                    f"<td class='{cls(w.get(s, 0))}'>{w.get(s, 0) * 100:+.1f}%</td></tr>" for s in data)
    svg = multi_svg([(names["long"], "#3fb68b", res["long"]["curve"]),
                     (names["longshort"], "#7cb7ff", res["longshort"]["curve"]),
                     (names["bh"], "#e8c96a", bh)])
    html = f"""<!DOCTYPE html><html lang="sv"><head><meta charset="utf-8"><title>Trendmodell - backtest</title>
<style>body{{background:#0f1115;color:#e6e6e6;font-family:Segoe UI,system-ui,sans-serif;padding:24px;max-width:1000px}}
h2{{font-size:17px;margin-top:28px}} .box{{background:#181b22;border:1px solid #262a33;border-radius:10px;padding:14px;overflow-x:auto}}
table{{border-collapse:collapse;width:100%;font-size:14px}} td,th{{padding:8px;border-bottom:1px solid #262a33;text-align:left}}
th{{color:#999;font-weight:500}} .pos{{color:#3fb68b}} .neg{{color:#e5534b}} .muted{{color:#888}}
.warn{{background:#2a2310;border:1px solid #5a4a1a;color:#e8c96a;padding:10px 14px;border-radius:8px;font-size:13px}}</style></head><body>
<h1>Enkel trendmodell - {fmt_ts(start_t)[:10]} till {fmt_ts(res['long']['curve'][-1][0])[:10]}</h1>
<p class="muted">Fasta regler från forskningen (inga inställningar har justerats efter resultatet). Dagsdata, handel en gång per dygn.
Avgift {FEE * 100:.2f}% + slippage {SLIPPAGE * 100:.2f}% per affär, finansiering för korta positioner inräknad. Ingen hävstång.</p>
<div class="warn">Papperstest på historik. Det visar hur reglerna hade gått - inte vad som händer framåt.</div>
<h2>Kapital över tid (logaritmisk skala, start 10 000)</h2><div class="box">{svg}</div>
<h2>Sammanfattning</h2><div class="box"><table><tr><th></th><th>Totalt</th><th>Per år</th><th>Sharpe</th><th>Största nedgång</th><th>Affärer</th><th>Kostnader USDT</th></tr>{rows}</table>
<p class="muted">Sharpe = avkastning delat med risk. Över 1 är bra, över 2 är mycket ovanligt.</p></div>
<h2>Känslighetstest (bara lång) - håller det om reglerna ändras lite?</h2><div class="box"><table><tr><th>Variant</th><th>Totalt</th><th>Per år</th><th>Sharpe</th><th>Största nedgång</th></tr>{vrows}</table>
<p class="muted">Om bara en exakt inställning fungerar är det troligen tur. Om de flesta varianter går bra är idén mer pålitlig.</p></div>
<h2>År för år</h2><div class="box"><table><tr><th>År</th><th>Trend, lång</th><th>Trend, lång + kort</th><th>Köp &amp; håll</th></tr>{yrows}</table></div>
<h2>Vikter just nu (vad modellen skulle hålla idag)</h2><div class="box"><table><tr><th>Mynt</th><th>Bara lång</th><th>Lång + kort</th></tr>{wrows}</table></div>
<p class="muted">Skapad {datetime.now().strftime('%Y-%m-%d %H:%M')}</p></body></html>"""
    with open(TREND_REPORT, "w", encoding="utf-8") as f:
        f.write(html)
    log(f"Rapport sparad: {TREND_REPORT}")
    open_in_browser(TREND_REPORT)
    return res, stats



# ============================================================================
# NYHETSVAKT - läser krypto-rubriker och marknadens rädsla/girighet
# ============================================================================
# Forskningen: nyheter påverkar priset, men är svåra att tjäna pengar på direkt.
# Därför används de som SKYDD: riktigt dåliga nyheter om ett mynt (hack, stämning,
# avnotering...) gör att boten säljer/undviker myntet ett tag.
NEWS_FEEDS = ["https://www.coindesk.com/arc/outboundfeeds/rss/", "https://cointelegraph.com/rss",
              "https://decrypt.co/feed"]
NEWS_EVERY_MIN = 10
NEWS_BLOCK_HOURS = 48
COIN_WORDS = {"BTCUSDT": ["bitcoin", "btc"], "ETHUSDT": ["ethereum", "ether ", "eth "], "SOLUSDT": ["solana", " sol "],
              "BNBUSDT": ["bnb", "binance coin"], "XRPUSDT": ["xrp", "ripple"], "DOGEUSDT": ["dogecoin", "doge"],
              "PEPEUSDT": ["pepe"], "WIFUSDT": ["dogwifhat", " wif "], "BONKUSDT": ["bonk"],
              "ADAUSDT": ["cardano", " ada "], "AVAXUSDT": ["avalanche", "avax"], "LINKUSDT": ["chainlink"],
              "SUIUSDT": [" sui ", "sui network"], "SHIBUSDT": ["shiba inu", "shib"], "FLOKIUSDT": ["floki"]}
BAD_WORDS = ["hack", "exploit", "stolen", "drained", "lawsuit", "sues ", "sued", "delist", "ban ", "bans ", "banned",
             "bankrupt", "insolven", "fraud", "rug pull", "halts withdrawals", "suspends withdrawals", "outage", "vulnerability"]
MARKET_BAD = ["crash", "liquidations", "sell-off", "selloff", "plunge", "capitulation", "emergency"]
GOOD_WORDS = ["approve", "approval", "etf inflow", "record high", "all-time high", "partnership", "adopt", "upgrade", "listing"]


def fetch_text(url, timeout=15):
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 paper-bot"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read().decode("utf-8", errors="replace")


def read_headlines():
    import xml.etree.ElementTree as ET
    out = []
    for url in NEWS_FEEDS:
        try:
            root = ET.fromstring(fetch_text(url))
            for it in root.iter("item"):
                title = (it.findtext("title") or "").strip()
                link = (it.findtext("link") or "").strip()
                if title:
                    out.append({"title": title, "link": link, "src": url.split("/")[2]})
        except Exception:
            continue
    return out[:150]


NOT_THE_COIN = ["mercado bitcoin", "bitcoin.com", "bitcoin depot", "bitcoin suisse", "bitcoin magazine",
                "ethereum foundation grant", "solana foundation grant"]
BIG_COINS = ["BTCUSDT", "ETHUSDT"]          # påverkas sällan av hack hos andra - spärras bara vid förbud/avnotering
BIG_COIN_BAD = ["ban ", "bans ", "banned", "delist"]


def score_headline(title):
    t = " " + title.lower() + " "
    for phrase in NOT_THE_COIN:
        t = t.replace(phrase, " ")
    coins = [s for s, words in COIN_WORDS.items() if any(w in t for w in words)]
    bad = any(w in t for w in BAD_WORDS)
    mbad = any(w in t for w in MARKET_BAD)
    good = any(w in t for w in GOOD_WORDS)
    return coins, (-2 if bad else (-1 if mbad else (1 if good else 0)))


TRUMP_FEED = "https://www.trumpstruth.org/feed"
RISK_OFF_WORDS = ["tariff", "sanctions on", "new sanctions", "declare war", "declared war", "go to war",
                  "invade", "invasion of", "military strike", "airstrike", "embargo", "trade war",
                  "martial law", "nuclear strike", "nuclear weapon", "ban crypto", "ban bitcoin"]
RISK_OFF_IGNORE = ["secretary of war", "department of war", "war room", "warrant"]
RISK_OFF_HOURS = 6
MUSK_HOURS = 24


def social_check(st, now):
    """Social media-vakt: Trumps inlägg (Truth Social-arkiv) och Musk i nyhetsrubrikerna.
    Påverkar bara risken - öppnar aldrig affärer själv."""
    import xml.etree.ElementTree as ET
    soc = st.setdefault("social", {"risk_off_until": 0, "reason": "", "no_short": {}, "seen": []})
    seen = set(soc.get("seen", []))
    try:
        root = ET.fromstring(fetch_text(TRUMP_FEED))
        for it in list(root.iter("item"))[:20]:
            txt = ((it.findtext("title") or "") + " " + (it.findtext("description") or "")).strip()
            key = (it.findtext("guid") or it.findtext("link") or txt[:80])
            if not txt or key in seen:
                continue
            seen.add(key)
            low = " " + txt.lower() + " "
            for ign in RISK_OFF_IGNORE:
                low = low.replace(ign, " ")
            if any(w in low for w in RISK_OFF_WORDS):
                soc["risk_off_until"] = now + RISK_OFF_HOURS * 3600 * 1000
                soc["reason"] = "Trump: " + re.sub(r"<[^>]+>", " ", txt)[:120].strip()
                log(f"  SOCIAL VAKT: Trump-inlägg kan skaka marknaden -> minskar risken i {RISK_OFF_HOURS} h: {soc['reason']}")
    except Exception as e:
        log(f"  Social vakt: kunde inte läsa Trumps inlägg ({e})")
    for h in st.get("news", [])[:40]:
        low = " " + h["title"].lower() + " "
        if ("musk" in low or "elon" in low) and h.get("ts", 0) > now - MUSK_HOURS * 3600 * 1000:
            for c in h.get("coins", []) or (["DOGEUSDT"] if "doge" in low else []):
                if soc["no_short"].get(c, 0) < now:
                    log(f"  SOCIAL VAKT: Musk nämner {c} -> blankar inte {c} i {MUSK_HOURS} h")
                soc["no_short"][c] = now + MUSK_HOURS * 3600 * 1000
    soc["no_short"] = {c: u for c, u in soc["no_short"].items() if u > now}
    soc["seen"] = list(seen)[-300:]


def risk_off(st, now):
    return st.get("social", {}).get("risk_off_until", 0) > now


def fear_greed():
    try:
        d = json.loads(fetch_text("https://api.alternative.me/fng/?limit=1"))["data"][0]
        return int(d["value"]), d["value_classification"]
    except Exception:
        return None, None


def news_check(st, now):
    """Uppdaterar st['news'] och st['blocked'] (mynt -> spärrat till tid)."""
    heads = read_headlines()
    seen = set(st.setdefault("news_seen", []))
    blocked = st.setdefault("blocked", {})
    new_items = []
    for h in heads:
        if h["title"] in seen:
            continue
        coins, sc = score_headline(h["title"])
        h.update({"ts": now, "coins": coins, "score": sc})
        new_items.append(h)
        seen.add(h["title"])
        if sc <= -2:
            low = " " + h["title"].lower() + " "
            for c in coins:
                if c in BIG_COINS and not any(w in low for w in BIG_COIN_BAD):
                    continue
                blocked[c] = now + NEWS_BLOCK_HOURS * 3600 * 1000
                log(f"  NYHETSVAKT: dålig nyhet om {c} -> undviker i {NEWS_BLOCK_HOURS} h: {h['title'][:90]}")
    st["news_seen"] = list(seen)[-600:]
    st["news"] = (new_items + st.get("news", []))[:60]
    for c in [c for c, until in blocked.items() if until < now]:
        del blocked[c]
    v, txt = fear_greed()
    if v is not None:
        st["fng"] = [v, txt]
    social_check(st, now)
    return len(heads)


def run_trend_recent(fake=False):
    """Testar trendmodellen bara på senaste tiden: 30/90/180/365 dagar.
    Två versioner: dagsljus (som live-boten) och timljus (kortsiktig trend)."""
    global TREND_LOOKBACKS, TREND_VOL_TARGET
    periods = [30, 90, 180, 365]
    versions = [("Trend dag (live-boten)", "1d", [7, 14, 28, 56], 0.005, 400),
                ("Trend timme (kortsiktig)", "1h", [12, 24, 48, 96], 0.005 / math.sqrt(24), 370)]
    orig = (TREND_LOOKBACKS, TREND_VOL_TARGET)
    table = {}
    bh_done = {}
    for name, tf, lb, vt, days in versions:
        set_timeframe(tf)
        TREND_LOOKBACKS, TREND_VOL_TARGET = lb, vt
        log(f"{name}: hämtar data ({tf})...")
        data = {}
        for i, sym in enumerate(SYMBOLS):
            try:
                data[sym] = fake_history(sym, int(days * 86400000 / BAR_MS), seed=i + 1) if fake else fetch_history(sym, days)
            except Exception as e:
                log(f"  {sym}: kunde inte hämtas ({e})")
        data = {k: v for k, v in data.items() if len(v) > lb[-1] + 40}
        if REGIME_SYMBOL not in data:
            log("Ingen BTC-data - hoppar över")
            continue
        end_t = data[REGIME_SYMBOL].t[-1]
        for p in periods:
            start_t = end_t - p * 86400000
            # signalerna räknas på historik före start, så modellen är "varm" från dag 1
            r = trend_simulate(data, "long", start_t)
            rl = trend_simulate(data, "longshort", start_t)
            st, stl = curve_stats(r["curve"]), curve_stats(rl["curve"])
            table[(name + " - bara lång", p)] = (st, r["trades"])
            table[(name + " - lång + kort", p)] = (stl, rl["trades"])
            if p not in bh_done:
                bh_done[p] = (curve_stats(buyhold_curve(data, start_t)), "-")
        log(f"  klart")
    TREND_LOOKBACKS, TREND_VOL_TARGET = orig
    for p in periods:
        if p in bh_done:
            table[("Köp & håll (lika i alla)", p)] = bh_done[p]
    names = []
    for k, _ in table:
        if k not in names:
            names.append(k)
    head = "".join(f"<th>Senaste {p} dagar</th>" for p in periods)
    rows = ""
    for n in names:
        rows += f"<tr><td>{n}</td>"
        for p in periods:
            v = table.get((n, p))
            if not v:
                rows += "<td>-</td>"
                continue
            st, tr = v
            rows += (f"<td><span class='{cls(st['ret'])}'><b>{pct(st['ret'])}</b></span><br>"
                     f"<small>nedgång {st['mdd'] * 100:.0f}% · {tr} affärer</small></td>")
        rows += "</tr>"
        log(f"{n:42}: " + " | ".join(f"{p}d {pct(table[(n, p)][0]['ret'])}" for p in periods if (n, p) in table))
    html = f"""<!DOCTYPE html><html lang="sv"><head><meta charset="utf-8"><title>Senaste tiden</title>
<style>body{{background:#0f1115;color:#e6e6e6;font-family:Segoe UI,system-ui,sans-serif;padding:24px}}
table{{border-collapse:collapse;width:100%;font-size:14px;background:#181b22}} td,th{{padding:10px;border-bottom:1px solid #262a33;text-align:left;vertical-align:top}}
th{{color:#999;font-weight:500}} .pos{{color:#3fb68b}} .neg{{color:#e5534b}} small{{color:#999}} .muted{{color:#888}}</style></head><body>
<h1>Hur hade trendmodellen gått på senaste tiden?</h1>
<p class="muted">Start 10 000 USDT i varje period, slut {datetime.now().strftime('%Y-%m-%d')}. Avgifter och slippage inräknade. Samma fasta regler som live-boten.</p>
<table><tr><th>Modell</th>{head}</tr>{rows}</table>
<p class="muted">"Trend timme" är en kortsiktig variant: tittar på 12/24/48/96 timmar och kan handla varje timme.</p>
</body></html>"""
    path = os.path.join(HERE, "senaste_tiden.html")
    with open(path, "w", encoding="utf-8") as f:
        f.write(html)
    log(f"Rapport sparad: {path}")
    open_in_browser(path)


def write_summary_md(st, prices, eq, mode):
    """Kort sammanfattning i Markdown - GitHub visar den snyggt, även i mobilen."""
    tr = st["trades"]
    n = len(tr)
    wins = sum(1 for t in tr if t["pnl"] > 0)
    sp = st["start_prices"]
    bh = [prices[s] / sp[s] - 1 for s in sp if s in prices]
    bh = sum(bh) / len(bh) if bh else 0
    best = max(tr, key=lambda t: t["ret"]) if tr else None
    worst = min(tr, key=lambda t: t["ret"]) if tr else None
    name = "bara lång" if mode == "long" else "lång + kort"
    lines = [f"## Trendbot ({name})", "",
             f"Igång sedan {fmt_ts(st['start_ms'])} · uppdaterad {datetime.now().strftime('%Y-%m-%d %H:%M')} (UTC)", "",
             "| | |", "|---|---|",
             f"| Kapital | **{money(eq)} USDT** ({pct(eq / START_CAPITAL - 1)}) |",
             f"| Köp & håll samma tid | {pct(bh)} |",
             f"| Avslutade affärer | {n} ({(wins / n * 100 if n else 0):.0f} % vinster) |",
             f"| Snitt per affär | {pct(sum(t['ret'] for t in tr) / n) if n else '-'} |",
             f"| Bästa | {pct(best['ret']) + ' ' + best['symbol'] if best else '-'} |",
             f"| Sämsta | {pct(worst['ret']) + ' ' + worst['symbol'] if worst else '-'} |", ""]
    if st.get("fng"):
        lines.append(f"Rädsla/girighet: **{st['fng'][0]}** ({st['fng'][1]})  ")
    if st.get("blocked"):
        lines.append("Spärrade p.g.a. nyheter: " + ", ".join(st["blocked"]) + "  ")
    lines += ["", "| Position | Sida | Insats | Resultat |", "|---|---|---|---|"]
    for s, p in st["pos"].items():
        cur = prices.get(s, p["avg"])
        r = (cur / p["avg"] - 1) * (1 if p["qty"] > 0 else -1)
        lines.append(f"| {s} | {'Lång' if p['qty'] > 0 else 'Kort'} | {money(p['margin'])} | {pct(r)} |")
    if not st["pos"]:
        lines.append("| (inga) | | | |")
    tag = 'lang' if mode == 'long' else 'langkort'
    svg = equity_svg(st["equity"])
    if svg.startswith("<svg"):
        svg = svg.replace('<svg viewBox="0 0 900 260" width="100%" preserveAspectRatio="none">',
                          '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 900 260" width="900" height="260">'
                          '<rect width="900" height="260" fill="#181b22"/>', 1)
        with open(os.path.join(HERE, f"graf_{tag}.svg"), "w", encoding="utf-8") as f:
            f.write(svg)
        lines.insert(4, f"![Kapital över tid](graf_{tag}.svg)\n")
    path = os.path.join(HERE, f"SAMMANFATTNING_{tag}.md")
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


# ============================================================================
# KOMBINATION AV KÄNDA STRATEGIER SOM LÄR SIG LÅNGSAMT
# ============================================================================
# A) Trend (time-series momentum) - samma som trendboten
# B) Rotation: köp de 3 starkaste senaste 14 dagarna, blanka de 3 svagaste (veckovis)
# C) Studs tillbaka: köp de 3 som fallit mest senaste 30 dagarna, blanka de 3 som stigit mest (veckovis)
# Lärandet: var 30:e dag flyttas pengar mot de strategier som haft bäst
# riskjusterad avkastning de senaste 90 dagarna - långsamt, aldrig på enstaka dagar.
ENS_LEARN_EVERY = 30
ENS_LOOKBACK = 90
ENS_MIN_SHARE = 0.10


def xs_targets(data, idx, t, look, k, reverse=False):
    rets = []
    for sym, b in data.items():
        i = idx[sym].get(t)
        if i is None or i < look + 31:
            continue
        rets.append((b.c[i] / b.c[i - look] - 1, sym))
    if len(rets) < 2 * k + 1:
        return {}
    rets.sort()
    losers, winners = [s for _, s in rets[:k]], [s for _, s in rets[-k:]]
    longs, shorts = (losers, winners) if reverse else (winners, losers)
    w = 0.5 / k
    out = {s: w for s in longs}
    out.update({s: -w for s in shorts})
    return out


ENS_STRATS = {
    "trend": lambda data, idx, t: trend_targets(data, idx, t, "longshort"),
    "rotation": lambda data, idx, t: xs_targets(data, idx, t, 14, 3),
    "studs": lambda data, idx, t: xs_targets(data, idx, t, 30, 3, reverse=True),
}


def ensemble_simulate(data, start_t, learn=True, only=None):
    master = max(data.values(), key=len)
    idx = {s: {t: i for i, t in enumerate(b.t)} for s, b in data.items()}
    names = only or list(ENS_STRATS)
    meta = {n: 1 / len(names) for n in names}
    sub = {n: {} for n in names}          # varje strategis egna vikter
    sub_hist = {n: [] for n in names}     # varje strategis egen dagsavkastning
    eq, w = START_CAPITAL, {}
    curve, trades, costs, meta_log = [], 0, 0.0, []
    cost_rate = FEE + SLIPPAGE
    funding_day = SHORT_FUNDING_8H * 3 * BAR_MS / 86400000
    day = 0
    for j in range(1, len(master)):
        t = master.t[j]
        rets = {}
        for sym, b in data.items():
            i = idx[sym].get(t)
            if i is not None and i > 0:
                rets[sym] = b.c[i] / b.c[i - 1] - 1
        if t >= start_t:
            pnl = sum(wt * rets.get(sym, 0) - (abs(wt) * funding_day if wt < 0 else 0) for sym, wt in w.items())
            eq *= 1 + pnl
        for n in names:   # strategiernas egna resultat (för lärandet), även före start
            sub_hist[n].append(sum(wt * rets.get(sym, 0) for sym, wt in sub[n].items()))
        # nya delmål
        weekly = (t // 86400000) % 7 == 0
        for n in names:
            if n == "trend" or weekly or not sub[n]:
                tg = ENS_STRATS[n](data, idx, t)
                if tg or n == "trend":
                    turn = sum(abs(tg.get(s, 0) - sub[n].get(s, 0)) for s in set(tg) | set(sub[n]))
                    if sub_hist[n]:
                        sub_hist[n][-1] -= turn * cost_rate
                    sub[n] = tg
        # långsamt lärande
        day += 1
        if learn and day % ENS_LEARN_EVERY == 0 and len(sub_hist[names[0]]) > ENS_LOOKBACK:
            sc = {}
            for n in names:
                h = sub_hist[n][-ENS_LOOKBACK:]
                m = sum(h) / len(h)
                sd = math.sqrt(sum((x - m) ** 2 for x in h) / len(h)) or 1e-9
                sc[n] = max(0.0, m / sd * math.sqrt(365))
            tot = sum(sc.values())
            if tot > 0:
                raw = {n: max(ENS_MIN_SHARE, sc[n] / tot) for n in names}
            else:
                raw = {n: 1.0 for n in names}
            z = sum(raw.values())
            meta = {n: raw[n] / z for n in names}
            if t >= start_t:
                meta_log.append([t, dict(meta)])
        if t < start_t:
            continue
        tgt = {}
        for n in names:
            for sym, wt in sub[n].items():
                tgt[sym] = tgt.get(sym, 0) + meta[n] * wt
        gross = sum(abs(x) for x in tgt.values())
        if gross > TREND_MAX_GROSS:
            tgt = {k: v * TREND_MAX_GROSS / gross for k, v in tgt.items()}
        for sym in set(w) | set(tgt):
            new, old = tgt.get(sym, 0.0), w.get(sym, 0.0)
            if abs(new - old) > TREND_MIN_TRADE or (abs(new) < 1e-9 and old != 0):
                c = abs(new - old) * cost_rate * eq
                eq -= c; costs += c; trades += 1
                w[sym] = new
        w = {k: v for k, v in w.items() if abs(v) > 1e-9}
        curve.append([t, eq])
    return {"curve": curve, "trades": trades, "costs": costs, "weights": w, "meta": meta, "meta_log": meta_log}


def run_ensemble_test(years=5.5, fake=False, out_path=None):
    """Jämför: trend ensam, varje strategi ensam, kombination utan och med lärande.
    Över hela perioden och senaste 30/90/180/365 dagarna."""
    set_timeframe("1d")
    days = years * 365
    data = {}
    for i, sym in enumerate(SYMBOLS):
        try:
            data[sym] = fake_history(sym, int(days), seed=i + 1) if fake else fetch_history(sym, days)
        except Exception as e:
            log(f"  {sym}: kunde inte hämtas ({e})")
    data = {k: v for k, v in data.items() if len(v) > 120}
    end_t = data[REGIME_SYMBOL].t[-1]
    first = data[REGIME_SYMBOL].t[TREND_LOOKBACKS[-1] + 31 + ENS_LOOKBACK]
    periods = [("Hela perioden", first), ("365 dagar", end_t - 365 * 86400000), ("180 dagar", end_t - 180 * 86400000),
               ("90 dagar", end_t - 90 * 86400000), ("30 dagar", end_t - 30 * 86400000)]
    variants = [("Trend lång + kort (nuvarande)", dict(only=["trend"], learn=False)),
                ("Rotation ensam", dict(only=["rotation"], learn=False)),
                ("Studs tillbaka ensam", dict(only=["studs"], learn=False)),
                ("Kombination, lika vikter", dict(learn=False)),
                ("Kombination som lär sig", dict(learn=True))]
    rows, results = "", {}
    for name, kw in variants:
        cells = ""
        for pname, st_t in periods:
            r = ensemble_simulate(data, st_t, **kw)
            s_ = curve_stats(r["curve"])
            results[(name, pname)] = (s_, r)
            cells += (f"<td><b class='{cls(s_['ret'])}'>{pct(s_['ret'])}</b><br><small>nedgång {s_['mdd'] * 100:.0f}% · "
                      f"Sharpe {s_['sharpe']:.2f}</small></td>")
        rows += f"<tr><td>{name}</td>{cells}</tr>"
        log(f"{name:32}: " + " | ".join(f"{p} {pct(results[(name, p)][0]['ret'])}" for p, _ in periods))
    bh_cells = ""
    for pname, st_t in periods:
        s_ = curve_stats(buyhold_curve(data, st_t))
        bh_cells += f"<td><b class='{cls(s_['ret'])}'>{pct(s_['ret'])}</b><br><small>nedgång {s_['mdd'] * 100:.0f}%</small></td>"
    rows += f"<tr><td>Köp &amp; håll</td>{bh_cells}</tr>"
    lr = results[("Kombination som lär sig", "Hela perioden")][1]
    mrows = "".join(f"<tr><td>{fmt_ts(t)[:10]}</td>" + "".join(f"<td>{m[n] * 100:.0f}%</td>" for n in ENS_STRATS) + "</tr>"
                    for t, m in lr["meta_log"][-12:])
    head = "".join(f"<th>{p}</th>" for p, _ in periods)
    html = f"""<!DOCTYPE html><html lang="sv"><head><meta charset="utf-8"><title>Kombination av strategier</title>
<style>body{{background:#0f1115;color:#e6e6e6;font-family:Segoe UI,system-ui,sans-serif;padding:24px}}
table{{border-collapse:collapse;width:100%;font-size:14px;background:#181b22;margin-bottom:24px}} td,th{{padding:9px;border-bottom:1px solid #262a33;text-align:left;vertical-align:top}}
th{{color:#999;font-weight:500}} .pos{{color:#3fb68b}} .neg{{color:#e5534b}} small{{color:#999}} .muted{{color:#888}}</style></head><body>
<h1>Kombination av kända strategier</h1>
<p class="muted">Dagsdata, avgifter och slippage inräknade. Start 10 000 i varje period. Slut {fmt_ts(end_t)[:10]}.</p>
<table><tr><th>Strategi</th>{head}</tr>{rows}</table>
<h2>Hur den lärande kombinationen fördelade pengarna (senaste 12 omfördelningarna)</h2>
<table><tr><th>Datum</th>{''.join(f'<th>{n}</th>' for n in ENS_STRATS)}</tr>{mrows}</table></body></html>"""
    out_path = out_path or os.path.join(HERE, "kombination.html")
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(html)
    md = ["| Strategi | " + " | ".join(p for p, _ in periods) + " |", "|---" * (len(periods) + 1) + "|"]
    for name, _ in variants:
        md.append(f"| {name} | " + " | ".join(pct(results[(name, p)][0]['ret']) for p, _ in periods) + " |")
    with open(out_path.replace(".html", ".md"), "w", encoding="utf-8") as f:
        f.write("\n".join(md) + "\n")
    log(f"Rapport sparad: {out_path}")
    return results


def usd_sek():
    """Aktuell växelkurs dollar -> kronor (gratis, ingen nyckel). Reserv: 10.5."""
    for url, path in (("https://api.frankfurter.dev/v1/latest?base=USD&symbols=SEK", ("rates", "SEK")),
                      ("https://api.frankfurter.app/latest?from=USD&to=SEK", ("rates", "SEK")),
                      ("https://open.er-api.com/v6/latest/USD", ("rates", "SEK"))):
        try:
            d = json.loads(fetch_text(url, timeout=10))
            v = float(d[path[0]][path[1]])
            if 5 < v < 20:
                try:
                    with open(os.path.join(HERE, "kurs.json"), "w", encoding="utf-8") as f:
                        json.dump({"usd_sek": v, "ts": int(time.time() * 1000)}, f)
                except Exception:
                    pass
                return v, True
        except Exception:
            continue
    try:   # senaste kända kurs i stället för en gissning
        with open(os.path.join(HERE, "kurs.json"), encoding="utf-8") as f:
            return float(json.load(f)["usd_sek"]), True
    except Exception:
        return 9.93, False


def kr(x, sign=False):
    t = f"{abs(x):,.0f}".replace(",", " ")
    if sign:
        return ("+" if x >= 0 else "−") + t + " kr"
    return ("−" if x < 0 else "") + t + " kr"


def pct_sv(x):
    return f"{x * 100:+.1f} %".replace(".", ",").replace("-", "−")


def write_mail_report(path=None):
    """Enkel timrapport i kronor för varje bot."""
    now_ms = int(time.time() * 1000)
    rate, live_rate = usd_sek()
    try:
        from zoneinfo import ZoneInfo
        se = datetime.now(ZoneInfo("Europe/Stockholm"))
    except Exception:
        se = datetime.utcnow() + __import__("datetime").timedelta(hours=1)
    se = se + __import__("datetime").timedelta(minutes=10)   # mejlet skickas strax före hel timme
    lines = [f"## 🕐 Kl {se.strftime('%H')}:00 – {se.strftime('%d/%m')}",
             f"<sub>Låtsaspengar · varje bot startade med {kr(START_CAPITAL * rate)}</sub>", ""]
    for tag, name in (("", "Bot 1 – köper bara"), ("_langkort", "Bot 2 – köper och blankar")):
        f = TREND_STATE_FILE.replace(".json", f"{tag}.json")
        if not os.path.exists(f):
            continue
        with open(f, encoding="utf-8") as fh:
            st = json.load(fh)
        eq_hist = st.get("equity") or [[now_ms, START_CAPITAL]]
        eq = eq_hist[-1][1]
        day_ago = next((e for t, e in reversed(eq_hist) if t <= now_ms - 86000 * 1000), eq_hist[0][1])
        tr = st.get("trades", [])
        today0 = int(datetime.now().replace(hour=0, minute=0, second=0, microsecond=0).timestamp() * 1000)
        day_tr = [t for t in tr if t["exit_ts"] >= today0]
        opened_today = [p for p in st.get("pos", {}).values() if p.get("ts", 0) >= today0]
        allt = [{"symbol": t["symbol"], "side": t["side"], "ret": t["ret"], "pnl": t["pnl"]} for t in tr]
        lp = st.get("last_prices", {})
        for sym, p in st.get("pos", {}).items():
            cur = lp.get(sym, p["avg"])
            side = "long" if p["qty"] > 0 else "short"
            fill = exit_price(cur, side)
            back = p["margin"] * (1 - FEE) + p["qty"] * (fill - p["avg"]) - abs(p["qty"] * fill) * FEE
            allt.append({"symbol": sym, "side": side, "ret": back / p["margin"] - 1, "pnl": back - p["margin"], "open": True})
        best = max(allt, key=lambda t: t["pnl"]) if allt else None
        worst = min(allt, key=lambda t: t["pnl"]) if allt else None

        def t_txt(t):
            if not t:
                return "inga affärer än"
            what = "köpt" if t["side"] == "long" else "blankat"
            state = "pågår" if t.get("open") else "såld"
            return f"{t['symbol'].replace('USDT', '')} ({what}, {state}) {pct_sv(t['ret'])} = {kr(t['pnl'] * rate, sign=True)}"
        holding = [t for t in allt if t.get("open")]
        coins = ", ".join(t["symbol"].replace("USDT", "") + (" (köpt)" if t["side"] == "long" else " (blankat)") for t in holding)
        verb = "tjänat" if eq >= START_CAPITAL else "förlorat"
        w = st.get("watch")
        if w and now_ms - w.get("last_poll", 0) < 20 * 60 * 1000:
            status = f"✅ igång – kollade priserna {w['polls']:,} gånger senaste körningen".replace(",", " ")
        elif w:
            status = f"⚠️ senaste priskollen var {fmt_ts(w.get('last_poll', 0))} – kan ha stannat"
        else:
            status = "✅ igång (kollar priserna varje timme)"
        lines += [f"Status: {status}  "]
        lines += [f"**{name}: har {kr(eq * rate)}** – har {verb} {kr(abs(eq - START_CAPITAL) * rate)} totalt ({pct_sv(eq / START_CAPITAL - 1)})  ",
                  f"Senaste dygnet: {kr((eq - day_ago) * rate, sign=True)} · Affärer idag: {len(day_tr) + len(opened_today)} · totalt: {len(tr) + len(st.get('pos', {}))}  ",
                  f"Bästa affär hittills: {t_txt(best)}  ",
                  f"Sämsta affär hittills: {t_txt(worst)}  ",
                  f"Äger/blankar: {coins or 'inget – väntar på bättre läge'}", ""]
    try:
        with open(TREND_STATE_FILE.replace(".json", "_langkort.json"), encoding="utf-8") as fh:
            soc = json.load(fh).get("social", {})
        if soc.get("risk_off_until", 0) > now_ms:
            lines.append(f"⚠️ **Social vakt aktiv** – minskad risk till {fmt_ts(soc['risk_off_until'] + 3600000)[11:]}: {soc.get('reason', '')}  ")
        if soc.get("no_short"):
            lines.append("Musk-skydd (blankas inte): " + ", ".join(c.replace('USDT', '') for c in soc["no_short"]) + "  ")
        lines.append("")
    except Exception:
        pass
    for fn, label in ((funding_mail_lines, "Bot 3"), (fast_mail_lines, "Bot 4"), (league_mail_lines, "Bot 5"), (chart_mail_lines, "Bot 6"), (gem_mail_lines, "Bot 7"), (copy_mail_lines, "Bot 8"), (news9_mail_lines, "Bot 9")):
        try:
            lines += fn(rate, now_ms)
        except Exception as e:
            lines.append(f"{label}: kunde inte läsa läget ({e})")
    lines.append(f"<sub>1 dollar = {rate:.2f} kr{'' if live_rate else ' (ungefär)'} · @PippiLangstrump</sub>")
    with open(path or os.path.join(HERE, "MAILRAPPORT.md"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")


# ============================================================================
# SJÄLVFÖRBÄTTRING (körs en gång i veckan) - med skyddsräcken mot överanpassning
# ============================================================================
# Testar ~30 varianter av trendreglerna på ~5 års data. En ny variant tas bara in om
# den är bättre än nuvarande BÅDE på hela perioden OCH senaste året OCH senaste
# halvåret, och inte har klart större nedgång. Annars behålls nuvarande.
TREND_CONFIG_FILE = os.path.join(HERE, "trend_config.json")
TREND_DEFAULT = {"lookbacks": [7, 14, 28, 56], "vol": 0.005, "min_trade": 0.03}


def load_trend_config(mode):
    try:
        with open(TREND_CONFIG_FILE, encoding="utf-8") as f:
            return json.load(f).get(mode, dict(TREND_DEFAULT))
    except Exception:
        return dict(TREND_DEFAULT)


def apply_trend_config(cfg):
    global TREND_LOOKBACKS, TREND_VOL_TARGET, TREND_MIN_TRADE
    TREND_LOOKBACKS, TREND_VOL_TARGET, TREND_MIN_TRADE = list(cfg["lookbacks"]), cfg["vol"], cfg["min_trade"]


def describe_cfg(c):
    return (f"perioder {'/'.join(map(str, c['lookbacks']))} dagar, insats {c['vol'] * 1000:.1f}‰/dag, "
            f"min ändring {c['min_trade'] * 100:.0f} %")


def run_self_improve(fake=False):
    set_timeframe("1d")
    data = {}
    for i, sym in enumerate(SYMBOLS):
        try:
            data[sym] = fake_history(sym, 2000, seed=i + 1) if fake else fetch_history(sym, 5.5 * 365)
        except Exception as e:
            log(f"  {sym}: kunde inte hämtas ({e})")
    data = {k: v for k, v in data.items() if len(v) > 200}
    end_t = data[REGIME_SYMBOL].t[-1]
    starts = {"hela": data[REGIME_SYMBOL].t[150], "365": end_t - 365 * 86400000, "180": end_t - 180 * 86400000}
    cands = []
    for lb in ([5, 10, 20, 40], [7, 14, 28, 56], [10, 20, 40, 80], [14, 28, 56, 112], [7, 14, 28, 56, 112]):
        for vol in (0.0035, 0.005, 0.007):
            for mt in (0.03, 0.06):
                cands.append({"lookbacks": lb, "vol": vol, "min_trade": mt})
    try:
        with open(TREND_CONFIG_FILE, encoding="utf-8") as f:
            conf = json.load(f)
    except Exception:
        conf = {}
    conf.setdefault("history", [])
    notes = []
    for mode, name in (("long", "Bot 1"), ("longshort", "Bot 2")):
        cur = conf.get(mode, dict(TREND_DEFAULT))
        # live-resultat sedan reglerna senast ändrades: går det bra live krävs mer för att byta
        live_ret = None
        try:
            with open(TREND_STATE_FILE.replace(".json", "" if mode == "long" else "_langkort.json"), encoding="utf-8") as fh:
                eqh = json.load(fh).get("equity", [])
            since = conf.get(f"{mode}_changed", 0)
            base = next((e for t, e in eqh if t >= since), None)
            if base and eqh:
                live_ret = eqh[-1][1] / base - 1
        except Exception:
            pass
        margin = 0.2 if (live_ret is not None and live_ret > 0) else 0.1

        def evaluate(c):
            apply_trend_config(c)
            out = {}
            for k, st_t in starts.items():
                out[k] = curve_stats(trend_simulate(data, mode, st_t)["curve"])
            return out
        cur_r = evaluate(cur)
        best, best_r = cur, cur_r
        for c in cands:
            if c == cur:
                continue
            r = evaluate(c)
            better_everywhere = all(r[k]["sharpe"] > cur_r[k]["sharpe"] + margin for k in starts)
            not_riskier = r["hela"]["mdd"] <= cur_r["hela"]["mdd"] + 0.05
            if better_everywhere and not_riskier and r["hela"]["sharpe"] > best_r["hela"]["sharpe"]:
                best, best_r = c, r
        live_txt = f" Live sedan förra ändringen: {pct(live_ret)}." if live_ret is not None else ""
        if best is not cur:
            conf[mode] = best
            conf[f"{mode}_changed"] = int(time.time() * 1000)
            msg = (f"{name} har förbättrats: nya regler ({describe_cfg(best)}). Sharpe hela perioden "
                   f"{cur_r['hela']['sharpe']:.2f} → {best_r['hela']['sharpe']:.2f}, senaste året "
                   f"{cur_r['365']['sharpe']:.2f} → {best_r['365']['sharpe']:.2f}." + live_txt)
        else:
            conf[mode] = cur
            msg = (f"{name}: testade {len(cands)} varianter - ingen var tydligt bättre överallt, behåller nuvarande regler "
                   f"(senaste året {pct(cur_r['365']['ret'])}, hela perioden {pct(cur_r['hela']['ret'])})." + live_txt)
        log(msg)
        notes.append(msg)
    conf["history"] = (conf["history"] + [{"ts": int(time.time() * 1000), "notes": notes}])[-52:]
    with open(TREND_CONFIG_FILE, "w", encoding="utf-8") as f:
        json.dump(conf, f, indent=1)
    with open(os.path.join(HERE, "FORBATTRING.md"), "w", encoding="utf-8") as f:
        f.write("**Veckans självförbättring**\n\n" + "\n\n".join(notes) + "\n\n@PippiLangstrump\n")
    apply_trend_config(TREND_DEFAULT)


TREND_EMERGENCY_STOP = 0.12   # en position som förlorat 12 % stängs direkt (väntar inte till nästa dygn)


def fetch_all_prices():
    """Alla mynts senaste pris i ett enda anrop (används varje sekund)."""
    syms = "[" + ",".join(f'"{s}"' for s in SYMBOLS) + "]"
    raw = http_json("/api/v3/ticker/price?symbols=" + urllib.parse.quote(syms), rounds=1)
    return {d["symbol"]: float(d["price"]) for d in raw}


# ============================================================================
# BOT 3: FUNDING-INSAMLARE (marknadsneutral, papperspengar)
# ============================================================================
# Köper myntet (spot) och blankar samma mängd på futures samtidigt. Prisrörelser tar
# ut varandra. Boten tjänar på "funding" som hävstångstraders betalar var 8:e timme
# (00, 08, 16 UTC) när de flesta är långa - och betalar när det är tvärtom.
# Väljer de mynt som betalat mest senaste dygnet, lämnar mynt där funding blivit negativ.
FUND_STATE_FILE = os.path.join(HERE, "funding_state.json")
FUND_SPOT_FEE = 0.001        # spot 0,1 %
FUND_MAX_COINS = 4
FUND_MIN_RATE = 0.00005      # minst 0,005 % per 8 h i snitt för att gå in
FUND_SWITCH_MARGIN = 0.00005


def funding_history(symbol, start_ms=None, limit=100):
    """Faktiska funding-betalningar [(tid_ms, rate)] - Binance, reserv OKX och Bybit."""
    try:
        path = f"/fapi/v1/fundingRate?symbol={symbol}&limit={limit}" + (f"&startTime={int(start_ms)}" if start_ms else "")
        req = urllib.request.Request("https://fapi.binance.com" + path, headers={"User-Agent": "paper-bot/1.0"})
        with urllib.request.urlopen(req, timeout=15) as r:
            raw = json.loads(r.read().decode())
        return [(int(d["fundingTime"]), float(d["fundingRate"])) for d in raw]
    except Exception:
        pass
    try:
        url = f"https://api.bybit.com/v5/market/funding/history?category=linear&symbol={symbol}&limit=200"
        if start_ms:
            url += f"&startTime={int(start_ms)}"
        d = json.loads(fetch_text(url))
        rows = [(int(x["fundingRateTimestamp"]), float(x["fundingRate"])) for x in d["result"]["list"]]
        return sorted(rows)
    except Exception:
        pass
    inst = symbol[:-4] + "-USDT-SWAP"
    d = json.loads(fetch_text(f"https://www.okx.com/api/v5/public/funding-rate-history?instId={inst}&limit=100"))
    rows = [(int(x["fundingTime"]), float(x["realizedRate"] or x["fundingRate"])) for x in d["data"]]
    rows = sorted(rows)
    return [r for r in rows if not start_ms or r[0] >= start_ms]


def fund_cost(notional):
    """Kostnad för att öppna ELLER stänga båda benen (spot + futures) inkl. slippage."""
    return notional * (FUND_SPOT_FEE + FEE + 2 * SLIPPAGE)


def run_funding_once():
    now = int(time.time() * 1000)
    st = None
    if os.path.exists(FUND_STATE_FILE):
        try:
            with open(FUND_STATE_FILE, encoding="utf-8") as f:
                st = json.load(f)
        except Exception:
            st = None
    if not st:
        st = {"start_ms": now, "cash": START_CAPITAL, "pos": {}, "trades": [], "equity": [], "last_pick_day": None,
              "funding_total": 0.0}
        log("Funding-boten startar med 10 000 låtsas-USDT")
    hist = {}
    for sym in SYMBOLS:
        try:
            hist[sym] = funding_history(sym, now - 3 * 86400000)
        except Exception as e:
            log(f"  {sym}: ingen funding-data ({e})")
    # 1) tillgodoräkna faktiska betalningar sedan senast
    for sym, p in st["pos"].items():
        for t, r in hist.get(sym, []):
            if t > p["last_paid"] and t <= now:
                amt = p["notional"] * r          # kort futures FÅR betalt när r > 0
                p["earned"] += amt
                st["funding_total"] += amt
                p["last_paid"] = t
    # 2) en gång per dygn (eller vid start): välj mynt
    day = now // 86400000
    avg = {s: sum(r for _, r in h[-3:]) / len(h[-3:]) for s, h in hist.items() if len(h) >= 3}
    if st["last_pick_day"] != day:
        st["last_pick_day"] = day
        ranked = sorted(avg.items(), key=lambda x: -x[1])
        want = [s for s, r in ranked if r >= FUND_MIN_RATE][:FUND_MAX_COINS]
        # stäng mynt som inte längre lönar sig (behåll om skillnaden är liten -> färre affärer)
        for sym in list(st["pos"]):
            if sym not in want and (avg.get(sym, 0) < FUND_MIN_RATE or
                                    (want and avg.get(want[-1], 0) - avg.get(sym, 0) > FUND_SWITCH_MARGIN)):
                p = st["pos"].pop(sym)
                back = p["margin"] + p["earned"] - fund_cost(p["notional"])
                st["cash"] += back
                st["trades"].append({"symbol": sym, "side": "carry", "ret": back / p["margin"] - 1,
                                     "pnl": back - p["margin"], "entry_ts": p["ts"], "exit_ts": now})
                log(f"  Funding: stänger {sym} ({money(back - p['margin'])} USDT)")
        slots = [s for s in want if s not in st["pos"]][:FUND_MAX_COINS - len(st["pos"])]
        eq_now = st["cash"] + sum(p["margin"] + p["earned"] for p in st["pos"].values())
        for sym in slots:
            margin = min(eq_now / FUND_MAX_COINS, st["cash"])
            if margin < MIN_TRADE_USDT:
                break
            notional = margin / 2              # halva till spot, halva som säkerhet för blankningen
            st["cash"] -= margin
            st["pos"][sym] = {"margin": margin, "notional": notional, "earned": -fund_cost(notional),
                              "ts": now, "last_paid": now, "rate_in": avg[sym]}
            log(f"  Funding: går in i {sym} för {money(margin)} USDT (betalar ~{avg[sym] * 100:.4f} % per 8 h)")
    st["avg_rates"] = avg
    eq = st["cash"] + sum(p["margin"] + p["earned"] for p in st["pos"].values())
    st["equity"].append([now, round(eq, 2)])
    st["equity"] = st["equity"][-3000:]
    with open(FUND_STATE_FILE + ".tmp", "w", encoding="utf-8") as f:
        json.dump(st, f)
    os.replace(FUND_STATE_FILE + ".tmp", FUND_STATE_FILE)
    log(f"Funding-boten: {money(eq)} USDT, {len(st['pos'])} mynt, insamlat {money(st['funding_total'])} USDT")
    return st


def funding_mail_lines(rate, now_ms):
    if not os.path.exists(FUND_STATE_FILE):
        return []
    with open(FUND_STATE_FILE, encoding="utf-8") as f:
        st = json.load(f)
    eq_hist = st.get("equity") or [[now_ms, START_CAPITAL]]
    eq = eq_hist[-1][1]
    day_ago = next((e for t, e in reversed(eq_hist) if t <= now_ms - 86000 * 1000), eq_hist[0][1])
    today0 = int(datetime.now().replace(hour=0, minute=0, second=0, microsecond=0).timestamp() * 1000)
    n_today = sum(1 for t in st["trades"] if t["exit_ts"] >= today0) + sum(1 for p in st.get("pos", {}).values() if p.get("ts", 0) >= today0)
    n_total = len(st["trades"]) + len(st.get("pos", {}))
    pos = st.get("pos", {})
    best = max(pos.items(), key=lambda x: x[1]["earned"]) if pos else None
    worst = min(pos.items(), key=lambda x: x[1]["earned"]) if pos else None

    def t_txt(x):
        if not x:
            return "inga än"
        s, p = x
        return f"{s.replace('USDT', '')} {pct_sv(p['earned'] / p['margin'])} = {kr(p['earned'] * rate, sign=True)}"
    verb = "tjänat" if eq >= START_CAPITAL else "förlorat"
    coins = ", ".join(s.replace("USDT", "") for s in pos) or "inget – väntar på bra funding"
    return [f"**Bot 3 – samlar funding (neutral): har {kr(eq * rate)}** – har {verb} {kr(abs(eq - START_CAPITAL) * rate)} totalt ({pct_sv(eq / START_CAPITAL - 1)})  ",
            f"Senaste dygnet: {kr((eq - day_ago) * rate, sign=True)} · Affärer idag: {n_today} · totalt: {n_total} · Insamlat: {kr(st.get('funding_total', 0) * rate, sign=True)}  ",
            f"Bästa just nu: {t_txt(best)}  ",
            f"Sämsta just nu: {t_txt(worst)}  ",
            f"Samlar på: {coins}", ""]


# ============================================================================
# BOT 4: DAYTRADERN (handlar många gånger per dag som en riktig daytrader)
# ============================================================================
# Bygger 1-minutsgrafer av sekundpriserna. Handlar bara MED trenden (snitt 20 min över
# snitt 60 min): köper på rekyler och utbrott i upptrend, blankar i nedtrend.
# Insats efter risk: varje affär riskerar 0,75 % av pengarna. Stopp efter hur mycket
# myntet svänger (0,5-2 %). Inget fast vinstmål: vid +1x risk flyttas stoppet till
# break-even, sedan följer ett släpande stopp efter så vinnarna får springa.
# Proffsregler: max 5 affärer samtidigt, 30 min paus i ett mynt efter förlust,
# slutar för dagen om dagen gått -3 %. Lär sig: mynt/riktningar som förlorar får halv insats.
FAST_STATE_FILE = os.path.join(HERE, "fast_state.json")
FAST_SLOTS = 5
FAST_RISK = 0.0075           # andel av pengarna som riskeras per affär
FAST_MAX_POS = 0.30          # max andel av pengarna i en affär
FAST_STOP_MIN, FAST_STOP_MAX = 0.005, 0.02
FAST_MAX_HOURS = 6
FAST_COOLDOWN_MIN = 30
FAST_DAY_LOSS = 0.03
FAST_MEM = 240               # minuter historik per mynt
FAST_RESET_MS = 1794495600000   # 12/11 kl 16:00 – nollställd när nya daytradern tog över


def _ema(vals, n):
    k = 2 / (n + 1)
    e = vals[0]
    for v in vals[1:]:
        e = v * k + e * (1 - k)
    return e


def fast_signal(closes):
    """(sida, stopp, varför) eller None. closes = minutpriser, äldst först."""
    if len(closes) < 61:
        return None
    rets = [closes[i] / closes[i - 1] - 1 for i in range(len(closes) - 60, len(closes))]
    m = sum(rets) / len(rets)
    vol = (sum((r - m) ** 2 for r in rets) / len(rets)) ** 0.5
    stop = min(FAST_STOP_MAX, max(FAST_STOP_MIN, vol * 30 ** 0.5 * 1.5))
    fast, slow = _ema(closes[-60:], 20), _ema(closes[-120:], 60)
    p, prev = closes[-1], closes[-2]
    hi30, lo30 = max(closes[-31:-1]), min(closes[-31:-1])
    trend = fast / slow - 1
    if abs(trend) < 0.0015:                  # ingen tydlig trend -> sitt still
        return None
    if trend > 0 and p > slow:
        if p > hi30 and p > prev:
            return "long", stop, "utbrott i upptrend"
        if abs(p / fast - 1) < 0.0015 and p > prev and min(closes[-6:]) < fast:
            return "long", stop, "rekyl i upptrend"
    if trend < 0 and p < slow:
        if p < lo30 and p < prev:
            return "short", stop, "utbrott i nedtrend"
        if abs(p / fast - 1) < 0.0015 and p < prev and max(closes[-6:]) > fast:
            return "short", stop, "rekyl i nedtrend"
    return None


def run_fast_watch(minutes=55):
    st = None
    if os.path.exists(FAST_STATE_FILE):
        try:
            with open(FAST_STATE_FILE, encoding="utf-8") as f:
                st = json.load(f)
        except Exception:
            st = None
    if not st:
        st = {"start_ms": int(time.time() * 1000), "cash": START_CAPITAL, "pos": {}, "trades": [], "equity": [], "mins": {}}
        log("Daytradern startar med 10 000 låtsas-USDT")
    if st.get("reset_at", 0) < FAST_RESET_MS:          # nollställning beställd av Gustav (ny daytrader-version)
        now0 = int(time.time() * 1000)
        log("Daytradern nollställs till 10 000 låtsas-USDT (ny version)")
        st = {"start_ms": now0, "cash": START_CAPITAL, "pos": {}, "trades": [], "equity": [[now0, START_CAPITAL]],
              "mins": st.get("mins", {}), "reset_at": FAST_RESET_MS, "v2_from": now0}
    st.setdefault("v2_from", int(time.time() * 1000))
    st.setdefault("cooldown", {})
    st.setdefault("day", {})
    prices = {}
    end = time.time() + minutes * 60
    last_min, polls, fails, last_save = None, 0, 0, time.time()

    def equity():
        e = st["cash"]
        for sym, p in st["pos"].items():
            e += mark_value(p["cost"], p["entry"], prices.get(sym, p["entry"]), p["side"])
        return e

    def close(sym, price, now, why):
        p = st["pos"].pop(sym)
        x = exit_price(price, p["side"])
        val = trade_value(p["cost"], p["entry"], x, p["side"], (now - p["ts"]) / 3.6e6)
        st["cash"] += val
        st["trades"].append({"symbol": sym, "side": p["side"], "ret": val / p["cost"] - 1, "pnl": val - p["cost"],
                             "entry_ts": p["ts"], "exit_ts": now, "reason": why, "setup": p.get("why", "")})
        st["trades"] = st["trades"][-5000:]
        if val < p["cost"]:
            st["cooldown"][sym] = now + FAST_COOLDOWN_MIN * 60000

    def size_factor(sym, side):
        """Lär sig: förlorar ett mynt+riktning på sina senaste 8 affärer -> halv insats."""
        recent = [t for t in st["trades"] if t["symbol"] == sym and t["side"] == side
                  and t["exit_ts"] >= st["v2_from"]][-8:]
        if len(recent) >= 4 and sum(t["pnl"] for t in recent) < 0:
            return 0.5
        return 1.0

    while time.time() < end:
        t1 = time.time()
        now = int(t1 * 1000)
        try:
            prices.update(fetch_all_prices())
            polls += 1
        except Exception:
            fails += 1
            time.sleep(1)
            continue
        # sälj-regler varje sekund
        for sym, p in list(st["pos"].items()):
            cur = prices.get(sym)
            if cur is None:
                continue
            stop = p.get("stop", 0.003)
            r = (cur / p["entry"] - 1) * (1 if p["side"] == "long" else -1)
            p["peak"] = max(p.get("peak", 0.0), r)
            if p["peak"] >= 2 * stop:
                floor = p["peak"] - 0.75 * stop          # släpande stopp
            elif p["peak"] >= stop:
                floor = 0.0025                           # break-even + avgifter
            else:
                floor = -stop
            if r <= floor:
                close(sym, cur, now, "stopp" if floor < 0 else "vinstlås")
            elif now - p["ts"] >= FAST_MAX_HOURS * 3600000:
                close(sym, cur, now, "tid")
        # ny minut: spara minutpriser, kolla trender och leta nya affärer
        minute = now // 60000
        if minute != last_min:
            last_min = minute
            for sym, pr in prices.items():
                arr = st["mins"].setdefault(sym, [])
                if arr and now - arr[-1][0] > 10 * 60000:
                    arr.clear()                          # för stort glapp -> börja om
                arr.append([now, pr])
                del arr[:-FAST_MEM]
            eq = equity()
            st["equity"].append([now, round(eq, 2)])
            st["equity"] = st["equity"][-6000:]
            today = datetime.now().strftime("%Y-%m-%d")
            if st["day"].get("date") != today:
                st["day"] = {"date": today, "start_eq": eq}
            day_ok = eq >= st["day"]["start_eq"] * (1 - FAST_DAY_LOSS)
            for sym, arr in st["mins"].items():
                closes = [x[1] for x in arr]
                sig = fast_signal(closes) if len(closes) >= 121 else None
                p = st["pos"].get(sym)
                # trenden vänt mot en öppen affär -> ut
                if p and sig and sig[0] != p["side"]:
                    close(sym, prices[sym], now, "trenden vände")
                    p = None
                if p or not sig or not day_ok or len(st["pos"]) >= FAST_SLOTS:
                    continue
                if st["cooldown"].get(sym, 0) > now:
                    continue
                side, stop, why = sig
                cost = min(eq * FAST_RISK / stop * size_factor(sym, side), eq * FAST_MAX_POS, st["cash"])
                if cost < MIN_TRADE_USDT:
                    continue
                st["cash"] -= cost
                st["pos"][sym] = {"side": side, "entry": entry_price(prices[sym], side), "cost": cost, "ts": now,
                                  "stop": stop, "peak": 0.0, "why": why}
        if time.time() - last_save > 120:
            with open(FAST_STATE_FILE + ".tmp", "w", encoding="utf-8") as f:
                json.dump(st, f)
            os.replace(FAST_STATE_FILE + ".tmp", FAST_STATE_FILE)
            last_save = time.time()
        time.sleep(max(0.0, 1.0 - (time.time() - t1)))
    st["watch"] = {"polls": polls, "fails": fails, "last_poll": int(time.time() * 1000)}
    st["last_prices"] = prices
    with open(FAST_STATE_FILE + ".tmp", "w", encoding="utf-8") as f:
        json.dump(st, f)
    os.replace(FAST_STATE_FILE + ".tmp", FAST_STATE_FILE)
    tr = st["trades"]
    log(f"Daytradern: {money(equity())} USDT, {len(tr)} affärer totalt, {len(st['pos'])} öppna")


def fast_mail_lines(rate, now_ms):
    if not os.path.exists(FAST_STATE_FILE):
        return []
    with open(FAST_STATE_FILE, encoding="utf-8") as f:
        st = json.load(f)
    eq_hist = st.get("equity") or [[now_ms, START_CAPITAL]]
    eq = eq_hist[-1][1]
    day_ago = next((e for t, e in reversed(eq_hist) if t <= now_ms - 86000 * 1000), eq_hist[0][1])
    tr = st["trades"]
    today0 = int(datetime.now().replace(hour=0, minute=0, second=0, microsecond=0).timestamp() * 1000)
    today = [t for t in tr if t["exit_ts"] >= today0]
    hour = [t for t in tr if t["exit_ts"] >= now_ms - 3600 * 1000]
    wins = sum(1 for t in tr if t["pnl"] > 0)
    fees = sum(t.get("cost", 0) for t in tr)
    best = max(tr, key=lambda t: t["pnl"]) if tr else None
    worst = min(tr, key=lambda t: t["pnl"]) if tr else None

    def t_txt(t):
        if not t:
            return "inga än"
        what = "köpt" if t["side"] == "long" else "blankat"
        return f"{t['symbol'].replace('USDT', '')} ({what}) {pct_sv(t['ret'])} = {kr(t['pnl'] * rate, sign=True)}"
    verb = "tjänat" if eq >= START_CAPITAL else "förlorat"
    return [f"**Bot 4 – daytradern: har {kr(eq * rate)}** – har {verb} {kr(abs(eq - START_CAPITAL) * rate)} totalt ({pct_sv(eq / START_CAPITAL - 1)})  ",
            f"Senaste dygnet: {kr((eq - day_ago) * rate, sign=True)} · Affärer senaste timmen: {len(hour)} · idag: {len(today)} · totalt: {len(tr)} · vinstandel: {(wins / len(tr) * 100 if tr else 0):.0f} %  ",
            f"Bästa affär: {t_txt(best)}  ",
            f"Sämsta affär: {t_txt(worst)}  ",
            f"Öppna just nu: {', '.join(s.replace('USDT', '') + (' (köpt)' if p['side'] == 'long' else ' (blankat)') for s, p in st['pos'].items()) or 'inga'}", ""]


# ============================================================================
# BOT 5: LAGLEDAREN (strategiliga) - fördelar pengar mellan bot 1-4 efter live-resultat
# ============================================================================
LEAGUE_FILE = os.path.join(HERE, "league_state.json")
LEAGUE_MEMBERS = {"Bot 1": "trend_state.json", "Bot 2": "trend_state_langkort.json",
                  "Bot 3": "funding_state.json", "Bot 4": "fast_state.json", "Bot 6": "chart_state.json"}
LEAGUE_MIN = 0.10


def _last_equity(fname):
    p = os.path.join(HERE, fname)
    if not os.path.exists(p):
        return None, []
    with open(p, encoding="utf-8") as f:
        eq = json.load(f).get("equity") or []
    return (eq[-1][1] if eq else None), eq


def run_league():
    now = int(time.time() * 1000)
    st = None
    if os.path.exists(LEAGUE_FILE):
        with open(LEAGUE_FILE, encoding="utf-8") as f:
            st = json.load(f)
    cur = {n: _last_equity(f)[0] for n, f in LEAGUE_MEMBERS.items()}
    resets = {}
    for n, f in LEAGUE_MEMBERS.items():               # en bot som nollställts ska inte ge låtsasvinst/-förlust
        try:
            with open(os.path.join(HERE, f), encoding="utf-8") as fh:
                resets[n] = json.load(fh).get("reset_at", 0)
        except Exception:
            resets[n] = 0
    if st:
        for k in LEAGUE_MEMBERS:
            st["weights"].setdefault(k, 0.0)    # ny bot får pengar vid nästa omfördelning
    if not st:
        n = len(LEAGUE_MEMBERS)
        st = {"start_ms": now, "equity": [[now, START_CAPITAL]], "weights": {k: 1 / n for k in LEAGUE_MEMBERS},
              "last_seen": cur, "last_rebal": now, "log": []}
        log("Lagledaren startar: lika mycket i varje bot")
    else:
        seen = st.setdefault("seen_reset", {})
        for k, r in resets.items():
            if r and seen.get(k) != r:
                st["last_seen"][k] = cur.get(k)
                seen[k] = r
        # dagens avkastning = viktad summa av varje bots avkastning sedan förra körningen
        r = 0.0
        for k, w in st["weights"].items():
            a, b = st["last_seen"].get(k), cur.get(k)
            if a and b:
                r += w * (b / a - 1)
        eq = st["equity"][-1][1] * (1 + r)
        st["equity"].append([now, round(eq, 2)])
        st["equity"] = st["equity"][-6000:]
        # vikterna driver med resultaten
        tot = sum(st["weights"][k] * ((cur[k] / st["last_seen"][k]) if cur.get(k) and st["last_seen"].get(k) else 1)
                  for k in st["weights"])
        st["weights"] = {k: st["weights"][k] * ((cur[k] / st["last_seen"][k]) if cur.get(k) and st["last_seen"].get(k) else 1) / tot
                         for k in st["weights"]}
        st["last_seen"] = cur
    # måndagar (eller 7 dagar sedan senast): ny fördelning efter senaste veckans live-resultat
    if now - st["last_rebal"] >= 7 * 86400000:
        score = {}
        for k, f in LEAGUE_MEMBERS.items():
            last, hist = _last_equity(f)
            base = next((e for t, e in hist if t >= now - 7 * 86400000), None)
            score[k] = max(0.0, (last / base - 1)) if last and base else 0.0
        tot = sum(score.values())
        raw = {k: (score[k] / tot if tot > 0 else 1 / len(score)) for k in score}
        raw = {k: max(LEAGUE_MIN, v) for k, v in raw.items()}
        z = sum(raw.values())
        st["weights"] = {k: v / z for k, v in raw.items()}
        cost = 0.002   # ungefärlig kostnad för att flytta pengar mellan botarna
        st["equity"][-1][1] = round(st["equity"][-1][1] * (1 - cost), 2)
        msg = "Ny fördelning efter veckans live-resultat: " + ", ".join(f"{k} {v * 100:.0f} %" for k, v in st["weights"].items())
        st["log"] = (st.get("log", []) + [[now, msg]])[-20:]
        st["last_rebal"] = now
        log(msg)
    with open(LEAGUE_FILE, "w", encoding="utf-8") as f:
        json.dump(st, f)


def league_mail_lines(rate, now_ms):
    if not os.path.exists(LEAGUE_FILE):
        return []
    with open(LEAGUE_FILE, encoding="utf-8") as f:
        st = json.load(f)
    eq = st["equity"][-1][1]
    day_ago = next((e for t, e in reversed(st["equity"]) if t <= now_ms - 86000 * 1000), st["equity"][0][1])
    verb = "tjänat" if eq >= START_CAPITAL else "förlorat"
    w = ", ".join(f"{k} {v * 100:.0f} %" for k, v in st["weights"].items())
    nxt = fmt_ts(st["last_rebal"] + 7 * 86400000 + 3600000)[:10]
    return [f"**Bot 5 – lagledaren (fördelar mellan de andra): har {kr(eq * rate)}** – har {verb} {kr(abs(eq - START_CAPITAL) * rate)} totalt ({pct_sv(eq / START_CAPITAL - 1)})  ",
            f"Senaste dygnet: {kr((eq - day_ago) * rate, sign=True)} · Fördelning: {w} · nästa omfördelning {nxt}", ""]


# ============================================================================
# MORGONRAPPORT + WEBBSIDA (läser alla botars sparfiler)
# ============================================================================
ALL_BOTS = [("Bot 1", "Köper bara (trend)", "trend_state.json", "#3fb68b"),
            ("Bot 2", "Köper och blankar (trend)", "trend_state_langkort.json", "#7cb7ff"),
            ("Bot 3", "Samlar funding (neutral)", "funding_state.json", "#e8c96a"),
            ("Bot 4", "Daytradern (handlar ofta)", "fast_state.json", "#f08a84"),
            ("Bot 5", "Lagledaren (fördelar mellan de andra)", "league_state.json", "#c39bff"),
            ("Bot 6", "Mönsterläsaren (läser grafen)", "chart_state.json", "#5fd3d3"),
            ("Bot 7", "Myntjägaren (letar nästa 100x)", "gem_state.json", "#ffb36b"),
            ("Bot 8", "Kopieraren (härmar kända traders)", "copy_state.json", "#ff7eb6"),
            ("Bot 9", "Nyhetsjägaren (okända projekt med nyheter)", "news_state.json", "#9be37a")]


def _bot_data(fname, now_ms):
    p = os.path.join(HERE, fname)
    if not os.path.exists(p):
        return None
    with open(p, encoding="utf-8") as f:
        st = json.load(f)
    eqh = st.get("equity") or [[now_ms, START_CAPITAL]]
    eq = eqh[-1][1]
    d24 = next((e for t, e in reversed(eqh) if t <= now_ms - 86000 * 1000), eqh[0][1])
    tr = st.get("trades", [])
    t24 = [t for t in tr if t.get("exit_ts", 0) >= now_ms - 86400 * 1000]
    return {"st": st, "eq": eq, "d24": d24, "eqh": eqh, "trades": tr, "t24": t24}


def _se_now():
    try:
        from zoneinfo import ZoneInfo
        return datetime.now(ZoneInfo("Europe/Stockholm"))
    except Exception:
        return datetime.utcnow() + __import__("datetime").timedelta(hours=1)


def write_morning_report(path=None, evening=False):
    """Morgon (kl 06): senaste 24 timmarna. Kväll (kl 20): dagens resultat sedan kl 06."""
    now_ms = int(time.time() * 1000)
    rate, _ = usd_sek()
    se = _se_now()
    if evening:
        since = now_ms - int((se - se.replace(hour=6, minute=0, second=0, microsecond=0)).total_seconds() * 1000)
        head = f"## 🌙 Kvällsrapport – dagens resultat {se.strftime('%d/%m')}"
        sub, when = "Sedan kl 06 i morse · låtsaspengar", "idag"
        fname = "KVALLSRAPPORT.md"
    else:
        since = now_ms - 86400 * 1000
        head = f"## ☀️ God morgon! Nattens resultat – {se.strftime('%d/%m')}"
        sub, when = "Senaste 24 timmarna · låtsaspengar", "i natt"
        fname = "MORGONRAPPORT.md"
    lines = [head, "", f"<sub>{sub}</sub>", ""]
    for name, desc, f, _c in ALL_BOTS:
        d = _bot_data(f, now_ms)
        if not d:
            continue
        start = next((e for t, e in reversed(d["eqh"]) if t <= since), d["eqh"][0][1])
        trs = [t for t in d["trades"] if t.get("exit_ts", 0) >= since]
        best = max(trs, key=lambda t: t["pnl"]) if trs else None
        worst = min(trs, key=lambda t: t["pnl"]) if trs else None
        bw = ""
        if best:
            bw = (f"  \nBästa: {best['symbol'].replace('USDT', '')} {kr(best['pnl'] * rate, sign=True)} · "
                  f"Sämsta: {worst['symbol'].replace('USDT', '')} {kr(worst['pnl'] * rate, sign=True)}")
        if f == "copy_state.json":
            per = copy_trader_stats(d["st"])
            who = ", ".join(f"{k} {pct_sv(v['pct'])}" for k, v in sorted(per.items(), key=lambda x: -x[1]["pct"]) if v["stake"])
            if who:
                bw += f"  \nPer trader (totalt): {who}"
        lines.append(f"**{name} – {desc}:** {kr((d['eq'] - start) * rate, sign=True)} ({pct_sv(d['eq'] / start - 1)}) {when} · "
                     f"totalt {kr((d['eq'] - START_CAPITAL) * rate, sign=True)} · {len(trs)} affärer{bw}")
        lines.append("")
    lines.append("Webbsida med grafer: https://raw.githack.com/PippiLangstrump/krypto-trendbot/main/docs/index.html")
    lines.append("")
    lines.append("@PippiLangstrump")
    with open(path or os.path.join(HERE, fname), "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")


BOT_EXPLAIN = {
    "Bot 1": "Köper mynt som har stigit de senaste veckorna och säljer när trenden vänder. Kollar trenderna en gång per dygn (kl 01). "
             "Står i kontanter när inget mynt stiger. Kan ha flera mynt samtidigt och köper mer när trenden blir starkare. "
             "Stop-loss och vinstlås kollas varje sekund (vinstlås: säljer om ett mynt som gått bra faller tillbaka).",
    "Bot 2": "Som Bot 1, men kan också blanka: satsar på att mynt som fallit i flera veckor fortsätter falla. "
             "Kan alltså tjäna både när marknaden går upp och ner. Ser över alla mynt en gång per dygn; stop-loss och vinstlås varje sekund.",
    "Bot 3": "Köper ett mynt och blankar samma mynt samtidigt, så prisrörelser tar ut varandra. Tjänar på avgiften som "
             "hävstångstraders betalar var 8:e timme (kl 01, 09, 17). Små men jämna intäkter.",
    "Bot 4": "Daytrader som handlar många gånger per dag, som en riktig person vid skärmen. Gör 1-minutsgrafer av "
             "sekundpriserna och handlar bara med trenden: köper rekyler och utbrott i upptrend, blankar i nedtrend. "
             "Varje affär riskerar 0,75 % av pengarna. Inget fast vinstmål: släpande stopp låter vinnarna springa, "
             "förlorare kapas snabbt. Pausar ett mynt 30 min efter förlust och slutar för dagen vid −3 %.",
    "Bot 7": "Letar nästa Bitcoin bland nya småmynt på DexScreener var 15:e minut. Sorterar bort skräp och bedrägerier "
             "(för lite pengar i handeln, för nya, fler säljare än köpare). Köper pyttesmå lotter, 2 % var, i upp till 40 mynt. "
             "Vid 2x säljs hälften så insatsen är hemma; resten får springa tills den tappar 60 % från toppen. "
             "Ett lotteri med regler: de flesta lotter förlorar, en enda stor vinnare kan bära allt.",
    "Bot 8": "Härmar 10 kända memecoin-traders (Cented, Theo, Cupsey, Decu, Pain, Kadenox, Trunoest, Kev, West, Yugi) genom att läsa deras offentliga plånböcker på "
             "Solana. När de köper (minst 0,5 SOL) köper boten samma mynt för 1 % av pengarna; när de säljer säljer den samma "
             "andel. Kommer alltid in lite efter dem och till sämre pris – det räknas med.",
    "Bot 9": "Läser kryptonyheter från 11 källor varannan minut och letar okända projekt (inte de 50 största) som har något "
             "stort på gång: börsnotering på Binance/Coinbase/Upbit, finansieringsrunda, lansering, stort samarbete eller ETF. "
             "Köper direkt efter nyheten om myntet inte redan rusat. Säljer hälften vid +30 %, resten med släpande stopp; "
             "stopp vid −12 %, säljer direkt vid dålig nyhet. Lär sig vilka sorters nyheter som ger pengar.",
    "Bot 6": "Läser graferna som en teknisk analytiker varje timme: utbrott med volym, dubbelbotten/-topp, trendstruktur "
             "och RSI-divergens. Stop-loss och vinstmål efter hur mycket myntet svänger. Lär sig: mönster som tjänar pengar live "
             "får större insats, mönster som förlorar mindre.",
    "Bot 5": "Handlar inte själv. Fördelar sina pengar mellan de andra botarna och flyttar varje vecka mer pengar till de botar som "
             "tjänat mest live senaste veckan (minst 10 % kvar i varje).",
}


def _mini_svg(points, rate, color):
    if len(points) < 2:
        return "<div class='small'>Grafen dyker upp när boten kört en stund.</div>"
    W, H, P = 600, 170, 8
    xs = [p[0] for p in points]; ys = [p[1] * rate for p in points]
    base = START_CAPITAL * rate
    y0, y1 = min(min(ys), base), max(max(ys), base)
    if y1 - y0 < 1:
        y0 -= 1; y1 += 1
    X = lambda v: P + (v - xs[0]) / max(1, xs[-1] - xs[0]) * (W - 2 * P)
    Y = lambda v: H - P - (v - y0) / (y1 - y0) * (H - 2 * P)
    step = max(1, len(points) // 400)
    pts = list(zip(xs, ys))[::step] + [(xs[-1], ys[-1])]
    d = " ".join(f"{'M' if i == 0 else 'L'}{X(a):.1f},{Y(b):.1f}" for i, (a, b) in enumerate(pts))
    return (f'<svg viewBox="0 0 {W} {H}" width="100%"><line x1="0" x2="{W}" y1="{Y(base):.1f}" y2="{Y(base):.1f}" '
            f'stroke="#555" stroke-dasharray="4 4"/><path d="{d}" fill="none" stroke="{color}" stroke-width="2"/>'
            f'<text x="{W - 4}" y="14" fill="#999" font-size="12" text-anchor="end">högst {kr(max(ys))}</text>'
            f'<text x="{W - 4}" y="{H - 4}" fill="#999" font-size="12" text-anchor="end">lägst {kr(min(ys))}</text></svg>')


def _with_open(f, st, trades):
    """Avslutade affärer + öppna positioner värderade till senaste pris (markerade 'pågår')."""
    out = [dict(t) for t in trades]
    lp = st.get("last_prices", {})
    now = int(time.time() * 1000)
    for sym, p in st.get("pos", {}).items():
        try:
            if f.startswith("trend_state"):
                side = "long" if p["qty"] > 0 else "short"
                fill = exit_price(lp.get(sym, p["avg"]), side)
                back = p["margin"] * (1 - FEE) + p["qty"] * (fill - p["avg"]) - abs(p["qty"] * fill) * FEE
                cost = p["margin"]
            elif f == "news_state.json":
                side, back, cost, sym = "long", p["qty"] * p["price"] * (1 - NEWS9_COST), p["cost"], p["name"]
            elif f in ("gem_state.json", "copy_state.json"):
                side = "long"
                back = p["qty"] * p["price"] * (1 - _gem_cost(p["qty"] * p["price"], p["liq"]))
                cost = p["cost"]
                sym = p["name"]
            elif f == "funding_state.json":
                side, back, cost = "carry", p["margin"] + p["earned"] - fund_cost(p["notional"]), p["margin"]
            else:
                side = p["side"]
                back = trade_value(p["cost"], p["entry"], exit_price(lp.get(sym, p["entry"]), side), side)
                cost = p["cost"]
            out.append({"symbol": sym, "side": side, "ret": back / cost - 1, "pnl": back - cost, "exit_ts": p.get("ts", now), "cost": cost,
                        "reason": "pågår", "pattern": p.get("pattern"), "open": True})
        except Exception:
            continue
    return out


def _copy_box(st, rate):
    import html as _h
    rows = "".join(
        f"<tr><td>{_h.escape(k)}</td><td>{v['n'] + v['open']} ({v['open']} öppna)</td><td>{kr(v['stake'] * rate)}</td>"
        f"<td style='color:{'#3fb68b' if v['pnl'] >= 0 else '#f08a84'}'>{pct_sv(v['pct'])}</td><td>{kr(v['pnl'] * rate, sign=True)}</td></tr>"
        for k, v in sorted(copy_trader_stats(st).items(), key=lambda x: -x[1]["pct"]))
    return ("<div class='sub'>Traders som kopieras – resultat för deras kopierade affärer</div><table>"
            "<tr class='th'><td>Trader</td><td>Affärer</td><td>Insatt</td><td>%</td><td>Resultat</td></tr>" + rows + "</table>")


TRADE_HEAD = ("<tr class='th'><td></td><td>Tid</td><td>Mynt</td><td></td><td>Insats</td><td>Värde nu / såld för</td>"
              "<td>%</td><td>Resultat</td><td>Varför</td></tr>")


def _trade_rows(trs, rate):
    rows = TRADE_HEAD
    for t in trs:
        side = {"long": "köpt", "short": "blankat"}.get(t.get("side"), "funding")
        why = "" if t.get("open") else {"trendsignal": "trenden vände", "signal": "trenden vände", "stopp": "stop-loss",
                                         "vinstmål": "vinstmål", "tid": "tiden gick ut", "vinst": "vinstmål"}.get(t.get("reason", ""), t.get("reason", ""))
        if t.get("pattern"):
            why = CHART_PATTERNS.get(t["pattern"], t["pattern"]) + (f" · {why}" if why else "")
        badge = ("<span class='b open'>Öppen</span>" if t.get("open") else "<span class='b done'>Avslutad</span>")
        stake = t.get("cost") or (t["pnl"] / t["ret"] if t.get("ret") else 0)
        value = stake + t["pnl"]
        rows += (f"<tr><td>{badge}</td><td>{fmt_ts(t.get('exit_ts', 0) + 3600000)[5:16]}</td><td>{t['symbol'].replace('USDT', '')}</td><td>{side}</td>"
                 f"<td>{kr(stake * rate)}</td><td>{kr(value * rate)}</td>"
                 f"<td class='{'pos' if t['pnl'] >= 0 else 'neg'}'>{pct_sv(t['ret'])}</td>"
                 f"<td class='{'pos' if t['pnl'] >= 0 else 'neg'}'>{kr(t['pnl'] * rate, sign=True)}</td><td class='small'>{why}</td></tr>")
    return rows


def _local_day(ms):
    return datetime.utcfromtimestamp(ms / 1000 + 3600).strftime("%m-%d")


def consistency(eqh):
    """Mått på om en bot går upp stadigt eller bara haft tur."""
    if len(eqh) < 3:
        return None
    days = {}
    for t, e in eqh:
        days[_local_day(t)] = e
    prev, rets = START_CAPITAL, []
    for d_ in sorted(days):
        rets.append((d_, days[d_] / prev - 1))
        prev = days[d_]
    peak, mdd, dd_series = START_CAPITAL, 0.0, []
    for t, e in eqh:
        peak = max(peak, e)
        dd = (e - peak) / peak
        mdd = min(mdd, dd)
        dd_series.append((t, dd))
    streak = best_streak = 0
    for _, r in rets:
        streak = streak + 1 if r < 0 else 0
        best_streak = max(best_streak, streak)
    # timavkastning -> stabilitet (avkastning delat med svängning, per år)
    hourly, last_t, last_e = [], eqh[0][0], eqh[0][1]
    for t, e in eqh:
        if t - last_t >= 3600 * 1000:
            hourly.append(e / last_e - 1)
            last_t, last_e = t, e
    stab = None
    if len(hourly) >= 72:     # minst 3 dygn, annars blir måttet missvisande
        m = sum(hourly) / len(hourly)
        sd = math.sqrt(sum((x - m) ** 2 for x in hourly) / len(hourly)) or 1e-9
        stab = m / sd * math.sqrt(24 * 365)
    hours_up = sum(1 for x in hourly if x > 0)
    return {"days": rets, "up_days": sum(1 for _, r in rets if r > 0), "mdd": mdd, "loss_streak": best_streak,
            "stab": stab, "dd": dd_series, "hours_up": hours_up, "hours": len(hourly)}


def _bars_svg(rets, rate_unused=None):
    if not rets:
        return ""
    W, H = 600, 140
    m = max(0.002, max(abs(r) for _, r in rets))
    bw = min(60, (W - 20) / len(rets))
    out = [f'<svg viewBox="0 0 {W} {H}" width="100%"><line x1="0" x2="{W}" y1="{H / 2}" y2="{H / 2}" stroke="#555"/>']
    for i, (d_, r) in enumerate(rets):
        h = abs(r) / m * (H / 2 - 18)
        x = 10 + i * bw
        y = H / 2 - h if r >= 0 else H / 2
        col = "#3fb68b" if r >= 0 else "#e5534b"
        out.append(f'<rect x="{x + 3:.1f}" y="{y:.1f}" width="{bw - 6:.1f}" height="{max(h, 1):.1f}" fill="{col}" rx="2"/>')
        out.append(f'<text x="{x + bw / 2:.1f}" y="{H - 2}" fill="#888" font-size="10" text-anchor="middle">{d_[3:]}</text>')
        out.append(f'<text x="{x + bw / 2:.1f}" y="{(y - 3) if r >= 0 else (y + h + 11):.1f}" fill="{col}" font-size="10" text-anchor="middle">{r * 100:+.1f}%</text>')
    out.append("</svg>")
    return "".join(out)


def _dd_svg(dd):
    if len(dd) < 2:
        return ""
    W, H = 600, 90
    lo = min(-0.005, min(v for _, v in dd))
    x0, x1 = dd[0][0], dd[-1][0]
    step = max(1, len(dd) // 400)
    pts = dd[::step] + [dd[-1]]
    path = " ".join(f"{'M' if i == 0 else 'L'}{(t - x0) / max(1, x1 - x0) * W:.1f},{v / lo * (H - 14):.1f}" for i, (t, v) in enumerate(pts))
    return (f'<svg viewBox="0 0 {W} {H}" width="100%"><path d="{path} L{W},0 L0,0 Z" fill="#e5534b33" stroke="#e5534b" stroke-width="1.5"/>'
            f'<text x="{W - 4}" y="{H - 2}" fill="#999" font-size="11" text-anchor="end">värsta: {lo * 100:.1f} %</text></svg>')


def write_dashboard():
    import html as _h
    now_ms = int(time.time() * 1000)
    rate, _ = usd_sek()
    os.makedirs(os.path.join(HERE, "docs"), exist_ok=True)
    data = [(n, d_, f, c, _bot_data(f, now_ms)) for n, d_, f, c in ALL_BOTS]
    data = [x for x in data if x[4]]
    # gemensam graf: % sedan start
    W, H, P = 900, 320, 46
    series = [(n, c, [(t, e / START_CAPITAL - 1) for t, e in d["eqh"]]) for n, _, _, c, d in data]
    pts = [p for _, _, s in series for p in s]
    svg = ""
    if len(pts) > 2:
        x0, x1 = min(p[0] for p in pts), max(p[0] for p in pts)
        y0, y1 = min(min(p[1] for p in pts), -0.005), max(max(p[1] for p in pts), 0.005)
        X = lambda v: P + (v - x0) / max(1, x1 - x0) * (W - 2 * P)
        Y = lambda v: H - P - (v - y0) / (y1 - y0) * (H - 2 * P)
        parts = [f'<svg viewBox="0 0 {W} {H}" width="100%">',
                 f'<line x1="{P}" x2="{W - P}" y1="{Y(0):.1f}" y2="{Y(0):.1f}" stroke="#555" stroke-dasharray="4 4"/>',
                 f'<text x="{P - 6}" y="{Y(0) + 4:.1f}" fill="#888" font-size="11" text-anchor="end">0 %</text>',
                 f'<text x="{P - 6}" y="{Y(y1) + 4:.1f}" fill="#888" font-size="11" text-anchor="end">{y1 * 100:+.1f} %</text>',
                 f'<text x="{P - 6}" y="{Y(y0) + 4:.1f}" fill="#888" font-size="11" text-anchor="end">{y0 * 100:+.1f} %</text>']
        for n, c, s in series:
            step = max(1, len(s) // 600)
            ss = s[::step] + [s[-1]]
            d = " ".join(f"{'M' if i == 0 else 'L'}{X(a):.1f},{Y(b):.1f}" for i, (a, b) in enumerate(ss))
            parts.append(f'<path d="{d}" fill="none" stroke="{c}" stroke-width="2.2"/>')
        parts.append(f'<text x="{P}" y="{H - 12}" fill="#888" font-size="11">{fmt_ts(x0 + 3600000)[:16]}</text>')
        parts.append(f'<text x="{W - P}" y="{H - 12}" fill="#888" font-size="11" text-anchor="end">{fmt_ts(x1 + 3600000)[:16]}</text>')
        parts.append("</svg>")
        svg = "".join(parts)
    crow = ""
    for n, desc, f, c, d in data:
        k = consistency(d["eqh"])
        if not k:
            continue
        stab = "för tidigt" if k["stab"] is None else f"{k['stab']:.1f}"
        crow += (f"<tr><td style='color:{c}'>{n}</td><td>{k['up_days']} av {len(k['days'])}</td>"
                 f"<td>{k['hours_up']} av {k['hours']}</td><td class='neg'>{k['mdd'] * 100:.1f} %</td>"
                 f"<td>{k['loss_streak']} dagar</td><td>{stab}</td></tr>")
    cons_table = ("<table><tr class='th'><td>Bot</td><td>Plusdagar</td><td>Plustimmar</td><td>Största nedgång</td>"
                  "<td>Längsta minussvit</td><td>Stabilitet</td></tr>" + crow + "</table>")
    cards = ""
    for i, (n, desc, f, c, d) in enumerate(data):
        tot = d["eq"] - START_CAPITAL
        st = d["st"]
        pos = st.get("pos", {})
        allt = _with_open(f, st, d["trades"])
        fee_line = ""
        open_tr = [t for t in allt if t.get("open")]
        if open_tr and "cash" in st:
            if_sold = st["cash"] + sum(t["pnl"] for t in open_tr) + sum(
                (p.get("margin") or p.get("cost") or 0) for p in pos.values())
            fee = d["eq"] - if_sold
            if fee > 0.05:
                fee_line = (f"<div class='tiny'>Om allt såldes nu: {kr(if_sold * rate)} "
                            f"(säljavgift + slippage ≈ {kr(-fee * rate, sign=True)})</div>")
        if f == "league_state.json":
            extra = "Fördelning: " + ", ".join(f"{k} {v * 100:.0f} %" for k, v in st.get("weights", {}).items())
        elif f == "funding_state.json":
            extra = f"Samlar på: {', '.join(s.replace('USDT', '') for s in pos) or 'inget'} · insamlat {kr(st.get('funding_total', 0) * rate, sign=True)}"
        elif f == "fast_state.json":
            wins = sum(1 for t in d["trades"] if t["pnl"] > 0)
            extra = f"Öppna: {', '.join(s.replace('USDT', '') for s in pos) or 'inga'} · vinstandel {(wins / len(d['trades']) * 100 if d['trades'] else 0):.0f} %"
        else:
            extra = "Äger/blankar: " + (", ".join(s.replace("USDT", "") + (" ↑" if p.get("qty", 1) > 0 else " ↓") for s, p in pos.items()) or "inget")
        cards += f"""<div class="card" style="border-left:4px solid {c}">
<details><summary class="name">{n} – {desc} <span class="info">ⓘ tryck för mer</span></summary>
<div class="explain">{_h.escape(BOT_EXPLAIN.get(n, ""))}{_copy_box(d['st'], rate) if n == "Bot 8" else ""}</div>
<div class="sub">Historik</div>{_mini_svg(d['eqh'], rate, c)}
<div class="sub">Dag för dag (grönt = plusdag, rött = minusdag)</div>{_bars_svg((consistency(d['eqh']) or {}).get('days', []))}
<div class="sub">Nedgång från toppen (hur ont det gjort på vägen)</div>{_dd_svg((consistency(d['eqh']) or {}).get('dd', []))}
{('<div class="sub">Bästa affärerna (även pågående)</div><table>' + _trade_rows(sorted([t for t in allt if t['pnl'] >= 0], key=lambda t: -t['pnl'])[:5], rate) + '</table>'
  '<div class="sub">Sämsta affärerna (även pågående)</div><table>' + _trade_rows(sorted([t for t in allt if t['pnl'] < 0], key=lambda t: t['pnl'])[:5], rate) + '</table>'
  '<div class="sub">Alla affärer (' + str(len(allt)) + ' st – öppna först, sen senaste)</div><div class="scroll"><table>' + _trade_rows(sorted(allt, key=lambda t: (not t.get('open'), -t.get('exit_ts', 0)))[:2000], rate) + '</table></div>')
 if allt else '<div class="small">Inga affärer än.</div>'}
</details>
<div class="big">{kr(d['eq'] * rate)}</div>
<div class="{'pos' if tot >= 0 else 'neg'}">{kr(tot * rate, sign=True)} totalt ({pct_sv(d['eq'] / START_CAPITAL - 1)})</div>
<div class="small">Senaste dygnet: <span class="{'pos' if d['eq'] >= d['d24'] else 'neg'}">{kr((d['eq'] - d['d24']) * rate, sign=True)}</span> · öppna affärer: {len(pos)} · avslutade: {len(d['trades'])}</div>
<div class="small">{_h.escape(extra)}</div>{fee_line}</div>"""
    trades = []
    for n, _, _, c, d in data:
        for t in d["trades"][-30:]:
            trades.append((t.get("exit_ts", 0), n, c, t))
    trades.sort(key=lambda x: -x[0])
    trows = "".join(f"<tr><td>{fmt_ts(ts + 3600000)[5:16]}</td><td style='color:{c}'>{n}</td><td>{t['symbol'].replace('USDT', '')}</td>"
                    f"<td>{'köpt' if t.get('side') == 'long' else ('blankat' if t.get('side') == 'short' else 'funding')}</td>"
                    f"<td class='{'pos' if t['pnl'] >= 0 else 'neg'}'>{kr(t['pnl'] * rate, sign=True)}</td></tr>"
                    for ts, n, c, t in trades[:25]) or "<tr><td colspan=5>Inga avslutade affärer än</td></tr>"
    soc = (data[1][4]["st"].get("social", {}) if len(data) > 1 else {})
    fng = data[1][4]["st"].get("fng") if len(data) > 1 else None
    guard = []
    if fng:
        guard.append(f"Rädsla/girighet: <b>{fng[0]}</b> ({_h.escape(fng[1])})")
    if soc.get("risk_off_until", 0) > now_ms:
        guard.append(f"⚠️ Social vakt aktiv: {_h.escape(soc.get('reason', ''))}")
    news = (data[1][4]["st"].get("news", []) if len(data) > 1 else [])[:8]
    nrows = "".join(f"<li>{_h.escape(x['title'])}</li>" for x in news)
    html = f"""<!DOCTYPE html><html lang="sv"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta http-equiv="refresh" content="300"><title>Kryptobotarna</title>
<style>body{{background:#0f1115;color:#e6e6e6;font-family:-apple-system,Segoe UI,system-ui,sans-serif;margin:0;padding:16px;max-width:960px;margin:auto}}
h1{{font-size:22px;margin:4px 0}} h2{{font-size:16px;color:#bbb;margin:22px 0 8px}} .muted,.small{{color:#999;font-size:13px}}
.card{{background:#181b22;border-radius:10px;padding:12px 14px;margin:10px 0;position:relative}} .rank{{position:absolute;right:14px;top:10px;color:#666;font-size:20px}}
.name{{font-size:14px;color:#ccc}} .big{{font-size:24px;font-weight:600;margin:4px 0}} .pos{{color:#3fb68b}} .neg{{color:#e5534b}}
.box{{background:#181b22;border-radius:10px;padding:10px}} table{{width:100%;border-collapse:collapse;font-size:13px}} td{{padding:6px;border-bottom:1px solid #262a33}}
.legend span{{margin-right:12px;font-size:12px}} summary{{cursor:pointer;list-style:none}} summary::-webkit-details-marker{{display:none}}
.info{{color:#7cb7ff;font-size:12px}} .sub{{color:#bbb;font-size:13px;font-weight:600;margin:12px 0 4px}}
.scroll{{max-height:300px;overflow:auto}} details table{{display:block;overflow-x:auto;white-space:nowrap}} .th td{{color:#888;font-size:11px}} .tiny{{color:#888;font-size:11px;margin-top:3px}} .b{{font-size:11px;padding:2px 6px;border-radius:8px;white-space:nowrap}} .b.open{{background:#173b2e;color:#5fd3a5}} .b.done{{background:#2a2e38;color:#aaa}} details table td{{font-size:12px;padding:4px}} .explain{{background:#11141a;border-radius:8px;padding:8px 10px;margin:6px 0;font-size:13px;color:#ccc;line-height:1.45}} ul{{padding-left:18px;font-size:13px;color:#bbb}}</style></head><body>
<h1>📈 Kryptobotarna</h1><div class="muted">Låtsaspengar, riktiga priser · uppdaterad {_se_now().strftime('%d/%m %H:%M')} · laddar om var 5:e minut</div>
<h2>Alla botar – % sedan start</h2><div class="box">{svg}<div class="legend">{''.join(f"<span style='color:{c}'>● {n}</span>" for n, _, _, c, _ in data)}</div></div>
<h2>Går de upp stadigt – eller var det tur?</h2><div class="box">{cons_table}
<div class="tiny">Stabilitet = avkastning delat med hur mycket den svänger (per år). Över 1 är bra, över 2 mycket bra. Måtten blir pålitliga först efter ungefär en vecka – en enda bra dag kan vara tur.</div></div>
<h2>Botarna</h2>{cards}
<h2>Senaste affärerna</h2><div class="box"><table>{trows}</table></div>
<h2>Nyheter och vakter</h2><div class="box"><div class="small">{' · '.join(guard)}</div><ul>{nrows}</ul></div>
</body></html>"""
    with open(os.path.join(HERE, "docs", "index.html"), "w", encoding="utf-8") as f:
        f.write(html)


# ============================================================================
# BOT 6: MÖNSTERLÄSAREN - läser grafen (1h-ljus) som en teknisk analytiker
# ============================================================================
CHART_STATE_FILE = os.path.join(HERE, "chart_state.json")
CHART_PATTERNS = {"utbrott": "Utbrott med volym", "dubbel": "Dubbelbotten/-topp",
                  "struktur": "Trendstruktur + rekyl", "divergens": "RSI-divergens"}
CHART_SLOTS = 4
CHART_BASE = 0.20          # 20 % av kassan per affär (justeras efter mönstrets betyg)
CHART_MAX_HOURS = 48


def _atr(b, n=14):
    tr = [max(b.h[i] - b.l[i], abs(b.h[i] - b.c[i - 1]), abs(b.l[i] - b.c[i - 1])) for i in range(1, len(b))]
    return sum(tr[-n:]) / n if len(tr) >= n else None


def _swings(vals, k=3, low=True):
    out = []
    for i in range(k, len(vals) - k):
        w = vals[i - k:i + k + 1]
        if (low and vals[i] == min(w)) or (not low and vals[i] == max(w)):
            out.append(i)
    return out


def detect_patterns(b):
    """Returnerar lista med (mönster, riktning +1/-1) för senaste stängda ljuset."""
    n = len(b)
    if n < 120:
        return []
    c, h, l, v = b.c, b.h, b.l, b.v
    i = n - 1
    found = []
    # 1) utbrott ur 48h-intervall med volym
    hh, ll = max(h[i - 48:i]), min(l[i - 48:i])
    vavg = sum(v[i - 48:i]) / 48 or 1
    if c[i] > hh and v[i] > 1.5 * vavg:
        found.append(("utbrott", 1))
    elif c[i] < ll and v[i] > 1.5 * vavg:
        found.append(("utbrott", -1))
    # 2) dubbelbotten / dubbeltopp (senaste 80 ljus)
    lows = [j for j in _swings(l[:i], 3, True) if j > i - 80]
    highs = [j for j in _swings(h[:i], 3, False) if j > i - 80]
    if len(lows) >= 2:
        a, b2 = lows[-2], lows[-1]
        if b2 - a >= 10 and abs(l[a] / l[b2] - 1) < 0.012:
            neck = max(h[a:b2 + 1])
            if c[i] > neck >= c[i - 1]:
                found.append(("dubbel", 1))
    if len(highs) >= 2:
        a, b2 = highs[-2], highs[-1]
        if b2 - a >= 10 and abs(h[a] / h[b2] - 1) < 0.012:
            neck = min(l[a:b2 + 1])
            if c[i] < neck <= c[i - 1]:
                found.append(("dubbel", -1))
    # 3) trendstruktur: högre toppar+bottnar och rekyl till EMA20
    e20 = ema(c, 20)
    if len(highs) >= 3 and len(lows) >= 3:
        up = h[highs[-1]] > h[highs[-2]] > h[highs[-3]] and l[lows[-1]] > l[lows[-2]] > l[lows[-3]]
        dn = h[highs[-1]] < h[highs[-2]] < h[highs[-3]] and l[lows[-1]] < l[lows[-2]] < l[lows[-3]]
        if up and l[i] <= e20[i] < c[i]:
            found.append(("struktur", 1))
        if dn and h[i] >= e20[i] > c[i]:
            found.append(("struktur", -1))
    # 4) RSI-divergens
    r = rsi(c, 14)
    if len(lows) >= 2:
        a, b2 = lows[-2], lows[-1]
        if l[b2] < l[a] and r[b2] > r[a] and r[b2] < 35 and i - b2 <= 3 and c[i] > c[i - 1]:
            found.append(("divergens", 1))
    if len(highs) >= 2:
        a, b2 = highs[-2], highs[-1]
        if h[b2] > h[a] and r[b2] < r[a] and r[b2] > 65 and i - b2 <= 3 and c[i] < c[i - 1]:
            found.append(("divergens", -1))
    return found


def run_chart_once():
    set_timeframe("1h")
    now = int(time.time() * 1000)
    st = None
    if os.path.exists(CHART_STATE_FILE):
        try:
            with open(CHART_STATE_FILE, encoding="utf-8") as f:
                st = json.load(f)
        except Exception:
            st = None
    if not st:
        st = {"start_ms": now, "cash": START_CAPITAL, "pos": {}, "trades": [], "equity": [], "last_bar": {},
              "score": {k: 0.0 for k in CHART_PATTERNS}, "count": {k: 0 for k in CHART_PATTERNS}}
        log("Mönsterläsaren startar med 10 000 låtsas-USDT")
    bars, prices = {}, {}
    for sym in SYMBOLS:
        try:
            b = fetch_klines(sym, 200)
            if b.t[-1] + BAR_MS > now:      # släng ljuset som inte stängt än
                prices[sym] = b.c[-1]
                b = b.slice(0, len(b) - 1)
            bars[sym] = b
            prices.setdefault(sym, b.c[-1])
        except Exception as e:
            log(f"  {sym}: kunde inte hämtas ({e})")

    def close(sym, px, why):
        p = st["pos"].pop(sym)
        x = exit_price(px, p["side"])
        val = trade_value(p["cost"], p["entry"], x, p["side"], (now - p["ts"]) / 3.6e6)
        st["cash"] += val
        ret = val / p["cost"] - 1
        st["trades"].append({"symbol": sym, "side": p["side"], "ret": ret, "pnl": val - p["cost"], "entry_ts": p["ts"],
                             "exit_ts": now, "reason": why, "pattern": p["pattern"]})
        st["trades"] = st["trades"][-3000:]
        # lär sig: mönstrets betyg = glidande snitt av resultaten
        k = p["pattern"]
        st["score"][k] = 0.8 * st["score"].get(k, 0.0) + 0.2 * ret
        st["count"][k] = st["count"].get(k, 0) + 1
        log(f"  Mönster: stänger {sym} ({CHART_PATTERNS[k]}, {why}) {pct(ret)}")

    # 1) sälj-regler: kolla varje ljus sedan förra körningen mot stopp/mål
    for sym, p in list(st["pos"].items()):
        b = bars.get(sym)
        if not b:
            continue
        for j in range(len(b)):
            if b.t[j] <= p.get("checked", p["ts"]):
                continue
            hi, lo = b.h[j], b.l[j]
            if p["side"] == "long":
                if lo <= p["stop"]:
                    close(sym, p["stop"], "stopp"); break
                if hi >= p["target"]:
                    close(sym, p["target"], "vinstmål"); break
            else:
                if hi >= p["stop"]:
                    close(sym, p["stop"], "stopp"); break
                if lo <= p["target"]:
                    close(sym, p["target"], "vinstmål"); break
            p["checked"] = b.t[j]
        if sym in st["pos"] and now - st["pos"][sym]["ts"] > CHART_MAX_HOURS * 3.6e6:
            close(sym, prices[sym], "tid")
    # 2) leta nya mönster på nya ljus
    eq = st["cash"] + sum(mark_value(p["cost"], p["entry"], prices.get(s, p["entry"]), p["side"]) for s, p in st["pos"].items())
    for sym, b in bars.items():
        if len(b) == 0 or st["last_bar"].get(sym) == b.t[-1]:
            continue
        st["last_bar"][sym] = b.t[-1]
        if sym in st["pos"] or len(st["pos"]) >= CHART_SLOTS:
            continue
        pats = detect_patterns(b)
        if not pats:
            continue
        # välj mönstret med bäst betyg
        k, d = max(pats, key=lambda x: st["score"].get(x[0], 0.0))
        mult = max(0.25, min(2.0, math.exp(40 * st["score"].get(k, 0.0))))
        cost = min(eq * CHART_BASE * mult, st["cash"])
        atr = _atr(b)
        if cost < MIN_TRADE_USDT or not atr:
            continue
        side = "long" if d > 0 else "short"
        e = entry_price(prices[sym], side)
        stop = e - 1.5 * atr if side == "long" else e + 1.5 * atr
        target = e + 3 * atr if side == "long" else e - 3 * atr
        st["cash"] -= cost
        st["pos"][sym] = {"side": side, "entry": e, "cost": cost, "ts": now, "stop": stop, "target": target,
                          "pattern": k, "checked": b.t[-1]}
        log(f"  Mönster: {CHART_PATTERNS[k]} i {sym} -> {'köper' if side == 'long' else 'blankar'} för {money(cost)} USDT")
    eq = st["cash"] + sum(mark_value(p["cost"], p["entry"], prices.get(s, p["entry"]), p["side"]) for s, p in st["pos"].items())
    st["equity"].append([now, round(eq, 2)])
    st["equity"] = st["equity"][-4000:]
    st["last_prices"] = prices
    with open(CHART_STATE_FILE + ".tmp", "w", encoding="utf-8") as f:
        json.dump(st, f)
    os.replace(CHART_STATE_FILE + ".tmp", CHART_STATE_FILE)
    log(f"Mönsterläsaren: {money(eq)} USDT, {len(st['pos'])} öppna, {len(st['trades'])} avslutade")
    set_timeframe(TIMEFRAME)


def chart_mail_lines(rate, now_ms):
    if not os.path.exists(CHART_STATE_FILE):
        return []
    with open(CHART_STATE_FILE, encoding="utf-8") as f:
        st = json.load(f)
    eqh = st.get("equity") or [[now_ms, START_CAPITAL]]
    eq = eqh[-1][1]
    d24 = next((e for t, e in reversed(eqh) if t <= now_ms - 86000 * 1000), eqh[0][1])
    tr = st["trades"]
    best = max(tr, key=lambda t: t["pnl"]) if tr else None
    worst = min(tr, key=lambda t: t["pnl"]) if tr else None

    def t_txt(t):
        if not t:
            return "inga än"
        return f"{t['symbol'].replace('USDT', '')} ({CHART_PATTERNS[t['pattern']]}) {pct_sv(t['ret'])} = {kr(t['pnl'] * rate, sign=True)}"
    verb = "tjänat" if eq >= START_CAPITAL else "förlorat"
    grades = ", ".join(f"{CHART_PATTERNS[k]} {pct_sv(v)} ({st['count'].get(k, 0)} st)" for k, v in st["score"].items() if st["count"].get(k, 0))
    opens = ", ".join(f"{s.replace('USDT', '')} ({'köpt' if p['side'] == 'long' else 'blankat'}, {CHART_PATTERNS[p['pattern']]})" for s, p in st["pos"].items())
    return [f"**Bot 6 – mönsterläsaren: har {kr(eq * rate)}** – har {verb} {kr(abs(eq - START_CAPITAL) * rate)} totalt ({pct_sv(eq / START_CAPITAL - 1)})  ",
            f"Senaste dygnet: {kr((eq - d24) * rate, sign=True)} · öppna: {len(st['pos'])} · avslutade: {len(tr)}  ",
            f"Bästa affär: {t_txt(best)}  ",
            f"Sämsta affär: {t_txt(worst)}  ",
            f"Öppna: {opens or 'inga – letar mönster'}  ",
            f"Mönstrens betyg (lärt sig hittills): {grades or 'inga avslutade affärer än'}", ""]


# ============================================================================
# BOT 7: MYNTJÄGAREN (letar nästa 100x bland nya småmynt - lotteri med regler)
# ============================================================================
# Skannar DexScreener var 15:e minut (nya och trendande mynt på Solana, Base, BSC, Ethereum).
# Sorterar bort skräp: för lite pengar i handeln, för nya, redan uppblåsta, fler säljare än köpare.
# Köper pyttesmå lotter (2 % av startkapitalet) i många mynt. Vid 2x säljs hälften
# (insatsen tillbaka), resten är en "månbiljett" som får springa tills den faller 60 % från toppen.
# Förlorare: säljs vid -50 %, eller efter 7 dagar utan vinst. Försvinner pengarna ur
# handeln (rugg) räknas nästan allt som förlorat. Avgifter + prispåverkan räknas efter
# hur lite pengar som finns i myntets handel - små mynt är dyra att handla.
GEM_STATE_FILE = os.path.join(HERE, "gem_state.json")
GEM_CHAINS = ("solana", "base", "bsc", "ethereum")
GEM_STAKE = 0.02 * START_CAPITAL
GEM_MAX_POS = 40
GEM_MIN_LIQ, GEM_MIN_VOL24 = 30_000, 100_000
GEM_MIN_AGE_H, GEM_MAX_AGE_D = 6, 30
GEM_MAX_FDV = 50_000_000
GEM_FEE = 0.003              # DEX-avgift per köp/sälj
GEM_STOP = -0.50
GEM_TRAIL = 0.60
GEM_MAX_DAYS = 7
GEM_SCAN_MIN = 15
DEX = "https://api.dexscreener.com"


def _dex(path):
    return json.loads(fetch_text(DEX + path, timeout=20))


def _gem_cost(usd, liq):
    """Avgift + prispåverkan (andel) för att handla usd dollar i ett mynt med liq dollar likviditet."""
    return min(0.9, GEM_FEE + 0.002 + 2 * usd / max(liq, 1.0))   # AMM: påverkan ≈ 2 × affär / likviditet


def gem_candidates(now_ms):
    toks = {}
    for path in ("/token-profiles/latest/v1", "/token-boosts/latest/v1", "/token-boosts/top/v1"):
        try:
            for t in _dex(path):
                if t.get("chainId") in GEM_CHAINS and t.get("tokenAddress"):
                    toks.setdefault(t["chainId"], set()).add(t["tokenAddress"])
        except Exception as e:
            log(f"  Myntjägaren: kunde inte läsa {path} ({e})")
    # fler källor: GeckoTerminals trendande pooler per kedja (gratis, öppet)
    gt = {"solana": "solana", "base": "base", "bsc": "bsc", "ethereum": "eth"}
    for chain, net in gt.items():
        for page in (1, 2):
            try:
                d = json.loads(fetch_text(f"https://api.geckoterminal.com/api/v2/networks/{net}/trending_pools?page={page}", timeout=20))
                for pool in d.get("data", []):
                    tid = pool["relationships"]["base_token"]["data"]["id"]
                    toks.setdefault(chain, set()).add(tid.split("_", 1)[1])
            except Exception as e:
                log(f"  Myntjägaren: GeckoTerminal {net} sida {page} misslyckades ({e})")
            time.sleep(3)                      # max ~30 anrop/minut hos GeckoTerminal
    pairs = []
    for chain, addrs in toks.items():
        addrs = sorted(addrs)
        for i in range(0, len(addrs), 30):
            try:
                pairs += _dex(f"/tokens/v1/{chain}/{','.join(addrs[i:i + 30])}") or []
            except Exception:
                continue
    best = {}
    for p in pairs:                                   # bästa paret per mynt (mest likviditet)
        key = (p.get("chainId"), (p.get("baseToken") or {}).get("address"))
        if (p.get("liquidity") or {}).get("usd", 0) > (best.get(key, {}).get("liquidity") or {}).get("usd", -1):
            best[key] = p
    out = []
    for p in best.values():
        try:
            liq = float(p["liquidity"]["usd"]); vol = float(p["volume"]["h24"]); price = float(p["priceUsd"])
            age_h = (now_ms - int(p["pairCreatedAt"])) / 3.6e6
            fdv = float(p.get("fdv") or p.get("marketCap") or 0)
            h1 = p["txns"]["h1"]; buys, sells = h1["buys"], h1["sells"]
            ch1, ch24 = float(p["priceChange"].get("h1", 0)), float(p["priceChange"].get("h24", 0))
            quote = (p.get("quoteToken") or {}).get("symbol", "")
        except Exception:
            continue
        if (liq < GEM_MIN_LIQ or vol < GEM_MIN_VOL24 or not (GEM_MIN_AGE_H <= age_h <= GEM_MAX_AGE_D * 24)
                or not (0 < fdv <= GEM_MAX_FDV) or fdv / liq > 60 or buys + sells < 100
                or buys < sells * 1.1 or ch1 <= 0 or not (0 < ch24 < 500) or price <= 0
                or quote not in ("SOL", "WETH", "ETH", "WBNB", "BNB", "USDC", "USDT")):
            continue
        score = min(vol / liq, 20) * (buys / max(sells, 1)) * (1 + min(ch1, 50) / 100)
        out.append((score, p))
    out.sort(key=lambda x: -x[0])
    return [p for _s, p in out]


def run_gem_watch(minutes=55):
    st = None
    if os.path.exists(GEM_STATE_FILE):
        try:
            with open(GEM_STATE_FILE, encoding="utf-8") as f:
                st = json.load(f)
        except Exception:
            st = None
    if not st:
        st = {"start_ms": int(time.time() * 1000), "cash": START_CAPITAL, "pos": {}, "trades": [], "equity": [],
              "seen": {}, "last_scan": 0}
        log("Myntjägaren startar med 10 000 låtsas-USDT")
    end = time.time() + minutes * 60
    last_upd = 0

    def value(p):
        return p["qty"] * p["price"] * (1 - _gem_cost(p["qty"] * p["price"], p["liq"]))

    def equity():
        return st["cash"] + sum(value(p) for p in st["pos"].values())

    def sell(key, frac, now, why, rug=False):
        p = st["pos"][key]
        got = value(p) * frac * (0.3 if rug else 1.0)
        cost = p["cost"] * frac
        st["cash"] += got
        st["trades"].append({"symbol": p["name"], "side": "long", "ret": got / cost - 1, "pnl": got - cost,
                             "entry_ts": p["ts"], "exit_ts": now, "reason": why, "cost": cost, "chain": p["chain"],
                             "url": p.get("url")})
        st["trades"] = st["trades"][-5000:]
        p["qty"] *= (1 - frac); p["cost"] -= cost
        if frac >= 0.999:
            del st["pos"][key]

    def update(now):
        by_chain = {}
        for key, p in st["pos"].items():
            by_chain.setdefault(p["chain"], []).append(p["pair"])
        fresh = {}
        for chain, prs in by_chain.items():
            for i in range(0, len(prs), 30):
                try:
                    for q in (_dex(f"/latest/dex/pairs/{chain}/{','.join(prs[i:i + 30])}").get("pairs") or []):
                        fresh[q["pairAddress"]] = q
                except Exception:
                    continue
        for key, p in list(st["pos"].items()):
            q = fresh.get(p["pair"])
            if q is None:
                p["missing"] = p.get("missing", 0) + 1
                if p["missing"] >= 30:                # borta i 30 min -> rugg
                    sell(key, 1.0, now, "försvann (rugg)", rug=True)
                continue
            p["missing"] = 0
            try:
                p["price"] = float(q["priceUsd"]); p["liq"] = float(q["liquidity"]["usd"])
            except Exception:
                continue
            x = p["price"] / p["entry"]
            p["peak"] = max(p.get("peak", 1.0), x)
            if p["liq"] < 0.25 * p["liq0"]:
                sell(key, 1.0, now, "likviditeten försvann (rugg)", rug=True)
            elif not p.get("half") and x >= 2.0:
                sell(key, 0.5, now, "2x – hälften såld, insatsen hemma")
                st["pos"][key]["half"] = True
            elif p.get("half") and x <= p["peak"] * (1 - GEM_TRAIL):
                sell(key, 1.0, now, f"månbiljetten såld ({p['peak']:.1f}x topp)")
            elif not p.get("half") and x - 1 <= GEM_STOP:
                sell(key, 1.0, now, "stopp −50 %")
            elif not p.get("half") and now - p["ts"] > GEM_MAX_DAYS * 86400000 and x < 1.0:
                sell(key, 1.0, now, "7 dagar utan vinst")

    def scan(now):
        cands = gem_candidates(now)
        bought = 0
        held = {(p["chain"], p["token"]) for p in st["pos"].values()}
        for p in cands:
            if bought >= 3 or len(st["pos"]) >= GEM_MAX_POS or st["cash"] < GEM_STAKE:
                break
            tok = (p["chainId"], p["baseToken"]["address"])
            if tok in held or st["seen"].get(f"{tok[0]}:{tok[1]}", 0) > now - 3 * 86400000:
                continue
            liq, price = float(p["liquidity"]["usd"]), float(p["priceUsd"])
            qty = GEM_STAKE * (1 - _gem_cost(GEM_STAKE, liq)) / price
            name = f"{p['baseToken']['symbol'][:12]} ({p['chainId']})"
            key = f"{name}#{p['pairAddress'][-4:]}"
            st["cash"] -= GEM_STAKE
            st["pos"][key] = {"name": name, "chain": p["chainId"], "pair": p["pairAddress"], "token": tok[1],
                              "entry": price, "price": price, "qty": qty, "cost": GEM_STAKE, "liq": liq, "liq0": liq,
                              "ts": now, "peak": 1.0, "url": p.get("url")}
            st["seen"][f"{tok[0]}:{tok[1]}"] = now
            held.add(tok)
            bought += 1
            log(f"  Myntjägaren köper {name}: likviditet {liq:,.0f} $, handel 24h {float(p['volume']['h24']):,.0f} $")
        log(f"  Myntjägaren: {len(cands)} kandidater klarade filtren, köpte {bought}")

    while time.time() < end:
        now = int(time.time() * 1000)
        try:
            if now - st.get("last_scan", 0) >= GEM_SCAN_MIN * 60000:
                scan(now)
                st["last_scan"] = now
        except Exception as e:
            log(f"  Myntjägaren: skanningen misslyckades ({e})")
        try:
            update(now)
        except Exception as e:
            log(f"  Myntjägaren: prisuppdatering misslyckades ({e})")
        st["equity"].append([now, round(equity(), 2)])
        st["equity"] = st["equity"][-6000:]
        st["last_prices"] = {k: p["price"] for k, p in st["pos"].items()}
        st["seen"] = {k: v for k, v in st["seen"].items() if v > now - 3 * 86400000}
        with open(GEM_STATE_FILE + ".tmp", "w", encoding="utf-8") as f:
            json.dump(st, f)
        os.replace(GEM_STATE_FILE + ".tmp", GEM_STATE_FILE)
        time.sleep(max(1.0, min(60.0, end - time.time())))
    log(f"Myntjägaren: {money(equity())} USDT, {len(st['pos'])} lotter, {len(st['trades'])} försäljningar")


def gem_mail_lines(rate, now_ms):
    if not os.path.exists(GEM_STATE_FILE):
        return []
    with open(GEM_STATE_FILE, encoding="utf-8") as f:
        st = json.load(f)
    eqh = st.get("equity") or [[now_ms, START_CAPITAL]]
    eq = eqh[-1][1]
    d24 = next((e for t, e in reversed(eqh) if t <= now_ms - 86000 * 1000), eqh[0][1])
    pos = st["pos"]
    best = max(pos.values(), key=lambda p: p["price"] / p["entry"]) if pos else None
    verb = "tjänat" if eq >= START_CAPITAL else "förlorat"
    moon = sum(1 for p in pos.values() if p.get("half"))
    return [f"**Bot 7 – myntjägaren: har {kr(eq * rate)}** – har {verb} {kr(abs(eq - START_CAPITAL) * rate)} totalt ({pct_sv(eq / START_CAPITAL - 1)})  ",
            f"Senaste dygnet: {kr((eq - d24) * rate, sign=True)} · lotter: {len(pos)} · månbiljetter (2x+): {moon} · försäljningar: {len(st['trades'])}  ",
            f"Bästa lott just nu: {best['name'] + ' ' + format(best['price'] / best['entry'], '.2f') + 'x' if best else 'inga än'}", ""]


# ============================================================================
# BOT 8: KOPIERAREN (härmar kända memecoin-traders plånböcker på Solana)
# ============================================================================
# Läser deras affärer direkt från blockkedjan (offentligt). När de köper ett mynt köper
# boten samma mynt med en liten insats; när de säljer säljer boten samma andel.
# Vi kommer alltid in lite senare och till sämre pris än dem - det räknas med.
COPY_STATE_FILE = os.path.join(HERE, "copy_state.json")
COPY_WALLETS = {   # namn: offentlig Solana-plånbok (från KOL-trackers; topplistor efter 30-dagars vinst)
    "Cented": "CyaE1VxvBrahnPWkqm5VsdCvyS2QmNht2UFrKJHga54o",
    "Theo": "Bi4rd5FH5bYEN8scZ7wevxNZyNmKHdaBcvewdPFxYdLt",
    "Cupsey": "2fg5QD1eD7rzNNCsvnhmXFm5hqNgwTTG8p7kQ6f3rx6f",
    "Decu": "4vw54BmAogeRV3vPKWyFet5yf8DTLcREzdSzx4rw9Ud9",
    "Pain": "J6TDXvarvpBdPXTaTU8eJbtso1PUCYKGkVtMKUUY8iEa",
    "Kadenox": "B32QbbdDAyhvUQzjcaM5j6ZVKwjCxAwGH5Xgvb9SJqnC",
    "Trunoest": "ardinRsN1mNYVeoJWTBsWeYeXvuR9UUDGMsCDKpb6AT",
    "Kev": "BTf4A2exGK9BCVDNzy65b9dUzXgMqB4weVkvTMFQsadd",
    "West": "JDd3hy3gQn2V982mi1zqhNqUw1GfV2UL6g76STojCJPN",
    "Yugi": "4TCMpxeevymUtCemwcVozhBLWq8Fikc1pVpfcW9zp66B",
}
COPY_STAKE = 0.01            # andel av pengarna per kopierat köp
COPY_MIN_SOL = 0.5           # kopiera alla riktiga köp (hoppar bara över damm/avgifter under 0,5 SOL)
COPY_MAX_POS = 30
COPY_STOP = -0.70
COPY_MAX_HOURS = 48
SOL_RPCS = ["https://solana-rpc.publicnode.com", "https://api.mainnet-beta.solana.com"]   # snabbast först
WSOL = "So11111111111111111111111111111111111111112"
STABLES = {"EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v", "Es9vMFrzaCERmJfrF4H2FYD4KCoNkY11McCe8BenwNYB"}


def _rpc(method, params):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
    last_err = None
    for url in SOL_RPCS:                       # snabba noden först, reserv om den krånglar
        try:
            req = urllib.request.Request(url, data=body, headers={"Content-Type": "application/json",
                                                                  "User-Agent": "paper-bot/1.0"})
            with urllib.request.urlopen(req, timeout=10) as r:
                d = json.loads(r.read().decode())
            if "error" in d:
                raise RuntimeError(d["error"].get("message"))
            return d["result"]
        except Exception as e:
            last_err = e
    raise last_err


def parse_swap(tx, wallet):
    """(mint, 'buy'/'sell', sol_belopp, andel_såld) eller None."""
    if not tx or tx["meta"].get("err"):
        return None
    raw = tx["transaction"]["message"]["accountKeys"]
    keys = [k["pubkey"] if isinstance(k, dict) else k for k in raw]
    if wallet not in keys:
        return None
    i = keys.index(wallet)
    if isinstance(raw[i], dict) and not raw[i].get("signer"):
        return None                              # någon annans transaktion som bara nämner plånboken
    sol = (tx["meta"]["postBalances"][i] - tx["meta"]["preBalances"][i]) / 1e9
    pre, post = {}, {}
    for side, arr in ((pre, tx["meta"].get("preTokenBalances") or []), (post, tx["meta"].get("postTokenBalances") or [])):
        for b in arr:
            if b.get("owner") == wallet:
                side[b["mint"]] = side.get(b["mint"], 0.0) + float(b["uiTokenAmount"].get("uiAmount") or 0)
    sol += post.get(WSOL, 0.0) - pre.get(WSOL, 0.0)
    best = None
    for mint in set(pre) | set(post):
        if mint == WSOL or mint in STABLES:
            continue
        d = post.get(mint, 0.0) - pre.get(mint, 0.0)
        if abs(d) > 0 and (best is None or abs(d) > abs(best[1])):
            best = (mint, d)
    if not best:
        return None
    mint, d = best
    if d > 0 and sol < 0:
        return mint, "buy", -sol, 0.0
    if d < 0 and sol > 0:
        return mint, "sell", sol, min(1.0, -d / max(pre.get(mint, 0.0), 1e-12))
    return None


def _token_market(mint):
    """(pris, likviditet, namn, url) från DexScreener."""
    pairs = _dex(f"/tokens/v1/solana/{mint}") or []
    if not pairs:
        return None
    p = max(pairs, key=lambda q: (q.get("liquidity") or {}).get("usd", 0) or 0)
    price = float(p.get("priceUsd") or 0)
    if price <= 0:
        return None
    liq = float((p.get("liquidity") or {}).get("usd") or 0) or max(5000.0, 0.2 * float(p.get("marketCap") or 0))
    return price, liq, p["baseToken"]["symbol"][:12], p.get("url")


def run_copy_watch(minutes=55):
    st = None
    if os.path.exists(COPY_STATE_FILE):
        try:
            with open(COPY_STATE_FILE, encoding="utf-8") as f:
                st = json.load(f)
        except Exception:
            st = None
    if not st:
        st = {"start_ms": int(time.time() * 1000), "cash": START_CAPITAL, "pos": {}, "trades": [], "equity": [],
              "last_sig": {}, "seen_kol": {}}
        log("Kopieraren startar med 10 000 låtsas-USDT")
    end = time.time() + minutes * 60
    last_px = 0

    def value(p):
        return p["qty"] * p["price"] * (1 - _gem_cost(p["qty"] * p["price"], p["liq"]))

    def equity():
        return st["cash"] + sum(value(p) for p in st["pos"].values())

    def sell(mint, frac, now, why):
        p = st["pos"][mint]
        got = value(p) * frac
        cost = p["cost"] * frac
        st["cash"] += got
        st["trades"].append({"symbol": p["name"], "side": "long", "ret": got / cost - 1, "pnl": got - cost,
                             "entry_ts": p["ts"], "exit_ts": now, "reason": why, "cost": cost, "kol": p["kol"],
                             "url": p.get("url")})
        st["trades"] = st["trades"][-5000:]
        p["qty"] *= (1 - frac); p["cost"] -= cost
        if frac >= 0.98 or p["cost"] < 1:
            del st["pos"][mint]

    import threading, queue
    found = queue.Queue()
    stop_flag = threading.Event()

    def watcher(kol, wallet):
        """Egen tråd per trader: kollar plånboken varje sekund, lägger hittade köp/sälj i kön."""
        wait = 1.0
        while not stop_flag.is_set():
            t0 = time.time()
            try:
                last = st["last_sig"].get(kol)
                opts = {"limit": 1000}   # kända plånböcker får ~20 skräptransaktioner/s, filtreras bort nedan
                if last:
                    opts["until"] = last
                sigs = _rpc("getSignaturesForAddress", [wallet, opts])
                if sigs:
                    st["last_sig"][kol] = sigs[0]["signature"]
                    ok = [x for x in sigs if not x.get("err")][:15] if last else []
                    for sg in reversed(ok):
                        try:
                            tx = _rpc("getTransaction", [sg["signature"], {"encoding": "jsonParsed", "maxSupportedTransactionVersion": 1}])
                            sw = parse_swap(tx, wallet)
                        except Exception:
                            continue
                        if sw:
                            found.put((kol, sw, int(time.time() * 1000), sg.get("blockTime")))
                wait = max(1.0, wait * 0.8)
            except Exception as e:
                if "429" in str(e):
                    wait = min(8.0, wait * 2)        # för många anrop -> sakta ner en stund
                else:
                    log(f"  Kopieraren: kunde inte läsa {kol} ({e})")
            stop_flag.wait(max(0.0, wait - (time.time() - t0)))

    def act(kol, sw, now, block_time):
        mint, kind, sol_amt, frac = sw
        st["seen_kol"][kol] = st["seen_kol"].get(kol, 0) + 1
        lag = (now / 1000 - block_time) if block_time else None
        if kind == "buy" and sol_amt >= COPY_MIN_SOL and mint not in st["pos"] and len(st["pos"]) < COPY_MAX_POS:
            m = _token_market(mint)
            if not m:
                return
            price, liq, name, url = m
            stake = min(equity() * COPY_STAKE, st["cash"])
            if stake < MIN_TRADE_USDT:
                return
            st["cash"] -= stake
            st["pos"][mint] = {"name": f"{name} ({kol})", "kol": kol, "entry": price, "price": price, "liq": liq,
                               "qty": stake * (1 - _gem_cost(stake, liq)) / price, "cost": stake, "ts": now,
                               "url": url, "kol_sol": sol_amt, "lag_s": lag}
            log(f"  Kopieraren: {kol} köpte {name} för {sol_amt:.1f} SOL -> köper för {stake:.0f} USDT"
                + (f" ({lag:.0f} s efter)" if lag is not None else ""))
        elif kind == "sell" and mint in st["pos"] and st["pos"][mint]["kol"] == kol:
            p = st["pos"][mint]
            m = _token_market(mint)
            if m:
                p["price"], p["liq"] = m[0], m[1]
            sell(mint, 1.0 if frac > 0.9 else frac, now, f"{kol} sålde {frac * 100:.0f} %")

    threads = [threading.Thread(target=watcher, args=(k, w), daemon=True) for k, w in COPY_WALLETS.items()]
    for i, t in enumerate(threads):
        t.start()
        time.sleep(0.1)

    while time.time() < end:
        now = int(time.time() * 1000)
        while not found.empty():
            kol, sw, ts, bt = found.get()
            try:
                act(kol, sw, ts, bt)
            except Exception as e:
                log(f"  Kopieraren: kunde inte kopiera {kol} ({e})")
        if time.time() - last_px > 60 and st["pos"]:
            last_px = time.time()
            for mint, p in list(st["pos"].items()):
                try:
                    m = _token_market(mint)
                except Exception:
                    m = None
                if not m:
                    continue
                p["price"], p["liq"] = m[0], m[1]
                r = p["price"] / p["entry"] - 1
                if r <= COPY_STOP:
                    sell(mint, 1.0, now, "stopp −70 %")
                elif now - p["ts"] > COPY_MAX_HOURS * 3600000:
                    sell(mint, 1.0, now, "48 timmar – släpper")
        if not st["equity"] or now - st["equity"][-1][0] >= 60000:
            st["equity"].append([now, round(equity(), 2)])
            st["equity"] = st["equity"][-6000:]
            st["last_prices"] = {k: p["price"] for k, p in st["pos"].items()}
            with open(COPY_STATE_FILE + ".tmp", "w", encoding="utf-8") as f:
                json.dump(st, f)
            os.replace(COPY_STATE_FILE + ".tmp", COPY_STATE_FILE)
        time.sleep(max(0.0, min(0.2, end - time.time())))
    stop_flag.set()
    st["equity"].append([int(time.time() * 1000), round(equity(), 2)])
    st["last_prices"] = {k: p["price"] for k, p in st["pos"].items()}
    with open(COPY_STATE_FILE + ".tmp", "w", encoding="utf-8") as f:
        json.dump(st, f)
    os.replace(COPY_STATE_FILE + ".tmp", COPY_STATE_FILE)
    log(f"Kopieraren: {money(equity())} USDT, {len(st['pos'])} öppna, {len(st['trades'])} försäljningar")


def copy_trader_stats(st):
    """Per trader: insatt, resultat (avslutat + öppet) och procent."""
    out = {k: {"stake": 0.0, "pnl": 0.0, "n": 0, "open": 0} for k in COPY_WALLETS}
    for t in st.get("trades", []):
        o = out.setdefault(t["kol"], {"stake": 0.0, "pnl": 0.0, "n": 0, "open": 0})
        o["stake"] += t.get("cost", 0); o["pnl"] += t["pnl"]; o["n"] += 1
    for p in st.get("pos", {}).values():
        o = out.setdefault(p["kol"], {"stake": 0.0, "pnl": 0.0, "n": 0, "open": 0})
        v = p["qty"] * p["price"] * (1 - _gem_cost(p["qty"] * p["price"], p["liq"]))
        o["stake"] += p["cost"]; o["pnl"] += v - p["cost"]; o["open"] += 1
    for o in out.values():
        o["pct"] = o["pnl"] / o["stake"] if o["stake"] else 0.0
    return out


def copy_mail_lines(rate, now_ms):
    if not os.path.exists(COPY_STATE_FILE):
        return []
    with open(COPY_STATE_FILE, encoding="utf-8") as f:
        st = json.load(f)
    eqh = st.get("equity") or [[now_ms, START_CAPITAL]]
    eq = eqh[-1][1]
    d24 = next((e for t, e in reversed(eqh) if t <= now_ms - 86000 * 1000), eqh[0][1])
    per = copy_trader_stats(st)
    verb = "tjänat" if eq >= START_CAPITAL else "förlorat"
    who = ", ".join(f"{k} {pct_sv(v['pct'])}" for k, v in sorted(per.items(), key=lambda x: -x[1]["pct"]) if v["stake"]) or "inga kopierade affärer än"
    return [f"**Bot 8 – kopieraren: har {kr(eq * rate)}** – har {verb} {kr(abs(eq - START_CAPITAL) * rate)} totalt ({pct_sv(eq / START_CAPITAL - 1)})  ",
            f"Senaste dygnet: {kr((eq - d24) * rate, sign=True)} · öppna: {len(st['pos'])} · försäljningar: {len(st['trades'])}  ",
            f"Resultat per trader: {who}", ""]


# ============================================================================
# BOT 9: NYHETSJÄGAREN (letar okända projekt med något stort på gång)
# ============================================================================
# Läser kryptonyheter från många källor varannan minut. Letar "katalysatorer" för MINDRE
# projekt (inte topp-50): börsnoteringar (Binance/Coinbase/Upbit...), finansieringsrundor,
# lanseringar (mainnet), stora samarbeten, ETF-ansökningar. Köper myntet direkt efter
# nyheten om det inte redan rusat. Säljer hälften vid +30 %, resten med släpande stopp.
# Dålig nyhet om myntet (hack, stämning...) -> säljer direkt. Lär sig vilka sorters
# nyheter som faktiskt ger pengar och satsar mer på dem.
NEWS9_STATE_FILE = os.path.join(HERE, "news_state.json")
NEWS9_FEEDS = NEWS_FEEDS + ["https://www.theblock.co/rss.xml", "https://cryptoslate.com/feed/",
                            "https://bitcoinmagazine.com/.rss/full/", "https://u.today/rss",
                            "https://www.newsbtc.com/feed/", "https://cryptopotato.com/feed/",
                            "https://beincrypto.com/feed/", "https://coinjournal.net/feed/"]
NEWS9_CATALYSTS = {
    "notering": (r"\b(binance|coinbase|upbit|bithumb|robinhood|okx|bybit|kraken|kucoin)\b.{0,60}\b(lists?|listing|to list|will list|adds?|launch(es)? trading)\b"
                 r"|\b(lists?|listing|adds?)\b.{0,60}\b(binance|coinbase|upbit|bithumb|robinhood|okx|bybit|kraken)\b", 1.0),
    "finansiering": (r"\braises? \$?\d|\bfunding round\b|\bseries [abc]\b|\bseed round\b|\bsecures? \$\d", 0.6),
    "etf": (r"\betf\b.{0,40}\b(fil(e|es|ed|ing)|approv|launch)", 0.8),
    "lansering": (r"\bmainnet\b|\bgoes live\b|\blaunch(es|ed)?\b.{0,30}\b(v2|v3|chain|network|protocol)\b", 0.5),
    "samarbete": (r"\bpartner(s|ship)? with\b|\bintegrat(es|ion) with\b|\bteams up with\b|\bselected by\b", 0.5),
}
NEWS9_STAKE = 0.05
NEWS9_MAX_POS = 10
NEWS9_MIN_RANK = 51          # inte de 50 största - vi letar det okända
NEWS9_MIN_MCAP, NEWS9_MAX_MCAP = 5e6, 2e9
NEWS9_STOP, NEWS9_TP, NEWS9_TRAIL, NEWS9_MAX_DAYS = -0.12, 0.30, 0.15, 5
NEWS9_COST = 0.004           # avgift + slippage per köp/sälj (börs, mindre mynt)
CG = "https://api.coingecko.com/api/v3"


def _cg(path):
    return json.loads(fetch_text(CG + path, timeout=20))


def news9_markets():
    """Topp ~1000 mynt efter värde (rank, namn, symbol, pris) från CoinGecko."""
    out = []
    for page in (1, 2, 3, 4):
        try:
            out += _cg(f"/coins/markets?vs_currency=usd&order=market_cap_desc&per_page=250&page={page}&price_change_percentage=24h")
        except Exception as e:
            log(f"  Nyhetsjägaren: CoinGecko sida {page} misslyckades ({e})")
        time.sleep(6)
    return out


def news9_match(title, markets):
    """Hitta vilket (mindre) mynt en rubrik handlar om. Returnerar CoinGecko-raden eller None."""
    import re
    low = " " + title.lower() + " "
    best = None
    for m in markets:
        rank = m.get("market_cap_rank") or 99999
        if rank < NEWS9_MIN_RANK:
            continue
        name, sym = (m.get("name") or "").lower(), (m.get("symbol") or "").upper()
        hit = False
        if len(name) >= 4 and re.search(r"(?<![a-z0-9])" + re.escape(name) + r"(?![a-z0-9])", low):
            hit = True
        elif len(sym) >= 3 and re.search(r"(\(|\$)" + re.escape(sym) + r"\b", title):
            hit = True
        if hit and (best is None or rank < (best.get("market_cap_rank") or 99999)):
            best = m
    return best


def news9_catalyst(title):
    import re
    low = title.lower()
    for kind, (rx, w) in NEWS9_CATALYSTS.items():
        if re.search(rx, low):
            return kind, w
    return None


def run_news_watch(minutes=55):
    st = None
    if os.path.exists(NEWS9_STATE_FILE):
        try:
            with open(NEWS9_STATE_FILE, encoding="utf-8") as f:
                st = json.load(f)
        except Exception:
            st = None
    if not st:
        st = {"start_ms": int(time.time() * 1000), "cash": START_CAPITAL, "pos": {}, "trades": [], "equity": [],
              "seen": [], "markets_ts": 0, "score": {}, "log": []}
        log("Nyhetsjägaren startar med 10 000 låtsas-USDT")
    first_run = not st["seen"]
    markets = []
    end = time.time() + minutes * 60
    last_news = last_px = 0

    def value(p):
        return p["qty"] * p["price"] * (1 - NEWS9_COST)

    def equity():
        return st["cash"] + sum(value(p) for p in st["pos"].values())

    def sell(cid, frac, now, why):
        p = st["pos"][cid]
        got = value(p) * frac
        cost = p["cost"] * frac
        st["cash"] += got
        st["trades"].append({"symbol": p["name"], "side": "long", "ret": got / cost - 1, "pnl": got - cost, "entry_ts": p["ts"],
                             "exit_ts": now, "reason": why, "cost": cost, "kind": p["kind"], "news": p["news"]})
        st["trades"] = st["trades"][-5000:]
        p["qty"] *= (1 - frac); p["cost"] -= cost
        if frac >= 0.999:
            del st["pos"][cid]
            sc = st["score"].setdefault(p["kind"], [])
            sc.append(round(got / cost - 1, 4) if cost else 0)
            del sc[:-10]

    def size_factor(kind):
        sc = st["score"].get(kind) or []
        if len(sc) < 3:
            return 1.0
        return max(0.5, min(1.5, 1 + 5 * sum(sc) / len(sc)))

    while time.time() < end:
        now = int(time.time() * 1000)
        if not markets or now - st.get("markets_ts", 0) > 30 * 60000:
            m = news9_markets()
            if m:
                markets = m
                st["markets_ts"] = now
        if time.time() - last_news >= 120 and markets:
            last_news = time.time()
            heads = []
            for url in NEWS9_FEEDS:
                try:
                    import xml.etree.ElementTree as ET
                    root = ET.fromstring(fetch_text(url))
                    for it in root.iter("item"):
                        t = (it.findtext("title") or "").strip()
                        if t:
                            heads.append({"title": t, "link": (it.findtext("link") or "").strip(), "src": url.split("/")[2]})
                except Exception:
                    continue
            seen = set(st["seen"])
            for h in heads:
                key = h["title"][:120]
                if key in seen:
                    continue
                st["seen"].append(key); seen.add(key)
                if first_run:
                    continue                          # gamla nyheter vid första start räknas inte
                low = h["title"].lower()
                m = news9_match(h["title"], markets)
                if not m:
                    continue
                cid = m["id"]
                # dålig nyhet om ett mynt vi äger -> sälj
                if cid in st["pos"] and any(w in low for w in BAD_WORDS):
                    sell(cid, 1.0, now, "dålig nyhet: " + h["title"][:80])
                    continue
                cat = news9_catalyst(h["title"])
                if not cat or any(w in low for w in BAD_WORDS) or cid in st["pos"] or len(st["pos"]) >= NEWS9_MAX_POS:
                    continue
                kind, w = cat
                mcap = m.get("market_cap") or 0
                ch24 = m.get("price_change_percentage_24h") or 0
                if not (NEWS9_MIN_MCAP <= mcap <= NEWS9_MAX_MCAP) or ch24 > 40 or not m.get("current_price"):
                    continue
                try:
                    price = float(_cg(f"/simple/price?ids={cid}&vs_currencies=usd")[cid]["usd"])
                except Exception:
                    price = float(m["current_price"])
                stake = min(equity() * NEWS9_STAKE * w * size_factor(kind), st["cash"])
                if stake < MIN_TRADE_USDT:
                    continue
                st["cash"] -= stake
                st["pos"][cid] = {"name": f"{m['symbol'].upper()} ({kind})", "kind": kind, "entry": price, "price": price,
                                  "qty": stake * (1 - NEWS9_COST) / price, "cost": stake, "ts": now, "peak": 1.0,
                                  "news": h["title"][:160], "link": h["link"], "rank": m.get("market_cap_rank")}
                st["log"].append([now, kind, m["symbol"].upper(), h["title"][:160]])
                st["log"] = st["log"][-200:]
                log(f"  Nyhetsjägaren köper {m['symbol'].upper()} (rank {m.get('market_cap_rank')}, {kind}): {h['title'][:90]}")
            st["seen"] = st["seen"][-3000:]
            first_run = False
        if time.time() - last_px >= 60 and st["pos"]:
            last_px = time.time()
            try:
                px = _cg(f"/simple/price?ids={','.join(st['pos'])}&vs_currencies=usd")
            except Exception:
                px = {}
            for cid, p in list(st["pos"].items()):
                if cid not in px:
                    continue
                p["price"] = float(px[cid]["usd"])
                x = p["price"] / p["entry"]
                p["peak"] = max(p.get("peak", 1.0), x)
                if not p.get("half") and x - 1 >= NEWS9_TP:
                    sell(cid, 0.5, now, "+30 % – hälften såld")
                    st["pos"][cid]["half"] = True
                elif p.get("half") and x <= p["peak"] * (1 - NEWS9_TRAIL):
                    sell(cid, 1.0, now, f"släpande stopp ({(p['peak'] - 1) * 100:.0f} % som mest)")
                elif x - 1 <= NEWS9_STOP:
                    sell(cid, 1.0, now, "stopp −12 %")
                elif now - p["ts"] > NEWS9_MAX_DAYS * 86400000:
                    sell(cid, 1.0, now, "5 dagar – nyheten är gammal")
        if not st["equity"] or now - st["equity"][-1][0] >= 60000:
            st["equity"].append([now, round(equity(), 2)])
            st["equity"] = st["equity"][-6000:]
            st["last_prices"] = {k: p["price"] for k, p in st["pos"].items()}
            with open(NEWS9_STATE_FILE + ".tmp", "w", encoding="utf-8") as f:
                json.dump(st, f)
            os.replace(NEWS9_STATE_FILE + ".tmp", NEWS9_STATE_FILE)
        time.sleep(max(0.0, min(5.0, end - time.time())))
    st["equity"].append([int(time.time() * 1000), round(equity(), 2)])
    with open(NEWS9_STATE_FILE + ".tmp", "w", encoding="utf-8") as f:
        json.dump(st, f)
    os.replace(NEWS9_STATE_FILE + ".tmp", NEWS9_STATE_FILE)
    log(f"Nyhetsjägaren: {money(equity())} USDT, {len(st['pos'])} öppna, {len(st['trades'])} försäljningar")


def news9_mail_lines(rate, now_ms):
    if not os.path.exists(NEWS9_STATE_FILE):
        return []
    with open(NEWS9_STATE_FILE, encoding="utf-8") as f:
        st = json.load(f)
    eqh = st.get("equity") or [[now_ms, START_CAPITAL]]
    eq = eqh[-1][1]
    d24 = next((e for t, e in reversed(eqh) if t <= now_ms - 86000 * 1000), eqh[0][1])
    verb = "tjänat" if eq >= START_CAPITAL else "förlorat"
    opens = ", ".join(p["name"] for p in st["pos"].values()) or "inga – väntar på rätt nyhet"
    last = st.get("log", [])[-1:] 
    return [f"**Bot 9 – nyhetsjägaren: har {kr(eq * rate)}** – har {verb} {kr(abs(eq - START_CAPITAL) * rate)} totalt ({pct_sv(eq / START_CAPITAL - 1)})  ",
            f"Senaste dygnet: {kr((eq - d24) * rate, sign=True)} · öppna: {opens}  ",
            f"Senaste köpnyhet: {last[0][3] if last else 'ingen än'}", ""]


def run_trend_live(mode="long", once=False, watch_minutes=0):
    """Kör trendmodellen live med papperspengar. Kollar priser varje minut,
    ombalanserar en gång per dygn (när dagsljuset stänger, kl 01:00 svensk vintertid)."""
    set_timeframe("1d")
    apply_trend_config(load_trend_config(mode))
    if not once:
        keep_awake()
    suffix = "" if mode == "long" else "_langkort"
    path = TREND_REPORT.replace(".html", f"_live{suffix}.html")
    state_file = TREND_STATE_FILE.replace(".json", f"{suffix}.json")
    st = None
    if os.path.exists(state_file):
        try:
            with open(state_file, encoding="utf-8") as f:
                st = json.load(f)
        except Exception:
            st = None
    if not st:
        st = {"start_ms": int(time.time() * 1000), "cash": START_CAPITAL, "pos": {}, "trades": [],
              "equity": [], "last_day": None, "mode": mode, "start_prices": {}}
        log(f"Trendmodellen startar med {money(START_CAPITAL)} låtsas-USDT ({'bara lång' if mode == 'long' else 'lång + kort'})")
    else:
        log(f"Fortsätter trendmodellen ({len(st['trades'])} avslutade affärer hittills)")
    log(f"Rapport: {path}")
    prices, opened, hist = {}, False, {}

    def value(sym, p):
        q = st["pos"][sym]["qty"]
        a = st["pos"][sym]["avg"]
        return st["pos"][sym]["margin"] * (1 - FEE) + q * (p - a)   # lång (q>0) och kort (q<0)

    def equity():
        return st["cash"] + sum(value(s, prices.get(s, st["pos"][s]["avg"])) for s in st["pos"])

    def trade_to(sym, target_w, p, now):
        eq = equity()
        cur = st["pos"].get(sym)
        cur_val = (cur["qty"] * p) if cur else 0.0
        tgt_val = target_w * eq
        if abs(tgt_val - cur_val) < TREND_MIN_TRADE * eq and not (target_w == 0 and cur):
            return
        # stäng befintlig position helt om riktningen byts eller målet är 0 / minskar
        if cur and (target_w == 0 or (target_w > 0) != (cur["qty"] > 0) or abs(tgt_val) < abs(cur_val)):
            close_frac = 1.0 if (target_w == 0 or (target_w > 0) != (cur["qty"] > 0)) else 1 - abs(tgt_val) / abs(cur_val)
            q = cur["qty"] * close_frac
            fill = exit_price(p, "long" if q > 0 else "short")
            margin = cur["margin"] * close_frac
            back = margin * (1 - FEE) + q * (fill - cur["avg"]) - abs(q * fill) * FEE
            pnl = back - margin
            st["cash"] += back
            cur["qty"] -= q
            cur["margin"] -= margin
            st["trades"].append({"symbol": sym, "side": "long" if q > 0 else "short", "entry": cur["avg"], "exit": fill,
                                 "cost": margin, "pnl": pnl, "ret": pnl / margin if margin else 0,
                                 "entry_ts": cur["ts"], "exit_ts": now, "reason": "trendsignal"})
            log(f"  {'SÅLT' if q > 0 else 'TÄCKT'} {sym} {abs(close_frac) * 100:.0f}% av positionen: {money(pnl)} USDT")
            if abs(cur["qty"]) * p < 1:
                del st["pos"][sym]
                cur = None
            cur_val = cur["qty"] * p if cur else 0.0
        add = tgt_val - cur_val
        if abs(add) >= MIN_TRADE_USDT and (add > 0) == (target_w > 0):
            side = "long" if target_w > 0 else "short"
            fill = entry_price(p, side)
            margin = min(abs(add), st["cash"])
            if margin < MIN_TRADE_USDT:
                return
            q = margin * (1 - FEE) / fill * (1 if side == "long" else -1)
            st["cash"] -= margin
            if cur:
                tot = cur["qty"] + q
                cur["avg"] = (cur["qty"] * cur["avg"] + q * fill) / tot
                cur["qty"], cur["margin"] = tot, cur["margin"] + margin
            else:
                hb = hist.get(sym)
                dv = trend_vol(hb.c, len(hb.c) - 1) if hb is not None and len(hb) > 40 else None
                stop_pct = max(0.05, min(0.15, 3 * dv)) if dv else TREND_EMERGENCY_STOP
                st["pos"][sym] = {"qty": q, "avg": fill, "margin": margin, "ts": now, "stop_pct": stop_pct}
            log(f"  {'KÖPT' if side == 'long' else 'BLANKAT'} {sym} för {money(margin)} USDT @ {fill:.6g}")

    def save():
        st["last_prices"] = dict(prices)
        with open(state_file + ".tmp", "w", encoding="utf-8") as f:
            json.dump(st, f)
        os.replace(state_file + ".tmp", state_file)

    def watch(end_ms):
        """Bevakar priserna varje sekund fram till end_ms."""
        polls, fails, last_eq, last_save, start = 0, 0, 0, time.time(), int(time.time() * 1000)
        log(f"Bevakar priserna varje sekund till {fmt_ts(end_ms)}")
        while int(time.time() * 1000) < end_ms:
            t1 = time.time()
            now = int(t1 * 1000)
            try:
                prices.update(fetch_all_prices())
                polls += 1
                st["watch"] = {"start": start, "polls": polls, "fails": fails, "last_poll": now}
            except Exception:
                fails += 1
            for sym, p in list(st["pos"].items()):
                cur = prices.get(sym)
                if cur is None:
                    continue
                r = (cur / p["avg"] - 1) * (1 if p["qty"] > 0 else -1)
                lim = p.get("stop_pct", TREND_EMERGENCY_STOP) * (0.5 if risk_off(st, now) else 1.0)
                # VINSTLÅS: har positionen gått bra flyttas stoppet upp och vinsten låses in
                p["peak"] = max(p.get("peak", 0.0), r)
                base = p.get("stop_pct", TREND_EMERGENCY_STOP)
                if p["peak"] >= base and r <= p["peak"] - 0.6 * base:
                    log(f"  VINSTLÅS: {sym} nådde {pct(p['peak'])}, föll tillbaka till {pct(r)} - säljer och tar hem vinsten")
                    trade_to(sym, 0.0, cur, now)
                    st.setdefault("blocked", {})[sym] = (now // 86400000 + 1) * 86400000 + 3600 * 1000
                    continue
                if p["qty"] < 0 and sym in st.get("social", {}).get("no_short", {}):
                    log(f"  SOCIAL VAKT: stänger blankningen i {sym} (Musk)")
                    trade_to(sym, 0.0, cur, now)
                    continue
                if r <= -lim:
                    log(f"  STOP-LOSS: {sym} har gått {pct(r)} emot oss - stänger direkt")
                    trade_to(sym, 0.0, cur, now)
                    st.setdefault("blocked", {})[sym] = (now // 86400000 + 1) * 86400000 + 3600 * 1000
            if now - st.get("news_ms", 0) >= NEWS_EVERY_MIN * 60 * 1000:
                try:
                    news_check(st, now)
                    st["news_ms"] = now
                except Exception:
                    pass
                for sym in list(st["pos"]):
                    if sym in st.get("blocked", {}) and sym in prices:
                        log(f"  Stänger {sym} p.g.a. nyhetsvakten")
                        trade_to(sym, 0.0, prices[sym], now)
            if now - last_eq >= 60000:
                st["equity"].append([now, round(equity(), 2)])
                last_eq = now
            if time.time() - last_save > 300:
                save()
                last_save = time.time()
            time.sleep(max(0.0, 1.0 - (time.time() - t1)))
        st["watch"] = {"start": start, "polls": polls, "fails": fails, "last_poll": st.get("watch", {}).get("last_poll", 0)}
        log(f"Bevakning klar: {polls} priskontroller, {fails} missade")
        save()
        render_trend_live(st, prices, equity(), path)

    errors = 0
    while True:
        t0 = time.time()
        now = int(t0 * 1000)
        try:
            for sym in SYMBOLS:
                try:
                    h = hist.get(sym)
                    if h is None or now >= h.t[-1] + 2 * BAR_MS:
                        hist[sym] = fetch_history(sym, 140)
                    k = fetch_klines(sym, 2)
                    if len(k):
                        prices[sym] = k.c[-1]
                        st["start_prices"].setdefault(sym, k.c[-1])
                except Exception as e:
                    log(f"  {sym}: kunde inte hämtas ({e})")
            if now - st.get("news_ms", 0) >= NEWS_EVERY_MIN * 60 * 1000:
                try:
                    n_h = news_check(st, now)
                    st["news_ms"] = now
                    if not st.get("news_logged"):
                        log(f"Nyhetsvakt igång: läste {n_h} rubriker")
                        st["news_logged"] = True
                except Exception as e:
                    log(f"  Nyhetsvakt: kunde inte läsa nyheter ({e})")
            for sym in list(st["pos"]):
                if sym in st.get("blocked", {}) and sym in prices:
                    log(f"  Stänger {sym} p.g.a. nyhetsvakten")
                    trade_to(sym, 0.0, prices[sym], now)
            data = {s: b for s, b in hist.items() if len(b) > 80}
            if REGIME_SYMBOL in data:
                last_day = data[REGIME_SYMBOL].t[-1]
                if st["last_day"] != last_day:
                    idx = {s: {t: i for i, t in enumerate(b.t)} for s, b in data.items()}
                    tgt = trend_targets(data, idx, last_day, st["mode"])
                    for sym in st.get("blocked", {}):
                        if sym in tgt:
                            tgt[sym] = 0.0
                    for sym in st.get("social", {}).get("no_short", {}):
                        if tgt.get(sym, 0) < 0:
                            tgt[sym] = 0.0
                    if risk_off(st, now):
                        log("  Social vakt aktiv -> halverar alla insatser idag")
                        tgt = {k: v * 0.5 for k, v in tgt.items()}
                    log(f"Nytt dygn ({fmt_ts(last_day + BAR_MS)[:10]}) - kollar trenderna och ombalanserar:")
                    for sym in sorted(set(tgt) | set(st["pos"])):
                        if sym in prices:
                            trade_to(sym, tgt.get(sym, 0.0), prices[sym], now)
                    st["last_day"] = last_day
                    st["targets"] = tgt
            st["last_prices"] = dict(prices)
            st["equity"].append([now, round(equity(), 2)])
            st["prices"] = dict(prices)
            if len(st["equity"]) > 6000:
                st["equity"] = st["equity"][:3000:2] + st["equity"][3000:]
            with open(state_file + ".tmp", "w", encoding="utf-8") as f:
                json.dump(st, f)
            os.replace(state_file + ".tmp", state_file)
            render_trend_live(st, prices, equity(), path)
            if once:
                if watch_minutes > 0:
                    watch(int(time.time() * 1000) + watch_minutes * 60 * 1000)
                write_summary_md(st, prices, equity(), mode)
                return
            if not opened:
                open_in_browser(path)
                opened = True
            errors = 0
        except KeyboardInterrupt:
            raise
        except Exception as e:
            errors += 1
            log(f"Problem ({e}) - försöker igen strax")
            time.sleep(min(300, 15 * errors))
        if once:
            return
        time.sleep(max(5, 60 - (time.time() - t0)))


def render_trend_live(st, prices, eq, path):
    tr = st["trades"]
    n = len(tr)
    wins = sum(1 for t in tr if t["pnl"] > 0)
    best = max(tr, key=lambda t: t["ret"]) if tr else None
    worst = min(tr, key=lambda t: t["ret"]) if tr else None
    sp = st["start_prices"]
    bh = [prices[s] / sp[s] - 1 for s in sp if s in prices]
    bh = sum(bh) / len(bh) if bh else 0
    peak, mdd = START_CAPITAL, 0
    for _, e in st["equity"]:
        peak = max(peak, e); mdd = max(mdd, (peak - e) / peak)

    def tt(t):
        return "-" if not t else f"<span class='{cls(t['ret'])}'>{pct(t['ret'])}</span> ({money(t['pnl'])})<br><small>{t['symbol']}</small>"
    cards = [("Kapital nu", f"{money(eq)} USDT"), ("Resultat", f"<span class='{cls(eq - START_CAPITAL)}'>{pct(eq / START_CAPITAL - 1)}</span>"),
             ("Köp &amp; håll samma tid", f"<span class='{cls(bh)}'>{pct(bh)}</span>"),
             ("Avslutade affärer", str(n)), ("Vinstandel", f"{wins / n * 100:.0f}%" if n else "-"),
             ("Snitt per affär", pct(sum(t['ret'] for t in tr) / n) if n else "-"),
             ("Bästa", tt(best)), ("Sämsta", tt(worst)), ("Största nedgång", f"<span class='neg'>{mdd * 100:.1f}%</span>"),
             ("Kontanter", f"{money(st['cash'])} USDT")]
    cards_html = "".join(f"<div class='card'><div class='lbl'>{a}</div><div class='val'>{b}</div></div>" for a, b in cards)
    prow = ""
    for s, p in st["pos"].items():
        cur = prices.get(s, p["avg"])
        r = (cur / p["avg"] - 1) * (1 if p["qty"] > 0 else -1)
        prow += (f"<tr><td>{s}</td><td>{side_badge('long' if p['qty'] > 0 else 'short')}</td><td>{money(p['margin'])}</td>"
                 f"<td>{p['avg']:.6g}</td><td>{cur:.6g}</td><td class='{cls(r)}'>{pct(r)}</td><td>{fmt_ts(p['ts'])}</td></tr>")
    prow = prow or "<tr><td colspan='7' class='muted'>Inga positioner - modellen ser ingen uppåttrend just nu och väntar</td></tr>"
    tgt = st.get("targets", {})
    trow = "".join(f"<tr><td>{s}</td><td class='{cls(w)}'>{w * 100:+.1f}%</td></tr>" for s, w in sorted(tgt.items(), key=lambda x: -x[1]))
    hrow = "".join(f"<tr><td>{fmt_ts(t['exit_ts'])}</td><td>{t['symbol']}</td><td>{side_badge(t['side'])}</td>"
                   f"<td class='{cls(t['ret'])}'>{pct(t['ret'])}</td><td class='{cls(t['pnl'])}'>{money(t['pnl'])}</td></tr>"
                   for t in reversed(tr[-50:])) or "<tr><td colspan='5' class='muted'>Inga avslutade affärer än</td></tr>"
    fng = st.get("fng")
    blk = st.get("blocked", {})
    news_html = (f"<p>Rädsla/girighet-index: <b>{fng[0]}</b> ({fng[1]})</p>" if fng else "<p class='muted'>Rädsla/girighet-index: inte hämtat än</p>")
    news_html += ("<p class='neg'>Spärrade mynt p.g.a. dåliga nyheter: " + ", ".join(f"{c} (till {fmt_ts(u)})" for c, u in blk.items()) + "</p>") if blk else "<p class='muted'>Inga mynt spärrade just nu.</p>"
    rowsn = ""
    for h in st.get("news", [])[:25]:
        c = "neg" if h["score"] < 0 else ("pos" if h["score"] > 0 else "")
        import html as _h
        rowsn += (f"<tr><td>{fmt_ts(h['ts'])}</td><td class='{c}'>{['mycket dålig', 'dålig', 'neutral', 'bra'][h['score'] + 2]}</td>"
                  f"<td>{', '.join(h['coins']) or '-'}</td><td><a style='color:#7cb7ff' href='{_h.escape(h['link'])}'>{_h.escape(h['title'])}</a></td></tr>")
    news_html += f"<table><tr><th>Tid</th><th>Bedömning</th><th>Mynt</th><th>Rubrik</th></tr>{rowsn or '<tr><td colspan=4 class=muted>Inga rubriker än</td></tr>'}</table>"
    html = f"""<!DOCTYPE html><html lang="sv"><head><meta charset="utf-8"><meta http-equiv="refresh" content="60"><title>Trendmodellen live</title>
<style>body{{background:#0f1115;color:#e6e6e6;font-family:Segoe UI,system-ui,sans-serif;padding:24px}}
h2{{font-size:17px;margin-top:26px}} .grid{{display:grid;grid-template-columns:repeat(auto-fill,minmax(180px,1fr));gap:12px}}
.card,.box{{background:#181b22;border:1px solid #262a33;border-radius:10px;padding:14px;overflow-x:auto}}
.lbl{{color:#999;font-size:12px;text-transform:uppercase}} .val{{font-size:19px;margin-top:6px}} small{{color:#999}}
table{{border-collapse:collapse;width:100%;font-size:13px}} td,th{{padding:7px;border-bottom:1px solid #262a33;text-align:left}} th{{color:#999}}
.pos{{color:#3fb68b}} .neg{{color:#e5534b}} .muted{{color:#888}} .badge{{font-size:11px;padding:2px 7px;border-radius:9px}}
.badge.long{{background:#173b2e;color:#5fd3a5}} .badge.short{{background:#40201f;color:#f08a84}}</style></head><body>
<h1>Trendmodellen ({'bara lång' if st.get('mode') == 'long' else 'lång + kort'}) - live papperstrading</h1>
<p class="muted">Igång sedan {fmt_ts(st['start_ms'])}. Ombalanserar en gång per dygn. Uppdateras varje minut. Inga riktiga pengar.</p>
<div class="grid">{cards_html}</div>
<h2>Kapital över tid</h2><div class="box">{equity_svg(st['equity'])}</div>
<h2>Positioner</h2><div class="box"><table><tr><th>Mynt</th><th>Sida</th><th>Insats</th><th>In</th><th>Nu</th><th>Resultat</th><th>Sedan</th></tr>{prow}</table></div>
<h2>Modellens målvikter (senaste dygnet)</h2><div class="box"><table><tr><th>Mynt</th><th>Andel av kapitalet</th></tr>{trow}</table></div>
<h2>Nyhetsvakten</h2><div class="box">{news_html}</div>
<h2>Avslutade affärer</h2><div class="box"><table><tr><th>Stängd</th><th>Mynt</th><th>Sida</th><th>Resultat</th><th>USDT</th></tr>{hrow}</table></div>
<p class="muted">Uppdaterad {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}</p></body></html>"""
    with open(path + ".tmp", "w", encoding="utf-8") as f:
        f.write(html)
    os.replace(path + ".tmp", path)



if __name__ == "__main__":
    args = sys.argv[1:]
    mode = args[0].lower() if args else "live"
    try:
        if mode == "backtest":
            tf = args[2] if len(args) > 2 else TIMEFRAME
            run_backtest(float(args[1]) if len(args) > 1 else None, tf=tf)
        elif mode == "trend":
            run_trend_backtest(float(args[1]) if len(args) > 1 else 5.5)
        elif mode == "senaste":
            run_trend_recent()
        elif mode == "senastedemo":
            run_trend_recent(fake=True)
        elif mode == "trendlive":
            run_trend_live(args[1] if len(args) > 1 else "long")
        elif mode == "kombination":
            run_ensemble_test(fake=len(args) > 1 and args[1] == "demo")
        elif mode == "forbattra":
            run_self_improve(fake=len(args) > 1 and args[1] == "demo")
        elif mode == "trendwatch":  # molnet: en körning + bevaka varje sekund i N minuter
            run_trend_live(args[1], once=True, watch_minutes=float(args[2]) if len(args) > 2 else 55)
        elif mode == "newswatch":
            run_news_watch(float(args[1]) if len(args) > 1 else 55)
        elif mode == "copywatch":
            run_copy_watch(float(args[1]) if len(args) > 1 else 55)
        elif mode == "gemwatch":
            run_gem_watch(float(args[1]) if len(args) > 1 else 55)
        elif mode == "fastwatch":
            run_fast_watch(float(args[1]) if len(args) > 1 else 55)
        elif mode == "morgon":
            write_morning_report()
        elif mode == "kvall":
            write_morning_report(evening=True)
        elif mode == "webbsida":
            write_dashboard()
        elif mode == "chartonce":
            run_chart_once()
        elif mode == "league":
            run_league()
        elif mode == "fundingonce":
            run_funding_once()
        elif mode == "mailrapport":
            write_mail_report()
        elif mode == "trendonce":   # en körning (för molnet / GitHub Actions)
            for m in (args[1:] or ["long", "longshort"]):
                run_trend_live(m, once=True)
            write_mail_report()
        elif mode == "trenddemo":
            run_trend_backtest(3, fake=True)
        elif mode in ("jamfor", "compare"):
            run_compare()
        elif mode == "demo":
            run_compare(fake=True)
        elif mode == "reset":
            for p in (STATE_FILE, REPORT_FILE, TRADES_CSV):
                if os.path.exists(p):
                    os.remove(p)
            log("Nollställd. Nästa start börjar om med nya låtsaspengar.")
        else:
            run_live()
    except KeyboardInterrupt:
        log("Boten stoppad. Allt är sparat.")
