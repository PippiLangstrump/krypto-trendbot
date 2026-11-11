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
           "PEPEUSDT", "WIFUSDT", "BONKUSDT"]   # sista tre = memecoins (mycket mer svängiga)
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
              "PEPEUSDT": ["pepe"], "WIFUSDT": ["dogwifhat", " wif "], "BONKUSDT": ["bonk"]}
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
                return v, True
        except Exception:
            continue
    return 10.5, False


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
    lines = [f"**Läget kl {datetime.utcnow().strftime('%H:%M')} UTC** (låtsaspengar, varje bot startade med {kr(START_CAPITAL * rate)})", ""]
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
        hour_tr = [t for t in tr if t["exit_ts"] >= now_ms - 3600 * 1000]
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
            return f"{t['symbol'].replace('USDT', '')} ({what}) {pct_sv(t['ret'])} = {kr(t['pnl'] * rate, sign=True)}"
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
                  f"Senaste dygnet: {kr((eq - day_ago) * rate, sign=True)} · Affärer senaste timmen: {len(hour_tr)}  ",
                  f"Bästa just nu: {t_txt(best)}  ",
                  f"Sämsta just nu: {t_txt(worst)}  ",
                  f"Äger/blankar: {coins or 'inget – väntar på bättre läge'}", ""]
    if st.get("note"):
        lines.append(st["note"])
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
            better_everywhere = all(r[k]["sharpe"] > cur_r[k]["sharpe"] + 0.1 for k in starts)
            not_riskier = r["hela"]["mdd"] <= cur_r["hela"]["mdd"] + 0.05
            if better_everywhere and not_riskier and r["hela"]["sharpe"] > best_r["hela"]["sharpe"]:
                best, best_r = c, r
        if best is not cur:
            conf[mode] = best
            msg = (f"{name} har förbättrats: nya regler ({describe_cfg(best)}). Sharpe hela perioden "
                   f"{cur_r['hela']['sharpe']:.2f} → {best_r['hela']['sharpe']:.2f}, senaste året "
                   f"{cur_r['365']['sharpe']:.2f} → {best_r['365']['sharpe']:.2f}.")
        else:
            conf[mode] = cur
            msg = (f"{name}: testade {len(cands)} varianter - ingen var tydligt bättre överallt, behåller nuvarande regler "
                   f"(senaste året {pct(cur_r['365']['ret'])}, hela perioden {pct(cur_r['hela']['ret'])}).")
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
                if r <= -p.get("stop_pct", TREND_EMERGENCY_STOP):
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
