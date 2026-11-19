"""Testvecka 1 -> 2: köp & håll under testveckan + ärligt test av en uppgradering av Bot 2.

Uppgradering som testas ("snabb vändning"): Bot 2 bestämmer trenden en gång per dygn som nu,
men kollar varje timme om ett mynts trend har vänt (samma 7/14/28/56-dagarsregel, där dagens
pris = senaste timpriset). Har trenden vänt mot positionen stängs den direkt i stället för att
vänta till nästa dygn. Nya positioner tas fortfarande bara vid den dagliga ombalanseringen.
Båda versionerna simuleras på exakt samma timdata, avgifter och finansieringskostnad.
"""
import os, sys, json, math, time
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import bot

H = 3600000
DAYS = int(os.environ.get("DAYS", "730"))


def fetch_hourly(sym, days):
    bot.set_timeframe("1h")
    end = int(time.time() * 1000)
    start = end - days * 86400000
    out = bot.Bars()
    t = start
    while t < end:
        try:
            b = bot.fetch_klines(sym, 1000, t)
        except Exception as e:
            print("  fel", sym, e)
            break
        if not len(b):
            break
        for i in range(len(b)):
            if not out.t or b.t[i] > out.t[-1]:
                out.append(b.t[i], b.o[i], b.h[i], b.l[i], b.c[i], b.v[i])
        t = b.t[-1] + H
        if len(b) < 1000:
            break
    return out


def daily_from_hourly(hb):
    """Dagsstängning = sista timljusets stängning före 00:00 UTC."""
    d = bot.Bars()
    for i in range(len(hb)):
        t = hb.t[i]
        if (t + H) % 86400000 == 0:                      # timljuset 23:00-24:00
            d.append(t + H - 86400000, 0, 0, 0, hb.c[i], 0)   # dagens öppningstid
    return d


def simulate(hdata, ddata, mode="longshort", flip=None, start_t=None, lookbacks=None):
    if lookbacks:
        old = bot.TREND_LOOKBACKS
        bot.TREND_LOOKBACKS = list(lookbacks)
    master = max(hdata.values(), key=len)
    hidx = {s: {t: i for i, t in enumerate(b.t)} for s, b in hdata.items()}
    didx = {s: {t: i for i, t in enumerate(b.t)} for s, b in ddata.items()}
    cost_rate = bot.FEE + bot.SLIPPAGE
    fund_h = bot.SHORT_FUNDING_8H / 8
    eq, w, curve, trades = bot.START_CAPITAL, {}, [], 0
    for j in range(1, len(master)):
        t = master.t[j]
        if start_t and t < start_t:
            continue
        pnl = 0.0
        for sym, wt in w.items():
            b = hdata[sym]; i = hidx[sym].get(t)
            if i is None or i == 0:
                continue
            pnl += wt * (b.c[i] / b.c[i - 1] - 1)
            if wt < 0:
                pnl -= abs(wt) * fund_h
        eq *= (1 + pnl)
        close_t = t + H                                    # timljuset stänger här
        if close_t % 86400000 == 0:                        # dygnsskifte: vanlig ombalansering
            day_t = close_t - 86400000
            tgt = bot.trend_targets(ddata, didx, day_t, mode)
            for sym in set(w) | set(tgt):
                new, old_w = tgt.get(sym, 0.0), w.get(sym, 0.0)
                if abs(new - old_w) > bot.TREND_MIN_TRADE or (new == 0 and old_w != 0):
                    eq -= abs(new - old_w) * cost_rate * eq
                    trades += 1
                    w[sym] = new
            w = {k: v for k, v in w.items() if v != 0}
        elif flip:                                         # uppgraderingen: kolla vändning varje timme
            day_t = close_t - (close_t % 86400000)
            for sym, wt in list(w.items()):
                d = ddata[sym]; i = didx[sym].get(day_t - 86400000)   # gårdagens dagsljus
                hi = hidx[sym].get(t)
                if i is None or hi is None:
                    continue
                c = d.c[:i + 1] + [hdata[sym].c[hi]]
                s = bot.trend_signal(c, len(c) - 1)
                if s is None:
                    continue
                against = (s < 0 if wt > 0 else s > 0) if flip == "motsatt" else (s <= 0 if wt > 0 else s >= 0)
                if against:
                    eq -= abs(wt) * cost_rate * eq
                    trades += 1
                    del w[sym]
        curve.append([t, eq])
    if lookbacks:
        bot.TREND_LOOKBACKS = old
    return curve, trades


def stats(curve, since=None):
    pts = [(t, e) for t, e in curve if since is None or t >= since]
    if len(pts) < 48:
        return None
    # dagliga avkastningar för Sharpe
    daily = [pts[0]]
    for t, e in pts:
        if t - daily[-1][0] >= 86400000:
            daily.append((t, e))
    rets = [daily[i][1] / daily[i - 1][1] - 1 for i in range(1, len(daily))]
    m = sum(rets) / len(rets); sd = math.sqrt(sum((r - m) ** 2 for r in rets) / len(rets)) or 1e-9
    peak, mdd = pts[0][1], 0.0
    for _, e in pts:
        peak = max(peak, e); mdd = max(mdd, (peak - e) / peak)
    return {"ret": pts[-1][1] / pts[0][1] - 1, "sharpe": m / sd * math.sqrt(365), "mdd": mdd}


def main():
    cfg = bot.load_trend_config("longshort")
    bot.apply_trend_config(cfg)
    print("Bot 2 regler:", cfg)
    hdata = {}
    for s in bot.SYMBOLS:
        hb = fetch_hourly(s, DAYS)
        if len(hb) > 24 * 70:
            hdata[s] = hb
        print("hämtat", s, len(hb))
    ddata = {s: daily_from_hourly(b) for s, b in hdata.items()}
    now = int(time.time() * 1000)
    # köp & håll under testveckan (lika mycket i alla 15 mynt) + BTC
    ws = int(os.environ["WEEK_START"])     # när botarna startade (11/11 kl 23:05)
    bh = []
    for s, b in hdata.items():
        i0 = next((i for i, t in enumerate(b.t) if t >= ws), None)
        if i0 is not None:
            bh.append((s, b.c[-1] / b.c[i0] - 1))
    res = {"buyhold_week": sum(r for _, r in bh) / len(bh), "btc_week": dict(bh).get("BTCUSDT"),
           "per_coin_week": {s: round(r, 4) for s, r in bh}}
    variants = {
        "nuvarande": dict(),
        "snabb vändning (motsatt)": dict(flip="motsatt"),
        "snabb vändning (neutral)": dict(flip="neutral"),
        "plus 3-dagarsperiod": dict(lookbacks=[3] + list(cfg["lookbacks"])),
    }
    start_t = min(b.t[0] for b in hdata.values()) + 60 * 86400000   # signalen behöver 56 dagar
    out = {}
    for name, kw in variants.items():
        curve, tr = simulate(hdata, ddata, start_t=start_t, **kw)
        out[name] = {"trades": tr}
        for lab, since in (("hela", None), ("365d", now - 365 * 86400000), ("180d", now - 180 * 86400000),
                           ("90d", now - 90 * 86400000), ("30d", now - 30 * 86400000)):
            st = stats(curve, since)
            out[name][lab] = st and {k: round(v, 4) for k, v in st.items()}
        print(name, json.dumps(out[name]))
    res["variants"] = out
    res["days"] = DAYS
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "vecka2.json"), "w") as f:
        json.dump(res, f, indent=1)
    print("RESULTAT", json.dumps(res))


if __name__ == "__main__":
    main()
