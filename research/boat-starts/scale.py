"""Does a plan's day of starts carry more of today's work? Today's mix replayed `v` times a day (each replay `24/v`
hours after the one before, so replays overlap once v > 24 / the mix's span), over three days; the figures are the
third day's (the rolling day's starts then come from replays only): its starts, its batches that fell back to Modal
and Modal's dollars for them, boat's dollars for the day's VM-seconds (idle ones apart: held by a batch but not running
a job, or up after a release), and its batches' walls over the same batch's wall with unlimited starts.

    python3 research/boat-starts/scale.py research/boat-starts/mix.json [policy ...] > research/boat-starts/scale.txt
"""
import math
import sys

sys.path.insert(0, __import__("os").path.dirname(__file__))
import sim

mix = sim.load(sys.argv[1])
t0 = min(b["start"] for b in mix)
span = max(b["start"] for b in mix) - t0
print(f"today's mix: {len(mix)} batches over {round(span / 3600, 2)} h (first to last start), {round(sum(j[0] * j[1] for b in mix for j in b['jobs']) / 3600, 1)} slot-hours")
DAY = 86400.0


def replay(v):
    out = []
    k = 0
    while k * DAY / v < 3 * DAY:
        for b in mix:
            out.append(dict(b, start=b["start"] - t0 + k * DAY / v, run=f"{b['run']}#{k}"))
        k += 1
    return out


def third_day(r, ref):
    rows = [x for x in r["rows"] if 2 * DAY <= x["t0"] < 3 * DAY]
    by = {x["run"]: x for x in ref["rows"]}
    sd = sorted(x["wall"] / by[x["run"]]["wall"] for x in rows if not x["modal"] and by[x["run"]]["wall"] > 0 and x["slot_s"] >= 60)
    q = lambda p: round(sd[min(len(sd) - 1, int(p * len(sd)))], 2) if sd else None
    return {"batches": len(rows), "starts": sum(x["starts"] for x in rows), "modal": sum(x["modal"] for x in rows), "modal_jobs": sum(x["jobs"] for x in rows if x["modal"]),
            "modal_dollars": round(sum(x["modal_dollars"] for x in rows), 2), "p50": q(0.5), "p90": q(0.9), "max": sd[-1] if sd else None}


POLS = sys.argv[2:] or ["old", "new"]
print("v/day  plan  policy                            starts  batches  to Modal: batches (jobs)   Modal $  boat $ (idle $)  boat+Modal $   wall/unlimited: median p90 max   (all day 3's)")
VS = [float(x) for x in __import__("os").environ.get("SCALE_V", "1,2,2.5,3,4,5,6").split(",")]
for v in VS:
    m = replay(v)
    ref = sim.Sim(m, sim.POLICIES["old"], "inf").run().report()
    for plan in ("100", "500"):
        for pol in POLS:
            S = sim.Sim(m, sim.POLICIES[pol], plan).run()
            r = S.report()
            d = third_day(r, ref)
            boat_d, idle_d = S.day_dollars(2)
            print(f"{v:5}  ${plan:4} {pol:32}  {d['starts']:6}  {d['batches']:6}  {d['modal']:4} ({d['modal_jobs']:6})  {d['modal_dollars']:8.2f}  {boat_d:6.2f} ({idle_d:5.2f})  {boat_d + d['modal_dollars']:8.2f}"
                  f"   {d['p50']} {d['p90']} {round(d['max'], 2) if d['max'] else None}")
