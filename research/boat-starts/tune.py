"""Defaults for a plan, wall time first: today's mix replayed v times a day (as scale.py), each policy's third day:
the benchmark runs' walls (the compare runners with 500 calls or more: CHC, TIP, termination), median and slowest,
the suites' slowest, what fell back to Modal, the starts and boat's dollars.

    python3 research/boat-starts/tune.py research/boat-starts/mix.json --plan 500 > research/boat-starts/tune-500.txt
"""
import argparse
import itertools
import sys

sys.path.insert(0, __import__("os").path.dirname(__file__))
import sim
from scale import replay, DAY

ap = argparse.ArgumentParser()
ap.add_argument("mix")
ap.add_argument("--plan", default="500")
ap.add_argument("--v", default="1,2,3")
a = ap.parse_args()

grid = []
for share, cap, idle in itertools.product([1 / 4, 1 / 3, 1 / 2, 1.0], [30, 50, 80, 120, None], ["60", "adaptive900", "300"]):
    p = dict(sim.BASE, share=share, cap=cap, reserve=(60, 15))
    if idle == "adaptive900":
        p["adaptive"] = {"exhaust": True, "long": 900}
    else:
        p["idle"] = int(idle)
    grid.append((f"share {share:.2f} cap {cap} idle {idle}", p))
grid.append(("old", sim.POLICIES["old"]))

print(f"plan ${a.plan} {sim.PLANS[a.plan][:3]}; benchmark runs: compare runners with >= 500 calls; walls in s (day 3)")
print("v    policy                                  bench median  bench max  suite max  to Modal (batches, $)  starts  boat $ (idle $)")
for v in [float(x) for x in a.v.split(",")]:
    m = replay(v)
    for name, p in grid:
        S = sim.Sim(m, p, a.plan).run()
        r = S.report()
        rows = [x for x in r["rows"] if 2 * DAY <= x["t0"] < 3 * DAY]
        bench = sorted(x["wall"] for x in rows if x["jobs"] >= 500 and not x["modal"])
        suites = [x["wall"] for x in rows if 168 <= x["jobs"] <= 204 and not x["modal"]]
        b, i = S.day_dollars(2)
        print(f"{v:<4} {name:40} {bench[len(bench) // 2] if bench else '-':>10} {bench[-1] if bench else '-':>10} {max(suites) if suites else '-':>10}"
              f"   {sum(x['modal'] for x in rows):3} (${round(sum(x['modal_dollars'] for x in rows), 2):6})  {sum(x['starts'] for x in rows):6}  {b:6} ({i})")

print()
print("the defaults (sim.NEW: 60 s idle, cap 50, waits within --max-wait), c985479's (sim.NEW300) and the $100 plan's (sim.NEW100); the old policy for reference")
print("v    plan  policy                                  bench median  bench max  suite max  to Modal (batches, $)  starts  boat $ (idle $)")
for v in [float(x) for x in a.v.split(",")]:
    m = replay(v)
    for plan in ("100", "500"):
        for name in ("new", "new with cap 30", "c985479 ($500: 300 s idle, cap 50)", "new for $100 (cap 30, 60 s idle, 900 s when short)", "old"):
            S = sim.Sim(m, sim.POLICIES[name], plan).run()
            rows = [x for x in S.report()["rows"] if 2 * DAY <= x["t0"] < 3 * DAY]
            bench = sorted(x["wall"] for x in rows if x["jobs"] >= 500 and not x["modal"])
            suites = [x["wall"] for x in rows if 168 <= x["jobs"] <= 204 and not x["modal"]]
            b, i = S.day_dollars(2)
            print(f"{v:<4} ${plan:4} {name[:38]:38} {bench[len(bench) // 2] if bench else '-':>10} {bench[-1] if bench else '-':>10} {max(suites) if suites else '-':>10}"
                  f"   {sum(x['modal'] for x in rows):3} (${round(sum(x['modal_dollars'] for x in rows), 2):6})  {sum(x['starts'] for x in rows):6}  {b:6} ({i})")
