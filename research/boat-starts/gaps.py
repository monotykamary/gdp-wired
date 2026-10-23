"""Today's gaps between batches, from the mix (each run's start and its measured wall): for each batch's end, the time
until the next batch started (any track), and until its own track's next batch (a track: the runs dir, runs/<track>/).
A VM released at a batch's end is reused without a start by the next batch only if it is still up then, so these
gaps are what an idle window has to cover.

    python3 research/boat-starts/gaps.py research/boat-starts/mix.json > research/boat-starts/gaps.txt
"""
import json
import sys

sys.path.insert(0, __import__("os").path.dirname(__file__))
import sim

mix = sim.load(sys.argv[1])
ev = sorted((b["start"], b["start"] + float(b["wall_s"] or 0), b["run"].split("/")[1], b["run"]) for b in mix)


def q(xs, p):
    xs = sorted(xs)
    return round(xs[min(len(xs) - 1, int(p * len(xs)))]) if xs else None


anyg, own, busy_any = [], [], 0
for s, e, track, run in ev:
    nxt = [s2 for s2, _, _, _ in ev if s2 >= e]
    if any(s2 < e < e2 for s2, e2, _, r2 in ev if r2 != run):
        busy_any += 1  # another batch was running when this one ended: its VMs could go straight to it
    if nxt:
        anyg.append(min(nxt) - e)
    mine = [s2 for s2, _, t2, _ in ev if t2 == track and s2 >= e]
    if mine:
        own.append(min(mine) - e)
print(f"{len(ev)} batches; at {busy_any} of their ends another batch was running")
for name, g in (("to the next batch of any track", anyg), ("to the same track's next batch", own)):
    print(f"{name}: {len(g)} gaps, median {q(g, 0.5)} s, p75 {q(g, 0.75)} s, p90 {q(g, 0.9)} s, max {q(g, 1.0)} s")
    for w in (60, 120, 300, 600, 900, 1800):
        print(f"  covered by an idle window of {w:5} s: {sum(1 for x in g if x <= w)} of {len(g)}")
