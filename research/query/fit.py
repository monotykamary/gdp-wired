"""The cost model's weights: `python3 research/query/fit.py <run dir> [<run dir> ...] [--min-ms 20] [--features a,b,...]`.

Each root query a run logged (q.jsonl: its wall ms, its counted work and its costs by kind) is a row; the weights w
(non-negative, work.n's own weight 1) are those that make the model's units, work + Σ w·cost, a constant multiple of
the wall ms as nearly as can be (least squares on the ratio's logarithm, by iterated reweighting of the relative
error). Prints the weights, the units a ms (the rate) and their spread across queries and by kind and job group,
beside work.n's alone."""
import collections
import json
import math
import pathlib
import sys

import numpy as np
from scipy.optimize import nnls

arg = lambda k, d: sys.argv[sys.argv.index(k) + 1] if k in sys.argv else d
dirs = [a for a in sys.argv[1:] if not a.startswith("--") and pathlib.Path(a).is_dir()]
min_ms = float(arg("--min-ms", "20"))
feats = arg("--features", "fm,fcells,plainRows,values,copies,edges,scan,pivotRows,unitRows,unfoldRows,goalNodes").split(",")
free = "--free" in sys.argv  # no work.n in the model: every term weighed (work.n's own parts among the features)
rows = []
for d in dirs:
    for f in pathlib.Path(d).glob("*/q.jsonl"):
        group = f.parent.name.split("__")[0]
        for l in f.read_text().splitlines():
            try: q = json.loads(l)
            except json.JSONDecodeError: continue
            if q["ms"] < min_ms: continue
            c = dict(q.get("c", {}))
            # (the float simplex's cells, where a run logged none: from work.n, what it counts beyond the solver's rows, the pairs, each pivot and each node's rows)
            if "fcells" not in c: c["fcells"] = max(0, q["work"] - sum(c.get(k, 0) for k in ("solveRows", "fm", "fpivots", "cdclNodes", "cdclRows", "plainNodes", "plainRows")))
            rows.append((group, q["kind"], q["ms"], q["work"], [c.get(k, 0) for k in feats], f.parent.name))
print(f"{len(rows)} queries of {min_ms} ms or more, from {len(dirs)} runs")
ms = np.array([r[2] for r in rows]); work = np.array([r[3] for r in rows], float); X = np.array([r[4] for r in rows], float)
work0 = work.copy()
if free: work = np.zeros(len(rows))


def spread(units, label):
    rate = units / ms
    q = lambda p: float(np.quantile(rate, p))
    lr = np.log(np.maximum(rate, 1e-3))
    print(f"{label}: units a ms p10 {q(.1):.0f} p50 {q(.5):.0f} p90 {q(.9):.0f} (p90/p10 {q(.9) / max(1e-9, q(.1)):.2f}), min {rate.min():.0f} max {rate.max():.0f}, sd of log {lr.std():.3f}")
    by = collections.defaultdict(list)
    for r, x in zip(rows, rate): by[(r[0], r[1])].append(x)
    for k in sorted(by): xs = np.array(by[k]); print(f"   {k[0]:>8} {k[1]:>6} {len(xs):6d} queries: p10 {np.quantile(xs, .1):7.0f} p50 {np.median(xs):7.0f} p90 {np.quantile(xs, .9):7.0f}")
    return rate


spread(work0, "work.n alone")
# Fit: Σ w·cost ≈ ms, every query's relative error weighed alike (w ≥ 0); then scaled so the median query does
# `--scale` units a ms (250, bmc.ts's rate for work.n's). Without --free, work.n is a term of its own, weighed too.
if not free: X = np.concatenate([work0[:, None], X], axis=1); feats = ["work"] + feats
A = X / ms[:, None]; b = np.ones(len(ms))
# (--balance: each job group (g332, sat, unsat, its, pairs, rw), kind and size (under 100 ms, under a second, longer)
# weighs alike, however many queries it has)
if "--balance" in sys.argv:
    size = lambda r: 0 if r[2] < 100 else 1 if r[2] < 1000 else 2
    cnt = collections.Counter((r[0], r[1], size(r)) for r in rows)
    sw = np.sqrt(np.array([1 / cnt[(r[0], r[1], size(r))] for r in rows]))
    A = A * sw[:, None]; b = b * sw
weights, _ = nnls(A, b)
scale = float(arg("--scale", "250"))
k = scale / float(np.median((X @ weights) / ms))
weights = weights * k
work = np.zeros(len(rows))
print("weights (units of work.n per unit of each cost):")
for k, w in zip(feats, weights): print(f"   {k:>12} {w:10.4f}")
spread(work + X @ weights, "the model")
json.dump({"features": feats, "weights": [float(x) for x in weights], "rate": scale}, open("/dev/stdout", "w"))
print()
