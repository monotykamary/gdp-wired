"""Summaries of a research/query run: `python3 research/query/agg.py <run dir> [--prefix p] [--top 40] [--queries]`.

  profiles: self ms by file and by function, summed over the jobs (named prefix*), with each one's share
  --queries: each root query's wall ms and counted work (q.jsonl): the distribution of ms, and of work per ms by kind
"""
import collections
import json
import pathlib
import sys

d = pathlib.Path(sys.argv[1])
arg = lambda k, dflt: sys.argv[sys.argv.index(k) + 1] if k in sys.argv else dflt
prefix, top = arg("--prefix", ""), int(arg("--top", "40"))
jobs = [p for p in sorted(d.iterdir()) if p.is_dir() and p.name.startswith(prefix)]


def pct(xs, q):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(q * len(xs)))] if xs else 0


if "--queries" not in sys.argv:
    selfs, files, totals, lines = collections.Counter(), collections.Counter(), collections.Counter(), collections.Counter()
    ms = 0.0
    for j in jobs:
        for f in j.glob("prof-*.json"):
            try:
                p = json.loads(f.read_text())
            except json.JSONDecodeError:
                continue
            ms += p["ms"]
            selfs.update(p["self"]); files.update(p["files"]); totals.update(p["total"]); lines.update(p.get("lines", {}))
    print(f"{len(jobs)} jobs, {ms:.0f} ms profiled")
    print("by file (self):")
    for k, v in files.most_common(25):
        print(f"  {v:10.0f} ms {100 * v / ms:5.1f}%  {k}")
    print("by function (self):")
    for k, v in selfs.most_common(top):
        print(f"  {v:10.0f} ms {100 * v / ms:5.1f}%  {k}")
    print("by line (self):")
    for k, v in lines.most_common(top):
        print(f"  {v:10.0f} ms {100 * v / ms:5.1f}%  {k}")
    print("by function (total):")
    for k, v in totals.most_common(top):
        print(f"  {v:10.0f} ms {100 * v / ms:5.1f}%  {k}")
else:
    qs = []
    for j in jobs:
        f = j / "q.jsonl"
        if f.exists():
            for l in f.read_text().splitlines():
                try:
                    q = json.loads(l); q["job"] = j.name; qs.append(q)
                except json.JSONDecodeError:
                    pass
    print(f"{len(qs)} queries over {len(jobs)} jobs")
    by = collections.defaultdict(list)
    for q in qs:
        by[q["kind"]].append(q)
    for k, xs in sorted(by.items()):
        ms = [q["ms"] for q in xs]
        rate = [q["work"] / q["ms"] for q in xs if q["ms"] >= 20]
        print(f"{k}: {len(xs)} queries, {sum(ms):.0f} ms; ms p50 {pct(ms, .5):.1f} p90 {pct(ms, .9):.1f} p99 {pct(ms, .99):.1f} max {max(ms):.1f}; "
              f"work/ms (queries of 20 ms or more, {len(rate)}) p10 {pct(rate, .1):.0f} p50 {pct(rate, .5):.0f} p90 {pct(rate, .9):.0f} min {min(rate, default=0):.0f} max {max(rate, default=0):.0f}")
