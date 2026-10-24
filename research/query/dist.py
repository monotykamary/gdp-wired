"""The root queries' times, each side of a paired run (jobs.py --pair): `python3 research/query/dist.py <run dir>
[prefix]`. Per job group: queries, summed ms, the ms quantiles (p10, p50, p90, p99, max), CDCL nodes a second."""
import collections
import json
import pathlib
import sys

d = pathlib.Path(sys.argv[1]); prefix = sys.argv[2] if len(sys.argv) > 2 else ""
spec = {j["name"]: j for j in json.loads((d / "jobs.json").read_text())}
by = collections.defaultdict(lambda: {"here": [], "main": []})
for name, j in spec.items():
    if not name.startswith(prefix): continue
    f = d / name / "q.jsonl"
    if not f.exists(): continue
    rows = [json.loads(l) for l in f.read_text().splitlines() if l.startswith("{")]
    pids = list(dict.fromkeys(r["pid"] for r in rows))
    first = "main" if j["cmd"].startswith("echo =main") else "here"
    other = "main" if first == "here" else "here"
    # (each side's processes run one after the other: the first side's are the first half of the pids)
    half = max(1, len(pids) // 2)
    for r in rows: by[name.split("__")[0]][first if pids.index(r["pid"]) < half else other].append(r)
q = lambda xs, p: sorted(xs)[min(len(xs) - 1, int(p * len(xs)))] if xs else 0
for g, sides in sorted(by.items()):
    for s in ("here", "main"):
        xs = [r["ms"] for r in sides[s]]; nodes = sum(r.get("nodes", 0) for r in sides[s])
        if not xs: continue
        print(f"{g:6} {s}: {len(xs)} queries, {sum(xs):.0f} ms; ms p10 {q(xs, .1):.1f} p50 {q(xs, .5):.1f} p90 {q(xs, .9):.1f} p99 {q(xs, .99):.1f} max {max(xs):.1f}; {1000 * nodes / max(1, sum(xs)):.0f} CDCL nodes a second")
