"""The 332 step goals beside main in one run (jobs.py g332 --base): `python3 research/query/g332.py <run dir>`. Per goal
the outcome, the tree's leaves and splits, CDCL's decisions, conflicts and nodes on both sides (the same search when all
match), and the search's ms; the sums, the ratio's quantiles, and every goal whose search or outcome differs."""
import json
import pathlib
import statistics
import sys

d = pathlib.Path(sys.argv[1])


def row(f, side=None):
    try:
        lines, at = f.read_text().splitlines(), None
        for l in lines:
            if l in ("=here", "=main"): at = l[1:]
            elif l.startswith('{"goal"') and (side is None or at == side): return json.loads(l)
    except (FileNotFoundError, json.JSONDecodeError):
        pass
    return None


same = differ = 0
mine_ms = base_ms = 0
ratios, diffs = [], []
proven = {"mine": 0, "base": 0}
for f in sorted(d.glob("g332__*.log")):
    paired = (d / f"base-{f.name}").exists() is False
    a, b = (row(f, "here"), row(f, "main")) if paired else (row(f), row(d / f"base-{f.name}"))
    if not a or not b:
        diffs.append((f.name, "missing", a and a.get("outcome"), b and b.get("outcome")))
        continue
    key = lambda r: (r["outcome"], r.get("leaves"), r.get("splits"), *(r.get("cdcl", {}).get(k) for k in ("decisions", "conflicts", "nodes")))
    proven["mine"] += a["outcome"] == "proven"; proven["base"] += b["outcome"] == "proven"
    if key(a) == key(b): same += 1
    else: differ += 1; diffs.append((f.name, key(a), key(b)))
    mine_ms += a["searchMs"]; base_ms += b["searchMs"]
    ratios.append(a["searchMs"] / max(1, b["searchMs"]))
ratios.sort()
q = lambda p: ratios[min(len(ratios) - 1, int(p * len(ratios)))]
print(f"goals {same + differ}: same search {same}, differ {differ}; proven here {proven['mine']}, main {proven['base']}")
print(f"search ms summed: here {mine_ms}, main {base_ms} ({mine_ms / max(1, base_ms):.3f}); per goal here/main p10 {q(.1):.3f} p50 {q(.5):.3f} p90 {q(.9):.3f}")
for x in diffs[:40]: print("  ", *x)
