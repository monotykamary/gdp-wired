"""The VM-paired side by side read: `python3 compare/chc/paired.py <run dir>... [--us gdp]` (runs of modal_chc.py
--paired 1, each tool on a task on the same VM in turn). Per run: each tool's solved and wrong. Then per task, summed
over the runs, each rival against us: the tasks we solve more often (wins) and those it does (losses), with the sign
test's two-sided p (ties dropped), and the noise rule: our lowest run against the leader's highest. Solved: the
expected verdict (the 2 disputed labels count as wrong, as everywhere)."""
import json, math, pathlib, sys, collections

args = [a for a in sys.argv[1:] if not a.startswith("--")]
us = sys.argv[sys.argv.index("--us") + 1] if "--us" in sys.argv else "gdp"
args = [a for a in args if a != us]
runs = []
for d in args:
    rows = [json.loads(l) for l in open(pathlib.Path(d) / "results.jsonl")]
    by = collections.defaultdict(dict)
    for r in rows:
        if r.get("tool") not in (None, "?"):
            by[r["tool"]][r["task"]] = r
    runs.append((d, by))
tools = sorted({t for _, by in runs for t in by}, key=lambda t: (t != us, t))
ok = lambda r: bool(r) and r.get("answer") in ("sat", "unsat") and r["answer"] == r.get("expected")
bad = lambda r: bool(r) and r.get("answer") in ("sat", "unsat") and r["answer"] != r.get("expected")
print("| run | " + " | ".join(tools) + " | rows paired on one VM |")
print("|" + " --- |" * (len(tools) + 2))
solved = collections.defaultdict(list)
for d, by in runs:
    cells = []
    for t in tools:
        n, w = sum(ok(r) for r in by[t].values()), sum(bad(r) for r in by[t].values())
        solved[t].append(n)
        cells.append(f"{n:,} ({w} wrong)")
    same = sum(1 for task in by[us] if len(hs := {by[t].get(task, {}).get("host") for t in tools}) == 1 and None not in hs)
    print(f"| {d} | " + " | ".join(cells) + f" | {same} of {len(by[us])} |")
def sign_p(w: int, l: int) -> float:
    n, k = w + l, min(w, l)
    return 1.0 if n == 0 else min(1.0, 2 * sum(math.comb(n, i) for i in range(k + 1)) / 2 ** n)
print()
print(f"| {us} against | tasks we solve more often | tasks it solves more often | sign test p | our lowest run | its highest run | noise rule |")
print("| --- | --- | --- | --- | --- | --- | --- |")
tasks = set().union(*(by[us].keys() for _, by in runs))
for t in tools[1:]:
    w = l = 0
    for task in tasks:
        a = sum(ok(by[us].get(task)) for _, by in runs); b = sum(ok(by[t].get(task)) for _, by in runs)
        w += a > b; l += b > a
    lo, hi = min(solved[us]), max(solved[t])
    print(f"| {t} | {w} | {l} | {sign_p(w, l):.3g} | {lo:,} | {hi:,} | {'lead' if lo > hi else 'level' if lo >= min(solved[t]) else 'behind'} |")
