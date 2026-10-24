"""Two runs of a compare/ runner (results.jsonl), task by task: `python3 research/query/diff.py <here dir> <main dir>
[--tool gdp]`. Each side's answers by kind, the tasks answered by one side only (gained and lost, with both sides'
answers and seconds), and every task whose answers contradict."""
import collections
import json
import pathlib
import sys

arg = lambda k, d: sys.argv[sys.argv.index(k) + 1] if k in sys.argv else d
tool = arg("--tool", "gdp")
NO = {"unknown", "timeout", "error", "unsupported", "not proven", None}


def load(d):
    out = {}
    for l in (pathlib.Path(d) / "results.jsonl").read_text().splitlines():
        r = json.loads(l)
        if r.get("tool") == tool: out[r["task"]] = r
    return out


a, b = load(sys.argv[1]), load(sys.argv[2])
for name, x in (("here", a), ("main", b)): print(name, len(x), dict(collections.Counter(r["answer"] for r in x.values())))
ans = lambda r: None if r is None or r["answer"] in NO else r["answer"]
gained = sorted(t for t in a if ans(a[t]) and not ans(b.get(t)))
lost = sorted(t for t in b if ans(b[t]) and not ans(a.get(t)))
clash = sorted(t for t in a if ans(a[t]) and ans(b.get(t)) and ans(a[t]) != ans(b[t]))
for label, ts in (("gained", gained), ("lost", lost), ("contradicting", clash)):
    print(f"{label} {len(ts)}")
    for t in ts: print(f"   {t}: here {a.get(t, {}).get('answer')} {a.get(t, {}).get('seconds')} s, main {b.get(t, {}).get('answer')} {b.get(t, {}).get('seconds')} s")
