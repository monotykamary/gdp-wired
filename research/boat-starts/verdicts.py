"""Two runs of the same code, verdict by verdict: a compare runner's results.jsonl (each (tool, task)'s answer) or
modal/run.py's summary.tsv (each job's exit code). A difference between a definite answer and a time limit (timeout,
unknown) is the time limit's (a job that ends near it may end either side); between two definite answers it would be
a contradiction.

    python3 research/boat-starts/verdicts.py <run A> <run B>
"""
import json
import pathlib
import sys

DEFINITE_NOT = {"timeout", "unknown", "error", "?", None, ""}


def load(d):
    d = pathlib.Path(d)
    if (d / "results.jsonl").exists():
        out = {}
        for l in (d / "results.jsonl").read_text().splitlines():
            r = json.loads(l)
            out[(r.get("tool"), r.get("task"))] = r.get("answer")
        return "results.jsonl", out
    rows = [l.split("\t") for l in (d / "summary.tsv").read_text().splitlines() if l.strip()]
    return "summary.tsv", {r[0]: r[1] for r in rows}


ka, a = load(sys.argv[1])
kb, b = load(sys.argv[2])
keys = sorted(set(a) | set(b), key=str)
same = [k for k in keys if a.get(k) == b.get(k)]
diff = [k for k in keys if a.get(k) != b.get(k)]
print(f"{sys.argv[1]} vs {sys.argv[2]} ({ka}): {len(keys)} entries, {len(same)} the same, {len(diff)} differ")
if ka == "results.jsonl":
    contra = [k for k in diff if a.get(k) not in DEFINITE_NOT and b.get(k) not in DEFINITE_NOT]
    print(f"  contradictions (two definite answers that differ): {len(contra)}")
    from collections import Counter
    for (x, y), n in sorted(Counter((a.get(k), b.get(k)) for k in diff).items(), key=lambda t: -t[1]):
        print(f"  {x} -> {y}: {n}")
    for k in contra:
        print("  CONTRADICTION", k, a.get(k), b.get(k))
    sa = sum(1 for v in a.values() if v not in DEFINITE_NOT)
    sb = sum(1 for v in b.values() if v not in DEFINITE_NOT)
    print(f"  definite answers: {sa} and {sb}")
else:
    for k in diff:
        print(f"  {k}: exit {a.get(k)} -> {b.get(k)}")
