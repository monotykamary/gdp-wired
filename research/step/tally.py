"""Tally goal.ts runs: `python3 research/step/tally.py <run dir> [<run dir> ...]`. Per run: proven (of the jobs, and of
the Lustre ones), the search's milliseconds (median of the proven, and summed), the certificate's leaves (median and
sum over the proven), the check's verdicts; with two runs, the goals each proves that the other doesn't and, on the goals
both prove, the leaves and times side by side."""
import json
import pathlib
import statistics
import sys


def load(d):
    out = {}
    for f in sorted(pathlib.Path(d).glob("*.log")):
        if f.name.endswith(".client.log"):
            continue
        lines = [x for x in f.read_text().splitlines() if x.startswith("{")]
        try:
            r = json.loads(lines[-1]) if lines else {}
        except json.JSONDecodeError:
            r = {}
        out[f.stem] = r
    return out


def med(xs):
    return statistics.median(xs) if xs else None


def summary(name, rs):
    proven = {k: r for k, r in rs.items() if r.get("outcome") == "proven"}
    lustre = [k for k in proven if "__lustre__" in k]
    rejected = [k for k, r in rs.items() if r.get("outcome") == "rejected"]
    outcomes = {}
    for r in rs.values():
        outcomes[r.get("outcome", "none")] = outcomes.get(r.get("outcome", "none"), 0) + 1
    ms = [r["searchMs"] for r in proven.values()]
    leaves = [r["leaves"] for r in proven.values()]
    print(f"{name}: jobs {len(rs)}, proven {len(proven)} (Lustre {len(lustre)} of {sum('__lustre__' in k for k in rs)}), rejected {len(rejected)}, outcomes {outcomes}")
    print(f"  search ms over the proven: median {med(ms)}, sum {sum(ms)}; over all: sum {sum(r.get('searchMs', 0) for r in rs.values())}")
    print(f"  leaves over the proven: median {med(leaves)}, sum {sum(leaves)}, max {max(leaves) if leaves else None}; check ms median {med([r['checkMs'] for r in proven.values()])}")
    return proven


runs = [(d, load(d)) for d in sys.argv[1:]]
ps = [summary(d, rs) for d, rs in runs]
if len(ps) == 2:
    a, b = ps
    both = sorted(set(a) & set(b))
    print(f"only {runs[0][0]}: {len(set(a) - set(b))} {sorted(set(a) - set(b))[:12]}")
    print(f"only {runs[1][0]}: {len(set(b) - set(a))}")
    if both:
        la, lb = [a[k]["leaves"] for k in both], [b[k]["leaves"] for k in both]
        ta, tb = [a[k]["searchMs"] for k in both], [b[k]["searchMs"] for k in both]
        print(f"both {len(both)}: leaves sum {sum(la)} vs {sum(lb)}, median {med(la)} vs {med(lb)}; ms median {med(ta)} vs {med(tb)}, sum {sum(ta)} vs {sum(tb)}")
