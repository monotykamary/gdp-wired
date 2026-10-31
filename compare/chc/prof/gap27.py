"""The gap to Spacer and Golem on CHC-COMP's LIA-Lin track at a release, by group, family and cause:
`python3 compare/chc/prof/gap27.py --runs <runs dir> [--mine query/m5/chc-mine,...] [--main query/m5/chc-main,...]
[--tasks] [--out <file.json>]`.

- **The gap:** tasks Spacer or Golem solves at 60 s (runs/modal/chc2/combined-v020, the answer its expected verdict
  where one is known) that the first of `--mine`'s runs doesn't; beside it, how many of all of `--mine`'s runs (and
  `--main`'s) solve each, so a task answered now and then reads as such.
- **The group:** research/frontier2/groups_chc.py's, from the 0.20.0 gap rows (runs/modal/chc2/gap-v020.json: the class
  of Spacer's invariant, what proveRule did given it); `new` for a task not in those rows (solved at 0.20.0).
- **The family:** the benchmark's directory, Lustre's tasks by model (DRAGON, car, metros, ...).
- **Given:** whether the kernel proves Spacer's invariant with the usual certificate (runs/chc3/given2-usual).
- **The cause,** from the stages the first run printed:
  - sat: the join's end (`time`, `target`: a counterexample no candidate or cube rules out, `stuck`: a goal undecided,
    `inductive` but the kernel's search after it failing), else the stage the search stopped in;
  - unsat: the deepest depth the bounded runs refuted, against Golem's derivation (gap-v020's cex steps).
"""
import argparse
import collections
import json
import os
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "..", "research", "frontier2"))


def load(path):
    return {r["task"]: r for r in map(json.loads, open(path)) if r.get("tool", "gdp") in ("gdp", "given")}


def family(task):
    parts = task.split("/")
    if task.startswith("vmt-chc-benchmarks/lustre/"):
        return "lustre/" + re.match(r"[A-Za-z]+(?:_[A-Za-z]+)*", parts[-1]).group(0).rstrip("_")
    return "/".join(parts[:-1])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", default="runs")
    ap.add_argument("--mine", default="query/m5/chc-mine,query/m5/chcr1-mine,query/m5/chcr2-mine,query/m5/chcr3-mine,query/m4/chc-mine")
    ap.add_argument("--main", default="query/m5/chc-main,query/m5/chcr1-main,query/m5/chcr2-main,query/m5/chcr3-main,query/m4/chc-main")
    ap.add_argument("--tasks", action="store_true")
    ap.add_argument("--out")
    a = ap.parse_args()
    R = lambda p: os.path.join(a.runs, p)
    disputed = json.load(open(os.path.join(os.path.dirname(__file__), "..", "disputed.json")))
    others = [json.loads(l) for l in open(R("supercomputer/chc2/combined-v020/results.jsonl"))]

    def right(r):
        if r is None or r.get("answer") not in ("sat", "unsat"):
            return False
        if disputed.get(r["task"], {}).get("answer") == r["answer"]:
            return True
        return r.get("expected") in (None, "", "unknown") or r["answer"] == r["expected"]

    rival = collections.defaultdict(dict)
    for r in others:
        if r["tool"] in ("z3", "golem") and right(r):
            rival[r["task"]][r["tool"]] = r["answer"]
    mine = [load(R(p + "/results.jsonl")) for p in a.mine.split(",") if os.path.exists(R(p + "/results.jsonl"))]
    base = [load(R(p + "/results.jsonl")) for p in a.main.split(",") if os.path.exists(R(p + "/results.jsonl"))]
    first = mine[0]
    gap20 = json.load(open(R("supercomputer/chc2/gap-v020.json")))
    given = load(R("chc3/given2-usual/results.jsonl")) if os.path.exists(R("chc3/given2-usual/results.jsonl")) else {}
    from groups_chc import GROUPS

    def group(t, kind):
        r = gap20.get(t)
        if r is None:
            return "new"
        return next(k for k, _, test in GROUPS if test(r))

    def cause(r, kind):
        st = r.get("stages", []) if r else []
        if kind == "unsat":
            bmc = [s for s in st if s["stage"] == "bmc"]
            refuted = max([d[0] for s in bmc for d in s.get("depths", []) if d[1] == "r"], default=0)
            return f"bounded runs refuted to depth {refuted}"
        end = [s for s in st if s["stage"] == "infer join end"]
        why = end[-1]["why"] if end else ("no join" if any(s["stage"] == "infer houdini" for s in st) else "no search")
        if why.startswith("stuck"):
            why = "stuck"
        return f"join: {why}"

    rows = []
    for t, who in sorted(rival.items()):
        if right(first.get(t)):
            continue
        kind = next(iter(who.values()))
        g = (given[t].get("stages") or [{}])[-1] if t in given else None
        rows.append({
            "task": t, "kind": kind, "rivals": "+".join(sorted(who)), "group": group(t, kind), "family": family(t),
            "mine": sum(right(m.get(t)) for m in mine), "of": len(mine), "main": sum(right(m.get(t)) for m in base), "ofMain": len(base),
            "given": None if g is None else ("proven" if g.get("proven") and g.get("checked") else "not proven"),
            "cause": cause(first.get(t), kind), "cex": gap20.get(t, {}).get("cex"),
        })
    solvedFirst = sum(right(r) for r in first.values())
    print(f"first run {a.mine.split(',')[0]}: {solvedFirst} solved; rivals' union {len(rival)}; gap {len(rows)} "
          f"({sum(r['kind'] == 'sat' for r in rows)} sat, {sum(r['kind'] == 'unsat' for r in rows)} unsat)")
    print(f"  of the gap, solved in some other run of mine: {sum(r['mine'] > 0 for r in rows)}; never: {sum(r['mine'] == 0 for r in rows)}")
    for kind in ("sat", "unsat"):
        rs = [r for r in rows if r["kind"] == kind]
        print(f"\n## {kind}: {len(rs)}")
        for key in ("group", "family", "cause", "rivals", "given"):
            c = collections.Counter(str(r[key]) for r in rs)
            print(f"by {key}: " + ", ".join(f"{k} {v}" for k, v in c.most_common()))
        if kind == "sat":
            c = collections.Counter((r["family"], r["cause"]) for r in rs)
            print("by family and cause: " + ", ".join(f"{f} / {k} {v}" for (f, k), v in c.most_common(25)))
    if a.tasks:
        for r in rows:
            print(json.dumps(r))
    if a.out:
        json.dump(rows, open(a.out, "w"), indent=1)


if __name__ == "__main__":
    main()
