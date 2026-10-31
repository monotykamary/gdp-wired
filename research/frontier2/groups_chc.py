"""The CHC-COMP groups of the second corpus: research/frontier2/candidates-chc.md's groups A-I, from the 0.20.0 gap rows
(runs/modal/chc2/gap-v020.json, compare/chc/prof/gap.py: tasks Spacer, Golem or Eldarica solve in 60 s and gdp-wired
0.20.0 doesn't, with the class of Spacer's invariant and what proveRule did given it), then restricted to the tasks
gdp-wired 0.21.0 still doesn't solve (runs/modal/infer/chc-final, the CHANGELOG's 0.21.0 run, Modal, 60 s); beside it,
how many of those boat's run solved (runs/backends/chc-gdp, the same commit's library on boat's faster vCPUs).

    python3 research/frontier2/groups_chc.py [--runs runs] [--tasks]

A task falls in the first group whose test it meets, in the order below (the candidates' groups overlap by 3: three tasks
of D whose Spacer invariant also reads a quantifier, counted in D here and in F there).
"""
import argparse
import collections
import json

WITHIN = {"bound", "a yes/no guard", "two values", "a disjunction of two (a counterexample's form)"}
SUB_C = "yes/no values beside at most one linear literal (of at most two values)"
SUB_D = {"three or more linear literals", "two linear literals and yes/no values"}


def lustre(t):
    return t.startswith("vmt-chc-benchmarks/lustre/")


GROUPS = [
    ("A", "Lustre: an invariant within the templates whose step goal the prover leaves undecided over the wide transition, even given",
     lambda r: r["kind"] == "sat" and lustre(r["task"]) and r.get("class") in WITHIN and (r.get("given") or "").startswith("not proven: an invariant conjunct's goal undecided")),
    ("B", "Lustre: an invariant within the templates, proven once given, that the search doesn't find",
     lambda r: r["kind"] == "sat" and lustre(r["task"]) and r.get("class") in WITHIN and r.get("given") == "proven"),
    ("G", "not Lustre: an invariant within the templates that the search doesn't find",
     lambda r: r["kind"] == "sat" and not lustre(r["task"]) and r.get("class") in WITHIN),
    ("C", "a guard over several yes/no values (a program counter in bits) beside at most one linear literal",
     lambda r: r["kind"] == "sat" and r.get("class") == "a disjunction of three or more" and r.get("sub") == SUB_C),
    ("D", "a clause of two or more linear literals (three or more, or two beside yes/no values)",
     lambda r: r["kind"] == "sat" and r.get("class") == "a disjunction of three or more" and r.get("sub") in SUB_D),
    ("E", "an atom over more than three values",
     lambda r: r["kind"] == "sat" and r.get("class") == "more than three values in one atom"),
    ("F", "the invariant reads a remainder or a quotient, or keeps an existential from its projection (stated since 0.20.0 as `exists`)",
     lambda r: r["kind"] == "sat" and (r.get("given") or "").startswith("a conjunct gdp-wired can't state here")),
    ("H", "unsat, Lustre: a derivation of false the runs don't find",
     lambda r: r["kind"] == "unsat" and lustre(r["task"])),
    ("I", "unsat, the others: a derivation of false the runs don't find",
     lambda r: r["kind"] == "unsat" and not lustre(r["task"])),
    ("-", "the rest (Boolean structure past 4,000 clauses, no Spacer model, other classes)", lambda r: True),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", default="runs")
    ap.add_argument("--tasks", action="store_true", help="list every task of each group")
    a = ap.parse_args()
    gap = json.load(open(f"{a.runs}/supercomputer/chc2/gap-v020.json"))
    load = lambda p: {r["task"]: r for r in map(json.loads, open(p))}
    final = load(f"{a.runs}/supercomputer/infer/chc-final/results.jsonl")
    boat = load(f"{a.runs}/backends/chc-gdp/results.jsonl")
    solved = lambda rs, t: rs.get(t, {}).get("answer") in ("sat", "unsat")
    by = collections.defaultdict(list)
    for t, r in sorted(gap.items()):
        g = next(k for k, _, test in GROUPS if test(r))
        by[g].append(t)
    print("group | reason | at 0.20.0 (gap-v020.json) | solved at 0.21.0 (chc-final) | left at 0.21.0 | of those, solved on boat (backends/chc-gdp)")
    for k, why, _ in GROUPS:
        ts = by[k]
        left = [t for t in ts if not solved(final, t)]
        onboat = [t for t in left if solved(boat, t)]
        print(f"{k} | {why} | {len(ts)} | {len(ts) - len(left)} | {len(left)} | {len(onboat)}")
    tot = sum(len(v) for v in by.values())
    left_all = [t for v in by.values() for t in v if not solved(final, t)]
    print(f"all | | {tot} | {tot - len(left_all)} | {len(left_all)} | {len([t for t in left_all if solved(boat, t)])}")
    if a.tasks:
        for k, why, _ in GROUPS:
            left = [t for t in by[k] if not solved(final, t)]
            print(f"\n## {k}: {len(left)} left at 0.21.0")
            for t in left:
                r = gap[t]
                extra = f"  [{r.get('class')}; given: {r.get('given')}]" if r["kind"] == "sat" else f"  [Golem: {r.get('cex')} steps; {r.get('class')}]"
                print(f"{t}{' (solved on boat)' if solved(boat, t) else ''}{extra}")


if __name__ == "__main__":
    main()
