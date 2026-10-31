"""The TIP 2015 groups the corpus's TIP items stand for, counted from the benchmark runs (run from the repo root):

    python3 research/frontier2/groups_tip.py [--runs runs] > runs/corpus2/groups-tip.txt

Every figure is read from a run directory under --runs: supercomputer/arith/tip-gdp (gdp-wired at 0.21.0, the CHANGELOG's
140 of 492), backends/tip-gdp3 (the same at 0.21.0 on boat VMs), supercomputer/tip/full2 (cvc5, cvc5 with conjecture
generation, Vampire, at 60 s), supercomputer/tip/diag-t300 (proveData at 300 s, a diagnostic). The classes of the 20 failures
read by hand are compare/tip/README.md's ("Where gdp-wired stops"), written out below as that table lists them: a
class's size is known only on that sample of 20, and nothing here extrapolates it.
"""
import argparse
import collections
import json
import re

# compare/tip/README.md, "Where gdp-wired stops": the 20 read of the sample of 30 (runs/modal/tip/sample30.txt).
READ = {
    "an equation about another function, beyond the conjectures": ["prod/lemma_09", "isaplanner/prop_53", "tip2015/sort_ISortCount", "prod/lemma_14", "tip2015/bin_nat_plus", "tip2015/bin_nat_times"],
    "a conditional lemma (an implication, a predicate kept, injectivity)": ["prod/prop_14", "tip2015/sort_nat_ISortSorts", "prod/prop_42", "grammars/packrat_unambigPackrat", "tip2015/list_nat_deleteAll_count"],
    "an accumulator's generalisation": ["prod/prop_35", "isaplanner/prop_49"],
    "a theory of several lemmas": ["tip2015/sort_nat_ISortPermutes", "tip2015/list_perm_trans", "tip2015/bin_nat_times_assoc", "tip2015/bin_times_assoc", "tip2015/int_add_assoc", "tip2015/regexp_SeqDistrPlus"],
    "induction on two lists together": ["isaplanner/prop_84"],
}
# Each item's problem and the group it stands for.
ITEMS = {
    "prod/lemma_09": "read: an equation about another function, beyond the conjectures",
    "isaplanner/prop_53": "read: an equation about another function, beyond the conjectures",
    "prod/prop_14": "read: a conditional lemma (an implication, a predicate kept, injectivity)",
    "prod/prop_42": "read: a conditional lemma (an implication, a predicate kept, injectivity)",
    "tip2015/sort_nat_ISortPermutes": "read: a theory of several lemmas",
    "prod/prop_35": "read: an accumulator's generalisation",
    "isaplanner/prop_49": "read: an accumulator's generalisation",
    "isaplanner/prop_84": "read: induction on two lists together",
    "tip2015/bin_nat_plus": "binary numbers (tip2015/bin_*)",
    "tip2015/nat_pow_pow": "powers and factorials (refute threw in full2)",
    "tip2015/list_PairOdds": "more time (proven by diag-t300 only)",
    "tip2015/weird_nat_add3acc_spec": "add3acc, taken by well-founded recursion (tip2015/weird_nat_add3acc_*)",
    "tip2015/sort_HSortCount": "termination not proven: no measure is proven to fall at every call",
    "tip2015/mccarthy91_M1": "recursion on an Int (no parameter a measure reads)",
    "tip2015/mccarthy91_M2": "recursion on an Int (no parameter a measure reads)",
}


def load(path, tool="gdp"):
    out = {}
    for line in open(path):
        r = json.loads(line)
        if r.get("tool", "gdp") == tool:
            out[r["task"].removesuffix(".smt2")] = r
    return out


def why(r):
    for s in r.get("stages", []):
        if s.get("stage") == "answer":
            return s.get("why", "")
    return ""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", default="runs")
    a = ap.parse_args()
    R = a.runs
    g = load(f"{R}/supercomputer/arith/tip-gdp/results.jsonl")
    b = load(f"{R}/backends/tip-gdp3/results.jsonl")
    full2 = {t: load(f"{R}/supercomputer/tip/full2/results.jsonl", t) for t in ("gdp", "cvc5", "cvc5cg", "vampire")}
    t300 = load(f"{R}/supercomputer/tip/diag-t300/results.jsonl")
    theorems = {t for t in g if not t.startswith("false/")}
    print(f"runs/modal/arith/tip-gdp (0.21.0): {len(theorems)} theorems, {sum(g[t]['answer'] == 'proven' for t in theorems)} proven; answers {dict(collections.Counter(g[t]['answer'] for t in theorems))}")
    print(f"runs/backends/tip-gdp3 (0.21.0, boat): {sum(b[t]['answer'] == 'proven' for t in b if not t.startswith('false/'))} proven of {sum(1 for t in b if not t.startswith('false/'))}")
    unproven = {t for t in theorems if g[t]["answer"] != "proven"}
    others = lambda t: ", ".join(x for x in ("cvc5", "cvc5cg", "vampire") if full2[x].get(t, {}).get("answer") == "proven") or "none"

    groups = collections.OrderedDict()
    for cls, ts in READ.items():
        groups[f"read: {cls}"] = ts
    groups["binary numbers (tip2015/bin_*)"] = sorted(t for t in theorems if t.startswith("tip2015/bin_"))
    groups["powers and factorials (refute threw in full2)"] = sorted(t for t in full2["gdp"] if full2["gdp"][t]["answer"] == "error")
    groups["more time (proven by diag-t300 only)"] = sorted(t for t in t300 if t300[t]["answer"] == "proven" and full2["gdp"].get(t, {}).get("answer") != "proven")
    groups["add3acc, taken by well-founded recursion (tip2015/weird_nat_add3acc_*)"] = sorted(t for t in theorems if t.startswith("tip2015/weird_nat_add3acc"))
    # Refusals at 0.21.0 by their reason (the answer's why), the function named.
    term = collections.defaultdict(list)
    fname = collections.defaultdict(collections.Counter)
    for t in theorems:
        if g[t]["answer"] != "unsupported":
            continue
        w = why(g[t])
        m = re.match(r"recursion whose termination isn't proven: (\S+): (.*)", w)
        if m:
            kind = "recursion on an Int (no parameter a measure reads)" if "no parameter a measure reads" in m.group(2) else "termination not proven: no measure is proven to fall at every call" if "no measure is proven to fall" in m.group(2) else m.group(2)[:80]
            term[kind].append(t)
            fname[kind][re.sub(r"^F[0-9]+_", "", m.group(1).rstrip(":"))] += 1
    for k, ts in term.items():
        groups[k] = sorted(ts)
        print(f"{k}: {len(ts)} theorems, by the function refused: {dict(fname[k].most_common())}")

    print("\n| group | tasks | unproven at 0.21.0 (arith/tip-gdp) | proven by another tool at 60 s (full2) | the items |")
    print("| --- | --- | --- | --- | --- |")
    for k, ts in groups.items():
        un = [t for t in ts if t in unproven]
        oth = [t for t in un if others(t) != "none"]
        items = [i for i, gr in ITEMS.items() if gr == k]
        size = f"{len(ts)} (of the 20 read)" if k.startswith("read: ") else str(len(ts))
        print(f"| {k} | {size} | {len(un)} | {len(oth)} | {', '.join(items)} |")
        for t in ts:
            print(f"|   | {t} | {g.get(t, {}).get('answer', 'not in the run')} (boat: {b.get(t, {}).get('answer', '-')}) | {others(t)} | |")
    print("\nPer item: gdp-wired at 0.21.0 (arith/tip-gdp; boat tip-gdp3), and full2's other tools")
    for i, k in ITEMS.items():
        print(f"  {i}: {g[i]['answer']} {g[i]['seconds']} s (boat {b[i]['answer']}); full2: cvc5 {full2['cvc5'][i]['answer']}, cvc5cg {full2['cvc5cg'][i]['answer']}, vampire {full2['vampire'][i]['answer']}; group: {k}")

    print("\nRefused at 0.21.0, by reason (arith/tip-gdp, the 492 theorems and false/'s 68):")
    reasons = collections.Counter()
    for t, r in g.items():
        if r["answer"] == "unsupported":
            w0 = why(r)
            w = re.sub(r": F\d+_\S+: .*", "", w0) + (" (on an Int: no parameter a measure reads)" if "no parameter a measure reads" in w0 else "")
            reasons[(w[:110], "false/" if t.startswith("false/") else "theorems")] += 1
    for (w, where), n in sorted(reasons.items(), key=lambda kv: -kv[1]):
        print(f"  {n:4}  {where:8}  {w}")


if __name__ == "__main__":
    main()
