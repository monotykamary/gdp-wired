"""Every figure in research/dag/README.md, from the run dirs under runs/modal/dag/: `python3 research/dag/summarize.py`."""
import collections
import glob
import json
import pathlib
import re
import statistics as st

RUNS = pathlib.Path(__file__).resolve().parent.parent.parent / "runs" / "modal" / "dag"
TASKS = json.loads((pathlib.Path(__file__).resolve().parent / "step332-tasks.json").read_text())
SAFE = {t.removesuffix(".yml").replace("/", "__"): t for t in TASKS}


def q(xs, p):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(p * len(xs)))] if xs else None


def med(xs):
    return st.median(xs) if xs else None


def solvers():
    print("## solvers (runs/modal/dag/solvers, the goals' SMT-LIB, 60 s, 2 vCPU)")
    res = collections.defaultdict(dict)
    for f in glob.glob(str(RUNS / "solvers" / "*.log")):
        n = pathlib.Path(f).stem
        tool, task = n.split("__", 1)
        t = open(f).read()
        secs = float(re.match(r"exit (-?\d+) in (\S+) s", t).group(2))
        w = [l.strip() for l in t.splitlines()[1:] if l.strip() in ("sat", "unsat", "unknown")]
        res[tool][task] = (w[0] if w else "none", secs)
    for tool, d in sorted(res.items()):
        un = [s for a, s in d.values() if a == "unsat"]
        print(f"  {tool}: {len(d)} goals, {dict(collections.Counter(a for a, _ in d.values()))}; unsat seconds median {med(un)}, p90 {q(un, .9)}, max {max(un) if un else None}; under 1 s: {sum(s < 1 for s in un)}")
    c = collections.Counter()
    for f in glob.glob(str(RUNS / "solvers-sanity" / "*.log")):
        w = [l.strip() for l in open(f).read().splitlines()[1:] if l.strip() in ("sat", "unsat", "unknown")]
        c[w[0] if w else "none"] += 1
    print(f"  sanity, z3 on each goal without its last hypothesis (runs/modal/dag/solvers-sanity): {dict(c)}")


def dump():
    print("## dump (runs/modal/dag/dump: given-dump.ts, the same 55 s as given.ts)")
    c = collections.Counter()
    for f in glob.glob(str(RUNS / "dump" / "*.log")):
        j = [json.loads(l) for l in open(f).read().splitlines() if l.startswith("{")][-1]
        c[(j.get("stuck"), j.get("lastGoal", {}).get("sameAsStuck"))] += 1
    print(f"  (stuck, last goal is the stuck one): {dict(c)}")
    hy = [len(json.load(open(d + "/goal.json"))["hyps"]) for d in glob.glob(str(RUNS / "goals" / "*"))]
    print(f"  goals: {len(hy)}, hypotheses median {med(hy)}, min {min(hy)}, max {max(hy)}")


def results(name, file="result.json"):
    out = {}
    for f in glob.glob(str(RUNS / name / "*" / file)):
        out[pathlib.Path(f).parent.name] = json.load(open(f))
    return out


def profile():
    print("## profile (runs/modal/dag/profile: tree.ts, kernel/prove.ts's search copied, the goal alone, its own budget within 55 s)")
    R = results("profile", "profile.json")
    print(f"  {len(R)} goals, outcomes {dict(collections.Counter(r['outcome'] for r in R.values()))}")
    tot = lambda k: sum(r[k] for r in R.values())
    L = tot("leavesProcessed")
    print(f"  leaves found {tot('leavesFound')}, processed {L}, each checked again over the kernel's rows: {tot('leafChecked')}; core replayed at the core alone: {tot('coreReplayed')}")
    print(f"  a leaf reading the same rows as an earlier leaf: {tot('sameRows')} ({100 * tot('sameRows') / L:.1f}%); the same core: {tot('sameCore')} ({100 * tot('sameCore') / L:.1f}%); its path holding an earlier leaf's core (a learned clause closes it): {tot('subsumedByEarlierCore')} ({100 * tot('subsumedByEarlierCore') / L:.1f}%)")
    per = [r["subsumedByEarlierCore"] / r["leavesProcessed"] for r in R.values() if r["leavesProcessed"]]
    print(f"  per goal, the share subsumed: median {med(per):.3f}, p10 {q(per, .1):.3f}, p90 {q(per, .9):.3f}")
    print(f"  time: search {tot('searchMs')} ms in all; solver {tot('solveMs')} ({100 * tot('solveMs') / tot('searchMs'):.1f}%), rows {tot('rowsMs')} ({100 * tot('rowsMs') / tot('searchMs'):.1f}%); nodes median {med([r['nodes'] for r in R.values()])}, leaves median {med([r['leavesFound'] for r in R.values()])}")
    ph = collections.Counter()
    for r in R.values():
        for k, v in r["phases"].items():
            ph[k] += v
    print(f"  growRoot's phases, ms in all: {dict(ph)}")
    print(f"  leaf depth (per goal median): median {med([r['depth']['median'] for r in R.values() if r['depth']['median'] is not None])}; deepest {max(r['depth']['max'] or 0 for r in R.values())}; core size (per goal median): median {med([r['coreSize']['median'] for r in R.values() if r['coreSize']['median'] is not None])}")
    return R


def proto(name):
    R = results(name)
    P = {k: r for k, r in R.items() if r["outcome"] == "proven"}
    ok = sum(1 for r in P.values() if r.get("check", {}).get("ok"))
    lustre = sum(1 for k in P if "lustre" in k)
    print(f"## {name}: {len(R)} goals, proven {len(P)} ({lustre} Lustre), checked by check-dag.ts {ok}; outcomes {dict(collections.Counter(r['outcome'] for r in R.values()))}")
    if P:
        ms = [r["searchMs"] for r in P.values()]
        print(f"  proven: search ms median {med(ms)}, p90 {q(ms, .9)}, max {max(ms)}; check ms median {med([r['check']['ms'] for r in P.values()])}, max {max(r['check']['ms'] for r in P.values())}")
        s = [r["size"] for r in P.values()]
        for k in ["nodes", "leaves", "steps", "unfoldedLeaves", "unfoldedSteps", "bytes"]:
            print(f"    {k}: median {med([x[k] for x in s])}, max {max(x[k] for x in s)}, sum {sum(x[k] for x in s)}")
        print(f"    unfolded/DAG leaves, per goal: median {med([x['unfoldedLeaves'] / x['leaves'] for x in s]):.2f}, max {max(x['unfoldedLeaves'] / x['leaves'] for x in s):.2f}")
    keys = [k for k in next(iter(R.values())).keys() if isinstance(next(iter(R.values()))[k], (int, float)) and k not in ("hyps",)]
    print("  medians over all goals: " + ", ".join(f"{k} {med([r[k] for r in R.values() if k in r])}" for k in keys))
    return R, P


def residual(prof, proven_any):
    print("## the goals no prototype closes: their variables (profile.ts, from the dumped goal)")
    left = {k: r for k, r in prof.items() if k not in proven_any}
    print(f"  {len(left)} goals ({sum('lustre' in k for k in left)} Lustre)")
    v = [r["vars"] for r in left.values()]
    for k in ["all", "yesNo", "numeric", "yesNoRead"]:
        xs = [x[k] for x in v]
        print(f"    {k}: median {med(xs)}, p10 {q(xs, .1)}, p90 {q(xs, .9)}, max {max(xs)}")
    share = [x["yesNoRead"] / x["yesNo"] for x in v if x["yesNo"]]
    print(f"    yes/no read by a hypothesis beside its bound, share: median {med(share):.2f}")
    fx = [f for r in left.values() for f in r["fixedYesNo"]]
    for k in ["open", "openNumeric", "rows", "numericVars"]:
        xs = [f[k] for f in fx]
        print(f"    every yes/no fixed at random (8 a goal): {k} median {med(xs)}, p90 {q(xs, .9)}, max {max(xs)}")
    print(f"    the solver's verdict there: {dict(collections.Counter(f['verdict'] for f in fx))}")
    zero = sum(1 for r in left.values() if all(f["openNumeric"] == 0 for f in r["fixedYesNo"]))
    print(f"    goals where fixing the yes/no values leaves no numeric atom open (all 8): {zero}")


def bmc():
    print("## bmc (runs/modal/dag/bmc: bmc.ts, k = 1..10, 240 s a task)")
    tasks = {t["task"].removesuffix(".yml").replace("/", "__"): t for t in json.loads((pathlib.Path(__file__).resolve().parent / "bmc-tasks.json").read_text())}
    rows = {}
    for f in glob.glob(str(RUNS / "bmc" / "*.log")):
        n = pathlib.Path(f).stem
        js = [json.loads(l) for l in open(f).read().splitlines() if l.startswith("{")]
        rows[n] = js
    done = {n: [j for j in js if j.get("done")] for n, js in rows.items()}
    proto = {n: d[0]["prototypeK"] for n, d in done.items() if d and d[0]["prototypeK"] is not None}
    z3 = {n: d[0]["z3K"] for n, d in done.items() if d and d[0]["z3K"] is not None}
    print(f"  tasks {len(rows)}, finished {sum(1 for d in done.values() if d)}; a checked run found: prototype {len(proto)}, z3 (reference) {len(z3)}, either {len(set(proto) | set(z3))}")
    for lab, d in [("prototype", proto), ("z3", z3)]:
        print(f"    {lab}: k found {dict(sorted(collections.Counter(d.values()).items()))}")
    bad = collections.Counter(j.get("why", "")[:40] for js in rows.values() for j in js if j.get("verdict") == "a model, not a run" or j.get("run") == "not a run")
    print(f"  models that weren't runs: {dict(bad)}")
    rej = sum(1 for js in rows.values() for j in js if j.get("verdict") == "no run (DAG REJECTED)")
    nr = sum(1 for js in rows.values() for j in js if j.get("verdict") == "no run (DAG checked)")
    print(f"  prototype 'no run of k' answers with their DAG checked: {nr}, rejected: {rej}")
    cex = {n: tasks[n]["cex"] for n in rows if n in tasks}
    short = [n for n, c in cex.items() if c is not None and c <= 10]
    print(f"  Golem's derivation within 10: {len(short)}; of those, found by the prototype {sum(n in proto for n in short)}, by z3 {sum(n in z3 for n in short)}")
    diffs = collections.Counter(z3[n] - cex[n] for n in z3 if cex.get(n) is not None)
    print(f"  z3's k minus Golem's derivation length: {dict(sorted(diffs.items()))}")


if __name__ == "__main__":
    solvers()
    dump()
    prof = profile()
    proven_any = set()
    for name in ["dag-nolearn", "dag-learn", "cdcl", "cdcl-lazy"]:
        if (RUNS / name).exists():
            _, P = proto(name)
            proven_any |= set(P)
    tree_proven = {k for k, r in prof.items() if r["outcome"] == "proven"}
    print(f"## union: proven by some prototype {len(proven_any)}; by the profiled tree search {len(tree_proven)}; by either {len(proven_any | tree_proven)}; tree-only {len(tree_proven - proven_any)}")
    residual(prof, proven_any | tree_proven)
    if (RUNS / "bmc").exists():
        bmc()
