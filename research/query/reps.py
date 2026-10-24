"""The representative queries, both sides of a paired run (jobs.py reps --pair or --envs): `python3 research/query/reps.py
<run dir>`. Per job: the answer each side printed; for the bounded runs and k-induction (unsat__), the depths each
reached and the wall ms of the depths both refuted; for the false step goals (pairs__) the CDCL nodes each searched in
the same time; for every job the root queries each logged (count, summed ms, CDCL nodes)."""
import json
import pathlib
import sys

d = pathlib.Path(sys.argv[1])
spec = {j["name"]: (i, j) for i, j in enumerate(json.loads((d / "jobs.json").read_text()))}


def sides(text):
    out, at = {"here": [], "main": []}, None
    for l in text.splitlines():
        if l in ("=here", "=main"): at = l[1:]
        elif at and l.startswith("{"):
            try: out[at].append(json.loads(l))
            except json.JSONDecodeError: pass
    return out


def queries(name):
    f = d / name / "q.jsonl"
    if not f.exists(): return {}
    rows = [json.loads(l) for l in f.read_text().splitlines() if l.startswith("{")]
    pids = list(dict.fromkeys(r["pid"] for r in rows))
    i, j = spec[name]
    first = "main" if j["cmd"].startswith("echo =main") else "here"
    # (each side's processes in the order they ran: the first side's first; kind.ts's child is a pid of its own)
    out = {"here": [], "main": []}
    text = (d / f"{name}.log").read_text()
    order = [l[1:] for l in text.splitlines() if l in ("=here", "=main")]
    # assign pids by time order: split where the second side's first query appears (pid sets are disjoint and in order)
    half = len(pids) // 2 if len(pids) > 1 else 1
    for r in rows: out[first if pids.index(r["pid"]) < half else ("main" if first == "here" else "here")].append(r)
    return out


tot = {"here": 0, "main": 0}
for name in sorted(spec):
    f = d / f"{name}.log"
    if not f.exists(): print(name, "missing"); continue
    s = sides(f.read_text())
    ans = {k: next((x.get("answer") for x in reversed(v) if "answer" in x), None) for k, v in s.items()}
    line = [name, f"answer {ans['here']} / {ans['main']}"]
    if name.startswith("unsat__"):
        for k in ("bmc", "kind"):
            st = {side: next((x for x in reversed(v) if x.get("stage") == k), None) for side, v in s.items()}
            if not all(st.values()): continue
            dh, dm = st["here"]["depths"], st["main"]["depths"]
            if k == "bmc":
                rh = {x[0]: x[3] for x in dh if x[1] == "r"}; rm = {x[0]: x[3] for x in dm if x[1] == "r"}
                common = sorted(set(rh) & set(rm))
                line.append(f"bmc depth {max([x[0] for x in dh] or [0])} / {max([x[0] for x in dm] or [0])}, refuted both {common[-3:]}: ms {[rh[c] for c in common[-3:]]} / {[rm[c] for c in common[-3:]]}")
            else:
                line.append(f"kind k {max([x[0] for x in dh] or [0])} / {max([x[0] for x in dm] or [0])}")
    q = queries(name)
    if q:
        agg = {side: (len(v), round(sum(r["ms"] for r in v)), sum(r.get("nodes", 0) for r in v)) for side, v in q.items()}
        line.append(f"queries (n, ms, nodes) {agg['here']} / {agg['main']}")
        if name.startswith("pairs__"):
            big = {side: max(v, key=lambda r: r["hyps"]) if v else {} for side, v in q.items()}
            line.append(f"the 944 goal's nodes {big['here'].get('nodes')} / {big['main'].get('nodes')} in {big['here'].get('ms')} / {big['main'].get('ms')} ms")
    print(" | ".join(line))
