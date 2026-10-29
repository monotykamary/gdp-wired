"""The side-by-side table from a DuoAI batch (duoai.py's --out) and a gdp-wired batch (modal/run.py's --out with
gdp-jobs.json): one row per protocol and limit, each tool's verdicts and wall times over its runs.

    python3 research/protocols/duoai/table.py runs/duoai/main runs/duoai/gdp [runs/duoai/hard]
"""
import json
import pathlib
import re
import sys

PROTOCOLS = ["lock_server_sync", "lock_server_async", "decentralized_lock", "distributed_lock", "two_phase_commit",
             "ticket_lock", "toy_consensus_forall", "consensus_wo_decide", "ring_leader_election", "sharded_key_value_store"]
PAPER = {"lock_server_sync": 1.3, "lock_server_async": 1.9, "decentralized_lock": 9.9, "distributed_lock": 6.1, "two_phase_commit": 1.5,
         "ticket_lock": 23.9, "toy_consensus_forall": 1.9, "consensus_wo_decide": 3.9, "ring_leader_election": 3.5, "sharded_key_value_store": 1.9}


def duoai(d: pathlib.Path) -> dict:
    out = {}
    for f in sorted(d.glob("*.json")):
        r = json.loads(f.read_text())
        rc = r.get("recheck") or {}
        ok = r["verdict"] == "proven" and rc.get("ok") and rc.get("safety_verbatim")
        out.setdefault((r["protocol"], r["limit"]), []).append(
            {"v": "proven" if ok else ("proven, recheck failed" if r["verdict"] == "proven" else r["verdict"]), "wall": r["wall"],
             "in_time": not r.get("killed", True),  # it exited by itself before the kill (the wall time is read just after)
             "runtime": r.get("duoai_runtime"), "sim": r.get("simulate"), "cpu": r.get("cpu_seconds"), "invs": rc.get("invariants")})
    return out


def gdp(d: pathlib.Path) -> dict:
    secs = {l.split("\t")[0]: float(l.split("\t")[2]) for l in (d / "summary.tsv").read_text().splitlines() if l}
    out = {}
    for f in sorted(d.glob("*-s*-r*.log")):
        name = f.stem
        p, lim = re.match(r"(.+)-s(\d+)-r\d+$", name).groups()
        t = f.read_text()
        m = re.search(r'^\{"id".*$', t, re.M)
        s = json.loads(m.group(0)).get("search", {}) if m else {}
        times = re.findall(r"^(\d+)m([\d.]+)s (\d+)m([\d.]+)s$", t, re.M)
        cpu = sum(int(a) * 60 + float(b) + int(c) * 60 + float(e) for a, b, c, e in times)
        out.setdefault((p, int(lim)), []).append({"v": s.get("verdict", "error"), "wall": secs[name], "ms": s.get("ms"), "cpu": round(cpu, 1),
                                                   "laws": len(s.get("found", []))})
    return out


def cell(rs: list, limit: int) -> str:
    if not rs:
        return "-"
    vs = [r["v"] for r in rs]
    n = sum(v == "proven" and r.get("in_time", r["wall"] <= limit) for v, r in zip(vs, rs))
    walls = sorted(r["wall"] for r in rs)
    span = f"{walls[0]:.1f}" if walls[0] == walls[-1] else f"{walls[0]:.1f}–{walls[-1]:.1f}"
    return f"{n}/{len(rs)}, {span} s"


def main():
    du, gd = duoai(pathlib.Path(sys.argv[1])), gdp(pathlib.Path(sys.argv[2]))
    hard = duoai(pathlib.Path(sys.argv[3])) if len(sys.argv) > 3 else {}
    head = "| Protocol | Paper (DuoAI, 28 cores) | DuoAI 60 s | gdp-wired 60 s | DuoAI 10 s | gdp-wired 10 s |" + (" DuoAI 60 s, hard 2 CPUs | DuoAI 10 s, hard 2 CPUs |" if hard else "")
    print(head)
    print("|" + " --- |" * (head.count("|") - 1))
    for p in PROTOCOLS:
        row = [p, f"{PAPER[p]} s", cell(du.get((p, 60), []), 60), cell(gd.get((p, 60), []), 60), cell(du.get((p, 10), []), 10), cell(gd.get((p, 10), []), 10)]
        if hard:
            row += [cell(hard.get((p, 60), []), 60), cell(hard.get((p, 10), []), 10)]
        print("| " + " | ".join(row) + " |")
    for name, rs in (("DuoAI", du), ("gdp-wired", gd), ("DuoAI hard", hard)):
        for lim in (60, 10):
            got = [p for p in PROTOCOLS if rs.get((p, lim)) and all(r["v"] == "proven" and r.get("in_time", r["wall"] <= lim) for r in rs[(p, lim)])]
            if rs:
                print(f"{name} at {lim} s: {len(got)} of 10 in every run")
    # detail: DuoAI's split and CPU, gdp-wired's search time and CPU, medians
    med = lambda xs: sorted(xs)[len(xs) // 2] if xs else None
    print("\n| Protocol | Limit | DuoAI wall / own runtime / simulation / CPU s (medians) | invariants | gdp-wired wall / search / CPU s (medians) | laws found |")
    print("| --- | --- | --- | --- | --- | --- |")
    for lim in (60, 10):
        for p in PROTOCOLS:
            d, g = du.get((p, lim), []), gd.get((p, lim), [])
            dp = [r for r in d if r["v"] == "proven"]
            print(f"| {p} | {lim} s | {med([r['wall'] for r in d])} / {med([r['runtime'] for r in dp])} / {med([r['sim'] for r in d if r['sim']])} / {med([r['cpu'] for r in d])} "
                  f"| {med([r['invs'] for r in dp])} | {med([r['wall'] for r in g])} / {med([r['ms'] / 1000 for r in g if r['ms']])} / {med([r['cpu'] for r in g])} | {med([r['laws'] for r in g])} |")


if __name__ == "__main__":
    main()
