"""The jobs files of research/query/modal_query.py: `python3 research/query/jobs.py <kind> [--base] [--prof] > jobs.json`.

  (--base: each job also on main's tree, its own container; --pair: both in one container, one after the other)
  reps    the representative queries: CHC sat (the join on Lustre's wide steps, solve.ts with no second CPU), CHC
          unsat (metros, car: compare/chc/kind.ts, k-induction and the bounded runs in turn), ITS nontermination (s1,
          hqr: compare/term/solve.ts), the false 944-hypothesis step goals (pairs-false.ts, 120 s)
  realworld  the real-world corpus' laws, research/realworld/jobs.ts's commands
  g332    research/step/goal.ts on each of research/dag's 332 step goals (grow, the goal's own budget within 55 s)
  base    (not a jobs file) writes `.base`: main e883e53's tree with research/query's instrumentation patch
          (research/query/base.patch), for runs beside main (each job then also as base-<name> with "base": true)
"""
import json
import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent.parent
MAIN = GDP.parent / "gdp-wired"
SAT = ["DRAGON_4_000_001", "DRAGON_5_000_001", "DRAGON_11_000_001", "DRAGON_13_000_001", "DRAGON_12_e2_1618_000_001", "car_5_000_001", "car_6_000_001", "metros_2_000_001"]
UNSAT = ["metros_2_e2_704_000", "metros_3_e3_1117_000", "metros_2_e3_112_000_001", "car_5_e3_11_000", "car_6_e2_893_000_001", "car_5_e2_405_e2_1083_000_001"]
ITS = ["s1.t2", "s1.t2_fixed", "s1-striped.t2", "hqr.t2_fixed", "hqr.c.i.hqr.pl.t2.nor.t2.rlgfixed.t2_fixed"]
BUGS = ["diagonal only", "skips the last left effect", "first right effect only", "within one side"]


def smt2(name: str) -> str:
    tasks = json.loads((MAIN / "runs/chc3/final-mine/tasks.json").read_text())
    return next(t["smt2"] for t in tasks if t["task"] == f"vmt-chc-benchmarks/lustre/{name}.yml")


def main(kind: str, extra: list[str]):
    prof = "--prof" in extra
    jobs = []
    if kind == "reps":
        for t in SAT:
            jobs.append({"name": f"sat__{t}", "limit": 100, "cmd": f"bun compare/chc/solve.ts /chc/{smt2(t)} --runs-ms 5000 --houdini-ms 55000 --kind-ms 0 --bmc-ms 0"})
        for t in UNSAT:
            jobs.append({"name": f"unsat__{t}", "limit": 80, "cmd": f"bun compare/chc/kind.ts /chc/{smt2(t)} --ms 55000"})
        for t in ITS:
            jobs.append({"name": f"its__{t}", "limit": 90, "cmd": f"bun compare/term/solve.ts /its/Integer_Transition_Systems/From_T2/{t}.ari --limit 60"})
        for b in BUGS:
            jobs.append({"name": f"pairs__{b.replace(' ', '_')}", "limit": 200, "cmd": f"bun research/query/pairs-false.ts '{b}' --ms 120000"})
    elif kind == "g332":
        for t in json.loads((GDP / "research/dag/step332-tasks.json").read_text()):
            s = t.removesuffix(".yml").replace("/", "__")
            jobs.append({"name": f"g332__{s}", "limit": 120, "cmd": f"bun research/step/goal.ts /goals/{s}/goal.json --ms 55000"})
    elif kind == "realworld":
        # the real-world corpus' laws (research/realworld/jobs.ts's jobs), as its runs give them
        rw = json.loads(subprocess.run(["bun", "research/realworld/jobs.ts"], cwd=GDP, capture_output=True, text=True, check=True).stdout)
        for j in rw:
            jobs.append({"name": f"rw__{j['name']}", "limit": 200, "cmd": j["cmd"]})
    elif kind == "base":
        base = GDP / ".base"
        subprocess.run(["rm", "-rf", str(base)], check=True)
        base.mkdir()
        subprocess.run(f"git -C {GDP} archive e883e53 | tar -x -C {base}", shell=True, check=True)
        subprocess.run(["git", "apply", "--directory=.base", str(HERE / "base.patch")], cwd=GDP, check=True)
        subprocess.run(["cp", "-r", str(HERE), str(base / "research/")], check=True)
        return
    else:
        raise SystemExit(__doc__)
    for j in jobs:
        j["prof"] = prof
    if "--base" in extra:
        jobs = jobs + [{**j, "name": f"base-{j['name']}", "base": True} for j in jobs]
    elif "--envs" in extra:
        # both settings in one container, one after the other (the first first in every other job): `--envs "A=1|A=0"`,
        # each side's output after a "=here" (the first) or "=main" (the second) line, as --pair writes them
        a, b = extra[extra.index("--envs") + 1].split("|")
        for i, j in enumerate(jobs):
            here, main = f"echo =here; (export {a}; {j['cmd']})", f"echo =main; (export {b}; {j['cmd']})"
            j["cmd"] = f"{here}; {main}" if i % 2 == 0 else f"{main}; {here}"
            j["limit"] = 2 * j["limit"]
    elif "--pair" in extra:
        # both sides in one container, one after the other (here first in every other job), each line of output after
        # a "=here" or "=main" line: the same CPU for both, so their times compare
        for i, j in enumerate(jobs):
            here, main = f"echo =here; {j['cmd']}", f"echo =main; (cd .base && {j['cmd']})"
            j["cmd"] = f"{here}; {main}" if i % 2 == 0 else f"{main}; {here}"
            j["limit"] = 2 * j["limit"]
    json.dump(jobs, sys.stdout, indent=0)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2:])
