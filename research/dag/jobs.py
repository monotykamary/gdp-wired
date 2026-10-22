"""The jobs files research/dag/modal_dag.py runs: `python3 research/dag/jobs.py <kind> > <jobs.json>`.

  dump      given-dump.ts on each of the 332 step-goal tasks (step332-tasks.json), the same 55 s as given.ts had
  solvers   z3 and cvc5 on each dumped goal.smt2 (runs/modal/dag/goals/<task>/), 60 s, one (solver, task) a container
  profile   profile.ts (the tree search, instrumented) on each dumped goal.json [--sample names-file]
  dag       dag.ts (the DAG search) on each dumped goal.json, its certificate checked by check-dag.ts
  cdcl      cdcl.ts (CDCL over the atoms, the same certificate) likewise [--no-bounds]
  vars      vars.ts (the goal's variables by class, and the reading with every yes/no and finite value fixed)
  items     items.ts on each example the test script runs (the tree against the DAG on the library's own goals)
  bmc       bmc.ts on each unsat Lustre task with a Golem derivation (bmc-tasks.json), k = 1..10
"""
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent.parent
TASKS = json.loads((HERE / "step332-tasks.json").read_text())
BYTASK = {t["task"]: t for t in json.loads((GDP / "runs/modal/chc2/given-spacer3/tasks.json").read_text())}


def safe(task: str) -> str:
    return task.removesuffix(".yml").replace("/", "__")


def main(kind: str, extra: list[str]):
    jobs = []
    names = TASKS
    if "--sample" in extra:
        names = json.loads(pathlib.Path(extra[extra.index("--sample") + 1]).read_text())
    if kind == "dump":
        for t in names:
            smt2 = BYTASK[t]["smt2"]
            jobs.append({"name": safe(t), "limit": 90, "collect": "/tmp/out",
                         "cmd": f"bun research/dag/given-dump.ts /bench/{smt2} compare/chc/prof/given-models.json --ms 55000 --out /tmp/out"})
    elif kind == "solvers":
        for t in names:
            g = f"/goals/{safe(t)}/goal.smt2"
            # (the job's seconds, modal_dag.py's, are the solver's wall time: nothing else runs in the command)
            jobs.append({"name": f"z3__{safe(t)}", "limit": 75, "cmd": f"timeout 60 z3 -smt2 {g}; echo exit=$?"})
            jobs.append({"name": f"cvc5__{safe(t)}", "limit": 75, "cmd": f"timeout 60 cvc5 {g}; echo exit=$?"})
    elif kind in ("profile", "dag", "cdcl"):
        ms = extra[extra.index("--ms") + 1] if "--ms" in extra else "55000"
        script = {"profile": "profile.ts", "dag": "dag.ts", "cdcl": "cdcl.ts"}[kind]
        flags = " ".join(x for x in extra if x.startswith("--no-"))
        for t in names:
            jobs.append({"name": safe(t), "limit": int(ms) // 1000 + 60, "collect": "/tmp/out",
                         "cmd": f"bun research/dag/{script} /goals/{safe(t)}/goal.json --ms {ms} --out /tmp/out {flags}".strip()})
    elif kind == "vars":
        for t in names:
            jobs.append({"name": safe(t), "limit": 120, "cmd": f"bun research/dag/vars.ts /goals/{safe(t)}/goal.json"})
    elif kind == "items":
        for x in "readme guide composition sets quantifiers functions datatypes lemmas discover invoices folds trees pairs groups charts xstate infer cyclic cycles data scopes lists sizes liveness budget gdp steps".split():
            jobs.append({"name": x, "limit": 1800, "cmd": f"bun research/dag/items.ts examples/{x}.ts --max 200 --ms 3000"})
    elif kind == "bmc":
        for t in json.loads((HERE / "bmc-tasks.json").read_text()):
            jobs.append({"name": safe(t["task"]), "limit": 300, "cmd": f"bun research/dag/bmc.ts /bench/{t['smt2']} --k 10 --ms 240000"})
    else:
        raise SystemExit(__doc__)
    json.dump(jobs, sys.stdout, indent=0)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2:])
