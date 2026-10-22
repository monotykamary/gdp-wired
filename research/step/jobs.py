"""The jobs files of research/step: `python3 research/step/jobs.py <kind> [--ms 55000] [--env K=V ...] > <jobs.json>`,
run by research/step/modal_step.py (one container a job).

  goals332   goal.ts on each of research/dag's 332 dumped step goals (/goals/<task>/goal.json)
  goals223   goal.ts on each table step goal dumped by `table` (/goals223/<task>/goal.json)
  table      research/table/chc.ts --kernel on the 223 tasks chc-kernel handed to the kernel, its model kept and its
             step goal dumped (research/dag/given-dump.ts with that model)
  given223   compare/chc/prof/given.ts on each of the 223 with the model `table` kept (/goals223/<task>/model.json)
  given332   compare/chc/prof/given.ts on each of the 332 with Spacer's model (compare/chc/prof/given-models.json)
"""
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent.parent
TASKS332 = json.loads((GDP / "research/dag/step332-tasks.json").read_text())


def safe(task: str) -> str:
    return task.removesuffix(".yml").replace("/", "__")


def main(kind: str, extra: list[str]):
    ms = extra[extra.index("--ms") + 1] if "--ms" in extra else "55000"
    env = " ".join(extra[i + 1] for i, x in enumerate(extra) if x == "--env")
    pre = f"export {env}; " if env else ""
    jobs = []
    if kind == "goals332":
        for t in TASKS332:
            jobs.append({"name": safe(t), "limit": int(ms) // 1000 + 120, "cmd": f"{pre}bun research/step/goal.ts /goals/{safe(t)}/goal.json --ms {ms}"})
    elif kind == "goals223":
        for d in sorted((GDP / "runs/step/goals223").iterdir()):
            if (d / "goal.json").exists():
                jobs.append({"name": d.name, "limit": int(ms) // 1000 + 120, "cmd": f"{pre}bun research/step/goal.ts /goals223/{d.name}/goal.json --ms {ms}"})
    elif kind == "given223":
        for d in sorted((GDP / "runs/step/goals223").iterdir()):
            if (d / "model.json").exists():
                key = json.loads((d / "model.json").read_text())
                smt2 = next(iter(key))
                jobs.append({"name": d.name, "limit": 180, "cmd": f"{pre}bun compare/chc/prof/given.ts {smt2} /goals223/{d.name}/model.json --ms 55000"})
    elif kind == "table":
        rows = [json.loads(x) for x in (GDP.parent / "gdp-wired/runs/modal/table/chc-kernel/results.jsonl").read_text().splitlines()]
        for r in rows:
            outs = [json.loads(x) for x in r["out"].strip().split("\n") if x.startswith("{")]
            res = [x for x in outs if x.get("stage") == "result"]
            k = res[0].get("kernel") if res else None
            if not k or "skipped" in k:
                continue
            t = r["name"]
            y = f"/chc/{t}"
            # chc.ts --kernel writes the table's kept relations as a model at /tmp/table-model.json, keyed by the .smt2 path;
            # given-dump.ts then dumps the step goal the prover stops on with that model.
            cmd = (f"{pre}f=$(dirname {y})/$(sed -n 's/^input_files:[[:space:]]*//p' {y} | head -1); mkdir -p /tmp/out; "
                   f"bun research/table/chc.ts \"$f\" --task '{t}' --model /data/spacer-models.jsonl --kernel; "
                   f"[ -f /tmp/table-model.json ] && cp /tmp/table-model.json /tmp/out/model.json && "
                   f"bun research/dag/given-dump.ts \"$f\" /tmp/table-model.json --key \"$f\" --ms 55000 --out /tmp/out")
            jobs.append({"name": safe(t), "limit": 900, "collect": "/tmp/out", "cmd": cmd})
    elif kind == "given332":
        for t in TASKS332:
            jobs.append({"name": safe(t), "limit": 180, "cmd": f"{pre}bun research/step/given332.ts '{t}'"})
    else:
        raise SystemExit(__doc__)
    json.dump(jobs, sys.stdout, indent=0)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2:])
