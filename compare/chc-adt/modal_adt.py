"""CHC-COMP 2026's ADT-LIA track on Modal: gdp-wired (compare/chc-adt/solve.ts) beside Z3's Spacer and Eldarica, each
task in its own container (2 vCPU, 4 GB) under the same wall-clock limit, as compare/chc/modal_chc.py runs LIA-Lin.
Golem reads no datatypes, so it isn't here.

    modal run compare/chc-adt/modal_adt.py --out runs/adt/<name> [--tools gdp,z3,eldarica] [--limit 60]
                                           [--tasks pilot|all] [--only <substring>|<substring>] [--env NAME=value,...]

The benchmarks are chc-comp/chc-comp26-benchmarks at modal_chc.py's pinned commit, the ADT-LIA.set tasks kept;
`--tasks pilot` (the default) is compare/chc-adt/pilot.json's 48. <out>/results.jsonl has one row per tool and task:
the answer, the seconds, the expected verdict and, for gdp-wired, the stages it printed. The app, and every call in it,
stops when this entrypoint exits.
"""
import json
import os
import pathlib
import time

import modal

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent.parent
BENCH_COMMIT = "b4fa7a708e5863bbcdb5de50d692ead3a67cbedc"
KEEP = r"""
import pathlib, re
root = pathlib.Path('/bench')
keep = set()
for y in (root / 'ADT-LIA.set').read_text().split():
    y = root / y
    keep.add(y)
    keep.add(y.parent / re.search(r'^input_files:\s*(\S+)', y.read_text(), re.M).group(1))
for p in sorted(root.rglob('*'), reverse=True):
    if p.is_file() and p not in keep and p.name != 'ADT-LIA.set':
        p.unlink()
    elif p.is_dir() and not any(p.iterdir()):
        p.rmdir()
"""

image = (
    modal.Image.from_registry("ubuntu:24.04", add_python="3.12")
    .apt_install("curl", "unzip", "ca-certificates", "coreutils")
    .run_commands(
        "curl -fsSL https://bun.sh/install | bash",
        "curl -fsSL -o /tmp/z3.zip https://github.com/Z3Prover/z3/releases/download/z3-5.3.1/z3-5.3.1-x64-glibc-2.39.zip"
        " && unzip -q /tmp/z3.zip -d /opt && ln -s /opt/z3-5.3.1-x64-glibc-2.39/bin/z3 /usr/local/bin/z3 && z3 --version",
        "curl -fsSL https://github.com/uuverifiers/eldarica/releases/download/v2.3/eldarica-x86-linux-static.gz | gunzip > /usr/local/bin/eld"
        " && chmod +x /usr/local/bin/eld && eld -h | head -3",
        f"mkdir /bench && curl -fsSL https://codeload.github.com/chc-comp/chc-comp26-benchmarks/tar.gz/{BENCH_COMMIT} | tar xz -C /bench --strip-components 1",
    )
    .run_commands(f"python3 - <<'EOF'\n{KEEP}\nEOF", "du -sh /bench")
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"})
    .add_local_dir(GDP, "/src/gdp-wired", ignore=["node_modules", "**/*.olean", "**/*.ilean", "**/node_modules/**", "**/runs/**", "runs/**", "supercomputer/**", "private/**",
                                              "vendor/**", "compare/**/*.js", "compare/**/out/**", "lean-kernel/**", "research/**"])
)
app = modal.App("gdp-wired-chc-adt", image=image)


def command(tool: str, task: str, limit: int) -> list[str]:
    if tool == "gdp":
        # the search's budget 3 s before the limit (solve.ts checks it between laws; proveData keeps each law's)
        return ["bun", "compare/chc-adt/solve.ts", task, "--ms", str(max(1000, (limit - 3) * 1000))]
    if tool == "z3":
        return ["z3", "fp.engine=spacer", task]
    if tool == "eldarica":
        return ["eld", task]
    raise ValueError(tool)


@app.function(scaledown_window=2, cpu=2.0, memory=4096, timeout=900)
def shard(tool: str, tasks: list[dict], limit: int, env: str = "") -> list[dict]:
    import shutil
    import subprocess

    work = pathlib.Path("/work/gdp-wired")
    if not work.exists():
        shutil.copytree("/src/gdp-wired", work)
    rows = []
    for t in tasks:
        t0 = time.time()
        try:
            extra = dict(kv.split("=", 1) for kv in env.split(",") if kv)
            p = subprocess.run(["timeout", "-k", "5", str(limit), *command(tool, f"/bench/{t['smt2']}", limit)], cwd=work, capture_output=True, text=True, timeout=limit + 30, env={**os.environ, **extra})
            code, out, err = p.returncode, p.stdout, p.stderr
        except subprocess.TimeoutExpired:
            code, out, err = 124, "", "killed"
        secs = round(time.time() - t0, 2)
        lines = [l for l in out.splitlines() if l.strip()]
        if tool == "gdp":
            stages = []
            for l in lines:
                try:
                    stages.append(json.loads(l))
                except json.JSONDecodeError:
                    pass
            answer = (stages[-1] if stages else {}).get("answer", "timeout" if code == 124 else "error")
            row = {"tool": tool, "task": t["task"], "answer": answer, "seconds": secs, "stages": stages}
        else:
            word = next((l.strip() for l in lines if l.strip() in ("sat", "unsat", "unknown")), None)
            answer = word or ("timeout" if code == 124 else "error")
            row = {"tool": tool, "task": t["task"], "answer": answer, "seconds": secs}
        if answer == "error":
            row["err"] = (err or out)[-600:]
        row["expected"] = t["expected"]
        rows.append(row)
    return rows


@app.function(scaledown_window=2, timeout=600)
def all_tasks() -> list[dict]:
    import re

    root = pathlib.Path("/bench")
    out = []
    for y in (root / "ADT-LIA.set").read_text().split():
        text = (root / y).read_text()
        smt2 = str(pathlib.Path(y).parent / re.search(r"^input_files:\s*(\S+)", text, re.M).group(1))
        exp = re.search(r"expected_verdict:\s*(\S+)", text).group(1)
        mv = re.search(r"majority_vote_verdict:\s*(\S+)", text)
        out.append({"task": y.removeprefix("./"), "smt2": smt2.removeprefix("./"), "expected": {"true": "sat", "false": "unsat"}[exp], "vote": mv.group(1) if mv else None})
    return out


@app.local_entrypoint()
def main(out: str, tools: str = "gdp,z3,eldarica", limit: int = 60, tasks: str = "pilot", only: str = "", env: str = ""):
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    chosen = json.loads((HERE / "pilot.json").read_text())["tasks"] if tasks == "pilot" else all_tasks.remote()
    chosen = [t for t in chosen if any(o in t["task"] for o in only.split("|"))]
    (outdir / "tasks.json").write_text(json.dumps(chosen, indent=1))
    shards = [(tool, [t], limit, env) for tool in tools.split(",") for t in chosen]
    print(f"{len(chosen)} tasks, {len(shards)} shards", flush=True)
    with (outdir / "results.jsonl").open("w") as f:
        for rows in shard.starmap(shards, return_exceptions=True):
            if isinstance(rows, BaseException):
                rows = [{"tool": "?", "task": "?", "answer": "error", "err": repr(rows)[:400]}]
            for r in rows:
                f.write(json.dumps(r) + "\n")
    print(f"done in {round(time.time() - t0, 1)} s wall")
