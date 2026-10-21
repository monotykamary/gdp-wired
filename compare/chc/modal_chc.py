"""CHC-COMP 2026's LIA-Lin track on Modal: gdp-wired (solve.ts) beside Z3's Spacer, Golem and Eldarica, each task in the
same container size under the same wall-clock limit, one tool and a shard of tasks per container.

    modal run compare/chc/modal_chc.py --out runs/modal/chc/<name> [--tools gdp,z3,golem,eldarica] [--limit 60]
                                       [--per 1] [--sample 0] [--only <substring>|<substring>]
                                       [--env NAME=value,...] (set for each task's process)

The benchmarks are chc-comp/chc-comp26-benchmarks at a pinned commit, fetched into the image; the track's task list is
its LIA-Lin.set, each task's expected verdict its .yml's. <out>/results.jsonl has one row per tool and task: the
answer, the seconds and, for gdp-wired, the stages it printed. The app id and client pid are registered in
modal/.live/ (modal/reap.sh stops an orphan); the app, and every call in it, stops when this entrypoint exits.
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
import pathlib, re, shutil
root = pathlib.Path('/bench')
keep = set()
for y in (root / 'LIA-Lin.set').read_text().split():
    y = root / y
    keep.add(y)
    m = re.search(r'^input_files:\s*(\S+)', y.read_text(), re.M)
    keep.add(y.parent / m.group(1))
for p in sorted(root.rglob('*'), reverse=True):
    if p.is_file() and p not in keep and p.name != 'LIA-Lin.set':
        p.unlink()
    elif p.is_dir() and not any(p.iterdir()):
        p.rmdir()
"""

image = (
    modal.Image.from_registry("ubuntu:24.04", add_python="3.12")
    .apt_install("curl", "unzip", "ca-certificates", "bzip2", "coreutils")
    .run_commands(
        "curl -fsSL https://bun.sh/install | bash",
        "curl -fsSL -o /tmp/z3.zip https://github.com/Z3Prover/z3/releases/download/z3-5.3.1/z3-5.3.1-x64-glibc-2.39.zip"
        " && unzip -q /tmp/z3.zip -d /opt && ln -s /opt/z3-5.3.1-x64-glibc-2.39/bin/z3 /usr/local/bin/z3 && z3 --version",
        "curl -fsSL https://github.com/usi-verification-and-security/golem/releases/download/v0.9.0/golem-x64-linux.tar.bz2"
        " | tar xj -C /opt && find /opt -name golem -type f -exec ln -s {} /usr/local/bin/golem \\; && golem --version",
        "curl -fsSL https://github.com/uuverifiers/eldarica/releases/download/v2.3/eldarica-x86-linux-static.gz | gunzip > /usr/local/bin/eld"
        " && chmod +x /usr/local/bin/eld && eld -h | head -3",
        f"mkdir /bench && curl -fsSL https://codeload.github.com/chc-comp/chc-comp26-benchmarks/tar.gz/{BENCH_COMMIT} | tar xz -C /bench --strip-components 1",
    )
    .run_commands(f"python3 - <<'EOF'\n{KEEP}\nEOF", "du -sh /bench")
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"})
    .add_local_dir(GDP, "/src/gdp-wired", ignore=["node_modules", "**/*.olean", "**/*.ilean", "**/node_modules/**", "**/runs/**", "runs/**", "modal/**", "private/**",
                                              "vendor/**", "compare/**/*.js", "compare/**/out/**"])
)
app = modal.App("gdp-wired-chc", image=image)


def command(tool: str, task: str, limit: int) -> list[str]:
    if tool == "gdp":
        # The search's deadline 2 s before the limit (the prover keeps it: kernel/prove.ts's withDeadline).
        return ["bun", "compare/chc/solve.ts", task, "--runs-ms", str(min(5000, limit * 100)), "--houdini-ms", str(max(1000, (limit - 2) * 1000))]
    if tool == "z3":
        return ["z3", "fp.engine=spacer", task]
    if tool == "golem":
        return ["golem", task]
    if tool == "eldarica":
        return ["eld", task]
    raise ValueError(tool)


@app.function(cpu=2.0, memory=4096, timeout=3600)
def shard(tool: str, tasks: list[dict], limit: int, env: str = "") -> list[dict]:
    import shutil
    import subprocess

    work = pathlib.Path("/work/gdp-wired")
    if not work.exists():
        shutil.copytree("/src/gdp-wired", work)
    rows = []
    for t in tasks:
        path = f"/bench/{t['smt2']}"
        t0 = time.time()
        try:
            extra = dict(kv.split("=", 1) for kv in env.split(",") if kv)
            p = subprocess.run(["timeout", "-k", "5", str(limit), *command(tool, path, limit)], cwd=work, capture_output=True, text=True, timeout=limit + 30, env={**os.environ, **extra})
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
            last = stages[-1] if stages else {}
            answer = last.get("answer", "timeout" if code == 124 else "error")
            for s in stages:
                s.pop("task", None)
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


@app.function(timeout=600)
def tasks() -> list[dict]:
    import re

    root = pathlib.Path("/bench")
    out = []
    for y in (root / "LIA-Lin.set").read_text().split():
        text = (root / y).read_text()
        smt2 = str((pathlib.Path(y).parent / re.search(r"^input_files:\s*(\S+)", text, re.M).group(1)))
        exp = re.search(r"expected_verdict:\s*(\S+)", text).group(1)
        mv = re.search(r"majority_vote_verdict:\s*(\S+)", text)
        out.append({"task": y.removeprefix("./"), "smt2": smt2.removeprefix("./"), "expected": {"true": "sat", "false": "unsat"}[exp], "vote": mv.group(1) if mv else None})
    return out


@app.local_entrypoint()
def main(out: str, tools: str = "gdp,z3,golem,eldarica", limit: int = 60, per: int = 1, sample: int = 0, only: str = "", env: str = ""):
    live = GDP / "modal" / ".live"
    live.mkdir(exist_ok=True)
    ticket = live / f"{app.app_id}"
    ticket.write_text(str(os.getpid()))
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    try:
        all_tasks = tasks.remote()
        (outdir / "tasks.json").write_text(json.dumps(all_tasks, indent=1))
        chosen = [t for t in all_tasks if any(o in t["task"] for o in only.split("|"))]
        if sample:
            step = max(1, len(chosen) // sample)
            chosen = chosen[::step][:sample]
        shards = [(tool, chosen[i:i + per], limit, env) for tool in tools.split(",") for i in range(0, len(chosen), per)]
        print(f"{len(chosen)} tasks, {len(shards)} shards", flush=True)
        n = 0
        # starmap sends the inputs in batches and yields each shard's rows as it finishes, every container at once.
        with (outdir / "results.jsonl").open("w") as f:
            for rows in shard.starmap(shards, order_outputs=False, return_exceptions=True):
                if isinstance(rows, BaseException):
                    rows = [{"tool": "?", "task": "?", "answer": "error", "err": repr(rows)[:400]}]
                for r in rows:
                    f.write(json.dumps(r) + "\n")
                n += 1
                if n % 100 == 0:
                    print(f"{n}/{len(shards)} shards, {round(time.time() - t0)} s", flush=True)
    finally:
        ticket.unlink(missing_ok=True)
    print(f"done in {round(time.time() - t0, 1)} s wall")
