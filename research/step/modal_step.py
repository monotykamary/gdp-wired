"""research/step on Modal: one job a container (2 vCPU, 4 GB), every job at once (research/dag/modal_dag.py's runner).

    modal run research/step/modal_step.py --jobs <jobs.json> --out runs/step/<name>

Modal only: the jobs read research/dag's dumped step goals (runs/modal/dag/goals/, mounted at /goals), the table's
(runs/step/goals223/, at /goals223), any other goals kept for a profile (runs/step/extra/, at /extra), the CHC-COMP'26 LIA-Lin benchmarks at compare/'s pinned commit (/chc) and Spacer's
models of the sat gap tasks (/data/spacer-models.jsonl), none of which supercomputer/run.py's tree carries. jobs.json is a list
of {"name", "cmd", "limit"?, "collect"?}: cmd runs under bash in /work/gdp-wired (this tree, mounted fresh), killed at
`limit` seconds (default 120) by `timeout -s KILL`; `collect`, a directory, has its files returned and written under
<out>/<name>/. <out>/<name>.log has the exit code, seconds, stdout and stderr; <out>/summary.tsv one row a job. The app
id and client pid are registered in supercomputer/.live/ (supercomputer/reap.sh stops an orphan); every call is cancelled when this
entrypoint exits.
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
root = pathlib.Path('/chc')
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
GOALS = GDP / "runs" / "supercomputer" / "dag" / "goals"
GOALS223 = GDP / "runs" / "step" / "goals223"
EXTRA = GDP / "runs" / "step" / "extra"
MODELS = GDP.parent / "gdp-wired" / "runs" / "supercomputer" / "chc2" / "spacer-models-sat" / "models.jsonl"

image = (
    modal.Image.from_registry("ubuntu:24.04", add_python="3.12")
    .apt_install("curl", "unzip", "ca-certificates", "bzip2", "coreutils")
    .run_commands(
        "curl -fsSL https://bun.sh/install | bash",
        "curl -fsSL -o /tmp/z3.zip https://github.com/Z3Prover/z3/releases/download/z3-5.3.1/z3-5.3.1-x64-glibc-2.39.zip"
        " && unzip -q /tmp/z3.zip -d /opt && ln -s /opt/z3-5.3.1-x64-glibc-2.39/bin/z3 /usr/local/bin/z3 && z3 --version",
        f"mkdir /chc && curl -fsSL https://codeload.github.com/chc-comp/chc-comp26-benchmarks/tar.gz/{BENCH_COMMIT} | tar xz -C /chc --strip-components 1",
    )
    .run_commands(f"python3 - <<'EOF'\n{KEEP}\nEOF", "du -sh /chc")
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"})
    .add_local_dir(GDP, "/src/gdp-wired", ignore=["node_modules", "**/*.olean", "**/*.ilean", "**/node_modules/**", "**/runs/**", "runs/**", "supercomputer/**", "private/**",
                                              "vendor/**", "compare/**/*.js", "compare/**/out/**", "research/enum/**", "research/perf/**", "research/hw/**", "research/modal-gpu/**",
                                              "docs/**", "static/**", "lean-kernel/.lake/**"])
)
if MODELS.exists():
    image = image.add_local_file(MODELS, "/data/spacer-models.jsonl")
if GOALS.exists():
    image = image.add_local_dir(GOALS, "/goals")
if GOALS223.exists():
    image = image.add_local_dir(GOALS223, "/goals223")
if EXTRA.exists():
    image = image.add_local_dir(EXTRA, "/extra")
app = modal.App("gdp-wired-step", image=image)


@app.function(scaledown_window=2, cpu=2.0, memory=4096, timeout=1200)
def job(name: str, cmd: str, limit: int, collect: str) -> dict:
    import shutil
    import subprocess

    work = pathlib.Path("/work/gdp-wired")
    if not work.exists():
        shutil.copytree("/src/gdp-wired", work)
    t0 = time.time()
    try:
        p = subprocess.run(["timeout", "-s", "KILL", str(limit), "bash", "-c", cmd], cwd=work, capture_output=True, encoding="utf-8", errors="replace", timeout=limit + 30)
        code, out, err = p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired as e:
        code, out, err = 124, (e.stdout or b"").decode("utf-8", "replace") if isinstance(e.stdout, bytes) else (e.stdout or ""), "killed"
    secs = round(time.time() - t0, 2)
    files = {}
    if collect:
        d = pathlib.Path(collect) if collect.startswith("/") else work / collect
        if d.exists():
            for f in d.rglob("*"):
                if f.is_file() and f.stat().st_size < 40_000_000:
                    files[str(f.relative_to(d))] = f.read_text(errors="replace")
    return {"name": name, "code": code, "seconds": secs, "out": out[-2_000_000:], "err": err[-200_000:], "files": files}


@app.local_entrypoint()
def main(jobs: str, out: str):
    live = GDP / "supercomputer" / ".live"
    live.mkdir(exist_ok=True)
    ticket = live / f"{app.app_id}"
    ticket.write_text(str(os.getpid()))
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    spec = json.loads(pathlib.Path(jobs).read_text())
    (outdir / "jobs.json").write_text(json.dumps(spec, indent=0))
    t0 = time.time()
    rows = []
    try:
        args = [(j["name"], j["cmd"], j.get("limit", 120), j.get("collect", "")) for j in spec]
        print(f"{len(args)} jobs", flush=True)
        for r in job.starmap(args, order_outputs=False, return_exceptions=True):
            if isinstance(r, BaseException):
                r = {"name": f"?{len(rows)}", "code": -1, "seconds": -1, "out": "", "err": repr(r)[:2000], "files": {}}
            safe = r["name"].replace("/", "__")
            (outdir / f"{safe}.log").write_text(f"exit {r['code']} in {r['seconds']} s\n{r['out']}" + ("\n--- stderr ---\n" + r["err"] if r["err"].strip() else ""))
            for rel, text in r["files"].items():
                p = outdir / safe / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(text)
            rows.append(r)
            if len(rows) % 50 == 0:
                print(f"{len(rows)}/{len(args)} done, {round(time.time() - t0)} s", flush=True)
    finally:
        (outdir / "summary.tsv").write_text("".join(f"{r['name']}\t{r['code']}\t{r['seconds']}\n" for r in rows))
        ticket.unlink(missing_ok=True)
    print(f"{len(rows)} jobs, {sum(r['code'] != 0 for r in rows)} nonzero, {round(time.time() - t0, 1)} s wall", flush=True)
