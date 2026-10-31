"""The comparison's checks on Modal: one container per job, bun and Lean 4.34.0 in the image, gdp-wired and the Bend
repo's bend2/ mounted fresh on every run (read-only sources, copied to /work in the container).

    modal run compare/modal_compare.py --jobs compare/jobs.json --out ../runs/modal/compare/<name>

jobs.json is a list of {"name", "cmd", "timeout"?}; cmd runs under bash in /work/gdp-wired, with BEND=/work/bend (the
Bend repo root, holding bend2/) in the environment. Each job's output lands in <out>/<name>.log and <out>/summary.tsv
has name, exit code and seconds. Modeled on supercomputer/run.py: the app id and client pid are registered in supercomputer/.live/
(so supercomputer/reap.sh can stop an orphan), and every spawned call is cancelled when this entrypoint exits.
"""
import json
import os
import pathlib
import time

import modal

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent
BEND = pathlib.Path(os.environ.get("BEND_REPO", GDP.parent / "bend"))

image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install("curl", "unzip", "git", "ca-certificates", "xz-utils", "zstd", "time", "bc")
    .run_commands(
        "curl -fsSL https://bun.sh/install | bash",
        "curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.34.0",
        "/root/.elan/bin/lean --version",
    )
    .env({"PATH": "/root/.bun/bin:/root/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin", "BEND_NO_TELEMETRY": "1"})
    .add_local_dir(GDP, "/src/gdp-wired", ignore=["**/*.olean", "**/*.ilean", "**/node_modules/**", "**/runs/**", "runs/**", "supercomputer/**", "private/**",
                                              "vendor/handwired/lab/ui-exploration/**", "vendor/handwired/lab/knuth-plass/**", "vendor/handwired/assets/**",
                                              "vendor/handwired/tests/**", "vendor/gdp-ts/examples/**", "compare/**/*.js", "compare/**/out/**"])
    .add_local_dir(BEND / "bend2", "/src/bend/bend2", ignore=["**/node_modules/**", "docs/**"])
)
app = modal.App("gdp-wired-compare", image=image)


@app.function(scaledown_window=2, cpu=2.0, memory=4096, timeout=1800)
def sh(name: str, cmd: str, limit: int = 1500) -> dict:
    import shutil
    import subprocess

    work = pathlib.Path("/work")
    if not (work / "gdp-wired").exists():
        shutil.copytree("/src/gdp-wired", work / "gdp-wired")
        shutil.copytree("/src/bend", work / "bend")
    env = {**os.environ, "BEND": str(work / "bend"), "GDP": str(work / "gdp-wired")}
    t0 = time.time()
    try:
        p = subprocess.run(["bash", "-c", cmd], cwd=work / "gdp-wired", capture_output=True, text=True, timeout=limit, env=env)
        code, out, err = p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired as e:
        code, out, err = 124, (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or ""), f"timed out after {limit} s"
    return {"name": name, "code": code, "seconds": round(time.time() - t0, 2), "out": out[-400_000:], "err": err[-100_000:]}


@app.local_entrypoint()
def main(jobs: str, out: str):
    spec = json.loads(pathlib.Path(jobs).read_text())
    live = GDP / "supercomputer" / ".live"
    live.mkdir(exist_ok=True)
    ticket = live / f"{app.app_id}"
    ticket.write_text(str(os.getpid()))
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    calls = []
    try:
        for j in spec:
            timeout = j.get("timeout", 1500)
            fn = sh.with_options(timeout=timeout + 120)
            calls.append((j["name"], fn.spawn(j["name"], j["cmd"], timeout)))
        rows = []
        for name, c in calls:
            try:
                r = c.get()
            except Exception as e:
                r = {"name": name, "code": -1, "seconds": -1, "out": "", "err": repr(e)}
            (outdir / f"{r['name']}.log").write_text(r["out"] + ("\n--- stderr ---\n" + r["err"] if r["err"].strip() else ""))
            rows.append(r)
            print(f"{r['name']:40} exit {r['code']:>3}  {r['seconds']:>8} s", flush=True)
        (outdir / "summary.tsv").write_text("".join(f"{r['name']}\t{r['code']}\t{r['seconds']}\n" for r in rows))
    finally:
        for _, c in calls:
            try:
                c.cancel()
            except Exception:
                pass
        ticket.unlink(missing_ok=True)
    print(f"{len(rows)} jobs, {sum(r['code'] != 0 for r in rows)} failed, {round(time.time() - t0, 1)} s wall")
