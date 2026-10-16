"""Fan experiment jobs out on Modal: one container per job, bun and Lean 4.34.0 in the image, gdp-wired mounted fresh
on every run (so edits need no rebuild).

    modal run modal/run.py --jobs jobs.json --out ../runs/modal/<name>

jobs.json is a list of {"name", "cmd", "cwd"?, "cpu"?, "memory"?, "timeout"?}; cmd runs under bash in gdp-wired/<cwd>.
Each job's output lands in <out>/<name>.log, and <out>/summary.tsv has name, exit code and seconds.

Cost hygiene: the default timeout is 15 minutes (set "timeout" per job for longer ones); a job's command is also killed
at that timeout inside the container, so it still returns its output; and if this entrypoint stops for any reason
(Ctrl-C, a kill, an error), every call it spawned is cancelled. Each run registers its app id and client pid in
modal/.live/; `modal/reap.sh` stops only apps whose client is gone, so it is safe while other runs are live.
"""
import json
import pathlib
import time

import modal

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent

image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install("curl", "unzip", "git", "ca-certificates", "xz-utils", "zstd")
    .run_commands(
        "curl -fsSL https://bun.sh/install | bash",
        "curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.34.0",
        "/root/.elan/bin/lean --version",
    )
    .env({"PATH": "/root/.bun/bin:/root/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"})
    .add_local_dir(GDP, "/src/gdp-wired", ignore=["**/*.olean", "**/*.ilean", "**/*.c", "**/node_modules/**", "**/runs/**", "modal/**", "private/**/bench/**",
                                              # the Handwired fork: its sources and lab/json-search, which hw/ and enum/ import
                                              "vendor/handwired/lab/ui-exploration/**", "vendor/handwired/lab/knuth-plass/**", "vendor/handwired/assets/**", "vendor/handwired/tests/**", "vendor/gdp-ts/examples/**"])
)
app = modal.App("gdp-wired-experiments", image=image)


@app.function(cpu=2.0, memory=4096, timeout=900)
def sh(name: str, cmd: str, cwd: str = ".", limit: int = 840) -> dict:
    import shutil
    import subprocess

    work = pathlib.Path("/work/gdp-wired")
    if not work.exists():
        shutil.copytree("/src/gdp-wired", work)
    t0 = time.time()
    try:
        p = subprocess.run(["bash", "-c", cmd], cwd=work / cwd, capture_output=True, text=True, timeout=limit)
        code, out, err = p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired as e:  # report what it printed rather than lose the container's work
        code, out, err = 124, (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or ""), f"timed out after {limit} s"
    return {"name": name, "code": code, "seconds": round(time.time() - t0, 2), "out": out[-400_000:], "err": err[-100_000:]}


@app.local_entrypoint()
def main(jobs: str, out: str):
    import os

    spec = json.loads(pathlib.Path(jobs).read_text())
    live = HERE / ".live"
    live.mkdir(exist_ok=True)
    ticket = live / f"{app.app_id}"
    ticket.write_text(str(os.getpid()))
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    # Jobs with the same resources share one function variant; every variant runs its jobs in parallel.
    groups: dict[tuple, list] = {}
    for j in spec:
        groups.setdefault((j.get("cpu", 2.0), j.get("memory", 4096), j.get("timeout", 900)), []).append(j)
    calls = []
    try:
        for (cpu, memory, timeout), js in groups.items():
            fn = sh.with_options(cpu=cpu, memory=memory, timeout=timeout + 60)
            calls += [(j["name"], fn.spawn(j["name"], j["cmd"], j.get("cwd", "."), timeout - 30)) for j in js]
        rows = collect(calls, outdir)
    finally:  # whatever happened, nothing keeps running (cancelling a finished call is a no-op)
        for _, c in calls:
            try:
                c.cancel()
            except Exception:
                pass
        ticket.unlink(missing_ok=True)
    print(f"{len(rows)} jobs, {sum(r['code'] != 0 for r in rows)} failed, {round(time.time() - t0, 1)} s wall, {round(sum(max(r['seconds'], 0) for r in rows), 1)} s of job time")


def collect(calls, outdir):
    rows = []
    for name, c in calls:
        try:
            r = c.get()
        except Exception as e:  # a container that timed out or died still gets a row
            r = {"name": name, "code": -1, "seconds": -1, "out": "", "err": repr(e)}
        (outdir / f"{r['name']}.log").write_text(r["out"] + ("\n--- stderr ---\n" + r["err"] if r["err"].strip() else ""))
        rows.append(r)
        print(f"{r['name']:40} exit {r['code']:>3}  {r['seconds']:>8} s", flush=True)
    (outdir / "summary.tsv").write_text("".join(f"{r['name']}\t{r['code']}\t{r['seconds']}\n" for r in rows))
    return rows
