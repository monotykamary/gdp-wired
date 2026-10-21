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
    .add_local_dir(GDP, "/src/gdp-wired", ignore=["vendor/handwired/lab/recovery-*/**", "**/*.olean", "**/*.ilean", "**/*.c", "**/node_modules/**", "**/runs/**", "modal/**", "private/**/bench/**",
                                              # the Handwired fork: its sources and lab/json-search, which research/hw/ and research/enum/ import
                                              "vendor/handwired/lab/ui-exploration/**", "vendor/handwired/lab/knuth-plass/**", "vendor/handwired/assets/**", "vendor/handwired/tests/**", "vendor/gdp-ts/examples/**"])
)
app = modal.App("gdp-wired-experiments", image=image)
# The Lean twin's library, compiled once per version of its sources: a job copies the .olean files in before it runs
# (its `[ -f X.olean ] ||` then skips the compile) and saves the ones it compiled. The key hashes every library source
# and the toolchain, so a job only ever reads files compiled from the sources it was given. A compile whose output a job
# checks (for sorry, say) is written without the skip, so it still runs.
oleans = modal.Volume.from_name("gdp-wired-olean", create_if_missing=True)
LIBRARY = ["Cert", "Kernel", "Progress", "StepLaw", "Steps", "Sets", "History", "Live", "Ghost", "Refine"]


def library_key(lean_dir: pathlib.Path) -> str:
    import hashlib
    h = hashlib.sha256(b"leanprover/lean4:v4.34.0\n")
    for mod in LIBRARY:
        h.update(mod.encode() + b"\0" + (lean_dir / f"{mod}.lean").read_bytes() + b"\0")
    return h.hexdigest()[:32]


@app.function(cpu=2.0, memory=4096, timeout=900, volumes={"/olean": oleans})
def sh(name: str, cmd: str, cwd: str = ".", limit: int = 840) -> dict:
    import shutil
    import subprocess

    work = pathlib.Path("/work/gdp-wired")
    if not work.exists():
        shutil.copytree("/src/gdp-wired", work)
    lean_dir = work / "lean-kernel"
    try:
        oleans.reload()
    except Exception:
        pass
    cache = pathlib.Path("/olean") / library_key(lean_dir)
    had = {f.name for f in cache.glob("*.olean")} if cache.exists() else set()
    for name_ in had:
        shutil.copy2(cache / name_, lean_dir / name_)
    t0 = time.time()
    try:
        p = subprocess.run(["bash", "-c", cmd], cwd=work / cwd, capture_output=True, encoding="utf-8", errors="replace", timeout=limit)
        code, out, err = p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired as e:  # report what it printed rather than lose the container's work
        code, out, err = 124, (e.stdout or b"").decode("utf-8", "replace") if isinstance(e.stdout, bytes) else (e.stdout or ""), f"timed out after {limit} s"
    # Save the library files this job compiled and the cache lacks (each written whole, then renamed into place).
    new = [m for m in LIBRARY if f"{m}.olean" not in had and (lean_dir / f"{m}.olean").exists()]
    if new:
        try:
            cache.mkdir(parents=True, exist_ok=True)
            for m in new:
                tmp = cache / f".{m}.olean.{name}"
                shutil.copy2(lean_dir / f"{m}.olean", tmp)
                tmp.rename(cache / f"{m}.olean")
            oleans.commit()
        except Exception:
            pass
    return {"name": name, "code": code, "seconds": round(time.time() - t0, 2), "out": out[-400_000:], "err": err[-100_000:]}


@app.local_entrypoint()
def main(jobs: str, out: str, native: bool = False, cyclic: bool = False):
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
            # --native: the Lean the jobs generate closes each check by native_decide (emit.ts's toLean `native`).
            # --cyclic: every proof core/cyclic.ts's instances cover is made again as a cyclic proof, a differing verdict
            # failing the job (GDP_CYCLIC=1).
            pre = ("export GDP_LEAN_NATIVE=1; " if native else "") + ("export GDP_CYCLIC=1; " if cyclic else "")
            # (every proof made twice, so a test's own time limit is lifted)
            cmd = lambda c: c.replace("bun test ", "bun test --timeout 600000 ") if cyclic else c
            calls += [(j["name"], fn.spawn(j["name"], pre + cmd(j["cmd"]), j.get("cwd", "."), timeout - 30)) for j in js]
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
