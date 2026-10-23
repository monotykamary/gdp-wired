"""Fan experiment jobs out on Modal: one container per job, bun and Lean 4.34.0 in the image, gdp-wired mounted fresh
on every run (so edits need no rebuild).

    modal run modal/run.py --jobs jobs.json --out ../runs/modal/<name>
    python3 modal/run.py --backend auto|boat|modal --jobs jobs.json --out runs/backends/<name> [--vms N] [--idle 60]

`--backend auto` runs the same jobs, with the same flags and outputs, on boat.dev VMs (modal/boat.py: a pool kept
stopped between batches, 2 vCPU and 4 GB a slot) and moves to Modal what boat can't serve (modal/fanout.py); summary.tsv
gets a 4th column, the backend each job ran on, and the final line says where they ran, why any moved and what the VMs
cost. `auto` is the default from `python3`; `--backend boat` forces boat; `modal` (and `modal run`) is Modal as before.

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

try:
    import modal
except ImportError:  # plain python3: --backend boat needs no Modal client
    import sys
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
    from agent import modal_stub
    modal = modal_stub()

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
LIBRARY = ["Cert", "Kernel", "Cyclic", "Progress", "StepLaw", "Steps", "Sets", "History", "Live", "Ghost", "Refine", "Bridge", "BridgeRules", "Data"]


def library_key(lean_dir: pathlib.Path) -> str:
    import hashlib
    h = hashlib.sha256(b"leanprover/lean4:v4.34.0\n")
    for mod in LIBRARY:
        h.update(mod.encode() + b"\0" + (lean_dir / f"{mod}.lean").read_bytes() + b"\0")
    return h.hexdigest()[:32]


@app.function(scaledown_window=2, cpu=2.0, memory=4096, timeout=900, volumes={"/olean": oleans})
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


def flags(native: bool, cyclic: bool, usual: bool):
    """What each job's command gets for the flags: exports before it, and the change to its command."""
    # --native: the Lean the jobs generate closes each check by native_decide (emit.ts's toLean `native`).
    # --cyclic: every proof core/cyclic.ts's instances cover is made again as a cyclic proof, a differing verdict
    # failing the job (GDP_CYCLIC=1).
    # --usual: each proof's certificate is the usual trees, and the Lean export reads those, not the cyclic proofs
    # (GDP_CERT=usual: core/cyclic.ts's certOn, lean-kernel/emit.ts's cyclicCerts).
    pre = "export GDP_CYCLIC_LOG=1; " + ("export GDP_LEAN_NATIVE=1; " if native else "") + ("export GDP_CYCLIC=1; " if cyclic else "") + ("export GDP_CERT=usual; " if usual else "")
    # (every proof made twice, so a test's own time limit is lifted)
    cmd = lambda c: c.replace("bun test ", "bun test --timeout 600000 ") if cyclic else c
    return pre, cmd


@app.local_entrypoint()
def main(jobs: str, out: str, native: bool = False, cyclic: bool = False, usual: bool = False, backend: str = "modal",
         vms: int = 0, idle: int = -1, teardown: bool = False, vm_type: str = "default", durations: str = "", max_vms: int = 0, max_wait: int = 120):
    import sys
    sys.path.insert(0, str(HERE))
    import fanout
    spec = json.loads(pathlib.Path(jobs).read_text())
    pre, cmd = flags(native, cyclic, usual)
    fanout.run_jobs(app, spec, out, pre, cmd, lambda js, on_done: modal_jobs(js, pre, cmd, on_done), backend=backend, vms=vms, idle=None if idle < 0 else idle, teardown=teardown,
                    durations=durations, vm_type=vm_type, max_vms=max_vms, max_wait=max_wait)


def modal_jobs(spec: list[dict], pre: str, cmd, on_done) -> dict:
    """The jobs on Modal, inside the running app: {name: {code, seconds, out, err}}."""
    # Jobs with the same resources share one function variant; every variant runs its jobs in parallel.
    groups: dict[tuple, list] = {}
    for j in spec:
        groups.setdefault((j.get("cpu", 2.0), j.get("memory", 4096), j.get("timeout", 900)), []).append(j)
    calls = []
    rows = {}
    try:
        for (cpu, memory, timeout), js in groups.items():
            fn = sh.with_options(cpu=cpu, memory=memory, timeout=timeout + 60)
            calls += [(j["name"], fn.spawn(j["name"], pre + cmd(j["cmd"]), j.get("cwd", "."), timeout - 30)) for j in js]
        for name, c in calls:
            try:
                r = c.get()
            except Exception as e:  # a container that timed out or died still gets a row
                r = {"name": name, "code": -1, "seconds": -1, "out": "", "err": repr(e)}
            rows[name] = r
            on_done(name, r)
    finally:  # whatever happened, nothing keeps running (cancelling a finished call is a no-op)
        for _, c in calls:
            try:
                c.cancel()
            except Exception:
                pass
    return rows


if __name__ == "__main__":
    import argparse
    import sys
    sys.path.insert(0, str(HERE))
    import fanout
    fanout.reexec_with_modal()
    ap = argparse.ArgumentParser(description="modal/run.py's jobs on a backend: auto (the default: boat, Modal when boat can't), boat, modal")
    ap.add_argument("--jobs", required=True)
    ap.add_argument("--out", required=True)
    for f in ("native", "cyclic", "usual", "teardown"):
        ap.add_argument(f"--{f}", action="store_true")
    ap.add_argument("--backend", default="auto", choices=["modal", "auto", "boat"])
    ap.add_argument("--vms", type=int, default=0, help="boat VMs for the batch (default: by the jobs' last times and the plan's limits)")
    ap.add_argument("--max-vms", type=int, default=0, help="at most this many VMs, and the batch's cap on its starts (default 50: GDPW_BOAT_MAX_STARTS)")
    ap.add_argument("--idle", type=int, default=-1, help="seconds a released VM stays up before boat stops it (0: stop at once; default 60)")
    ap.add_argument("--vm-type", default="default", choices=["small", "default", "large"])
    ap.add_argument("--durations", default="", help="a summary.tsv whose times order the jobs (default: the last run's)")
    ap.add_argument("--max-wait", type=int, default=120, help="auto: seconds to wait for a boat VM before Modal takes the batch")
    a = ap.parse_args()
    main(a.jobs, a.out, a.native, a.cyclic, a.usual, a.backend, a.vms, a.idle, a.teardown, a.vm_type, a.durations, a.max_vms, a.max_wait)
