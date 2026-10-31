"""research/query: where a kernel query's time goes. One job a 2 vCPU, 4 GB slot (a boat item, or a Modal container),
every job at once.

    python3 research/query/modal_query.py --jobs <jobs.json> --out runs/query/<name> [--backend boat|auto|modal]
    modal run research/query/modal_query.py --jobs <jobs.json> --out runs/query/<name>          (Modal, as before)

--backend boat (the default) runs each job as a boat item (supercomputer/fanout.py), auto falls back to Modal when boat
can't take a batch or loses a job, modal is `modal run`'s. jobs.json is a list of {"name", "cmd", "limit"?, "prof"?,
"base"?}: cmd runs under bash in /work/gdp-wired (this tree, copied fresh), or in /work/base (main with research/query's
instrumentation, made outside the tree by `jobs.py base` and mounted; Modal only) with "base": true, killed at `limit`
seconds (default 120) by `timeout -s KILL`. Every bun process it starts loads research/query/log.ts (each root query a
line of <out>/<name>/q.jsonl); with "prof": true each also writes a CPU profile, summarized by top.py
(<out>/<name>/prof-<n>.json). The data: the CHC-COMP'26 LIA-Lin benchmarks at compare/chc's pinned commit (/chc),
TermComp's ITS at compare/term's (/its), research/dag's 332 dumped step goals (/goals, from the main checkout's
runs/modal/dag/goals). On Modal they are in the image; on boat /chc and /its are the image's chc and term layers
(/opt/gdpw/chc/bench, /opt/gdpw/term/bench) and the goals the jobs read go with the batch's tree (packed into
research/query/.goals-<pid>.tar.zst for the run), so a command's /chc/, /its/ and /goals/ paths are read there. <out>/<name>.log has the exit code, seconds, stdout and stderr; <out>/summary.tsv one row
a job. Every call is cancelled when the client exits (supercomputer/reap.sh stops an orphan app or VM lease).
"""
import json
import os
import pathlib
import re
import time

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent.parent
# the pool's code: supercomputer/, or modal/ in a tree from before the rename (the bar runs this runner in old trees too)
SC = next((GDP / d for d in ("supercomputer", "modal") if (GDP / d / "fanout.py").exists()), GDP / "supercomputer")
try:
    import modal
except ImportError:  # plain python3, --backend boat: the job function runs on boat VMs (supercomputer/fanout.py)
    import sys
    sys.path.insert(0, str(SC))
    from agent import modal_stub
    modal = modal_stub()
MAIN = GDP.parent / "gdp-wired"
BENCH_COMMIT = "b4fa7a708e5863bbcdb5de50d692ead3a67cbedc"
ARI_COMMIT = "183f29db5ec7702215c6aabe12732bf3e836fced"
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
# (the main checkout's dumped goals: under runs/supercomputer since the folder's rename, else where they were made, runs/modal)
GOALS = next((g for g in (MAIN / "runs" / d / "dag" / "goals" for d in ("supercomputer", "modal")) if g.exists()), MAIN / "runs" / "supercomputer" / "dag" / "goals")
BASE = pathlib.Path(os.environ.get("GDP_QUERY_BASE", "/tmp/gdp-query-base"))
IGNORE = ["node_modules", "**/*.olean", "**/*.ilean", "**/node_modules/**", "**/runs/**", "runs/**", "supercomputer/**", "modal/**", "modal", "private/**", "vendor/**",
          "compare/**/*.js", "compare/**/out/**", "research/enum/**", "research/perf/bend-enum/**", "research/hw/**", "research/modal-gpu/**",
          "docs/**", "static/**", "**/lean-kernel/.lake/**", "research/extract/.cache/**", "**/.git"]

image = (
    modal.Image.from_registry("ubuntu:24.04", add_python="3.12")
    .apt_install("curl", "unzip", "ca-certificates", "bzip2", "coreutils")
    .run_commands(
        "curl -fsSL https://bun.sh/install | bash",
        f"mkdir /chc && curl -fsSL https://codeload.github.com/chc-comp/chc-comp26-benchmarks/tar.gz/{BENCH_COMMIT} | tar xz -C /chc --strip-components 1",
        f"mkdir /its && curl -fsSL https://codeload.github.com/TermCOMP/TPDB-ARI/tar.gz/{ARI_COMMIT} | tar xz -C /its --strip-components 1 TPDB-ARI-{ARI_COMMIT}/Integer_Transition_Systems",
    )
    .run_commands(f"python3 - <<'EOF'\n{KEEP}\nEOF", "du -sh /chc /its")
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"})
    .add_local_dir(GOALS, "/goals")
    .add_local_dir(GDP, "/src/gdp-wired", ignore=IGNORE)
)
if BASE.exists():
    image = image.add_local_dir(BASE, "/src/base", ignore=IGNORE)
app = modal.App("gdp-wired-query", image=image)

# On boat (a VM of the pool's image): the benchmarks the chc and term layers hold, and the goals the jobs read packed
# into this tree for the batch (a batch's tree is what git sees, as Modal's image carries /goals), each job's unpacked
# into its own /work. A command's /chc/, /its/ and /goals/ paths are read there; nothing else in it changes.
ON_BOAT = {"/chc/": "/opt/gdpw/chc/bench/", "/its/": "/opt/gdpw/term/bench/", "/goals/": "/work/data/goals/"}
PATHS = re.compile(r"(?<![\w./-])/(chc|its|goals)/")
GOAL = re.compile(r"(?<![\w./-])/goals/([^\s'\"]+)")


def pack(jobs: str) -> str:
    """The goal files a jobs file reads, from the main checkout's dump, as research/query/.goals-<pid>.tar.zst in this
    tree (untracked, so the batch's tree has it; removed when the run ends). Its path in the tree, or "" for none."""
    import subprocess
    files = sorted({f"goals/{g}" for j in json.loads(pathlib.Path(jobs).read_text()) for g in GOAL.findall(j["cmd"])})
    if not files:
        return ""
    rel = f"research/query/.goals-{os.getpid()}.tar.zst"
    subprocess.run(f"tar -C {GOALS.parent} -cf - {' '.join(files)} | zstd -q -10 -o {GDP / rel}", shell=True, check=True)
    return rel


@app.function(scaledown_window=2, cpu=2.0, memory=4096, timeout=2400)
def job(name: str, cmd: str, limit: int, prof: bool, base: bool, goals: str = "") -> dict:
    import shutil
    import subprocess

    if not pathlib.Path("/goals").exists():  # a boat VM: the image's benchmarks, this job's goals from the tree's pack
        if goals:
            pathlib.Path("/work/data").mkdir(parents=True, exist_ok=True)
            subprocess.run(["tar", "--zstd", "-xf", f"/src/gdp-wired/{goals}", "-C", "/work/data", *(f"goals/{g}" for g in GOAL.findall(cmd))], check=True)
        cmd = PATHS.sub(lambda m: ON_BOAT[m.group(0)], cmd)
    work = pathlib.Path("/work/gdp-wired")
    if not work.exists():
        shutil.copytree("/src/gdp-wired", work)
    if pathlib.Path("/src/base").exists() and not pathlib.Path("/work/base").exists():
        shutil.copytree("/src/base", "/work/base")
    cwd = pathlib.Path("/work/base") if base else work
    out = pathlib.Path("/tmp/out")
    shutil.rmtree(out, ignore_errors=True)
    (out / "raw").mkdir(parents=True)
    opts = "--preload ./research/query/log.ts" + (f" --cpu-prof --cpu-prof-dir={out / 'raw'}" if prof else "")
    env = {**os.environ, "BUN_OPTIONS": opts, "GDP_QUERY_LOG": str(out / "q.jsonl")}
    t0 = time.time()
    try:
        p = subprocess.run(["timeout", "-s", "KILL", str(limit), "bash", "-c", cmd], cwd=cwd, env=env, capture_output=True, encoding="utf-8", errors="replace", timeout=limit + 30)
        code, so, se = p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired as e:
        code, so, se = 124, "", "killed"
    secs = round(time.time() - t0, 2)
    files = {}
    for i, f in enumerate(sorted((out / "raw").glob("*.cpuprofile"))):
        s = subprocess.run(["python3", str(work / "research/query/top.py"), str(f), "300"], capture_output=True, encoding="utf-8")
        files[f"prof-{i}.json"] = s.stdout or s.stderr
    q = out / "q.jsonl"
    if q.exists():
        files["q.jsonl"] = q.read_text(errors="replace")[-30_000_000:]
    return {"name": name, "code": code, "seconds": secs, "out": so[-2_000_000:], "err": se[-200_000:], "files": files}


@app.local_entrypoint()
def main(jobs: str, out: str):
    import sys
    sys.path.insert(0, str(SC))
    import fanout
    run(fanout.ModalEx(app), jobs, out)


def run(ex, jobs: str, out: str):
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    spec = json.loads(pathlib.Path(jobs).read_text())
    (outdir / "jobs.json").write_text(json.dumps(spec, indent=0))
    t0 = time.time()
    rows = []
    boat = getattr(ex, "backend", "modal") != "modal"
    if boat and any(j.get("base") for j in spec):
        raise SystemExit("jobs on main's instrumented tree (\"base\": true, jobs.py --base) need its mount: --backend modal")
    try:
        goals = os.environ.get("GDP_QUERY_PACK", "") if boat else ""
        args = [(j["name"], j["cmd"], j.get("limit", 120), bool(j.get("prof")), bool(j.get("base")), *([goals] if goals else [])) for j in spec]
        print(f"{len(args)} jobs", flush=True)
        for r in ex.starmap(job, args):
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
        ex.close()
    print(f"{len(rows)} jobs, {sum(r['code'] != 0 for r in rows)} nonzero, {round(time.time() - t0, 1)} s wall", flush=True)


if __name__ == "__main__":
    import sys
    sys.path.insert(0, str(SC))
    import fanout
    if not any(a == "--backend" or a.startswith("--backend=") for a in sys.argv[1:]):
        sys.argv[1:1] = ["--backend", "boat"]  # (boat by default; auto and modal on request)
    # (the goals packed before the batch takes its tree; the same run again under the Modal client's interpreter finds
    # the pack already made)
    backend = sys.argv[sys.argv.index("--backend") + 1] if "--backend" in sys.argv else ""
    if "GDP_QUERY_PACK" not in os.environ and "--jobs" in sys.argv and backend != "modal":
        os.environ["GDP_QUERY_PACK"] = pack(sys.argv[sys.argv.index("--jobs") + 1])
    try:
        fanout.cli(run, __file__, __doc__)
    finally:
        if os.environ.get("GDP_QUERY_PACK"):
            (GDP / os.environ["GDP_QUERY_PACK"]).unlink(missing_ok=True)
