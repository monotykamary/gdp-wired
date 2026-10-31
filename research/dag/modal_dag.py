"""research/dag on Modal: one job per container, every job at once (modelled on compare/chc/modal_chc.py).

    modal run research/dag/modal_dag.py --jobs <jobs.json> --out runs/modal/dag/<name>

jobs.json is a list of {"name", "cmd", "limit"?, "collect"?}: cmd runs under bash in /work/gdp-wired (gdp-wired as it is
here, mounted fresh), killed at `limit` seconds (default 120); `collect`, a directory, has its files returned and
written under <out>/<name>/. The image is modal_chc.py's (Ubuntu 24.04, bun, Z3 5.3.1, the CHC-COMP'26 benchmarks at the
same pinned commit under /bench) plus cvc5 1.4.1; runs/modal/dag/goals/ (the step goals given-dump.ts wrote) is mounted
at /goals. Each container has 2 vCPU and 4 GB. <out>/<name>.log has the job's exit code, seconds, stdout and stderr;
<out>/summary.tsv one row per job. The app id and client pid are registered in supercomputer/.live/ (supercomputer/reap.sh stops an
orphan); every call is cancelled when this entrypoint exits.
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
GOALS = GDP / "runs" / "supercomputer" / "dag" / "goals"

image = (
    modal.Image.from_registry("ubuntu:24.04", add_python="3.12")
    .apt_install("curl", "unzip", "ca-certificates", "bzip2", "coreutils")
    .run_commands(
        "curl -fsSL https://bun.sh/install | bash",
        "curl -fsSL -o /tmp/z3.zip https://github.com/Z3Prover/z3/releases/download/z3-5.3.1/z3-5.3.1-x64-glibc-2.39.zip"
        " && unzip -q /tmp/z3.zip -d /opt && ln -s /opt/z3-5.3.1-x64-glibc-2.39/bin/z3 /usr/local/bin/z3 && z3 --version",
        "curl -fsSL https://github.com/usi-verification-and-security/golem/releases/download/v0.9.0/golem-x64-linux.tar.bz2"
        " | tar xj -C /opt && find /opt -name golem -type f -exec ln -s {} /usr/local/bin/golem \\; && golem --version",
        f"mkdir /bench && curl -fsSL https://codeload.github.com/chc-comp/chc-comp26-benchmarks/tar.gz/{BENCH_COMMIT} | tar xz -C /bench --strip-components 1",
    )
    .run_commands(f"python3 - <<'EOF'\n{KEEP}\nEOF", "du -sh /bench")
    .run_commands(
        "curl -fsSL -o /tmp/cvc5.zip https://github.com/cvc5/cvc5/releases/download/cvc5-1.4.1/cvc5-Linux-x86_64-static.zip"
        " && unzip -q /tmp/cvc5.zip -d /opt/cvc5 && find /opt/cvc5 -name cvc5 -type f -exec ln -s {} /usr/local/bin/cvc5 \\; && cvc5 --version | head -1",
    )
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"})
    .add_local_dir(GDP, "/src/gdp-wired", ignore=["node_modules", "**/*.olean", "**/*.ilean", "**/node_modules/**", "**/runs/**", "runs/**", "supercomputer/**", "modal/**", "modal", "private/**",
                                              "vendor/**", "compare/**/*.js", "compare/**/out/**", "research/enum/**", "research/perf/**", "research/hw/**", "research/modal-gpu/**"])
)
if GOALS.exists():
    image = image.add_local_dir(GOALS, "/goals")
app = modal.App("gdp-wired-dag", image=image)


@app.function(scaledown_window=2, cpu=2.0, memory=4096, timeout=3600)
def job(name: str, cmd: str, limit: int, collect: str) -> dict:
    import shutil
    import subprocess

    work = pathlib.Path("/work/gdp-wired")
    if not work.exists():
        shutil.copytree("/src/gdp-wired", work)
    t0 = time.time()
    try:
        p = subprocess.run(["timeout", "-k", "5", str(limit), "bash", "-c", cmd], cwd=work, capture_output=True, encoding="utf-8", errors="replace", timeout=limit + 30)
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
            if len(rows) % 25 == 0:
                print(f"{len(rows)}/{len(args)} done, {round(time.time() - t0)} s", flush=True)
    finally:
        (outdir / "summary.tsv").write_text("".join(f"{r['name']}\t{r['code']}\t{r['seconds']}\n" for r in rows))
        ticket.unlink(missing_ok=True)
    print(f"{len(rows)} jobs, {sum(r['code'] != 0 for r in rows)} nonzero, {round(time.time() - t0, 1)} s wall", flush=True)
