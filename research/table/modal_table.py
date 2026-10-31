"""The observation-table experiment on Modal: one container (2 vCPU, 4 GB) per job, every job at once (`starmap`).

    modal run research/table/modal_table.py --jobs research/table/jobs/<name>.json --out runs/modal/table/<name>

jobs.json is a list of {"name", "cmd", "timeout"?}; cmd runs under bash in gdp-wired/. The image has bun, Z3 5.3.1 (the
oracle the drivers check with), KoAT2 2.7.0 (its proofs, for the termination comparison), pycparser (c2ari.py), and the
benchmarks at the commits compare/ pins: CHC-COMP 2026 (/chc, the LIA-Lin tasks), TIP 2015 (/tip), TPDB-ARI's
integer transition systems (/ari), sv-benchmarks' termination directories (/sv). Spacer's models of the 536 sat gap
tasks are at /data/spacer-models.jsonl. <out>/results.jsonl: one row per job (name, exit code, seconds, stdout). The
app id and client pid are registered in supercomputer/.live/ (supercomputer/reap.sh stops an orphan)."""
import json
import os
import pathlib
import time

import modal

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent.parent
CHC_COMMIT = "b4fa7a708e5863bbcdb5de50d692ead3a67cbedc"
TIP_COMMIT = "bace5b2f0e45d526ec82ce5de6b25fe024984161"
ARI_COMMIT = "183f29db5ec7702215c6aabe12732bf3e836fced"
SV_COMMIT = "c5cc603f325550a65b94a7d9dbfcf7896ad28b91"
SV_DIRS = ["termination-crafted", "termination-crafted-lit", "termination-numeric", "termination-restricted-15", "termination-nla", "properties"]
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
image = (
    modal.Image.from_registry("ubuntu:24.04", add_python="3.12")
    .apt_install("curl", "unzip", "ca-certificates", "bzip2", "zstd", "coreutils")
    .pip_install("pycparser==3.0")
    .run_commands(
        "curl -fsSL https://bun.sh/install | bash",
        "curl -fsSL -o /tmp/z3.zip https://github.com/Z3Prover/z3/releases/download/z3-5.3.1/z3-5.3.1-x64-glibc-2.39.zip"
        " && unzip -q /tmp/z3.zip -d /opt && ln -s /opt/z3-5.3.1-x64-glibc-2.39/bin/z3 /usr/local/bin/z3 && z3 --version",
        "curl -fsSL https://github.com/aprove-developers/KoAT2-Releases/releases/download/v2.7.0/koat2_static.zst | zstd -d > /usr/local/bin/koat2 && chmod +x /usr/local/bin/koat2",
        f"mkdir /chc && curl -fsSL https://codeload.github.com/chc-comp/chc-comp26-benchmarks/tar.gz/{CHC_COMMIT} | tar xz -C /chc --strip-components 1",
    )
    .run_commands(f"python3 - <<'EOF'\n{KEEP}\nEOF", "du -sh /chc")
    .run_commands(
        f"mkdir /tip && curl -fsSL https://codeload.github.com/tip-org/benchmarks/tar.gz/{TIP_COMMIT} | tar xz -C /tip --strip-components 1",
        f"mkdir /ari && curl -fsSL https://codeload.github.com/TermCOMP/TPDB-ARI/tar.gz/{ARI_COMMIT} | tar xz -C /ari --strip-components 1 TPDB-ARI-{ARI_COMMIT}/Integer_Transition_Systems",
        "mkdir -p /sv && cd /sv && for d in " + " ".join(SV_DIRS) + f"; do curl -fsSL 'https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks/-/archive/{SV_COMMIT}/sv-benchmarks-{SV_COMMIT}.tar.gz?path=c/'$d | tar xz --strip-components 1; done && ls /sv/c",
    )
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"})
    .add_local_file(GDP / "runs/modal/chc2/spacer-models-sat/models.jsonl", "/data/spacer-models.jsonl")
    .add_local_dir(GDP, "/src/gdp-wired", ignore=["node_modules", "**/*.olean", "**/*.ilean", "**/node_modules/**", "**/runs/**", "runs/**", "supercomputer/**", "private/**",
                                              "vendor/gdp-ts/**", "vendor/handwired/lab/**", "vendor/handwired/assets/**", "vendor/handwired/tests/**", "vendor/handwired/docs/**", "compare/**/*.js", "compare/**/out/**", "docs/**", "static/**", "lean-kernel/.lake/**"])
)
app = modal.App("gdp-wired-table", image=image)


@app.function(scaledown_window=2, cpu=2.0, memory=4096, timeout=1800)
def job(name: str, cmd: str, limit: int) -> dict:
    import shutil
    import subprocess

    work = pathlib.Path("/work/gdp-wired")
    if not work.exists():
        shutil.copytree("/src/gdp-wired", work)
    t0 = time.time()
    try:
        p = subprocess.run(["timeout", "-k", "5", str(limit), "bash", "-c", cmd], cwd=work, capture_output=True, text=True, timeout=limit + 30)
        code, out, err = p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        code, out, err = 124, "", "killed"
    return {"name": name, "code": code, "seconds": round(time.time() - t0, 2), "out": out[-400_000:], "err": err[-2000:]}


@app.local_entrypoint()
def main(jobs: str, out: str):
    live = GDP / "supercomputer" / ".live"
    live.mkdir(exist_ok=True)
    ticket = live / f"{app.app_id}"
    ticket.write_text(str(os.getpid()))
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    try:
        js = json.loads(pathlib.Path(jobs).read_text())
        (outdir / "jobs.json").write_text(json.dumps(js, indent=1))
        print(f"{len(js)} jobs", flush=True)
        n = 0
        with (outdir / "results.jsonl").open("w") as f:
            for row in job.starmap([(j["name"], j["cmd"], j.get("timeout", 600)) for j in js], order_outputs=False, return_exceptions=True):
                if isinstance(row, BaseException):
                    row = {"name": "?", "code": -1, "err": repr(row)[:400]}
                f.write(json.dumps(row) + "\n")
                f.flush()
                n += 1
                if n % 50 == 0:
                    print(f"{n}/{len(js)}, {round(time.time() - t0)} s", flush=True)
    finally:
        ticket.unlink(missing_ok=True)
    print(f"done in {round(time.time() - t0, 1)} s wall")
