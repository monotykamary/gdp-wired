"""The table's GPU passes on Modal GPUs, through Dawn's node bindings on NVIDIA's Vulkan driver (research/modal-gpu/):
one container per job, every job at once.

    modal run research/table/run_gpu.py --jobs research/table/jobs/<name>.json --out runs/modal/table/gpu-<name> [--gpu L4]

jobs.json as modal_table.py's ({"name", "cmd", "timeout"?}); cmd runs under bash in gdp-wired/ with DAWN_MODULE set.
The image has bun, Dawn (webgpu 0.6.2), Z3 5.3.1, pycparser, and the same benchmarks as modal_table.py at the same
commits. <out>/results.jsonl: one row per job (name, gpu, exit code, seconds, stdout). The app id and client pid are
registered in modal/.live/ (modal/reap.sh stops an orphan); every call is cancelled when this entrypoint stops."""
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
    .apt_install("libvulkan1", "vulkan-tools", "libxext6", "libx11-6", "libglvnd0", "libegl1", "curl", "ca-certificates", "unzip", "coreutils")
    .pip_install("pycparser==3.0")
    .run_commands(
        "curl -fsSL https://bun.sh/install | bash",
        "mkdir -p /opt/dawn && cd /opt/dawn && /root/.bun/bin/bun init -y >/dev/null && /root/.bun/bin/bun add webgpu@0.6.2",
        "curl -fsSL -o /tmp/z3.zip https://github.com/Z3Prover/z3/releases/download/z3-5.3.1/z3-5.3.1-x64-glibc-2.39.zip"
        " && unzip -q /tmp/z3.zip -d /opt && ln -s /opt/z3-5.3.1-x64-glibc-2.39/bin/z3 /usr/local/bin/z3 && z3 --version",
        f"mkdir /chc && curl -fsSL https://codeload.github.com/chc-comp/chc-comp26-benchmarks/tar.gz/{CHC_COMMIT} | tar xz -C /chc --strip-components 1",
    )
    .run_commands(f"python3 - <<'EOF'\n{KEEP}\nEOF")
    .run_commands(
        f"mkdir /tip && curl -fsSL https://codeload.github.com/tip-org/benchmarks/tar.gz/{TIP_COMMIT} | tar xz -C /tip --strip-components 1",
        f"mkdir /ari && curl -fsSL https://codeload.github.com/TermCOMP/TPDB-ARI/tar.gz/{ARI_COMMIT} | tar xz -C /ari --strip-components 1 TPDB-ARI-{ARI_COMMIT}/Integer_Transition_Systems",
        "mkdir -p /sv && cd /sv && for d in " + " ".join(SV_DIRS) + f"; do curl -fsSL 'https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks/-/archive/{SV_COMMIT}/sv-benchmarks-{SV_COMMIT}.tar.gz?path=c/'$d | tar xz --strip-components 1; done",
    )
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin", "NVIDIA_DRIVER_CAPABILITIES": "all", "DAWN_MODULE": "/opt/dawn/node_modules/webgpu/index.js"})
    .add_local_file(GDP / "runs/modal/chc2/spacer-models-sat/models.jsonl", "/data/spacer-models.jsonl")
    .add_local_dir(GDP / "research" / "table", "/work/gdp-wired/research/table", ignore=["*.py", "__pycache__"])
    .add_local_dir(GDP / "compare", "/work/gdp-wired/compare", ignore=["**/*.py", "**/out/**", "**/*.js"])
    .add_local_file(GDP / "compare/term/c2ari.py", "/work/gdp-wired/compare/term/c2ari.py")
    .add_local_dir(GDP / "vendor" / "handwired" / "src", "/work/gdp-wired/vendor/handwired/src", ignore=["**/node_modules/**"])
)
app = modal.App("gdp-wired-table-gpu", image=image)


def run(name: str, cmd: str, limit: int) -> dict:
    import subprocess

    gpu = subprocess.run(["bash", "-c", "nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv,noheader"], capture_output=True, text=True).stdout.strip()
    t0 = time.time()
    try:
        p = subprocess.run(["timeout", "-k", "5", str(limit), "bash", "-c", cmd], cwd="/work/gdp-wired", capture_output=True, text=True, timeout=limit + 30)
        code, out, err = p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        code, out, err = 124, "", "killed"
    return {"name": name, "gpu": gpu, "code": code, "seconds": round(time.time() - t0, 2), "out": out[-400_000:], "err": err[-2000:]}


@app.function(scaledown_window=2, gpu="L4", cpu=2.0, memory=8192, timeout=1800)
def job_l4(name: str, cmd: str, limit: int) -> dict:
    return run(name, cmd, limit)


@app.function(scaledown_window=2, gpu="H100", cpu=2.0, memory=8192, timeout=1800)
def job_h100(name: str, cmd: str, limit: int) -> dict:
    return run(name, cmd, limit)


@app.local_entrypoint()
def main(jobs: str, out: str, gpu: str = "L4"):
    live = GDP / "modal" / ".live"
    live.mkdir(exist_ok=True)
    ticket = live / f"{app.app_id}"
    ticket.write_text(str(os.getpid()))
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    fn = {"L4": job_l4, "H100": job_h100}[gpu]
    t0 = time.time()
    try:
        js = json.loads(pathlib.Path(jobs).read_text())
        (outdir / "jobs.json").write_text(json.dumps({"gpu": gpu, "jobs": js}, indent=1))
        print(f"{len(js)} jobs on {gpu}", flush=True)
        n = 0
        with (outdir / "results.jsonl").open("w") as f:
            for row in fn.starmap([(j["name"], j["cmd"], j.get("timeout", 600)) for j in js], order_outputs=False, return_exceptions=True):
                if isinstance(row, BaseException):
                    row = {"name": "?", "code": -1, "err": repr(row)[:400]}
                f.write(json.dumps(row) + "\n")
                f.flush()
                n += 1
                if n % 20 == 0:
                    print(f"{n}/{len(js)}, {round(time.time() - t0)} s", flush=True)
    finally:
        ticket.unlink(missing_ok=True)
    print(f"done in {round(time.time() - t0, 1)} s wall")
