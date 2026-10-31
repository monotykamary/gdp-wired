"""Bend's GPU path on the three rules (compare/bench/gpu.ts), on a Modal GPU: CUDA 12 (devel, for nvrtc), clang 19 from
apt.llvm.org, bun, and the Bend repo's bend2/ mounted beside gdp-wired's compare/.

    modal run compare/bench/modal_gpu.py --out ../runs/modal/compare-bench/gpu [--gpu L4]

One container, a 30-minute timeout, cancelled if this entrypoint stops for any reason; `sh supercomputer/reap.sh` afterwards.
"""
import os
import pathlib

import modal

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent.parent
BEND = pathlib.Path(os.environ.get("BEND_REPO", GDP.parent / "bend"))

image = (
    modal.Image.from_registry("nvidia/cuda:12.6.3-devel-ubuntu24.04", add_python="3.12")
    .apt_install("curl", "unzip", "ca-certificates", "wget", "gnupg", "lsb-release", "software-properties-common")
    .run_commands(
        "wget -qO /tmp/llvm.sh https://apt.llvm.org/llvm.sh && bash /tmp/llvm.sh 19 && clang-19 --version",
        "curl -fsSL https://bun.sh/install | bash",
    )
    .env({"PATH": "/root/.bun/bin:/usr/local/cuda/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
          "CUDA_HOME": "/usr/local/cuda", "BEND_NO_TELEMETRY": "1", "NVIDIA_DRIVER_CAPABILITIES": "all"})
    .add_local_dir(GDP / "compare", "/work/gdp-wired/compare", ignore=["**/node_modules/**", "**/*.js", "**/out/**", "**/*.py"])
    .add_local_dir(BEND / "bend2", "/work/bend/bend2", ignore=["**/node_modules/**", "docs/**"])
)
app = modal.App("gdp-wired-bend-gpu", image=image)


def run(probe: bool = False) -> dict:
    import subprocess
    env = {**os.environ, **({"PROBE": "1"} if probe else {})}
    p = subprocess.run(["bash", "-c", "cd /work/gdp-wired && BEND=/work/bend bun compare/bench/gpu.ts"], capture_output=True, text=True, timeout=1700, env=env)
    return {"code": p.returncode, "out": p.stdout, "err": p.stderr[-50_000:]}


@app.function(scaledown_window=2, gpu="L4", timeout=1800)
def bench_l4(probe: bool = False) -> dict:
    return run(probe)


@app.function(scaledown_window=2, gpu="H100", timeout=1800)
def bench_h100(probe: bool = False) -> dict:
    return run(probe)


@app.local_entrypoint()
def main(out: str, gpu: str = "L4", probe: bool = False):
    call = {"L4": bench_l4, "H100": bench_h100}[gpu].spawn(probe)
    try:
        res = call.get()
    except BaseException:
        call.cancel()
        raise
    d = pathlib.Path(out)
    d.mkdir(parents=True, exist_ok=True)
    (d / f"gpu-{gpu.lower()}{'-probe' if probe else ''}.log").write_text(res["out"] + "\n--- stderr ---\n" + res["err"])
    print(res["out"][-6000:])
    print("exit", res["code"])
