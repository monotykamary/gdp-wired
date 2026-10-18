"""Synthesis (research/synth/run.ts) on a Modal GPU, through Dawn's node bindings on NVIDIA's Vulkan driver (see modal-gpu/).

    modal run research/synth/run_gpu.py --out ../runs/modal/synth/h100.json [--gpu H100] [--args "--only bucket"] [--script run-more.ts]

Cost hygiene: one container per run, a 15-minute function timeout, the call is cancelled if this entrypoint stops, and
the app is named hw-gpu-synth (check `modal app list` afterwards; `modal app stop -y <id>` for anything left).
"""
import json
import pathlib

import modal

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent.parent
HANDWIRED = GDP / "vendor" / "handwired"

image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install("libvulkan1", "vulkan-tools", "libxext6", "libx11-6", "libglvnd0", "libegl1", "curl", "ca-certificates", "unzip")
    .run_commands(
        "curl -fsSL https://bun.sh/install | bash",
        "mkdir -p /opt/dawn && cd /opt/dawn && /root/.bun/bin/bun init -y >/dev/null && /root/.bun/bin/bun add webgpu@0.6.2",
    )
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin", "NVIDIA_DRIVER_CAPABILITIES": "all"})
    .add_local_dir(GDP / "core", "/work/gdp-wired/core")
    .add_local_dir(GDP / "kernel", "/work/gdp-wired/kernel")
    .add_local_dir(GDP / "research" / "search", "/work/gdp-wired/research/search")
    .add_local_dir(GDP / "research" / "synth", "/work/gdp-wired/research/synth", ignore=["*.py", "__pycache__"])
    .add_local_dir(HANDWIRED / "src", "/work/gdp-wired/vendor/handwired/src", ignore=["**/node_modules/**"])
)
app = modal.App("hw-gpu-synth", image=image)


def run(args: str, script: str = "run.ts") -> dict:
    import subprocess

    def sh(cmd: str, timeout: int = 60) -> str:
        p = subprocess.run(["bash", "-c", cmd], capture_output=True, text=True, timeout=timeout)
        return p.stdout + p.stderr

    gpu = sh("nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv,noheader").strip()
    try:
        log = sh(f"cd /work/gdp-wired/research/synth && SYNTH_WORK=4e10 DAWN_MODULE=/opt/dawn/node_modules/webgpu/index.js bun {script} --gpu --out /tmp/result.json {args} 2>&1", timeout=820)
    except subprocess.TimeoutExpired as e:
        log = f"timed out: {(e.stdout or b'').decode() if isinstance(e.stdout, bytes) else e.stdout}"
    result = json.loads(pathlib.Path("/tmp/result.json").read_text()) if pathlib.Path("/tmp/result.json").exists() else None
    return {"gpu": gpu, "log": log[-30000:], "result": result}


@app.function(gpu="L4", timeout=900)
def synth_l4(args: str = "", script: str = "run.ts") -> dict:
    return run(args, script)


@app.function(gpu="H100", timeout=900)
def synth_h100(args: str = "", script: str = "run.ts") -> dict:
    return run(args, script)


@app.local_entrypoint()
def main(out: str, gpu: str = "H100", args: str = "", script: str = "run.ts"):
    call = {"L4": synth_l4, "H100": synth_h100}[gpu].spawn(args, script)
    try:
        r = call.get()
    finally:
        try:
            call.cancel()
        except Exception:
            pass
    pathlib.Path(out).parent.mkdir(parents=True, exist_ok=True)
    pathlib.Path(out).write_text(json.dumps(r, indent=1))
    print(r["gpu"])
    print(r["log"])
