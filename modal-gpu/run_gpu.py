"""Handwired's GPU searches on a Modal GPU, through Dawn's node bindings (the `webgpu` npm package) on NVIDIA's Vulkan
driver. Headless Chrome is in the image too (--mode chrome), but on these containers it only ever finds SwiftShader.

    modal run modal-gpu/run_gpu.py --config modal-gpu/suite.json --out ../runs/modal/gpu-search/suite.json [--gpu L4] [--mode dawn]

The config is {"jobs": [{"search": <index into search/models.ts>, "what"?, "space"?: {"depth", "bound"}, "warm"?}]}.
Cost hygiene: one container per call, a 15-minute function timeout (the driver gives up at 13), and the call is
cancelled if this entrypoint stops for any reason.
"""
import json
import pathlib

import modal

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent
HANDWIRED = GDP / "vendor" / "handwired"

image = (
    modal.Image.debian_slim(python_version="3.12")
    # NVIDIA's Vulkan ICD (mounted by Modal at /etc/vulkan/icd.d) loads libGLX_nvidia, which needs the X libraries.
    .apt_install("libvulkan1", "vulkan-tools", "libxext6", "libx11-6", "libglvnd0", "libegl1", "curl", "ca-certificates", "unzip", "wget")
    .run_commands(
        "wget -q https://dl.google.com/linux/direct/google-chrome-stable_current_amd64.deb && apt-get install -y ./google-chrome-stable_current_amd64.deb && rm google-chrome-stable_current_amd64.deb",
        "curl -fsSL https://bun.sh/install | bash",
        "mkdir -p /opt/dawn && cd /opt/dawn && /root/.bun/bin/bun init -y >/dev/null && /root/.bun/bin/bun add webgpu@0.6.2",
    )
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin", "NVIDIA_DRIVER_CAPABILITIES": "all"})
    .add_local_dir(GDP / "core", "/work/gdp-wired/core")
    .add_local_dir(GDP / "kernel", "/work/gdp-wired/kernel")
    .add_local_dir(GDP / "search", "/work/gdp-wired/search")
    .add_local_dir(GDP / "modal-gpu", "/work/gdp-wired/modal-gpu", ignore=["*.py", "__pycache__"])
    .add_local_dir(HANDWIRED / "src", "/work/gdp-wired/vendor/handwired/src", ignore=["**/node_modules/**"])
    .add_local_dir(HANDWIRED / "lab", "/work/gdp-wired/vendor/handwired/lab", ignore=["**/node_modules/**", "**/*.json"])
)
app = modal.App("hw-gpu-search", image=image)


def run(config: dict, mode: str) -> dict:
    import subprocess

    def sh(cmd: str, timeout: int = 60) -> str:
        p = subprocess.run(["bash", "-c", cmd], capture_output=True, text=True, timeout=timeout)
        return p.stdout + p.stderr

    gpu = sh("nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv,noheader").strip()
    vulkan = sh("vulkaninfo --summary 2>/dev/null | grep -E 'deviceName|driverName|apiVersion' | head -6").strip()
    try:
        if mode == "chrome":
            log = sh(f"cd /work/gdp-wired/modal-gpu && bun driver.ts --config '{json.dumps(config)}' --out /tmp/result.json --timeout 780000", timeout=820)
        else:
            log = sh(f"cd /work/gdp-wired/modal-gpu && DAWN_MODULE=/opt/dawn/node_modules/webgpu/index.js bun dawn-run.ts --config '{json.dumps(config)}' --out /tmp/result.json 2>&1", timeout=820)
    except subprocess.TimeoutExpired as e:
        log = f"timed out: {e}"
    result = json.loads(pathlib.Path("/tmp/result.json").read_text()) if pathlib.Path("/tmp/result.json").exists() else None
    chrome = sh("tail -c 6000 /tmp/chrome.log 2>/dev/null")
    return {"gpu": gpu, "vulkan": vulkan, "log": log[-20000:], "chromeLog": chrome, "result": result}


@app.function(gpu="L4", timeout=900)
def search_l4(config: dict, mode: str = "dawn") -> dict:
    return run(config, mode)


@app.function(gpu="A10G", timeout=900)
def search_a10g(config: dict, mode: str = "dawn") -> dict:
    return run(config, mode)


@app.function(gpu="H100", timeout=900)
def search_h100(config: dict, mode: str = "dawn") -> dict:
    return run(config, mode)


@app.local_entrypoint()
def main(config: str, out: str, gpu: str = "L4", mode: str = "dawn"):
    fn = {"L4": search_l4, "A10G": search_a10g, "H100": search_h100}[gpu]
    call = fn.spawn(json.loads(pathlib.Path(config).read_text()), mode)
    try:
        r = call.get()
    finally:
        try:
            call.cancel()
        except Exception:
            pass
    pathlib.Path(out).parent.mkdir(parents=True, exist_ok=True)
    pathlib.Path(out).write_text(json.dumps(r, indent=1))
    print(r["gpu"], "|", r["vulkan"].replace("\n", " | "))
    print(r["log"][-6000:])
