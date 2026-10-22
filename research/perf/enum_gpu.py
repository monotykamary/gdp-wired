"""The predicate enumeration on a Modal GPU, Bend's CUDA build beside our Handwired fork, in one container.

    modal run research/perf/enum_gpu.py --out perf/bend-enum/modal.json

Bend: the C that `bend kK.bend -o kK.c` writes on the Mac (perf/bend-enum/c), built here as bend2/main.ts's cli_build does
on Linux (clang 19, -DBEND_CUDA=1, -lcuda -lnvrtc, then `./kK --gpu-build`), and the CPU twins (-cpu, no `!`). Ours:
perf/enum-ours.ts through Dawn on NVIDIA's Vulkan driver. Cost hygiene: one container per GPU, 15-minute timeout, calls
cancelled when the entrypoint stops, app name enum-bend-vs-hw.
"""
import json
import pathlib

import modal

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent.parent
HANDWIRED = GDP / "vendor" / "handwired"

image = (
    modal.Image.from_registry("nvidia/cuda:12.4.1-devel-ubuntu22.04", add_python="3.12")
    .apt_install("wget", "lsb-release", "software-properties-common", "gnupg", "curl", "ca-certificates", "unzip",
                 "libvulkan1", "vulkan-tools", "libxext6", "libx11-6", "libglvnd0", "libegl1")
    .run_commands(
        "wget -q https://apt.llvm.org/llvm.sh && bash llvm.sh 19 >/dev/null",
        "curl -fsSL https://bun.sh/install | bash",
        "mkdir -p /opt/dawn && cd /opt/dawn && /root/.bun/bin/bun init -y >/dev/null && /root/.bun/bin/bun add webgpu@0.6.2",
    )
    .env({"PATH": "/root/.bun/bin:/usr/local/cuda/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin", "NVIDIA_DRIVER_CAPABILITIES": "all"})
    .add_local_dir(GDP / "research" / "perf" / "bend-enum" / "c", "/work/bend")
    .add_local_file(GDP / "research" / "perf" / "enum-ours.ts", "/work/gdp-wired/research/perf/enum-ours.ts")
    .add_local_dir(GDP / "research" / "hw", "/work/gdp-wired/research/hw", ignore=["*.py", "__pycache__"])
    .add_local_file(GDP / "research" / "enum" / "js.jsonl", "/work/gdp-wired/research/enum/js.jsonl")
    .add_local_dir(HANDWIRED / "src", "/work/gdp-wired/vendor/handwired/src", ignore=["**/node_modules/**"])
)
app = modal.App("enum-bend-vs-hw", image=image)
EXPECTED = {"24": "2576841102", "28": "1716719882", "30": "855026720", "31": "1710144229", "31x8": "1665511304"}


def run() -> dict:
    import statistics
    import subprocess
    import time

    def sh(cmd: str, timeout: int = 90) -> str:
        try:
            p = subprocess.run(["bash", "-c", cmd], capture_output=True, text=True, timeout=timeout)
            return (p.stdout + p.stderr).strip()
        except subprocess.TimeoutExpired as e:
            got = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
            return f"TIMEOUT after {timeout}s: {got[-300:]}"

    def timed(cmd: str, n: int = 5) -> dict:
        times, out = [], ""
        for _ in range(n):
            t = time.perf_counter()
            out = sh(cmd)
            times.append((time.perf_counter() - t) * 1000)
            if out.startswith("TIMEOUT"):
                break
        return {"ms": round(statistics.median(times), 1), "out": out[-300:]}

    info = {"gpu": sh("nvidia-smi --query-gpu=name,driver_version --format=csv,noheader"), "cpus": sh("nproc"), "clang": sh("clang-19 --version | head -1")}
    # Why the GPU binary may hang: its probe, the GPU program it wrote, and a short run with the GPU off and on.
    info["probe"] = sh("cd /work/bend && clang-19 -DBEND_CUDA=1 -I/usr/local/cuda/include -L/usr/local/cuda/lib64 -std=c11 -O3 k24.c -lpthread -lm -o k24 -lcuda -lnvrtc 2>&1 | tail -5;"
                       " (timeout 120 ./k24 --gpu-build; echo build-exit $?) 2>&1 | tail -20; ls -la /work/bend | grep k24;"
                       " (timeout 30 ./k24 --gpu off; echo off-exit $?) 2>&1 | tail -3; (timeout 30 ./k24; echo on-exit $?) 2>&1 | tail -10; ./k24 --help 2>&1 | head -20", timeout=300)
    bend = []
    for k in EXPECTED:
        build = sh(f"cd /work/bend && clang-19 -DBEND_CUDA=1 -I/usr/local/cuda/include -L/usr/local/cuda/lib64 -L/usr/local/cuda/lib -std=c11 -O3 k{k}.c -lpthread -lm -o k{k} -lcuda -lnvrtc && ./k{k} --gpu-build"
                   f" && clang-19 -std=c11 -O3 k{k}-cpu.c -lpthread -lm -o k{k}-cpu && echo built")
        row = {"k": k, "build": build[-400:]}
        if build.endswith("built"):
            row["gpu"] = timed(f"cd /work/bend && ./k{k}")
            row["par"] = timed(f"cd /work/bend && ./k{k}-cpu --gpu off")
            if k != "31x8":
                row["seq"] = timed(f"cd /work/bend && ./k{k}-cpu --threads 1 --gpu off", 3)
            row["agree"] = all(row[m]["out"].endswith(EXPECTED[k]) for m in ("gpu", "par"))
        bend.append(row)
    ours = sh("cd /work/gdp-wired/research/perf && DAWN_MODULE=/opt/dawn/node_modules/webgpu/index.js bun enum-ours.ts 24 28 30 31 2>&1", timeout=600)
    whole = {k: timed(f"cd /work/gdp-wired/research/perf && DAWN_MODULE=/opt/dawn/node_modules/webgpu/index.js bun enum-ours.ts {k}", 3) for k in ("24", "31")}
    return {**info, "bend": bend, "ours": ours, "oursWholeProcess": whole}


@app.function(scaledown_window=2, gpu="H100", timeout=900, cpu=8.0)
def h100() -> dict:
    return run()


@app.function(scaledown_window=2, gpu="L4", timeout=900, cpu=8.0)
def l4() -> dict:
    return run()


@app.local_entrypoint()
def main(out: str, gpus: str = "H100,L4"):
    calls = {g: {"H100": h100, "L4": l4}[g].spawn() for g in gpus.split(",")}
    results = {}
    try:
        for name, call in calls.items():
            try:
                results[name] = call.get()
            except Exception as e:  # keep the other GPU's result
                results[name] = {"error": repr(e)}
    finally:
        for call in calls.values():
            try:
                call.cancel()
            except Exception:
                pass
    pathlib.Path(out).write_text(json.dumps(results, indent=1))
    print(json.dumps(results, indent=1)[:6000])
