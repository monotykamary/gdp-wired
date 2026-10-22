"""Probe: does a Modal GPU container expose NVIDIA Vulkan (what Chrome's and Dawn's WebGPU need)?"""
import modal

image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install("libvulkan1", "vulkan-tools", "libxext6", "libx11-6", "libglvnd0", "libegl1", "curl", "ca-certificates", "unzip", "pciutils")
    .env({"NVIDIA_DRIVER_CAPABILITIES": "all", "NVIDIA_VISIBLE_DEVICES": "all"})
)
app = modal.App("hw-gpu-probe", image=image)


@app.function(scaledown_window=2, gpu="L4", timeout=300)
def probe() -> str:
    import subprocess
    def sh(c):
        p = subprocess.run(["bash", "-c", c], capture_output=True, text=True)
        return f"$ {c}\n{p.stdout[-4000:]}{p.stderr[-2000:]}\n"
    out = ""
    for c in ["nvidia-smi --query-gpu=name,driver_version --format=csv", "ls -la /usr/share/vulkan/icd.d /etc/vulkan/icd.d 2>&1",
              "ls /usr/lib/x86_64-linux-gnu | grep -i -E 'nvidia|GLX|EGL' | head -40", "find / -name 'nvidia_icd*.json' 2>/dev/null | head",
              "vulkaninfo --summary 2>&1 | head -60"]:
        out += sh(c)
    return out


@app.local_entrypoint()
def main():
    print(probe.remote())
