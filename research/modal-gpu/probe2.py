import modal, pathlib
HERE = pathlib.Path(__file__).resolve().parent
image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install("libvulkan1", "vulkan-tools", "libxext6", "libx11-6", "libglvnd0", "libegl1", "curl", "ca-certificates", "unzip", "wget")
    .run_commands(
        "wget -q https://dl.google.com/linux/direct/google-chrome-stable_current_amd64.deb && apt-get install -y ./google-chrome-stable_current_amd64.deb && rm google-chrome-stable_current_amd64.deb",
        "curl -fsSL https://bun.sh/install | bash",
        "mkdir -p /opt/dawn && cd /opt/dawn && /root/.bun/bin/bun init -y >/dev/null && /root/.bun/bin/bun add webgpu",
    )
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin", "NVIDIA_DRIVER_CAPABILITIES": "all"})
    .add_local_file(HERE / "probe-chrome.ts", "/work/probe-chrome.ts")
    .add_local_file(HERE / "probe-dawn.ts", "/opt/dawn/probe-dawn.ts")
)
app = modal.App("hw-gpu-probe", image=image)

@app.function(scaledown_window=2, gpu="L4", timeout=600)
def probe() -> str:
    import subprocess
    def sh(c, t=300):
        try:
            p = subprocess.run(["bash", "-c", c], capture_output=True, text=True, timeout=t); return f"$ {c}\n{p.stdout[-6000:]}{p.stderr[-3000:]}\n"
        except subprocess.TimeoutExpired: return f"$ {c}\nTIMEOUT\n"
    return sh("cd /work && bun probe-chrome.ts") + sh("cd /opt/dawn && bun probe-dawn.ts 2>&1 | tail -5") + sh("cd /opt/dawn && node --version 2>&1; grep -l 'NVIDIA\\|vulkan' /tmp/probe-*.log | head; tail -n 15 /tmp/probe-vulkan-feature.log")

@app.local_entrypoint()
def main():
    print(probe.remote())
