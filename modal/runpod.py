"""RunPod pods as a backend for the GPU runners (research/hw/run_gpu.py, run_synth_gpu.py, research/modal-gpu/run_gpu.py):
one pod per batch, prepared once (Dawn's node bindings, bun, NVIDIA's Vulkan driver through its EGL ICD), the batch's
calls run on it one after another, the pod deleted when the batch ends however it ends.

    python3 research/hw/run_gpu.py --backend runpod --out runs/backends/hw/x.json [--args ...] [--gpus "NVIDIA GeForce RTX 4090,..."]
    python3 modal/runpod.py batch --jobs gpu-jobs.json --out runs/backends/gpu/<name>   (jobs: [{name, runner, fn, args}])
    python3 modal/runpod.py reap | status

Each call runs the runner's own function (the one its Modal GPU function wraps) on the pod, imported with a stub
`modal`, in the same paths as the Modal image (/work/gdp-wired, /opt/dawn, /tmp/result.json), so its output is the
Modal run's output. The GPU types are tried in order (--gpus, else $GDPW_RUNPOD_GPUS, else GPUS below) until one is
in stock, in the secure cloud then the community cloud ($GDPW_RUNPOD_CLOUDS). Before any call, `vulkaninfo --summary` must list an NVIDIA device, else the batch fails at once.

Cost hygiene: the pod's name and this client's pid are in modal/.live/runpod-<name>.json from before the pod exists
until it's deleted; the pod is deleted in a finally (Ctrl-C, SIGTERM and SIGHUP included); `modal/reap.sh` deletes a
pod whose client is gone, and any gdpw- pod with no ticket.
"""
import base64
import contextlib
import json
import os
import pathlib
import random
import signal
import socket
import subprocess
import sys
import tempfile
import time

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent
sys.path.insert(0, str(HERE))
GPUS = ["NVIDIA GeForce RTX 4090", "NVIDIA L4", "NVIDIA RTX A5000", "NVIDIA GeForce RTX 3090", "NVIDIA RTX A4000", "NVIDIA RTX 2000 Ada Generation",
        "NVIDIA RTX PRO 4000 Blackwell", "NVIDIA A40", "NVIDIA L40S", "NVIDIA L40", "NVIDIA RTX 6000 Ada Generation", "NVIDIA GeForce RTX 5090"]
KEY = pathlib.Path.home() / ".runpod" / "ssh" / "runpodctl-ssh-key"
TEMPLATE = "runpod-ubuntu-2404"
# NVIDIA's Vulkan ICD as the container has it (libGLX_nvidia) needs an X server; its EGL library doesn't
ICD = {"file_format_version": "1.0.1", "ICD": {"library_path": "libEGL_nvidia.so.0", "api_version": "1.4.329"}}
PREP = r"""
set -e
export DEBIAN_FRONTEND=noninteractive
apt-get update -y -q > /dev/null
apt-get install -y -q libvulkan1 vulkan-tools libxext6 libx11-6 libglvnd0 libegl1 curl ca-certificates unzip python3 > /dev/null
[ -x /root/.bun/bin/bun ] || curl -fsSL https://bun.sh/install | bash -s bun-v1.4.3 > /dev/null 2>&1
mkdir -p /opt/dawn && cd /opt/dawn && [ -d node_modules/webgpu ] || { /root/.bun/bin/bun init -y > /dev/null && /root/.bun/bin/bun add webgpu@0.6.2 > /dev/null; }
mkdir -p /etc/gdpw && echo '%s' > /etc/gdpw/nvidia_egl_icd.json
echo PREP-OK
""" % json.dumps(ICD)
ENV = "export PATH=/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin NVIDIA_DRIVER_CAPABILITIES=all VK_ICD_FILENAMES=/etc/gdpw/nvidia_egl_icd.json; "


class NoCapacity(RuntimeError):
    """No pod of any GPU type in the list (out of stock, or never reachable)."""


def log(*a):
    print("[runpod]", *a, file=sys.stderr, flush=True)


def live() -> pathlib.Path:
    import boat
    boat.LIVE.mkdir(parents=True, exist_ok=True)
    return boat.LIVE


def rp(*args, timeout=120, check=True) -> str:
    p = subprocess.run(["runpodctl", *args], capture_output=True, text=True, timeout=timeout)
    if check and p.returncode != 0:
        raise RuntimeError(f"runpodctl {' '.join(args[:2])}: {(p.stderr or p.stdout)[-500:]}")
    return p.stdout


def last_json(text: str):
    """The JSON object a runpodctl command printed after its progress lines."""
    i = text.find("{")
    while i >= 0:
        try:
            return json.loads(text[i:])
        except json.JSONDecodeError:
            i = text.find("{", i + 1)
    raise ValueError(f"no JSON in: {text[-300:]}")


def balance() -> float:
    return float(json.loads(rp("user"))["clientBalance"])


def preflight() -> str | None:
    """None if RunPod can take a batch now, else why not (its API, the balance under $GDPW_RUNPOD_MIN_BALANCE)."""
    floor = float(os.environ.get("GDPW_RUNPOD_MIN_BALANCE", "5"))
    try:
        b = balance()
    except Exception as e:
        return f"runpod API unreachable ({str(e)[:160]})"
    if b < floor:
        return f"runpod balance ${b:.2f} under ${floor:.2f}"
    return None


class Pod:
    def __init__(self, label: str, gpus: list[str] | None = None, disk: int = 20):
        self.gpus = gpus or [g for g in os.environ.get("GDPW_RUNPOD_GPUS", "").split(",") if g] or GPUS
        self.name = f"gdpw-{label}-{''.join(random.choice('abcdefghijklmnopqrstuvwxyz0123456789') for _ in range(6))}"
        self.disk = disk
        self.id = None
        self.info = {}
        self.ticket = live() / f"runpod-{self.name}.json"
        self.cm = pathlib.Path(tempfile.gettempdir()) / f"gdpw-rp-{os.getpid()}"
        self.t_create = None
        self.t_end = None

    def _ticket(self):
        self.ticket.write_text(json.dumps({"name": self.name, "id": self.id, "pid": os.getpid(), "host": socket.gethostname(), "since": time.time()}))

    def __enter__(self):
        self._ticket()
        self.balance0 = balance()
        errs = []
        clouds = [c for c in os.environ.get("GDPW_RUNPOD_CLOUDS", "SECURE,COMMUNITY").split(",") if c]
        for cloud, g in [(c, g) for c in clouds for g in self.gpus]:
            self.t_create = time.time()
            p = subprocess.run(["runpodctl", "pod", "create", "--name", self.name, "--gpu-id", g, "--cloud-type", cloud, "--template-id", TEMPLATE, "--container-disk-in-gb", str(self.disk),
                                "--env", json.dumps({"NVIDIA_DRIVER_CAPABILITIES": "all"}), "--wait", "--wait-timeout", "6m"], capture_output=True, text=True, timeout=480)
            out = p.stdout + p.stderr
            try:
                d = last_json(p.stdout)
            except ValueError:
                d = {}
            if p.returncode == 0 and d.get("id"):
                self.id, self.info = d["id"], d
                self._ticket()
                log(f"pod {self.id} ({g}, {cloud.lower()} cloud, ${d.get('costPerHr')}/h) up after {round(time.time() - self.t_create, 1)} s")
                return self
            # made but never reachable (or half made): gone before the next type
            for q in json.loads(rp("pod", "list", "--all", check=False) or "[]"):
                if q.get("name") == self.name:
                    self.id = q["id"]
                    self._delete()
            self.id = None
            errs.append(f"{g} ({cloud.lower()}): {out.strip().splitlines()[-1][-160:] if out.strip() else p.returncode}")
            log(f"no {g} in {cloud.lower()} cloud: {errs[-1][-200:]}")
        self.ticket.unlink(missing_ok=True)
        raise NoCapacity("no GPU pod: " + " | ".join(errs))

    def ssh_args(self) -> list[str]:
        s = self.info["ssh"]
        return ["ssh", "-i", str(KEY), "-p", str(s["port"]), "-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null", "-o", "LogLevel=ERROR",
                "-o", "ServerAliveInterval=15", "-o", "ControlMaster=auto", "-o", f"ControlPath={self.cm}", "-o", "ControlPersist=120", f"root@{s['ip']}"]

    def sh(self, cmd: str, timeout: int = 600, stdin: bytes | None = None) -> tuple[int, str]:
        p = subprocess.run([*self.ssh_args(), cmd], input=stdin, capture_output=True, timeout=timeout)
        return p.returncode, (p.stdout + p.stderr).decode("utf-8", "replace")

    def prepare(self):
        t0 = time.time()
        for k in range(10):  # sshd answers before the container is quite ready
            code, out = self.sh("true", 60)
            if code == 0:
                break
            time.sleep(5)
        code, out = self.sh(PREP, 900)
        if "PREP-OK" not in out:
            raise RuntimeError(f"pod prep failed: {out[-1500:]}")
        code, vk = self.sh(ENV + "vulkaninfo --summary 2>&1 | grep -E 'deviceName|driverName|apiVersion' | head -8", 120)
        if "NVIDIA" not in vk:
            raise RuntimeError(f"Vulkan sees no NVIDIA device on {self.id}: {vk[-800:]}")
        self.vulkan = vk.strip()
        import boat
        tar = boat.tree_tarball()
        code, out = self.sh("rm -rf /work/gdp-wired && mkdir -p /work/gdp-wired /root/gdpw && tar xzf - -C /work/gdp-wired && echo TREE-OK", 600, stdin=tar)
        if "TREE-OK" not in out:
            raise RuntimeError(f"tree upload failed: {out[-800:]}")
        code, out = self.sh("cat > /root/gdpw/agent.py", 60, stdin=(HERE / "agent.py").read_bytes())
        log(f"pod {self.id} prepared in {round(time.time() - t0, 1)} s; " + " | ".join(l.strip() for l in self.vulkan.splitlines()[:3]))

    def call(self, runner: str, fn: str, args: list, timeout: int = 900) -> dict:
        """The runner's function on the pod, as its Modal function calls it."""
        mod = str(pathlib.Path(runner).resolve().relative_to(GDP))
        py = ("import json, sys; sys.path.insert(0, '/root/gdpw'); from agent import import_runner; "
              f"m = import_runner('/work/gdp-wired/{mod}'); r = m.{fn}(*json.loads(sys.argv[1])); print('\\nGDPW-RESULT ' + json.dumps(r))")
        cmd = ENV + f"rm -f /tmp/result.json; cd /work/gdp-wired && python3 -c {sh_quote(py)} {sh_quote(json.dumps(args))}"
        code, out = self.sh(cmd, timeout + 60)
        tail = out.rsplit("GDPW-RESULT ", 1)
        if len(tail) < 2:
            raise RuntimeError(f"{fn} on the pod failed ({code}): {out[-2000:]}")
        return json.loads(tail[1].strip().splitlines()[0])

    def _delete(self):
        if not self.id:
            return
        for _ in range(5):
            rp("pod", "delete", self.id, check=False)
            time.sleep(2)
            if not any(p.get("id") == self.id for p in json.loads(rp("pod", "list", "--all") or "[]")):
                return
        log(f"pod {self.id} still listed after delete: check `runpodctl pod list --all`")

    def __exit__(self, *exc):
        self.t_end = time.time()
        with contextlib.suppress(Exception):
            subprocess.run([*self.ssh_args()[:-1], "-O", "exit", self.ssh_args()[-1]], capture_output=True, timeout=10)
        self._delete()
        self.ticket.unlink(missing_ok=True)
        time.sleep(5)
        with contextlib.suppress(Exception):
            self.balance1 = balance()
        up = round(self.t_end - (self.t_create or self.t_end), 1)
        self.cost = {"pod": self.id, "gpu": self.info.get("gpuId"), "cost_per_hr": self.info.get("costPerHr"), "held_s": up,
                     "balance_before": self.balance0, "balance_after": getattr(self, "balance1", None),
                     "balance_delta": round(self.balance0 - self.balance1, 4) if hasattr(self, "balance1") else None}
        log(f"pod {self.id} deleted after {up} s; balance {self.balance0} -> {getattr(self, 'balance1', '?')}")
        return False


def sh_quote(s: str) -> str:
    return "'" + s.replace("'", "'\\''") + "'"


@contextlib.contextmanager
def signals_as_interrupt():
    def h(sig, frame):
        raise KeyboardInterrupt(f"signal {sig}")
    old = {s: signal.signal(s, h) for s in (signal.SIGTERM, signal.SIGHUP)}
    try:
        yield
    finally:
        for s, o in old.items():
            signal.signal(s, o)


def call(runner: str, fn: str, args: list, gpus: str = "", label: str = "gpu", timeout: int = 900) -> dict:
    """One call on a pod of its own (created, prepared, the call, deleted)."""
    with signals_as_interrupt():
        pod = Pod(label, [g for g in gpus.split(",") if g] or None)
        with pod:
            pod.prepare()
            t0 = time.time()
            r = pod.call(runner, fn, args, timeout)
            r = {**r, "runpod": {"seconds": round(time.time() - t0, 1), "vulkan": pod.vulkan}}
        r["runpod"].update(pod.cost)
        return r


def batch(jobs: list[dict], out: str, gpus: str = ""):
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    rows = []
    with signals_as_interrupt():
        pod = Pod("batch", [g for g in gpus.split(",") if g] or None)
        with pod:
            pod.prepare()
            for j in jobs:
                s = time.time()
                try:
                    r = pod.call(str(GDP / j["runner"]), j.get("fn", "run"), j.get("args", []), j.get("timeout", 900))
                    code = 0
                except Exception as e:
                    r, code = {"error": str(e)[-3000:]}, 1
                (outdir / f"{j['name']}.json").write_text(json.dumps(r, indent=1))
                rows.append((j["name"], code, round(time.time() - s, 2)))
                print(f"{j['name']:40} exit {code:>3}  {rows[-1][2]:>8} s", flush=True)
        (outdir / "summary.tsv").write_text("".join(f"{n}\t{c}\t{s}\n" for n, c, s in rows))
        (outdir / "runpod.json").write_text(json.dumps({**pod.cost, "vulkan": pod.vulkan, "wall_s": round(time.time() - t0, 1)}, indent=1))
    print(f"{len(rows)} jobs, {sum(c != 0 for _, c, _ in rows)} failed, {round(time.time() - t0, 1)} s wall, {round(sum(s for _, _, s in rows), 1)} s of job time; "
          f"pod {pod.cost['gpu']} ${pod.cost['cost_per_hr']}/h held {pod.cost['held_s']} s, balance delta ${pod.cost['balance_delta']}")


def reap():
    pods = json.loads(rp("pod", "list", "--all") or "[]")
    tickets = {}
    for t in live().glob("runpod-*.json"):
        d = json.loads(t.read_text())
        tickets[d["name"]] = (t, d)
    import boat
    for p in pods:
        name = p.get("name", "")
        if not name.startswith("gdpw-"):
            continue
        t = tickets.get(name)
        if t and boat.pid_alive(t[1]["pid"], t[1].get("host", "")):
            print(f"live: pod {p['id']} {name} (client {t[1]['pid']})")
            continue
        rp("pod", "delete", p["id"], check=False)
        print(f"deleted pod {p['id']} {name} ({'client gone' if t else 'no ticket'})")
        if t:
            t[0].unlink(missing_ok=True)
    for name, (t, d) in tickets.items():
        if not any(p.get("name") == name for p in pods) and not boat.pid_alive(d["pid"], d.get("host", "")):
            t.unlink(missing_ok=True)
    print(f"{len(json.loads(rp('pod', 'list') or '[]'))} pods up")


def cli(main, runner: str):
    """`python3 <GPU runner> --backend runpod ...`: the runner's entrypoint parameters as flags."""
    import argparse
    import inspect
    ap = argparse.ArgumentParser()
    for p in inspect.signature(main).parameters.values():
        flag = "--" + p.name.replace("_", "-")
        if p.default is inspect.Parameter.empty:
            ap.add_argument(flag, required=True, dest=p.name)
        elif isinstance(p.default, bool):
            ap.add_argument(flag, action="store_true", default=p.default, dest=p.name)
        else:
            ap.add_argument(flag, type=type(p.default), default=p.default, dest=p.name)
    a = ap.parse_args()
    if getattr(a, "backend", "runpod") != "runpod":
        raise SystemExit(f"on Modal: modal run {runner} ...")
    main(**vars(a))


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    b = sub.add_parser("batch")
    b.add_argument("--jobs", required=True)
    b.add_argument("--out", required=True)
    b.add_argument("--gpus", default="")
    sub.add_parser("reap")
    sub.add_parser("status")
    a = ap.parse_args()
    if a.cmd == "batch":
        batch(json.loads(pathlib.Path(a.jobs).read_text()), a.out, a.gpus)
    elif a.cmd == "reap":
        reap()
    else:
        print(rp("pod", "list", "--all"))
