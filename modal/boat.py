"""boat.dev VMs as a backend for modal/run.py and the compare runners: a pool of VMs that lives across batches, kept
stopped between them (a stopped VM bills no compute and keeps its disk), resumed per batch, stopped again a short idle
time after it, and deleted only on teardown or when the image changes.

    python3 modal/run.py --backend boat --jobs modal/suite.json --out runs/backends/suite [--vms N] [--idle 60]
    python3 modal/boat.py status | reap | teardown [--all] | image [--build] | usage <since ISO>

The image is one named snapshot, `gdpw-<hash>`, built in layers (bun and Lean, then each compare runner's solvers and
benchmarks: its BOAT_SETUP), each layer a snapshot of its own, so changing a layer rebuilds it and the ones above only.
The pool is a registry of VM ids in modal/.live/boat-pool.json of the main checkout (so every worktree shares it),
guarded by a lock: a batch leases VMs (its pid on each), resumes the stopped ones, creates the rest within the plan's
limits (`boat limits`: active VMs, starts per minute, hour and day), and releases them at the end. Every VM a batch
holds has a TTL renewed while the client lives (a VM whose client died stops by itself within 15 minutes); a released
VM's TTL is the idle time, after which boat stops it.

A batch: the worktree as git sees it (tracked and untracked files that aren't ignored, with the submodules', minus the
same paths modal/run.py leaves out) goes to one VM, which serves it to the others through a token-gated boat URL, and
each VM unpacks it fresh (no item sees an earlier batch's tree). Items run as modal/agent.py describes, longest first
by the last run's times, each VM taking what fits its free CPUs (2 vCPU and 4 GB a slot, as Modal's default container).
"""
import base64
import contextlib
import fcntl
import hashlib
import io
import json
import math
import os
import pathlib
import random
import signal
import socket
import subprocess
import sys
import tarfile
import threading
import time
import urllib.parse

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent
BOAT = os.environ.get("BOAT_BIN") or next((p for p in [str(pathlib.Path.home() / ".ascii/bin/boat")] if os.path.exists(p)), "boat")
ENV = {**os.environ, "BOAT_NO_UPDATE": "1", "NO_COLOR": "1"}
SLOT_CPU, SLOT_MEM = 2, 4096  # a slot: Modal's default container
TYPES = {"small": (2, 4096), "default": (4, 8192), "large": (8, 16384)}  # vCPU, MB
LIBRARY = ["Cert", "Kernel", "Cyclic", "Progress", "StepLaw", "Steps", "Sets", "History", "Live", "Ghost", "Refine", "Bridge", "BridgeRules", "Data"]
BACKSTOP = 900  # the TTL a held VM keeps renewing: a VM whose client is gone stops within this
STARTS_RESERVE = 10  # starts of the day and the hour never spent by one batch


def log(*a):
    print("[boat]", *a, file=sys.stderr, flush=True)


def main_checkout() -> pathlib.Path:
    try:
        common = subprocess.run(["git", "-C", str(GDP), "rev-parse", "--path-format=absolute", "--git-common-dir"], capture_output=True, text=True, check=True).stdout.strip()
        return pathlib.Path(common).parent
    except Exception:
        return GDP


LIVE = pathlib.Path(os.environ.get("GDPW_LIVE") or main_checkout() / "modal" / ".live")


# ------------------------------------------------------------------------------------------------------------- the CLI
_sem = threading.BoundedSemaphore(int(os.environ.get("GDPW_BOAT_PARALLEL", "48")))


def boat(*args, timeout=120, check=True, stdin=None) -> str:
    with _sem:
        p = subprocess.run([BOAT, *args], capture_output=True, text=True, timeout=timeout, env=ENV, input=stdin)
    if check and p.returncode != 0:
        raise RuntimeError(f"boat {args[0]} failed ({p.returncode}): {(p.stderr or p.stdout)[-400:]}")
    return p.stdout


def bj(*args, timeout=120, check=True):
    return json.loads(boat(*args, "--json", timeout=timeout, check=check))


def exec_(vm: str, argv: list[str], timeout: int = 60) -> dict:
    out = boat("exec", vm, "--timeout", str(timeout), "--json", "--", *argv, timeout=timeout + 60, check=False)
    try:
        return json.loads(out)
    except json.JSONDecodeError:
        return {"exitCode": -1, "stdout": "", "stderr": out[-400:], "success": False}


def exec_json(vm: str, argv: list[str], timeout: int = 60, tries: int = 4):
    last = None
    for k in range(tries):
        r = exec_(vm, argv, timeout)
        if r.get("exitCode") == 0:
            try:
                return json.loads(r["stdout"].strip().splitlines()[-1])
            except Exception as e:
                last = f"bad answer: {e}: {r.get('stdout', '')[-300:]} {r.get('stderr', '')[-300:]}"
        else:
            last = f"exit {r.get('exitCode')}: {r.get('stderr', '')[-400:]}{r.get('error', '')}"
        time.sleep(1 + 2 * k)
    raise RuntimeError(f"{vm}: {last}")


def limits() -> dict:
    return bj("limits")


def sandboxes() -> dict:
    return {s["id"]: s for s in bj("list", "--all")["sandboxes"]}


def named_snapshots() -> dict:
    return {s["name"]: s for s in bj("snapshots").get("named", [])}


RUNNING = {"ready", "idle", "running"}


_states = {"t": 0.0, "d": {}}
_states_lock = threading.Lock()


def states(max_age: float = 3.0) -> dict:
    """`boat list` at most every few seconds, however many threads ask."""
    with _states_lock:
        if time.time() - _states["t"] > max_age:
            _states["d"] = sandboxes()
            _states["t"] = time.time()
        return _states["d"]


def wait_running(ids: list[str], timeout: int = 600) -> dict:
    """Waits until each VM answers an exec; returns {id: seconds} for those that did."""
    t0, ok = time.time(), {}
    pending = list(ids)
    while pending and time.time() - t0 < timeout:
        try:
            states_ = states()
        except Exception:
            time.sleep(3)
            continue
        for i in list(pending):
            if states_.get(i, {}).get("state") in RUNNING:
                r = exec_(i, ["true"], 30)
                if r.get("exitCode") == 0:
                    ok[i] = round(time.time() - t0, 1)
                    pending.remove(i)
        if pending:
            time.sleep(3)
    return ok


# ---------------------------------------------------------------------------------------------------------- the image
TOOLS = r"""
sudo apt-get update -y -q
sudo DEBIAN_FRONTEND=noninteractive apt-get install -y -q curl unzip git ca-certificates xz-utils zstd bzip2 coreutils python3-pip
# as modal/run.py's image: bun (the version that image has) and Lean 4.34.0 by elan
curl -fsSL https://bun.sh/install | bash -s bun-v1.4.3
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.34.0
~/.elan/bin/lean --version
~/.bun/bin/bun --version
sudo mkdir -p /work /src/gdp-wired /bench /smt /vamp /sv /opt/gdpw
sudo chown "$USER" /smt /vamp /sv /opt/gdpw
"""
# the compare runners' solvers, a layer each (their BOAT_SETUP, next to their Modal image), the slowest to build first
RUNNERS = ["compare/tip/modal_tip.py", "compare/chc/modal_chc.py", "compare/term/modal_term.py", "compare/term/modal_sv.py"]


def runner_boat(path: str) -> dict:
    sys.path.insert(0, str(HERE))
    import agent
    mod = agent.import_runner(str(GDP / path))
    return {"setup": getattr(mod, "BOAT_SETUP", ""), **getattr(mod, "BOAT", {})}


def layers() -> list[tuple[str, str, str]]:
    """(layer, its snapshot's name, its script), each name hashing every script below it too."""
    out, h = [], hashlib.sha256(b"gdpw-image-v1\n")
    for name, script in [("tools", TOOLS), *[(pathlib.Path(r).stem.removeprefix("modal_"), runner_boat(r)["setup"]) for r in RUNNERS]]:
        h.update(name.encode() + b"\0" + script.encode() + b"\0")
        out.append((name, f"gdpw-{name}-{h.hexdigest()[:10]}", script))
    final = f"gdpw-{h.hexdigest()[:12]}"
    out[-1] = (out[-1][0], final, out[-1][2])
    return out


def image_name() -> str:
    return layers()[-1][1]


def build_layer(name: str, snap: str, script: str, parent: str | None):
    log(f"building layer {name} as {snap}" + (f" from {parent}" if parent else ""))
    args = ["new", "--ttl", "7200", "--no-env", "--no-monitoring", "--json"] + (["--from", parent] if parent else [])
    vm = None
    for line in boat(*args, timeout=900).splitlines():
        with contextlib.suppress(Exception):
            vm = vm or json.loads(line).get("id")
    if not vm:
        raise RuntimeError("no VM for the build")
    ticket = LIVE / f"boat-build-{vm}.json"
    LIVE.mkdir(parents=True, exist_ok=True)
    ticket.write_text(json.dumps({"vm": vm, "pid": os.getpid(), "host": socket.gethostname(), "snapshot": snap}))
    try:
        wait_running([vm])
        b64 = base64.b64encode(("set -ex\nexport DEBIAN_FRONTEND=noninteractive\n" + script).encode()).decode()
        exec_json(vm, ["bash", "-c", 'mkdir -p ~/.gdpw/build && echo "$1" | base64 -d > ~/.gdpw/build/l.sh && (setsid nohup bash -c "bash ~/.gdpw/build/l.sh > ~/.gdpw/build/l.log 2>&1; echo \\$? > ~/.gdpw/build/l.rc" > /dev/null 2>&1 &) && echo "{}"', "_", b64])
        t0 = time.time()
        while True:
            time.sleep(20)
            r = exec_(vm, ["bash", "-c", "cat ~/.gdpw/build/l.rc 2>/dev/null; echo; tail -c 600 ~/.gdpw/build/l.log"], 60)
            out = r.get("stdout", "")
            rc = out.split("\n", 1)[0].strip()
            if int(time.time() - t0) % 120 < 20:
                log(f"  {name}: {int(time.time() - t0)} s, {out.splitlines()[-1][-120:] if out.strip() else ''}")
            if rc:
                break
            if time.time() - t0 > 6600:
                raise RuntimeError(f"layer {name} still building after {int(time.time() - t0)} s")
        if rc != "0":
            raise RuntimeError(f"layer {name} failed ({rc}):\n{out[-1500:]}")
        exec_(vm, ["bash", "-c", "sudo apt-get clean; rm -rf ~/.cache/pip; sync"], 120)
        log(f"  {name} built in {int(time.time() - t0)} s; saving {snap}")
        boat("snapshot", vm, snap, "--json", timeout=1800)
        for _ in range(180):
            s = named_snapshots().get(snap)
            if s and s.get("status") == "ready":
                break
            time.sleep(10)
        else:
            raise RuntimeError(f"snapshot {snap} not ready")
    finally:
        boat("delete", vm, "--yes", "--json", check=False, timeout=180)
        ticket.unlink(missing_ok=True)


def ensure_image(build: bool = True) -> str:
    have = named_snapshots()
    chain = layers()
    parent = None
    for name, snap, script in chain:
        if snap not in have or have[snap].get("status") != "ready":
            if not build:
                raise RuntimeError(f"the image needs layer {snap}; run `python3 modal/boat.py image --build`")
            build_layer(name, snap, script, parent)
        parent = snap
    prune_snapshots({s for _, s, _ in chain})
    return chain[-1][1]


def prune_snapshots(keep: set[str]):
    """Named snapshots of older images (gdpw-*), except those a pool VM still comes from; the plan names 10 for free."""
    try:
        used = {v["snapshot"] for v in Registry().read()["vms"].values()}
        for n in named_snapshots():
            if n.startswith("gdpw-") and n not in keep and n not in used and n != "gdpw-base":
                boat("snapshot", "rm", n, "--json", check=False)
                log(f"removed old snapshot {n}")
    except Exception as e:
        log(f"(snapshot prune skipped: {e})")


# ------------------------------------------------------------------------------------------------------- the registry
def pid_alive(pid: int, host: str) -> bool:
    if host != socket.gethostname():
        return True  # another machine's client: never presumed dead
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


class Registry:
    def __init__(self):
        LIVE.mkdir(parents=True, exist_ok=True)
        self.path = LIVE / "boat-pool.json"
        self.lockf = LIVE / "boat-pool.lock"

    @contextlib.contextmanager
    def locked(self):
        with open(self.lockf, "a") as f:
            fcntl.flock(f, fcntl.LOCK_EX)
            try:
                d = self.read()
                yield d
                tmp = self.path.with_suffix(".tmp")
                tmp.write_text(json.dumps(d, indent=1))
                tmp.rename(self.path)
            finally:
                fcntl.flock(f, fcntl.LOCK_UN)

    def read(self) -> dict:
        try:
            return json.loads(self.path.read_text())
        except Exception:
            return {"vms": {}}


def reconcile(d: dict, live: dict):
    """Drops VMs boat no longer has (deleted, or their data expired) and records each one's state."""
    for i in list(d["vms"]):
        s = live.get(i)
        if not s or s.get("dataExpiredAt") or s.get("state") in ("deleted", "error", "deleting"):
            d["vms"].pop(i)
        else:
            d["vms"][i]["state"] = s.get("state")


def lease_free(v: dict) -> bool:
    l = v.get("lease")
    return not l or not pid_alive(l["pid"], l.get("host", ""))


# ---------------------------------------------------------------------------------------------------------- the tree
IGNORE = ["vendor/handwired/lab/recovery-*/**", "**/*.olean", "**/*.ilean", "**/*.c", "**/node_modules/**", "**/runs/**", "runs/**", "modal/**", "private/**",
          "vendor/handwired/lab/ui-exploration/**", "vendor/handwired/lab/knuth-plass/**", "vendor/handwired/assets/**", "vendor/handwired/tests/**", "vendor/gdp-ts/examples/**",
          "**/__pycache__/**"]


def _ignored(path: str, patterns: list[str]) -> bool:
    import fnmatch
    for p in patterns:
        if fnmatch.fnmatch(path, p) or (p.startswith("**/") and fnmatch.fnmatch(path, p[3:])):
            return True
    return False


def tree_files(root: pathlib.Path = GDP, ignore: list[str] = IGNORE) -> list[str]:
    """What git sees: tracked and untracked-not-ignored files, the submodules' too, minus `ignore` (modal/run.py's)."""
    def ls(d: pathlib.Path, prefix: str) -> list[str]:
        out = subprocess.run(["git", "-C", str(d), "ls-files", "-z", "-co", "--exclude-standard"], capture_output=True, check=True).stdout.decode().split("\0")
        files = []
        for f in filter(None, out):
            p = d / f
            if p.is_dir() and (p / ".git").exists():
                files += ls(p, prefix + f + "/")
            elif p.is_file() and not p.is_symlink() or p.is_symlink():
                files.append(prefix + f)
        return files
    return sorted(f for f in set(ls(root, "")) if not _ignored(f, ignore))


def tree_tarball(key: str = "") -> bytes:
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:gz", compresslevel=6) as tf:
        for f in tree_files():
            tf.add(GDP / f, arcname=f, recursive=False)
        cache = LIVE / "olean" / key
        if key and cache.exists():
            for f in sorted(cache.glob("*.olean")):
                tf.add(f, arcname=f".gdpw-olean/{f.name}")
    return buf.getvalue()


def library_key(lean_dir: pathlib.Path = GDP / "lean-kernel") -> str:
    h = hashlib.sha256(b"leanprover/lean4:v4.34.0\n")
    for mod in LIBRARY:
        h.update(mod.encode() + b"\0" + (lean_dir / f"{mod}.lean").read_bytes() + b"\0")
    return h.hexdigest()[:32]


# ------------------------------------------------------------------------------------------------------------- a batch
class VM:
    def __init__(self, id: str, type: str, how: str):
        self.id, self.type, self.how = id, type, how
        self.cpus = TYPES[type][0]
        self.slots = max(1, self.cpus // SLOT_CPU)
        self.t_request = time.time()
        self.t_ready = None
        self.t_end = None
        self.busy: list[list[float]] = []  # [start, end] per item
        self.dead = False


class Session:
    """The VMs a batch holds: leased from the pool, resumed, or created, each prepared with the batch's tree."""

    def __init__(self, label: str, idle: int = 60, teardown: bool = False, vm_type: str = "default", build: bool = True):
        self.batch = time.strftime("%Y%m%d-%H%M%S") + "-" + "".join(random.choice("abcdefghijklmnopqrstuvwxyz0123456789") for _ in range(6))
        self.label, self.idle, self.teardown, self.vm_type = label, idle, teardown, vm_type
        self.reg = Registry()
        self.image = ensure_image(build)
        self.key = library_key()
        self.tar = tree_tarball(self.key)
        self.agent_b64 = base64.b64encode((HERE / "agent.py").read_bytes()).decode()
        self.vms: dict[str, VM] = {}
        self.ready: list[VM] = []
        self.cv = threading.Condition()
        self.stop = threading.Event()
        self.seed_url = None
        self.seed_vm = None
        self.seed_done = threading.Event()
        self.wanted = 0
        self.creating = 0
        self.t0 = time.time()
        self.threads: list[threading.Thread] = []
        self.counts = {"leased_running": 0, "resumed": 0, "created": 0}
        threading.Thread(target=self._heartbeat, daemon=True).start()
        log(f"batch {self.batch}: image {self.image}, tree {len(self.tar) // 1024} KB, library {self.key[:12]}"
            f" ({len(list((LIVE / 'olean' / self.key).glob('*.olean'))) if (LIVE / 'olean' / self.key).exists() else 0} .olean shipped)")

    # -- acquiring
    def ensure(self, n: int, vm_type: str | None = None):
        """Asks for n VMs of a type in all (leased, resumed or created); returns at once, VMs join as they're ready."""
        vm_type = vm_type or self.vm_type
        have = sum(1 for v in self.vms.values() if v.type == vm_type and not v.dead)
        need = n - have
        if need <= 0:
            return
        self.wanted += need
        mine = []
        with self.reg.locked() as d:
            try:
                reconcile(d, sandboxes())
            except Exception as e:
                log(f"(reconcile skipped: {e})")
            free = [i for i, v in d["vms"].items() if v["snapshot"] == self.image and v["type"] == vm_type and lease_free(v) and i not in self.vms]
            free.sort(key=lambda i: (d["vms"][i].get("state") not in RUNNING, -d["vms"][i].get("last_used", 0)))
            for i in free[:need]:
                d["vms"][i]["lease"] = {"pid": os.getpid(), "host": socket.gethostname(), "batch": self.batch, "since": time.time(), "label": self.label}
                mine.append((i, d["vms"][i].get("state")))
        for i, state in mine:
            vm = VM(i, vm_type, "running" if state in RUNNING else "resumed")
            self.vms[i] = vm
            self._go(self._bring_up, vm, state in RUNNING)
        rest = need - len(mine)
        if rest > 0:
            self._go(self._create, rest, vm_type)

    def _go(self, f, *a):
        t = threading.Thread(target=f, args=a, daemon=True)
        t.start()
        self.threads.append(t)

    def _bring_up(self, vm: VM, running: bool):
        try:
            if not running:
                boat("resume", vm.id, "--json", timeout=300, check=False)
                self.counts["resumed"] += 1
            else:
                self.counts["leased_running"] += 1
            boat("extend", vm.id, "--ttl", str(BACKSTOP), "--json", check=False)
            if not wait_running([vm.id], 600):
                raise RuntimeError("never came up")
            self._prepare(vm)
        except Exception as e:
            log(f"{vm.id}: {e}")
            vm.dead = True
            self._release([vm.id])

    def _create(self, n: int, vm_type: str):
        """Creates n VMs within the plan's limits, as many per request as the minute allows, until enough or not useful."""
        self.creating += 1
        try:
            self._create1(n, vm_type)
        finally:
            self.creating -= 1

    def _create1(self, n: int, vm_type: str):
        while n > 0 and not self.stop.is_set():
            if self.enough():
                break
            try:
                lim = limits()
            except Exception:
                time.sleep(5)
                continue
            st = lim["starts"]
            room = min(st["minute"]["remaining"], st["hour"]["remaining"] - STARTS_RESERVE, st["day"]["remaining"] - STARTS_RESERVE,
                       lim["currentLimits"]["activeSandboxes"] - lim["activeSandboxes"], n)
            if not lim.get("canStart", True) or room <= 0:
                if st["hour"]["remaining"] - STARTS_RESERVE <= 0 or st["day"]["remaining"] - STARTS_RESERVE <= 0:
                    log("no starts left this hour or day: no more VMs for this batch")
                    break
                time.sleep(10)
                continue
            out = boat("new", "--from", self.image, "--type", vm_type, "--count", str(room), "--ttl", str(BACKSTOP), "--no-env", "--no-monitoring", "--json", timeout=600, check=False)
            ids = []
            for line in out.splitlines():
                with contextlib.suppress(Exception):
                    e = json.loads(line)
                    if e.get("id") and e["id"] not in ids and e.get("event") != "error":
                        ids.append(e["id"])
            if not ids:
                log(f"boat new gave no VM: {out[-300:]}")
                time.sleep(15)
                continue
            if self.stop.is_set():  # the batch ended while they were made: into the pool, stopped
                with self.reg.locked() as d:
                    for i in ids:
                        d["vms"][i] = {"type": vm_type, "snapshot": self.image, "created": time.time(), "last_used": time.time(), "state": "starting", "lease": None}
                for i in ids:
                    boat("extend", i, "--ttl", str(max(60, self.idle)), "--json", check=False)
                break
            with self.reg.locked() as d:
                for i in ids:
                    d["vms"][i] = {"type": vm_type, "snapshot": self.image, "created": time.time(), "last_used": time.time(), "state": "starting",
                                   "lease": {"pid": os.getpid(), "host": socket.gethostname(), "batch": self.batch, "since": time.time(), "label": self.label}}
            self.counts["created"] += len(ids)
            for i in ids:
                vm = VM(i, vm_type, "created")
                self.vms[i] = vm
                self._go(self._bring_up_new, vm)
            n -= len(ids)

    def _bring_up_new(self, vm: VM):
        try:
            if not wait_running([vm.id], 600):
                raise RuntimeError("never came up")
            self._prepare(vm)
        except Exception as e:
            log(f"{vm.id}: {e}")
            vm.dead = True
            self._release([vm.id])

    def enough(self) -> bool:
        return getattr(self, "_enough", lambda: False)()

    # -- preparing
    def _prepare(self, vm: VM):
        with self.cv:
            seed = self.seed_vm is None and self.wanted > 2
            if seed:
                self.seed_vm = vm
        src = f"/home/user/.gdpw/in-{self.batch}.tar.gz"
        if seed or self.wanted <= 2:
            try:
                self._upload(vm, src)
            except Exception:
                if seed:
                    self.seed_vm = None
                raise
            if seed:
                try:
                    self._serve(vm)
                except Exception as e:
                    log(f"seed {vm.id} can't serve ({e}); each VM gets the tree from here")
                self.seed_done.set()
        else:
            self.seed_done.wait(900)
            if self.seed_url:
                src = self.seed_url
            else:
                src = f"/home/user/.gdpw/in-{self.batch}.tar.gz"
                self._upload(vm, src)
        r = self._agent(vm, ["prep", self.batch, src, self.key], 600, ship=True)
        if not r.get("ok") and src == self.seed_url:  # the URL failed: straight from here
            src = f"/home/user/.gdpw/in-{self.batch}.tar.gz"
            self._upload(vm, src)
            r = self._agent(vm, ["prep", self.batch, src, self.key], 600, ship=True)
        if not r.get("ok"):
            raise RuntimeError(f"prep failed: {r}")
        vm.cpus = r.get("cpus") or vm.cpus
        vm.slots = max(1, vm.cpus // SLOT_CPU)
        vm.t_ready = time.time()
        with self.cv:
            self.ready.append(vm)
            self.cv.notify_all()

    def _agent(self, vm: VM, args: list[str], timeout: int = 60, ship: bool = False, tries: int = 4):
        if ship:  # the agent itself, with the batch's first call to each VM
            return exec_json(vm.id, ["bash", "-c", 'mkdir -p ~/.gdpw && echo "$1" | base64 -d > ~/.gdpw/agent.py.new && mv ~/.gdpw/agent.py.new ~/.gdpw/agent.py && shift && exec python3 ~/.gdpw/agent.py "$@"', "_", self.agent_b64, *args], timeout, tries)
        return exec_json(vm.id, ["python3", "/home/user/.gdpw/agent.py", *args], timeout, tries)

    def _upload(self, vm: VM, dst: str):
        err = ""
        for k in range(4):
            try:
                with _sem:
                    p = subprocess.run([BOAT, "ssh", vm.id, "--", f"mkdir -p ~/.gdpw && cat > {dst}.part && mv {dst}.part {dst} && wc -c < {dst}"], input=self.tar, capture_output=True, timeout=600, env=ENV)
                if p.returncode == 0 and p.stdout.decode().strip().endswith(str(len(self.tar))):
                    return
                err = p.stderr.decode()[-300:]
            except Exception as e:
                err = repr(e)
            time.sleep(2 + 3 * k)
        raise RuntimeError(f"upload to {vm.id} failed: {err}")

    def _serve(self, vm: VM):
        self.tok = "".join(random.choice("abcdefghijklmnopqrstuvwxyz0123456789") for _ in range(32))
        port = 8765
        exec_json(vm.id, ["bash", "-c", f"mkdir -p ~/.gdpw/srv/{self.tok} && cp ~/.gdpw/in-{self.batch}.tar.gz ~/.gdpw/srv/{self.tok}/tree.tar.gz && echo '{{}}'"], 60)
        self._agent(vm, ["serve", "/home/user/.gdpw/srv", str(port)], 60, ship=True)
        h = bj("host", vm.id, str(port), "--localhost", "--private")
        u = urllib.parse.urlparse(h["url"])
        self.seed_url = urllib.parse.urlunparse(u._replace(path=f"/{self.tok}/tree.tar.gz"))
        # (the URL carries boat's token: it never goes to a log or a file)

    # -- running
    def run(self, items: list[dict], on_done, on_start=None):
        """Runs items ({name, kind, weight, est, ...spec}) longest first over the session's VMs, as they come up."""
        queue = sorted(items, key=lambda it: -it.get("est", 60))
        lock = threading.Lock()
        left = {"n": len(items)}
        tries: dict[str, int] = {}
        self._enough = lambda: len(queue) <= sum(v.slots for v in self.vms.values() if not v.dead)
        started_threads = set()
        all_done = threading.Event()
        if not items:
            return

        def take(vm: VM, free: int) -> list[dict]:
            """The longest items that fit the VM's free slots. A VM of a bigger type than the batch's own takes the
            items that need it first, and others only once none of those waits."""
            got = []
            with lock:
                bigs_wait = any(it.get("vm_type") == vm.type for it in queue)
                for it in list(queue):
                    if free <= 0:
                        break
                    if it["weight"] > free or it["weight"] > vm.slots:
                        continue
                    if bigs_wait and it.get("vm_type") != vm.type:
                        continue
                    queue.remove(it)
                    got.append(it)
                    free -= it["weight"]
            return got

        def finish(it: dict, row: dict):
            try:
                on_done(it, row)
            finally:
                with lock:
                    left["n"] -= 1
                    if left["n"] <= 0:
                        all_done.set()

        def worker(vm: VM):
            running: dict[str, tuple[dict, float]] = {}
            unsent: list[dict] = []  # starts whose tick got no answer: sent again (the agent ignores one it has)
            acks: list[str] = []
            fails = 0
            while not self.stop.is_set():
                free = vm.slots - sum(it["weight"] for it, _ in running.values())
                starts = take(vm, free) if free > 0 else []
                if not starts and not running and not acks and not unsent:
                    with lock:
                        if not queue:
                            break
                    time.sleep(2)  # what's left doesn't fit this VM now
                    continue
                now = time.time()
                for it in starts:
                    running[it["name"]] = (it, now)
                    if on_start:
                        on_start(it, vm)
                unsent += [{k: v for k, v in it.items() if k not in ("est", "weight", "vm_type", "meta")} | {"cpus": it["weight"] * SLOT_CPU} for it in starts]
                msg = json.dumps({"start": unsent, "acks": acks, "wait": 25 if running else 0}).encode()
                b64 = base64.b64encode(msg).decode()
                parts = [b64[k:k + 100_000] for k in range(0, len(b64), 100_000)]
                try:
                    r = self._agent(vm, ["tick", self.batch, *parts], 60, tries=1)
                    fails = 0
                    acks, unsent = [], []
                except Exception as e:
                    fails += 1
                    log(f"{vm.id}: tick failed ({fails}): {str(e)[:200]}")
                    if fails >= 8:
                        vm.dead = True
                        lost = []
                        with lock:
                            for name, (it, _) in running.items():
                                tries[name] = tries.get(name, 0) + 1
                                if tries[name] <= 1:
                                    queue.insert(0, it)
                                else:
                                    lost.append(it)
                        for it in lost:
                            finish(it, {"name": it["name"], "code": -1, "seconds": -1, "error": f"VM {vm.id} lost"})
                        log(f"{vm.id}: given up; its items go to other VMs")
                        return
                    time.sleep(min(30, 3 * fails))
                    continue
                for row in r.get("done", []):
                    name = row["name"]
                    acks.append(name)
                    if name in running:
                        it, t = running.pop(name)
                        vm.busy.append([t, time.time()])
                        finish(it, row)

        def spawn_workers():
            while not all_done.is_set() and not self.stop.is_set():
                with self.cv:
                    for vm in self.ready:
                        if vm.id not in started_threads:
                            started_threads.add(vm.id)
                            threading.Thread(target=worker, args=(vm,), daemon=True).start()
                    self.cv.wait(2)

        sp = threading.Thread(target=spawn_workers, daemon=True)
        sp.start()
        while not all_done.wait(1):
            if self.stop.is_set():
                raise KeyboardInterrupt
            if self.vms and all(v.dead for v in self.vms.values()) and not any(t.is_alive() for t in self.threads):
                raise RuntimeError("no VM left to run on")

    def call(self, module: str, fn: str, args, extra: dict | None = None, limit: int = 600):
        """One function of a runner on one of the session's VMs (the first ready), its result."""
        out = {}
        self.run([{"name": f"call-{fn}-{int(time.time() * 1000)}", "kind": "py", "module": module, "fn": fn, "args": args, "limit": limit, "weight": 1, "est": 1, **(extra or {})}],
                 lambda it, row: out.update(row))
        if "result" not in out:
            raise RuntimeError(f"{fn} failed on boat: {str(out.get('error', out))[-2000:]}")
        return out["result"]

    # -- collecting and closing
    def collect(self) -> dict[str, dict]:
        """Every item's out and err (their tails, as modal/run.py keeps), by name."""
        got: dict[str, dict] = {}
        lock = threading.Lock()

        def one(vm: VM):
            try:
                first = self._agent(vm, ["collect", self.batch, "0"], 120)
                parts = [base64.b64decode(first["data"])]
                for k in range(1, first["parts"]):
                    parts.append(base64.b64decode(self._agent(vm, ["collect", self.batch, str(k)], 120)["data"]))
                with tarfile.open(fileobj=io.BytesIO(b"".join(parts))) as tf:
                    for m in tf.getmembers():
                        name, f = m.name.rsplit("/", 1)
                        with lock:
                            got.setdefault(name, {})[f] = tf.extractfile(m).read().decode("utf-8", "replace")
            except Exception as e:
                log(f"{vm.id}: collect failed: {e}")
        ts = [threading.Thread(target=one, args=(vm,)) for vm in self.ready if not vm.dead]
        [t.start() for t in ts]
        [t.join() for t in ts]
        return got

    def harvest_oleans(self):
        """The Lean library this batch compiled, kept here so the next batch ships it to every VM."""
        cache = LIVE / "olean" / self.key
        have = lambda: len(list(cache.glob("*.olean"))) if cache.exists() else 0
        for vm in self.ready:
            if have() == len(LIBRARY):
                return
            if vm.dead:
                continue
            try:
                r = self._agent(vm, ["oleans", self.key], 120)
                with tarfile.open(fileobj=io.BytesIO(base64.b64decode(r["data"]))) as tf:
                    names = tf.getnames()
                    if len(names) > have():
                        cache.mkdir(parents=True, exist_ok=True)
                        tf.extractall(cache, filter="data")
                        log(f"kept {len(names)} .olean files of library {self.key[:12]} from {vm.id}")
            except Exception as e:
                log(f"{vm.id}: oleans: {e}")

    def _heartbeat(self):
        while not self.stop.wait(300):
            for vm in list(self.vms.values()):
                if not vm.dead and vm.t_end is None:
                    with contextlib.suppress(Exception):
                        boat("extend", vm.id, "--ttl", str(BACKSTOP), "--json", check=False)

    def close(self, kill: bool = True) -> dict:
        """Kills what still runs, releases every VM (stopped after the idle time, or deleted on teardown), and returns
        the batch's figures: VMs, VM-seconds held, seconds busy, idle VM-seconds and boat's dollars."""
        self.stop.set()
        for _ in range(600):  # a creation request in flight: its VMs join the pool before we let go
            if self.creating == 0:
                break
            time.sleep(1)
        vms = [v for v in self.vms.values()]

        def wind(vm: VM):
            if kill and vm.t_ready and not vm.dead:
                with contextlib.suppress(Exception):
                    self._agent(vm, ["kill", self.batch], 60)
            if self.seed_vm is vm:
                with contextlib.suppress(Exception):
                    exec_(vm.id, ["bash", "-c", f"pkill -f 'http.server 8765' ; rm -rf ~/.gdpw/srv"], 30)
            vm.t_end = time.time()
            if self.teardown:
                boat("delete", vm.id, "--yes", "--json", check=False, timeout=180)
            elif self.idle <= 0:
                boat("stop", vm.id, "--yes", "--json", check=False, timeout=180)
            else:
                boat("extend", vm.id, "--ttl", str(self.idle), "--json", check=False)
        ts = [threading.Thread(target=wind, args=(vm,)) for vm in vms]
        [t.start() for t in ts]
        [t.join(timeout=400) for t in ts]
        self._release([v.id for v in vms], deleted=self.teardown)
        held = sum((v.t_end or time.time()) - v.t_request for v in vms)
        busy = sum(union(v.busy) for v in vms)
        ready_held = sum((v.t_end or time.time()) - v.t_ready for v in vms if v.t_ready)
        return {"vms": len(vms), **self.counts, "types": sorted({v.type for v in vms}), "held_s": round(held, 1), "ready_held_s": round(ready_held, 1),
                "busy_s": round(busy, 1), "idle_vm_s": round(ready_held - busy, 1), "bring_up_s": round(held - ready_held, 1),
                "idle_tail_s": 0 if self.teardown or self.idle <= 0 else self.idle * len([v for v in vms if not v.dead])}

    def _release(self, ids: list[str], deleted: bool = False):
        with self.reg.locked() as d:
            for i in ids:
                if i in d["vms"]:
                    if deleted:
                        d["vms"].pop(i)
                    else:
                        d["vms"][i]["lease"] = None
                        d["vms"][i]["last_used"] = time.time()

    def dollars(self, ids: list[str] | None = None) -> float:
        since = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(self.t0 - 5))
        total = 0.0
        for i in ids or list(self.vms):
            with contextlib.suppress(Exception):
                total += bj("usage", i, "--since", since)["dollars"]
        return round(total, 5)


def union(iv: list[list[float]]) -> float:
    tot, end = 0.0, -1e18
    for a, b in sorted(iv):
        if b <= end:
            continue
        tot += b - max(a, end)
        end = b
    return tot


@contextlib.contextmanager
def signals_as_interrupt():
    """SIGTERM and SIGHUP end the batch as Ctrl-C does, so its finally runs (kill, release)."""
    def h(sig, frame):
        raise KeyboardInterrupt(f"signal {sig}")
    old = {s: signal.signal(s, h) for s in (signal.SIGTERM, signal.SIGHUP) if threading.current_thread() is threading.main_thread()}
    try:
        yield
    finally:
        for s, o in old.items():
            signal.signal(s, o)


# ----------------------------------------------------------------------------------------------------------- sizing
def plan_vms(items: list[dict], slots_per_vm: int, override: int = 0, cap: int = 0) -> int:
    """Enough VMs that the longest item bounds the batch (no more help), fewer when VMs come at the plan's start rate:
    with W slot-seconds of work, r starts a second and c slots a VM, n VMs arriving over n/r seconds finish by about
    W/(c n) + n/(2r), least at n = sqrt(2 r W / c). VMs the pool already holds come without a start."""
    if override:
        return override
    if not items:
        return 0
    W = sum(it["weight"] * it.get("est", 60) for it in items)
    L = max(it.get("est", 60) for it in items)
    useful = max(1, math.ceil(W / (slots_per_vm * L)))
    useful = min(useful, sum(it["weight"] for it in items) // max(1, slots_per_vm) + 1, len(items))
    try:
        lim = limits()
        pool = sum(1 for v in Registry().read()["vms"].values() if lease_free(v))
        rate = max(lim["currentLimits"]["creationRatePerMinute"], 1) / 60
        by_rate = pool + math.ceil(math.sqrt(2 * rate * W / slots_per_vm))
        room = lim["currentLimits"]["activeSandboxes"] - lim["activeSandboxes"] + pool
        st = lim["starts"]
        starts = min(st["hour"]["remaining"], st["day"]["remaining"]) - STARTS_RESERVE
        n = min(useful, by_rate, room, pool + max(0, starts))
    except Exception:
        n = min(useful, 10)
    if cap:
        n = min(n, cap)
    return max(1, n)


def last_durations(out: pathlib.Path, names: set[str], explicit: str = "") -> dict[str, float]:
    """Each job's seconds in the last run that has them: --durations, else <out>/summary.tsv, else the newest
    summary.tsv under runs/ (here and in the main checkout) sharing most of the names."""
    cands = [pathlib.Path(explicit)] if explicit else []
    cands.append(out / "summary.tsv")
    found = []
    for root in {GDP / "runs", main_checkout() / "runs"}:
        if root.exists():
            found += list(root.glob("**/summary.tsv"))
    found.sort(key=lambda p: -p.stat().st_mtime)
    cands += found[:200]
    for c in cands:
        try:
            rows = [l.split("\t") for l in c.read_text().splitlines() if l.strip()]
            d = {r[0]: float(r[2]) for r in rows if len(r) >= 3 and float(r[2]) >= 0}
        except Exception:
            continue
        if d and len(names & set(d)) >= 0.5 * len(names):
            return d
    return {}


# ------------------------------------------------------------------------------------------------- modal/run.py's jobs
def run_jobs(spec: list[dict], out: str, pre: str, cmd, vms: int = 0, idle: int = 60, teardown: bool = False, durations: str = "", vm_type: str = "default", max_vms: int = 0):
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    past = last_durations(outdir, {j["name"] for j in spec}, durations)
    med = sorted(past.values())[len(past) // 2] if past else 60
    cap_slots = TYPES[vm_type][0] // SLOT_CPU
    items, order = [], []
    groups: dict[tuple, list] = {}
    for j in spec:  # (modal/run.py's summary order: its resource groups, in the order they first appear)
        groups.setdefault((j.get("cpu", 2.0), j.get("memory", 4096), j.get("timeout", 900)), []).append(j)
    for (cpu, memory, timeout), js in groups.items():
        for j in js:
            w = max(math.ceil(cpu / SLOT_CPU), math.ceil(memory / SLOT_MEM), 1)
            it = {"name": j["name"], "kind": "sh", "cmd": pre + cmd(j["cmd"]), "cwd": j.get("cwd", "."), "limit": timeout - 30, "weight": w, "est": past.get(j["name"], med)}
            if w > cap_slots:
                big = next((t for t, (c, m) in TYPES.items() if c // SLOT_CPU >= w and m >= memory), None)
                if not big:
                    raise SystemExit(f"{j['name']} asks for {cpu} vCPU and {memory} MB: no boat VM type has that")
                it["vm_type"] = big
            items.append(it)
            order.append(j["name"])
    rows: dict[str, dict] = {}
    sess = None
    summary = {}
    try:
        with signals_as_interrupt():
            sess = Session(f"run.py {pathlib.Path(out).name}", idle=idle, teardown=teardown, vm_type=vm_type)
            plain = [it for it in items if not it.get("vm_type")]
            bigs: dict[str, int] = {}
            for it in items:
                if it.get("vm_type"):
                    bigs[it["vm_type"]] = bigs.get(it["vm_type"], 0) + 1
            n = plan_vms(plain, cap_slots, vms, max_vms)
            log(f"{len(items)} jobs on {n} {vm_type} VM(s)" + "".join(f" + {k} {t}" for t, k in bigs.items()) + f" (times from {'the last run' if past else 'a guess'})")
            sess.ensure(n, vm_type)
            for t, k in bigs.items():
                sess.ensure(k, t)

            def done(it, row):
                rows[it["name"]] = row
                print(f"{it['name']:40} exit {row.get('code', -1):>3}  {row.get('seconds', -1):>8} s", flush=True)
            sess.run(items, done)
            logs = sess.collect()
            for name in order:
                r = rows.get(name, {"code": -1, "seconds": -1})
                lg = logs.get(name, {})
                o, e = lg.get("out", ""), lg.get("err", "")
                if r.get("error"):
                    e += ("\n" if e else "") + str(r["error"])
                (outdir / f"{name}.log").write_text(o + ("\n--- stderr ---\n" + e if e.strip() else ""))
            sess.harvest_oleans()
    finally:
        if sess:
            summary = sess.close()
    done_rows = [rows.get(n, {"code": -1, "seconds": -1}) for n in order]
    (outdir / "summary.tsv").write_text("".join(f"{n}\t{r.get('code', -1)}\t{r.get('seconds', -1)}\n" for n, r in zip(order, done_rows)))
    wall = round(time.time() - t0, 1)
    print(f"{len(done_rows)} jobs, {sum(r.get('code', -1) != 0 for r in done_rows)} failed, {wall} s wall, {round(sum(max(r.get('seconds', 0), 0) for r in done_rows), 1)} s of job time")
    if sess:
        summary["dollars_so_far"] = sess.dollars()
        summary["batch"] = sess.batch
        summary["wall_s"] = wall
        summary["image"] = sess.image
        (outdir / "boat.json").write_text(json.dumps(summary, indent=1))
        print(f"boat: {summary['vms']} VMs ({summary['created']} created, {summary['resumed']} resumed, {summary['leased_running']} already up), "
              f"${summary['dollars_so_far']} so far (boat usage), {summary['idle_vm_s']} idle VM-s of {summary['ready_held_s']} held ready, "
              f"{summary['bring_up_s']} VM-s bringing up" + (f", then up to {summary['idle_tail_s']} VM-s idle before they stop" if summary["idle_tail_s"] else ""))


# ----------------------------------------------------------------------------------------------------------- the CLI
def status():
    reg = Registry()
    with reg.locked() as d:
        reconcile(d, sandboxes())
        vms = d["vms"]
    by = {}
    for i, v in vms.items():
        k = (v["snapshot"], v["type"], v.get("state"), "leased" if not lease_free(v) else "free")
        by.setdefault(k, []).append(i)
    print(f"pool ({reg.path}): {len(vms)} VMs; image now {image_name()}")
    for k, ids in sorted(by.items()):
        print(f"  {len(ids):4} {k[1]:8} {k[2] or '?':10} {k[3]:6} {k[0]}")
    return vms


def reap():
    """Releases leases whose client died (killing what they left running), stops free VMs still up past their idle,
    and deletes build VMs whose client is gone."""
    reg = Registry()
    now = time.time()
    stop, kill = [], []
    with reg.locked() as d:
        reconcile(d, sandboxes())
        for i, v in d["vms"].items():
            l = v.get("lease")
            if l and not pid_alive(l["pid"], l.get("host", "")):
                kill.append((i, l["batch"]))
                v["lease"] = None
                v["last_used"] = now
            if not v.get("lease") and v.get("state") in RUNNING and now - v.get("last_used", 0) > 120:
                stop.append(i)
    for i, b in kill:
        exec_(i, ["bash", "-c", f"python3 ~/.gdpw/agent.py kill {b} 2>/dev/null || true"], 60)
        print(f"released {i} (client gone), killed batch {b}")
    for i in set(stop) | {i for i, _ in kill}:
        boat("stop", i, "--yes", "--json", check=False, timeout=180)
        print(f"stopped idle {i}")
    for t in LIVE.glob("boat-build-*.json"):
        b = json.loads(t.read_text())
        if not pid_alive(b["pid"], b.get("host", "")):
            boat("delete", b["vm"], "--yes", "--json", check=False)
            t.unlink()
            print(f"deleted orphan build VM {b['vm']}")
    live = sandboxes()
    up = [i for i, s in live.items() if s.get("state") in RUNNING]
    mine = set(reg.read()["vms"])
    print(f"{len(up)} boat VMs up ({len([i for i in up if i in mine])} of the pool)" + "".join(f"\n  not in the pool: {i} {live[i].get('name')}" for i in up if i not in mine))


def teardown(everything: bool = False):
    """Deletes the pool's free VMs that come from an older image (all free VMs with --all)."""
    img = image_name()
    gone = []
    with Registry().locked() as d:
        reconcile(d, sandboxes())
        for i, v in list(d["vms"].items()):
            if lease_free(v) and (everything or v["snapshot"] != img):
                gone.append(i)
                d["vms"].pop(i)
    def rm(i):
        boat("delete", i, "--yes", "--json", check=False, timeout=180)
    ts = [threading.Thread(target=rm, args=(i,)) for i in gone]
    [t.start() for t in ts]
    [t.join() for t in ts]
    print(f"deleted {len(gone)} VMs")


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("status")
    sub.add_parser("reap")
    t = sub.add_parser("teardown")
    t.add_argument("--all", action="store_true")
    i = sub.add_parser("image")
    i.add_argument("--build", action="store_true")
    u = sub.add_parser("usage")
    u.add_argument("since")
    a = ap.parse_args()
    if a.cmd == "status":
        status()
    elif a.cmd == "reap":
        reap()
    elif a.cmd == "teardown":
        teardown(a.all)
    elif a.cmd == "image":
        if a.build:
            print(ensure_image(True))
        else:
            have = named_snapshots()
            for name, snap, _ in layers():
                print(f"{name:6} {snap:28} {'ready' if have.get(snap, {}).get('status') == 'ready' else 'missing'}")
    elif a.cmd == "usage":
        tot = 0.0
        for i in Registry().read()["vms"]:
            with contextlib.suppress(Exception):
                d = bj("usage", i, "--since", a.since)
                tot += d["dollars"]
                print(i, d["seconds"], d["dollars"])
        print("total", round(tot, 5))
