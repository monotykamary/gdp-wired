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


class Unavailable(RuntimeError):
    """boat can't serve this batch (API, billing, limits, image): the caller may move it to Modal."""


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
# the ticks wait on the VM up to 20 s for a finish: their own, wider bound (a `boat` process holds about 12 MB)
_tick_sem = threading.BoundedSemaphore(int(os.environ.get("GDPW_BOAT_TICKS", "200")))


def boat(*args, timeout=120, check=True, stdin=None, sem=None) -> str:
    with sem or _sem:
        p = subprocess.run([BOAT, *args], capture_output=True, text=True, timeout=timeout, env=ENV, input=stdin)
    if check and p.returncode != 0:
        raise RuntimeError(f"boat {args[0]} failed ({p.returncode}): {(p.stderr or p.stdout)[-400:]}")
    return p.stdout


def bj(*args, timeout=120, check=True):
    return json.loads(boat(*args, "--json", timeout=timeout, check=check))


def exec_(vm: str, argv: list[str], timeout: int = 60, sem=None) -> dict:
    out = boat("exec", vm, "--timeout", str(timeout), "--json", "--", *argv, timeout=timeout + 60, check=False, sem=sem)
    try:
        return json.loads(out)
    except json.JSONDecodeError:
        return {"exitCode": -1, "stdout": "", "stderr": out[-400:], "success": False}


def exec_json(vm: str, argv: list[str], timeout: int = 60, tries: int = 4, sem=None):
    last = None
    for k in range(tries):
        r = exec_(vm, argv, timeout, sem)
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
sudo chown "$(id -un)" /smt /vamp /sv /opt/gdpw
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
    """The pool's snapshot; $GDPW_BOAT_IMAGE names another (a test of the fallback names one that doesn't exist)."""
    return os.environ.get("GDPW_BOAT_IMAGE") or layers()[-1][1]


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
        b64 = base64.b64encode(("set -ex\nexport DEBIAN_FRONTEND=noninteractive PATH=$HOME/.bun/bin:$HOME/.elan/bin:$HOME/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin\n" + script).encode()).decode()
        exec_json(vm, ["bash", "-c", 'rm -rf ~/.gdpw/build && mkdir -p ~/.gdpw/build && echo "$1" | base64 -d > ~/.gdpw/build/l.sh && (setsid nohup bash -c "bash ~/.gdpw/build/l.sh > ~/.gdpw/build/l.log 2>&1; echo \\$? > ~/.gdpw/build/l.rc" > /dev/null 2>&1 &) && echo "{}"', "_", b64])
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
        full = exec_(vm, ["bash", "-c", "tail -c 400000 ~/.gdpw/build/l.log"], 120).get("stdout", "")
        (LIVE / "builds").mkdir(parents=True, exist_ok=True)
        (LIVE / "builds" / f"{snap}.log").write_text(full)
        if rc != "0":
            raise RuntimeError(f"layer {name} failed ({rc}), its log in {LIVE / 'builds' / (snap + '.log')}:\n{out[-1500:]}")
        exec_(vm, ["bash", "-c", "sudo apt-get clean; rm -rf ~/.cache/pip ~/.gdpw/build; sync"], 120)
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
    if os.environ.get("GDPW_BOAT_IMAGE"):
        if have.get(image_name(), {}).get("status") != "ready":
            raise Unavailable(f"boat image {image_name()} doesn't exist")
        return image_name()
    chain = layers()
    parent = None
    for name, snap, script in chain:
        if snap not in have or have[snap].get("status") != "ready":
            if not build:
                raise Unavailable(f"boat image {chain[-1][1]} isn't built (layer {snap} missing): python3 modal/boat.py image --build")
            build_layer(name, snap, script, parent)
        parent = snap
    prune_snapshots({s for _, s, _ in chain}, chain[-1][1])
    return chain[-1][1]


def prune_snapshots(keep: set[str], current: str):
    """Named snapshots of superseded images (gdpw-*): every layer of the current image is kept, and the image before
    it (the registry's `images`, newest last), nothing older; the plan names 10 for free."""
    try:
        with Registry().locked() as d:
            imgs = [i for i in d.get("images", []) if i != current] + [current]
            d["images"] = imgs[-2:]
        keep = keep | set(imgs[-2:])
        for n in named_snapshots():
            if n.startswith("gdpw-") and n not in keep and n != "gdpw-base":
                boat("snapshot", "rm", n, "--json", check=False)
                log(f"removed superseded snapshot {n}")
    except Exception as e:
        log(f"(snapshot prune skipped: {e})")


def retire(d: dict, image: str):
    """Free VMs of an image neither current nor the one before: deleted (the toolchain changed)."""
    keep = set(d.get("images", [])[-2:]) | {image}
    old = [i for i, v in d["vms"].items() if lease_free(v) and v["snapshot"] not in keep]
    for i in old:
        d["vms"].pop(i)
        threading.Thread(target=boat, args=("delete", i, "--yes", "--json"), kwargs={"check": False}, daemon=False).start()
    if old:
        log(f"deleted {len(old)} VMs of superseded images")


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
    """Drops VMs boat no longer has, deletes those whose stopped disk expired (boat keeps it 14 days; the pool never
    counts on one), and records each one's state."""
    for i in list(d["vms"]):
        s = live.get(i)
        if not s or s.get("state") in ("deleted", "deleting"):
            d["vms"].pop(i)
        elif s.get("dataExpiredAt") or (s.get("state") in ("error", "stopped") and lease_free(d["vms"][i]) and not s.get("snapshotAvailable")):
            # (a stopped VM with no snapshot can't be resumed: boat stops a VM that young without one)
            d["vms"].pop(i)
            threading.Thread(target=boat, args=("delete", i, "--yes", "--json"), kwargs={"check": False}, daemon=False).start()
        else:
            d["vms"][i]["state"] = s.get("state")


REFRESH_DAYS = 12  # a VM stopped this long is resumed and stopped again when a batch runs, before boat drops its disk


def refresh_old(d: dict, image: str):
    """Free VMs stopped for REFRESH_DAYS: resumed and stopped again (in the background), which restarts boat's clock."""
    old = [i for i, v in d["vms"].items() if lease_free(v) and v.get("state") == "stopped" and time.time() - v.get("last_used", time.time()) > REFRESH_DAYS * 86400]

    def one(i):
        boat("resume", i, "--json", check=False, timeout=300)
        boat("stop", i, "--yes", "--json", check=False, timeout=300)
    for i in old:
        d["vms"][i]["last_used"] = time.time()
        threading.Thread(target=one, args=(i,), daemon=True).start()
    if old:
        log(f"refreshing {len(old)} VMs stopped over {REFRESH_DAYS} days")


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


def tree_tarball() -> bytes:
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:gz", compresslevel=6) as tf:
        for f in tree_files():
            tf.add(GDP / f, arcname=f, recursive=False)
    return buf.getvalue()


def olean_tarball(key: str) -> tuple[bytes | None, list[str]]:
    """The Lean library compiled for this key that an earlier batch brought back, for the VMs that lack it."""
    cache = LIVE / "olean" / key
    files = sorted(cache.glob("*.olean")) if cache.exists() else []
    if not files:
        return None, []
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:gz", compresslevel=6) as tf:
        for f in files:
            tf.add(f, arcname=f.name)
    return buf.getvalue(), [f.stem for f in files]


def library_key(lean_dir: pathlib.Path = GDP / "lean-kernel") -> str:
    h = hashlib.sha256(b"leanprover/lean4:v4.34.0\n")
    for mod in LIBRARY:
        h.update(mod.encode() + b"\0" + (lean_dir / f"{mod}.lean").read_bytes() + b"\0")
    return h.hexdigest()[:32]


# ------------------------------------------------------------------------------------------------------------- a batch
class StartGate:
    """boat's start limits (per minute, hour and day; a creation and a resume each one start), shared by a batch's
    resumes and creations: take(n) waits for the minute's room and grants up to n, 0 once the hour or the day is spent."""

    def __init__(self):
        self.lock = threading.Lock()
        self.t, self.used, self.st, self.room = 0.0, 0, None, 0

    def take(self, n: int, stop: threading.Event) -> int:
        while not stop.is_set():
            with self.lock:
                if time.time() - self.t > 5:
                    try:
                        lim = limits()
                        self.st, self.room = lim["starts"], lim["currentLimits"]["activeSandboxes"] - lim["activeSandboxes"]
                        self.t, self.used = time.time(), 0
                    except Exception:
                        pass
                if self.st:
                    left = min(self.st["hour"]["remaining"], self.st["day"]["remaining"]) - STARTS_RESERVE - self.used
                    if left <= 0:
                        return 0
                    k = min(n, left, self.st["minute"]["remaining"] - self.used)
                    if k > 0:
                        self.used += k
                        return k
            time.sleep(3)
        return 0


class VM:
    def __init__(self, id: str, type: str, how: str):
        self.id, self.type, self.how = id, type, how
        self.cpus = TYPES[type][0]
        self.slots = max(1, self.cpus // SLOT_CPU)
        self.t_request = time.time()
        self.t_running = None
        self.t_ready = None
        self.t_end = None
        self.src = ""
        self.busy: list[list[float]] = []  # [start, end] per item
        self.dead = False


class Session:
    """The VMs a batch holds: leased from the pool, resumed, or created, each prepared with the batch's tree."""

    def __init__(self, label: str, idle: int = 60, teardown: bool = False, vm_type: str = "default", build: bool = True, oleans: bool = True):
        self.batch = time.strftime("%Y%m%d-%H%M%S") + "-" + "".join(random.choice("abcdefghijklmnopqrstuvwxyz0123456789") for _ in range(6))
        self.label, self.idle, self.teardown, self.vm_type = label, idle, teardown, vm_type
        self.reg = Registry()
        self.image = ensure_image(build)  # (raises Unavailable when it's missing and build is off)
        self.key = library_key()
        self.tar = tree_tarball()
        self.olean, self.olean_names = olean_tarball(self.key) if oleans else (None, [])
        self.olean_url = None
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
        self.gate = StartGate()
        self.last_error = ""
        threading.Thread(target=self._heartbeat, daemon=True).start()
        log(f"batch {self.batch}: image {self.image}, tree {len(self.tar) // 1024} KB, library {self.key[:12]}"
            f" ({len(self.olean_names)} .olean here, {len(self.olean or b'') // 1024} KB, for VMs that lack them)")

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
            refresh_old(d, self.image)
            retire(d, self.image)
            free = [i for i, v in d["vms"].items() if v["snapshot"] == self.image and v["type"] == vm_type and lease_free(v) and i not in self.vms]
            free.sort(key=lambda i: (d["vms"][i].get("state") not in RUNNING, -d["vms"][i].get("last_used", 0)))
            up = [i for i in free if d["vms"][i].get("state") in RUNNING]
            try:  # a stopped VM takes a start to resume: no more of them than the plan has starts left
                st = limits()["starts"]
                starts = max(0, min(st["hour"]["remaining"], st["day"]["remaining"]) - STARTS_RESERVE)
            except Exception:
                starts = need
            free = up + [i for i in free if i not in up][:starts]
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
            if running:
                self.counts["leased_running"] += 1
                boat("extend", vm.id, "--ttl", str(BACKSTOP), "--json", check=False)
                up = wait_running([vm.id], 300)
            else:
                up = False
                attempt = 0
                while attempt < 3:
                    # a VM still stopping (the last batch just let it go) takes a resume only once it has stopped
                    for _ in range(60):
                        if states().get(vm.id, {}).get("state") not in ("stopping", "pausing", "snapshotting"):
                            break
                        time.sleep(3)
                    if not self.gate.take(1, self.stop):
                        raise RuntimeError("no boat starts left this hour or day (a resume is a start)")
                    with _sem:
                        p = subprocess.run([BOAT, "resume", vm.id, "--json"], capture_output=True, text=True, timeout=300, env=ENV)
                    said = p.stdout + p.stderr
                    if p.returncode != 0 and ("rate_limited" in said or '"status":429' in said):
                        if "per hour" in said or "per day" in said:
                            raise RuntimeError("boat's start limit (a resume counts as a start): " + said.split('"error":"')[-1][:120])
                        time.sleep(15)  # the minute's starts: the next minute
                        continue
                    attempt += 1
                    if p.returncode != 0 and "snapshot_data_expired" in said:
                        # a stopped disk boat no longer keeps (14 days): the VM goes, a new one from the image takes its place
                        log(f"{vm.id}: its stopped disk expired; a new VM instead")
                        boat("delete", vm.id, "--yes", "--json", check=False, timeout=180)
                        vm.dead = True
                        self._release([vm.id], deleted=True)
                        self._create(1, vm.type)
                        return
                    boat("extend", vm.id, "--ttl", str(BACKSTOP), "--json", check=False)
                    if wait_running([vm.id], 150):
                        up = True
                        break
                    log(f"{vm.id}: not up after resume ({said.strip()[-160:]}); again")
                self.counts["resumed"] += 1
            if not up:
                raise RuntimeError("never came up")
            vm.t_running = time.time()
            self._prepare(vm)
        except Exception as e:
            log(f"{vm.id}: {e}")
            self.last_error = f"{vm.id}: {str(e)[:200]}"
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
            room = min(lim["currentLimits"]["activeSandboxes"] - lim["activeSandboxes"], n)
            if not lim.get("canStart", True) or room <= 0:
                time.sleep(10)
                continue
            room = self.gate.take(room, self.stop)
            if room <= 0:
                log("no starts left this hour or day: no more VMs for this batch")
                break
            out = boat("new", "--from", self.image, "--type", vm_type, "--count", str(room), "--ttl", str(BACKSTOP), "--no-env", "--no-monitoring", "--json", timeout=600, check=False)
            ids = []
            for line in out.splitlines():
                with contextlib.suppress(Exception):
                    e = json.loads(line)
                    if e.get("id") and e["id"] not in ids and e.get("event") != "error":
                        ids.append(e["id"])
            if not ids:
                self.last_error = f"boat new: {out.strip()[-200:]}"
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
            vm.t_running = time.time()
            self._prepare(vm)
        except Exception as e:
            log(f"{vm.id}: {e}")
            self.last_error = f"{vm.id}: {str(e)[:200]}"
            vm.dead = True
            self._release([vm.id])

    def enough(self) -> bool:
        """Whether the run under way has slots for all it still has to start (no more VMs worth creating)."""
        f = getattr(self, "_enough", None)
        return bool(f and f())

    # -- preparing
    def _prepare(self, vm: VM):
        with self.cv:
            seed = self.seed_vm is None and self.wanted > 2
            if seed:
                self.seed_vm = vm
        src = f"/home/user/.gdpw/in-{self.batch}.tar.gz"
        if seed or self.wanted <= 2:
            try:
                if seed and self.olean:  # both files in one upload (each ssh session costs seconds to open)
                    buf = io.BytesIO()
                    with tarfile.open(fileobj=buf, mode="w") as tf:
                        for name, data in ((f"in-{self.batch}.tar.gz", self.tar), (f"olean-{self.batch}.tar.gz", self.olean)):
                            ti = tarfile.TarInfo(name)
                            ti.size = len(data)
                            tf.addfile(ti, io.BytesIO(data))
                    self._upload(vm, f"/home/user/.gdpw/bundle-{self.batch}.tar", buf.getvalue())
                    exec_json(vm.id, ["bash", "-c", f"cd ~/.gdpw && tar xf bundle-{self.batch}.tar && rm bundle-{self.batch}.tar && echo '{{}}'"], 60)
                else:
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
                if os.environ.get("GDPW_BOAT_VERBOSE"):
                    log(f"seed {vm.id}: {'serving' if self.seed_url else 'not serving'}")
        else:
            self.seed_done.wait(900)
            if self.seed_url:
                src = self.seed_url
            else:
                src = f"/home/user/.gdpw/in-{self.batch}.tar.gz"
                self._upload(vm, src)
        osrc = self.olean_url if (src == self.seed_url or vm is self.seed_vm) and self.olean_url else "-"
        r = self._agent(vm, ["prep", self.batch, src, self.key, osrc, ",".join(self.olean_names)], 600, ship=True)
        if not r.get("ok") and src == self.seed_url:  # the URL failed: straight from here
            log(f"{vm.id}: the seed's URL failed ({str(r.get('err'))[:200]}); the tree from here")
            src = f"/home/user/.gdpw/in-{self.batch}.tar.gz"
            self._upload(vm, src)
            r = self._agent(vm, ["prep", self.batch, src, self.key], 600, ship=True)
        if not r.get("ok"):
            raise RuntimeError(f"prep failed: {r}")
        if self.olean and set(self.olean_names) - set(r.get("olean", [])) - set(r.get("shipped", [])) and osrc == "-":
            dst = f"/home/user/.gdpw/olean-{self.batch}.tar.gz"
            if vm is not self.seed_vm:
                self._upload(vm, dst, self.olean)
            self._agent(vm, ["oleanin", self.key, dst], 120)
        vm.src = "seed" if src == self.seed_url else "direct"
        if os.environ.get("GDPW_BOAT_VERBOSE"):
            log(f"{vm.id} ({vm.how}) running after {round(vm.t_running - vm.t_request, 1)} s, prepared {round(time.time() - vm.t_running, 1)} s later ({vm.src})")
        vm.cpus = r.get("cpus") or vm.cpus
        vm.slots = max(1, vm.cpus // SLOT_CPU)
        vm.t_ready = time.time()
        with self.cv:
            self.ready.append(vm)
            self.cv.notify_all()

    def _agent(self, vm: VM, args: list[str], timeout: int = 60, ship: bool = False, tries: int = 4, sem=None):
        if ship:  # the agent itself, with the batch's first call to each VM
            return exec_json(vm.id, ["bash", "-c", 'mkdir -p ~/.gdpw && echo "$1" | base64 -d > ~/.gdpw/agent.py.new && mv ~/.gdpw/agent.py.new ~/.gdpw/agent.py && shift && exec python3 ~/.gdpw/agent.py "$@"', "_", self.agent_b64, *args], timeout, tries)
        return exec_json(vm.id, ["python3", "/home/user/.gdpw/agent.py", *args], timeout, tries, sem)

    def _upload(self, vm: VM, dst: str, data: bytes | None = None):
        data = self.tar if data is None else data
        err = ""
        for k in range(4):
            try:
                with _sem:
                    p = subprocess.run([BOAT, "ssh", vm.id, "--", f"mkdir -p ~/.gdpw && cat > {dst}.part && mv {dst}.part {dst} && wc -c < {dst}"], input=data, capture_output=True, timeout=600, env=ENV)
                if p.returncode == 0 and p.stdout.decode().strip().endswith(str(len(data))):
                    return
                err = p.stderr.decode()[-300:]
            except Exception as e:
                err = repr(e)
            time.sleep(2 + 3 * k)
        raise RuntimeError(f"upload to {vm.id} failed: {err}")

    def _serve(self, vm: VM):
        self.tok = "".join(random.choice("abcdefghijklmnopqrstuvwxyz0123456789") for _ in range(32))
        port = 8765
        exec_json(vm.id, ["bash", "-c", f"mkdir -p ~/.gdpw/srv/{self.tok} && cp ~/.gdpw/in-{self.batch}.tar.gz ~/.gdpw/srv/{self.tok}/tree.tar.gz"
                                        f" && {{ [ ! -f ~/.gdpw/olean-{self.batch}.tar.gz ] || mv ~/.gdpw/olean-{self.batch}.tar.gz ~/.gdpw/srv/{self.tok}/olean.tar.gz; }} && echo '{{}}'"], 60)
        self._agent(vm, ["serve", "/home/user/.gdpw/srv", str(port)], 60, ship=True)
        h = bj("host", vm.id, str(port), "--localhost", "--private")
        u = urllib.parse.urlparse(h["url"])
        self.seed_url = urllib.parse.urlunparse(u._replace(path=f"/{self.tok}/tree.tar.gz"))
        if self.olean:
            self.olean_url = urllib.parse.urlunparse(u._replace(path=f"/{self.tok}/olean.tar.gz"))
        # (the URL carries boat's token: it never goes to a log or a file)

    # -- running
    def run(self, items: list[dict], on_done, on_start=None, on_lost=None, max_wait: int = 0):
        """Runs items ({name, kind, weight, est, ...spec}) longest first over the session's VMs, as they come up.

        An item whose VM died (or whose runner vanished) runs again once on another VM; lost again, it goes to
        on_lost(item, reason) (else it's done with exit -1). With max_wait, if no VM is ready that many seconds after
        the start, or every VM is gone, what hasn't run goes to on_lost too."""
        queue = sorted(items, key=lambda it: -it.get("est", 60))
        lock = threading.Lock()
        left = {"n": len(items)}
        self._enough = lambda: len(queue) <= sum(v.slots for v in self.vms.values() if not v.dead)
        started_threads = set()
        all_done = threading.Event()
        t_start = time.time()
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

        def finish(it: dict, row: dict | None, lost_reason: str = ""):
            orig = {**it, "name": it.get("orig", it["name"])}
            try:
                if row is None:
                    if on_lost:
                        on_lost(orig, lost_reason)
                    else:
                        on_done(orig, {"name": orig["name"], "code": -1, "seconds": -1, "error": lost_reason})
                else:
                    on_done(orig, {**row, "name": orig["name"]})
            finally:
                with lock:
                    left["n"] -= 1
                    if left["n"] <= 0:
                        all_done.set()

        def lose(it: dict, reason: str):
            """Once more on another VM (under a name of its own there), then on_lost."""
            k = it.get("try", 0) + 1
            if k <= 1:
                with lock:
                    queue.insert(0, {**it, "try": k, "orig": it.get("orig", it["name"]), "name": f"{it.get('orig', it['name'])}~r{k}"})
                log(f"{it.get('orig', it['name'])}: {reason}; once more on boat")
            else:
                finish(it, None, reason)

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
                unsent += [{k: v for k, v in it.items() if k not in ("est", "weight", "vm_type", "meta", "try", "orig")} | {"cpus": it["weight"] * SLOT_CPU} for it in starts]
                msg = json.dumps({"start": unsent, "acks": acks, "wait": 20 if running else 0}).encode()
                b64 = base64.b64encode(msg).decode()
                parts = [b64[k:k + 100_000] for k in range(0, len(b64), 100_000)]
                try:
                    r = self._agent(vm, ["tick", self.batch, *parts], 60, tries=1, sem=_tick_sem)
                    fails = 0
                    acks, unsent = [], []
                except Exception as e:
                    fails += 1
                    log(f"{vm.id}: tick failed ({fails}): {str(e)[:200]}")
                    if fails >= 8:
                        vm.dead = True
                        log(f"{vm.id}: given up")
                        for name, (it, _) in list(running.items()):
                            lose(it, f"boat VM {vm.id} lost")
                        return
                    time.sleep(min(30, 3 * fails))
                    continue
                for row in r.get("done", []):
                    name = row["name"]
                    acks.append(name)
                    if name in running:
                        it, t = running.pop(name)
                        vm.busy.append([t, time.time()])
                        if row.get("lost"):
                            lose(it, f"its runner on {vm.id} vanished")
                        else:
                            finish(it, row)

        def spawn_workers():
            while not all_done.is_set() and not self.stop.is_set():
                with self.cv:
                    for vm in self.ready:
                        if vm.id not in started_threads:
                            started_threads.add(vm.id)
                            threading.Thread(target=worker, args=(vm,), daemon=True).start()
                    self.cv.wait(2)

        def give_up(reason: str):
            with lock:
                rest = list(queue)
                queue.clear()
            for it in rest:
                finish(it, None, reason)

        sp = threading.Thread(target=spawn_workers, daemon=True)
        sp.start()
        while not all_done.wait(1):
            if self.stop.is_set():
                raise KeyboardInterrupt
            gone = self.vms and all(v.dead for v in self.vms.values()) and not any(t.is_alive() for t in self.threads)
            if max_wait and not self.ready and time.time() - t_start > max_wait:
                give_up(f"no boat VM ready after {max_wait} s" + (f" ({self.last_error})" if self.last_error else ""))
                if not any(t.is_alive() for t in self.threads) or all_done.is_set():
                    break
            elif gone:
                if on_lost:
                    give_up("every boat VM lost" + (f" ({self.last_error})" if self.last_error else ""))
                else:
                    raise Unavailable("no VM left to run on" + (f" ({self.last_error})" if self.last_error else ""))
        all_done.wait(5)
        self._enough = None

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
        """The Lean library this batch compiled, from the VM that has the most of it, kept here so the next batch
        ships it to the VMs that lack it."""
        cache = LIVE / "olean" / self.key
        have = len(list(cache.glob("*.olean"))) if cache.exists() else 0
        if have == len(LIBRARY):
            return
        names: dict[str, list] = {}

        def ls(vm):
            with contextlib.suppress(Exception):
                names[vm.id] = self._agent(vm, ["oleans", self.key, "-"], 30, tries=1)["names"]
        ts = [threading.Thread(target=ls, args=(vm,)) for vm in self.ready if not vm.dead]
        [t.start() for t in ts]
        [t.join(60) for t in ts]
        if not names:
            return
        best = max(names, key=lambda i: len(names[i]))
        if len(names[best]) <= have:
            return
        vm = self.vms[best]
        try:
            first = self._agent(vm, ["oleans", self.key, "0"], 120)
            parts = [base64.b64decode(first["data"])]
            for k in range(1, first["parts"]):
                parts.append(base64.b64decode(self._agent(vm, ["oleans", self.key, str(k)], 120)["data"]))
            with tarfile.open(fileobj=io.BytesIO(b"".join(parts))) as tf:
                cache.mkdir(parents=True, exist_ok=True)
                tf.extractall(cache, filter="data")
            log(f"kept {len(names[best])} .olean files of library {self.key[:12]} from {vm.id}")
        except Exception as e:
            log(f"{vm.id}: oleans: {str(e)[:200]}")

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
        held = sum((v.t_end or time.time()) - v.t_request for v in vms if v.t_running)  # (a VM that never ran bills nothing)
        busy = sum(union(v.busy) for v in vms)
        ready_held = sum((v.t_end or time.time()) - v.t_ready for v in vms if v.t_ready)
        up = [v.t_running - v.t_request for v in vms if v.t_running]
        prep = [v.t_ready - v.t_running for v in vms if v.t_ready and v.t_running]
        return {"vms": len(vms), **self.counts, "to_running_s": [round(min(up), 1), round(sorted(up)[len(up) // 2], 1), round(max(up), 1)] if up else None,
                "prep_s": [round(min(prep), 1), round(sorted(prep)[len(prep) // 2], 1), round(max(prep), 1)] if prep else None,
                "tree_from_seed": sum(1 for v in vms if v.src == "seed"), "types": sorted({v.type for v in vms}), "held_s": round(held, 1), "ready_held_s": round(ready_held, 1),
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
        """What boat bills for this batch's VMs since it began (`boat usage`, every VM at once)."""
        return usage_since(ids or list(self.vms), self.t0 - 5)


def usage_since(ids: list[str], t: float) -> float:
    since = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t))
    got: list[float] = []

    def one(i):
        with contextlib.suppress(Exception):
            got.append(bj("usage", i, "--since", since)["dollars"])
    ts = [threading.Thread(target=one, args=(i,)) for i in ids]
    [x.start() for x in ts]
    [x.join(120) for x in ts]
    return round(sum(got), 5)


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
    W/(c n) + n/(2r), least at n = sqrt(2 r W / c). boat counts a resume as a start, as a creation is: only the pool's
    VMs still up (within their idle time) come without one."""
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
        up = sum(1 for v in Registry().read()["vms"].values() if lease_free(v) and v.get("state") in RUNNING)
        rate = max(lim["currentLimits"]["creationRatePerMinute"], 1) / 60
        by_rate = up + math.ceil(math.sqrt(2 * rate * W / slots_per_vm))
        room = lim["currentLimits"]["activeSandboxes"] - lim["activeSandboxes"] + up
        st = lim["starts"]
        starts = min(st["hour"]["remaining"], st["day"]["remaining"]) - STARTS_RESERVE
        n = min(useful, by_rate, room, up + max(0, starts))
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
def preflight(want: int = 1, vm_type: str = "default") -> tuple[str | None, dict]:
    """Can boat serve a batch now? None and what it can give, or the reason it can't: its API, the account's billing,
    the image, or no VM to be had (the pool's free VMs, and what the plan lets this batch start)."""
    try:
        lim = limits()
    except Exception as e:
        return f"boat API unreachable ({str(e)[:160]})", {}
    if lim.get("billingStatus") not in (None, "active") or lim.get("blockedReason") or lim.get("startBlockedReason") or not lim.get("canStart", True):
        return f"boat can't start VMs ({lim.get('billingStatus')}, {lim.get('blockedReason') or lim.get('startBlockedReason')})", {}
    if not lim.get("unlimited") and lim.get("creditBalanceSeconds", 1) <= 0 and lim.get("packBalanceSeconds", 0) <= 0:
        return "boat credit used up", {}
    img = image_name()
    try:
        snap = named_snapshots().get(img)
    except Exception as e:
        return f"boat API unreachable ({str(e)[:160]})", {}
    if not snap or snap.get("status") != "ready":
        return f"boat image {img} isn't there (python3 modal/boat.py image --build)", {}
    try:
        with Registry().locked() as d:
            reconcile(d, sandboxes())
            free = [v for v in d["vms"].values() if v["snapshot"] == img and v["type"] == vm_type and lease_free(v)]
    except Exception as e:
        return f"boat API unreachable ({str(e)[:160]})", {}
    up = sum(1 for v in free if v.get("state") in RUNNING)
    room = lim["currentLimits"]["activeSandboxes"] - lim["activeSandboxes"]
    st = lim["starts"]
    starts = max(0, min(st["minute"]["remaining"], st["hour"]["remaining"] - STARTS_RESERVE, st["day"]["remaining"] - STARTS_RESERVE))
    # (a resume is a start to boat, as a creation is)
    resumable = min(len(free) - up, max(0, room), starts)
    creatable = min(starts - resumable, max(0, room - resumable))
    can = up + resumable + creatable
    info = {"free_up": up, "free_stopped": len(free) - up, "active_room": room, "starts_now": starts, "can": can}
    if can <= 0:
        why = "boat at its active-VM limit" if room <= 0 else "no boat starts left this hour or day" if starts <= 0 else "no boat VM to be had"
        return why, info
    return None, info


def job_items(spec: list[dict], pre: str, cmd, vm_type: str, past: dict) -> tuple[list[dict], list[str]]:
    """modal/run.py's jobs as items, in its summary's order (its resource groups, in the order they first appear)."""
    med = sorted(past.values())[len(past) // 2] if past else 60
    cap_slots = TYPES[vm_type][0] // SLOT_CPU
    items, order = [], []
    groups: dict[tuple, list] = {}
    for j in spec:
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
    return items, order


def boat_jobs(spec: list[dict], out: str, pre: str, cmd, vms: int = 0, idle: int = 60, teardown: bool = False, durations: str = "", vm_type: str = "default",
              max_vms: int = 0, on_lost=None, max_wait: int = 0, on_done=None) -> tuple[dict, dict]:
    """modal/run.py's jobs on the pool: {name: {code, seconds, out, err}} for those that ran, and the batch's figures.
    A job lost twice (its VM died) goes to on_lost(name, reason), as does every job when boat can't serve the batch."""
    outdir = pathlib.Path(out)
    past = last_durations(outdir, {j["name"] for j in spec}, durations)
    items, order = job_items(spec, pre, cmd, vm_type, past)
    cap_slots = TYPES[vm_type][0] // SLOT_CPU
    rows: dict[str, dict] = {}
    sess = None
    summary = {}
    try:
        with signals_as_interrupt():
            sess = Session(f"run.py {outdir.name}", idle=idle, teardown=teardown, vm_type=vm_type, build=on_lost is None)
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
                if on_done:
                    on_done(it["name"], row)
            t_run = time.time()
            sess.run(items, done, on_lost=(lambda it, why: on_lost(it["name"], why)) if on_lost else None, max_wait=max_wait)
            t_jobs = time.time()
            logs = sess.collect()
            t_logs = time.time()
            for name in list(rows):
                lg = logs.get(name, {})
                for k in range(1, 3):  # a job that ran again: its last run's logs
                    lg = logs.get(f"{name}~r{k}", lg)
                o, e = lg.get("out", ""), lg.get("err", "")
                if rows[name].get("error"):
                    e += ("\n" if e else "") + str(rows[name]["error"])
                rows[name].update(out=o, err=e)
            sess.harvest_oleans()
            sess.phases = {"jobs_s": round(t_jobs - t_run, 1), "collect_s": round(t_logs - t_jobs, 1), "harvest_s": round(time.time() - t_logs, 1)}
    except Unavailable as e:
        if on_lost is None:
            raise
        for it in items:
            if it["name"] not in rows:
                on_lost(it["name"], str(e))
    finally:
        if sess:
            t_close = time.time()
            summary = sess.close()
            summary["phases"] = {**getattr(sess, "phases", {}), "close_s": round(time.time() - t_close, 1)}
            summary["dollars_so_far"] = sess.dollars()
            summary["batch"] = sess.batch
            summary["image"] = sess.image
    return rows, summary


def summary_line(s: dict) -> str:
    return (f"boat: {s['vms']} VMs ({s['created']} created, {s['resumed']} resumed, {s['leased_running']} already up), ${s['dollars_so_far']} so far (boat usage), "
            f"{s['idle_vm_s']} idle VM-s of {s['ready_held_s']} held ready, {s['bring_up_s']} VM-s bringing up"
            + (f", then up to {s['idle_tail_s']} VM-s idle before they stop" if s.get("idle_tail_s") else ""))


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


def teardown(everything: bool = False, vm_type: str = ""):
    """Deletes the pool's free VMs that come from an older image (all free VMs with --all, or all of a --type)."""
    img = image_name()
    gone = []
    with Registry().locked() as d:
        reconcile(d, sandboxes())
        for i, v in list(d["vms"].items()):
            if lease_free(v) and (everything or v["snapshot"] != img or v["type"] == vm_type):
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
    t.add_argument("--type", default="", choices=["", "small", "default", "large"])
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
        teardown(a.all, a.type)
    elif a.cmd == "image":
        if a.build:
            with signals_as_interrupt():
                print(ensure_image(True))
        else:
            have = named_snapshots()
            for name, snap, _ in layers():
                print(f"{name:6} {snap:28} {'ready' if have.get(snap, {}).get('status') == 'ready' else 'missing'}")
    elif a.cmd == "usage":  # every pool VM's dollars since a time (ISO 8601 UTC)
        import datetime
        t = datetime.datetime.fromisoformat(a.since.replace("Z", "+00:00")).timestamp()
        ids = list(Registry().read()["vms"])
        print(f"{len(ids)} VMs, ${usage_since(ids, t)} since {a.since}")
