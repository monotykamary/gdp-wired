"""The VM side of modal/boat.py: one file, the Python standard library only, sent to every boat VM it leases.

    python3 agent.py prep <batch> <tree source> <library key>   unpack a batch's tree (a URL or a file), drop older batches
    python3 agent.py tick <batch> <base64 JSON, in parts>       start items, ack reported ones, wait (<= 25 s) for a finish
    python3 agent.py kill <batch>                               kill every running item of the batch
    python3 agent.py collect <batch> <part>                     the batch's logs, as base64 tar.gz parts of 5 MB
    python3 agent.py oleans <key>                               the VM's compiled Lean library for a key, base64 tar.gz
    python3 agent.py run <batch> <name>                         (internal) one item, detached

An item runs in a mount namespace of its own: a private /tmp, its own /work (a fresh copy of the batch's tree at
/work/gdp-wired for a shell job, as on Modal), the batch's tree read-only at /src/gdp-wired (for the compare runners,
which copy it to /work themselves) and the mounts its runner names (/bench); then as the VM's user on its own CPUs
(`taskset`, so `nproc` is the job's share), under `timeout -s KILL`. A shell job gets the Lean library's .olean files
from the VM's cache before it runs and saves the ones it compiled. A Python item (`py`) imports a Modal runner with the
stub below as `modal` (each decorator gives the function back) and calls one of its functions.
"""
import base64
import io
import json
import os
import pathlib
import shutil
import signal
import subprocess
import sys
import tarfile
import time

ROOT = pathlib.Path.home() / ".gdpw"
LIBRARY = ["Cert", "Kernel", "Cyclic", "Progress", "StepLaw", "Steps", "Sets", "History", "Live", "Ghost", "Refine", "Bridge", "BridgeRules", "Data"]
HOME = str(pathlib.Path.home())
PATH = f"{HOME}/.bun/bin:{HOME}/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
MOUNTPOINTS = ["/work", "/src/gdp-wired", "/bench", "/smt", "/vamp", "/sv"]


# ---------------------------------------------------------------------------------------------------------------- stub
class _Any:
    """Whatever a Modal image or volume definition chains (`.apt_install(...).run_commands(...)`): nothing."""

    def __init__(self, *a, **k):
        pass

    def __getattr__(self, name):
        return _Any()

    def __call__(self, *a, **k):
        return _Any()


class _App(_Any):
    app_id = None

    def function(self, *a, **k):
        return lambda f: f

    def local_entrypoint(self, *a, **k):
        return lambda f: f

    def cls(self, *a, **k):
        return lambda c: c


def modal_stub():
    import types
    m = types.ModuleType("modal")
    m.__gdpw_stub__ = True
    m.App = _App
    m.Image = _Any()
    m.Volume = _Any()
    m.Secret = _Any()
    m.Mount = _Any()
    m.gpu = _Any()
    return m


def import_runner(path: str):
    import importlib.util
    sys.modules.setdefault("modal", modal_stub())
    spec = importlib.util.spec_from_file_location(pathlib.Path(path).stem, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# -------------------------------------------------------------------------------------------------------------- helpers
def batch_dir(batch: str) -> pathlib.Path:
    return ROOT / "b" / batch


def sudo(*cmd, check=True):
    return subprocess.run(["sudo", "-n", *cmd], check=check, capture_output=True, text=True)


def write_json(p: pathlib.Path, obj):
    tmp = p.with_name(p.name + ".tmp")
    tmp.write_text(json.dumps(obj))
    tmp.rename(p)


def alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    st = pathlib.Path(f"/proc/{pid}/stat")
    try:
        return st.read_text().split(") ")[1].split()[0] != "Z"
    except Exception:
        return False


def descendants(pid: int) -> list[int]:
    kids: dict[int, list[int]] = {}
    for p in pathlib.Path("/proc").iterdir():
        if p.name.isdigit():
            try:
                ppid = int((p / "stat").read_text().split(") ")[1].split()[1])
            except Exception:
                continue
            kids.setdefault(ppid, []).append(int(p.name))
    out, todo = [], [pid]
    while todo:
        q = todo.pop()
        for c in kids.get(q, []):
            out.append(c)
            todo.append(c)
    return out


def kill_tree(pid: int):
    pids = [pid, *descendants(pid)]
    sudo("kill", "-KILL", *map(str, pids), check=False)


# ----------------------------------------------------------------------------------------------------------------- prep
def fetch(source: str, dst: pathlib.Path, jar: pathlib.Path) -> str:
    """A file from a boat host URL (its token sets a cookie on the first response, then redirects) or a local path."""
    if source.startswith("https://"):
        # (HTTP/1.1: many VMs at once through boat's HTTP/2 front broke streams)
        p = subprocess.run(["curl", "-sSfL", "--http1.1", "--retry", "5", "--retry-all-errors", "--retry-delay", "1", "-c", str(jar), "-b", str(jar), "-o", str(dst), source],
                           capture_output=True, text=True, timeout=300)
        return "" if p.returncode == 0 else "download failed: " + p.stderr[-300:]
    shutil.move(source, dst)
    return ""


def olean_in(key: str, tar: pathlib.Path) -> list[str]:
    """The Lean library's .olean files for a key, into this VM's cache (each written whole, then renamed in)."""
    cache = ROOT / "olean" / key
    cache.mkdir(parents=True, exist_ok=True)
    got = []
    with tarfile.open(tar) as tf:
        for m in tf.getmembers():
            name = pathlib.Path(m.name).name
            if name.endswith(".olean") and not (cache / name).exists():
                data = tf.extractfile(m).read()
                (cache / f".{name}.in").write_bytes(data)
                (cache / f".{name}.in").rename(cache / name)
                got.append(name[:-6])
    tar.unlink()
    return got


def oleanin(key: str, path: str):
    print(json.dumps({"ok": True, "got": olean_in(key, pathlib.Path(path))}))


def prep(batch: str, source: str, key: str, olean_src: str = "-", names: str = ""):
    t0 = time.time()
    for old in (ROOT / "b").glob("*") if (ROOT / "b").exists() else []:
        if old.name != batch:
            for j in old.glob("jobs/*/pid"):
                try:
                    kill_tree(int(j.read_text()))
                except Exception:
                    pass
            sudo("rm", "-rf", str(old), check=False)
    d = batch_dir(batch)
    tree = d / "tree"
    if (d / "ready").exists():
        print(json.dumps({"ok": True, "again": True}))
        return
    sudo("mkdir", "-p", *MOUNTPOINTS)
    if tree.exists():
        shutil.rmtree(tree)
    tree.mkdir(parents=True)
    (d / "jobs").mkdir(exist_ok=True)
    tar = d / "tree.tar.gz"
    err = fetch(source, tar, d / "cookies")
    if err:
        print(json.dumps({"ok": False, "err": err}))
        return
    with tarfile.open(tar) as tf:
        tf.extractall(tree, filter="tar")
    tar.unlink()
    # the Lean library the client has for this key, fetched only when this VM's cache lacks some of it
    got = []
    cache = ROOT / "olean" / key
    if olean_src != "-" and any(not (cache / f"{n}.olean").exists() for n in names.split(",") if n):
        if not fetch(olean_src, d / "olean.tar.gz", d / "cookies"):
            got = olean_in(key, d / "olean.tar.gz")
    (d / "key").write_text(key)
    (d / "ready").write_text(str(time.time()))
    have = sorted(f.stem for f in (ROOT / "olean" / key).glob("*.olean")) if (ROOT / "olean" / key).exists() else []
    print(json.dumps({"ok": True, "seconds": round(time.time() - t0, 2), "olean": have, "shipped": got, "cpus": os.cpu_count()}))


def serve(directory: str, port: int):
    """A file server for the other VMs (behind boat's token-gated URL), detached."""
    subprocess.Popen(["python3", "-m", "http.server", str(port), "--bind", "127.0.0.1", "--directory", directory],
                     stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
    print(json.dumps({"ok": True}))


# ----------------------------------------------------------------------------------------------------------------- tick
def cpus_in_use(d: pathlib.Path) -> set[int]:
    used = set()
    for j in (d / "jobs").iterdir():
        if (j / "spec.json").exists() and not (j / "done.json").exists() and not (j / "acked.json").exists():
            try:
                used |= set(json.loads((j / "cpus").read_text()))
            except Exception:
                pass
    return used


def start(d: pathlib.Path, spec: dict):
    j = d / "jobs" / spec["name"]
    if j.exists():  # a start the client sent again (its first tick's answer was lost)
        return
    j.mkdir(parents=True)
    n = os.cpu_count() or 1
    want = min(n, max(1, int(spec.get("cpus", 2))))
    used = cpus_in_use(d)
    free = [c for c in range(n) if c not in used]
    cpus = free[:want] if len(free) >= want else list(range(n))[:want]
    (j / "cpus").write_text(json.dumps(cpus))
    write_json(j / "spec.json", spec)
    p = subprocess.Popen([sys.executable, __file__, "run", d.name, spec["name"]], stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                         stderr=open(j / "agent.err", "w"), start_new_session=True, close_fds=True)
    (j / "pid").write_text(str(p.pid))


def report(d: pathlib.Path) -> tuple[list, list]:
    done, running = [], []
    for j in sorted((d / "jobs").iterdir()):
        if (j / "acked.json").exists():
            continue
        if (j / "done.json").exists():
            done.append(json.loads((j / "done.json").read_text()))
        elif (j / "pid").exists():
            if alive(int((j / "pid").read_text())):
                running.append(j.name)
            elif not (j / "done.json").exists():  # the runner died without a word
                time.sleep(0.2)
                if not (j / "done.json").exists():
                    err = (j / "agent.err").read_text()[-2000:] if (j / "agent.err").exists() else ""
                    write_json(j / "done.json", {"name": j.name, "code": -1, "seconds": -1, "lost": True, "err": err})
                    done.append(json.loads((j / "done.json").read_text()))
    return done, running


def tick(batch: str, *parts: str):
    d = batch_dir(batch)
    msg = json.loads(base64.b64decode("".join(parts))) if parts and parts[0] != "-" else {}
    for name in msg.get("acks", []):
        j = d / "jobs" / name
        if (j / "done.json").exists():
            (j / "done.json").rename(j / "acked.json")
    for spec in msg.get("start", []):
        start(d, spec)
    wait = float(msg.get("wait", 25))
    t0 = time.time()
    while True:
        done, running = report(d)
        if done or not running or time.time() - t0 >= wait:
            break
        time.sleep(0.25)
    load = os.getloadavg()[0]
    print(json.dumps({"done": done, "running": running, "load": load}))


def kill(batch: str):
    d = batch_dir(batch)
    n = 0
    if (d / "jobs").exists():
        for j in (d / "jobs").iterdir():
            if (j / "pid").exists() and not (j / "done.json").exists() and not (j / "acked.json").exists():
                kill_tree(int((j / "pid").read_text()))
                n += 1
    print(json.dumps({"killed": n}))


# ------------------------------------------------------------------------------------------------------------------ run
def wrap(j: pathlib.Path, spec: dict, work: pathlib.Path, tree: pathlib.Path, cwd: str, argv: list[str]) -> list[str]:
    tmp = j / "tmp"
    tmp.mkdir(exist_ok=True)
    binds = [(str(tmp), "/tmp"), (str(work), "/work"), (str(tree), "/src/gdp-wired")]
    binds += [(src, dst) for dst, src in spec.get("mounts", {}).items()]
    lines = ["set -e"] + [f"mount --bind {json.dumps(s)} {json.dumps(t)}" for s, t in binds]
    # a directory a tool writes into (as root on Modal, each in its own container): a private overlay per item
    for k, o in enumerate(spec.get("overlays", [])):
        up, wk = j / f"ov{k}" / "up", j / f"ov{k}" / "work"
        up.mkdir(parents=True, exist_ok=True)
        wk.mkdir(parents=True, exist_ok=True)
        lines.append(f"mount -t overlay overlay -o lowerdir={o},upperdir={up},workdir={wk} {o}")
    lines.append(f"mount -o remount,bind,ro /src/gdp-wired")
    lines.append(f"cd {json.dumps(cwd)}")
    lines.append('exec "$@"')
    (j / "ns.sh").write_text("\n".join(lines) + "\n")
    path = ":".join([*spec.get("path", []), PATH])
    env = ["env", "-i", f"PATH={path}", f"HOME={HOME}", "USER=user", "LOGNAME=user", "SHELL=/bin/bash", "LANG=C.UTF-8", *[f"{k}={v}" for k, v in spec.get("env", {}).items()]]
    cpus = ",".join(map(str, json.loads((j / "cpus").read_text())))
    return ["sudo", "-n", "unshare", "-m", "--propagation", "private", "--", "sh", str(j / "ns.sh"),
            "setpriv", f"--reuid={os.getuid()}", f"--regid={os.getgid()}", "--init-groups", "--",
            *env, "taskset", "-c", cpus, "timeout", "-s", "KILL", str(int(spec["limit"])), *argv]


def run(batch: str, name: str):
    d = batch_dir(batch)
    j = d / "jobs" / name
    spec = json.loads((j / "spec.json").read_text())
    tree = d / "tree"
    key = (d / "key").read_text().strip() if (d / "key").exists() else ""
    work = j / "work"
    work.mkdir()
    row: dict = {"name": name}
    try:
        if spec["kind"] == "sh":
            subprocess.run(["cp", "-a", str(tree), str(work / "gdp-wired")], check=True)
            lean_dir = work / "gdp-wired" / "lean-kernel"
            cache = ROOT / "olean" / key
            had = {f.name for f in cache.glob("*.olean")} if key and cache.exists() else set()
            for f in had:
                shutil.copy2(cache / f, lean_dir / f)
            argv = wrap(j, spec, work, tree, f"/work/gdp-wired/{spec.get('cwd', '.')}", ["bash", "-c", spec["cmd"]])
            t0 = time.time()
            with open(j / "out", "wb") as out, open(j / "err", "wb") as err:
                p = subprocess.run(argv, stdout=out, stderr=err, stdin=subprocess.DEVNULL)
            secs = round(time.time() - t0, 2)
            code = p.returncode
            if code in (137, -9) and secs >= spec["limit"] - 1:  # as modal/run.py reports its own limit
                code = 124
                (j / "err").write_text(f"timed out after {spec['limit']} s")
            row.update(code=code, seconds=secs)
            # save the library files this job compiled and the cache lacks (each written whole, then renamed in)
            if key:
                new = [m for m in LIBRARY if f"{m}.olean" not in had and (lean_dir / f"{m}.olean").exists()]
                if new:
                    cache.mkdir(parents=True, exist_ok=True)
                    for m in new:
                        tmp = cache / f".{m}.olean.{name}"
                        shutil.copy2(lean_dir / f"{m}.olean", tmp)
                        tmp.rename(cache / f"{m}.olean")
                    row["saved"] = new
        else:  # py: a function of a Modal runner, its arguments and result as JSON
            (j / "args.json").write_text(json.dumps(spec["args"]))
            argv = wrap(j, spec, work, tree, "/", ["python3", "-I", f"{ROOT}/agent.py", "call", f"/src/gdp-wired/{spec['module']}", spec["fn"], str(j / "args.json"), str(j / "result.json")])
            t0 = time.time()
            with open(j / "out", "wb") as out, open(j / "err", "wb") as err:
                p = subprocess.run(argv, stdout=out, stderr=err, stdin=subprocess.DEVNULL)
            row.update(code=p.returncode, seconds=round(time.time() - t0, 2))
            if (j / "result.json").exists():
                row["result"] = json.loads((j / "result.json").read_text())
            else:
                row["error"] = ((j / "err").read_bytes()[-3000:].decode("utf-8", "replace") or f"exit {p.returncode}")
    except Exception as e:
        row.update(code=-1, seconds=-1, error=repr(e))
    finally:
        sudo("rm", "-rf", str(work), str(j / "tmp"), *map(str, j.glob("ov*")), check=False)
        write_json(j / "done.json", row)


def call(module: str, fn: str, args_file: str, out_file: str):
    os.chdir("/work") if os.path.isdir("/work") else None
    sys.path.insert(0, str(pathlib.Path(module).parent))
    mod = import_runner(module)
    args = json.loads(pathlib.Path(args_file).read_text())
    res = getattr(mod, fn)(*args) if isinstance(args, list) else getattr(mod, fn)(**args)
    pathlib.Path(out_file).write_text(json.dumps(res))


# -------------------------------------------------------------------------------------------------------------- collect
def collect(batch: str, part: str):
    d = batch_dir(batch)
    blob = d / "logs.tar.gz"
    if part == "0" or not blob.exists():
        buf = io.BytesIO()
        with tarfile.open(fileobj=buf, mode="w:gz") as tf:
            for j in sorted((d / "jobs").iterdir()) if (d / "jobs").exists() else []:
                for f, cap in (("out", 400_000), ("err", 100_000)):
                    p = j / f
                    if p.exists():
                        data = p.read_bytes()
                        data = data[-cap:] if len(data) > cap else data
                        ti = tarfile.TarInfo(f"{j.name}/{f}")
                        ti.size = len(data)
                        tf.addfile(ti, io.BytesIO(data))
        blob.write_bytes(buf.getvalue())
    data = blob.read_bytes()
    size = 5_000_000
    k = int(part)
    print(json.dumps({"parts": max(1, -(-len(data) // size)), "data": base64.b64encode(data[k * size:(k + 1) * size]).decode()}))


def oleans(key: str, part: str = "-"):
    """The VM's compiled Lean library for a key: its names (part "-"), or base64 tar.gz parts of 5 MB."""
    cache = ROOT / "olean" / key
    files = sorted(cache.glob("*.olean")) if cache.exists() else []
    if part == "-":
        print(json.dumps({"names": [f.stem for f in files]}))
        return
    blob = ROOT / f"oleans-{key}.tar.gz"
    if part == "0" or not blob.exists():
        buf = io.BytesIO()
        with tarfile.open(fileobj=buf, mode="w:gz") as tf:
            for f in files:
                tf.add(f, arcname=f.name)
        blob.write_bytes(buf.getvalue())
    data = blob.read_bytes()
    size, k = 5_000_000, int(part)
    print(json.dumps({"parts": max(1, -(-len(data) // size)), "data": base64.b64encode(data[k * size:(k + 1) * size]).decode()}))


if __name__ == "__main__":
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    cmd, *rest = sys.argv[1:]
    {"prep": prep, "oleanin": oleanin, "tick": tick, "kill": kill, "run": run, "call": call, "collect": collect, "oleans": oleans,
     "serve": lambda d, p: serve(d, int(p))}[cmd](*rest)
