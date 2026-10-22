"""One interface over three providers: boat.dev VMs for CPU work (modal/boat.py), RunPod pods for GPU work
(modal/runpod.py), Modal for the rest and as the fallback of both.

    --backend modal     Modal, as always (the default until it's flipped)
    --backend auto      CPU work on boat, GPU work on RunPod; Modal takes over when the primary can't serve
    --backend boat | runpod                   force one, no fallback

Fallback is per batch where it can be (the whole batch moves before anything starts) and per job when a VM or pod dies
under it (that job once more on the primary, then on Modal). The reasons: the provider's API unreachable or erroring,
its billing (credit, balance), no capacity (boat's active-VM or start limits leaving no VM within --max-wait, a pool
image that isn't built; RunPod out of every GPU type in the list), a VM or pod lost mid-job. Every fallback is logged
with its reason, in the final line and in <out>/backends.json; a job's results are the same whichever provider ran it.
Whatever happens, each provider's cleanup runs: boat VMs released (stopped after --idle), pods deleted, the Modal app
stopped (its id and this client's pid in modal/.live/ while it runs).

The compare runners write their entrypoint's body as `run(ex, ...)` with `ex.remote(fn, *args)` and
`ex.starmap(fn, args)` (results as they finish, an exception for a failed call); `python3 <runner> --backend ...`
gives it the right `ex` (`fanout.cli`), and `modal run <runner>` still runs it on Modal.
"""
import contextlib
import inspect
import json
import os
import pathlib
import queue
import shutil
import sys
import threading
import time

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent
sys.path.insert(0, str(HERE))
BACKENDS = ["modal", "auto", "boat", "runpod"]


def log(*a):
    print("[backend]", *a, file=sys.stderr, flush=True)


def fname(fn) -> str:
    for get in (lambda: fn.__name__, lambda: fn._tag_, lambda: fn.get_raw_f().__name__, lambda: fn.info().function_name):
        try:
            n = get()
            if n:
                return n.split(".")[-1]
        except Exception:
            pass
    raise ValueError(f"can't name {fn!r}")


# ------------------------------------------------------------------------------------------------------------- Modal
def modal_real() -> bool:
    m = sys.modules.get("modal")
    return m is not None and not getattr(m, "__gdpw_stub__", False)


def reexec_with_modal():
    """Plain python3 without the Modal client: run again under the interpreter the `modal` CLI uses, so Modal can take
    over a batch. (Without one, Modal is simply not a fallback.)"""
    if modal_real() or os.environ.get("GDPW_REEXEC"):
        return
    exe = shutil.which("modal")
    if not exe:
        return
    with contextlib.suppress(Exception):
        first = pathlib.Path(exe).read_text(errors="replace").splitlines()[0]
        py = first[2:].strip().split()[0] if first.startswith("#!") else ""
        # (a venv's python is often a symlink to the same interpreter: compare the paths, not what they resolve to)
        if py and os.path.exists(py) and os.path.abspath(py) != os.path.abspath(sys.executable):
            os.environ["GDPW_REEXEC"] = "1"
            os.execv(py, [py, *sys.argv])


class ModalCtx:
    """The runner's Modal app, running: the one `modal run` started, or one started here (and stopped on exit), its
    id and this client's pid in modal/.live/ while it runs (modal/reap.sh stops it if this client dies)."""

    def __init__(self, app):
        self.app, self.ctx, self.ticket = app, None, None

    def __enter__(self):
        if not modal_real():
            raise RuntimeError("the Modal client isn't installed here, so Modal can't take this over")
        if getattr(self.app, "app_id", None) is None:
            self.ctx = self.app.run()
            self.ctx.__enter__()
        live = GDP / "modal" / ".live"
        live.mkdir(exist_ok=True)
        self.ticket = live / f"{self.app.app_id}"
        self.ticket.write_text(str(os.getpid()))
        if self.ctx:
            log(f"Modal app {self.app.app_id}")
        return self

    def __exit__(self, *exc):
        if self.ticket:
            self.ticket.unlink(missing_ok=True)
        if self.ctx:
            self.ctx.__exit__(*exc)
        return False


# ------------------------------------------------------------------------------------------------- modal/run.py jobs
def run_jobs(app, spec: list[dict], out: str, pre: str, cmd, modal_jobs, backend: str = "modal", vms: int = 0, idle: int = 60, teardown: bool = False,
             durations: str = "", vm_type: str = "default", max_vms: int = 0, max_wait: int = 120):
    """modal/run.py's batch on its backend. modal_jobs(jobs, on_done) runs jobs on Modal (inside the running app)
    and returns {name: {code, seconds, out, err}}. Writes <out>/<name>.log and <out>/summary.tsv (name, exit,
    seconds, backend) and prints modal/run.py's final line, with where the jobs ran and why any moved."""
    if backend not in ("modal", "auto", "boat"):
        raise SystemExit(f"--backend for CPU jobs is modal, auto or boat, not {backend}")
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    rows: dict[str, dict] = {}
    where: dict[str, str] = {}
    moved: dict[str, str] = {}  # job -> why it went to Modal
    bsum = None
    lock = threading.Lock()

    def printer(name, row):
        with lock:
            print(f"{name:40} exit {row.get('code', -1):>3}  {row.get('seconds', -1):>8} s", flush=True)

    todo = list(spec)
    if backend in ("auto", "boat"):
        import boat
        reason, info = boat.preflight(1, vm_type) if backend == "auto" else (None, {})
        if reason is None:
            got, bsum = boat.boat_jobs(spec, out, pre, cmd, vms=vms, idle=idle, teardown=teardown, durations=durations, vm_type=vm_type, max_vms=max_vms,
                                       on_lost=(lambda n, why: moved.__setitem__(n, why)) if backend == "auto" else None, max_wait=max_wait if backend == "auto" else 0, on_done=printer)
            rows.update(got)
            where.update({n: "boat" for n in got})
        else:
            moved.update({j["name"]: reason for j in spec})
            log(f"boat can't take this batch ({reason}): Modal runs it")
        todo = [j for j in spec if j["name"] not in rows]
        if backend == "boat":
            for j in todo:
                rows[j["name"]] = {"code": -1, "seconds": -1, "out": "", "err": moved.get(j["name"], "never ran")}
                where[j["name"]] = "boat"
            todo = []
    if todo:
        with ModalCtx(app):
            got = modal_jobs(todo, printer)
        rows.update(got)
        where.update({n: "modal" for n in got})
    order = [j["name"] for j in boat_order(spec)]
    for name in order:
        r = rows.get(name, {"code": -1, "seconds": -1, "out": "", "err": "never ran"})
        (outdir / f"{name}.log").write_text(r.get("out", "") + ("\n--- stderr ---\n" + r.get("err", "") if r.get("err", "").strip() else ""))
    (outdir / "summary.tsv").write_text("".join(f"{n}\t{rows.get(n, {}).get('code', -1)}\t{rows.get(n, {}).get('seconds', -1)}\t{where.get(n, '-')}\n" for n in order))
    wall = round(time.time() - t0, 1)
    done = [rows.get(n, {"code": -1, "seconds": -1}) for n in order]
    line = f"{len(done)} jobs, {sum(r.get('code', -1) != 0 for r in done)} failed, {wall} s wall, {round(sum(max(r.get('seconds', 0), 0) for r in done), 1)} s of job time"
    tail, why = where_line(where, moved)
    print(line + (f"; {tail}" if backend != "modal" else ""))
    if bsum:
        import boat
        print(boat.summary_line(bsum))
    (outdir / "backends.json").write_text(json.dumps({"backend": backend, "wall_s": wall, "where": count(where), "fallbacks": why, "boat": bsum}, indent=1))


def boat_order(spec):
    """modal/run.py's summary order: its resource groups, in the order they first appear."""
    groups: dict[tuple, list] = {}
    for j in spec:
        groups.setdefault((j.get("cpu", 2.0), j.get("memory", 4096), j.get("timeout", 900)), []).append(j)
    return [j for js in groups.values() for j in js]


def count(where: dict) -> dict:
    c: dict[str, int] = {}
    for b in where.values():
        c[b] = c.get(b, 0) + 1
    return c


def where_line(where: dict, moved: dict) -> tuple[str, list]:
    """"186 on boat, 12 on modal (fallback: boat VM bx_... lost)", and the fallbacks as rows."""
    why: dict[str, int] = {}
    for n, r in moved.items():
        if where.get(n) == "modal":
            why[r] = why.get(r, 0) + 1
    parts = [f"{k} on {b}" for b, k in sorted(count(where).items(), key=lambda x: (x[0] != "boat" and x[0] != "runpod", x[0]))]
    text = ", ".join(parts)
    if why:
        text += " (fallback: " + "; ".join(f"{k} job{'s' if k > 1 else ''}: {r}" for r, k in why.items()) + ")"
    return text, [{"jobs": k, "to": "modal", "reason": r} for r, k in why.items()]


# ----------------------------------------------------------------------------------------------- the compare runners
class ModalEx:
    """Modal, as the runners always did (`modal run`, the app already running)."""

    backend = "modal"

    def __init__(self, app):
        self.m = ModalCtx(app).__enter__()

    def remote(self, fn, *args):
        return fn.remote(*args)

    def starmap(self, fn, args: list, **_):
        return fn.starmap(args, order_outputs=False, return_exceptions=True)

    def close(self):
        self.m.__exit__(None, None, None)
        return {}


class BoatEx:
    """The pool (modal/boat.py): each call a py item in the runner's setting (its BOAT mounts and PATH, 2 vCPU and
    4 GB, the function's own timeout)."""

    backend = "boat"

    def __init__(self, runner: str, vms: int = 0, idle: int = 60, teardown: bool = False, vm_type: str = "default", max_vms: int = 0, durations: str = "",
                 limit: int = 3600, build: bool = True, max_wait: int = 0):
        import boat
        self.boat = boat
        self.module = str(pathlib.Path(runner).resolve().relative_to(GDP))
        cfg = boat.runner_boat(self.module)
        self.extra = {k: v for k, v in cfg.items() if k in ("mounts", "path", "overlays", "env")}
        self.weight = int(cfg.get("weight", 1))  # slots a call takes (a runner whose calls need more than 4 GB says 2)
        self.vms, self.max_vms, self.limit, self.max_wait = vms, max_vms, limit, max_wait
        self.past = {}
        if durations:  # a results.jsonl of an earlier run: each (tool, task)'s seconds, to start the longest first
            for l in pathlib.Path(durations).read_text().splitlines():
                with contextlib.suppress(Exception):
                    r = json.loads(l)
                    self.past[(r.get("tool"), r.get("task"))] = float(r.get("seconds", 0))
        self.sess = boat.Session(pathlib.Path(runner).name, idle=idle, teardown=teardown, vm_type=vm_type, build=build, oleans=False)
        self.n = 0
        self.calls = 0
        self.summary = None

    def _est(self, args) -> float:
        tool = args[0] if args and isinstance(args[0], str) else None
        tasks = args[1] if len(args) > 1 else []
        tasks = tasks if isinstance(tasks, list) else [tasks]
        lim = next((a for a in args if isinstance(a, int) and not isinstance(a, bool)), 60)
        name = lambda t: t.get("task") if isinstance(t, dict) else t
        return sum(self.past.get((tool, name(t)), lim / 2) for t in tasks) or 1

    def remote(self, fn, *args):
        self.sess.ensure(1)
        self.calls += 1
        out = {}
        self.sess.run([{"name": f"call-{fname(fn)}-{int(time.time() * 1000)}", "kind": "py", "module": self.module, "fn": fname(fn), "args": list(args),
                        "limit": self.limit, "weight": 1, "est": 1, **self.extra}], lambda it, row: out.update(row), max_wait=self.max_wait or 600)
        if "result" not in out or out.get("code") != 0:
            raise RuntimeError(f"{fname(fn)} failed on boat: {str(out.get('error', out))[-1500:]}")
        return out["result"]

    def starmap(self, fn, args: list, on_lost=None, **_):
        """Each call's result as it finishes (an exception for a call that failed); a call lost twice goes to on_lost."""
        name = fname(fn)
        items = []
        for a in args:
            self.n += 1
            items.append({"name": f"{name}-{self.n}", "kind": "py", "module": self.module, "fn": name, "args": list(a), "limit": self.limit,
                          "weight": self.weight, "est": self._est(list(a)), **self.extra})
        slots = self.boat.TYPES[self.sess.vm_type][0] // self.boat.SLOT_CPU
        n = self.boat.plan_vms(items, slots, self.vms, self.max_vms)
        self.boat.log(f"{len(items)} calls of {name} on up to {n} {self.sess.vm_type} VM(s)")
        self.sess.ensure(n)
        q: queue.Queue = queue.Queue()
        END = object()

        def done(it, row):
            if "result" in row and row.get("code") == 0:
                q.put(row["result"])
            else:
                q.put(RuntimeError(f"{it['name']}: exit {row.get('code')}: {str(row.get('error', ''))[-600:]}"))

        def go():
            try:
                self.sess.run(items, done, on_lost=(lambda it, why: on_lost(it["args"], why)) if on_lost else None, max_wait=self.max_wait)
            except BaseException as e:
                q.put(e if isinstance(e, Exception) else RuntimeError(repr(e)))
            finally:
                q.put(END)
        threading.Thread(target=go, daemon=True).start()
        while True:
            try:
                r = q.get(timeout=1)
            except queue.Empty:
                continue
            if r is END:
                break
            yield r

    def close(self):
        if self.summary is None:
            self.summary = self.sess.close()
            self.summary["dollars_so_far"] = self.sess.dollars()
            self.summary["batch"] = self.sess.batch
            self.summary["image"] = self.sess.image
            self.boat.log(self.boat.summary_line(self.summary))
            print(f"{self.n + self.calls} calls on boat", flush=True)
            self.summary["where"] = {"boat": self.n + self.calls}
        return self.summary


class AutoEx:
    """boat first; Modal for the whole batch when boat can't take it, and for each call boat lost twice."""

    backend = "auto"

    def __init__(self, runner: str, app, max_wait: int = 120, **opts):
        import boat
        self.app, self.modal, self.bx = app, None, None
        self.where = {"boat": 0, "modal": 0}
        self.why: dict[str, int] = {}
        self.reason, _ = boat.preflight(1, opts.get("vm_type", "default"))
        if self.reason is None:
            try:
                self.bx = BoatEx(runner, build=False, max_wait=max_wait, **opts)
            except boat.Unavailable as e:
                self.reason = str(e)
        if self.reason:
            log(f"boat can't take this batch ({self.reason}): Modal runs it")

    def _modal(self):
        if self.modal is None:
            self.modal = ModalCtx(self.app).__enter__()
        return self.modal

    def _moved(self, k: int, reason: str):
        self.why[reason] = self.why.get(reason, 0) + k

    def remote(self, fn, *args):
        if self.bx:
            try:
                r = self.bx.remote(fn, *args)
                self.where["boat"] += 1
                return r
            except Exception as e:
                self.reason = f"boat failed ({str(e)[:200]})"
                log(f"{self.reason}: Modal runs the rest of this batch")
                with contextlib.suppress(Exception):
                    self.bx.close()
                self.bx = None
        self._modal()
        self._moved(1, self.reason)
        self.where["modal"] += 1
        return fn.remote(*args)

    def starmap(self, fn, args: list, **_):
        rest = list(args)
        if self.bx:
            lost: list = []
            for r in self.bx.starmap(fn, rest, on_lost=lambda a, why: lost.append((a, why))):
                self.where["boat"] += 1
                yield r
            for _, why in lost:
                self._moved(1, why)
            rest = [a for a, _ in lost]
        else:
            self._moved(len(rest), self.reason)
        if rest:
            self._modal()
            log(f"{len(rest)} calls of {fname(fn)} on Modal")
            for r in fn.starmap(rest, order_outputs=False, return_exceptions=True):
                self.where["modal"] += 1
                yield r

    def close(self):
        if getattr(self, "closed", None) is not None:
            return self.closed
        s = {}
        try:
            if self.bx:
                s = self.bx.close()
        finally:
            if self.modal:
                self.modal.__exit__(None, None, None)
        text = ", ".join(f"{k} calls on {b}" for b, k in self.where.items() if k)
        if self.why:
            text += " (fallback: " + "; ".join(f"{k}: {r}" for r, k in self.why.items()) + ")"
        print(text, flush=True)
        self.closed = {**s, "where": self.where, "fallbacks": [{"calls": k, "to": "modal", "reason": r} for r, k in self.why.items()]}
        return self.closed


def cli(run, runner: str, doc: str = ""):
    """`python3 <runner> --backend auto|boat|modal ...`: run's own parameters as flags (as `modal run` makes them),
    plus the pool's."""
    import argparse
    import signal
    reexec_with_modal()
    ap = argparse.ArgumentParser(description=(doc or "").split("\n\n")[0])
    ap.add_argument("--backend", default="modal", choices=["modal", "auto", "boat"])
    ap.add_argument("--vms", type=int, default=0, help="boat VMs for the batch (default: by the work and the plan's limits)")
    ap.add_argument("--max-vms", type=int, default=0)
    ap.add_argument("--idle", type=int, default=60, help="seconds a released VM stays up before boat stops it (0: stop at once)")
    ap.add_argument("--teardown", action="store_true", help="delete the batch's VMs at the end instead of stopping them")
    ap.add_argument("--vm-type", default="default", choices=["small", "default", "large"])
    ap.add_argument("--durations", default="", help="an earlier results.jsonl: the longest calls start first")
    ap.add_argument("--max-wait", type=int, default=120, help="auto: seconds to wait for a boat VM before Modal takes the batch")
    params = list(inspect.signature(run).parameters.values())[1:]
    for p in params:
        flag = "--" + p.name.replace("_", "-")
        if p.default is inspect.Parameter.empty:
            ap.add_argument(flag, required=True, dest=p.name)
        elif isinstance(p.default, bool):
            ap.add_argument(flag, action="store_true", default=p.default, dest=p.name)
        else:
            ap.add_argument(flag, type=type(p.default), default=p.default, dest=p.name)
    a = ap.parse_args()
    kw = {p.name: getattr(a, p.name) for p in params}
    mod = sys.modules["__main__"]
    t0 = time.time()

    def h(sig, frame):
        raise KeyboardInterrupt(f"signal {sig}")
    for s in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(s, h)
    opts = dict(vms=a.vms, idle=a.idle, teardown=a.teardown, vm_type=a.vm_type, max_vms=a.max_vms, durations=a.durations)
    if a.backend == "modal":
        with ModalCtx(mod.app):
            ex = ModalEx.__new__(ModalEx)
            ex.m = contextlib.nullcontext()
            ex.close = lambda: {}
            return run(ex, **kw)
    ex = BoatEx(runner, max_wait=0, **opts) if a.backend == "boat" else AutoEx(runner, mod.app, max_wait=a.max_wait, **opts)
    s = {}
    try:
        run(ex, **kw)
    finally:
        s = ex.close()
        out = kw.get("out")
        if out:
            pathlib.Path(out).mkdir(parents=True, exist_ok=True)
            (pathlib.Path(out) / "backends.json").write_text(json.dumps({"backend": a.backend, **(s or {}), "wall_s": round(time.time() - t0, 1)}, indent=1))


# -------------------------------------------------------------------------------------------------------- GPU runners
def gpu_call(runner: str, fn: str, args: list, app, modal_fn, backend: str = "auto", gpus: str = "", label: str = "gpu") -> tuple[dict, dict]:
    """A GPU runner's function: on RunPod (auto, runpod), on Modal when RunPod can't (auto) or when asked (modal).
    Returns the function's result (the same either way) and where it ran and why."""
    import runpod
    meta: dict = {"backend": None, "fallback": None}
    if backend in ("auto", "runpod"):
        reason = runpod.preflight() if backend == "auto" else None
        if reason is None:
            for attempt in (1, 2):
                try:
                    r = runpod.call(runner, fn, args, gpus, label=label)
                    meta.update(backend="runpod", runpod=r.pop("runpod", None))
                    return r, meta
                except runpod.NoCapacity as e:
                    reason = f"runpod has no GPU in the list ({str(e)[:300]})"
                    break
                except KeyboardInterrupt:
                    raise
                except Exception as e:
                    reason = f"runpod pod failed ({str(e)[:300]})"
                    log(f"{reason}" + ("; once more on a new pod" if attempt == 1 else ""))
                    if backend == "runpod" and attempt == 2:
                        raise
        if backend == "runpod":
            raise RuntimeError(reason)
        log(f"{reason}: Modal runs it")
        meta["fallback"] = reason
    with ModalCtx(app):
        call = modal_fn.spawn(*args)
        try:
            r = call.get()
        finally:
            with contextlib.suppress(Exception):
                call.cancel()
    meta["backend"] = "modal"
    return r, meta


def gpu_cli(main, runner: str):
    """`python3 <GPU runner> --backend auto|runpod|modal ...`: the entrypoint's parameters as flags."""
    import argparse
    import signal
    reexec_with_modal()
    main = getattr(getattr(main, "info", None), "raw_f", None) or main  # (under the Modal client, the entrypoint wraps it)
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

    def h(sig, frame):
        raise KeyboardInterrupt(f"signal {sig}")
    for s in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(s, h)
    main(**vars(a))
