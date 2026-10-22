"""One way for a runner to fan its functions out, on Modal or on boat.dev VMs (modal/boat.py), the same code either way.

A runner writes its entrypoint's body as `run(ex, ...)`, calling `ex.remote(fn, *args)` and `ex.starmap(fn, args)`
(results as they finish, an exception in place of a failed call), and keeps its Modal entrypoint as
`main(...): run(fanout.ModalEx(app), ...)`. Then

    modal run compare/chc/modal_chc.py --out ...                    on Modal, as before
    python3 compare/chc/modal_chc.py --backend boat --out ...       on the boat pool: the same flags, plus --vms,
                                                                    --idle, --teardown, --vm-type, --max-vms, --durations

On boat each call runs on a VM in the runner's own setting: the runner's BOAT (the mounts that stand for its Modal
image's paths, e.g. /bench, and PATH additions), its function imported with a stub `modal`, the batch's tree at
/src/gdp-wired, 2 vCPU and 4 GB per call (Modal's container), under the function's own timeout.
"""
import inspect
import json
import os
import pathlib
import queue
import threading
import time

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent


def fname(fn) -> str:
    for get in (lambda: fn.__name__, lambda: fn.get_raw_f().__name__, lambda: fn.info.function_name, lambda: fn._info.function_name):
        try:
            n = get()
            if n:
                return n.split(".")[-1]
        except Exception:
            pass
    raise ValueError(f"can't name {fn!r}")


class ModalEx:
    """Modal, as the runners always did: the app's id and this client's pid in modal/.live/ while it runs."""

    backend = "modal"

    def __init__(self, app):
        live = GDP / "modal" / ".live"
        live.mkdir(exist_ok=True)
        self.ticket = live / f"{app.app_id}"
        self.ticket.write_text(str(os.getpid()))

    def remote(self, fn, *args):
        return fn.remote(*args)

    def starmap(self, fn, args: list, **_):
        return fn.starmap(args, order_outputs=False, return_exceptions=True)

    def close(self):
        self.ticket.unlink(missing_ok=True)


class BoatEx:
    backend = "boat"

    def __init__(self, runner: str, vms: int = 0, idle: int = 60, teardown: bool = False, vm_type: str = "default", max_vms: int = 0, durations: str = "", limit: int = 3600):
        import boat
        self.boat = boat
        self.module = str(pathlib.Path(runner).resolve().relative_to(GDP))
        cfg = boat.runner_boat(self.module)
        self.extra = {k: v for k, v in cfg.items() if k in ("mounts", "path", "overlays", "env")}
        self.vms, self.max_vms, self.limit = vms, max_vms, limit
        self.past = {}
        if durations:  # a results.jsonl of an earlier run: each (tool, task)'s seconds, to start the longest first
            for l in pathlib.Path(durations).read_text().splitlines():
                try:
                    r = json.loads(l)
                    self.past[(r.get("tool"), r.get("task"))] = float(r.get("seconds", 0))
                except Exception:
                    pass
        self.sess = boat.Session(f"{pathlib.Path(runner).name}", idle=idle, teardown=teardown, vm_type=vm_type)
        self.n = 0
        self.summary = None

    def _est(self, args) -> float:
        tool = args[0] if args and isinstance(args[0], str) else None
        tasks = args[1] if len(args) > 1 else []
        tasks = tasks if isinstance(tasks, list) else [tasks]
        lim = next((a for a in args if isinstance(a, int)), 60)
        name = lambda t: t.get("task") if isinstance(t, dict) else t
        return sum(self.past.get((tool, name(t)), lim / 2) for t in tasks) or 1

    def remote(self, fn, *args):
        self.sess.ensure(1)
        return self.sess.call(self.module, fname(fn), list(args), self.extra, self.limit)

    def starmap(self, fn, args: list, **_):
        """Each call's result as it finishes (an exception for a call that failed), every VM the plan allows at once."""
        name = fname(fn)
        items = []
        for a in args:
            self.n += 1
            items.append({"name": f"{name}-{self.n}", "kind": "py", "module": self.module, "fn": name, "args": list(a), "limit": self.limit,
                          "weight": 1, "est": self._est(list(a)), **self.extra})
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
                self.sess.run(items, done)
            except BaseException as e:
                q.put(e if isinstance(e, Exception) else RuntimeError(repr(e)))
            finally:
                q.put(END)
        t = threading.Thread(target=go, daemon=True)
        t.start()
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
            s = self.summary
            self.boat.log(f"boat: {s['vms']} VMs ({s['created']} created, {s['resumed']} resumed, {s['leased_running']} already up), ${s['dollars_so_far']} so far (boat usage), "
                          f"{s['idle_vm_s']} idle VM-s of {s['ready_held_s']} held ready, {s['bring_up_s']} VM-s bringing up")
        return self.summary


def cli(run, runner: str, doc: str = ""):
    """`python3 <runner> --backend boat ...`: run's own parameters as flags (as `modal run` makes them), plus the pool's."""
    import argparse
    import signal
    ap = argparse.ArgumentParser(description=(doc or "").split("\n\n")[0])
    ap.add_argument("--backend", default="boat", choices=["boat", "modal"])
    ap.add_argument("--vms", type=int, default=0, help="VMs for the batch (default: by the work and the plan's limits)")
    ap.add_argument("--max-vms", type=int, default=0)
    ap.add_argument("--idle", type=int, default=60, help="seconds a released VM stays up before boat stops it (0: stop at once)")
    ap.add_argument("--teardown", action="store_true", help="delete the batch's VMs at the end instead of stopping them")
    ap.add_argument("--vm-type", default="default", choices=["small", "default", "large"])
    ap.add_argument("--durations", default="", help="an earlier results.jsonl: the longest calls start first")
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
    if a.backend == "modal":
        raise SystemExit(f"on Modal: modal run {runner} " + " ".join(f"--{p.name.replace('_', '-')} ..." for p in params[:2]))
    kw = {p.name: getattr(a, p.name) for p in params}
    t0 = time.time()

    def h(sig, frame):
        raise KeyboardInterrupt(f"signal {sig}")
    for s in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(s, h)
    ex = BoatEx(runner, vms=a.vms, idle=a.idle, teardown=a.teardown, vm_type=a.vm_type, max_vms=a.max_vms, durations=a.durations)
    try:
        run(ex, **kw)
    finally:
        s = ex.close()
        out = kw.get("out")
        if out:
            pathlib.Path(out).mkdir(parents=True, exist_ok=True)
            (pathlib.Path(out) / "boat.json").write_text(json.dumps({**s, "wall_s": round(time.time() - t0, 1)}, indent=1))
