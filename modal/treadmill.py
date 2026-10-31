"""The treadmill: a long-lived client of the boat pool (modal/boat.py) that keeps a base pool of VMs busy with a queue
of experiments, caches every result by (commit, benchmark, task, config) so nothing unchanged runs twice, and writes a
daily digest.

    python3 modal/treadmill.py run [--vms 8] [--hours 0] [--budget-vmh 384] [--quiet 1500] [--nogain 3]
    python3 modal/treadmill.py submit <jobs.json> [--tree DIR] [--name NAME]     a lane's (or terra's) batch
    python3 modal/treadmill.py results <name> | status | digest [--day YYYY-MM-DD]

The base pool: `--vms` large VMs (4 slots each) held by the treadmill's batches, which a scheduler keeps full every
15 s, in this order:
  (b) a floor of one VM of soundness work: the kernel fuzz, the CDCL fuzz and the randomized tamper test at fresh seeds,
      and at a commit that changes kernel/kernel.ts or core/check.ts, its mutants (kernel/mutants.ts ids, one each);
  (c) submissions (`submit`: a jobs.json and its tree as it is), up to two VMs while any wait;
  (a) at each new main commit, per benchmark (CHC-COMP, TermComp ITS, SV-COMP, TIP, IC3Syn): the whole set at 60 s (the
      bar's baseline of that commit when there is one), then rounds over the tasks no round has solved, at 300 s and
      900 s, each budget with the search's variants (VARIANTS: knobs the prover reads); a benchmark stops after
      `--nogain` rounds in a row that solve nothing new;
  then more of (b) and (c) in what's left.
Bars and lane batches don't wait on it: they lease or start VMs of their own (elastic, extra starts allowed).

Every batch is the pool's (a Session): it leases warm VMs first, starts what's missing, and lets each VM go the moment
it has nothing left to take (boat.py's early release), so the next batch, the treadmill's or anyone's, leases it
without a start. While it has work running or queued the treadmill declares it (boat.py's demand), so a released VM
stays up for its next batch; with nothing queued for --quiet seconds it declares the end and its VMs stop a minute
later (TOS-6: VMs kept for queued work, never parked). It stops launching once the day's VM-hours reach
--budget-vmh (default-VM hours, as the plan counts them: a large VM is 2).

Under <main checkout>/runs/treadmill: cache.jsonl (every task's verdict), commits/<sha>/ (each benchmark's rounds and
state, the fuzz and mutants' results), subs/<name>/ (submissions), trees/<sha> (worktrees of main's commits),
vmh.jsonl (each batch's VM-hours), digest/<day>.md, status.json, treadmill.log.
"""
import argparse
import contextlib
import datetime
import hashlib
import io
import json
import math
import os
import pathlib
import subprocess
import sys
import tarfile
import threading
import time

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import boat  # noqa: E402

MAIN = boat.main_checkout()
TM = pathlib.Path(os.environ.get("GDPW_TREADMILL") or MAIN / "runs" / "treadmill")
CLIENT = "treadmill"
SLOTS = boat.TYPES[boat.VM_TYPE][0] // boat.SLOT_CPU
# the search's variants: knobs the prover already reads (core/infer.ts, core/interp.ts, core/cyclic.ts, kernel/prove.ts)
VARIANTS = {"base": {}, "cyclic": {"GDP_CYCLIC": "1"}, "td": {"GDP_TD": "1"}, "clausal": {"GDP_ITP_CLAUSAL": "1"},
            "cdcl90": {"GDP_CDCL_SHARE": "0.9"}, "nojoin": {"GDP_JOIN": "0"}}
BUDGETS = [300, 900]
# a benchmark: its runner, the bar's view of its results (gates/bar-lib.ts) and its group's name in a bar baseline;
# `env`: its shard takes the variants' environment (SV-COMP's and TIP's don't: their rounds are by budget alone)
BENCHES = {
    "chc": {"module": "compare/chc/modal_chc.py", "view": "chc", "env": True},
    "its": {"module": "compare/term/modal_term.py", "view": "its", "env": True},
    "sv": {"module": "compare/term/modal_sv.py", "view": "sv", "env": False},
    "tip": {"module": "compare/tip/modal_tip.py", "view": "tip", "env": False},
    "ic3syn": {"sh": True, "env": True},
}
TIP_SETS = ["isaplanner", "prod", "tip2015", "grammars"]
FUZZ = {"kernel": ("kernel", "FUZZ_SEED={s} bun test kernel.test.ts 2>&1"),
        "cdcl": ("kernel", "FUZZ_SEED={s} FUZZ_SCALE=4 GDP_CDCL_VERIFY=1 bun test cdcl.test.ts 2>&1"),
        "tamper": ("kernel", "FUZZ_SEED={s} bun test tamper.test.ts 2>&1")}
REFUSED = ("unsupported", "refused")


def log(*a):
    line = f"[treadmill {time.strftime('%H:%M:%S')}] " + " ".join(map(str, a))
    print(line, file=sys.stderr, flush=True)
    with contextlib.suppress(Exception):
        with open(TM / "treadmill.log", "a") as f:
            f.write(line + "\n")


def jl(path: pathlib.Path) -> list[dict]:
    return [json.loads(l) for l in path.read_text().splitlines() if l.strip()] if path.exists() else []


def append(path: pathlib.Path, row: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "a") as f:
        f.write(json.dumps(row) + "\n")


def git(*a, cwd=MAIN) -> str:
    return subprocess.run(["git", "-C", str(cwd), *a], capture_output=True, text=True, check=True).stdout.strip()


def today() -> str:
    return time.strftime("%Y-%m-%d", time.gmtime())


# ------------------------------------------------------------------------------------------------------- the cache
class Cache:
    """Every verdict, by (commit, benchmark, task, config); appended to cache.jsonl as it comes."""

    def __init__(self):
        self.path = TM / "cache.jsonl"
        self.d = {(r["commit"], r["bench"], r["task"], r["config"]): r for r in jl(self.path)}
        self.lock = threading.Lock()

    def put(self, row: dict):
        with self.lock:
            self.d[(row["commit"], row["bench"], row["task"], row["config"])] = row
            append(self.path, row)

    def solved(self, commit: str, bench: str) -> dict[str, str]:
        """The tasks some round of this commit solved, each with the first config that did."""
        out = {}
        for (c, b, t, cfg), r in sorted(self.d.items(), key=lambda x: x[1]["t"]):
            if c == commit and b == bench and r["solved"] and t not in out:
                out[t] = cfg
        return out

    def seen(self, commit: str, bench: str, config: str) -> set[str]:
        return {t for (c, b, t, cfg) in self.d if c == commit and b == bench and cfg == config}

    def refused(self, commit: str, bench: str) -> set[str]:
        return {t for (c, b, t, cfg), r in self.d.items() if c == commit and b == bench and r["answer"] in REFUSED}


# ------------------------------------------------------------------------------------------------------ the batches
class Batch:
    """One Session's worth of items in a thread: `vms` asked for, the session's live VMs counted while it runs."""

    def __init__(self, tm, label: str, chain: str, items: list[dict], vms: int, on_row, root=None, tar=None, after=None, oleans=False):
        self.tm, self.label, self.chain, self.items, self.vms = tm, label, chain, items, vms
        self.on_row, self.root, self.tar, self.after, self.oleans = on_row, root, tar, after, oleans
        self.sess, self.done, self.failed, self.t0 = None, False, False, time.time()
        self.thread = threading.Thread(target=self.go, daemon=True)
        self.thread.start()

    def held(self) -> int:
        s = self.sess
        if s is None:
            return 0 if self.done else self.vms
        return sum(1 for v in list(s.vms.values()) if not v.dead and not v.released and v.t_end is None) or (0 if self.done else 1)

    def go(self):
        summary = {}
        try:
            self.sess = boat.Session(f"treadmill {self.label}", build=False, oleans=self.oleans, root=self.root or MAIN, tar=self.tar)
            self.sess.ensure(self.vms)
            self.sess.run(self.items, lambda it, row: self.on_row(it, row), on_lost=lambda it, why: self.on_row(it, {"code": -1, "error": why, "lost": True}), max_wait=900)
            logs = self.sess.collect()
            if self.after:
                self.after(logs)
        except Exception as e:
            log(f"{self.label}: {str(e)[:300]}")
            self.failed = True
            for it in self.items:
                with contextlib.suppress(Exception):
                    self.on_row(it, {"code": -1, "error": str(e)[:300], "lost": True, "batch_failed": True})
        finally:
            if self.sess:
                summary = self.sess.close()
                mult = boat.TYPES[boat.VM_TYPE][0] / boat.TYPES["default"][0]
                append(TM / "vmh.jsonl", {"t": time.time(), "day": today(), "label": self.label, "chain": self.chain, "vmh": round(summary["held_s"] * mult / 3600, 3),
                                         "busy_vmh": round(summary["busy_s"] * mult / 3600, 3), "ready_vmh": round(summary["ready_held_s"] * mult / 3600, 3),
                                         "starts": summary["starts"], "vms": summary["vms"], "items": len(self.items)})
            self.done = True


_boat_cfg: dict = {}


def py_item(name: str, module: str, fn: str, args: list, limit: int, est: float, root: pathlib.Path, weight: int = 1) -> dict:
    """A runner's function as an item (as fanout.BoatEx's), in the runner's boat setting (its mounts, PATH, overlays)."""
    if (root, module) not in _boat_cfg:
        import agent
        _boat_cfg[(root, module)] = getattr(agent.import_runner(str(root / module)), "BOAT", {})
    cfg = _boat_cfg[(root, module)]
    return {"name": name, "kind": "py", "module": module, "fn": fn, "args": args, "limit": limit, "est": est,
            "weight": max(weight, int(cfg.get("weight", 1))), **{k: v for k, v in cfg.items() if k in ("mounts", "path", "overlays", "env")}}


def sh_item(name: str, cmd: str, cwd: str, limit: int, est: float, weight: int = 1) -> dict:
    return {"name": name, "kind": "sh", "cmd": cmd, "cwd": cwd, "limit": limit, "est": est, "weight": weight}


# -------------------------------------------------------------------------------------------- (a) the sweeps
def rounds(bench: str) -> list[tuple[int, str]]:
    return [(60, "base")] + [(b, v) for b in BUDGETS for v in (VARIANTS if BENCHES[bench]["env"] else ["base"])]


class Sweep:
    """A benchmark's rounds at a commit: its state in commits/<sha>/<bench>/state.json."""

    def __init__(self, tm, commit: str, tree: pathlib.Path, bench: str):
        self.tm, self.commit, self.tree, self.bench, self.spec = tm, commit, tree, bench, BENCHES[bench]
        self.dir = TM / "commits" / commit[:12] / bench
        self.dir.mkdir(parents=True, exist_ok=True)
        self.state = json.loads((self.dir / "state.json").read_text()) if (self.dir / "state.json").exists() else {"round": 0, "nogain": 0, "done": False, "gains": []}
        self.batch: Batch | None = None
        self.fetching, self.retry_at = False, 0.0

    def save(self):
        (self.dir / "state.json").write_text(json.dumps(self.state, indent=1))

    def tasks(self):
        """The benchmark's tasks (its runner's own list, kept per commit), or a batch on its way to get them."""
        f = self.dir / "tasks.json"
        if f.exists():
            return json.loads(f.read_text())
        if self.spec.get("sh"):
            ids = subprocess.run(["bun", "-e", "import {protocols} from './research/protocols/ic3syn/models.ts'; console.log(JSON.stringify(protocols.map(p => p.id)))"],
                                 cwd=self.tree, capture_output=True, text=True, timeout=120).stdout.strip().splitlines()[-1]
            f.write_text(ids)
            return json.loads(ids)

        def on_row(it, row):
            if row.get("code") == 0 and "result" in row:
                f.write_text(json.dumps(row["result"]))
            else:
                log(f"{self.bench}: tasks() failed: {str(row.get('error', row))[-300:]}")
        self.fetching = True
        self.batch = Batch(self.tm, f"{self.commit[:12]} {self.bench} tasks", "a", [py_item("tasks", self.spec["module"], "tasks", [TIP_SETS] if self.bench == "tip" else [], 900, 30, self.tree)],
                           1, on_row, root=self.tree)
        return self.batch

    def task_ids(self, got) -> list[str]:
        if self.bench == "tip":
            return list(got["tasks"])
        return [t if isinstance(t, str) else t["task"] for t in (got if isinstance(got, list) else got.get("tasks", []))]

    def import_bar(self) -> bool:
        """Round 0 from the bar's baseline of this commit (its first run), when there is one."""
        bases = sorted((MAIN / "runs" / "bar" / "base").glob(f"{self.commit[:12]}-*-r1/{self.bench}/run1"))
        if self.spec.get("sh") or not bases or not (bases[0] / "results.jsonl").exists():
            return False
        self.verdicts(bases[0], "60:base", "bar baseline")
        return True

    def next_round(self, free: int) -> Batch | None:
        st = self.state
        if st["done"] or self.batch or time.time() < self.retry_at:
            return None
        plan = rounds(self.bench)
        if st["round"] >= len(plan):
            st["done"] = True
            self.save()
            return None
        budget, variant = plan[st["round"]]
        config = f"{budget}:{variant}"
        if st["round"] == 0 and self.import_bar():
            return self.finish_round(config, 0)
        got = self.tasks()
        if isinstance(got, Batch):
            return got
        ids = self.task_ids(got)
        solved, refused, seen = self.tm.cache.solved(self.commit, self.bench), self.tm.cache.refused(self.commit, self.bench), self.tm.cache.seen(self.commit, self.bench, config)
        todo = [t for t in ids if t not in solved and t not in refused and t not in seen]
        if not todo:
            return self.finish_round(config, 0)
        env = VARIANTS[variant]
        rdir = self.dir / f"{budget}-{variant}"
        rdir.mkdir(parents=True, exist_ok=True)
        by = {t if isinstance(t, str) else t["task"]: t for t in (got if isinstance(got, list) else got.get("tasks", []))}
        items = []
        for k, t in enumerate(todo):
            name = f"{self.bench}-{budget}-{variant}-{k}"
            if self.spec.get("sh"):
                pre = " ".join(f"{a}={b}" for a, b in env.items())
                items.append(sh_item(name, f"{pre} bun research/protocols/ic3syn/run.ts --ms {budget * 1000} --only '{t}' --skip broken 2>/dev/null | tail -1", ".", budget * 3 + 120, budget))
                continue
            envs = ",".join(f"{a}={b}" for a, b in env.items())
            args = {"chc": lambda: ["gdp", [by[t]], budget, envs], "its": lambda: ["gdp", [by[t]], budget, envs],
                    "sv": lambda: ["gdp", by[t], budget], "tip": lambda: ["gdp", [t], budget, {}]}[self.bench]()
            items.append(py_item(name, self.spec["module"], "shard", args, budget + 600, budget, self.tree))
        rows: list = []
        lock = threading.Lock()

        def on_row(it, row):
            with lock:
                res = row.get("result")
                if isinstance(res, dict):
                    res = [res]
                rows.extend(res or [{"tool": "gdp", "task": todo[int(it["name"].rsplit("-", 1)[1])], "answer": "error", "seconds": -1, "err": str(row.get("error", ""))[:300]}])

        def after(logs):
            if self.spec.get("sh"):  # IC3Syn: each item's last line, run.ts's JSON
                out = {}
                for k, t in enumerate(todo):
                    text = logs.get(f"{self.bench}-{budget}-{variant}-{k}", {}).get("out", "").strip().splitlines()
                    with contextlib.suppress(Exception):
                        v = json.loads(text[-1])["search"]
                        out[t] = {"answer": v["verdict"], "solved": v["verdict"] == "proven", "secs": v.get("ms", 0) / 1000}
                    out.setdefault(t, {"answer": "error", "solved": False, "secs": -1})
                self.record(out, config)
                (rdir / "verdicts.json").write_text(json.dumps(out))
            else:
                (rdir / "tasks.json").write_text(json.dumps({"limit": budget, **got} if isinstance(got, dict) else got))
                with open(rdir / "results.jsonl", "w") as f:
                    for r in rows:
                        f.write(json.dumps(r) + "\n")
                self.verdicts(rdir, config, "")
        vms = max(1, min(free, math.ceil(len(items) * budget / (SLOTS * 1800))))
        log(f"{self.commit[:12]} {self.bench} round {st['round']} ({config}): {len(items)} tasks on {vms} VMs")
        self.round_t = time.time()
        self.batch = Batch(self.tm, f"{self.commit[:12]} {self.bench} {config}", "a", items, vms, on_row, root=self.tree, after=after, oleans=self.bench == "ic3syn")
        return self.batch

    def verdicts(self, rdir: pathlib.Path, config: str, source: str):
        p = subprocess.run(["bun", str(HERE.parent / "gates" / "bar.ts"), "read", BENCHES[self.bench]["view"], str(rdir), "--tree", str(self.tree), "--tasks"],
                           capture_output=True, text=True, timeout=300)
        obs = json.loads(p.stdout.strip().split(" ", 1)[1]) if p.returncode == 0 and p.stdout.strip() else {}
        self.record(obs, config, source)

    def record(self, obs: dict, config: str, source: str = ""):
        for t, o in obs.items():
            self.tm.cache.put({"commit": self.commit, "bench": self.bench, "task": t, "config": config, "answer": o.get("answer"), "solved": bool(o.get("solved")),
                               "wrong": bool(o.get("wrong")), "secs": o.get("secs"), "t": round(time.time(), 1), **({"source": source} if source else {})})
            if o.get("wrong"):
                log(f"WRONG: {self.bench} {t} at {config}: {o.get('answer')}")

    def finish_round(self, config: str, _=None):
        """After a round: its gains, the no-gain count, the next round (or done)."""
        st = self.state
        gained = [t for t, cfg in self.tm.cache.solved(self.commit, self.bench).items() if cfg == config]
        st["gains"].append({"round": st["round"], "config": config, "gained": len(gained), "t": round(time.time())})
        st["nogain"] = 0 if gained or st["round"] == 0 else st["nogain"] + 1
        st["round"] += 1
        if st["nogain"] >= self.tm.nogain or st["round"] >= len(rounds(self.bench)):
            st["done"] = True
        self.save()
        log(f"{self.commit[:12]} {self.bench} {config}: {len(gained)} newly solved{'; done' if st['done'] else ''}")
        return None

    def poll(self):
        if self.batch and self.batch.done:
            b, self.batch = self.batch, None
            if self.fetching or b.failed:  # (the task list fetched, or a batch boat couldn't run: the round again later)
                self.fetching = False
                if b.failed or not (self.dir / "tasks.json").exists():
                    self.retry_at = time.time() + 600
                return
            budget, variant = rounds(self.bench)[self.state["round"]]
            self.finish_round(f"{budget}:{variant}")


# --------------------------------------------------------------------------------------- (b) soundness work
class Soundness:
    """Fresh fuzz seeds (kernel, CDCL, tamper) and, at a commit whose trusted base changed, its mutants."""

    def __init__(self, tm, commit: str, tree: pathlib.Path):
        self.tm, self.commit, self.tree = tm, commit, tree
        self.dir = TM / "commits" / commit[:12]
        self.dir.mkdir(parents=True, exist_ok=True)
        self.mutants = self.mutant_ids()

    def mutant_ids(self) -> list[int]:
        """The trusted base's mutants, once per version of kernel/kernel.ts and core/check.ts (their hash)."""
        h = hashlib.sha256(b"".join((self.tree / f).read_bytes() for f in ("kernel/kernel.ts", "core/check.ts"))).hexdigest()[:16]
        done = {r["id"] for r in jl(TM / "mutants.jsonl") if r["hash"] == h}
        self.hash = h
        with contextlib.suppress(Exception):
            out = subprocess.run(["bun", "mutants.ts", "list"], cwd=self.tree / "kernel", capture_output=True, text=True, timeout=120).stdout
            return [int(l.split("\t")[0]) for l in out.splitlines() if l.split("\t")[0].isdigit() and int(l.split("\t")[0]) not in done]
        return []

    def batch(self, vms: int) -> Batch:
        st = self.tm.state
        items, kinds = [], []
        n = vms * SLOTS * 4
        while self.mutants and len(items) < vms * SLOTS:
            m = self.mutants.pop(0)
            items.append(sh_item(f"mutant-{m}", f"bun mutants.ts ids {m} 2>&1 | tail -1", "kernel", 3600, 600))
            kinds.append(("mutant", m))
        while len(items) < n:
            s = st["seed"] = st.get("seed", 1000) + 1
            k = list(FUZZ)[s % len(FUZZ)]
            cwd, cmd = FUZZ[k]
            items.append(sh_item(f"{k}-fuzz-{s}", cmd.format(s=s), cwd, 900, 60))
            kinds.append((k, s))
        self.tm.save_state()
        codes = {}

        def on_row(it, row):
            codes[it["name"]] = row.get("code", -1)

        def after(logs):
            for it, (k, s) in zip(items, kinds):
                out = logs.get(it["name"], {}).get("out", "")
                if k == "mutant":
                    with contextlib.suppress(Exception):
                        r = json.loads(out.strip().splitlines()[-1])
                        append(TM / "mutants.jsonl", {"t": time.time(), "commit": self.commit, "hash": self.hash, "id": s, "killedBy": r.get("killedBy"), "where": f"{r.get('file')}:{r.get('line')}",
                                                      "change": f"{r.get('from')} -> {r.get('to')}"})
                    continue
                append(TM / "fuzz.jsonl", {"t": time.time(), "commit": self.commit, "kind": k, "seed": s, "code": codes.get(it["name"], -1),
                                           **({"tail": out[-1500:]} if codes.get(it["name"], -1) != 0 else {})})
                if codes.get(it["name"], -1) not in (0,):
                    log(f"FUZZ FAILED: {k} seed {s} at {self.commit[:12]} (exit {codes.get(it['name'])})")
        return Batch(self.tm, f"{self.commit[:12]} soundness", "b", items, vms, on_row, root=self.tree, after=after)


# --------------------------------------------------------------------------------------- (c) submissions
def tree_key(tar: bytes) -> str:
    return hashlib.sha256(tar).hexdigest()[:16]


def job_key(tk: str, j: dict) -> str:
    return hashlib.sha256((tk + json.dumps({k: j.get(k) for k in ("cmd", "cwd", "cpu", "memory", "timeout")}, sort_keys=True)).encode()).hexdigest()[:24]


def submit(jobs: str, tree: str, name: str):
    spec = json.loads(pathlib.Path(jobs).read_text())
    if any(j.get("image") or j.get("backend") == "modal" for j in spec):
        raise SystemExit("a job on Modal's own image doesn't belong on the treadmill: run it with modal/run.py")
    root = pathlib.Path(git("rev-parse", "--show-toplevel", cwd=pathlib.Path(tree).resolve()))
    tar = boat.tree_tarball(root)
    name = name or f"{root.name}-{pathlib.Path(jobs).stem}-{time.strftime('%m%d-%H%M%S')}"
    d = TM / "subs" / name
    if d.exists():
        raise SystemExit(f"{d} exists: another --name")
    d.mkdir(parents=True)
    (d / "tree.tar.gz").write_bytes(tar)
    (d / "jobs.json").write_text(json.dumps(spec, indent=1))
    (d / "meta.json").write_text(json.dumps({"name": name, "tree": str(root), "sha": git("rev-parse", "HEAD", cwd=root), "tree_key": tree_key(tar), "jobs": len(spec),
                                             "t": time.time(), "status": "queued"}, indent=1))
    print(f"queued {name}: {len(spec)} jobs from {root} (tree {tree_key(tar)}); results: python3 modal/treadmill.py results {name}")


def results(name: str):
    d = TM / "subs" / name
    meta = json.loads((d / "meta.json").read_text())
    print(f"{name}: {meta['status']}, {meta['jobs']} jobs" + (f", done in {round(meta['wall_s'])} s" if meta.get("wall_s") else ""))
    if (d / "out" / "summary.tsv").exists():
        print((d / "out" / "summary.tsv").read_text(), end="")
        print(f"(logs: {d / 'out'})")


class Submission:
    def __init__(self, tm, d: pathlib.Path):
        self.tm, self.d = tm, d
        self.meta = json.loads((d / "meta.json").read_text())
        self.batch: Batch | None = None

    def start(self, vms: int) -> Batch | None:
        spec = json.loads((self.d / "jobs.json").read_text())
        tar = (self.d / "tree.tar.gz").read_bytes()
        cache = TM / "subs" / ".cache"
        cache.mkdir(parents=True, exist_ok=True)
        keys = {j["name"]: job_key(self.meta["tree_key"], j) for j in spec}
        rows = {n: json.loads((cache / f"{k}.json").read_text()) for n, k in keys.items() if (cache / f"{k}.json").exists()}
        todo = [j for j in spec if j["name"] not in rows]
        items, _ = boat.job_items(todo, "", lambda c: c, boat.VM_TYPE, {})
        self.meta["status"], self.meta["started"] = "running", time.time()
        self.save()

        def on_row(it, row):
            rows[it["name"]] = {k: row.get(k) for k in ("code", "seconds", "error")}

        def after(logs):
            out = self.d / "out"
            out.mkdir(exist_ok=True)
            for j in spec:
                n, r = j["name"], rows.get(j["name"], {"code": -1, "seconds": -1, "error": "never ran"})
                lg = logs.get(n, {})
                for k in range(1, 3):
                    lg = logs.get(f"{n}~r{k}", lg)
                if "out" in lg or "err" in lg:
                    (out / f"{n}.log").write_text(lg.get("out", "") + ("\n--- stderr ---\n" + lg["err"] + (f"\n{r['error']}" if r.get("error") else "") if lg.get("err", "").strip() else ""))
                    if r.get("code") == 0 or not r.get("error"):
                        (cache / f"{keys[n]}.json").write_text(json.dumps({**r, "log": str(out / f"{n}.log")}))
            (out / "summary.tsv").write_text("".join(f"{j['name']}\t{rows.get(j['name'], {}).get('code', -1)}\t{rows.get(j['name'], {}).get('seconds', -1)}\tboat\n" for j in spec))
            self.meta["status"], self.meta["wall_s"] = "done", time.time() - self.meta["started"]
            self.save()
        if not todo:
            after({})
            return None
        self.batch = Batch(self.tm, f"sub {self.meta['name']}", "c", items, vms, on_row, tar=tar, after=after, oleans=True)
        return self.batch

    def save(self):
        (self.d / "meta.json").write_text(json.dumps(self.meta, indent=1))


# ---------------------------------------------------------------------------------------------- the controller
class Treadmill:
    def __init__(self, vms: int, budget_vmh: float, quiet: int, nogain: int):
        TM.mkdir(parents=True, exist_ok=True)
        self.vms, self.budget_vmh, self.quiet, self.nogain = vms, budget_vmh, quiet, nogain
        self.cache = Cache()
        self.state = json.loads((TM / "state.json").read_text()) if (TM / "state.json").exists() else {}
        self.batches: list[Batch] = []
        self.commit, self.tree, self.sweeps, self.sound = None, None, {}, None
        self.subs: dict[str, Submission] = {}
        self.last_work = time.time()
        self.declared, self.declared_t = False, 0.0

    def save_state(self):
        (TM / "state.json").write_text(json.dumps(self.state, indent=1))

    def tree_of(self, sha: str) -> pathlib.Path:
        """A worktree of main's commit (with its submodules), the last three kept."""
        path = TM / "trees" / sha[:12]
        if not (path / ".treadmill-ready").exists():
            path.parent.mkdir(parents=True, exist_ok=True)
            if not path.exists():
                git("worktree", "add", "--detach", str(path), sha)
            for m in ("vendor/handwired", "vendor/gdp-ts"):
                with contextlib.suppress(Exception):
                    git("config", f"submodule.{m}.url", str(MAIN / m), cwd=path)
            subprocess.run(["git", "-C", str(path), "-c", "protocol.file.allow=always", "submodule", "update", "--init"], capture_output=True, timeout=600)
            (path / ".treadmill-ready").write_text(sha)
        for old in sorted((TM / "trees").iterdir(), key=lambda p: p.stat().st_mtime)[:-3]:
            with contextlib.suppress(Exception):
                git("worktree", "remove", "--force", str(old))
        return path

    def held(self) -> int:
        return sum(b.held() for b in self.batches if not b.done)

    def vmh_today(self) -> float:
        return sum(r["vmh"] for r in jl(TM / "vmh.jsonl") if r["day"] == today())

    def step(self):
        self.batches = [b for b in self.batches if not b.done]
        head = git("rev-parse", "main")
        if head != self.commit:
            log(f"main is {head[:12]}: sweeps and soundness work at it")
            self.commit, self.tree = head, self.tree_of(head)
            self.sweeps = {b: Sweep(self, head, self.tree, b) for b in BENCHES}
            self.sound = Soundness(self, head, self.tree)
        for sw in self.sweeps.values():
            sw.poll()
        for d in sorted((TM / "subs").glob("*/meta.json")) if (TM / "subs").exists() else []:
            if d.parent.name not in self.subs and json.loads(d.read_text())["status"] in ("queued", "running"):
                self.subs[d.parent.name] = Submission(self, d.parent)
        over = self.vmh_today() >= self.budget_vmh
        free = self.vms - self.held()
        want = lambda c: [b for b in self.batches if b.chain == c and not b.done]
        if not over:
            if free > 0 and not want("b"):  # (b)'s floor: one VM
                self.batches.append(self.sound.batch(1))
                free -= 1
            waiting = [s for s in self.subs.values() if s.meta["status"] == "queued"]
            for s in waiting:  # (c): up to two VMs while submissions wait
                k = min(free, 2 - sum(b.held() for b in want("c")))
                if k <= 0:
                    break
                b = s.start(k)
                if b:
                    self.batches.append(b)
                    free -= k
            for sw in self.sweeps.values():  # (a): the next round of each benchmark
                if free <= 0:
                    break
                b = sw.next_round(free)
                if b:
                    self.batches.append(b)
                    free -= b.vms
            for s in [s for s in self.subs.values() if s.meta["status"] == "queued"]:  # (c) in what's left
                if free <= 0:
                    break
                b = s.start(min(free, 4))
                if b:
                    self.batches.append(b)
                    free -= b.vms
            if free > 0 and len(want("b")) < 1 + self.vms // 2:  # (b) fills the rest
                self.batches.append(self.sound.batch(min(free, 2)))
        busy = bool([b for b in self.batches if not b.done])
        if busy:
            self.last_work = time.time()
        if busy or time.time() - self.last_work < self.quiet:
            if not self.declared or time.time() - self.declared_t > 60:
                boat.demand(CLIENT, 300, os.getpid(), "treadmill")
                self.declared, self.declared_t = True, time.time()
        elif self.declared:
            log(f"nothing queued for {self.quiet} s: the pool's VMs stop")
            boat.undeclare(CLIENT)
            self.declared = False
        (TM / "status.json").write_text(json.dumps({"t": time.time(), "pid": os.getpid(), "commit": self.commit, "vms": self.vms, "held": self.held(), "vmh_today": round(self.vmh_today(), 2),
                                                    "budget_vmh": self.budget_vmh, "over_budget": over,
                                                    "batches": [{"label": b.label, "chain": b.chain, "held": b.held(), "items": len(b.items), "since": round(time.time() - b.t0)} for b in self.batches if not b.done],
                                                    "sweeps": {k: s.state for k, s in self.sweeps.items()}, "queued_subs": [n for n, s in self.subs.items() if s.meta["status"] == "queued"]}, indent=1))

    def run(self, hours: float):
        os.environ["GDPW_BOAT_CLIENT"] = CLIENT
        (TM / "treadmill.pid").write_text(str(os.getpid()))
        t_end = time.time() + hours * 3600 if hours else None
        last_digest = 0.0
        log(f"running: {self.vms} {boat.VM_TYPE} VMs, {self.budget_vmh} VM-hours a day, quiet {self.quiet} s" + (f", for {hours} h" if hours else ""))
        try:
            with boat.signals_as_interrupt():
                while not t_end or time.time() < t_end:
                    try:
                        self.step()
                    except Exception as e:
                        log(f"step: {str(e)[:400]}")
                    if time.time() - last_digest > 3600:
                        last_digest = time.time()
                        with contextlib.suppress(Exception):
                            digest(today(), quiet=True)
                    time.sleep(15)
        except KeyboardInterrupt:
            log("stopping: the batches running end (their VMs released)")
        finally:
            for b in self.batches:
                if b.sess:
                    b.sess.stop.set()
            for b in self.batches:
                b.thread.join(timeout=600)
            boat.undeclare(CLIENT)
            digest(today(), quiet=True)
            (TM / "treadmill.pid").unlink(missing_ok=True)
            log("stopped")


# ------------------------------------------------------------------------------------------------- the digest
def digest(day: str, quiet: bool = False) -> str:
    """The day's new solves (and the config that solved each), regressions against the commit before, wrong answers,
    the soundness work, submissions, VM-hours, busy share, starts and extra-start dollars."""
    rows = [r for r in jl(TM / "cache.jsonl") if time.strftime("%Y-%m-%d", time.gmtime(r["t"])) == day]
    allrows = jl(TM / "cache.jsonl")
    out = [f"# Treadmill digest, {day}", ""]
    commits = sorted({r["commit"] for r in rows}, key=lambda c: min(r["t"] for r in rows if r["commit"] == c))
    for c in commits:
        out.append(f"## {c[:12]}")
        for b in BENCHES:
            mine = [r for r in allrows if r["commit"] == c and r["bench"] == b]
            if not mine:
                continue
            first = {}
            for r in sorted(mine, key=lambda r: r["t"]):
                if r["solved"] and r["task"] not in first:
                    first[r["task"]] = r["config"]
            base = {t for t, cfg in first.items() if cfg == "60:base"}
            new = {t: cfg for t, cfg in first.items() if cfg != "60:base"}
            tasks = {r["task"] for r in mine}
            by_cfg = {}
            for t, cfg in new.items():
                by_cfg.setdefault(cfg, []).append(t)
            wrong = [r for r in mine if r["wrong"]]
            st = json.loads((TM / "commits" / c[:12] / b / "state.json").read_text()) if (TM / "commits" / c[:12] / b / "state.json").exists() else {}
            out.append(f"- **{b}**: {len(base)} of {len(tasks)} at 60 s; {len(new)} more solved past it" + (f" ({', '.join(f'{k}: {len(v)}' for k, v in by_cfg.items())})" if by_cfg else "")
                       + f"; round {st.get('round', '?')}{' (done)' if st.get('done') else ''}" + (f"; **WRONG: {len(wrong)}** ({', '.join(r['task'] + ' at ' + r['config'] for r in wrong[:5])})" if wrong else ""))
            for cfg, ts in by_cfg.items():
                out.append(f"  - {cfg}: " + ", ".join(ts[:12]) + (" ..." if len(ts) > 12 else ""))
            prev = [p for p in sorted({r["commit"] for r in allrows if r["bench"] == b and r["config"] == "60:base" and r["commit"] != c}, key=lambda x: max(r["t"] for r in allrows if r["commit"] == x))]
            if prev:
                p = prev[-1]
                was = {r["task"] for r in allrows if r["commit"] == p and r["bench"] == b and r["config"] == "60:base" and r["solved"]}
                now = {r["task"] for r in mine if r["config"] == "60:base" and r["solved"]}
                seen = {r["task"] for r in mine if r["config"] == "60:base"}
                lost, gained = sorted((was - now) & seen), sorted(now - was)
                if lost or gained:
                    out.append(f"  - at 60 s against {p[:12]}: {len(gained)} gained, {len(lost)} lost" + (f" (lost: {', '.join(lost[:10])})" if lost else ""))
    fz = [r for r in jl(TM / "fuzz.jsonl") if time.strftime("%Y-%m-%d", time.gmtime(r["t"])) == day]
    mt = [r for r in jl(TM / "mutants.jsonl") if time.strftime("%Y-%m-%d", time.gmtime(r["t"])) == day]
    bad = [r for r in fz if r["code"] != 0]
    out += ["", "## Soundness", f"- fuzz: {len(fz)} seeds ({', '.join(f'{k} {sum(1 for r in fz if r["kind"] == k)}' for k in FUZZ)}), "
            + (f"**{len(bad)} failed**: " + ", ".join(f"{r['kind']} seed {r['seed']} (exit {r['code']})" for r in bad[:10]) if bad else "none failed"),
            f"- mutants: {len(mt)} run, {sum(1 for r in mt if not r.get('killedBy'))} survived" + "".join(f"\n  - survived: {r['id']} {r['where']} {r['change']}" for r in mt if not r.get("killedBy"))]
    subs = [json.loads(p.read_text()) for p in (TM / "subs").glob("*/meta.json")] if (TM / "subs").exists() else []
    subs = [s for s in subs if time.strftime("%Y-%m-%d", time.gmtime(s["t"])) == day]
    out += ["", "## Submissions", *(f"- {s['name']}: {s['status']}, {s['jobs']} jobs" for s in subs)] if subs else []
    v = [r for r in jl(TM / "vmh.jsonl") if r["day"] == day]
    vmh, busy, ready = sum(r["vmh"] for r in v), sum(r["busy_vmh"] for r in v), sum(r["ready_vmh"] for r in v)
    led = [r for r in jl(boat.LEDGER) if r["utc"][:10] == day]
    ours = sum(r.get("starts", 0) for r in led if r.get("client") == CLIENT)
    allst = sum(r.get("starts", 0) for r in led)
    out += ["", "## The pool",
            f"- treadmill batches: {len(v)}, {vmh:.1f} default-VM hours (busy {100 * busy / max(ready, 1e-9):.0f}% of the hours they held VMs ready), {sum(r['starts'] for r in v)} starts",
            f"- starts today (the ledger): {ours} the treadmill's, {allst} every client's"]
    with contextlib.suppress(Exception):
        out.append(f"- {boat.extra_starts()}")
    text = "\n".join(out) + "\n"
    (TM / "digest").mkdir(parents=True, exist_ok=True)
    (TM / "digest" / f"{day}.md").write_text(text)
    if not quiet:
        print(text)
    return text


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--vms", type=int, default=8)
    r.add_argument("--hours", type=float, default=0)
    r.add_argument("--budget-vmh", type=float, default=384)
    r.add_argument("--quiet", type=int, default=1500)
    r.add_argument("--nogain", type=int, default=3)
    s = sub.add_parser("submit")
    s.add_argument("jobs")
    s.add_argument("--tree", default=".")
    s.add_argument("--name", default="")
    s = sub.add_parser("results")
    s.add_argument("name")
    sub.add_parser("status")
    s = sub.add_parser("digest")
    s.add_argument("--day", default="")
    a = ap.parse_args()
    if a.cmd == "run":
        Treadmill(a.vms, a.budget_vmh, a.quiet, a.nogain).run(a.hours)
    elif a.cmd == "submit":
        submit(a.jobs, a.tree, a.name)
    elif a.cmd == "results":
        results(a.name)
    elif a.cmd == "status":
        print((TM / "status.json").read_text() if (TM / "status.json").exists() else "not running")
    elif a.cmd == "digest":
        digest(a.day or today())
