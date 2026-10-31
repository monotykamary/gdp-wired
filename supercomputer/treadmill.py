"""gdp-wired's treadmill: the supercomputer's treadmill (~/.local/share/supercomputer, its generic batches, cache,
queue and digest) with this repo's chains: a base pool of VMs kept busy with sweeps of the benchmarks, soundness work
and the queue, every result cached by (commit, benchmark, task, config) so nothing unchanged runs twice, and a daily
digest.

    python3 supercomputer/treadmill.py run [--vms 8] [--max-vms 32] [--step-vms 4] [--backlog-hours 2] [--budget-vmh auto] [--quiet 1500] [--nogain 3]
    python3 supercomputer/treadmill.py submit <jobs.json> [--tree DIR] [--name NAME]     a lane's (or terra's) batch
    python3 supercomputer/treadmill.py results <name> | status | digest [--day YYYY-MM-DD]
    (the same as `supercomputer treadmill run ...`, `supercomputer queue add|ls|results`, `supercomputer digest`)

The base pool: `--vms` large VMs (4 slots each) held by the treadmill's batches, which a scheduler keeps full every
15 s, in this order:
  (b) a floor of one VM of soundness work: the kernel fuzz, the CDCL fuzz and the randomized tamper test at fresh seeds,
      and at a commit that changes kernel/kernel.ts or core/check.ts, its mutants (kernel/mutants.ts ids, one each);
  (c) submissions (the queue: a jobs.json and its tree as it is), up to two VMs while any wait;
  (a) at each new main commit, per benchmark (CHC-COMP, TermComp ITS, SV-COMP, TIP, IC3Syn): the whole set at 60 s (the
      bar's baseline of that commit when there is one), then rounds over the tasks no round has solved, at 300 s and
      900 s, each budget with the search's variants (VARIANTS: knobs the prover reads); a benchmark stops after
      `--nogain` rounds in a row that solve nothing new;
  then more of (b) and (c) in what's left.
Bars and lane batches don't wait on it: they lease or start VMs of their own.

How it spends the pool (warm VMs first, early release, demand declared while work is queued, --budget-vmh a day) is
the generic treadmill's. Under <main checkout>/runs/treadmill: cache.jsonl (every task's verdict), commits/<sha>/ (each
benchmark's rounds and state, the fuzz and mutants' results), subs/<name>/ (submissions), trees/<sha> (worktrees of
main's commits), vmh.jsonl, digest/<day>.md, status.json, treadmill.log.
"""
import argparse
import contextlib
import hashlib
import json
import math
import os
import pathlib
import re
import subprocess
import sys
import threading
import time

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import boat  # noqa: E402  (the tool's, configured for this repo)
from supercomputer import config  # noqa: E402
from supercomputer import treadmill as T  # noqa: E402
from supercomputer.treadmill import Batch, append, append_many, jl, log, py_item, sh_item, today  # noqa: E402,F401

TM = T.use()
MAIN = config.main_checkout(HERE.parent)
CLIENT = os.environ.get("SUPERCOMPUTER_TREADMILL_CLIENT", "treadmill")  # (a test treadmill beside the real one: a name of its own)
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
SWEEP_HOURS = 24  # a sweep's commit is replaced by main's at the latest after this long


def git(*a, cwd=MAIN) -> str:
    return subprocess.run(["git", "-C", str(cwd), *a], capture_output=True, text=True, check=True).stdout.strip()


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
        if self.tm.sample:  # (a test: the first few tasks)
            ids = ids[:self.tm.sample]
        solved, refused, seen = self.tm.cache.solved(self.commit, self.bench), self.tm.cache.refused(self.commit, self.bench), self.tm.cache.seen(self.commit, self.bench, config)
        rdir = self.dir / f"{budget}-{variant}"
        rdir.mkdir(parents=True, exist_ok=True)
        # (a round cut short, the treadmill stopped: its rows so far are kept, and only the rest run again)
        had = [r for r in jl(rdir / "results.jsonl") if r.get("answer") != "error"]
        done_ = {r.get("task") for r in had}
        todo = [t for t in ids if t not in solved and t not in refused and t not in seen and t not in done_]
        if not todo:
            if had:
                self.verdicts(rdir, config, "")
            return self.finish_round(config, 0)
        env = VARIANTS[variant]
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
        rows: list = list(had)
        lock = threading.Lock()
        (rdir / "results.jsonl").write_text("".join(json.dumps(r) + "\n" for r in had))

        def on_row(it, row):
            with lock:
                res = row.get("result")
                if isinstance(res, dict):
                    res = [res]
                res = res or [{"tool": "gdp", "task": todo[int(it["name"].rsplit("-", 1)[1])], "answer": "error", "seconds": -1, "err": str(row.get("error", ""))[:300]}]
                rows.extend(res)
                append_many(rdir / "results.jsonl", res)

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
        n = vms * SLOTS * 8
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


# ---------------------------------------------------------------------------------------------- the controller
class Treadmill(T.Treadmill):
    """The generic loop (T.Treadmill.step: the floor, the queue, the main chains, the queue again, backlogs, the
    fill) with this repo's chains: (b) soundness as the floor and the fill, (a) the sweeps as the main chains."""

    CLIENT = CLIENT

    def __init__(self, vms: int, budget_vmh, quiet: int, nogain: int, benches: str = "", sample: int = 0, sound: bool = True, modal: bool = True, max_wait: int = 900,
                 max_vms: int = 0, step_vms: int = 4, backlog_hours: float = 2.0):
        super().__init__(vms, budget_vmh, quiet, modal, max_wait, max_vms, step_vms, backlog_hours)
        self.nogain = nogain
        self.benches = [b for b in benches.split(",") if b] or list(BENCHES)
        self.sample, self.sound_on = sample, sound
        self.commit, self.tree, self.sweeps, self.sound, self.head = None, None, {}, None, None

    def tree_of(self, sha: str) -> pathlib.Path:
        """A worktree of main's commit (with its submodules); of the others, those of the sweeps' commit and the two
        newest are kept."""
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
        keep = {sha[:12], (self.state.get("sweep") or "")[:12]}
        for old in [p for p in sorted((TM / "trees").iterdir(), key=lambda p: p.stat().st_mtime)[:-2] if p.name not in keep]:
            with contextlib.suppress(Exception):
                git("worktree", "remove", "--force", str(old))
        return path

    def poll(self):
        head = git("rev-parse", "main")
        if head != self.head and self.sound_on:  # soundness work follows main at once
            log(f"main is {head[:12]}: soundness work at it")
            self.head = head
            self.sound = Soundness(self, head, self.tree_of(head))
        # the sweeps keep their commit until every benchmark's chain is done (or SWEEP_HOURS pass), then take main's:
        # main moves several times an hour, and a chain restarted at each commit would never get past its first round
        sw = self.state.get("sweep")
        stale = not sw or (all(s.state["done"] for s in self.sweeps.values()) and self.sweeps) or time.time() - self.state.get("sweep_t", 0) > SWEEP_HOURS * 3600
        if stale and sw != head and not any(b.chain == "a" and not b.done for b in self.batches):
            sw = None
        if not sw or not self.sweeps:
            if not sw:
                self.state.update(sweep=head, sweep_t=time.time())
                self.save_state()
                sw = head
                log(f"sweeps at {head[:12]}")
            self.commit, self.tree = sw, self.tree_of(sw)
            self.sweeps = {b: Sweep(self, sw, self.tree, b) for b in self.benches}
        for s in self.sweeps.values():
            s.poll()

    def floor(self, free: int) -> int:
        if free > 0 and not self.want("b") and self.sound_on:  # (b)'s floor: one VM
            self.batches.append(self.sound.batch(1))
            free -= 1
        return free

    def main_chains(self, free: int) -> int:
        live = max(1, sum(1 for sw in self.sweeps.values() if not sw.state["done"]))
        for sw in self.sweeps.values():  # (a): the next round of each benchmark, a fair share of the pool to start with
            if free <= 0:
                break
            b = sw.next_round(min(free, max(1, (self.vms - 1) // live)))
            if b:
                self.batches.append(b)
                free -= b.vms
        return free

    def fill(self, free: int) -> int:
        if free > 0 and self.sound_on and len(self.want("b")) < 1 + self.floor_vms // 2:  # (b) fills the rest (the floor busy)
            b = self.sound.batch(min(free, 2))
            self.batches.append(b)
            free -= b.vms
        return free

    def status_extra(self) -> dict:
        return {"commit": self.commit, "sweeps": {k: s.state for k, s in self.sweeps.items()}}


# ------------------------------------------------------------------------------------------------- the digest
def sections(day: str) -> list[str]:
    """The day's new solves (and the config that solved each), regressions against the commit before, wrong answers,
    and the soundness work (the generic digest adds the queue and the pool)."""
    rows = [r for r in jl(TM / "cache.jsonl") if time.strftime("%Y-%m-%d", time.gmtime(r["t"])) == day]
    allrows = jl(TM / "cache.jsonl")
    out = []
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
    mt = list({(r["hash"], r["id"]): r for r in jl(TM / "mutants.jsonl") if time.strftime("%Y-%m-%d", time.gmtime(r["t"])) == day}.values())
    bad = [r for r in fz if r["code"] != 0]
    unsound = [r for r in bad if re.search(r"^\s*(error: )?(Error: )?UNSOUND", r.get("tail", ""), re.M)]  # (thrown, not quoted from the source)
    out += ["", "## Soundness", f"- fuzz: {len(fz)} seeds ({', '.join(f'{k} {sum(1 for r in fz if r["kind"] == k)}' for k in FUZZ)}), "
            + (f"**{len(unsound)} UNSOUND**; " if unsound else "") + (f"{len(bad)} failed (" + ("none unsound: " if not unsound else "") + "a count a test expects at its own seeds, e.g. accepted > 0): " + ", ".join(f"{r['kind']} seed {r['seed']} (exit {r['code']}: {next((l.strip() for l in r.get('tail', '').splitlines() if l.strip().startswith(('error', '(fail)'))), '')[:120]})" for r in bad[:10]) if bad else "none failed"),
            f"- mutants: {len(mt)} run, {sum(1 for r in mt if not r.get('killedBy'))} survived" + "".join(f"\n  - survived: {r['id']} {r['where']} {r['change']}" for r in mt if not r.get("killedBy"))]
    return out


def digest(day: str, quiet: bool = False) -> str:
    return T.digest(day, quiet, sections=sections)


def main(argv: list[str]):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--vms", type=int, default=8, help="the floor: VMs kept busy (the soundness fill keeping them so)")
    r.add_argument("--max-vms", type=int, default=0, help="the ceiling of its growth on a backlog (default 4x the floor)")
    r.add_argument("--step-vms", type=int, default=4, help="VMs added a step (one step per 5 minutes while the backlog lasts)")
    r.add_argument("--backlog-hours", type=float, default=2.0, help="grow while the sweeps' and the queue's work would take longer on the floor")
    r.add_argument("--hours", type=float, default=0)
    r.add_argument("--budget-vmh", default="auto", help="default-VM hours a day (a large VM counts 2); auto: the plan's prepaid hours left over the days to its period's end")
    r.add_argument("--quiet", type=int, default=1500)
    r.add_argument("--nogain", type=int, default=3)
    r.add_argument("--benches", default="", help="these benchmarks only (default: all)")
    r.add_argument("--sample", type=int, default=0, help="a test: each benchmark's first N tasks")
    r.add_argument("--no-soundness", action="store_true")
    r.add_argument("--no-modal", action="store_true", help="what boat can't run waits for boat (default: Modal runs it)")
    r.add_argument("--max-wait", type=int, default=900, help="seconds a batch waits for a boat VM before Modal")
    s = sub.add_parser("submit")
    s.add_argument("jobs")
    s.add_argument("--tree", default=".")
    s.add_argument("--name", default="")
    s = sub.add_parser("results")
    s.add_argument("name")
    sub.add_parser("status")
    s = sub.add_parser("digest")
    s.add_argument("--day", default="")
    a = ap.parse_args(argv)
    if a.cmd == "run":
        Treadmill(a.vms, a.budget_vmh, a.quiet, a.nogain, a.benches, a.sample, not a.no_soundness, not a.no_modal, a.max_wait, a.max_vms, a.step_vms, a.backlog_hours).run(a.hours, digest)
    elif a.cmd == "submit":
        T.submit(a.jobs, a.tree, a.name)
    elif a.cmd == "results":
        T.results(a.name)
    elif a.cmd == "status":
        print((TM / "status.json").read_text() if (TM / "status.json").exists() else "not running")
    elif a.cmd == "digest":
        digest(a.day or today())


if __name__ == "__main__":
    import fanout
    fanout.reexec_with_modal()  # (Modal runs what boat can't: the interpreter that has its client)
    main(sys.argv[1:])
