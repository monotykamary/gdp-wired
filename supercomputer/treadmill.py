"""gdp-wired's treadmill: the supercomputer's treadmill (~/.local/share/supercomputer, its generic batches, cache,
queue and digest) with this repo's chains. Every result is cached by (commit, benchmark, task, config), so nothing
unchanged runs twice; a chain whose inputs (INPUTS: the files its runs read) are a commit's it already ran is skipped.

    python3 supercomputer/treadmill.py run [--vms 8] [--max-vms 32] [--step-vms 4] [--backlog-hours 2] [--budget-vmh auto]
                                           [--quiet 1500] [--nogain 3] [--chains sweep,speed,...] [--sample N] [--hours H]
    python3 supercomputer/treadmill.py idea --name N --bench chc --tasks <file|glob> --env GDP_X=1 [--env ...] --budget 300 [--tree DIR]
    python3 supercomputer/treadmill.py idea-results <name>          the idea's table: gained and lost against the base, per task
    python3 supercomputer/treadmill.py plan [--bench chc]           what the sweep would run next at each budget, and why (no launch)
    python3 supercomputer/treadmill.py submit <jobs.json> [--tree DIR] [--name NAME] | results <name> | status | digest [--day D]

The chains, each at main's newest commit whose inputs changed (a commit main passed meanwhile is skipped), highest
first:
  speed   (b) each benchmark's solved set at 60 s, timing placement (alone on its VM), against the previous run: a
          task 1.5x slower (and 1 s more) or lost is flagged. These runs are the commit's 60 s round for those tasks.
  ic3syn  (c) IC3Syn's 29 protocols and their broken variants at 60 s (timing placement) and 300 s: a broken variant
          proven is a SOUNDNESS ALERT. These are the sweep's IC3Syn rounds at 60 and 300 s.
  rw      (d) the real-world corpus (the bar's rw group: research/realworld/jobs.ts), verdict changes flagged.
  sweep   (a) per benchmark (CHC-COMP, TermComp ITS, SV-COMP, TIP, IC3Syn): the whole set at 60 s, then the unsolved
          at 300 s and 900 s under every search variant (VARIANTS: each knob the prover reads, set the other way) and
          pairs of the most promising, in the order of their gains in the cache (variants never tried yet explored
          once; tried ones with no gain parked, tried again every REVISIT sweeps); a budget stops after --nogain tried
          rounds in a row that solve nothing new. A task solved past 60 s (a target) runs with timing placement, and
          its per-stage profile is kept (e: the target list).
  ten     (f) the ten core protocols (research/protocols) at 60 s, 20 runs each, timing placement, launched last.
  sound   the floor and the fill: kernel, CDCL and tamper fuzz at fresh seeds, the extractor correspondence fuzz (each
          reader's own check harness, core/<lang>, at a fresh seed: the extracted rule against the real code on random
          requests), and at a commit that changes kernel/kernel.ts or core/check.ts its mutants. A NEW survivor (not
          killed, not listed equivalent in kernel/MUTANTS.md, never a survivor before) is an alert.
  ideas   a lane's or terra's "knobs K on tasks S at budget B" (`idea`), the submission class, cached like the rest.

Under <main checkout>/runs/treadmill (the controller's: ~/sc/treadmill): cache.jsonl, commits/<sha>/ (rounds, runs),
chains/<chain>.json, inputs.json, speed.jsonl, profiles.jsonl, ten.jsonl, fuzz.jsonl, xfuzz.jsonl, mutants.jsonl,
spend.jsonl (VM-hours by chain), subs/ (submissions and ideas), digest/<day>.md and .json, status.json.
"""
import argparse
import calendar
import contextlib
import fnmatch
import hashlib
import json
import math
import os
import pathlib
import re
import statistics
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
DEFAULT_VCPU = boat.TYPES["default"][0]
knob = lambda k, d: type(d)(os.environ.get(f"GDPW_TM_{k}") or d)  # noqa: E731  (the chains' knobs, by environment)

# ------------------------------------------------------------------------------------------- the search's variants
# Every search knob the prover reads, set the other way (core/infer.ts, core/interp.ts, core/bmc.ts, core/cyclic.ts,
# core/counts.ts, kernel/prove.ts, kernel/cdcl.ts, kernel/epr.ts), and the benchmarks whose search reads it (those whose
# shard takes an environment: CHC, ITS and IC3Syn). Left out: knobs that take an unconfirmed model as one
# (GDP_REAL_MODELS=0, GDP_STRICT=0: wrong refutations, by their own comments), caches only (GDP_TREES, GDP_MEMO_ALPHA),
# traces and logs, and the trusted reader's GDP_READER_CLEAN.
E, IC = ("chc", "its", "ic3syn"), ("ic3syn",)
KNOBS = [
    # core/cyclic.ts: cyclic proofs
    ("cyclic", {"GDP_CYCLIC": "1"}, E), ("cyclic-lax", {"GDP_CYCLIC": "1", "GDP_CYCLIC_LAX": "1"}, E),
    ("cyclic-noslice", {"GDP_CYCLIC": "1", "GDP_CYCLIC_SLICE": "0"}, E), ("certsearch", {"GDP_CERT_SEARCH": "1"}, E), ("cert30", {"GDP_CERT_MS": "30000"}, E),
    # core/infer.ts: top-down, the join, its pool, the engine
    ("td", {"GDP_TD": "1"}, E), ("notd", {"GDP_TD": "0"}, E), ("td-decided", {"GDP_TD": "1", "GDP_TD_DECIDED": "1"}, E), ("td-noorder", {"GDP_TD_ORDER": "0"}, E),
    ("nojoin", {"GDP_JOIN": "0"}, E), ("join-noatoms", {"GDP_JOIN_ATOMS": "0"}, E), ("join-nocore", {"GDP_JOIN_CORE": "0"}, E),
    ("join-nocubes", {"GDP_JOIN_CUBES": "0"}, E), ("join-nodown", {"GDP_JOIN_DOWN": "0"}, E), ("join-nonevers", {"GDP_JOIN_NEVERS": "0"}, E),
    ("join-noprime", {"GDP_JOIN_PRIME": "0"}, E), ("join-nolevels", {"GDP_JOIN_LEVELS": "0"}, E), ("join-noclocks", {"GDP_JOIN_CLOCKS": "0"}, E),
    ("nopool", {"GDP_POOL": "0"}, E), ("pool-nostop", {"GDP_POOL_STOP": "0"}, E), ("pool-long", {"GDP_POOL_MS": "90000"}, E),
    ("pool-wide", {"GDP_POOL_STATES": "4000"}, E), ("pool-quiet", {"GDP_POOL_QUIET": "600"}, E),
    ("nohalves", {"GDP_INFER_HALVES": "0"}, E), ("nocone", {"GDP_IC3_CONE": "0"}, E), ("engine80", {"GDP_ENGINE_SHARE": "0.8"}, E),
    # core/interp.ts, core/bmc.ts: interpolation and bounded search
    ("clausal", {"GDP_ITP_CLAUSAL": "1"}, E), ("itp-nodag", {"GDP_ITP_DAG": "0"}, E), ("itp-weak", {"GDP_ITP_STRONG": "0"}, E),
    ("itp-notidy", {"GDP_ITP_TIDY": "0"}, E), ("imc-norelax", {"GDP_IMC_RELAX": "0"}, E), ("bmc-norelax", {"GDP_BMC_RELAX": "0"}, E),
    ("bmc-noinc", {"GDP_BMC_INC": "0"}, E), ("bmc-notidy", {"GDP_BMC_TIDY": "0"}, E),
    # kernel/prove.ts, kernel/cdcl.ts: the CDCL's share, its LP, the memo, instances
    ("cdcl90", {"GDP_CDCL_SHARE": "0.9"}, E), ("cdcl50", {"GDP_CDCL_SHARE": "0.5"}, E), ("quick64", {"GDP_QUICK_CAP": "64"}, E),
    ("nolp", {"GDP_CDCL_LP": "0"}, E), ("lp-deep", {"GDP_CDCL_BASE": "2000", "GDP_CDCL_GREEDY": "800"}, E),
    ("lp-fill", {"GDP_CDCL_FILL": "16", "GDP_CDCL_GROW": "8"}, E), ("cdcl-batch64", {"GDP_CDCL_BATCH": "64"}, E), ("memo16", {"GDP_MEMO_CAP": "16"}, E),
    ("dltrig", {"GDP_DLTRIG": "1"}, E), ("notrigger", {"GDP_TRIGGER": "0"}, E), ("nounits", {"GDP_UNITS": "0"}, E), ("nosorted", {"GDP_SORTED": "0"}, E),
    # kernel/epr.ts, core/counts.ts: the protocols' EPR and counts
    ("noepr", {"GDP_EPR": "0"}, IC), ("epr-noinc", {"GDP_EPR_INC": "0"}, IC),
    ("k-pairs", {"GDP_K_PAIRS": "1"}, IC), ("k-ts", {"GDP_K_TS": "1"}, IC), ("k-cap64", {"GDP_K_CAP": "64"}, IC),
    ("k-rounds4", {"GDP_K_ROUNDS": "4"}, IC), ("k-nokeyed", {"GDP_K_KEYED": "0"}, IC), ("k-noflagts", {"GDP_K_FLAGTS": "0"}, IC),
]
VARIANTS = {"base": {}, **{n: env for n, env, _ in KNOBS}}
SCOPE = {n: s for n, _, s in KNOBS}
PAIR_TOP, PAIRS_MAX = knob("PAIR_TOP", 4), knob("PAIRS_MAX", 6)  # pairs among the top 4 singles with a gain, 6 at most
REVISIT = knob("REVISIT", 5)  # a parked variant (tried, never a gain) runs again once every 5 sweeps of its benchmark
# the sweep's stages after the 60 s base: the variants at 60 s (the base ran), then base and variants at 300 s and 900 s;
# untried variants are explored at 60 s and 300 s, 900 s takes only what gained
STAGES = [int(b) for b in knob("STAGES", "60,300,900").split(",")]
EXPLORE = (60, 300)
PLAN_MAX = knob("PLAN_MAX", 0)  # (a pilot: a stage's plan cut to this many rounds)
# a benchmark: its runner, the bar's view of its results (gates/bar-lib.ts); `env`: its shard takes the variants'
# environment (SV-COMP's shard takes none; TIP's search reads none of the knobs: their rounds are by budget alone)
BENCHES = {
    "chc": {"module": "compare/chc/modal_chc.py", "view": "chc", "env": True},
    "its": {"module": "compare/term/modal_term.py", "view": "its", "env": True},
    "sv": {"module": "compare/term/modal_sv.py", "view": "sv", "env": False},
    "tip": {"module": "compare/tip/modal_tip.py", "view": "tip", "env": False},
    "ic3syn": {"sh": True, "env": True},
}
TIP_SETS = ["isaplanner", "prod", "tip2015", "grammars"]
REFUSED = ("unsupported", "refused")
SWEEP_HOURS = 24  # a sweep's commit is replaced by main's at the latest after this long

# ---------------------------------------------------------------------------------------- inputs (skip unchanged)
# The files a chain's runs read: a commit whose files are a commit's the chain already ran gives the same answers, so
# the chain skips it. (*.md, tests, job lists and results are no input; package.json without its version.)
COMMON = ("core/", "kernel/", "interchange/", "lean-kernel/", "examples/", "vendor/", "types/", "tsconfig.json", "bun.lock", "package.json")
INPUTS = {"chc": COMMON + ("compare/chc/",), "its": COMMON + ("compare/term/",), "sv": COMMON + ("compare/term/",), "tip": COMMON + ("compare/tip/",),
          "ic3syn": COMMON + ("research/protocols/",), "ten": COMMON + ("research/protocols/",),
          "rw": COMMON + ("research/realworld/", "research/langs/", "research/sol/", "research/protocols/")}
NOT_INPUT = re.compile(r"\.md$|\.test\.ts$|^kernel/mutants\.ts$|(^|/)(jobs[^/]*\.json|results[^/]*\.(json|md|tsv)|RESULTS[^/]*)$")
_fp: dict = {}
_fp_lock = threading.Lock()


def git(*a, cwd=MAIN) -> str:
    return subprocess.run(["git", "-C", str(cwd), *a], capture_output=True, text=True, check=True).stdout.strip()


def fingerprint(commit: str, chain: str) -> str:
    """The hash of a chain's input files at a commit (their blob ids; submodules by commit)."""
    with _fp_lock:
        if not _fp:
            with contextlib.suppress(Exception):
                _fp.update(json.loads((TM / "inputs.json").read_text()))
        if chain in _fp.get(commit, {}):
            return _fp[commit][chain]
        tree = git("ls-tree", "-r", commit)
        out = {}
        for ch, prefixes in INPUTS.items():
            h = hashlib.sha256()
            for line in tree.splitlines():
                meta, path = line.split("\t", 1)
                if path.startswith(prefixes) and not NOT_INPUT.search(path):
                    blob = meta.split()[2]
                    if path == "package.json":
                        blob = hashlib.sha256(re.sub(r'"version":\s*"[^"]*"', "", git("show", f"{commit}:package.json")).encode()).hexdigest()
                    h.update(f"{path} {blob}\n".encode())
            out[ch] = h.hexdigest()[:16]
        _fp[commit] = out
        with contextlib.suppress(Exception):
            (TM / "inputs.json").write_text(json.dumps(_fp))
        return out[chain]


# -------------------------------------------------------------------------------------------------- helpers
def budget_of(cfg: str) -> int:
    return int(cfg.split(":", 1)[0])


def variant_of(cfg: str) -> str:
    return cfg.split(":", 1)[1]


def env_of(variant: str) -> dict:
    """A variant's environment: a name in VARIANTS, a pair `a+b`, or an idea's `env:K=V,K=V`."""
    if variant.startswith("env:"):
        return dict(kv.split("=", 1) for kv in variant[4:].split(",") if kv)
    out = {}
    for v in variant.split("+"):
        out.update(VARIANTS[v])
    return out


def label_of(env: dict) -> str:
    """An environment's config name: a variant's (or a pair's) when it is one, else `env:K=V,...` (sorted)."""
    for v, e in VARIANTS.items():
        if e == env:
            return v
    names = [n for n in VARIANTS if n != "base"]
    for i, a in enumerate(names):
        for b in names[i + 1:]:
            if {**VARIANTS[a], **VARIANTS[b]} == env and not set(VARIANTS[a]) & set(VARIANTS[b]):
                return f"{a}+{b}"
    return "env:" + ",".join(f"{k}={v}" for k, v in sorted(env.items()))


def family(task: str) -> str:
    return task.rsplit("/", 1)[0] if "/" in task else task.split("_")[0]


def profile_of(stages) -> dict:
    """A runner row's stages (each with its cumulative ms) as ms per stage."""
    out, last = {}, 0
    for s in stages or []:
        if isinstance(s, dict) and isinstance(s.get("ms"), (int, float)) and s.get("stage"):
            out[s["stage"]] = out.get(s["stage"], 0) + max(0, s["ms"] - last)
            last = s["ms"]
    return out


def tracked(tm, chain: str, label: str, on_row):
    """on_row, and each finished item's VM time to spend.jsonl by chain: a timing item counts its whole VM."""
    def f(it, row):
        with contextlib.suppress(Exception):
            secs = float(row.get("seconds") or 0)
            if secs > 0:
                pl = row.get("placement") or {}
                vcpus = pl.get("vm_vcpus", boat.TYPES[boat.VM_TYPE][0]) if (pl.get("exclusive") or it.get("timing")) else it.get("weight", 1) * boat.SLOT_CPU
                append(TM / "spend.jsonl", {"t": round(time.time(), 1), "day": today(), "chain": chain, "label": label, "secs": round(secs, 1),
                                            "vmh": round(secs * vcpus / DEFAULT_VCPU / 3600, 4), **({"cpu": pl.get("cpu")} if pl.get("cpu") else {})})
        on_row(it, row)
    return f


def shard_item(name: str, bench: str, tasks: list, budget: int, env: dict, tree: pathlib.Path, timing=False, est=None) -> dict:
    """One runner call (a shard of tasks, SV-COMP's one task) at a budget, in an environment."""
    spec = BENCHES[bench]
    if spec.get("sh"):  # IC3Syn: run.ts on one protocol, its search only
        pre = " ".join(f"{a}={b}" for a, b in env.items())
        it = sh_item(name, f"bun install --frozen-lockfile >/dev/null 2>&1; {pre} bun research/protocols/ic3syn/run.ts --ms {budget * 1000} --only '{tasks[0]}' --skip broken 2>/dev/null | tail -1",
                     ".", budget * 3 + 120, est or budget)
    else:
        envs = ",".join(f"{a}={b}" for a, b in env.items())
        args = {"chc": lambda: ["gdp", tasks, budget, envs], "its": lambda: ["gdp", tasks, budget, envs], "sv": lambda: ["gdp", tasks[0], budget],
                "tip": lambda: ["gdp", tasks, budget, {"*": [f"--env={a}={b}" for a, b in env.items()]} if env else {}]}[bench]()
        it = py_item(name, spec["module"], "shard", args, budget * len(tasks) + 600, est or budget * len(tasks), tree)
    if timing:
        it["timing"] = True
    return it


def read_obs(rdir: pathlib.Path, bench: str, tree: pathlib.Path) -> dict:
    """A round's verdicts as the bar reads them (gates/bar.ts read <view> --tasks): {task: {answer, solved, wrong, secs}}."""
    p = subprocess.run(["bun", str(HERE.parent / "gates" / "bar.ts"), "read", BENCHES[bench]["view"], str(rdir), "--tree", str(tree), "--tasks"],
                       capture_output=True, text=True, timeout=300)
    return json.loads(p.stdout.strip().split(" ", 1)[1]) if p.returncode == 0 and p.stdout.strip() else {}


def put(tm, commit: str, bench: str, task: str, cfg: str, o: dict, source: str = ""):
    tm.cache.put({"commit": commit, "bench": bench, "task": task, "config": cfg, "answer": o.get("answer"), "solved": bool(o.get("solved")),
                  "wrong": bool(o.get("wrong")), "secs": o.get("secs"), "t": round(time.time(), 1), **({"source": source} if source else {})})
    if o.get("wrong"):
        log(f"WRONG: {bench} {task} at {cfg} ({commit[:12]}): {o.get('answer')}")


# ------------------------------------------------------------------------------------------ the shared task lists
LISTS = {  # (a list a chain needs at a commit, fetched by an item on boat, kept in commits/<sha>/lists/<key>.json)
    "ic3syn": "bun install --frozen-lockfile >/dev/null 2>&1; bun -e \"import {protocols} from './research/protocols/ic3syn/models.ts'; console.log(JSON.stringify(protocols.map(p => p.id)))\" | tail -1",
    "ten": "bun install --frozen-lockfile >/dev/null 2>&1; bun -e \"import {protocols} from './research/protocols/models.ts'; console.log(JSON.stringify(protocols.map(p => p.id)))\" | tail -1",
    "rw": "bun install --frozen-lockfile >/dev/null 2>&1; bun research/realworld/jobs.ts",
}


class Lists:
    """Task lists by (commit, key): a benchmark's (its runner's `tasks`), IC3Syn's and the ten's ids, the real-world
    corpus' jobs. get() answers the list, or None while the item fetching it runs (once, retried after 10 minutes)."""

    def __init__(self, tm):
        self.tm, self.fetching, self.retry = tm, {}, {}
        self.lock = threading.Lock()

    def path(self, commit: str, key: str) -> pathlib.Path:
        old = TM / "commits" / commit[:12] / key / "tasks.json"  # (the sweeps' place before)
        return old if old.exists() else TM / "commits" / commit[:12] / "lists" / f"{key}.json"

    def get(self, commit: str, tree: pathlib.Path, key: str):
        f = self.path(commit, key)
        if f.exists():
            return json.loads(f.read_text())
        with self.lock:
            b = self.fetching.get((commit, key))
            if b is not None and b.done:  # (its batch ended with no list: boat couldn't run it, or its after() had nothing)
                self.fetching.pop((commit, key), None)
                self.retry[(commit, key)] = time.time() + 600
            if (commit, key) in self.fetching or time.time() < self.retry.get((commit, key), 0):
                return None
            f.parent.mkdir(parents=True, exist_ok=True)

            def done(data):
                if data is None:
                    self.retry[(commit, key)] = time.time() + 600
                else:
                    f.write_text(json.dumps(data))
            if key in LISTS:
                def after(logs):
                    out = logs.get(f"list-{key}", {}).get("out", "").strip()
                    try:
                        done(json.loads(out if key == "rw" else out.splitlines()[-1]))
                    except Exception:
                        log(f"{commit[:12]} list {key}: unreadable ({out[-200:]!r})")
                        done(None)
                item = sh_item(f"list-{key}", LISTS[key], ".", 600, 30)
                b = Batch(self.tm, f"lists {commit[:12]} {key}", "a", [item], 1, lambda it, row: None, root=tree, after=after)
            else:
                spec = BENCHES[key]

                def on_row(it, row):
                    if row.get("code") == 0 and "result" in row:
                        got = row["result"]
                        done(list(got["tasks"]) if key == "tip" else got)
                    else:
                        log(f"{commit[:12]} list {key}: {str(row.get('error', row))[-300:]}")
                        done(None)
                b = Batch(self.tm, f"lists {commit[:12]} {key}", "a", [py_item("tasks", spec["module"], "tasks", [TIP_SETS] if key == "tip" else [], 900, 30, tree)], 1, on_row, root=tree)
            self.fetching[(commit, key)] = b
            self.tm.batches.append(b)
            return None


def task_ids(got) -> list[str]:
    if isinstance(got, dict):
        got = got.get("tasks", [])
    return [t if isinstance(t, str) else t["task"] for t in got]


def task_specs(got) -> dict:
    if isinstance(got, dict):
        got = got.get("tasks", [])
    return {(t if isinstance(t, str) else t["task"]): t for t in got}


# ----------------------------------------------------------------------------------- the ranking of the variants
def ranking(cache, bench: str, budget: int) -> dict:
    """Each config's record on a benchmark at a budget, over every commit in the cache: the commits it ran at (`runs`)
    and the tasks it solved that the base at that budget or less didn't (`gains`)."""
    by: dict = {}
    base_solved: dict = {}
    for (c, b, t, cfg), r in cache.d.items():
        if b != bench or not cfg[:1].isdigit() or str(r.get("source", "")).startswith("idea") or c.startswith("tree:"):
            continue  # (an idea's few tasks are no round of the sweep's: they don't rank its variants)
        bud, v = budget_of(cfg), variant_of(cfg)
        if v in ("base", "timing", "full") and bud <= budget and r["solved"]:
            base_solved.setdefault(c, set()).add(t)
        if bud == budget and (v in VARIANTS or "+" in v) and v != "base":
            by.setdefault(v, {}).setdefault(c, set())
            if r["solved"]:
                by[v][c].add(t)
    out = {}
    for v, cs in by.items():
        out[v] = {"runs": len(cs), "gains": sum(len(ts - base_solved.get(c, set())) for c, ts in cs.items())}
    return out


def plan(cache, bench: str, budget: int, sweeps_done: int) -> list[tuple[str, str]]:
    """The variants to run at a budget, best first, each with why: those with gains by their rate (gains a run; at
    900 s their gains at 300 s count too), pairs of the top PAIR_TOP of them (keys apart, PAIRS_MAX at most, none
    parked), then the untried (at 60 s and 300 s only: 900 s takes what gained), then this sweep's revisits of the
    parked."""
    if not BENCHES[bench]["env"]:
        return [("base", "")]
    st = ranking(cache, bench, budget)
    st300 = ranking(cache, bench, 300) if budget == 900 else {}
    singles = [v for v in VARIANTS if v != "base" and bench in SCOPE[v]]
    score = lambda v: (st.get(v, {}).get("gains", 0) + st300.get(v, {}).get("gains", 0)) / max(1, st.get(v, {}).get("runs", 0))  # noqa: E731
    gained = sorted([v for v in singles if st.get(v, {}).get("gains") or st300.get(v, {}).get("gains")], key=lambda v: -score(v))
    out = [("base", "")] + [(v, f"{st.get(v, {}).get('gains', 0)} gains in {st.get(v, {}).get('runs', 0)} runs") for v in gained]
    top = gained[:PAIR_TOP]
    pairs = []
    for i, a in enumerate(top):
        for b in top[i + 1:]:
            p = f"{a}+{b}"
            if set(VARIANTS[a]) & set(VARIANTS[b]):
                continue
            ps = st.get(p, {})
            if ps.get("runs", 0) >= 2 and not ps.get("gains"):
                continue  # (a pair tried twice with no gain: parked)
            pairs.append((p, f"pair of the top {len(top)}" + (f"; {ps.get('gains', 0)} gains in {ps.get('runs')} runs" if ps.get("runs") else "")))
    out += sorted(pairs, key=lambda x: -(st.get(x[0], {}).get("gains", 0) / max(1, st.get(x[0], {}).get("runs", 0))))[:PAIRS_MAX]
    if budget in EXPLORE:
        out += [(v, "untried") for v in singles if v not in st]
    parked = [v for v in singles if v in st and not st[v]["gains"] and (budget in EXPLORE or st300.get(v, {}).get("gains"))]
    out += [(v, f"revisit (0 gains in {st[v]['runs']} runs)") for v in parked if int(hashlib.sha256(v.encode()).hexdigest(), 16) % REVISIT == sweeps_done % REVISIT]
    return out


def targets_of(cache) -> dict:
    """The target list: per benchmark, tasks solved past 60 s and never at 60 s at the newest commit that ran them at 60
    s, each with the config (and commit) of its latest solve."""
    at60: dict = {}
    past: dict = {}
    for (c, b, t, cfg), r in cache.d.items():
        if not cfg[:1].isdigit() or b.endswith("-broken"):
            continue
        if budget_of(cfg) == 60:
            k = (b, t)
            if k not in at60 or r["t"] > at60[k][0]:
                at60[k] = (r["t"], r["solved"])
        elif r["solved"]:
            k = (b, t)
            if k not in past or r["t"] > past[k]["t"]:
                past[k] = {"t": r["t"], "config": cfg, "commit": c, "secs": r.get("secs")}
    out: dict = {}
    for (b, t), p in past.items():
        if not at60.get((b, t), (0, False))[1]:
            out.setdefault(b, {})[t] = p
    return out


# -------------------------------------------------------------------------------------------- (a) the sweeps
class Sweep:
    """A benchmark's rounds at a commit (commits/<sha>/<bench>/state.json): 60 s on every task (the tasks the speed
    chain times are its, IC3Syn's are the ic3syn chain's), then the plan's variants at 300 s and 900 s on the unsolved."""

    def __init__(self, tm, commit: str, tree: pathlib.Path, bench: str):
        self.tm, self.commit, self.tree, self.bench, self.spec = tm, commit, tree, bench, BENCHES[bench]
        self.dir = TM / "commits" / commit[:12] / bench
        self.dir.mkdir(parents=True, exist_ok=True)
        self.state = json.loads((self.dir / "state.json").read_text()) if (self.dir / "state.json").exists() else \
            {"round": 0, "nogain": 0, "done": False, "gains": [], "plan": [[60, "base", ""]], "stage": -1}
        if "plan" not in self.state:  # (a sweep from before the plan: its 60 s and 300 s rounds as they were, 900 s planned)
            old = ["base"] + (["cyclic", "td", "clausal", "cdcl90", "nojoin"] if self.spec["env"] else [])
            self.state.update(plan=[[60, "base", ""]] + [[300, v, "as before"] for v in old], stage=STAGES.index(300) if 300 in STAGES else len(STAGES))
            self.state["round"] = min(self.state["round"], len(self.state["plan"]))
            if self.state.get("done") and self.state["round"] < len(self.state["plan"]):
                self.state["done"] = self.state["nogain"] >= self.tm.nogain
        self.batch: Batch | None = None
        self.retry_at = 0.0

    def save(self):
        (self.dir / "state.json").write_text(json.dumps(self.state, indent=1))

    def extend(self) -> bool:
        """The next stage's plan (STAGES), when the last one's is spent: True if there is one."""
        st = self.state
        while st.get("stage", -1) + 1 < len(STAGES):
            st["stage"] = st.get("stage", -1) + 1
            bud = STAGES[st["stage"]]
            done_sweeps = sum(1 for p in (TM / "commits").glob(f"*/{self.bench}/state.json") if jl_one(p).get("done"))
            rounds = [[bud, v, why] for v, why in plan(self.tm.cache, self.bench, bud, done_sweeps) if not (bud == 60 and v == "base")]
            rounds = rounds[:PLAN_MAX] if PLAN_MAX else rounds
            st["nogain"] = 0
            if rounds:
                st["plan"] += rounds
                self.save()
                log(f"{self.commit[:12]} {self.bench}: the {bud} s plan: {', '.join(p[1] for p in rounds)}")
                return True
        self.save()
        return False

    def next_round(self, free: int) -> Batch | None:
        st = self.state
        if st["done"] or self.batch or time.time() < self.retry_at:
            return None
        # (--nogain tried rounds in a row with no gain end a stage's tried rounds; its untried and revisits still run)
        while st["round"] < len(st["plan"]) and st["nogain"] >= self.tm.nogain and st["plan"][st["round"]][1] != "base" \
                and st["plan"][st["round"]][2] != "untried" and not st["plan"][st["round"]][2].startswith("revisit"):
            st["round"] += 1
        if st["round"] >= len(st["plan"]) and not self.extend():
            st["done"] = True
            self.save()
            log(f"{self.commit[:12]} {self.bench}: the sweep is done")
            return None
        budget, variant, why = st["plan"][st["round"]]
        cfg = f"{budget}:{variant}"
        got = self.tm.lists.get(self.commit, self.tree, self.bench)
        if got is None:
            return None
        ids = task_ids(got)
        if self.tm.sample:  # (a test: the first few tasks)
            ids = ids[:self.tm.sample]
        claimed, wait = self.claimed(cfg)
        if wait:
            return None
        cache = self.tm.cache
        solved, refused, seen = cache.solved(self.commit, self.bench), cache.refused(self.commit, self.bench), cache.seen(self.commit, self.bench, cfg)
        rdir = self.dir / f"{budget}-{variant}"
        rdir.mkdir(parents=True, exist_ok=True)
        # (a round cut short, the treadmill stopped: its rows so far are kept, and only the rest run again)
        had = [r for r in jl(rdir / "results.jsonl") if r.get("answer") != "error"]
        done_ = {r.get("task") for r in had}
        todo = [t for t in ids if t not in solved and t not in refused and t not in seen and t not in done_ and t not in claimed]
        if not todo:
            if had:
                self.record_rows(rdir, cfg, had, self.tm.lists.get(self.commit, self.tree, self.bench))
            return self.finish_round(cfg)
        env = env_of(variant)
        by = task_specs(got)
        targets = self.tm.targets.get(self.bench, {}) if budget > 60 else {}
        items = []
        for k, t in enumerate(todo):
            items.append(shard_item(f"{self.bench}-{budget}-{variant}-{k}", self.bench, [t if self.spec.get("sh") else by[t]], budget, env, self.tree,
                                    timing=t in targets and targets[t]["config"] == cfg))
        rows: list = list(had)
        lock = threading.Lock()
        (rdir / "results.jsonl").write_text("".join(json.dumps(r) + "\n" for r in had))

        def on_row(it, row):
            with lock:
                k = int(it["name"].rsplit("-", 1)[1])
                if self.spec.get("sh"):
                    row = {**row, "task": todo[k]}
                    rows.append(row)
                    return
                res = row.get("result")
                if isinstance(res, dict):
                    res = [res]
                res = res or [{"tool": "gdp", "task": todo[k], "answer": "error", "seconds": -1, "err": str(row.get("error", ""))[:300]}]
                pl = row.get("placement") or {}
                res = [{**r, **({"placement": {"exclusive": pl.get("exclusive"), "cpu": pl.get("cpu")}} if pl else {})} for r in res]
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
                for t, o in out.items():
                    put(self.tm, self.commit, self.bench, t, cfg, o)
                    if o["solved"] and budget > 60:
                        append(TM / "profiles.jsonl", {"t": time.time(), "commit": self.commit, "bench": self.bench, "task": t, "config": cfg, "secs": o["secs"], "stages": {}})
                (rdir / "verdicts.json").write_text(json.dumps(out))
            else:
                (rdir / "tasks.json").write_text(json.dumps({"limit": budget, **got} if isinstance(got, dict) else got))
                with open(rdir / "results.jsonl", "w") as f:
                    for r in rows:
                        f.write(json.dumps(r) + "\n")
                self.record_rows(rdir, cfg, rows, got)
        vms = max(1, min(free, math.ceil(len(items) * budget / (SLOTS * 1800))))
        log(f"{self.commit[:12]} {self.bench} round {st['round']} ({cfg}{', ' + why if why else ''}): {len(items)} tasks on {vms} VMs"
            + (f", {sum(1 for i in items if i.get('timing'))} targets timed" if any(i.get("timing") for i in items) else ""))
        label = f"sweep {self.commit[:12]} {self.bench} {cfg}"
        self.batch = Batch(self.tm, label, "a", items, vms, tracked(self.tm, "sweep", label, on_row), root=self.tree, after=after, oleans=self.bench == "ic3syn")
        return self.batch

    def claimed(self, cfg: str) -> tuple[set, bool]:
        """Tasks another chain runs at this commit and config (the speed chain's solved set at 60 s, the ic3syn chain's
        60 s and 300 s), and whether to wait for it."""
        if cfg == "60:base" and self.bench in SPEED_BENCHES and "speed" in self.tm.chains:
            return self.tm.speed.claim(self.commit, self.bench)
        if cfg in ("60:base", "300:base") and self.bench == "ic3syn" and "ic3syn" in self.tm.chains:
            s = self.tm.ic3.want(self.commit)
            return set(), s in ("pending", "running")
        return set(), False

    def record_rows(self, rdir: pathlib.Path, cfg: str, rows: list, got):
        obs = read_obs(rdir, self.bench, self.tree)
        for t, o in obs.items():
            put(self.tm, self.commit, self.bench, t, cfg, o)
        if budget_of(cfg) > 60:  # (each task solved past 60 s: its per-stage profile, for the target list)
            for r in rows:
                o = obs.get(r.get("task"), {})
                if o.get("solved"):
                    append(TM / "profiles.jsonl", {"t": time.time(), "commit": self.commit, "bench": self.bench, "task": r["task"], "config": cfg, "secs": o.get("secs"),
                                                   "stages": profile_of(r.get("stages")), **({"cpu": r["placement"].get("cpu"), "timed": bool(r["placement"].get("exclusive"))} if r.get("placement") else {})})

    def finish_round(self, cfg: str, _=None):
        """After a round: its gains, the no-gain count (tried variants only), the next round (or done)."""
        st = self.state
        gained = [t for t, c in self.tm.cache.solved(self.commit, self.bench).items() if c == cfg]
        why = st["plan"][st["round"]][2] if st["round"] < len(st["plan"]) else ""
        st["gains"].append({"round": st["round"], "config": cfg, "gained": len(gained), "t": round(time.time())})
        if gained or variant_of(cfg) == "base":
            st["nogain"] = 0
        elif why != "untried" and not why.startswith("revisit"):
            st["nogain"] += 1
        st["round"] += 1
        self.save()
        log(f"{self.commit[:12]} {self.bench} {cfg}: {len(gained)} newly solved")
        return None

    def poll(self):
        if self.batch and self.batch.done:
            b, self.batch = self.batch, None
            if b.failed:  # (a batch boat couldn't run: the round again later)
                self.retry_at = time.time() + 600
                return
            st = self.state
            if st["round"] < len(st["plan"]):
                budget, variant, _ = st["plan"][st["round"]]
                self.finish_round(f"{budget}:{variant}")


# ------------------------------------------------------------------------------- the chains that follow main
class Follow:
    """A chain run once per commit: the commits the sweep asks for (want), else main's newest; never a commit whose
    inputs are those of a commit it ran (`skipped`, with the commit that had them); a commit main passed while it was
    busy isn't run. At most MAX_ACTIVE runs at once and PER_DAY a day. State: chains/<name>.json."""
    name, inputs = "", ""
    MAX_ACTIVE, PER_DAY = 2, 48

    def __init__(self, tm):
        self.tm = tm
        self.path = TM / "chains" / f"{self.name}.json"
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.st = json.loads(self.path.read_text()) if self.path.exists() else {"runs": {}, "wanted": []}
        self.active: dict = {}  # commit -> the run's live part (its batches, lists)
        self.lock = threading.Lock()
        for r in self.st["runs"].values():  # (a run the treadmill stopped in the middle: again, its finished parts kept)
            if r["status"] == "running":
                r["status"] = "pending"
                self.reset(r)

    def reset(self, r: dict):
        """A run's parts that were running when the treadmill stopped: to run again."""

    def save(self):
        with self.lock:
            self.path.write_text(json.dumps(self.st, indent=1))

    def status(self, commit: str) -> str | None:
        r = self.st["runs"].get(commit)
        return r and r["status"]

    def want(self, commit: str) -> str:
        """The sweep's commit: run (or skipped) before main's newest."""
        if commit not in self.st["runs"] and commit not in self.st["wanted"]:
            self.st["wanted"].append(commit)
            self.save()
        return self.status(commit) or "pending"

    def decide(self, commit: str) -> bool:
        """A commit's run made pending, or skipped (its inputs a run's): True if it is to run."""
        fp = fingerprint(commit, self.inputs)
        same = next((c for c, r in self.st["runs"].items() if c != commit and r.get("fp") == fp and r["status"] in ("done", "running", "pending")), None)
        if same:
            self.st["runs"][commit] = {"fp": fp, "status": "skipped", "same": same, "t0": round(time.time())}
            log(f"{self.name}: {commit[:12]} skipped (its inputs are {same[:12]}'s)")
        else:
            self.st["runs"][commit] = {"fp": fp, "status": "pending", "t0": round(time.time())}
        self.save()
        return not same

    def poll(self, head: str):
        for c in list(self.active):
            if self.active[c].get("done"):
                del self.active[c]
        for c in dict.fromkeys([*self.st["wanted"], head]):
            if c not in self.st["runs"]:
                self.decide(c)
        self.st["wanted"] = [c for c in self.st["wanted"] if self.status(c) not in ("done", "skipped")]

    def launch(self, free: int) -> int:
        """Batches of the pending runs (the sweep's first, then the newest), within `free` VMs."""
        pend = [c for c, r in self.st["runs"].items() if r["status"] in ("pending", "running")]
        # (main passed a pending commit nobody asked for: not run, the newest is)
        newest = max(pend, key=lambda c: self.st["runs"][c]["t0"], default=None)
        for c in pend:
            if c not in self.st["wanted"] and c != newest and self.st["runs"][c]["status"] == "pending" and c not in self.active:
                self.st["runs"][c]["status"] = "passed"
                self.save()
        started_today = sum(1 for r in self.st["runs"].values() if r.get("started_day") == today())
        order = sorted([c for c in pend if self.st["runs"][c]["status"] in ("pending", "running")], key=lambda c: (c not in self.st["wanted"], -self.st["runs"][c]["t0"]))
        for c in order:
            if free <= 0:
                break
            r = self.st["runs"][c]
            if c not in self.active:
                if len(self.active) >= self.MAX_ACTIVE or (started_today >= self.PER_DAY and c not in self.st["wanted"]) or time.time() < r.get("retry_at", 0):
                    continue
                r.setdefault("started_day", today())
                r["status"] = "running"
                self.save()
                self.active[c] = {"tree": self.tm.tree_of(c), "batches": {}, "done": False}
                started_today += 1
            free = self.advance(c, self.active[c], free)
        return free

    def finish(self, c: str, failed: bool = False):
        r = self.st["runs"][c]
        if failed:
            r["status"], r["retry_at"] = "pending", time.time() + 900
        else:
            r["status"], r["t1"] = "done", round(time.time())
        self.active[c]["done"] = True
        self.save()

    def advance(self, c: str, a: dict, free: int) -> int:
        raise NotImplementedError

    def prev_done(self, c: str) -> str | None:
        """The run before this one (by start), done."""
        t0 = self.st["runs"][c]["t0"]
        done = [(r["t0"], x) for x, r in self.st["runs"].items() if r["status"] == "done" and x != c and r["t0"] <= t0]
        return max(done)[1] if done else None


SPEED_BENCHES = ("chc", "its", "sv", "tip")


class Speed(Follow):
    """(b) each benchmark's solved set at 60 s, timing placement, against the previous run's times: the tasks solved
    by the previous run (or at the newest 60 s round in the cache), in shards of about ten minutes."""
    name, inputs = "speed", "chc"
    PER_DAY = knob("SPEED_PER_DAY", 12)
    SLOWER, FLOOR_S = knob("SLOWER", 1.5), knob("FLOOR_S", 1.0)

    def reset(self, r: dict):
        r["benches"] = {b: x for b, x in r.get("benches", {}).items() if x.get("status") == "done"}

    def fingerprint_all(self, c: str) -> str:
        return "".join(fingerprint(c, b) for b in SPEED_BENCHES)

    def decide(self, commit: str) -> bool:
        fp = hashlib.sha256(self.fingerprint_all(commit).encode()).hexdigest()[:16]
        same = next((c for c, r in self.st["runs"].items() if c != commit and r.get("fp") == fp and r["status"] in ("done", "running", "pending")), None)
        self.st["runs"][commit] = {"fp": fp, "status": "skipped" if same else "pending", "t0": round(time.time()), **({"same": same} if same else {})}
        if same:
            log(f"speed: {commit[:12]} skipped (its inputs are {same[:12]}'s)")
        self.save()
        return not same

    def claim(self, commit: str, bench: str) -> tuple[set, bool]:
        """The sweep's question at its 60 s round: the tasks this chain times at that commit (and whether to wait)."""
        s = self.want(commit)
        if s in ("skipped", "passed") or s is None:
            return set(), False
        b = self.st["runs"].get(commit, {}).get("benches", {}).get(bench)
        if not b:
            return set(), s in ("pending", "running")
        return set(b.get("claimed", [])), b.get("status") != "done"

    def solved_set(self, c: str, bench: str) -> list[str]:
        prev = self.prev_done(c)
        ts = set()
        if prev:
            ts |= {t for t, o in json.loads(self.obs_file(prev, bench).read_text()).items() if o.get("solved")} if self.obs_file(prev, bench).exists() else set()
        newest = max((r["t"], cc) for (cc, b, t, cfg), r in self.tm.cache.d.items() if b == bench and cfg == "60:base") if any(
            b == bench and cfg == "60:base" for (_, b, _, cfg) in self.tm.cache.d) else None
        if newest:
            ts |= {t for (cc, b, t, cfg), r in self.tm.cache.d.items() if cc == newest[1] and b == bench and cfg == "60:base" and r["solved"]}
        return sorted(ts)

    def obs_file(self, c: str, bench: str) -> pathlib.Path:
        return TM / "commits" / c[:12] / "speed" / bench / "obs.json"

    def advance(self, c: str, a: dict, free: int) -> int:
        r = self.st["runs"][c]
        r.setdefault("benches", {})
        for bench in SPEED_BENCHES:
            if bench not in self.tm.benches:
                continue
            b = r["benches"].get(bench)
            if b and b["status"] in ("done", "running"):
                continue
            got = self.tm.lists.get(c, a["tree"], bench)
            if got is None or free <= 0:
                continue
            ids = set(task_ids(got))
            tasks = [t for t in self.solved_set(c, bench) if t in ids]
            if self.tm.sample:
                tasks = tasks[:self.tm.sample]
            if not tasks:
                r["benches"][bench] = {"status": "done", "claimed": [], "note": "no solved set yet"}
                self.save()
                continue
            r["benches"][bench] = {"status": "running", "claimed": tasks}
            self.save()
            free -= self.batch(c, a, bench, got, tasks, free)
        if not all(r["benches"].get(b, {}).get("status") == "done" for b in SPEED_BENCHES if b in self.tm.benches) or any(not x.done for x in a["batches"].values()):
            return free
        # each task flagged (slower or lost) once more, timed, at both commits: the search's own spread on identical code
        # reaches 3x on a few tasks (two runs of 0010208 and 604b62d: 6.3 s and 2.0 s), so one run is no regression
        prev = self.prev_done(c)
        if "confirm" not in r:
            r["confirm"] = {b: {"tasks": ts, c: "pending", prev: "pending"} for b, ts in self.flagged(c, prev).items() if ts} if prev else {}
            self.save()
        for bench, cf in r["confirm"].items():
            for side in (c, prev):
                if cf[side] == "pending" and free > 0:
                    got = self.tm.lists.get(c, a["tree"], bench)
                    if got is None:
                        continue
                    cf[side] = "running"
                    self.save()
                    free -= self.batch(c, a, bench, got, cf["tasks"], free, side=side)
        if all(cf[x] == "done" for cf in r["confirm"].values() for x in (c, prev)) and not any(not x.done for x in a["batches"].values()):
            self.compare(c)
            self.finish(c)
        return free

    def flagged(self, c: str, prev: str) -> dict:
        """Per benchmark, the tasks one run says are slower (SLOWER and FLOOR_S) or lost against the previous run."""
        out = {}
        for bench in SPEED_BENCHES:
            if self.obs_file(c, bench).exists() and self.obs_file(prev, bench).exists():
                now, was = json.loads(self.obs_file(c, bench).read_text()), json.loads(self.obs_file(prev, bench).read_text())
                out[bench] = [t for t in now if was.get(t, {}).get("solved") and (not now[t].get("solved") or (now[t]["secs"] > self.SLOWER * was[t]["secs"] and now[t]["secs"] - was[t]["secs"] >= self.FLOOR_S))]
        return out

    def batch(self, c: str, a: dict, bench: str, got, tasks: list[str], free: int, side: str = "") -> int:
        """The timed shards of tasks at c (or, `side`, the confirming runs of c's flagged tasks at c or the commit before)."""
        tree = self.tm.tree_of(side) if side else a["tree"]
        by = task_specs(got)
        est = {t: max(1.0, float(r.get("secs") or 10)) for (cc, b, t, cfg), r in self.tm.cache.d.items() if b == bench and cfg in ("60:base", "60:timing") and r["solved"]}
        shards, cur, s = [], [], 0.0
        for t in sorted(tasks, key=lambda t: -est.get(t, 10)):
            if bench == "sv" or s + est.get(t, 10) > 600 or len(cur) >= 40:
                if cur:
                    shards.append((cur, s))
                cur, s = [], 0.0
            cur.append(t)
            s += est.get(t, 10)
        if cur:
            shards.append((cur, s))
        items = [shard_item(f"speed-{bench}-{k}", bench, [by[t] for t in ts], 60, {}, tree, timing=True, est=s) for k, (ts, s) in enumerate(shards)]
        rdir = TM / "commits" / c[:12] / "speed" / bench / (f"confirm-{side[:12]}" if side else "")
        rdir.mkdir(parents=True, exist_ok=True)
        (rdir / "results.jsonl").write_text("")
        rows, lock = [], threading.Lock()

        def on_row(it, row):
            with lock:
                res = row.get("result")
                res = [res] if isinstance(res, dict) else (res or [])
                pl = row.get("placement") or {}
                res = [{**x, "placement": {"exclusive": pl.get("exclusive"), "cpu": pl.get("cpu"), "co_tenants": pl.get("co_tenants")}} for x in res]
                rows.extend(res)
                append_many(rdir / "results.jsonl", res)

        def after(logs):
            (rdir / "tasks.json").write_text(json.dumps({"limit": 60, **got} if isinstance(got, dict) else got))
            obs = read_obs(rdir, bench, tree)
            cpu = {x.get("task"): x.get("placement", {}).get("cpu") for x in rows}
            obs = {t: {**o, "cpu": cpu.get(t)} for t, o in obs.items()}
            (rdir / "obs.json").write_text(json.dumps(obs))
            if side:
                self.st["runs"][c]["confirm"][bench][side] = "done"
                self.save()
                return
            seen = self.tm.cache.seen(c, bench, "60:base")
            for t, o in obs.items():
                put(self.tm, c, bench, t, "60:timing", o)
                if t not in seen:
                    put(self.tm, c, bench, t, "60:base", o, "speed")
            self.st["runs"][c]["benches"][bench]["status"] = "done"
            self.save()
        label = f"speed {c[:12]} {bench}" + (f" confirm at {side[:12]}" if side else "")
        vms = max(1, min(free, len(items), math.ceil(sum(i["est"] for i in items) / 1800)))
        log(f"{label}: {len(tasks)} {'flagged' if side else 'solved'} tasks in {len(items)} timed shards on {vms} VMs")
        b = Batch(self.tm, label, "a", items, vms, tracked(self.tm, "speed", label, on_row), root=tree, after=after)
        a["batches"][bench + (f"@{side[:12]}" if side else "")] = b
        self.tm.batches.append(b)
        return vms

    def poll(self, head: str):
        super().poll(head)
        for c, a in self.active.items():  # (a shard batch boat couldn't run: the benchmark again later)
            for key, b in list(a["batches"].items()):
                if b.done and b.failed:
                    del a["batches"][key]
                    bench, _, side = key.partition("@")
                    if side:
                        cf = self.st["runs"][c].get("confirm", {}).get(bench, {})
                        for x in cf:
                            if x.startswith(side) and cf[x] == "running":
                                cf[x] = "pending"
                    else:
                        self.st["runs"][c]["benches"].pop(bench, None)
                    self.save()

    def compare(self, c: str):
        """Against the previous run: slower (1.5x and 1 s more), lost, faster; one speed.jsonl row a benchmark. A task
        flagged by the first runs counts only if its confirming runs agree: slower when the faster of its two runs here
        is SLOWER times the slower of its two there (and FLOOR_S more), lost when neither run here solved it; the others
        are `noise`."""
        prev = self.prev_done(c)
        for bench in SPEED_BENCHES:
            f = self.obs_file(c, bench)
            if not f.exists():
                continue
            now = json.loads(f.read_text())
            row = {"t": time.time(), "commit": c, "bench": bench, "prev": prev, "tasks": len(now), "solved": sum(1 for o in now.values() if o.get("solved"))}
            if prev and self.obs_file(prev, bench).exists():
                was = json.loads(self.obs_file(prev, bench).read_text())
                both = [t for t in now if t in was and was[t].get("solved")]
                cdir = TM / "commits" / c[:12] / "speed" / bench
                cn = jl_one(cdir / f"confirm-{c[:12]}" / "obs.json")
                cp = jl_one(cdir / f"confirm-{prev[:12]}" / "obs.json")
                flagged = self.st["runs"].get(c, {}).get("confirm", {}).get(bench, {}).get("tasks", [])
                slower, lost, noise = [], [], []
                for t in flagged:
                    runs_now, runs_was = [now[t], cn.get(t, now[t])], [was[t], cp.get(t, was[t])]
                    if not any(o.get("solved") for o in runs_now):
                        lost.append((t, now[t].get("answer")))
                    elif all(o.get("solved") for o in runs_now) and min(o["secs"] for o in runs_now) > self.SLOWER * max(o["secs"] for o in runs_was) \
                            and min(o["secs"] for o in runs_now) - max(o["secs"] for o in runs_was) >= self.FLOOR_S:
                        slower.append((t, max(o["secs"] for o in runs_was), min(o["secs"] for o in runs_now), now[t].get("cpu") != was[t].get("cpu")))
                    else:
                        noise.append(t)
                faster = [t for t in both if now[t].get("solved") and was[t]["secs"] > self.SLOWER * now[t]["secs"] and was[t]["secs"] - now[t]["secs"] >= self.FLOOR_S]
                tot_now, tot_was = sum(now[t]["secs"] for t in both if now[t].get("solved")), sum(was[t]["secs"] for t in both if now[t].get("solved"))
                row.update(compared=len(both), slower=sorted(slower, key=lambda x: -x[2] / max(0.01, x[1])), faster=len(faster), lost=lost, noise=noise,
                           total_s=round(tot_now, 1), prev_total_s=round(tot_was, 1))
            append(TM / "speed.jsonl", row)
            log(f"speed {c[:12]} {bench}: " + (f"{len(row.get('slower', []))} slower, {len(row.get('lost', []))} lost (confirmed), {len(row.get('noise', []))} flags not confirmed, "
                                                 f"{row.get('faster', 0)} faster against {prev[:12]}" if prev else "the first run (its baseline)"))


class IC3(Follow):
    """(c) IC3Syn's 29 protocols with their broken variants (run.ts without --skip) at 60 s (timing placement: these
    are IC3Syn's speed run too) and 300 s. The searches' verdicts are the sweep's IC3Syn rounds at those budgets."""
    name, inputs = "ic3syn", "ic3syn"
    BUDGETS = (60, 300)

    def reset(self, r: dict):
        r["budgets"] = {b: x for b, x in r.get("budgets", {}).items() if x == "done"}

    def advance(self, c: str, a: dict, free: int) -> int:
        r = self.st["runs"][c]
        ids = self.tm.lists.get(c, a["tree"], "ic3syn")
        if ids is None:
            return free
        if self.tm.sample:
            ids = ids[:self.tm.sample]
        r.setdefault("budgets", {})
        for bud in self.BUDGETS:
            if r["budgets"].get(str(bud)) in ("done", "running") or free <= 0:
                continue
            r["budgets"][str(bud)] = "running"
            self.save()
            items = [sh_item(f"ic3full-{bud}-{k}", f"bun install --frozen-lockfile >/dev/null 2>&1; bun research/protocols/ic3syn/run.ts --ms {bud * 1000} --only '{p}' 2>/dev/null | tail -1",
                             ".", bud * 2 + 240, bud) for k, p in enumerate(ids)]
            if bud == 60:
                for it in items:
                    it["timing"] = True
            label = f"ic3syn {c[:12]} {bud}s"
            b = Batch(self.tm, label, "a", items, max(1, min(free, math.ceil(len(items) * bud / (SLOTS * 1800)) if bud > 60 else min(8, len(items)))),
                      tracked(self.tm, "ic3syn", label, lambda it, row: None), root=a["tree"], after=self.after_fn(c, bud, ids), oleans=True)
            a["batches"][bud] = b
            self.tm.batches.append(b)
            free -= b.vms
        for bud, b in list(a["batches"].items()):
            if b.done and b.failed:
                del a["batches"][bud]
                r["budgets"].pop(str(bud), None)
                self.save()
        if all(r["budgets"].get(str(b)) == "done" for b in self.BUDGETS):
            self.finish(c)
        return free

    def after_fn(self, c: str, bud: int, ids: list[str]):
        def after(logs):
            out = []
            for k, p in enumerate(ids):
                text = logs.get(f"ic3full-{bud}-{k}", {}).get("out", "").strip().splitlines()
                row = {"id": p}
                with contextlib.suppress(Exception):
                    row = json.loads(text[-1])
                out.append(row)
                s, b = row.get("search") or {}, row.get("broken") or {}
                seen = self.tm.cache.seen(c, "ic3syn", f"{bud}:base")
                o = {"answer": s.get("verdict", "error"), "solved": s.get("verdict") == "proven", "secs": (s.get("ms") or 0) / 1000}
                if p not in seen:
                    put(self.tm, c, "ic3syn", p, f"{bud}:base", o, "ic3syn chain")
                put(self.tm, c, "ic3syn", p, f"{bud}:timing" if bud == 60 else f"{bud}:full", o)
                bv = b.get("verdict", "error")
                put(self.tm, c, "ic3syn-broken", p, f"{bud}:base", {"answer": bv, "solved": bv == "refuted", "wrong": bv == "proven", "secs": (b.get("ms") or 0) / 1000})
                if bv == "proven":
                    log(f"SOUNDNESS ALERT: IC3Syn's broken variant of {p} proven at {bud} s ({c[:12]}): {b.get('bug')}")
            d = TM / "commits" / c[:12] / "ic3syn-full"
            d.mkdir(parents=True, exist_ok=True)
            (d / f"{bud}.json").write_text(json.dumps(out, indent=1))
            prev = self.prev_done(c)
            pf = TM / "commits" / (prev or "")[:12] / "ic3syn-full" / "60.json"
            if bud == 60 and prev and pf.exists():  # (the 60 s searches, each alone on its VM: IC3Syn's speed run)
                was = {x.get("id"): x.get("search") or {} for x in json.loads(pf.read_text())}
                now = {x.get("id"): x.get("search") or {} for x in out}
                both = [p for p in now if was.get(p, {}).get("verdict") == "proven"]
                secs = lambda s: (s.get("ms") or 0) / 1000  # noqa: E731
                slower = [(p, secs(was[p]), secs(now[p]), False) for p in both if now[p].get("verdict") == "proven" and secs(now[p]) > Speed.SLOWER * secs(was[p])
                          and secs(now[p]) - secs(was[p]) >= Speed.FLOOR_S]
                append(TM / "speed.jsonl", {"t": time.time(), "commit": c, "bench": "ic3syn", "prev": prev, "tasks": len(now), "solved": sum(1 for s in now.values() if s.get("verdict") == "proven"),
                                            "compared": len(both), "slower": slower, "lost": [(p, now[p].get("verdict")) for p in both if now[p].get("verdict") != "proven"],
                                            "faster": sum(1 for p in both if now[p].get("verdict") == "proven" and secs(was[p]) > Speed.SLOWER * secs(now[p]) and secs(was[p]) - secs(now[p]) >= Speed.FLOOR_S),
                                            "total_s": round(sum(secs(now[p]) for p in both if now[p].get("verdict") == "proven"), 1),
                                            "prev_total_s": round(sum(secs(was[p]) for p in both if now[p].get("verdict") == "proven"), 1)})
            self.st["runs"][c]["budgets"][str(bud)] = "done"
            self.save()
        return after


class RealWorld(Follow):
    """(d) the real-world corpus (the bar's rw group: research/realworld/jobs.ts's jobs, each law's search 60 s), each
    law's verdict against the previous run's."""
    name, inputs = "rw", "rw"

    def advance(self, c: str, a: dict, free: int) -> int:
        if a["batches"] or free <= 0:
            if a["batches"] and all(b.done for b in a["batches"].values()):
                if any(b.failed for b in a["batches"].values()):
                    a["batches"] = {}
                    self.finish(c, failed=True)
                elif self.st["runs"][c].get("rw") == "done":
                    self.finish(c)
            return free
        jobs = self.tm.lists.get(c, a["tree"], "rw")
        if jobs is None:
            return free
        if self.tm.sample:
            jobs = jobs[:self.tm.sample]
        items = [sh_item(j["name"], j["cmd"], j.get("cwd", "."), int(j.get("timeout", 300)), 40) for j in jobs]
        label = f"rw {c[:12]}"

        def after(logs):
            obs = {}
            for it in items:
                ls = logs.get(it["name"], {}).get("out", "").split("\n--- stderr ---")[0].strip().splitlines()
                if not ls:
                    continue
                key = ls[0]
                try:
                    r = json.loads(ls[-1])
                except Exception:
                    r = {"outcome": "timeout", "ms": 150_000}
                obs[key] = {"answer": r.get("outcome"), "solved": r.get("outcome") == "proven", "secs": (r.get("ms") or 0) / 1000}
            for k, o in obs.items():
                put(self.tm, c, "rw", k, "60:base", o)
            d = TM / "commits" / c[:12] / "rw"
            d.mkdir(parents=True, exist_ok=True)
            (d / "obs.json").write_text(json.dumps(obs))
            prev = self.prev_done(c)
            row = {"t": time.time(), "commit": c, "prev": prev, "laws": len(obs), "proven": sum(1 for o in obs.values() if o["solved"]),
                   "refuted": sum(1 for o in obs.values() if o["answer"] == "refuted")}
            pf = TM / "commits" / (prev or "")[:12] / "rw" / "obs.json"
            if prev and pf.exists():
                was = json.loads(pf.read_text())
                row["changes"] = [(k, was[k]["answer"], o["answer"]) for k, o in obs.items() if k in was and was[k]["answer"] != o["answer"]]
            append(TM / "rw.jsonl", row)
            self.st["runs"][c]["rw"] = "done"
            self.save()
        vms = max(1, min(free, math.ceil(len(items) * 40 / (SLOTS * 1800))))
        b = Batch(self.tm, label, "a", items, vms, tracked(self.tm, "rw", label, lambda it, row: None), root=a["tree"], after=after)
        a["batches"]["rw"] = b
        self.tm.batches.append(b)
        return free - vms


class Ten(Follow):
    """(f) the ten core protocols (research/protocols/models.ts) at 60 s, RUNS runs each, timing placement, at low
    priority: launched last (from the fill, with what the main chains left), at the sweep class all the same, as a
    timing item needs an empty VM and only a higher class empties a VM of the fuzz fill (a filler timing item waited
    behind it: 6 of 20 placed in 15 minutes in the pilot)."""
    name, inputs = "ten", "ten"
    RUNS = knob("TEN_RUNS", 20)

    def advance(self, c: str, a: dict, free: int) -> int:
        if a["batches"]:
            b = a["batches"]["ten"]
            if b.done:
                if b.failed:
                    a["batches"] = {}
                    self.finish(c, failed=True)
                else:
                    self.finish(c)
            return free
        if free <= 0:
            return free
        ids = self.tm.lists.get(c, a["tree"], "ten")
        if ids is None:
            return free
        runs = 2 if self.tm.sample else self.RUNS
        items = [sh_item(f"ten-{k}-{r}", f"bun install --frozen-lockfile >/dev/null 2>&1; timeout -s KILL 150 bun research/protocols/run.ts --ms 60000 --only {p} --skip given,broken 2>/dev/null | tail -1",
                         ".", 240, 30) | {"timing": True} for r in range(runs) for k, p in enumerate(ids)]
        label = f"ten {c[:12]}"
        place: dict = {}

        def on_row(it, row):
            place[it["name"]] = (row.get("placement") or {}).get("cpu")

        def after(logs):
            for it in items:
                k, r = map(int, it["name"].split("-")[1:])
                with contextlib.suppress(Exception):
                    v = json.loads(logs.get(it["name"], {}).get("out", "").strip().splitlines()[-1])
                    s = v.get("search") or {}
                    append(TM / "ten.jsonl", {"t": time.time(), "commit": c, "id": ids[k], "run": r, "verdict": s.get("verdict"), "ms": s.get("ms"), "cpu": place.get(it["name"])})
        b = Batch(self.tm, label, "a", items, max(1, min(free, 4)), tracked(self.tm, "ten", label, on_row), root=a["tree"], after=after, oleans=True)
        a["batches"]["ten"] = b
        self.tm.batches.append(b)
        return free - b.vms


# --------------------------------------------------------------------------------------- the soundness work
FUZZ = {"kernel": ("kernel", "FUZZ_SEED={s} bun test kernel.test.ts 2>&1"),
        "cdcl": ("kernel", "FUZZ_SEED={s} FUZZ_SCALE=4 GDP_CDCL_VERIFY=1 bun test cdcl.test.ts 2>&1"),
        "tamper": ("kernel", "FUZZ_SEED={s} bun test tamper.test.ts 2>&1")}
# The extractor correspondence fuzz: each reader's tests (core/extract-<lang>.test.ts: its own check harness, core/py,
# core/rb, core/jvm, core/swift, core/go, core/rs, core/c, core/sol on anvil, core/ex) with the check's requests drawn
# from a fresh seed: core/extract-check.ts's drive() (every reader's check but Solidity's) and core/extract-sol.ts's
# replays read XFUZZ_SEED (patched in the item's own copy of the tree; refused if the patch finds nothing to patch).
# A test that fails with "the rule and the code differ" is an extracted rule the code contradicts on a request the
# default seed never drew: an alert.
XPATCH = ("sed -i 's/seeded((opts.seed ?? 7) >>> 0 || 1)/seeded((Number(process.env.XFUZZ_SEED) || (opts.seed ?? 7)) >>> 0 || 1)/' core/extract-check.ts && "
          "sed -i 's/seeded((opts.check?.seed ?? 11) >>> 0 || 1)/seeded((Number(process.env.XFUZZ_SEED) || (opts.check?.seed ?? 11)) >>> 0 || 1)/' core/extract-sol.ts && "
          "grep -q XFUZZ_SEED core/extract-check.ts && grep -q XFUZZ_SEED core/extract-sol.ts || { echo 'xfuzz: the seed patch found nothing to patch'; exit 3; }; ")
XFUZZ = {  # lang: (setup, test file, weight, limit)
    "python": ("(python3 -m pip install -q fastapi >/dev/null 2>&1 || true)", "extract-py.test.ts", 1, 600),
    "ruby": (". research/langs/ruby/ruby-setup.sh >/dev/null 2>&1", "extract-rb.test.ts", 1, 900),
    "jvm": (". research/langs/jvm/jvm-setup.sh >/dev/null 2>&1", "extract-jvm.test.ts", 1, 900),
    "swift": (". research/langs/swift/swift-setup.sh >/dev/null 2>&1", "--timeout 900000 extract-swift.test.ts", 2, 1800),
    "go": (". research/extract/go-setup.sh >/dev/null 2>&1", "extract-go.test.ts", 1, 1200),
    "rust": (". research/langs/rust/rust-setup.sh >/dev/null 2>&1", "--timeout 600000 extract-rs.test.ts", 1, 1500),
    "c": (". research/langs/c/clang-setup.sh >/dev/null 2>&1", "extract-c.test.ts", 1, 900),
    "solidity": (". research/sol/sol-setup.sh >/dev/null 2>&1", "--timeout 600000 extract-sol.test.ts", 1, 1200),
    "elixir": (". research/langs/elixir/elixir-setup.sh >/dev/null 2>&1", "extract-ex.test.ts", 1, 900),
    "typescript": ("true", "extract.test.ts", 1, 900),
}
XFUZZ_EVERY = knob("XFUZZ_EVERY", 6)  # one correspondence item for every 6 fuzz items
DIFFER = re.compile(r"the rule and the code differ: (?!the code doesn't load|the check's harness)(.{0,300})")


def xfuzz_cmd(lang: str, seed: int) -> str:
    setup, test, _, _ = XFUZZ[lang]
    return (f"bun install --frozen-lockfile >/dev/null 2>&1; {XPATCH}{setup}; cd core && XFUZZ_SEED={seed} bun test {test} 2>&1 | "
            f"grep -v '^(pass)' | tail -c 6000; s=${{PIPESTATUS[0]}}; echo xfuzz-exit $s; exit $s")


def mutant_sig(commit: str, where: str, change: str, _cache: dict = {}) -> str:  # noqa: B006  (the files by commit, kept)
    """A mutant by its file, its line's text and its change: the same mutant at another commit, whose lines moved."""
    f, _, line = where.rpartition(":")
    k = (commit, f)
    if k not in _cache:
        with contextlib.suppress(Exception):
            _cache[k] = git("show", f"{commit}:{f}").split("\n")
    lines = _cache.get(k) or []
    text = lines[int(line) - 1].strip() if line.isdigit() and 0 < int(line) <= len(lines) else line
    return f"{f}|{text}|{change}"


class Soundness:
    """Fresh fuzz seeds (kernel, CDCL, tamper), the extractor correspondence fuzz and, at a commit whose trusted base
    changed, its mutants."""

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
        while self.mutants and "mutants" in self.tm.chains and len(items) < vms * SLOTS:
            m = self.mutants.pop(0)
            items.append(sh_item(f"mutant-{m}", f"bun mutants.ts ids {m} 2>&1 | tail -1", "kernel", 3600, 600))
            kinds.append(("mutant", m))
        while len(items) < n:
            s = st["seed"] = st.get("seed", 1000) + 1
            if "xfuzz" in self.tm.chains and s % XFUZZ_EVERY == 0:
                langs = [l for l, x in XFUZZ.items() for _ in range(x[2])]
                lang = langs[(s // XFUZZ_EVERY) % len(langs)]
                items.append(sh_item(f"xfuzz-{lang}-{s}", xfuzz_cmd(lang, s), ".", XFUZZ[lang][3], XFUZZ[lang][3] / 3, weight=2 if lang == "swift" else 1))
                kinds.append(("x:" + lang, s))
                continue
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
                        where, change = f"{r.get('file')}:{r.get('line')}", f"{r.get('from')} -> {r.get('to')}"
                        append(TM / "mutants.jsonl", {"t": time.time(), "commit": self.commit, "hash": self.hash, "id": s, "killedBy": r.get("killedBy"), "where": where,
                                                      "change": change, "sig": mutant_sig(self.commit, where, change), **({"equivalent": r["equivalent"]} if r.get("equivalent") else {})})
                    continue
                code = codes.get(it["name"], -1)
                if k.startswith("x:"):
                    m = DIFFER.search(out)
                    # (the tests' own counts, kept every time: a seed whose tests all skipped, a toolchain missing, ran nothing)
                    counts = {w: int(x.group(1)) for w in ("pass", "skip", "fail") for x in [re.search(rf"^\s*(\d+) {w}$", out, re.M)] if x}
                    append(TM / "xfuzz.jsonl", {"t": time.time(), "commit": self.commit, "lang": k[2:], "seed": s, "code": code, **counts,
                                                **({"differ": m.group(1)} if m else {}), **({"tail": out[-1500:]} if code != 0 else {})})
                    if m:
                        log(f"XFUZZ: {k[2:]} seed {s} at {self.commit[:12]}: the rule and the code differ: {m.group(1)[:200]}")
                    continue
                append(TM / "fuzz.jsonl", {"t": time.time(), "commit": self.commit, "kind": k, "seed": s, "code": code, **({"tail": out[-1500:]} if code != 0 else {})})
                if code != 0:
                    log(f"FUZZ FAILED: {k} seed {s} at {self.commit[:12]} (exit {code})")
        label = f"sound {self.commit[:12]}"
        return Batch(self.tm, label, "b", items, vms, tracked(self.tm, "sound", label, on_row), root=self.tree, after=after)


# ------------------------------------------------------------------------------------------------- the ideas
IDEA_CMD = "echo 'an idea (supercomputer/treadmill.py idea): this treadmill predates ideas, so it ran nothing'; exit 3"


class Idea:
    """A submission that is an idea (`idea`): knobs on a task set at a budget, against the base at that budget. At main
    (the sweep's commit) the base comes from the cache where it ran; from a lane's tree (its tarball, keyed by its
    hash) the base runs too. Its table: subs/<name>/out/table.log and summary.tsv (`idea-results`)."""

    def __init__(self, tm, d: pathlib.Path):
        self.tm, self.d = tm, d
        self.meta = json.loads((d / "meta.json").read_text())
        self.spec = json.loads((d / "jobs.json").read_text())[0]["idea"]
        self.batch: Batch | None = None
        self.done = self.meta["status"] in ("done", "failed")

    def save(self):
        (self.d / "meta.json").write_text(json.dumps(self.meta, indent=1))

    def fail(self, why: str):
        self.meta.update(status="failed", why=why)
        self.save()
        (self.d / "out").mkdir(exist_ok=True)
        (self.d / "out" / "table.log").write_text(f"idea {self.meta['name']}: failed: {why}\n")
        self.done = True

    def step(self, free: int) -> int:
        if self.done or free <= 0:
            return free
        if self.batch:
            if self.batch.done:
                if self.batch.failed:
                    self.batch = None  # (again later)
                else:
                    self.done = True
            return free
        sp = self.spec
        bench, budget, env = sp["bench"], int(sp["budget"]), sp.get("env", {})
        if bench not in BENCHES:
            self.fail(f"no benchmark {bench}")
            return free
        if env and not BENCHES[bench]["env"] and bench != "tip":
            self.fail(f"{bench}'s shard takes no environment")
            return free
        at_main = not sp.get("tree")
        commit = self.tm.commit if at_main else f"tree:{self.meta['tree_key']}"
        tree = self.tm.tree if at_main else None
        got = self.tm.lists.get(self.tm.commit, self.tm.tree, bench)
        if got is None:
            return free
        ids = task_ids(got)
        tasks = [t for t in ids if t in set(sp.get("tasks") or [])] or [t for t in ids if sp.get("glob") and fnmatch.fnmatch(t, sp["glob"])]
        if not tasks:
            self.fail("no task matches")
            return free
        cfg_base, cfg = f"{budget}:base", f"{budget}:{label_of(env)}"
        self.meta.update(status="running", commit=commit, config=cfg, tasks=len(tasks))
        self.save()
        by = task_specs(got)
        todo = [(t, cfg_base, {}) for t in tasks if (commit, bench, t, cfg_base) not in self.tm.cache.d] + \
               [(t, cfg, env) for t in tasks if (commit, bench, t, cfg) not in self.tm.cache.d]
        if not todo:
            self.table(commit, bench, tasks, cfg_base, cfg)
            self.done = True
            return free
        items = [shard_item(f"idea-{k}", bench, [t if BENCHES[bench].get("sh") else by[t]], budget, e, tree or self.tm.tree) for k, (t, _, e) in enumerate(todo)]
        rows: dict = {}
        lock = threading.Lock()

        def on_row(it, row):
            with lock:
                rows[it["name"]] = row

        def after(logs):
            for c_ in (cfg_base, cfg):
                ks = [k for k, (_, cc, _) in enumerate(todo) if cc == c_]
                if not ks:
                    continue
                rdir = self.d / "rounds" / c_.replace(":", "-")
                rdir.mkdir(parents=True, exist_ok=True)
                if BENCHES[bench].get("sh"):
                    for k in ks:
                        with contextlib.suppress(Exception):
                            v = json.loads(logs.get(f"idea-{k}", {}).get("out", "").strip().splitlines()[-1])["search"]
                            put(self.tm, commit, bench, todo[k][0], c_, {"answer": v["verdict"], "solved": v["verdict"] == "proven", "secs": v.get("ms", 0) / 1000}, f"idea {self.meta['name']}")
                    continue
                res = []
                for k in ks:
                    r = rows.get(f"idea-{k}", {}).get("result")
                    res += [r] if isinstance(r, dict) else (r or [{"tool": "gdp", "task": todo[k][0], "answer": "error", "seconds": -1}])
                (rdir / "results.jsonl").write_text("".join(json.dumps(r) + "\n" for r in res))
                (rdir / "tasks.json").write_text(json.dumps({"limit": budget, **got} if isinstance(got, dict) else got))
                for t, o in read_obs(rdir, bench, self.tm.tree).items():
                    put(self.tm, commit, bench, t, c_, o, f"idea {self.meta['name']}")
            self.table(commit, bench, tasks, cfg_base, cfg)
        label = f"idea {self.meta['name']}"
        vms = max(1, min(free, 8, math.ceil(len(items) * budget / (SLOTS * 1800))))
        log(f"idea {self.meta['name']}: {bench} {cfg} on {len(tasks)} tasks ({len(todo)} runs, the rest cached) on {vms} VMs")
        self.batch = Batch(self.tm, label, "c", items, vms, tracked(self.tm, "ideas", label, on_row), root=tree, tar=None if at_main else (self.d / "tree.tar.gz").read_bytes(),
                           after=after, oleans=bench == "ic3syn")
        self.tm.batches.append(self.batch)
        return free - vms

    def table(self, commit: str, bench: str, tasks: list[str], cfg_base: str, cfg: str):
        d = self.tm.cache.d
        rows, gained, lost = [], 0, 0
        for t in tasks:
            b, i = d.get((commit, bench, t, cfg_base), {}), d.get((commit, bench, t, cfg), {})
            delta = "gained" if i.get("solved") and not b.get("solved") else "lost" if b.get("solved") and not i.get("solved") else "same"
            gained, lost = gained + (delta == "gained"), lost + (delta == "lost")
            rows.append((t, b.get("answer"), b.get("secs"), i.get("answer"), i.get("secs"), delta))
        out = self.d / "out"
        out.mkdir(exist_ok=True)
        head = f"idea {self.meta['name']}: {bench}, {cfg} against {cfg_base} at {commit[:17]}: {gained} gained, {lost} lost, {len(tasks) - gained - lost} the same"
        (out / "table.log").write_text(head + "\n\n| task | base | s | idea | s | |\n| --- | --- | --- | --- | --- | --- |\n"
                                       + "".join(f"| {t} | {a} | {s} | {a2} | {s2} | {x} |\n" for t, a, s, a2, s2, x in sorted(rows, key=lambda r: (r[5] == "same", r[0]))))
        (out / "summary.tsv").write_text("".join(f"{t}\t{0 if x != 'lost' else 1}\t{s2}\t{x}: {a} -> {a2}\n" for t, a, s, a2, s2, x in rows))
        self.meta.update(status="done", gained=gained, lost=lost, wall_s=time.time() - self.meta["t"], t_done=time.time())
        self.save()
        log(head)


def idea_submit(a):
    """`idea`: the spec as a one-job submission (its job only says what it is to a treadmill before ideas), to the
    controller's queue (or this machine's treadmill directory with --local)."""
    env = dict(kv.split("=", 1) for kv in a.env)
    spec = {"bench": a.bench, "budget": a.budget, "env": env, "by": os.environ.get("USER", "?")}
    if os.path.isfile(a.tasks):
        spec["tasks"] = [l.strip() for l in pathlib.Path(a.tasks).read_text().splitlines() if l.strip() and not l.startswith("#")]
    else:
        spec["glob"] = a.tasks
    spec["tree"] = bool(a.tree)
    name = a.name or f"idea-{a.bench}-{label_of(env)}-{time.strftime('%m%d-%H%M%S')}".replace(":", "-").replace(",", "-").replace("=", "")
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        tmp = pathlib.Path(td) / f"{name}.json"
        tmp.write_text(json.dumps([{"name": "idea", "cmd": IDEA_CMD, "idea": spec}]))
        tree = a.tree or str(MAIN)
        if a.local:
            T.submit(str(tmp), tree, name)
        else:
            subprocess.run(["supercomputer", "queue", "add", str(tmp), "--tree", tree, "--name", name], check=True)
    print(f"idea {name}: {a.bench} at {a.budget} s, {label_of(env)}, tasks {spec.get('glob') or str(len(spec['tasks'])) + ' listed'}; "
          f"its table: python3 supercomputer/treadmill.py idea-results {name}{' --local' if a.local else ''}")


def idea_results(name: str, local: bool):
    if local:
        f = TM / "subs" / name / "out" / "table.log"
        m = json.loads((TM / "subs" / name / "meta.json").read_text())
        print(f.read_text() if f.exists() else f"{name}: {m['status']}")
        return
    from supercomputer import scheduler
    r = scheduler.connect().req("/queue/results", {"name": name}, timeout=120)
    print(r.get("logs", {}).get("table") or f"{name}: {r['meta']['status']}" + (f" ({r['meta'].get('why')})" if r["meta"].get("why") else ""))


# ---------------------------------------------------------------------------------------------- the controller
ALL_CHAINS = ("speed", "ic3syn", "rw", "sweep", "ten", "sound", "xfuzz", "mutants", "ideas")


class Treadmill(T.Treadmill):
    """The generic loop (T.Treadmill.step: the floor, the queue, the main chains, the queue again, backlogs, the
    fill) with this repo's chains: soundness as the floor and the fill, the per-commit chains and the sweeps as the
    main chains (in that order), the ten and the rest of the soundness work in what's left."""

    CLIENT = CLIENT

    def __init__(self, vms: int, budget_vmh, quiet: int, nogain: int, benches: str = "", sample: int = 0, sound: bool = True, modal: bool = True, max_wait: int = 900,
                 max_vms: int = 0, step_vms: int = 4, backlog_hours: float = 2.0, chains: str = ""):
        super().__init__(vms, budget_vmh, quiet, modal, max_wait, max_vms, step_vms, backlog_hours)
        self.nogain = nogain
        self.benches = [b for b in benches.split(",") if b] or list(BENCHES)
        self.chains = set([c for c in chains.split(",") if c] or ALL_CHAINS) - (set() if sound else {"sound", "xfuzz", "mutants"})
        self.sample, self.sound_on = sample, "sound" in self.chains
        self.commit, self.tree, self.sweeps, self.sound, self.head = None, None, {}, None, None
        self.lists = Lists(self)
        self.speed, self.ic3, self.rw, self.ten = Speed(self), IC3(self), RealWorld(self), Ten(self)
        self.follow = [f for f in (self.speed, self.ic3, self.rw) if f.name in self.chains]
        self.ideas: dict[str, Idea] = {}
        self.targets: dict = {}
        self.t_targets = 0.0

    def tree_of(self, sha: str) -> pathlib.Path:
        """A worktree of main's commit (with its submodules); of the others, those in use (the sweeps', the per-commit
        runs') and the two newest are kept."""
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
        keep = {sha[:12], (self.state.get("sweep") or "")[:12], *(c[:12] for f in (self.speed, self.ic3, self.rw, self.ten) for c in f.active),
                *((self.speed.prev_done(c) or "")[:12] for c in self.speed.active)}
        for old in [p for p in sorted((TM / "trees").iterdir(), key=lambda p: p.stat().st_mtime)[:-2] if p.name not in keep]:
            with contextlib.suppress(Exception):
                git("worktree", "remove", "--force", str(old))
        return path

    def poll(self):
        head = git("rev-parse", "main")
        if head != self.head and self.sound_on:  # soundness work follows main at once
            log(f"main is {head[:12]}: soundness work at it")
            self.sound = Soundness(self, head, self.tree_of(head))
        self.head = head
        if time.time() - self.t_targets > 600:
            self.targets, self.t_targets = targets_of(self.cache), time.time()
        if "sweep" in self.chains:
            self.poll_sweeps(head)
        elif not self.commit:
            self.commit, self.tree = head, self.tree_of(head)
        for f in self.follow + ([self.ten] if "ten" in self.chains else []):
            f.poll(head)
        if "ideas" in self.chains:
            self.poll_ideas()

    def poll_sweeps(self, head: str):
        # the sweeps keep their commit until every benchmark's chain is done (or SWEEP_HOURS pass), then take main's:
        # main moves several times an hour, and a chain restarted at each commit would never get past its first round
        sw = self.state.get("sweep")
        stale = not sw or (all(s.state["done"] for s in self.sweeps.values()) and self.sweeps) or time.time() - self.state.get("sweep_t", 0) > SWEEP_HOURS * 3600
        if stale and sw != head and not any(b.chain == "a" and b.label.startswith("sweep") and not b.done for b in self.batches):
            if sw and all(fingerprint(head, b) == fingerprint(sw, b) for b in self.benches) and all(s.state["done"] for s in self.sweeps.values()):
                pass  # (main moved, but nothing the sweeps read: they stay done at their commit)
            else:
                sw = None
        if not sw or not self.sweeps:
            if not sw:
                self.state.update(sweep=head, sweep_t=time.time())
                self.save_state()
                sw = head
                log(f"sweeps at {head[:12]}")
            self.commit, self.tree = sw, self.tree_of(sw)
            prev = self.state.get("sweep_prev")
            self.sweeps = {b: Sweep(self, sw, self.tree, b) for b in self.benches}
            for b, s in self.sweeps.items():  # (a benchmark whose inputs are the previous sweep's: nothing to sweep again)
                if prev and prev != sw and not s.state["done"] and s.state["round"] == 0 and fingerprint(sw, b) == fingerprint(prev, b):
                    s.state.update(done=True, same=prev)
                    s.save()
                    log(f"sweep {sw[:12]} {b}: skipped (its inputs are {prev[:12]}'s)")
            for f in self.follow:
                f.want(sw)
        for s in self.sweeps.values():
            s.poll()
        if self.sweeps and all(s.state["done"] for s in self.sweeps.values()) and self.state.get("sweep_prev") != sw:
            self.state["sweep_prev"] = sw
            self.save_state()

    def poll_ideas(self):
        for d in sorted((TM / "subs").glob("*/meta.json")) if (TM / "subs").exists() else []:
            name = d.parent.name
            if name in self.ideas:
                continue
            m = json.loads(d.read_text())
            if m.get("status") == "queued":
                with contextlib.suppress(Exception):
                    j = json.loads((d.parent / "jobs.json").read_text())
                    if isinstance(j, list) and j and isinstance(j[0], dict) and "idea" in j[0]:
                        m["status"] = "idea"  # (not the generic queue's: this chain's)
                        d.write_text(json.dumps(m, indent=1))
                        self.ideas[name] = Idea(self, d.parent)
            elif m.get("status") in ("idea", "running") and (d.parent / "jobs.json").exists() and '"idea"' in (d.parent / "jobs.json").read_text()[:4000]:
                self.ideas[name] = Idea(self, d.parent)

    def floor(self, free: int) -> int:
        if free > 0 and not self.want("b") and self.sound_on and self.sound:  # (soundness's floor: one VM)
            self.batches.append(self.sound.batch(1))
            free -= 1
        return free

    def main_chains(self, free: int) -> int:
        if "ideas" in self.chains and self.tree:  # (ideas first among the main chains: a lane is waiting on each)
            for i in list(self.ideas.values()):
                free = i.step(free)
        for f in self.follow:  # the per-commit chains: bounded, and the regressions' first word
            if free <= 0:
                break
            free = f.launch(free)
        if "sweep" in self.chains:
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
        if free > 0 and "ten" in self.chains:  # (f) at the filler class, before the fuzz
            free = self.ten.launch(free)
        while free > 0 and self.sound_on and self.sound:  # the fuzz fills the rest of the pool (filler: preempted at once)
            b = self.sound.batch(min(free, 4))
            self.batches.append(b)
            free -= b.vms
        return free

    def status_extra(self) -> dict:
        return {"commit": self.commit, "chains": sorted(self.chains), "sweeps": {k: {x: s.state[x] for x in ("round", "nogain", "done")} for k, s in self.sweeps.items()},
                "follow": {f.name: {c[:12]: r["status"] for c, r in list(f.st["runs"].items())[-4:]} for f in (self.speed, self.ic3, self.rw, self.ten)},
                "ideas": {n: i.meta["status"] for n, i in self.ideas.items() if not i.done}}


# ------------------------------------------------------------------------------------------------- the digest
LIMIT = 150  # the digest's lines, about (each list cut short past its share; digest.json has all)


def on(day: str, t: float) -> bool:
    return time.strftime("%Y-%m-%d", time.gmtime(t)) == day


def report(day: str) -> dict:
    """The day's findings as data (digest.json): alerts, new solves, targets, speed, the corpora, soundness, ideas,
    spend and the pool."""
    allrows = jl(TM / "cache.jsonl")
    rows = [r for r in allrows if on(day, r["t"])]
    alerts: list = []
    # soundness: wrong answers, IC3Syn's broken variants proven, fuzz UNSOUND, correspondence differences, new survivors
    for r in rows:
        if r.get("wrong"):
            alerts.append({"kind": "soundness", "what": f"{'IC3Syn broken variant PROVEN' if r['bench'] == 'ic3syn-broken' else 'WRONG answer'}: {r['bench']} {r['task']} at {r['config']} ({r['commit'][:12]}): {r['answer']}"})
    fz = [r for r in jl(TM / "fuzz.jsonl") if on(day, r["t"])]
    bad = [r for r in fz if r["code"] != 0]
    unsound = [r for r in bad if re.search(r"^\s*(error: )?(Error: )?UNSOUND", r.get("tail", ""), re.M)]  # (thrown, not quoted from the source)
    for r in unsound:
        alerts.append({"kind": "soundness", "what": f"UNSOUND: {r['kind']} fuzz seed {r['seed']} at {r['commit'][:12]}"})
    xz = [r for r in jl(TM / "xfuzz.jsonl") if on(day, r["t"])]
    for r in [r for r in xz if r.get("differ")]:
        alerts.append({"kind": "soundness", "what": f"extractor correspondence: {r['lang']} seed {r['seed']} at {r['commit'][:12]}: the rule and the code differ: {r['differ'][:160]}"})
    mall = jl(TM / "mutants.jsonl")
    for r in mall:
        r.setdefault("sig", mutant_sig(r["commit"], r["where"], r["change"]))
    mt = list({(r["hash"], r["id"]): r for r in mall if on(day, r["t"])}.values())
    surv = [r for r in mt if not r.get("killedBy")]
    # (a survivor is new when no survivor before today had its signature: its file, its line's text and its change)
    t_day = calendar.timegm(time.strptime(day, "%Y-%m-%d"))
    before = {r["sig"] for r in mall if not r.get("killedBy") and r["t"] < t_day}
    new_surv = list({r["sig"]: r for r in surv if not r.get("equivalent") and r["sig"] not in before}.values())
    for r in new_surv:
        alerts.append({"kind": "soundness", "what": f"NEW mutant survivor: {r['where']} {r['change'].strip()} (id {r['id']}, {r['commit'][:12]})"})
    # regressions: the speed chain, 60 s losses, the corpus, the ten, IC3Syn
    speed = [r for r in jl(TM / "speed.jsonl") if on(day, r["t"])]
    for r in speed:
        for t, was, now, cpu in r.get("slower", [])[:5]:
            alerts.append({"kind": "regression", "what": f"slower: {r['bench']} {t} {was:.1f} s -> {now:.1f} s ({now / max(0.01, was):.1f}x) at {r['commit'][:12]}{' (another CPU model)' if cpu else ''}"})
        if len(r.get("slower", [])) > 5:
            alerts.append({"kind": "regression", "what": f"slower: {r['bench']}: {len(r['slower']) - 5} more at {r['commit'][:12]} (digest.json)"})
        for t, ans in r.get("lost", []):
            alerts.append({"kind": "regression", "what": f"lost at 60 s: {r['bench']} {t} ({ans}) at {r['commit'][:12]}"})
    rw = [r for r in jl(TM / "rw.jsonl") if on(day, r["t"])]
    for r in rw:
        for k, was, now in r.get("changes", []):
            flip = {was, now} == {"proven", "refuted"}
            if flip or was == "proven":
                alerts.append({"kind": "soundness" if flip else "regression", "what": f"real-world: {k}: {was} -> {now} at {r['commit'][:12]}"})
    ten = ten_summary(day)
    for c, ps in ten.items():
        for p, s in ps.items():
            if s.get("slower") or s.get("fewer"):
                alerts.append({"kind": "regression", "what": f"ten: {p}: median {s['median_s']} s against {s.get('prev_median_s')} s, {s['proven']}/{s['runs']} proven against {s.get('prev_proven')} at {c[:12]}"})
    ic3 = {}
    for r in rows:
        if r["bench"] == "ic3syn" and r["config"] in ("60:base", "300:base"):
            ic3.setdefault(r["commit"], {}).setdefault(r["config"], {})[r["task"]] = r["solved"]
    commits = sorted({r["commit"] for r in rows if not r["commit"].startswith("tree:")}, key=lambda c: min(r["t"] for r in rows if r["commit"] == c))
    # new solves: per commit, each task solved past the 60 s base, by the config that solved it first, by family
    solves, sweeps = [], []
    for c in commits:
        for b in BENCHES:
            mine = [r for r in allrows if r["commit"] == c and r["bench"] == b]
            if not mine:
                continue
            first = {}  # (each task's solving config with the least budget, the base first: chains land in any order)
            for r in sorted(mine, key=lambda r: (budget_of(r["config"]) if r["config"][:1].isdigit() else 10**6, variant_of(r["config"]) not in ("base", "timing", "full"), r["t"])):
                if r["solved"] and r["task"] not in first:
                    first[r["task"]] = r["config"]
            at60 = {t for t, cfg in first.items() if budget_of(cfg) == 60}
            new = {t: cfg for t, cfg in first.items() if budget_of(cfg) > 60}
            st = jl_one(TM / "commits" / c[:12] / b / "state.json")
            sweeps.append({"commit": c, "bench": b, "tasks": len({r["task"] for r in mine}), "solved60": len(at60), "past60": len(new), "round": st.get("round"),
                           "of": len(st.get("plan", [])) or "?", "done": st.get("done"), "same": st.get("same"), "swept": bool(st)})
            fams: dict = {}
            for t, cfg in new.items():
                fams.setdefault(family(t), {}).setdefault(cfg, []).append(t)
            for f, by in fams.items():
                n = sum(len(v) for v in by.values())
                best = max(by.items(), key=lambda kv: len(kv[1]))
                note = (f"candidate for a general change: {best[0]} wins {len(best[1])} of {n}" if variant_of(best[0]) != "base" and len(best[1]) >= 3 and len(best[1]) >= 0.6 * n else "")
                solves.append({"commit": c, "bench": b, "family": f, "by": {k: v for k, v in by.items()}, "n": n, "note": note})
            # (the commit before: the newest whose first 60 s row came before this one's)
            t60 = {}
            for r in allrows:
                if r["bench"] == b and r["config"] == "60:base" and not r["commit"].startswith("tree:"):
                    t60[r["commit"]] = min(t60.get(r["commit"], r["t"]), r["t"])
            prev = [x for x in t60 if x != c and c in t60 and t60[x] < t60[c]]
            if prev:
                p = max(prev, key=lambda x: t60[x])
                was = {r["task"] for r in allrows if r["commit"] == p and r["bench"] == b and r["config"] == "60:base" and r["solved"]}
                now_ = {r["task"] for r in mine if r["config"] == "60:base" and r["solved"]}
                seen = {r["task"] for r in mine if r["config"] == "60:base"}
                lost = sorted((was - now_) & seen)
                sweeps[-1].update(gained60=len(now_ - was), lost60=len(lost), against=p)
                if lost and b not in SPEED_BENCHES:  # (the speed chain's own losses are listed already)
                    for t in lost[:5]:
                        alerts.append({"kind": "regression", "what": f"lost at 60 s: {b} {t} against {p[:12]} at {c[:12]}"})
    # targets: the latest profile of each target against the one before
    targets = []
    tg = targets_of(T.Cache())
    prof = jl(TM / "profiles.jsonl")
    for b, ts in tg.items():
        for t, p in ts.items():
            ps = sorted([x for x in prof if x["bench"] == b and x["task"] == t], key=lambda x: x["t"])
            last = ps[-1] if ps else None
            before = next((x for x in reversed(ps[:-1]) if x["commit"] != (last or {}).get("commit") and x["config"] == (last or {}).get("config")), None)
            targets.append({"bench": b, "task": t, "config": p["config"], "commit": p["commit"], "secs": p.get("secs"), "stages": (last or {}).get("stages", {}),
                            "timed": (last or {}).get("timed", False), **({"prev_secs": before.get("secs"), "prev_stages": before.get("stages"), "prev_commit": before["commit"]} if before else {})})
    # spend by chain (spend.jsonl), the pool (vms.jsonl), extra starts
    sp: dict = {}
    for r in jl(TM / "spend.jsonl"):
        if r.get("day") == day:
            sp[r["chain"]] = sp.get(r["chain"], 0.0) + r["vmh"]
    samples = [r for r in jl(TM / "vms.jsonl") if r.get("day") == day]
    pool = {"peak_vms": max([r["vms"] for r in samples] or [0]), "target_peak": max([r["target"] for r in samples] or [0]), "held_vmh": round(sum(r.get("vmh", 0) for r in samples), 1)}
    pool["busy_pct"] = round(100 * sum(sp.values()) / pool["held_vmh"]) if pool["held_vmh"] else None
    with contextlib.suppress(Exception):
        pool["extra_starts"] = boat.extra_starts()
    ideas = [json.loads(p.read_text()) for p in (TM / "subs").glob("*/meta.json")] if (TM / "subs").exists() else []
    ideas = [m for m in ideas if m.get("config") and on(day, m.get("t_done", m["t"]))]
    sound = {"fuzz": {k: sum(1 for r in fz if r["kind"] == k) for k in FUZZ}, "fuzz_failed": [(r["kind"], r["seed"], r["code"], first_error(r)) for r in bad],
             "unsound": len(unsound), "xfuzz": {l: sum(1 for r in xz if r["lang"] == l) for l in XFUZZ}, "xfuzz_tests": sum(r.get("pass", 0) for r in xz),
             "xfuzz_idle": sorted({r["lang"] for r in xz if r["code"] == 0 and "pass" in r and not r["pass"]}), "xfuzz_failed": [(r["lang"], r["seed"], r["code"], first_error(r)) for r in xz if r["code"] != 0],
             "mutants": len(mt), "survived": len(surv), "equivalent": sum(1 for r in surv if r.get("equivalent")), "new_survivors": len(new_surv),
             "known_survivors": sorted({f"{r['where']} {r['change'].strip()}" for r in surv if not r.get("equivalent")} - {f"{r['where']} {r['change'].strip()}" for r in new_surv})}
    chains = {f: jl_one(TM / "chains" / f"{f}.json").get("runs", {}) for f in ("speed", "ic3syn", "rw", "ten")}
    return {"day": day, "alerts": alerts, "solves": solves, "sweeps": sweeps, "targets": targets, "speed": speed, "rw": rw, "ten": ten, "ic3syn": ic3,
            "soundness": sound, "ideas": ideas, "spend_vmh": {k: round(v, 1) for k, v in sorted(sp.items())}, "pool": pool,
            "chains": {f: {c[:12]: {k: v for k, v in r.items() if k in ("status", "same", "t0", "t1")} for c, r in runs.items() if on(day, r.get("t0", 0))} for f, runs in chains.items()}}


def jl_one(p: pathlib.Path) -> dict:
    with contextlib.suppress(Exception):
        return json.loads(p.read_text())
    return {}


def first_error(r: dict) -> str:
    return next((l.strip() for l in r.get("tail", "").splitlines() if l.strip().startswith(("error", "(fail)", "xfuzz:"))), "")[:120]


def ten_summary(day: str) -> dict:
    """The ten's runs by commit (those run today): per protocol the runs, proven, median ms, against the commit before."""
    tr = jl(TM / "ten.jsonl")
    by: dict = {}
    for r in tr:
        by.setdefault(r["commit"], {}).setdefault(r["id"], []).append(r)
    order = sorted(by, key=lambda c: min(r["t"] for v in by[c].values() for r in v))
    out = {}
    for i, c in enumerate(order):
        if not any(on(day, r["t"]) for v in by[c].values() for r in v):
            continue
        prev = by[order[i - 1]] if i else {}
        out[c] = {}
        for p, rs in by[c].items():
            ok = [r["ms"] / 1000 for r in rs if r.get("verdict") == "proven" and r.get("ms") is not None]
            s = {"runs": len(rs), "proven": len(ok), "median_s": round(statistics.median(ok), 2) if ok else None}
            if p in prev:
                pok = [r["ms"] / 1000 for r in prev[p] if r.get("verdict") == "proven" and r.get("ms") is not None]
                s.update(prev_median_s=round(statistics.median(pok), 2) if pok else None, prev_proven=len(pok))
                s["slower"] = bool(ok and pok and s["median_s"] > 1.5 * s["prev_median_s"] and s["median_s"] - s["prev_median_s"] >= 1)
                s["fewer"] = len(ok) / max(1, len(rs)) < len(pok) / max(1, len(prev[p])) - 0.1
            out[c][p] = s
    return out


def sections(day: str) -> list[str]:
    """The digest's own part (the generic digest adds the queue and the pool): alerts first, then new solves by config
    and family, targets, the per-commit chains, soundness, ideas and the spend by chain. digest/<day>.json has it all."""
    R = report(day)
    (TM / "digest").mkdir(parents=True, exist_ok=True)
    (TM / "digest" / f"{day}.json").write_text(json.dumps(R, indent=1, default=str))
    out = ["## Alerts"]
    al = R["alerts"]
    for kind in ("soundness", "regression"):
        xs = [a["what"] for a in al if a["kind"] == kind]
        out.append(f"- **{kind.upper()}: {len(xs)}**" if xs else f"- {kind}: none")
        out += [f"  - {x}" for x in xs[:12]] + ([f"  - ... {len(xs) - 12} more (digest.json)"] if len(xs) > 12 else [])
    out += ["", "## New solves (past the 60 s base, by the config that solved each first)"]
    if not R["solves"]:
        out.append("- none")
    for s in sorted(R["solves"], key=lambda s: -s["n"])[:20]:
        cfgs = ", ".join(f"{k} {len(v)}" for k, v in sorted(s["by"].items(), key=lambda kv: -len(kv[1])))
        ex = next(iter(s["by"].values()))[:2]
        out.append(f"- {s['bench']} {s['family']}: {s['n']} ({cfgs}) at {s['commit'][:12]}, e.g. {', '.join(t.rsplit('/', 1)[-1] for t in ex)}" + (f" **{s['note']}**" if s["note"] else ""))
    if len(R["solves"]) > 20:
        out.append(f"- ... {len(R['solves']) - 20} more families (digest.json)")
    out += ["", "## Sweeps"]
    for s in R["sweeps"]:
        out.append(f"- {s['commit'][:12]} {s['bench']}: {s['solved60']} of {s['tasks']} at 60 s, {s['past60']} past it; "
                   + (f"round {s['round']} of {s['of']}{' (done)' if s['done'] else ''}" if s["swept"] else "no sweep here (the per-commit chains' rows)")
                   + (f"; same inputs as {s['same'][:12]}" if s.get("same") else "") + (f"; at 60 s against {s['against'][:12]}: +{s['gained60']} -{s['lost60']}" if s.get("against") else ""))
    tg = R["targets"]
    out += ["", f"## Targets: {len(tg)} tasks solved only past 60 s (the latest profile, ms by stage; against the one before)"]
    for t in sorted(tg, key=lambda t: (t["bench"], t.get("secs") or 0))[:25]:
        top = sorted(t["stages"].items(), key=lambda kv: -kv[1])[:3]
        d = f"; was {t['prev_secs']:.0f} s at {t['prev_commit'][:12]}" if t.get("prev_secs") else ""
        out.append(f"- {t['bench']} {t['task'].rsplit('/', 1)[-1]}: {t['config']} {t['secs'] or 0:.0f} s{' (timed)' if t['timed'] else ''}"
                   + (f" [{', '.join(f'{k} {v / 1000:.0f}s' for k, v in top)}]" if top else "") + d)
    if len(tg) > 25:
        out.append(f"- ... {len(tg) - 25} more (digest.json)")
    out += ["", "## Speed (the solved set at 60 s, alone on a VM, against the previous run)"]
    for r in R["speed"][-8:]:
        out.append(f"- {r['commit'][:12]} {r['bench']}: {r['solved']} of {r['tasks']} solved" + (f"; against {r['prev'][:12]}: {len(r.get('slower', []))} slower (1.5x, 1 s), {len(r.get('lost', []))} lost, "
                                                                                                    f"{r.get('faster', 0)} faster, {len(r.get('noise', []))} flags not confirmed; {r.get('total_s')} s against {r.get('prev_total_s')} s in all" if r.get("prev") else " (the first run: its baseline)"))
    if not R["speed"]:
        out.append("- no run today")
    out += ["", "## Corpora"]
    for r in R["rw"][-3:]:
        out.append(f"- real world {r['commit'][:12]}: {r['proven']} proven, {r['refuted']} refuted of {r['laws']}" + (f"; {len(r.get('changes', []))} verdicts changed against {r['prev'][:12]}" if r.get("prev") else ""))
    for c, by in R["ic3syn"].items():
        out.append(f"- IC3Syn {c[:12]}: " + ", ".join(f"{sum(v.values())} of {len(v)} at {k.split(':')[0]} s" for k, v in sorted(by.items(), key=lambda kv: budget_of(kv[0]))))
    for c, ps in R["ten"].items():
        out.append(f"- the ten {c[:12]}: " + ", ".join(f"{p} {s['proven']}/{s['runs']} {s['median_s']}s" for p, s in sorted(ps.items())))
    s = R["soundness"]
    out += ["", "## Soundness",
            f"- fuzz: {sum(s['fuzz'].values())} seeds ({', '.join(f'{k} {v}' for k, v in s['fuzz'].items())}), {s['unsound']} unsound, {len(s['fuzz_failed'])} failed"
            + (" (a count a test expects at its own seeds): " + "; ".join(f"{k} {sd} ({e or 'exit ' + str(c)})" for k, sd, c, e in s["fuzz_failed"][:4]) if s["fuzz_failed"] else ""),
            f"- extractor correspondence: {sum(s['xfuzz'].values())} seeds ({', '.join(f'{k} {v}' for k, v in s['xfuzz'].items() if v)}), {s['xfuzz_tests']} tests passed, {len(s['xfuzz_failed'])} failed"
            + (f"; ran no test (a toolchain missing?): {', '.join(s['xfuzz_idle'])}" if s["xfuzz_idle"] else "")
            + (": " + "; ".join(f"{k} {sd} ({e or 'exit ' + str(c)})" for k, sd, c, e in s["xfuzz_failed"][:4]) if s["xfuzz_failed"] else ""),
            f"- mutants: {s['mutants']} run, {s['survived']} survived ({s['equivalent']} listed equivalent, {s['new_survivors']} new, {len(s['known_survivors'])} known before)"]
    if R["ideas"]:
        out += ["", "## Ideas"] + [f"- {m['name']}: {m.get('config')} on {m.get('tasks')} tasks: {m.get('status')}, {m.get('gained', 0)} gained, {m.get('lost', 0)} lost" for m in R["ideas"][-8:]]
    out += ["", "## Spend by chain (default-VM hours of item time; a timed item counts its whole VM)",
            "- " + (", ".join(f"{k} {v}" for k, v in R["spend_vmh"].items()) or "none") + f"; {sum(R['spend_vmh'].values()):.1f} in all; the pool: peak {R['pool']['peak_vms']} VMs, "
            f"{R['pool']['held_vmh']} VM-hours held, busy {R['pool']['busy_pct']}%"]
    if len(out) > LIMIT - 20:
        out = out[:LIMIT - 21] + ["- ... (cut at the digest's length: digest.json has it all)"]
    return out


def digest(day: str, quiet: bool = False) -> str:
    return T.digest(day, quiet, sections=sections)


def show_plan(bench: str):
    """What the sweep would run next at each budget on a benchmark, and why (from the cache; nothing launched)."""
    c = T.Cache()
    for b in [bench] if bench else [b for b in BENCHES if BENCHES[b]["env"]]:
        for bud in STAGES:
            p = plan(c, b, bud, 0)
            print(f"{b} {bud} s: {len(p)} rounds")
            for v, why in p:
                print(f"  {v:28} {why}")


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
    r.add_argument("--chains", default="", help=f"these chains only (default: all of {','.join(ALL_CHAINS)})")
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
    s = sub.add_parser("idea", help="knobs on a task set at a budget, against the base: the treadmill runs it (submission class)")
    s.add_argument("--name", default="")
    s.add_argument("--bench", required=True, choices=list(BENCHES))
    s.add_argument("--tasks", required=True, help="a file of task ids (one a line) or a glob over the benchmark's task ids")
    s.add_argument("--env", action="append", default=[], help="K=V (again for more)")
    s.add_argument("--budget", type=int, default=300)
    s.add_argument("--tree", default="", help="a lane's tree to run (default: main at the sweep's commit, its base from the cache)")
    s.add_argument("--local", action="store_true", help="this machine's treadmill directory, not the controller's")
    s = sub.add_parser("idea-results")
    s.add_argument("name")
    s.add_argument("--local", action="store_true")
    s = sub.add_parser("plan")
    s.add_argument("--bench", default="")
    sub.add_parser("status")
    s = sub.add_parser("digest")
    s.add_argument("--day", default="")
    a = ap.parse_args(argv)
    if a.cmd == "run":
        Treadmill(a.vms, a.budget_vmh, a.quiet, a.nogain, a.benches, a.sample, not a.no_soundness, not a.no_modal, a.max_wait, a.max_vms, a.step_vms, a.backlog_hours,
                  a.chains).run(a.hours, digest)
    elif a.cmd == "submit":
        T.submit(a.jobs, a.tree, a.name)
    elif a.cmd == "results":
        T.results(a.name)
    elif a.cmd == "idea":
        idea_submit(a)
    elif a.cmd == "idea-results":
        idea_results(a.name, a.local)
    elif a.cmd == "plan":
        show_plan(a.bench)
    elif a.cmd == "status":
        print((TM / "status.json").read_text() if (TM / "status.json").exists() else "not running")
    elif a.cmd == "digest":
        digest(a.day or today())


if __name__ == "__main__":
    if sys.argv[1:2] == ["run"]:
        import fanout
        fanout.reexec_with_modal()  # (Modal runs what boat can't: the interpreter that has its client)
    main(sys.argv[1:])
