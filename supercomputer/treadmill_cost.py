"""The treadmill's own CPU, measured on a copy of its directory (runs/treadmill): the per-tick work of the loop's fill
(Soundness.batch: the day's fuzz counts, the floor and the fill's steps), the status's VM-hours (vmh_today) and the
hourly digest (sections), as the controller's process runs them, with the logs growing as they grow live.

    python3 supercomputer/treadmill_cost.py --tm <copy of runs/treadmill> [--code DIR] [--git TABLE.json] [--ticks 240]
                                            [--fill 5] [--day YYYY-MM-DD] [--digests 2]

--code: the directory of the treadmill.py to measure (default this one's: a commit's, to compare); --git: a table of
the git answers the digest asks (`show -s --format=%ct <commit>`, `show <commit>:<file>`) where the tree has no
history (a boat VM's). Prints JSON: CPU seconds a tick (median, p95, max) after the first (the logs' first read), the
first tick's, the digest's per call, CPU seconds an hour (ticks of 15 s plus one digest), and the outputs' hashes (the
day's counts, digest.json, the digest's lines) so two codes' outputs can be compared."""
import argparse
import hashlib
import importlib
import json
import os
import pathlib
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
import types


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tm", required=True)
    ap.add_argument("--code", default=str(pathlib.Path(__file__).resolve().parent))
    ap.add_argument("--git", default="")
    ap.add_argument("--ticks", type=int, default=240)
    ap.add_argument("--fill", type=int, default=5, help="fill steps a tick (each Soundness.batch of 4 VMs, capped then uncapped)")
    ap.add_argument("--day", default="")
    ap.add_argument("--digests", type=int, default=2)
    a = ap.parse_args()
    work = pathlib.Path(tempfile.mkdtemp()) / "tm"
    shutil.copytree(a.tm, work)  # (the ticks append to its logs)
    os.environ["SUPERCOMPUTER_TREADMILL"] = str(work)
    sys.path.insert(0, a.code)
    tm = importlib.import_module("treadmill")
    git_calls = [0]
    if a.git:
        table = json.loads(pathlib.Path(a.git).read_text())

        def git(*args, cwd=None):
            git_calls[0] += 1
            k = " ".join(args)
            if k not in table:
                raise subprocess.CalledProcessError(128, ["git", *args])
            return table[k]
        tm.git = git
    else:
        real = tm.git

        def git(*args, cwd=None):
            git_calls[0] += 1
            return real(*args, cwd=cwd) if cwd else real(*args)
        tm.git = git
    tm.boat.extra_starts = lambda: (_ for _ in ()).throw(RuntimeError("not measured"))

    # the fill as the loop runs it: a Soundness at main, its batches (stubs: no VM), the live ones counted per tick
    class Stub:
        def __init__(self, _tm, label, chain, items, vms, *x, **k):
            self.label, self.chain, self.items, self.vms, self.done = label, chain, items, vms, False

    tm.Batch = Stub
    state = json.loads((work / "state.json").read_text()) if (work / "state.json").exists() else {}
    state["fuzz_recheck_seeded"] = True
    fake = types.SimpleNamespace(state=state, batches=[], chains=set(tm.ALL_CHAINS), save_state=lambda: None)
    s = object.__new__(tm.Soundness)
    s.tm, s.commit, s.tree, s.dir, s.mutants, s.hash = fake, "0" * 40, work, work, [], "h"
    vmh_today = tm.Treadmill.vmh_today  # (the generic one, or the override)

    # the logs as they grow live (11-01's rates): fuzz ~200k rows a day, xfuzz ~32k, spend ~250k, a VM sample a tick
    per_tick = {"fuzz.jsonl": 35, "xfuzz.jsonl": 6, "spend.jsonl": 45, "vms.jsonl": 1}
    seed = [10 ** 7]

    def grow():
        now = time.time()
        for f, n in per_tick.items():
            rows = []
            for _ in range(n):
                seed[0] += 1
                rows.append({"fuzz.jsonl": {"t": now, "commit": "0" * 40, "kind": "kernel", "seed": seed[0], "code": 0},
                             "xfuzz.jsonl": {"t": now, "commit": "0" * 40, "lang": "go", "seed": seed[0], "code": 0, "pass": 40, "fail": 0},
                             "spend.jsonl": {"t": now, "day": tm.today(), "chain": "sound", "label": "sound x", "secs": 120.0, "vmh": 0.0167},
                             "vms.jsonl": {"t": round(now), "day": tm.today(), "vms": 40, "target": 8, "vmh": 0.1667}}[f])
            with open(work / f, "a") as fh:
                fh.write("".join(json.dumps(r) + "\n" for r in rows))

    counts0 = s.today_counts()
    cpu = []
    for k in range(a.ticks):
        if k:
            grow()
        c0 = time.process_time()
        for b in fake.batches[:-40]:  # (the live batches: about 40 at once)
            b.done = True
        fake.batches = [b for b in fake.batches if not b.done]
        for _ in range(a.fill):
            b = s.batch(4) or s.batch(4, uncapped=True)
            if b:
                fake.batches.append(b)
        vmh_today(None)
        cpu.append(time.process_time() - c0)
    day = a.day or tm.today()
    dg = []
    for _ in range(a.digests):
        g0, c0, w0 = git_calls[0], time.process_time(), time.time()
        lines = tm.sections(day)
        dg.append({"cpu_s": round(time.process_time() - c0, 3), "wall_s": round(time.time() - w0, 3), "git_calls": git_calls[0] - g0})
    rest = sorted(cpu[1:]) or [0.0]
    h = lambda x: hashlib.sha256(x.encode()).hexdigest()[:16]  # noqa: E731
    out = {"code": a.code, "python": sys.version.split()[0], "ticks": a.ticks, "fill": a.fill,
           "first_tick_cpu_s": round(cpu[0], 3), "tick_cpu_s": {"median": round(statistics.median(rest), 5), "p95": round(rest[int(0.95 * (len(rest) - 1))], 5), "max": round(rest[-1], 5)},
           "digest": dg, "cpu_s_per_hour": round(240 * statistics.mean(rest) + dg[-1]["cpu_s"], 1),
           "counts_at_start": counts0, "digest_json_sha": h((work / "digest" / f"{day}.json").read_text()), "digest_lines_sha": h("\n".join(lines)), "day": day}
    print(json.dumps(out))


if __name__ == "__main__":
    main()
