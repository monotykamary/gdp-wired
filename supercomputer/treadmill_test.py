"""The treadmill's alert rules: python3 supercomputer/treadmill_test.py (reads the main checkout's git history and
kernel/MUTANTS.md as it stands).

stale_mutants.jsonl: the 73 survivors of 31 Oct's commits up to 17:42 (078bd1d, b5ba56b, a5b5814, 42f78b3, b7a2d85,
fdf3460, 0393f93, e4aef01, cf00792, b6a23b0, de6aa95), all stored without an equivalent flag, and the 85 later rows of
their signatures. The digest called 47 of them NEW survivors; 43 are listed equivalent now and 30 were killed at a later
commit, so none stands."""
import json
import pathlib
import sys
import time
import types
import unittest

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import treadmill as tm  # noqa: E402

ROWS = [json.loads(l) for l in (HERE / "stale_mutants.jsonl").read_text().splitlines() if l.strip()]
EQS = tm.equivalents((tm.MAIN / "kernel" / "MUTANTS.md").read_text())
OLD = ("078bd1d", "b5ba56b", "a5b5814", "42f78b3", "b7a2d85", "fdf3460", "0393f93", "e4aef01", "cf00792", "b6a23b0", "de6aa95")
WHEN: dict = {}


def lines_of(r):
    return tm.file_at(r["commit"], r["where"].rpartition(":")[0])


def rank(r):
    return (WHEN.setdefault(r["commit"], int(tm.git("show", "-s", "--format=%ct", r["commit"]).strip())), r["t"])


class MutantAlerts(unittest.TestCase):
    def test_the_stale_rows_stand_no_more(self):
        stale = [r for r in ROWS if r["commit"].startswith(OLD) and not r.get("killedBy")]
        self.assertEqual(len(stale), 73)
        self.assertFalse(any(r.get("equivalent") for r in stale))  # (the flag they were stored with)
        listed = [r for r in stale if tm.listed_equivalent(r, EQS, lines_of(r))]
        self.assertEqual(len(listed), 43)
        self.assertEqual(tm.standing_survivors(ROWS, EQS, lines_of, rank), set())

    def test_a_survivor_at_its_newest_commit_stands(self):
        # each killed-later signature, its later rows dropped: it survives where it ran last
        killed = {r["sig"] for r in ROWS if r.get("killedBy")}
        alone = [r for r in ROWS if r["sig"] in killed and not r.get("killedBy") and r["commit"].startswith(OLD)
                 and not tm.listed_equivalent(r, EQS, lines_of(r))]
        self.assertTrue(alone)
        self.assertEqual(tm.standing_survivors(alone, EQS, lines_of, rank), {r["sig"] for r in alone})

    def test_killed_first_survives_later_stands(self):
        r = next(r for r in ROWS if r.get("killedBy"))
        old, new = {**r, "t": r["t"] - 1}, {**r, "killedBy": None}
        self.assertEqual(tm.standing_survivors([old, new], [], lines_of, lambda x: (0, x["t"])), {r["sig"]})
        self.assertEqual(tm.standing_survivors([new, {**old, "t": r["t"] + 1}], [], lines_of, lambda x: (0, x["t"])), set())


class FuzzClasses(unittest.TestCase):
    def test_classes(self):
        c = tm.fuzz_class
        self.assertEqual(c(0, ""), "ok")
        self.assertEqual(c(1, "error: COVERAGE: clausal satisfiable: 0, under 1\n(fail) x"), "coverage")
        self.assertEqual(c(1, "error: COVERAGE: a\nerror: a model of a refuted goal"), "soundness")
        self.assertEqual(c(1, "bun test v1.4.3\n\ncdcl.test.ts:\n"), "infra")
        self.assertEqual(c(1, '(fail) t [600000ms]\nerror: Test "t" timed out after 600000ms'), "infra")


class FillYields(unittest.TestCase):
    """11-01 04:24: every fuzz kind at its day's cap since 00:10, the fill launched nothing, the VMs above the floor
    had nothing to run, the drain let 84 go and the next wave resumed 32 (churn). The fill's batch yields the caps."""

    def soundness(self):
        s = object.__new__(tm.Soundness)

        class TM:
            # (no soundness failure waiting for its re-run at the newest main: FuzzRecheck has those)
            state, batches, chains = {"fuzz_recheck_seeded": True}, [], {"fuzz", "xfuzz", "mutants"}

            def save_state(self):
                pass
        s.tm, s.commit, s.mutants, s.hash, s.tree = TM(), "c" * 40, [], "h", HERE.parent
        import types
        real = tm.Batch, tm.tracked
        tm.Batch, tm.tracked = (lambda _tm, label, chain, items, vms, *a, **k: types.SimpleNamespace(items=items, vms=vms)), (lambda *a, **k: None)
        self.addCleanup(lambda: setattr(tm, "Batch", real[0]) or setattr(tm, "tracked", real[1]))
        s.today_counts = lambda: {**{k: tm.FUZZ_PER_DAY for k in tm.FUZZ}, **{"x:" + l: tm.XFUZZ_PER_DAY for l in tm.XFUZZ}}
        return s

    def test_capped_batch_is_empty(self):
        self.assertIsNone(self.soundness().batch(4))

    def test_the_fill_yields_the_caps(self):
        b = self.soundness().batch(4, uncapped=True)
        self.assertIsNotNone(b)
        self.assertGreaterEqual(len(b.items), 4 * tm.SLOTS)


class ReaderFuzz(unittest.TestCase):
    """The reader fuzz takes one of each two of the readers' slots, beside xfuzz; at its day's cap a reader yields."""

    def soundness(self):
        s = FillYields.soundness(self)
        s.tm.chains = {"fuzz", "xfuzz", "rfuzz", "mutants"}
        s.today_counts = lambda: {}
        return s

    def test_both_kinds_in_a_batch(self):
        names = [it["name"] for it in self.soundness().batch(4).items]
        self.assertTrue(any(n.startswith("rfuzz-") for n in names) and any(n.startswith("xfuzz-") for n in names))
        rf = next(it for it in self.soundness().batch(4).items if it["name"].startswith("rfuzz-"))
        self.assertIn("--preload ./extract-fuzz.ts", json.dumps(rf))

    def test_capped(self):
        s = self.soundness()
        s.today_counts = lambda: {**{k: tm.FUZZ_PER_DAY for k in tm.FUZZ}, **{"x:" + l: tm.XFUZZ_PER_DAY for l in tm.XFUZZ}, **{"r:" + l: tm.RFUZZ_PER_DAY for l in tm.XFUZZ}}
        self.assertIsNone(s.batch(4))

    def test_the_hash_reads_cyclic(self):
        self.assertIn("kernel/cyclic.ts", tm.TRUSTED)


# The eight regressions of 31 Oct's digest, each run again at both commits with the prover's work counted (kernel/prove.ts
# fullWork, read at exit; quiet, two runs a side; a lost one also as four copies at once on its two vCPUs, the load the
# treadmill's VMs may carry): (task, commit, against, wall seconds before and at it, the work of the commit before's
# solved runs, this commit's runs' work, solved here). Equal work in more wall time, or a run stopped before its 60 s
# budget's work: the VM, all eight. (refreshTokenRotation#1's before is the law proven at ad88d36: 2c41f02's runs did
# not prove it again; transfers#5 at 9b454f0 was killed at 150 s in every run, quiet or loaded, and printed nothing.)
EIGHT = [
    ("ic3syn lock_server", "2c41f02", "b5ba56b", 3.846, 9.172, [45675, 45675], [45675, 45675], True),
    ("ic3syn simple_decentralized_lock", "2c41f02", "b5ba56b", 4.662, 10.002, [444702, 444702], [444702, 444702], True),
    ("ic3syn lock_server", "ad88d36", "b5ba56b", 3.846, 7.835, [45675, 45675], [45675, 45675], True),
    ("ic3syn lockserv", "ad88d36", "b5ba56b", 6.962, 15.812, [2465877, 2465877], [2465877, 2465877], True),
    ("rw refreshTokenRotation#0", "2c41f02", "b5ba56b", 16.1, 65.9, [1988218, 1943314], [4001829, 2756418, 2762896, 2715022, 2764144], False),
    ("rw refreshTokenRotation#1", "ad88d36", "2c41f02", 6.6, 49.2, [1682156], [5009718, 1640307, 1816607, 1784083, 1647384], False),
    ("rw slidingWindow#3", "ad88d36", "2c41f02", 57.6, 69.0, [6413405], [3535620, 1492448, 1492448, 1492448, 1492448], False),
    ("rw transfers#5", "9b454f0", "ad88d36", 84.3, 150.0, [17958637, 17938909], [None, None, None, None, None, None], False),
]


class SpeedByWork(unittest.TestCase):
    def test_the_eight_are_noise(self):
        for task, c, prev, was_s, now_s, was_w, now_w, solved in EIGHT:
            self.assertEqual(tm.by_work(was_w, now_w, solved), "noise", f"{task} at {c} against {prev}: {was_s} s -> {now_s} s")
        rw = [(w, n) for task, _, _, _, _, w, n, solved in EIGHT if task.startswith("rw")]
        self.assertFalse(any(tm.rw_lost([min(w), max((x for x in n if x is not None), default=None)]) for w, n in rw))

    def test_more_work_is_the_code(self):
        self.assertEqual(tm.by_work([1000], [1300], True), "slower")
        self.assertEqual(tm.by_work([1000], [1100], True), "noise")
        self.assertEqual(tm.by_work([1000], [60_000 * tm.FULL_PER_MS], False), "lost")  # (its whole budget spent, no answer)
        self.assertEqual(tm.by_work([], [5], True), "unmeasured")
        self.assertTrue(tm.rw_lost([]))  # (a change row from before the counters: a loss, as it was read then)


# The five UNSOUND cdcl seeds of 1 Nov's digest, all at a00fcee, before gen/laneD2's reader fix (main since 75c1171):
# their rows as fuzz.jsonl holds them (the tails cut), and each seed run again at the newest main.
A00, D2 = "a00fcee2960518d1b61f05f4a2283fc18966b652", "75c1171"
FIVE = [{"t": t, "commit": A00, "kind": "cdcl", "seed": sd, "code": 1, "class": "soundness", "tail": "(fail) the CDCL search's trees check, and refutes only goals with no model"}
        for t, sd in ((1793493727.47, 63373), (1793494151.15, 65377), (1793494585.63, 70621), (1793494593.05, 70990), (1793494595.57, 71551))]


class FuzzRecheck(unittest.TestCase):
    def test_fixed_at_the_newest_main(self):
        again = [{"t": r["t"] + 7200, "commit": D2, "kind": "cdcl", "seed": r["seed"], "code": 0, "recheck": True} for r in FIVE]
        status = tm.fuzz_status(FIVE + again, {("cdcl", r["seed"]) for r in FIVE})
        self.assertEqual({k: v[0] for k, v in status.items()}, {("cdcl", r["seed"]): "fixed" for r in FIVE})
        self.assertTrue(all(v[1]["first"] == A00 and v[1]["commit"] == D2 for v in status.values()))

    def test_pending_then_still_failing(self):
        keys = {("cdcl", r["seed"]) for r in FIVE}
        self.assertEqual({v[0] for v in tm.fuzz_status(FIVE, keys).values()}, {"pending"})
        still = [{**FIVE[0], "t": FIVE[0]["t"] + 7200, "commit": D2, "recheck": True}]
        self.assertEqual(tm.fuzz_status(FIVE + still, keys)[("cdcl", 63373)][0], "unsound")


# 11-01 to 11-02: 2,275 fuzz rows "exit -1" with no output, each filed as FUZZ CRASH (infrastructure) and run again.
# None was a run that crashed (a run prints at least bun's header): items boat gave back or never reported. They are no
# result now: not filed, not counted, not run again; a mutant, a recheck and a crash's second run are put back.
class NeverRan(unittest.TestCase):
    def test_never_ran_is_no_result(self):
        s = FillYields.soundness(self)
        s.today_counts = lambda: {}
        s.tm.state.update(fuzz_again=[["kernel", 5]], fuzz_recheck=[["cdcl", 6, "f" * 40]])
        s.mutants = [41]
        got, logged = [], []
        real = tm.Batch, tm.append, tm.log
        tm.tracked = lambda _tm, chain, label, on_row: on_row  # (FillYields' stub restores the real one)
        tm.Batch = lambda _tm, label, chain, items, vms, on_row, root=None, after=None, **k: types.SimpleNamespace(items=items, on_row=on_row, after=after)
        tm.append, tm.log = (lambda path, row: got.append((path.name, row))), logged.append
        self.addCleanup(lambda: (setattr(tm, "Batch", real[0]), setattr(tm, "append", real[1]), setattr(tm, "log", real[2])))
        b = s.batch(1)
        names = [it["name"] for it in b.items]
        self.assertIn("mutant-41", names)
        self.assertIn("kernel-fuzz-5-again", names)
        self.assertIn("cdcl-fuzz-6-recheck", names)
        fresh = [n for n in names if n.split("-")[1] == "fuzz" and n.split("-")[-1].isdigit()]
        ran, crashed = fresh[0], fresh[1]
        logs = {ran: {"out": "bun test v1.4.3\n 12 pass\n"}, crashed: {"out": "bun test v1.4.3\nkernel.test.ts:\n"}}
        for it in b.items:
            if it["name"] == ran:
                b.on_row(it, {"code": 0})
            elif it["name"] == crashed:
                b.on_row(it, {"code": -1})
            elif it["name"] in ("mutant-41", "kernel-fuzz-5-again"):
                b.on_row(it, {"code": -1, "error": "boat couldn't run it now", "lost": True})
            # (the rest: no row at all)
        b.after(logs)
        fuzz = [r for f, r in got if f == "fuzz.jsonl"]
        self.assertEqual(sorted(r["code"] for r in fuzz), [-1, 0])  # (the run and the crash, no more)
        self.assertEqual(next(r for r in fuzz if r["code"] == -1)["class"], "infra")
        self.assertFalse([f for f, _ in got if f in ("xfuzz.jsonl", "rfuzz.jsonl", "mutants.jsonl")])
        self.assertEqual(s.mutants, [41])
        self.assertIn(["kernel", 5], s.tm.state["fuzz_again"])
        self.assertIn(["cdcl", 6, "f" * 40], s.tm.state["fuzz_recheck"])
        self.assertEqual(s.tm.state["fuzz_again"].count(["kernel", 5]), 1)
        self.assertEqual(sum(1 for l in logged if "FUZZ CRASH" in l), 1)
        self.assertTrue(any("never ran" in l and "boat couldn't run it now (2)" in l for l in logged))


# The logs read as they grow (tm.Log): 11-01 to 11-02 the loop parsed fuzz.jsonl, xfuzz.jsonl and rfuzz.jsonl whole
# (500k rows, 80 MB) at each fill step for the day's counts, a core of the laptop for minutes at a time. A Log's
# tallies and day rows are the whole file's filtered, and a call parses only what was appended since the last.
class Logs(unittest.TestCase):
    def setUp(self):
        import tempfile
        self.dir = pathlib.Path(tempfile.mkdtemp())
        self.addCleanup(lambda: __import__("shutil").rmtree(self.dir, ignore_errors=True))

    def rows(self, n, t0, step=97.3):
        return [{"t": t0 + i * step, "kind": ("kernel", "cdcl", "tamper")[i % 3], "seed": i, "code": i % 7 == 0} for i in range(n)]

    def write(self, p, rows, mode="a"):
        with open(p, mode) as f:
            f.write("".join(json.dumps(r) + "\n" for r in rows))

    def naive(self, p, day):
        rows = tm.jl(p)
        c: dict = {}
        for r in rows:
            if time.strftime("%Y-%m-%d", time.gmtime(r["t"])) == day:
                c[r["kind"]] = c.get(r["kind"], 0) + 1
        return c, [r for r in rows if time.strftime("%Y-%m-%d", time.gmtime(r["t"])) == day]

    def test_day_of_is_strftime(self):
        import random
        rnd = random.Random(7)
        for t in [0, 86399.999, 86400, 1793491199.9999, 1793491200.0] + [rnd.uniform(0, 4e9) for _ in range(20000)]:
            self.assertEqual(tm.day_of(t), time.strftime("%Y-%m-%d", time.gmtime(t)), t)

    def test_tallies_and_day_rows_are_the_whole_files(self):
        p = self.dir / "fuzz.jsonl"
        log = tm.Log(p, *tm.LOGS["fuzz.jsonl"])
        self.write(p, self.rows(5000, 1793300000))
        for k in range(6):  # (appended between calls, a line cut in the middle of a write too)
            day = tm.day_of(1793300000 + k * 90000)
            counts, rows = self.naive(p, day)
            self.assertEqual(log.tally(day), counts)
            self.assertEqual(log.rows_on(day), rows)
            self.write(p, self.rows(700, 1793300000 + 5000 * 97.3 + k * 70000))
            with open(p, "a") as f:
                f.write(json.dumps(self.rows(1, 1793900000)[0])[:20])
            self.assertEqual(log.tally(day), counts)  # (the half line: not read yet)
            with open(p, "a") as f:
                f.write(json.dumps(self.rows(1, 1793900000)[0])[20:] + "\n")

    def test_a_call_parses_only_what_was_appended(self):
        p = self.dir / "fuzz.jsonl"
        folded = []
        _, fold = tm.LOGS["fuzz.jsonl"]
        log = tm.Log(p, "t", lambda acc, r: folded.append(r) or fold(acc, r))
        self.write(p, self.rows(20000, 1790000000))  # (the days before)
        day = tm.day_of(time.time())
        log.tally(day)
        self.assertEqual(len(folded), 20000)
        for _ in range(50):  # (a tick: ~35 rows appended, the counts asked a few times)
            self.write(p, self.rows(35, time.time(), step=0.01))
            for _ in range(4):
                log.tally(day)
        self.assertEqual(len(folded), 20000 + 50 * 35)
        self.assertEqual(log.tally(day)["kernel"] + log.tally(day)["cdcl"] + log.tally(day)["tamper"], 50 * 35)

    def test_a_file_replaced_or_cut_is_read_again(self):
        p = self.dir / "fuzz.jsonl"
        log = tm.Log(p, *tm.LOGS["fuzz.jsonl"])
        self.write(p, self.rows(300, 1793300000))
        day = tm.day_of(1793300000)
        log.tally(day)
        self.write(p, self.rows(10, 1793300000), mode="w")
        self.assertEqual(log.tally(day), self.naive(p, day)[0])
        p.unlink()
        self.assertEqual(log.tally(day), {})

    def test_sums_as_the_digest_summed(self):
        p = self.dir / "vms.jsonl"
        rows = [{"t": 1793300000 + i, "day": "2026-10-30", "vms": i % 13, "target": 8, "vmh": 0.1 * (i % 9) / 3} for i in range(3000)]
        self.write(p, rows)
        a = tm.Log(p, *tm.LOGS["vms.jsonl"]).tally("2026-10-30")
        self.assertEqual((a["vms"], a["target"], sum(a["vmh"])), (max(r["vms"] for r in rows), 8, sum(r["vmh"] for r in rows)))
        s = self.dir / "spend.jsonl"
        rows = [{"day": "2026-10-30", "chain": ("sound", "sweep")[i % 2], "vmh": 0.0137 * (i % 11)} for i in range(3000)]
        self.write(s, rows)
        sp: dict = {}
        for r in rows:
            sp[r["chain"]] = sp.get(r["chain"], 0.0) + r["vmh"]
        self.assertEqual(tm.Log(s, *tm.LOGS["spend.jsonl"]).tally("2026-10-30"), sp)

    def test_rows_of_seeds(self):
        p = self.dir / "fuzz.jsonl"
        rows = self.rows(3000, 1793300000)
        self.write(p, rows)
        self.assertEqual(tm.rows_of(p, "seed", {5, 2999, 77777}), [r for r in rows if r["seed"] in (5, 2999)])
        self.assertEqual(tm.rows_of(p, "seed", set()), [])


if __name__ == "__main__":
    unittest.main()
