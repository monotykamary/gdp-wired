"""The treadmill's alert rules: python3 supercomputer/treadmill_test.py (reads the main checkout's git history and
kernel/MUTANTS.md as it stands).

stale_mutants.jsonl: the 73 survivors of 31 Oct's commits up to 17:42 (078bd1d, b5ba56b, a5b5814, 42f78b3, b7a2d85,
fdf3460, 0393f93, e4aef01, cf00792, b6a23b0, de6aa95), all stored without an equivalent flag, and the 85 later rows of
their signatures. The digest called 47 of them NEW survivors; 43 are listed equivalent now and 30 were killed at a later
commit, so none stands."""
import json
import pathlib
import sys
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
            state, batches, chains = {}, [], {"fuzz", "xfuzz", "mutants"}

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


if __name__ == "__main__":
    unittest.main()
