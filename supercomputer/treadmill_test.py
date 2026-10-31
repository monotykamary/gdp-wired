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


if __name__ == "__main__":
    unittest.main()
