"""Regression checks for independently extractable per-job goal archives.
Run: python3 research/query/pack_test.py (requires the runner's zstd).
"""
import io
import os
import pathlib
import subprocess
import tarfile
import tempfile
import unittest

from goalpack import pack_goal_files


class GoalPackTests(unittest.TestCase):
    def test_hardlinked_goals_are_independent_regular_entries(self):
        with tempfile.TemporaryDirectory() as temp:
            root = pathlib.Path(temp)
            (root / "research/query").mkdir(parents=True)
            goals = root / "goals"
            for name in ("left", "right"):
                (goals / name).mkdir(parents=True)
            content = b'{"expected": 123}\n'
            (goals / "left/goal.json").write_bytes(content)
            os.link(goals / "left/goal.json", goals / "right/goal.json")
            packed = pack_goal_files(root, goals, [f"goals/{name}/goal.json" for name in ("left", "right")])
            raw = subprocess.check_output(["zstd", "-q", "-d", "-c", str(root / packed)])
            with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
                for name in ("left", "right"):
                    member = archive.getmember(f"goals/{name}/goal.json")
                    self.assertTrue(member.isfile(), f"not independently extractable: {member.name}")
                    self.assertEqual(archive.extractfile(member).read(), content)
            out = root / "one-job"
            out.mkdir()
            subprocess.run(["tar", "--zstd", "-xf", str(root / packed), "-C", str(out), "goals/right/goal.json"], check=True)
            self.assertEqual((out / "goals/right/goal.json").read_bytes(), content)
            self.assertFalse((out / "goals/left/goal.json").exists())

    def test_no_goals_needs_no_archive(self):
        with tempfile.TemporaryDirectory() as temp:
            root = pathlib.Path(temp)
            self.assertEqual(pack_goal_files(root, root / "missing", []), "")
            self.assertEqual(list(root.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
