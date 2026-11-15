"""Pure wrapper controls; no JVM, Bun, assets, dispatch or proof search."""
import importlib.util
from pathlib import Path
import tempfile
import sys
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("tlc_native", Path(__file__).with_name("tlc_native.py"))
assert spec and spec.loader
native = importlib.util.module_from_spec(spec)
spec.loader.exec_module(native)


class NativeTLC(unittest.TestCase):
    def setUp(self):
        self.tlc = {"exit": 0, "states": 4, "edges": 3, "complete": True, "violated": False}
        self.port = {"exit": 0, "states": 4, "edges": 3, "done": True, "bad": 0, "edgeComplete": True, "ms": 1}
        self.broken = {"exit": 0, "done": True, "bad": 1, "ms": 1}

    def test_good_crosscheck(self):
        self.assertEqual(native.verdict(self.tlc, self.port, self.broken), [])

    def test_refuses_each_missing_or_bad_fact(self):
        for which, key, value in [(0, "exit", 124), (0, "complete", False), (0, "violated", True),
                                  (0, "states", None), (0, "edges", None), (1, "exit", 1),
                                  (1, "done", False), (1, "bad", 1), (1, "states", 3),
                                  (1, "edges", 2), (1, "edgeComplete", False), (1, "ms", 120001),
                                  (0, "exit", False), (0, "states", True), (0, "complete", 1),
                                  (1, "bad", False), (1, "edges", True), (1, "states", True),
                                  (2, "exit", 1), (2, "done", False), (2, "bad", 0),
                                  (2, "bad", True), (2, "ms", None)]: 
            rows = [self.tlc.copy(), self.port.copy(), self.broken.copy()]
            rows[which][key] = value
            with self.subTest(which=which, key=key):
                self.assertTrue(native.verdict(*rows))

    def test_record_identity_and_multiplicity(self):
        self.assertEqual(native.record('noise\n{"id":"consensus"}\n', 'consensus'), {"id": "consensus"})
        for text in ['', '{"id":"other"}', '{"id":"consensus"}\n{"id":"consensus"}']:
            with self.assertRaises(ValueError):
                native.record(text, 'consensus')

    def test_invalid_ids_never_spawn(self):
        with patch.object(native, 'command') as spawn:
            for pid in ['../x', 'consensus;exit', 'x,y']:
                with self.assertRaises(ValueError):
                    native.one(pid, 100)
            with self.assertRaises(ValueError):
                native.one('consensus', 0)
            spawn.assert_not_called()

    def test_cfg_failure_retained_and_refused(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(native, 'command', return_value=(1, 'bad cfg')):
            result = native.one('consensus', 100, Path(tmp))
            self.assertEqual(result['status'], 'not-verified')
            self.assertIn('cfg emission exited 1', result['error'])
            self.assertTrue((Path(tmp) / 'result.json').is_file())


    def test_timeout_stops_exact_child_tree(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)
            program = ("import pathlib,subprocess,sys,time; "
                       "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)']); "
                       "pathlib.Path('child.pid').write_text(str(p.pid)); time.sleep(30)")
            code, _ = native.command([sys.executable, '-c', program], path, 2, path / 'timeout.log')
            self.assertEqual(code, 124)
            pid = int((path / 'child.pid').read_text())
            stat = Path(f'/proc/{pid}/stat')
            if stat.exists():
                self.assertEqual(stat.read_text().rsplit(')', 1)[1].split()[0], 'Z')

    def test_termination_stops_exact_child_tree(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)
            program = ("import os,pathlib,signal,subprocess,sys,time; "
                       "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)']); "
                       "pathlib.Path('child.pid').write_text(str(p.pid)); "
                       "os.kill(os.getppid(),signal.SIGTERM); time.sleep(30)")
            with self.assertRaises(InterruptedError):
                native.command([sys.executable, '-c', program], path, 10, path / 'term.log')
            pid = int((path / 'child.pid').read_text())
            stat = Path(f'/proc/{pid}/stat')
            if stat.exists():
                self.assertEqual(stat.read_text().rsplit(')', 1)[1].split()[0], 'Z')


if __name__ == '__main__':
    unittest.main()
