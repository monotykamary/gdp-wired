"""Isolated tests of the actual treadmill registry and fingerprint; no scheduler imports."""
import ast
import hashlib
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
TREE = ast.parse((ROOT / 'supercomputer/treadmill.py').read_text())
REGISTRY = ast.literal_eval(next(n.value for n in TREE.body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'FUZZ' for t in n.targets)))
METHOD = next(m for n in TREE.body if isinstance(n, ast.ClassDef) and n.name == 'Soundness' for m in n.body if isinstance(m, ast.FunctionDef) and m.name == 'fuzz_fingerprint')
METHOD.decorator_list = []
SCOPE = {'pathlib': pathlib, 'hashlib': hashlib}
exec(compile(ast.Module(body=[METHOD], type_ignores=[]), '<actual treadmill fingerprint>', 'exec'), SCOPE)


class TranslationSweep(unittest.TestCase):
    def test_registry_is_bounded_and_uses_default_source_protection(self):
        cwd, command = REGISTRY['translation']
        self.assertEqual(cwd, '.')
        command = command.format(s=31)
        for option in ('--seed 31', '--count 26', '--case-ms 15000', '--replay', '--expect-clean'):
            self.assertIn(option, command)
        self.assertNotIn('--no-replay', command)

    def test_reader_law_native_and_generator_changes_invalidate_the_fingerprint(self):
        fingerprint = SCOPE['fuzz_fingerprint']
        with tempfile.TemporaryDirectory() as d:
            root = pathlib.Path(d)
            for file in ('kernel/kernel.ts', 'core/check.ts', 'core/solver.ts', 'core/laws.ts', 'core/source-check.ts', 'core/native-law.ts', 'core/extract-read.ts', 'research/translation-fuzz/model.ts'):
                path = root / file
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(file)
            before = fingerprint(root)
            (root / 'README.md').write_text('documentation only')
            self.assertEqual(before, fingerprint(root))
            for file in ('core/laws.ts', 'core/source-check.ts', 'core/native-law.ts', 'core/extract-read.ts', 'research/translation-fuzz/model.ts'):
                (root / file).write_text('changed')
                after = fingerprint(root)
                self.assertNotEqual(before, after)
                before = after


if __name__ == '__main__':
    unittest.main()
