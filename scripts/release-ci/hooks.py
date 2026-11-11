"""Local control-tree adapter; the source path is generated, never restored from a Mac constant."""
import importlib.util
import pathlib
import sys

SOURCE = pathlib.Path(__file__).with_name('source-root.txt').read_text().strip()
SOURCE = pathlib.Path(SOURCE)
spec = importlib.util.spec_from_file_location('gdp_source_hooks', SOURCE / 'supercomputer/hooks.py')
original = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = original
spec.loader.exec_module(original)


def layers(_root):
    return original.layers(SOURCE)


def __getattr__(name):
    return getattr(original, name)
