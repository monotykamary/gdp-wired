"""One lightweight driver for an explicit-boat pass; all shards still use one starmap.

Auto/Modal must use the ordinary runner: those modes need the real Modal client.
The bar chooses this wrapper only for --backend boat, including boat retries.
"""
import pathlib
import runpy
import sys


def main():
    root, runner = map(pathlib.Path, sys.argv[1:3])
    args = sys.argv[3:]
    backend = None
    for i, arg in enumerate(args):
        if arg == "--backend" and i + 1 < len(args):
            backend = args[i + 1]
        elif arg.startswith("--backend="):
            backend = arg.split("=", 1)[1]
    if backend != "boat":
        raise SystemExit("boat-pass requires explicit --backend boat; use the ordinary runner for auto/Modal")
    door = root / ("supercomputer" if (root / "supercomputer" / "fanout.py").exists() else "modal")
    sys.path.insert(0, str(door))
    import agent
    sys.modules["modal"] = agent.modal_stub()
    import fanout
    # fanout.cli otherwise re-execs even an explicit boat pass under the Modal
    # CLI's interpreter. No fallback is disabled: the bar owns its three boat
    # attempts and launches the ordinary, real-Modal driver for attempt four.
    fanout.reexec_with_modal = lambda: None
    sys.argv = [str(runner), *args]
    sys.path.insert(0, str(runner.parent))
    runpy.run_path(str(runner), run_name="__main__")


if __name__ == "__main__":
    main()
