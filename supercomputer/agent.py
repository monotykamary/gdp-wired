"""gdp-wired's door to the supercomputer's `agent` module (the VM side, and the Modal stub the runners import without Modal). The code is the `supercomputer`
tool's (~/.local/share/supercomputer, or $SUPERCOMPUTER_HOME), configured by this repo's supercomputer.toml; importing
this file gives that module itself, so `import agent` here works as it did."""
import os as _os
import pathlib as _p
import sys as _sys

_tool = str(_p.Path(_os.environ.get("SUPERCOMPUTER_HOME") or _p.Path.home() / ".local/share/supercomputer"))
if _tool not in _sys.path:
    _sys.path.insert(0, _tool)
from supercomputer import config as _config  # noqa: E402

if _config._current is None:
    _config.use(_p.Path(__file__).resolve().parent.parent)
from supercomputer import agent as _m  # noqa: E402

_sys.modules[__name__] = _m
