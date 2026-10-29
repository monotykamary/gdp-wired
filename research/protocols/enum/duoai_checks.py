"""DuoAI's candidate sets, counted: every file DuoAI hands to ivy_check during one run, kept with its invariant count.

    modal run research/protocols/enum/duoai_checks.py --out runs/enum/duoai [--protocols a,b] [--limit 60]

The image is ../duoai/duoai.py's (the same pinned artifact), with one change: DuoAI's IVY_CHECK_PATH points at a
wrapper that copies the file it is given (numbered, with the caller's process id) and then runs the real ivy_check, so
the run is DuoAI's own and every check it makes is on record. Outside the timed window the function counts, per
check, the invariants in the file and whether ivy_check said OK, and returns them with DuoAI's log.

Cost: one container per protocol, cpu=2.0 as duoai.py, a 300 s function timeout, scaledown_window=2, every call
cancelled when the client exits.
"""
import base64
import json
import pathlib
import sys
import time

import modal

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "duoai"))
import duoai  # noqa: E402  (the pinned image and PROTOCOLS)

WRAP = """#!/bin/bash
# keep a numbered copy of every file DuoAI checks, then the real ivy_check, its exit code passed back
n=$(date +%s%N)_$$
f="$1"; for a in "$@"; do case "$a" in *.ivy) f="$a";; esac; done
cp "$f" "/work/checks/$n-$PPID-$(basename "$f")" 2>/dev/null
REAL "$@" > "/work/checks/$n.out" 2>&1; s=$?
cat "/work/checks/$n.out"; exit $s
"""

image = duoai.image.run_commands(
    "mkdir -p /opt/ivywrap",
    f"echo {base64.b64encode(WRAP.encode()).decode()} | base64 -d | sed \"s|REAL|$(command -v ivy_check)|\" > /opt/ivywrap/ivy_check && chmod +x /opt/ivywrap/ivy_check && cat /opt/ivywrap/ivy_check",
    "sed -i 's|^#define IVY_CHECK_PATH .*|#define IVY_CHECK_PATH \"/opt/ivywrap/ivy_check\"|' /opt/DuoAI/src-c/InvRefiner.h && grep -n IVY_CHECK_PATH /opt/DuoAI/src-c/InvRefiner.h",
    "cd /opt/DuoAI/src-c && make -j2 >/dev/null && ls -la main",
).add_local_file(str(pathlib.Path(duoai.__file__).resolve()), "/root/duoai.py")  # (this module imports it in the container too)
app = modal.App("gdp-wired-enum-duoai", image=image)


@app.function(cpu=2.0, memory=4096, timeout=300, scaledown_window=2)
def counted(protocol: str, limit: int) -> dict:
    import os
    import re
    import shutil
    import signal
    import subprocess

    work = pathlib.Path("/work/DuoAI")
    shutil.rmtree("/work", ignore_errors=True)
    shutil.copytree("/opt/DuoAI", work, symlinks=True)
    checks = pathlib.Path("/work/checks")
    checks.mkdir()
    env = {"PATH": duoai.ENV_PATH, "HOME": "/root", "PYTHONUNBUFFERED": "1"}
    t0 = time.monotonic()
    import threading
    lines: list[str] = []
    p = subprocess.Popen(["python", "DuoAI.py", protocol], cwd=work, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         text=True, errors="replace", start_new_session=True)

    def read():
        for line in p.stdout:
            lines.append(f"{time.monotonic() - t0:8.3f} {line.rstrip()}")
    reader = threading.Thread(target=read, daemon=True)
    reader.start()
    try:
        p.wait(timeout=limit)
        killed = False
    except subprocess.TimeoutExpired:
        killed = True
    wall = round(time.monotonic() - t0, 3)
    try:
        os.killpg(p.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    p.wait()
    reader.join(timeout=5)
    out = "\n".join(lines)
    rows = []
    for f in sorted(checks.glob("*.ivy")):
        n = f.name.split("-", 1)[0]
        text = f.read_text(errors="replace")
        res = (checks / f"{n}.out")
        res_text = res.read_text(errors="replace").strip() if res.exists() else ""
        invs = [l for l in text.splitlines() if l.strip().startswith("invariant")]
        rows.append({"n": n, "file": f.name, "invariants": len(invs), "ok": res_text.endswith("OK"),
                     "failed": len(re.findall(r"FAIL", res_text)), "mtime": round(f.stat().st_mtime, 3)})
    first = sorted(checks.glob("*.ivy"))
    sample = first[0].read_text(errors="replace")[-30_000:] if first else ""
    largest = max(first, key=lambda f: f.stat().st_size).read_text(errors="replace")[-60_000:] if first else ""
    return {"protocol": protocol, "limit": limit, "killed": killed, "wall": wall, "checks": rows, "log": (out or "")[-100_000:],
            "first": sample, "largest": largest}


@app.local_entrypoint()
def main(out: str, protocols: str = "toy_consensus_forall,distributed_lock,consensus_wo_decide,ring_leader_election,sharded_key_value_store", limit: int = 60):
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    calls = []
    try:
        for p in protocols.split(","):
            calls.append((p, counted.spawn(p, limit)))
        for p, c in calls:
            try:
                r = c.get(timeout=400)
            except Exception as e:
                r = {"protocol": p, "error": repr(e), "checks": []}
            for k in ("log", "first", "largest"):
                if r.get(k):
                    (outdir / f"{p}.{k}.txt").write_text(r.pop(k))
            (outdir / f"{p}.json").write_text(json.dumps(r, indent=1))
            ch = r.get("checks", [])
            print(p, "wall", r.get("wall"), "checks", len(ch), "invariants per check", [c["invariants"] for c in ch][:40], flush=True)
    finally:
        for _, c in calls:
            try:
                c.cancel()
            except Exception:
                pass
