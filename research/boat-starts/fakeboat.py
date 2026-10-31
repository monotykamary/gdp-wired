#!/usr/bin/env python3
"""A boat CLI that fails on purpose, for the fallback tests (research/boat-starts/fallback.sh): BOAT_BIN points here,
GDPW_FAKE_BOAT names the failure, and every other call goes to the real CLI ($BOAT_REAL).

    nostarts   `limits`: every start of the day, hour and minute spent, the free ones and the wallet's
    api        every call fails (exit 1), as when boat's API is down
    create     `new` and `resume` fail (exit 1), as a creation or a resume refused or timed out
    lose       an agent `tick` on a VM fails as the VM gone (404), once the batch has started items
"""
import json
import os
import subprocess
import sys

mode, real, args = os.environ.get("GDPW_FAKE_BOAT", ""), os.environ.get("BOAT_REAL") or os.path.expanduser("~/.ascii/bin/boat"), sys.argv[1:]
cmd = args[0] if args else ""
if mode == "api" or (mode == "create" and cmd in ("new", "resume")):
    print(json.dumps({"event": "error", "error": f"fake boat: {cmd} refused"}))
    sys.exit(1)
if mode == "lose" and cmd == "exec" and "tick" in args and '"start": []' not in " ".join(args):
    flag = os.path.join(os.environ.get("TMPDIR", "/tmp"), f"fakeboat-lose-{os.getppid()}")
    if os.path.exists(flag):
        print(json.dumps({"exitCode": 1, "stdout": "", "stderr": "sandbox not found (404)", "success": False}))
        sys.exit(0)
    open(flag, "w").close()  # (the first tick goes through: the items start, then the VM is lost)
p = subprocess.run([real, *args], capture_output=True, text=True)
out = p.stdout
if mode == "nostarts" and cmd == "limits" and p.returncode == 0:
    d = json.loads(out)
    for k, w in (("day", "perDay"), ("hour", "perHour"), ("minute", "perMinute")):
        lim = d.get("startLimitsWithWallet", {}).get(w, d["starts"][k]["limit"])
        d["starts"][k].update(used=lim, remaining=d["starts"][k]["limit"] - lim)
    out = json.dumps(d)
sys.stdout.write(out)
sys.stderr.write(p.stderr)
sys.exit(p.returncode)
