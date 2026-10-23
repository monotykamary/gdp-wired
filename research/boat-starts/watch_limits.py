"""Samples `boat limits` every --every seconds into a TSV (UTC time, starts used per minute, hour and day, VMs up),
to learn how boat's day of starts resets (rolling 24 hours, or at a fixed time).

    python3 research/boat-starts/watch_limits.py --out research/boat-starts/limits-log.tsv [--every 120] [--hours 20]
"""
import argparse, json, os, pathlib, subprocess, time

BOAT = os.environ.get("BOAT_BIN") or str(pathlib.Path.home() / ".ascii/bin/boat")
ap = argparse.ArgumentParser()
ap.add_argument("--out", required=True)
ap.add_argument("--every", type=int, default=120)
ap.add_argument("--hours", type=float, default=20)
a = ap.parse_args()
out = pathlib.Path(a.out)
if not out.exists():
    out.write_text("utc\tminute_used\thour_used\tday_used\tday_remaining\tactive\n")
end = time.time() + a.hours * 3600
while time.time() < end:
    try:
        p = subprocess.run([BOAT, "limits", "--json"], capture_output=True, text=True, timeout=60, env={**os.environ, "BOAT_NO_UPDATE": "1"})
        d = json.loads(p.stdout)
        s = d["starts"]
        line = f"{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}\t{s['minute']['used']}\t{s['hour']['used']}\t{s['day']['used']}\t{s['day']['remaining']}\t{d['activeSandboxes']}\n"
    except Exception as e:
        line = f"{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}\terror\t{str(e)[:80]}\n"
    with open(out, "a") as f:
        f.write(line)
    time.sleep(a.every)
