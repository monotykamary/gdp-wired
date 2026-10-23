"""Today's mix of batches for the simulation: every run under the given runs dirs whose backend was boat or auto
(the work that asked boat for VMs, whether boat or Modal ran it), with its start, its jobs' measured seconds and
weights (slots of 2 vCPU and 4 GB), and what the old policy did with it (from its log's `[boat]` lines and its
backends.json).

    python3 research/boat-starts/mix.py <runs dir> --since 2026-10-22T17:00:00Z --until 2026-10-23T02:30:00Z > research/boat-starts/mix.json

A run.py job's seconds are its summary.tsv's (its weight from <out>-jobs.json, else modal/suite.json by name); a compare
runner's call is one task (its results.jsonl's seconds), weight 2 for TIP (BOAT["weight"]) and 1 otherwise.
"""
import argparse, datetime, json, math, pathlib, re, sys

ap = argparse.ArgumentParser()
ap.add_argument("runs")
ap.add_argument("--since", required=True)
ap.add_argument("--until", required=True)
ap.add_argument("--suite", default=str(pathlib.Path(__file__).resolve().parents[2] / "modal" / "suite.json"))
a = ap.parse_args()
iso = lambda s: datetime.datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp()
since, until = iso(a.since), iso(a.until)
root = pathlib.Path(a.runs)
TZ = datetime.timezone(datetime.timedelta(hours=7))


def weight(j):
    cpu, mem = j.get("cpu", 2.0), j.get("memory", 4096)
    w = max(math.ceil(cpu / 2), math.ceil(mem / 4096), 1)
    return w, ("large" if w > 2 else "default")


suite = {j["name"]: j for j in json.load(open(a.suite))}
out = []
for bj in sorted(root.rglob("backends.json")):
    d = json.loads(bj.read_text())
    if d.get("backend") not in ("auto", "boat"):
        continue
    run = bj.parent
    rel = str(run.relative_to(root.parent))
    log = next((p for p in [run.with_suffix(".log"), run.parent / (run.name + ".client.log")] if p.exists()), None)
    start = None
    obs = {"vms": None, "created": None, "resumed": None, "up": None}
    if log:
        text = log.read_text(errors="replace")
        m = re.search(r"^\[boat\] batch (\d{8}-\d{6})", text, re.M)
        if m:
            start = datetime.datetime.strptime(m[1], "%Y%m%d-%H%M%S").replace(tzinfo=TZ).timestamp()
        m = re.search(r"boat: (\d+) VMs \((\d+) created, (\d+) resumed, (\d+) already up\)", text)
        if m:
            obs = {"vms": int(m[1]), "created": int(m[2]), "resumed": int(m[3]), "up": int(m[4])}
    b = d.get("boat") or d
    if obs["vms"] is None and b.get("vms") is not None:
        obs = {"vms": b["vms"], "created": b["created"], "resumed": b["resumed"], "up": b["leased_running"]}
    if start is None:
        start = bj.stat().st_mtime - float(d.get("wall_s") or 0)
    if not (since <= start < until):
        continue
    jobs, kind = [], ""
    if (run / "summary.tsv").exists():
        kind = "run.py"
        spec = {}
        for p in [run.parent / (run.name + "-jobs.json")]:
            if p.exists():
                spec = {j["name"]: j for j in json.load(open(p))}
        unknown = 0
        for l in (run / "summary.tsv").read_text().splitlines():
            f = l.split("\t")
            if len(f) < 3 or float(f[2]) < 0:
                continue
            j = spec.get(f[0]) or suite.get(f[0])
            if j is None:
                unknown += 1
                j = {}
            w, t = weight(j)
            jobs.append([float(f[2]), w, t, f[3] if len(f) > 3 else ""])
    elif (run / "results.jsonl").exists():
        kind = "runner"
        w = 2 if "/tip" in rel or rel.endswith("tip") or "tip-" in run.name else 1
        for l in (run / "results.jsonl").read_text().splitlines():
            try:
                r = json.loads(l)
            except Exception:
                continue
            jobs.append([float(r.get("seconds", 0)), w, "default", ""])
    out.append({"run": rel, "batch": b.get("batch"), "start": round(start, 1), "start_utc": time_utc if (time_utc := datetime.datetime.fromtimestamp(start, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")) else "",
                "backend": d.get("backend"), "where": d.get("where"), "fallbacks": d.get("fallbacks"), "wall_s": d.get("wall_s"), "kind": kind,
                "observed": obs, "boat": {k: b.get(k) for k in ("to_running_s", "prep_s", "held_s", "ready_held_s", "busy_s", "idle_vm_s", "bring_up_s", "dollars_so_far")} if b.get("held_s") is not None else None,
                "jobs": sorted(jobs, key=lambda x: -x[0])})
out.sort(key=lambda r: r["start"])
json.dump(out, sys.stdout, indent=None, separators=(",", ":"))
print()
for r in out:
    print(f"{r['start_utc']} {r['run']:40} {r['kind']:7} {len(r['jobs']):5} jobs {round(sum(x[0] * x[1] for x in r['jobs'])):7} slot-s  obs {r['observed']} wall {r['wall_s']} {r['where']}", file=sys.stderr)
