"""Today's boat batches from the runners' logs: each `[boat] batch <id>` line (the id is the client's local start
time) with what followed it: the VMs asked for, created, resumed and found up, the wall time, where the jobs ran and
any fallback. Writes a TSV, one batch a row, sorted by start.

    python3 research/boat-starts/timeline.py <runs dir> [<runs dir> ...] > research/boat-starts/batches.tsv

Each row's source is the log's path relative to its runs dir's parent (`runs/...`), the batch id ties it to the run.
"""
import datetime, pathlib, re, sys

TZ = datetime.timezone(datetime.timedelta(hours=7))  # the client's local zone (+07), as the batch ids are written
rows = {}
for root in map(pathlib.Path, sys.argv[1:]):
    for f in sorted(root.rglob("*.log")):
        try:
            text = f.read_text(errors="replace")
        except Exception:
            continue
        if "[boat] batch " not in text:
            continue
        parts = re.split(r"^\[boat\] batch (\S+): ", text, flags=re.M)
        for k in range(1, len(parts), 2):
            bid, body = parts[k], parts[k + 1]
            r = {"batch": bid, "src": str(f.relative_to(root.parent)), "asked": "", "kind": "", "jobs": "", "vms": "", "created": "", "resumed": "", "up": "",
                 "wall_s": "", "where": "", "no_starts": "0", "fallback": ""}
            m = re.search(r"^\[boat\] (\d+) jobs on (\d+) (\w+) VM\(s\)(?: \+ (\d+) (\w+))?", body, re.M)
            if m:
                r.update(kind="run.py", jobs=m[1], asked=str(int(m[2]) + int(m[4] or 0)))
            ms = re.findall(r"^\[boat\] (\d+) calls of (\w+) on up to (\d+)", body, re.M)
            if ms:
                r.update(kind="runner", jobs=str(sum(int(x[0]) for x in ms)), asked="+".join(x[2] for x in ms))
            m = re.search(r"boat: (\d+) VMs \((\d+) created, (\d+) resumed, (\d+) already up\)", body)
            if m:
                r.update(vms=m[1], created=m[2], resumed=m[3], up=m[4])
            m = re.search(r"^(\d+) jobs, \d+ failed, ([\d.]+) s wall", body, re.M) or re.search(r"^done in ([\d.]+) s wall", body, re.M)
            if m:
                r["wall_s"] = m[m.lastindex]
            m = re.search(r"^\d+ jobs, \d+ failed, [\d.]+ s wall, [\d.]+ s of job time; (.*)$", body, re.M) or re.search(r"^(\d+ calls on .*)$", body, re.M)
            if m:
                r["where"] = m[1][:160]
            r["no_starts"] = str(len(re.findall(r"no (boat )?starts left", body)))
            m = re.search(r"fallback: ([^)]*)", body)
            if m:
                r["fallback"] = m[1][:160]
            rows.setdefault(bid, r)
cols = ["start_utc", "batch", "src", "kind", "jobs", "asked", "vms", "created", "resumed", "up", "wall_s", "no_starts", "where", "fallback"]
print("\t".join(cols))
for bid in sorted(rows):
    r = rows[bid]
    t = datetime.datetime.strptime(bid[:15], "%Y%m%d-%H%M%S").replace(tzinfo=TZ).astimezone(datetime.timezone.utc)
    r["start_utc"] = t.strftime("%Y-%m-%dT%H:%M:%SZ")
    print("\t".join(r.get(c, "").replace("\t", " ") for c in cols))
