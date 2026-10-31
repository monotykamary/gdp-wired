"""Every launch we made (one runner process: a batch to the pool, whichever backend ran it) with its start, end, source
and jobs, from what the runs left on disk: the bar's <dir>.meta.json (start and wall), every other run's
backends.json (its mtime the end, its wall_s back to the start), the lanes' worktrees too, and the boat day of
10-22 (mix.json). A job is [seconds, weight, type, where] as in mix.json (summary.tsv's seconds, a compare runner's
results.jsonl seconds; weight from <dir>.jobs.json's cpu and memory, TIP calls 2).

    python3 research/boat-starts/launches.py <main checkout> > launches.json      (a few seconds: it only reads files)
    python3 research/boat-starts/launches.py --gaps launches.json                    the gaps between batches
"""
import datetime, glob, json, math, os, pathlib, sys

iso = lambda s: datetime.datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp()


def weight(j):
    w = max(math.ceil(j.get("cpu", 2.0) / 2), math.ceil(j.get("memory", 4096) / 4096), 1)
    return w, ("large" if w > 2 else "default")


def jobs_of(d: pathlib.Path, spec_path: pathlib.Path | None, tip: bool):
    spec = {}
    if spec_path and spec_path.exists():
        try:
            spec = {j["name"]: j for j in json.loads(spec_path.read_text())}
        except Exception:
            pass
    out = []
    if (d / "summary.tsv").exists():
        for l in (d / "summary.tsv").read_text().splitlines():
            r = l.split("\t")
            if len(r) >= 3:
                with_ = weight(spec.get(r[0], {}))
                out.append([max(0.0, float(r[2])), *with_, r[3] if len(r) > 3 else "modal"])
    elif (d / "results.jsonl").exists():
        for l in (d / "results.jsonl").read_text().splitlines():
            try:
                r = json.loads(l)
            except Exception:
                continue
            out.append([max(0.0, float(r.get("seconds") or 0)), 2 if tip else 1, "default", "modal"])
    return out


def walk(root: pathlib.Path, suffix: str):
    """Files under root ending in suffix, skipping the bar's worktrees, node_modules and the per-job logs' dirs' depth."""
    for d, dirs, files in os.walk(root):
        dirs[:] = [x for x in dirs if x not in ("trees", "node_modules", ".git", ".lake", "olean", "bench")]
        for f in files:
            if f.endswith(suffix):
                yield os.path.join(d, f)


def gather(main: pathlib.Path):
    rows, seen = [], set()
    # the bar: one meta.json per launch
    for m in [*walk(main / "runs/bar/runs", ".meta.json"), *walk(main / "runs/bar/base", ".meta.json")]:
        mp = pathlib.Path(m)
        try:
            meta = json.loads(mp.read_text())
            t0 = iso(meta["started"])
        except Exception:
            continue
        d = mp.with_name(mp.name[: -len(".meta.json")])
        seen.add(str(d.resolve()))
        rel = str(mp.relative_to(main / "runs/bar"))
        track = "/".join(rel.split("/")[:2])  # runs/<bar run> or base/<sha>
        rows.append({"start": t0, "end": t0 + float(meta.get("wall_s") or 0), "src": "bar", "group": meta.get("group"), "track": "bar:" + track,
                     "name": rel[: -len(".meta.json")], "backend": meta.get("backend"),
                     "jobs": jobs_of(d, mp.with_name(d.name + ".jobs.json"), meta.get("group") == "tip")})
    # every other run.py launch (the main checkout's runs, archived lanes' runs, the live lanes' worktrees)
    roots = [main / "runs"] + [pathlib.Path(p) / "runs" for p in sorted(glob.glob(str(main.parent / (main.name + "-lane*"))))]
    for root in roots:
        for b in (b for b in walk(root, "backends.json") if b.endswith("/backends.json") and "/runs/bar/" not in b):
            bp = pathlib.Path(b)
            d = bp.parent
            if str(d.resolve()) in seen or "/runs/bar/" in str(bp):
                continue
            try:
                info = json.loads(bp.read_text())
            except Exception:
                continue
            end = bp.stat().st_mtime
            rel = str(d.relative_to(root.parent))
            lane = root.parent.name if root.parent != main else ("archive:" + rel.split("/")[2] if rel.startswith("runs/archive/") else "main:" + rel.split("/")[1])
            src = "suite" if "suite" in d.name else "lane"
            if info.get("backend") in ("boat", "auto"):
                continue  # (the boat day's runs come from mix.json)
            # (an archived lane's runs were copied: their mtimes are the copy's, so their times are unknown)
            rows.append({"start": end - float(info.get("wall_s") or 0), "end": end, "src": "archive" if lane.startswith("archive:") else src, "group": None, "track": lane, "name": rel,
                         "backend": info.get("backend"), "jobs": jobs_of(d, d.parent / (d.name + "-jobs.json"), False)})
    # the boat day (10-22 to 10-23): its batches with their measured jobs
    mix = main / "research/boat-starts/mix.json"
    if mix.exists():
        seenb = set()
        for b in json.loads(mix.read_text()):
            key = b.get("batch") or b["run"]
            if key in seenb:
                continue
            seenb.add(key)
            rows.append({"start": b["start"], "end": b["start"] + float(b["wall_s"] or 0), "src": "boatday", "group": b["kind"], "track": "boatday:" + b["run"].split("/")[1],
                         "name": b["run"], "backend": b["backend"], "jobs": b["jobs"]})
    rows.sort(key=lambda r: r["start"])
    return rows


def q(xs, p):
    xs = sorted(xs)
    return round(xs[min(len(xs) - 1, int(p * len(xs)))]) if xs else None


def gaps(rows, label):
    """For each launch's end: the time to the next launch's start (any track; 0 when another is already running and
    still has work), and to its own track's next one."""
    ev = sorted((r["start"], r["end"], r["track"]) for r in rows)
    anyg, own, overl = [], [], 0
    starts = [s for s, _, _ in ev]
    import bisect
    for s, e, tr in ev:
        k = bisect.bisect_left(starts, e)
        if any(s2 < e < e2 for s2, e2, _ in ev[max(0, k - 400):k] if (s2, e2) != (s, e)):
            overl += 1
        if k < len(ev):
            anyg.append(ev[k][0] - e)
        nxt = next((s2 for s2, _, t2 in ev[k:] if t2 == tr), None)
        if nxt is not None:
            own.append(nxt - e)
    w = (60, 120, 300, 600, 900, 1800)
    out = [f"{label}: {len(ev)} launches; at {overl} of their ends another launch was running"]
    for name, g in (("next launch, any track", anyg), ("next launch, same track", own)):
        g = [x for x in g if x < 6 * 3600]  # (a gap of hours is a pause in the work, not a gap between batches)
        out.append(f"  {name:24} {len(g):5} gaps  p10 {q(g, .1)}  p25 {q(g, .25)}  median {q(g, .5)}  p75 {q(g, .75)}  p90 {q(g, .9)} s;  covered by idle "
                   + "  ".join(f"{x}s {round(100 * sum(1 for y in g if y <= x) / max(1, len(g)))}%" for x in w))
    return out


if __name__ == "__main__":
    if sys.argv[1] == "--gaps":
        rows = json.load(open(sys.argv[2]))
        since = iso(sys.argv[3]) if len(sys.argv) > 3 else 0
        sized = rows
        rows = [r for r in rows if r["start"] >= since and r["src"] != "archive"]
        print("\n".join(gaps(rows, "all")))
        for src in ("bar", "suite", "lane", "boatday"):  # (the bar's suite groups are under bar)
            sel = [r for r in rows if r["src"] == src]
            if sel:
                print("\n".join(gaps(sel, src)))
        bars = [r for r in rows if r["src"] == "bar"]
        for g in sorted({r["group"] for r in bars if r["group"]}):
            print("\n".join(gaps([r for r in bars if r["group"] == g], f"bar group {g}")[1:2]).replace("next launch, any track", f"{g:12} any"))
        # the launches' sizes: how many are tiny (the share a warm VM or Modal could take without a start)
        js = [len(r["jobs"]) for r in sized if r["jobs"]]
        sm = [sum(j[0] * j[1] for j in r["jobs"]) / 60 for r in sized if r["jobs"]]
        print(f"sizes: {len(js)} launches with jobs; jobs median {q(js, .5)} p90 {q(js, .9)}; <=4 jobs {sum(1 for x in js if x <= 4)};"
              f" slot-min median {q(sm, .5)} p90 {q(sm, .9)}; <10 slot-min {sum(1 for x in sm if x < 10)}")
        days = {}
        for r in rows:
            days.setdefault(datetime.datetime.fromtimestamp(r["start"], datetime.timezone.utc).strftime("%m-%d"), []).append(r)
        for d, rs in sorted(days.items()):
            print(f"  {d}: {len(rs):4} launches, {sum(len(r['jobs']) for r in rs):6} jobs, {round(sum(j[0] * j[1] for r in rs for j in r['jobs']) / 3600, 1):6} slot-h  "
                  + ", ".join(f"{s} {sum(1 for r in rs if r['src'] == s)}" for s in ("bar", "suite", "lane", "boatday")))
    else:
        json.dump(gather(pathlib.Path(sys.argv[1]).resolve()), sys.stdout)
