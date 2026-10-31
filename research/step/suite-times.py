"""Suite job times side by side: `python3 research/step/suite-times.py <run dir> <run dir> [...]` (each a supercomputer/run.py
output: summary.tsv with name, exit code, seconds, backend). Prints each run's failures and total job seconds over the
jobs every run has, then the jobs whose time moved most between the first two."""
import pathlib
import sys

runs = []
for d in sys.argv[1:]:
    rows = {}
    for line in (pathlib.Path(d) / "summary.tsv").read_text().splitlines():
        parts = line.split("\t")
        if len(parts) >= 3:
            rows[parts[0]] = (int(parts[1]), float(parts[2]), parts[3] if len(parts) > 3 else "")
    runs.append((d, rows))
common = set.intersection(*[set(r) for _, r in runs])
for d, rows in runs:
    failed = sorted(n for n, (c, _, _) in rows.items() if c != 0)
    backends = sorted({b for _, _, b in rows.values()})
    print(f"{d}: {len(rows)} jobs, failed {failed}, backends {backends}, job seconds over the {len(common)} common: {round(sum(rows[n][1] for n in common), 1)} (all: {round(sum(x[1] for x in rows.values()), 1)})")
if len(runs) >= 2:
    a, b = runs[0][1], runs[1][1]
    moved = sorted(common, key=lambda n: b[n][1] - a[n][1])
    print("most slower:", [(n, a[n][1], b[n][1]) for n in moved[-10:][::-1]])
    print("most faster:", [(n, a[n][1], b[n][1]) for n in moved[:6]])
