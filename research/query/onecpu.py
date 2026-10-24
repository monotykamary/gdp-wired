"""The 1-vCPU test jobs, each side's test times (bun test's [ms]): `python3 research/query/onecpu.py <run dir> [n]`. For
each test, over the jobs of each side: the median and the most, the n slowest by the most on either side, and any failure."""
import collections
import pathlib
import re
import statistics
import sys

d = pathlib.Path(sys.argv[1]); n = int(sys.argv[2]) if len(sys.argv) > 2 else 8
t = collections.defaultdict(lambda: collections.defaultdict(list)); fails = []
for f in sorted(d.glob("*.log")):
    side, suite = f.stem.split("-")[0], f.stem.split("-")[1]
    text = f.read_text()
    if "(fail)" in text or re.search(r"\b[1-9]\d* fail\b", text): fails.append(f.name)
    for m in re.finditer(r"\(pass\) (.*?) \[([\d.]+)(ms|s)\]", text):
        ms = float(m.group(2)) * (1000 if m.group(3) == "s" else 1)
        t[(suite, m.group(1))][side].append(ms)
print("failed jobs:", fails or "none")
rows = sorted(t.items(), key=lambda kv: -max(max(v) for v in kv[1].values()))[:n]
for (suite, name), v in rows:
    print(f"{suite} | {name[:70]} | " + " | ".join(f"{s}: n {len(x)}, median {statistics.median(x):.2f} ms, most {max(x):.2f} ms" for s, x in sorted(v.items())))
