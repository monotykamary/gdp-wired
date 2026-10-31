"""The top functions of a V8/JSC .cpuprofile by self time (and by total time through them), for smallbench.ts's runs.
    python3 research/protocols/engine/cpuprof.py <file.cpuprofile> [n]"""
import collections
import json
import sys

prof = json.load(open(sys.argv[1]))
n = int(sys.argv[2]) if len(sys.argv) > 2 else 30
nodes = {x["id"]: x for x in prof["nodes"]}
dt = collections.Counter()
for s, d in zip(prof["samples"], prof["timeDeltas"]):
    dt[s] += d
name = lambda x: f'{x["callFrame"]["functionName"] or "(anon)"} {x["callFrame"]["url"].split("/")[-1]}:{x["callFrame"]["lineNumber"] + 1}'
self_t = collections.Counter()
for i, t in dt.items():
    self_t[name(nodes[i])] += t
parent = {c: x["id"] for x in prof["nodes"] for c in x.get("children", [])}
total = collections.Counter()
for i, t in dt.items():
    seen, j = set(), i
    while j is not None:
        k = name(nodes[j])
        if k not in seen:
            total[k] += t
            seen.add(k)
        j = parent.get(j)
all_t = sum(dt.values()) or 1
print(f"total {all_t / 1000:.0f} ms")
print("self:")
for k, t in self_t.most_common(n):
    print(f"  {t / 1000:9.0f} ms {100 * t / all_t:5.1f}%  {k}")
print("total:")
for k, t in total.most_common(n):
    print(f"  {t / 1000:9.0f} ms {100 * t / all_t:5.1f}%  {k}")
