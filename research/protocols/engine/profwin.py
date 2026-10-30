"""The functions on the stack in a bun CPU profile's samples between two times (seconds from the profile's start).
    python3 research/protocols/engine/profwin.py <x.cpuprofile> <from_s> <to_s> [top=30]"""
import json, sys
from collections import Counter
prof = json.load(open(sys.argv[1])); lo = float(sys.argv[2]) * 1e6; hi = float(sys.argv[3]) * 1e6; top = int(sys.argv[4]) if len(sys.argv) > 4 else 30
nodes = {n['id']: n for n in prof['nodes']}; parent = {}
for n in prof['nodes']:
    for c in n.get('children', []): parent[c] = n['id']
def name(n): cf = n['callFrame']; return f"{cf['functionName'] or '(anon)'}@{cf['url'].split('/')[-1]}:{cf['lineNumber'] + 1}"
t, incl, self_, k = 0, Counter(), Counter(), 0
for sid, dt in zip(prof['samples'], prof['timeDeltas']):
    t += dt
    if t < lo or t > hi: continue
    k += 1; seen = set(); i = sid; self_[name(nodes[i])] += 1
    while i is not None:
        nm = name(nodes[i])
        if nm not in seen: seen.add(nm); incl[nm] += 1
        i = parent.get(i)
print(f'samples {sys.argv[2]}-{sys.argv[3]} s: {k} of {len(prof["samples"])}; total {round(t / 1e6, 1)} s')
print('-- inclusive'); [print(f'{c:6d} {x}') for x, c in incl.most_common(top)]
print('-- self'); [print(f'{c:6d} {x}') for x, c in self_.most_common(12)]
