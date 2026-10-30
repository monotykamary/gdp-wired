"""The functions on the stack in a bun CPU profile's samples past a time (seconds from the profile's start).
    python3 research/protocols/engine/pastwall.py <x.cpuprofile> <after_s> [top=25]"""
import json, sys
from collections import Counter
prof = json.load(open(sys.argv[1])); after = float(sys.argv[2]) * 1e6; top = int(sys.argv[3]) if len(sys.argv) > 3 else 25
nodes = {n['id']: n for n in prof['nodes']}; parent = {}
for n in prof['nodes']:
    for c in n.get('children', []): parent[c] = n['id']
def name(n): cf = n['callFrame']; return f"{cf['functionName'] or '(anon)'}@{cf['url'].split('/')[-1]}:{cf['lineNumber'] + 1}"
t, incl, self_ = 0, Counter(), Counter(); n_after = 0
for sid, dt in zip(prof['samples'], prof['timeDeltas']):
    t += dt
    if t < after: continue
    n_after += 1; seen = set(); i = sid; self_[name(nodes[i])] += 1
    while i is not None:
        k = name(nodes[i])
        if k not in seen: seen.add(k); incl[k] += 1
        i = parent.get(i)
print('samples past', sys.argv[2], 's:', n_after, 'of', len(prof['samples']), '; total', round(t / 1e6, 1), 's')
print('-- inclusive'); [print(f'{c:6d} {k}') for k, c in incl.most_common(top)]
print('-- self'); [print(f'{c:6d} {k}') for k, c in self_.most_common(10)]
