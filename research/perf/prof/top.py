# The top self-time functions of a bun CPU profile: `python3 top.py <file.cpuprofile> [n]`.
import collections, json, sys
p = json.load(open(sys.argv[1]))
nodes = {n['id']: n for n in p['nodes']}
self_t, total_t = collections.Counter(), collections.Counter()
parent = {}
for n in p['nodes']:
    for c in n.get('children', []): parent[c] = n['id']
for sid, d in zip(p['samples'], p.get('timeDeltas', [])):
    cf = nodes[sid]['callFrame']
    self_t[(cf['functionName'] or '(anon)', cf['url'].split('/')[-1], cf['lineNumber'] + 1)] += d
    seen, i = set(), sid
    while i is not None:
        f = nodes[i]['callFrame']; k = (f['functionName'] or '(anon)', f['url'].split('/')[-1], f['lineNumber'] + 1)
        if k not in seen: total_t[k] += d; seen.add(k)
        i = parent.get(i)
tot = sum(self_t.values()) or 1
n = int(sys.argv[2]) if len(sys.argv) > 2 else 30
print('self:')
for (fn, url, line), t in self_t.most_common(n): print(f"{t/1000:9.0f} ms {100*t/tot:5.1f}%  {fn}  {url}:{line}")
print('total:')
for (fn, url, line), t in total_t.most_common(n): print(f"{t/1000:9.0f} ms {100*t/tot:5.1f}%  {fn}  {url}:{line}")
