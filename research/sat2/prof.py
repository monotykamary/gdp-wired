# The self and total time of a .cpuprofile's functions, the heaviest first: python3 prof.py <file> [n]
import json, sys, collections
p = json.load(open(sys.argv[1]))
nodes = {n['id']: n for n in p['nodes']}
dt = collections.Counter()
for sid, d in zip(p['samples'], p['timeDeltas']): dt[sid] += d
parent = {}
for n in p['nodes']:
    for c in n.get('children', []): parent[c] = n['id']
selfT = collections.Counter(); total = collections.Counter()
for nid, t in dt.items():
    f = nodes[nid]['callFrame']; key = f"{f['functionName'] or '(anon)'} {f['url'].split('/')[-1]}:{f['lineNumber']}"
    selfT[key] += t
    seen = set(); x = nid
    while x in nodes:
        f = nodes[x]['callFrame']; k = f"{f['functionName'] or '(anon)'} {f['url'].split('/')[-1]}:{f['lineNumber']}"
        if k not in seen: total[k] += t; seen.add(k)
        x = parent.get(x, -1)
n = int(sys.argv[2]) if len(sys.argv) > 2 else 25
print('self'); [print(f'{t/1000:9.0f} ms  {k}') for k, t in selfT.most_common(n)]
print('total'); [print(f'{t/1000:9.0f} ms  {k}') for k, t in total.most_common(n)]
