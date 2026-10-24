# A bun CPU profile summarized as JSON: self and total ms by function (name, file, line) and self ms by file, the top
# entries; `python3 top.py <file.cpuprofile> [n]`. Research tooling.
import collections, json, sys
p = json.load(open(sys.argv[1]))
n = int(sys.argv[2]) if len(sys.argv) > 2 else 200
nodes = {x['id']: x for x in p['nodes']}
parent = {}
for x in p['nodes']:
    for c in x.get('children', []): parent[c] = x['id']
import re
short = lambda u: re.sub(r'^.*?/gdp-wired[^/]*/(\.base/)?', '', u)
key = lambda cf: f"{cf['functionName'] or '(anon)'} {short(cf['url'])}:{cf['lineNumber'] + 1}"
self_t, total_t, files, lines = collections.Counter(), collections.Counter(), collections.Counter(), collections.Counter()
node_self = collections.Counter()
memo = {}
def chain(i):
    if i in memo: return memo[i]
    out, j = set(), i
    while j is not None:
        out.add(key(nodes[j]['callFrame'])); j = parent.get(j)
    memo[i] = out
    return out
for sid, d in zip(p['samples'], p.get('timeDeltas', [])):
    cf = nodes[sid]['callFrame']
    self_t[key(cf)] += d
    node_self[sid] += d
    files[short(cf['url']) or '(native)'] += d
    for k in chain(sid): total_t[k] += d
for i, t in node_self.items():
    x = nodes[i]
    pt = x.get('positionTicks') or []
    tot = sum(y['ticks'] for y in pt)
    f = short(x['callFrame']['url']) or '(native)'
    for y in pt: lines[f"{f}:{y['line']}"] += t * y['ticks'] / tot
r = lambda c: {k: round(v / 1000, 1) for k, v in c.most_common(n)}
print(json.dumps({'ms': round(sum(self_t.values()) / 1000, 1), 'self': r(self_t), 'total': r(total_t), 'files': r(files), 'lines': r(lines)}))
