"""Who calls a function in a bun CPU profile: for each name given (a function name, matched as a prefix of
`name@file:line`), its self samples by the chain of its nearest callers (depth frames up).
    python3 research/protocols/ic3syn/profcallers.py <x.cpuprofile> <depth> <name>..."""
import sys
import json
from collections import Counter
prof = json.load(open(sys.argv[1])); depth = int(sys.argv[2]); names = sys.argv[3:]
nodes = {n['id']: n for n in prof['nodes']}; parent = {}
for n in prof['nodes']:
    for c in n.get('children', []): parent[c] = n['id']
def name(n): cf = n['callFrame']; return f"{cf['functionName'] or '(anon)'}@{cf['url'].split('/')[-1]}:{cf['lineNumber'] + 1}"
by = {x: Counter() for x in names}
for sid in prof['samples']:
    nm = name(nodes[sid])
    for x in names:
        if nm.startswith(x):
            chain, i = [], parent.get(sid)
            while i is not None and len(chain) < depth:
                chain.append(name(nodes[i])); i = parent.get(i)
            by[x][' < '.join(chain)] += 1
for x in names:
    print(f'-- {x}: {sum(by[x].values())} self samples')
    for c, k in by[x].most_common(12): print(f'{k:6d} {c}')
