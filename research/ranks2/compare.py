# Two runs' answers side by side: python3 research/ranks2/compare.py <base dir> <mine dir> [--others <dirs,...>]
import json, sys
def rows(d):
    out = {}
    for l in open(d + '/results.jsonl'):
        r = json.loads(l); out[(r['tool'], r['task'])] = r
    return out
base, mine = rows(sys.argv[1]), rows(sys.argv[2])
others = {}
if '--others' in sys.argv:
    for d in sys.argv[sys.argv.index('--others') + 1].split(','): others.update(rows(d))
tools = sorted({t for t, _ in mine})
for tool in tools:
    for name, rs in (('base', base), ('mine', mine)):
        ans = [r['answer'] for (t, _), r in rs.items() if t == tool]
        print(tool, name, 'terminates', ans.count('terminates'), 'nonterminating', ans.count('nonterminating'), 'of', len(ans))
    tasks = sorted({k for t, k in mine if t == tool})
    gained = [k for k in tasks if mine[(tool, k)]['answer'] in ('terminates', 'nonterminating') and base.get((tool, k), {}).get('answer') != mine[(tool, k)]['answer']]
    lost = [k for k in tasks if base.get((tool, k), {}).get('answer') in ('terminates', 'nonterminating') and mine[(tool, k)]['answer'] != base[(tool, k)]['answer']]
    print(f'  {tool}: gained {len(gained)}, lost {len(lost)}')
    for k in gained: print('   +', mine[(tool, k)]['answer'], mine[(tool, k)]['seconds'], k)
    for k in lost: print('   -', base[(tool, k)]['answer'], base[(tool, k)]['seconds'], '->', mine[(tool, k)]['answer'], mine[(tool, k)]['seconds'], k)
    # contradictions with any other tool's answer
    for k in tasks:
        a = mine[(tool, k)]['answer']
        if a not in ('terminates', 'nonterminating'): continue
        opp = 'nonterminating' if a == 'terminates' else 'terminates'
        bad = [t for (t, kk), r in list(others.items()) + list(base.items()) + list(mine.items()) if kk == k and r['answer'] == opp]
        if bad: print('   CONTRADICTION', tool, k, a, bad)
