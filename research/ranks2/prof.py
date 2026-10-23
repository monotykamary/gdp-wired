import json,collections,sys,glob
p=json.load(open(glob.glob(sys.argv[1]+'/*.cpuprofile')[0]))
nodes={n['id']:n for n in p['nodes']}
self=collections.Counter()
for s,d in zip(p['samples'],p['timeDeltas']): self[s]+=d
parent={}
for n in p['nodes']:
    for c in n.get('children',[]): parent[c]=n['id']
f=collections.Counter(); inc=collections.Counter()
for i,t in self.items():
    cf=nodes[i]['callFrame']; f[(cf['functionName'],cf['url'].split('/')[-1],cf['lineNumber'])]+=t
    seen=set(); j=i
    while j is not None:
        cf=nodes[j]['callFrame']; key=(cf['functionName'],cf['url'].split('/')[-1],cf['lineNumber'])
        if key not in seen: inc[key]+=t; seen.add(key)
        j=parent.get(j)
for k,t in f.most_common(12): print('self',round(t/1000),k)
for k,t in inc.most_common(int(sys.argv[2]) if len(sys.argv)>2 else 25): print('inc',round(t/1000),k)
