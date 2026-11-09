"""Independent source receipts and exhaustive finite sanity test of MLDR overlap arithmetic. Boat only."""
import urllib.request, hashlib, base64, json, itertools
sources={
'mypyvy-paxos_epr.pyv':'https://raw.githubusercontent.com/wilcoxjay/mypyvy/12a8f5434a25587c56814d090b6ab7fa95851e71/examples/pd/paxos_epr.pyv',
'endive-paxos_epr.tla':'https://raw.githubusercontent.com/will62794/endive/8b6f2abd1988eeb308f965813635e9871f253e2d/benchmarks/paxos_epr.tla',
'endive-MongoLoglessDynamicRaft.tla':'https://raw.githubusercontent.com/will62794/endive/8b6f2abd1988eeb308f965813635e9871f253e2d/benchmarks/MongoLoglessDynamicRaft.tla'}
for name,url in sources.items():
    try:
        data=urllib.request.urlopen(url,timeout=45).read()
        print(json.dumps({'name':name,'url':url,'sha256':hashlib.sha256(data).hexdigest(),'base64':base64.b64encode(data).decode()}),flush=True)
    except Exception as e: print(json.dumps({'name':name,'url':url,'error':repr(e)}),flush=True)
tests=0; mismatches=[]
for n in range(1,7):
    subsets=[frozenset(i for i in range(n) if mask>>i&1) for mask in range(1<<n)]
    majority={x:[q for q in subsets if q<=x and 2*len(q)>len(x)] for x in subsets if x}
    for x in majority:
        for y in majority:
            actual=all(q&r for q in majority[x] for r in majority[y])
            dx,dy,m=len(x-y),len(y-x),len(x&y)
            arithmetic=max(0,len(x)//2+1-dx)+max(0,len(y)//2+1-dy)>m
            tests+=1
            if bool(actual)!=arithmetic: mismatches.append([n,sorted(x),sorted(y)])
print(json.dumps({'overlap_nonempty_sets_sizes':'1..6','ordered_pairs':tests,'mismatches':mismatches}),flush=True)
