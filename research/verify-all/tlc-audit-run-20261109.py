"""Fresh TLC + unchanged check.ts; only writes into unique runs/verify-all workdir.
Run on boat: python3 research/verify-all/tlc-audit-run-20261109.py ID [MS]
Full command receipts, hashes and compressed source/log bundle are printed for retention.
"""
import base64, gzip, hashlib, json, os, pathlib, re, shutil, subprocess, sys, tarfile, time, traceback
ID = sys.argv[1]
MS = int(sys.argv[2]) if len(sys.argv)>2 else 120000
ROOT = pathlib.Path.cwd()
OUT = ROOT / 'runs/verify-all' / ('tlc-evidence-' + ID + '-' + str(os.getpid()))
OUT.mkdir(parents=True)
W = OUT / 'benchmarks'
CFG = OUT / 'cfg'; CFG.mkdir()
records=[]
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def run(args, name, cwd=ROOT, seconds=90):
    start=time.time()
    # GNU timeout targets only the child process/group it creates, never other jobs.
    cmd=['timeout','-s','KILL',str(seconds),*map(str,args)]
    p=subprocess.run(cmd,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (OUT/(name+'.log')).write_bytes(p.stdout)
    records.append({'name':name,'cmd':cmd,'cwd':str(cwd),'exit':p.returncode,'seconds':time.time()-start})
    print('RECEIPT '+json.dumps(records[-1]),flush=True)
    return p.returncode,p.stdout.decode(errors='replace')
def obj(s):
    for l in s.splitlines():
        if l.startswith('{'):
            try:return json.loads(l)
            except ValueError: pass
result={'id':ID,'ms':MS,'endive':'8b6f2abd1988eeb308f965813635e9871f253e2d','records':records}
try:
    if hasattr(os,'sched_getaffinity'):
        affinity=sorted(os.sched_getaffinity(0)); os.sched_setaffinity(0,affinity)
        result['affinity']=affinity
    result['hashes']={str(p):sha(p) for p in [pathlib.Path('research/protocols/ic3syn')/f for f in ['models.ts','common.ts','check.ts','tlc.py','README.md']]}
    run(['bun','--version'],'bun-version')
    run(['java','-version'],'java-version')
    rc,text=run(['bun','research/protocols/ic3syn/check.ts','--only',ID,'--cfg',CFG],'config')
    meta=obj(text); result['meta']=meta
    if not meta or not meta.get('module'): raise RuntimeError('No TLC module from unchanged harness')
    rc,_=run(['curl','-fLsS','--retry','5','-o',OUT/'endive.tgz','https://codeload.github.com/will62794/endive/tar.gz/'+result['endive']],'fetch-endive',seconds=180)
    if rc: raise RuntimeError('Endive fetch failed')
    with tarfile.open(OUT/'endive.tgz') as t:
        prefix='endive-'+result['endive']+'/benchmarks/'
        for m in t.getmembers():
            if m.isfile() and m.name.startswith(prefix):
                dst=W/m.name[len(prefix):]; dst.parent.mkdir(parents=True,exist_ok=True); dst.write_bytes(t.extractfile(m).read())
    original=W/(meta['module']+'.tla')
    result['original_spec_sha256']=sha(original) if original.exists() else None
    if original.exists(): (OUT/'original.tla').write_bytes(original.read_bytes())
    for i,fix in enumerate(meta['fix']):
        rc,_=run(['bash','-c',fix],'fix-'+str(i),cwd=W)
        if rc: raise RuntimeError('source preparation failed')
    result['used_spec_sha256']=sha(W/(meta['module']+'.tla'))
    (OUT/'used.tla').write_bytes((W/(meta['module']+'.tla')).read_bytes())
    result['cfg_sha256']=sha(CFG/(ID+'.cfg'))
    rc,_=run(['curl','-fLsS','--retry','5','-o',OUT/'tla2tools.jar','https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar'],'fetch-tlc',seconds=180)
    if rc: raise RuntimeError('TLC fetch failed')
    result['jar_sha256']=sha(OUT/'tla2tools.jar')
    rc,text=run(['java','-Xmx10g','-XX:+UseParallelGC','-cp',OUT/'tla2tools.jar','tlc2.TLC','-deadlock','-workers','2','-metadir',OUT/'meta','-dump','dot',OUT/'graph','-config',CFG/(ID+'.cfg'),meta['module']+'.tla'],'tlc',cwd=W,seconds=600)
    m=re.findall(r'([\d,]+) distinct states found',text); d=re.search(r'depth of the complete state graph search is (\d+)',text)
    result['tlc']={'exit':rc,'states':int(m[-1].replace(',','')) if m else None,'depth':int(d.group(1)) if d else None,'complete':'Model checking completed. No error has been found.' in text,'violated':bool(re.search(r'Invariant \S+ is violated',text))}
    graph=OUT/'graph.dot'
    if graph.exists():
        pairs=set()
        with graph.open() as f:
            for line in f:
                e=re.match(r'\s*(-?\d+) -> (-?\d+)',line)
                if e and e[1]!=e[2]: pairs.add((e[1],e[2]))
        result['tlc'].update(edges=len(pairs),graph_sha256=sha(graph))
    for broken in ([False] if "--skip-broken" in sys.argv else [False,True]):
        args=['bun','research/protocols/ic3syn/check.ts','--only',ID,'--ms',str(MS)]
        if broken: args.append("--broken")
        elif "--states-only" not in sys.argv: args.append("--edges")
        rc,text=run(args,'broken' if broken else 'port',seconds=MS//1000+60)
        result['broken' if broken else 'port']={'exit':rc,'result':obj(text)}
except Exception:
    result['error']=traceback.format_exc()
finally:
    (OUT/'result.json').write_text(json.dumps(result,indent=2))
    print('RESULT '+json.dumps(result),flush=True)
    # Compact full receipts, logs, config and pre/post source; graph's hash above (not shipped).
    bundle={str(p.relative_to(OUT)):base64.b64encode(p.read_bytes()).decode() for p in OUT.rglob('*') if p.is_file() and (p.suffix in ['.log','.json','.cfg'] or p.name in ['original.tla','used.tla'])}
    packed=gzip.compress(json.dumps(bundle).encode())
    print('EVIDENCE_GZIP_BASE64 '+base64.b64encode(packed).decode(),flush=True)
