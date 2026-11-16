"""No-search SDL transport diagnostic; only retained Lean proof terms are used."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,time
ROOT=Path.cwd(); OUT=Path(os.environ['SUPERCOMPUTER_OUTPUT_DIR']); RET=ROOT/'sdl-retained'; LEAN=RET/'lean'
RE=OUT/'rechecked';RE.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected='95b20356ad9606abd1e4ea2489f8473c72b50451424b3ebdd2f13443528d5e2c'
if sha(LEAN/'Proofs.lean')!=expected: raise RuntimeError('wrong retained SDL Proofs')
family=json.loads((RET/'FAMILY-CHECK.json').read_text())
if family['capsuleSHA256']!='e123183e89e3d5e0378d9aaf3e4d00a5f7e55b3584821faf0c6fa2d739e82958': raise RuntimeError('wrong SDL capsule')
env=dict(os.environ);env['PATH']=str(ROOT/'scripts/lean-gate')+':'+env['PATH']
env['LEAN_PATH']=':'.join(map(str,[RE,ROOT/'research/bapa',LEAN/'.lake/build/lib/lean',LEAN]));env['LEAN_NUM_THREADS']='1'
records=[]
meta={'schema':'bapa-sdl-transport/v1','sourceSHA256':expected,'capsuleSHA256':family['capsuleSHA256'],'newProofSearches':0,'sourceBridge':'PENDING','accepted':False}
def lean(src,name):
    if src.resolve() != (OUT/(name+'.lean')).resolve(): shutil.copyfile(src,OUT/(name+'.lean'))
    start=time.monotonic();print('LEAN_START',name,flush=True)
    with (OUT/(name+'.log')).open('wb') as log:
        p=subprocess.run(['timeout','--signal=TERM','--kill-after=10s','600s','lean','-o',str(RE/(name+'.olean')),str(src)],cwd=src.parent,env=env,stdout=log,stderr=subprocess.STDOUT)
    records.append({'module':name,'sourceSHA256':sha(src),'exitCode':p.returncode,'seconds':round(time.monotonic()-start,3)})
    (OUT/'LEAN-RECEIPTS.json').write_text(json.dumps(records,indent=2)+'\n')
    print('LEAN_DONE',name,p.returncode,flush=True)
    if p.returncode: raise RuntimeError(name+' failed')
try:
    for name in ['RadixKeySyntax','RadixBinderExpansion','RadixCertificateTable','RadixTupleSyntax','CertificateBoundErasure','BoundErasureReplay','CertificateBooleanCleanup','RadixEqualityTree','RadixCertificateTransport']:
        lean(ROOT/'research/bapa'/(name+'.lean'),name)
    lean(LEAN/'Proofs.lean','Proofs')
    lean(OUT/'SdlSourceDefs.lean','SdlSourceDefs')
    lean(ROOT/'research/bapa/SimpleDecentralizedLockTransport.lean','SimpleDecentralizedLockTransport')
    lean(OUT/'SdlCandidateData.lean','SdlCandidateData')
    if (OUT/'Checks.lean').exists(): lean(OUT/'Checks.lean','Checks')
    if (OUT/'SumChecks.lean').exists(): lean(OUT/'SumChecks.lean','SumChecks')
    lean(OUT/'SdlTargetData.lean','SdlTargetData')
    lean(ROOT/'research/bapa/SdlExactTransport.lean','SdlExactTransport')
    lean(ROOT/'research/bapa/SdlSourceBridge.lean','SdlSourceBridge')
    meta['diagnostic']=(OUT/'SDL-DIAGNOSTIC.txt').read_text()
    subprocess.run(['bun',str(ROOT/'research/bapa/sdl-source-verify.ts'),str(OUT),str(OUT),str(OUT/'SOURCE-CHECKED.json')],cwd=ROOT,check=True)
    meta.update(status='SOURCE_CHECKED',sourceBridge='CHECKED',accepted=True)
except Exception as e:
    meta.update(status='CHECK_FAILED',error=repr(e));raise
finally:
    meta['leanReceipts']=records;(OUT/'REPLAY-METADATA.json').write_text(json.dumps(meta,indent=2)+'\n')
