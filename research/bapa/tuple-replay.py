"""Retained packed-key replay. No prover/search API is called."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,time
ROOT=Path.cwd(); OUT=Path(os.environ['SUPERCOMPUTER_OUTPUT_DIR'])
RE=OUT/'rechecked';RE.mkdir(exist_ok=True)
retained=ROOT/'radix-retained'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=dict(os.environ)
env['PATH']=str(ROOT/'scripts/lean-gate')+':'+env['PATH']
env['LEAN_PATH']=':'.join(map(str,[RE,ROOT/'research/bapa',retained/'.lake/build/lib/lean',retained]))
env['LEAN_NUM_THREADS']='1'
records=[]
prior=ROOT/'radix-prior'
prior_receipts=json.loads((prior/'LEAN-RECEIPTS.json').read_text()) if (prior/'LEAN-RECEIPTS.json').is_file() else []
meta={'schema':'bapa-tuple-replay/v1','protocol':'sharded_kv','retainedIdentity':'2d81751966afd9edebcaf04f5acdeadbe3ec75cccee60e0e0df633d08fdbda73','sourceSHA256':sha(retained/'Proofs.lean'),'newProofSearches':0,'route':'typed-tuple-certificate-translator','sourceBridge':{'status':'PENDING','productionAcceptance':False}}
helpers=['RadixKeySyntax','RadixBinderExpansion','RadixCertificateTable','RadixTupleSyntax','CertificateBoundErasure','BoundErasureReplay','CertificateBooleanCleanup','RadixEqualityTree','RadixCertificateTransport']
def lean(src,name,seconds=600):
    text=Path(src).read_text();(OUT/(name+'.lean')).write_text(text)
    cached=next((r for r in prior_receipts if r['module']==name and r['exitCode']==0 and r['sourceSHA256']==sha(Path(src))),None)
    artifact=prior/'rechecked'/(name+'.olean')
    if cached and artifact.is_file():
        shutil.copy2(artifact,RE/(name+'.olean'))
        records.append({**cached,'reusedFrom':'radix-prior','oleanSHA256':sha(artifact)})
        (OUT/'LEAN-RECEIPTS.json').write_text(json.dumps(records,indent=2)+'\n')
        print('LEAN_REUSED',name,flush=True);return
    print('LEAN_START',name,flush=True);start=time.monotonic()
    with (OUT/(name+'.log')).open('wb') as log:
        p=subprocess.run(['timeout','--signal=TERM','--kill-after=10s',str(seconds)+'s','lean','-o',str(RE/(name+'.olean')),str(src)],cwd=Path(src).parent,env=env,stdout=log,stderr=subprocess.STDOUT)
    records.append({'module':name,'sourceSHA256':sha(Path(src)),'exitCode':p.returncode,'seconds':round(time.monotonic()-start,3)})
    (OUT/'LEAN-RECEIPTS.json').write_text(json.dumps(records,indent=2)+'\n')
    print('LEAN_DONE',name,p.returncode,flush=True)
    if p.returncode:raise RuntimeError(name+' failed; see its .log')
try:
    failed_helpers=[]
    for name in helpers:
        try:lean(ROOT/'research/bapa'/(name+'.lean'),name,240)
        except RuntimeError:failed_helpers.append(name)
    if failed_helpers:raise RuntimeError('helpers failed: '+', '.join(failed_helpers))
    lean(retained/'Proofs.lean','Proofs',900)
    lean(ROOT/'research/bapa/ShardedKvTupleTransport.lean','ShardedKvTupleTransport',900)
    lean(OUT/'Checks.lean','Checks',900)
    lines=[parts for line in (OUT/'checks.tsv').read_text().splitlines()[1:]
           if len(parts:=line.split('\t'))==3 and parts[1] in {'init','step','all'}]
    family=next(r[2]=='true' for r in lines if r[:2]==['family','all'])
    meta.update(status='CHECKED_ACCEPTED' if family else 'CHECKED_REJECTED',familyAccepted=family,checkedParts=sum(r[1] in {'init','step'} for r in lines))
except Exception as e:
    error=OUT/'TRANSLATION-ERROR.txt'
    meta.update(status='TRANSLATION_REFUSED' if error.is_file() else 'CHECK_FAILED',error=repr(e))
    if error.is_file():meta['translationError']=error.read_text()
    raise
finally:
    meta['leanReceipts']=records
    (OUT/'REPLAY-METADATA.json').write_text(json.dumps(meta,indent=2)+'\n')
