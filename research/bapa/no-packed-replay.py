"""No-search bound-erasure replay; every observed Boolean gets a Lean receipt."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys,tarfile,time
ROOT=Path.cwd();OUT=Path(os.environ['SUPERCOMPUTER_OUTPUT_DIR']);RE=OUT/'rechecked';RE.mkdir(exist_ok=True)
protocol=sys.argv[1]
assert protocol in {'client_server_db_ae','mldr'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if protocol=='client_server_db_ae':
    retained=ROOT/'transport-client';source=retained/'Proofs.lean';module='Proofs';target='ClientServerDbAeTransport'
    capsule='e76ed2d24da036b98a98ea1edf509abe741499a2647c88f647c4d4f235cc87f0'
    if '--cleanup' in sys.argv:target='ClientServerDbAeCleanup'
    if '--sized' in sys.argv:target='ClientServerDbAeSizedTransport'
else:
    archive=ROOT/'transport-mldr/PROJECT.tar.gz';capsule=sha(archive)
    assert capsule=='23f8a704f3b1f9e9cf3ede0ac9e8a69777187b75521e06dbadd6b68eff4825af'
    retained=OUT/'retained-project';retained.mkdir(exist_ok=True)
    with tarfile.open(archive) as t:
        assert all(m.isfile() and not Path(m.name).is_absolute() and '..' not in Path(m.name).parts for m in t.getmembers())
        t.extractall(retained)
    spec=json.loads((ROOT/'transport-mldr/RUN-SPEC.json').read_text())
    for f in spec['projectManifest']:assert sha(retained/f['path'])==f['sha256'],f['path']
    source=retained/'Shared.lean';module='Shared';target='MLDRBoundErasureTransport'
source_text=source.read_text()
radix={p:source_text.count(p) for p in ['.mul 64 ','.mul 4096 ']}
triage={'protocol':protocol,'source':source.name,'sourceSHA256':sha(source),'radixOccurrences':radix,'tupleOccurrences':source_text.count('.tup '),'cellTupleOccurrences':source_text.count('.cellT '),'proofSearches':0,'leanExecutions':0,'requiresRekeying':any(radix.values())}
(OUT/'TRIAGE.json').write_text(json.dumps(triage,indent=2)+'\n')
print('TRIAGE',json.dumps(triage),flush=True)
if triage['requiresRekeying']:
    (OUT/'REPLAY-METADATA.json').write_text(json.dumps({'status':'NEEDS_REKEYING','triage':triage,'sourceBridge':{'status':'PENDING','productionAcceptance':False}},indent=2)+'\n')
    sys.exit(0)
meta={'schema':'bapa-no-packed-replay/v1','protocol':protocol,'retainedIdentity':capsule,'sourceSHA256':sha(source),'radixOccurrences':radix,'route':('bound-substitution-symbolic-size' if '--sized' in sys.argv else 'bound-erasure-existing-tuple-or-unary-keys'),'newProofSearches':0,'retainedTreeReplay':True,'booleanClosureCleanup':('--cleanup' in sys.argv),'sourceBridge':{'status':'PENDING','obligations':['show unbounded source parameters/admission correspond to translated machine','show typed source maps and public goal correspond to retained tuple/unary machine','include ghost/witness projection where present'],'productionAcceptance':False}}
(OUT/'REPLAY-METADATA.json').write_text(json.dumps(meta,indent=2)+'\n')
env=dict(os.environ);env['PATH']=str(ROOT/'scripts/lean-gate')+':'+env['PATH'];env['LEAN_PATH']=':'.join(map(str,[RE,ROOT/'research/bapa',retained/'.lake/build/lib/lean',retained]));env['LEAN_NUM_THREADS']='1'
records=[]
prior=ROOT/f'transport-prior-{protocol}'
prior_records=json.loads((prior/'LEAN-RECEIPTS.json').read_text()) if (prior/'LEAN-RECEIPTS.json').is_file() else []
def lean(src,name,seconds=600):
    old=next((r for r in prior_records if r['module']==name and r['exitCode']==0 and r['sourceSHA256']==sha(Path(src))),None)
    prior_olean=prior/'rechecked'/f'{name}.olean'
    if old and prior_olean.is_file():
        shutil.copy2(prior_olean,RE/prior_olean.name)
        records.append(dict(old,reusedFrom=str(prior),oleanSHA256=sha(prior_olean)))
        (OUT/'LEAN-RECEIPTS.json').write_text(json.dumps(records,indent=2)+'\n')
        if name==target:
            for artifact in ['checks.tsv','Checks.lean']:
                if (prior/artifact).is_file():shutil.copy2(prior/artifact,OUT/artifact)
        print('LEAN_REUSED_CHECKED',name,flush=True)
        return
    log=OUT/(name+'.log');start=time.monotonic();print('LEAN_START',name,flush=True)
    with log.open('wb') as f:
        p=subprocess.run(['timeout','--signal=TERM','--kill-after=10s',str(seconds)+'s','lean','-o',str(RE/(name+'.olean')),str(src)],cwd=Path(src).parent,env=env,stdout=f,stderr=subprocess.STDOUT)
    records.append({'module':name,'exitCode':p.returncode,'seconds':round(time.monotonic()-start,3),'sourceSHA256':sha(Path(src))})
    (OUT/'LEAN-RECEIPTS.json').write_text(json.dumps(records,indent=2)+'\n')
    print('LEAN_DONE',name,p.returncode,flush=True)
    if p.returncode:raise RuntimeError(f'{name} failed; see {log}')
try:
    lean(source,module)
    helpers=['CertificateBoundErasure','BoundErasureReplay']+(['BoundErasureCountedReplay'] if protocol=='mldr' else [])
    if target=='ClientServerDbAeCleanup':helpers+=['CertificateBooleanCleanup','ClientServerDbAeTransport']
    if target=='ClientServerDbAeSizedTransport':helpers+=['CertificateBoundSubstitution']
    for h in helpers:
        src=ROOT/'research/bapa'/f'{h}.lean';shutil.copy2(src,OUT/src.name);lean(src,h)
    src=ROOT/'research/bapa'/f'{target}.lean';shutil.copy2(src,OUT/src.name);lean(src,target,1200)
    if protocol=='client_server_db_ae':
        lean(OUT/'Checks.lean','Checks',1200)
    else:
        rows=[r.split('\t') for r in (OUT/'checks.tsv').read_text().splitlines()[1:]]
        observed={(r[0],r[1]):r[2] for r in rows if r[0]!='diagnostic'}
        ns='Bapa.MLDRBoundErasureTransport';hns=ns+'.Checked';n=17
        assert all((str(i),p) in observed for i in range(n) for p in ['guards','init','step'])
        prefix=f'import {target}\nopen Kern\nnamespace {hns}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
        def term(i):return f'({ns}.entryAt {i} (by decide +kernel))'
        global_text=prefix+f'theorem global : cGlobalOkF {ns}.machine {ns}.declarations ({ns}.proof.map (·.e)) = {observed[("global","all")]} := by decide +kernel\n#print axioms global\n'
        for i in range(n):global_text+=f'theorem guard_{i} : Bapa.BoundErasureCountedReplay.guardCheck {ns}.machine {ns}.declarations {ns}.proof {term(i)} = {observed[(str(i),"guards")]} := by decide +kernel\n#print axioms guard_{i}\n'
        global_text+=f'end {hns}\n';(OUT/'GlobalCheck.lean').write_text(global_text);lean(OUT/'GlobalCheck.lean','GlobalCheck')
        names=['GlobalCheck']
        for i in range(n):
            for phase,fn in [('init','startCheck'),('step','stepCheck')]:
                name=f'Row{i:02d}{phase.title()}';names.append(name)
                args=f'{ns}.machine {ns}.declarations '+(f'{ns}.proof ' if phase=='step' else '')+term(i)
                text=prefix+f'theorem row_{i}_{phase} : Bapa.BoundErasureCountedReplay.{fn} {args} = {observed[(str(i),phase)]} := by decide +kernel\n#print axioms row_{i}_{phase}\nend {hns}\n'
                (OUT/f'{name}.lean').write_text(text);lean(OUT/f'{name}.lean',name,1200)
        text=''.join(f'import {name}\n' for name in names)+f'open Kern\nnamespace {hns}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
        family=observed[('family','all')]
        if family=='true':
            for i in range(n):
                text+=f'theorem entry_{i} : cEntryCheckF {ns}.machine {ns}.declarations ({ns}.proof.map (·.e)) {term(i)} = true := by\n  change ((Bapa.BoundErasureCountedReplay.guardCheck {ns}.machine {ns}.declarations {ns}.proof {term(i)} && Bapa.BoundErasureCountedReplay.startCheck {ns}.machine {ns}.declarations {term(i)}) && Bapa.BoundErasureCountedReplay.stepCheck {ns}.machine {ns}.declarations {ns}.proof {term(i)}) = true\n  rw [guard_{i}, row_{i}_init, row_{i}_step]\n  rfl\n'
            terms=', '.join(term(i) for i in range(n))
            text+=f'theorem family : checkCMachineF {ns}.machine {ns}.declarations {ns}.proof = true := by\n  apply checkCMachineF_of_parts\n  · exact global\n  · intro ce hce\n    have shape : {ns}.proof = [{terms}] := rfl\n    rw [shape] at hce\n    simp only [List.mem_cons, List.not_mem_nil, or_false] at hce\n    rcases hce with '+' | '.join('h' for _ in range(n))+'\n'
            for i in range(n):text+=f'    · subst ce\n      exact entry_{i}\n'
            text+=f'theorem laws : ∀ ρ M, CReach {ns}.machine {ns}.declarations ρ M → ∀ e ∈ {ns}.proof, e.e.Holds ρ (withCnt {ns}.declarations ρ M) := cmachineF_sound _ _ _ family\n#print axioms laws\n'
        else:text+=f'theorem family : checkCMachineF {ns}.machine {ns}.declarations {ns}.proof = false := by decide +kernel\n'
        text+=f'#print axioms family\nend {hns}\n';(OUT/'Checks.lean').write_text(text);lean(OUT/'Checks.lean','Checks',1200)
    rows=[r.split('\t') for r in (OUT/'checks.tsv').read_text().splitlines()[1:]]
    family=next(r[2] for r in rows if r[:2]==['family','all'])
    meta['status']='CHECKED_ACCEPTED' if family=='true' else 'CHECKED_REJECTED';meta['familyAccepted']=family=='true';meta['checkedParts']=len([r for r in rows if r[0]!='diagnostic' and r[1] in ['init','step']])+(1 if protocol=='mldr' else 0)
except Exception as e:
    meta.update(status='CHECK_FAILED',error=repr(e));raise
finally:
    meta['leanReceipts']=records
    (OUT/'REPLAY-METADATA.json').write_text(json.dumps(meta,indent=2)+'\n')
