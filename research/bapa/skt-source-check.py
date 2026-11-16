"""Check only new source-bridge modules; reuse immutable accepted target oleans."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,time
ROOT=Path.cwd();OUT=Path(os.environ['SUPERCOMPUTER_OUTPUT_DIR']);RE=OUT/'rechecked';RE.mkdir(parents=True,exist_ok=True)
PRIOR=ROOT/'skt-checked';ALIGNED=ROOT/'skt-aligned';DATA=ROOT/'skt-source-data'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=json.loads((DATA/'SOURCE-DATA.json').read_text())
if source['modelSHA256']!='3063304ae3bf8d7c7cc9870c838f7f5da7ab916a96d3729a7ca0b8db5f5b1d76':raise RuntimeError('wrong source')
if source['leanSHA256']!=sha(DATA/'SktSourceDefs.lean'):raise RuntimeError('source literal changed')
if source['frontendSHA256']!=sha(ROOT/'core/dsl.ts'):raise RuntimeError('source frontend changed')
if sha(PRIOR/'Snapshot.lean')!='2bef0af2d1fb819fa5f1f7ac67dc4cb27e6893e49775edf318a13be1f6f96ea5':raise RuntimeError('target changed')
records=json.loads((PRIOR/'LEAN-RECEIPTS.json').read_text());kept=[]
for r in records:
 name=r['module'];src=PRIOR/(name+'.lean')
 if not src.exists():src=ALIGNED/(name+'.lean')
 artifact=PRIOR/'rechecked'/(name+'.olean')
 if r['exitCode'] or sha(src)!=r['sourceSHA256'] or not artifact.is_file():raise RuntimeError('prior custody failed '+name)
 if r.get('oleanSHA256') and sha(artifact)!=r['oleanSHA256']:raise RuntimeError('prior olean changed '+name)
 shutil.copy2(src,OUT/src.name);shutil.copy2(artifact,RE/artifact.name)
 kept.append({**r,'reused':True,'oleanSHA256':sha(artifact)})
for name in ['SOURCE-DATA.json','SktSourceDefs.lean','SktSourceOriginal.ts']:
 shutil.copy2(DATA/name,OUT/name)
snapshot=(PRIOR/'Snapshot.lean').read_text()
machine=snapshot.split('def machine : SMachine :=\n',1)[1].split('\ndef entry0 : SEntry :=',1)[0]
(OUT/'SktSourceTarget.lean').write_text('import Snapshot\nopen Kern\ndef skt_target : SMachine :=\n'+machine+'\ntheorem skt_target_identity : skt_target = Bapa.ShardedKvSnapshot.machine := rfl\n#print axioms skt_target_identity\n')
env=dict(os.environ);env['PATH']=str(ROOT/'scripts/lean-gate')+':'+env['PATH'];env['LEAN_PATH']=':'.join(map(str,[RE,ROOT/'skt-retained/.lake/build/lib/lean',ROOT/'skt-retained']));env['LEAN_NUM_THREADS']='1'
modules=['SktSourceDefs','SktSourceTarget']+sys.argv[1:]
previous=ROOT/'skt-prior';previous_records={}
if (previous/'SOURCE-DATA.json').exists() and json.loads((previous/'SOURCE-DATA.json').read_text())['leanSHA256']==source['leanSHA256']:
 previous_records={r['module']:r for r in json.loads((previous/'LEAN-RECEIPTS.json').read_text()) if r['exitCode']==0}
for name in modules:
 src=OUT/(name+'.lean')
 if name not in ['SktSourceDefs','SktSourceTarget']:shutil.copy2(ROOT/'research/bapa'/(name+'.lean'),src)
 old=previous_records.get(name);artifact=previous/'rechecked'/(name+'.olean')
 if old and old['sourceSHA256']==sha(src) and artifact.is_file():
  if old.get('oleanSHA256') and old['oleanSHA256']!=sha(artifact):raise RuntimeError('previous source artifact changed '+name)
  shutil.copy2(artifact,RE/artifact.name);shutil.copy2(previous/(name+'.log'),OUT/(name+'.log'))
  kept.append({**old,'reused':True,'oleanSHA256':sha(artifact)});continue
 start=time.monotonic()
 with (OUT/(name+'.log')).open('wb') as log:
  p=subprocess.run(['timeout','--signal=TERM','--kill-after=10s','600s','lean','-o',str(RE/(name+'.olean')),str(src)],cwd=OUT,env=env,stdout=log,stderr=subprocess.STDOUT)
 kept.append({'module':name,'sourceSHA256':sha(src),'exitCode':p.returncode,'reused':False,'seconds':round(time.monotonic()-start,3),**({'oleanSHA256':sha(RE/(name+'.olean'))} if p.returncode==0 else {})})
 (OUT/'LEAN-RECEIPTS.json').write_text(json.dumps(kept,indent=2)+'\n')
 if p.returncode:raise RuntimeError('new source module failed: '+name)
(OUT/'SOURCE-STRUCTURAL-STATUS.json').write_text(json.dumps({'checkedModules':modules,'targetFamilyChecked':False,'sourceSafetyChecked':False,'newProofSearches':0,'targetFamilyReplays':0,'sourceSHA256':source['sourceSHA256'],'targetSHA256':sha(PRIOR/'Snapshot.lean')},indent=2)+'\n')
