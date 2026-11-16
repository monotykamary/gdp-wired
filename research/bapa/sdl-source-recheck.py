"""Recheck only SDL source composition; reuse hash-bound successful dependency modules."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess
ROOT=Path.cwd();OUT=Path(os.environ['SUPERCOMPUTER_OUTPUT_DIR']);PRIOR=ROOT/'sdl-prior';RE=OUT/'rechecked';RE.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((PRIOR/'LEAN-RECEIPTS.json').read_text());kept=[]
source=json.loads((PRIOR/'SOURCE-DATA.json').read_text())
if source['modelSHA256']!=sha(ROOT/'research/protocols/ic3syn/models.ts'):raise RuntimeError('source model changed')
for r in records:
 name=r['module']
 if r['exitCode'] or name=='SdlSourceBridge':continue
 src=PRIOR/(name+'.lean');artifact=PRIOR/'rechecked'/(name+'.olean')
 if sha(src)!=r['sourceSHA256'] or not artifact.is_file():raise RuntimeError('prior custody failed '+name)
 current=ROOT/'research/bapa'/(name+'.lean')
 if current.exists() and sha(current)!=r['sourceSHA256']:raise RuntimeError('dependency changed '+name)
 shutil.copy2(src,OUT/src.name);shutil.copy2(artifact,RE/artifact.name)
 kept.append({**r,'reused':True,'oleanSHA256':sha(artifact)})
for name in ['SOURCE-DATA.json','SDL-SUM-CHECK.txt','checks.tsv']:
 shutil.copy2(PRIOR/name,OUT/name)
env=dict(os.environ);env['PATH']=str(ROOT/'scripts/lean-gate')+':'+env['PATH'];env['LEAN_PATH']=':'.join(map(str,[RE,ROOT/'research/bapa',ROOT/'sdl-retained/lean/.lake/build/lib/lean',ROOT/'sdl-retained/lean']));env['LEAN_NUM_THREADS']='1'
name='SdlSourceBridge';src=ROOT/'research/bapa'/(name+'.lean');shutil.copy2(src,OUT/src.name)
with (OUT/(name+'.log')).open('wb') as log:
 p=subprocess.run(['timeout','--signal=TERM','--kill-after=10s','600s','lean','-o',str(RE/(name+'.olean')),str(src)],cwd=src.parent,env=env,stdout=log,stderr=subprocess.STDOUT)
kept.append({'module':name,'sourceSHA256':sha(src),'exitCode':p.returncode,'reused':False})
(OUT/'LEAN-RECEIPTS.json').write_text(json.dumps(kept,indent=2)+'\n')
if p.returncode:raise RuntimeError('source bridge failed; see log')
