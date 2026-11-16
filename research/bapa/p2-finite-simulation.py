from pathlib import Path
import os, subprocess, json, hashlib
root=Path.cwd(); out=Path(os.environ['SUPERCOMPUTER_OUTPUT_DIR']); built=out/'checked'; built.mkdir()
env=dict(os.environ); env['PATH']=str(root/'scripts/lean-gate')+':'+env['PATH']
env['LEAN_PATH']=':'.join(map(str,[built,root/'research/bapa',root/'simulation-retained/.lake/build/lib/lean',root/'simulation-retained']))
env['LEAN_NUM_THREADS']='1'; rows=[]
for name in ['CountedSourceProjection','CountedNoninterference','CountedSourceBridge','SourceInclusion','FiniteSimulation','FiniteSimulationControls','PaxosEprScanSimulation']:
    src=root/'research/bapa'/(name+'.lean'); (out/(name+'.lean')).write_bytes(src.read_bytes())
    with (out/(name+'.log')).open('wb') as log:
        p=subprocess.run(['timeout','240s','lean','-o',str(built/(name+'.olean')),str(src)],env=env,stdout=log,stderr=subprocess.STDOUT)
    rows.append({'module':name,'code':p.returncode,'sha256':hashlib.sha256(src.read_bytes()).hexdigest()})
    (out/'receipt.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(name,p.returncode,flush=True)
    if p.returncode: raise SystemExit(p.returncode)
