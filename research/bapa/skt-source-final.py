"""Static/receipt gate or the pinned put-without-ownership negative control."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys
ROOT=Path.cwd();OUT=Path(os.environ['SUPERCOMPUTER_OUTPUT_DIR']);GOOD=ROOT/'skt-good'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def run(args,name,env=None,expect=0,stdin=None,cwd=None):
 with (OUT/(name+'.log')).open('wb') as log:
  p=subprocess.run(args,cwd=cwd or ROOT,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=650,stdin=stdin)
 if expect==0 and p.returncode!=0:raise RuntimeError(name+' failed')
 return p.returncode
run(['bun','install','--frozen-lockfile'],'install')
if sys.argv[1]=='receipt':
 config={'extends':str(ROOT/'tsconfig.json'),'files':[str(ROOT/'research/bapa'/p) for p in ['skt-source-data.ts','skt-source-verify.ts','skt-source-verify.test.ts']],'include':[]}
 configpath=ROOT/'research/bapa/SktSource.config.json'
 configpath.write_text(json.dumps(config));shutil.copy2(configpath,OUT/'SktSourceConfig.json')
 run(['bunx','tsc','-p',str(configpath)],'types')
 fixture=OUT/'fixture';shutil.copytree(GOOD,fixture)
 env=dict(os.environ);env['SKT_CHECKED_ROOT']=str(fixture)
 run(['bun','test','research/bapa/skt-source-verify.test.ts'],'tests',env)
 run(['bun','research/bapa/skt-source-verify.ts',str(GOOD),str(OUT/'STRUCTURAL-BRIDGE.json')],'receipt')
 (OUT/'commit-message.txt').write_text('feat(bapa): bridge sharded source to the retained tuple target\n')
 with (OUT/'commit-message.txt').open('rb') as msg:
  run(['bunx','@commitlint/cli','--config','research/egraph/historical/commitlint.config.cjs'],'commitlint',stdin=msg)
elif sys.argv[1]=='negative':
 if sha(ROOT/'research/bapa/SktSourceBridge.lean')!=sha(GOOD/'SktSourceBridge.lean'):raise RuntimeError('positive bridge source drift')
 broken=OUT/'broken';broken.mkdir();rechecked=broken/'rechecked';rechecked.mkdir()
 env=dict(os.environ);env['SUPERCOMPUTER_OUTPUT_DIR']=str(broken)
 run(['bun','research/bapa/skt-source-data.ts','--broken-source'],'negative-data',env)
 gooddata=json.loads((GOOD/'SOURCE-DATA.json').read_text());bad=json.loads((broken/'SOURCE-DATA.json').read_text())
 if not bad['brokenSource'] or bad['sourceSHA256']==gooddata['sourceSHA256']:raise RuntimeError('negative source unchanged')
 env['PATH']=str(ROOT/'scripts/lean-gate')+':'+env['PATH'];env['LEAN_PATH']=':'.join(map(str,[rechecked,GOOD/'rechecked',ROOT/'skt-retained/.lake/build/lib/lean',ROOT/'skt-retained']));env['LEAN_NUM_THREADS']='1'
 for name in ['SktSourceDefs','SktSourceInvariant']:
  src=broken/(name+'.lean')
  if name!='SktSourceDefs':shutil.copy2(ROOT/'research/bapa'/(name+'.lean'),src)
  run(['lean','-o',str(rechecked/(name+'.olean')),str(src)],'negative-'+name,env,cwd=broken)
 src=broken/'SktSourceBridge.lean';shutil.copy2(GOOD/src.name,src)
 code=run(['lean','-o',str(rechecked/'SktSourceBridge.olean'),str(src)],'broken-source',env,expect=None,cwd=broken)
 log=(OUT/'broken-source.log').read_text()
 if code==0 or not re.search(r'SktSourceBridge\.lean:\d+:\d+: error: unsolved goals',log) or re.search(r'unknown identifier|unknown module|object file.*does not exist',log,re.I):raise RuntimeError('negative did not fail at a bridge obligation')
 (OUT/'NEGATIVE-SOURCE.json').write_text(json.dumps({'variant':'put without ownership','bridgeRefused':True,'nativeExitCode':code,'positiveSourceSHA256':gooddata['sourceSHA256'],'negativeSourceSHA256':bad['sourceSHA256'],'bridgeSHA256':sha(src),'logSHA256':sha(OUT/'broken-source.log')},indent=2)+'\n')
else:raise RuntimeError('expected receipt or negative')
