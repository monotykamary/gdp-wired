// Deterministic accepted-Paxos replay ONLY. This is not the native data-only lift CLI.
// CLI: bun research/bapa/paxos-release-replay.ts --out "$SUPERCOMPUTER_OUTPUT_DIR"
// Requires LIFT_REGRESSION_SNAPSHOT and three private mounts (see jobs JSON).
import {spawn} from 'node:child_process'
import {closeSync,copyFileSync,existsSync,mkdirSync,openSync,readFileSync,writeFileSync} from 'node:fs'
import {dirname,join,resolve} from 'node:path'
import {implementationFiles} from './lift-regression.ts'
import {auditPaxosReplay,expectedReuse,verifyOriginalExports} from './paxos-release-audit.ts'
import {CAPSULE,CHECKED,EMITTER,FAMILY,FRESH,MANIFEST,MODE,REPRODUCED,SOURCE,SOURCE_INPUTS,assert,capsuleFiles,checkAxioms,checkedFile,expectedAxioms,hash,hashFile,runnerFiles,type NativeCommand,type PaxosReplayReceipt} from './paxos-release.helpers.ts'

export async function replayPaxos(out:string,root=process.cwd()):Promise<PaxosReplayReceipt>{
 out=resolve(out)
 assert(!existsSync(join(out,'PAXOS-REPLAY.json'))&&!existsSync(join(out,'project')),'fresh output directory required')
 mkdirSync(out,{recursive:true});mkdirSync(join(out,'logs'))
 const commands:NativeCommand[]=[],implementation=implementationFiles(root),own=runnerFiles(root)
 const receipt:PaxosReplayReceipt={schema:'paxos-release-replay/v1',id:'paxos_epr',status:'FAILED',mode:MODE,format:'Lean-source',nativeCliAcceptance:false,cleanSourceBuild:false,noSearch:true,claimedSnapshot:process.env.LIFT_REGRESSION_SNAPSHOT??'',implementationFiles:implementation,implementationSha256:hash(JSON.stringify(implementation)),runnerFiles:own,runnerSha256:hash(JSON.stringify(own)),capsuleManifestSha256:MANIFEST,sourceFiles:{},sourcePortSha256:'3063304ae3bf8d7c7cc9870c838f7f5da7ab916a96d3729a7ca0b8db5f5b1d76',checkedSha256:CHECKED,familyTheorem:FAMILY,sourceTheorem:SOURCE,entries:Array.from({length:25},(_,i)=>i),obligations:Array.from({length:25},(_,law)=>[{law,step:false},{law,step:true}]).flat(),axioms:{},reused:[],fresh:[],commands,originalExports:{},sourceInputFiles:SOURCE_INPUTS,sourceReproductionFiles:{},reachableModules:[],toolchainModules:{}}
 const save=()=>writeFileSync(join(out,'PAXOS-REPLAY.json'),JSON.stringify(receipt,null,2)+'\n')
 const project=join(out,'project')
 async function run(label:string,argv:string[],sourceEmission=false):Promise<string>{
  const stdout='logs/'+label+'.stdout.log',stderr='logs/'+label+'.stderr.log'
  const fds=[openSync(join(out,stdout),'wx'),openSync(join(out,stderr),'wx')]
  let exitCode:number|null=null,signal:string|null=null,problem:unknown
  try{
   await new Promise<void>((done,fail)=>{
    const child=spawn(argv[0]!,argv.slice(1),{cwd:sourceEmission?root:project,env:{...process.env,LEAN_PATH:join(project,'checked'),LEAN_NUM_THREADS:'1',GDP_LEAN_NATIVE:'0',...(sourceEmission?{SUPERCOMPUTER_OUTPUT_DIR:join(out,'source-reproduction')}:{})},stdio:['ignore',fds[0]!,fds[1]!]})
    child.once('error',fail);child.once('close',(code,sig)=>{exitCode=code;signal=sig;done()})
   })
  }catch(error){problem=error}
  finally{for(const fd of fds)closeSync(fd);commands.push({label,argv,cwd:sourceEmission?'root':'project',environment:{LEAN_PATH:'project/checked',LEAN_NUM_THREADS:'1',GDP_LEAN_NATIVE:'0',...(sourceEmission?{SUPERCOMPUTER_OUTPUT_DIR:'source-reproduction'}:{})},exitCode,signal,stdout,stderr,stdoutSha256:hashFile(join(out,stdout)),stderrSha256:hashFile(join(out,stderr))});save()}
  assert(!problem&&exitCode===0&&signal===null,'native command failed '+label+': '+(problem instanceof Error?problem.message:typeof problem==='string'?problem:String(exitCode)))
  return readFileSync(join(out,stdout),'utf8')
 }
 try{
  assert(receipt.claimedSnapshot,'LIFT_REGRESSION_SNAPSHOT required')
  const files=capsuleFiles(join(root,CAPSULE),root);receipt.sourceFiles=files
  const {base,rows,reused,reachable}=expectedReuse(root,files)
  receipt.reachableModules=reachable.modules
  const data=(key:string,fallback:string)=>resolve(root,process.env[key]??fallback)
  const accepted=data('PAXOS_REPLAY_ACCEPTED_DATA','paxos-replay-accepted'),baseDir=data('PAXOS_REPLAY_BASE_DATA','paxos-replay-base'),provenance=data('PAXOS_REPLAY_PROVENANCE_DATA','paxos-replay-provenance')
  receipt.originalExports=verifyOriginalExports(provenance,root,files)
  mkdirSync(join(out,'provenance/base'),{recursive:true});mkdirSync(join(project,'checked'),{recursive:true})
  for(const [kind,pin]of Object.entries(base.exports))for(const [suffix,digest]of [['export',pin.manifestSha256],['results',pin.resultsSha256]]){
   const name=kind+'-'+suffix+'.json';copyFileSync(checkedFile(provenance,name,digest!),join(out,'provenance',name))
  }
  copyFileSync(checkedFile(accepted,'CHECKED.json',CHECKED),join(out,'provenance/CHECKED.json'))
  for(const [name,digest]of Object.entries(base.files))copyFileSync(checkedFile(baseDir,name,digest),join(out,'provenance/base',name))
  // Verify every supplied accepted object, even the ones deliberately replaced below.
  for(const r of rows){checkedFile(accepted,r.module+'.lean',r.sha256);checkedFile(accepted,'checked/'+r.module+'.olean',r.oleanSHA256)}
  for(const [module,digest]of Object.entries(base.objects)){
   checkedFile(baseDir,'project/'+module+'.lean',files[module+'.lean']!)
   checkedFile(baseDir,'project/.lake/build/lib/lean/'+module+'.olean',digest)
  }
  for(const name of [...Object.keys(files),'SHA256SUMS'])copyFileSync(join(root,CAPSULE,name),join(project,name))
  for(const row of reused){
   const src=row.origin==='retained-core'?checkedFile(baseDir,'project/.lake/build/lib/lean/'+row.module+'.olean',row.objectSha256):checkedFile(accepted,'checked/'+row.module+'.olean',row.objectSha256)
   copyFileSync(src,join(project,'checked',row.module+'.olean'))
  }
  receipt.reused=reused;save()
  for(const [path,digest]of Object.entries(SOURCE_INPUTS)){
   mkdirSync(dirname(join(out,'source-inputs',path)),{recursive:true})
   copyFileSync(checkedFile(root,path,digest),join(out,'source-inputs',path))
  }
  mkdirSync(join(out,'source-reproduction'))
  await run('source-emission',['timeout','--kill-after=10s','120s','bun',EMITTER],true)
  for(const name of REPRODUCED){
   checkedFile(join(out,'source-reproduction'),name,files[name]!)
   assert(readFileSync(join(out,'source-reproduction',name)).equals(readFileSync(join(project,name))),'source reproduction bytes changed '+name)
   receipt.sourceReproductionFiles[name]=files[name]!
  }
  save()
  // No inherited build directory, alternate cache, or external LEAN_PATH is consulted.
  // Elan selects the unmodified capsule's pinned lean-toolchain; no auto installation.
  const lean=(await run('lean-path',['elan','which','lean'])).trim()
  assert(lean.startsWith('/')&&lean.endsWith('/lean'),'unexpected Lean path')
  const version=await run('lean-version',[lean,'--version'])
  assert(/^Lean \(version 4\.34\.0(?:,|\))/.test(version),'capsule requires Lean 4.34.0')
  receipt.lean={path:lean,sha256:hashFile(lean),version}
  mkdirSync(join(out,'runtime'))
  for(const module of reachable.external){
   const library=resolve(dirname(lean),'../lib/lean'),digest=hashFile(join(library,module+'.olean'))
   copyFileSync(checkedFile(library,module+'.olean',digest),join(out,'runtime',module+'.olean'))
   receipt.toolchainModules[module]=digest
  }
  for(const module of FRESH){
   assert(!existsSync(join(project,'checked',module+'.olean')),'fresh module object already exists '+module)
   const log=await run(module,['timeout','--kill-after=10s','300s',lean,'-o','checked/'+module+'.olean',module+'.lean'])
   Object.assign(receipt.axioms,checkAxioms(log+'\n'+readFileSync(join(out,'logs',module+'.stderr.log'),'utf8'),expectedAxioms(module)))
   receipt.fresh.push({module,sourceSha256:files[module+'.lean']!,objectSha256:hashFile(join(project,'checked',module+'.olean'))});save()
  }
  assert(receipt.implementationSha256===hash(JSON.stringify(implementationFiles(root))),'implementation changed during replay')
  assert(receipt.runnerSha256===hash(JSON.stringify(runnerFiles(root))),'runner changed during replay')
  receipt.status='SOURCE_CHECKED';save();auditPaxosReplay(out,root)
 }catch(error){receipt.status='FAILED';receipt.reason=error instanceof Error?error.message:String(error);save();throw error}
 return receipt
}
if(import.meta.main){
 const args=process.argv.slice(2)
 assert(args.length===2&&args[0]==='--out','usage: bun research/bapa/paxos-release-replay.ts --out DIRECTORY')
 replayPaxos(args[1]!).then(r=>console.log(r.status+' '+r.mode)).catch(e=>{console.error(e);process.exitCode=1})
}
