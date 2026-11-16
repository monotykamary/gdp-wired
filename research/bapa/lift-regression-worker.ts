// One fresh process per fixture. Product lift + ordinary native Lean checks only.
import {spawn} from 'node:child_process'
import {closeSync,mkdirSync,openSync,readFileSync,rmSync,writeFileSync,writeSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {lift} from '../../lean-kernel/lift.ts'
import {auditLiftLog,gate} from '../../lean-kernel/axiom-audit.ts'
import {readLiftSource} from '../../lean-kernel/lift/source.ts'
import {assert,checkEmission,hash,hashFile,implementationFiles,json,verifyFiles,type Manifest} from './lift-regression.ts'

const root=process.cwd(),id=process.argv[2],output=process.env.SUPERCOMPUTER_OUTPUT_DIR
assert(output,'SUPERCOMPUTER_OUTPUT_DIR required; use a fresh supercomputer job')
const out=resolve(output),project=join(out,'project'),commands:unknown[]=[]
mkdirSync(out,{recursive:true})
const receipt:Record<string,unknown>={schema:'gdp-lift-regression-check/v1',id,status:'FAILED',noSearch:true,allSizesProven:false,independentTlaVerification:false,scope:'provided encoded source machine and laws',commands}
async function run(label:string,argv:string[],cwd:string,seconds:number):Promise<string>{
  const paths=[join(out,label+'.stdout.log'),join(out,label+'.stderr.log')],fds=paths.map(p=>openSync(p,'wx')),counts=[0,0]
  const child=spawn(argv[0]!,argv.slice(1),{cwd,env:{...process.env,GDP_LEAN_NATIVE:'0'},stdio:['ignore','pipe','pipe']})
  let problem:string|undefined
  const stop=()=>{if(child.pid)try{process.kill(child.pid,'SIGKILL')}catch(e){if((e as NodeJS.ErrnoException).code!=='ESRCH')problem??=String(e)}}
  const timer=setTimeout(()=>{problem??=label+' deadline exceeded';stop()},seconds*1000)
  for(const [i,stream]of [child.stdout!,child.stderr!].entries())stream.on('data',(chunk:Buffer)=>{
    try{const remaining=32*1024*1024-counts[i]!;if(remaining>0)writeSync(fds[i]!,chunk.subarray(0,remaining));counts[i]!+=chunk.length;if(counts[i]!>32*1024*1024){problem??=label+' log overflow';stop()}}catch(e){problem??=String(e);stop()}
  })
  const result=await new Promise<{code:number|null;signal:string|null}>(done=>{
    child.on('error',e=>{problem??=String(e)})
    child.on('close',(code,signal)=>done({code,signal}))
  })
  clearTimeout(timer);fds.forEach(fd=>closeSync(fd))
  commands.push({argv,cwd,exitCode:result.code,signal:result.signal,problem,logs:paths.map(path=>({path,sha256:hashFile(path)}))})
  assert(!problem&&result.code===0&&!result.signal,problem??label+' failed: '+JSON.stringify(result))
  return paths.map(p=>readFileSync(p,'utf8')).join('\n')
}
try{
  assert(process.argv.length===3&&/^[A-Za-z][A-Za-z0-9_]*$/.test(id??''),'usage: lift-regression-worker.ts ID')
  // This opt-in is deliberately absent from fixture preparation and unit jobs.
  assert(process.env.LIFT_REGRESSION_NATIVE==='1','native replay requires explicit final-source-freeze authorization')
  assert(/^[a-f0-9]{40}$/.test(process.env.LIFT_REGRESSION_SNAPSHOT??''),'exact frozen snapshot required')
  const manifestPath=join(root,'research/bapa/lift-regression-manifest.json'),manifest=json<Manifest>(manifestPath)
  assert(manifest.schema==='gdp-lift-regression/v1'&&manifest.allSizesProven===false,'invalid suite manifest')
  const matches=manifest.entries.filter(e=>e.id===id);assert(matches.length===1,'fixture not unique')
  const e=matches[0]!
  receipt.manifestSha256=hashFile(manifestPath)
  assert(e.pending.length===0&&e.source.status==='FROZEN'&&e.source.sha256,'fixture/baseline pending: '+e.pending.join('; '))
  const sourcePath=resolve(root,e.source.path),capsule=resolve(root,e.capture.path)
  const {source,sourceSha256}=readLiftSource(sourcePath)
  assert(source.id===id&&sourceSha256===e.source.sha256,'frozen fixture changed')
  assert(hashFile(join(capsule,'CAPTURE.json'))===e.capture.sha256,'CAPTURE changed')
  const before=implementationFiles(root)
  receipt.implementationFiles=before;receipt.implementationSha256=hash(JSON.stringify(before))
  receipt.claimedSnapshot=process.env.LIFT_REGRESSION_SNAPSHOT??null
  receipt.input={capture:e.capture,source:e.source}
  const emitted=lift(capsule,sourcePath,project,{expectedManifestSha256:e.capture.sha256})
  receipt.emissionSha256=hashFile(join(project,'EMITTED.json'));receipt.files=emitted.files
  checkEmission(e,emitted,sourceSha256);verifyFiles(project,emitted.files)
  const build=await run('lift-build',['lake','build'],project,3300)
  const buildErrors=gate(build,[],false)
  assert(!buildErrors.length&&!/\berror:/.test(build),buildErrors.join('; ')||'Lean build error')
  const log=await run('lift-root',['lake','env','lean','BapaProof.lean'],project,3300)
  const checked=auditLiftLog(log,[readFileSync(join(project,'BapaProof.lean'),'utf8')],emitted.requiredTheorems,e.baseline.axioms)
  receipt.checkedTheorems=checked
  verifyFiles(project,emitted.files)
  assert(hashFile(join(project,'EMITTED.json'))===receipt.emissionSha256,'emission changed during check')
  assert(hashFile(sourcePath)===sourceSha256&&hashFile(join(capsule,'CAPTURE.json'))===e.capture.sha256,'inputs changed during check')
  assert(hashFile(manifestPath)===receipt.manifestSha256,'expectations changed during check')
  assert(hash(JSON.stringify(implementationFiles(root)))===receipt.implementationSha256,'implementation changed during check')
  receipt.status='SOURCE_CHECKED'
}catch(error){receipt.reason=error instanceof Error?error.message:String(error);process.exitCode=1}
finally{
  try{rmSync(join(project,'.lake'),{recursive:true,force:true})}catch(error){receipt.status='FAILED';receipt.reason='cache cleanup failed: '+String(error);process.exitCode=1}
  writeFileSync(join(out,'LIFT-REGRESSION.json'),JSON.stringify(receipt,null,2)+'\n',{flag:'wx'})
}
console.log(JSON.stringify({id,status:receipt.status,reason:receipt.reason}))
