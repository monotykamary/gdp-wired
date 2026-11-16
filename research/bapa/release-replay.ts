// Data-only release replay. Run in a supercomputer job AFTER gen-lean-library.ts.
// EMITTED is a custody record, never evidence that Lean accepted the source.
import {createHash} from 'node:crypto'
import {spawn} from 'node:child_process'
import {mkdirSync, readFileSync, writeFileSync, openSync, closeSync, writeSync, rmSync, lstatSync, readdirSync} from 'node:fs'
import {resolve, join, sep, isAbsolute} from 'node:path'
import {answers, asked, gate} from '../../scripts/lean-gate/gate.ts'

interface Entry {
  id:string; mode:'alpha'|'witness'|'counted'|'toy'|'client'
  capture:string; sha256:string; proof?:string; proofSha256?:string
}
interface CommandReceipt {
  command:string[]; cwd:string; exitCode:number|null; signal:string|null
  stdout:string; stderr:string; stdoutSha256:string; stderrSha256:string
}
const sha=(data:string|Uint8Array)=>createHash('sha256').update(data).digest('hex')
const hashFile=(path:string)=>sha(readFileSync(path))
const requireThat:(ok:unknown,why:string)=>asserts ok=(ok,why)=>{if(!ok)throw Error(why)}
const digest=(x:unknown):x is string=>typeof x==='string'&&/^[a-f0-9]{64}$/.test(x)
const root=process.cwd(), id=process.argv[2]
const output=process.env.SUPERCOMPUTER_OUTPUT_DIR
// Without a destination there is nowhere to publish a failure receipt.
if(!output)throw Error('SUPERCOMPUTER_OUTPUT_DIR is required; run via supercomputer --skill')
const out=resolve(output)
mkdirSync(out,{recursive:true})
const project=join(out,'project'), commands:CommandReceipt[]=[]
const receipt:Record<string,unknown>={schema:'bapa-release-replay/v1',id,noSearch:true,commands}

// Drain both pipes, but retain at most 32 MiB per stream. Overflow FAILS rather
// than silently dropping the output a checker may need. Stop the exact owned child PID on deadline/overflow; the bounded
// supercomputer job remains responsible for namespace cleanup of descendants.
async function run(label:string,command:string[],cwd:string,seconds:number):Promise<void>{
  const stdout=join(out,label+'.stdout.log'),stderr=join(out,label+'.stderr.log')
  const fds=[openSync(stdout,'wx'),openSync(stderr,'wx')]
  let problem:string|undefined
  const child=spawn(command[0]!,command.slice(1),{cwd,env:{...process.env,GDP_LEAN_NATIVE:'0'},stdio:['ignore','pipe','pipe'],detached:true})
  const stop=()=>{if(child.pid){try{process.kill(child.pid,'SIGKILL')}catch(e){if((e as NodeJS.ErrnoException).code!=='ESRCH')problem??=String(e)}}}
  const timer=setTimeout(()=>{problem??=`${label} deadline exceeded (${seconds}s)`;stop()},seconds*1000)
  const counts=[0,0]
  for(const [i,stream]of [child.stdout!,child.stderr!].entries())stream.on('data',(chunk:Buffer)=>{
    try{
      const left=32*1024*1024-counts[i]!
      if(left>0)writeSync(fds[i]!,chunk.subarray(0,left))
      counts[i]=counts[i]!+chunk.length
      if(counts[i]!>32*1024*1024){problem??=`${label} log limit exceeded`;stop()}
    }catch(e){problem??=String(e);stop()}
  })
  const result=await new Promise<{code:number|null;signal:NodeJS.Signals|null}>(done=>{
    child.on('error',e=>{problem??=String(e)})
    child.on('close',(code,signal)=>done({code,signal}))
  }).finally(()=>{clearTimeout(timer);for(const fd of fds)closeSync(fd)})
  commands.push({command,cwd,exitCode:result.code,signal:result.signal,stdout,stderr,stdoutSha256:hashFile(stdout),stderrSha256:hashFile(stderr)})
  if(problem||result.code!==0||result.signal)throw Error(problem??`${label} failed: exit ${result.code}, signal ${result.signal}`)
}
function logs(label:string){return readFileSync(join(out,label+'.stdout.log'),'utf8')+'\n'+readFileSync(join(out,label+'.stderr.log'),'utf8')}
function checkFiles(files:unknown):Record<string,string>{
  requireThat(files&&typeof files==='object'&&!Array.isArray(files),'missing emitted file manifest')
  const hashes:Record<string,string>={}
  for(const [name,value]of Object.entries(files)){
    const path=resolve(project,name)
    requireThat(path.startsWith(project+sep)&&!isAbsolute(name)&&digest(value),'invalid emitted file entry: '+name)
    requireThat(lstatSync(path).isFile()&&!lstatSync(path).isSymbolicLink(),'not a regular emitted file: '+name)
    requireThat(hashFile(path)===value,'emitted file changed: '+name)
    hashes[name]=value
  }
  requireThat(hashes['BapaProof.lean']&&hashes['lakefile.lean']&&hashes['lean-toolchain'],'incomplete Lean project')
  // Emitters currently create flat projects; reject omitted files before build.
  for(const name of readdirSync(project))requireThat(name==='EMITTED.json'||Object.hasOwn(hashes,name),'unmanifested project file: '+name)
  return hashes
}
function checkAxioms(log:string,source:string[],wanted:string[],namespace=''){
  const errors=gate(log,source,false)
  requireThat(!errors.length,errors.join('; '))
  requireThat(!/\berror:|declaration uses 'sorry'/.test(log),'Lean error in log')
  const found=new Set(answers(log).map(x=>x.name))
  // gate checks counts; check exact names too (duplicates must not fill a gap).
  for(const name of [...source.flatMap(asked).map(n=>namespace+n),...wanted])requireThat(found.has(name),'missing exact theorem axiom output: '+name)
}
async function replay(){
  requireThat(process.argv.length===3&&typeof id==='string'&&id.length>0,'usage: release-replay.ts ID')
  const revision=process.env.BAPA_RELEASE_COMMIT
  requireThat(typeof revision==='string'&&/^[a-f0-9]{40}$/.test(revision),'BAPA_RELEASE_COMMIT must be an exact source revision')
  receipt.sourceRevision=revision
  const manifestPath=join(root,'research/bapa/release-replay-manifest.json')
  const raw=readFileSync(manifestPath,'utf8'),parsed=JSON.parse(raw)
  const entries:unknown=Array.isArray(parsed)?parsed:parsed.entries
  requireThat(Array.isArray(entries),'release manifest must be an array or contain entries')
  const selected=entries.filter((e:Entry)=>e?.id===id)
  requireThat(selected.length===1,'selected id must occur exactly once: '+id)
  const entry=selected[0] as Entry
  requireThat(['alpha','witness','counted','toy','client'].includes(entry.mode),'unsupported replay mode')
  requireThat(typeof entry.capture==='string'&&!isAbsolute(entry.capture)&&digest(entry.sha256),'invalid capture mount/hash')
  receipt.mode=entry.mode;receipt.manifestSha256=sha(raw)
  const capture=resolve(root,entry.capture),captureFile=join(capture,'CAPTURE.json')
  requireThat(hashFile(captureFile)===entry.sha256,'CAPTURE.json SHA-256 mismatch')
  const cap=JSON.parse(readFileSync(captureFile,'utf8'))
  requireThat(digest(cap.identity?.inputSha256),'invalid capture identity.inputSha256')
  receipt.input={capture:entry.capture,captureSha256:entry.sha256,identity:cap.identity}
  const special=entry.mode==='toy'||entry.mode==='client'
  let proof:string|undefined
  if(special){
    requireThat(typeof entry.proof==='string'&&!isAbsolute(entry.proof)&&digest(entry.proofSha256),'special mode requires proof mount and SHA-256')
    proof=resolve(root,entry.proof)
    requireThat(hashFile(proof)===entry.proofSha256,'retained proof SHA-256 mismatch')
    receipt.proof={path:entry.proof,sha256:entry.proofSha256}
  }
  const script=(name:string)=>join(root,'research/bapa',name+'.ts')
  const bun=process.execPath
  const emit=special?[bun,script(entry.mode==='toy'?'p2-toy-inclusion':'p3-client-typed'),capture,proof!,project]:[
    bun,script(entry.mode==='counted'?'proof-counted-source':'proof-emit'),'--capture',capture,'--sha256',entry.sha256,'--out',project,
    ...(entry.mode==='counted'?[]:['--projection',entry.mode])]
  await run('emit',emit,root,1800)
  const emittedRaw=readFileSync(join(project,'EMITTED.json'),'utf8'),r=JSON.parse(emittedRaw)
  requireThat(r.status==='EMITTED_NOT_CHECKED'&&r.inputSha256===entry.sha256,'emission input/status mismatch')
  const files=checkFiles(r.files)
  receipt.emissionSha256=sha(emittedRaw);receipt.files=files
  let wanted:string[]
  if(entry.mode==='client'){
    requireThat(r.schema==='p3-typed-source/v1'&&r.sourceAccepted===false&&r.newSearches===0,'invalid client emission')
    requireThat(r.retainedLeanSha256===entry.proofSha256,'client proof identity mismatch')
    requireThat(r.sourceTheorem==='bapa_client_server_db_ae_source','unexpected client source theorem')
    requireThat(Array.isArray(r.parameters)&&r.parameters.length===4&&r.parameters.every((n:unknown)=>Number.isSafeInteger(n)&&Number(n)>=0)&&new Set(r.parameters).size===4,'client requires four distinct parameter indices')
    requireThat(files['TypedBoundControls.lean']&&files['basis.json'],'missing typed bound controls/basis')
    const basis=JSON.parse(readFileSync(join(project,'basis.json'),'utf8'))
    requireThat(JSON.stringify(basis.sizes)===JSON.stringify(r.parameters),'client receipt parameters differ from emitted basis')
    wanted=[r.sourceTheorem];receipt.parameters=r.parameters
  }else{
    requireThat(r.schema==='bapa-emission/v1'&&r.leanExecuted===false&&r.allSizesProven===false,'invalid source emission')
    requireThat(r.identity?.inputSha256===cap.identity.inputSha256&&r.identity?.protocol===cap.identity.protocol,'emission capture identity mismatch')
    requireThat(r.sourceProjection?.kind===(entry.mode==='toy'?'counted':entry.mode),'wrong source projection kind')
    const source:unknown=r.sourceProjection.sourceTheorems
    requireThat(Array.isArray(source)&&source.length>0&&source.every((n:unknown)=>typeof n==='string'&&/^bapa_[A-Za-z0-9_]+$/.test(n)),'invalid source theorem coverage')
    requireThat(typeof r.familyTheorem==='string'&&/^bapa_[A-Za-z0-9_]+$/.test(r.familyTheorem),'invalid family theorem')
    wanted=[r.familyTheorem,...source]
    requireThat(new Set(wanted).size===wanted.length,'duplicate theorem coverage')
    if(entry.mode==='alpha'){
      const prefix='bapa_'+String(cap.identity.protocol).replace(/[^A-Za-z0-9_]/g,'_')
      const names=r.sourceProjection.publicLawNames
      requireThat(Array.isArray(names)&&names.length>0,'alpha public law coverage missing')
      const expected=[prefix+'_source_laws',...names.map((_:unknown,j:number)=>prefix+'_source_law'+j+'_holds')]
      requireThat(r.familyTheorem===prefix+'_laws'&&JSON.stringify(source)===JSON.stringify(expected),'alpha source theorem coverage mismatch')
      wanted.push(prefix+'_alpha_valid',prefix+'_alpha_result')
    }
  }
  await run('build',['lake','build'],project,10800)
  await run('lean',['lake','env','lean','BapaProof.lean'],project,10800)
  const source=readFileSync(join(project,'BapaProof.lean'),'utf8')
  checkAxioms(logs('lean'),[source],wanted)
  checkAxioms(logs('build'),[],[])
  if(entry.mode==='client'){
    await run('controls',['lake','env','lean','TypedBoundControls.lean'],project,1800)
    checkAxioms(logs('controls'),[readFileSync(join(project,'TypedBoundControls.lean'),'utf8')],[],'TypedBoundControls.')
  }
  const combined=logs('build')+'\n'+logs('lean')
  writeFileSync(join(out,'lean.log'),combined,{flag:'wx'})
  receipt.leanLogSha256=sha(combined)
  if(entry.mode==='counted'||entry.mode==='toy'||entry.mode==='witness'){
    await run('source-verify',[bun,script(entry.mode==='witness'?'witness-source-verify':'proof-source-verify'),project,join(out,'lean.log'),join(out,'SOURCE-CHECKED.json')],root,300)
    receipt.sourceCheckSha256=hashFile(join(out,'SOURCE-CHECKED.json'))
  }
  // A successful compiler run is not allowed to change any emitted input.
  for(const [name,hash]of Object.entries(files))requireThat(hashFile(join(project,name))===hash,'file changed during native checking: '+name)
  requireThat(hashFile(captureFile)===entry.sha256,'capture changed during replay')
  if(proof)requireThat(hashFile(proof)===entry.proofSha256,'proof changed during replay')
  receipt.checkedTheorems=wanted
}
try{
  await replay()
  receipt.status='SOURCE_CHECKED'
}catch(error){
  receipt.status='FAILED';receipt.reason=error instanceof Error?error.message:String(error)
  process.exitCode=1
}finally{
  // Keep sources and bounded logs for audit, never upload the compiled cache.
  try{rmSync(join(project,'.lake'),{recursive:true,force:true})}catch(error){
    receipt.status='FAILED';receipt.reason='project cache cleanup failed: '+String(error);process.exitCode=1
  }
  writeFileSync(join(out,'RELEASE-REPLAY.json'),JSON.stringify(receipt,null,2)+'\n')
}
console.log(JSON.stringify({id,status:receipt.status,reason:receipt.reason}))
