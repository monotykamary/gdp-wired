// Strict comparison input boundary. No prover, job submission or retry.
import {readFileSync,lstatSync,realpathSync,openSync,readSync,closeSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {dirname,join,relative,sep,posix,isAbsolute} from 'node:path'
import {validateResourcePair} from './resource-checks.ts'
function assert(ok:unknown,message:string):asserts ok{if(!ok)throw Error(message)}
const hash=(bytes:Uint8Array)=>createHash('sha256').update(bytes).digest('hex')
const hex=(value:unknown)=>typeof value==='string'&&/^[a-f0-9]{64}$/.test(value)
const present=(value:unknown)=>typeof value==='string'&&value.length>0
const stable=(v:unknown):string=>JSON.stringify(v,(_k,x)=>x&&typeof x==='object'&&!Array.isArray(x)?Object.fromEntries(Object.keys(x).sort().map(k=>[k,x[k]])):x)
function regular(path:string,root:string):{path:string,bytes:Buffer}{
 assert(lstatSync(path).size<=64*1024*1024,'receipt metadata exceeds 64MiB')
 assert(lstatSync(path).isFile(),'not a regular file: '+path)
 const actual=realpathSync(path),rel=relative(root,actual)
 assert(rel!==''&&!rel.startsWith('..'+sep)&&rel!=='..'&&!isAbsolute(rel),'file escapes receipt root: '+path)
 return {path:actual,bytes:readFileSync(actual)}
}
// Native boat seals close JSON with json.dumps(sort_keys=True): spaced separators,
// ASCII escapes and exact integer fields. Refuse unsupported number encodings.
export function nativeCloseJson(value:any):string{
 if(value===null)return 'null'
 if(Array.isArray(value))return '['+value.map(nativeCloseJson).join(', ')+']'
 if(typeof value==='object')return '{'+Object.keys(value).sort().map(key=>nativeCloseJson(key)+': '+nativeCloseJson(value[key])).join(', ')+'}'
 if(typeof value==='number')assert(Number.isSafeInteger(value),'unsupported close receipt number')
 assert(['string','number','boolean'].includes(typeof value),'unsupported close receipt value')
 return JSON.stringify(value).replace(/[\u007f-\uffff]/g,char=>'\\u'+char.charCodeAt(0).toString(16).padStart(4,'0'))
}
export function bindNativeReceipts(receiptFile:string,verdictFiles:readonly string[],names:readonly string[]=['mldr-3g-timed','mldr-3g-instrumented']){
 const root=realpathSync(dirname(receiptFile)),receiptData=regular(receiptFile,root),receipt=JSON.parse(receiptData.bytes.toString()),rows=receipt.rows??{}
 assert(stable(Object.keys(rows).sort())===stable([...names].sort()),'expected exact named native rows')
 const batch=rows[names[0]!]!.batch
 assert(present(batch)&&/^[A-Za-z0-9_-]+$/.test(batch),'invalid batch identity')
 const cleanup=receipt.cleanup,c=cleanup?.batches?.[batch]
 assert(cleanup?.cleanup_complete===true&&cleanup?.cleanup_validation?.[batch]===true,'cleanup validation absent')
 assert(c?.batch===batch&&c.ok===true&&c.complete===true&&c.cleanup_complete===true&&c.admission_closed===true&&c.journals_retained===true&&c.strict_once===true&&c.max_attempts===1,'incomplete strict close')
 assert(Array.isArray(c.pending)&&c.pending.length===0&&Array.isArray(c.unlaunched)&&c.unlaunched.length===0,'pending or unlaunched attempts')
 assert(Array.isArray(c.attempts)&&c.attempts.length===names.length&&new Set(c.attempts.map((a:any)=>a.name)).size===names.length,'wrong cleanup attempt set')
 const journal=regular(join(root,'custody',batch+'.jsonl'),root),journalHash=hash(journal.bytes),events=journal.bytes.toString().trim().split('\n').map(line=>JSON.parse(line))
 assert(events.length>0&&events.every((e:any,i:number)=>Number.isInteger(e.sequence)&&(i===0||e.sequence>events[i-1].sequence)),'invalid custody event sequence')
 const closes=events.filter((e:any)=>e.event==='close_receipt')
 assert(closes.length===1&&closes[0].cleanup_complete===true&&hex(closes[0].receipt_sha256),'missing positive close event')
 assert(hash(Buffer.from(nativeCloseJson(c)))===closes[0].receipt_sha256,'cleanup object does not match native close receipt hash')
 const verdicts:any[]=[],evidence:any[]=[]
 for(let i=0;i<names.length;i++){
  const name=names[i]!,row=rows[name],attempt=c.attempts.find((a:any)=>a.name===name)
  assert(row?.name===name&&row.run_name===name&&row.status==='SUCCEEDED'&&row.code===0&&row.terminal===true&&row.identity_unavailable===false&&row.strict_once===true&&row.max_attempts===1&&row.attempt===1&&row.attempts===1&&row.batch===batch,'invalid successful strict row: '+name)
  for(const key of ['vm','boot_id','launch_identity'])assert(present(row[key])&&attempt?.[key]===row[key],'cleanup identity mismatch '+name+':'+key)
  assert(attempt.run_name===row.run_name&&attempt.attempt===1&&attempt.cleanup_complete===true,'attempt not completely reaped: '+name)
  assert(row.placement?.vm===row.vm&&row.placement?.boot_id===row.boot_id&&row.placement?.attempt===1,'placement identity mismatch: '+name)
  assert(row.placement.type==='xlarge'&&present(row.placement.cpu)&&row.placement.vcpus===16&&row.placement.exclusive===true&&row.placement.co_tenants===0,'exclusive 16-CPU placement not observed: '+name)
  // Serving79a9 has no per-job memory enforcement. Bind observations below,
  // not nonexistent resource_verified/cgroup enforcement receipts.

  const runtime=row.runtime_verification,bun=runtime?.observed?.bun
  assert(row.runtime_verified===true&&runtime?.protocol===1&&runtime.ok===true&&runtime.required?.bun?.version==='1.4.3'&&runtime.required.bun.sha256==='7ce7d6b654eddeec20afddf2396317fba6dc19ab52788a27e894e1806bf8f24b'&&bun?.version==='1.4.3'&&bun.sha256===runtime.required.bun.sha256&&bun.hash_matches===true&&bun.version_matches===true&&bun.stable===true,'runtime pin not verified: '+name)
  assert(row.custody?.batch===batch&&row.custody.max_attempts===1&&row.custody.sha256===journalHash&&row.custody.event_count===events.length&&stable(row.custody.events)===stable(events),'custody journal not bound: '+name)
  assert(cleanup.custody?.[batch]?.sha256===journalHash,'close journal not retained')
  const dir=join(root,name+'.files')
  assert(regular(join(dir,'cpu-model.txt'),dir).bytes.toString().includes(row.placement.cpu),'native/worker CPU model observations differ: '+name)
  assert(realpathSync(dir)===dir&&realpathSync(row.output_files_dir)===dir,'wrong output directory: '+name)
  const manifest=regular(row.output_files_manifest,root),ref=row.output_files_ref
  assert(relative(join(root,'.payloads'),manifest.path).split(sep)[0]!=='..'&&hex(ref?.sha256)&&ref.version===1&&ref.format==='json'&&Number.isSafeInteger(ref.bytes)&&ref.bytes===manifest.bytes.length&&ref.sha256===hash(manifest.bytes),'native output manifest not bound: '+name)
  const entries=JSON.parse(manifest.bytes.toString()),seen=new Set<string>(),artifacts:any[]=[]
  assert(Array.isArray(entries)&&entries.length>0,'invalid output manifest')
  let supplied:Buffer|undefined
  for(const entry of entries){
   assert(present(entry.path)&&!entry.path.includes('\\')&&!entry.path.includes('\0')&&!posix.isAbsolute(entry.path)&&posix.normalize(entry.path)===entry.path&&!entry.path.split('/').some((p:string)=>p==='.'||p==='..'||p==='')&&!seen.has(entry.path),'invalid or duplicate output path')
   seen.add(entry.path)
   assert(entry.version===1&&entry.format==='file'&&hex(entry.sha256)&&Number.isSafeInteger(entry.bytes)&&entry.bytes>=0,'invalid output entry')
   const path=join(dir,entry.path),actual=realpathSync(path),rel=relative(dir,actual)
   assert(lstatSync(path).isFile()&&rel!==''&&!rel.startsWith('..'+sep)&&!isAbsolute(rel),'artifact escapes native directory')
   assert(lstatSync(path).size===entry.bytes,'artifact length mismatch')
   const fd=openSync(path,'r'),digest=createHash('sha256'),buffer=Buffer.alloc(65536)
   try{for(;;){const n=readSync(fd,buffer,0,buffer.length,null);if(!n)break;digest.update(buffer.subarray(0,n))}}finally{closeSync(fd)}
   assert(digest.digest('hex')===entry.sha256,'output bytes do not match native manifest: '+name+'/'+entry.path)
   const file={path:actual}
   artifacts.push({path:entry.path,sha256:entry.sha256,bytes:entry.bytes})
   if(entry.path==='verdict.json'){
    assert(regular(verdictFiles[i]!,root).path===file.path,'supplied verdict is not native exported file: '+name)
    supplied=regular(file.path,dir).bytes
   }
  }
  for(const required of ['verdict.json','identity.json','root-initial.json','root-final-before-unwind.json','root-settled.json','source-before.json','source-postinstall.json','source-after.json','resources-before.json','resources-after.json','resource-exits.json','worker-cleanup.json','ARTIFACTS.sha256','measurement-total.json','replay-declines.json','CONFIG.json','SEAL.json','INPUTS.sha256','AUTHORIZATION.json'])assert(seen.has(required),'required native artifact absent: '+name+'/'+required)
  const scratch=JSON.parse(regular(join(dir,'worker-cleanup.json'),dir).bytes.toString());assert(scratch.scratchRemoved===true&&scratch.exitCode===0,'worker scratch not cleaned: '+name)
  if(name==='mldr-3g-instrumented')for(const required of ['trace-result.json','trace-replay.json','measurement-rows.json','measurement-rows-replayed.json'])assert(seen.has(required),'instrumented artifact absent: '+required)
  assert(supplied!==undefined,'verdict missing from native manifest: '+name)
  const verdict=JSON.parse(supplied.toString()),diagnosticBytes=regular(join(dir,'replay-declines.json'),dir).bytes
  assert(diagnosticBytes.length<=2097152,'replay diagnostic aggregate bound')
  const diagnostic=JSON.parse(diagnosticBytes.toString())
  assert(diagnostic.schema==='count-replay-diagnostic/v1'&&diagnostic.proofAuthority===false&&diagnostic.identityCapture?.complete===true,'wrong replay diagnostic schema')
  assert(diagnostic.identity.sourceCommit===verdict.identity.sourceCommit&&diagnostic.identity.sourceTree===verdict.identity.sourceTree&&diagnostic.identity.mode===verdict.mode,'replay diagnostic identity mismatch')
  assert(diagnostic.identity.sealSHA256===hash(regular(join(dir,'SEAL.json'),dir).bytes)&&diagnostic.identity.inputIndexSHA256===hash(regular(join(dir,'INPUTS.sha256'),dir).bytes),'replay diagnostic input binding')
  assert(Array.isArray(diagnostic.events)&&diagnostic.events.length<=16&&Array.isArray(diagnostic.repairHistory)&&diagnostic.repairHistory.length<=64,'replay diagnostic record bounds')
  assert(diagnostic.accounting?.chargedToProofUnits===false&&diagnostic.accounting?.timingNeutralClaim===false,'diagnostic overhead disclosure absent')
  verdicts.push(verdict)
  const resourceExits=JSON.parse(regular(join(dir,'resource-exits.json'),dir).bytes.toString());assert(resourceExits.before===0&&resourceExits.after===0,'resource observation incomplete: '+name)
  const resources=validateResourcePair(JSON.parse(regular(join(dir,'resources-before.json'),dir).bytes.toString()),JSON.parse(regular(join(dir,'resources-after.json'),dir).bytes.toString()),name==='mldr-3g-timed'?'timed':'instrumented',scratch.workerPid)
  evidence.push({name,resources,vm:row.vm,boot_id:row.boot_id,launch_identity:row.launch_identity,manifestSha256:ref.sha256,artifacts})
 }
 assert(new Set(c.attempts.map((a:any)=>a.launch_identity)).size===names.length,'reused launch identity')
 assert(new Set(c.attempts.map((a:any)=>a.vm)).size===names.length,'distinct VM requirement failed')
 return {control:verdicts[0],treatment:verdicts[1],evidence:{receiptSha256:hash(receiptData.bytes),batch,journalSha256:journalHash,closeReceiptSha256:closes[0].receipt_sha256,attempts:evidence}}
}

export function bindPairReceipts(receiptFile:string,verdictFiles:readonly string[]){return bindNativeReceipts(receiptFile,verdictFiles,['mldr-3g-timed','mldr-3g-instrumented'])}
