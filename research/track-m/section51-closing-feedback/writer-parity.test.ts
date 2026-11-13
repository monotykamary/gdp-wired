import {expect,test} from 'bun:test'
import {mkdtempSync,rmSync,readFileSync,readdirSync,statSync,mkdirSync,cpSync,writeFileSync,existsSync,writeSync,closeSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {gunzipSync,gzipSync} from 'node:zlib'
import {createBankEventRecorder,MAX_BANK_BYTES} from './bank-event-recorder.ts'
import {workLedger,type WorkAdmissionEvent} from '../../../core/work-admission.ts'
import {workKeys} from '../../../core/work-kinds.ts'
import {join,dirname} from 'node:path'
import {tmpdir} from 'node:os'
import {fileURLToPath} from 'node:url'
import {spawnSync} from 'node:child_process'
import {readGraphCapsule} from './graph-reader.test-support.ts'
import {capsulePrototypes} from './capture.ts'
import {isCheckedReducedScope} from '../../../core/count-proof-scope.ts'
function compareBankStreams(a:string,b:string){
 const options={maxOutputLength:MAX_BANK_BYTES}
 const x=gunzipSync(readFileSync(a),options),y=gunzipSync(readFileSync(b),options)
 expect(x.equals(y)).toBe(true)
 let records=0,firstSequence=0,lastSequence=0,depth=0,cursor=0
 while(cursor<x.length){
  const end=x.indexOf(10,cursor)
  if(end<0)throw Error('bank stream has an incomplete JSON row')
  const event=JSON.parse(x.toString('utf8',cursor,end));cursor=end+1
  if(event.version!=='strict-work-v1'||!Number.isSafeInteger(event.sequence)||event.sequence<=0||
   (records?event.sequence!==lastSequence+1:event.kind!=='trace-start')||
   (records&&depth===0))throw Error('bank stream sequence discontinuity')
  depth+=event.kind==='trace-start'?1:event.kind==='trace-end'?-1:0
  if(depth<0)throw Error('bank stream trace ended without a start')
  if(!records)firstSequence=event.sequence
  lastSequence=event.sequence;records++
 }
 if(!records||depth!==0)throw Error('bank stream lacks a complete trace')
 return {bytes:x.length,sha256:createHash('sha256').update(x).digest('hex'),records,firstSequence,lastSequence}
}
const inRecorderDirectory=(run:(directory:string)=>void)=>{
 const directory=mkdtempSync(join(tmpdir(),'bank-recorder-'))
 try{run(directory)}finally{rmSync(directory,{recursive:true,force:true})}
}
const bankEvent=(sequence:number,kind:WorkAdmissionEvent['kind']):WorkAdmissionEvent=>({...workLedger.snapshot(),sequence,kind})
const failureOf=(run:()=>unknown):unknown=>{try{run()}catch(error){return error}throw Error('expected recorder failure')}

test('a caught tiny-cap overflow permanently prevents a successful control report',()=>inRecorderDirectory(directory=>{
 const first=bankEvent(11,'trace-start'),last=bankEvent(13,'trace-end')
 const maxBytes=Buffer.byteLength(JSON.stringify(first)+'\n'+JSON.stringify(last)+'\n')
 const file=join(directory,'events.gz'),control=join(directory,'control.json')
 const recorder=createBankEventRecorder(file,{maxBytes,flushBytes:1})
 recorder.record(first)
 // Model a native caller catching the ordinary Error and trying to continue.
 const rejected=failureOf(()=>recorder.record({...bankEvent(12,'start'),site:'x'.repeat(maxBytes+1)}))
 expect(String(rejected)).toContain('complete-evidence bound')
 expect(failureOf(()=>recorder.record(last))).toBe(rejected)
 const accept=()=>{const summary=recorder.finish();writeFileSync(control,JSON.stringify(summary))}
 expect(failureOf(accept)).toBe(rejected)
 expect(failureOf(accept)).toBe(rejected)
 expect(existsSync(control)).toBe(false)
 // A fully readable prefix still must never qualify as a complete stream.
 expect(gunzipSync(readFileSync(file)).toString()).toBe(JSON.stringify(first)+'\n')
}))

for(const phase of ['serialize','compress','write','close','final-flush','non-error'] as const){
 test(`caught ${phase} failure stays latched through finalization`,()=>inRecorderDirectory(directory=>{
  const fault=phase==='non-error'?undefined:new Error('injected '+phase),file=join(directory,'events.gz')
  const fail=():never=>{throw fault}
  const options=phase==='compress'?{flushBytes:1,compress:fail}:
   phase==='write'?{flushBytes:1,write:fail}:
   phase==='close'?{close:(fd:number)=>{closeSync(fd);fail()}}:
   phase==='final-flush'||phase==='non-error'?{compress:fail}:{}
  const recorder=createBankEventRecorder(file,options),first=bankEvent(21,'trace-start'),last=bankEvent(22,'trace-end')
  let rejected:unknown
  if(phase==='serialize'){
   const cyclic:WorkAdmissionEvent&{cycle?:unknown}={...first};cyclic.cycle=cyclic
   rejected=failureOf(()=>recorder.record(cyclic))
  }else if(phase==='compress'||phase==='write'){
   rejected=failureOf(()=>recorder.record(first));expect(rejected).toBe(fault)
  }else{
   recorder.record(first);recorder.record(last)
   rejected=failureOf(()=>recorder.finish());expect(rejected).toBe(fault)
  }
  expect(failureOf(()=>recorder.record(last))).toBe(rejected)
  expect(failureOf(()=>recorder.finish())).toBe(rejected)
  expect(failureOf(()=>recorder.finish())).toBe(rejected)
 }))
}

test('concatenated gzip members retain every full event through partial writes',()=>inRecorderDirectory(directory=>{
 const file=join(directory,'events.gz'),events=[bankEvent(31,'trace-start'),{...bankEvent(32,'start'),site:'full payload: \n λ',requested:'19',granted:'17'},bankEvent(33,'trace-end')]
 let writes=0
 const recorder=createBankEventRecorder(file,{flushBytes:1,write:(fd,bytes,offset,length)=>{writes++;return writeSync(fd,bytes,offset,Math.min(length,17))}})
 for(const event of events)recorder.record(event)
 const summary=recorder.finish(),plain=events.map(event=>JSON.stringify(event)+'\n').join('')
 expect(recorder.finish()).toBe(summary)
 expect(writes).toBeGreaterThan(events.length)
 expect(gunzipSync(readFileSync(file)).toString()).toBe(plain)
 expect(gunzipSync(readFileSync(file)).toString().trimEnd().split('\n').map(row=>JSON.parse(row))).toEqual(events)
 expect(compareBankStreams(file,file)).toEqual({records:events.length,bytes:Buffer.byteLength(plain),sha256:summary.sha256,firstSequence:31,lastSequence:33})
 expect(summary.bytes).toBe(Buffer.byteLength(plain));expect(summary.storedBytes).toBe(statSync(file).size)
}))

test('decoded equality alone cannot accept an omitted sequence number',()=>inRecorderDirectory(directory=>{
 const file=join(directory,'gap.gz'),plain=[bankEvent(41,'trace-start'),bankEvent(43,'trace-end')].map(event=>JSON.stringify(event)+'\n').join('')
 writeFileSync(file,gzipSync(plain))
 expect(()=>compareBankStreams(file,file)).toThrow('sequence discontinuity')
}))

const here=dirname(fileURLToPath(import.meta.url)),flags=JSON.parse(readFileSync(join(here,'writer-flags.json'),'utf8'))
test('production native closing: writer off/on/failure has identical verdict, exact units and order',()=>{
 const root=mkdtempSync(join(tmpdir(),'closing-writer-parity-'))
 try{
  const env={...process.env};for(const key of Object.keys(env))if(key.startsWith('GDP_'))delete env[key];Object.assign(env,flags)
  const rows=new Map<string,any>()
  for(const mode of ['off','on','failed-write']){
   const out=join(root,mode),run=spawnSync(process.execPath,[join(here,'writer-control.ts'),mode,out],{env,timeout:60000,encoding:'utf8',maxBuffer:8*1024*1024})
   expect({status:run.status,signal:run.signal,error:run.error?.message,stderr:run.stderr}).toEqual({status:0,signal:null,error:undefined,stderr:''})
   const row=JSON.parse(readFileSync(join(out,'control.json'),'utf8'));rows.set(mode,row)
   expect(row.error).toBeUndefined();expect(row.outcome.checked).toBe(true)
   expect(row.meterChanged).toBe(false);expect(row.termsChanged).toBe(false);expect(row.fixtureStillChecked).toBe(true)
   expect(row.evidenceMode).toBe('streaming-digest/v1');expect(row.materializedEvidenceLimit).toBe(128*1024*1024)
   expect(row.closingStages).toBeGreaterThan(0);expect(row.settledClean).toBe(true)
   expect(Object.keys(row.counters)).toEqual([...workKeys]);expect(workKeys).toHaveLength(26)
   expect(BigInt(row.countedUnits.numerator)).toBeGreaterThan(0n);expect(BigInt(row.countedUnits.denominator)).toBeGreaterThan(0n)
   for(const certificates of [row.certificateSHA256s.admitted,row.certificateSHA256s.metadata]){
    expect(Object.keys(certificates).length).toBeGreaterThan(0)
    for(const hash of Object.values(certificates))expect(hash).toMatch(/^[a-f0-9]{64}$/)
   }
   expect(row.bankStream.records).toBeGreaterThan(0);expect(row.expectedNative.context.length).toBeGreaterThan(0)
   expect(row.bankStream.lastSequence-row.bankStream.firstSequence+1).toBe(row.bankStream.records)
   expect(row.bankStream.materialized).toBe(false);expect(row.bankStream.retainedBytes).toBe(0)
   for(const stream of [row.bankStream,row.stageSequence,row.replaySequence])expect(stream.sha256).toMatch(/^[a-f0-9]{64}$/)
   expect(row.stageSequence.records).toBeGreaterThan(0)
   expect(readdirSync(out).some(name=>/^bank-events\./.test(name))).toBe(false)
   for(const field of ['events','replayEvents','final','privateFinal','settled','privateSettled'])expect(Object.hasOwn(row,field)).toBe(false)
  }
  const pick=(row:any)=>({outcome:row.outcome,counters:row.counters,countedUnits:row.countedUnits,certificateSHA256s:row.certificateSHA256s,stageSequence:row.stageSequence,replaySequence:row.replaySequence,bankStream:row.bankStream,closingStages:row.closingStages,settledClean:row.settledClean,expectedNative:row.expectedNative,fixtureStillChecked:row.fixtureStillChecked})
  expect(pick(rows.get('on'))).toEqual(pick(rows.get('off')))
  expect(pick(rows.get('failed-write'))).toEqual(pick(rows.get('off')))
  expect(rows.get('on').captures).toBeGreaterThan(0)
  expect(rows.get('on').writer).toMatchObject({attempted:rows.get('on').captures,completed:rows.get('on').captures,failures:0,writerOnly:true})
  expect(rows.get('failed-write').writer.completed).toBe(0);expect(rows.get('failed-write').writer.failures).toBeGreaterThan(0)
  const captures=readdirSync(join(root,'on')).filter(name=>name.startsWith('closing-entry-'))
  expect(captures).toHaveLength(rows.get('on').captures)
  for(const name of captures){
   const dir=join(root,'on',name),complete=JSON.parse(readFileSync(join(dir,'CAPTURE.json'),'utf8')),metadata=new WeakMap<object,unknown>()
   expect(complete.complete).toBe(true)
   const data:any=readGraphCapsule(join(dir,'graph'),{prototypes:capsulePrototypes,restoreMetadata:(object,value)=>metadata.set(object,value)})
   expect(data.snapshot.reachAbsent).toBe(true);expect(data.snapshot.m).toBeDefined();expect(data.snapshot.set.length).toBeGreaterThan(0)
   expect(data.checkpoint.leases).toEqual([]);expect(data.checkpoint.capacityBoundaries).toEqual([]);expect(data.checkpoint.notifying).toBe(false)
   expect(data.checkpoint.ledger).toEqual(complete.originalLedger)
   expect(data.kernel.identities).toHaveLength(data.kernel.terms.length)
   expect(data.kernel.terms.length).toBeGreaterThan(0)
   const f=data.snapshot.nativeFixture,expected=rows.get('on').expectedNative
   expect(f).toBeDefined();expect(f.expected).toEqual(expected)
   const ordinal=Number(/^⟦([0-9]+)⟧$/.exec(expected.column)![1])
   expect(data.kernel.terms[ordinal]).toBe(f.term);expect(f.termAlias).toBe(f.term)
   expect(data.kernel.identities.some((entry:[string,number])=>entry[1]===ordinal)).toBe(true)
   expect((metadata.get(f.term) as any).termId).toBe(ordinal)
   const mark=(metadata.get(f.markTree) as any)?.conditionalMark
   expect(mark).toBeDefined();expect(mark.goal).toBe(f.markGoal);expect(mark.goal.name).toBe(expected.markGoalName)
   expect(mark.lemmas).toHaveLength(1);expect(mark.lemmas[0]).toBe(f.markLemmas[0]);expect(mark.lemmas[0].tree).toBe(f.markTree)
   expect(f.markTreeAlias).toBe(f.markTree);expect(f.holder.yes).toBe(f.holder.no);expect(f.holder.yes).toBe(f.markTree)
   const contains=(tree:any):boolean=>tree===f.markTree||('split'in tree&&(contains(tree.yes)||contains(tree.no)))
   expect(Object.values(f.scoped.proof.certs).some((cert:any)=>contains(cert.tree))).toBe(true)
   const binding=(metadata.get(f.scoped.checkedReduced) as any)?.scopeBinding
   expect(binding).toBeDefined();expect(binding.context.length).toBeGreaterThan(0)
   expect(binding.token).toBe(f.scoped.checkedReduced);expect(binding.context).toEqual(expected.context)
   expect(binding.problem).toBe(expected.problem);expect(binding.scope).toBe(expected.scope)
   expect(binding.laws.map((law:any)=>law.name)).toEqual(expected.lawNames)
   expect(binding.laws.every((law:any)=>f.family.includes(law))).toBe(true)
   expect(isCheckedReducedScope(f.scoped,f.m,f.family)).toBe(false) // data is never re-minted
   expect(data.runtime.flags).toEqual(flags);expect(data.runtime.lemmaCuts).toBeNull();expect(data.runtime.fullAccounting).toBe(true)
   for(const member of data.snapshot.controller.pass.states){expect(member.recipes).toBeDefined();for(const recipe of member.recipes)expect(typeof recipe.tickets.started).toBe('number')}
  }
 }finally{
  try{if(process.env.SUPERCOMPUTER_OUTPUT_DIR){const target=join(process.env.SUPERCOMPUTER_OUTPUT_DIR,'writer-parity');mkdirSync(target,{recursive:true});cpSync(root,target,{recursive:true})}}
  finally{rmSync(root,{recursive:true,force:true})}
 }
},200000)
