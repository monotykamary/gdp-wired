// Focused production counted-family control, never the full MLDR search.
import {mkdirSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {MAX_BANK_BYTES} from './bank-event-recorder.ts'
import {n,same,x} from '../../../core/machine.ts'
import {selectedCountStrategies} from '../../../core/count-strategies.ts'
import {rowCompositionFixture} from '../../../core/count-row-composition.fixture.ts'
import {admitCountedFamily,countsDump,countRecipeClosingCapture} from '../../../core/counts.ts'
import {countReplayDiagnostic} from '../../../core/count-replay-diagnostic.ts'
import {clock,fullRate,withBudget} from '../../../kernel/prove.ts'
import {checkCountedLaws,snapshotKernelTermState} from '../../../kernel/kernel.ts'
import {workLedger,type WorkAdmissionEvent,type WorkAdmissionSnapshot} from '../../../core/work-admission.ts'
import {workKeys} from '../../../core/work-kinds.ts'
import {isCheckedReducedScope} from '../../../core/count-proof-scope.ts'
import {workAmount,workFromExact,workSub,exactRaw} from '../../../core/work-amount.ts'
import {installClosingCapture} from './capture.ts'
import {nativeMetadataFixture} from './native-metadata.fixture.ts'
const [mode,out]=process.argv.slice(2)
if(!['off','on','failed-write'].includes(mode!)||!out)throw Error('invalid writer control arguments')
mkdirSync(out,{recursive:true})
const signature=(value:unknown)=>JSON.stringify(value,(_key,value)=>typeof value==='bigint'?{bigint:String(value)}:value)
// Main's compact-evidence mode: retain no event stream and never pass digest
// state to native receipts. The unchanged 128MiB cap still governs full-file
// recording in bank-event-recorder.ts; it is not a cumulative hashing limit.
function streamDigest<T>(validate:(value:T)=>void=()=>{},complete:()=>void=()=>{}){
 const hash=createHash('sha256');let records=0,bytes=0,failed=false,failure:unknown,result:{records:number,bytes:number,sha256:string}|undefined
 const record=(value:T)=>{
  if(failed)throw failure
  try{if(result)throw Error('digest already finalized');validate(value);const serialized=signature(value);if(typeof serialized!=='string')throw Error('digest serialization produced no row');const row=serialized+'\n';hash.update(row);records++;bytes+=Buffer.byteLength(row)}
  catch(error){if(!failed){failed=true;failure=error}throw failure}
 }
 const finish=()=>{
  if(failed)throw failure
  try{if(!result){complete();result={records,bytes,sha256:hash.digest('hex')}}return result}
  catch(error){if(!failed){failed=true;failure=error}throw failure}
 }
 return {record,finish}
}
let firstSequence=0,lastSequence=0,depth=0
const bank=streamDigest<WorkAdmissionEvent>(event=>{
 if(!Number.isSafeInteger(event.sequence)||event.sequence<=0||
  (lastSequence?event.sequence!==lastSequence+1:event.kind!=='trace-start')||
  (lastSequence&&depth===0))throw Error('bank stream sequence discontinuity')
 depth+=event.kind==='trace-start'?1:event.kind==='trace-end'?-1:0
 if(depth<0)throw Error('bank stream trace ended without a start')
 if(!firstSequence)firstSequence=event.sequence
 lastSequence=event.sequence
},()=>{if(!firstSequence||depth!==0)throw Error('bank stream lacks a complete trace')})
const stages=streamDigest<Record<string,unknown>>(),replay=streamDigest<Record<string,unknown>>()
let closingStages=0
countsDump.on=value=>{
 const e=value as Record<string,unknown>,row:Record<string,unknown>={}
 for(const key of ['phase','stage','law','recipe','reason','route','outcome','checked','members','supplierRepairUsed','at','units','end'])if(e[key]!==undefined)row[key]=e[key]
 if(e.phase==='count-recipe-closing')closingStages++
 stages.record(row)
}
countReplayDiagnostic.on=e=>replay.record({kind:e.kind,context:e.context,case:e.case,reason:e.reason,route:e.route,members:e.members})
let writerPath=out
if(mode==='failed-write'){writerPath=join(out,'not-a-directory');writeFileSync(writerPath,'fault injection')}
const uninstall=mode==='off'?undefined:installClosingCapture(writerPath,{fixture:'bounded-row-agreement',mode:'parity'},()=>{})
const originalCapture=countRecipeClosingCapture.on
let meterChanged=false,termsChanged=false,captures=0,nativeFixture:ReturnType<typeof nativeMetadataFixture>|undefined
if(originalCapture)countRecipeClosingCapture.on=snapshot=>{
 captures++
 const before=signature(workLedger.diagnosticCheckpoint()),terms=snapshotKernelTermState()
 // Test-only additional graph roots, not replacements for production inputs.
 const captured={...snapshot,nativeFixture};originalCapture(captured)
 meterChanged ||= signature(workLedger.diagnosticCheckpoint())!==before
 const after=snapshotKernelTermState()
 termsChanged ||= after.terms.length!==terms.terms.length||after.terms.some((term,i)=>term!==terms.terms[i])||JSON.stringify(after.identities)!==JSON.stringify(terms.identities)
}
let answer:any,checked=false,error:unknown,initial:WorkAdmissionSnapshot|undefined,final:WorkAdmissionSnapshot|undefined,fixtureStillChecked=false
let bankStream:ReturnType<typeof bank.finish>|undefined,stageSequence:ReturnType<typeof stages.finish>|undefined,replaySequence:ReturnType<typeof replay.finish>|undefined,writer:ReturnType<NonNullable<typeof uninstall>>|undefined
try{
 workLedger.withTrace(bank.record,()=>withBudget(workAmount(25000000n),()=>{
  initial=workLedger.snapshot()
  try{
   nativeFixture=nativeMetadataFixture(clock()+25000000/fullRate)
   // Exercise real structural selection, ordinary fallback and final native
   // closing, not the unrelated three-operation/count-supplier search. The
   // fixed operation is identity on the row/guard; no producer is mocked.
   const base=rowCompositionFixture()
   const f={...base,m:{...base.m,counts:{},assume:same(x('mode'),n(0))},family:[base.law]}
   if(!selectedCountStrategies(f.m,f.family).includes(f.law))throw Error('bounded row fixture was not structurally selected')
   answer=admitCountedFamily(f.m,[f.law],f.family,new Set(),clock()+25000000/fullRate)
   checked=!!(answer.proven&&answer.proof&&checkCountedLaws(answer.m,answer.laws,answer.proof))
   fixtureStillChecked=isCheckedReducedScope(nativeFixture.scoped,nativeFixture.m,nativeFixture.family)
  }catch(e){error={name:e instanceof Error?e.name:'unknown',message:String(e)}}
  finally{final=workLedger.snapshot()}
 }))
}finally{
 countsDump.on=undefined;countReplayDiagnostic.on=undefined;countRecipeClosingCapture.on=originalCapture
 try{writer=uninstall?.()}finally{
  // Outside native catches: hashing/sequence failures cannot produce a report.
  bankStream=bank.finish();stageSequence=stages.finish();replaySequence=replay.finish()
 }
}
if(!bankStream||!stageSequence||!replaySequence||!initial?.rootBaseline||!final)throw Error('compact evidence not finalized')
const completed=final
if(workKeys.length!==26||Object.keys(completed.counters).length!==26)throw Error('incomplete counter vector')
const counters=Object.fromEntries(workKeys.map(key=>[key,completed.counters[key]]))
const countedUnits=exactRaw(workSub(workFromExact(completed.actual),workFromExact(initial.rootBaseline.actual)))
const certificateHashes=(certs:Record<string,unknown>)=>Object.fromEntries(Object.entries(certs).map(([name,cert])=>[name,createHash('sha256').update(JSON.stringify(cert)).digest('hex')]))
const certificateSHA256s={admitted:certificateHashes(answer?.proof?.certs??{}),metadata:certificateHashes(nativeFixture?.scoped.proof.certs??{})}
const settled=workLedger.snapshot(),settledClean=settled.activeEndpoints.length===0&&settled.rootBaseline===null&&settled.effectiveEnd===null&&settled.reserved.numerator==='0'
const result={evidenceMode:'streaming-digest/v1',materializedEvidenceLimit:MAX_BANK_BYTES,
 outcome:answer?{proven:answer.proven,laws:answer.laws.map((law:any)=>law.name),why:answer.why,checked,proofSHA256:answer.proof&&createHash('sha256').update(JSON.stringify(answer.proof)).digest('hex')}:null,error,
 counters,countedUnits,certificateSHA256s,stageSequence,replaySequence,closingStages,settledClean,
 bankStream:{...bankStream,firstSequence,lastSequence,materialized:false,retainedBytes:0},expectedNative:nativeFixture?.expected,fixtureStillChecked,
 writer:writer??null,captures,meterChanged,termsChanged}
writeFileSync(join(out,'control.json'),signature(result)+'\n')
