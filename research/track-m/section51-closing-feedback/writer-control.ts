// Focused production counted-family control, never the full MLDR search.
import {mkdirSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {createBankEventRecorder,type BankEventSummary} from './bank-event-recorder.ts'
import {n,same,x} from '../../../core/machine.ts'
import {selectedCountStrategies} from '../../../core/count-strategies.ts'
import {rowCompositionFixture} from '../../../core/count-row-composition.fixture.ts'
import {admitCountedFamily,countsDump,countRecipeClosingCapture} from '../../../core/counts.ts'
import {countReplayDiagnostic} from '../../../core/count-replay-diagnostic.ts'
import {clock,fullRate,withBudget} from '../../../kernel/prove.ts'
import {checkCountedLaws,snapshotKernelTermState} from '../../../kernel/kernel.ts'
import {workLedger} from '../../../core/work-admission.ts'
import {isCheckedReducedScope} from '../../../core/count-proof-scope.ts'
import {workAmount} from '../../../core/work-amount.ts'
import {installClosingCapture} from './capture.ts'
import {nativeMetadataFixture} from './native-metadata.fixture.ts'
const [mode,out]=process.argv.slice(2)
if(!['off','on','failed-write'].includes(mode!)||!out)throw Error('invalid writer control arguments')
mkdirSync(out,{recursive:true})
const signature=(value:unknown)=>JSON.stringify(value,(_key,value)=>typeof value==='bigint'?{bigint:String(value)}:value)
const bank=createBankEventRecorder(join(out,'bank-events.jsonl.gz'))
const events:Record<string,unknown>[]=[],replayEvents:Record<string,unknown>[]=[]
countsDump.on=value=>{
 const e=value as Record<string,unknown>,row:Record<string,unknown>={}
 for(const key of ['phase','stage','law','recipe','reason','route','outcome','checked','members','supplierRepairUsed','at','units','end'])if(e[key]!==undefined)row[key]=e[key]
 events.push(row)
}
countReplayDiagnostic.on=e=>replayEvents.push({kind:e.kind,context:e.context,case:e.case,reason:e.reason,route:e.route,members:e.members})
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
let answer:any,checked=false,error:unknown,final:unknown,privateFinal:unknown,fixtureStillChecked=false
let bankStream:BankEventSummary|undefined,writer:ReturnType<NonNullable<typeof uninstall>>|undefined
try{
 workLedger.withTrace(bank.record,()=>withBudget(workAmount(25000000n),()=>{
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
  finally{final=workLedger.snapshot();privateFinal=workLedger.diagnosticCheckpoint()}
 }))
}finally{
 countsDump.on=undefined;countReplayDiagnostic.on=undefined;countRecipeClosingCapture.on=originalCapture
 try{writer=uninstall?.()}finally{
  // Outside all native proof/trace catches: even a swallowed callback error
  // permanently rejects this stream before any control.json can be written.
  bankStream=bank.finish()
 }
}
if(!bankStream)throw Error('bank stream not finalized')
const result={outcome:answer?{proven:answer.proven,laws:answer.laws.map((law:any)=>law.name),why:answer.why,checked,proofSHA256:answer.proof&&createHash('sha256').update(JSON.stringify(answer.proof)).digest('hex')}:null,error,final,privateFinal,settled:workLedger.snapshot(),privateSettled:workLedger.diagnosticCheckpoint(),events,replayEvents,
 bankStream,expectedNative:nativeFixture?.expected,fixtureStillChecked,
 writer:writer??null,captures,meterChanged,termsChanged}
writeFileSync(join(out,'control.json'),signature(result)+'\n')
