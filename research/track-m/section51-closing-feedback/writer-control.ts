// Focused production counted-family control, never the full MLDR search.
import {mkdirSync,writeFileSync,openSync,writeSync,closeSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {rowCompositionFixture} from '../../../core/count-row-composition.fixture.ts'
import {admitCountedFamily,countsDump,countRecipeClosingCapture} from '../../../core/counts.ts'
import {countReplayDiagnostic} from '../../../core/count-replay-diagnostic.ts'
import {clock,fullRate,withBudget} from '../../../kernel/prove.ts'
import {checkCountedLaws,snapshotKernelTermState} from '../../../kernel/kernel.ts'
import {workLedger,type WorkAdmissionEvent} from '../../../core/work-admission.ts'
import {isCheckedReducedScope} from '../../../core/count-proof-scope.ts'
import {workAmount} from '../../../core/work-amount.ts'
import {installClosingCapture} from './capture.ts'
import {nativeMetadataFixture} from './native-metadata.fixture.ts'
const [mode,out]=process.argv.slice(2)
if(!['off','on','failed-write'].includes(mode!)||!out)throw Error('invalid writer control arguments')
mkdirSync(out,{recursive:true})
const signature=(value:unknown)=>JSON.stringify(value,(_key,value)=>typeof value==='bigint'?{bigint:String(value)}:value)
const bankFile=openSync(join(out,'bank-events.jsonl'),'wx'),bankHash=createHash('sha256')
let bankCount=0,bankBytes=0,bankBuffer='',bankBufferBytes=0
const flushBank=()=>{
 if(!bankBufferBytes)return
 const data=Buffer.from(bankBuffer);let offset=0
 while(offset<data.length){const written=writeSync(bankFile,data,offset,data.length-offset);if(written<=0)throw Error('bank stream short write');offset+=written}
 bankBuffer='';bankBufferBytes=0
}
const recordBank=(event:WorkAdmissionEvent)=>{
 const row=JSON.stringify(event)+'\n',bytes=Buffer.byteLength(row)
 bankHash.update(row);bankCount++;bankBytes+=bytes;bankBuffer+=row;bankBufferBytes+=bytes
 if(bankBufferBytes>=256*1024)flushBank()
}
const events:Record<string,unknown>[]=[],replayEvents:Record<string,unknown>[]=[]
countsDump.on=value=>{
 const e=value as Record<string,unknown>,row:Record<string,unknown>={}
 for(const key of ['phase','stage','law','recipe','reason','route','outcome','checked','members','supplierRepairUsed','at','units','end'])if(e[key]!==undefined)row[key]=e[key]
 events.push(row)
}
countReplayDiagnostic.on=e=>replayEvents.push({kind:e.kind,context:e.context,case:e.case,reason:e.reason,route:e.route,members:e.members})
let writerPath=out
if(mode==='failed-write'){writerPath=join(out,'not-a-directory');writeFileSync(writerPath,'fault injection')}
const uninstall=mode==='off'?undefined:installClosingCapture(writerPath,{fixture:'row-composition',mode:'parity'},()=>{})
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
try{
 workLedger.withTrace(recordBank,()=>withBudget(workAmount(25000000n),()=>{
  try{
   nativeFixture=nativeMetadataFixture(clock()+25000000/fullRate)
   const f=rowCompositionFixture()
   answer=admitCountedFamily(f.m,[f.law],f.family,new Set(),clock()+25000000/fullRate)
   checked=!!(answer.proven&&answer.proof&&checkCountedLaws(answer.m,answer.laws,answer.proof))
   fixtureStillChecked=isCheckedReducedScope(nativeFixture.scoped,nativeFixture.m,nativeFixture.family)
  }catch(e){error={name:e instanceof Error?e.name:'unknown',message:String(e)}}
  finally{final=workLedger.snapshot();privateFinal=workLedger.diagnosticCheckpoint()}
 }))
}finally{
 flushBank();closeSync(bankFile)
 countsDump.on=undefined;countReplayDiagnostic.on=undefined;countRecipeClosingCapture.on=originalCapture
}
const writer=uninstall?.()
const result={outcome:answer?{proven:answer.proven,laws:answer.laws.map((law:any)=>law.name),why:answer.why,checked,proofSHA256:answer.proof&&createHash('sha256').update(JSON.stringify(answer.proof)).digest('hex')}:null,error,final,privateFinal,settled:workLedger.snapshot(),privateSettled:workLedger.diagnosticCheckpoint(),events,replayEvents,
 bankStream:{records:bankCount,bytes:bankBytes,sha256:bankHash.digest('hex')},expectedNative:nativeFixture?.expected,fixtureStillChecked,
 writer:writer??null,captures,meterChanged,termsChanged}
writeFileSync(join(out,'control.json'),signature(result)+'\n')
