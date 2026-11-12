// Write-only closing snapshot. There is deliberately no loader or hydration API.
import {openSync,closeSync,writeFileSync,fsyncSync,mkdirSync,readFileSync,appendFileSync,unlinkSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {countRecipeClosingCapture,countsDump,type CountedRecipeClosingSnapshot} from '../../../core/counts.ts'
import {workLedger,BudgetExpired} from '../../../core/work-admission.ts'
import {completeWorkProfile} from '../../../core/work-profile.ts'
import {snapshotKernelTermState,snapshotKernelTermMemo} from '../../../kernel/kernel.ts'
import {atPoint,snapshotProofClock} from '../../../kernel/prove.ts'
import {WallExpired} from '../../../core/wall.ts'
import {proofOrigins} from '../../../core/lemma-cuts.ts'
import {snapshotTraceClockDepth} from '../../../core/trace-clock.ts'
import {countReplayDiagnostic} from '../../../core/count-replay-diagnostic.ts'
import {snapshotConditionalProofMark} from '../../../core/count-recovery/conditional-proof.ts'
import {snapshotCountScopeBinding} from '../../../core/count-proof-scope.ts'
import {writeGraphCapsule} from './graph-writer.ts'
export const capsulePrototypes={BudgetExpired:BudgetExpired.prototype,WallExpired:WallExpired.prototype}
const hash=(bytes:Uint8Array|string)=>createHash('sha256').update(bytes).digest('hex')
function durableJSON(path:string,value:unknown){
 const text=JSON.stringify(value)+'\n',fd=openSync(path,'wx')
 try{writeFileSync(fd,text);fsyncSync(fd)}finally{closeSync(fd)}
 return hash(text)
}
export function installClosingCapture(out:string,identity:unknown,phase:(name:string)=>void,options:{syncDirectory?:(path:string)=>void}={}){
 if(countRecipeClosingCapture.on)throw Error('closing capture already installed')
 let attempted=0,completed=0,failures=0
 const syncDirectory=options.syncDirectory??((path:string)=>{const fd=openSync(path,'r');try{fsyncSync(fd)}finally{closeSync(fd)}})
 const capture=(snapshot:CountedRecipeClosingSnapshot)=>{
  const ordinal=++attempted
  let completionPath:string|undefined
  try{
   phase('closing-capture')
   // Unsupported observations make this export incomplete, not the proof fail.
   if(!completeWorkProfile.enabled||atPoint.on!==undefined||!snapshot.reachAbsent)throw Error('unsupported closing runtime')
   const checkpoint=workLedger.diagnosticCheckpoint()
   if(checkpoint.leases.length||checkpoint.capacityBoundaries.length||checkpoint.notifying)throw Error('closing entry is not quiescent')
   const runtime={schema:'closing-runtime/v1',identity,
    flags:Object.fromEntries(Object.entries(process.env).filter(([key])=>key.startsWith('GDP_'))),
    fullAccounting:completeWorkProfile.enabled,lemmaCuts:process.env.GDP_COUNT_LEMMA_CUTS??null,
    atPointInstalled:false,proofOrigins:proofOrigins.enabled,countsObserver:countsDump.on!==undefined,replayObserver:countReplayDiagnostic.on!==undefined,
    cachePolicy:'native caches not restored; any future replay must prove fidelity separately'}
   const directory=join(out,`closing-entry-${String(ordinal).padStart(4,'0')}`)
   mkdirSync(directory,{recursive:false})
   const headerSHA256=durableJSON(join(directory,'runtime.json'),runtime),graph=join(directory,'graph')
   const data={snapshot,checkpoint,kernel:snapshotKernelTermState(),clock:snapshotProofClock(),traceDepth:snapshotTraceClockDepth(),runtime}
   writeGraphCapsule(graph,data,{prototypes:capsulePrototypes,metadata:object=>{
    const conditionalMark=snapshotConditionalProofMark(object),scopeBinding=snapshotCountScopeBinding(object),termId=snapshotKernelTermMemo(object),capacityRefusal=workLedger.capacityRefusal(object)
    return conditionalMark!==undefined||scopeBinding!==undefined||termId!==undefined||capacityRefusal!==undefined?{conditionalMark,scopeBinding,termId,capacityRefusal}:undefined
   }})
   const graphManifestSHA256=hash(readFileSync(join(graph,'manifest.json')))
   completionPath=join(directory,'CAPTURE.json')
   durableJSON(completionPath,{schema:'closing-capture/v1',complete:true,ordinal,headerSHA256,graphManifestSHA256,
    originalLedger:checkpoint.ledger,qualification:false,WClaim:false,writerOnly:true})
   for(const dir of [graph,directory,out])syncDirectory(dir)
   completed++
  }catch(error){
   failures++
   if(completionPath)try{unlinkSync(completionPath)}catch{/* never retain an acknowledged complete marker on export failure */}
   try{appendFileSync(join(out,'closing-capture-errors.jsonl'),JSON.stringify({ordinal,error:String(error),complete:false})+'\n')}catch{/* output failure cannot replace native result */}
  }finally{try{phase('closing')}catch{/* phase telemetry cannot replace native result */}}
 }
 countRecipeClosingCapture.on=capture
 return ()=>{
  if(countRecipeClosingCapture.on===capture)countRecipeClosingCapture.on=undefined
  else failures++
  return {attempted,completed,failures,writerOnly:true}
 }
}
