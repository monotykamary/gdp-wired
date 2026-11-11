// Scoped admission for table work performed by the ordinary count model step.
// Protected readers and canonicalizers are unchanged. Credit is permission to
// do work, never a raw charge or an addition to the active budget.
import {coreMeter} from './meter.ts'
import {costs} from './solver.ts'
import {eprMeter} from '../kernel/epr.ts'
import {budgetEnd,inBudget} from './wall.ts'
import {rawWork,type RawWork} from './work-meter.ts'
import {completeWorkProfile} from './work-profile.ts'
import {runtimeWall} from './runtime-wall.ts'
import {tableAdmissionHook} from './table-admission-hook.ts'

// A cheap equality guard, not a weighted sum. Cached permission is usable only
// while every other raw bucket is unchanged. Interleaved work therefore cannot
// spend the same allowance twice; direct/raw table writes also invalidate it.
function sameOtherWork(w:RawWork):boolean{
 return w.fm===costs.fm&&w.fcells===costs.fcells&&w.plainRows===costs.plainRows
 &&w.values===costs.values&&w.copies===costs.copies&&w.edges===costs.edges
 &&w.scan===costs.scan&&w.pivotRows===costs.pivotRows&&w.unitRows===costs.unitRows
 &&w.unfoldRows===costs.unfoldRows&&w.goalNodes===costs.goalNodes&&w.translateRows===costs.translateRows
 &&w.checkSteps===coreMeter.checkSteps&&w.astNodes===coreMeter.astNodes&&w.evals===coreMeter.evals
 &&w.cubeTests===coreMeter.cubeTests&&w.ticks===coreMeter.ticks&&w.cdclNodes===costs.cdclNodes
 &&w.epr===eprMeter.n&&w.tinyNodes===coreMeter.tinyNodes&&w.tinyTerms===coreMeter.tinyTerms
 &&w.reachStates===coreMeter.reachStates&&w.reachEdges===coreMeter.reachEdges
 &&w.reachEvals===coreMeter.reachEvals&&w.reachCompiledEvals===coreMeter.reachCompiledEvals
}
export function withTableAdmission<T>(run:()=>T):T{
 if(!completeWorkProfile.enabled||!inBudget())return run()
 const previous={...tableAdmissionHook},priorAdmit=runtimeWall.admit
 previous.invalidate?.()
 let credit=0,end=budgetEnd(),other=rawWork(),expectedTables=coreMeter.tableCells
 const invalidate=()=>{credit=0}
 // Refusal or admission by another primitive cannot leave a stale permission.
 runtimeWall.admit=(units,phase)=>{invalidate();priorAdmit?.(units,phase)}
 tableAdmissionHook.invalidate=invalidate
 tableAdmissionHook.admit=count=>{
  if(!Number.isSafeInteger(count)||count<0)throw new RangeError('table work must be a nonnegative safe integer')
  if(end!==budgetEnd()||expectedTables!==coreMeter.tableCells||!sameOtherWork(other))credit=0
  if(credit<count){
   const weight=completeWorkProfile.weights.tableCells
   const maximum=Math.max(count,Math.max(1,Math.min(256,Math.floor(256/weight))))
   const block=(runtimeWall.remaining?.()??Infinity)>=maximum*weight?maximum:count
   runtimeWall.admit?.(block*weight,'count reader tables')
   credit=block;other=rawWork();end=budgetEnd()
  }
  credit-=count;expectedTables=coreMeter.tableCells+count
 }
 try{return run()}finally{
  credit=0;tableAdmissionHook.admit=previous.admit;tableAdmissionHook.invalidate=previous.invalidate
  runtimeWall.admit=priorAdmit;previous.invalidate?.()
 }
}
