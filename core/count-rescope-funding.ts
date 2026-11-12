// Caller-side authority only: no reservation, grant, root replacement or clock
// conversion. The rescope helper itself remains default-deny. An unchecked
// retained offer is still subject to conservative S and final native checking.
import {type CountRescopeOptions} from './count-proof-rescope.ts'
import {type WorkLedger,workLedger} from './work-admission.ts'
import {compareWork,zeroWork} from './work-amount.ts'
export function countRescopeFunding(bank:WorkLedger=workLedger):CountRescopeOptions{
 const owner=bank.currentScope(),rootEpoch=bank.snapshot().rootEpoch
 return {
  retainUncheckedOffer:true,
  allowFullFallback:()=>{
   if(!owner||owner.kind==='root'||!bank.inBudget())return false
   const active=bank.snapshot()
   if(active.rootEpoch!==rootEpoch||!active.activeEndpoints.some(scope=>scope.id===owner.id))return false
   const left=bank.available()
   return left!==null&&compareWork(left,zeroWork)>0
  }
 }
}
