import {expect,test} from 'bun:test'
import {observeEval} from './work-observe.ts'
import {withEvaluationAdmission} from './evaluation-admission.ts'
import {completeWorkProfile} from './work-profile.ts'
import {runtimeWall} from './runtime-wall.ts'
import {rawWork,workKeys} from './work-meter.ts'
import {coreMeter} from './meter.ts'
import {admittedWork,startWork,withAdmittedChunk,workLedger} from './work-admission.ts'
import {compareWork,workAdd,workSub,workMultiply,workAmount} from './work-amount.ts'
import {BudgetExpired,fullWork} from '../kernel/prove.ts'
import {withBudget} from './wall.ts'
const full=completeWorkProfile.enabled?test:test.skip
test('scoped evaluation counts are unchanged without an active budget',()=>{
 const before=rawWork().evals
 withEvaluationAdmission(()=>{for(let i=0;i<513;i++)observeEval()})
 expect(rawWork().evals-before).toBe(513)
})
full('ordinary interpreter visits use exact starts with no numeric side-credit hook',()=>{
 const prior=runtimeWall.admit;let calls=0
 runtimeWall.admit=(units,phase)=>{calls++;prior?.(units,phase)}
 const start=admittedWork(),before=rawWork().evals
 try{withBudget(100000,()=>withEvaluationAdmission(()=>{for(let i=0;i<1024;i++)observeEval()}))}finally{runtimeWall.admit=prior}
 expect(rawWork().evals-before).toBe(1024)
 expect(compareWork(workSub(admittedWork(),start),workMultiply(workLedger.weights.evals,workAmount(1024n)))).toBe(0)
 expect(calls).toBe(0)
})
full('zero and near-endpoint budgets refuse before another evaluation',()=>{
 let before=rawWork().evals
 expect(()=>withBudget(0,()=>withEvaluationAdmission(()=>observeEval()))).toThrow(BudgetExpired)
 expect(rawWork().evals).toBe(before)
 before=rawWork().evals;const weight=completeWorkProfile.weights.evals
 expect(()=>withBudget(2*weight,()=>withEvaluationAdmission(()=>{observeEval();observeEval();observeEval()}))).toThrow(BudgetExpired)
 expect(rawWork().evals-before).toBe(2)
})
full('nested and exceptional scopes do not retain a stale evaluation credit',()=>{
 withBudget(1000,()=>withEvaluationAdmission(()=>{observeEval();expect(()=>withEvaluationAdmission(()=>{observeEval();throw Error('unwind')})).toThrow('unwind');observeEval()}))
 const before=rawWork().evals
 expect(()=>withBudget(0,()=>withEvaluationAdmission(()=>observeEval()))).toThrow(BudgetExpired)
 expect(rawWork().evals).toBe(before)
})
full('a large compiled charge is admitted as one exact block',()=>{
 const before=rawWork().evals,weight=completeWorkProfile.weights.evals
 expect(()=>withBudget(weight*9,()=>withEvaluationAdmission(()=>observeEval(10)))).toThrow(BudgetExpired)
 expect(rawWork().evals).toBe(before)
})
full('unscoped evaluator fallback refuses before charging past the endpoint',()=>{
 const weight=completeWorkProfile.weights.evals
 for(const W of [0,weight,2*weight]){
  const before=rawWork().evals,start=fullWork()
  expect(()=>withBudget(W,()=>{for(let i=0;i<3;i++)observeEval()})).toThrow(BudgetExpired)
  expect(rawWork().evals-before).toBe(W/weight)
  expect(fullWork()-start).toBeLessThanOrEqual(W)
 }
})
full('every other raw bucket invalidates unused evaluator permission',()=>{
 for(const key of workKeys.filter(key=>key!=='evals')){
  const cost=workAdd(workLedger.weights.evals,workLedger.weights[key]),start=admittedWork()
  withBudget(workAdd(cost,workLedger.weights.evals),()=>withAdmittedChunk('evals',2,lease=>{
   lease.start();startWork(key,1,'foreign evaluator control');expect(()=>lease.start()).toThrow(BudgetExpired)
  }))
  expect(compareWork(workSub(admittedWork(),start),cost),key).toBe(0)
  expect(workLedger.reserved().num).toBe(0n)
 }
})
full('direct evaluator writes and smaller nested budgets invalidate permission',()=>{
 const weight=completeWorkProfile.weights.evals,before=rawWork().evals
 expect(()=>withBudget(1000*weight,()=>withEvaluationAdmission(()=>{observeEval();coreMeter.evals+=999;observeEval()}))).toThrow('unadmitted work counter mutation')
 expect(rawWork().evals-before).toBe(1)
 const nested=rawWork().evals
 withBudget(1000*weight,()=>withEvaluationAdmission(()=>{observeEval();expect(()=>withBudget(0,()=>observeEval())).toThrow(BudgetExpired);observeEval()}))
 expect(rawWork().evals-nested).toBe(2)
})
full('a caught request refusal cannot grant credit or poison legal remaining work',()=>{
 const prior=runtimeWall.admit,before=rawWork().evals
 withBudget(1000,()=>withEvaluationAdmission(()=>{
  observeEval();expect(()=>runtimeWall.admit!(1001,'foreign refusal')).toThrow(BudgetExpired);observeEval()
 }))
 expect(rawWork().evals-before).toBe(2)
 expect(workLedger.reserved().num).toBe(0n);expect(runtimeWall.admit).toBe(prior)
})
