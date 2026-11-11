import {expect,test} from 'bun:test'
import {observeEval} from './work-observe.ts'
import {withEvaluationAdmission} from './evaluation-admission.ts'
import {completeWorkProfile} from './work-profile.ts'
import {runtimeWall} from './runtime-wall.ts'
import {rawWork,workKeys,legacyWeights} from './work-meter.ts'
import {coreMeter} from './meter.ts'
import {costs} from './solver.ts'
import {eprMeter} from '../kernel/epr.ts'
import {BudgetExpired,fullWork} from '../kernel/prove.ts'
import {withBudget} from './wall.ts'
const full=completeWorkProfile.enabled?test:test.skip
test('scoped evaluation counts are unchanged without an active budget',()=>{
 const before=rawWork().evals
 withEvaluationAdmission(()=>{for(let i=0;i<513;i++)observeEval()})
 expect(rawWork().evals-before).toBe(513)
})
full('ordinary interpreter batches reduce admission calls without granting units',()=>{
 const prior=runtimeWall.admit;let calls=0
 runtimeWall.admit=(units,phase)=>{calls++;prior?.(units,phase)}
 const start=fullWork(),before=rawWork().evals
 try{withBudget(100000,()=>withEvaluationAdmission(()=>{for(let i=0;i<1024;i++)observeEval()}))}finally{runtimeWall.admit=prior}
 expect(rawWork().evals-before).toBe(1024)
 expect(fullWork()-start).toBeCloseTo(1024*completeWorkProfile.weights.evals,6)
 expect(calls).toBeLessThan(20)
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
full('every other raw bucket invalidates evaluator permission',()=>{
 const weights=Object.fromEntries([...legacyWeights,...Object.entries(completeWorkProfile.weights)])
 for(const key of workKeys.filter(key=>key!=='evals')){
  const scale=Math.ceil(512/weights[key]!),W=completeWorkProfile.weights.evals+weights[key]!*scale+0.25
  const start=fullWork(),before=rawWork().evals
  expect(()=>withBudget(W,()=>withEvaluationAdmission(()=>{
   observeEval()
   if(key==='epr')eprMeter.n+=scale
   else if(key in coreMeter)(coreMeter as Record<string,number>)[key]!+=scale
   else (costs as Record<string,number>)[key]!+=scale
   observeEval()
  }))).toThrow(BudgetExpired)
  expect(rawWork().evals-before,key).toBe(1)
  expect(fullWork()-start,key).toBeLessThanOrEqual(W)
 }
})
full('direct evaluator writes and smaller nested budgets invalidate permission',()=>{
 const weight=completeWorkProfile.weights.evals,before=rawWork().evals
 expect(()=>withBudget(1000*weight,()=>withEvaluationAdmission(()=>{observeEval();coreMeter.evals+=999;observeEval()}))).toThrow(BudgetExpired)
 expect(rawWork().evals-before).toBe(1000)
 const nested=rawWork().evals
 withBudget(1000*weight,()=>withEvaluationAdmission(()=>{observeEval();expect(()=>withBudget(0,()=>observeEval())).toThrow(BudgetExpired);observeEval()}))
 expect(rawWork().evals-nested).toBe(2)
})
full('a caught admission refusal cannot spend cached evaluator permission',()=>{
 const prior=runtimeWall.admit,before=rawWork().evals
 expect(()=>withBudget(1000,()=>withEvaluationAdmission(()=>{
  observeEval();expect(()=>runtimeWall.admit!(1001,'foreign refusal')).toThrow(BudgetExpired);observeEval()
 }))).toThrow(BudgetExpired)
 expect(rawWork().evals-before).toBe(1)
 expect(runtimeWall.admit).toBe(prior)
})
