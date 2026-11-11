import {expect,test} from 'bun:test'
import {observeEval,withEvaluationAdmission} from './work-observe.ts'
import {completeWorkProfile} from './work-profile.ts'
import {runtimeWall} from './runtime-wall.ts'
import {rawWork} from './work-meter.ts'
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
