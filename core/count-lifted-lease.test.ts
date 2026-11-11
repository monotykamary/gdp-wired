import {expect,test} from 'bun:test'
import {liftedLeaseOptions,liftedWorkLeaseBudget,withLiftedCase,withLiftedLeaf,type LiftedWorkSlice} from './count-lifted-budget.ts'
import {BudgetExpired,startWork,withWorkAdmissionTrace,workAdmissionSnapshot,workLedger} from './work-admission.ts'
import {compareWork,workAdd,workAmount,workFromExact,workShare} from './work-amount.ts'
import {completeWorkProfile} from './work-profile.ts'
const full=completeWorkProfile.enabled?test:test.skip
full('original rational grant is split once, without a clock or remaining-share conversion',()=>{
 const original=workAmount(9007199254740993n,7n),overrides={'op:2':workAmount(17n,9n)}
 const budget=liftedWorkLeaseBudget(original,{cases:overrides})
 expect(compareWork(budget.lease!.leaf,workShare(original,1n,120n))).toBe(0)
 expect(compareWork(budget.lease!.operation,workShare(original,1n,30n))).toBe(0)
 overrides['op:2']=workAmount(999n)
 expect(compareWork(budget.lease!.cases['op:2']!,workAmount(17n,9n))).toBe(0)
 expect(budget.leafUnits).toBe(Infinity)
})
full('exact case and leaf expose stable keys and their actual scope IDs',()=>{
 const seen:LiftedWorkSlice[]=[],budget=liftedWorkLeaseBudget(workAmount(120000n),{observe:s=>seen.push(s)})
 withWorkAdmissionTrace(event=>{for(const endpoint of event.activeEndpoints)expect(compareWork(workAdd(workFromExact(event.actual),workFromExact(event.reserved)),workFromExact(endpoint.end))).toBeLessThanOrEqual(0)},()=>workLedger.withBudget(workAmount(1000000n),()=>{
  withLiftedCase(0,budget,false,'op:2',until=>{
   expect(until).toBe(Infinity)
   expect(workAdmissionSnapshot().activeEndpoints.at(-1)!.id).toBe(seen.at(-1)!.scopeId)
   withLiftedLeaf(0,liftedLeaseOptions(budget,'op:2'),500,'leaf:copy:transport',end=>{
    expect(end).toBe(Infinity)
    const active=workAdmissionSnapshot()
    expect(active.activeEndpoints.at(-1)!.id).toBe(seen.at(-1)!.scopeId)
    expect(seen.at(-1)!.caseKey).toBe('op:2')
   })
  })
 }))
 expect(seen.map(s=>s.key)).toEqual(['op:2','leaf:copy:transport'])
 expect(compareWork(seen[0]!.allocation,workAmount(4000n))).toBe(0)
 expect(compareWork(seen[1]!.allocation,workAmount(1000n))).toBe(0)
 expect(seen[0]!.scopeId).not.toBe(seen[1]!.scopeId)
})
full('a slice cannot silently mint a root or accept an empty identity',()=>{
 const budget=liftedWorkLeaseBudget(workAmount(120n))
 expect(()=>withLiftedCase(Infinity,budget,false,'op:0',()=>true)).toThrow('inherited FULL endpoint')
 workLedger.withBudget(workAmount(10n),()=>expect(()=>withLiftedCase(Infinity,budget,false,'',()=>true)).toThrow('stable key'))
})
full('a zero leaf refuses before work and restores the ancestor scopes',()=>{
 const budget=liftedWorkLeaseBudget(workAmount(120n),{leaf:workAmount(0n)});let ran=false
 workLedger.withBudget(workAmount(1000n),()=>{
  const count=workAdmissionSnapshot().activeEndpoints.length
  expect(()=>withLiftedLeaf(Infinity,liftedLeaseOptions(budget,'op:1'),500,'leaf:load:query',()=>{startWork('tableCells');ran=true})).toThrow(BudgetExpired)
  expect(workAdmissionSnapshot().activeEndpoints).toHaveLength(count)
 })
 expect(ran).toBe(false)
})
full('original refusal objects escape unchanged with all scopes cleaned up',()=>{
 const failure=new BudgetExpired('opaque fixture'),budget=liftedWorkLeaseBudget(workAmount(120n));let caught:unknown
 const before=workAdmissionSnapshot().activeEndpoints.length
 try{workLedger.withBudget(workAmount(1000n),()=>withLiftedCase(Infinity,budget,false,'op:3',()=>{throw failure}))}catch(error){caught=error}
 expect(caught).toBe(failure)
 expect(workAdmissionSnapshot().activeEndpoints).toHaveLength(before)
})
full('invalid exact grants and overrides are refused before a scope starts',()=>{
 for(const value of [workAmount(-1n),{num:1n,den:0n}])expect(()=>liftedWorkLeaseBudget(value)).toThrow(RangeError)
 expect(()=>liftedWorkLeaseBudget(workAmount(1n),{leaf:workAmount(-1n)})).toThrow(RangeError)
 expect(()=>liftedWorkLeaseBudget(workAmount(1n),{cases:{'op:1':workAmount(-1n)}})).toThrow(RangeError)
})
test('without an exact option the historical helper path remains available',()=>{
 let called=false
 withLiftedLeaf(0,{leafUnits:0},500,'legacy',until=>{called=true;expect(until).toBe(0)})
 expect(called).toBe(true)
})
