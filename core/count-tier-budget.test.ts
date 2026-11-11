import {expect,test} from 'bun:test'
import {countTierBudget,ordinaryTierShare,remainingCountTierBudget,strategyPhase} from './count-tier-budget.ts'
import {attemptShare} from './support-budget.ts'
import {BudgetExpired,budgetEnd,checkBudget,clock,counted,fullRate,withBudget} from '../kernel/prove.ts'
import {costs} from './solver.ts'

test('generation has a 25 percent ceiling, strategies a 35 percent floor, ordinary a 30 percent floor',()=>{
 const p=countTierBudget(100,60100,4)
 expect(p).toEqual({active:true,generationUntil:15100,strategyFloor:21000,ordinaryFloor:18000,strategyUntil:42100,until:60100})
 expect(p.generationUntil-100).toBe(15000)
 expect(p.strategyUntil!-p.generationUntil).toBe(27000)
 expect(p.until-p.strategyUntil!).toBe(18000)
})
test('strategies may borrow the unreserved remainder beyond their minimum reservation',()=>{
 const p=countTierBudget(0,60000,4)
 expect(p.strategyFloor).toBe(21000)
 expect(p.strategyUntil!-p.generationUntil-p.strategyFloor).toBe(6000)
 // The old 35 percent hard-pool endpoint was 36000; it must not constrain this path.
 expect(p.strategyUntil).toBeGreaterThan(36000)
 expect(p.until-p.strategyUntil!).toBeGreaterThanOrEqual(p.ordinaryFloor)
})
test('unused generation and strategy allowance flows down without moving deadlines',()=>{
 const p=countTierBudget(1000,61000,4),generationFinished=4000,strategyFinished=11000
 expect(p.strategyUntil!-generationFinished).toBe(39000)
 expect(p.until-strategyFinished).toBe(50000)
 expect(ordinaryTierShare(p,strategyFinished,new Set(['a','b']))).toBe(25000)
 expect(p.strategyUntil).toBe(43000)
})
test('all selected laws share one borrowing endpoint, not one reservation per law',()=>{
 for(const selected of [1,2,3,49]){
  const p=countTierBudget(0,60000,selected)
  expect(p.strategyFloor).toBe(21000)
  expect(p.strategyUntil).toBe(42000)
  expect(p.until-p.strategyUntil!).toBe(18000)
 }
})
test('no dispatch is exactly the existing split and does not cap generation',()=>{
 for(const remaining of [0,1,29,60000,Infinity]){
  const p=countTierBudget(0,remaining,0)
  expect(p).toEqual({active:false,generationUntil:remaining,strategyFloor:0,ordinaryFloor:0,strategyUntil:undefined,until:remaining})
  for(let n=0;n<=29;n++){
   const pending=new Set(Array.from({length:n},(_,i)=>String(i)))
   for(const used of [0,1,19])expect(ordinaryTierShare(p,used,pending)).toBe(attemptShare(remaining-used,pending))
  }
 }
})
test('ordinary shares recompute after cheap attempts and never create work',()=>{
 const p=countTierBudget(0,60000,3),pending=new Set(['a','b','c'])
 expect(ordinaryTierShare(p,42000,pending)).toBe(6000)
 pending.delete('a');expect(ordinaryTierShare(p,43000,pending)).toBe(8500)
 pending.delete('b');expect(ordinaryTierShare(p,44000,pending)).toBe(16000)
 expect(ordinaryTierShare(p,60001,pending)).toBe(0)
})
test('invalid counts and unbounded active tiers are refused; expired work grants nothing',()=>{
 for(const count of [-1,.5,Infinity,NaN])expect(()=>countTierBudget(0,1,count)).toThrow(RangeError)
 expect(()=>countTierBudget(0,Infinity,1)).toThrow(RangeError)
 expect(countTierBudget(2,1,1)).toEqual({active:true,generationUntil:1,strategyFloor:0,ordinaryFloor:0,strategyUntil:1,until:1})
})
test('the production tier basis cannot restart W after preflight',()=>{
 const old=costs.fm
 try{counted(fullRate,()=>withBudget(10_000,()=>{
  costs.fm+=1864
  const start=clock(),plan=remainingCountTierBudget(start,10_000/fullRate,1)
  expect(plan.until).toBe(budgetEnd());expect(plan.until).toBeLessThan(start+10_000/fullRate)
  expect(plan.generationUntil).toBeCloseTo(budgetEnd()-10_000/fullRate*.75)
  expect(plan.until-plan.strategyUntil!).toBeCloseTo(plan.ordinaryFloor)
  expect(plan.ordinaryFloor).toBeCloseTo((budgetEnd()-start)*.3)
 }),true)}finally{costs.fm=old}
})
test('one expired strategy endpoint hands off its reserve and cannot refresh on fallback',()=>{
 const old=costs.fm
 try{counted(fullRate,()=>withBudget(10_000,()=>{
  const plan=remainingCountTierBudget(clock(),10_000/fullRate,1)
  strategyPhase(plan,plan.until,()=>{while(clock()<plan.strategyUntil!){costs.fm++;checkBudget('strategy')}costs.fm++;checkBudget('strategy')})
  expect(plan.until-clock()).toBeGreaterThan(plan.ordinaryFloor-1)
  let retried=false;expect(strategyPhase(plan,plan.until,()=>{retried=true})).toBeUndefined();expect(retried).toBe(false)
  costs.fm++;checkBudget('ordinary INIT and final check');expect(clock()).toBeLessThan(plan.until)
 }),true)}finally{costs.fm=old}
})
// Construct the boundary from a genuine plan and an integer fm increment, not
// by overwriting its endpoint or assigning a fractional counter value.
function exactEndpoint(run:(plan:ReturnType<typeof countTierBudget>,arrive:()=>void)=>void):void{
 const before=costs.fm
 try{counted(fullRate,()=>withBudget(10_000_000,()=>{
  const start=clock()
  for(let charge=1;charge<=1000;charge++){
   costs.fm=before+charge;const target=clock();costs.fm=before
   const plan=countTierBudget(start,start+(target-start)/.7,1)
   if(plan.strategyUntil!==target)continue
   expect(plan.ordinaryFloor).toBeGreaterThan(0)
   run(plan,()=>{costs.fm+=charge;expect(clock()).toBe(plan.strategyUntil!);expect(clock()).toBeLessThan(plan.until);expect(clock()).toBeLessThan(budgetEnd())})
   return
  }
  throw Error('no exact integer-work plan found')
 }),true)}finally{costs.fm=before}
}
test('exact strategy endpoint unknown hands back the ordinary reserve',()=>exactEndpoint((plan,arrive)=>{
 const result=strategyPhase(plan,plan.until,()=>{arrive();return {stuck:'unknown'}})
 expect(result).toBeUndefined()
 let ordinary=false;if(result===undefined)ordinary=true
 expect(ordinary).toBe(true)
}))
for(const result of [{stuck:'sat',refuted:true},{stuck:'unknown',refuted:true},{proof:{checked:true}},{stuck:'sat'}]){
 test('exact strategy endpoint preserves '+JSON.stringify(result),()=>exactEndpoint((plan,arrive)=>{
  expect(strategyPhase(plan,plan.until,()=>{arrive();return result})).toBe(result)
 }))
}
test('unknown before the strategy endpoint keeps its ordinary result',()=>exactEndpoint(plan=>{
 const result={stuck:'unknown'}
 expect(strategyPhase(plan,plan.until,()=>result)).toBe(result)
}))
test('no-dispatch unknown retains legacy behavior at the same clock',()=>exactEndpoint((plan,arrive)=>{
 const legacy=countTierBudget(clock(),plan.until,0),result={stuck:'unknown'}
 expect(strategyPhase(legacy,plan.until,()=>{arrive();return result})).toBe(result)
}))

test('strategy handoff does not hide a smaller outer budget',()=>{
 const old=costs.fm
 try{counted(fullRate,()=>{
  const plan=countTierBudget(clock(),clock()+100,1)
  expect(()=>withBudget(1,()=>strategyPhase(plan,plan.until,()=>{costs.fm+=2;checkBudget('outer')}))).toThrow(BudgetExpired)
 },true)}finally{costs.fm=old}
})
