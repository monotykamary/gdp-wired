import {expect,test} from 'bun:test'
import {atMost,n,x} from './machine.ts'
import {BudgetExpired,withBudget} from './wall.ts'
import {completeWorkProfile} from './work-profile.ts'
import {tableAdmissionHook} from './table-admission-hook.ts'
import {fullWork} from '../kernel/prove.ts'
import {leafConstraints} from '../kernel/kernel.ts'
import {proverRowsReusingFacts} from '../kernel/prover-rows.ts'
const full=completeWorkProfile.enabled?test:test.skip
full('facts-only reindex refuses unaffordable table work and restores admission',()=>{
 const goal={name:'facts-only cap',hyps:[atMost(x('facts_only_long_variable_name'),n(2)),atMost(x('facts_only_other_variable_name'),n(3))]},expected=leafConstraints(goal,new Map())
 let refused=0,completed=0
 for(const W of [0,1,5,17,31,100000]){
  const hook=tableAdmissionHook.admit,start=fullWork()
  let rows:ReturnType<typeof proverRowsReusingFacts>|undefined
  try{rows=withBudget(W,()=>proverRowsReusingFacts(goal,new Map()));completed++}
  catch(error){expect(error).toBeInstanceOf(BudgetExpired);refused++}
  const used=fullWork()-start
  console.log('FACTS_ONLY_CAP '+JSON.stringify({W,used,completed:rows!==undefined}))
  expect(used,'W='+W).toBeLessThanOrEqual(W)
  expect(tableAdmissionHook.admit).toBe(hook)
  if(rows)expect(rows).toEqual(expected)
  if(W===0)expect(rows).toBeUndefined()
 }
 expect(refused).toBeGreaterThan(0);expect(completed).toBeGreaterThan(0)
})
