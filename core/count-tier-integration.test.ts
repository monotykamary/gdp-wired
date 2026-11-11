import {expect,test} from 'bun:test'
import {type Law,n,same} from './machine.ts'
import {countTierBudget} from './count-tier-budget.ts'
import {admitCountedFamily,countedAttempts,countsDump} from './counts.ts'
import {selectedCountStrategies} from './count-strategies.ts'
import {rowCompositionFixture} from './count-row-composition.fixture.ts'
import {clock,counted,fullRate,withWall} from '../kernel/prove.ts'
import {checkCountedLaws} from '../kernel/kernel.ts'
import {env} from './solver.ts'
function mode<T>(tiers:string,run:()=>T):T{
 const old=env.GDP_COUNT_TIERS,strategies=env.GDP_COUNT_STRATEGIES
 env.GDP_COUNT_TIERS=tiers;env.GDP_COUNT_STRATEGIES='1'
 try{return run()}finally{
  if(old===undefined)delete env.GDP_COUNT_TIERS;else env.GDP_COUNT_TIERS=old
  if(strategies===undefined)delete env.GDP_COUNT_STRATEGIES;else env.GDP_COUNT_STRATEGIES=strategies
 }
}
test('empty structural dispatch reserves no pool and preserves the legacy result',()=>{
 const m={name:'no dispatch',params:[],inputs:[],state:{},step:{}},law:Law={name:'tautology',holds:same(n(0),n(0))},prior=countsDump.on
 try{
  const outcomes=[0,1].map(flag=>mode(String(flag),()=>counted(fullRate,()=>withWall(performance.now()+2000,()=>{
   const events:Record<string,unknown>[]=[];countsDump.on=e=>events.push(e as Record<string,unknown>)
   expect(selectedCountStrategies(m,[law])).toEqual([])
   const out=admitCountedFamily(m,[law],[law],new Set(),clock()+1000)
   expect(events.some(e=>e.phase==='count-tier-plan')).toBe(false)
   expect(out.proven).toBe(true)
   return out
  }))))
  expect(outcomes[1]).toEqual(outcomes[0])
 }finally{countsDump.on=prior}
})
test('structurally selected laws share the original absolute strategy deadline',()=>mode('1',()=>counted(fullRate,()=>withWall(performance.now()+10000,()=>{
 const f=rowCompositionFixture(),prior=countsDump.on,events:Record<string,unknown>[]=[]
 const start=clock(),until=start+10000,budget=countTierBudget(start,until,selectedCountStrategies(f.m,f.family).length)
 expect(budget.active).toBe(true)
 countsDump.on=e=>events.push(e as Record<string,unknown>)
 try{
  const out=admitCountedFamily(f.m,[f.law],f.family,new Set(),until,budget)
  expect(out.proven).toBe(true)
  if(out.proof)expect(checkCountedLaws(out.m,out.laws,out.proof)).toBe(true)
  const selected=events.filter(e=>e.phase==='count-tier-attempt'&&e.tier==='strategy')
  expect(selected.length).toBeGreaterThan(0)
  expect(selected.every(e=>e.end===budget.strategyUntil)).toBe(true)
  expect(events.filter(e=>e.phase==='count-strategy-result').every(e=>Number(e.end)<=budget.strategyUntil!)).toBe(true)
  const leafBudgets=events.filter(e=>e.phase==='count-strategy'&&e.stage==='search-budget')
  expect(leafBudgets.length).toBeGreaterThan(0)
  expect(leafBudgets.every(e=>e.workAllowance===10000&&e.leafUnits===10000/120)).toBe(true)
 }finally{countsDump.on=prior}
}))),15000)
test('a selected strategy decline cannot spend the ordinary-law remainder',()=>mode('1',()=>counted(fullRate,()=>withWall(performance.now()+2000,()=>{
 const m={name:'decline',params:[],inputs:[],state:{},step:{}},law:Law={name:'ordinary tautology',holds:same(n(0),n(0))}
 const result=countedAttempts(m,[law],new Set(),clock()+1000,true,new Set([law])).traced(law,[law],0,500)
 expect(result).toEqual({stuck:'strategy declined'})
}))))

test('structured fallback cannot recreate a strategy reservation',()=>mode('1',()=>counted(fullRate,()=>withWall(performance.now()+10000,()=>{
 const f=rowCompositionFixture(),prior=countsDump.on,plans:Record<string,unknown>[]=[]
 const impossible:Law={name:'false caller',holds:same(n(0),n(1))},family=[...f.family,impossible]
 const until=clock()+10000
 countsDump.on=e=>{const event=e as Record<string,unknown>;if(event.phase==='count-tier-plan')plans.push(event)}
 try{
  const out=admitCountedFamily(f.m,[impossible],family,new Set(),until)
  expect(out.proven).toBe(false)
  expect(plans.length).toBeGreaterThanOrEqual(2)
  expect(new Set(plans.map(p=>p.strategyUntil)).size).toBe(1)
  expect(plans.every(p=>Number(p.strategyUntil)<=until-3000)).toBe(true)
 }finally{countsDump.on=prior}
}))),15000)

test('an external tier reservation cannot change the enclosing deadline',()=>mode('1',()=>counted(fullRate,()=>{
 const f=rowCompositionFixture(),until=clock()+1000,budget=countTierBudget(clock(),until+1,1)
 expect(()=>admitCountedFamily(f.m,[f.law],f.family,new Set(),until,budget)).toThrow('mismatched tier deadline')
})))
