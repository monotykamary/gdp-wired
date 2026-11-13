import {expect,test} from 'bun:test'
import {completeWorkProfile} from './work-profile.ts'
import {BudgetExpired,workLedger} from './work-admission.ts'
import {workAmount} from './work-amount.ts'
import {canUseCountedProxy,inProxySearch,withCountedSearchPolicy,withPlainSearchPolicy,withPublicSearchPolicy} from './search-policy.ts'
import {withSearchAllowance} from './count-search-allowance.ts'
import {countGenerationPhase} from './count-generation-phase.ts'
import {isLocalCountExpiration,strategyPhase,type CountTierBudget} from './count-tier-budget.ts'
import {workRefusalWhy} from './work-refusal.ts'
import {clock} from '../kernel/prove.ts'
const rooted=<T>(run:()=>T,units=1_000_000n)=>workLedger.withBudget(workAmount(units),run)
if(completeWorkProfile.enabled){
 test('a public counted call defers its branch, and legacy selection restores it',()=>rooted(()=>{
  withPublicSearchPolicy(true,()=>{
   expect(inProxySearch()).toBe(false);expect(canUseCountedProxy()).toBe(true)
   withCountedSearchPolicy(false,()=>expect(inProxySearch()).toBe(true))
   expect(inProxySearch()).toBe(false)
  })
  expect(inProxySearch()).toBe(false)
 }))
 test('rejecting and explicit native ancestors lock nested nonrejecting calls',()=>rooted(()=>{
  const nested=()=>withPublicSearchPolicy(true,()=>withCountedSearchPolicy(false,()=>{
   expect(inProxySearch()).toBe(false);expect(canUseCountedProxy()).toBe(false)
   withPublicSearchPolicy(false,()=>expect(inProxySearch()).toBe(false))
  }))
  withPublicSearchPolicy(true,()=>withCountedSearchPolicy(true,nested))
  withPlainSearchPolicy(true,nested)
 }))
 test('counted policy restores proxy state after a nested rejecting exception',()=>rooted(()=>withPlainSearchPolicy(false,()=>{
  const boom=new Error('fixture')
  expect(()=>withPublicSearchPolicy(true,()=>withCountedSearchPolicy(true,()=>{
   expect(inProxySearch()).toBe(false);throw boom
  }))).toThrow(boom)
  expect(inProxySearch()).toBe(true)
 })))
 test('proxy allowance polls but creates no native scope or local refusal handler',()=>rooted(()=>withPublicSearchPolicy(true,()=>withCountedSearchPolicy(false,()=>{
  const before=workLedger.snapshot();let refused=false
  withSearchAllowance(clock(),()=>workLedger.start('ticks',2),()=>{refused=true})
  expect(refused).toBe(false)
  expect(workLedger.snapshot().activeEndpoints).toEqual(before.activeEndpoints)
 }))))
 test('proxy allowance and generation cannot swallow an oversized enclosing request',()=>{
  for(const generation of [false,true]){
   let refused=false
   expect(()=>rooted(()=>withPublicSearchPolicy(true,()=>withCountedSearchPolicy(false,()=>{
    const run=()=>workLedger.start('ticks',6)
    return generation?countGenerationPhase(clock()+100,run):withSearchAllowance(clock()+100,run,()=>{refused=true})
   })),5n)).toThrow(BudgetExpired)
   expect(refused).toBe(false);expect(inProxySearch()).toBe(false)
  }
 })
 test('proxy locality rejects authenticated root and explicit scope refusals',()=>rooted(()=>withPlainSearchPolicy(false,()=>{
  let failure:unknown
  try{workLedger.withBudget(workAmount(1n),()=>workLedger.start('ticks',2))}catch(error){failure=error}
  expect(failure).toBeInstanceOf(BudgetExpired)
  expect(isLocalCountExpiration(failure,Infinity)).toBe(false)
  expect(isLocalCountExpiration(new BudgetExpired('synthetic local stop'),Infinity)).toBe(true)
 })))
 test('proxy strategy never consumes a real refusal even past its local deadline',()=>{
  expect(()=>rooted(()=>withPlainSearchPolicy(false,()=>{
   const end=clock(),budget:CountTierBudget={active:true,workAllowance:1,generationUntil:end,strategyFloor:1,ordinaryFloor:0,strategyUntil:end+0.001,until:end+2}
   return strategyPhase(budget,end+0.001,()=>{workLedger.start('plainRows',1);workLedger.start('ticks',20)})
  }),10n)).toThrow(BudgetExpired)
 })
 test('native allowance retains its real child quota and native refusal callback',()=>rooted(()=>withPlainSearchPolicy(true,()=>{
  let called=false
  withSearchAllowance(clock()+1,()=>{
   expect(workLedger.currentScope()?.kind).toBe('scope');workLedger.start('ticks',251)
  },error=>{called=true;expect(error).toBeInstanceOf(BudgetExpired)})
  expect(called).toBe(true)
 })))
 test('refusal diagnostics expose authenticated endpoint kinds without changing them',()=>{
  let failure:Error|undefined
  try{rooted(()=>workLedger.start('ticks',2),1n)}catch(error){failure=error as Error}
  expect(workRefusalWhy(failure!)).toContain('[limits=root]')
  expect(workRefusalWhy(new BudgetExpired('unowned'))).toBe('work budget (unowned)')
 })
}else test('legacy mode does not activate the counted proxy selector',()=>{
 withPublicSearchPolicy(true,()=>withCountedSearchPolicy(false,()=>expect(inProxySearch()).toBe(false)))
 expect(canUseCountedProxy()).toBe(false)
})
