// Exact rational envelope for the production reserve formula. This proves
// allocation conservation, not an upper bound on native certificate costs.
import {expect,test} from 'bun:test'
import {nonneg,proveRatRule,ratRule,rmax,rmin} from './rationals.ts'
import {reserveCheckedCountClosing,reserveCountClosing,type CountClosingBudget} from './count-closing-budget.ts'
import {countTierBudget} from './count-tier-budget.ts'
function envelope(broken=false){
 return ratRule('checked packet reserve envelope').params({root:nonneg}).inputs({native:nonneg,demand:nonneg}).state({spent:0,protected:0})
  .step(({root,native,demand,spent})=>{
   const remaining=root.minus(spent),wanted=rmax(1,native.times(2)),protectedWork=broken?wanted:rmin(remaining,wanted)
   const granted=rmin(demand,remaining.minus(protectedWork))
   return {spent:spent.plus(granted),protected:protectedWork}
  })
}
function laws(r:ReturnType<typeof envelope>){return [
 r.law('spent is nonnegative',({spent})=>spent.atLeast(0)),
 r.law('protected work is nonnegative',({protected:reserve})=>reserve.atLeast(0)),
 r.law('allocation and reserve fit the original root',({spent,protected:reserve,root})=>spent.plus(reserve).atMost(root)),
]}
test('the rational allocation envelope is kernel-checked and its uncapped twin is refused',()=>{
 const good=envelope(),result=proveRatRule(good,laws(good))
 expect(result.proven&&result.checked).toBe(true)
 const bad=envelope(true),refused=proveRatRule(bad,laws(bad))
 expect(refused.proven).toBe(false);expect(refused.stuck).toBe('sat')
})
test('production reserve agrees with the exact envelope on sequential resizes',()=>{
 const model=envelope(),requests=[{native:4,demand:128},{native:10,demand:256},{native:1,demand:512},{native:80,demand:256}]
 const expected=model.run({root:1024},requests)
 let spent=0,base=reserveCountClosing(countTierBudget(0,1024,1),true) as CountClosingBudget
 for(const [i,request]of requests.entries()){
  base=reserveCheckedCountClosing(base,[request.native],spent)
  spent+=Math.min(request.demand,Math.max(0,base.searchUntil-spent))
  expect(expected[i+1]).toEqual({spent:String(spent),protected:String(base.closingFloor)})
 }
})
