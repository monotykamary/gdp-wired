import {expect,test} from 'bun:test'
import {countPrerequisiteComponents} from './count-prerequisite-components.ts'
import {nonneg,proveRatRule,ratRule,rmin} from './rationals.ts'
test('a reachable rejection invalidates even committed users without calling them false',()=>{
 const q=countPrerequisiteComponents(['bad','owner','later'],new Map(),[],['bad','owner'],{held:new Map([['bad',[]],['owner',['bad']]]),proofGuided:true})
 expect(q.reject(['bad'])).toEqual(['owner']);expect(q.failed()).toEqual(['bad']);expect(q.available()).toEqual([])
 expect(q.next()).toMatchObject({name:'owner'});q.finish('owner',[])
 expect(q.next()).toEqual({kind:'ready',members:['owner']});q.commit(['owner'])
 expect(q.available()).toEqual(['owner']);expect(q.retryCount()).toEqual({owner:1})
})
test('reachable rejection abandons an active stale context and rebuilds it',()=>{
 const q=countPrerequisiteComponents(['owner','bad'],new Map([['owner',['bad']]]),['owner'],[],{proofGuided:true,discoveryFirst:true,discovered:['bad'],targets:['owner']})
 expect(q.next()).toMatchObject({name:'owner',context:['owner','bad']})
 q.reject(['bad']);expect(q.next()).toMatchObject({name:'owner',context:['owner']})
 q.finish('owner',[]);expect(q.next()).toEqual({kind:'ready',members:['owner']})
})
test('the single-grant ledger conserves its cap; the renewed-grant mutant is refused',()=>{
 const model=(broken=false)=>ratRule('single reachability grant').params({cap:nonneg}).inputs({request:nonneg}).state({spent:0})
  .step(({cap,request,spent})=>({spent:spent.plus(rmin(request,broken?cap:cap.minus(spent)))}))
 const good=model(),bad=model(true)
 const laws=(r:typeof good)=>[r.law('single cap survives every retry',({spent,cap})=>spent.atMost(cap)),r.law('spending is nonnegative',({spent})=>spent.atLeast(0))]
 const proven=proveRatRule(good,laws(good)),refused=proveRatRule(bad,laws(bad))
 expect(proven.proven&&proven.checked).toBe(true);expect(refused.proven).toBe(false);expect(refused.stuck).toBe('sat')
})
