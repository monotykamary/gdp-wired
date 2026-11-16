import {expect,test} from 'bun:test'
import {rule,nat,everyKey,someKey,forall,exists,Cond,Term,proveRule,proveSteps,proveDecision,proveLeadsTo} from './dsl.ts'
import {interpret} from './machine.ts'

for(const name of ['k$1','key$1','key$2','s$1','gdp$bound$1']){
  test(`a user parameter ${name} is never a generated quantifier`,()=>{
    const r=rule('parameter collision').params({[name]:nat}).state({s:0}).step(()=>({}))
    const params={[name]:0},state=interpret(r.machine).init(params)
    expect(state.scalars.s).toBe(0)
    expect(1===params[name]).toBe(false) // Original universal, concrete key 1.
    const law=r.law('false universal',env=>everyKey(k=>k.eq(env[name]!)))
    expect(law.forall).not.toBe(name)
    expect(proveRule(r as never,[law],{search:false}).proven).toBe(false)
  })
}
test('an existential witness never captures a free user parameter',()=>{
  const r=rule('existential collision').params({'s$1':nat}).state({s:0}).step(()=>({}))
  const p={'s$1':0};interpret(r.machine).init(p)
  expect(p['s$1']===2).toBe(false) // False for EVERY existential candidate.
  const law=r.law('false existential',env=>someKey(k=>k.eq(env['s$1']).and(env['s$1'].eq(2)),2))
  expect(proveRule(r as never,[law],{search:false}).proven).toBe(false)
})
test('state and input namespaces cannot capture generated binders',()=>{
  const state=rule('state collision').state({'k$1':0}).step(()=>({}))
  const law=state.law('false at key 1',env=>forall(k=>k.eq(env['k$1'])))
  expect(proveRule(state as never,[law],{search:false}).proven).toBe(false)
  const input=rule('input collision').inputs({'k$1':nat}).state({s:0}).step(()=>({}))
  const step=input.stepLaw('false for input 0, key 1',env=>everyKey(k=>k.eq(env['k$1'])))
  expect(proveSteps(input as never,[],[step],{search:false}).proven).toBe(false)
})
test('map names and encoded aliases are kept distinct',()=>{
  const r=rule('map collision').inputs({key:nat,value:nat}).maps({'gdp$bound$1':0}).step(env=>({'gdp$bound$1':env['gdp$bound$1'].set(env.key,env.value)}))
  const law=r.law('all cells natural',env=>everyKey(k=>env['gdp$bound$1'].at(k).atLeast(0)))
  expect(law.forall).not.toBe('gdp$bound$1')
  expect(proveRule(r as never,[law],{search:false}).proven).toBe(true)
})
test('generated binds remain admissible for machine flags and each writes',()=>{
  const r=rule('machine boundary').inputs({key:nat,value:nat}).maps({M:0}).flags(({M})=>({ok:everyKey(k=>M.at(k).atLeast(0))})).step(({M})=>({M:M.each(k=>M.at(k))}))
  const run=interpret(r.machine),s=run.step({},run.init({}),{key:0,value:1})
  expect(s.maps.M!.size).toBe(0)
})
test('real k-step marks work but user colon names are refused',()=>{
  const r=rule('step marks').inputs({u:nat}).state({s:0}).step(({u})=>({s:u}))
  const law=r.stepsLaw('last request wins',2,(_before,after,requests)=>after.s.eq(requests[1]!.u))
  expect(proveSteps(r as never,[],[law],{search:false}).proven).toBe(true)
  for(const name of ['2:u','?step2:u']){
    const bad=rule('forged mark').params({[name]:nat}).inputs({u:nat}).state({s:0}).step(({u})=>({s:u}))
    expect(()=>bad.stepsLaw('alias',2,(env,_after,rs)=>env[name]!.eq(rs[1]!.u))).toThrow('reserved')
  }
})
test('reserved free names in a manually built law are refused',()=>{
  const r=rule('reserved free variable').state({s:0}).step(()=>({}))
  const forged=()=>new Cond({op:'=',a:{op:'var',name:'?unowned'},b:{op:'const',value:0}})
  expect(()=>r.law('forged',forged)).toThrow('free reserved')
  expect(()=>r.stepLaw('forged',forged)).toThrow('free reserved')
  expect(()=>r.decide('forged',forged,forged)).toThrow('free reserved')
  expect(()=>r.law('escaped binder',()=>{let escaped:Term|undefined;everyKey(k=>{escaped=k;return k.eq(k)});return escaped!.eq(0)})).toThrow('free reserved')
})
test('a forged reserved name cannot be laundered by markedE',()=>{
  const r=rule('forged temporal variable').inputs({u:nat}).state({s:0}).step(({u})=>({s:u}))
  expect(()=>r.stepsLaw('forged',2,()=>new Cond({op:'=',a:{op:'var',name:'?step9:u'},b:{op:'const',value:0}}))).toThrow()
})
test('duplicate declarations still fail before proof',()=>{
  const r=rule('duplicate').params({x:nat}).inputs({x:nat}).state({s:0}).step(()=>({}))
  expect(()=>r.machine).toThrow('a param and an input')
})
test('positive quantified decisions and keyed liveness still prove',()=>{
  const r=rule('positive controls').inputs({u:nat}).state({s:0}).step(()=>({s:0}))
  const decision=r.decide('true decision',()=>everyKey(k=>k.atLeast(0)),()=>everyKey(k=>k.atLeast(0)))
  expect(proveDecision(decision).proven).toBe(true)
  const live=r.leadsTo('reaches zero',{from:({s},k)=>s.gt(0).and(k.eq(k)),to:({s},k)=>s.eq(0).and(k.eq(k)),rank:({s})=>s,helpful:()=>({u:0})})
  expect(proveLeadsTo(r as never,[],live).proven).toBe(true)
})
test('exists value binders retain witness metadata',()=>{
  const r=rule('exists boundary').state({s:0}).step(()=>({}))
  expect(proveRule(r as never,[r.law('exists two',()=>exists(k=>k.eq(2),2))],{search:false}).proven).toBe(true)
})
