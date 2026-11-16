import {expect,test} from 'bun:test'
import {rule,nat,everyKey,forall,all,Cond,proveRule,QuantifierAdmissionError} from './dsl.ts'
import {interpret,compileJs,type C,type Law} from './machine.ts'
import {scope} from '../kernel/kernel.ts'
const make=()=>rule('prenex regression').inputs({k:nat,v:nat}).maps({M:0}).state({n:0}).step(({M,k,v,n})=>({M:M.set(k,v),n}))
const refused=(f:()=>unknown,code:QuantifierAdmissionError['code']='nested-universal')=>{let error:unknown;try{f()}catch(e){error=e};expect(error).toBeInstanceOf(QuantifierAdmissionError);expect((error as QuantifierAdmissionError).code).toBe(code)}
test('false two- and three-level map laws refuse before any proof',()=>{
 const r=make(),run=interpret(r.machine),state=run.step({},run.init({}),{k:0,v:1})
 expect(state.maps.M!.get(0)).toBe(1);expect(state.maps.M!.get(1)??0).toBe(0)
 refused(()=>r.law('false nested',({M})=>everyKey(a=>everyKey(b=>M.at(a).atMost(M.at(b))))))
 refused(()=>r.law('false triple',({M})=>everyKey(a=>everyKey(b=>everyKey(c=>M.at(a).atMost(M.at(b)).and(M.at(b).atMost(M.at(c))))))))
 refused(()=>r.law('outer forall',({M})=>forall(a=>everyKey(b=>M.at(a).atMost(M.at(b))))))
 const proper=r.law('proper two keys',({M})=>forall((a,b)=>M.at(a).atMost(M.at(b))))
 expect(proveRule(r as never,[proper],{search:false}).proven).toBe(false)
})
test('step and multi-step conclusions use the same refusal',()=>{
 const r=make()
 refused(()=>r.stepLaw('step nested',({M})=>everyKey(a=>everyKey(b=>M.at(a).eq(M.at(b))))))
 refused(()=>r.stepsLaw('steps nested',2,({M})=>everyKey(a=>everyKey(b=>M.at(a).eq(M.at(b))))))
 refused(()=>r.stepLaw('step forall',({M})=>forall(a=>everyKey(b=>M.at(a).eq(M.at(b))))))
 refused(()=>r.stepsLaw('steps forall',2,({M})=>forall(a=>everyKey(b=>M.at(a).eq(M.at(b))))))
})
test('sibling universals may share a key and still prove',()=>{
 const r=make(),law=r.law('siblings',({M})=>all(everyKey(a=>M.at(a).atLeast(0)),everyKey(b=>M.at(b).atLeast(0))))
 const v=proveRule(r as never,[law],{search:false});expect(v.proven).toBe(true);expect(v.checked).toBe(true)
})
test('raw nested laws and machines remain refused by existing admission',()=>{
 const r=make(),v=(name:string)=>({op:'var' as const,name}),read=(name:string)=>({op:'get' as const,map:'M',key:v(name)})
 const body:C={op:'<=',a:read('a'),b:read('b')},nested:C={op:'all',key:'a',c:{op:'all',key:'b',c:body}}
 const law:Law={name:'raw',forall:'a',holds:{op:'all',key:'b',c:body}}
 expect(()=>scope(r.machine,[law])).toThrow();expect(proveRule(r as never,[law],{search:false}).proven).toBe(false)
 const machine={...r.machine,step:{...r.machine.step,flags:{bad:nested}}}
 expect(()=>interpret(machine)).toThrow();expect(()=>compileJs(machine)).toThrow()
})
test('shadowed positive binders are not coalesced',()=>{
 const r=make(),x={op:'var' as const,name:'a'},body:C={op:'=',a:x,b:x}
 refused(()=>r.law('shadow',()=>new Cond({op:'all',key:'a',c:{op:'all',key:'a',c:body}})))
})
test('substitution preserves occurrences owned by a shadowing negative binder',()=>{
 const r=make(),read={op:'get' as const,map:'M',key:{op:'var' as const,name:'shadow'}}
 const law=r.law('negative shadow',()=>new Cond({op:'all',key:'shadow',c:{op:'not',x:{op:'all',key:'shadow',c:{op:'=',a:read,b:read}}}}))
 expect(law.holds).toEqual({op:'not',x:{op:'all',key:'shadow',c:{op:'=',a:read,b:read}}})
})
test('a free user variable cannot be captured by a generated law key',()=>{
 const anchor=make().law('anchor',({M})=>everyKey(a=>M.at(a).atLeast(0)))
 const collision='key$'+(Number(anchor.forall!.slice(4))+1)
 const r=rule('collision').maps({M:0}).state({[collision]:1})
 refused(()=>r.law('capture',env=>everyKey(a=>env.M.at(a).atLeast(0)).and(env[collision]!.eq(1))),'binder-capture')
})
test('renaming refuses capture by a differently named inner binder',()=>{
 const anchor=make().law('anchor',({M})=>everyKey(a=>M.at(a).atLeast(0))),target='key$'+(Number(anchor.forall!.slice(4))+1)
 const read=(name:string)=>({op:'get' as const,map:'M',key:{op:'var' as const,name}})
 refused(()=>make().law('inner capture',()=>new Cond({op:'all',key:'outer',c:{op:'not',x:{op:'all',key:target,c:{op:'<=',a:read('outer'),b:read(target)}}}})),'binder-capture')
})
test('AST substitution handles quoted names without textual replacement',()=>{
 const name='a"\\b',r=make(),law=r.law('quoted binder',()=>new Cond({op:'all',key:name,c:{op:'=',a:{op:'get',map:'M',key:{op:'var',name}},b:{op:'get',map:'M',key:{op:'var',name}}}}))
 expect(JSON.stringify(law)).not.toContain(JSON.stringify(name).slice(1,-1))
 expect(proveRule(r as never,[law],{search:false}).proven).toBe(true)
})
