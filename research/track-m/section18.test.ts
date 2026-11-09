import {test,expect} from 'bun:test'
import {normalize,dependence,independent,inequalityKey} from './section18-data.ts'
import {lemmaRecorder as r} from './section18-recorder.ts'
import {pack,unpack} from './section18-codec.ts'
test('goal table round-trips shared proof context without column renaming',()=>{const g={name:'test',hyps:[{op:'var',name:'⟦123⟧'}]},x=unpack(pack({source:g,target:g}));expect(x.source).toEqual(g);expect(x.source).toBe(x.target)})
test('normalization removes read allocation identities but preserves keys and post-state',()=>{
 const a={op:'<=',a:{op:'var',name:'r17'},b:{op:'const',value:0}},b={op:'<=',a:{op:'var',name:'r3'},b:{op:'const',value:0}}
 expect(normalize(a,[['r17','xm#',{op:'var',name:'a$#'}]])).toEqual(normalize(b,[['r3','xm#',{op:'var',name:'a$#'}]]))
 expect(normalize(a,[['r17','xm',{op:'var',name:'a$#'}]])).not.toEqual(normalize(b,[['r3','xm#',{op:'var',name:'a$#'}]]))
})
test('a quantified hash suffix is not a post-state scalar or a guard',()=>{
 expect(independent(dependence({op:'var',name:'a$#'},['started']))).toBe(true)
 expect(dependence({op:'var',name:'started#'},['started']).postState).toBe(true)
 expect(dependence({op:'var',name:'?canVote'}).guard).toBe(true)
 expect(dependence({op:'var',name:'op'}).op).toBe(true)
})
test('linear comparison keys coalesce strict bounds, zero terms and common factors',()=>{
 const i={op:'var',name:'i'},j={op:'var',name:'j'},size={op:'var',name:'size'},c=(value:number)=>({op:'const',value}),mul=(k:number,a:any)=>({op:'mul',k,a}),add=(a:any,b:any)=>({op:'add',a,b}),le=(a:any,b:any)=>({op:'<=',a,b})
 expect(inequalityKey({op:'<',a:i,b:size})).toBe(inequalityKey(le(add(add(i,c(1)),mul(-1,size)),c(0))))
 expect(inequalityKey(le(add(i,mul(0,{op:'get',map:'post#',key:i})),size))).toBe(inequalityKey(le(i,size)))
 expect(inequalityKey(le(mul(2,i),mul(2,size)))).toBe(inequalityKey(le(i,size)))
 expect(inequalityKey(le(i,size))).not.toBe(inequalityKey(le(j,size)))
})
test('observer frames nest exactly and are disabled in controls',()=>{
 r.reset({state:{}},'test',0);const a=r.begin('helper','field'),b=r.begin('attempt','bound');r.end(b);r.end(a);expect(r.stack.length).toBe(0);expect(r.frames[1]!.parent).toBe(0)
 r.reset({state:{}},'test',0,false);expect(r.begin('helper','field')).toBeUndefined();expect(r.frames.length).toBe(0)
})
