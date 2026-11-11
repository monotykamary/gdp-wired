import {expect,test} from 'bun:test'
import {alphaEqual} from './alpha-source.ts'
const v=(name:string)=>({op:'var',name}), all=(key:string,c:unknown)=>({op:'all',key,c})
test('lexical flag and each binders compare modulo fresh names',()=>{
 expect(alphaEqual(all('k$1',v('k$1')),all('k$99',v('k$99')))).toBe(true)
 expect(alphaEqual({each:'a',value:v('a')},{each:'b',value:v('b')})).toBe(true)
})
test('free names and capture remain distinct',()=>{
 expect(alphaEqual(all('a',v('free')),all('b',v('other')))).toBe(false)
 expect(alphaEqual(all('a',v('a')),all('b',v('a')))).toBe(false)
 expect(alphaEqual(all('a',v('$I_alpha$0')),all('b',v('b')))).toBe(false)
})
test('nested shadowing is scoped and not flattened',()=>{
 expect(alphaEqual(all('a',all('a',v('a'))),all('b',all('c',v('c'))))).toBe(true)
 expect(alphaEqual(all('a',all('b',v('a'))),all('c',all('d',v('d'))))).toBe(false)
})
test('operators values field presence and tuple order are not erased',()=>{
 expect(alphaEqual(all('a',{op:'const',value:1}),all('b',{op:'const',value:2}))).toBe(false)
 expect(alphaEqual({op:'all',key:'a',keys:[],c:v('a')},all('b',v('b')))).toBe(false)
 expect(alphaEqual({op:'all',key:'a',keys:['b'],c:[v('a'),v('b')]},{op:'all',key:'c',keys:['d'],c:[v('d'),v('c')]})).toBe(false)
})
test('count below binds j but not the counted key',()=>{
 const a={j:'j',key:'k',below:v('j'),body:[v('j'),v('k')]},b={j:'r',key:'s',below:v('r'),body:[v('r'),v('s')]}
 expect(alphaEqual(a,b,'count')).toBe(true)
 expect(alphaEqual({...a,below:v('k')},{...b,below:v('s')},'count')).toBe(false)
 expect(alphaEqual({counts:{C:a},step:{}},{counts:{C:b},step:{}},'machine')).toBe(true)
})
test('law binders are local to the predicate',()=>{
 expect(alphaEqual({name:'L',forall:'a',holds:v('a')},{name:'L',forall:'b',holds:v('b')},'law')).toBe(true)
 expect(alphaEqual({name:'L',forall:'a',holds:v('a')},{name:'M',forall:'b',holds:v('b')},'law')).toBe(false)
})
test('invalid duplicate binders fail closed',()=>{
 expect(()=>alphaEqual({op:'all',key:'a',keys:['a'],c:v('a')},all('b',v('b')))).toThrow('invalid alpha binder')
})
