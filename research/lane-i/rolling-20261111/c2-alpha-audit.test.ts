import {test,expect} from 'bun:test'
import {alphaAstKey,alphaStepKey,alphaCountKey,sameAlphaCounts} from './c2-alpha-audit.ts'
const variable=(name:string)=>({op:'var',name})
const all=(key:string,c:unknown,extra:Record<string,unknown>={})=>({op:'all',key,c,...extra})
test('alpha audit renames lexical bound occurrences only',()=>{
 expect(alphaAstKey(all('a',variable('a')))).toBe(alphaAstKey(all('b',variable('b'))))
 expect(alphaAstKey(all('a',variable('free')))).not.toBe(alphaAstKey(all('b',variable('other'))))
})
test('alpha audit preserves extra metadata and outer bounds',()=>{
 expect(alphaAstKey(all('a',variable('a'),{below:variable('a')}))).not.toBe(alphaAstKey(all('b',variable('b'),{below:variable('b')})))
 expect(alphaAstKey(all('a',variable('a'),{below:variable('free'),tag:1}))).toBe(alphaAstKey(all('b',variable('b'),{below:variable('free'),tag:1})))
 expect(alphaAstKey(all('a',variable('a'),{tag:1}))).not.toBe(alphaAstKey(all('b',variable('b'),{tag:2})))
})
test('alpha audit preserves shadowing and multiple-binder order',()=>{
 expect(alphaAstKey(all('a',all('a',variable('a'))))).toBe(alphaAstKey(all('b',all('c',variable('c')))))
 expect(alphaAstKey(all('a',all('a',variable('a'))))).not.toBe(alphaAstKey(all('b',all('c',variable('b')))))
 expect(alphaAstKey(all('a',variable('b'),{keys:['b']}))).toBe(alphaAstKey(all('c',variable('d'),{keys:['d']})))
 expect(()=>alphaAstKey(all('a',variable('a'),{keys:['a']}))).toThrow()
})
test('alpha audit preserves variable metadata and entire AST structure',()=>{
 expect(alphaAstKey(all('a',{...variable('a'),sort:1}))).not.toBe(alphaAstKey(all('b',{...variable('b'),sort:2})))
 expect(alphaAstKey({one:all('a',variable('a')),two:1})).not.toBe(alphaAstKey({one:all('b',variable('b')),two:2}))
})
test('count audit preserves literal declaration binders, aliases and order',()=>{
 const a={j:'j',lo:'j',base:0,key:'k',below:variable('j'),body:{op:'get',map:'M',key:variable('k')}}
 const b={...a,j:'i',lo:'i',below:variable('i')}
 expect(alphaCountKey(a)).not.toBe(alphaCountKey(b))
 expect(alphaCountKey(a)).toBe(alphaCountKey({...a}))
 expect(alphaCountKey(a)).not.toBe(alphaCountKey({...a,lo:'different'}))
 expect(alphaCountKey(a)).not.toBe(alphaCountKey({...a,base:1}))
 expect(sameAlphaCounts({count:a},{count:{...a}})).toBe(true)
 expect(sameAlphaCounts({count:a},{other:a})).toBe(false)
})
test('nested all renaming in a count cannot capture the literal count key',()=>{
 const a={j:'j',lo:'j',base:0,key:'k',below:variable('j'),body:all('i',variable('i'),{below:variable('k')})}
 const b={...a,body:all('q',variable('q'),{below:variable('k')})}
 expect(alphaCountKey(a)).toBe(alphaCountKey(b))
 expect(alphaCountKey(a)).not.toBe(alphaCountKey({...b,body:all('q',variable('q'),{below:variable('q')})}))
})

test('step maps each binds only its value and preserves every other field',()=>{
 const step=(each:string,extra:Record<string,unknown>={})=>({maps:{M:{each,value:variable(each),...extra}},vars:{v:variable('free')}})
 expect(alphaStepKey(step('a'))).toBe(alphaStepKey(step('b')))
 expect(alphaStepKey(step('a',{below:variable('a')}))).not.toBe(alphaStepKey(step('b',{below:variable('b')})))
 expect(alphaStepKey(step('a',{below:variable('free')}))).toBe(alphaStepKey(step('b',{below:variable('free')})))
 expect(alphaStepKey(step('a',{tag:1}))).not.toBe(alphaStepKey(step('b',{tag:2})))
 expect(alphaStepKey({...step('a'),vars:{v:variable('a')}})).not.toBe(alphaStepKey({...step('b'),vars:{v:variable('b')}}))
 expect(()=>alphaStepKey(step('a',{key:variable('key')}))).toThrow()
})
test('step-map each scope interacts lexically with nested all, not global names',()=>{
 const step=(each:string,c:unknown)=>({maps:{M:{each,value:all('inner',c)}}})
 expect(alphaStepKey(step('outer',variable('outer')))).toBe(alphaStepKey(step('other',variable('other'))))
 expect(alphaStepKey(step('inner',variable('inner')))).not.toBe(alphaStepKey(step('other',variable('other'))))
 expect(alphaStepKey(step('a',variable('free')))).not.toBe(alphaStepKey(step('b',variable('b'))))
 expect(alphaStepKey({maps:{M:{key:variable('a'),value:variable('a')}}})).not.toBe(alphaStepKey({maps:{M:{key:variable('b'),value:variable('b')}}}))
})
test('alpha audit refuses non-JSON literals rather than erasing them',()=>{
 expect(()=>alphaAstKey({unexpected:()=>1})).toThrow()
 expect(()=>alphaAstKey({unexpected:Infinity})).toThrow()
})
