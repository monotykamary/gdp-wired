import {expect,test} from 'bun:test'
import {n,x} from '../../core/machine.ts'
import {check} from '../../kernel/kernel.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {proveRowCases} from './row-cases.ts'
test('row cases cover both directions of disequality and reuse only checked trees',()=>{
 const g={name:'false',hyps:[{op:'<=' as const,a:n(1),b:n(0)}]},events:object[]=[];let calls=0
 const tree=proveRowCases(g,new Map(),[[x('a'),x('i')],[x('b'),x('i')]],clock()+1000,(path,until)=>{calls++;const out=grow(g,path,{nodes:0,until});return 'tree'in out?out.tree:undefined},e=>events.push(e))
 expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)
 expect(calls).toBe(3);expect(events.length).toBeGreaterThan(calls)
})
test('row cases never accept an unchecked leaf',()=>{
 const g={name:'possible',hyps:[{op:'<=' as const,a:n(0),b:x('a')}]}
 expect(proveRowCases(g,new Map(),[[x('a'),x('i')]],clock()+100,()=>({leaf:[]}))).toBeUndefined()
})
test('deferred row proposals still require the composing kernel check',()=>{
 const g={name:'possible',hyps:[{op:'<=' as const,a:n(0),b:x('a')}]}
 const tree=proveRowCases(g,new Map(),[[x('a'),x('i')]],clock()+1000,()=>({leaf:[]}),undefined,{deferToCaller:true})
 expect(tree).toBeDefined()
 if(tree)expect(check(g,tree)).toBe(false)
})
