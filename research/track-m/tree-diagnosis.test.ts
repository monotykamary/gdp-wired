import {expect,test} from 'bun:test'
import {n} from '../../core/machine.ts'
import {canon} from '../../kernel/kernel.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {diagnoseTree} from './tree-diagnosis.ts'
test('tree diagnostics name repeated and constant split rejections',()=>{
 const g={name:'empty',hyps:[]},split={x:1},leaf={leaf:[]}
 expect(diagnoseTree(g,{split,yes:leaf,no:leaf},new Map([[canon(split),{lin:split,holds:true}]]))).toMatchObject({kind:'duplicate-split',id:canon(split)})
 expect(diagnoseTree(g,{split:{'1':1},yes:leaf,no:leaf})).toMatchObject({kind:'constant-split'})
})
test('tree diagnostics report bad arithmetic leaves but accept checked trees',()=>{
 expect(diagnoseTree({name:'empty',hyps:[]},{leaf:[]})).toMatchObject({kind:'leaf'})
 const g={name:'false',hyps:[{op:'<=' as const,a:n(1),b:n(0)}]},out=grow(g,new Map(),{nodes:0,until:clock()+100})
 expect('tree'in out).toBe(true)
 if('tree'in out)expect(diagnoseTree(g,out.tree)).toBeUndefined()
})
