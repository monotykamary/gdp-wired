import {expect,test} from 'bun:test'
import {n} from '../../core/machine.ts'
import {canon} from '../../kernel/kernel.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {countLeafKinds,diagnoseTree,treeMetrics} from './tree-diagnosis.ts'
test('tree metrics distinguish shared objects from expanded proof size',()=>{
 const leaf={leaf:[{kind:'input' as const,index:0}]},child={split:{x:1},yes:leaf,no:leaf},tree={split:{y:1},yes:child,no:child}
 expect(treeMetrics(tree)).toEqual({nodes:7,leaves:4,steps:4,depth:2,unique:3})
})
test('leaf kinds count failed count cuts, not their successful continuation',()=>{
 const leaf={leaf:[]},tree={split:{count:1},yes:{split:{control:1},yes:leaf,no:leaf},no:leaf},cert={reads:[['count','C',{op:'const' as const,value:0}]] as [string,string,{op:'const',value:number}][],insts:[{wit:'row',below:n(4),terms:[[1,'count']] as [number,string][],unit:0}]}
 expect(countLeafKinds(tree,cert)).toEqual({countRowLeaves:1,arithmeticLeaves:2})
 const lin={count:1},root=new Map([[canon(lin),{lin,holds:false}]])
 expect(countLeafKinds(tree,cert,root)).toEqual({countRowLeaves:3,arithmeticLeaves:0})
})
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
