import {test,expect} from 'bun:test'
import {canon,check,type Goal,type Path} from '../../kernel/kernel.ts'
import {grow,widen,withWall,withWork,fullWork} from '../../kernel/prove.ts'
import {focusGoal} from './focus-goal.ts'
const x={op:'var' as const,name:'x'},zero={op:'const' as const,value:0}
const goal:Goal={name:'permutation',hyps:[{op:'<',a:x,b:zero},{op:'=',a:x,b:x}]}
test('focus keeps every row exactly once and leaves the original order untouched',()=>{
  const view=focusGoal(goal,0)
  expect(view.hyps).toEqual([goal.hyps[1]!,goal.hyps[0]!])
  expect(goal.hyps[0]!.op).toBe('<');expect(view.hyps[1]).toBe(goal.hyps[0])
})
test('permuted proof remaps and checks at root and under an exact cut path',()=>{
  const cut={x:1,'1':-5},paths:Path[]=[new Map(),new Map([[canon(cut),{lin:cut,holds:true}]])]
  for(const path of paths)withWall(performance.now()+1000,()=>withWork(fullWork()+100000,()=>{
    const view=focusGoal(goal,0),out=grow(view,path,{nodes:0})
    if(!('tree'in out))throw Error('expected proof')
    const tree=widen(view,goal,out.tree,{},path,path)
    expect(tree!==undefined&&check(goal,tree,path)).toBe(true)
  }))
})
test('an invalid focus index cannot remove or invent a row',()=>{
  for(const index of [-1,goal.hyps.length,0.5])expect(()=>focusGoal(goal,index)).toThrow('invalid')
})
