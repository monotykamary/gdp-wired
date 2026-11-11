import {expect,test} from 'bun:test'
import {type Goal,type Path,type Tree,check} from '../kernel/kernel.ts'
import {clock} from '../kernel/prove.ts'
import {atMost,n,x} from './machine.ts'
import {replayLinearSkeleton} from './count-replay-skeleton.ts'

const modes=[undefined,{deferCheck:false},{deferCheck:true}]
test('strict and deferred skeleton replay construct the same natively checked proof',()=>{
 const goal:Goal={name:'contradiction',hyps:[atMost(x('a'),n(0)),atMost(n(1),x('a'))]},hint:Tree={leaf:[]},root:Path=new Map(),before=JSON.stringify([hint,[...root]])
 const strict=replayLinearSkeleton(goal,hint,root,Infinity)
 expect(strict).toBeDefined()
 for(const options of modes){
  const tree=replayLinearSkeleton(goal,hint,root,Infinity,options)
  expect(tree).toEqual(strict)
  expect(tree&&check(goal,tree,root)).toBe(true)
 }
 expect(JSON.stringify([hint,[...root]])).toBe(before)
})
test('deferring duplicate checks cannot make a satisfiable skeleton into a proof',()=>{
 const goal:Goal={name:'satisfiable',hyps:[atMost(x('a'),n(0))]},hint:Tree={leaf:[]}
 for(const options of modes)expect(replayLinearSkeleton(goal,hint,new Map(),Infinity,options)).toBeUndefined()
})
test('every skeleton replay mode respects an expired deadline without mutation',()=>{
 const goal:Goal={name:'contradiction',hyps:[atMost(n(1),n(0))]},hint:Tree={leaf:[]},root:Path=new Map(),before=JSON.stringify([hint,[...root]])
 for(const options of modes)expect(replayLinearSkeleton(goal,hint,root,clock()-1,options)).toBeUndefined()
 expect(JSON.stringify([hint,[...root]])).toBe(before)
})
