import {expect,test} from 'bun:test'
import {atMost,n,x} from '../core/machine.ts'
import {check} from './kernel.ts'
import {clock,grow,treeReuseStats,withTrees} from './prove.ts'
test('completed exact goals serve another law name within one scope',()=>{
 const goal={name:'first law',hyps:[atMost(n(1),n(0))]},before=treeReuseStats.hits
 withTrees(()=>{
  const first=grow(goal,new Map(),{nodes:0,until:clock()+1000}),second=grow({...goal,name:'second law'},new Map(),{nodes:0,until:clock()+1000})
  expect('tree'in first&&'tree'in second).toBe(true)
  if('tree'in first&&'tree'in second){expect(second.tree).toBe(first.tree);expect(check(goal,second.tree)).toBe(true)}
 })
 expect(treeReuseStats.hits-before).toBe(1)
 const after=treeReuseStats.hits;grow(goal,new Map(),{nodes:0,until:clock()+1000});expect(treeReuseStats.hits).toBe(after)
})
test('changed assumptions and unknown results never become cached proofs',()=>{
 withTrees(()=>{
  const bad={name:'contradiction',hyps:[atMost(n(1),n(0))]},possible={name:'possible',hyps:[atMost(n(0),x('n'))]}
  grow(bad,new Map(),{nodes:0,until:clock()+1000})
  const before=treeReuseStats.hits
  for(let i=0;i<2;i++)expect('tree'in grow(possible,new Map(),{nodes:0,until:clock()+1000})).toBe(false)
  expect(treeReuseStats.hits).toBe(before)
 })
})
