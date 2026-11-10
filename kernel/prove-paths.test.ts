import {expect,test} from 'bun:test'
import {type C,atMost,get,ite,less,n,not,same,x} from '../core/machine.ts'
import {type Goal,type Path,type Tree,canon,check,foldPinned} from './kernel.ts'
import {clock,grow,widen} from './prove.ts'

test('a constant-folded action proof cannot escape its singleton branch',()=>{
  const cell=get('M',n(0)),value=ite(same(x('op'),n(4)),n(1),cell)
  const goal:Goal={name:'pinned action',hyps:[same(cell,n(2)),not(same(value,n(2)))]}
  const part:Goal={...goal,hyps:goal.hyps.map(c=>foldPinned(c,[['op',3]]))}
  const path:Path=new Map([2,3,4].map(v=>{const lin={op:1,'1':-v};return [canon(lin),{lin,holds:v>=3}]}))
  const proof=grow(part,new Map(),{nodes:0,until:clock()+1000})
  expect('tree'in proof).toBe(true)
  if(!('tree'in proof))return
  const lifted=widen(part,goal,proof.tree,{},new Map(),path)
  expect(lifted&&check(goal,lifted,path)).toBe(true)
  expect(lifted&&check(goal,lifted)).toBe(false)
})

test('rebasing a conditional branch preserves its source and target paths',()=>{
  const split={op:1},id=canon(split),condition=atMost(x('op'),n(0))
  const goal:Goal={name:'conditional rows',hyps:[atMost(x('op'),n(1)),same(x('y'),ite(same(x('op'),n(0)),n(0),n(1))),not(less(x('y'),n(2)))]}
  const bigger:Goal={name:goal.name,hyps:[atMost(x('unused'),n(9)),...goal.hyps]}
  const branches:Tree[]=[]
  for(const holds of [true,false]){
    const path:Path=new Map([[id,{lin:split,holds}]]),guard:C=holds?condition:not(condition)
    const part:Goal={name:goal.name,hyps:[guard,...goal.hyps]},out=grow(part,new Map(),{nodes:0,until:clock()+1000})
    expect('tree'in out).toBe(true)
    if(!('tree'in out))return
    const lifted=widen(part,goal,out.tree,{},new Map(),path)
    expect(lifted&&check(goal,lifted,path)).toBe(true)
    if(!lifted)return
    const rebased=widen(goal,bigger,lifted,{},path,path)
    expect(rebased&&check(bigger,rebased,path)).toBe(true)
    if(!rebased)return
    branches.push(rebased)
  }
  expect(check(bigger,{split,yes:branches[0]!,no:branches[1]!})).toBe(true)
})
