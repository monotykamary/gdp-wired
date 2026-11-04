import {test,expect} from 'bun:test'
import {check,type Goal} from '../../kernel/kernel.ts'
import {grow} from '../../kernel/prove.ts'
import {decisionAction,guidedSplit} from './guided-split.ts'
const goal:Goal={name:'false',hyps:[{op:'<',a:{op:'const',value:0},b:{op:'const',value:0}}]}
const hint={split:{op:1,'1':-5},yes:{split:{op:-1,'1':5}}}
test('decision action uses engine condition tags and only positive conjunctions',()=>{
  const atom={op:'=' as const,a:{op:'var' as const,name:'op'},b:{op:'const' as const,value:5}}
  expect(decisionAction({op:'and',xs:[atom,goal.hyps[0]!]})).toBe(5)
  expect(()=>decisionAction({op:'not',x:atom})).toThrow('ambiguous')
  expect(()=>decisionAction({op:'or',xs:[atom]})).toThrow('ambiguous')
  expect(()=>decisionAction({op:'and',xs:[atom,atom]})).toThrow('ambiguous')
  expect(()=>decisionAction(undefined)).toThrow('ambiguous')
})
test('guided cuts preserve the same entire goal and prove every branch',()=>{
  const paths:number[]=[]
  const out=guidedSplit(goal,hint,(g,p)=>{expect(g).toBe(goal);paths.push(p.size);return grow(g,p)})
  expect(paths).toEqual([1,2,2]);expect('tree'in out&&check(goal,out.tree)).toBe(true)
})
test('one open branch cannot be promoted to a proof',()=>{
  const out=guidedSplit(goal,hint,(_g,p)=>({stuck:'unknown',path:p}))
  expect('tree'in out).toBe(false)
})
test('repeated and constant cuts are refused',()=>{
  const ask=(_g:Goal,p:Parameters<typeof grow>[1])=>grow(goal,p)
  expect(()=>guidedSplit(goal,{split:hint.split,no:{split:hint.split}},ask)).toThrow('invalid')
  expect(()=>guidedSplit(goal,{split:{'1':2}},ask)).toThrow('invalid')
})
