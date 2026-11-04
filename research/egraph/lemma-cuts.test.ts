import {test,expect} from 'bun:test'
import {canon,type Goal} from '../../kernel/kernel.ts'
import {lemmaCuts} from './lemma-cuts.ts'
const goal:Goal={name:'cut',hyps:[{op:'or',xs:[{op:'<=',a:{op:'var',name:'x'},b:{op:'var',name:'y'}},{op:'<',a:{op:'var',name:'x'},b:{op:'var',name:'y'}}]}]}
const tail={split:{op:1,'1':-4}}
test('lemma cut is the exact arithmetic arm, with its false branch focused not assumed',()=>{
  const p=lemmaCuts(goal,[0],tail),split=p.cuts[0]!.split
  expect(split).toEqual({x:1,y:-1});expect(p.hint.yes).toBe(tail)
  expect(p.focusIndex(new Map([[canon(split),{lin:split,holds:false}]]),7)).toBe(0)
  expect(p.focusIndex(new Map([[canon(split),{lin:split,holds:true}]]),7)).toBe(7)
})
test('invalid, duplicate and non-lemma rows are refused',()=>{
  expect(()=>lemmaCuts(goal,[0,0],tail)).toThrow('invalid')
  expect(()=>lemmaCuts(goal,[2],tail)).toThrow('arithmetic')
  expect(()=>lemmaCuts({name:'bad',hyps:[{op:'not',x:goal.hyps[0]!}]},[0],tail)).toThrow('arithmetic')
})
