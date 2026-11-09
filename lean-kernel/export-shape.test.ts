import {expect, test} from 'bun:test'
import type {C} from '../core/machine.ts'
import type {Tree} from '../kernel/kernel.ts'
import {check} from '../kernel/kernel.ts'
import {encode} from './emit.ts'
import {leanConnective, leanTerms} from './lean-terms.ts'

const atom: C = {op:'<',a:{op:'var',name:'x'},b:{op:'var',name:'y'}}
const term = leanTerms(['x','y'], [], 'singleton-test')
test('singleton connectives retain their row-extraction boundary', () => {
  expect(term.c({op:'or',xs:[atom]})).toBe('.or (.lt (.var 0) (.var 1)) (.lt (.const 0) (.const 0))')
  expect(term.c({op:'and',xs:[atom]})).toBe('.and (.lt (.var 0) (.var 1)) (.le (.const 0) (.const 0))')
  expect(leanConnective('or',[])).toBe('.lt (.const 0) (.const 0)')
  expect(leanConnective('and',[])).toBe('.le (.const 0) (.const 0)')
  expect(leanConnective('or',['a','b','c'])).toBe('.or (a) (.or (b) (c))')
})
test('retained singleton-disjunction tree is encoded without replacing its leaves', () => {
  const goal = {name:'singleton',hyps:[{op:'or',xs:[atom]} as C,{op:'not',x:atom} as C]}
  const tree: Tree = {split:{x:1,y:-1,'1':1},yes:{leaf:[{kind:'input',index:2}]},no:{leaf:[{kind:'input',index:1}]}}
  const before = JSON.stringify({goal,tree})
  expect(check(goal,tree)).toBe(true)
  const out = encode({name:'singleton',goal,tree})
  expect(out.hyps).toContain('.or (.lt (.var 0) (.var 1)) (.lt (.const 0) (.const 0))')
  expect(out.tree).not.toContain('.combine')
  expect(JSON.stringify({goal,tree})).toBe(before)
  expect(check({...goal,hyps:[atom,{op:'not',x:atom}]},tree)).toBe(false)
})
