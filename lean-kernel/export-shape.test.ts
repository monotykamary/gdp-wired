import {expect, test} from 'bun:test'
import type {C, Law, Machine} from '../core/machine.ts'
import type {Tree} from '../kernel/kernel.ts'
import {check, checkLaws, obligations} from '../kernel/kernel.ts'
import {encode, seedStepProof, smachineToLean} from './emit.ts'
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

function ghostFamily(id: string, original: boolean): string {
  const body: C = {op:'<=',a:{op:'const',value:0},b:{op:'const',value:0}}
  const machine: Machine = {name:id,params:[],inputs:[],state:{w:{op:'const',value:0}},step:{state:{w:{op:'var',name:'w'}}}}
  const laws: Law[] = [{name:'a witness exists',holds:body,ex:{vars:['w'],body,ghost:true}}]
  // Fixed one-leaf certificates; no prover call or search is needed by this regression.
  const proof = {instances:{},trees:Object.fromEntries(obligations(machine,laws).map(g =>
    [g.name,{leaf:[{kind:'input' as const,index:g.hyps.length-1}]}]))}
  expect(checkLaws(machine,laws,proof)).toBe(true)
  const incomplete = {...proof,trees:{...proof.trees}}
  delete incomplete.trees[Object.keys(incomplete.trees)[0]!]
  expect(checkLaws(machine,laws,incomplete)).toBe(false)
  seedStepProof(machine,laws,[],{proven:true,checked:true,nodes:0,leaves:0,proof:{laws:proof,instances:{},perStep:{},trees:{}}})
  return smachineToLean(id,machine,laws,original ? {ghosts:['w']} : {})
}

test('a retained ghost family never invents an original-machine declaration', () => {
  const text = ghostFamily('captured_ghost',false)
  expect(text).toContain('SReach captured_ghost_machine ρ μ')
  expect(text).toContain('some_of_subst')
  expect(text).toContain('substC [(0, .var 0)]')
  expect(text).not.toContain('captured_ghost_ghosted')
  expect(text).not.toContain('captured_ghost_ghostOk')
})

test('an explicitly exported scalar ghost still proves the original-machine existential', () => {
  const text = ghostFamily('explicit_ghost',true)
  expect(text).toContain('def explicit_ghost_ghosted : SGhosted')
  expect(text).toContain('SReach explicit_ghost_ghosted.orig ρ μ')
  expect(text).toContain('some_of_ghost explicit_ghost_ghosted explicit_ghost_ghostOk')
})
