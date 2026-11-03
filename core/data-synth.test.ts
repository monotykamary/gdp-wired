import {expect, test} from 'bun:test'
import {type DataLaw, type Nat, type Val, type Value, type Integer, Bool, data, define, evalY, integer, law, natural, programOf, proveData, refute, self, when} from './data.ts'
import {synthesizedLemmas} from './data-synth.ts'
import {checkCyclic} from '../kernel/cyclic.ts'
import {dataLean} from '../lean-kernel/data.ts'

// Generated names must never replace an existing user definition.
define('observer1', {x: natural}, natural, () => 99)
const List = data('ObserverList', {nil: {}, cons: {head: natural, tail: self}})
const Tree = data('ObserverTree', {nil: {}, node: {left: self, value: natural, right: self}})
const count: ReturnType<typeof define> = define('observerCount', {key: natural, xs: List}, natural, ({key, xs}) => (xs as Val).match({nil: () => 0, cons: ({head, tail}) => when((key as Nat).eq(head), (count(key, tail) as Nat).plus(1), count(key, tail))}))
const flatten: ReturnType<typeof define> = define('observerFlatten', {tree: Tree, acc: List}, List, ({tree, acc}) => (tree as Val).match({nil: () => acc as Val, node: ({left, value, right}) => flatten(left, List.cons(value, flatten(right, acc)))}))
const remove: ReturnType<typeof define> = define('observerRemove', {key: natural, xs: List}, List, ({key, xs}) => (xs as Val).match({nil: () => List.nil, cons: ({head, tail}) => when((key as Nat).eq(head), tail, List.cons(head, remove(key, tail)))}))
const treeLaw = law('flatten preserves each count', {key: natural, tree: Tree, acc: List}, ({key, tree, acc}) => (count(key, flatten(tree, acc)) as Nat).atLeast(count(key, acc)))
const removeLaw = law('remove cannot add occurrences', {key: natural, item: natural, xs: List}, ({key, item, xs}) => (count(key, remove(item, xs)) as Nat).atMost(count(key, xs)))
const checked = (l: DataLaw, lemmas: DataLaw[] = []) => {
  const v = proveData(l, {ms: 20000, transfer: false, lemmas})
  expect(v.proven && v.checked && v.proof?.proven && checkCyclic(v.proof.proof), JSON.stringify({goal: v.goal, stuck: v.stuck, ms: v.ms, tried: v.tried})).toBe(true)
  return v
}

test('a guarded list algebra lifts to both branches of a tree, with an accumulator', () => {
  const ls = synthesizedLemmas(programOf([treeLaw]))
  const c = ls.find(l => l.name.includes('observerFlatten'))!
  expect(c).toBeDefined()
  const p = programOf([c]), observer = p.fns.find(f => f.name.startsWith('observer') && f.params.some(q => q.sort === Tree) && f.ret === natural && f !== flatten.fn)!
  expect(observer).toBeDefined()
  expect(observer.name).not.toBe('observer1')
  expect(observer.decreases).toBeDefined()
  checked(c)
  const broken: DataLaw = {...c, holds: c.holds.op === '=' ? {...c.holds, b: {op: 'nat', value: 0}} : c.holds}
  expect(refute(broken, 500)).toBeDefined()
}, 60000)

test('both sides of a selection guard yield equations, not unconditional axioms', () => {
  const ls = synthesizedLemmas(programOf([removeLaw])), conditional = ls.filter(l => l.name.includes('observerRemove') && l.holds.op === 'or')
  expect(conditional.length).toBe(2)
  for (const c of conditional) {
    const v = checked(c)
    if (!v.proof?.proven || !v.program || v.node === undefined) throw new Error('missing certificate')
    expect(dataLean('guarded', c, v.program, v.proof.proof, v.node, 'guarded')(() => 0, () => 0)).toContain('simp_all <;> omega')
  }
  const present = conditional.find(l => l.name.includes('+'))!
  const eq = (present.holds as {op: 'or', xs: DataLaw['holds'][]}).xs[1]!
  expect(refute({...present, holds: eq}, 500)).toBeDefined()
  const absent = new Map<string, Value>([['o0', 3], ['v0', 3], ['v1', {c: 0, f: []}]])
  expect(evalY(present.holds, absent, {})).toBe(true)
  expect(evalY(eq, absent, {})).toBe(false)
}, 60000)

test('nested containers compose the lifted observer instead of treating containers as elements', () => {
  const Forest = data('ObserverForest', {nil: {}, cons: {tree: Tree, rest: self}})
  const flat: ReturnType<typeof define> = define('observerForestFlatten', {trees: Forest, acc: List}, List, ({trees, acc}) => (trees as Val).match({nil: () => acc as Val, cons: ({tree, rest}) => flatten(tree, flat(rest, acc))}))
  const l = law('forest accumulator', {key: natural, trees: Forest, acc: List}, ({key, trees, acc}) => (count(key, flat(trees, acc)) as Nat).atLeast(count(key, acc)))
  const ls = synthesizedLemmas(programOf([l])), tree = ls.find(l => l.name.includes('observerFlatten'))!, forest = ls.find(l => l.name.includes('observerForestFlatten'))!
  expect(tree).toBeDefined(); expect(forest).toBeDefined()
  checked(forest, [tree])
}, 60000)

test('a non-additive recurrence is not mistaken for an additive observer', () => {
  const power: ReturnType<typeof define> = define('observerPower', {xs: List}, natural, ({xs}) => (xs as Val).match({nil: () => 1, cons: ({tail}) => (power(tail) as Nat).times(2)}))
  const l = law('power after flatten', {tree: Tree}, ({tree}) => (power(flatten(tree, List.nil)) as Nat).atLeast(1))
  expect(synthesizedLemmas(programOf([l]))).toEqual([])
})

test('selection premises come from values, and are independently proved', () => {
  const least: ReturnType<typeof define> = define('observerLeast', {seed: natural, xs: List}, natural, ({seed, xs}) => (xs as Val).match({nil: () => seed as Nat, cons: ({head, tail}) => when((head as Nat).atMost(seed), least(head, tail), least(seed, tail))}))
  const l = law('least is bounded', {seed: natural, xs: List}, ({seed, xs}) => (least(seed, xs) as Nat).atMost(count(seed, xs)))
  const c = synthesizedLemmas(programOf([l])).find(c => c.holds.op === '<' && c.name.includes('observerLeast'))!
  expect(c).toBeDefined()
  checked(c)
}, 60000)

test('signed algebras retain their arithmetic; sampled law and kernel-checked empty case', () => {
  const IL = data('ObserverInts', {nil: {}, cons: {head: integer, tail: self}})
  const IT = data('ObserverIntTree', {nil: {}, node: {left: self, value: integer, right: self}})
  const countI: ReturnType<typeof define> = define('observerIntCount', {key: integer, xs: IL}, integer, ({key, xs}) => (xs as Val).match({nil: () => 0, cons: ({head, tail}) => when((key as Integer).eq(head), (countI(key, tail) as Integer).plus(1), countI(key, tail))}))
  const flatI: ReturnType<typeof define> = define('observerIntFlatten', {tree: IT, acc: IL}, IL, ({tree, acc}) => (tree as Val).match({nil: () => acc as Val, node: ({left, value, right}) => flatI(left, IL.cons(value, flatI(right, acc)))}))
  const l = law('signed flatten', {key: integer, tree: IT, acc: IL}, ({key, tree, acc}) => (countI(key, flatI(tree, acc)) as Integer).atLeast(countI(key, acc)))
  const c = synthesizedLemmas(programOf([l])).find(c => c.name.includes('observerIntFlatten'))!
  expect(c).toBeDefined()
  expect(refute(c, 500)).toBeUndefined()
  const tree = c.vars.find(v => v.sort === IT)!
  const atNil: DataLaw = {...c, vars: c.vars.filter(v => v !== tree), holds: JSON.parse(JSON.stringify(c.holds), (_, v) => v && v.op === 'var' && v.name === tree.name ? IT.nil.x : v) as DataLaw['holds']}
  checked(atNil)
}, 60000)

test('a broken deletion cannot borrow a sampled guarded equation', () => {
  const all: ReturnType<typeof define> = define('observerRemoveAll', {key: natural, xs: List}, List, ({key, xs}) => (xs as Val).match({nil: () => List.nil, cons: ({head, tail}) => when((key as Nat).eq(head), all(key, tail), List.cons(head, all(key, tail)))}))
  const l = law('broken deletion', {key: natural, item: natural, xs: List}, ({key, item, xs}) => (count(key, all(item, xs)) as Nat).atMost(count(key, xs)))
  const ls = synthesizedLemmas(programOf([l]))
  expect(ls.filter(c => c.name.includes('observerRemoveAll') && c.name.includes('+'))).toEqual([])
  // A forged candidate is still refuted by the ordinary prover, not installed as a fact.
  const bad = law('forged remove-all count', {key: natural, xs: List}, ({key, xs}) => new Bool({op: 'or', xs: [{op: 'not', x: (count(key, xs) as Nat).gt(0).y}, (count(key, all(key, xs)) as Nat).plus(1).eq(count(key, xs)).y]}))
  expect(proveData(bad).proven).toBe(false)
})
