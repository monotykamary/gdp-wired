// What the kernel must refuse or reject, one case each, so the mutation run (mutants.ts) sees a change to any of these
// checks: non-natural constants and factors anywhere a machine, loop, fold, history or progress law has terms; names the
// kernel's cells and monomials would read as something else; a rank that reads the turn's input; a fold whose node sets
// other names than its leaf; a proof set where one tree is bad; and a law that holds only under its precondition (a
// kernel that dropped the precondition from its goals could no longer prove it).
import {expect, test} from 'bun:test'
import type {C, E, Law, Machine} from '../core/machine.ts'
import {type Fold, type Goal, type Loop, check, checkLaws, foldObligations, historyMachine, loopObligations, obligations, progressObligations, scope} from './kernel.ts'
import {grow, proveLaws} from './prove.ts'

const x = (name: string): E => ({op: 'var', name}), n = (value: number): E => ({op: 'const', value})
const le = (a: E, b: E): C => ({op: '<=', a, b}), plus = (a: E, b: E): E => ({op: 'add', a, b})
const counter: Machine = {name: 'counter', params: ['cap'], inputs: ['k'], state: {s: n(0)}, step: {state: {s: {op: 'if', c: le(plus(x('s'), n(1)), x('cap')), then: plus(x('s'), n(1)), else: x('s')}}}}
const law: Law = {name: 's <= cap', holds: le(x('s'), x('cap'))}

test('non-natural constants and factors are refused wherever terms appear', () => {
  expect(proveLaws(counter, [law]).proven).toBe(true)
  const bad: Machine[] = [
    {...counter, state: {s: n(-1)}},
    {...counter, state: {s: n(0.5)}},
    {...counter, step: {state: {s: {op: 'mul', k: -2, a: x('s')}}}},
    {...counter, step: {state: {s: {op: 'mul', k: 1.5, a: x('s')}}}},
    {...counter, step: {state: {s: {op: 'if', c: le(x('s'), n(-3)), then: x('s'), else: n(0)}}}},
    {...counter, step: {state: {s: {op: 'prod', a: x('s'), b: n(-1)}}}},
    {...counter, step: {state: {s: {op: 'min', a: x('s'), b: n(-1)}}}},
    {...counter, maps: {M: -1}, step: {...counter.step, maps: {M: {key: x('k'), value: n(0)}}}},
    {...counter, maps: {M: 0}, step: {...counter.step, maps: {M: {key: n(-1), value: n(0)}}}},
    {...counter, step: {...counter.step, flags: {f: le(x('s'), n(-1))}}},
  ]
  for (const m of bad) expect(() => obligations(m, [law]), JSON.stringify(m.step)).toThrow()
  expect(() => obligations(counter, [{name: 'negative', holds: le(x('s'), n(-1))}])).toThrow()
  expect(() => obligations({...counter, pre: le(x('cap'), n(-1))}, [law])).toThrow()
})

test('histories: non-natural sums, queries and keep conditions are refused', () => {
  const h: Machine = {name: 'h', params: ['p'], inputs: ['a', 'q'], state: {}, step: {}, history: {keep: le(n(0), n(0)), record: ['a'], sums: {u: x('r.a')}, queries: {q: x('r.a')}}}
  expect(() => historyMachine(h)).not.toThrow()
  expect(() => historyMachine({...h, history: {...h.history!, sums: {u: {op: 'mul', k: -1, a: x('r.a')}}}})).toThrow()
  expect(() => historyMachine({...h, history: {...h.history!, queries: {q: n(-2)}}})).toThrow()
  expect(() => historyMachine({...h, history: {...h.history!, keep: le(x('a'), n(-1))}})).toThrow()
  expect(() => historyMachine({...h, history: {...h.history!, queries: {q2: x('r.a')}}})).toThrow() // a query that isn't an input
  expect(() => historyMachine({...h, history: {...h.history!, record: ['zz']}})).toThrow() // a record that isn't a plain input
  expect(() => historyMachine({...h, history: {...h.history!, sums: {p: x('r.a')}}})).toThrow() // a sum named like a param
  expect(() => historyMachine({...h, history: {...h.history!, sums: {u: x('r.a')}, relations: [{when: le(n(0), n(0)), holds: le(x('u'), plus(x('q'), n(1)))}]}})).toThrow()
})

test('loops, folds and progress laws: their own refusals', () => {
  const loop: Loop = {name: 'count down', params: ['n0'], inputs: ['w'], state: {i: x('n0')}, while: le(n(1), x('i')), body: {i: {op: 'sub', a: x('i'), b: n(1)}}}
  expect(() => loopObligations(loop, [], x('i'))).not.toThrow()
  expect(() => loopObligations(loop, [], {op: 'sub', a: x('w'), b: x('i')})).toThrow() // a rank that reads the turn's input
  expect(() => loopObligations({...loop, body: {i: {op: 'mul', k: -1, a: x('i')}}}, [], x('i'))).toThrow()
  expect(() => loopObligations({...loop, while: le(x('i'), n(-1))}, [], x('i'))).toThrow()
  expect(() => loopObligations(loop, [{name: 'reads w', holds: le(x('w'), x('i'))}], x('i'))).toThrow()
  expect(() => loopObligations(loop, [{name: 'forall', holds: le(n(0), x('i')), forall: 'k'}], x('i'))).toThrow()
  const fold: Fold = {name: 'size', params: [], inputs: ['v'], leaf: {size: n(1)}, node: {size: plus(x('l_size'), x('r_size'))}}
  expect(() => foldObligations(fold, [{name: 'size >= 1', holds: le(n(1), x('size'))}])).not.toThrow()
  expect(() => foldObligations({...fold, node: {other: n(1)}}, [])).toThrow() // the node sets other names
  expect(() => foldObligations({...fold, leaf: {size: n(-1)}}, [])).toThrow()
  expect(() => foldObligations(fold, [{name: 'reads v', holds: le(x('v'), x('size'))}])).toThrow()
  const caps: Machine = {name: 'caps', params: ['cap'], inputs: ['k'], state: {}, maps: {M: 0}, step: {maps: {M: {key: x('k'), value: {op: 'if', c: {op: '<', a: {op: 'get', map: 'M', key: x('k')}, b: x('cap')}, then: plus({op: 'get', map: 'M', key: x('k')}, n(1)), else: {op: 'get', map: 'M', key: x('k')}}}}}}
  const p = {name: 'room', when: le(n(0), n(0)), then: le(n(0), n(0)), request: {k: n(0)}}
  expect(() => progressObligations(caps, [], {}, p)).not.toThrow()
  expect(() => progressObligations(caps, [], {}, {...p, request: {}})).toThrow() // an input left unnamed
  expect(() => progressObligations(caps, [], {}, {...p, request: {k: n(-1)}})).toThrow()
  expect(() => progressObligations(caps, [], {}, {...p, request: {k: x('k')}})).toThrow() // named from the request itself
  expect(() => progressObligations(caps, [], {}, {...p, when: le(x('k'), n(1))})).toThrow()
})

test('names the kernel would read as a constant, a cell or a monomial are refused', () => {
  for (const name of ['1', 'M[x:1]', 'a*b', 'a,b', 'k:2']) expect(() => scope({...counter, inputs: [name]}), name).toThrow()
  // And no goal over such a name is ever refuted when it has a model: '1' at 2 satisfies 2 <= '1'.
  const goal: Goal = {name: 'odd name', hyps: [le(n(2), x('1'))]}
  const out = grow(goal)
  if ('tree' in out) expect(check(goal, out.tree)).toBe(false)
})

test('a proof set with one bad tree is rejected, and a law that needs its precondition is proven with it', () => {
  const pre: Machine = {...counter, params: ['cap', 'step'], pre: le(n(1), x('step')), step: {state: {s: {op: 'if', c: le(plus(x('s'), x('step')), x('cap')), then: plus(x('s'), x('step')), else: x('s')}}}}
  const laws: Law[] = [law, {name: 'step >= 1', holds: le(n(1), x('step'))}]
  const r = proveLaws(pre, laws)
  expect(r.proven).toBe(true) // 'step >= 1' holds only because of the precondition
  const proof = r.proof!
  expect(checkLaws(pre, laws, proof)).toBe(true)
  const name = Object.keys(proof.trees)[0]!
  expect(checkLaws(pre, laws, {...proof, trees: {...proof.trees, [name]: {leaf: []}}})).toBe(false)
  const {[name]: _gone, ...fewer} = proof.trees
  expect(checkLaws(pre, laws, {...proof, trees: fewer})).toBe(false)
})

// Checks over lists must look at every element: one bad element among good ones (the mutation run's survivors).
test('every element is checked, not just one', () => {
  // A non-natural condition inside an `and` with a natural one.
  expect(() => obligations({...counter, step: {...counter.step, flags: {f: {op: 'and', xs: [le(n(0), x('s')), le(x('s'), n(-1))]}}}}, [law])).toThrow()
  // Histories: a second sum, query or record field that breaks the rules while the first doesn't.
  const h: Machine = {name: 'h', params: ['p'], inputs: ['a', 'b', 'q', 'q2'], state: {}, step: {}, history: {keep: le(n(0), n(0)), record: ['a'], sums: {u: x('r.a')}, queries: {q: x('r.a'), q2: x('r.a')}}}
  expect(() => historyMachine(h)).not.toThrow()
  expect(() => historyMachine({...h, history: {...h.history!, sums: {u: x('r.a'), v: x('b')}}})).toThrow() // reads the request
  expect(() => historyMachine({...h, history: {...h.history!, sums: {u: x('r.a'), v: n(-1)}}})).toThrow()
  expect(() => historyMachine({...h, history: {...h.history!, queries: {q: x('r.a'), q2: x('q')}}})).toThrow() // a query reads a query
  expect(() => historyMachine({...h, history: {...h.history!, queries: {q: x('r.a'), q2: n(-1)}}})).toThrow()
  expect(() => historyMachine({...h, history: {...h.history!, queries: {q: x('r.a'), zz: x('r.a')}}})).toThrow() // not an input
  expect(() => historyMachine({...h, history: {...h.history!, record: ['a', 'q']}})).toThrow() // a query recorded
  expect(() => historyMachine({...h, history: {...h.history!, sums: {u: x('r.a'), a: x('r.a')}}})).toThrow() // named like an input
  // A relation with a constant hidden in a product: proven per record, it would sum to + 2n, not + 2.
  const rel = (holds: C) => () => historyMachine({...h, history: {...h.history!, relations: [{when: le(n(0), n(0)), holds}]}})
  expect(rel(le(x('u'), {op: 'mul', k: 2, a: x('q')}))).not.toThrow()
  expect(rel(le(x('u'), {op: 'mul', k: 2, a: n(1)}))).toThrow()
  expect(rel(le(x('u'), plus(x('q'), {op: 'mul', k: 2, a: n(1)})))).toThrow()
  expect(rel(le(x('u'), {op: 'mul', k: 2, a: plus(x('q'), n(1))}))).toThrow()
  // A tuple rank where only the second part reads the turn's input.
  const loop: Loop = {name: 'count down', params: ['n0'], inputs: ['w'], state: {i: x('n0')}, while: le(n(1), x('i')), body: {i: {op: 'sub', a: x('i'), b: n(1)}}}
  expect(() => loopObligations(loop, [], [x('i'), x('w')])).toThrow()
  // A progress law whose request names one input but not the other, or names one with a non-natural term.
  const two: Machine = {name: 'two', params: [], inputs: ['k', 'j'], state: {s: n(0)}, step: {state: {s: plus(x('s'), x('k'))}}}
  const p = {name: 'grows', when: le(n(0), n(0)), then: le(n(0), n(0)), request: {k: n(1), j: n(0)}}
  expect(() => progressObligations(two, [], {}, p)).not.toThrow()
  expect(() => progressObligations(two, [], {}, {...p, request: {k: n(1)}})).toThrow()
  expect(() => progressObligations(two, [], {}, {...p, request: {k: n(1), j: n(-1)}})).toThrow()
  // Folds: a second leaf term that isn't natural, a law with a key, a law that reads an input next to one that doesn't.
  const fold: Fold = {name: 'size', params: [], inputs: ['v'], leaf: {size: n(1), w: n(0)}, node: {size: plus(x('l_size'), x('r_size')), w: n(0)}}
  const ok: Law = {name: 'size >= 1', holds: le(n(1), x('size'))}
  expect(() => foldObligations(fold, [ok])).not.toThrow()
  expect(() => foldObligations({...fold, leaf: {size: n(1), w: n(-1)}}, [ok])).toThrow()
  expect(() => foldObligations(fold, [ok, {name: 'keyed', holds: le(n(0), x('size')), forall: 'k'}])).toThrow()
  expect(() => foldObligations(fold, [ok, {name: 'reads v', holds: le(x('v'), x('size'))}])).toThrow()
})

test('a law whose step goal needs the precondition', () => {
  // s grows by `step` unguarded; s <= cap holds only because the precondition fixes step at 0.
  const fixed: Machine = {name: 'fixed step', params: ['cap', 'step'], inputs: [], state: {s: n(0)}, pre: {op: '=', a: x('step'), b: n(0)}, step: {state: {s: plus(x('s'), x('step'))}}}
  expect(proveLaws(fixed, [law]).proven).toBe(true)
  expect(proveLaws({...fixed, pre: undefined}, [law]).proven).toBe(false)
})
