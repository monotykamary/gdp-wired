// What the kernel must refuse or reject, one case each, so the mutation run (mutants.ts) sees a change to any of these
// checks: non-natural constants and factors anywhere a machine, loop, fold, history or progress law has terms; names the
// kernel's cells and monomials would read as something else; a rank that reads the turn's input; a fold whose node sets
// other names than its leaf; a proof set where one tree is bad; and a law that holds only under its precondition (a
// kernel that dropped the precondition from its goals could no longer prove it).
import {expect, test} from 'bun:test'
import type {C, E, Law, Machine} from '../core/machine.ts'
import {checkRefutation, checkWitness} from '../core/check.ts'
import {type Fold, type Goal, type Loop, type RecurCases, check, checkLaws, checkRecur, foldObligations, historyMachine, loopObligations, obligations, progressObligations, scope} from './kernel.ts'
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

test('no float is rounded: a true hypothesis past 2^53 is not refuted, nor a certificate with unsafe multipliers accepted', () => {
  // 2^53 - 1 + 3 <= 2^53 - 1 + 1 + 1 + 1 is true (both 2^53 + 2); in floats each + 1 past 2^53 rounds back to 2^53, and the
  // left side would read 2 more than the right (terra's review of gen/laneK, 2026-10-31).
  const big = n(Number.MAX_SAFE_INTEGER), one = n(1)
  const rounded: Goal = {name: 'rounded', hyps: [le(plus(big, n(3)), plus(plus(plus(big, one), one), one))]}
  expect(check(rounded, {leaf: [{kind: 'input', index: 0}]})).toBe(false)
  // A rounded sum brought back under 2^53 by a subtraction: (2^53 - 1 + 1 + 1) ∸ 10 is 2^53 - 9, not 2^53 - 10.
  const back: Goal = {name: 'back', hyps: [le(n(Number.MAX_SAFE_INTEGER - 8), {op: 'sub', a: plus(plus(big, one), one), b: n(10)})]}
  expect(check(back, {leaf: [{kind: 'input', index: 0}]})).toBe(false)
  // x <= 1 and 1 <= x hold at x = 1; multipliers past a safe integer are refused in the integers as in the rationals.
  const rows = [{lin: {x: 1, 1: -1}, label: ''}, {lin: {x: -1, 1: 1}, label: ''}]
  expect(checkRefutation(rows, [{kind: 'input', index: 0}, {kind: 'input', index: 1}, {kind: 'combine', a: 0, b: 1, ma: 2 ** 60, mb: 2 ** 60 + 2 ** 8}])).toBe(false)
  expect(checkRefutation([{lin: {1: 2 ** 60}, label: ''}], [{kind: 'input', index: 0}])).toBe(false)
})

// Each test below is a goal with a model (or a certificate of something false) that a float rounded on the way would
// have let the kernel accept; each holds in exact arithmetic, as Lean's Nat and Int read it.
const lt = (a: E, b: E): C => ({op: '<', a, b}), mul = (k: number, a: E): E => ({op: 'mul', k, a}), sub = (a: E, b: E): E => ({op: 'sub', a, b})
const M = Number.MAX_SAFE_INTEGER

test('no float is rounded: a combination whose product rounds and whose sum cancels it is refused', () => {
  // 1801439850948199x + 1 <= 4y and 5y <= 2251799813685249x + 1 hold at x = 1, y = 450359962737050; five times the
  // first is 9007199254740995x, a float 9007199254740996x, which four times the second cancels: 1 <= 0 (x's 1 lost).
  const rows = [{lin: {x: 1801439850948199, y: -4, 1: 1}, label: ''}, {lin: {x: -2251799813685249, y: 5, 1: -1}, label: ''}]
  const steps = [{kind: 'input', index: 0}, {kind: 'input', index: 1}, {kind: 'combine', a: 0, b: 1, ma: 5, mb: 4}] as const
  expect(checkRefutation(rows, [...steps])).toBe(false)
  expect(checkRefutation(rows, [...steps], false)).toBe(false)
  const goal: Goal = {name: 'cancelled', hyps: [le(plus(mul(1801439850948199, x('x')), n(1)), mul(4, x('y'))), le(mul(5, x('y')), plus(mul(2251799813685249, x('x')), n(1)))]}
  expect(check(goal, {leaf: [...steps]})).toBe(false)
})

test('no float is rounded: a comparison whose difference rounds gives no fact', () => {
  // (x ∸ 2) < 2^53 - 1 and 2^53 - 1 + y <= x and 1 <= y hold at x = 2^53, y = 1. Where x >= 2, the first is
  // x - 2 - (2^53 - 1) + 1 <= 0: its constant -(2^53 + 1) is a float -2^53, plus 1 a safe -(2^53 - 1), so the row read
  // x <= 2^53 - 1, which the second and third refute.
  const goal: Goal = {name: 'rounded difference', hyps: [lt(sub(x('x'), n(2)), n(M)), le(plus(n(M), x('y')), x('x')), le(n(1), x('y'))]}
  const tree = {split: {1: 2, x: -1}, yes: {leaf: [{kind: 'input', index: 1}, {kind: 'input', index: 2}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}, {kind: 'input', index: 3}, {kind: 'combine', a: 2, b: 3, ma: 1, mb: 1}]},
    no: {leaf: [{kind: 'input', index: 0}, {kind: 'input', index: 2}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}, {kind: 'input', index: 3}, {kind: 'combine', a: 2, b: 3, ma: 1, mb: 1}]}} as const
  expect(check(goal, structuredClone(tree) as never)).toBe(false)
})

test('no float is rounded: a choice is not decided by a rounded difference', () => {
  // min(2^53 - 1, 2y ∸ 2) <= 2^53 - 2 and 2^52 <= y hold at y = 2^52 (the min is 2^53 - 2). Where y >= 1, which side
  // is smaller is (2^53 - 1) - (2y - 2) <= 0, its constant 2^53 + 1 a float 2^53; flipped, 1 - 2^53 is safe, and a split
  // on 2y - (2^53 - 1) <= 0 read its no side (y >= 2^52) as min = 2^53 - 1, false at y = 2^52.
  const goal: Goal = {name: 'rounded choice', hyps: [le({op: 'min', a: n(M), b: sub(mul(2, x('y')), n(2))}, n(M - 1)), le(n(2 ** 52), x('y'))]}
  const tree = {split: {1: 2, y: -2},
    yes: {split: {1: -M, y: 2}, yes: {leaf: [{kind: 'input', index: 1}, {kind: 'cut', of: 0, g: 2}, {kind: 'input', index: 3}, {kind: 'combine', a: 1, b: 2, ma: 1, mb: 1}]}, no: {leaf: [{kind: 'input', index: 2}]}},
    no: {leaf: [{kind: 'input', index: 0}, {kind: 'cut', of: 0, g: 2}, {kind: 'input', index: 2}, {kind: 'combine', a: 1, b: 2, ma: 1, mb: 1}]}}
  expect(check(goal, tree as never)).toBe(false)
})

test('no float is rounded: a square or product multiplies safe integers only', () => {
  // 17·x·x + 4503599963078413 <= 553393890x holds at x = 16276291 (it is equality there). The square of
  // t = 4.123105625617661x - 67108866.50121884, multiplied in floats, has the safe integer coefficients 17, -553393890 and
  // 4503599963078412, and is -1 at that x: its row -(t·t) <= 0 and the hypothesis add to 1 <= 0.
  const goal: Goal = {name: 'rounded square', hyps: [le(plus(mul(17, {op: 'prod', a: x('x'), b: x('x')}), n(4503599963078413)), mul(553393890, x('x')))]}
  const t = {x: 4.123105625617661, 1: -67108866.50121884}, at = 3 // the hypothesis's row, the naturality of x·x and x, then the square
  expect(check(goal, {leaf: [{kind: 'input', index: 0}, {kind: 'input', index: at}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}], squares: [t]})).toBe(false)
})

test('no float is rounded: a factor that is not a safe integer gives no form', () => {
  // x < 0.1·(10·x) holds at x = 1 (0.1 as a float is a little more than 1/10); 10 · 0.1 is a float 1, so the form read x < x.
  const goal: Goal = {name: 'fractional factor', hyps: [lt(x('x'), mul(0.1, mul(10, x('x'))))]}
  expect(check(goal, {leaf: [{kind: 'input', index: 0}]})).toBe(false)
})

test('no float is rounded: a nontermination certificate folds no constant past a safe integer', () => {
  // The loop starts at x = 2 and runs while x + (2^53 - 1) + 1 <= 2^53, false there: it ends at once. Folded at x = 2 in
  // floats, 2 + (2^53 - 1) is 2^53 and 2^53 + 1 is 2^53 again, so the case read the guard as true and the turn as kept.
  const l: Loop = {name: 'rounded guard', params: [], inputs: [], state: {x: n(2)}, while: le(plus(plus(x('x'), n(M)), n(1)), n(2 ** 53)), body: {x: x('x')}}
  const set: C = {op: '=', a: x('x'), b: n(2)}, trueC: C = le(n(0), n(0))
  const cert: RecurCases = {start: {}, stem: [], set, wit: {}, cover: {split: {x: 1, 1: -2},
    yes: {split: {1: 2, x: -1}, yes: {leaf: [{kind: 'input', index: 4}]}, no: {leaf: [{kind: 'input', index: 1}, {kind: 'input', index: 3}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]}},
    no: {leaf: [{kind: 'input', index: 0}, {kind: 'input', index: 1}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]}}, cases: [{pins: [['x', 2]], cond: trueC, tree: {leaf: [{kind: 'input', index: 1}]}}]}
  expect(checkRecur(l, cert)).toBe(false)
})

test('no float is rounded: a witness is checked with exact products and sums', () => {
  // 3x - 4y <= 0 fails at x = 3002399751580331, y = 2^51 (it is 1 there); 3x is a float 2^53, which -4y cancels.
  expect(checkWitness([{lin: {x: 3, y: -4}, label: ''}], {x: 3002399751580331, y: 2 ** 51})).toBe(false)
  expect(checkWitness([{lin: {x: 3, y: -4}, label: ''}], {x: 4, y: 3})).toBe(true)
})

test('a law is proven at k#: no further key and no name of the machine may be k#', () => {
  // Before: ∀ k, k#. k = k# read k as k# (k# = k#), and a state named k# made ∀ k. k = 0 read 0 = 0 at the start, so
  // checkLaws accepted "every two naturals are equal" (found by terra's review of gen/laneK2, 2026-10-31).
  const plain: Machine = {name: 'empty', params: [], inputs: [], state: {}, step: {state: {}}}
  const capture: Law = {name: 'every two naturals equal', forall: 'k', keys: ['k#'], holds: {op: '=', a: x('k'), b: x('k#')}}
  expect(() => obligations(plain, [capture])).toThrow(/reserved/)
  const tree = {leaf: [{kind: 'input' as const, index: 0}]}
  expect(() => checkLaws(plain, [capture], {instances: {}, trees: {'every two naturals equal @start': tree, 'every two naturals equal @step': tree}})).toThrow(/reserved/)
  expect(() => obligations({...plain, state: {'k#': n(0)}}, [{name: 'all zero', forall: 'k', holds: {op: '=', a: x('k'), b: n(0)}}])).toThrow(/reserved/)
})
