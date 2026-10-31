// What the kernel must refuse or reject, one case each, so the mutation run (mutants.ts) sees a change to any of these
// checks: non-natural constants and factors anywhere a machine, loop, fold, history or progress law has terms; names the
// kernel's cells and monomials would read as something else; a rank that reads the turn's input; a fold whose node sets
// other names than its leaf; a proof set where one tree is bad; and a law that holds only under its precondition (a
// kernel that dropped the precondition from its goals could no longer prove it).
import {expect, test} from 'bun:test'
import type {C, E, Law, Machine} from '../core/machine.ts'
import {checkRefutation, checkWitness} from '../core/check.ts'
import {type Fold, type Goal, type Loop, type QE, type QGoal, type RecurCases, type StepLaw, type Tree, check, checkQTree, checkLaws, checkRecur, checkStepLaws, foldObligations, historyMachine, loopObligations, obligations, progressObligations, scope, stepLawObligations, termColumn} from './kernel.ts'
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

// The names the kernel makes (a flag's ?f and witness w?f, a state after a step s~1, the state after the step s', a
// term's column ⟦n⟧) are reserved, a later step's (a@2, I@2) kept apart from the machine's, and a fold's children's
// copies (l_n, r_n) are no names of the fold: before, a name of the machine or a step law's key spelled like one was
// read as the kernel's own, and each certificate below was accepted of something false. Lean's twin refuses the ?f
// param, I@2, s~1 and l_size ones (checkSMachine, checkSKStep, checkFold compute false); it reads a step law's key ?f
// as the flag's value.
const get = (map: string, key: E): E => ({op: 'get', map, key})
// A flag f at every key, 1 while no cell of M passes 3 (none ever does): s is 1 after any step.
const flagged: Machine = {name: 'flagged', params: [], inputs: [], state: {s: n(0)}, maps: {M: 0},
  step: {flags: {f: {op: 'all', key: 'k', c: le(get('M', x('k')), n(3))}}, state: {s: {op: 'if', c: {op: 'flag', name: 'f'}, then: n(1), else: n(0)}}}}

test('reserved names: ?, a param ?f read as the flag f\'s variable', () => {
  // s <= ?f is false at ?f = 0 after one step (s = 1); the param was the flag's 0/1 variable, which is 1 where s is.
  const m: Machine = {...flagged, params: ['?f']}, laws: Law[] = [{name: 's <= ?f', holds: le(x('s'), x('?f'))}]
  const proof = {instances: {'s <= ?f': {'?f': [x('w?f')]}}, trees: {
    's <= ?f @start': {leaf: [{kind: 'input', index: 0}, {kind: 'input', index: 1}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]},
    's <= ?f @step': {split: {1: -1, '?f': 1}, yes: {split: {1: 1, '?f': -1}, yes: {leaf: [{kind: 'input', index: 5}]},
      no: {leaf: [{kind: 'input', index: 5}, {kind: 'input', index: 6}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]}},
    no: {leaf: [{kind: 'input', index: 0}, {kind: 'input', index: 4}, {kind: 'combine', a: 1, b: 0, ma: 1, mb: 1}]}},
  }} as {instances: Record<string, Record<string, E[]>>, trees: Record<string, Tree>}
  expect(() => checkLaws(m, laws, proof)).toThrow(/reserved/)
  for (const name of ['?f', 'w?f', 'w2?f']) expect(() => scope({...flagged, params: [name]}), name).toThrow(/reserved/)
  // A step law's key ?f: "every natural is at most 1" read as the flag's variable, which is.
  expect(() => stepLawObligations(flagged, [], {}, {name: 'every natural is at most 1', forall: '?f', then: le(x('?f'), n(1))})).toThrow(/reserved/)
  // A progress law reads its machine as obligations does: when ?f = 0 (the param) met ?f = 1 (the flag, whose body
  // always holds), so any `then` followed, 1 <= 0 too.
  expect(() => progressObligations({...flagged, params: ['?f']}, [], {}, {name: 'p', when: {op: '=', a: x('?f'), b: n(0)}, then: le(n(1), n(0)), request: {}})).toThrow(/reserved/)
})

test('later steps\' names (a@2, I@2, ?f@2): a function I@2 read as the second request\'s carried map', () => {
  // Two steps add I[0] of the first request and I[0] of the second; the second's map is I@2, so a function I@2 at 0
  // made "two steps add the first request's I[0] only" provable.
  const m: Machine = {name: 'carried', params: [], inputs: [], inputMaps: ['I'], state: {s: n(0)}, fns: {'I@2': {js: 'x => 0', lean: 'fun _ => 0'}},
    facts: [{name: 'zero', forall: 'k', holds: le(get('I@2', x('k')), n(0))}], step: {state: {s: plus(x('s'), get('I', n(0)))}}}
  const sl: StepLaw = {name: 'two steps add the first only', then: le(x('s\''), plus(x('s'), get('I', n(0)))), steps: 2}
  expect(() => stepLawObligations(m, [], {zero: [n(0)]}, sl)).toThrow(/a name a step law reads/)
  // '@' is not reserved (compose's steps names inputs x@s1): a later step's names are kept apart from each name instead,
  // a flag's variable too (a flag f@2 beside f: ?f@2 is both).
  const two: Machine = {...flagged, step: {...flagged.step, flags: {...flagged.step.flags, 'f@2': le(x('s'), n(1))}}}
  expect(() => stepLawObligations(two, [], {}, {name: 'two', then: le(n(0), n(0)), steps: 2})).toThrow(/a name a step law reads/)
  expect(() => stepLawObligations({...counter, params: ['cap', 'k@s1']}, [], {}, {name: 'two', then: le(n(0), n(0)), steps: 2})).not.toThrow()
})

test('reserved names: ~, a step law\'s key s~1 read as the state after the first step', () => {
  // s is 0 after every step; a key named s~1 was that state, so "every natural is 0" was accepted over two steps.
  const m: Machine = {name: 'zero', params: [], inputs: [], state: {s: n(0)}, step: {state: {s: n(0)}}}
  const sl: StepLaw = {name: 'every natural is 0', forall: 's~1', then: le(x('s~1'), n(0)), steps: 2}
  const trees: Record<string, Tree> = {'every natural is 0 @2 steps': {leaf: [{kind: 'input', index: 0}, {kind: 'input', index: 2}, {kind: 'combine', a: 1, b: 0, ma: 1, mb: 1}]}}
  expect(() => checkStepLaws(m, [], [sl], {laws: {instances: {}, trees: {}}, instances: {}, trees})).toThrow(/reserved/)
  expect(() => scope({...counter, params: ['cap', 's~1']})).toThrow(/reserved/)
})

test('reserved names: \', the state and maps after the step (s\', M\')', () => {
  // s' is s after the step in a step law, a progress law and liveness: a state named s' beside s reads either way.
  expect(() => scope({...counter, state: {s: n(0), 's\'': n(0)}})).toThrow(/reserved/)
  expect(() => scope({...counter, maps: {'M\'': 0}})).toThrow(/reserved/)
  // And a term's column: a map named ⟦0⟧ made a cell the leaf took for a column.
  expect(() => scope({...counter, maps: {'⟦0⟧': 0}})).toThrow(/reserved/)
})

test('rationals: a variable spelled like a row is no variable (x:1,y would be read as x + y)', () => {
  // x = y = 0, v = 10, min(v, 5) <= 5 hold together. A row's key is its canonical text, and v named x:1,y has the text
  // of x + y: a split on x + y <= 5 decided min(v, 5) as v, so v <= 5 met v = 10, and the other side met x = y = 0.
  const qv = (name: string): QE => ({op: 'var', name}), qn = (num: number): QE => ({op: 'const', q: {num: BigInt(num), den: 1n}})
  const v = qv('x:1,y'), goal: QGoal = {name: 'a row named', hyps: [{op: '=', a: qv('x'), b: qn(0)}, {op: '=', a: qv('y'), b: qn(0)}, {op: '=', a: v, b: qn(10)}, {op: '<=', a: {op: 'min', a: v, b: qn(5)}, b: qn(5)}]}
  const tree: Tree = {split: {x: 1, y: 1, 1: -5},
    yes: {leaf: [{kind: 'input', index: 6}, {kind: 'input', index: 7}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]},
    no: {leaf: [{kind: 'input', index: 0}, {kind: 'input', index: 1}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}, {kind: 'input', index: 3}, {kind: 'combine', a: 2, b: 3, ma: 1, mb: 1}]}}
  expect(checkQTree(goal, tree)).toBe(false)
})

test('a fold\'s names are not its children\'s copies: a param l_size read as the left child\'s size', () => {
  // The node's size is the param l_size (5, say); read as the left child's size (at most 1), size <= 1 was accepted.
  const fold: Fold = {name: 'capped', params: ['l_size'], inputs: [], leaf: {size: n(0)}, node: {size: x('l_size')}}
  expect(() => foldObligations(fold, [{name: 'size <= 1', holds: le(x('size'), n(1))}])).toThrow(/copy/)
  expect(() => foldObligations({...fold, params: ['p']}, [{name: 'size <= 1', holds: le(x('size'), n(1))}])).not.toThrow()
})

// The mutation run's survivors of 2026-10-31 (kernel/MUTANTS.md): a certificate or a machine each mutant answers
// otherwise than the kernel. The first two are certificates of something false that the mutant accepts.
test('termRows: a column whose sides the path leaves without a form gives no row', () => {
  // z >= 1 and min(x, if(z >= 1, 2^60, y)) >= 1 hold at x = y = z = 1. Where z >= 1 the if's form is 2^60's, none (past
  // a safe integer), so the min's column has no bounds there; read as min(x, nothing) it was col <= x and col <= 0.
  const T: E = {op: 'min', a: x('x'), b: {op: 'if', c: le(n(1), x('z')), then: n(2 ** 60), else: x('y')}}, col = termColumn(T)
  const goal: Goal = {name: 'a column without bounds', hyps: [le(n(1), x('z')), le(n(1), T)]}
  const tree: Tree = {split: {[col]: 1},
    yes: {leaf: [{kind: 'input', index: 0}, {kind: 'input', index: 2}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]},
    no: {split: {1: 1, z: -1},
      yes: {leaf: [{kind: 'input', index: 0}, {kind: 'input', index: 4}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]},
      no: {leaf: [{kind: 'input', index: 1}, {kind: 'input', index: 2}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]}}}
  expect(check(goal, tree)).toBe(false)
})

test('products: a factor that is not a safe integer gives no product, so a fractional split stays unusable', () => {
  // x = 3 holds 3 <= x and x <= 3. A split on x/2 - 1 <= 0 is no split over the integers (x = 3 is on neither side), and
  // its rows can't be read; times 2 (the row 0 <= 2) they would be x <= 2 and x >= 4, each refuting one side.
  const goal: Goal = {name: 'fractional split', hyps: [le(n(3), x('x')), le(x('x'), n(3)), le(n(0), n(2))]}
  const tree: Tree = {split: {x: 0.5, 1: -1},
    yes: {leaf: [{kind: 'input', index: 5}, {kind: 'input', index: 1}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}], products: [[0, 3]]},
    no: {leaf: [{kind: 'input', index: 5}, {kind: 'input', index: 2}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}], products: [[0, 3]]}}
  expect(check(goal, tree)).toBe(false)
})

test('a term is one column however its parts list their fields', () => {
  // 1 <= min(x, y) and min(x, y) <= 0, the second built with its parts' fields in another order: one column, refuted.
  const goal: Goal = {name: 'one column', hyps: [le(n(1), {op: 'min', a: x('x'), b: x('y')}), le({op: 'min', a: {name: 'x', op: 'var'} as E, b: x('y')}, n(0))]}
  expect(check(goal, {leaf: [{kind: 'input', index: 0}, {kind: 'input', index: 1}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]})).toBe(true)
})

test('a multiple by 0 is natural', () => {
  expect(() => obligations({...counter, step: {state: {s: {op: 'mul', k: 0, a: x('s')}}}}, [law])).not.toThrow()
})

test('a progress law: its when, request and precondition read what they may, all of it', () => {
  const grow: Machine = {name: 'grow', params: ['cap'], inputs: ['k'], state: {s: n(0)}, step: {state: {s: plus(x('s'), x('k'))}}}
  const p = {name: 'grows', when: le(n(0), n(0)), then: le(n(0), n(0)), request: {k: n(1)}}
  expect(() => progressObligations(grow, [], {}, p)).not.toThrow()
  expect(() => progressObligations(grow, [], {}, {...p, when: le(x('k'), x('cap'))})).toThrow() // the request's input beside a param
  expect(() => progressObligations(grow, [], {}, {...p, request: {k: plus(x('k'), x('cap'))}})).toThrow()
  expect(() => progressObligations({...grow, pre: {op: '=', a: x('s'), b: n(0)}}, [], {}, p)).toThrow() // a precondition about the state
  expect(() => progressObligations({...grow, pre: le(x('s'), x('cap'))}, [], {}, p)).toThrow() // the state beside a param
  // And a history's record goals, which read the precondition where no scope has: an input, alone or beside a param.
  const h: Machine = {name: 'h', params: ['p'], inputs: ['a', 'q'], state: {}, step: {}, history: {keep: le(n(0), n(0)), record: ['a'], sums: {u: x('r.a')}, queries: {q: x('r.a')},
    relations: [{when: le(n(0), n(0)), holds: le(x('u'), x('q'))}]}}
  expect(() => historyMachine(h)).not.toThrow()
  expect(() => historyMachine({...h, pre: le(x('a'), n(1))})).toThrow()
  expect(() => historyMachine({...h, pre: le(x('a'), x('p'))})).toThrow()
})

test('a flag over two keys compares them plainly anywhere, in a comparison or a term', () => {
  const at = (key: E): E => ({op: 'get', map: 'I', key}), k1 = x('k'), j = x('j'), lt = (a: E, b: E): C => ({op: '<', a, b}), eq = (a: E, b: E): C => ({op: '=', a, b})
  const bit = (c: C): E => ({op: 'if', c, then: n(1), else: n(0)})
  const body: C = {op: 'or', xs: [lt(k1, j), le(k1, j), eq(k1, j),
    le(at(k1), plus(bit(lt(k1, j)), at(j))), le(at(k1), {op: 'sub', a: at(j), b: bit(le(k1, j))}), le(at(k1), {op: 'min', a: bit(eq(k1, j)), b: at(j)}),
    le(at(k1), {op: 'max', a: bit(lt(k1, j)), b: at(j)}), le(at(k1), {op: 'prod', a: bit(lt(k1, j)), b: at(j)})]}
  const m: Machine = {name: 'pairs', params: [], inputs: ['a'], state: {r: n(0)}, inputMaps: ['I'],
    step: {flags: {f: {op: 'all', key: 'k', keys: ['j'], c: body}}, state: {r: {op: 'if', c: {op: 'flag', name: 'f'}, then: n(1), else: n(0)}}}}
  expect(() => scope(m)).not.toThrow()
})
