// There exists (core/exists.ts): laws with exists(...) are proven through a witness the kernel's counterexamples choose
// (a term of the state, or a ghost the machine carries), the kernel seeing only plain laws of a plain machine; a false
// one is refused (by a run, where no value can be a witness, or for want of a witness), a witness given that doesn't
// satisfy the law is refused by the kernel; an existential in the assumption is a value each request brings; inferLaws
// finds congruences as existentials; the Lean export states each as ∃, proven by ⟨witness, proof⟩.
import {expect, test} from 'bun:test'
import {type Law, evalC, interpret} from './machine.ts'
import {exists, int, nat, oneOf, proveRule, proveSteps, rule, when} from './dsl.ts'
import {proveSome, someHolds} from './exists.ts'
import {inferLaws} from './infer.ts'
import {proveLaws} from '../kernel/prove.ts'
import {toLean} from '../lean-kernel/emit.ts'
import {evenLaws, evens, ledger, ledgerLaws, leanItems, memberLaws, members, window, windowLaws} from '../examples/exists.ts'

test('the examples: each law proven through a witness, each broken variant refused by a run', () => {
  for (const [r, laws] of [[evens(), evenLaws], [members(), memberLaws], [ledger(), ledgerLaws], [window(), windowLaws]] as const) {
    const v = proveRule(r as never, (laws as (r: never) => Law[])(r as never), {search: false})
    expect(v, r.machine.name).toMatchObject({proven: true, checked: true})
    expect(Object.keys(v.witnesses ?? {}).length).toBe(1)
  }
  for (const [r, laws] of [[evens('steps by 3'), evenLaws], [members('drops a name'), memberLaws], [ledger('charges a fee of 1'), ledgerLaws]] as const) {
    const v = proveRule(r as never, (laws as (r: never) => Law[])(r as never), {search: false})
    expect(v.proven, r.machine.name).toBe(false)
    expect(v.run, r.machine.name).toBeDefined()
  }
}, 120_000)

test('the kernel sees plain laws: a witness term in place, or ghosts the machine gains', () => {
  const w = window(), out = proveLaws(w.machine, windowLaws(w))
  expect(out.proven && out.checked).toBe(true)
  const law = out.laws![0]!
  expect(law.some).toBeUndefined()
  expect(law.ex?.sub).toBeDefined()
  expect(JSON.stringify(law.holds)).not.toContain('some$')
  const e = evens(), ghosted = proveLaws(e.machine, evenLaws(e))
  expect(ghosted.proven && ghosted.checked).toBe(true)
  expect(ghosted.ghosts?.length).toBe(1)
  expect(Object.keys(ghosted.machine!.state)).toContain(ghosted.ghosts![0]!)
  // The original machine's state and step are untouched: the ghost is read by no part of it.
  for (const [n, t] of Object.entries(e.machine.step.state ?? {})) expect(ghosted.machine!.step.state![n]).toEqual(t)
}, 60_000)

test('a witness given that does not satisfy the law is refused by the kernel, with its counterexample', () => {
  const w = window(), v = proveRule(w, windowLaws(w, 'hi + 1'), {search: false})
  expect(v.proven).toBe(false)
  expect(v.why).toContain('witness given')
  expect(v.stuck).toBe('sat')
  // A ghost witness given that moves the wrong way.
  const e = evens(), bad = e.law('x is even', ({x}) => exists(k => x.eq(k.times(2)), {start: 0, step: k => k.plus(2)}))
  expect(proveRule(e, [bad], {search: false})).toMatchObject({proven: false, stuck: 'sat'})
}, 60_000)

test('a false existential is refused: no witness at a reachable state (a run), or none found', () => {
  const e = evens()
  // x + 1 is never even: at the start, no k makes 0 + 1 = 2k (decided exactly: one natural read linearly).
  expect(proveRule(e, [e.law('x is odd', ({x}) => exists(k => x.plus(1).eq(k.times(2))))], {search: false}).run).toBeDefined()
  // Some value above x and below x (none): refused.
  const v = proveRule(e, [e.law('a value strictly between x and x + 1', ({x}) => exists(k => x.lt(k).and(k.lt(x.plus(1)))))], {search: false})
  expect(v.proven).toBe(false)
}, 60_000)

test('exists under a not, or on the left of implies, is refused where it is written', () => {
  const e = evens()
  expect(() => e.law('no k', ({x}) => exists(k => x.eq(k.times(2))).not())).toThrow(/for every value/)
  expect(() => e.law('if some k', ({x}) => exists(k => x.eq(k.times(2))).implies(x.atLeast(0)))).toThrow(/for every value/)
})

test('an existential in the assumption: a value each request brings, found by encodeInput', () => {
  const l = ledger(), m = l.machine
  expect(m.inputs).toEqual(['amount', 'amount$neg', 'some$a0', 'some$a0$neg'])
  expect(l.encodeInput({amount: -15} as never)).toMatchObject({amount: 0, amount$neg: 15, some$a0: 0, some$a0$neg: 3})
  const run = interpret(m), st = run.init({})
  // A request no witness makes a multiple of 5 fails the assumption: the runtime refuses it.
  expect(() => run.step({}, st, l.encodeInput({amount: 7} as never))).toThrow(/assumption/)
  expect(l.decode(run.step({}, st, l.encodeInput({amount: 10} as never))).balance).toBe(10)
  // Each request's own: a fresh value every step (an input), so two steps take two witnesses.
  expect(m.state['some$a0']).toBeUndefined()
})

test('someHolds: exact for one natural or integer read linearly, and for a natural read as a map key', () => {
  const r = rule('r').state({x: 0}).maps({M: 0}), m = r.machine
  const x = {op: 'var', name: 'x'} as const, k = {op: 'var', name: 'k'} as const
  const twice = {op: '=', a: x, b: {op: 'mul', k: 2, a: k}} as const
  expect(someHolds(twice, ['k'], {}, {scalars: {x: 6}, maps: {M: new Map()}}, m)).toMatchObject({holds: true, witness: {k: 3}})
  expect(someHolds(twice, ['k'], {}, {scalars: {x: 7}, maps: {M: new Map()}}, m)).toEqual({holds: false})
  const cell = {op: '=', a: {op: 'get', map: 'M', key: k}, b: {op: 'const', value: 5}} as const
  expect(someHolds(cell, ['k'], {}, {scalars: {x: 0}, maps: {M: new Map([[40, 5]])}}, m)).toMatchObject({holds: true, witness: {k: 40}})
  expect(someHolds(cell, ['k'], {}, {scalars: {x: 0}, maps: {M: new Map([[40, 4]])}}, m)).toEqual({holds: false})
  // An integer: x = 2z at x = −6 (z = −3), as two naturals.
  const iz = {op: '=', a: {op: 'add', a: x, b: {op: 'mul', k: 2, a: {op: 'var', name: 'z$neg'}}}, b: {op: 'mul', k: 2, a: {op: 'var', name: 'z'}}} as const
  const hit = someHolds(iz, ['z', 'z$neg'], {}, {scalars: {x: 6}, maps: {M: new Map()}}, m)
  expect(hit?.holds).toBe(true)
  expect(evalC(iz, {...hit!.witness}, {scalars: {x: 6}, maps: {}}, m)).toBe(true)
})

test('with step laws, and in a rule proven by proveSteps', () => {
  const e = evens()
  const up = e.stepLaw('up adds 2', ({x}, after) => after.x.eq(x.plus(2)), ({go}) => go.is('up'))
  expect(proveSteps(e, evenLaws(e), [up], {search: false})).toMatchObject({proven: true, checked: true})
}, 60_000)

test('inferLaws finds a congruence as an existential, with the source to paste (remainders off; by default the same claim is a remainder)', () => {
  const r = rule('steps of two').inputs({go: oneOf('up', 'down', 'stay')}).state({x: 0})
    .step(({go, x}) => ({x: when(go.is('up'), x.plus(2), when(go.is('down'), x.minus(2), x))}))
  const plain = inferLaws(r, [r.law('x is never 7', ({x}) => x.ne(7))], [], {ms: 15000})
  expect(plain).toMatchObject({proven: true, checked: true})
  expect(plain.found.map(f => f.text)).toContain('x mod 2 = 0')
  const v = inferLaws(r, [r.law('x is never 7', ({x}) => x.ne(7))], [], {ms: 15000, remainders: false})
  expect(v).toMatchObject({proven: true, checked: true})
  expect(v.found.map(f => f.source)).toContain("r.law('∃k. x = 2·k', ({x}) => exists(k => x.eq(k.times(2))))")
  const off = inferLaws(r, [r.law('x is never 7', ({x}) => x.ne(7))], [], {ms: 3000, remainders: false, existentials: false})
  expect(off.found.some(f => f.law.some)).toBe(false)
}, 60_000)

test('integers and several bound values: a witness per value, the laws proven together', () => {
  const r = rule('pair').inputs({d: int}).ints({a: 0, b: 0}).step(({a, b, d}) => ({a: a.plus(d), b: b.plus(d.times(3))}))
  const v = proveSome(r.machine, [r.law('b is 3a', ({a, b}) => exists(int, z => z.eq(a).and(b.eq(z.times(3)))))])
  expect(v.proven && v.checked).toBe(true)
  void nat
}, 60_000)

test('the Lean export states each law as ∃, from a witness term (some_of_subst) or ghosts (some_of_ghost)', () => {
  for (const cyclic of [false, true]) {
    const text = toLean(leanItems(), {cyclic})
    expect(text).toContain('import Ghost')
    expect(text).toContain('theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : SReach evens_ghosted.orig ρ μ) : ∃ w1 : Nat, ρ «x» = (2 * w1)')
    expect(text).toContain('some_of_ghost members_ghosted members_ghostOk')
    expect(text).toContain('∃ w1 : Nat, (ρ «lo» ≤ w1 ∧ w1 ≤ ρ «hi»)')
    expect(text).toContain('some_of_subst')
    expect(text).toContain('#print axioms window.some0')
  }
}, 120_000)
