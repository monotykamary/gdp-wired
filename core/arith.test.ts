// Division and remainder by a constant (core/dsl.ts modBy, divBy; core/machine.ts arithmetic): the examples proven and
// their broken variants refused, the facts true of what the runtimes compute, integers by Euclid's rule, the remainders
// inferLaws finds.
import {expect, test} from 'bun:test'
import {Int, bool, int, nat, proveDecision, proveRule, rule, when} from './dsl.ts'
import {arithmetic, evalC, interpret, withArithmetic} from './machine.ts'
import {inferLaws} from './infer.ts'
import {billing, billingLaws, evenLaw, ledger, ledgerLaws, pairs, pairsLaw, rota, rotaLaws} from '../examples/arith.ts'

const proven = (v: {proven: boolean, checked: boolean}) => v.proven && v.checked

test('the examples are proven and their broken variants refused', () => {
  expect(proven(proveRule(rota(), rotaLaws(rota()), {search: false}))).toBe(true)
  expect(proven(proveRule(rota('lead by the day'), rotaLaws(rota('lead by the day')), {search: false}))).toBe(false)
  expect(proven(proveRule(billing(), billingLaws(billing()), {search: false}))).toBe(true)
  expect(proven(proveRule(billing('rounds down'), billingLaws(billing('rounds down')), {search: false}))).toBe(false)
  expect(proven(proveRule(pairs(), [evenLaw()], {search: false}))).toBe(true)
  expect(proven(proveRule(pairs('odd refill'), [evenLaw(pairs('odd refill'))], {search: false}))).toBe(false)
  expect(proven(proveRule(ledger(), ledgerLaws(ledger()), {search: false}))).toBe(true)
  expect(proven(proveRule(ledger('a fee of 1'), ledgerLaws(ledger('a fee of 1')), {search: false}))).toBe(false)
})

test('a broken law is refused with a run that breaks it', () => {
  const r = pairs('odd refill'), v = proveRule(r, [evenLaw(r)], {search: false})
  expect(v.proven).toBe(false)
  expect(v.run).toBeDefined()
})

test('the facts hold of what the runtimes compute', () => {
  for (const k of [1, 2, 3, 7, 60]) {
    const {fns, facts} = arithmetic([k]), m = {name: 'f', params: [], inputs: [], state: {}, step: {}, fns, facts}
    for (let x = 0; x < 200; x++) for (const f of facts) expect(evalC(f.holds, {[f.forall!]: x}, {scalars: {}, maps: {}}, m)).toBe(true)
  }
})

test('a term and an integer carry the value they compute', () => {
  const r = rule('t').inputs({x: nat}).state({s: 0})
  const env = r.law('x', ({s}) => s.modBy(5).eq(s.divBy(5)))
  expect(env.holds).toEqual({op: '=', a: {op: 'get', map: 'mod$5', key: {op: 'var', name: 's'}}, b: {op: 'get', map: 'div$5', key: {op: 'var', name: 's'}}})
  expect(() => r.law('by 0', ({s}) => s.modBy(0).eq(0))).toThrow(/at least 1/)
  expect(() => r.law('by a half', ({s}) => s.divBy(0.5).eq(0))).toThrow(/at least 1/)
  // Euclid's rule for integers: -7 div 2 is -4, -7 mod 2 is 1.
  const z = rule('z').inputs({}).ints({x: -7, q: 0, m: 0}).step(({x}) => ({q: x.divBy(2), m: Int.of(x.modBy(2))}))
  const run = interpret(z.machine), st = run.step({}, run.init({}), {})
  expect(z.decode(st)).toEqual({x: -7, q: -4, m: 1})
})

test('an integer read by Euclid: its remainder in 0..k − 1 whatever its sign', () => {
  const d = rule('euclid').inputs({x: int})
  const ok = d.decide('x = 3·(x div 3) + x mod 3, 0 <= x mod 3 < 3', () => [], ({x}) => x.eq(x.divBy(3).times(3).plus(x.modBy(3))).and(x.modBy(3).lt(3)))
  expect(proven(proveDecision(ok))).toBe(true)
  const wrong = d.decide('x mod 3 is x when x is below 3', ({x}) => x.lt(3), ({x}) => x.eq(x.modBy(3)))
  expect(proven(proveDecision(wrong))).toBe(false)
})

test('a law from another instance of the rule is proven (the divisors it reads are noted on the rule proven)', () => {
  const r = pairs()
  expect(proven(proveRule(r, [evenLaw()], {search: false}))).toBe(true)
})

test('inferLaws finds a remainder nobody wrote', () => {
  const r = pairs(), v = inferLaws(r, [pairsLaw(r)], [], {ms: 8000})
  expect(proven(v)).toBe(true)
  expect(v.found.map(f => f.text)).toContain('issued mod 2 = 0')
  // The law found is a law of the rule as the caller has it.
  expect(proven(proveRule(r, [pairsLaw(r), ...v.found.map(f => f.law)], {search: false}))).toBe(true)
  const bad = pairs('odd refill'), w = inferLaws(bad, [pairsLaw(bad)], [], {ms: 8000})
  expect(proven(w)).toBe(false)
})

test('the parity of a sum two counters keep', () => {
  const r = rule('two counters').inputs({first: bool}).state({a: 0, b: 1}).step(({first, a, b}) => ({a: when(first, a.plus(1), a), b: when(first, b, b.plus(1))}))
  const law = r.law('a + b is never 10', ({a, b}) => a.plus(b).eq(10).not())
  // a + b goes up by one each step, so its parity changes: no remainder is kept, and the law is false.
  expect(proven(inferLaws(r, [law], [], {ms: 4000}))).toBe(false)
  const s = rule('two counters by two').inputs({first: bool}).state({a: 0, b: 1}).step(({first, a, b}) => ({a: when(first, a.plus(2), a), b: when(first, b, b.plus(2))}))
  const law2 = s.law('a + b is never 10', ({a, b}) => a.plus(b).eq(10).not())
  const v = inferLaws(s, [law2], [], {ms: 8000})
  expect(proven(v)).toBe(true)
})

test('a machine with no division is left as it is', () => {
  const m = rule('plain').inputs({}).state({s: 0}).step(({s}) => ({s: s.plus(1)})).machine
  expect(withArithmetic(m)).toBe(m)
  expect(m.fns).toBeUndefined()
})

test('integers and remainders in the datatype language: proven, refused with a value, and an integer literal in a branch', async () => {
  const {dataLaws, first} = await import('../examples/arith.ts')
  const {proveData, evalX, programOf, integer, law} = await import('./data.ts')
  for (const mk of [dataLaws.firstOfCons, dataLaws.twiceLess, dataLaws.euclid, dataLaws.evenSum]) expect(proven(proveData(mk(), {ms: 20000}))).toBe(true)
  expect(proveData(dataLaws.natural(), {ms: 5000}).counterexample).toEqual({x: '-2'})
  expect(proveData(dataLaws.oddSum(), {ms: 5000}).counterexample).toBeDefined()
  // first's nil case is the integer 0, not a natural's code (an integer literal in a match's case).
  const body = first.fn.body()
  expect(JSON.stringify(body)).toContain('{"op":"int","value":0}')
  // Euclid on a negative value, as the runtime computes it.
  const l = law('q', {x: integer}, ({x}) => x.divBy(2).eq(-4))
  expect(evalX((l.holds as unknown as {a: never}).a, new Map([['x', -7]]), {})).toBe(-4)
  expect(programOf([l]).ints).toBe(true)
})
