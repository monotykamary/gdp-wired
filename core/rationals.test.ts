// Rules over the rationals: the examples proven and checked, their broken twins refuted by exact runs; laws true over
// one domain and false over the other decided both ways; a proof of one machine refused for another; the runtimes
// exact; products of unknowns refused.
import {expect, test} from 'bun:test'
import {adversarial, decided, feeLaws, feeSplit, ledger, ledgerLaws, limiter, limiterLaws} from '../examples/rationals.ts'
import {checkQMachine} from '../kernel/kernel.ts'
import {q, qeq} from './q.ts'
import {type QEnv, interpretQ, loadQJs, nonneg, proveQMachine, proveRatRule, ratRule, rlit} from './rationals.ts'

test('the examples are proven and checked; their broken twins are refuted by a run from the start', () => {
  for (const [good, laws, bad, badLaws] of [
    [feeSplit(), feeLaws(), feeSplit('payout 97.6%'), feeLaws(feeSplit('payout 97.6%'))],
    [limiter(), limiterLaws(), limiter('refill past the cap'), limiterLaws(limiter('refill past the cap'))],
    [ledger(), ledgerLaws(), ledger('a transfer short by 0.01'), ledgerLaws(ledger('a transfer short by 0.01'))],
  ] as const) {
    const v = proveRatRule(good, laws)
    expect(v.proven && v.checked).toBe(true)
    const w = proveRatRule(bad, badLaws)
    expect(w.proven).toBe(false)
    expect(w.stuck).toBe('sat')
    expect(w.run).toBeDefined()
    // The good machine's proof doesn't prove the broken one.
    if (v.proof) expect(checkQMachine(bad.machine, badLaws, v.proof.trees)).toBe(false)
  }
})

test('laws true over one domain and false over the other are decided both ways', () => {
  expect(adversarial.length).toBeGreaterThanOrEqual(10)
  for (const a of adversarial) {
    expect(decided(a.nat(), a.holdsOver === 'ℕ'), `${a.name} over ℕ`).toBe(true)
    expect(decided(a.rat(), a.holdsOver === 'ℚ'), `${a.name} over ℚ`).toBe(true)
  }
  expect(adversarial.filter(a => a.holdsOver === 'ℚ').length).toBeGreaterThanOrEqual(5)
  expect(adversarial.filter(a => a.holdsOver === 'ℕ').length).toBeGreaterThanOrEqual(5)
})

test('the runtimes compute exactly, interpreted and compiled alike', () => {
  const r = limiter()
  expect(r.run({cap: 2}, [{cost: '0.5'}, {cost: '1/3'}])).toEqual([{tokens: '2'}, {tokens: '3/2'}, {tokens: '47/30'}])
  // 0.1 + 0.2 is 3/10 exactly.
  const sum = ratRule('sum').inputs({x: nonneg}).state({s: 0}).step(({s, x}) => ({s: s.plus(x)}))
  expect(sum.run({}, [{x: 0.1}, {x: 0.2}]).at(-1)).toEqual({s: '3/10'})
  const m = ledger().machine, ps = {}, st: QEnv = {a: q(0), b: q(0), inflow: q(0), outflow: q(0)}
  for (const run of [interpretQ(m), loadQJs(m)]) {
    let s = st
    for (const req of [{op: q(0), amount: q(1, 10)}, {op: q(0), amount: q(2, 10)}, {op: q(2), amount: q(3, 100)}, {op: q(1), amount: q(1, 3)}]) {
      if (run.allowed(ps, s, req)) s = run.step(ps, s, req)
    }
    expect(qeq(s.a!, q(27, 100))).toBe(true)
    expect(qeq(s.b!, q(3, 100))).toBe(true)
  }
})

test('a product of two unknowns is refused: nonlinear arithmetic is outside these certificates', () => {
  expect(() => ratRule('area').inputs({w: nonneg, h: nonneg}).state({a: 0}).step(({w, h}) => ({a: w.times(h)})).machine).toThrow(/nonlinear/)
  expect(() => rlit(1).over(0)).toThrow(/division by 0/)
})

test('a law that is not inductive is unproven, with the step that breaks it', () => {
  // s stays at most 2 only because it starts at 0 and moves by 0 or 1, but s ≤ 2 alone is not preserved by s + 1.
  const r = ratRule('climb').inputs({up: nonneg}).state({s: 0}).assume(({up}) => up.atMost(1)).step(({s, up}) => ({s: s.plus(up)}))
  const v = proveQMachine(r.machine, [r.law('s ≤ 2', ({s}) => s.atMost(2))])
  expect(v.proven).toBe(false)
  expect(v.stuck).toBe('sat')
  expect(v.goal).toBe('s ≤ 2 @step')
})
