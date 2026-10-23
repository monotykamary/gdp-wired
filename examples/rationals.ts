// Rules over the rationals (core/rationals.ts): for the suite (`bun examples/rationals.ts`), core/rationals.test.ts and
// the Lean export (lean-kernel/qlean.ts, `lean-rationals` in modal/suite.json). Every value is an exact rational: 0.1
// is 1/10 and a third is 1/3; no law below is scaled to cents or encoded as naturals.
//   - a fee split: each payment splits into a 2.5% fee and the rest, the parts sum to the whole exactly, the fee is a
//     fortieth of the total (broken: a fee rounded up to the cent can't be written here; broken instead: the payout
//     takes 97.6%, so the parts overshoot)
//   - a rate limiter with fractional tokens: a request refills 0.4 of a token, up to the cap, and spends what it costs,
//     at most what's there; tokens stay within 0 and the cap (broken: a refill past the cap)
//   - a ledger in decimals: deposits, withdrawals at most the balance, and transfers between two accounts, each amount a
//     decimal; the balances stay at least 0 and their sum is what came in less what went out (broken: a transfer that
//     moves 0.01 less than it takes)
//   - laws true over one domain and false over the other, each decided both ways: over ℕ by dsl.ts's rule (the cut is
//     the integers' rule), over ℚ by ratRule
import {type Verdict, nat, proveRule, rule} from '../core/dsl.ts'
import {type QVerdict, type RatLaw, nonneg, proveRatRule, rat, ratRule, rmin, rwhen} from '../core/rationals.ts'
import type {QLaw, QMachine} from '../kernel/kernel.ts'

export const feeSplit = (bug?: 'payout 97.6%') => ratRule('fee split').inputs({payment: nonneg}).state({total: 0, fee: 0, payout: 0})
  .step(({payment, total, fee, payout}) => ({total: total.plus(payment), fee: fee.plus(payment.times('0.025')), payout: payout.plus(payment.times(bug ? '0.976' : '0.975'))}))
export const feeLaws = (r = feeSplit()): RatLaw<string, string>[] => [
  r.law('the parts sum to the whole', ({fee, payout, total}) => fee.plus(payout).eq(total)),
  r.law('the fee is a fortieth of the total', ({fee, total}) => fee.times(40).eq(total)),
]

export const limiter = (bug?: 'refill past the cap') => ratRule('fractional rate limiter').params({cap: nonneg}).inputs({cost: nonneg}).state({tokens: ({cap}) => cap})
  .assume(({cost, tokens, cap}) => cost.atMost(rmin(cap, tokens.plus('0.4'))))
  .step(({tokens, cap, cost}) => ({tokens: (bug ? tokens.plus('0.4') : rmin(cap, tokens.plus('0.4'))).minus(cost)}))
export const limiterLaws = (r = limiter()): RatLaw<string, string>[] => [
  r.law('tokens are never negative', ({tokens}) => tokens.atLeast(0)),
  r.law('tokens never exceed the cap', ({tokens, cap}) => tokens.atMost(cap)),
]

// op: 0 deposit to a, 1 withdraw from a, 2 transfer a to b (any other value: nothing).
export const ledger = (bug?: 'a transfer short by 0.01') => ratRule('decimal ledger').inputs({op: rat, amount: nonneg}).state({a: 0, b: 0, inflow: 0, outflow: 0})
  .assume(({op, amount, a}) => op.eq(0).or(op.eq(1).and(amount.atMost(a)), op.eq(2).and(amount.atMost(a))))
  .step(({op, amount, a, b, inflow, outflow}) => ({
    a: rwhen(op.eq(0), a.plus(amount), a.minus(amount)),
    b: rwhen(op.eq(2), b.plus(bug ? amount.minus('0.01') : amount), b),
    inflow: rwhen(op.eq(0), inflow.plus(amount), inflow),
    outflow: rwhen(op.eq(1), outflow.plus(amount), outflow),
  }))
export const ledgerLaws = (r = ledger()): RatLaw<string, string>[] => [
  r.law('a is never negative', ({a}) => a.atLeast(0)),
  r.law('b is never negative', ({b}) => b.atLeast(0)),
  r.law('the balances are what came in less what went out', ({a, b, inflow, outflow}) => a.plus(b).eq(inflow.minus(outflow))),
]

// --- one law, two domains -------------------------------------------------------------------------------------------
// Each: the rule over ℕ (rule) and over ℚ (ratRule), the same law, and where it holds.
type Pair = {name: string, holdsOver: 'ℚ' | 'ℕ', nat: () => Verdict, q: () => {machine: QMachine, laws: QLaw[]}}
export type Adversarial = Pair & {rat: () => QVerdict}
const N = (name: string) => rule(name)
const pairs: Pair[] = [
  {name: 'halving a positive amount keeps it positive', holdsOver: 'ℚ',
    nat: () => { const r = N('halve').inputs({}).state({s: 1}).step(({s}) => ({s: s.divBy(2)})); return proveRule(r, [r.law('s > 0', ({s}) => s.gt(0))]) },
    q: () => { const r = ratRule('halve').state({s: 1}).step(({s}) => ({s: s.over(2)})); return {machine: r.machine, laws: [r.law('s > 0', ({s}) => s.gt(0))]} }},
  {name: 'taking c away and giving it back leaves s as it was', holdsOver: 'ℚ',
    nat: () => { const r = N('round trip').params({a: nat}).inputs({c: nat}).state({s: ({a}) => a}).step(({s, c}) => ({s: s.minus(c).plus(c)})); return proveRule(r, [r.law('s = a', ({s, a}) => s.eq(a))]) },
    q: () => { const r = ratRule('round trip').params({a: rat}).inputs({c: rat}).state({s: ({a}) => a}).step(({s, c}) => ({s: s.minus(c).plus(c)})); return {machine: r.machine, laws: [r.law('s = a', ({s, a}) => s.eq(a))]} }},
  {name: 'an amount splits into two equal halves', holdsOver: 'ℚ',
    nat: () => { const r = N('even split').inputs({amount: nat}).state({half: 0, whole: 0}).step(({amount}) => ({half: amount.divBy(2), whole: amount})); return proveRule(r, [r.law('2·half = whole', ({half, whole}) => half.times(2).eq(whole))]) },
    q: () => { const r = ratRule('even split').inputs({amount: nonneg}).state({half: 0, whole: 0}).step(({amount}) => ({half: amount.over(2), whole: amount})); return {machine: r.machine, laws: [r.law('2·half = whole', ({half, whole}) => half.times(2).eq(whole))]} }},
  {name: 'the midpoint of lo < hi lies strictly between', holdsOver: 'ℚ',
    nat: () => { const r = N('midpoint').inputs({x: nat, y: nat}).state({lo: 0, hi: 0, m: 0}).step(({x, y}) => ({lo: x, hi: y, m: x.plus(y).divBy(2)})); return proveRule(r, [r.law('lo < hi ⇒ lo < m < hi', ({lo, m, hi}) => lo.lt(hi).implies(lo.lt(m).and(m.lt(hi))))]) },
    q: () => { const r = ratRule('midpoint').inputs({x: rat, y: rat}).state({lo: 0, hi: 0, m: 0}).step(({x, y}) => ({lo: x, hi: y, m: x.plus(y).over(2)})); return {machine: r.machine, laws: [r.law('lo < hi ⇒ lo < m < hi', ({lo, m, hi}) => lo.lt(hi).implies(lo.lt(m).and(m.lt(hi))))]} }},
  {name: 'a third of a, three times over, is a', holdsOver: 'ℚ',
    nat: () => { const r = N('thirds').inputs({a: nat}).state({t: 0, w: 0}).step(({a}) => ({t: a.divBy(3).times(3), w: a})); return proveRule(r, [r.law('t = w', ({t, w}) => t.eq(w))]) },
    q: () => { const r = ratRule('thirds').inputs({a: rat}).state({t: 0, w: 0}).step(({a}) => ({t: a.over(3).times(3), w: a})); return {machine: r.machine, laws: [r.law('t = w', ({t, w}) => t.eq(w))]} }},
  {name: 'below y means at least 1 below y', holdsOver: 'ℕ',
    nat: () => { const r = N('discrete').params({x: nat, y: nat}).inputs({}).state({s: ({x}) => x, t: ({y}) => y}); return proveRule(r, [r.law('s < t ⇒ s + 1 ≤ t', ({s, t}) => s.lt(t).implies(s.plus(1).atMost(t)))]) },
    q: () => { const r = ratRule('discrete').params({x: nonneg, y: nonneg}).state({s: ({x}) => x, t: ({y}) => y}); return {machine: r.machine, laws: [r.law('s < t ⇒ s + 1 ≤ t', ({s, t}) => s.lt(t).implies(s.plus(1).atMost(t)))]} }},
  {name: 'no amount is half of 1', holdsOver: 'ℕ',
    nat: () => { const r = N('no half').inputs({c: nat}).state({s: 0}).step(({c}) => ({s: c})); return proveRule(r, [r.law('2s ≠ 1', ({s}) => s.times(2).ne(1))]) },
    q: () => { const r = ratRule('no half').inputs({c: nonneg}).state({s: 0}).step(({c}) => ({s: c})); return {machine: r.machine, laws: [r.law('2s ≠ 1', ({s}) => s.times(2).ne(1))]} }},
  {name: 'a positive amount is at least 1', holdsOver: 'ℕ',
    nat: () => { const r = N('positive').inputs({c: nat}).state({s: 0}).step(({s, c}) => ({s: s.plus(c)})); return proveRule(r, [r.law('s > 0 ⇒ s ≥ 1', ({s}) => s.gt(0).implies(s.atLeast(1)))]) },
    q: () => { const r = ratRule('positive').inputs({c: nonneg}).state({s: 0}).step(({s, c}) => ({s: s.plus(c)})); return {machine: r.machine, laws: [r.law('s > 0 ⇒ s ≥ 1', ({s}) => s.gt(0).implies(s.atLeast(1)))]} }},
  {name: 'nothing lies strictly between 0 and 1', holdsOver: 'ℕ',
    nat: () => { const r = N('gap').inputs({c: nat}).state({s: 2}).step(({s, c}) => ({s: s.plus(c).minus(1)})); return proveRule(r, [r.law('not 0 < s < 1', ({s}) => s.gt(0).and(s.lt(1)).not())]) },
    q: () => { const r = ratRule('gap').inputs({c: nonneg}).state({s: 2}).step(({s, c}) => ({s: s.plus(c).minus(1)})); return {machine: r.machine, laws: [r.law('not 0 < s < 1', ({s}) => s.gt(0).and(s.lt(1)).not())]} }},
  {name: 'twice an amount is never 3', holdsOver: 'ℕ',
    nat: () => { const r = N('odd').inputs({c: nat}).state({s: 0}).step(({s, c}) => ({s: s.plus(c)})); return proveRule(r, [r.law('s + s ≠ 3', ({s}) => s.plus(s).ne(3))]) },
    q: () => { const r = ratRule('odd').inputs({c: nonneg}).state({s: 0}).step(({s, c}) => ({s: s.plus(c)})); return {machine: r.machine, laws: [r.law('s + s ≠ 3', ({s}) => s.plus(s).ne(3))]} }},
  {name: 'a difference is never negative', holdsOver: 'ℕ',
    nat: () => { const r = N('difference').params({a: nat, b: nat}).inputs({}).state({d: ({a, b}) => a.minus(b)}); return proveRule(r, [r.law('d ≥ 0', ({d}) => d.atLeast(0))]) },
    q: () => { const r = ratRule('difference').params({a: nonneg, b: nonneg}).state({d: ({a, b}) => a.minus(b)}); return {machine: r.machine, laws: [r.law('d ≥ 0', ({d}) => d.atLeast(0))]} }},
  {name: 'a counter moved by positive steps is 0 or at least 1', holdsOver: 'ℕ',
    nat: () => { const r = N('steps').inputs({c: nat}).state({s: 0}).step(({s, c}) => ({s: s.plus(c)})); return proveRule(r, [r.law('s = 0 or s ≥ 1', ({s}) => s.eq(0).or(s.atLeast(1)))]) },
    q: () => { const r = ratRule('steps').inputs({c: nonneg}).state({s: 0}).step(({s, c}) => ({s: s.plus(c)})).assume(({c}) => c.gt(0)); return {machine: r.machine, laws: [r.law('s = 0 or s ≥ 1', ({s}) => s.eq(0).or(s.atLeast(1)))]} }},
]
export const adversarial: Adversarial[] = pairs.map(a => ({...a, rat: () => { const {machine, laws} = a.q(); return proveRatRule(machine, laws) }}))
export const ratOf = (a: Adversarial): {machine: QMachine, laws: QLaw[]} => a.q()
// Decided: proven and checked where the law holds, refuted by a run from the start where it doesn't.
export const decided = (v: Verdict | QVerdict, holds: boolean): boolean => (holds ? v.proven && v.checked : !v.proven && v.stuck === 'sat' && !!v.run)

if (import.meta.main) {
  const show = (what: string, v: QVerdict) => console.log(`${what}: ${v.proven ? `proven${v.checked ? ', checked' : ''}` : `refuted (${v.goal}: ${JSON.stringify(v.run ?? v.witness)})`}`)
  show('fee split', proveRatRule(feeSplit(), feeLaws()))
  show('fee split (payout 97.6%)', proveRatRule(feeSplit('payout 97.6%'), feeLaws(feeSplit('payout 97.6%'))))
  show('rate limiter', proveRatRule(limiter(), limiterLaws()))
  show('rate limiter (refill past the cap)', proveRatRule(limiter('refill past the cap'), limiterLaws(limiter('refill past the cap'))))
  show('decimal ledger', proveRatRule(ledger(), ledgerLaws()))
  show('decimal ledger (a transfer short by 0.01)', proveRatRule(ledger('a transfer short by 0.01'), ledgerLaws(ledger('a transfer short by 0.01'))))
  console.log('the limiter run exactly, cap 2, costs 0.5 and 1/3:', JSON.stringify(limiter().run({cap: 2}, [{cost: '0.5'}, {cost: '1/3'}])))
  let ok = 0
  for (const a of adversarial) {
    const n = a.nat(), r = a.rat(), good = decided(n, a.holdsOver === 'ℕ') && decided(r, a.holdsOver === 'ℚ')
    if (good) ok++
    console.log(`${good ? 'decided' : 'WRONG'}: ${a.name} (holds over ${a.holdsOver}): ℕ ${n.proven ? 'proven' : `refuted ${JSON.stringify(n.witness)}`}, ℚ ${r.proven ? 'proven' : `refuted ${JSON.stringify(r.run)}`}`)
  }
  console.log(`${ok} of ${adversarial.length} laws decided correctly over both domains`)
  if (ok !== adversarial.length) process.exit(1)
}
