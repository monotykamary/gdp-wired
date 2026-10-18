// The builders checked against what they build (core/dsl.ts crossCheck, crossCheckDecision): every law, step law, flag,
// update and decision run again on concrete values, the builders' own arithmetic against the expressions the
// interpreter evaluates. Clean rules agree; a builder made to write a different expression than it computes (a planted
// bug: truncated minus written as plus, ≤ as <, a map read one key off, a case's branches swapped) is caught, even where
// the kernel still proves the law the broken expression states.
import {expect, test} from 'bun:test'
import {Cond, Int, MapRef, Term, bool, crossCheckDecision, decimal, fun, int, min, modBy, nat, oneOf, proveRule, rule, str, when} from './dsl.ts'
import type {E} from './machine.ts'

// Built on demand, so a planted bug is in force while the rule and its laws are built.
const budget = () => rule('budget').params({b: nat, m: nat}).inputs({c: nat}).state({s: 0, left: ({b}) => b})
  .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(c.minus(c.minus(m))), s), left: b.minus(s)}))
const budgetLaws = (r: ReturnType<typeof budget>) => [r.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m))), r.law('left is b less the spend before', ({left, b}) => left.atMost(b))]
const budgetCheck = () => { const r = budget(); return r.crossCheck(budgetLaws(r)) }
const caps = () => rule('caps').params({cap: nat}).inputs({day: nat, amount: nat}).maps({spent: 0})
  .flags(({day, amount, spent, cap}) => ({ok: spent.at(day).plus(amount).atMost(cap)}))
  .step(({day, amount, ok, spent}) => ({spent: spent.bump(day, ok, amount)}))
const capLaws = (r: ReturnType<typeof caps>) => [r.law('no day passes its cap', ({spent, cap}) => ({forall: (k: Term) => spent.at(k).atMost(cap)}))]
const capsCheck = () => { const r = caps(); return r.crossCheck(capLaws(r)) }

// A planted bug: the builder's expression changed, its value left as it computes.
function planted(target: object, method: string, wrong: (out: Term | Cond) => E | Cond['c']): () => void {
  const proto = target as Record<string, (...a: unknown[]) => Term | Cond>, orig = proto[method]!
  proto[method] = function (this: unknown, ...args: unknown[]) {
    const out = orig.apply(this, args)
    return out instanceof Term ? new Term(wrong(out) as E, out.val) : new Cond(wrong(out) as Cond['c'], out.ok)
  }
  return () => { proto[method] = orig }
}

test('clean rules, decisions and values agree with what was built from them', () => {
  expect(budgetCheck().failure).toBeUndefined()
  expect(budgetCheck().checked).toBeGreaterThan(1000)
  const c = caps()
  expect(c.crossCheck(capLaws(c), [c.stepLaw('a refused request changes nothing', ({spent}, after) => ({forall: (k: Term) => after.spent.at(k).eq(spent.at(k))}), ({ok}) => ok.not())]).failure).toBeUndefined()
  const account = rule('account').params({limit: nat}).inputs({op: oneOf('in', 'out'), amount: nat, fee: decimal(2)}).ints({balance: 0}).decimals(2, {fees: 0})
    .step(({op, amount, balance, fee, fees}) => ({balance: when(op.is('in'), balance.plus(amount), balance.minus(amount)), fees: fees.plus(fee)}))
  expect(account.crossCheck([account.law('fees never negative', ({fees}) => fees.atLeast(0))]).failure).toBeUndefined()
  const f = fun('f').inputs({host: str({like: ['*.a']}), staff: bool, x: int}).returns(({host, staff, x}) => ({ok: host.like('*.a').implies(staff), y: x.abs}))
  const d = f.law('a.* needs staff', ({host}) => host.like('*.a'), (o, {staff}) => o.ok.implies(staff))
  expect(crossCheckDecision(d).failure).toBeUndefined()
  expect(crossCheckDecision(d).checked).toBeGreaterThan(500)
})

test('a builder that writes a different expression than it computes is caught', () => {
  const cases: [string, () => () => void, () => string | undefined][] = [
    ['minus written as plus', () => planted(Term.prototype, 'minus', t => ({...(t as Term).e, op: 'add'} as E)), () => budgetCheck().failure],
    ['at most written as below', () => planted(Term.prototype, 'atMost', c => ({...(c as Cond).c, op: '<'} as Cond['c'])), () => budgetCheck().failure],
    ['a map read one key off', () => planted(MapRef.prototype, 'at', t => ({...(t as Term).e, key: {op: 'add', a: ((t as Term).e as Extract<E, {op: 'get'}>).key, b: {op: 'const', value: 1}}} as E)), () => capsCheck().failure],
    ['a case\'s branches swapped', () => planted(Term.prototype, 'lt', c => ({op: 'not', x: (c as Cond).c} as Cond['c'])), () => budgetCheck().failure],
  ]
  for (const [what, plant, check] of cases) {
    const undo = plant()
    let failure: string | undefined
    try { failure = check() } finally { undo() }
    expect([what, failure === undefined ? 'NOT CAUGHT' : 'caught']).toEqual([what, 'caught'])
  }
  // Where the planted bug still lets the kernel prove a law (≤ written as <: "spend < b + m + 1" is no weaker here), the
  // proof alone says nothing is wrong; the cross check does.
  const undo = planted(Term.prototype, 'atMost', c => ({...(c as Cond).c, op: '<'} as Cond['c']))
  try {
    const r = rule('r').inputs({c: nat}).state({s: 0}).step(({s, c}) => ({s: when(c.atMost(2), s, s.plus(1))}))
    const l = r.law('s never falls', ({s}) => s.atLeast(0))
    expect(proveRule(r, [l]).proven).toBe(true)
    expect(r.crossCheck([l]).failure).toContain('the step writes s')
  } finally { undo() }
})

test('compare: a function and a rule against the code they describe, the encoding checked on real inputs', () => {
  // TimeCore.cap as jev-fabric writes it: U32.from_nat(min(left, local)), against a JavaScript rendering of it.
  const cap = fun('cap').inputs({left: nat, local: nat}).fns({narrow: modBy(2 ** 32)}).returns(({left, local, narrow}) => ({out: narrow(min(left, local))}))
  const real = ({left, local}: {left: unknown, local: unknown}) => ({out: Math.min(left as number, local as number) % 2 ** 32})
  expect(cap.compare(real, {edges: [{left: 2 ** 32 + 5, local: 2 ** 33}]}).failure).toBeUndefined()
  // An encoding that forgot the narrowing agrees on small inputs and is caught at the edge.
  const forgot = fun('cap').inputs({left: nat, local: nat}).returns(({left, local}) => ({out: min(left, local)}))
  expect(forgot.compare(real).failure).toBeUndefined()
  expect(forgot.compare(real, {edges: [{left: 2 ** 32 + 5, local: 2 ** 33}]}).failure).toContain('out is 4294967301 here, 5 in the code it describes')
  // Strings and decimals reach the reference as themselves.
  const fee = fun('fee').inputs({host: str({like: ['*.internal']}), price: decimal(2)}).returns(({host, price}) => ({free: host.like('*.internal'), total: when(host.like('*.internal'), 0, price)}))
  expect(fee.compare(({host, price}) => ({free: (host as string).endsWith('.internal'), total: (host as string).endsWith('.internal') ? 0 : price as number})).failure).toBeUndefined()
  // A rule, step by step, against a class-free implementation of the same account.
  const account = rule('account').params({limit: nat}).inputs({op: oneOf('in', 'out'), amount: nat}).ints({balance: 0})
    .flags(({op, amount, balance, limit}) => ({ok: op.is('in').or(balance.minus(amount).atLeast(Int.of(limit).negate()))}))
    .step(({op, amount, balance, ok}) => ({balance: when(ok, when(op.is('in'), balance.plus(amount), balance.minus(amount)), balance)}))
  const impl = (strict: boolean) => ({
    init: () => ({balance: 0}),
    step: ({limit}: {limit: unknown}, st: {balance: number}, {op, amount}: {op: unknown, amount: unknown}) => {
      const next = op === 'in' ? st.balance + (amount as number) : st.balance - (amount as number)
      return {balance: op === 'in' || (strict ? next > -(limit as number) : next >= -(limit as number)) ? next : st.balance}
    },
  })
  expect(account.compare(impl(false)).failure).toBeUndefined()
  expect(account.compare(impl(true), {bound: 5}).failure).toMatch(/balance is -?\d+ here, -?\d+ in the code it describes/)
})
