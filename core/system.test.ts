// core/system.ts against runs of its parts, and the patterns it was built for on toy handlers: a charge under
// at-least-once delivery (with and without a dedupe table, at each isolation level), a read-modify-write, an outbox.
import {describe, expect, test} from 'bun:test'
import {forall, nat, proveRule, proveSteps, rule, when} from './dsl.ts'
import {interpret, seeded} from './machine.ts'
import {asRule, client, delivery, expiry, isolation, lift, modelsOf, system} from './system.ts'

const verdict = (v: {proven: boolean, checked: boolean, run?: unknown}) => (v.proven && v.checked ? 'proven' : v.run ? 'refuted' : 'unknown')
// A charge per key; with `dedupe`, only where the key isn't done yet (the done mark written with it).
const charge = (dedupe: boolean) => rule('charge').inputs({key: nat}).maps({Charged: 0, Done: 0})
  .flags(({key, Done}) => ({fresh: dedupe ? Done.at(key).eq(0) : Done.at(key).atLeast(0)}))
  .step(({key, fresh, Charged, Done}) => ({Charged: Charged.set(key, when(fresh, Charged.at(key).plus(1), Charged.at(key))), Done: Done.set(key, when(fresh, 1, Done.at(key)))}))
// The client sends each charge once, as a message whose id is the charge's key: only the delivery can repeat it.
const payments = (dedupe: boolean, level: 'atomic' | 'read committed' | 'snapshot', mode: 'exactly-once' | 'at-least-once') => {
  const h = delivery(isolation(charge(dedupe).machine, level), 'Q', [], mode, {id: 'key'})
  return system('payments', {send: client('Q', []), handle: level === 'atomic' ? h : {rule: h, id: 't'}})
}
const once = (r: ReturnType<typeof payments>) => r.law('a key is charged at most once', ({Charged}: any) => forall(k => Charged.at(k).atMost(1)))

describe('system', () => {
  test('asRule keeps the machine: the same runs', () => {
    const r = charge(true), back = asRule(r.machine)
    const a = interpret(r.machine), b = interpret(back.machine), rand = seeded(3)
    let sa = a.init({}), sb = b.init({})
    for (let i = 0; i < 200; i++) {
      const input = {key: rand(4)}
      sa = a.step({}, sa, input); sb = b.step({}, sb, input)
      expect([...sb.maps.Charged!]).toEqual([...sa.maps.Charged!])
    }
  })
  test('lift: each process keeps its own scalars', () => {
    const counter = rule('counter').inputs({by: nat}).state({n: 0}).step(({n, by}) => ({n: n.plus(by)}))
    const m = lift(counter.machine, 't'), run = interpret(m)
    let st = run.init({})
    st = run.step({}, st, {by: 2, t: 1}); st = run.step({}, st, {by: 5, t: 2}); st = run.step({}, st, {by: 1, t: 1})
    expect(st.maps.n!.get(1)).toBe(3)
    expect(st.maps.n!.get(2)).toBe(5)
  })
  test('the models a system assumes are named', () => {
    const r = payments(true, 'read committed', 'at-least-once')
    expect(modelsOf(r).map(m => m.name).sort()).toEqual(['at-least-once delivery', 'read committed'])
  })
  // The six cells: what each delivery and isolation level allows of a charge.
  test('a charge without a dedupe is charged twice when delivered twice', () => {
    const e = payments(false, 'atomic', 'exactly-once')
    expect(verdict(proveRule(e, [once(e)], {search: {ms: 10_000}}))).toBe('proven')
    const r = payments(false, 'atomic', 'at-least-once')
    expect(verdict(proveRule(r, [once(r)], {search: {ms: 5000}}))).toBe('refuted')
  })
  test('a dedupe in one step holds under at-least-once; split by read committed it does not; snapshot refuses the second commit', () => {
    for (const [level, want] of [['atomic', 'proven'], ['read committed', 'refuted'], ['snapshot', 'proven']] as const) {
      const r = payments(true, level, 'at-least-once')
      expect([level, verdict(proveRule(r, [once(r)], {search: {ms: 10_000}}))]).toEqual([level, want])
    }
  })
  test('a read-modify-write loses an update at read committed, not at snapshot', () => {
    const deposit = rule('deposit').inputs({acct: nat, amount: nat}).maps({Bal: 0}).step(({acct, amount, Bal}) => ({Bal: Bal.set(acct, Bal.at(acct).plus(amount))}))
    for (const [level, want] of [['read committed', 'refuted'], ['snapshot', 'proven']] as const) {
      const r = system('bank', {deposit: {rule: isolation(deposit.machine, level), id: 't'}})
      // each commit adds its amount to the balance it lands on (unless snapshot refused it)
      const law = r.stepLaw('a deposit adds its amount', ({t, Bal, in$acct, in$amount}: any, after: any) =>
        level === 'snapshot' ? after.Bal.at(in$acct.at(t)).eq(Bal.at(in$acct.at(t)).plus(in$amount.at(t))).or(after.aborted$.at(t).eq(1)) : after.Bal.at(in$acct.at(t)).eq(Bal.at(in$acct.at(t)).plus(in$amount.at(t))),
      ({t, pc$}: any) => pc$.at(t).eq(1 + (level === 'snapshot' ? 0 : 1)))
      expect([level, verdict(proveSteps(r, [], [law], {search: {ms: 5000}}))]).toEqual([level, want])
    }
  })
  test('client: a message at a fresh id', () => {
    const run = interpret(client('Q', ['amount']))
    let st = run.init({})
    st = run.step({}, st, {msg: 2, Q_amount$in: 9})
    expect([st.maps.Q!.get(2), st.maps.Q_amount!.get(2)]).toEqual([1, 9])
  })
  test('expiry: a key vanishes', () => {
    const m = expiry({Lock: 0}), run = interpret(m)
    const st = run.step({}, {scalars: {}, maps: {Lock: new Map([[3, 7]])}}, {key: 3})
    expect(st.maps.Lock!.get(3) ?? 0).toBe(0)
  })
})
