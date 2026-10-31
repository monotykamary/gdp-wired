// core/system.ts against runs of its parts, and the patterns it was built for on toy handlers: a charge under
// at-least-once delivery (with and without a dedupe table, at each isolation level), a read-modify-write, an outbox.
// Time: the clock within a skew, keys that expire at their time, a lease (research/distributed/time.ts), and an outbox's
// liveness over every row. (The prover's tests get 30 s each: on one vCPU some pass 5 s.)
import {describe, expect, test} from 'bun:test'
import {forall, keyed, nat, proveLeadsTo, proveRule, proveSteps, rule, when} from './dsl.ts'
import {type Request, evalC, interpret, seeded} from './machine.ts'
import {asRule, client, clocked, delivery, expires, expiry, isolation, lift, modelsOf, system, time} from './system.ts'
import {refutedBy} from './live.ts'
import {handled, lease, leaseInvariant, leaseLaw, marked, outbox, published} from '../research/distributed/time.ts'

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
  }, 30_000)
  test('a dedupe in one step holds under at-least-once; split by read committed it does not; snapshot refuses the second commit', () => {
    for (const [level, want] of [['atomic', 'proven'], ['read committed', 'refuted'], ['snapshot', 'proven']] as const) {
      const r = payments(true, level, 'at-least-once')
      expect([level, verdict(proveRule(r, [once(r)], {search: {ms: 10_000}}))]).toEqual([level, want])
    }
  }, 30_000)
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
  }, 30_000)
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
  test('time, clocked, expires: the time rises; a reading within the skew (the time itself at 0); a key gone only past its time', () => {
    const t = interpret(time())
    expect(t.step({}, t.init({}), {dt: 5}).scalars.now).toBe(5)
    const at = rule('stamp').inputs({t: nat}).state({last: 0}).step(({t}) => ({last: t}))
    const zero = clocked(at.machine, 't', 0), skewed = clocked(at.machine, 't', 'E')
    expect([zero.inputs, zero.step.state!.last]).toEqual([[], {op: 'var', name: 'now'}])
    expect(skewed.params).toEqual(['E'])
    const st = {scalars: {last: 0, now: 10}, maps: {}}
    expect([7, 8, 12, 13].map(r => evalC(skewed.assume!, {E: 2, t: r, ...st.scalars}, st, skewed))).toEqual([false, true, true, false])
    const ex = expires({Owner: 0}, 'At', {key: 'k'}), er = interpret(ex)
    const s0 = {scalars: {now: 4}, maps: {Owner: new Map([[1, 7]]), At: new Map([[1, 5]])}}
    expect(evalC(ex.assume!, {k: 1, now: 4}, s0, ex)).toBe(false)
    expect(er.step({}, {...s0, scalars: {now: 5}}, {k: 1}).maps.Owner!.get(1) ?? 0).toBe(0)
    expect(modelsOf(skewed).map(m => m.name)).toEqual(['clock skew ≤ E'])
  })
  test('a lease under skew ≤ E and a margin of 2E: proven with its invariant; the skew unbounded, or a margin of E: refuted by a run', () => {
    const r = lease('bounded', 'twice the skew')
    expect(verdict(proveSteps(r, [leaseInvariant(r)], [leaseLaw(r)], {search: false}))).toBe('proven')
    for (const [skew, margin] of [['unbounded', 'twice the skew'], ['bounded', 'the skew']] as const) {
      const b = lease(skew, margin), v = proveSteps(b, [], [leaseLaw(b)], {search: {ms: 5000}})
      expect(verdict(v)).toBe('refuted')
      // the run on the interpreter: each request allowed, and the law broken at its last use
      const m = b.machine, run = interpret(m), ps = v.run!.params
      let st = run.init(ps), broken = false
      for (const q of v.run!.trace as Request[]) {
        const before = st
        st = run.step(ps, st, q)
        if (q.act === 3) broken ||= !(before.scalars.taken === 1 && before.scalars.owner === q.p && before.scalars.now! < before.scalars.at!)
      }
      expect(broken).toBe(true)
    }
  }, 30_000)
  test('an outbox: every row eventually published (weak fairness), its rank and laws found; eventually marked: a fair ring under weak fairness, none under strong', () => {
    const r = outbox()
    expect(verdict(proveLeadsTo(r, [], published(r), {ms: 15_000}))).toBe('proven')
    void handled
    for (const fairness of ['weak', 'strong'] as const) {
      const l = marked(r, fairness), kr = keyed(r, l), K = {op: 'var', name: l.forall!} as const
      const at = (map: string, value: number) => ({op: '=', a: {op: 'get', map, key: K}, b: {op: 'const', value}}) as const
      const req = (act: number) => ({act: {op: 'const', value: act}, msg: K}) as never
      const zero = Object.fromEntries(kr.machine.inputs.map(i => [i, 0]))
      const ring = {params: {[l.forall!]: 0}, stem: [{...zero, act: 0, msg: 0}], sets: [
        {holds: {op: 'and', xs: [at('Outbox', 1), at('InFlight', 0)]}, request: req(1)},
        {holds: {op: 'and', xs: [at('Outbox', 1), at('InFlight', 1)]}, request: req(3)}]} as never
      expect(refutedBy(kr.machine, [], l, ring)).toEqual(fairness === 'weak' ? {refuted: true, fair: ['weak']} : {refuted: false, fair: ['weak'], why: 'the run is not strongly fair'})
    }
  }, 30_000)
})
