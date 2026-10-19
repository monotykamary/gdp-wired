// Records and variants (core/dsl.ts record, variant): encoded as the variables of their fields and a case's index, so the
// kernel, both runtimes and the Lean twin see only naturals. A payment decided over a variant and a record, proven and
// a broken variant refused; a hold whose state is a variant, its laws and step laws proven, the runs decoded as the
// code it describes keeps them; values outside their kinds refused.
import {expect, test} from 'bun:test'
import {crossCheckDecision, fun, nat, proveDecision, proveSteps, record, rule, same, variant, when, yes} from './dsl.ts'
import {accountLaws, accountSteps, accounts, approve, approveLaws, customer, hold, holdLaws, holdSteps, jobLaws, jobSteps, jobs, seatLaws, seatSteps, seats} from '../examples/datatypes.ts'

test('a decision over a variant and a record: proven, the broken variant refused, run on runtime values', () => {
  const f = approve()
  for (const d of approveLaws(f)) {
    expect(proveDecision(d)).toMatchObject({proven: true, checked: true})
    expect(crossCheckDecision(d).failure).toBeUndefined()
  }
  const broken = approve('approves unverified cards')
  expect(proveDecision(approveLaws(broken)[1]!).proven).toBe(false)
  const gold = {tier: 'gold', limit: 100, blocked: false}
  expect(f.run({pay: {tag: 'card', amount: 550, last4: 4242, verified: true}, who: gold})).toEqual({ok: true, charged: 550})
  expect(f.run({pay: {tag: 'card', amount: 50, last4: 4242, verified: false}, who: gold})).toEqual({ok: false, charged: 50})
  expect(f.run({pay: {tag: 'voucher', cover: 30}, who: {...gold, tier: 'basic'}})).toEqual({ok: false, charged: 0})
  expect(f.run({pay: {tag: 'cash', amount: 200}, who: gold})).toEqual({ok: true, charged: 200})
  // Against the code it describes, on drawn payments and customers.
  const real = (pay: {tag: string, amount?: number, verified?: boolean}, who: {tier: string, limit: number, blocked: boolean}) => {
    const cap = who.tier === 'gold' ? who.limit + 500 : who.limit
    const ok = !who.blocked && (pay.tag === 'card' ? !!pay.verified && pay.amount! <= cap : pay.tag === 'cash' ? pay.amount! <= 200 : who.tier === 'gold')
    return {ok, charged: pay.tag === 'voucher' ? 0 : pay.amount!}
  }
  expect(f.compare(({pay, who}) => real(pay as never, who as never), {trials: 3000, bound: 700}).failure).toBeUndefined()
})

test('values outside their kinds are refused as the runtimes refuse them', () => {
  const f = approve(), who = {tier: 'gold', limit: 1, blocked: false}
  expect(() => f.run({pay: {tag: 'cheque', amount: 1}, who})).toThrow(RangeError)
  expect(() => f.run({pay: {tag: 'card', amount: 1, last4: 10000, verified: true}, who})).toThrow(RangeError)
  expect(() => f.run({pay: {tag: 'voucher', cover: 1, amount: 3}, who})).toThrow(RangeError) // not a field of voucher
  expect(() => f.run({pay: {tag: 'cash', amount: 1}, who: {tier: 'gold', limit: 1}})).toThrow(RangeError) // blocked left out
  expect(() => f.run({pay: 3, who})).toThrow(RangeError)
  expect(() => variant({a: {tag: nat}})).toThrow(/names the case/)
  expect(() => rule('x').inputs({r: customer}).machine).toThrow(/history record/)
})

test('a variant as state: laws and step laws proven, the broken variant refused, runs decoded', () => {
  const r = hold(), laws = holdLaws(r), steps = holdSteps(r)
  expect(proveSteps(r, laws, steps)).toMatchObject({proven: true, checked: true})
  expect(r.crossCheck(laws, steps).failure).toBeUndefined()
  const early = hold('releases early')
  expect(proveSteps(early, holdLaws(early), holdSteps(early)).proven).toBe(false)
  const gen = r.compiled(), ps = r.encodeParams({cap: 100, wait: 10})
  let st = gen.init(ps)
  const seen: unknown[] = []
  for (const req of [{op: 'hold', amount: 40, now: 1}, {op: 'release', amount: 0, now: 5}, {op: 'release', amount: 0, now: 11}, {op: 'hold', amount: 1, now: 12}] as const) {
    st = gen.step(ps, st, r.encodeInput(req))
    seen.push(r.decode(st))
  }
  expect(seen).toEqual([{at: {tag: 'holding', amount: 40, since: 1}, paid: 0}, {at: {tag: 'holding', amount: 40, since: 1}, paid: 0}, {at: {tag: 'released', amount: 40}, paid: 40}, {at: {tag: 'released', amount: 40}, paid: 40}])
  // Against the code it describes.
  type St = {at: {tag: string, amount?: number, since?: number}, paid: number}
  const real = {
    init: (): St => ({at: {tag: 'idle'}, paid: 0}),
    step: (p: {cap: unknown, wait: unknown}, s: St, q: {op: unknown, amount: unknown, now: unknown}): St => {
      const cap = p.cap as number, wait = p.wait as number, amount = q.amount as number, now = q.now as number
      if (q.op === 'hold' && s.at.tag === 'idle' && amount <= cap && amount > 0) return {...s, at: {tag: 'holding', amount, since: now}}
      if (q.op === 'release' && s.at.tag === 'holding' && s.at.since! + wait <= now) return {at: {tag: 'released', amount: s.at.amount!}, paid: s.paid + s.at.amount!}
      if (q.op === 'refund' && s.at.tag === 'holding') return {...s, at: {tag: 'idle'}}
      return s
    },
  }
  expect(r.compare(real as never, {trials: 300, bound: 30}).failure).toBeUndefined()
})

test('same: values alike part by part', () => {
  const k = record({a: nat, b: variant({x: {n: nat}, y: {}})})
  const c = JSON.stringify(same(k.value('p'), k.value('q')).c)
  for (const part of ['q.a', 'q.b', 'q.b.x.n']) expect(c).toContain(`"${part}"`)
  expect(() => same(k.value('p'), nat.value('n'))).toThrow()
})

test('a function returns records and variants, run as runtime values', () => {
  const Verdict = variant({allow: {until: nat}, deny: {}})
  const decide = fun('decide').inputs({who: customer, now: nat})
    .returns(({who, now}) => ({verdict: when(who.blocked, Verdict.make({tag: 'deny'}), Verdict.make({tag: 'allow', until: now.plus(60)})), seen: {tier: who.tier, limit: who.limit}}))
  expect(decide.run({who: {tier: 'gold', limit: 5, blocked: false}, now: 10})).toEqual({verdict: {tag: 'allow', until: 70}, seen: {tier: 'gold', limit: 5}})
  expect(decide.run({who: {tier: 'basic', limit: 0, blocked: true}, now: 10})).toEqual({verdict: {tag: 'deny'}, seen: {tier: 'basic', limit: 0}})
  const d = decide.law('a blocked customer is denied', ({who}) => who.blocked, out => out.verdict.is('deny'))
  expect(proveDecision(d)).toMatchObject({proven: true, checked: true})
  expect(proveDecision(decide.law('an allow lasts an hour', () => [], (out, {now}) => out.verdict.match({allow: a => a.until.eq(now.plus(60)), deny: () => yes}))).proven).toBe(true)
})

test('maps and lists of a kind: proven, cross-checked, the broken variants refused, runs decoded', () => {
  const cases = [
    {r: accounts(), laws: accountLaws, steps: accountSteps, broken: accounts('lowers a limit below what is spent')},
    {r: seats(), laws: seatLaws, steps: seatSteps, broken: seats('lets a hold replace a sale')},
    {r: jobs(), laws: jobLaws, steps: jobSteps, broken: jobs('pushes past the cap')},
  ] as const
  for (const {r, laws, steps, broken} of cases) {
    const l = laws(r as never), st = steps(r as never)
    expect(proveSteps(r, l, st)).toMatchObject({proven: true, checked: true})
    expect((r as ReturnType<typeof jobs>).crossCheck(l, st).failure).toBeUndefined()
    expect(proveSteps(broken, laws(broken as never), steps(broken as never)).proven).toBe(false)
  }
  const a = accounts(), ga = a.compiled()
  let sa = ga.init({})
  for (const q of [{op: 'limit', who: 3, amount: 50}, {op: 'spend', who: 3, amount: 20}, {op: 'freeze', who: 3, amount: 0}, {op: 'spend', who: 3, amount: 5}] as const) sa = ga.step({}, sa, a.encodeInput(q))
  expect(a.decode(sa).Acct).toEqual({3: {limit: 50, spent: 20, frozen: true}})
  const s = seats(), gs = s.compiled()
  let ss = gs.init({})
  for (const q of [{op: 'hold', seat: 1, who: 7, now: 0}, {op: 'buy', seat: 1, who: 8, now: 5}, {op: 'buy', seat: 1, who: 7, now: 6}, {op: 'hold', seat: 1, who: 8, now: 30}] as const) ss = gs.step({}, ss, s.encodeInput(q))
  expect(s.decode(ss).Seats).toEqual({1: {tag: 'sold', to: 7}})
  const j = jobs(), gj = j.compiled(), ps = j.encodeParams({cap: 2})
  let sj = gj.init(ps)
  for (const q of [{op: 'push', job: {id: 4, prio: 1}}, {op: 'push', job: {id: 5, prio: 9}}, {op: 'push', job: {id: 6, prio: 2}}, {op: 'pop', job: {id: 0, prio: 0}}, {op: 'push', job: {id: 7, prio: 3}}] as const) sj = gj.step(ps, sj, j.encodeInput(q))
  expect(j.decode(sj).Queue).toEqual([{id: 4, prio: 1}, {id: 7, prio: 3}])
})
