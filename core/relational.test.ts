// Laws about two runs (relational.ts): each construction proves what holds and refutes what doesn't, the refutation a
// real pair of runs; the rule built runs as its two sides do.
import {expect, test} from 'bun:test'
import {interpret, type State} from './machine.ts'
import {all, forall, nat, oneOf, proveRule, proveSteps, rule, when} from './dsl.ts'
import {agreement, isolation, noninterference, proveTwoRuns, twoRuns} from './relational.ts'
import {businessDays, citesIn, duration, parse} from './laws.ts'
import {check} from './cli.ts'
import {type Document, fromInterchange} from '../interchange/format.ts'
import {checkCertificate} from '../interchange/check.ts'
import {spawnSync} from 'node:child_process'
import {mkdtempSync, readFileSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'

// A claim desk: a claim is submitted with an amount and a diagnosis (kept in notes), then decided by the amount.
const desk = (leak: boolean, refuseBySecret = false) => rule('desk')
  .inputs({op: oneOf('submit', 'decide'), amount: nat, diagnosis: nat})
  .state({status: oneOf('none', 'pending', 'approved', 'denied').from('none'), total: 0, notes: 0})
  .assume(({op, diagnosis}) => (refuseBySecret ? op.is('decide').or(diagnosis.atMost(9)) : op.is('decide').or(op.is('submit'))))
  .step(({op, amount, diagnosis, status, total, notes}) => {
    const approve = leak ? diagnosis.lt(5) : amount.atMost(100)
    return {
      status: when(op.is('submit'), 'pending', when(status.is('pending'), when(approve, status.of('approved'), 'denied'), status)),
      total: when(op.is('submit'), total.plus(amount), total),
      notes: when(op.is('submit'), diagnosis, notes),
    }
  })

test('noninterference: the diagnosis never reaches the status, the total or the refusals', () => {
  const l = noninterference(desk(false), {secret: ['diagnosis'], visible: ['status', 'total']})
  const v = proveTwoRuns(l, {search: {ms: 5000}})
  expect(v.proven && v.checked).toBe(true)
})
test('noninterference: a decision by the diagnosis is refuted by two runs', () => {
  const l = noninterference(desk(true), {secret: ['diagnosis'], visible: ['status', 'total']})
  const v = proveTwoRuns(l, {search: {ms: 5000}})
  expect(v.proven).toBe(false)
  expect(v.run).toBeDefined()
  const last = v.run!.trace.at(-1)!
  expect(last.a_diagnosis === last.b_diagnosis).toBe(false)
})
test('noninterference: a refusal by the secret is a difference', () => {
  const l = noninterference(desk(false, true), {secret: ['diagnosis'], visible: ['status']})
  const v = proveTwoRuns(l, {search: {ms: 5000}})
  expect(v.proven).toBe(false)
  expect(v.goal).toContain('refuse the same requests')
  // ... and with refusals assumed, only the state is compared
  expect(proveTwoRuns(noninterference(desk(false, true), {secret: ['diagnosis'], visible: ['status'], refusals: 'assumed'}), {search: {ms: 5000}}).proven).toBe(true)
})

// A lockout: each user's failures counted, a login refused at 3 (per user), or at 10 failures of anyone (global).
const lockout = (global: boolean) => rule('lockout')
  .inputs({op: oneOf('fail', 'login'), user: nat})
  .state({total: 0})
  .maps({Fails: 0})
  .assume(({op, user, Fails, total}) => op.is('fail').or(Fails.at(user).lt(3)).and(global ? op.is('fail').or(total.lt(10)) : op.is('fail').or(op.is('login'))))
  .step(({op, user, Fails, total}) => ({Fails: Fails.set(user, when(op.is('fail'), Fails.at(user).plus(1), Fails.at(user))), total: when(op.is('fail'), total.plus(1), total)}))

test('isolation: a per-user lockout keeps each user\'s cell and refusals whatever the others do', () => {
  const v = proveTwoRuns(isolation(lockout(false), {owner: 'user'}), {search: {ms: 5000}})
  expect(v.proven && v.checked).toBe(true)
})
test('isolation: a global lockout lets the others lock B out', () => {
  const v = proveTwoRuns(isolation(lockout(true), {owner: 'user'}), {search: {ms: 5000}})
  expect(v.proven).toBe(false)
  expect(v.goal).toContain('refuse the same requests')
  expect(v.run).toBeDefined()
})

// A cap, and two refactors of it: one the same rule, one with the boundary moved.
const cap = (variant: 0 | 1 | 2) => rule('cap').params({limit: nat}).inputs({cost: nat}).state({used: 0})
  .step(({cost, used, limit}) => ({used: variant === 0 ? when(used.plus(cost).atMost(limit), used.plus(cost), used)
    : variant === 1 ? when(limit.lt(used.plus(cost)), used, used.plus(cost)) : when(used.plus(cost).lt(limit), used.plus(cost), used)}))

test('agreement: a refactor agrees on every history; a moved boundary is refuted', () => {
  expect(proveTwoRuns(agreement(cap(0), cap(1)), {search: {ms: 5000}}).proven).toBe(true)
  const v = proveTwoRuns(agreement(cap(0), cap(2)), {search: {ms: 5000}})
  expect(v.proven).toBe(false)
  expect(v.run).toBeDefined()
})

test('two runs side by side run as their sides do', () => {
  const r = desk(false), p = twoRuns(r, r, {shared: ['op', 'amount'], refusals: 'assumed'})
  const one = interpret(r.machine), two = interpret(p.machine)
  let a: State = one.init({}), b: State = one.init({}), ab: State = two.init({})
  const reqs = [{op: 0, amount: 50, diagnosis: 3, d2: 7}, {op: 1, amount: 0, diagnosis: 1, d2: 2}, {op: 0, amount: 200, diagnosis: 8, d2: 0}, {op: 1, amount: 0, diagnosis: 0, d2: 0}]
  for (const q of reqs) {
    a = one.step({}, a, {op: q.op, amount: q.amount, diagnosis: q.diagnosis})
    b = one.step({}, b, {op: q.op, amount: q.amount, diagnosis: q.d2})
    ab = two.step({}, ab, {op: q.op, amount: q.amount, a_diagnosis: q.diagnosis, b_diagnosis: q.d2})
    for (const [n, x] of Object.entries(a.scalars)) expect(ab.scalars[`a_${n}`]).toBe(x)
    for (const [n, x] of Object.entries(b.scalars)) expect(ab.scalars[`b_${n}`]).toBe(x)
  }
})

// --- the law text: durations, citations, laws about two runs in the CLI --------------------------------------------------
test('durations: linear over the clock; a month, a year or a business day refused', () => {
  expect(duration('30 days')).toBe(2_592_000)
  expect(duration('15 minutes', 'ms')).toBe(900_000)
  expect(duration('2 weeks')).toBe(1_209_600)
  for (const t of ['1 month', '2 years', '10 business days', '1 quarter']) expect(() => duration(t)).toThrow(/fixed number of seconds/)
  expect(() => parse('now - t >= 30 days')).not.toThrow()
  expect(() => parse('now - t < 1 month')).toThrow(/state it in days/)
  expect(citesIn('x = 1\n# gdp: cite a law: 45 CFR §164.524(b)(2): within 30 days\n', 'f.py')).toEqual([{law: 'a law', text: '45 CFR §164.524(b)(2): within 30 days', where: 'f.py:2'}])
})

// A records desk (a patient's request for their records): received, then fulfilled within 30 days or escalated.
const DESK = `import time
from dataclasses import dataclass


@dataclass
class Req:
    received: int
    fulfilled: bool
    escalated: bool


class RecordsDesk:
    def __init__(self) -> None:
        self.requests: dict[str, Req] = {}
        self.notes: dict[str, int] = {}

    # gdp: law the diagnosis stays private: diagnosis never reaches requests
    # gdp: law one patient's requests never change another's: isolated by rid
    def receive(self, rid: str, diagnosis: int) -> None:
        if rid in self.requests:
            raise ValueError("already received")
        self.requests[rid] = Req(int(time.time()), False, False)
        self.notes[rid] = diagnosis

    # gdp: law fulfilled only within 30 days: requests[rid].fulfilled implies now - requests[rid].received < 30 days
    # gdp: cite fulfilled only within 30 days: 45 CFR 164.524(b)(2): act on a request for access no later than 30 calendar days after its receipt
    def fulfill(self, rid: str) -> None:
        if rid not in self.requests:
            raise ValueError("no such request")
        r = self.requests[rid]
        if r.fulfilled or r.escalated:
            raise ValueError("closed")
        if int(time.time()) - r.received >= 2592000:
            r.escalated = True
        else:
            r.fulfilled = True
`
const hasPython = (() => { try { return spawnSync('python3', ['--version']).status === 0 } catch { return false } })()
test.skipIf(!hasPython)('the CLI: laws about two runs, a deadline in days, its citation and certificate, in Python', async () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-regulated-`)
  writeFileSync(`${dir}/desk.py`, DESK)
  const r = await check([`${dir}/desk.py`], {ms: 5000, propose: false, cert: `${dir}/certs`})
  const laws = Object.fromEntries(r.rules[0]!.laws.map(l => [l.name, l]))
  if (!r.rules[0]!.ok) console.log(JSON.stringify(r.rules[0]!.refusals))
  expect(r.rules[0]!.ok).toBe(true)
  for (const n of ['the diagnosis stays private', 'one patient\'s requests never change another\'s', 'fulfilled only within 30 days']) expect(laws[n]?.verdict).toBe('proven')
  expect(laws['fulfilled only within 30 days']!.cites).toEqual(['45 CFR 164.524(b)(2): act on a request for access no later than 30 calendar days after its receipt'])
  // the certificate: the kernel's to check, its meta the citation (never read by a checker)
  const doc = JSON.parse(readFileSync(laws['fulfilled only within 30 days']!.cert!, 'utf8')) as Document
  expect((doc.meta as {cites: string[]}).cites[0]).toContain('164.524')
  expect(checkCertificate(fromInterchange(doc)).every(c => c.accepted)).toBe(true)
  expect(laws['one patient\'s requests never change another\'s']!.cert).toBeDefined()
  // a law over the diagnosis that it does reach: broken by two runs
  writeFileSync(`${dir}/desk.py`, DESK.replace('Req(int(time.time()), False, False)', 'Req(int(time.time()) + diagnosis, False, False)'))
  const r2 = await check([`${dir}/desk.py`], {ms: 5000, propose: false})
  const leak = r2.rules[0]!.laws.find(l => l.name === 'the diagnosis stays private')!
  expect(leak.verdict).toBe('broken')
  expect(leak.run!.some(s => s.includes('|'))).toBe(true)
}, 300_000)

// --- business days over a calendar (calendar.ts) ------------------------------------------------------------------------
// The count against a day-by-day walk of the calendar (JavaScript's Date): the business days after a's day up to and
// including b's, at several weekends, offsets and both clocks.
const walked = (weekend: string[], holidays: string[], off: number, a: number, b: number) => {
  const day = (t: number) => Math.floor((t + off) / 86_400), names = ['sun', 'mon', 'tue', 'wed', 'thu', 'fri', 'sat']
  const work = (d: number) => { const t = new Date(d * 86_400_000); return !weekend.includes(names[t.getUTCDay()]!) && !holidays.includes(t.toISOString().slice(0, 10)) }
  let n = 0
  for (let d = Math.min(day(a), day(b)) + 1; d <= Math.max(day(a), day(b)); d++) if (work(d)) n += day(b) >= day(a) ? 1 : -1
  return n
}
const HOLIDAYS = ['2026-01-01', '2026-05-25', '2026-07-03', '2026-11-26', '2026-12-25', '2027-01-01', '2026-02-13', '2026-02-14']
test('business days: the count is the calendar walked day by day', () => {
  let seed = 7
  const rnd = (k: number) => { seed = (seed * 1_103_515_245 + 12_345) % 2_147_483_648; return seed % k }
  for (const [weekend, off, secs] of [[['sat', 'sun'], '-05:00', -18_000], [['fri', 'sat'], '+03:00', 10_800], [['sun'], '+14:00', 50_400], [['sat', 'sun'], '-14:00', -50_400]] as const) {
    for (const clock of ['s', 'ms'] as const) {
      const bd = businessDays({weekend: [...weekend], holidays: HOLIDAYS, utc_offset: off}, clock), u = clock === 'ms' ? 1000 : 1
      for (let i = 0; i < 400; i++) {
        const a = 1_766_361_600 + rnd(400 * 86_400), b = a + rnd(40 * 86_400) - (i % 5 ? 0 : rnd(10 * 86_400))
        const x = bd.between(a * u, b * u), want = walked([...weekend], HOLIDAYS, secs, a, b)
        expect(x.pos.val! - x.neg.val!).toBe(want)
        expect(bd.count(a * u, b * u)).toBe(want)
      }
    }
  }
  for (const bad of [{weekend: ['sat', 'sun', 'mon', 'tue', 'wed', 'thu', 'fri']}, {weekend: ['caturday']}, {holidays: ['2026-02-30']}, {utc_offset: '+15:00'}, {utc_offset: 'EST'}]) expect(() => businessDays(bad)).toThrow()
  expect(() => parse('now - t <= 10 business days')).not.toThrow()
})

// A records desk written with the builders: a request is received, then answered while it is under 14 calendar days old.
const cal = businessDays({weekend: ['sat', 'sun'], holidays: HOLIDAYS, utc_offset: '-05:00'})
const desk14 = (days: number) => rule('desk14').inputs({op: oneOf('receive', 'answer'), now: nat}).state({received: 0, answered: 0, open: 0, done: 0})
  .step(({op, now, received, answered, open, done}) => {
    const answers = op.is('answer').and(open.eq(1)).and(now.lt(received.plus(days * 86_400)))
    return {received: when(op.is('receive').and(open.eq(0)), now, received), open: when(op.is('receive'), 1, when(answers, 0, open)),
      answered: when(answers, now, answered), done: when(answers, 1, when(op.is('receive'), 0, done))}
  })
test('business days: a deadline law of one step (each time\'s week a key) and of the state (divided out), proven and broken', () => {
  // (of one step: an answer given now is at most n business days after the request's day)
  const stepLaw = (r: ReturnType<typeof desk14>, n: number) => r.stepLaw(`answered within ${n} business days`, (b, a) => forall((w1, w2) => {
    const p = cal.pin(b.received, w1), q = cal.pin(b.now, w2)
    return all(p.guard, q.guard).implies(a.done.eq(1).and(b.done.eq(0)).implies(cal.between(p.at, q.at).atMost(n)))
  }))
  const r = desk14(14)
  expect(proveSteps(r, [], [stepLaw(r, 10)], {search: false})).toMatchObject({proven: true, checked: true})
  // (14 calendar days can be 10 business days: from a request on a Saturday, the tenth falls on the 13th day)
  const broken = proveSteps(r, [], [stepLaw(r, 9)], {search: {ms: 20_000}})
  expect(broken.proven).toBe(false)
  expect(broken.run).toBeDefined()
  // (of the state: every answer recorded is within 10 business days of its request, given that it is under 14
  // calendar days, the helper the kernel's step needs)
  const law = (r: ReturnType<typeof desk14>, n: number) => r.law(`recorded within ${n}`, ({done, received, answered}) => done.eq(1).implies(cal.between(received, answered).atMost(n)))
  const helper = r.law('answered under 14 days', ({done, received, answered}) => done.eq(1).implies(answered.lt(received.plus(14 * 86_400))))
  expect(proveRule(r, [helper, law(r, 10)], {search: false})).toMatchObject({proven: true, checked: true})
  const r15 = desk14(15)
  expect(proveRule(r15, [law(r15, 10)], {search: {ms: 20_000}}).run).toBeDefined()
}, 120_000)

test.skipIf(!hasPython)('the CLI: a deadline in business days over the calendar in gdp.toml, proven and broken', async () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-bdays-`)
  const src = DESK.replace('# gdp: law fulfilled only within 30 days: requests[rid].fulfilled implies now - requests[rid].received < 30 days',
    '# gdp: law within 10 business days: requests[rid].fulfilled implies now - requests[rid].received <= 10 business days\n    # gdp: law within 9 business days: requests[rid].fulfilled implies now - requests[rid].received <= 9 business days')
    .replace('# gdp: cite fulfilled only within 30 days: 45 CFR 164.524(b)(2): act on a request for access no later than 30 calendar days after its receipt', '').replace('>= 2592000', '>= 14 * 86400')
  writeFileSync(`${dir}/desk.py`, src)
  const none = await check([`${dir}/desk.py`], {ms: 5000, propose: false})
  expect(none.rules[0]!.laws.find(l => l.name === 'within 10 business days')).toMatchObject({verdict: 'not read', why: expect.stringContaining('need a calendar')})
  writeFileSync(`${dir}/gdp.toml`, `[calendar]\nweekend = ["sat", "sun"]\nholidays = ${JSON.stringify(HOLIDAYS)}\nutc_offset = "-05:00"\n`)
  const r = await check([`${dir}/desk.py`], {ms: 20_000, propose: false})
  const laws = Object.fromEntries(r.rules[0]!.laws.map(l => [l.name, l]))
  expect(laws['within 10 business days']!.verdict).toBe('proven')
  expect(laws['within 9 business days']!.verdict).toBe('broken')
  expect(laws['within 9 business days']!.run!.length).toBeGreaterThan(1)
}, 300_000)
