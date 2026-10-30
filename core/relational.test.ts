// Laws about two runs (relational.ts): each construction proves what holds and refutes what doesn't, the refutation a
// real pair of runs; the rule built runs as its two sides do.
import {expect, test} from 'bun:test'
import {interpret, type State} from './machine.ts'
import {nat, oneOf, rule, when} from './dsl.ts'
import {agreement, isolation, noninterference, proveTwoRuns, twoRuns} from './relational.ts'
import {citesIn, duration, parse} from './laws.ts'
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
from typing import Literal


@dataclass
class Req:
    received: int
    status: Literal["open", "fulfilled", "escalated"]


class RecordsDesk:
    def __init__(self) -> None:
        self.requests: dict[str, Req] = {}
        self.notes: dict[str, int] = {}

    # gdp: law the diagnosis stays private: diagnosis never reaches requests
    # gdp: law one patient's requests never change another's: isolated by rid
    def receive(self, rid: str, diagnosis: int) -> None:
        if rid in self.requests:
            raise ValueError("already received")
        self.requests[rid] = Req(int(time.time()), "open")
        self.notes[rid] = diagnosis

    # gdp: law fulfilled only within 30 days: requests[rid].status == "fulfilled" implies now - requests[rid].received < 30 days
    # gdp: cite fulfilled only within 30 days: 45 CFR 164.524(b)(2): act on a request for access no later than 30 calendar days after its receipt
    def fulfill(self, rid: str) -> None:
        if rid not in self.requests:
            raise ValueError("no such request")
        r = self.requests[rid]
        if r.status != "open":
            raise ValueError("closed")
        if int(time.time()) - r.received >= 2592000:
            r.status = "escalated"
        else:
            r.status = "fulfilled"
`
const hasPython = (() => { try { return spawnSync('python3', ['--version']).status === 0 } catch { return false } })()
test.skipIf(!hasPython)('the CLI: laws about two runs, a deadline in days, its citation and certificate, in Python', async () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-regulated-`)
  writeFileSync(`${dir}/desk.py`, DESK)
  const r = await check([`${dir}/desk.py`], {ms: 10_000, propose: false, cert: `${dir}/certs`})
  const laws = Object.fromEntries(r.rules[0]!.laws.map(l => [l.name, l]))
  expect(r.rules[0]!.ok).toBe(true)
  for (const n of ['the diagnosis stays private', 'one patient\'s requests never change another\'s', 'fulfilled only within 30 days']) expect(laws[n]?.verdict).toBe('proven')
  expect(laws['fulfilled only within 30 days']!.cites).toEqual(['45 CFR 164.524(b)(2): act on a request for access no later than 30 calendar days after its receipt'])
  // the certificate: the kernel's to check, its meta the citation (never read by a checker)
  const doc = JSON.parse(readFileSync(laws['fulfilled only within 30 days']!.cert!, 'utf8')) as Document
  expect((doc.meta as {cites: string[]}).cites[0]).toContain('164.524')
  expect(checkCertificate(fromInterchange(doc)).every(c => c.accepted)).toBe(true)
  expect(laws['one patient\'s requests never change another\'s']!.cert).toBeDefined()
  // a law over the diagnosis that it does reach: broken by two runs
  writeFileSync(`${dir}/desk.py`, DESK.replace('Req(int(time.time()), "open")', 'Req(int(time.time()), "open" if diagnosis < 5 else "escalated")'))
  const r2 = await check([`${dir}/desk.py`], {ms: 10_000, propose: false})
  const leak = r2.rules[0]!.laws.find(l => l.name === 'the diagnosis stays private')!
  expect(leak.verdict).toBe('broken')
  expect(leak.run!.some(s => s.includes('|'))).toBe(true)
})
