// Business days over a calendar (calendar.ts) and drafting laws from a clause (draft.ts): the count against the calendar
// walked day by day, deadline laws over it proven and broken (built, and through the CLI with gdp.toml's calendar), and
// a drafter's laws read over the code's names, an unreviewed citation refused by --require-review. Apart from
// relational.test.ts: these are the suite's heaviest tests of law text, and run last of core's.
import {expect, test} from 'bun:test'
import {all, forall, nat, oneOf, proveRule, proveSteps, rule, when} from './dsl.ts'
import {businessDays, parse} from './laws.ts'
import {draftComments, draftPrompt, parseDraft, reviewOf, vetDrafts} from './draft.ts'
import {check} from './cli.ts'
import {spawnSync} from 'node:child_process'
import {mkdtempSync, readFileSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'

const hasPython = (() => { try { return spawnSync('python3', ['--version']).status === 0 } catch { return false } })()
// A records desk (relational.test.ts's): a patient's request for their records, fulfilled within 30 days or escalated.

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
        // (a week's guard holds at that week alone)
        const w = Math.floor((a * u + secs * u + 10 * 86_400 * u) / (7 * 86_400 * u))
        expect([w - 1, w, w + 1].map(k => bd.pin(a * u, k).guard.ok)).toEqual([false, true, false])
      }
      // (at the turn of a day: a holiday's midnight, local time, and the second before it)
      for (const h of HOLIDAYS) for (const d of [0, -1, 1]) {
        const mid = Date.UTC(Number(h.slice(0, 4)), Number(h.slice(5, 7)) - 1, Number(h.slice(8, 10))) / 1000 - secs, a = mid - 3 * 86_400
        const x = bd.between(a * u, (mid + d) * u)
        expect(x.pos.val! - x.neg.val!).toBe(walked([...weekend], HOLIDAYS, secs, a, mid + d))
      }
    }
  }
  // (a holiday before 1969-12-22, a day below 0: its weekday by the remainder at least 0)
  const old = businessDays({holidays: ['1969-12-19', '1969-12-05']}), at = (d: string) => Date.UTC(Number(d.slice(0, 4)), Number(d.slice(5, 7)) - 1, Number(d.slice(8, 10))) / 1000 + 3600
  for (const [a, b] of [['1969-12-18', '1969-12-19'], ['1969-12-01', '1969-12-23'], ['1969-11-30', '1970-01-05']]) {
    const x = old.between(at(a!), at(b!))
    expect(x.pos.val! - x.neg.val!).toBe(walked(['sat', 'sun'], ['1969-12-19', '1969-12-05'], 0, at(a!), at(b!)))
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

// --- drafting laws from a clause (draft.ts): read over the code's names, marked unreviewed until a person signs ------------
test.skipIf(!hasPython)('drafting: a drafter\'s laws read over the code\'s names, refused where they name what it lacks; an unreviewed citation refused by --require-review', async () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-draft-`)
  writeFileSync(`${dir}/desk.py`, DESK.split('\n').filter(l => !l.includes('gdp:')).join('\n'))
  const {extractPython} = await import('./extract-py.ts')
  const x = extractPython(`${dir}/desk.py`, {})
  const prompt = draftPrompt(x, 'Act on a request for access no later than 30 days after its receipt.', '45 CFR 164.524(b)(2)')
  expect(prompt).toContain('requests  state (fields: received, fulfilled, escalated)')
  expect(prompt).toContain('fulfill(rid)  request')
  const answer = 'Sure:\n[{"method": "fulfill", "name": "acted on within 30 days.", "expr": "requests[rid].fulfilled implies now - requests[rid].received < 30 days", "answers": "no later than 30 days"},' +
    ' {"method": null, "name": "denied: never both", "expr": "forall r in requests: not requests[r].denied", "answers": "deny"}]'
  const {kept, refused} = vetDrafts(x, parseDraft(answer), {clock: 1})
  expect(kept.map(d => d.name)).toEqual(['acted on within 30 days'])
  expect(refused[0]!.d.name).toBe('denied - never both')
  const lines = draftComments('#', kept[0]!, '45 CFR 164.524(b)(2)', 'a model')
  expect(lines[1]).toBe('# gdp: cite acted on within 30 days: 45 CFR 164.524(b)(2): "no later than 30 days" [unreviewed: drafted by a model]')
  expect([reviewOf(lines[1]!), reviewOf('x [reviewed-by: A. Person, 2026-11-02]'), reviewOf('45 CFR 164.524')]).toEqual(['unreviewed', 'reviewed', 'unmarked'])
  // (pasted above fulfill: checked as any law, its citation unreviewed until signed)
  writeFileSync(`${dir}/desk.py`, DESK.split('\n').filter(l => !l.includes('gdp:')).join('\n').replace('    def fulfill(', `    ${lines[0]}\n    ${lines[1]}\n    def fulfill(`))
  const {main} = await import('./cli.ts')
  expect(await main(['check', `${dir}/desk.py`, '--no-propose', '--json'])).toBe(0)
  expect(await main(['check', `${dir}/desk.py`, '--no-propose', '--json', '--require-review'])).toBe(2)
  writeFileSync(`${dir}/desk.py`, readFileSync(`${dir}/desk.py`, 'utf8').replace('[unreviewed: drafted by a model]', '[reviewed-by: A. Person, 2026-11-02]'))
  expect(await main(['check', `${dir}/desk.py`, '--no-propose', '--json', '--require-review'])).toBe(0)
}, 300_000)
