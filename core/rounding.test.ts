// Fixed-point rounding read from Python (core/extract-step.ts's quotient): a price put on a tick by a floor (p // k * k,
// p - p % k), by Python's round(p / k) * k (to the nearest, a half to the even one), each exact over the integers, the
// rule checked against the code by running both; laws about the tick proven (on a tick: in every state, as the kernel
// reads a division only in a law about every state), and "a half never rounds down" broken by a run the code itself
// takes (round(25 / 10) is 2). Skipped where python3 isn't installed.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {check} from './cli.ts'
import {extractPython} from './extract-py.ts'

const hasPy = (() => { try { execFileSync('python3', ['--version'], {stdio: 'ignore'}); return true } catch { return false } })()
const t = hasPy ? test : test.skip

const QUOTER = `TICK = 10


class Quoter:
    def __init__(self):
        self.bid = 0
        self.ask = 0

    # gdp: law the bid is at most the price: bid <= p
    # gdp: law the bid is within a tick: p - bid < 10
    def quote_bid(self, p: int) -> None:
        self.bid = p // TICK * TICK

    # gdp: law the ask is within half a tick: 2 * (ask - p) <= 10 and 2 * (p - ask) <= 10
    # gdp: law a half never rounds down: p - ask != 5
    def quote_ask(self, p: int) -> None:
        self.ask = round(p / TICK) * TICK

    # gdp: law the bid is on a tick: bid == bid // 10 * 10
    # gdp: law the ask is on a tick: ask == ask // 10 * 10
`

t('a price on a tick: a floor and Python round, exact; the tick laws proven, a half rounding up broken', async () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-tick-`), f = `${dir}/quoter.py`
  writeFileSync(f, QUOTER)
  const x = extractPython(f, {check: {runs: 60, depth: 6, states: 80}})
  if (!x.ok) throw new Error(JSON.stringify(x.refusals))
  expect(x.evidence!.mismatch).toBeUndefined()
  const {rules} = await check([f], {ms: 20_000, propose: false})
  const v = Object.fromEntries(rules[0]!.laws.map(l => [l.name, l]))
  if (rules[0]!.laws.some(l => l.verdict === 'unknown')) console.log(x.source, JSON.stringify(rules[0]!.laws, null, 1))
  for (const n of ['the bid is at most the price', 'the bid is within a tick', 'the ask is within half a tick', 'the bid is on a tick', 'the ask is on a tick']) expect([n, v[n]!.verdict]).toEqual([n, 'proven'])
  expect(v['a half never rounds down']!.verdict).toBe('broken')
  // The break, replayed in Python: the code rounds that half down too (to the even tick).
  const call = v['a half never rounds down']!.run!.at(-1)!, p = Number(/p=(-?\d+)/.exec(call)![1])
  const got = Number(execFileSync('python3', ['-c', `import sys; sys.path.insert(0, ${JSON.stringify(dir)}); from quoter import Quoter; q = Quoter(); q.quote_ask(p=${p}); print(q.ask)`], {encoding: 'utf8'}).trim())
  expect(p - got).toBe(5)
}, 300_000)

// round(a / k) past 2^52: the float a / k may land on a half it isn't (3·2^51 + 2 over 3 is 2^51 + 0.5 as a float, and
// Python rounds it to the even 2^51, 2 below the true 2^51 + 2/3 rounded), so the claim stops there: an edge the check
// counts apart, never a step the rule takes otherwise than the code.
t('round(a / k) at |a| of 2^52 or more: an edge, the claim below it', async () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-tick-`), f = `${dir}/third.py`
  writeFileSync(f, `class Q:\n    def __init__(self):\n        self.ask = 0\n\n    # gdp: law within half a tick: 2 * (ask - p) <= 3 and 2 * (p - ask) <= 3\n    def quote(self, p: int) -> None:\n        self.ask = round(p / 3) * 3\n`)
  const x = extractPython(f, {check: {runs: 60, depth: 6, states: 80}})
  if (!x.ok) throw new Error(JSON.stringify(x.refusals))
  expect(x.evidence!.edge).toBeGreaterThan(0)
  const a = 3 * 2 ** 51 + 2
  expect(Number(execFileSync('python3', ['-c', `print(round(${a} / 3) * 3 - ${a})`], {encoding: 'utf8'}).trim())).toBe(-2)
  const {rules} = await check([f], {ms: 20_000, propose: false})
  expect(rules[0]!.laws[0]!.verdict).toBe('proven')

}, 300_000)

// Java: a float division read where it is rounded to a whole number (Math.floor, Math.round ties up, a cast truncating
// toward zero), as a quotient by the constant; the half-up law proven, "a half never rounds up" refuted and replayed.
const javac = process.env.JAVA_HOME ? `${process.env.JAVA_HOME}/bin/javac` : 'javac'
const hasJdk = (() => { try { execFileSync(javac, ['-version'], {stdio: 'ignore'}); return true } catch { return false } })()
const JQUOTER = `public class Quoter {
    private long bid = 0;
    private long ask = 0;
    private long mid = 0;

    // gdp: law the bid is at most the price: bid <= p
    // gdp: law the bid is within a tick: p - bid < 10
    public void quoteBid(long p) {
        bid = (long) Math.floor(p / 10.0) * 10;
    }

    // gdp: law the ask is within half a tick: 2 * (ask - p) <= 10 and 2 * (p - ask) <= 10
    // gdp: law a half never rounds up: 2 * (ask - p) != 10
    public void quoteAsk(long p) {
        ask = Math.round(p / 10.0) * 10;
    }

    // gdp: law a cast truncates toward zero: (p >= 0 implies mid <= p) and (p <= 0 implies p <= mid)
    public void quoteMid(long p) {
        mid = (long) (p / 10.0) * 10;
    }
}
`
;(hasJdk ? test : test.skip)('Java: Math.floor, Math.round and a cast of a float division, exact below their edges', async () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-jtick-`), f = `${dir}/Quoter.java`
  writeFileSync(f, JQUOTER)
  const {rules} = await check([f], {ms: 20_000, propose: false})
  const r = rules[0]!
  if (!r.ok) throw new Error(JSON.stringify(r.refusals))
  const v = Object.fromEntries(r.laws.map(l => [l.name, l]))
  for (const n of ['the bid is at most the price', 'the bid is within a tick', 'the ask is within half a tick', 'a cast truncates toward zero']) expect([n, v[n]!.verdict]).toEqual([n, 'proven'])
  expect(v['a half never rounds up']!.verdict).toBe('broken')
  const p = Number(/p=(-?\d+)/.exec(v['a half never rounds up']!.run!.at(-1)!)![1])
  expect(Math.round(p / 10) * 10 - p).toBe(5)
  // (Math.round of an integer, an integer division's say: javac's round(float), the argument a float of 24 bits first:
  // itself below 2^24, an edge past it)
  const g = `${dir}/Ten.java`
  writeFileSync(g, 'public class Ten {\n    private long q = 0;\n\n    public void quote(long p) {\n        q = Math.round(p / 10) * 10;\n    }\n}\n')
  const {rules: r2} = await check([g], {ms: 5_000, propose: false})
  expect(r2[0]!.refusals).toEqual([])
}, 300_000)
