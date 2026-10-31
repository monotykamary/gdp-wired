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
