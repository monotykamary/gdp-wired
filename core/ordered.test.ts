// Ordered collections read from Python (core/extract-step.ts's lists of the state, core/dsl.ts's least keys): a list
// of records the constructor makes empty is its items in order, each at a key that only grows; min and max by a key,
// xs[0] and xs[-1], append, remove and pop are its least keys and writes of one place; laws over every two items
// (core/laws.ts) proven or refuted through `check`, each rule checked against the code by running both. Skipped where
// python3 isn't installed.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {check} from './cli.ts'
import {extractPython} from './extract-py.ts'

const hasPy = (() => { try { execFileSync('python3', ['--version'], {stdio: 'ignore'}); return true } catch { return false } })()
const t = hasPy ? test : test.skip
const file = (code: string) => { const dir = mkdtempSync(`${tmpdir()}/gdp-ordered-`); writeFileSync(`${dir}/book.py`, code); return `${dir}/book.py` }

// A continuous double auction of single units, as small exchanges write one: the best bid the highest price, the
// earliest at it; the best ask the lowest, the earliest at it.
const BOOK = `from dataclasses import dataclass


@dataclass
class Order:
    trader: int
    price: int
    side: str
    time: int


class Book:
    def __init__(self):
        self.bids: list[Order] = []
        self.asks: list[Order] = []

    def bid(self, trader: int, price: int, time: int) -> None:
        self.bids.append(Order(trader, price, "bid", time))

    def ask(self, trader: int, price: int, time: int) -> None:
        self.asks.append(Order(trader, price, "ask", time))

    def best_bid(self) -> Order | None:
        if not self.bids:
            return None
        return max(self.bids, key=lambda o: (o.price, -o.time))

    def best_ask(self) -> Order | None:
        if not self.asks:
            return None
        return min(self.asks, key=lambda o: (o.price, o.time))

    # gdp: law an ask fills the best bid: forall o in old(self.bids): forall j in old(self.bids): o in self.bids or o.price > j.price or (o.price == j.price and o.time <= j.time)
    # gdp: law a bid fills the best ask: forall o in old(self.asks): forall j in old(self.asks): o in self.asks or o.price < j.price or (o.price == j.price and o.time <= j.time)
    # gdp: law a fill crosses: forall b in old(self.bids): forall a in old(self.asks): b in self.bids or a in self.asks or a.price <= b.price
    # gdp: law no trader trades with itself: forall b in old(self.bids): forall a in old(self.asks): b in self.bids or a in self.asks or b.trader != a.trader
    def match(self) -> bool:
        bb, ba = self.best_bid(), self.best_ask()
        if bb is None or ba is None:
            return False
        if bb.price < ba.price:
            return False
        self.bids.remove(bb)
        self.asks.remove(ba)
        return True
`

t('an order book of two lists: price-time priority proven, a self-trade found and replayed', async () => {
  const f = file(BOOK)
  const {rules} = await check([f], {ms: 20_000, propose: false})
  const r = rules[0]!
  if (!r.ok) throw new Error(JSON.stringify(r.refusals))
  expect(r.notes.join('\n')).toMatch(/bids: a list, read as its items in order/)
  expect(r.notes.join('\n')).toMatch(/Order\.side: a string the module only sets to "ask" or "bid"/)
  const v = Object.fromEntries(r.laws.map(l => [l.name, l]))
  expect(v['an ask fills the best bid']!.verdict).toBe('proven')
  expect(v['a bid fills the best ask']!.verdict).toBe('proven')
  expect(v['a fill crosses']!.verdict).toBe('proven')
  expect(v['no trader trades with itself']!.verdict).toBe('broken')
  // The run that breaks it, replayed in the code: one trader's bid and ask at one price, matched.
  const run = v['no trader trades with itself']!.run!.join('\n')
  expect(run).toMatch(/match/)
}, 300_000)

t('the extracted rule: its least keys printed, checked against the code', () => {
  const x = extractPython(file(BOOK), {check: {runs: 40, depth: 8, states: 80}})
  if (!x.ok) throw new Error(JSON.stringify(x.refusals))
  expect(x.evidence!.mismatch).toBeUndefined()
  expect(x.evidence!.requests).toBeGreaterThan(100)
  expect(x.source).toMatch(/\.least\(\{/)
  expect(x.source).toMatch(/desc\(/)
})

// A FIFO queue of numbers: append and pop(0), the first item and the last; a pop takes the oldest.
const QUEUE = `class Queue:
    def __init__(self):
        self.items: list[int] = []
        self.taken = 0

    def put(self, x: int) -> None:
        self.items.append(x)

    # gdp: law a take removes the first item: forall o in old(self.items): forall j in old(self.items): o in self.items or o <= j
    # gdp: law a take keeps the others: forall o in old(self.items): forall j in old(self.items): o in self.items or j == o or j in self.items
    def take(self) -> int:
        if not self.items:
            return -1
        self.taken = self.items[0]
        return self.items.pop(0)

    def last(self) -> int:
        if not self.items:
            return -1
        return self.items[-1]
`

t('a queue of numbers: the first and last items, pop(0), checked against the code; a take removes the first item', async () => {
  const f = file(QUEUE), x = extractPython(f, {check: {runs: 40, depth: 8, states: 80}})
  if (!x.ok) throw new Error(JSON.stringify(x.refusals))
  expect(x.evidence!.mismatch).toBeUndefined()
  expect(x.evidence!.requests).toBeGreaterThan(100)
  const {rules} = await check([f], {ms: 20_000, propose: false})
  expect(rules[0]!.laws.map(l => [l.name, l.verdict])).toEqual([['a take removes the first item', 'proven'], ['a take keeps the others', 'proven']])
}, 300_000)

t('refused, each where it is: a list read past its first and last place, a lambda elsewhere, a least read after a write', () => {
  const bad = (body: string, why: RegExp) => {
    const x = extractPython(file(`class Q:\n    def __init__(self):\n        self.items: list[int] = []\n\n    def f(self, x: int) -> int:\n${body}`), {entry: 'Q', check: {runs: 5}})
    expect(x.ok).toBe(false)
    expect(x.refusals.map(r => r.what).join('; ')).toMatch(why)
  }
  bad('        return self.items[1]\n', /other than the first or the last/)
  bad('        g = lambda y: y + 1\n        return g(x)\n', /a lambda/)
  bad('        self.items.append(x)\n        return max(self.items)\n', /a collection the step has written/)
  // (found by review: a list read after a write in a call's own arguments, or through bool(), is the list as written)
  bad('        self.items.append(x)\n        return int(bool(self.items))\n', /a collection the step has written/)
  bad('        return min(self.items, default=self.items.pop())\n', /a collection the step has written/)
  bad('        self.items.remove(self.items.pop())\n        return 0\n', /a collection the step has written/)
  const ident = extractPython(file(`from dataclasses import dataclass\n\n\n@dataclass(eq=False)\nclass R:\n    x: int\n\n\nclass Q:\n    def __init__(self):\n        self.items: list[R] = []\n\n    def put(self, x: int) -> None:\n        self.items.append(R(x))\n\n    def drop(self, x: int) -> None:\n        self.items.remove(R(x))\n`), {entry: 'Q', check: {runs: 5}})
  expect(ident.refusals.map(r => r.what).join('; ')).toMatch(/whose equality isn't its fields'/)
})
