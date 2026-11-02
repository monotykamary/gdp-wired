// While loops over the state's ordered collections, read from Python (core/extract-step.ts's whileStmt and whileRank):
// a loop whose passes take the first item of a list, each taking it out or ending the loop, as a fold over the list's
// places (a queue's front) or over its items in an order of its own (min or max by a key: a book's best first), every
// request carrying the run its passes compute; each rule checked against the code by running both, and laws about the
// items taken proven or refuted through `check`. Skipped where python3 isn't installed.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {check} from './cli.ts'
import {extractPython} from './extract-py.ts'

const hasPy = (() => { try { execFileSync('python3', ['--version'], {stdio: 'ignore'}); return true } catch { return false } })()
const t = hasPy ? test : test.skip
const file = (name: string, code: string) => { const dir = mkdtempSync(`${tmpdir()}/gdp-loops-`); writeFileSync(`${dir}/${name}`, code); return `${dir}/${name}` }

// A queue of tasks run in the order they came, each due at a time: the passes take the front while it is due.
const QUEUE = `from dataclasses import dataclass


@dataclass
class Task:
    due: int
    cost: int


class Queue:
    def __init__(self):
        self.tasks: list[Task] = []

    def add(self, due: int, cost: int) -> None:
        self.tasks.append(Task(due, cost))

    # gdp: law the tasks run were due: forall t in old(self.tasks): t in self.tasks or t.due <= now
    # gdp: law no task left is due: forall t in self.tasks: now < t.due
    def run_due(self, now: int) -> int:
        spent = 0
        while self.tasks and self.tasks[0].due <= now:
            spent += self.tasks[0].cost
            self.tasks.pop(0)
        return spent
`

t('a queue drained from its front: the fold over its places; the tasks run were due, and one left may be due (it waits behind one that isn’t)', async () => {
  const f = file('queue.py', QUEUE)
  const x = extractPython(f, {check: {runs: 60, depth: 6, states: 80}})
  if (!x.ok) throw new Error(JSON.stringify(x.refusals))
  expect(x.evidence!.mismatch).toBeUndefined()
  expect(x.source).toContain('.carriesList("loop$0"')
  const {rules} = await check([f], {ms: 30_000, propose: false})
  const v = Object.fromEntries(rules[0]!.laws.map(l => [l.name, l]))
  expect(v['the tasks run were due']!.verdict).toBe('proven')
  expect(v['no task left is due']!.verdict).not.toBe('proven')
}, 600_000)

// A pass that keeps its item ends the loop: the code reads the same item again, where the condition fails (or the
// rule refuses: the next pass would take it again), never the next item.
t('a pass that keeps its item ends the loop, the next item untouched', () => {
  const f = file('bump.py', `from dataclasses import dataclass


@dataclass
class Item:
    qty: int


class Q:
    def __init__(self):
        self.items: list[Item] = []

    def add(self, q: int) -> None:
        self.items.append(Item(q))

    def bump(self, limit: int) -> None:
        while self.items and self.items[0].qty < limit:
            self.items[0].qty = limit
`)
  const x = extractPython(f, {check: {runs: 60, depth: 6, states: 80}})
  if (!x.ok) throw new Error(JSON.stringify(x.refusals))
  expect(x.evidence!.mismatch).toBeUndefined()
}, 300_000)

// A book's asks taken best first (the lowest price, the earliest at it), each fill as much as the order still needs.
const BOOK = `from dataclasses import dataclass


@dataclass
class Order:
    price: int
    qty: int
    seq: int


class Book:
    def __init__(self):
        self.asks: list[Order] = []
        self.seq = 0

    def ask(self, price: int, qty: int) -> None:
        if qty <= 0:
            return
        self.seq += 1
        self.asks.append(Order(price, qty, self.seq))

    # gdp: law an ask filled never grows: forall o in old(self.asks): o not in self.asks or o.qty <= old(o.qty)
    # gdp: law the best asks fill first: forall o in old(self.asks): forall j in old(self.asks): o in self.asks or j not in self.asks or o.price < j.price or (o.price == j.price and o.seq < j.seq)
    def buy(self, price: int, qty: int) -> int:
        left = qty
        while left > 0 and self.asks:
            best = min(self.asks, key=lambda o: (o.price, o.seq))
            if best.price > price:
                break
            fill = min(left, best.qty)
            left -= fill
            best.qty -= fill
            if best.qty == 0:
                self.asks.remove(best)
        return qty - left
`

t('a book taken best first: the fold over its items in the order min reads them, the rule checked against the code', () => {
  // (its laws are about every two items through the order the request carries: decided in research/trading/corpus,
  // minutes each, not in this quick suite)
  const f = file('book.py', BOOK)
  const x = extractPython(f, {check: {runs: 60, depth: 6, states: 80}})
  if (!x.ok) throw new Error(JSON.stringify(x.refusals))
  expect(x.evidence!.mismatch).toBeUndefined()
  expect(x.evidence!.requests).toBeGreaterThan(100)
  expect(x.source).toContain('.carriesList("asks__ord", record({k: nat}))')
  expect(x.source).toContain('.carries("asks__rk")')
}, 300_000)

t('refused, each where it is: a pass writing another item, a list taken by two orders, a dict taken in its keys’ order', () => {
  const refusal = (code: string) => { const x = extractPython(file('r.py', code), {check: false as never}); return x.ok ? 'read' : x.refusals.map(r => r.what).join('; ') }
  const head = 'from dataclasses import dataclass\n\n\n@dataclass\nclass O:\n    p: int\n    q: int\n\n\nclass B:\n    def __init__(self):\n        self.xs: list[O] = []\n        self.d: dict[int, int] = {}\n\n    def add(self, p: int, q: int) -> None:\n        self.xs.append(O(p, q))\n\n'
  expect(refusal(`${head}    def go(self) -> None:\n        while self.xs:\n            a = min(self.xs, key=lambda o: o.p)\n            b = max(self.xs, key=lambda o: o.p)\n            self.xs.remove(a)\n`)).toContain('read in two orders')
  expect(refusal(`${head}    def go(self) -> None:\n        while self.xs:\n            self.xs.pop(0)\n            self.xs.append(O(1, 1))\n`)).toContain('an item put in xs in a pass of a loop')
  // (the list read again after the pass took its item out: the pass's item is the one it took)
  expect(refusal(`${head}    def go(self) -> None:\n        while self.xs:\n            self.xs.pop(0)\n            self.xs.pop(0)\n`)).toContain('read again in a pass of the loop')
  // (a failure after the loop wrote the list: the caller would see it changed)
  expect(refusal(`${head}    def go(self, n: int) -> None:\n        while self.xs and self.xs[0].p <= n:\n            self.xs.pop(0)\n        if n > 5:\n            raise ValueError("late")\n`)).toContain('after the state is written')
})

// A loop on one branch only: the list is written at every key where the branch is taken, as it was elsewhere.
t('a loop on one branch: the list as the passes left it there, as it was on the other', () => {
  const body = QUEUE.slice(0, QUEUE.indexOf('    # gdp: law')) + `    def run_due(self, now: int, paused: bool) -> int:
        spent = 0
        if not paused:
            while self.tasks and self.tasks[0].due <= now:
                spent += self.tasks[0].cost
                self.tasks.pop(0)
        return spent
`
  const f = file('paused.py', body)
  const x = extractPython(f, {check: {runs: 60, depth: 6, states: 80}})
  if (!x.ok) throw new Error(JSON.stringify(x.refusals))
  expect(x.evidence!.mismatch).toBeUndefined()
}, 300_000)
