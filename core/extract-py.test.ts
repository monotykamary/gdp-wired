// The Python front end (core/extract-py.ts on core/extract-step.ts): rules read from Python, each checked against the
// Python code it was read from (core/py/harness.py runs it). The cases: a class with a clock and a lock, a dict of
// dataclasses, a decision whose failure is kept, a store the caller states, the boundary (answers, skip), and the
// refusals (a loop, a float that isn't whole, other code). Skipped where python3 isn't installed.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {type PyOptions, extractPython} from './extract-py.ts'
import {all, proveRule, proveSteps, yes} from './dsl.ts'
import {assumed, disjoint} from './extract-step.ts'

const hasPy = (() => { try { execFileSync('python3', ['--version'], {stdio: 'ignore'}); return true } catch { return false } })()
const t = hasPy ? test : test.skip
const budget = {runs: 40, depth: 8, states: 80}
const EX = new URL('./py/examples/bucket.py', import.meta.url).pathname
type X = ReturnType<typeof extractPython>
const ok = (x: X) => {
  if (!x.ok) throw new Error(`refused: ${JSON.stringify(x.refusals)}\n${x.source ?? ''}\n${JSON.stringify(x.evidence)}`)
  expect(x.evidence!.mismatch).toBeUndefined()
  expect(x.evidence!.requests).toBeGreaterThan(0)
  expect(x.evidence!.coverage.hit).toBe(x.evidence!.coverage.arms)
  return x
}
const refused = (x: X, why: RegExp) => { expect(x.ok).toBe(false); expect(x.refusals.map(r => `${r.where}: ${r.what}`).join('; ')).toMatch(why) }
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type A = any
const step = (x: X, name: string, then: (b: A, a: A) => A, when?: (b: A) => A) => {
  const r = x.rule as A
  return proveSteps(r, x.invariants ?? [], [r.stepLaw(name, then, when)])
}
const py = (code: string, opts: PyOptions): X => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-pycase-`)
  writeFileSync(`${dir}/m.py`, code)
  return extractPython(`${dir}/m.py`, {check: budget, ...opts})
}

t('a token bucket: the clock an input, the lock atomic, a failure before any write the refusal', () => {
  const x = ok(extractPython(EX, {entry: 'TokenBucket', check: budget}))
  expect(x.source).toContain('.pre(({capacity0}) => capacity0.gt(0))')
  expect(x.notes.join('\n')).toMatch(/the lock held .*atomic/)
  expect(proveRule(x.rule!, [x.rule!.law('never past its capacity', ({tokens, capacity}: A) => tokens.atMost(capacity))]).proven).toBe(true)
})

t('a dict of dataclasses: a missing key, a Literal mode, a result kept', () => {
  const x = ok(extractPython(EX, {entry: 'Ledger', check: budget}))
  expect(x.source).toContain("mode: oneOf('open', 'closed')")
  expect(step(x, 'a charge never takes a budget past its limit', (b, a) => a.budgets.at(b.charge_user.id).spent.atMost(a.budgets.at(b.charge_user.id).limit),
    b => b.method.is('charge').and(b.budgets.at(b.charge_user.id).spent.atMost(b.budgets.at(b.charge_user.id).limit))).proven).toBe(true)
})

t('a decision whose failure is kept: the law about when it raises', () => {
  const x = ok(extractPython(EX, {entry: ['check'], failures: 'kept', check: budget}))
  expect(step(x, 'refused at the budget', (_b, a) => a.failed, b => b.max_budget_none.not().and(b.spend.atLeast(b.max_budget))).proven).toBe(true)
  expect(step(x, 'refused only past the budget', (_b, a) => a.failed, b => b.max_budget_none.not().and(b.spend.gt(b.max_budget))).proven).toBe(true)
  expect(step(x, 'admitted below it', (_b, a) => a.failed.not(), b => b.spend.lt(b.max_budget)).proven).toBe(true)
})

t('a store the caller states: its keys by template, a count kept with the failure after it', () => {
  const x = ok(extractPython(EX, {entry: 'SessionLimit', methods: ['hit'], failures: 'kept', stores: {cache: {get: ['get'], set: ['set'], value: 'int'}}, check: budget}))
  expect(x.notes.join('\n')).toMatch(/"hits:\{\}" keys held as cache_hits/)
  expect(step(x, 'admitted only below the limit', (b, a) => a.failed.not().implies(b.limit.gt(b.cache_hits.at(b.session.id).value))).proven).toBe(true)
  expect(step(x, 'every hit counts one', (b, a) => a.cache_hits.at(b.session.id).value.eq(b.cache_hits.at(b.session.id).value.plus(1))).proven).toBe(true)
})

t('the boundary: an answered call an input, a skipped one kept only where nothing reads it', () => {
  const x = ok(py(`import logging\nlog = logging.getLogger("m")\n\ndef spend_of(key: str) -> float:\n    raise RuntimeError("not here")\n\n` +
    `async def gate(key: str, cap: int | None) -> None:\n    log.info("gate %s", key)\n    used = spend_of(key)\n    if cap is not None and used >= cap:\n        raise RuntimeError(f"{key} over")\n`,
  {entry: ['gate'], failures: 'kept', answers: {spend_of: 'float'}, skip: ['log']}))
  expect(x.notes.join('\n')).toMatch(/spend_of .*answered by the request/)
  expect(x.notes.join('\n')).toMatch(/log.info .*left out/)
})

// The boundary inferred (no answers, skip or stores stated): each test's rule as the stated one's, or what it needs.
const body = (x: X) => (x.source ?? '').split('\n').filter(l => !l.startsWith('//')).join('\n')
t('the boundary inferred: a store, a skip, an answer tagged where the code is a stand-in', () => {
  const stated = ok(extractPython(EX, {entry: 'SessionLimit', methods: ['hit'], failures: 'kept', stores: {cache: {get: ['get'], set: ['set'], value: 'int'}}, check: budget}))
  const bare = ok(extractPython(EX, {entry: 'SessionLimit', methods: ['hit'], failures: 'kept', check: budget}))
  expect(bare.source).toBe(stated.source!)
  expect(bare.notes.join('\n')).toMatch(/SessionLimit\(cache\): an injected dependency \(inferred/)
  const gate = `import logging\nlog = logging.getLogger("m")\n\ndef spend_of(key: str) -> float:  # gdp: answer\n    raise RuntimeError("not here")\n\n` +
    `async def gate(key: str, cap: int | None) -> None:\n    log.info("gate %s", key)\n    used = spend_of(key)\n    if cap is not None and used >= cap:\n        raise RuntimeError(f"{key} over")\n`
  const tagged = ok(py(gate, {entry: ['gate'], failures: 'kept'}))
  expect(body(tagged)).toBe(body(ok(py(gate, {entry: ['gate'], failures: 'kept', answers: {spend_of: 'float'}, skip: ['log']}))))
  expect(tagged.notes.join('\n')).toMatch(/log.info .*left out \(inferred/)
  expect(tagged.notes.join('\n')).toMatch(/spend_of .*answered by the request \(tagged/)
  // (untagged, the stand-in is read as it is: it raises, so every call fails)
  const standIn = py(gate.replace('  # gdp: answer', ''), {entry: ['gate'], failures: 'kept'})
  expect(standIn.ok).toBe(true)
  expect(standIn.source).toContain('failed: yes')
  refused(extractPython(EX, {entry: 'SessionLimit', methods: ['hit'], failures: 'kept', strict: true}), /state it as a store/)
})

t('the boundary inferred: the entry, own code outside the subset cut, an injected protocol answered', () => {
  const code = `from typing import Protocol\n\nclass Flags(Protocol):\n    def enabled(self, name: str) -> bool: ...\n\n` +
    `def score(xs: dict[str, int]) -> int:\n    total = 0\n    for k in xs:\n        total += xs[k]\n    return total\n\n` +
    `class Gate:\n    def __init__(self, flags: Flags, cap: int):\n        self.flags = flags\n        self.cap = cap\n        self.used = 0\n\n` +
    `    def take(self, xs: dict[str, int]) -> None:\n        if not self.flags.enabled("limits"):\n            return\n        n = score(xs)\n        if self.used + n > self.cap:\n            raise RuntimeError("over")\n        self.used += n\n\n` +
    `    def left(self) -> int:\n        return self.cap - self.used\n`
  const x = ok(py(code, {}))
  const notes = x.notes.join('\n')
  expect(notes).toMatch(/the entry inferred: Gate, the class whose public methods write its state \(take; the others read it\)/)
  expect(notes).toMatch(/score: the module's own code, outside the subset \(m.py:\d+:\d+: a loop/)
  expect(notes).toMatch(/score .*answered by the request \(inferred: its value is read; assumes score may return any int\)/)
  expect(notes).toMatch(/flags.enabled .*answered by the request \(inferred/)
  expect(step(x, 'within the cap where it starts so', (_b, a) => a.used.atMost(a.cap), b => b.used.atMost(b.cap)).proven).toBe(true)
  // A refutation that depends on an inferred answer says so.
  const v = step(x, 'used never goes down', (b, a) => a.used.atLeast(b.used))
  expect(v.proven).toBe(false)
  expect(assumed(x, (v.witness ?? v.run) as Record<string, unknown>).join('; ')).toMatch(/assumes `score` may return -\d+ \(inferred: any int\)/)
  // Other code given the rule's state may change it: refused, with what accepts it.
  const touch = 'import logging\n\nclass C:\n    def __init__(self):\n        self.n = 0\n\n    def bump(self) -> None:\n        logging.getLogger("c").info(self)\n        self.n += 1\n'
  refused(py(touch, {entry: 'C'}), /it is given the rule's state, which other code may change \(if it doesn't, state it: skip: \["info"\], or a `gdp: skip` comment on its line\)/)
  ok(py(touch.replace('.info(self)', '.info(self)  # gdp: skip'), {entry: 'C'}))
})

// FastAPI's Depends marks an injected dependency (a class used as one: its constructor's argument): held as a store.
const hasFastapi = hasPy && (() => { try { execFileSync('python3', ['-c', 'import fastapi'], {stdio: 'ignore'}); return true } catch { return false } })()
;(hasFastapi ? test : test.skip)('the boundary inferred: a dependency FastAPI injects (Depends) held as a store', () => {
  const x = ok(py(`from fastapi import Depends, HTTPException


class Cache:
    async def get(self, key: str) -> int | None: ...
    async def set(self, key: str, value: int) -> None: ...


def get_cache() -> Cache:
    return Cache()


class RateLimiter:
    def __init__(self, cache: Cache = Depends(get_cache), limit: int = 3):
        self.cache = cache
        self.limit = limit

    async def hit(self, user: str) -> None:
        n = (await self.cache.get(f"rl:{user}")) or 0
        if n >= self.limit:
            raise HTTPException(status_code=429)
        await self.cache.set(f"rl:{user}", n + 1)
`, {entry: 'RateLimiter', failures: 'kept'}))
  expect(x.notes.join('\n')).toMatch(/RateLimiter\(cache\): an injected dependency \(inferred: marked so\)/)
  expect(step(x, 'admitted only below the limit', (b, a) => a.failed.not().implies(b.limit.gt(b.cache_rl.at(b.user.id).value))).proven).toBe(true)
})

t('refusals, each where it is with why', () => {
  refused(extractPython(EX, {entry: ['drain'], check: budget}), /bucket.py:\d+:\d+: a loop/)
  refused(py('def f(x: int) -> int:\n    return x * 0.5\n', {entry: ['f']}), /a float that isn't whole/)
  refused(py('import os\n\ndef f(x: int) -> int:\n    return os.getpid() + x\n', {entry: ['f']}), /os.getpid\(\): os.getpid, other code \(m.py:4:12\), whose value is read, and it declares no type: state what it returns/)
  refused(py('import os\n\ndef f(x: int) -> int:\n    return os.getpid() + x\n', {entry: ['f'], strict: true}), /os.getpid, other code/)
  refused(py('def f(x: int) -> bool:\n    if x / 3 > 1:\n        return True\n    return False\n', {entry: ['f']}), /a true division/)
  refused(py('import x\n\ndef f(k: int) -> int:\n    try:\n        raise x.Boom()\n    except KeyError:\n        return 0\n', {entry: ['f']}), /a raise of x.Boom, whose bases the reader doesn't know, inside a try whose handler names builtins.KeyError/)
  refused(py('import x\n\ndef f(k: int) -> int:\n    try:\n        x.go()\n    finally:\n        if k > 0:\n            return 1\n    return 0\n', {entry: ['f']}), /a finally that returns, raises or breaks/)
})

// Loops over a list the request carries, read as folds (any length, no pass unrolled): a continue, a raise in a pass,
// an early return; the check gives the code lists of 0 to 12 items, the rule the running values its passes compute.
const FOLD = `from dataclasses import dataclass


@dataclass
class Line:
    amount: int
    refund: bool


class Ledger:
    def __init__(self, cap: int):
        self.cap = cap
        self.spent = 0

    def charge(self, lines: list[Line]) -> bool:
        total = 0
        for line in lines:
            if line.refund:
                continue
            if line.amount < 0:
                raise ValueError("negative")
            total += line.amount
        if self.spent + total > self.cap:
            return False
        self.spent += total
        return True

    def has_big(self, xs: list[int], k: int) -> bool:
        for x in xs:
            if x > k:
                return True
        return False

    def matches(self, verbs: list[str], verb: str) -> bool:
        return any(v == "*" or v == verb for v in verbs)

    def owed(self, xs: list[int]) -> int:
        return sum(x for x in xs if x > 0) + self.spent

    def count(self, xs: list[int], ys: list[int]) -> int:
        n = 0
        for _ in xs:
            n += 1
        return n + len(ys)
`
t('a loop over a list the request carries: a fold, exact for every length', () => {
  const x = ok(py(FOLD, {entry: 'Ledger', failures: 'kept'}))
  expect(x.source).toContain('.carriesList("charge_lines", record({amount: int, refund: bool}))')
  expect(x.source).toMatch(/charge_lines\$0\.every\(\(_x, i\$\) => i\$\.lt\(charge_lines_len\)/)
  expect(step(x, 'a charge admitted keeps the spend within the cap', (b, a) => a.spent.atMost(b.cap).or(a.spent.eq(b.spent)), b => b.method.is('charge')).proven).toBe(true)
  // (a fact of the passes past the first needs induction over them, which the equations alone don't give: one line)
  expect(step(x, 'a charge of one negative line fails', (_b, a) => a.failed, b => all(b.method.is('charge'), b.charge_lines_len.eq(1), b.charge_lines.at(0).refund.not(), b.charge_lines.at(0).amount.lt(0))).proven).toBe(true)
  expect(step(x, 'has_big is false on an empty list', (_b, a) => a.has_big_result.not(), b => all(b.method.is('has_big'), b.has_big_xs_len.eq(0))).proven).toBe(true)
  expect(step(x, 'has_big of one item past k is true', (_b, a) => a.has_big_result, b => all(b.method.is('has_big'), b.has_big_xs_len.eq(1), b.has_big_xs.at(0).value.gt(b.has_big_k))).proven).toBe(true)
  expect(step(x, 'matches of one "*" is true', (_b, a) => a.matches_result, b => all(b.method.is('matches'), b.matches_verbs_len.eq(1), b.matches_verbs.at(0).value.eq('*'))).proven).toBe(true)
  expect(step(x, 'owed of no items is the spend', (b, a) => a.owed_result.eq(b.spent), b => all(b.method.is('owed'), b.owed_xs_len.eq(0))).proven).toBe(true)
  expect(step(x, 'count of no items is the other list\'s length', (_b, a) => a.count_result.eq(_b.count_ys_len), b => all(b.method.is('count'), b.count_xs_len.eq(0))).proven).toBe(true)
  expect(step(x, 'has_big is never true', (_b, a) => a.has_big_result.not(), b => b.method.is('has_big')).proven).toBe(false)
}, 60_000)

// A loop over a list of the state (an ordered collection, a map by place): the same fold, its passes the places up to
// the last, each where it holds an item.
t('a loop over a list of the state: the fold over its places', () => {
  const x = ok(py(`from dataclasses import dataclass


@dataclass
class Item:
    amount: int


class Book:
    def __init__(self):
        self.items: list[Item] = []

    def add(self, a: int) -> None:
        if a > 0:
            self.items.append(Item(amount=a))

    def drop_first(self) -> None:
        if self.items:
            self.items.pop(0)

    def total(self) -> int:
        t = 0
        for it in self.items:
            t += it.amount
        return t
`, {entry: 'Book'}))
  expect(x.source).toMatch(/items\$0\.every\(\(_x, i\$\) =>/)
  // (its passes: one past the last place, the least key a list of the state's last item is read by)
  expect(x.source).toMatch(/items\$0_len\.eq\(when\(/)
}, 60_000)

// A store's get and set inside a try that catches what they raise (a cache that may fail): each may raise, an input
// says which, the check's store raising there; and terra's two cases: a finally an outer handler's raise goes out
// through (refused), and a raise whose argument fails first (that failure is what is raised).
t('a store that may fail inside a try; a finally on a raise\'s way out; a raise\'s argument failing first', () => {
  const x = ok(py(`class Hits:
    def __init__(self, cache, limit: int):
        self.cache = cache
        self.limit = limit
        self.misses = 0

    async def hit(self, user: str) -> bool:
        try:
            n = await self.cache.async_get_cache(key=f"h:{user}") or 0
        except Exception:
            self.misses += 1
            return True
        if n >= self.limit:
            return False
        try:
            await self.cache.async_set_cache(key=f"h:{user}", value=n + 1)
        except Exception:
            pass
        return True
`, {entry: 'Hits', stores: {cache: {get: ['async_get_cache'], set: ['async_set_cache'], value: 'int'}}}))
  expect(x.source).toMatch(/async_get_cache_raises: bool/)
  expect(step(x, 'a failed read admits and counts a miss', (b, a) => a.misses.eq(b.misses.plus(1)).and(a.hit_result), b => b.async_get_cache_raises).proven).toBe(true)
  expect(step(x, 'admitted past the limit never', (b, a) => a.hit_result.not(), b => b.limit.atMost(b.cache_h.at(b.user.id).value).and(b.async_get_cache_raises.not())).proven).toBe(true)
  refused(py('class A:\n    def __init__(self):\n        self.x = 0\n\n    def f(self, n: int) -> int:\n        try:\n            try:\n                if n == 7:\n                    raise ValueError()\n            finally:\n                self.x = 1\n        except ValueError:\n            pass\n        return self.x\n', {entry: 'A'}), /finally on a raise's way out of its try/)
  const y = ok(py('class A:\n    def __init__(self):\n        self.x = 0\n        self.d: dict[str, int] = {}\n\n    def f(self, k: str) -> int:\n        try:\n            raise ValueError(self.d[k])\n        except KeyError:\n            self.x = 1\n        except ValueError:\n            self.x = 2\n        return self.x\n', {entry: 'A'}))
  expect(step(y, 'a key it doesn\'t hold is the KeyError\'s', (_b, a) => a.x.eq(1), b => b.d.at(b.k.id).has.not()).proven).toBe(true)
})

// A module function whose try returns other code's object field: where the caller reads it and it can't be answered,
// that function is cut (other code, answered by its declared bool), as it was while the try was refused.
t('a function returning other code\'s value its caller reads: cut, answered by its declared type', () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-pycase-`)
  writeFileSync(`${dir}/m.py`, 'from other import Settings\n\n\ndef _deny(s: dict[str, int]) -> bool:\n    try:\n        return Settings.model_validate(s).flag\n    except ValueError:\n        return True\n\n\ndef applied(s: dict[str, int], b: bool) -> bool:\n    return _deny(s) and b\n')
  writeFileSync(`${dir}/other.py`, 'class Settings:\n    flag: bool = False\n\n    @classmethod\n    def model_validate(cls, s) -> "Settings":\n        return cls()\n')
  const x = extractPython(`${dir}/m.py`, {entry: ['applied'], check: budget})
  if (!x.ok) throw new Error(`${JSON.stringify(x.refusals)}\n${x.notes.join('\n')}`)
  expect(x.notes.join('\n')).toMatch(/_deny/)
})

// try/except: other code called inside a try may return or raise what a handler catches (an input of the request says
// which, the check's stub raising it); the executor's own failures and the code's raises go to the handler naming their
// class or a base; else, finally and a re-raise.
const TRY = `import other


class Full(LookupError):
    pass


class Book:
    def __init__(self, cap: int):
        self.cap = cap
        self.n = 0
        self.used: dict[str, int] = {}
        self.misses = 0
        self.errors = 0

    def take(self, k: str) -> int:
        try:
            u = self.used[k]
        except KeyError:
            self.misses += 1
            return -1
        try:
            if u >= self.cap:
                raise Full("x")
            self.used[k] = u + 1
        except KeyError:
            return -2
        except LookupError:
            return -3
        else:
            self.n += 1
        finally:
            other.log(k)
        return u + 1

    def hit(self, d: int) -> int:
        self.n += 1
        try:
            other.notify(d)
            self.n += 1
            if d > 3:
                return 7
        except ValueError:
            self.n -= 1
            return 0
        except Exception:
            self.errors += 1
        return 1

    def strict(self, d: int) -> int:
        try:
            other.ping()
        except ValueError:
            raise
        return d
`
const OTHER = 'def log(k):\n    pass\ndef notify(d):\n    pass\ndef ping():\n    pass\n'
t('try/except: a call that may raise, a KeyError, a raise by its class, else and finally, a re-raise', () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-pycase-`)
  writeFileSync(`${dir}/m.py`, TRY); writeFileSync(`${dir}/other.py`, OTHER)
  const x = ok(extractPython(`${dir}/m.py`, {entry: 'Book', failures: 'kept', check: budget}))
  expect(x.source).toContain("notify_raises: oneOf('none', 'ValueError', 'Exception')")
  expect(x.notes.join('\n')).toMatch(/other.notify \(m.py:\d+:\d+\): may raise inside a try that catches it/)
  // (the raise's outcomes: each handler's)
  expect(step(x, 'a hit counts its errors only where notify raised', (b, a) => a.errors.gt(b.errors).implies(b.notify_raises.is('Exception')), b => b.method.is('hit')).proven).toBe(true)
  expect(step(x, 'a hit past 3 returns 7', (_b, a) => a.hit_result.eq(7), b => b.method.is('hit').and(b.hit_d.gt(3))).proven).toBe(false)
  expect(step(x, 'a take never past the cap', (b, a) => b.cap.atLeast(a.used.at(b.take_k.id).value).or(a.used.at(b.take_k.id).value.eq(b.used.at(b.take_k.id).value)), b => b.method.is('take')).proven).toBe(true)
  expect(step(x, 'strict fails only where ping raised', (_b, a) => a.failed.implies(_b.ping_raises), b => b.method.is('strict')).proven).toBe(true)
})

test('key templates: disjoint where their fixed parts differ', () => {
  expect(disjoint('{a:{}}:spend', '{b:{}}:spend')).toBe(true)
  expect(disjoint('x:{}:count', 'x:{}:spend')).toBe(true)
  expect(disjoint('{}', 'x:{}')).toBe(false)
  expect(disjoint('a{}', 'ab{}')).toBe(false)
})

// The adversarial round (research/langs/adversarial): no false checked proof; what reaches the rule's state, refused.
import {cases as advCases, judge, ADV} from '../research/langs/adversarial/cases.test-lib.ts'
for (const c of advCases('Python')) t(`adversarial ${c.id}: ${c.attack}`, () => judge(c, extractPython(`${ADV}${c.file}`, {...(c.discover ? {} : {entry: 'Meter'}), check: {runs: 30, depth: 6, states: 60}})))

// A record store over a Redis-like client (an idempotency layer's shape): the
// client's set by name= with nx (a conditional set, its result whether it set), JSON records whose keys are a
// constructor default's, a module's constant map, a class of the module made by its __init__ with a property,
// super().__init__(), datetime.now(), and a @contextmanager lock around a write.
const CLAIMS = `
import datetime as dt
import json
from contextlib import contextmanager
from typing import Protocol

STATUS = {"OPEN": "OPEN", "DONE": "DONE"}

class Client(Protocol):
    def get(self, name: str) -> str | None: ...
    def set(self, name: str, value: str, ex: int | None = None, nx: bool = False) -> bool | None: ...

class Base:
    def __init__(self):
        self.ttl = 60

class Record:
    def __init__(self, key: str, status: str = ""):
        self.key = key
        self._status = status

    @property
    def status(self) -> str:
        if self._status in STATUS.values():
            return self._status
        raise ValueError(self._status)

class Claims(Base):
    def __init__(self, client: Client | None = None, status_attr: str = "status"):
        self.client = client
        self.status_attr = status_attr
        super().__init__()

    @contextmanager
    def _lock(self, name: str):
        if self.client.set(name=f"{name}:lock", value="1", nx=True):
            yield
        else:
            raise KeyError(name)

    def claim(self, key: str) -> bool:
        rec = Record(key, STATUS["OPEN"])
        item = {self.status_attr: rec.status, "until": int(dt.datetime.now().timestamp()) + self.ttl}
        if self.client.set(name=key, value=json.dumps(item), ex=self.ttl, nx=True):
            return True
        raw = self.client.get(key)
        if raw is None:
            return False
        if json.loads(raw)[self.status_attr] == STATUS["DONE"]:
            return False
        with self._lock(key):
            self.client.set(name=key, value=json.dumps(item), ex=self.ttl)
        return True

    def finish(self, key: str) -> None:
        self.client.set(name=key, value=json.dumps({self.status_attr: STATUS["DONE"], "until": 0}))
`
const claims = (o: Partial<PyOptions> = {}) => py(CLAIMS, {entry: 'Claims', methods: ['claim', 'finish'], failures: 'kept', defaults: ['status_attr'],
  stores: {client: {get: ['get'], set: ['set'], apart: true, values: {'{}': {json: {status: ['OPEN', 'DONE'], until: 'int'}}, '{}:lock': ['1']}}}, ...o})
t('a store of JSON records over a client of name= and nx: the conditional set, the lock by @contextmanager, a record made by its class', () => {
  const x = ok(claims())
  expect(x.notes.join('\n')).toMatch(/a @contextmanager generator, run around the with's body/)
  expect(x.notes.join('\n')).toMatch(/Record\(\.\.\.\) .*made by its __init__, read/)
  expect(x.notes.join('\n')).toMatch(/its ex \(the key's expiry\) left out/)
  // a claim never takes a key over from a DONE record; it takes one over only by the lock (a second lock refused)
  expect(step(x, 'a DONE record stays DONE through a claim', (_b, a) => a['client_'].at(_b.claim_key.id).status.is('DONE'),
    b => b.method.is('claim').and(b['client_'].at(b.claim_key.id).has).and(b['client_'].at(b.claim_key.id).status.is('DONE'))).proven).toBe(true)
  expect(step(x, 'a claim of a held OPEN record whose lock is held fails', (_b, a) => a.failed,
    b => b.method.is('claim').and(b['client_'].at(b.claim_key.id).has).and(b['client_'].at(b.claim_key.id).status.is('OPEN')).and(b.client_lock.at(b.claim_key.id).has)).proven).toBe(true)
  // the nx set read as conditional: a claim of a free key is the one that writes it
  expect(step(x, 'a claim always writes the record (refuted: a DONE one is kept)', (_b, a) => a['client_'].at(_b.claim_key.id).status.is('OPEN'), b => b.method.is('claim')).proven).toBe(false)
})
t('a store key template that may name another\'s is refused unless stated apart', () => {
  refused(claims({stores: {client: {get: ['get'], set: ['set'], values: {'{}': {json: {status: ['OPEN', 'DONE'], until: 'int'}}, '{}:lock': ['1']}}}}), /the key templates "\{\}" and "\{\}:lock" may name one key/)
})

// What a scheduler's rules hit (supercomputer's rules.py and scheduler.py, read as they ship): sets, type aliases,
// Literal results, an int param beside a choice, an untyped dict given to the constructor, a dict of other code's
// objects, another module's constants, bytes.
const FATE = `
from typing import Literal

Fate = Literal["queued", "placed", "done", "modal"]
Strike = Literal["again", "modal", "none"]


class ItemFate:
    def __init__(self, boat_tries: int):
        self.boat_tries = boat_tries
        self.state: Fate = "queued"
        self.fails = 0
        self.vm = ""
        self.avoid: set[str] = set()

    def place(self, vm: str, another: bool) -> bool:
        if self.state != "queued" or (vm in self.avoid and another):
            return False
        self.state = "placed"
        self.vm = vm
        return True

    def boat_failed(self, vm: str) -> Strike:
        if self.state != "placed" or self.vm != vm:
            return "none"
        self.state = "queued"
        if vm in self.avoid:
            return "none"
        self.avoid.add(vm)
        return self._strike()

    def waited(self, start_failed: bool) -> Strike:
        if self.state != "queued" or not start_failed:
            return "none"
        return self._strike()

    def forgive(self, vm: str) -> None:
        self.avoid.discard(vm)

    def _strike(self) -> Strike:
        self.fails += 1
        if self.fails < self.boat_tries:
            self.state = "queued"
            return "again"
        self.state = "modal"
        return "modal"
`
t('a set of the state (add, discard, in), a Literal alias, a Literal result, an int param beside a choice', () => {
  const x = ok(py(FATE, {entry: 'ItemFate', check: budget}))
  expect(x.source).toContain("state: oneOf('queued', 'placed', 'done', 'modal')")
  expect(x.source).toContain("boat_failed_result: oneOf('again', 'modal', 'none')")
  expect(x.source).not.toContain('undefined')
  expect(proveRule(x.rule!, [...x.invariants ?? [], x.rule!.law('Modal only after boat_tries strikes', ({state, fails, boat_tries}: A) => state.is('modal').implies(boat_tries.atMost(fails)))]).proven).toBe(true)
  // a strike only for a VM the item hadn't failed on: the set before the step
  expect(step(x, 'one strike per VM', (b, a) => a.fails.gt(b.fails).implies(b.avoid.at(b.boat_failed_vm.id).has.not()), b => b.method.is('boat_failed')).proven).toBe(true)
  expect(step(x, 'a VM failed on is avoided after', (b, a) => a.avoid.at(b.boat_failed_vm.id).has.or(b.state.is('placed').not()).or(b.vm.eq(b.boat_failed_vm).not()), b => b.method.is('boat_failed')).proven).toBe(true)
})

t('a set removed from: a key it doesn\'t hold is a KeyError, the step\'s failure', () => {
  const x = ok(py(`class Seen:\n    def __init__(self):\n        self.ids: set[str] = set()\n\n    def add(self, i: str) -> None:\n        self.ids.add(i)\n\n    def drop(self, i: str) -> None:\n        self.ids.remove(i)\n`,
    {entry: 'Seen', failures: 'kept', check: budget}))
  expect(step(x, 'a drop of an id not held fails', (_b, a) => a.failed, b => b.method.is('drop').and(b.ids.at(b.drop_i.id).has.not())).proven).toBe(true)
  expect(step(x, 'a drop of a held id leaves it out', (b, a) => a.failed.not().and(a.ids.at(b.drop_i.id).has.not()), b => b.method.is('drop').and(b.ids.at(b.drop_i.id).has)).proven).toBe(true)
})

t('a type alias of 3.12 (type X = ...), and dict() as {}', () => {
  const x = ok(py(`from typing import Literal\n\ntype Mode = Literal["on", "off"]\n\nclass Switch:\n    def __init__(self):\n        self.mode: Mode = "off"\n        self.n: dict[str, int] = dict()\n\n    def flip(self, k: str) -> None:\n        self.mode = "on" if self.mode == "off" else "off"\n        self.n[k] = self.n.get(k, 0) + 1\n`,
    {entry: 'Switch', check: budget}))
  expect(x.source).toContain("mode: oneOf('on', 'off')")
})

t('a constructor given a dict of no stated types, read nowhere the rule keeps; a dict of other code\'s objects left out', () => {
  const x = ok(py(`import threading\n\nclass Gate:\n    def __init__(self, msg: dict, cap: int):\n        self.msg = msg\n        self.cap = cap\n        self.n = 0\n        self.events: dict[str, threading.Event] = {}\n\n    def hit(self) -> bool:\n        if self.n >= self.cap:\n            return False\n        self.n += 1\n        return True\n`,
    {entry: 'Gate', check: budget}))
  expect(x.notes.join('\n')).toMatch(/Gate\(msg\): dict with no key and value types, read nowhere the rule keeps/)
  expect(proveRule(x.rule!, [x.rule!.law('within the cap', ({n, cap}: A) => cap.atLeast(n).or(n.eq(0)))]).proven).toBe(true)
  // (read by the constructor: refused, whether it holds the key is the dict's)
  refused(py(`class Gate:\n    def __init__(self, msg: dict):\n        self.cap = int(msg["cap"])\n        self.n = 0\n\n    def hit(self) -> None:\n        self.n += 1\n`, {entry: 'Gate', check: budget}), /msg\['cap'\]: an item of msg: dict with no key and value types/)
})

t('another module\'s constant read as its value; bytes never equal to a str', () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-pycase-`)
  writeFileSync(`${dir}/conf.py`, 'LIMIT = 3\n')
  writeFileSync(`${dir}/m.py`, `import conf\n\nclass Box:\n    def __init__(self):\n        self.n = 0\n\n    def put(self, body: bytes, tag: bytes | None) -> bool:\n        if self.n >= conf.LIMIT or body == "x" or (tag is not None and tag == body):\n            return False\n        self.n += 1\n        return True\n`)
  const x = ok(extractPython(`${dir}/m.py`, {entry: 'Box', check: budget}))
  expect(proveRule(x.rule!, [x.rule!.law('at most conf.LIMIT', ({n}: A) => n.atMost(3))]).proven).toBe(true)
  // (body == "x" is never true: bytes and a str differ in Python)
  expect(step(x, 'a body other than its tag is always put below the limit', (_b, a) => a.put_result, b => b.n.lt(3).and(b.tag_none)).proven).toBe(true)
})

t('a str result that is one of its literals on every path: a choice of them', () => {
  const x = ok(py(`class Life:\n    def __init__(self):\n        self.up = True\n        self.owned = False\n\n    def tick(self, work: bool) -> str:\n        if not self.up or self.owned:\n            return "keep"\n        if work:\n            self.owned = True\n            return "adopt"\n        self.up = False\n        return "stop"\n`,
    {entry: 'Life', check: budget}))
  expect(x.source).toContain("tick_result: oneOf('keep', 'adopt', 'stop')")
  expect(step(x, 'a VM stopped only with no work', (b, a) => a.tick_result.is('stop').implies(b.work.not()), () => yes).proven).toBe(true)
})

t('an argument the code ignores, kept where a law reads it (keep): the law about it broken', () => {
  const code = `class Fate:\n    def __init__(self):\n        self.fails = 0\n\n    def waited(self, start_failed: bool) -> None:\n        self.fails += 1\n`
  const bare = ok(py(code, {entry: 'Fate', check: budget}))
  expect(bare.model!.inputs.map(v => v.name)).not.toContain('start_failed')
  const x = ok(py(code, {entry: 'Fate', keep: ['start_failed'], check: budget}))
  expect(step(x, 'a wait counts only where a start failed', (b, a) => a.fails.gt(b.fails).implies(b.start_failed), () => yes).proven).toBe(false)
})

// The clock pinned only while the code runs, and never in what a module imported then copies: a framework's module
// first imported by a call (FastAPI's routes, pydantic's models) that reads the types the code's modules hold sees the
// real datetime (it raised `_Now | None is not a valid Pydantic field type` on LiteLLM's auth checks).
t('the clock pinned only in the code\'s run: a module a call first imports reads the real datetime', () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-pyclock-`)
  writeFileSync(`${dir}/win.py`, `import datetime as dt


class Window:
    def __init__(self, limit: int):
        self.limit = limit
        self.start = 0
        self.count = 0

    def hit(self) -> bool:
        from views import record
        now = int(dt.datetime.now().timestamp())
        if now - self.start >= 60:
            self.start = now
            self.count = 0
        if self.count >= self.limit:
            return False
        self.count += 1
        record()
        return True
`)
  writeFileSync(`${dir}/views.py`, `import datetime
from win import *

if dt is not datetime or dt.datetime is not datetime.datetime:
    raise TypeError(f"{dt.datetime!r} is not a valid field type")


def record():
    pass
`)
  const x = ok(extractPython(`${dir}/win.py`, {entry: 'Window', check: budget}))
  expect(step(x, 'a hit counts at most one', (b, a) => a.count.atMost(b.count.plus(1)), () => yes).proven).toBe(true)
})

// A constructor argument typed by a Protocol (or by nothing) is an injected dependency, kept in a field however the
// constructor assigns it (one place of a tuple's too): its methods' declared results answered by the request.
t('a Protocol-typed constructor argument, assigned in a tuple: an injected dependency whose calls are answered', () => {
  const code = (ret: string) => `from typing import Protocol


class Pricing(Protocol):
    def cost(self, model: str)${ret}: ...


class Limiter:
    def __init__(self, limit: int, pricing: Pricing):
        self.limit, self.used, self.pricing = limit, 0, pricing

    def hit(self, model: str) -> bool:
        cost = self.pricing.cost(model)
        if cost <= 0 or self.used + cost > self.limit:
            return False
        self.used += cost
        return True
`
  const x = ok(py(code(' -> int'), {entry: 'Limiter', check: budget}))
  expect(x.notes.join('\n')).toMatch(/Limiter\(pricing\): an injected dependency \(inferred: of Pricing/)
  expect(x.notes.join('\n')).toMatch(/pricing\.cost .*answered by the request \(inferred/)
  expect(step(x, 'a counted hit stays within the limit', (_b, a) => a.used.atMost(a.limit_ ?? a.limit), b => b.used.atMost(b.limit_ ?? b.limit)).proven).toBe(true)
  // (its result declared nowhere: refused saying what states it, and the answer stated reads it)
  refused(py(code(''), {entry: 'Limiter', check: budget}), /state what it returns \(answers: \{"cost": 'int'\}/)
  ok(py(code(''), {entry: 'Limiter', answers: {cost: 'int'}, check: budget}))
})

// A store's get and set given options of a constant (a tracing span of None, which tier to use): the store read as one
// map whatever they say, noted (LiteLLM's limiters, refused since 0.33); an option the request decides is refused.
t('a store\'s options given a constant read as one map, noted; one the request decides refused', () => {
  const code = (opt: string) => `class Cache:
    async def async_get_cache(self, key, span=None, local_only=False): ...
    async def async_set_cache(self, key, value, ttl=None, span=None, local_only=False): ...


class Hits:
    def __init__(self, cache: Cache, limit: int):
        self.cache = cache
        self.limit = limit

    async def hit(self, session: str, fast: bool) -> bool:
        key = f"hits:{session}"
        n = await self.cache.async_get_cache(key=key, span=None, local_only=${opt})
        n = (n or 0) + 1
        await self.cache.async_set_cache(key=key, value=n, ttl=60, span=None, local_only=${opt})
        return n <= self.limit
`
  const x = ok(py(code('True'), {entry: 'Hits', stores: {cache: {}}, check: budget}))
  expect(x.notes.join('\n')).toMatch(/cache\.async_get_cache: its local_only \(true\) left out: the store read as one map whatever it says/)
  expect(x.notes.join('\n')).toMatch(/cache\.async_get_cache: its span \(None\) left out/)
  refused(py(code('fast'), {entry: 'Hits', stores: {cache: {}}, check: budget}), /given local_only, a value the request decides/)
})

// The reader fuzz's misreads (core/extract-fuzz.ts), each refused where it is or read as the code runs.
t('a name nothing binds, an attribute Python\'s library lacks, the module object\'s own method: refused (they raise where they run)', () => {
  const c = (line: string, head = 'import logging\n') => `${head}\nclass C:\n    def __init__(self):\n        self.n = 0\n\n    def bump(self) -> None:\n        ${line}\n        self.n += 1\n`
  refused(py(c('logging.getLogger("c").info(self)  # gdp: skip', ''), {entry: 'C'}), /logging: a name the module doesn't define, import or bind \(a NameError where it runs\)/)
  refused(py(c('logging.getLogger("c").info(selfdef)'), {entry: 'C'}), /selfdef: a name the module doesn't define/)
  refused(py(c('logging.getLo'), {entry: 'C'}), /logging.getLo: logging has no getLo \(an AttributeError where it runs\)/)
  refused(py(c('logging.getLo: skip', ''), {entry: 'C'}), /logging: a name the module doesn't define/)
  refused(py(c('logging.__init__("c").info(self)  # gdp: skip'), {entry: 'C'}), /logging.__init__: the module object's own method/)
  refused(py('def spend_of(key: str) -> float:\n    raise RuntimeError("not here")\n\ndef gate(key: str) -> None:\n    used = spend_of(here)\n', {entry: ['gate'], failures: 'kept', answers: {spend_of: 'float'}}), /here: a name the module doesn't define/)
  refused(py('def f(x: int) -> int:\n    retu\n', {entry: ['f']}), /retu: a name the module doesn't define/)
  // (a parameter of another function is no name here)
  refused(py('def g(key: str) -> int:\n    return 0\n\ndef f(k: str) -> int:\n    return g(key)\n', {entry: ['f']}), /key: a name the module doesn't define/)
  refused(py('class Seen:\n    def __init__(self):\n        self.ids: set[str] = remove()\n\n    def add(self, i: str) -> None:\n        self.ids.add(i)\n', {entry: 'Seen'}), /remove: a name the module doesn't define/)
})

t('a module variable a function rebinds (global) is no constant: refused where it is read', () => {
  refused(py('value = 0\ndef bump() -> None:\n    global value\n    value = 1\nclass Meter:\n    def __init__(self):\n        self.n = 0\n    def tick(self) -> None:\n        bump()\n        self.n = value\n', {entry: 'Meter'}),
    /value: a module variable a function rebinds \(global value\)/)
})

t('an injected dependency\'s call left out inside a try: the check\'s dependency raises where the request says', () => {
  const x = ok(py('from typing import Protocol\nclass Source(Protocol):\n    def check(self) -> bool: ...\nclass Meter:\n    def __init__(self, source: Source):\n        self.source = source\n        self.n = 2\n    def tick(self) -> None:\n        try:\n            self.source.check()\n        except ValueError:\n            self.n = 1\n', {entry: 'Meter', check: budget}))
  expect(x.source).toContain('when(check_raises, 1, n)')
})

t('a key of the other kind than its dict\'s (a str into a dict[int, int]): refused, never one it holds', () => {
  refused(py('class A:\n    def __init__(self):\n        self.d: dict[int, int] = {}\n\n    def f(self, k: str) -> int:\n        return self.d.get(k, 0)\n', {entry: 'A'}), /a string key of a map keyed by numbers/)
})
