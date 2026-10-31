// The Python front end (core/extract-py.ts on core/extract-step.ts): rules read from Python, each checked against the
// Python code it was read from (core/py/harness.py runs it). The cases: a class with a clock and a lock, a dict of
// dataclasses, a decision whose failure is kept, a store the caller states, the boundary (answers, skip), and the
// refusals (a loop, a float that isn't whole, other code). Skipped where python3 isn't installed.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {type PyOptions, extractPython} from './extract-py.ts'
import {all, proveRule, proveSteps} from './dsl.ts'
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
  expect(x.source).toContain('.carriesList("charge_lines", record({refund: bool, amount: int}))')
  expect(x.source).toMatch(/charge_lines\.every\(\(_x, i\$\) =>/)
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
  expect(step(x, 'the total of no items is 0', (_b, a) => a.total_result.eq(0), b => all(b.method.is('total'), b.items_least1$some.not())).proven).toBe(true)
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
