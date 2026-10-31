// The Python front end (core/extract-py.ts on core/extract-step.ts): rules read from Python, each checked against the
// Python code it was read from (core/py/harness.py runs it). The cases: a class with a clock and a lock, a dict of
// dataclasses, a decision whose failure is kept, a store the caller states, the boundary (answers, skip), and the
// refusals (a loop, a float that isn't whole, other code). Skipped where python3 isn't installed.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {type PyOptions, extractPython} from './extract-py.ts'
import {proveRule, proveSteps} from './dsl.ts'
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
  refused(py('def f(d: dict[str, int]) -> int:\n    try:\n        return d["a"]\n    except KeyError:\n        return 0\n', {entry: ['f']}), /try\/except/)
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
