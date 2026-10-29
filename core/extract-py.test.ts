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
import {disjoint} from './extract-step.ts'

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

t('refusals, each where it is with why', () => {
  refused(extractPython(EX, {entry: ['drain'], check: budget}), /bucket.py:\d+:\d+: a loop/)
  refused(py('def f(x: int) -> int:\n    return x * 0.5\n', {entry: ['f']}), /a float that isn't whole/)
  refused(py('import os\n\ndef f(x: int) -> int:\n    return os.getpid() + x\n', {entry: ['f']}), /os.getpid, other code/)
  refused(py('def f(x: int) -> float:\n    return x / 3\n', {entry: ['f']}), /a true division/)
  refused(py('def f(d: dict[str, int]) -> int:\n    try:\n        return d["a"]\n    except KeyError:\n        return 0\n', {entry: ['f']}), /try\/except/)
})

test('key templates: disjoint where their fixed parts differ', () => {
  expect(disjoint('{a:{}}:spend', '{b:{}}:spend')).toBe(true)
  expect(disjoint('x:{}:count', 'x:{}:spend')).toBe(true)
  expect(disjoint('{}', 'x:{}')).toBe(false)
  expect(disjoint('a{}', 'ab{}')).toBe(false)
})
