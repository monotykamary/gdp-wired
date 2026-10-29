// The Rust front end (core/extract-rs.ts on core/extract-step.ts): rules read from Rust, each checked against the crate
// it was read from (built by cargo beside a generated harness, overflow checks on). The cases: a u8 that traps past
// its range, a wrapping and a checked one, an Option field, a Result's Err as the failure, a C-like enum and its
// discriminant, an atomic's fetch_add, and the refusals (a loop, a map in the state). Skipped where cargo isn't
// installed (research/langs/rust/rust-setup.sh installs it in a job).
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {extractRust} from './extract-rs.ts'
import {proveRule, proveSteps} from './dsl.ts'

const hasCargo = (() => { try { execFileSync('cargo', ['--version'], {stdio: 'ignore'}); return true } catch { return false } })()
const t = hasCargo ? test : test.skip
const DIR = new URL('./rs/examples/limits', import.meta.url).pathname
const budget = {runs: 40, depth: 8, states: 80}
type X = ReturnType<typeof extractRust>
const ok = (x: X) => {
  if (!x.ok) throw new Error(`refused: ${JSON.stringify(x.refusals)}\n${x.source ?? ''}\n${JSON.stringify(x.evidence)}`)
  expect(x.evidence!.requests).toBeGreaterThan(0)
  return x
}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type A = any
const step = (x: X, name: string, then: (b: A, a: A) => A, when?: (b: A) => A) => proveSteps(x.rule as A, x.invariants ?? [], [(x.rule as A).stepLaw(name, then, when)])

t('integers of a width: + traps past it (the failure), wrapping_add wraps, checked_add is an Option', () => {
  const x = ok(extractRust(DIR, {entry: 'Budget', methods: ['spend', 'lap', 'try_spend', 'mark'], failures: 'kept', check: budget}))
  expect(x.notes.join('\n')).toMatch(/past u8's range \(a panic/)
  expect(proveRule(x.rule!, [...x.invariants!, x.rule!.law('spent within the limit', ({spent, limit}: A) => spent.atMost(limit))]).proven).toBe(true)
  expect(step(x, 'a lap wraps at 256', (b, a) => a.laps.eq(0), b => b.method.is('lap').and(b.laps.eq(255))).proven).toBe(true)
  expect(step(x, 'mark keeps the phase', (b, a) => a.phase.eq(b.mark_p).and(a.phase_none.not()), b => b.method.is('mark')).proven).toBe(true)
}, 120_000)

t('a C-like enum, its discriminant, an Err returned, an atomic counter', () => {
  const x = ok(extractRust(DIR, {entry: 'Job', methods: ['start', 'finish'], failures: 'kept', check: budget}))
  expect(x.source).toContain("phase: oneOf('Idle', 'Running', 'Done')")
  expect(step(x, 'finish only from running', (b, a) => a.failed.not().implies(b.phase.is('Running').and(a.finish_result.eq(2))), b => b.method.is('finish')).proven).toBe(true)
  expect(step(x, 'a start counts one', (b, a) => a.start_result.implies(a.hits.eq(b.hits.plus(1))), b => b.method.is('start').and(b.hits.lt(1000))).proven).toBe(true)
}, 120_000)

t('refusals, each where it is with why', () => {
  const loop = extractRust(DIR, {entry: 'Tally', methods: ['add_all']})
  expect(loop.ok).toBe(false)
  expect(loop.refusals[0]!.what).toMatch(/a loop/)
  const map = extractRust(DIR, {entry: 'Ledger', methods: []})
  expect(map.ok).toBe(false)
}, 120_000)
