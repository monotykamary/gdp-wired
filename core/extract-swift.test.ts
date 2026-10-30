// The Swift front end (core/extract-swift.ts on core/extract-step.ts): rules read from Swift, each checked against the
// package it was read from (built by `swift build` beside a generated harness, in debug: overflow traps and assert on).
// The cases: a UInt8 that traps past its range and one that wraps (&+), an Optional, an enum's raw value, a throw and a
// precondition; injected protocols (a store by a key, an answer over a declared result) with the entry inferred; an
// actor; the refusals; the adversarial round's Swift shapes. Skipped where swift isn't installed
// (research/langs/swift/modal_swift.py runs them in the official Linux image).
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {extractSwift} from './extract-swift.ts'
import {proveRule, proveSteps} from './dsl.ts'
import {ADV, cases as advCases, judge} from '../research/langs/adversarial/cases.test-lib.ts'

const hasSwift = (() => { try { execFileSync(process.env.GDP_SWIFT ?? 'swift', ['--version'], {stdio: 'ignore'}); return true } catch { return false } })()
const t = hasSwift ? test : test.skip
const DIR = new URL('./swift/examples/limits/Sources/Limits/', import.meta.url).pathname
const budget = {runs: 30, depth: 6, states: 60}
type X = ReturnType<typeof extractSwift>
const ok = (x: X) => {
  if (!x.ok) throw new Error(`refused: ${JSON.stringify(x.refusals)}\n${x.source ?? ''}\n${JSON.stringify(x.evidence)}`)
  expect(x.evidence!.requests).toBeGreaterThan(0)
  return x
}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type A = any
const step = (x: X, name: string, then: (b: A, a: A) => A, when?: (b: A) => A) => proveSteps(x.rule as A, x.invariants ?? [], [(x.rule as A).stepLaw(name, then, when)])

t('a struct: + traps past UInt8 (a crash, the failure), &+ wraps, an Optional set, an enum\'s raw value, a throw', () => {
  const x = ok(extractSwift(`${DIR}Budget.swift`, {entry: 'Budget', methods: ['spend', 'lap', 'setMark', 'advance'], failures: 'kept', check: budget}))
  expect(x.source).toContain("phase: oneOf('idle', 'running', 'done')")
  expect(proveRule(x.rule!, [...(x.invariants ?? []), x.rule!.law('spent within the limit', ({spent, limit}: A) => spent.atMost(limit))]).proven).toBe(true)
  expect(step(x, 'a lap wraps at 256', (_b, a) => a.laps.eq(0), b => b.method.is('lap').and(b.laps.eq(255))).proven).toBe(true)
  expect(step(x, 'spend past 255 fails', (_b, a) => a.failed, b => b.method.is('spend').and(b.spent.eq(200)).and(b.spend_n.eq(100))).proven).toBe(true)
  expect(step(x, 'advance from done fails', (_b, a) => a.failed, b => b.method.is('advance').and(b.phase.is('done'))).proven).toBe(true)
  expect(step(x, 'advance returns the raw value', (_b, a) => a.failed.not().implies(a.advance_result.eq(1).or(a.advance_result.eq(2))), b => b.method.is('advance')).proven).toBe(true)
}, 900_000)

t('the boundary inferred: an injected store by its keys, an answer over a protocol\'s declared result, the entry', () => {
  const x = ok(extractSwift(`${DIR}Limiter.swift`, {check: budget}))
  const notes = x.notes.join('\n')
  expect(notes).toMatch(/the entry inferred: Limiter/)
  expect(notes).toMatch(/Limiter\(counter\): an injected dependency/)
  expect(notes).toMatch(/flags\.limit .*answered by the request \(inferred/)
  expect(notes).toMatch(/counter: a store \(inferred: an injected dependency, read and written by a key\): "hits:{}" keys/)
  expect(step(x, 'an allowed hit keeps the user within the limit', (b, a) => a.allow_result.implies(b.limit.atLeast(a.counter_hits.at(b.user).value))).proven).toBe(true)
  expect(step(x, 'a denial counts nothing', (b, a) => a.allow_result.not().implies(a.counter_hits.at(b.user).value.eq(b.counter_hits.at(b.user).value))).proven).toBe(true)
  expect(step(x, 'a denied user is counted', (b, a) => a.allow_result.not().implies(a.denied.at(b.user).value.atLeast(1))).proven).toBe(true)
}, 900_000)

t('an actor: its methods each one step', () => {
  const x = ok(extractSwift(`${DIR}Tally.swift`, {entry: 'Tally', check: budget}))
  expect(x.notes.join('\n')).toMatch(/an actor, its methods each one step/)
  expect(proveRule(x.rule!, [...(x.invariants ?? []), x.rule!.law('n within the cap', ({n, cap}: A) => n.atMost(cap))]).proven).toBe(false)
  const y = ok(extractSwift(`${DIR}Tally.swift`, {entry: 'Tally', methods: ['add'], check: budget}))
  expect(step(y, 'an add keeps n within the cap', (_b, a) => a.n.atMost(a.cap), b => b.n.atMost(b.cap)).proven).toBe(true)
}, 900_000)

t('refusals, each where it is with why', () => {
  const loop = extractSwift(`${DIR}Loop.swift`, {entry: 'Loop'})
  expect(loop.ok).toBe(false)
  expect(loop.refusals[0]!.what).toMatch(/a loop/)
}, 900_000)

// The adversarial round (research/langs/adversarial): what reaches the rule's state through an injected protocol,
// refused; two of one protocol, refused; no false checked proof.
for (const c of advCases('Swift')) t(`adversarial ${c.id}: ${c.attack}`, () => judge(c, extractSwift(`${ADV}${c.file}`, {entry: 'Meter', check: budget})), 900_000)
