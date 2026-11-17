// The Swift front end (core/extract-swift.ts on core/extract-step.ts): rules read from Swift, each checked against the
// package it was read from (built by `swift build` beside a generated harness, in debug: overflow traps and assert on).
// The cases: a UInt8 that traps past its range and one that wraps (&+), an Optional, an enum's raw value, a throw and a
// precondition; injected protocols (a store by a key, an answer over a declared result) with the entry inferred; an
// actor; the refusals; the adversarial round's Swift shapes. Skipped where swift isn't installed
// (research/langs/swift/modal_swift.py runs them with Swift 6.3.3 on boat, or in the official Linux image).
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {extractSwift} from './extract-swift.ts'
import {proveRule, proveSteps} from './dsl.ts'
import {buildLaw} from './laws.ts'
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

// Independent scalar positive, false-native-lowering and disabled controls;
// the original callback claims above remain untouched and separately blocked.
t('Swift native scalar arguments have tamper and disabled controls', () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-sw-native-`), file = `${dir}/Meter.swift`
  writeFileSync(file, `struct Meter {
    var value: UInt8 = 0
    init() {}
    mutating func set(_ n: UInt8) { value = n }
  }`)
  const read = (disabled: boolean) => {
    const x = extractSwift(file, {entry: 'Meter', check: disabled ? {runs: 0, states: 0, probes: false} : budget})
    if (!disabled) return ok(x)
    expect(x.ok).toBe(true)
    expect(x.evidence?.requests ?? 0).toBe(0)
    return x
  }
  const law = (x: X, expr: string) => {
    const b = buildLaw(x, {name: 'set exact', expr, method: 'set'})
    if (b.kind !== 'step') throw new Error('expected a step law')
    return b.law
  }
  const x = read(false)
  const v = proveSteps(x.rule!, x.invariants ?? [], [law(x, 'value == n')], {search: false})
  expect(v).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  expect(v.translationChecks).toBeGreaterThan(0)
  const wrong = law(x, 'value != n')
  wrong.then = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const rejected = proveSteps(x.rule!, x.invariants ?? [], [wrong], {search: false})
  expect(rejected).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'error'})
  expect(rejected.translationWitness?.bindings).toHaveProperty('n')
  const disabled = read(true)
  expect(proveSteps(disabled.rule!, disabled.invariants ?? [], [law(disabled, 'value == n')], {search: false})).toMatchObject({proven: false, checked: false, translation: 'unchecked'})
}, 900_000)

t('initializer alternatives retain separate original-code replays', () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-swinit-`), file = `${dir}/Meter.swift`
  writeFileSync(file, `struct Meter {
    var n: Int
    init() { n = 7 }
    init(seed: Int) { n = seed }
    mutating func tick() { n = n &+ 1 }
  }`)
  const choice = extractSwift(file, {entry: 'Meter', check: budget})
  expect(choice.ok).toBe(false)
  expect(choice.initializers?.selectors.sort()).toEqual(['()', '(seed: Int)'].sort())
  for (const ctor of choice.initializers!.selectors) {
    const x = ok(extractSwift(file, {entry: 'Meter', ctor, check: budget}))
    expect(x.evidence!.mismatch).toBeUndefined()
  }
}, 900_000)

t('typed same-label initializer delegation is resolved by signature', () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-swinit-`), file = `${dir}/Meter.swift`
  writeFileSync(file, `struct Meter {
    var n: Int
    init() { self.init(seed: Int32(3)) }
    init(first: Int32, second: Bool) { self.init(seed: first) }
    init(seed: Int) { n = seed }
    init(seed: Int32) { n = Int(seed) + 1 }
    mutating func tick() { n = n &+ 1 }
  }`)
  for (const ctor of ['()', '(first: Int32, second: Bool)']) {
    const x = ok(extractSwift(file, {entry: 'Meter', ctor, check: budget}))
    expect(x.evidence!.mismatch).toBeUndefined()
  }
}, 900_000)

t('context-dependent literal initializer overloads remain refused', () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-swinit-`), file = `${dir}/Meter.swift`
  writeFileSync(file, `struct Meter {
    var n: Int
    init() { self.init(seed: 3) }
    init(seed: Int) { n = seed }
    init(seed: Int32) { n = Int(seed) + 1 }
    mutating func tick() { n = n &+ 1 }
  }`)
  const x = extractSwift(file, {entry: 'Meter', ctor: '()', check: budget})
  expect(x.ok).toBe(false)
  expect(x.refusals.map(r => r.what).join('; ')).toContain('ambiguous parameter labels')
}, 900_000)

t('failable initializers are not omitted or replaced by a memberwise initializer', () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-swinit-`), file = `${dir}/Meter.swift`
  writeFileSync(file, `struct Meter {
    var n: Int
    init?(valid: Bool) { if !valid { return nil }; n = 0 }
    mutating func tick() { n = n &+ 1 }
  }`)
  const x = extractSwift(file, {entry: 'Meter', check: budget})
  expect(x.ok).toBe(false)
  expect(x.refusals.map(r => r.what).join('; ')).toContain('failable initializer')
}, 900_000)

t('an actor: its methods each one step', () => {
  const x = ok(extractSwift(`${DIR}Tally.swift`, {entry: 'Tally', check: budget}))
  expect(x.notes.join('\n')).toMatch(/an actor, its methods each one step/)
  expect(proveRule(x.rule!, [...(x.invariants ?? []), x.rule!.law('n within the cap', ({n, cap}: A) => n.atMost(cap))]).proven).toBe(false)
  const y = ok(extractSwift(`${DIR}Tally.swift`, {entry: 'Tally', methods: ['add'], check: budget}))
  expect(step(y, 'an add keeps n within the cap', (_b, a) => a.n.atMost(a.cap), b => b.n.atMost(b.cap)).proven).toBe(true)
  // Keep the original positive until crash-observation support is established;
  // this registered companion is the same guarded claim, not a scalar smoke test.
  const add = buildLaw(y, {name: 'an add keeps n within the cap (native)', expr: 'old(n) <= old(cap) implies n <= cap', method: 'add'})
  const v = proveSteps(y.rule!, y.invariants ?? [], [add.law])
  expect(v).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  expect(v.translationChecks).toBeGreaterThan(0)
}, 900_000)

t('refusals, each where it is with why', () => {
  const loop = extractSwift(`${DIR}Loop.swift`, {entry: 'Loop'})
  expect(loop.ok).toBe(false)
  expect(loop.refusals[0]!.what).toMatch(/a loop/)
}, 900_000)

// The adversarial round (research/langs/adversarial): what reaches the rule's state through an injected protocol,
// refused; two of one protocol, refused; no false checked proof.
for (const c of advCases('Swift')) t(`adversarial ${c.id}: ${c.attack}`, () => judge(c, extractSwift(`${ADV}${c.file}`, {entry: 'Meter', check: budget})), 900_000)

// The reader fuzz's misreads (core/extract-fuzz.ts): a constructor argument of a protocol nothing reads, given a fake.
t('an injected protocol nothing the rule keeps reads: the check gives a fake that does nothing', () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-swcase-`)
  writeFileSync(`${dir}/Meter.swift`, 'protocol Store {\n  func get(_ key: String) -> Int?\n  func set(_ key: String, value: Int)\n}\nfinal class Meter {\n  let a: Store\n  let b: Store\n  var n = 0\n  init(a: Store, b: Store) { self.a = a; self.b = b }\n  func tick() {\n    n = b.get("k") ?? 0\n  }\n}\n')
  ok(extractSwift(`${dir}/Meter.swift`, {entry: 'Meter', check: budget}))
}, 900_000)

// The check's build (the code with the harness): a compiler failing with nothing to say of the code (killed, past
// GDP_COMPILE_S) is retried once, then the check's harness failure; its errors about the code, the source refused with
// its message. Never "the rule and the code differ".
const killedBuild = <X>(make: () => X): X => { const old = process.env.GDP_COMPILE_S; process.env.GDP_COMPILE_S = '0.001'; try { return make() } finally { if (old === undefined) delete process.env.GDP_COMPILE_S; else process.env.GDP_COMPILE_S = old } }
t('the check\'s build: a package swiftc rejects refused with its message; swift build killed is the harness\'s failure, retried once', () => {
  const file = (code: string) => { const d = mkdtempSync(`${tmpdir()}/gdp-swcase-`); writeFileSync(`${d}/Meter.swift`, code); return `${d}/Meter.swift` }
  const src = 'final class Meter {\n  var used = 0\n  func take(_ n: Int) -> Bool { if n < 0 || n > 10 { return false }; used = used &+ n; return true }\n}\n'
  const bad = extractSwift(file(src.replace('if n < 0', 'let s: Int = "x"; if n < 0')), {entry: 'Meter', check: budget})
  expect(bad.refusals[0]!.what).toMatch(/^the source doesn't compile \(swift build\): .*cannot convert value of type 'String' to specified type 'Int'/)
  const killed = killedBuild(() => extractSwift(file(src), {entry: 'Meter', check: budget}))
  expect(killed.refusals[0]!.what).toMatch(/^the check's harness failed, twice .*swift build failed twice with nothing to say of the code/)
  expect(killed.refusals[0]!.what).toContain('Swift compiler build-check limit 0.001 s per attempt (source not verified)')
}, 900_000)

// (no harness can be made for the code, a property of a type it can't name: the code refused, never a difference)
t('a property whose type the harness can\'t name: refused with why, not "the rule and the code differ"', () => {
  const d = mkdtempSync(`${tmpdir()}/gdp-swcase-`)
  writeFileSync(`${d}/Meter.swift`, 'final class Meter {\n  var n = (((0)))\n  func tick() { n = n &+ 1 }\n}\n')
  const x = extractSwift(`${d}/Meter.swift`, {entry: 'Meter', check: budget})
  expect(x.ok).toBe(false)
  expect(x.refusals.map(r => r.what).join('; ')).not.toMatch(/the rule and the code differ/)
}, 900_000)

for (const [seed, entry] of [[735726, 'Tally'], [739158, 'Meter'], [744834, 'Meter'], [735990, 'Tally'], [746946, 'Limiter']] as const) {
  t(`reader fuzz ${seed}: deep open Swift syntax is refused before parser recovery`, () => {
    const x = extractSwift(new URL(`./reader-fixtures/swift-${seed}.swift`, import.meta.url), {entry, check: budget})
    expect(x.ok).toBe(false)
    expect(x.refusals[0]!.what).toMatch(/delimiter characters.*reader limit 32/)
  }, 60_000)
}
