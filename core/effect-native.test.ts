// Native source-law confirmation for Effect services (core/effect.ts + core/native-domain.ts + core/cli.ts):
// atomic Ref.modify, Semaphore(1)-locked, and transactional services confirm natively (exit 0 / broken exit 1),
// while multi-op plain-Ref methods (race.ts, nolock.ts, get-then-set limiter, quota, lease), unlocked siblings,
// Schedules, rewritten Queue/Semaphore models, and lifted multi-fiber models fail closed as unchecked with clear
// reasons; AST-based TS/JS law scoping (scope.ts) prevents template literals/comments from detaching class laws.
import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import * as effect from 'effect'
import * as effect3 from 'effect3'
import {check, scoped} from './cli.ts'
import {proveRule, proveSteps} from './dsl.ts'
import {extractEffect, runner} from './effect.ts'
import {type CodeSide, drive, sandbox} from './extract-check.ts'
import {buildLaw} from './laws.ts'
import {nativeCaptureEdits} from './native-domain.ts'
import {attachSource} from './source-check.ts'

// Atomic token limiter using Ref.modify (one atomic state operation per method).
const ATOMIC_MODIFY_LIMITER = `import {Effect, Ref, Schema} from 'effect'

export class RateLimited extends Schema.TaggedError<RateLimited>()(
  'RateLimited',
  {n: Schema.Number},
) {}

// gdp: law tokens stay within the capacity: tokens <= capacity
export const make = (capacity: number) => Effect.gen(function* () {
  const tokens = yield* Ref.make(capacity)

  const take = Effect.fn('take')(function* (n: number) {
    const next = yield* Ref.modify(tokens, (t) =>
      n < 0 || n > t ? [undefined, t] as const : [t - n, t - n] as const)
    if (next === undefined) {
      return yield* new RateLimited({n})
    }
    return next
  })

  const refill = (n: number) =>
    Ref.update(tokens, (t) =>
      Math.min(capacity, t + Math.max(0, n)))

  return {take, refill}
})
`

// Atomic token limiter guarding all stateful methods under one Semaphore(1) lock.
const ATOMIC_LOCK_LIMITER = `import {Effect, Ref, Schema, Semaphore} from 'effect'

export class RateLimited extends Schema.TaggedError<RateLimited>()(
  'RateLimited',
  {n: Schema.Number},
) {}

// gdp: law tokens stay within the capacity: tokens <= capacity
export const make = (capacity: number) => Effect.gen(function* () {
  const tokens = yield* Ref.make(capacity)
  const lock = yield* Semaphore.make(1)

  const take = Effect.fn('take')(function* (n: number) {
    return yield* lock.withPermits(1)(Effect.gen(function* () {
      const t = yield* Ref.get(tokens)
      if (n < 0 || n > t) {
        return yield* new RateLimited({n})
      }
      yield* Ref.set(tokens, t - n)
      return t - n
    }))
  })

  const refill = (n: number) =>
    lock.withPermits(1)(Ref.update(tokens, (t) =>
      Math.min(capacity, t + Math.max(0, n))))

  return {take, refill}
})
`

// Non-atomic get-then-set limiter (the original film source): Ref.get and Ref.set can interleave under concurrency.
const NON_ATOMIC_LIMITER = `import {Effect, Ref, Schema} from 'effect'

export class RateLimited extends Schema.TaggedError<RateLimited>()(
  'RateLimited',
  {n: Schema.Number},
) {}

// gdp: law tokens stay within the capacity: tokens <= capacity
export const make = (capacity: number) => Effect.gen(function* () {
  const tokens = yield* Ref.make(capacity)

  const take = Effect.fn('take')(function* (n: number) {
    const t = yield* Ref.get(tokens)
    if (n < 0 || n > t) {
      return yield* new RateLimited({n})
    }
    yield* Ref.set(tokens, t - n)
    return t - n
  })

  const refill = (n: number) =>
    Ref.update(tokens, (t) =>
      Math.min(capacity, t + Math.max(0, n)))

  return {take, refill}
})
`

function withTempEffectFile<T>(v: 3 | 4, name: string, code: string, run: (file: string) => Promise<T>): Promise<T> {
  const dir = mkdtempSync(join(tmpdir(), `gdp-effect-native-${v}-`))
  mkdirSync(join(dir, 'node_modules'))
  symlinkSync(join(import.meta.dir, `../node_modules/${v === 3 ? 'effect3' : 'effect'}`), join(dir, 'node_modules/effect'))
  const file = join(dir, name)
  writeFileSync(file, code)
  return run(file).finally(() => rmSync(dir, {recursive: true, force: true}))
}

test('atomic Ref.modify limiter: proven natively (exit 0), step laws proven, broken twins caught with real run (exit 1)', async () => {
  await withTempEffectFile(4, 'limiter-modify.ts', ATOMIC_MODIFY_LIMITER, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: true, check: {runs: 40, depth: 6, states: 60}})
    expect(exit).toBe(0)
    expect(rules.length).toBe(1)
    const r = rules[0]!
    expect(r.ok).toBe(true)
    const law = r.laws[0]!
    expect(law).toMatchObject({name: 'tokens stay within the capacity', verdict: 'proven', translation: 'sampled'})
    expect(law.translationChecks).toBeGreaterThan(0)
    expect(law.why).toBeUndefined()
    for (const p of r.proposed) expect(p.why ?? '').not.toContain('native parameter capture unavailable')
  })

  const withStepLaws = ATOMIC_MODIFY_LIMITER
    .replace("  const take = Effect.fn('take')", "  // gdp: law take lowers tokens by n: tokens == old(tokens) - n and result == tokens\n  const take = Effect.fn('take')")
    .replace('  const refill = (n: number) =>', '  // gdp: law refill never lowers tokens: tokens >= old(tokens) and tokens <= capacity\n  const refill = (n: number) =>')
  await withTempEffectFile(4, 'limiter-modify-steps.ts', withStepLaws, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 40, depth: 6, states: 60}})
    expect(exit).toBe(0)
    expect(rules[0]!.laws.map(l => [l.name, l.verdict, l.translation])).toEqual([
      ['tokens stay within the capacity', 'proven', 'sampled'],
      ['take lowers tokens by n', 'proven', 'sampled'],
      ['refill never lowers tokens', 'proven', 'sampled'],
    ])
    for (const l of rules[0]!.laws) expect(l.translationChecks).toBeGreaterThan(0)
  })

  // Broken twin 1: take skips n < 0, allowing negative takes to exceed capacity.
  const brokenTake = ATOMIC_MODIFY_LIMITER.replace('n < 0 || n > t', 'n > t')
  await withTempEffectFile(4, 'broken-modify-take.ts', brokenTake, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 40, depth: 6, states: 60}})
    expect(exit).toBe(1)
    const law = rules[0]!.laws[0]!
    expect(law).toMatchObject({verdict: 'broken', translation: 'sampled'})
    expect(law.run!.length).toBeGreaterThan(0)
    expect(law.run!.at(-1)!).toMatch(/take\(n=-\d+\)/)
    const real = effect.Effect.runSync(effect.Effect.gen(function* () {
      const tokens = yield* effect.Ref.make(0)
      yield* effect.Ref.modify(tokens, t => (-1 > t ? [undefined, t] as const : [t - -1, t - -1] as const))
      return yield* effect.Ref.get(tokens)
    }))
    expect(real).toBeGreaterThan(0)
  })

  // Broken twin 2: refill omits Math.min(capacity, ...).
  const brokenRefill = ATOMIC_MODIFY_LIMITER.replace('Math.min(capacity, t + Math.max(0, n))', 't + Math.max(0, n)')
  await withTempEffectFile(4, 'broken-modify-refill.ts', brokenRefill, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 40, depth: 6, states: 60}})
    expect(exit).toBe(1)
    const law = rules[0]!.laws[0]!
    expect(law).toMatchObject({verdict: 'broken', translation: 'sampled'})
    expect(law.run!.at(-1)!).toMatch(/refill\(n=\d+\)/)
  })
}, 120_000)

test('atomic Semaphore(1)-locked limiter: proven natively (exit 0), broken twins caught (exit 1), unlocked sibling stays unchecked (exit 2)', async () => {
  await withTempEffectFile(4, 'limiter-lock.ts', ATOMIC_LOCK_LIMITER, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 40, depth: 6, states: 60}})
    expect(exit).toBe(0)
    expect(rules[0]!.laws[0]).toMatchObject({name: 'tokens stay within the capacity', verdict: 'proven', translation: 'sampled'})
    expect(rules[0]!.laws[0]!.translationChecks).toBeGreaterThan(0)
  })

  // Broken twin 1: locked take skips n < 0.
  const brokenTake = ATOMIC_LOCK_LIMITER.replace('if (n < 0 || n > t)', 'if (n > t)')
  await withTempEffectFile(4, 'broken-lock-take.ts', brokenTake, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 40, depth: 6, states: 60}})
    expect(exit).toBe(1)
    expect(rules[0]!.laws[0]).toMatchObject({verdict: 'broken', translation: 'sampled'})
    expect(rules[0]!.laws[0]!.run!.at(-1)!).toMatch(/take\(n=-\d+\)/)
  })

  // Broken twin 2: locked refill omits Math.min(capacity, ...).
  const brokenRefill = ATOMIC_LOCK_LIMITER.replace('Math.min(capacity, t + Math.max(0, n))', 't + Math.max(0, n)')
  await withTempEffectFile(4, 'broken-lock-refill.ts', brokenRefill, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 40, depth: 6, states: 60}})
    expect(exit).toBe(1)
    expect(rules[0]!.laws[0]).toMatchObject({verdict: 'broken', translation: 'sampled'})
    expect(rules[0]!.laws[0]!.run!.at(-1)!).toMatch(/refill\(n=\d+\)/)
  })

  // Control: if take relies on lock across get+set, an unlocked refill can interleave -> must stay unchecked (exit 2).
  const unlockedRefill = ATOMIC_LOCK_LIMITER.replace(
    'lock.withPermits(1)(Ref.update(tokens, (t) =>\n      Math.min(capacity, t + Math.max(0, n))))',
    'Ref.update(tokens, (t) =>\n      Math.min(capacity, t + Math.max(0, n)))',
  )
  await withTempEffectFile(4, 'unlocked-sibling.ts', unlockedRefill, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(exit).toBe(2)
    const law = rules[0]!.laws[0]!
    expect(law).toMatchObject({verdict: 'unknown', translation: 'unchecked'})
    expect(law.why).toContain('refill')
    expect(law.why).toContain('Semaphore(1) lock')
  })
}, 120_000)

test('non-atomic plain-Ref methods (race.ts, nolock.ts on v4 & v3, get-then-set limiter): never proven exit 0; analyzed with interleavings and reported unchecked with actionable reason', async () => {
  const raceCode = `import {Effect, Ref} from 'effect'

// gdp: law only one grant: granted <= 1
export const make = Effect.gen(function* () {
  const consumed = yield* Ref.make(0)
  const granted = yield* Ref.make(0)
  const claim = Effect.fn('claim')(function* () {
    const current = yield* Ref.get(consumed)
    if (current !== 0) return
    yield* Effect.sleep('10 millis')
    yield* Ref.set(consumed, 1)
    yield* Ref.update(granted, n => n + 1)
  })
  const count = Effect.fn('count')(function* () { return yield* Ref.get(granted) })
  return {claim, count}
})
`
  const nolockCode = `import {Effect, Ref} from 'effect'

// gdp: law only one grant: granted <= 1
export const make = Effect.gen(function* () {
  const consumed = yield* Ref.make(0)
  const granted = yield* Ref.make(0)
  const claim = Effect.fn('claim')(function* () {
    const current = yield* Ref.get(consumed)
    if (current !== 0) return
    yield* Ref.set(consumed, 1)
    yield* Ref.update(granted, n => n + 1)
  })
  return {claim}
})
`
  for (const v of [4, 3] as const) {
    for (const [name, code] of [['race.ts', raceCode], ['nolock.ts', nolockCode]] as const) {
      await withTempEffectFile(v, name, code, async file => {
        const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
        expect([v, name, exit]).toEqual([v, name, 2])
        const law = rules[0]!.laws[0]!
        // Fibered interleaving model refutes the race (kernelProven: false) and source verdict stays unchecked.
        expect(law).toMatchObject({name: 'only one grant', verdict: 'unknown', translation: 'unchecked', kernelProven: false})
        expect(law.why).toContain('claim')
        expect(law.why).toContain('consumed')
        expect(law.why).toContain('Ref.modify')
        expect(law.why).toContain('Semaphore(1)')
      })
    }
  }

  // Independently confirm the real Effect.all concurrency race on Effect 4 gives granted === 2.
  const racedGranted = await effect.Effect.runPromise(effect.Effect.gen(function* () {
    const consumed = yield* effect.Ref.make(0)
    const granted = yield* effect.Ref.make(0)
    const claim = effect.Effect.fn('claim')(function* () {
      const current = yield* effect.Ref.get(consumed)
      if (current !== 0) return
      yield* effect.Effect.sleep('10 millis')
      yield* effect.Ref.set(consumed, 1)
      yield* effect.Ref.update(granted, n => n + 1)
    })
    yield* effect.Effect.all([claim(), claim()], {concurrency: 'unbounded'})
    return yield* effect.Ref.get(granted)
  }))
  expect(racedGranted).toBe(2)

  // Original non-atomic film limiter (Ref.get then Ref.set): must stay unchecked with clear fix guidance.
  await withTempEffectFile(4, 'non-atomic-limiter.ts', NON_ATOMIC_LIMITER, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(exit).toBe(2)
    const law = rules[0]!.laws[0]!
    expect(law).toMatchObject({name: 'tokens stay within the capacity', verdict: 'unknown', translation: 'unchecked'})
    expect(law.why).toContain('take reads and writes tokens in separate steps; concurrent calls can interleave: make it atomic with Ref.modify, a Semaphore(1) lock or a transaction')
  })

  // Plain Ref inside Effect.tx is NOT transactional on Effect 4 -> must be refused.
  const fakeTx = `import {Effect, Ref} from 'effect'
export const make = Effect.gen(function* () {
  const n = yield* Ref.make(0)
  const inc = Effect.fn('inc')(function* () {
    yield* Effect.tx(Effect.gen(function* () {
      const c = yield* Ref.get(n)
      yield* Ref.set(n, c + 1)
    }))
  })
  return {inc}
})`
  const fx = extractEffect(fakeTx, {file: 'fake-tx.ts', entry: 'make', effect})
  expect(fx.ok).toBe(false)
  expect(fx.refusals[0]!.what).toContain('only TxRef and TRef participate in a transaction')
}, 180_000)

test('AST scoping regression (scope.ts): template literals and comments inside a class never detach its law onto an Effect service', async () => {
  const scopeProbe = `import {Effect, Ref} from 'effect'

export class Ledger {
  bal = 10
  help() { return \`
let me explain
\` }
  // gdp: law never negative: bal >= 0
  take(k: number) { if (k < 0) throw new Error('neg'); this.bal -= k }
}

export const make = Effect.gen(function* () {
  const bal = yield* Ref.make(10)
  const take = Effect.fn('take')(function* (k: number) {
    const next = yield* Ref.modify(bal, b => (k < 0 || k > b ? [undefined, b] as const : [b - k, b - k] as const))
    if (next === undefined) return yield* Effect.fail('no')
  })
  return {take}
})
`
  await withTempEffectFile(4, 'scope.ts', scopeProbe, async file => {
    expect(scoped(file).map(l => [l.name, l.cls ?? '', l.fn ?? ''])).toEqual([['never negative', 'Ledger', 'take']])
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(exit).toBe(2)
    const makeRule = rules.find(r => r.entry === 'make')!
    expect(makeRule.laws).toEqual([])
    const ledgerRule = rules.find(r => r.entry === 'Ledger')!
    expect(ledgerRule.ok).toBe(false)
    const ledgerLaw = ledgerRule.laws.find(l => l.name === 'never negative')!
    expect(ledgerLaw).toMatchObject({verdict: 'not read', why: 'the rule was refused'})
  })

  // Non-exported class with template literal decoy: Ledger's law still stays scoped to Ledger, never leaking to make.
  await withTempEffectFile(4, 'scope-unexported.ts', scopeProbe.replace('export class Ledger', 'class Ledger'), async file => {
    expect(scoped(file).map(l => [l.name, l.cls ?? '', l.fn ?? ''])).toEqual([['never negative', 'Ledger', 'take']])
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(exit).toBe(2)
    const makeRule = rules.find(r => r.entry === 'make')!
    expect(makeRule.laws).toEqual([])
    const ledgerRule = rules.find(r => r.entry === 'Ledger')!
    expect(ledgerRule.ok).toBe(false)
    expect(ledgerRule.laws.find(l => l.name === 'never negative')).toMatchObject({verdict: 'not read', why: 'the rule was refused'})
  })

  // Also test block comments containing column-0 `const` inside a class, plus closed error class above `make`.
  const blockCommentProbe = `import {Effect, Ref, Schema} from 'effect'

export class RateLimited extends Schema.TaggedError<RateLimited>()('RateLimited', {n: Schema.Number}) {}

export class Vault {
  bal = 10
  /*
export const fake = 1
function decoy() {}
  */
  // gdp: law vault law: bal >= 0
  take(k: number) { this.bal -= k }
}

// gdp: law service inv: tokens <= 10
export const make = Effect.gen(function* () {
  const tokens = yield* Ref.make(10)
  // gdp: law service step: tokens <= old(tokens)
  const take = Effect.fn('take')(function* (n: number) {
    const next = yield* Ref.modify(tokens, t => (n < 0 || n > t ? [undefined, t] as const : [t - n, t - n] as const))
    if (next === undefined) return yield* new RateLimited({n})
  })
  return {take}
})
`
  await withTempEffectFile(4, 'scope-block.ts', blockCommentProbe, async file => {
    expect(scoped(file).map(l => [l.name, l.cls ?? '', l.fn ?? ''])).toEqual([
      ['vault law', 'Vault', 'take'],
      ['service inv', '', 'make'],
      ['service step', '', 'take'],
    ])
  })
}, 120_000)

test('controls: faulty lowering, disagreeing captured parameters, missing capture and disabled replay all refuse', () => {
  // 1. Faulty symbolic law lowering is caught by the native Effect observations and captured bindings.
  const x = extractEffect(ATOMIC_MODIFY_LIMITER, {file: 'limiter.ts', entry: 'make', effect, check: {runs: 25, depth: 5, states: 20, probes: false}})
  expect(x.ok).toBe(true)
  const bad = buildLaw(x, {name: 'wrong take step', expr: 'tokens == old(tokens) - n + 1', method: 'take'})
  if (bad.kind !== 'step') throw new Error('expected step law')
  bad.law.then = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const badVerdict = proveSteps(x.rule!, x.invariants ?? [], [bad.law], {search: false})
  expect(badVerdict).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'error', stuck: 'translation-error'})
  expect(badVerdict.why).toContain('translation error: wrong take step is false in the native code')
  expect(badVerdict.translationWitness?.method).toBe('take')
  expect(typeof badVerdict.translationWitness?.bindings.n).toBe('number')

  // 2. Entry parameter capture occurs before body reassignment of the parameter.
  const mutCode = `import {Effect, Ref} from 'effect'
export const make = Effect.gen(function* () {
  const total = yield* Ref.make(0)
  const add = Effect.fn('add')(function* (n: number) {
    const orig = n
    if (n < 0) return yield* Effect.fail('neg')
    n = n + 1
    yield* Ref.update(total, t => t + orig)
    return n
  })
  return {add}
})`
  const mx = extractEffect(mutCode, {file: 'mut.ts', entry: 'make', effect, check: {runs: 20, depth: 4, states: 20, probes: false}})
  expect(mx.ok).toBe(true)
  const okStep = buildLaw(mx, {name: 'entry param preserved', expr: 'total == old(total) + n and result == n + 1', method: 'add'})
  if (okStep.kind !== 'step') throw new Error('expected step law')
  expect(proveSteps(mx.rule!, mx.invariants ?? [], [okStep.law], {search: false})).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  const wrongStep = buildLaw(mx, {name: 'confuses mutated param', expr: 'result == n', method: 'add'})
  if (wrongStep.kind !== 'step') throw new Error('expected step law')
  wrongStep.law.then = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  expect(proveSteps(mx.rule!, mx.invariants ?? [], [wrongStep.law], {search: false}))
    .toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'error', stuck: 'translation-error'})

  // 3. Direct control where captured nativeBindings disagrees with the rule's input parameters MUST refuse.
  const model = x.model!, sorts = x.sorts!
  const ruleCopy = x.rule!.withDivisors(2)
  const R = runner(effect)
  type LimiterSvc = {take: (n: number) => unknown, refill: (n: number) => unknown, tokens: effect.Ref.Ref<number>, capacity: number}
  let lastCallArgs: unknown[] = []
  const makeSide = (mode: 'disagree' | 'missing'): CodeSide => ({
    make: params => {
      const cap = params.capacity as number
      const tokens = R.run(effect.Ref.make(cap)) as effect.Ref.Ref<number>
      const svc: LimiterSvc = {
        tokens, capacity: cap,
        take: (n: number) => effect.Effect.gen(function* () {
          const next = yield* effect.Ref.modify(tokens, t => (n < 0 || n > t ? [-1, t] as const : [t - n, t - n] as const))
          if (next < 0) return yield* effect.Effect.fail('RateLimited')
          return next
        }),
        refill: (n: number) => effect.Ref.update(tokens, t => Math.min(cap, t + Math.max(0, n))),
      }
      return {ok: true, value: svc}
    },
    at: (snap, params) => {
      const cap = params.capacity as number
      const tokens = R.run(effect.Ref.make(snap.leaves.tokens as number)) as effect.Ref.Ref<number>
      return {
        tokens, capacity: cap,
        take: (n: number) => effect.Effect.gen(function* () {
          const next = yield* effect.Ref.modify(tokens, t => (n < 0 || n > t ? [-1, t] as const : [t - n, t - n] as const))
          if (next < 0) return yield* effect.Effect.fail('RateLimited')
          return next
        }),
        refill: (n: number) => effect.Ref.update(tokens, t => Math.min(cap, t + Math.max(0, n))),
      }
    },
    snapOf: self => { const s = self as LimiterSvc; return {leaves: {tokens: R.get('Ref', s.tokens) as number}, maps: {}} },
    nativeState: self => { const s = self as LimiterSvc; return {tokens: R.get('Ref', s.tokens), capacity: s.capacity} },
    call: (self, e, args) => {
      lastCallArgs = args
      const s = self as LimiterSvc
      const eff = e.call === 'take' ? s.take(args[0] as number) : s.refill(args[0] as number)
      return R.exit(eff, 0)
    },
    nativeBindings: e => mode === 'missing' ? undefined : ({n: (lastCallArgs[0] as number) + (e.call === 'take' ? 1 : 0)}),
    args: (inputs, e) => [inputs[`${e.call}_n`]],
    setNow: () => {},
    coverage: () => ({arms: 0, hit: 0, missed: []}),
  })

  const evDisagree = drive(model, ruleCopy, sorts, makeSide('disagree'), {runs: 20, depth: 5, states: 0, probes: false})
  expect(evDisagree.mismatch).toBeUndefined()
  const disagreeRule = x.rule!.withDivisors(2)
  attachSource(disagreeRule, evDisagree, x.invariants ?? [])
  const takeExact = buildLaw({...x, rule: disagreeRule}, {name: 'take subtracts n', expr: 'tokens == old(tokens) - n', method: 'take'})
  if (takeExact.kind !== 'step') throw new Error('expected step law')
  const disagreeVerdict = proveSteps(disagreeRule, x.invariants ?? [], [takeExact.law], {search: false})
  expect(disagreeVerdict).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'error', stuck: 'translation-error'})
  expect(disagreeVerdict.why).toContain('translation error: take subtracts n is false in the native code')

  // 4. Missing nativeBindings must stay unchecked, never silently falling back to model inputs.
  const evMissing = drive(model, ruleCopy, sorts, makeSide('missing'), {runs: 20, depth: 5, states: 0, probes: false})
  expect(evMissing.mismatch).toBeUndefined()
  const missingRule = x.rule!.withDivisors(2)
  attachSource(missingRule, evMissing, x.invariants ?? [])
  const missingLaw = buildLaw({...x, rule: missingRule}, {name: 'take subtracts n', expr: 'tokens == old(tokens) - n', method: 'take'})
  if (missingLaw.kind !== 'step') throw new Error('expected step law')
  const missingVerdict = proveSteps(missingRule, x.invariants ?? [], [missingLaw.law], {search: false})
  expect(missingVerdict).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'unchecked'})
  expect(missingVerdict.why).toContain('native parameter capture unavailable')

  // 5. Disabled cross-check and uncapturable syntactic shapes stay fail-closed.
  const disabled = extractEffect(ATOMIC_MODIFY_LIMITER, {file: 'limiter.ts', entry: 'make', effect, check: {runs: 10, depth: 4, states: 0, probes: false, lawCrossCheck: false}})
  const dLaw = buildLaw(disabled, {name: 'bounded', expr: 'tokens <= capacity'})
  expect(proveRule(disabled.rule!, [dLaw.law], {search: false})).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'unchecked'})
  expect(nativeCaptureEdits(`const take = Effect.fn('take')(function* (n: number) { return n }, Effect.tap(() => Effect.void))`, 'extra.ts', ['take'])).toEqual([])
  expect(nativeCaptureEdits(`const inner = Effect.fn('take')(function* (n: number) { return n }); const o = {take: inner}`, 'alias.ts', ['take'])).toEqual([])
}, 120_000)

test('Effect.fn forms across Effect 4.x and 3.x: unnamed, fnUntraced, inline property, aliased import, Effect.Service', async () => {
  const shapes4 = [
    `import {Effect, Ref} from 'effect'
// gdp: law bounded: n <= 5
export const make = Effect.gen(function* () {
  const n = yield* Ref.make(0)
  const inc = Effect.fn(function* (k: number) {
    const ok = yield* Ref.modify(n, cur => (k < 0 || cur + k > 5 ? [false, cur] as const : [true, cur + k] as const))
    if (!ok) return yield* Effect.fail('cap')
  })
  return {inc}
})`,
    `import {Effect as Ef, Ref} from 'effect'
// gdp: law bounded: n <= 5
export const make = Ef.gen(function* () {
  const n = yield* Ref.make(0)
  return {
    inc: Ef.fn('Counter.inc')(function* (k: number) {
      const ok = yield* Ref.modify(n, cur => (k < 0 || cur + k > 5 ? [false, cur] as const : [true, cur + k] as const))
      if (!ok) return yield* Ef.fail('cap')
    }),
  }
})`,
    `import * as E from 'effect'
// gdp: law bounded: n <= 5
export const make = E.Effect.gen(function* () {
  const n = yield* E.Ref.make(0)
  const inc = (E.Effect.fnUntraced(function* (k: number) {
    const ok = yield* E.Ref.modify(n, cur => (k < 0 || cur + k > 5 ? [false, cur] as const : [true, cur + k] as const))
    if (!ok) return yield* E.Effect.fail('cap')
  }))
  return {inc}
})`,
  ]
  for (const [i, code] of shapes4.entries()) {
    await withTempEffectFile(4, `shape-${i}.ts`, code, async file => {
      const {rules, exit} = await check([file], {ms: 8000, propose: false, check: {runs: 25, depth: 5, states: 20}})
      expect([i, exit, rules[0]!.laws[0]!.verdict, rules[0]!.laws[0]!.translation]).toEqual([i, 0, 'proven', 'sampled'])
      expect(rules[0]!.laws[0]!.translationChecks).toBeGreaterThan(0)
    })
  }

  // Effect 3.x with Effect.Service, atomic SynchronizedRef.modify, Effect.fn, Clock.currentTimeMillis.
  const svc3 = `import {Clock, Data, Effect, SynchronizedRef} from 'effect'
export class Cooling extends Data.TaggedError('Cooling')<{}> {}
// gdp: law last never negative: last >= 0
export class Cooldown extends Effect.Service<Cooldown>()('Cooldown', {
  effect: Effect.gen(function* () {
    const last = yield* SynchronizedRef.make(0)
    // gdp: law fire records the clock: last == now
    const fire = Effect.fn('Cooldown.fire')(function* () {
      const now = yield* Clock.currentTimeMillis
      const ok = yield* SynchronizedRef.modify(last, cur => (now < 0 || now - cur < 10 ? [false, cur] as const : [true, now] as const))
      if (!ok) return yield* Effect.fail(new Cooling())
    })
    return {fire}
  })
}) {}`
  await withTempEffectFile(3, 'cooldown3.ts', svc3, async file => {
    const {rules, exit} = await check([file], {ms: 8000, propose: false, check: {runs: 25, depth: 5, states: 20}})
    expect(exit).toBe(0)
    expect(rules[0]!.laws.map(l => [l.name, l.verdict, l.translation])).toEqual([
      ['last never negative', 'proven', 'sampled'],
      ['fire records the clock', 'proven', 'sampled'],
    ])
  })
}, 180_000)

test('Clock observations: only actual Clock.currentTimeMillis reads are recorded (not Effect.fn tracing spans)', () => {
  const code = `import {Clock, Effect, Ref} from 'effect'
export const make = Effect.gen(function* () {
  const last = yield* Ref.make(0)
  const fire = Effect.fn('ClockSvc.fire')(function* () {
    const now = yield* Clock.currentTimeMillis
    if (now < 0) return yield* Effect.fail('neg')
    yield* Ref.set(last, now)
    return now
  })
  const reset = Effect.fn('ClockSvc.reset')(function* () {
    yield* Ref.set(last, 0)
  })
  return {fire, reset}
})`
  for (const [v, E] of [[4, effect], [3, effect3]] as const) {
    const x = extractEffect(code, {file: `clock-svc${v}.ts`, entry: 'make', effect: E, check: {runs: 20, depth: 4, states: 20, probes: false}})
    expect(x.ok).toBe(true)
    const fireLaw = buildLaw(x, {name: `fire records now ${v}`, expr: 'last == now and result == now', method: 'fire'})
    if (fireLaw.kind !== 'step') throw new Error('expected step law')
    const fireV = proveSteps(x.rule!, x.invariants ?? [], [fireLaw.law], {search: false})
    expect(fireV).toMatchObject({proven: true, checked: true, translation: 'sampled'})
    expect(fireV.translationChecks).toBeGreaterThan(0)
    const resetLaw = buildLaw(x, {name: `reset claims now ${v}`, expr: 'last == 0 and now >= 0', method: 'reset'})
    if (resetLaw.kind !== 'step') throw new Error('expected step law')
    const resetV = proveSteps(x.rule!, x.invariants ?? [], [resetLaw.law], {search: false})
    expect(resetV).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'unchecked'})
    expect(resetV.why).toContain('unobserved native clock read')
  }

  // Direct sandbox check: conflicting clock reads across Effect.sleep fail closed.
  const modules = {effect, 'gdp-wired:effect': runner(effect)}
  const driftCode = `import {Clock, Effect} from 'effect'
const R = require('gdp-wired:effect')
export function drift() {
  return R.run(Effect.gen(function* () {
    const a = yield* Clock.currentTimeMillis
    yield* Effect.sleep('5 millis')
    const b = yield* Clock.currentTimeMillis
    return b - a
  }), __gdp_clock(), __gdp_observe_clock)
}
export function quiet() {
  const f = Effect.fn('quiet')(function* () { return 1 })
  return R.run(f(), __gdp_clock(), __gdp_observe_clock)
}`
  const box = sandbox(driftCode, 'drift.ts', ['drift', 'quiet'], modules)
  box.setNow(100)
  expect(box.call('quiet', undefined, [])).toEqual({ok: true, value: 1})
  expect(box.observations().clock).toBeUndefined()
  expect(box.call('drift', undefined, [])).toEqual({ok: true, value: 5})
  expect(() => box.observations()).toThrow('conflicting actual clock reads')
}, 120_000)

test('existing Effect examples: non-atomic plain-Ref quota/lease, Schedule, and rewritten Queue/Semaphore stay unchecked with clear reasons', async () => {
  // 1. examples/effect-quota.ts: spend does Ref.get then Ref.update (non-atomic under concurrency) -> unchecked with fix reason.
  const quotaSrc = readFileSync(join(import.meta.dir, '../examples/effect-quota.ts'), 'utf8')
    .replace('export const make =', '// gdp: law a user stays within limit: forall k in usage: usage[k].used <= limit\nexport const make =')
  await withTempEffectFile(4, 'effect-quota.ts', quotaSrc, async file => {
    const {rules, exit} = await check([file], {entry: 'make', ms: 15_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(exit).toBe(2)
    expect(rules[0]!.laws[0]).toMatchObject({name: 'a user stays within limit', verdict: 'unknown', translation: 'unchecked'})
    expect(rules[0]!.laws[0]!.why).toContain('spend reads and writes usage in separate steps')
    expect(rules[0]!.laws[0]!.why).toContain('Ref.modify')
  })

  // 2. examples/effect-retry-policy.ts: acquire/release do Ref.get then Ref.set (non-atomic) and backoff is Schedule -> both unchecked.
  const leaseSrc = readFileSync(join(import.meta.dir, '../examples/effect-retry-policy.ts'), 'utf8')
    .replace('  const acquire = Effect.fn', '  // gdp: law acquire never steals lease: old(holder) == 0 or holder == old(holder)\n  const acquire = Effect.fn')
  await withTempEffectFile(4, 'effect-retry-policy.ts', leaseSrc, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(exit).toBe(2)
    const backoff = rules.find(r => r.entry === 'backoff')!
    const makeRule = rules.find(r => r.entry === 'make')!
    for (const l of backoff.laws) expect(l).toMatchObject({verdict: 'unknown', translation: 'unchecked', kernelProven: true})
    expect(makeRule.laws[0]).toMatchObject({name: 'acquire never steals lease', verdict: 'unknown', translation: 'unchecked'})
    expect(makeRule.laws[0]!.why).toContain('acquire, release read and write holder in separate steps')
  })

  // 3. Single-step rewritten Queue and Semaphore services MUST stay unchecked.
  const singleStepQueue = `import {Effect, Option, Queue} from 'effect'
// gdp: law head stays at most tail: q_head <= q_tail
export const make = Effect.gen(function* () {
  const q = yield* Queue.bounded<number>(4)
  const submit = Effect.fn('submit')(function* (x: number) {
    return yield* Queue.offer(q, x)
  })
  const next = Effect.fn('next')(function* () {
    const o = yield* Queue.poll(q)
    return Option.isNone(o) ? 0 : Option.getOrElse(o, () => 0)
  })
  return {submit, next}
})`
  await withTempEffectFile(4, 'single-queue.ts', singleStepQueue, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 20, depth: 4, states: 20}})
    expect(exit).toBe(2)
    expect(rules[0]!.laws[0]).toMatchObject({verdict: 'unknown', translation: 'unchecked', kernelProven: true})
    expect(rules[0]!.laws[0]!.why).toContain('rewritten model')
  })

  const singleStepSem = `import {Effect, Semaphore} from 'effect'
// gdp: law permits never exceed two: s_taken <= 2
export const make = Effect.gen(function* () {
  const s = yield* Semaphore.make(2)
  const takeOne = Effect.fn('takeOne')(function* () {
    yield* s.take(1)
  })
  const freeOne = Effect.fn('freeOne')(function* () {
    yield* s.release(1)
  })
  return {takeOne, freeOne}
})`
  await withTempEffectFile(4, 'single-sem.ts', singleStepSem, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 20, depth: 4, states: 20}})
    expect(exit).toBe(2)
    expect(rules[0]!.laws[0]).toMatchObject({verdict: 'unknown', translation: 'unchecked', kernelProven: true})
    expect(rules[0]!.laws[0]!.why).toContain('rewritten model')
  })
}, 180_000)

test('reader-driven atomicity regressions: p1b (fn decl helper), p7a (fn decl method), p7e (method syntax), p14 (unlocked method-syntax drain), p12/p13 (mixed tx), p3 (clock across sleep)', async () => {
  // p1b: FunctionDeclaration helper doing Ref.get, sleep, Ref.update.
  const p1b = `import {Effect, Ref} from 'effect'
// gdp: law only one grant: granted <= 1
export const make = Effect.gen(function* () {
  const granted = yield* Ref.make(0)
  function grantOnce() {
    return Effect.gen(function* () {
      const g = yield* Ref.get(granted)
      if (g !== 0) return
      yield* Effect.sleep('10 millis')
      yield* Ref.update(granted, n => n + 1)
    })
  }
  const claim = Effect.fn('claim')(function* () { yield* grantOnce() })
  const count = Effect.fn('count')(function* () { return yield* Ref.get(granted) })
  return {claim, count}
})`

  // p7a: FunctionDeclaration method returned via shorthand.
  const p7a = `import {Effect, Ref} from 'effect'
// gdp: law only one grant: granted <= 1
export const make = Effect.gen(function* () {
  const granted = yield* Ref.make(0)
  function claim() {
    return Effect.gen(function* () {
      const g = yield* Ref.get(granted)
      if (g !== 0) return
      yield* Effect.sleep('10 millis')
      yield* Ref.update(granted, n => n + 1)
    })
  }
  const count = Effect.fn('count')(function* () { return yield* Ref.get(granted) })
  return {claim, count}
})`

  // p7e: Object-method syntax inside returned object literal.
  const p7e = `import {Effect, Ref} from 'effect'
// gdp: law only one grant: granted <= 1
export const make = Effect.gen(function* () {
  const granted = yield* Ref.make(0)
  return {
    claim() {
      return Effect.gen(function* () {
        const g = yield* Ref.get(granted)
        if (g !== 0) return
        yield* Effect.sleep('10 millis')
        yield* Ref.update(granted, n => n + 1)
      })
    },
    count() { return Ref.get(granted) },
  }
})`

  // p12 & p13: TxRef read outside tx then tx/update across suspension (and via fn decl helper).
  const p12 = `import {Effect, TxRef} from 'effect'
// gdp: law only one grant: granted <= 1
export const make = Effect.gen(function* () {
  const granted = yield* TxRef.make(0)
  const claim = Effect.fn('claim')(function* () {
    const g = yield* TxRef.get(granted)
    if (g !== 0) return
    yield* Effect.sleep('10 millis')
    yield* Effect.tx(TxRef.update(granted, n => n + 1))
  })
  const count = Effect.fn('count')(function* () { return yield* TxRef.get(granted) })
  return {claim, count}
})`

  const p13 = `import {Effect, TxRef} from 'effect'
// gdp: law only one grant: granted <= 1
export const make = Effect.gen(function* () {
  const granted = yield* TxRef.make(0)
  function checkOnce() { return TxRef.get(granted) }
  const claim = Effect.fn('claim')(function* () {
    const g = yield* checkOnce()
    if (g !== 0) return
    yield* Effect.sleep('10 millis')
    yield* TxRef.update(granted, n => n + 1)
  })
  const count = Effect.fn('count')(function* () { return yield* TxRef.get(granted) })
  return {claim, count}
})`

  for (const [name, code] of [['p1b.ts', p1b], ['p7a.ts', p7a], ['p7e.ts', p7e], ['p12.ts', p12], ['p13.ts', p13]] as const) {
    await withTempEffectFile(4, name, code, async file => {
      const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
      expect([name, exit]).toEqual([name, 2])
      const law = rules[0]!.laws[0]!
      expect(law).toMatchObject({name: 'only one grant', verdict: 'unknown', translation: 'unchecked'})
      expect(law.why).toContain('claim')
      expect(law.why).toContain('granted')
      expect(law.why).toContain('Ref.modify')
    })
  }

  // p14: locked take + unlocked method-syntax drain() and count() -> real concurrency drives tokens to -1.
  const p14 = `import {Effect, Ref, Semaphore} from 'effect'
// gdp: law tokens never go negative: tokens >= 0
export const make = Effect.gen(function* () {
  const tokens = yield* Ref.make(1)
  const lock = yield* Semaphore.make(1)
  const take = Effect.fn('take')(function* () {
    return yield* lock.withPermits(1)(Effect.gen(function* () {
      const t = yield* Ref.get(tokens)
      if (t < 1) return false
      yield* Effect.sleep('10 millis')
      yield* Ref.update(tokens, x => x - 1)
      return true
    }))
  })
  return {
    take,
    drain() { return Ref.set(tokens, 0) },
    count() { return Ref.get(tokens) },
  }
})`
  await withTempEffectFile(4, 'p14-lockgap.ts', p14, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(exit).toBe(2)
    const law = rules[0]!.laws[0]!
    expect(law).toMatchObject({name: 'tokens never go negative', verdict: 'unknown', translation: 'unchecked'})
    expect(law.why).toContain('drain')
    expect(law.why).toContain('outside the Semaphore(1) lock held by take')
  })

  // p3: Clock read before sleep followed by Ref write -> stale clock across suspension is unchecked.
  const p3 = `import {Clock, Effect, Ref} from 'effect'
// gdp: law last never goes down: last >= old(last)
export const make = Effect.gen(function* () {
  const last = yield* Ref.make(0)
  const stamp = Effect.fn('stamp')(function* () {
    const now = yield* Clock.currentTimeMillis
    yield* Effect.sleep('10 millis')
    yield* Ref.set(last, now)
  })
  const read = Effect.fn('read')(function* () { return yield* Ref.get(last) })
  return {stamp, read}
})`
  await withTempEffectFile(4, 'p3-clock.ts', p3, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(exit).toBe(2)
    expect(rules[0]!.laws[0]).toMatchObject({verdict: 'unknown', translation: 'unchecked'})
    expect(rules[0]!.laws[0]!.why).toContain('reads the clock')
  })
}, 180_000)

test('closure let state (p8): refused unless provably confined to one atomic step; single-Effect.sync control accepted; tx-mixed let refused', async () => {
  // p8: closure `let granted = 0` touched across two Effect.sync calls with sleep between -> refused (exit 2).
  const p8 = `import {Effect} from 'effect'
// gdp: law only one grant: granted <= 1
export const make = Effect.gen(function* () {
  let granted = 0
  const claim = Effect.fn('claim')(function* () {
    const g = yield* Effect.sync(() => granted)
    if (g !== 0) return
    yield* Effect.sleep('10 millis')
    yield* Effect.sync(() => { granted = granted + 1 })
  })
  const count = Effect.fn('count')(function* () { return yield* Effect.sync(() => granted) })
  return {claim, count}
})`
  await withTempEffectFile(4, 'p8-letsync.ts', p8, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(exit).toBe(2)
    expect(rules[0]!.ok).toBe(false)
    expect(rules[0]!.refusals[0]!.what).toContain('closure state granted')
    expect(rules[0]!.laws[0]).toMatchObject({name: 'only one grant', verdict: 'not read'})
  })

  // Same without sleep: two separate Effect.sync yields can still interleave -> refused (exit 2).
  await withTempEffectFile(4, 'p8-nosleep.ts', p8.replace("yield* Effect.sleep('10 millis')\n", ''), async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(exit).toBe(2)
    expect(rules[0]!.ok).toBe(false)
    expect(rules[0]!.refusals[0]!.what).toContain('closure state granted')
  })

  // Closure `let` inside Effect.tx does not roll back -> refused (exit 2).
  const letInTx = `import {Effect, TxRef} from 'effect'
// gdp: law only one grant: granted <= 1
export const make = Effect.gen(function* () {
  let granted = 0
  const flag = yield* TxRef.make(0)
  const claim = Effect.fn('claim')(function* () {
    yield* Effect.tx(Effect.gen(function* () {
      const f = yield* TxRef.get(flag)
      if (f !== 0) return
      yield* TxRef.set(flag, 1)
      yield* Effect.sync(() => { granted = granted + 1 })
    }))
  })
  return {claim}
})`
  await withTempEffectFile(4, 'p8-tx.ts', letInTx, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(exit).toBe(2)
    expect(rules[0]!.ok).toBe(false)
    expect(rules[0]!.refusals[0]!.what).toContain('closure state cannot be used inside a transaction')
  })

  // Positive control: closure `let` provably touched only inside one synchronous Effect.sync per method -> proven natively (exit 0).
  const atomicLet = `import {Effect} from 'effect'
// gdp: law only one grant: granted <= 1
export const make = Effect.gen(function* () {
  let granted = 0
  const claim = () => Effect.sync(() => {
    if (granted !== 0) return false
    granted = granted + 1
    return true
  })
  const count = () => Effect.sync(() => granted)
  return {claim, count}
})`
  await withTempEffectFile(4, 'p8-atomic.ts', atomicLet, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(exit).toBe(0)
    expect(rules[0]!.laws[0]).toMatchObject({name: 'only one grant', verdict: 'proven', translation: 'sampled'})
  })
}, 180_000)

test('AST declaration-span law attribution (s1, s2, s3, s4): anonymous default class, wrapped class, named class, and module fn never bind to Effect make; CLI text output lists every law', async () => {
  const makePart = `export const make = Effect.gen(function* () {
  const bal = yield* Ref.make(10)
  const take = Effect.fn('take')(function* (k: number) {
    return yield* Ref.modify(bal, b => (k >= 0 && k <= b ? [true, b - k] as const : [false, b] as const))
  })
  return {take}
})`

  // s1: anonymous `export default class`
  const s1 = `import {Effect, Ref} from 'effect'\n\nexport default class {\n  bal = 10\n  // gdp: law never negative: bal >= 0\n  take(k: number) { this.bal -= k }\n}\n\n${makePart}\n`
  // s2: `wrap(class { ... })`
  const s2 = `import {Effect, Ref} from 'effect'\n\nconst wrap = <T,>(c: T) => c\nexport const Ledger = wrap(class {\n  bal = 10\n  // gdp: law never negative: bal >= 0\n  take(k: number) { this.bal -= k }\n})\n\n${makePart}\n`
  // s3: named `export class Ledger`
  const s3 = `import {Effect, Ref} from 'effect'\n\nexport class Ledger {\n  bal = 10\n  // gdp: law never negative: bal >= 0\n  take(k: number) { this.bal -= k }\n}\n\n${makePart}\n`
  // s4: module-level `export function take`
  const s4 = `import {Effect, Ref} from 'effect'\n\nlet bal = 10\n// gdp: law never negative: bal >= 0\nexport function take(k: number) { bal -= k }\n\n${makePart}\n`

  const cliPath = join(import.meta.dir, 'cli.ts')
  for (const [name, code] of [['s1-anon.ts', s1], ['s2-wrapped.ts', s2], ['s3-named.ts', s3], ['s4-fnlaw.ts', s4]] as const) {
    await withTempEffectFile(4, name, code, async file => {
      const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
      expect([name, exit]).toEqual([name, 2])
      const makeRule = rules.find(r => r.entry === 'make')!
      expect(makeRule.ok).toBe(true)
      expect(makeRule.laws).toEqual([])
      const allLaws = rules.flatMap(r => r.laws)
      expect(allLaws.length).toBe(1)
      expect(allLaws[0]).toMatchObject({name: 'never negative', verdict: 'not read'})

      // Verify explicit `--entry make` STILL refuses to bind another declaration's law to `make`.
      const explicit = await check([file], {entry: 'make', ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
      expect(explicit.exit).toBe(2)
      expect(explicit.rules.find(r => r.entry === 'make')!.laws).toEqual([])
      expect(explicit.rules.flatMap(r => r.laws).find(l => l.name === 'never negative')?.verdict).toBe('not read')

      // Verify plain text CLI output (without --json) is non-empty, exits 2, and lists the law explicitly.
      const proc = spawnSync('bun', [cliPath, 'check', file, '--no-propose'], {encoding: 'utf8', timeout: 60_000})
      expect([name, proc.status]).toEqual([name, 2])
      expect(proc.stdout.length).toBeGreaterThan(0)
      expect(proc.stdout).toContain('never negative')
      expect(proc.stdout).toContain('not read')
      expect(proc.stdout).toContain('0 of 1 stated laws proven, 0 broken, 0 unknown, 1 not read')
    })
  }
}, 180_000)

test('film limiters g-atomic and g-lock stay proven (2/2, exit 0) and all four broken twins stay broken (exit 1)', async () => {
  const gAtomic = `import {Effect, Ref, Schema} from 'effect'

export class RateLimited extends Schema.TaggedError<RateLimited>()('RateLimited', {n: Schema.Number}) {}

// gdp: law tokens stay within the capacity: tokens <= capacity
// gdp: law tokens never go negative: capacity < 0 or tokens >= 0
export const make = (capacity: number) => Effect.gen(function* () {
  const tokens = yield* Ref.make(capacity)

  const take = Effect.fn('take')(function* (n: number) {
    const left = yield* Ref.modify(tokens, (t) =>
      n < 0 || n > t ? [undefined, t] as const : [t - n, t - n] as const)
    if (left === undefined) return yield* new RateLimited({n})
    return left
  })

  const refill = (n: number) =>
    Ref.update(tokens, (t) => Math.min(capacity, t + Math.max(0, n)))

  return {take, refill}
})
`
  const gLock = `import {Effect, Ref, Schema, Semaphore} from 'effect'

export class RateLimited extends Schema.TaggedError<RateLimited>()('RateLimited', {n: Schema.Number}) {}

// gdp: law tokens stay within the capacity: tokens <= capacity
// gdp: law tokens never go negative: capacity < 0 or tokens >= 0
export const make = (capacity: number) => Effect.gen(function* () {
  const tokens = yield* Ref.make(capacity)
  const lock = yield* Semaphore.make(1)

  const take = Effect.fn('take')(function* (n: number) {
    return yield* lock.withPermits(1)(Effect.gen(function* () {
      const t = yield* Ref.get(tokens)
      if (n < 0 || n > t) return yield* new RateLimited({n})
      yield* Ref.set(tokens, t - n)
      return t - n
    }))
  })

  const refill = (n: number) =>
    lock.withPermits(1)(Ref.update(tokens, (t) => Math.min(capacity, t + Math.max(0, n))))

  return {take, refill}
})
`
  // Two good limiters: both 2/2 proven natively (exit 0).
  for (const [name, code] of [['g-atomic.ts', gAtomic], ['g-lock.ts', gLock]] as const) {
    await withTempEffectFile(4, name, code, async file => {
      const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 40, depth: 6, states: 60}})
      expect([name, exit]).toEqual([name, 0])
      expect(rules[0]!.laws.map(l => [l.name, l.verdict, l.translation])).toEqual([
        ['tokens stay within the capacity', 'proven', 'sampled'],
        ['tokens never go negative', 'proven', 'sampled'],
      ])
    })
  }

  // Four broken twins: (1) g-atomic without `n > t`, (2) g-lock without `n > t`,
  // (3) g-atomic without Math.min cap in refill, (4) g-lock without Math.min cap in refill.
  const twins: [string, string, string][] = [
    ['g-atomic-no-t.ts', gAtomic.replace('n < 0 || n > t', 'n < 0'), 'tokens never go negative'],
    ['g-lock-no-t.ts', gLock.replace('n < 0 || n > t', 'n < 0'), 'tokens never go negative'],
    ['g-atomic-no-min.ts', gAtomic.replace('Math.min(capacity, t + Math.max(0, n))', 't + Math.max(0, n)'), 'tokens stay within the capacity'],
    ['g-lock-no-min.ts', gLock.replace('Math.min(capacity, t + Math.max(0, n))', 't + Math.max(0, n)'), 'tokens stay within the capacity'],
  ]
  for (const [name, code, brokenLaw] of twins) {
    await withTempEffectFile(4, name, code, async file => {
      const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 40, depth: 6, states: 60}})
      expect([name, exit]).toEqual([name, 1])
      const broken = rules[0]!.laws.find(l => l.name === brokenLaw)!
      expect(broken).toMatchObject({verdict: 'broken', translation: 'sampled'})
      expect(broken.run!.length).toBeGreaterThan(0)
    })
  }
}, 180_000)

test('multi-declarator export const a = ..., b = ... binds laws per VariableDeclaration span, never per statement (b5b, g1, g2)', async () => {
  // b5b-multidecl: Effect services in one `export const make = ..., other = ...` statement
  const b5b = `import {Effect, Ref} from 'effect'

export const make = Effect.gen(function* () {
  const tokens = yield* Ref.make(1)
  const take = Effect.fn('take')(function* () { return yield* Ref.modify(tokens, t => t >= 1 ? [true, t - 1] as const : [false, t] as const) })
  return {take}
}),
  // gdp: law tokens never go negative: tokens >= 0
  other = Effect.gen(function* () {
    const tokens = yield* Ref.make(1)
    const take = Effect.fn('take')(function* () { yield* Ref.update(tokens, t => t - 1) })
    const count = Effect.fn('count')(function* () { return yield* Ref.get(tokens) })
    return {take, count}
  })
`
  await withTempEffectFile(4, 'b5b-multidecl.ts', b5b, async file => {
    const def = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(def.exit).toBe(1)
    expect(def.rules.find(r => r.entry === 'make')!.laws).toEqual([])
    expect(def.rules.find(r => r.entry === 'other')!.laws[0]).toMatchObject({name: 'tokens never go negative', verdict: 'broken', translation: 'sampled'})

    const onlyMake = await check([file], {entry: 'make', ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(onlyMake.exit).toBe(2)
    expect(onlyMake.rules.find(r => r.entry === 'make')!.laws).toEqual([])
    expect(onlyMake.rules.flatMap(r => r.laws)[0]).toMatchObject({name: 'tokens never go negative', verdict: 'not read'})
  })

  // Unextractable second declarator and inline block comment between declarators never leak to `make`
  const b5Unextractable = `import {Effect, Ref} from 'effect'

export const make = Effect.gen(function* () {
  const tokens = yield* Ref.make(1)
  const take = Effect.fn('take')(function* () { return yield* Ref.modify(tokens, t => t >= 1 ? [true, t - 1] as const : [false, t] as const) })
  return {take}
}), /* gdp: law tokens never go negative: tokens >= 0 */ other = { take() { return -1 } }
`
  await withTempEffectFile(4, 'b5-inline-unextractable.ts', b5Unextractable, async file => {
    const res = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(res.exit).toBe(2)
    expect(res.rules.find(r => r.entry === 'make')!.laws).toEqual([])
    expect(res.rules.flatMap(r => r.laws)[0]).toMatchObject({name: 'tokens never go negative', verdict: 'not read'})
  })

  // g1-classexpr: class expressions in `export const Good = class {...}, Bad = class {...}`
  const g1 = `export const Good = class {
  tokens = 1
  take(n: number) { if (n < 0 || n > this.tokens) throw new Error('no'); this.tokens -= n }
}, Bad = class {
  tokens = 1
  // gdp: law never negative: tokens >= 0
  take(n: number) { if (n < 0) throw new Error('no'); this.tokens -= n }
}
`
  const g1Above = `export const Good = class {
  tokens = 1
  take(n: number) { if (n < 0 || n > this.tokens) throw new Error('no'); this.tokens -= n }
},
  // gdp: law never negative: tokens >= 0
  Bad = class {
    tokens = 1
    take(n: number) { if (n < 0) throw new Error('no'); this.tokens -= n }
  }
`
  for (const [name, code] of [['g1-classexpr.ts', g1], ['g1-classexpr-above.ts', g1Above]] as const) {
    await withTempEffectFile(4, name, code, async file => {
      const def = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
      expect([name, def.exit]).toEqual([name, 1])
      expect(def.rules.find(r => r.entry === 'Good')!.laws).toEqual([])
      expect(def.rules.find(r => r.entry === 'Bad')!.laws[0]).toMatchObject({name: 'never negative', verdict: 'broken', translation: 'sampled'})

      const onlyGood = await check([file], {entry: 'Good', ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
      expect([name, onlyGood.exit]).toEqual([name, 2])
      expect(onlyGood.rules.find(r => r.entry === 'Good')!.laws).toEqual([])
      expect(onlyGood.rules.flatMap(r => r.laws)[0]).toMatchObject({name: 'never negative', verdict: 'not read'})
    })
  }

  // g2-fnfactory: function factories in `export const good = () => {...}, bad = () => {...}`
  const g2 = `export const good = () => {
  let tokens = 1
  return { take(n: number) { if (n < 0 || n > tokens) throw new Error('no'); tokens -= n } }
},
  // gdp: law never negative: tokens >= 0
  bad = () => {
    let tokens = 1
    return { take(n: number) { if (n < 0) throw new Error('no'); tokens -= n } }
  }
`
  const g2Inside = `export const good = () => {
  let tokens = 1
  return { take(n: number) { if (n < 0 || n > tokens) throw new Error('no'); tokens -= n } }
}, bad = () => {
  let tokens = 1
  // gdp: law never negative: tokens >= 0
  return { take(n: number) { if (n < 0) throw new Error('no'); tokens -= n } }
}
`
  for (const [name, code] of [['g2-fnfactory.ts', g2], ['g2-fnfactory-inside.ts', g2Inside]] as const) {
    await withTempEffectFile(4, name, code, async file => {
      const def = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
      expect([name, def.exit]).toEqual([name, 1])
      expect(def.rules.find(r => r.entry === 'good')!.laws).toEqual([])
      expect(def.rules.find(r => r.entry === 'bad')!.laws[0]).toMatchObject({name: 'never negative', verdict: 'broken', translation: 'sampled'})

      const onlyGood = await check([file], {entry: 'good', ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
      expect([name, onlyGood.exit]).toEqual([name, 2])
      expect(onlyGood.rules.find(r => r.entry === 'good')!.laws).toEqual([])
      expect(onlyGood.rules.flatMap(r => r.laws)[0]).toMatchObject({name: 'never negative', verdict: 'not read'})
    })
  }
}, 180_000)
