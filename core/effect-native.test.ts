// Native source-law confirmation for Effect services (core/effect.ts + core/native-domain.ts):
// real Effect.fn / Effect.fnUntraced parameter capture, invocation-bound Clock.currentTimeMillis
// observations, real native Ref/TxRef/TRef/SynchronizedRef states, broken-twin counterexamples,
// disagreeing-binding controls, and fail-closed boundaries for rewritten primitives, schedules
// and lifted multi-fiber models.
import {expect, test} from 'bun:test'
import {mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import * as effect from 'effect'
import * as effect3 from 'effect3'
import {check} from './cli.ts'
import {proveRule, proveSteps} from './dsl.ts'
import {extractEffect, runner} from './effect.ts'
import {type CodeSide, drive, sandbox} from './extract-check.ts'
import {buildLaw} from './laws.ts'
import {nativeCaptureEdits} from './native-domain.ts'
import {attachSource} from './source-check.ts'

// Exact limiter source from the TypeScript/Effect short film (Effect 4.0.7).
const FILM_LIMITER = `import {Effect, Ref, Schema} from 'effect'

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

test('film limiter: CLI proves the Effect service law natively (exit 0) and proves step laws on take and refill', async () => {
  await withTempEffectFile(4, 'limiter.ts', FILM_LIMITER, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: true, check: {runs: 40, depth: 6, states: 60}})
    expect(exit).toBe(0)
    expect(rules.length).toBe(1)
    const r = rules[0]!
    expect(r.ok).toBe(true)
    expect(r.laws.length).toBe(1)
    const law = r.laws[0]!
    expect(law).toMatchObject({name: 'tokens stay within the capacity', verdict: 'proven', translation: 'sampled'})
    expect(law.translationChecks).toBeGreaterThan(0)
    expect(law.why).toBeUndefined()
    // Proposed laws must not fail with native parameter capture unavailable either.
    for (const p of r.proposed) expect(p.why ?? '').not.toContain('native parameter capture unavailable')
  })

  const withStepLaws = FILM_LIMITER
    .replace("  const take = Effect.fn('take')", "  // gdp: law take lowers tokens by n: tokens == old(tokens) - n and result == tokens\n  const take = Effect.fn('take')")
    .replace('  const refill = (n: number) =>', '  // gdp: law refill never lowers tokens: tokens >= old(tokens) and tokens <= capacity\n  const refill = (n: number) =>')
  await withTempEffectFile(4, 'limiter-steps.ts', withStepLaws, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 40, depth: 6, states: 60}})
    expect(exit).toBe(0)
    expect(rules[0]!.laws.map(l => [l.name, l.verdict, l.translation])).toEqual([
      ['tokens stay within the capacity', 'proven', 'sampled'],
      ['take lowers tokens by n', 'proven', 'sampled'],
      ['refill never lowers tokens', 'proven', 'sampled'],
    ])
    for (const l of rules[0]!.laws) expect(l.translationChecks).toBeGreaterThan(0)
  })
}, 120_000)

test('broken limiter twins: skipping the negative-take check or the refill cap breaks with a real run (exit 1)', async () => {
  // Broken twin 1: take skips n < 0, so a negative take adds tokens past capacity.
  const brokenTake = FILM_LIMITER.replace('if (n < 0 || n > t)', 'if (n > t)')
  await withTempEffectFile(4, 'broken-take.ts', brokenTake, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 40, depth: 6, states: 60}})
    expect(exit).toBe(1)
    const law = rules[0]!.laws[0]!
    expect(law).toMatchObject({verdict: 'broken', translation: 'sampled'})
    expect(law.run!.length).toBeGreaterThan(0)
    expect(law.run!.at(-1)!).toMatch(/take\(n=-\d+\)/)
    // Independently confirm the bug on the real Effect runtime.
    const real = effect.Effect.runSync(effect.Effect.gen(function* () {
      const tokens = yield* effect.Ref.make(0)
      const t = yield* effect.Ref.get(tokens)
      const n = -1
      if (n <= t) yield* effect.Ref.set(tokens, t - n)
      return yield* effect.Ref.get(tokens)
    }))
    expect(real).toBeGreaterThan(0)
  })

  // Broken twin 2: refill skips Math.min(capacity, ...), overflowing capacity.
  const brokenRefill = FILM_LIMITER.replace('Math.min(capacity, t + Math.max(0, n))', 't + Math.max(0, n)')
  await withTempEffectFile(4, 'broken-refill.ts', brokenRefill, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 40, depth: 6, states: 60}})
    expect(exit).toBe(1)
    const law = rules[0]!.laws[0]!
    expect(law).toMatchObject({verdict: 'broken', translation: 'sampled'})
    expect(law.run!.length).toBeGreaterThan(0)
    expect(law.run!.at(-1)!).toMatch(/refill\(n=\d+\)/)
  })
}, 120_000)

test('controls: faulty lowering, disagreeing captured parameters, missing capture and disabled replay all refuse', () => {
  // 1. Faulty symbolic law lowering is caught by the native Effect observations and captured bindings.
  const x = extractEffect(FILM_LIMITER, {file: 'limiter.ts', entry: 'make', effect, check: {runs: 25, depth: 5, states: 20, probes: false}})
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
          const t = yield* effect.Ref.get(tokens)
          if (n < 0 || n > t) return yield* effect.Effect.fail('RateLimited')
          yield* effect.Ref.set(tokens, t - n)
          return t - n
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
          const t = yield* effect.Ref.get(tokens)
          if (n < 0 || n > t) return yield* effect.Effect.fail('RateLimited')
          yield* effect.Ref.set(tokens, t - n)
          return t - n
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
  const disabled = extractEffect(FILM_LIMITER, {file: 'limiter.ts', entry: 'make', effect, check: {runs: 10, depth: 4, states: 0, probes: false, lawCrossCheck: false}})
  const dLaw = buildLaw(disabled, {name: 'bounded', expr: 'tokens <= capacity'})
  expect(proveRule(disabled.rule!, [dLaw.law], {search: false})).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'unchecked'})
  expect(nativeCaptureEdits(`const take = Effect.fn('take')(function* (n: number) { return n }, Effect.tap(() => Effect.void))`, 'extra.ts', ['take'])).toEqual([])
  expect(nativeCaptureEdits(`const inner = Effect.fn('take')(function* (n: number) { return n }); const o = {take: inner}`, 'alias.ts', ['take'])).toEqual([])
}, 120_000)

test('Effect.fn forms across Effect 4.x and 3.x: unnamed, fnUntraced, inline property, aliased import, Layer/Service', async () => {
  const shapes4 = [
    `import {Effect, Ref} from 'effect'
// gdp: law bounded: n <= 5
export const make = Effect.gen(function* () {
  const n = yield* Ref.make(0)
  const inc = Effect.fn(function* (k: number) {
    if (k < 0) return yield* Effect.fail('neg')
    const cur = yield* Ref.get(n)
    if (cur + k > 5) return yield* Effect.fail('cap')
    yield* Ref.set(n, cur + k)
  })
  return {inc}
})`,
    `import {Effect as Ef, Ref} from 'effect'
// gdp: law bounded: n <= 5
export const make = Ef.gen(function* () {
  const n = yield* Ref.make(0)
  return {
    inc: Ef.fn('Counter.inc')(function* (k: number) {
      if (k < 0) return yield* Ef.fail('neg')
      const cur = yield* Ref.get(n)
      if (cur + k > 5) return yield* Ef.fail('cap')
      yield* Ref.set(n, cur + k)
    }),
  }
})`,
    `import * as E from 'effect'
// gdp: law bounded: n <= 5
export const make = E.Effect.gen(function* () {
  const n = yield* E.Ref.make(0)
  const inc = (E.Effect.fnUntraced(function* (k: number) {
    if (k < 0) return yield* E.Effect.fail('neg')
    const cur = yield* E.Ref.get(n)
    if (cur + k > 5) return yield* E.Effect.fail('cap')
    yield* E.Ref.set(n, cur + k)
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

  // Effect 3.x with Effect.Service, SynchronizedRef, Effect.fn, Clock.currentTimeMillis.
  const svc3 = `import {Clock, Data, Effect, SynchronizedRef} from 'effect'
export class Cooling extends Data.TaggedError('Cooling')<{}> {}
// gdp: law last never negative: last >= 0
export class Cooldown extends Effect.Service<Cooldown>()('Cooldown', {
  effect: Effect.gen(function* () {
    const last = yield* SynchronizedRef.make(0)
    // gdp: law fire records the clock: last == now
    const fire = Effect.fn('Cooldown.fire')(function* () {
      const now = yield* Clock.currentTimeMillis
      if (now < 0 || now - (yield* SynchronizedRef.get(last)) < 10) return yield* Effect.fail(new Cooling())
      yield* SynchronizedRef.set(last, now)
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
  const x = extractEffect(code, {file: 'clock-svc.ts', entry: 'make', effect, check: {runs: 25, depth: 5, states: 20, probes: false}})
  expect(x.ok).toBe(true)

  // Method that reads Clock.currentTimeMillis: law reading `now` is natively confirmed.
  const fireLaw = buildLaw(x, {name: 'fire records now', expr: 'last == now and result == now', method: 'fire'})
  if (fireLaw.kind !== 'step') throw new Error('expected step law')
  const fireV = proveSteps(x.rule!, x.invariants ?? [], [fireLaw.law], {search: false})
  expect(fireV).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  expect(fireV.translationChecks).toBeGreaterThan(0)

  // Method that does NOT read Clock.currentTimeMillis (even with Effect.fn span tracing):
  // `now` was never natively observed, so a law reading `now` MUST refuse as unchecked.
  const resetLaw = buildLaw(x, {name: 'reset claims now', expr: 'last == 0 and now >= 0', method: 'reset'})
  if (resetLaw.kind !== 'step') throw new Error('expected step law')
  const resetV = proveSteps(x.rule!, x.invariants ?? [], [resetLaw.law], {search: false})
  expect(resetV).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'unchecked'})
  expect(resetV.why).toContain('unobserved native clock read')

  // Direct sandbox check: conflicting clock reads across Effect.sleep fail closed, and Effect 3.x matches.
  const x3 = extractEffect(code, {file: 'clock-svc3.ts', entry: 'make', effect: effect3, check: {runs: 20, depth: 4, states: 20, probes: false}})
  expect(x3.ok).toBe(true)
  const fireLaw3 = buildLaw(x3, {name: 'fire records now 3', expr: 'last == now and result == now', method: 'fire'})
  if (fireLaw3.kind !== 'step') throw new Error('expected step law')
  expect(proveSteps(x3.rule!, x3.invariants ?? [], [fireLaw3.law], {search: false})).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  const resetLaw3 = buildLaw(x3, {name: 'reset claims now 3', expr: 'last == 0 and now >= 0', method: 'reset'})
  if (resetLaw3.kind !== 'step') throw new Error('expected step law')
  expect(proveSteps(x3.rule!, x3.invariants ?? [], [resetLaw3.law], {search: false})).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'unchecked'})
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

test('existing Effect examples: quota and lease services prove natively; rewritten Queue/Semaphore and Schedule stay unchecked', async () => {
  // 1. examples/effect-quota.ts with its laws as comments (Map ref, Clock, Effect.fn).
  const quotaSrc = readFileSync(join(import.meta.dir, '../examples/effect-quota.ts'), 'utf8')
    .replace('export const make =', '// gdp: law a user stays within limit: forall k in usage: usage[k].used <= limit\nexport const make =')
    .replace('  const spend = Effect.fn', '  // gdp: law spend reports non-negative remaining: result >= 0 and usage[user].windowStart <= now\n  const spend = Effect.fn')
    .replace('  const refund = (user: string, units: number) =>', '  // gdp: law refund never raises use: forall k in usage: usage[k].used <= old(usage[k].used)\n  const refund = (user: string, units: number) =>')
  await withTempEffectFile(4, 'effect-quota.ts', quotaSrc, async file => {
    const {rules, exit} = await check([file], {entry: 'make', ms: 15_000, propose: false, check: {runs: 30, depth: 6, states: 40}})
    expect(exit).toBe(0)
    expect(rules[0]!.laws.map(l => [l.name, l.verdict, l.translation])).toEqual([
      ['a user stays within limit', 'proven', 'sampled'],
      ['spend reports non-negative remaining', 'proven', 'sampled'],
      ['refund never raises use', 'proven', 'sampled'],
    ])
    for (const l of rules[0]!.laws) expect(l.translationChecks).toBeGreaterThan(0)
  })

  // 2. examples/effect-retry-policy.ts: lease service proves natively; Schedule backoff remains unchecked.
  const leaseSrc = readFileSync(join(import.meta.dir, '../examples/effect-retry-policy.ts'), 'utf8')
    .replace('  const acquire = Effect.fn', '  // gdp: law acquire never steals lease: old(holder) == 0 or holder == old(holder)\n  const acquire = Effect.fn')
  await withTempEffectFile(4, 'effect-retry-policy.ts', leaseSrc, async file => {
    const {rules, exit} = await check([file], {ms: 10_000, propose: false, check: {runs: 25, depth: 5, states: 30}})
    expect(exit).toBe(2) // backoff is a Schedule (unchecked)
    const backoff = rules.find(r => r.entry === 'backoff')!
    const makeRule = rules.find(r => r.entry === 'make')!
    for (const l of backoff.laws) expect(l).toMatchObject({verdict: 'unknown', translation: 'unchecked', kernelProven: true})
    expect(makeRule.laws).toHaveLength(1)
    expect(makeRule.laws[0]).toMatchObject({name: 'acquire never steals lease', verdict: 'proven', translation: 'sampled'})
    expect(makeRule.laws[0]!.translationChecks).toBeGreaterThan(0)
  })

  // 3. Single-step rewritten Queue and Semaphore services (where fibered() does NOT run) MUST still stay unchecked.
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
