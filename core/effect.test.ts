// Effect services (core/effect.ts): read from their source on Effect 4.x and 3.x (the forms a service is written in),
// checked by running them on Effect's runtime; the example's quota proven; a rule written by hand run beside a service
// (Effect's own Semaphore on both versions, and the quota) and a wrong one caught by a run; Schemas as kinds; and what the
// reader doesn't take refused with the reason.
import {expect, test} from 'bun:test'
import {mkdirSync, mkdtempSync, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {pathToFileURL} from 'node:url'
import * as effect from 'effect'
import * as effect3 from 'effect3'
import {type Term, int, nat, oneOf, proveRule, proveSteps, rule, when} from './dsl.ts'
import {conforms, extractEffect, fromSchema} from './effect.ts'
import {quotaConforms, quotaLaws, readQuota} from '../examples/effect.ts'

const SVC = 'effect-svc.ts'
const read = (code: string, entry = 'make') => extractEffect(code, {file: SVC, entry, effect})
// Code for Effect 3.x, read where `effect` is 3.x (its types) and run on it.
const dir3 = mkdtempSync(join(tmpdir(), 'gdp-effect3-'))
mkdirSync(join(dir3, 'node_modules'))
symlinkSync(join(import.meta.dir, '../node_modules/effect3'), join(dir3, 'node_modules/effect'))
const read3 = (code: string, entry: string) => extractEffect(code, {file: join(dir3, 'svc.ts'), entry, effect: effect3})

const LIMITER = `
import {Effect, Ref, Schema} from 'effect'
export class RateLimited extends Schema.TaggedError<RateLimited>()('RateLimited', {n: Schema.Number}) {}
export const make = (capacity: number) => Effect.gen(function* () {
  const tokens = yield* Ref.make(capacity)
  const take = Effect.fn('take')(function* (n: number) {
    const t = yield* Ref.get(tokens)
    if (n < 0 || n > t) return yield* new RateLimited({n})
    yield* Ref.set(tokens, t - n)
    return t - n
  })
  const refill = (n: number) => Ref.update(tokens, t => Math.min(capacity, t + Math.max(0, n)))
  return {take, refill}
})
`

test('a service (4.x): Refs, Effect.fn methods, a yielded error, a result; read, checked on the runtime, its law proven', () => {
  const x = read(LIMITER)
  expect(x.ok).toBe(true)
  expect(x.evidence).toMatchObject({coverage: {missed: []}})
  expect(x.evidence!.refusedBoth).toBeGreaterThan(100)
  expect(x.source).toContain('an Effect service')
  const r = x.rule!
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  expect(proveRule(r, [r.law('tokens stay within the capacity', ({tokens, capacity}: any) => tokens.atMost(capacity))]).proven).toBe(true)
}, 120_000)

test('the forms a make effect is written in (4.x): Layer.effect, a Context.Service, Effect.fn, a lock, Ref.modify', () => {
  const svc = (make: string, tail = '') => `
import {Context, Effect, Layer, Ref, Semaphore} from 'effect'
export class Counter extends Context.Service<Counter, {readonly next: Effect.Effect<number>, readonly reset: (to: number) => Effect.Effect<void>}>()('Counter') {}
${make}
${tail}`
  const body = `{
  const n = yield* Ref.make(0)
  const lock = yield* Semaphore.make(1)
  const next = lock.withPermits(1)(Ref.modify(n, x => [x + 1, x + 1] as const))
  return Counter.of({next: () => next, reset: (to: number) => Ref.set(n, Math.max(0, to))})
}`
  for (const [code, entry] of [
    [svc(`export const make = Effect.gen(function* () ${body})`), 'make'],
    [svc(`const make = Effect.gen(function* () ${body})`, 'export const layer = Layer.effect(Counter, make)'), 'layer'],
    [svc(`export const layer = Layer.effect(Counter, Effect.gen(function* () ${body}))`), 'layer'],
    [svc(`export const make = Effect.fn('make')(function* () ${body})`), 'make'],
    [svc(`export function make() { return Effect.gen(function* () ${body}) }`), 'make'],
  ] as const) {
    const x = read(code, entry)
    expect([entry, x.ok, x.refusals]).toEqual([entry, true, []])
    expect(x.source).toContain('next_result: 0')
    // (one way in: the service inferred, the make effect its names reach once; effect from the file's project)
    const y = extractEffect({code, file: SVC})
    expect([y.ok, y.source, y.notes[0]]).toEqual([true, x.source, `the entry inferred: ${entry}, the file's one make effect`])
  }
}, 120_000)

test('a service (3.x): Effect.Service, Data.TaggedError, SynchronizedRef, a lock, Effect.fail; run on Effect 3', () => {
  const wallet = `
import {Data, Effect, SynchronizedRef} from 'effect'
export class Overdrawn extends Data.TaggedError('Overdrawn')<{readonly amount: number}> {}
export class Wallet extends Effect.Service<Wallet>()('Wallet', {
  effect: Effect.gen(function* () {
    const balance = yield* SynchronizedRef.make(0)
    const lock = yield* Effect.makeSemaphore(1)
    const deposit = (amount: number) => SynchronizedRef.update(balance, b => b + Math.max(0, amount))
    const withdraw = (amount: number) => lock.withPermits(1)(Effect.gen(function* () {
      const b = yield* SynchronizedRef.get(balance)
      if (amount < 0 || amount > b) return yield* Effect.fail(new Overdrawn({amount}))
      return yield* SynchronizedRef.modify(balance, x => [x - amount, x - amount] as const)
    }))
    return {deposit, withdraw}
  })
}) {}`, x = read3(wallet, 'Wallet')
  expect([x.ok, x.refusals]).toEqual([true, []])
  // (one way in: Effect 3 resolved from the file's own node_modules, the service inferred, a path and a URL)
  writeFileSync(join(dir3, 'wallet.ts'), wallet)
  for (const at of [join(dir3, 'wallet.ts'), pathToFileURL(join(dir3, 'wallet.ts'))]) expect(extractEffect(at).source).toBe(extractEffect(wallet, {file: join(dir3, 'wallet.ts'), entry: 'Wallet', effect: effect3}).source)
  expect(x.evidence).toMatchObject({coverage: {missed: []}})
  const r = x.rule!
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  expect(proveRule(r, [r.law('the balance never goes below 0', ({balance}: any) => balance.atLeast(0))]).proven).toBe(true)
  // The clock on 3.x: a cooldown, Ref.make outside a class, Effect.fn.
  const y = read3(`
import {Clock, Data, Effect, Ref} from 'effect'
export class Cooling extends Data.TaggedError('Cooling')<{}> {}
export const make = (gap: number) => Effect.gen(function* () {
  const last = yield* Ref.make(0)
  const fire = Effect.fn('fire')(function* () {
    const now = yield* Clock.currentTimeMillis
    if (now - (yield* Ref.get(last)) < gap) return yield* Effect.fail(new Cooling())
    yield* Ref.set(last, now)
  })
  return {fire}
})`, 'make')
  expect([y.ok, y.refusals]).toEqual([true, []])
  expect(y.evidence).toMatchObject({coverage: {missed: []}})
}, 120_000)

test('a Set in a Ref, a flag from Ref.modify, and a failure after a write that changed nothing', () => {
  const x = read(`
import {Effect, Ref, Schema} from 'effect'
export class AlreadyRunning extends Schema.TaggedError<AlreadyRunning>()('AlreadyRunning', {target: Schema.String}) {}
export const make = Effect.gen(function* () {
  const running = yield* Ref.make<ReadonlySet<string>>(new Set())
  const acquire = Effect.fn('acquire')(function* (target: string) {
    const ok = yield* Ref.modify(running, r => {
      if (r.has(target)) return [false, r] as const
      const next = new Set(r)
      next.add(target)
      return [true, next] as const
    })
    if (!ok) return yield* new AlreadyRunning({target})
  })
  const release = (target: string) => Ref.update(running, r => { const next = new Set(r); next.delete(target); return next })
  return {acquire, release}
})`)
  expect([x.ok, x.refusals]).toEqual([true, []])
  expect(x.evidence).toMatchObject({coverage: {missed: []}})
  expect(x.source).toContain(`.maps({running: record({has: bool}).from({has: false})})`)
}, 120_000)

test('state typed by a Schema (a Struct of Literals and an Int), a record replaced by cases', () => {
  const x = read(`
import {Effect, Ref, Schema} from 'effect'
export const Job = Schema.Struct({status: Schema.Literals(['idle', 'running', 'done']), attempts: Schema.Int})
export class Busy extends Schema.TaggedError<Busy>()('Busy', {}) {}
export const make = Effect.gen(function* () {
  const job = yield* Ref.make<typeof Job.Type>({status: 'idle', attempts: 0})
  const start = Effect.fn('start')(function* () {
    const j = yield* Ref.get(job)
    if (j.status === 'running') return yield* new Busy()
    yield* Ref.set(job, {status: 'running', attempts: j.attempts + 1})
  })
  const finish = () => Ref.update(job, j => (j.status === 'running' ? {...j, status: 'done' as const} : j))
  return {start, finish}
})`)
  expect([x.ok, x.refusals]).toEqual([true, []])
  expect(x.source).toContain(`job_status: oneOf('idle', 'running', 'done').from('idle')`)
  expect(x.evidence).toMatchObject({coverage: {missed: []}})
}, 120_000)

test('a map of records in a Ref, copied and set, with the clock: the example\'s quota proven', () => {
  const x = readQuota()
  expect([x.ok, x.refusals]).toEqual([true, []])
  expect(x.evidence).toMatchObject({coverage: {missed: []}})
  const {laws, stepLaws} = quotaLaws(x.rule!)
  expect(proveRule(x.rule!, [...x.invariants!, ...laws])).toMatchObject({proven: true, checked: true})
  expect(proveSteps(x.rule!, x.invariants!, stepLaws)).toMatchObject({proven: true, checked: true})
}, 120_000)

test('a rule by hand beside the service: the right one runs as it does, a wrong one is caught by a run', () => {
  expect(quotaConforms().failure).toBeUndefined()
  expect(quotaConforms('a window a millisecond too long').failure).toMatch(/now":86400000.*the service takes the request, the rule refuses it/)
}, 120_000)

// Effect's own Semaphore: takeIfAvailable, release, releaseAll and resize (a take that would wait is a fiber that
// acquires later, outside one request: left out), on 4.x and, without takeIfAvailable, 3.x.
export const semaphore = (bug?: 'release clamps at 0') => rule('semaphore').params({permits: nat})
  .inputs({op: oneOf('takeIfAvailable', 'release', 'releaseAll', 'resize'), n: int})
  .state({taken: int.from(0), size: int.from(({permits}) => permits), last: int.from(0)})
  .step(({op, n, taken, size}) => {
    const free = size.minus(taken), takes = op.is('takeIfAvailable').and(free.atLeast(n))
    const released = bug ? when(taken.minus(n).atLeast(0), taken.minus(n), 0) : taken.minus(n)
    const after = when(takes, taken.plus(n), when(op.is('release'), released, when(op.is('releaseAll'), 0, taken)))
    return {taken: after, size: when(op.is('resize'), n, size), last: when(op.is('takeIfAvailable'), when(takes, 1, 0), when(op.is('release').or(op.is('releaseAll')), size.minus(after), 0))}
  })
const OPS = ['takeIfAvailable', 'release', 'releaseAll', 'resize'] as const
const semService = (E: typeof effect | typeof effect3, ops: readonly string[]) => ({
  effect: E as never,
  make: ({permits}: Record<string, unknown>) => ('Semaphore' in E ? (E as typeof effect).Semaphore.makeUnsafe(permits as number) : (E as typeof effect3).Effect.unsafeMakeSemaphore(permits as number)),
  request: (s: never, {op, n}: Record<string, unknown>) => (s as Record<string, (n: number) => unknown>)[op as string] instanceof Function ? (s as Record<string, (n: number) => unknown>)[op as string]!(n as number) : (s as Record<string, unknown>)[op as string],
  observe: (s: {taken: number, permits: number}, result: unknown, {op}: Record<string, unknown>) => ({taken: s.taken, size: s.permits, ...(op === 'resize' || !ops.includes(op as string) ? {} : {last: typeof result === 'boolean' ? Number(result) : result})}),
})
test('Effect\'s Semaphore (4.x and 3.x) runs as a rule written by hand; a rule that clamps a release is caught', () => {
  const draw = (ops: readonly string[]) => (rand: (n: number) => number) => ({op: ops[rand(ops.length)]!, n: rand(5) - 1})
  const params = (rand: (n: number) => number) => ({permits: rand(4)})
  expect(conforms(semaphore(), semService(effect, OPS), {draw: draw(OPS), params, runs: 200, depth: 12})).toEqual({checked: 2400})
  expect(conforms(semaphore(), semService(effect3, OPS.slice(1)), {draw: draw(OPS.slice(1)), params, runs: 200, depth: 12})).toEqual({checked: 2400})
  expect(conforms(semaphore('release clamps at 0'), semService(effect, OPS), {draw: draw(OPS), params, runs: 200, depth: 12}).failure).toMatch(/the service's taken is -\d+, the rule's 0/)
  // Its documented gotcha, as a refuted law: a release past what is taken makes more free than the permits.
  const r = semaphore()
  expect(proveRule(r, [r.law('never more free than the permits', ({taken}) => taken.atLeast(0))]).proven).toBe(false)
}, 120_000)

test('Schemas as kinds (4.x and 3.x): structs, literals, tagged unions, integers, null and optional fields', () => {
  for (const [E, v] of [[effect, 4], [effect3, 3]] as const) {
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    const S: any = E.Schema
    const nonneg = v === 4 ? S.Int.check(S.isGreaterThanOrEqualTo(0)) : S.NonNegativeInt
    const lits = v === 4 ? S.Literals(['open', 'closed']) : S.Literal('open', 'closed')
    const k = fromSchema(S.Struct({n: nonneg, i: S.Int, b: S.Boolean, s: S.String, state: lits, maybe: S.NullOr(S.Int), opt: S.optional(S.Boolean)}))
    expect(k.sample(() => 0, 1)).toEqual({n: 0, i: -1, b: false, s: expect.anything(), state: 'open', maybe: null, opt: null})
    const cmd = fromSchema(v === 4 ? S.Union([S.TaggedStruct('Add', {n: nonneg}), S.TaggedStruct('Clear', {})]) : S.Union(S.TaggedStruct('Add', {n: nonneg}), S.TaggedStruct('Clear', {})))
    const r = rule('sum').inputs({cmd}).state({total: 0}).step(({cmd, total}) => ({total: cmd.match({Add: (c: {n: Term}) => total.plus(c.n), Clear: () => 0})}))
    expect(proveRule(r, [r.law('the total is never below 0', ({total}) => total.atLeast(0))]).proven).toBe(true)
    expect(() => fromSchema(S.Number)).toThrow(/a number that may be fractional/)
    expect(() => fromSchema(S.Struct({at: S.Array(S.Int)}))).toThrow(/fromSchema: at is a/)
  }
}, 120_000)

test('one way in: two services in a file are refused with their names, none with what to write', () => {
  const two = extractEffect({code: `import {Effect, Ref} from 'effect'
export const a = Effect.gen(function* () { const n = yield* Ref.make(0); return {bump: () => Ref.update(n, x => x + 1)} })
export const b = Effect.gen(function* () { const n = yield* Ref.make(0); return {bump: () => Ref.update(n, x => x + 1)} })`, file: SVC})
  expect(two.refusals[0]!.what).toBe('several services in the file (a, b): name one (entry)')
  expect(extractEffect({code: `export const n = 1`, file: SVC}).refusals[0]!.what).toMatch(/^no make effect in the file/)
  expect(extractEffect(join(dir3, 'absent.ts')).refusals[0]!.what).toBe('no such file')
})

test('what the reader doesn\'t take is refused where it is, with the reason', () => {
  const cases: [string, RegExp][] = [
    [`export const make = Effect.gen(function* () { const n = yield* Ref.make(0); return {bump: Effect.fn(function* () { yield* Ref.update(n, x => x + 1); if ((yield* Ref.get(n)) > 3) return yield* Effect.fail('too many') })} })`, /fails after writing n: a Ref keeps what was written/],
    [`export const make = Effect.gen(function* () { const n = yield* Ref.make(0); return {go: (op: 'a' | 'b') => Ref.update(n, x => Match.value(op).pipe(Match.when('a', () => x + 1), Match.orElse(() => x)))} })`, /Match.value\(op\): a matcher/],
    [`export const make = Effect.gen(function* () { const n = yield* Ref.make(0); return {go: () => Ref.update(n, x => x + 1).pipe(Effect.retry({times: 2}))} })`, /Effect.retry\(\{times: 2\}\) in a pipe/],
    [`export const make = Effect.gen(function* () { const n = yield* Ref.make(0); return {roll: Effect.fn(function* () { yield* Ref.set(n, yield* Random.nextInt) })} })`, /Random.nextInt: an answer from outside/],
    [`export const make = Effect.gen(function* () { const n = yield* Ref.make(0); return {go: () => Effect.gen(function* () { const m = yield* Ref.make(1); yield* Ref.set(n, yield* Ref.get(m)) })} })`, /Ref.make in a step/],
    [`export const make = Effect.gen(function* () { const s = yield* Ref.make<ReadonlySet<string>>(new Set()); return {add: (k: string) => Ref.update(s, x => new Set([...x, k]))} })`, /a spread of other than an array/],
    [`type S = Data.TaggedEnum<{Idle: {}, Busy: {n: number}}>\nconst S = Data.taggedEnum<S>()\nexport const make = Effect.gen(function* () { const s = yield* Ref.make<S>(S.Idle()); return {go: () => Ref.set(s, S.Busy({n: 1}))} })`, /a union of other than string literals/],
    [`export const make = Effect.gen(function* () { const n = yield* Ref.make(0); return {go: () => Effect.timeout(Ref.update(n, x => x + 1), '1 second')} })`, /Effect.timeout \(Effect.gen/],
    [`export const make = Effect.gen(function* () { const c = yield* Clock.currentTimeMillis; const n = yield* Ref.make(c); return {go: () => Ref.set(n, 0)} })`, /run while the service is made/],
  ]
  for (const [body, why] of cases) {
    const x = read(`import {Clock, Data, Effect, Match, Random, Ref} from 'effect'\n${body}`)
    expect(x.ok).toBe(false)
    expect(x.refusals[0]!.what).toMatch(why)
  }
}, 120_000)
