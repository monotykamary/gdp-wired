// Effect's Queue and Semaphore, modelled once (core/effect-prims.ts) on 4.x and 3.x: each primitive's canonical rule
// read and checked, its laws proven (bounded, nothing lost, FIFO, the permits) and run beside Effect's own primitive on
// random operations and fibers (a wrong strategy caught); the worker pool of examples/effect-pool.ts read as every fiber's
// steps, its laws proven, a release without its acquire refuted by a run and seen on the runtime; the CLI on the pool's
// comments; and what isn't modelled refused with why.
import {expect, test} from 'bun:test'
import * as effect from 'effect'
import * as effect3 from 'effect3'
import {join} from 'node:path'
import {proveRule, proveSteps} from './dsl.ts'
import {extractEffect, fiberRun, primitiveConforms, primitiveLaws, withLemmas} from './effect.ts'
import {check} from './cli.ts'
import {inProject} from '../examples/effect-retry.ts'
import {SPECS, pool3, pool4, poolLaws, primRule, provePool, racePool, readPool, specName} from '../examples/effect-queue.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Any = any
// These callback laws prove the extracted model, not native source-law semantics.
const modelOnly = {kernelProven: true, proven: false, checked: false, translation: 'unchecked'}
const svc = (v: 3 | 4, body: string, decls = '') => `import {Data, Effect, Option, Queue, Ref${v === 4 ? ', Semaphore' : ''}} from 'effect'
export class No extends Data.TaggedError('No')<{}> {}
${decls}export const make = Effect.gen(function* () {
${body}
})`

test('each primitive\'s rule (4.x and 3.x): read, checked, its laws proven for every capacity and number of permits', () => {
  for (const v of [4, 3] as const) for (const spec of SPECS) {
    const x = primRule(spec, v) as Any, {laws, stepLaws, refuted} = primitiveLaws(x, spec)
    expect([v, specName(spec), x.ok, x.refusals]).toEqual([v, specName(spec), true, []])
    expect(x.evidence.requests).toBeGreaterThan(100)
    expect([v, specName(spec), proveRule(x.rule, laws)]).toMatchObject([v, specName(spec), modelOnly])
    for (const sl of stepLaws) expect([v, sl.name, proveSteps(x.rule, laws, [sl])]).toMatchObject([v, sl.name, modelOnly])
    // (Effect's own semaphore gives back what it is given, unchecked: its use law is a service's to keep)
    for (const l of refuted) expect(proveRule(x.rule, [...laws, l]).run?.trace.length).toBe(1)
  }
}, 600_000)

test('each rule beside Effect\'s own primitive (4.x and 3.x) on random operations and fibers; a wrong strategy is caught', async () => {
  for (const v of [4, 3] as const) for (const spec of SPECS) {
    const c = await primitiveConforms(spec, v === 4 ? effect : effect3, {x: primRule(spec, v), runs: 60})
    expect([v, specName(spec), c.failure]).toEqual([v, specName(spec), undefined])
    expect(c.checked).toBeGreaterThan(400)
    expect([c.blocked, c.interrupted].every(n => n > 10)).toBe(true)
  }
  // (the dropping queue's rule beside a sliding queue: an offer to it full answers true, the rule false)
  const wrong = await primitiveConforms({kind: 'queue', strategy: 'sliding'}, effect, {x: primRule({kind: 'queue', strategy: 'dropping'}, 4), runs: 60})
  expect(wrong.failure).toMatch(/offer completes with true, the rule answers false/)
}, 600_000)

test('the pool (examples/effect-pool.ts, and on 3.x): every fiber\'s steps, its laws proven; a release without its acquire refuted by a run and seen on the runtime', async () => {
  for (const v of [4, 3] as const) {
    const {x} = readPool(v) as {x: Any}
    expect([v, x.ok, x.refusals, x.rule.machine.name]).toEqual([v, true, [], 'make, every fiber'])
    expect(x.notes.join('\n')).toMatch(/jobs is an Effect \d Queue \(bounded, 4 items\), modelled/)
    expect(x.primitives.map((p: Any) => p.invariants.map((l: Any) => l.name))).toEqual([['jobs holds at most 4 items'], ['workers never has more permits taken than its 2', 'workers\'s permits taken are those its fibers hold']])
    const p = provePool(x)
    expect(p.lemmas).toContain('workers: what its fibers hold is never below nothing')
    for (const [name, verdict] of p.verdicts) expect([v, name, verdict]).toMatchObject([v, name, modelOnly])
    const b = readPool(v, 'release without acquire') as {x: Any, file: string}, use = poolLaws(b.x).at(-1)!
    const bv = proveRule(b.x.rule, [...b.x.invariants, use])
    expect([v, bv.proven]).toEqual([v, false])
    expect(fiberRun(b.x, bv.run!).join('; ')).toMatch(/cancel\(\)/)
    expect(await racePool(v, b.file, true)).toBe(3)
    expect(await racePool(v, b.file, false)).toBe(2)
  }
}, 900_000)

test('a failure in withPermits\' body gives the permits back first (checked on the runtime, no run breaks the use law); a poll, a dropping and a sliding queue', () => {
  for (const v of [4, 3] as const) {
    const code = svc(v, `  const q = yield* Queue.sliding<boolean>(2)
  const w = yield* Queue.dropping<number>(3)
  const s = yield* ${v === 4 ? 'Semaphore.make' : 'Effect.makeSemaphore'}(1)
  const n = yield* Ref.make(0)
  const put = Effect.fn('put')(function* (urgent: boolean) { return yield* Queue.offer(q, urgent) })
  const next = Effect.fn('next')(function* () {
    const o = yield* Queue.poll(q)
    return Option.isNone(o) ? 0 : Option.getOrElse(o, () => false) ? 2 : 1
  })
  const add = Effect.fn('add')(function* (k: number) { return yield* Queue.offer(w, k) })
  const serve = Effect.fn('serve')(function* () {
    yield* s.withPermits(1)(Effect.gen(function* () {
      const k = yield* Queue.take(w)
      if (k < 0) return yield* new No()
      yield* Ref.update(n, x => x + k)
    }))
  })
  return {put, next, add, serve}`)
    const x = extractEffect(inProject(v, 'svc.ts', code), {entry: 'make'}) as Any
    expect([v, x.ok, x.refusals]).toEqual([v, true, []])
    expect(x.evidence.requests).toBeGreaterThan(500)
    // (its use law: no run breaks it; the release on the failure's path is the model's, checked on the runtime above)
    const w = withLemmas(x, {ms: 20_000}), use = proveRule(w.x.rule!, [...w.x.invariants!, x.primitives[2].laws[0]], {search: {ms: 20_000}})
    expect([v, use.run]).toEqual([v, undefined])
  }
}, 600_000)

test('what the model doesn\'t hold is refused where it is, with why', () => {
  const cases: [3 | 4, string, RegExp][] = [
    [3, `  const q = yield* Queue.bounded<number>(2)\n  return {size: () => Queue.size(q)}`, /Queue.size: Effect 3's size counts the fibers waiting on the queue/],
    [4, `  const q = yield* Queue.bounded<number>(2)\n  return {all: () => Queue.takeAll(q)}`, /Queue.takeAll \(offer, take, poll, size, isFull, shutdown are read\)/],
    [4, `  const q = yield* Queue.bounded<number>(2)\n  const give = (x: Queue.Queue<number>) => Queue.offer(x, 1)\n  return {go: () => give(q)}`, /q used other than by its operations/],
    [4, `  const k = 2\n  const q = yield* Queue.bounded<number>(k)\n  return {go: () => Queue.take(q)}`, /a capacity of other than a whole number from 1 written here/],
    [4, `  const q = yield* Queue.make<number>({capacity: 2, strategy: 'dropping', extra: 1} as never)\n  return {go: () => Queue.take(q)}`, /Queue.make's extra/],
    [4, `  const s = yield* Semaphore.make(2)\n  const n = yield* Ref.make(0)\n  return {go: Effect.fn('go')(function* () { yield* s.resize(3) })}`, /resize changes its permits, which the model holds fixed/],
    [4, `  const s = yield* Semaphore.make(2)\n  const n = yield* Ref.make(0)\n  return {go: (k: number) => s.withPermits(2)(Ref.update(n, x => x + k))}`, /other than yielded as a statement of a generator's body/],
    [4, `  const s = yield* Semaphore.make(2)\n  const n = yield* Ref.make(0)\n  return {go: Effect.fn('go')(function* (k: number) { yield* s.take(k) })}`, /a permit count of other than a whole number from 1 written here/],
    [4, `  const s = yield* Semaphore.make(2)\n  const n = yield* Ref.make(0)\n  const bad = Effect.fn('bad')(function* () { return yield* new No() })\n  return {go: Effect.fn('go')(function* () { yield* s.withPermits(1)(Effect.gen(function* () { yield* Ref.update(n, x => x + 1); yield* bad() })) })}`, /inside withPermits may fail \(or be interrupted\) other than by a statement of its body/],
    [3, `  const q = yield* Queue.bounded<number>(2)\n  const s = yield* Effect.makeSemaphore(1)\n  const n = yield* Ref.make(0)\n  return {stop: () => Queue.shutdown(q), go: Effect.fn('go')(function* () { yield* s.withPermits(1)(Effect.gen(function* () { const x = yield* Queue.take(q); yield* Ref.set(n, x) })) })}`, /a take from a queue the service shuts down|an operation on a queue the service shuts down/],
    [4, `  const q = yield* Queue.bounded<number>(2)\n  return {go: Effect.fn('go')(function* () { const o = yield* Queue.poll(q); return o._tag === 'Some' ? 1 : 0 })}`, /o._tag: an Option's _tag/],
    [4, `  const q = yield* Queue.bounded<{id: number}>(2)\n  return {go: () => Queue.take(q)}`, /a queue of \{ id: number; \} \(numbers and booleans are read/],
    [4, `  const q = yield* Queue.bounded<number>(2)\n  const q_head = yield* Ref.make(0)\n  return {go: () => Queue.take(q), h: () => Ref.get(q_head)}`, /q_head is a name of the code's, and one the model of q gives/],
  ]
  // (Effect's RateLimiter, 3.x's and 4.x's, refused with why)
  const rl3 = svc(3, `  const limit = yield* RateLimiter.make({limit: 2, interval: '1 second'})\n  const n = yield* Ref.make(0)\n  return {go: () => limit(Ref.update(n, x => x + 1))}`).replace("Ref} from 'effect'", "Ref, RateLimiter} from 'effect'")
  const rl4 = svc(4, `  const limiter = yield* RateLimiter.RateLimiter\n  const n = yield* Ref.make(0)\n  return {go: () => Ref.update(n, x => x + 1)}`, "import {RateLimiter} from 'effect/persistence'\n")
  for (const [v, code] of [[3, rl3], [4, rl4]] as const) expect(extractEffect(inProject(v, 'rl.ts', code), {entry: 'make'}).refusals[0]?.what).toMatch(/a RateLimiter \(not modelled: 3.x's gives its permits back on timers/)
  for (const [v, body, why] of cases) {
    const x = extractEffect(inProject(v, 'bad.ts', svc(v, body)), {entry: 'make'})
    expect([body, x.ok]).toEqual([body, false])
    expect([body, x.refusals[0]!.what]).toEqual([body, expect.stringMatching(why)])
  }
}, 300_000)

test('the CLI refuses unchecked pool source laws on both Effect versions and the broken variant', async () => {
  const want = ['every job waiting costs 1 to 10: unknown', 'the work done never goes negative: unknown', 'no permit is given back that wasn\'t taken: unknown']
  const {rules, exit} = await check([join(import.meta.dir, '../examples/effect-pool.ts')], {ms: 30_000, propose: false})
  expect([exit, rules.map(r => r.laws.map(l => `${l.name}: ${l.verdict}`))]).toEqual([2, [want]])
  const r3 = await check([inProject(3, 'pool.ts', pool3())], {ms: 30_000, propose: false})
  expect([r3.exit, r3.rules.map(r => r.laws.map(l => `${l.name}: ${l.verdict}`))]).toEqual([2, [want]])
  for (const r of [...rules, ...r3.rules]) for (const l of r.laws) expect(l).toMatchObject({kernelProven: true, translation: 'unchecked', verdict: 'unknown'})
  for (const [v, code] of [[4, pool4('release without acquire')], [3, pool3('release without acquire')]] as const) {
    const b = await check([inProject(v, 'broken.ts', code)], {ms: 30_000, propose: false})
    const use = b.rules[0]!.laws.find(l => l.name === 'no permit is given back that wasn\'t taken')!
    expect([v, b.exit, use.verdict]).toEqual([v, 2, 'unknown'])
    expect(use.translation).toBe('unchecked')
    expect(use.kernelProven).toBe(false)
    expect(use.run).toBeUndefined()
  }
}, 900_000)
