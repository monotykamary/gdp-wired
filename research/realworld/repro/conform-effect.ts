// Conformance for the Effect items, through gdp-wired/effect's conforms (core/effect.ts): each rule beside the real
// code on Effect's own runtime, the requests run with Effect.runSyncExit and the clock fixed at the request's time.
// - concurrency/effect/Semaphore: Effect 4.0.7's Semaphore.makeUnsafe and 3.22.4's Effect.unsafeMakeSemaphore (the
//   dev dependencies `effect` and `effect3`, pinned at those versions), its taken and permits read after each request;
// - ratelimit/effect/fixedWindow and tokenBucket: 4.0.7's RateLimiter.layerStoreMemory, each reply compared;
// - ratelimit/t3code/SourceControlRateLimit: the original file at the pin (fetched into a temp dir, its one foreign
//   import, @t3tools/contracts' SourceControlProviderKind, stubbed by a Schema of the two providers), run on 4.0.7; after
//   each request the key's generation (a check with allowPaused) and its pause (a check that fails, and the retryAt it
//   fails with) are read. Then extractEffect reads the original: it is refused where it first leaves the subset (check's
//   optional argument), the reason printed.
// `bun research/realworld/repro/conform-effect.ts [runs]`
import {mkdirSync, mkdtempSync, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import * as effect from 'effect'
import * as effect3 from 'effect3'
import {Duration, Effect} from 'effect'
import {RateLimiter} from 'effect/persistence'
import {conforms, extractEffect} from '../../../core/effect.ts'
import {semaphore} from '../items/concurrency-effect.ts'
import {R, fixedWindow, tokenBucket} from '../items/ratelimit-effect.ts'
import {pause} from '../items/ratelimit-t3code.ts'

const runs = Number(process.argv[2] ?? 300)
const results: [string, {checked: number, failure?: string}][] = []
type Rand = (n: number) => number

// The Semaphore, on both versions (3.x has no takeIfAvailable).
const OPS = ['takeIfAvailable', 'release', 'releaseAll', 'resize']
for (const [name, E, ops] of [['4.0.7', effect, OPS], ['3.22.4', effect3, OPS.slice(1)]] as const) {
  results.push([`Semaphore (${name})`, conforms(semaphore(), {
    effect: E as never,
    make: ({permits0}) => ('Semaphore' in E ? effect.Semaphore.makeUnsafe(permits0 as number) : effect3.Effect.unsafeMakeSemaphore(permits0 as number)),
    request: (s: {taken: number, permits: number} & Record<string, unknown>, {op, n}) => (typeof s[op as string] === 'function' ? (s[op as string] as (n: number) => unknown)(n as number) : s[op as string]),
    observe: (s: {taken: number, permits: number}) => ({taken: s.taken, permits: s.permits}),
  }, {params: rand => ({permits0: rand(4)}), draw: rand => ({op: ops[rand(ops.length)]!, n: rand(6) - 1}), runs, depth: 16})])
}

// The store: one key, the refill rate R; time moving on by parts of R and whole Rs, and sometimes back.
const clock = (rand: Rand, t: {now: number}) => { const d = rand(8); t.now = Math.max(0, d === 0 ? t.now - rand(R) : d < 4 ? t.now + rand(R) : t.now + R * rand(3)); return t.now }
const store = Effect.gen(function* () { return yield* RateLimiter.RateLimiterStore }).pipe(Effect.provide(RateLimiter.layerStoreMemory))
type Store = RateLimiter.RateLimiterStore['Service']
const tf = {now: 0}, tt = {now: 0}
results.push(['RateLimiter fixedWindow (4.0.7)', conforms(fixedWindow(), {
  effect, now: 'now', make: () => { tf.now = 0; return store },
  request: (s: Store, {n}, {limit, given}) => s.fixedWindow({key: 'k', tokens: n as number, refillRate: Duration.millis(R), limit: given ? limit as number : undefined}),
  observe: (_, [count, ttl]: readonly [number, number]) => ({returned: count, ttl}),
}, {params: rand => ({limit: rand(4), given: rand(4) > 0}), draw: rand => ({n: rand(3), now: clock(rand, tf)}), runs, depth: 16})])
results.push(['RateLimiter tokenBucket (4.0.7)', conforms(tokenBucket(), {
  effect, now: 'now', make: () => { tt.now = 0; return store },
  request: (s: Store, {n}, {limit, overflow}) => s.tokenBucket({key: 'k', tokens: n as number, limit: limit as number, refillRate: Duration.millis(R), allowOverflow: overflow as boolean}),
  observe: (_, [remaining, elapsed]: readonly [number, number]) => ({remaining, elapsed}),
}, {params: rand => ({limit: rand(5), overflow: rand(3) === 0}), draw: rand => ({n: rand(3), now: clock(rand, tt)}), runs, depth: 16})])

// T3 Code's pause, the original file.
const COMMIT = '9826dbb9904b2591bfbf60d1317486b59132f56b', PATH = 'packages/source-control-core/src/server/SourceControlRateLimit.ts'
const code = await (await fetch(`https://raw.githubusercontent.com/pingdotgg/t3code/${COMMIT}/${PATH}`)).text()
const dir = mkdtempSync(join(tmpdir(), 't3code-'))
mkdirSync(join(dir, 'node_modules/@t3tools/contracts'), {recursive: true})
symlinkSync(join(import.meta.dir, '../../../node_modules/effect'), join(dir, 'node_modules/effect'))
writeFileSync(join(dir, 'node_modules/@t3tools/contracts/package.json'), '{"name":"@t3tools/contracts","type":"module","main":"index.ts","types":"index.ts"}')
writeFileSync(join(dir, 'node_modules/@t3tools/contracts/index.ts'), 'import * as Schema from "effect/Schema"\nexport const SourceControlProviderKind = Schema.Literals(["github", "gitlab"])\nexport type SourceControlProviderKind = typeof SourceControlProviderKind.Type\n')
writeFileSync(join(dir, 'SourceControlRateLimit.ts'), code)
const t3 = await import(join(dir, 'SourceControlRateLimit.ts')) as {make: unknown}
type Svc = {check: (k: object, o?: object) => Effect.Effect<number, {retryAt: number}>, recordRateLimit: (i: object) => Effect.Effect<void>, recordSuccess: (i: object) => Effect.Effect<void>}
const key = {provider: 'github', host: 'api.github.com'}, tp = {now: 0, gen: 0}
results.push(['T3 Code SourceControlRateLimit (the original, 4.0.7)', conforms(pause(), {
  effect, now: 'now', make: () => { tp.now = 1_000; tp.gen = 0; return t3.make },
  request: (s: Svc, {op, allowPaused, lease, hinted, hint}) => (op === 'check' ? s.check(key, {allowPaused}) : op === 'recordRateLimit' ? s.recordRateLimit({...key, lease, retryAt: hinted ? hint : undefined}) : s.recordSuccess({...key, lease})),
  observe: (s: Svc, result, {op}) => Effect.gen(function* () {
    const generation = yield* s.check(key, {allowPaused: true}), paused = yield* Effect.flip(s.check(key)).pipe(Effect.map(e => e.retryAt), Effect.orElseSucceed(() => 0))
    tp.gen = generation
    return {generation, paused, ...(op === 'check' ? {result} : {})}
  }),
  view: (st, {now}) => ({generation: st.generation, paused: st.has && (st.retryAt as number) > (now as number) ? st.retryAt : 0, result: st.result}),
}, {draw: rand => {
  const d = rand(6); tp.now += d === 0 ? 0 : d < 3 ? rand(60_000) : d < 5 ? 30_000 * rand(4) : 900_000
  return {op: ['check', 'recordRateLimit', 'recordSuccess'][rand(3)]!, allowPaused: rand(4) === 0, lease: Math.max(0, tp.gen - rand(2)), hinted: rand(3) === 0, hint: Math.max(0, tp.now + rand(3) * 45_000 - 30_000), now: tp.now}
}, runs, depth: 16})])

// The refuted laws' counterexamples, replayed on the real code (research/realworld/triage/effect.json).
const run = <A>(e: Effect.Effect<A, unknown>) => Effect.runSync(e)
for (const [name, mk, E] of [['4.0.7', (n: number) => effect.Semaphore.makeUnsafe(n), effect], ['3.22.4', (n: number) => effect3.Effect.unsafeMakeSemaphore(n) as never as effect.Semaphore.Semaphore, effect3]] as const) {
  const run = (e: unknown) => (E.Effect.runSync as (e: unknown) => unknown)(e), andThen = (a: unknown, b: unknown) => (E.Effect.andThen as (a: unknown, b: unknown) => unknown)(a, b)
  const a = mk(2)
  console.log(`replayed, Semaphore ${name}: makeSemaphore(2), release(1) -> ${run(a.release(1))} free (more than the 2 permits)`)
  const b = mk(2)
  run(b.take(2)); console.log(`replayed, Semaphore ${name}: makeSemaphore(2), 2 taken, resize(1) -> ${run(andThen(b.resize(1), b.release(0)))} free (2 taken of 1 permit)`)
  const c = mk(2), d = mk(2)
  if (name === '4.0.7') console.log(`replayed, Semaphore ${name}: makeSemaphore(2), takeIfAvailable(-3) -> ${run(c.takeIfAvailable(-3))}, then ${run(c.release(0))} free`)
  console.log(`replayed, Semaphore ${name}: makeSemaphore(2), take(-3) -> ${run(d.take(-3))}, then ${run(d.release(0))} free`)
}
const s0 = run(store)
console.log(`replayed, RateLimiter fixedWindow (4.0.7): limit 0, tokens 1 twice -> ${JSON.stringify(run(s0.fixedWindow({key: 'k', tokens: 1, refillRate: Duration.millis(R), limit: 0})))}, ${JSON.stringify(run(s0.fixedWindow({key: 'k', tokens: 1, refillRate: Duration.millis(R), limit: 0})))} ([count, ttl]: the count past the limit given)`)

for (const [name, r] of results) console.log(`${r.failure ? 'FAIL' : 'ok  '} ${name}: ${r.checked} requests${r.failure ? `\n     ${r.failure}` : ''}`)
const x = extractEffect(code, {file: join(dir, 'SourceControlRateLimit.ts'), entry: 'make', effect})
console.log(`extractEffect on the original: ${x.ok ? 'read' : `refused at ${x.refusals[0]!.where}: ${x.refusals[0]!.what}`}`)
if (results.some(([, r]) => r.failure)) process.exit(1)
