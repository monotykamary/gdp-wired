// Effect's concurrency primitives, modelled once (gdp-wired/effect, core/effect-prims.ts): for the suite (`bun
// examples/effect-queue.ts`) and core/effect-queue.test.ts.
//   - the primitives' own rules: a Queue of each strategy (bounded, dropping, sliding, unbounded) for every capacity,
//     a Semaphore for every number of permits; their laws proven (a queue holds at most its capacity; nothing is lost:
//     what comes in comes by an offer at the tail, what leaves is the oldest, to the take or poll whose answer it is, to a
//     slide or a shutdown; what is held stays; at most the permits are taken), and each run beside Effect's own primitive
//     on random operations, each on a fiber of its own, on Effect 4 and Effect 3;
//   - a worker pool (examples/effect-pool.ts on Effect 4, the same pool on Effect 3): a bounded job queue, a Semaphore of
//     2 around each job; read as every fiber's steps (a worker's take, its job, its work and its release each a step),
//     its laws proven: every job waiting costs 1 to 10, the work done never goes negative, no permit is given back that
//     wasn't taken (the semaphore's use law, on the lemma that each fiber gives back only what it took);
//   - broken: a cancel that gives a permit back without taking one. The use law is refuted by a run (fiber 0: cancel()),
//     and on Effect's runtime, after one cancel, three workers hold the pool's two permits at once.
import {readFileSync} from 'node:fs'
import {fileURLToPath} from 'node:url'
import * as effect from 'effect'
import * as effect3 from 'effect3'
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Any = any
import {type Law} from '../core/machine.ts'
import {proveRule, proveSteps} from '../core/dsl.ts'
import {type Extraction} from '../core/extract.ts'
import {extractEffect, fiberRun, primitiveConforms, primitiveLaws, primitiveRule, withLemmas} from '../core/effect.ts'
import type {Spec} from '../core/effect-prims.ts'
import {buildLaw, lawsIn} from '../core/laws.ts'
import {inProject} from './effect-retry.ts'

export const poolFile = fileURLToPath(new URL('./effect-pool.ts', import.meta.url))
const CANCEL = `  // Stops a worker early: gives its permit back (without having taken one).
  const cancel = Effect.fn('Pool.cancel')(function* () {
    yield* workers.release(1)
  })
`
// The pool on Effect 4, as written; broken, with a cancel that releases a permit it never took.
export const pool4 = (bug?: 'release without acquire') => {
  const code = readFileSync(poolFile, 'utf8')
  return bug ? code.replace('  return {submit, work, backlog}', `${CANCEL}  return {submit, work, backlog, cancel}`) : code
}
// The pool on Effect 3: Effect.makeSemaphore, a Data.TaggedError, no backlog (Effect 3's Queue.size counts the fibers
// waiting on the queue, which the rule doesn't hold: refused).
export const pool3 = (bug?: 'release without acquire') => pool4(bug).replace("import {Effect, Queue, Ref, Schema, Semaphore} from 'effect'", "import {Data, Effect, Queue, Ref} from 'effect'")
  .replace("export class BadJob extends Schema.TaggedError<BadJob>()('BadJob', {cost: Schema.Number}) {}", "export class BadJob extends Data.TaggedError('BadJob')<{readonly cost: number}> {}")
  .replace('Semaphore.make(2)', 'Effect.makeSemaphore(2)').replace(/  const backlog = [\s\S]*?\n {2}\}\)\n/, '').replace(/backlog(, )?/, '').replace(', }', '}')
export const readPool = (v: 3 | 4, bug?: 'release without acquire'): {x: Extraction, file: string} => {
  const file = v === 4 && !bug ? poolFile : inProject(v, 'pool.ts', v === 4 ? pool4(bug) : pool3(bug))
  return {x: extractEffect(file, {entry: 'make'}), file}
}
// The laws as the pool's comments state them, read through the extraction's names.
export const poolLaws = (x: Extraction): Law[] => lawsIn(readFileSync(poolFile, 'utf8')).filter(l => l.expr).map(l => buildLaw(x, l).law as Law)
// The pool's laws, each proven with its rule's invariants and the lemmas of its primitives' use proven first.
export function provePool(x: Extraction, ms = 60_000): {lemmas: string[], verdicts: [string, Any][]} {
  const w = withLemmas(x, {ms})
  return {lemmas: w.proven, verdicts: poolLaws(w.x).map(l => [l.name, proveRule(w.x.rule!, [...w.x.invariants ?? [], l], {search: {ms}})])}
}
// Three workers at once on Effect's runtime (real fibers; a cancel first, broken), the most that held a permit at once:
// the pool as written, its job counted in and out around the work.
export async function racePool(v: 3 | 4, file: string, cancel: boolean): Promise<number> {
  const code = `${readFileSync(file, 'utf8').replace("yield* Effect.sleep('10 millis')", "busy++; peak = Math.max(peak, busy); yield* Effect.sleep('10 millis'); busy--")}
let busy = 0, peak = 0
export const race = () => Effect.runPromise(Effect.gen(function* () {
  const pool = yield* make
  ${cancel ? 'yield* (pool as any).cancel()' : ''}
  for (let i = 0; i < 3; i++) yield* pool.submit(1)
  yield* Effect.all([pool.work(), pool.work(), pool.work()], {concurrency: 'unbounded'})
  return peak
}))
`
  const mod = await import(inProject(v, 'race.ts', code)) as {race: () => Promise<number>}
  return mod.race()
}
export const SPECS: Spec[] = [{kind: 'queue', strategy: 'bounded'}, {kind: 'queue', strategy: 'dropping'}, {kind: 'queue', strategy: 'sliding'}, {kind: 'queue', strategy: 'unbounded'}, {kind: 'semaphore'}]
export const specName = (s: Spec) => (s.kind === 'queue' ? `Queue (${s.strategy})` : 'Semaphore')
// A primitive's canonical rule on Effect v, read where its imports resolve to that Effect.
export const primRule = (spec: Spec, v: 3 | 4) => primitiveRule(spec, v === 4 ? effect : effect3, {file: inProject(v, 'prim.ts', '')})

if (import.meta.main) {
  const results: [string, boolean, boolean][] = [], runs: string[] = []
  for (const v of [4, 3] as const) {
    const E = v === 4 ? effect : effect3
    for (const spec of SPECS) {
      const x = primRule(spec, v), {laws, stepLaws, refuted} = primitiveLaws(x, spec)
      results.push([`${specName(spec)} (Effect ${v}): its rule read and checked (${x.evidence?.requests} requests)`, x.ok, true])
      results.push([`${specName(spec)} (Effect ${v}): ${laws.map(l => l.name).join('; ')}`, proveRule(x.rule!, laws).proven, true])
      for (const sl of stepLaws) results.push([`${specName(spec)} (Effect ${v}): ${sl.name}`, proveSteps(x.rule!, laws, [sl]).proven, true])
      for (const l of refuted) results.push([`${specName(spec)} (Effect ${v}): ${l.name} (Effect's own: a release is unchecked)`, proveRule(x.rule!, [...laws, l]).proven, false])
      const c = await primitiveConforms(spec, E, {x, runs: 40})
      results.push([`${specName(spec)} (Effect ${v}): the rule beside Effect's own on random operations and fibers (${c.checked} completions, ${c.blocked} found waiting, ${c.interrupted} interrupted${c.failure ? `; ${c.failure}` : ''})`, !c.failure, true])
    }
    const {x} = readPool(v)
    results.push([`pool (Effect ${v}): read as every fiber's steps and checked on the runtime (${x.evidence?.requests} requests)`, x.ok && /every fiber/.test(x.rule?.machine.name ?? ''), true])
    const p = provePool(x)
    for (const [name, verdict] of p.verdicts) results.push([`pool (Effect ${v}): ${name}`, verdict.proven && verdict.checked, true])
    const b = readPool(v, 'release without acquire'), use = poolLaws(b.x).at(-1)!
    const bv = proveRule(b.x.rule!, [...b.x.invariants ?? [], use])
    results.push([`pool with a cancel that gives back a permit it never took (Effect ${v}): ${use.name}`, bv.proven, false])
    const peak = await racePool(v, b.file, true), peak0 = await racePool(v, b.file, false)
    if (bv.run) runs.push(`release without acquire (Effect ${v}): ${fiberRun(b.x, bv.run).join('; ')}; on the runtime, three workers after one cancel: ${peak} hold a permit at once (${peak0} without the cancel)`)
    results.push([`pool with a cancel (Effect ${v}): on the runtime, at most two workers at once after a cancel`, peak <= 2, false])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  for (const r of runs) console.log(`     ${r}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
