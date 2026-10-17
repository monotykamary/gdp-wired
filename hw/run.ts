// The search suite through the Handwired fork on a GPU: each machine and law compiled to a loop program of word stages
// (compile.ts), written as WGSL by Handwired's loop-emit.ts and run by its createProgramRunner. Every counterexample is
// replayed by the interpreter. With --hand, the hand-written kernel of search/compile.ts runs the same searches on the
// same device, for comparison.
//   DAWN_MODULE=<webgpu>/index.js bun run.ts [--hand] [--big] [--steps] [--out result.json]
// --steps adds the step-law and k-step-law searches (step-searches.ts), each three steps deeper than its CPU check.
import {writeFileSync} from 'node:fs'
import {createDocumentStore, createKernelRunner, createProgramRunner, requestBatchDevice} from '../vendor/handwired/src/json-search/gpu/host.ts'
import {emitLoopWgsl} from '../vendor/handwired/src/json-search/loop-emit.ts'
import {CHUNK as HAND_CHUNK, replay, size, wgsl} from '../search/compile.ts'
import {searches} from '../search/models.ts'
import {compile, decodeBest, lowSteps, setRange} from './compile.ts'
import {stepSearches} from './step-searches.ts'
import {isStepLaw} from '../core/watch.ts'

const has = (f: string) => process.argv.includes(f), arg = (f: string) => { const i = process.argv.indexOf(f); return i < 0 ? undefined : process.argv[i + 1] }
const dawn = await import(process.env.DAWN_MODULE ?? 'webgpu') as {create: (flags: string[]) => GPU, globals: Record<string, unknown>}
Object.assign(globalThis, dawn.globals)
Object.defineProperty(globalThis.navigator, 'gpu', {value: dawn.create(process.platform === 'linux' ? ['backend=vulkan'] : []), configurable: true})
const docsPerDispatch = 65535 * 64
const batch = await requestBatchDevice(docsPerDispatch * 4)
const device = batch.device
console.log(`adapter ${JSON.stringify(batch.adapterInfo)}`)
const store = await createDocumentStore(device, 1, docsPerDispatch)
const chunk = Number(arg('--chunk') ?? 64)
const round = (v: number) => Math.round(v * 1000) / 1000
const reps = Number(arg('--reps') ?? 1) // the median of this many timed runs, after a warm-up
const timed = async <T>(f: () => Promise<T>) => {
  const times: number[] = []
  let result: T | undefined
  for (let r = 0; r < reps; r++) { const t0 = performance.now(); result = await f(); times.push(performance.now() - t0) }
  times.sort((a, b) => a - b)
  return {result: result!, ms: times[Math.floor(times.length / 2)]!}
}

type Job = {s: {m: (typeof searches)[number]['m'], law: (typeof searches)[number]['law'] | (typeof stepSearches)[number]['law']}, space: {depth: number, bound: number}, what: string}
const jobs: Job[] = [...searches.map(s => ({s, space: s.space, what: s.what})), {s: searches[2]!, space: {depth: 9, bound: 2}, what: searches[2]!.what + ' (depth 9)'}]
if (has('--steps')) jobs.push(...stepSearches.map(s => ({s, space: {...s.space, depth: s.space.depth + 3}, what: `${s.what} (depth ${s.space.depth + 3})`})))
if (has('--big')) jobs.push({s: searches[2]!, space: {depth: 10, bound: 2}, what: searches[2]!.what + ' (depth 10)'}, {s: searches[1]!, space: {depth: 10, bound: 2}, what: searches[1]!.what + ' (depth 10)'}, {s: searches[2]!, space: {depth: 11, bound: 2}, what: searches[2]!.what + ' (depth 11)'}, {s: searches[2]!, space: {depth: 8, bound: 3}, what: searches[2]!.what + ' (bound 3, depth 8)'})
if (has('--huge')) jobs.push({s: searches[2]!, space: {depth: 12, bound: 2}, what: searches[2]!.what + ' (depth 12)'})
const only = arg('--only') // run the jobs whose name contains this
const results: Record<string, unknown>[] = []
for (const {s, space, what} of jobs.filter(job => only === undefined || job.what.includes(only))) {
  const total = size(s.m, space)
  // Slices: perSlice candidates each (the index's digits), `slices` of them (the later steps' requests).
  const forced = Number(arg('--low') ?? space.depth) // --low n: slice after n steps, to test slicing on a small space
  const K = space.bound + 1, low = lowSteps(s.m, space, forced)
  const perSlice = K ** (s.m.params.length + s.m.inputs.length * low), slices = total / perSlice
  const loop = compile(s.m, s.law, space, chunk, forced)
  const module = emitLoopWgsl(loop)
  const compileStarted = performance.now()
  const runner = await createProgramRunner(device, module, loop.sharedValues, store)
  const compileMs = performance.now() - compileStarted
  const run = async () => {
    let best: {depth: number, index: number} | undefined
    for (let hi = 0; hi < slices; hi++) for (let base = 0; base < perSlice; base += docsPerDispatch * chunk) {
      const count = Math.min(docsPerDispatch, Math.ceil((perSlice - base) / chunk))
      const {outputs} = await runner.evaluate({count, shared: setRange(loop, base, perSlice, hi), readbacks: [{group: 0, firstDocument: 0, documentCount: count}]})
      const words = new Uint32Array(outputs[0]!.buffer, outputs[0]!.byteOffset, count)
      for (let d = 0; d < count; d++) {
        const found = decodeBest(words[d]!, base, d, chunk)
        if (!found) continue
        const index = hi * perSlice + found.index // the candidate's index over the whole space
        if (!best || found.depth < best.depth || (found.depth === best.depth && index < best.index)) best = {depth: found.depth, index}
      }
    }
    return best
  }
  await run()
  const {result: best, ms: gpuMs} = await timed(run)
  runner.destroy()
  const confirmed = best ? replay(s.m, s.law, space, best.index) : undefined
  const entry: Record<string, unknown> = {what, space, candidates: total, slices, statements: module.statementCount, compileMs: round(compileMs), handwiredMs: round(gpuMs),
    found: best ? {...best, ...confirmed, replayed: confirmed !== undefined && confirmed.trace.length === best.depth} : null}
  if (has('--hand') && slices === 1 && !isStepLaw(s.law)) {
    // search/compile.ts's hand-written shader on the same device.
    const kernel = await createKernelRunner(device, {code: wgsl(s.m, s.law, space), workgroupSize: 64, tableLength: 2, cellsPerDocument: 1}, store, 1)
    const handRun = async () => {
      let hand: {depth: number, index: number} | undefined
      for (let base = 0; base < total; base += docsPerDispatch * HAND_CHUNK) {
        const threads = Math.min(docsPerDispatch, Math.ceil((total - base) / HAND_CHUNK))
        const out = await kernel.evaluate({count: threads, tables: new Uint32Array([base, total])})
        for (let i = 0; i < threads; i++) {
          const v = out.counts[i]!
          if (v === 0) continue
          const depth = Math.floor((v - 1) / HAND_CHUNK), index = base + i * HAND_CHUNK + ((v - 1) % HAND_CHUNK)
          if (!hand || depth < hand.depth || (depth === hand.depth && index < hand.index)) hand = {depth, index}
        }
      }
      return hand
    }
    await handRun()
    const {result: hand, ms: handMs} = await timed(handRun)
    entry.handMs = round(handMs)
    entry.handAgrees = JSON.stringify(hand) === JSON.stringify(best)
    kernel.destroy()
  }
  results.push(entry)
  console.log(JSON.stringify(entry))
}
const out = arg('--out')
if (out) writeFileSync(out, JSON.stringify({adapter: batch.adapterInfo, chunk, results}, null, 1))
process.exit(0)
