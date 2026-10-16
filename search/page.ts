// Every candidate history of each search on the GPU, the least failing one replayed by the interpreter.
import {createDocumentStore, createKernelRunner, requestBatchDevice} from '../vendor/handwired/src/json-search/gpu/host.ts'
import {createReporter, round} from '../vendor/handwired/lab/json-search/gpu/measure.ts'
import {CHUNK, replay, size, wgsl} from './compile.ts'
import {searches} from './models.ts'

const {report, post, log} = createReporter()
const results: Record<string, unknown>[] = []
report['results'] = results
try {
  const perDispatch = 65535 * 64 // threads
  const {device} = await requestBatchDevice(perDispatch * 4)
  const store = await createDocumentStore(device, 1, perDispatch)
  for (const s of [...searches, {...searches[2]!, what: searches[2]!.what + ' (depth 9)', space: {depth: 9, bound: 2}}]) {
    const total = size(s.m, s.space)
    const runner = await createKernelRunner(device, {code: wgsl(s.m, s.law, s.space), workgroupSize: 64, tableLength: 2, cellsPerDocument: 1}, store, 1)
    const run = async () => {
      let best: {depth: number, index: number} | undefined
      for (let base = 0; base < total; base += perDispatch * CHUNK) {
        const threads = Math.min(perDispatch, Math.ceil((total - base) / CHUNK))
        const out = await runner.evaluate({count: threads, tables: new Uint32Array([base, total])})
        for (let i = 0; i < threads; i++) {
          const value = out.counts[i]!
          if (value === 0) continue
          const depth = Math.floor((value - 1) / CHUNK), index = base + i * CHUNK + ((value - 1) % CHUNK)
          if (!best || depth < best.depth || (depth === best.depth && index < best.index)) best = {depth, index}
        }
      }
      return best
    }
    await run() // warm-up
    const started = performance.now()
    const best = await run()
    const gpuMs = performance.now() - started
    const confirmed = best ? replay(s.m, s.law, s.space, best.index) : undefined
    const entry = {what: s.what, candidates: total, gpuMs: round(gpuMs), found: best ? {...best, ...confirmed, replayed: confirmed !== undefined && confirmed.trace.length === best.depth} : null}
    results.push(entry)
    log(JSON.stringify(entry))
    await post(false)
    runner.destroy()
  }
} catch (error) {
  report['error'] = String(error instanceof Error ? error.stack : error)
  log(`error: ${String(error)}`)
}
await post(true)
