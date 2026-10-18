// The search suite on whatever WebGPU navigator.gpu gives: Chrome's (gpu-page.ts) or Dawn's node bindings (dawn-run.ts,
// an NVIDIA GPU on Modal). Spaces past 2^31 candidates run in slices: the low digits (params and the first steps'
// requests) are the dispatch index as in search/page.ts, and the high digits (the last steps' requests) are one number
// per slice, which the shader takes from tables[2] when it reaches those steps; compile.ts's code is otherwise unchanged.
// Every reported counterexample is replayed by the interpreter, so the GPU stays untrusted.
import {createDocumentStore, createKernelRunner, requestBatchDevice} from '../../vendor/handwired/src/json-search/gpu/host.ts'
import {CHUNK, type Space, replay, size, wgsl} from '../search/compile.ts'
import {searches} from '../search/models.ts'

export type Job = {search: number, what?: string, space?: Space, warm?: boolean, sliceAt?: number} // sliceAt: a smaller slice, to test slicing
const round = (v: number) => Math.round(v * 1000) / 1000

export async function runSuite(jobs: Job[], report: Record<string, unknown>, log: (line: string) => void, flush: () => Promise<unknown> = async () => {}) {
  const results: Record<string, unknown>[] = []
  report['results'] = results
  const perDispatch = 65535 * 64 // threads
  const batch = await requestBatchDevice(perDispatch * 4)
  report['adapter'] = batch.adapterInfo
  report['adapterLimits'] = batch.adapterLimits
  log(`adapter ${JSON.stringify(batch.adapterInfo)}`)
  await flush()
  const {device} = batch
  const store = await createDocumentStore(device, 1, perDispatch)
  for (const job of jobs) {
    const s = searches[job.search]!
    const space = job.space ?? s.space
    const what = job.what ?? s.what
    const total = size(s.m, space)
    const K = space.bound + 1, P = s.m.params.length, I = s.m.inputs.length
    // The most steps whose requests (with the params) fit in one slice of at most 2^31 candidates.
    let low = space.depth
    while (low > 0 && K ** (P + I * low) > (job.sliceAt ?? 2 ** 31)) low--
    const perSlice = K ** (P + I * low), slices = K ** (I * (space.depth - low))
    let code = wgsl(s.m, s.law, space)
    if (low < space.depth) {
      const loop = `for (var t = 0u; t < ${space.depth}u; t++) {`
      if (!code.includes(loop)) throw new Error('unexpected shader text')
      code = code.replace(loop, `${loop}\n    if (t == ${low}u) { rest = tables[2]; }`)
    }
    const compileStarted = performance.now()
    const runner = await createKernelRunner(device, {code, workgroupSize: 64, tableLength: 3, cellsPerDocument: 1}, store, 1)
    const compileMs = performance.now() - compileStarted
    const run = async () => {
      let best: {depth: number, index: number} | undefined
      for (let hi = 0; hi < slices; hi++) {
        for (let base = 0; base < perSlice; base += perDispatch * CHUNK) {
          const threads = Math.min(perDispatch, Math.ceil((perSlice - base) / CHUNK))
          const out = await runner.evaluate({count: threads, tables: new Uint32Array([base, perSlice, hi])})
          for (let i = 0; i < threads; i++) {
            const value = out.counts[i]!
            if (value === 0) continue
            const depth = Math.floor((value - 1) / CHUNK), index = hi * perSlice + base + i * CHUNK + ((value - 1) % CHUNK)
            if (!best || depth < best.depth || (depth === best.depth && index < best.index)) best = {depth, index}
          }
        }
      }
      return best
    }
    if (job.warm !== false) await run()
    const started = performance.now()
    const best = await run()
    const gpuMs = performance.now() - started
    const confirmed = best ? replay(s.m, s.law, space, best.index) : undefined
    const entry = {what, space, candidates: total, slices, perSlice, compileMs: round(compileMs), gpuMs: round(gpuMs), candidatesPerSecond: Math.round(total / (gpuMs / 1000)),
      found: best ? {...best, ...confirmed, replayed: confirmed !== undefined && confirmed.trace.length === best.depth} : null}
    results.push(entry)
    log(JSON.stringify(entry))
    await flush()
    runner.destroy()
  }
  store.destroy()
  return report
}
