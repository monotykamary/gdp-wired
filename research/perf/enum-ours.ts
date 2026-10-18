// The predicate enumeration through the Handwired fork on this machine's GPU, with every setup cost reported:
// process start to device, building and writing the WGSL, the pipeline compile (createProgramRunner), the first
// evaluation, and the median of 9 warm evaluations (dispatch + readback of one packed word per 2,048 worlds).
//   DAWN_MODULE=<webgpu>/index.js bun enum-ours.ts [k ...]
import {readFileSync} from 'node:fs'
const t0 = performance.now()
const {createDocumentStore, createProgramRunner, requestBatchDevice} = await import('../../vendor/handwired/src/json-search/gpu/host.ts')
const {emitLoopWgsl} = await import('../../vendor/handwired/src/json-search/loop-emit.ts')
const {buildEnum} = await import('../hw/enum.ts')
const dawn = await import(process.env.DAWN_MODULE ?? 'webgpu') as {create: (flags: string[]) => GPU, globals: Record<string, unknown>}
Object.assign(globalThis, dawn.globals)
Object.defineProperty(globalThis.navigator, 'gpu', {value: dawn.create(process.platform === 'linux' ? ['backend=vulkan'] : []), configurable: true})
const {device} = await requestBatchDevice(2 ** 20 * 4)
const store = await createDocumentStore(device, 1, 2 ** 20)
const deviceMs = performance.now() - t0 // includes bun start-up after process launch only from here: see the wall time
const expected = new Map(readFileSync(new URL('../enum/js.jsonl', import.meta.url), 'utf8').trim().split('\n').map(l => JSON.parse(l)).map((r: any) => [r.k, r]))
const ks = process.argv.slice(2).map(Number)
const r3 = (v: number) => Math.round(v * 100) / 100
console.log(JSON.stringify({deviceMs: r3(deviceMs)}))
for (const k of ks.length ? ks : [24, 28, 30, 31]) {
  let t = performance.now()
  const {loop, documents} = buildEnum(k, true)
  const module = emitLoopWgsl(loop)
  const buildMs = performance.now() - t
  t = performance.now()
  const runner = await createProgramRunner(device, module, loop.sharedValues, store)
  const compileMs = performance.now() - t
  const evaluate = () => runner.evaluate({count: documents, readbacks: [{group: 0, firstDocument: 0, documentCount: documents}]})
  t = performance.now()
  const {outputs} = await evaluate()
  const firstMs = performance.now() - t
  const packed = new Uint32Array(outputs[0]!.buffer, outputs[0]!.byteOffset, documents)
  let r = 0, v = 0
  for (let d = 0; d < documents; d++) { r += packed[d]! >>> 12; v += packed[d]! & 4095 }
  const want = expected.get(k)!
  const times: number[] = []
  for (let i = 0; i < 9; i++) { const s = performance.now(); await evaluate(); times.push(performance.now() - s) }
  runner.destroy()
  console.log(JSON.stringify({k, agree: r === want.reachable && v === want.violations, buildMs: r3(buildMs), compileMs: r3(compileMs), firstMs: r3(firstMs), warmMedianMs: r3(times.sort((a, b) => a - b)[4]!), sinceStartMs: r3(performance.now() - t0)}))
}
process.exit(0)
