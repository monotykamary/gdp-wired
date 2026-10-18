// Probe: which differences between the Handwired shader and the hand-written one cost time. Variants of the emitted
// WGSL, edited as text, on the enumeration at k = 31 (M2 via Dawn).
import {createDocumentStore, createProgramRunner, requestBatchDevice} from '../../vendor/handwired/src/json-search/gpu/host.ts'
import {emitLoopWgsl} from '../../vendor/handwired/src/json-search/loop-emit.ts'
import {buildEnum} from './enum.ts'
const dawn = await import(process.env.DAWN_MODULE ?? 'webgpu') as {create: (flags: string[]) => GPU, globals: Record<string, unknown>}
Object.assign(globalThis, dawn.globals)
Object.defineProperty(globalThis.navigator, 'gpu', {value: dawn.create(process.platform === 'linux' ? ['backend=vulkan'] : []), configurable: true})
const {device} = await requestBatchDevice(2 ** 22)
const k = Number(process.argv[2] ?? 31)
const {loop, documents} = buildEnum(k, true)
const module = emitLoopWgsl(loop)
const store = await createDocumentStore(device, 1, documents)
const variants: Record<string, (code: string) => string> = {
  as_emitted: c => c,
  const_positions: c => c.replace('let positions: u32 = 2048u;', 'const positions: u32 = 2048u;'),
  literal_bound: c => c.replace('j < positions', 'j < 2048u'),
}
for (const [name, edit] of Object.entries(variants)) {
  const code = edit(module.code)
  const runner = await createProgramRunner(device, {...module, code}, loop.sharedValues, store)
  const run = () => runner.evaluate({count: documents, readbacks: [{group: 0, firstDocument: 0, documentCount: documents}]})
  await run()
  const ts: number[] = []
  for (let i = 0; i < 9; i++) { const t0 = performance.now(); await run(); ts.push(performance.now() - t0) }
  ts.sort((a, b) => a - b)
  const timed = await runner.evaluate({count: documents, timestamps: runner.hasTimestamps, readbacks: [{group: 0, firstDocument: 0, documentCount: documents}]})
  console.log(name.padEnd(20), ts[4]!.toFixed(2), 'ms', timed.passMs !== undefined ? `pass ${timed.passMs.toFixed(2)} ms` : '')
  runner.destroy()
}
process.exit(0)
