// Probe: what the ReBAC shader's time goes to, by text variants of the emitted WGSL (M2 via Dawn, 1M users).
import {createDocumentStore, createProgramRunner, requestBatchDevice} from '../vendor/handwired/src/json-search/gpu/host.ts'
import {emitLoopWgsl} from '../vendor/handwired/src/json-search/loop-emit.ts'
import {derive, generate} from '../next/rebac/model.ts'
import {CELLS, buildRebac, userCells} from './rebac.ts'
const dawn = await import(process.env.DAWN_MODULE ?? 'webgpu') as {create: (flags: string[]) => GPU, globals: Record<string, unknown>}
Object.assign(globalThis, dawn.globals)
Object.defineProperty(globalThis.navigator, 'gpu', {value: dawn.create(process.platform === 'linux' ? ['backend=vulkan'] : []), configurable: true})
const users = 1_000_000
const {device} = await requestBatchDevice(users * CELLS * 4)
const org = generate(users, 2048, true)
const loop = buildRebac(org, derive(org), true)
const module = emitLoopWgsl(loop)
const store = await createDocumentStore(device, CELLS, users)
store.write(userCells(org), users)
const code = module.code
const loopStart = code.indexOf('for (var j')
const _before = code.slice(0, loopStart), _body = code.slice(loopStart)
const ufLoad = /let (b_w\d+): u32 = shared_values\[(\d+)u \+ j\];\n(?![\s\S]*let b_w\d+: u32 = shared_values\[\d+u \+ j\])/
const variants: Record<string, (c: string) => string> = {
  as_emitted: c => c,
  // The /finance read gone (the last table read in the loop).
  no_uf_read: c => c.replace(ufLoad, 'let $1: u32 = 0u;\n'),
  // The /finance read only when the object is seen, as the hand shader does.
  uf_read_if_seen: c => { const m = ufLoad.exec(c)!; const sees = /let (b_w\d+): u32 = \(b_w\d+\) \| \(b_w\d+\);\n(?=let b_w\d+: u32 = shared_values)/.exec(c); return sees ? c.replace(ufLoad, `let ${m[1]}: u32 = select(0u, shared_values[${m[2]}u + j], ${sees[1]} != 0u);\n`) : c },
}
for (const [name, edit] of Object.entries(variants)) {
  const runner = await createProgramRunner(device, {...module, code: edit(code)}, loop.sharedValues, store)
  const run = () => runner.evaluate({count: users, readbacks: [{group: 0, firstDocument: 0, documentCount: users}]})
  await run()
  const ts: number[] = []
  for (let i = 0; i < 9; i++) { const t0 = performance.now(); await run(); ts.push(performance.now() - t0) }
  ts.sort((a, b) => a - b)
  console.log(name.padEnd(14), ts[4]!.toFixed(2), 'ms')
  runner.destroy()
}
process.exit(0)
