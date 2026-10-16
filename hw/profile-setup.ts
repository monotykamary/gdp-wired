// Where the setup of the Handwired synthesis kernels goes: building the word circuits, writing their WGSL, and the GPU's
// shader compile (createProgramRunner), per kernel of the rank-pair and single-rank cases.
//   DAWN_MODULE=<webgpu>/index.js bun profile-setup.ts
import {fromLoop} from '../synth/compile.ts'
import {packForms, rankTemplates} from '../synth/more.ts'
import {pairCases} from '../synth/models-more.ts'
import {rankCases} from '../synth/models.ts'
import {templates} from '../synth/synth.ts'
import {emitLoopWgsl} from '../vendor/handwired/src/json-search/loop-emit.ts'
import {compileKernel} from './synth.ts'
import {compileMoreKernel} from './synth-more.ts'

const dawn = await import(process.env.DAWN_MODULE ?? 'webgpu') as {create: (flags: string[]) => GPU, globals: Record<string, unknown>}
Object.assign(globalThis, dawn.globals)
Object.defineProperty(globalThis.navigator, 'gpu', {value: dawn.create(process.platform === 'linux' ? ['backend=vulkan'] : []), configurable: true})
const host = await import('../vendor/handwired/src/json-search/gpu/host.ts')
const {device} = await host.requestBatchDevice(65535 * 64 * 4)
const store = await host.createDocumentStore(device, 1, 1024)
const time = async (what: string, build: () => {loop: any}) => {
  const t0 = performance.now(), {loop} = build(), t1 = performance.now()
  const module = emitLoopWgsl(loop), t2 = performance.now()
  const r = await host.createProgramRunner(device, module, loop.sharedValues, store), t3 = performance.now()
  r.destroy()
  console.log(`${what.padEnd(48)} build ${(t1 - t0).toFixed(0).padStart(6)} ms  wgsl ${(t2 - t1).toFixed(0).padStart(5)} ms  compile ${(t3 - t2).toFixed(0).padStart(6)} ms  (${module.code.length.toLocaleString()} chars, shared ${loop.sharedValues.length.toLocaleString()})`)
}
for (const c of pairCases.slice(0, 1)) {
  const p = fromLoop(c.l, c.laws), forms = rankTemplates(p, c)
  const pairs = forms.slice(0, 117).flatMap(a => forms.map(b => [a, b]))
  await time(`${c.what.slice(0, 20)}: nonincreasing`, () => compileMoreKernel(p, c.box, forms.length, 'nonincreasing'))
  await time(`${c.what.slice(0, 20)}: guards`, () => compileMoreKernel(p, c.box, forms.length, 'guards'))
  await time(`${c.what.slice(0, 20)}: rankPair (${pairs.length})`, () => compileMoreKernel(p, c.box, pairs.length, 'rankPair'))
  void packForms
}
for (const c of rankCases) {
  const p = fromLoop(c.l, c.laws), forms = templates(p, c)
  await time(`${c.what.slice(0, 20)}: rank kill (${forms.length})`, () => compileKernel(p, c.box, forms.length, 'kill'))
}
process.exit(0)
