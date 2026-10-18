// The Handwired word kernels (synth.ts) against synth/compile.ts's JS twin on the small boxes, both on the CPU: every
// round's kill set must be the same, from the same alive set, through whole Houdini runs (history, then rounds of
// region + kill; ranks from all alive).
//   bun check-synth.ts [--gpu]     --gpu: the Handwired kernels on Dawn's GPU instead of Handwired's CPU loop runner
import {fromLoop, fromMachine, points} from '../synth/compile.ts'
import {allAlive, atStart, countAlive, cpuEvaluator, templates} from '../synth/synth.ts'
import {invariantCases, rankCases} from '../synth/models.ts'
import {hwEvaluator} from './synth.ts'

let target: Parameters<typeof hwEvaluator>[0] = {kind: 'cpu'}
if (process.argv.includes('--gpu')) {
  const dawn = await import(process.env.DAWN_MODULE ?? 'webgpu') as {create: (flags: string[]) => GPU, globals: Record<string, unknown>}
  Object.assign(globalThis, dawn.globals)
  Object.defineProperty(globalThis.navigator, 'gpu', {value: dawn.create(process.platform === 'linux' ? ['backend=vulkan'] : []), configurable: true})
  const host = await import('../../vendor/handwired/src/json-search/gpu/host.ts')
  const batch = await host.requestBatchDevice(65535 * 64 * 4)
  target = {kind: 'gpu', device: batch.device, host}
}
const same = (a: number[], b: number[]) => a.length === b.length && [...a].sort((x, y) => x - y).every((x, i) => x === [...b].sort((x2, y2) => x2 - y2)[i])
let failures = 0
const compare = async (what: string, p: ReturnType<typeof fromMachine>, box: Record<string, number>, forms: ReturnType<typeof templates>, alive: Uint32Array, once: boolean) => {
  const twin = cpuEvaluator(p, box, forms), hw = await hwEvaluator(target, p, box, forms)
  let rounds = 0, killedTotal = 0
  const t0 = performance.now()
  for (;;) {
    const a = await twin.round(alive.slice()), b = await hw.round(alive.slice())
    if (!same(a, b)) { failures++; console.log(`  ${what}: round ${rounds + 1} differs: twin ${a.length}, handwired ${b.length}`); break }
    rounds++
    killedTotal += a.length
    if (a.length === 0) break
    for (const j of a) alive[j >>> 5]! &= ~(1 << (j & 31))
    if (once) break
  }
  hw.destroy?.()
  console.log(`  ${what.padEnd(58)} ${rounds} rounds agree, ${killedTotal} killed, ${countAlive(alive, forms.length)} left (${Math.round(performance.now() - t0)} ms)`)
  return alive
}
console.log(`Invariants (small boxes, ${target.kind === 'cpu' ? 'Handwired loop runner' : 'Handwired on the GPU'} vs the JS twin)`)
for (const c of invariantCases) {
  const p = fromMachine(c.m), forms = templates(p, c), box = c.small
  const start = atStart(c.m, box, forms)
  const hp = {...p, kind: 'history' as const, depth: Math.min(c.depth, 6)}
  const hbox = {...box, ...Object.fromEntries(Object.entries(c.history).map(([v, b]) => [v, Math.min(b, 3)]))}
  const reach = await compare(`${c.what}: ${points(hp, hbox).toLocaleString()} histories`, hp, hbox, forms, start, true)
  await compare(`${c.what}: region + kill, ${points(p, box).toLocaleString()} points`, p, box, forms, reach, false)
}
console.log('Ranks')
for (const c of rankCases) {
  const p = fromLoop(c.l, c.laws), forms = templates(p, c)
  await compare(`${c.what}: ${points(p, c.small).toLocaleString()} points`, p, c.small, forms, allAlive(forms.length), false)
}
console.log(failures === 0 ? 'every round agrees' : `${failures} disagreements`)
process.exit(failures === 0 ? 0 : 1)
