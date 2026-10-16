// The Handwired word kernels for rank pairs and map invariants (synth-more.ts) against synth/compile-more.ts's JS twin on
// the small boxes: every round's kill set must be the same, from the same alive set. Rank pairs: the nonincreasing round
// from all alive, then the pair round over (survivor × every rank); maps: rounds of region + kill from the start to the
// fixpoint.
//   bun check-synth-more.ts [--gpu]     --gpu: the Handwired kernels on Dawn's GPU instead of Handwired's CPU loop runner
import {type Form, type Problem, fromLoop, points} from '../synth/compile.ts'
import {type MoreKind, fromMapMachine} from '../synth/compile-more.ts'
import {mapAtStart, mapTemplates, moreEvaluator, packForms, rankTemplates} from '../synth/more.ts'
import {allAlive, countAlive} from '../synth/synth.ts'
import {mapCases, pairCases} from '../synth/models-more.ts'
import {type Target, moreHwEvaluator} from './synth-more.ts'

let target: Target = {kind: 'cpu'}
if (process.argv.includes('--gpu')) {
  const dawn = await import(process.env.DAWN_MODULE ?? 'webgpu') as {create: (flags: string[]) => GPU, globals: Record<string, unknown>}
  Object.assign(globalThis, dawn.globals)
  Object.defineProperty(globalThis.navigator, 'gpu', {value: dawn.create(process.platform === 'linux' ? ['backend=vulkan'] : []), configurable: true})
  const host = await import('../vendor/handwired/src/json-search/gpu/host.ts')
  const batch = await host.requestBatchDevice(65535 * 64 * 4)
  target = {kind: 'gpu', device: batch.device, host}
}
const sorted = (a: number[]) => [...a].sort((x, y) => x - y)
const same = (a: number[], b: number[]) => a.length === b.length && sorted(a).every((x, i) => x === sorted(b)[i])
let failures = 0
const compare = async (what: string, p: Problem, box: Record<string, number>, kind: MoreKind, cands: Form[][], alive: Uint32Array, once: boolean) => {
  const coefs = packForms(p, kind, cands), K = cands.length
  const twin = await moreEvaluator(undefined, p, box, kind, coefs, K), hw = await moreHwEvaluator(target, p, box, kind, coefs, K)
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
  console.log(`  ${what.padEnd(64)} ${rounds} rounds agree, ${killedTotal} killed, ${countAlive(alive, K)} of ${K} left (${Math.round(performance.now() - t0)} ms)`)
  return alive
}
console.log(`Rank pairs (small boxes, ${target.kind === 'cpu' ? 'Handwired loop runner' : 'Handwired on the GPU'} vs the JS twin)`)
for (const c of pairCases) {
  const p = fromLoop(c.l, c.laws), forms = rankTemplates(p, c), box = c.small
  const ni = await compare(`${c.what}: nonincreasing, ${points(p, box).toLocaleString()} points`, p, box, 'nonincreasing', forms.map(f => [f]), allAlive(forms.length), true)
  const firsts = forms.filter((_, j) => ((ni[j >>> 5]! >>> (j & 31)) & 1) === 1)
  const pairs = firsts.flatMap(a => forms.map(b => [a, b]))
  await compare(`${c.what}: pairs`, p, box, 'rankPair', pairs, allAlive(pairs.length), true)
}
console.log('Map invariants')
for (const c of mapCases) {
  const p = fromMapMachine(c.m), forms = mapTemplates(p, c), box = c.small
  await compare(`${c.what}: region + kill, ${points(p, box).toLocaleString()} points`, p, box, 'mapKill', forms.map(f => [f]), mapAtStart(c.m, p, box, forms), false)
}
console.log(failures === 0 ? 'every round agrees' : `${failures} disagreements`)
process.exit(failures === 0 ? 0 : 1)
