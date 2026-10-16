// Rank pairs and ∀-key map invariants end to end: the GPU (Handwired's kernel runner, through Dawn) or the JS twin
// filters, the kernel proves.
//   bun run-more.ts --gpu | --cpu [--small] [--only <substring>] [--out <file.json>]
import {writeFileSync} from 'node:fs'
import {fromLoop, points} from './compile.ts'
import {fromMapMachine} from './compile-more.ts'
import {type GpuHost, mapAtStart, mapLawOf, mapTemplates, moreEvaluator, packForms, proveAll, rankPairs, rankTemplates, strongestOf} from './more.ts'
import {allAlive, countAlive, cpuEvaluator, gpuEvaluator, houdini, proveRank} from './synth.ts'
import {proveLaws} from '../kernel/prove.ts'
import {mapCases, pairCases} from './models-more.ts'

const has = (f: string) => process.argv.includes(f), arg = (f: string) => { const i = process.argv.indexOf(f); return i < 0 ? undefined : process.argv[i + 1] }
const small = has('--small'), only = arg('--only')
let gpu: GpuHost | undefined
if (has('--gpu')) {
  const dawn = await import(process.env.DAWN_MODULE ?? 'webgpu') as {create: (flags: string[]) => GPU, globals: Record<string, unknown>}
  Object.assign(globalThis, dawn.globals)
  Object.defineProperty(globalThis.navigator, 'gpu', {value: dawn.create(process.platform === 'linux' ? ['backend=vulkan'] : []), configurable: true})
  const host = await import('../vendor/handwired/src/json-search/gpu/host.ts')
  const batch = await host.requestBatchDevice(65535 * 64 * 4)
  gpu = {host, device: batch.device}
  console.log(`adapter ${JSON.stringify(batch.adapterInfo)}`)
}
const fmt = (v: number) => v.toLocaleString('en-US')
const report: Record<string, unknown>[] = []

console.log('Rank pairs (ranks compared in order)')
for (const c of pairCases) {
  if (only && !c.what.includes(only)) continue
  const box = small ? c.small : c.box, p = fromLoop(c.l, c.laws)
  const forms = rankTemplates(p, c)
  // A single rank first, with synth.ts's kernel: none of these loops has one.
  const t0 = performance.now()
  const ev = gpu ? await gpuEvaluator(gpu.host, gpu.device, p, box, forms) : cpuEvaluator(p, box, forms)
  const h = await houdini(ev, forms.length, allAlive(forms.length))
  ev.destroy?.()
  const singles = forms.filter((_, j) => ((h.alive[j >>> 5]! >>> (j & 31)) & 1) === 1)
  const single = proveRank(c.l, c.laws, singles)
  const singleMs = Math.round(performance.now() - t0)
  const r = await rankPairs(gpu, c.l, c.laws, p, box, forms)
  const entry = {what: c.what, evaluator: r.evaluator, points: points(p, box), candidates: forms.length, singleSurvivors: singles.length, singleRank: single.rank ? 'found' : null, singleMs, ...r}
  report.push(entry)
  console.log(`  ${c.what}\n    single ranks: ${fmt(forms.length)} candidates, ${singles.length} survive, ${single.rank ? 'one PROVEN' : 'none proven'} (${fmt(singleMs)} ms)`)
  console.log(`    pairs: ${r.firsts} never go up → ${fmt(r.pairs)} pairs over ${fmt(entry.points)} points on ${r.evaluator}: ${r.survivors} survive in ${fmt(r.filterMs)} ms`)
  console.log(`    kernel: ${r.pair ? `HALTS with (${r.pair.join(', ')}) in order (${r.leaves} leaves, tried ${r.tried})` : `no pair proven (tried ${r.tried})`} in ${fmt(r.kernelMs)} ms`)
}

console.log('Invariants at every key of a map (Houdini over tracked cells, then the kernel)')
for (const c of mapCases) {
  if (only && !c.what.includes(only)) continue
  const box = small ? c.small : c.box, p = fromMapMachine(c.m)
  const forms = mapTemplates(p, c)
  const t0 = performance.now()
  const start = mapAtStart(c.m, p, box, forms), trueAtStart = countAlive(start, forms.length)
  const ev = await moreEvaluator(gpu, p, box, 'mapKill', packForms(p, 'mapKill', forms.map(f => [f])), forms.length)
  const h = await houdini(ev, forms.length, start.slice())
  ev.destroy?.()
  const survivors = strongestOf(forms, h.alive)
  const t1 = performance.now()
  const proof = proveAll(c.m, survivors.map(f => mapLawOf(p, f)))
  // Is each expected law among what was found, or implied by it?
  const implied = c.expect.map(e => ({name: e.name, implied: proveLaws(c.m, [...proof.kept, {...e, name: `expected: ${e.name}`}]).proven}))
  const t2 = performance.now()
  const entry = {what: c.what, evaluator: ev.name, candidates: forms.length, trueAtStart, points: points(p, box), rounds: h.rounds, killedPerRound: h.perRound, survivors: countAlive(h.alive, forms.length), strongest: survivors.length,
    filterMs: Math.round(t1 - t0), proven: proof.proven, kept: proof.kept.map(l => l.name), dropped: proof.dropped, leaves: proof.leaves, implied, kernelMs: Math.round(t2 - t1)}
  report.push(entry)
  console.log(`  ${c.what}\n    ${fmt(forms.length)} candidates, ${trueAtStart} true at the start; ${fmt(entry.points)} points × ${h.rounds} rounds on ${ev.name}: ${entry.survivors} survive (${survivors.length} strongest) in ${fmt(entry.filterMs)} ms`)
  console.log(`    kernel: ${proof.proven ? `PROVEN ${proof.kept.length} laws together (${proof.leaves} leaves, ${proof.dropped.length} dropped): ${proof.kept.map(l => l.name).join('; ')}` : 'nothing proven'} in ${fmt(entry.kernelMs)} ms`)
  console.log(`    expected laws: ${implied.map(i => `${i.name} ${i.implied ? 'follows' : 'NOT found'}`).join('; ')}`)
}
const out = arg('--out')
if (out) writeFileSync(out, JSON.stringify(report, null, 1))
process.exit(0)
