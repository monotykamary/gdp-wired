// Synthesis end to end: templates, Houdini rounds on the GPU (Handwired, through Dawn or Chrome's navigator.gpu) or the
// CPU twin, then the kernel proves what survives.
//   bun run.ts --cpu [--small]          the JS twin, one thread
//   bun run.ts --gpu [--small]          Dawn's navigator.gpu ($DAWN_MODULE), Metal on a Mac, Vulkan on Linux
//   --only <substring>, --out <file.json>
import {writeFileSync} from 'node:fs'
import {type Box, type Form, fromLoop, fromMachine, points} from './compile.ts'
import {type Evaluator, atStart, allAlive, countAlive, cpuEvaluator, gpuEvaluator, houdini, prove, proveRank, show, strongest, support, templates} from './synth.ts'
import {invariantCases, rankCases} from './models.ts'

const has = (f: string) => process.argv.includes(f), arg = (f: string) => { const i = process.argv.indexOf(f); return i < 0 ? undefined : process.argv[i + 1] }
const small = has('--small'), only = arg('--only'), useGpu = has('--gpu')
const report: Record<string, unknown>[] = []
let device: GPUDevice | undefined, host: any
if (useGpu) {
  const dawn = await import(process.env.DAWN_MODULE ?? 'webgpu') as {create: (flags: string[]) => GPU, globals: Record<string, unknown>}
  Object.assign(globalThis, dawn.globals)
  Object.defineProperty(globalThis.navigator, 'gpu', {value: dawn.create(process.platform === 'linux' ? ['backend=vulkan'] : []), configurable: true})
  host = await import('../vendor/handwired/src/json-search/gpu/host.ts')
  const batch = await host.requestBatchDevice(65535 * 64 * 4)
  device = batch.device
  console.log(`adapter ${JSON.stringify(batch.adapterInfo)}`)
}
const evaluator = async (p: ReturnType<typeof fromMachine>, box: Box, forms: Form[]): Promise<Evaluator> => (useGpu ? gpuEvaluator(host, device!, p, box, forms) : cpuEvaluator(p, box, forms))
const fmt = (n: number) => n.toLocaleString('en-US')

console.log('Invariants (Houdini over a box, then the kernel)')
for (const c of invariantCases) {
  if (only && !c.what.includes(only)) continue
  const box = small ? c.small : c.box, p = fromMachine(c.m)
  const forms = templates(p, c)
  const t0 = performance.now()
  const start = atStart(c.m, box, forms), trueAtStart = countAlive(start, forms.length)
  // Histories first (every request sequence of c.depth steps): a candidate a reachable state breaks is false.
  const hp = {...p, kind: 'history' as const, depth: small ? Math.min(c.depth, 6) : c.depth}
  const hbox = small ? {...box, ...Object.fromEntries(Object.entries(c.history).map(([v, b]) => [v, Math.min(b, 3)]))} : {...box, ...c.history}
  const hev = await evaluator(hp, hbox, forms)
  const hh = await houdini(hev, forms.length, start.slice(), true)
  hev.destroy?.()
  const afterReach = hh.alive, trueReachable = countAlive(afterReach, forms.length), reach = {length: points(hp, hbox)}
  const tReach = performance.now()
  const ev = await evaluator(p, box, forms)
  const h = await houdini(ev, forms.length, afterReach.slice())
  ev.destroy?.()
  const survivors = strongest(forms, h.alive)
  const needed = support(p, c.small, c.goalForm, survivors) // counterexamples to induction on the small box; the kernel finds the rest
  const t1 = performance.now()
  const timing = {historiesMs: Math.round(tReach - t0), roundsMs: Math.round(h.ms), supportMs: Math.round(t1 - tReach - h.ms), historyRounds: hh.rounds}
  const proof = prove(c.m, c.goal, survivors, needed)
  const t2 = performance.now()
  const entry = {what: c.what, evaluator: ev.name, candidates: forms.length, trueAtStart, histories: reach.length, trueReachable, ...timing, points: points(p, box), rounds: h.rounds, killedPerRound: h.perRound,
    survivors: countAlive(h.alive, forms.length), strongest: survivors.length, support: needed.length, filterMs: Math.round(t1 - t0), proven: proof.proven, kept: 'kept' in proof ? proof.kept!.map(l => l.name) : [], dropped: proof.dropped.length, leaves: 'leaves' in proof ? proof.leaves : 0, kernelMs: Math.round(t2 - t1)}
  report.push(entry)
  console.log(`  ${c.what}\n    ${fmt(forms.length)} candidates, ${fmt(entry.trueAtStart)} true at the start, ${fmt(trueReachable)} on ${fmt(reach.length)} histories of ${c.depth} (${hh.rounds} rounds, ${fmt(timing.historiesMs)} ms); ${fmt(entry.points)} points × ${h.rounds} rounds (${fmt(timing.roundsMs)} ms) on ${ev.name}: ${entry.survivors} survive (${survivors.length} strongest, ${needed.length} needed) in ${fmt(entry.filterMs)} ms`)
  console.log(`    kernel: ${proof.proven ? `PROVEN with ${entry.kept.filter(k => k !== c.goal.name).join(', ') || 'nothing more'} (${entry.leaves} leaves, ${proof.dropped.length} survivors not inductive)` : `STUCK ${JSON.stringify((proof as any).stuck)}`} in ${fmt(entry.kernelMs)} ms`)
}

console.log('Ranks (every survivor drops on every turn in the box, then the kernel)')
for (const c of rankCases) {
  if (only && !c.what.includes(only)) continue
  const box = small ? c.small : c.box, p = fromLoop(c.l, c.laws)
  const forms = templates(p, c)
  const t0 = performance.now()
  const ev = await evaluator(p, box, forms)
  const h = await houdini(ev, forms.length, allAlive(forms.length))
  ev.destroy?.()
  const alive = forms.filter((_, j) => ((h.alive[j >>> 5]! >>> (j & 31)) & 1) === 1)
  const t1 = performance.now()
  const r = proveRank(c.l, c.laws, alive)
  const t2 = performance.now()
  const entry = {what: c.what, evaluator: ev.name, candidates: forms.length, points: points(p, box), rounds: h.rounds, survivors: alive.length, filterMs: Math.round(t1 - t0), rank: r.rank ? show(r.rank, true) : null, tried: r.tried, leaves: r.leaves, kernelMs: Math.round(t2 - t1)}
  report.push(entry)
  console.log(`  ${c.what}\n    ${fmt(forms.length)} candidate ranks; ${fmt(entry.points)} points × ${h.rounds} rounds on ${ev.name}: ${alive.length} survive in ${fmt(entry.filterMs)} ms`)
  console.log(`    kernel: ${r.rank ? `HALTS with rank ${entry.rank} (${r.leaves} leaves, tried ${r.tried})` : `no survivor proven (tried ${r.tried})`} in ${fmt(entry.kernelMs)} ms`)
}
const out = arg('--out')
if (out) writeFileSync(out, JSON.stringify(report, null, 1))
process.exit(0)
