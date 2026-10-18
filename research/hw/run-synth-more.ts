// synth/run-more.ts (rank pairs, ∀-key map invariants) with the filtering on the Handwired u32-words kernels: the
// single-rank pass on hw/synth.ts's, the pair and map passes on synth-more.ts's. The templates, Houdini, kernel proofs
// and expected-law checks are synth/more.ts's. --both also runs synth/'s hand-written kernels on the same device and
// checks that every case ends the same way.
//   DAWN_MODULE=<webgpu>/index.js bun run-synth-more.ts [--both] [--small] [--only <substring>] [--out <file.json>]
//   bun run-synth-more.ts --cpu --small      Handwired's CPU loop runner
import {writeFileSync} from 'node:fs'
import {type Box, type Form, type Problem, fromLoop, points} from '../synth/compile.ts'
import {type MoreKind, fromMapMachine} from '../synth/compile-more.ts'
import {mapAtStart, mapLawOf, mapTemplates, moreEvaluator, packForms, proveAll, rankTemplates, strongestOf} from '../synth/more.ts'
import {type Evaluator, allAlive, countAlive, gpuEvaluator, houdini, proveRank, rankOf, show} from '../synth/synth.ts'
import {check, loopObligations} from '../../kernel/kernel.ts'
import {countLeaves, grow, proveLaws} from '../../kernel/prove.ts'
import {mapCases, pairCases} from '../synth/models-more.ts'
import {hwEvaluator} from './synth.ts'
import {moreHwEvaluator} from './synth-more.ts'

const has = (f: string) => process.argv.includes(f), arg = (f: string) => { const i = process.argv.indexOf(f); return i < 0 ? undefined : process.argv[i + 1] }
const small = has('--small'), only = arg('--only'), useGpu = !has('--cpu'), both = has('--both')
let device: GPUDevice | undefined, host: any
if (useGpu) {
  const dawn = await import(process.env.DAWN_MODULE ?? 'webgpu') as {create: (flags: string[]) => GPU, globals: Record<string, unknown>}
  Object.assign(globalThis, dawn.globals)
  Object.defineProperty(globalThis.navigator, 'gpu', {value: dawn.create(process.platform === 'linux' ? ['backend=vulkan'] : []), configurable: true})
  host = await import('../../vendor/handwired/src/json-search/gpu/host.ts')
  const batch = await host.requestBatchDevice(65535 * 64 * 4)
  device = batch.device
  console.log(`adapter ${JSON.stringify(batch.adapterInfo)}`)
}
let hand = false
const target = () => (useGpu ? {kind: 'gpu' as const, device: device!, host} : {kind: 'cpu' as const})
const single = (p: Problem, box: Box, forms: Form[]): Promise<Evaluator> => (hand ? gpuEvaluator(host, device!, p, box, forms) : hwEvaluator(target(), p, box, forms))
const more = (p: Problem, box: Box, kind: MoreKind, coefs: Int32Array, K: number): Promise<Evaluator> =>
  (hand ? moreEvaluator({host, device: device!}, p, box, kind, coefs, K) : moreHwEvaluator(target(), p, box, kind, coefs, K))
const fmt = (v: number) => v.toLocaleString('en-US')
const isAlive = (a: Uint32Array, j: number) => ((a[j >>> 5]! >>> (j & 31)) & 1) === 1
const simplicity = (f: Form) => Object.keys(f.coef).length * 100 + Object.values(f.coef).reduce((s, c) => s + Math.abs(c), 0) * 10 + Math.abs(f.d)
const report: Record<string, unknown>[] = []

for (const which of both ? [false, true] : [false]) {
  hand = which
  if (hand && !useGpu) throw new Error('--both needs the GPU')
  console.log(`=== ${hand ? 'synth/ hand-written kernels' : 'Handwired u32-words kernels'}`)
  console.log('Rank pairs (ranks compared in order)')
  for (const c of pairCases) {
    if (only && !c.what.includes(only)) continue
    const box = small ? c.small : c.box, p = fromLoop(c.l, c.laws)
    const forms = rankTemplates(p, c)
    const t0 = performance.now()
    const ev = await single(p, box, forms)
    const h = await houdini(ev, forms.length, allAlive(forms.length))
    ev.destroy?.()
    const singles = forms.filter((_, j) => isAlive(h.alive, j))
    const singleRank = proveRank(c.l, c.laws, singles)
    const singleMs = Math.round(performance.now() - t0)
    // As synth/more.ts's rankPairs: ranks that never go up (one round), then every such r1 with every r2 (one round).
    const t1 = performance.now()
    const ni = await more(p, box, 'nonincreasing', packForms(p, 'nonincreasing', forms.map(f => [f])), forms.length)
    const tni = performance.now()
    const hn = await houdini(ni, forms.length, allAlive(forms.length), true)
    ni.destroy?.()
    const firsts = forms.filter((_, j) => isAlive(hn.alive, j))
    const pairs: Form[][] = firsts.flatMap(a => forms.map(b => [a, b]))
    const t2 = performance.now()
    const pe = await more(p, box, 'rankPair', packForms(p, 'rankPair', pairs), pairs.length)
    const tpe = performance.now()
    const hp = await houdini(pe, pairs.length, allAlive(pairs.length), true)
    pe.destroy?.()
    const survivors = pairs.filter((_, j) => isAlive(hp.alive, j)).sort((a, b) => simplicity(a[0]!) + simplicity(a[1]!) - simplicity(b[0]!) - simplicity(b[1]!))
    const t3 = performance.now()
    let tried = 0, pair: string[] | null = null, leaves = 0
    for (const [a, b] of survivors) {
      tried++
      let ok = true, l = 0
      for (const g of loopObligations(c.l, c.laws, [rankOf(a!), rankOf(b!)])) { const o = grow(g); if (!('tree' in o) || !check(g, o.tree)) { ok = false; break } l += countLeaves(o.tree) }
      if (ok) { pair = [show(a!, true), show(b!, true)]; leaves = l; break }
      if (tried >= 200) break
    }
    const entry = {kernels: hand ? 'hand' : 'handwired', what: c.what, evaluator: pe.name, points: points(p, box), candidates: forms.length, singleSurvivors: singles.length, singleRank: singleRank.rank ? 'found' : null, singleMs,
      firsts: firsts.length, pairs: pairs.length, survivors: survivors.length, pair, leaves, tried, firstMs: Math.round(t2 - t1), filterMs: Math.round(t3 - t1), kernelMs: Math.round(performance.now() - t3),
      setupMs: Math.round(tni - t1 + tpe - t2), roundsMs: Math.round(hn.ms + hp.ms)}
    report.push(entry)
    console.log(`  ${c.what}\n    single ranks: ${fmt(forms.length)} candidates, ${singles.length} survive, ${singleRank.rank ? 'one PROVEN' : 'none proven'} (${fmt(singleMs)} ms)`)
    console.log(`    pairs: ${firsts.length} never go up → ${fmt(pairs.length)} pairs over ${fmt(entry.points)} points on ${pe.name}: ${survivors.length} survive in ${fmt(entry.filterMs)} ms`)
    console.log(`    kernel: ${pair ? `HALTS with (${pair.join(', ')}) in order (${leaves} leaves, tried ${tried})` : `no pair proven (tried ${tried})`} in ${fmt(entry.kernelMs)} ms`)
  }

  console.log('Invariants at every key of a map (Houdini over tracked cells, then the kernel)')
  for (const c of mapCases) {
    if (only && !c.what.includes(only)) continue
    const box = small ? c.small : c.box, p = fromMapMachine(c.m)
    const forms = mapTemplates(p, c)
    const t0 = performance.now()
    const start = mapAtStart(c.m, p, box, forms), trueAtStart = countAlive(start, forms.length)
    const ts = performance.now()
    const ev = await more(p, box, 'mapKill', packForms(p, 'mapKill', forms.map(f => [f])), forms.length)
    const setupMs = Math.round(performance.now() - ts)
    const h = await houdini(ev, forms.length, start.slice())
    ev.destroy?.()
    const survivors = strongestOf(forms, h.alive)
    const t1 = performance.now()
    const proof = proveAll(c.m, survivors.map(f => mapLawOf(p, f)))
    const implied = c.expect.map(e => ({name: e.name, implied: proveLaws(c.m, [...proof.kept, {...e, name: `expected: ${e.name}`}]).proven}))
    const t2 = performance.now()
    const entry = {kernels: hand ? 'hand' : 'handwired', what: c.what, evaluator: ev.name, candidates: forms.length, trueAtStart, points: points(p, box), rounds: h.rounds, killedPerRound: h.perRound, survivors: countAlive(h.alive, forms.length), strongest: survivors.length,
      filterMs: Math.round(t1 - t0), setupMs, roundsMs: Math.round(h.ms), proven: proof.proven, kept: proof.kept.map(l => l.name), dropped: proof.dropped, leaves: proof.leaves, implied, kernelMs: Math.round(t2 - t1)}
    report.push(entry)
    console.log(`  ${c.what}\n    ${fmt(forms.length)} candidates, ${trueAtStart} true at the start; ${fmt(entry.points)} points × ${h.rounds} rounds on ${ev.name}: ${entry.survivors} survive (${survivors.length} strongest) in ${fmt(entry.filterMs)} ms`)
    console.log(`    kernel: ${proof.proven ? `PROVEN ${proof.kept.length} laws together (${proof.leaves} leaves, ${proof.dropped.length} dropped): ${proof.kept.map(l => l.name).join('; ')}` : 'nothing proven'} in ${fmt(entry.kernelMs)} ms`)
    console.log(`    expected laws: ${implied.map(i => `${i.name} ${i.implied ? 'follows' : 'NOT found'}`).join('; ')}`)
  }
}
if (both) {
  const key = (e: any) => JSON.stringify([e.what, e.singleSurvivors, e.firsts, e.survivors, e.pair, e.strongest, e.proven, e.kept, e.implied])
  const hw = report.filter(e => e.kernels === 'handwired'), hd = report.filter(e => e.kernels === 'hand')
  console.log(`same outcome on both: ${hw.filter((e, i) => key(e) === key(hd[i])).length} / ${hw.length} cases`)
  console.log('  filter time (setup: circuits + shader compile; rounds: the GPU work)')
  for (const e of hw as any[]) { const o = hd.find(x => x.what === e.what) as any; console.log(`  ${String(e.what).padEnd(52)} handwired ${String(e.filterMs).padStart(6)} ms (setup ${e.setupMs}, rounds ${e.roundsMs})   hand ${String(o?.filterMs).padStart(6)} ms (setup ${o?.setupMs}, rounds ${o?.roundsMs})`) }
}
const out = arg('--out')
if (out) writeFileSync(out, JSON.stringify(report, null, 1))
process.exit(0)
