// Drivers for compile-more.ts's kernels: rank pairs for loops no single linear rank fits, and ∀-key invariants for
// machines with maps. As in synth.ts, the GPU (Handwired's kernel runner) or the JS twin filters, and the kernel proves.
import {type C, type E, type Law, type Machine, atMost, evalE, get, minus, n, plus, times, x} from '../../core/machine.ts'
import {type Loop, check, loopObligations} from '../../kernel/kernel.ts'
import {countLeaves, grow, proveLaws} from '../../kernel/prove.ts'
import {type Box, type Form, type Problem, BLOCK, CHUNK, blocks, points, varsOf} from './compile.ts'
import {type MapProblem, type MoreKind, jsMore, moreTables, wgslMore, widthOf} from './compile-more.ts'
import {type Evaluator, allAlive, houdini, rankOf, show} from './synth.ts'

const isAlive = (a: Uint32Array, j: number) => ((a[j >>> 5]! >>> (j & 31)) & 1) === 1
const unpack = (masks: ArrayLike<number>, count: number, nb: number, killed: Set<number>) => {
  for (let i = 0; i < count; i++) { const m = masks[i]!; if (m) for (let q = 0; q < BLOCK; q++) if ((m >>> q) & 1) killed.add((i % nb) * BLOCK + q) }
}
// Candidates (forms, or pairs of forms) as i32 coefficients in the kernels' order.
export function packForms(p: Problem, kind: MoreKind, cands: Form[][]): Int32Array {
  const vs = varsOf(p), width = widthOf(p, kind), out = new Int32Array(cands.length * width)
  cands.forEach((fs, j) => fs.forEach((f, slot) => { vs.forEach((v, i) => (out[j * width + slot * (vs.length + 1) + i] = f.coef[v] ?? 0)); out[j * width + slot * (vs.length + 1) + vs.length] = f.d }))
  return out
}

// A round over the box: for maps, the region (points satisfying every candidate alive) and then kill over it; for ranks,
// kill over every point. `kill` is 'mapKill', 'nonincreasing' or 'rankPair'.
export type GpuHost = {host: {createKernelRunner: Function, createDocumentStore: Function}, device: GPUDevice}
export async function moreEvaluator(gpu: GpuHost | undefined, p: Problem, box: Box, kill: MoreKind, coefs: Int32Array, K: number): Promise<Evaluator> {
  const total = points(p, box), nb = blocks(K), maps = kill === 'mapKill'
  if (!gpu) {
    const killFn = jsMore(p, box, K, kill).kill!, regionFn = maps ? jsMore(p, box, K, 'mapRegion').region! : undefined
    return {
      name: 'js, one thread',
      round: async alive => {
        const t = moreTables(p, kill, coefs, K, alive), T = new Int32Array(t.buffer), killed = new Set<number>()
        for (let i = 0; i < total; i++) {
          if (regionFn && !regionFn(i, T, t)) continue
          for (let b = 0; b < nb; b++) { const m = killFn(i, b, T, t); if (m) for (let q = 0; q < BLOCK; q++) if ((m >>> q) & 1) killed.add(b * BLOCK + q) }
        }
        return [...killed]
      },
    }
  }
  if (total >= 2 ** 32) throw new Error('the box has more than 2^32 points')
  const {host, device} = gpu, maxThreads = 65535 * 64, budget = Number(process.env.SYNTH_WORK ?? 4e9)
  const store = await host.createDocumentStore(device, 1, maxThreads)
  const base = moreTables(p, kill, coefs, K, allAlive(K)).length, LIST = 1 << 20
  const killRunner = await host.createKernelRunner(device, {code: wgslMore(p, box, K, kill), workgroupSize: 64, tableLength: base + (maps ? LIST : 0), cellsPerDocument: 1}, store, 3)
  const regionRunner = maps ? await host.createKernelRunner(device, {code: wgslMore(p, box, K, 'mapRegion'), workgroupSize: 64, tableLength: base, cellsPerDocument: 1}, store, 4) : undefined
  const chunksPer = Math.max(1, Math.min(Math.floor(maxThreads / nb), Math.floor(budget / (CHUNK * BLOCK * (kill === 'rankPair' ? 2 : 1)) / nb)))
  const regionThreads = Math.max(64, Math.min(maxThreads, Math.floor(budget / (BLOCK * (2 * K + 1)))))
  return {
    name: 'gpu',
    round: async alive => {
      const killed = new Set<number>()
      if (!maps) {
        for (let at = 0; at < total; at += chunksPer * CHUNK) {
          const count = Math.min(chunksPer, Math.ceil((total - at) / CHUNK)) * nb
          unpack((await killRunner.evaluate({count, tables: moreTables(p, kill, coefs, K, alive, at, total)})).counts, count, nb, killed)
        }
        return [...killed]
      }
      const region: number[] = []
      for (let at = 0; at < total; at += regionThreads * BLOCK) {
        const count = Math.min(regionThreads, Math.ceil((total - at) / BLOCK))
        const out = await regionRunner!.evaluate({count, tables: moreTables(p, 'mapRegion', coefs, K, alive, at, total)})
        for (let i = 0; i < count; i++) { const m = out.counts[i]!; if (m) for (let q = 0; q < BLOCK; q++) if ((m >>> q) & 1) region.push(at + i * BLOCK + q) }
      }
      for (let at = 0; at < region.length; at += LIST) {
        const list = Uint32Array.from(region.slice(at, at + LIST)), padded = new Uint32Array(LIST); padded.set(list)
        for (let c = 0; c * CHUNK < list.length; c += chunksPer) {
          const from = c * CHUNK, count = Math.min(chunksPer, Math.ceil((list.length - from) / CHUNK)) * nb
          unpack((await killRunner.evaluate({count, tables: moreTables(p, kill, coefs, K, alive, from, list.length, padded)})).counts, count, nb, killed)
        }
      }
      return [...killed]
    },
    destroy: () => { killRunner.destroy(); regionRunner?.destroy(); store.destroy() },
  }
}

// --- rank pairs ---

// Rank templates: up to `terms` nonzero coefficients (coprime, at least one on a state variable, of either sign: n - i
// is a rank) and each constant.
export function rankTemplates(p: Problem, opts: {coefs: number[], consts: number[], terms: number}): Form[] {
  const vs = varsOf(p), out: Form[] = []
  const gcd = (a: number, b: number): number => (b === 0 ? Math.abs(a) : gcd(b, a % b))
  const go = (i: number, coef: Record<string, number>, used: number) => {
    if (i === vs.length) {
      const cs = Object.values(coef)
      if (cs.length && cs.reduce(gcd, 0) === 1 && p.state.some(v => coef[v])) for (const d of opts.consts) out.push({coef: {...coef}, d})
      return
    }
    go(i + 1, coef, used)
    if (used < opts.terms) for (const c of opts.coefs) go(i + 1, {...coef, [vs[i]!]: c}, used + 1)
  }
  go(0, {}, 0)
  return out
}

const simplicity = (f: Form) => Object.keys(f.coef).length * 100 + Object.values(f.coef).reduce((s, c) => s + Math.abs(c), 0) * 10 + Math.abs(f.d)
// r1 must never go up where the loop runs (one round: whether a rank goes up doesn't depend on the others); then every
// pair of such an r1 with any r2 is tried as (r1, r2) compared in order, also in one round.
export async function rankPairs(gpu: GpuHost | undefined, l: Loop, laws: Law[], p: Problem, box: Box, forms: Form[]) {
  const t0 = performance.now()
  const ni = await moreEvaluator(gpu, p, box, 'nonincreasing', packForms(p, 'nonincreasing', forms.map(f => [f])), forms.length)
  const hn = await houdini(ni, forms.length, allAlive(forms.length), true)
  ni.destroy?.()
  // An r1 that never moves is useless as a first part: it would leave r2 to drop alone, which single ranks already tried.
  const firsts = forms.filter((_, j) => isAlive(hn.alive, j))
  const pairs: Form[][] = firsts.flatMap(a => forms.map(b => [a, b]))
  const t1 = performance.now()
  const pe = await moreEvaluator(gpu, p, box, 'rankPair', packForms(p, 'rankPair', pairs), pairs.length)
  const hp = await houdini(pe, pairs.length, allAlive(pairs.length), true)
  pe.destroy?.()
  const survivors = pairs.filter((_, j) => isAlive(hp.alive, j)).sort((a, b) => simplicity(a[0]!) + simplicity(a[1]!) - simplicity(b[0]!) - simplicity(b[1]!))
  const t2 = performance.now()
  // The kernel, simplest first.
  let tried = 0
  for (const [a, b] of survivors) {
    tried++
    let leaves = 0, ok = true
    for (const g of loopObligations(l, laws, [rankOf(a!), rankOf(b!)])) { const o = grow(g); if (!('tree' in o) || !check(g, o.tree)) { ok = false; break } leaves += countLeaves(o.tree) }
    if (ok) return {firsts: firsts.length, pairs: pairs.length, survivors: survivors.length, pair: [show(a!, true), show(b!, true)], leaves, tried, filterMs: Math.round(t2 - t0), firstMs: Math.round(t1 - t0), kernelMs: Math.round(performance.now() - t2), evaluator: pe.name}
    if (tried >= 200) break
  }
  return {firsts: firsts.length, pairs: pairs.length, survivors: survivors.length, pair: null, leaves: 0, tried, filterMs: Math.round(t2 - t0), firstMs: Math.round(t1 - t0), kernelMs: Math.round(performance.now() - t2), evaluator: pe.name}
}

// --- invariants for machines with maps --------------------------------------------------------------------------------

// Forms about one map's cell at k (a positive coefficient on it) plus up to `terms - 1` scalars or params, and forms
// over scalars alone.
export function mapTemplates(p: MapProblem, opts: {coefs: number[], consts: number[], terms: number}): Form[] {
  const others = varsOf(p).filter(v => v !== 'k' && !p.maps.some(M => v === `${M}_k`)), out: Form[] = []
  const gcd = (a: number, b: number): number => (b === 0 ? Math.abs(a) : gcd(b, a % b))
  const extend = (base: Record<string, number>, from: number, left: number, need: (c: Record<string, number>) => boolean) => {
    const cs = Object.values(base)
    if (cs.length && cs.reduce(gcd, 0) === 1 && need(base)) for (const d of opts.consts) out.push({coef: {...base}, d})
    if (left === 0) return
    for (let i = from; i < others.length; i++) for (const c of opts.coefs) extend({...base, [others[i]!]: c}, i + 1, left - 1, need)
  }
  for (const M of p.maps) for (const c of opts.coefs.filter(c => c > 0)) extend({[`${M}_k`]: c}, 0, opts.terms - 1, () => true)
  const scalars = p.state.filter(v => !p.maps.some(M => v === `${M}_k`))
  extend({}, 0, opts.terms, coef => scalars.some(v => (coef[v] ?? 0) > 0))
  return out
}

// At the start every cell holds the map's initial value; the scalars start from the params.
export function mapAtStart(m: Machine, p: MapProblem, box: Box, forms: Form[]): Uint32Array {
  const alive = allAlive(forms.length)
  const tuples = m.params.reduce<Record<string, number>[]>((acc, v) => acc.flatMap(t => Array.from({length: box[v]! + 1}, (_, i) => ({...t, [v]: i}))), [{}])
  for (const params of tuples) {
    const env: Record<string, number> = {...params, ...Object.fromEntries(Object.entries(m.state).map(([name, e]) => [name, evalE(e, params, {scalars: {}, maps: {}}, m)])), ...Object.fromEntries(p.maps.map(M => [`${M}_k`, m.maps![M]!]))}
    forms.forEach((f, j) => { if (Object.entries(f.coef).reduce((s, [v, c]) => s + c * env[v]!, 0) > f.d) alive[j >>> 5]! &= ~(1 << (j & 31)) })
  }
  return alive
}

// A form as a law: a cell M_k is the read M[k], and the law holds for every k.
export function mapLawOf(p: MapProblem, f: Form): Law {
  const term = (v: string): E => { const M = p.maps.find(M => v === `${M}_k`); return M ? get(M, x('k')) : x(v) }
  const side = (sign: 1 | -1) => Object.entries(f.coef).filter(([, c]) => c * sign > 0).map(([v, c]) => (Math.abs(c) === 1 ? term(v) : times(Math.abs(c), term(v))))
  const sum = (ts: E[]) => ts.reduce((a, b) => plus(a, b), n(0))
  const holds: C = atMost(sum([...side(1), ...(f.d < 0 ? [n(-f.d)] : [])]), sum([...side(-1), ...(f.d > 0 ? [n(f.d)] : [])]))
  const about = Object.keys(f.coef).some(v => p.maps.some(M => v === `${M}_k`))
  return {name: show(f).replace(/(\w+)_k/g, '$1[k]'), holds, ...(about ? {forall: 'k'} : {})}
}

// Among survivors with the same coefficients, the least d implies the rest.
export function strongestOf(forms: Form[], alive: Uint32Array): Form[] {
  const best = new Map<string, Form>()
  forms.forEach((f, j) => { if (!isAlive(alive, j)) return; const key = JSON.stringify(Object.entries(f.coef).sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0))); const b = best.get(key); if (!b || f.d < b.d) best.set(key, f) })
  return [...best.values()]
}

// Prove the whole set with the kernel; a law whose goal gets stuck is dropped and the rest tried again.
export function proveAll(m: Machine, laws: Law[]) {
  let kept = laws
  const dropped: string[] = []
  for (;;) {
    if (kept.length === 0) return {proven: false, kept, dropped, leaves: 0}
    const r = proveLaws(m, kept)
    if (r.proven) return {proven: r.checked, kept, dropped, leaves: r.leaves}
    const name = r.failed!.goal.replace(/ @(start|step)$/, '')
    kept = kept.filter(l => l.name !== name)
    dropped.push(name)
  }
}
void minus
