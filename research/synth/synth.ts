// The synthesis driver: templates, Houdini rounds on an evaluator (GPU or CPU), then the kernel. Nothing before the
// kernel is trusted; the box and the rounds only decide which candidates are worth a proof.
import {type C, type E, type Law, type Machine, atMost, evalC, evalE, interpret, minus, n, plus, times, x} from '../../core/machine.ts'
import {type Goal, type Loop, type Path, type Tree, canon, check, facts, leafConstraints, loopObligations, obligations} from '../../kernel/kernel.ts'
import {countLeaves, grow, proveLaws} from '../../kernel/prove.ts'
import {type Box, type Form, type Problem, BLOCK, CHUNK, blocks, js, order, points, tables, varsOf, wgsl} from './compile.ts'

// Every form with up to `terms` nonzero coefficients from `coefs` (coprime, at least one positive on a state variable)
// and each constant from `consts`.
export function templates(p: Problem, opts: {coefs: number[], consts: number[], terms: number}): Form[] {
  const vs = varsOf(p), out: Form[] = []
  const gcd = (a: number, b: number): number => (b === 0 ? Math.abs(a) : gcd(b, a % b))
  const go = (i: number, coef: Record<string, number>, used: number) => {
    if (i === vs.length) {
      const cs = Object.values(coef)
      if (cs.length === 0 || cs.reduce(gcd, 0) !== 1 || !p.state.some(v => (coef[v] ?? 0) > 0)) return
      for (const d of opts.consts) out.push({coef: {...coef}, d})
      return
    }
    go(i + 1, coef, used)
    if (used < opts.terms) for (const c of opts.coefs) if (c !== 0) go(i + 1, {...coef, [vs[i]!]: c}, used + 1)
  }
  go(0, {}, 0)
  return out
}

export type Evaluator = {name: string, round: (alive: Uint32Array) => Promise<number[]>, destroy?: () => void}
const words = (K: number) => Math.ceil(K / 32)
export const allAlive = (K: number) => { const a = new Uint32Array(words(K)); for (let j = 0; j < K; j++) a[j >>> 5]! |= 1 << (j & 31); return a }
const isAlive = (a: Uint32Array, j: number) => ((a[j >>> 5]! >>> (j & 31)) & 1) === 1
export const countAlive = (a: Uint32Array, K: number) => { let c = 0; for (let j = 0; j < K; j++) if (isAlive(a, j)) c++; return c }

// The kill masks of a round, turned into candidate indices.
const unpack = (masks: ArrayLike<number>, count: number, nb: number, killed: Set<number>) => {
  for (let i = 0; i < count; i++) { const m = masks[i]!; if (m) for (let q = 0; q < BLOCK; q++) if ((m >>> q) & 1) killed.add((i % nb) * BLOCK + q) }
}

// The CPU twin: one thread, the same emitted bodies (region, then kill over the region's points).
export function cpuEvaluator(p: Problem, box: Box, forms: Form[]): Evaluator {
  const f = js(p, box, forms.length), total = points(p, box), nb = blocks(forms.length)
  return {
    name: 'js, one thread',
    round: async alive => {
      const t = tables(p, forms, alive), T = new Int32Array(t.buffer), killed = new Set<number>()
      for (let i = 0; i < total; i++) {
        if (p.kind === 'invariant' && !f.region(i, T, t)) continue
        for (let b = 0; b < nb; b++) { const m = f.kill(i, b, T, t); for (let q = 0; q < BLOCK; q++) if ((m >>> q) & 1) killed.add(b * BLOCK + q) }
      }
      return [...killed]
    },
  }
}

// The GPU: Handwired's kernel runner (host.ts). Invariants take two passes per round: the region (which points
// satisfy every candidate alive), then kill over just those points. Dispatches are sized by their work, so none runs
// long enough for the operating system's GPU watchdog (macOS aborts a few-second dispatch); $SYNTH_WORK raises it.
export async function gpuEvaluator(host: {createKernelRunner: Function, createDocumentStore: Function}, device: GPUDevice, p: Problem, box: Box, forms: Form[]): Promise<Evaluator> {
  const K = forms.length, nb = blocks(K), total = points(p, box), budget = Number(process.env.SYNTH_WORK ?? 4e9), maxThreads = 65535 * 64
  if (total >= 2 ** 32) throw new Error('the box has more than 2^32 points')
  const store = await host.createDocumentStore(device, 1, maxThreads)
  const base = tables(p, forms, allAlive(K)).length
  const LIST = 1 << 20 // region points per kill dispatch
  const killRunner = await host.createKernelRunner(device, {code: wgsl(p, box, K, 'kill'), workgroupSize: 64, tableLength: base + (p.kind === 'invariant' ? LIST : 0), cellsPerDocument: 1}, store, 1)
  const regionRunner = p.kind === 'invariant' ? await host.createKernelRunner(device, {code: wgsl(p, box, K, 'region'), workgroupSize: 64, tableLength: base, cellsPerDocument: 1}, store, 2) : undefined
  const perThread = CHUNK * BLOCK * (p.kind === 'history' ? p.depth! + 1 : 1)
  const chunksPer = Math.max(1, Math.min(Math.floor(maxThreads / nb), Math.floor(budget / perThread / nb)))
  const regionThreads = Math.max(64, Math.min(maxThreads, Math.floor(budget / (BLOCK * (K + 1)))))
  return {
    name: 'gpu',
    round: async alive => {
      const killed = new Set<number>()
      if (p.kind !== 'invariant') {
        for (let at = 0; at < total; at += chunksPer * CHUNK) {
          const count = Math.min(chunksPer, Math.ceil((total - at) / CHUNK)) * nb
          const out = await killRunner.evaluate({count, tables: tables(p, forms, alive, at, total)})
          unpack(out.counts, count, nb, killed)
        }
        return [...killed]
      }
      // The region's points, then kill over them in slices.
      const region: number[] = []
      for (let at = 0; at < total; at += regionThreads * BLOCK) {
        const count = Math.min(regionThreads, Math.ceil((total - at) / BLOCK))
        const out = await regionRunner!.evaluate({count, tables: tables(p, forms, alive, at, total)})
        for (let i = 0; i < count; i++) { const m = out.counts[i]!; if (m) for (let q = 0; q < BLOCK; q++) if ((m >>> q) & 1) region.push(at + i * BLOCK + q) }
      }
      for (let at = 0; at < region.length; at += LIST) {
        const list = Uint32Array.from(region.slice(at, at + LIST)), padded = new Uint32Array(LIST); padded.set(list)
        for (let c = 0; c * CHUNK < list.length; c += chunksPer) {
          const from = c * CHUNK, count = Math.min(chunksPer, Math.ceil((list.length - from) / CHUNK)) * nb
          const out = await killRunner.evaluate({count, tables: tables(p, forms, alive, from, list.length, padded)})
          unpack(out.counts, count, nb, killed)
        }
      }
      lastRegion = region.length
      return [...killed]
    },
    destroy: () => { killRunner.destroy(); regionRunner?.destroy(); store.destroy() },
  }
}
export let lastRegion = 0

// Houdini: kill what the rounds report until nothing dies.
// once: the kills don't depend on which candidates are alive (histories), so one round finds them all.
export async function houdini(ev: Evaluator, K: number, alive = allAlive(K), once = false) {
  const perRound: number[] = []
  const t0 = performance.now()
  for (;;) {
    const killed = await ev.round(alive)
    if (killed.length === 0) break
    for (const j of killed) alive[j >>> 5]! &= ~(1 << (j & 31))
    perRound.push(killed.length)
    if (once) break
  }
  return {alive, rounds: perRound.length, perRound, ms: performance.now() - t0}
}

// Which candidates hold at the start, for every params in the box (and the precondition): the rest die at once.
export function atStart(m: Machine, box: Box, forms: Form[]): Uint32Array {
  const alive = allAlive(forms.length)
  const tuples = m.params.reduce<Record<string, number>[]>((acc, v) => acc.flatMap(t => Array.from({length: box[v]! + 1}, (_, i) => ({...t, [v]: i}))), [{}])
  const empty = {scalars: {}, maps: {}}
  for (const params of tuples) {
    if (m.pre && !evalPre(m, params)) continue
    const st = Object.fromEntries(Object.entries(m.state).map(([name, e]) => [name, evalE(e, params, empty, m)]))
    const env = {...params, ...st}
    forms.forEach((f, j) => { if (Object.entries(f.coef).reduce((s, [v, c]) => s + c * env[v]!, 0) > f.d) alive[j >>> 5]! &= ~(1 << (j & 31)) })
  }
  return alive
}
const evalPre = (m: Machine, params: Record<string, number>) => {
  const c = m.pre!
  const ev = (e: E): number => evalE(e, params, {scalars: {}, maps: {}}, m)
  const go = (c: C): boolean => c.op === 'not' ? !go(c.x) : c.op === 'and' ? c.xs.every(go) : c.op === 'or' ? c.xs.some(go) : c.op === 'flag' || c.op === 'all' ? false : c.op === '<' ? ev(c.a) < ev(c.b) : c.op === '<=' ? ev(c.a) <= ev(c.b) : ev(c.a) === ev(c.b)
  return go(c)
}

// The few survivors the goal needs, chosen on the box: while some point satisfies the goal and the chosen laws but its
// step breaks one of them (a counterexample to induction), add the survivor that rules out that point and the most
// later ones. Survivors are inductive together with the goal, so one always rules it out.
export function support(p: Problem, box: Box, goal: Form, survivors: Form[]): Form[] {
  const forms = [goal, ...survivors], f = js(p, box, forms.length), total = points(p, box)
  const digits = order(p)
  const decode = (index: number) => { let rest = index; const env: Record<string, number> = {}; for (const v of digits) { env[v] = rest % (box[v]! + 1); rest = Math.floor(rest / (box[v]! + 1)) } return env }
  const value = (form: Form, env: Record<string, number>) => Object.entries(form.coef).reduce((s, [v, c]) => s + c * env[v]!, 0)
  const chosen = new Set([0])
  for (;;) {
    const alive = new Uint32Array(Math.ceil(forms.length / 32)); for (const j of chosen) alive[j >>> 5]! |= 1 << (j & 31)
    const t = tables(p, forms, alive), T = new Int32Array(t.buffer)
    const ctis: Record<string, number>[] = []
    const nb = blocks(forms.length)
    for (let i = 0; i < total && ctis.length < 64; i++) { if (!f.region(i, T, t)) continue; for (let b = 0; b < nb; b++) if (f.kill(i, b, T, t)) { ctis.push(decode(i)); break } }
    if (ctis.length === 0) return [...chosen].filter(j => j > 0).map(j => survivors[j - 1]!)
    let best = -1, score = -1
    forms.forEach((form, j) => { if (j === 0 || chosen.has(j) || value(form, ctis[0]!) <= form.d) return; const s = ctis.filter(c => value(form, c) > form.d).length; if (s > score) (best = j, score = s) })
    if (best < 0) throw new Error('no survivor rules out a counterexample to induction: the survivors are not inductive with the goal')
    chosen.add(best)
  }
}

// The CPU alternative to the history kernel: reachable states inside the box (breadth first from every start, every
// request in the box); a candidate false at one of them is false. States that leave the box are not followed.
export function reachable(m: Machine, box: Box, limit = 200_000): Record<string, number>[] {
  const run = interpret(m), out: Record<string, number>[] = []
  const tuples = (names: string[]) => names.reduce<Record<string, number>[]>((acc, v) => acc.flatMap(t => Array.from({length: box[v]! + 1}, (_, i) => ({...t, [v]: i}))), [{}])
  const inputs = tuples(m.inputs)
  for (const params of tuples(m.params)) {
    if (m.pre && !evalPre(m, params)) continue
    const seen = new Set<string>(), queue = [run.init(params)]
    for (let head = 0; head < queue.length && out.length < limit; head++) {
      const st = queue[head]!, key = JSON.stringify(st.scalars)
      if (seen.has(key) || Object.entries(st.scalars).some(([v, val]) => val > box[v]!)) continue
      seen.add(key)
      out.push({...params, ...st.scalars})
      for (const input of inputs) if (!m.assume || evalC(m.assume, {...params, ...input}, st, m)) queue.push(run.step(params, st, input))
    }
  }
  return out
}
export function killFalse(forms: Form[], alive: Uint32Array, envs: Record<string, number>[]) {
  forms.forEach((f, j) => { if (((alive[j >>> 5]! >>> (j & 31)) & 1) && envs.some(env => Object.entries(f.coef).reduce((s, [v, c]) => s + c * env[v]!, 0) > f.d)) alive[j >>> 5]! &= ~(1 << (j & 31)) })
}

// The kernel decides; when it gets stuck at a step, its witness is a counterexample to induction, so add the survivor
// that rules it out and try again (the box chose the first laws, the kernel's witnesses choose the rest).
export function prove(m: Machine, goal: Law, survivors: Form[], first: Form[]) {
  const chosen = [...first]
  for (;;) {
    const r = proveWith(m, goal, chosen.map(lawOf))
    const w = r.proven ? undefined : (r as {stuck?: {goal: string, witness?: Record<string, number>}}).stuck
    if (r.proven || !w?.witness || !w.goal.endsWith('@step')) return {...r, chosen}
    const env = w.witness
    const next = survivors.find(f => !chosen.includes(f) && Object.entries(f.coef).reduce((s, [v, c]) => s + c * (env[v] ?? 0), 0) > f.d)
    if (!next) return {...r, chosen}
    chosen.push(next)
  }
}

// --- the kernel's side --------------------------------------------------------------------------------------------

const sum = (terms: E[]): E => terms.reduce((a, b) => plus(a, b), n(0))
const side = (f: Form, sign: 1 | -1) => Object.entries(f.coef).filter(([, c]) => c * sign > 0).map(([v, c]) => (Math.abs(c) === 1 ? x(v) : times(Math.abs(c), x(v))))
export const show = (f: Form, rank = false) => {
  const term = (v: string, c: number) => `${c === 1 ? '' : c === -1 ? '-' : c}${v}`
  const lhs = Object.entries(f.coef).map(([v, c], i) => (i > 0 && c > 0 ? '+ ' : '') + term(v, c)).join(' ').replace(/ -/g, ' - ')
  return rank ? `max(0, ${lhs}${f.d > 0 ? ` - ${f.d}` : f.d < 0 ? ` + ${-f.d}` : ''})` : `${lhs} <= ${f.d}`
}
// Σ c·v <= d over naturals: positive terms on the left, negative ones and d on the right.
export const lawOf = (f: Form): Law => ({name: show(f), holds: atMost(sum([...side(f, 1), ...(f.d < 0 ? [n(-f.d)] : [])]), sum([...side(f, -1), ...(f.d > 0 ? [n(f.d)] : [])]))})
// max(0, Σ c·v - d) as a natural term: (positives + max(0, -d)) ∸ (negatives + max(0, d)).
export const rankOf = (f: Form): E => minus(sum([...side(f, 1), ...(f.d < 0 ? [n(-f.d)] : [])]), sum([...side(f, -1), ...(f.d > 0 ? [n(f.d)] : [])]))

// Among survivors with the same coefficients, the least d implies the rest.
export function strongest(forms: Form[], alive: Uint32Array): Form[] {
  const best = new Map<string, Form>()
  forms.forEach((f, j) => { if (!isAlive(alive, j)) return; const key = JSON.stringify(Object.entries(f.coef).sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0))); const b = best.get(key); if (!b || f.d < b.d) best.set(key, f) })
  return [...best.values()]
}

// The hypotheses a tree's leaves use. A leaf's rows (kernel.ts leafConstraints) are the path's atoms, each hypothesis's
// facts in order, then cell equalities and natural rows; product rows come after and name two earlier rows.
export function usedHyps(goal: Goal, tree: Tree): Set<number> {
  const used = new Set<number>()
  const walk = (t: Tree, path: Path) => {
    if ('split' in t) { const id = canon(t.split); walk(t.yes, new Map(path).set(id, {lin: t.split, holds: true})); walk(t.no, new Map(path).set(id, {lin: t.split, holds: false})); return }
    const owner: number[] = [...path.keys()].map(() => -1)
    goal.hyps.forEach((h, i) => { for (const _ of facts(h, path)) owner.push(i) })
    const L = leafConstraints(goal, path).length, pairs = t.products ?? []
    const visit = (i: number): void => { if (i < L) { if ((owner[i] ?? -1) >= 0) used.add(owner[i]!) } else if (pairs[i - L]) { visit(pairs[i - L]![0]); visit(pairs[i - L]![1]) } }
    for (const step of t.leaf) if (step.kind === 'input') visit(step.index)
  }
  walk(tree, new Map())
  return used
}

// Prove the goal from the survivors with the kernel. A survivor the box let through but that isn't inductive is dropped
// (its step goal gets stuck); then only the laws the proof actually uses are kept, and that set is proven again.
export function proveWith(m: Machine, goal: Law, survivors: Law[]) {
  let laws = [goal, ...survivors]
  const dropped: string[] = []
  for (;;) {
    const r = proveLaws(m, laws)
    if (r.proven) break
    const name = r.failed!.goal.replace(/ @(start|step)$/, '')
    if (name === goal.name) return {proven: false as const, dropped, stuck: r.failed}
    laws = laws.filter(l => l.name !== name)
    dropped.push(name)
  }
  // Keep what the goal needs: follow the step trees' leaves back to the laws they use.
  const proof = proveLaws(m, laws).proof!
  const need = new Set([goal.name]), queue = [goal.name]
  while (queue.length) {
    const name = queue.pop()!
    const g = obligations(m, laws, proof.instances).find(o => o.name === `${name} @step`)!
    // The laws are assumed in order, each once (they are plain), after the facts, the precondition and the assumption.
    const holds = laws.map(l => JSON.stringify(l.holds)), hyps = g.hyps.map(h => JSON.stringify(h))
    const offset = hyps.findIndex((_, i) => holds.every((h, j) => hyps[i + j] === h))
    for (const h of usedHyps(g, proof.trees[g.name]!)) {
      const law = laws[h - offset]
      if (law && !need.has(law.name)) (need.add(law.name), queue.push(law.name))
    }
  }
  const kept = laws.filter(l => need.has(l.name))
  const final = proveLaws(m, kept)
  return {proven: final.proven && final.checked, dropped, kept, leaves: final.leaves}
}

// Ranks: try survivors, simplest first, until the kernel accepts one.
export function proveRank(l: Loop, laws: Law[], ranks: Form[]) {
  const simple = [...ranks].sort((a, b) => Object.keys(a.coef).length - Object.keys(b.coef).length || Object.values(a.coef).reduce((s, c) => s + Math.abs(c), 0) - Object.values(b.coef).reduce((s, c) => s + Math.abs(c), 0) || Math.abs(a.d) - Math.abs(b.d))
  let tried = 0
  for (const f of simple) {
    tried++
    const goals = loopObligations(l, laws, rankOf(f))
    let leaves = 0, ok = true
    for (const g of goals) { const o = grow(g); if (!('tree' in o) || !check(g, o.tree)) { ok = false; break } leaves += countLeaves(o.tree) }
    if (ok) return {rank: f, tried, leaves}
  }
  return {rank: undefined, tried, leaves: 0}
}
