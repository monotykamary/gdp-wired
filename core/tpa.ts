// Transition power abstraction (Blicha, Fedyukovich, Hyvärinen and Sharygina's TPA, as Golem runs it): relations
// R_n ⊇ T^{≤2ⁿ} over a state and a later one, each R_{n+1} a conjunction of interpolants (core/interp.ts) learned
// where two R_n in a row can't take one state to another. Nothing here is trusted: a run it finds is taken by the
// interpreter (and the caller checks it against the CHC), an invariant it finds is the kernel's to prove.
//
// - R_0 is a step or none (exact). Whether D is reached from S within 2^{n+1} steps: S, R_n, R_n, D asked of the kernel's
//   search. Refuted, the interpolant of the two R_n against S and D (over the first state and the last) is a conjunct of
//   R_{n+1}: every pair two R_n join, and no pair of S and D. A model at n = 0 is a run (its steps, each taken or not);
//   above, its middle state m is a point, and S to m, then m to D, are asked at n − 1, each refuted one strengthening
//   R_n, and the query is asked again.
// - Deep runs in few queries: each level doubles the depth, and each query reads two relations, not the 2^{n+1} steps a
//   bounded run's goal would.
// - Invariants: once the start doesn't reach the law broken within 2^{n+1}, each conjunct of R_{n+1} read from the start
//   (the start's values put in) holds of every state 2^{n+1} steps or fewer away; Houdini keeps those a step keeps (each
//   asked of the CDCL search for a model alone), and where they leave the law unbroken they are an invariant.
// Integers are read relaxed (core/bmc.ts's relax): each pair of naturals by its difference.
import {type C, type E, type Law, type Machine, type Request, type State, evalC, interpret} from './machine.ts'
import {allowed} from './watch.ts'
import {type Goal, substC, substE} from '../kernel/kernel.ts'
import {REFUTED, growCdcl} from '../kernel/cdcl.ts'
import {clock} from '../kernel/prove.ts'
import {relax, replay} from './bmc.ts'
import {fromTree, refute} from './interp.ts'

export type TpaResult = {run: {params: Record<string, number>, trace: Request[]}, level: number}
  | {inv: C[], level: number}
  | {why: string, level: number}
export type TpaOptions = {until: number, wall?: number, levels?: number, kinds?: C[], progress?: (level: number, what: string) => void}

const v = (name: string): E => ({op: 'var', name}), kE = (value: number): E => ({op: 'const', value})
const and = (xs: C[]): C => (xs.length === 1 ? xs[0]! : {op: 'and', xs})
const tops = (c: C): C[] => (c.op === 'and' ? c.xs.flatMap(tops) : [c])

export function tpa(m: Machine, law: Law, opts: TpaOptions): TpaResult {
  if (Object.keys(m.maps ?? {}).length || Object.keys(m.step.flags ?? {}).length || m.params.length || m.history || m.inputMaps?.length) return {why: 'not a plain machine', level: 0}
  const names = Object.keys(m.state), over = () => clock() > opts.until || (opts.wall !== undefined && performance.now() > opts.wall)
  const budget = {until: opts.until, ...(opts.wall !== undefined ? {wall: opts.wall} : {})}
  const at = (j: number) => (n: string) => `${n}~${j}`
  // A condition over the state at copy j; a relation (n before, n' after) between copies i and j.
  const stateAt = (c: C, j: number): C => substC(c, {vars: Object.fromEntries(names.map(n => [n, v(at(j)(n))])), maps: {}, flags: {}})
  const relAt = (c: C, i: number, j: number): C => substC(c, {vars: Object.fromEntries(names.flatMap(n => [[n, v(at(i)(n))], [`${n}'`, v(at(j)(n))]])), maps: {}, flags: {}})
  const bad: C = {op: 'not', x: law.holds}
  let tags = 0
  // One step or none from copy i to i + 1: a yes/no s chooses none; a pair's truncated difference stays one (relax).
  const step = (i: number): C[] => {
    const t = ++tags, s = v(`s@${t}`), none: C = {op: '=', a: s, b: kE(1)}
    const sub = {vars: {...Object.fromEntries(names.map(n => [n, v(at(i)(n))])), ...Object.fromEntries(m.inputs.map(n => [n, v(`${n}@${t}`)]))}, maps: {}, flags: {}}
    const out: C[] = [{op: '<=', a: s, b: kE(1)}, ...(m.assume ? [{op: 'or', xs: [none, substC(m.assume, sub)]} as C] : [])]
    for (const n of names) {
      const e = m.step.state?.[n] ?? v(n), pn = n.endsWith('$neg') ? n.slice(0, -4) : `${n}$neg`, before = v(at(i)(n))
      const kept: E = e.op === 'sub' && pn in m.state
        ? {op: 'sub', a: {op: 'if', c: none, then: before, else: substE(e.a, sub)}, b: {op: 'if', c: none, then: v(at(i)(pn)), else: substE(e.b, sub)}}
        : {op: 'if', c: none, then: before, else: substE(e, sub)}
      out.push({op: '=', a: v(at(i + 1)(n)), b: kept})
    }
    return out
  }
  const kinds = (j: number): C[] => (opts.kinds ?? []).map(c => stateAt(c, j))
  // R_n, n >= 1: the conjuncts learned (relations over n and n').
  const R: C[][] = []
  const rel = (n: number, i: number): C[] => (n === 0 ? step(i) : (R[n] ?? []).map(c => relAt(c, i, i + 1)))
  // A state as a condition (every value), and a model's state at copy j as one (each integer's pair by its difference).
  const pointOf = (st: State): C => and(names.map((n): C => ({op: '=', a: v(n), b: kE(st.scalars[n] ?? 0)})))
  const middleOf = (w: Record<string, number>, j: number): C => and(names.filter(n => !n.endsWith('$neg')).map((n): C => {
    const x = w[at(j)(n)] ?? 0, pn = `${n}$neg`
    if (!(pn in m.state)) return {op: '=', a: v(n), b: kE(x)}
    const d = x - (w[at(j)(pn)] ?? 0)
    return d >= 0 ? {op: '=', a: v(n), b: {op: 'add', a: v(pn), b: kE(d)}} : {op: '=', a: {op: 'add', a: v(n), b: kE(-d)}, b: v(pn)}
  }))
  const it = interpret(m)
  type Reach = {steps: Request[], end: State} | 'no' | 'unknown'
  // Is D reached from the state s within 2^{n+1} steps? The run's requests and the state it ends in.
  const reach = (n: number, s: State, D: C, depth: number): Reach => {
    const S = pointOf(s)
    for (let tries = 0; tries < 64; tries++) {
      if (over()) return 'unknown'
      tags = 0
      const a = [...rel(n, 0), ...rel(n, 1), ...kinds(1)], b = [stateAt(S, 0), stateAt(D, 2)]
      // (relax keeps the other hypotheses as they are and adds the pairs' equations, each a step's: A's)
      const hyps = relax([...a, ...b]) ?? [...a, ...b], bs = new Set(b), isA = (h: number) => !bs.has(hyps[h]!)
      const goal: Goal = {name: `tpa ${n}`, hyps}
      const out = refute(goal, budget)
      if (!('tree' in out)) {
        if (out.stuck !== 'sat' || !out.witness) return 'unknown'
        const w = out.witness
        if (n === 0) {
          const steps: Request[] = []
          for (let t = 1; t <= 2; t++) if ((w[`s@${t}`] ?? 0) === 0) steps.push(Object.fromEntries(m.inputs.map(x => [x, Math.max(0, Math.round(w[`${x}@${t}`] ?? 0))])) as Request)
          const end = taken(s, steps)
          if (end && evalC(D, {}, end, m)) return {steps, end}
          return 'unknown'
        }
        const r1 = reach(n - 1, s, middleOf(w, 1), depth + 1)
        if (r1 === 'unknown') return r1
        if (r1 === 'no') continue
        const r2 = reach(n - 1, r1.end, D, depth + 1)
        if (r2 === 'unknown') return r2
        if (r2 === 'no') continue
        return {steps: [...r1.steps, ...r2.steps], end: r2.end}
      }
      const itp = fromTree(goal, out.tree, isA, opts.wall)
      if (!itp) return 'unknown'
      const back = {vars: Object.fromEntries(names.flatMap(x => [[at(0)(x), v(x)], [at(2)(x), v(`${x}'`)]])), maps: {}, flags: {}}
      ;(R[n + 1] ??= []).push(...tops(substC(itp, back)))
      return 'no'
    }
    return 'unknown'
  }
  // The state the interpreter reaches from s by the requests (undefined where it refuses one).
  const taken = (s: State, steps: Request[]): State | undefined => {
    let st = s
    try { for (const input of steps) { if (!allowed(m, it, {}, st, input)) return undefined; st = it.step({}, st, input) } } catch (e) { if (e instanceof RangeError) return undefined; throw e }
    return st
  }
  // Houdini over R_{n+1} read from the start: the conjuncts a step keeps, by the CDCL search for a model alone.
  const invariant = (n: number): C[] | undefined => {
    const fromStart = (R[n + 1] ?? []).map(c => substC(c, {vars: Object.fromEntries(names.flatMap(x => [[x, (m.state[x] ?? kE(0))], [`${x}'`, v(x)]])), maps: {}, flags: {}}))
    let kept = fromStart
    for (let changed = true; changed && kept.length;) {
      changed = false
      for (const c of [...kept]) {
        if (over()) return undefined
        tags = 0
        const hyps0 = [...kept.map(k => stateAt(k, 0)), ...kinds(0), ...step(0), {op: 'not', x: stateAt(c, 1)} as C]
        const hyps = relax(hyps0) ?? hyps0
        const out = growCdcl({name: 'tpa houdini', hyps: [...hyps, {op: '=', a: v('s@1'), b: kE(0)}]}, new Map(), {nodes: 0, until: opts.until}, {model: true, ...(opts.wall !== undefined ? {wall: opts.wall} : {})})
        if ('tree' in out || out.why === REFUTED) continue
        if (out.stuck === 'unknown') return undefined
        kept = kept.filter(k => k !== c); changed = true
      }
    }
    // The law where the kept hold.
    const safe = growCdcl({name: 'tpa safe', hyps: [...kept, ...(opts.kinds ?? []), bad]}, new Map(), {nodes: 0, until: opts.until}, {model: true, ...(opts.wall !== undefined ? {wall: opts.wall} : {})})
    return ('tree' in safe || safe.why === REFUTED) && kept.length ? kept : undefined
  }
  for (let n = 0; n <= (opts.levels ?? 20); n++) {
    const r = reach(n, it.init({}), bad, 0)
    opts.progress?.(n, typeof r === 'object' ? 'reached' : r)
    if (r === 'unknown') return {why: 'the budget', level: n}
    if (typeof r === 'object') {
      const run = {params: {}, trace: r.steps}, broken = replay(m, [law], run)
      return broken ? {run: {params: {}, trace: r.steps.slice(0, broken.steps)}, level: n} : {why: 'a run the interpreter refuses', level: n}
    }
    const inv = invariant(n)
    if (inv) return {inv, level: n}
  }
  return {why: 'no level left', level: opts.levels ?? 20}
}
