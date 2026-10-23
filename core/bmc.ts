// Bounded runs: a law broken by a run of k steps from the start, found by the prover's model search. Nothing here is
// trusted. The goal of depth k is the kernel's own k-step goal (kernel.ts's stepLawObligations, `steps: k`): its first
// `when` is the start (each state variable its start value over the params), its `then` the laws after the last step
// (primed names), refuted. Its constants are put in (`fixed`), and a model of it is asked of kernel/cdcl.ts's search
// over its atoms with the incremental simplex (`model`: a refutation isn't unfolded into a tree, and each decision's
// phase is the simplex's point's). The model names the params and each step's request; the run is then taken by the
// interpreter, each request checked against the rule's assumption, and kept only where it breaks a law. A goal refuted
// at depth k says no run of k steps breaks the laws; the depths grow until the budget, or 64 (the kernel's bound on k),
// runs out.
//
// The budget is read off prove.ts's clock inside `counted` (the kernel's work, bmcRate units a millisecond), so the
// search is the same on any machine; a wall-clock stop beside it (`wall`) is for callers under a wall-clock limit.
import {type C, type E, type Law, type Machine, type Request, type State, evalC, interpret, isArithmetic, numbersOf} from './machine.ts'
import {stepLawObligations, substC} from '../kernel/kernel.ts'
import {clock, counted} from '../kernel/prove.ts'
import {REFUTED, growCdcl} from '../kernel/cdcl.ts'
import {allowed} from './watch.ts'
import {simpC} from './nonterm.ts'

export type BoundedRun = {law: string, depth: number, witness: Record<string, number>, params: Record<string, number>, trace: Request[]}
export type BmcOptions = {
  ms: number // the budget, counted (bmcRate units a millisecond of the kernel's work)
  wall?: number // a stop, in wall time (performance.now())
  from?: number // the first depth (1)
  depth?: number // the last depth (64, the kernel's bound)
  progress?: (depth: number, outcome: 'refuted' | 'sat' | 'unknown', ms: number) => void
}

// Machines whose runs the goals describe as they are: scalars only (no maps, history or carried maps), no quantified
// flag, no function but division by a constant (whose facts fix its value); laws plain (no key, no "there exists").
export function bmcFits(m: Machine, laws: Law[]): boolean {
  if (Object.keys(m.maps ?? {}).length || m.history || m.inputMaps?.length) return false
  if (Object.values(m.step.flags ?? {}).some(f => f.op === 'all')) return false
  if (Object.keys(m.fns ?? {}).some(f => !isArithmetic(f))) return false
  if (JSON.stringify([m.state, m.step, m.assume ?? null, laws.map(l => l.holds)]).includes('"op":"prod"')) return false
  return laws.every(l => !l.forall && !l.some?.length)
}
// The counted clock's rate here, units of the kernel's work a millisecond: the median of what Modal's 2-vCPU containers
// did on the k-step goals of CHC-COMP's unsat LIA-Lin tasks (runs/unsat/bmc-only1: 1,462 depths past 200 ms, from 0 to
// 340 units a ms at the 90th percentile, 190 at the median). The CDCL search counts its rows, which a goal of many atoms
// and few rows a node keeps low, so a caller under a wall-clock limit gives a wall stop too.
export const bmcRate = 200

// The goal of depth k: a run of k steps from the start whose last state breaks a law.
export function bmcGoal(m: Machine, laws: Law[], k: number) {
  const start: C = {op: 'and', xs: Object.entries(m.state).map(([n, e]): C => ({op: '=', a: {op: 'var', name: n}, b: e}))}
  const after = {vars: Object.fromEntries(Object.keys(m.state).map(n => [n, {op: 'var', name: `${n}'`} as E])), maps: {}, flags: {}}
  const then: C = substC({op: 'and', xs: laws.map(l => l.holds)}, after)
  // Renamed: prove.ts keeps CDCL off goals named `@k steps` (for the size of their proofs); a model is all wanted here.
  const g = stepLawObligations(m, [], {}, {name: 'a bounded run', when: start, then, steps: k})[0]!
  return {name: `a bounded run of ${k}`, hyps: g.hyps}
}

// The goal with its constants put in: each name a hypothesis fixes (n = c, at the top) replaced by its value and the
// terms folded (core/nonterm.ts's simpC), until none is left; the names fixed, with their values (a model's part), or
// undefined where a hypothesis folds to false (no model).
export function fixed(hyps: C[]): {hyps: C[], fixed: Record<string, number>} | undefined {
  const top = (c: C): C[] => (c.op === 'and' ? c.xs.flatMap(top) : [c])
  const isFalse = (c: C) => (c.op === '<' || c.op === '<=') && c.a.op === 'const' && c.b.op === 'const' && (c.op === '<' ? c.a.value >= c.b.value : c.a.value > c.b.value)
  const isTrue = (c: C) => c.op === '<=' && c.a.op === 'const' && c.b.op === 'const' && c.a.value <= c.b.value
  const values: Record<string, number> = {}
  let cs = hyps.flatMap(top)
  for (;;) {
    const now: Record<string, E> = {}
    for (const c of cs) if (c.op === '=') {
      const [v, k] = c.a.op === 'var' && c.b.op === 'const' ? [c.a.name, c.b.value] : c.b.op === 'var' && c.a.op === 'const' ? [c.b.name, c.a.value] : []
      if (v !== undefined && !(v in now)) { now[v] = {op: 'const', value: k!}; values[v] = k! }
    }
    if (!Object.keys(now).length) return {hyps: cs, fixed: values}
    cs = cs.map(c => simpC(substC(c, {vars: now, maps: {}, flags: {}}))).flatMap(top)
    if (cs.some(isFalse)) return undefined
    cs = cs.filter(c => !isTrue(c))
  }
}

// The run a model names: the params, the first request by plain names, the j-th (j >= 2) as input@j.
export function runOf(m: Machine, w: Record<string, number>, k: number): {params: Record<string, number>, trace: Request[]} {
  const at = (n: string) => Math.max(0, Math.round(w[n] ?? 0))
  const params = Object.fromEntries(m.params.map(p => [p, at(p)]))
  const trace = Array.from({length: k}, (_, j) => Object.fromEntries(m.inputs.map(n => [n, at(j ? `${n}@${j + 1}` : n)])) as Request)
  return {params, trace}
}

// The run taken by the interpreter, up to the first step that breaks a law: the law, the steps, and the witness (the
// params, the state the last step starts from and its request), or undefined (a request refused, or no law broken).
export function replay(m: Machine, laws: Law[], run: {params: Record<string, number>, trace: Request[]}): {law: string, steps: number, witness: Record<string, number>} | undefined {
  const it = interpret(m)
  if (m.pre && !evalC(m.pre, run.params, {scalars: {}, maps: {}}, m)) return undefined
  try {
    let st: State = it.init(run.params)
    for (const [j, input] of run.trace.entries()) {
      if (!allowed(m, it, run.params, st, input)) return undefined
      const before = st
      st = it.step(run.params, st, input)
      const law = laws.find(l => !evalC(l.holds, {...run.params}, st, m))?.name
      if (law !== undefined) return {law, steps: j + 1, witness: {...run.params, ...before.scalars, ...numbersOf(input)}}
    }
    return undefined
  } catch (e) { if (e instanceof RangeError) return undefined; throw e }
}

export function findBoundedRun(m: Machine, laws: Law[], opts: BmcOptions): BoundedRun | undefined {
  if (!laws.length || !bmcFits(m, laws)) return undefined
  const last = Math.min(64, opts.depth ?? 64)
  return counted(bmcRate, () => {
    const until = clock() + opts.ms
    for (let k = opts.from ?? 1; k <= last && clock() < until && !(opts.wall !== undefined && performance.now() > opts.wall); k++) {
      const t0 = clock()
      let goal
      try { goal = bmcGoal(m, laws, k) } catch { return undefined }
      const f = fixed(goal.hyps)
      if (!f) { opts.progress?.(k, 'refuted', Math.round(clock() - t0)); continue }
      const out = growCdcl({name: goal.name, hyps: f.hyps}, new Map(), {nodes: 0, until}, {model: true, ...(opts.wall !== undefined ? {wall: opts.wall} : {})})
      const refuted = !('tree' in out) && out.why === REFUTED
      opts.progress?.(k, refuted ? 'refuted' : 'tree' in out ? 'refuted' : out.stuck, Math.round(clock() - t0))
      if (refuted || 'tree' in out) continue
      if (out.stuck !== 'sat' || !out.witness) return undefined
      const run = runOf(m, {...out.witness, ...f.fixed}, k), broken = replay(m, laws, run)
      return broken ? {law: broken.law, witness: broken.witness, depth: broken.steps, params: run.params, trace: run.trace.slice(0, broken.steps)} : undefined
    }
    return undefined
  })
}
