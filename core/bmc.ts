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
// Before the search each goal is made smaller, keeping its models (`reduce`): a name equal to another name or a constant
// replaced by it, and a definition (n = e) of a name nothing else reads dropped (the cone of influence: a state value no
// later step and no law reads, a request value only its own equation reads), each name put back into the model from
// its definition. And it is first asked relaxed (`relax`): an integer is a pair of naturals (n, n$neg) normalized where
// it is written (n = a ∸ b, n$neg = b ∸ a: one case of the kernel's per pair and step), and every read of a pair is of
// its difference (dsl.ts's Int: sums, comparisons, products by constants, remainders and quotients alike), so the pair
// written as any two naturals of difference a − b (n + b = a + n$neg) is the same integer to every later read. The
// relaxed goal has every model of the goal; a run it gives is taken by the interpreter, which normalizes, and where
// that run breaks no law (a read of a pair the relaxation doesn't keep), the goal itself is asked at that depth. A
// relaxed goal refuted is the goal refuted.
//
// The budget is read off prove.ts's clock inside `counted` (the kernel's work, bmcRate units a millisecond), so the
// search is the same on any machine; a wall-clock stop beside it (`wall`) is for callers under a wall-clock limit.
import {type C, type E, type Law, type Machine, type Request, type State, evalC, evalE, interpret, isArithmetic, loadJs, numbersOf} from './machine.ts'
import {stepLawObligations, substC, substE} from '../kernel/kernel.ts'
import {clock, counted} from '../kernel/prove.ts'
import {REFUTED, cdclSession, growCdcl} from '../kernel/cdcl.ts'
import type {Outcome} from '../kernel/prove.ts'
import {allowed} from './watch.ts'
import {isF as isFalse, isT as isTrue, simpC, simpE} from './nonterm.ts'
import {env, linOfE, plus, vars} from './solver.ts'

export type BoundedRun = {law: string, depth: number, witness: Record<string, number>, params: Record<string, number>, trace: Request[]}
export type BmcOptions = {
  ms: number // the budget, counted (bmcRate units a millisecond of the kernel's work)
  wall?: number // a stop, in wall time (performance.now())
  from?: number // the first depth (1)
  depth?: number // the last depth (64, the kernel's bound)
  progress?: (depth: number, outcome: 'refuted' | 'sat' | 'unknown', ms: number) => void
  steps?: boolean // (findBoundedRun, with no wall stop) the forced run's share counted in its steps, forcedRate a millisecond
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
// did on the k-step goals of CHC-COMP's unsat LIA-Lin tasks, the stage alone (runs/bmc2/only-mine3: 1,215 depths past
// 200 ms, 252 units a ms at the median, 383 at the 90th percentile; 168 at the median before reader.ts kept its clean
// values and the goals were reduced, runs/bmc2/only-base1). The CDCL search counts its rows, which a goal of many atoms
// and few rows a node keeps low, so a caller under a wall-clock limit gives a wall stop too.
export const bmcRate = 250
// A forced run's share of the budget, and its steps at most (a derivation checkDerivation replays step by step).
const forcedShare = 0.3, forcedSteps = 1_000_000, forcedRate = 1_000
// GDP_BMC_RELAX=0: no relaxed goal first; GDP_BMC_INC=0: each depth's goal a search of its own (for comparing).
const useRelax = env.GDP_BMC_RELAX !== '0', useInc = env.GDP_BMC_INC !== '0', useTidy = env.GDP_BMC_TIDY !== '0'

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
const top = (c: C): C[] => (c.op === 'and' ? c.xs.flatMap(top) : [c])
export function fixed(hyps: C[]): {hyps: C[], fixed: Record<string, number>} | undefined {
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

// Each name's occurrences in some terms (a goal's terms are trees as the kernel reads them).
const occurrences = (xs: (C | E)[], out = new Map<string, number>()): Map<string, number> => {
  const go = (x: C | E): void => {
    switch (x.op) {
      case 'var': out.set(x.name, (out.get(x.name) ?? 0) + 1); return
      case 'const': case 'flag': return
      case 'add': case 'sub': case 'min': case 'max': case 'prod': case '<': case '<=': case '=': go(x.a); go(x.b); return
      case 'mul': go(x.a); return
      case 'if': go(x.c); go(x.then); go(x.else); return
      case 'get': go(x.key); return
      case 'and': case 'or': x.xs.forEach(go); return
      case 'not': go(x.x); return
      case 'all': go(x.c); return
    }
  }
  xs.forEach(go)
  return out
}

// The goal tidied, keeping its models (`tidy`): a comparison whose sides differ by a constant (x5 = 10 + x5, the CHC's
// pairs read on both sides) folded to its truth, and a yes/no copied through an if (b~1 = if y = 1 then 1 else 0, how a
// CHC Bool argument is written) read as the copy itself where y is a yes/no (0 or 1: an input the assumption bounds by 1,
// or a state value every step writes as one), so `reduce` puts it in. Each step's yes/no values are the inputs a
// hypothesis bounds by 1 and the names an equation gives a 0/1 value.
const diffConst = (a: E, b: E): number | undefined => {
  const l = linOfE(a), r = l && linOfE(b), d = r && plus(l, r, -1)
  return d && !vars(d).length ? d['1'] ?? 0 : undefined
}
const T0: C = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}, F0: C = {op: '<', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
export function tidier(bools: Set<string>) {
  const memo = new WeakMap<object, E | C>()
  const isBool = (e: E): boolean => (e.op === 'const' ? e.value === 0 || e.value === 1 : e.op === 'var' ? bools.has(e.name) : e.op === 'if' ? isBool(e.then) && isBool(e.else) : false)
  const oneOf = (c: C): string | undefined => (c.op === '=' && c.a.op === 'var' && bools.has(c.a.name) && c.b.op === 'const' && c.b.value === 1 ? c.a.name : c.op === '=' && c.b.op === 'var' && bools.has(c.b.name) && c.a.op === 'const' && c.a.value === 1 ? c.b.name : undefined)
  const e1 = (e: E): E => {
    const hit = memo.get(e)
    if (hit) return hit as E
    let out: E = e
    switch (e.op) {
      case 'add': case 'sub': case 'min': case 'max': case 'prod': { const a = e1(e.a), b = e1(e.b); if (a !== e.a || b !== e.b) out = {...e, a, b}; break }
      case 'mul': { const a = e1(e.a); if (a !== e.a) out = {...e, a}; break }
      case 'if': {
        const c = c1(e.c), t = e1(e.then), f = e1(e.else), v = oneOf(c)
        if (v !== undefined && t.op === 'const' && t.value === 1 && f.op === 'const' && f.value === 0) out = {op: 'var', name: v}
        else if (c.op === '<=' && c.a.op === 'const' && c.b.op === 'const') out = c.a.value <= c.b.value ? t : f
        else if (c.op === '<' && c.a.op === 'const' && c.b.op === 'const') out = c.a.value < c.b.value ? t : f
        else if (c !== e.c || t !== e.then || f !== e.else) out = {op: 'if', c, then: t, else: f}
        break
      }
      case 'get': { const key = e1(e.key); if (key !== e.key) out = {...e, key}; break }
      case 'var': case 'const': break
    }
    memo.set(e, out)
    return out
  }
  const c1 = (c: C): C => {
    const hit = memo.get(c)
    if (hit) return hit as C
    let out: C = c
    switch (c.op) {
      case '<=': case '<': case '=': {
        const a = e1(c.a), b = e1(c.b), d = diffConst(a, b)
        if (d !== undefined) out = (c.op === '<=' ? d <= 0 : c.op === '<' ? d < 0 : d === 0) ? T0 : F0
        else if (a !== c.a || b !== c.b) out = {op: c.op, a, b}
        break
      }
      case 'and': case 'or': { const xs = c.xs.map(c1); if (xs.some((x, i) => x !== c.xs[i])) out = simpC({op: c.op, xs}); break }
      case 'not': { const x = c1(c.x); if (x !== c.x) out = simpC({op: 'not', x}); break }
      case 'flag': case 'all': break
    }
    memo.set(c, out)
    return out
  }
  // Learns the yes/no names of some hypotheses (a bound by 1, an equation giving a 0/1 value), then tidies them.
  return (cs: C[]): C[] => {
    for (const c of cs) {
      if (c.op === '<=' && c.a.op === 'var' && c.b.op === 'const' && c.b.value <= 1) bools.add(c.a.name)
      if (c.op === '<' && c.a.op === 'var' && c.b.op === 'const' && c.b.value <= 2) bools.add(c.a.name)
    }
    for (let again = true; again;) {
      again = false
      for (const c of cs) if (c.op === '=' && c.a.op === 'var' && !bools.has(c.a.name) && isBool(e1(c.b))) { bools.add(c.a.name); again = true }
    }
    return cs.map(c1)
  }
}

// The goal relaxed (above): each pair written normalized at a step (n = a ∸ b and n$neg = b ∸ a, its partner the name
// with $neg before the step's ~j) as one equation of differences.
const partnerOf = (n: string) => (n.includes('$neg') ? undefined : n.replace(/(~\d+)?$/, j => `$neg${j}`))
const alike = (a: E, b: E) => a === b || JSON.stringify(a) === JSON.stringify(b)
export function relax(hyps: C[]): C[] | undefined {
  const defs = new Map<string, {h: C, e: {a: E, b: E}}>()
  for (const h of hyps) if (h.op === '=' && h.a.op === 'var' && h.b.op === 'sub') defs.set(h.a.name, {h, e: h.b})
  const gone = new Set<C>(), out: C[] = []
  for (const [n, {h, e}] of defs) {
    const p = partnerOf(n), d = p === undefined ? undefined : defs.get(p)
    if (!d || !alike(e.a, d.e.b) || !alike(e.b, d.e.a)) continue
    gone.add(h); gone.add(d.h)
    out.push({op: '=', a: {op: 'add', a: {op: 'var', name: n}, b: e.b}, b: {op: 'add', a: e.a, b: {op: 'var', name: p!}}})
  }
  return out.length ? [...hyps.filter(h => !gone.has(h)), ...out] : undefined
}

// The goal made smaller with its models kept (above): the hypotheses left, and the names taken out with their terms,
// in the order taken (a later one's term may read an earlier one's name, never the other way), or undefined where a
// hypothesis folds to false.
export function reduce(hyps: C[]): {hyps: C[], defs: [string, E][]} | undefined {
  let cs = hyps
  const defs: [string, E][] = []
  for (;;) {
    const n = occurrences(cs), sub: Record<string, E> = {}, drop = new Set<C>()
    for (const h of cs) {
      if (h.op !== '=') continue
      for (const [a, e] of [[h.a, h.b], [h.b, h.a]] as const) {
        if (a.op !== 'var' || a.name in sub || occurrences([e]).has(a.name)) continue
        const copy = (e.op === 'var' && !(e.name in sub)) || e.op === 'const'
        if (n.get(a.name) !== 1 && !copy) continue
        drop.add(h); defs.push([a.name, e])
        if (copy) sub[a.name] = e
        break
      }
    }
    if (!drop.size) return {hyps: cs, defs}
    // (a copy's name may be another's copy: each replaced by the end of its chain)
    for (const n0 of Object.keys(sub)) { let e = sub[n0]!; for (let i = 0; e.op === 'var' && sub[e.name] && i < 64; i++) e = sub[e.name]!; sub[n0] = e }
    const s = {vars: sub, maps: {}, flags: {}}, any = Object.keys(sub).length > 0
    cs = cs.filter(h => !drop.has(h)).map(h => (any ? simpC(substC(h, s)) : h)).flatMap(top)
    if (cs.some(isFalse)) return undefined
    cs = cs.filter(c => !isTrue(c))
  }
}
// A model's names taken out put back, the last taken first (each term read at the model, a name it doesn't give 0).
export function putBack(m: Machine, w: Record<string, number>, defs: [string, E][]): Record<string, number> {
  const out = {...w}
  for (const [n, e] of [...defs].reverse()) {
    for (const x of occurrences([e]).keys()) if (!(x in out)) out[x] = 0
    try { out[n] = evalE(e, out, {scalars: {}, maps: {}}, m) } catch { out[n] = 0 }
  }
  return out
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

// A forced run: from the start, each step the one the rule allows (a machine without params whose requests choose among
// a few cases, each request value below a bound its assumption states, the others 0), taken by the compiled rule until a
// step breaks a law, the run reaches a state with no way on, or `steps` or `wall` runs out. A step is forced where one
// case moves the state and that case reads no other request value; at most `guesses` steps aren't (a start of free
// values taken as 0, two ways on taken by the first). A deterministic loop's long runs (CHC-COMP's s_split: 10,002
// steps; the k-step goals fold to false without a case past depth 64) are its runs; a machine whose steps read their
// requests stops within a few steps. The run, as a bounded run's.
export function forcedRun(m: Machine, laws: Law[], opts: {steps: number, wall: number, guesses?: number}): BoundedRun | undefined {
  const out = forcedRunner(m, laws, opts)?.(opts.wall)
  return typeof out === 'object' ? out : undefined
}
// The same run, resumable: each call goes on from where the last stopped, until `wall`: the run, or 'over' (no way on,
// a guess too many, its steps spent), or 'paused' (the wall reached first). Undefined where it doesn't apply.
type Forced = (wall: number) => BoundedRun | 'over' | 'paused'
function forcedRunner(m: Machine, laws: Law[], opts: {steps: number, guesses?: number}): Forced | undefined {
  if (m.params.length || !laws.length || !bmcFits(m, laws)) return undefined
  // Each input bounded by the assumption (a top-level i < c or i <= c, c at most 64): its values; the others free.
  const bound = new Map<string, number>()
  for (const c of m.assume ? top(m.assume) : []) if ((c.op === '<' || c.op === '<=') && c.a.op === 'var' && c.b.op === 'const' && m.inputs.includes(c.a.name)) bound.set(c.a.name, Math.min(bound.get(c.a.name) ?? Infinity, c.op === '<' ? c.b.value : c.b.value + 1))
  const finite = m.inputs.filter(i => (bound.get(i) ?? Infinity) <= 64), free = m.inputs.filter(i => !finite.includes(i))
  let choices: Record<string, number>[] = [{}]
  for (const i of finite) { const n = bound.get(i)!; choices = choices.flatMap(ch => Array.from({length: n}, (_, v) => ({...ch, [i]: v}))); if (choices.length > 256) return undefined }
  // Whether a case reads a free value: its assumption and updates with the case put in.
  // (the step's flags put in first: each a condition of the step, read where the terms read it, and each over the flags
  // before it, as kernel.ts's flagsOf reads them)
  const inlined: Record<string, C> = {}
  for (const [f, c] of Object.entries(m.step.flags ?? {})) inlined[f] = substC(c, {vars: {}, maps: {}, flags: inlined})
  const flags = {vars: {}, maps: {}, flags: inlined}
  const assume = m.assume && substC(m.assume, flags)
  const conds: C[] = assume ? [assume] : [], updates = Object.values(m.step.state ?? {}).map(e => substE(e, flags))
  const reads = choices.map(ch => {
    const s = {vars: Object.fromEntries(Object.entries(ch).map(([n, v]) => [n, {op: 'const', value: v} as E])), maps: {}, flags: {}}
    const ns = occurrences([...conds.map(c => simpC(substC(c, s))), ...updates.map(e => simpE(substE(e, s)))])
    return free.some(i => ns.has(i))
  })
  // Each case's assumption's top-level equations of a state value and a constant (where a CHC clause's body is), read
  // before the step is taken.
  const at = choices.map(ch => {
    const s = {vars: Object.fromEntries(Object.entries(ch).map(([n, v]) => [n, {op: 'const', value: v} as E])), maps: {}, flags: {}}
    return (assume ? top(simpC(substC(assume, s))) : []).flatMap(c => (c.op === '=' && c.a.op === 'var' && c.a.name in m.state && c.b.op === 'const' ? [[c.a.name, c.b.value] as const] : []))
  })
  // The rule with its assumption as a value (bmc$ok: 1 where the request is allowed), so a refused request throws nothing.
  const ok = 'bmc$ok'
  if (ok in m.state) return undefined
  let js
  try { js = loadJs({...m, state: {...m.state, [ok]: {op: 'const', value: 1}}, step: {...m.step, state: {...m.step.state, [ok]: m.assume ? {op: 'if', c: m.assume, then: {op: 'const', value: 1}, else: {op: 'const', value: 0}} : {op: 'const', value: 1}}}, assume: undefined}) } catch { return undefined }
  const same = (a: State, b: State) => { for (const key in a.scalars) if (key !== ok && a.scalars[key] !== b.scalars[key]) return false; return true }
  const take = (st: State, input: Request): State | undefined => { try { const next = js.step({}, js.fork(st), input); return next.scalars[ok] === 1 ? next : undefined } catch (e) { if (e instanceof RangeError) return undefined; throw e } }
  const broken = (st: State) => laws.find(l => !evalC(l.holds, {}, st, m))?.name
  const requests = choices.map(ch => ({...Object.fromEntries(free.map(i => [i, 0])), ...ch}) as Request)
  let st: State = js.init({}), guesses = opts.guesses ?? 2, n = 0, over = false
  const trace: Request[] = []
  return (wall: number) => {
    if (over) return 'over'
    for (; n < opts.steps; n++) {
      if (!(n % 256) && performance.now() >= wall) return 'paused'
      let next: State | undefined, request: Request | undefined, forced = true
      for (const [j, input] of requests.entries()) {
        if (at[j]!.some(([x, v]) => st.scalars[x] !== v)) continue
        const a = take(st, input)
        if (!a) continue
        const law = broken(a)
        if (law !== undefined) { const {[ok]: _, ...before} = st.scalars; over = true; return {law, depth: n + 1, witness: {...before, ...numbersOf(input)}, params: {}, trace: [...trace, input]} }
        if (same(a, st)) continue
        if (reads[j]) forced = false
        if (!next) { next = a; request = input } else if (!same(next, a)) forced = false
      }
      if (!next || (!forced && --guesses < 0)) { over = true; return 'over' }
      trace.push(request!); st = next
    }
    over = true
    return 'over'
  }
}

// The deeper goals as one growing goal, for one CDCL search kept from depth to depth (kernel/cdcl.ts's cdclSession):
// each step's hypotheses written once, in names that stay (the state after step j as n~j, the j-th request as input@j),
// relaxed and folded as above (each name of the step a constant or another name fixes put in, never one of an earlier
// step's), and each depth's last state breaking a law a hypothesis of its own, `act@k >= 1 or <the law broken at ~k>`,
// assumed by act@k <= 0 at depth k and set aside (act@k >= 1) at depth k + 1. Every clause the search learns is then a
// consequence of the hypotheses it has, at every later depth too. For machines whose goals read no function and no
// flag (whose kernel goals carry no fact this one would lack); the others, and a relaxed model the interpreter refuses,
// are asked as before, depth by depth.
function unrolled(m: Machine, laws: Law[]) {
  const goal = {name: 'a bounded run', hyps: [] as C[]}, sub: Record<string, E> = {}, defs: [string, E][] = []
  const v = (name: string): E => ({op: 'var', name}), K = (value: number): E => ({op: 'const', value})
  const stateAt = (j: number): Record<string, E> => Object.fromEntries(Object.keys(m.state).map(n => [n, j === 0 ? m.state[n]! : v(`${n}~${j}`)]))
  const put = (c: C): C => simpC(substC(c, {vars: sub, maps: {}, flags: {}}))
  let k = 0, dead = false
  const session = cdclSession(goal, new Map(), {model: true}), tidy = useTidy ? tidier(new Set()) : (cs: C[]) => cs
  // The cone of influence: the state values the laws, the assumption or the precondition read, and those the updates of
  // these read, again until no more; the others' terms are left out at every step (no hypothesis reads them, and the
  // interpreter takes the run's own values).
  const live = new Set<string>(), names = (xs: (C | E)[]) => [...occurrences(xs).keys()].filter(n => n in m.state)
  const todo = names([...laws.map(l => l.holds), ...(m.assume ? [m.assume] : []), ...(m.pre ? [m.pre] : [])])
  while (todo.length) { const n = todo.pop()!; if (live.has(n)) continue; live.add(n); todo.push(...names([m.step.state?.[n] ?? v(n)])) }
  // Step j's hypotheses: its request allowed, each state value its term; folded; undefined where they can't hold.
  const step = (j: number): C[] | undefined => {
    const before = stateAt(j - 1), inputs = Object.fromEntries(m.inputs.map(i => [i, v(j === 1 ? i : `${i}@${j}`)]))
    const at = {vars: {...before, ...inputs}, maps: {}, flags: {}}
    const own = new Set([...Object.values(inputs).map(e => (e as {name: string}).name), ...Object.keys(m.state).map(n => `${n}~${j}`)])
    const raw: C[] = [...(j === 1 && m.pre ? [m.pre] : []), ...(m.assume ? [substC(m.assume, at)] : []), ...[...live].map((n): C => ({op: '=', a: v(`${n}~${j}`), b: substE(m.step.state?.[n] ?? v(n), at)}))]
    let cs = (useRelax ? relax(raw) : undefined) ?? raw
    for (;;) {
      cs = tidy(cs.map(put).flatMap(top)).flatMap(top)
      if (cs.some(isFalse)) return undefined
      cs = cs.filter(c => !isTrue(c))
      // (each round, every name of this step that an equation gives a constant or another name, put in at once)
      const now: Record<string, E> = {}, used = new Set<C>()
      for (const c of cs) {
        if (c.op !== '=') continue
        const free = (x: E) => x.op === 'var' && own.has(x.name) && !(x.name in sub) && !(x.name in now)
        const [n, e] = free(c.a) && (c.b.op === 'const' || (c.b.op === 'var' && c.b.name !== (c.a as {name: string}).name && !(c.b.name in now))) ? [(c.a as {name: string}).name, c.b] : free(c.b) && c.a.op === 'const' ? [(c.b as {name: string}).name, c.a] : []
        if (n === undefined) continue
        now[n] = e!; used.add(c)
      }
      if (!Object.keys(now).length) return cs
      // (a name another of this round's names is: the end of the chain)
      for (const n of Object.keys(now)) { let e = now[n]!; for (let i = 0; e.op === 'var' && now[e.name] && i < 64; i++) e = now[e.name]!; now[n] = e }
      for (const [n, e] of Object.entries(now)) { sub[n] = e; defs.push([n, e]) }
      for (const x of Object.keys(sub)) { const e = sub[x]!; if (e.op === 'var' && e.name in now) sub[x] = now[e.name]! }
      cs = cs.filter(c => !used.has(c))
    }
  }
  // The next depth: its hypotheses added, and asked; the query folded to false is refuted with no search.
  const next = (b: {nodes: number, until?: number}, wall?: number): {k: number, out: Outcome | 'refuted' | 'impossible'} => {
    k++
    if (dead) return {k, out: 'impossible'}
    const cs = step(k)
    if (!cs) { dead = true; return {k, out: 'impossible'} }
    if (k > 1) goal.hyps.push({op: '<=', a: K(1), b: v(`act@${k - 1}`)})
    goal.hyps.push(...cs)
    const query = put(substC({op: 'not', x: {op: 'and', xs: laws.map(l => l.holds)}}, {vars: stateAt(k), maps: {}, flags: {}}))
    if (isFalse(query)) return {k, out: 'refuted'}
    goal.hyps.push({op: 'or', xs: [{op: '<=', a: K(1), b: v(`act@${k}`)}, query]})
    return {k, out: session.run(b, wall, {[`act@${k}`]: 1})}
  }
  // The same depth's query asked again (its search cut short by its budget), its hypotheses already in.
  const again = (b: {nodes: number, until?: number}, wall?: number): {k: number, out: Outcome | 'refuted' | 'impossible'} => ({k, out: dead ? 'impossible' : session.run(b, wall, {[`act@${k}`]: 1})})
  return {next, again, defs}
}

export function findBoundedRun(m: Machine, laws: Law[], opts: BmcOptions): BoundedRun | undefined {
  // A forced run first, within forcedShare of the budget (as wall time: it is the compiled rule's, not the kernel's;
  // with `steps` and no wall stop, in its steps instead).
  const now = performance.now(), end = Math.min(opts.wall ?? Infinity, now + opts.ms), steps = opts.steps && opts.wall === undefined
  const out = boundedSearch(m, laws, {...opts, forcedMs: steps ? Infinity : forcedShare * (end - now), ...(steps ? {forcedSteps: Math.min(forcedSteps, Math.round(forcedShare * forcedRate * opts.ms))} : {})})?.run(opts.ms, opts.wall)
  return typeof out === 'object' ? out : undefined
}

// The same search, resumable (compare/chc/kind.ts gives it slices of a second CPU in turn with k-induction): each `run`
// goes on where the last stopped, within its own budget (`ms` counted, `wall`), and answers a run, 'over' (every depth
// up to the last refuted, or a search that can't go on) or 'paused' (its budget spent first: the depth it was asking is
// asked again next time, the CDCL session's learned clauses kept). The forced run has `forcedMs` of wall time in all,
// across runs. Undefined where the machine doesn't fit.
export type BoundedSearch = {run: (ms: number, wall?: number) => BoundedRun | 'over' | 'paused', depth: () => number}
export function boundedSearch(m: Machine, laws: Law[], opts: Omit<BmcOptions, 'ms' | 'wall'> & {forcedMs: number, forcedSteps?: number}): BoundedSearch | undefined {
  if (!laws.length || !bmcFits(m, laws)) return undefined
  const last = Math.min(64, opts.depth ?? 64)
  const forced = forcedRunner(m, laws, {steps: opts.forcedSteps ?? forcedSteps})
  let forcedLeft = forced === undefined ? 0 : opts.forcedMs, over = false, again = false
  let inc: ReturnType<typeof unrolled> | undefined, made = false, k = opts.from ?? 1
  const run = (ms: number, wall?: number): BoundedRun | 'over' | 'paused' => {
    if (over) return 'over'
    if (forced && forcedLeft > 0) {
      const t0 = performance.now(), out = forced(Math.min(wall ?? Infinity, t0 + forcedLeft))
      forcedLeft -= performance.now() - t0
      if (typeof out === 'object') { over = true; return out }
      if (out === 'over') forcedLeft = 0
      else if (wall !== undefined && performance.now() >= wall) return 'paused'
    }
    return counted(bmcRate, () => {
      const until = clock() + ms
      const late = () => clock() >= until || (wall !== undefined && performance.now() >= wall)
      if (!made) { made = true; inc = useInc && !(opts.from && opts.from > 1) && !Object.keys(m.fns ?? {}).length && !Object.keys(m.step.flags ?? {}).length ? unrolled(m, laws) : undefined }
      const done = (out: BoundedRun | 'over') => { over = true; return out }
      for (; k <= last; k++) {
        if (late()) return 'paused'
        const t0 = clock()
        if (inc) {
          const {out} = again ? inc.again({nodes: 0, until}, wall) : inc.next({nodes: 0, until}, wall)
          again = false
          if (out === 'impossible') { opts.progress?.(k, 'refuted', Math.round(clock() - t0)); return done('over') }
          if (out === 'refuted' || 'tree' in out || out.why === REFUTED) { opts.progress?.(k, 'refuted', Math.round(clock() - t0)); continue }
          if (out.stuck !== 'sat' || !out.witness) {
            opts.progress?.(k, 'unknown', Math.round(clock() - t0))
            if (out.why === 'time' && late()) { again = true; return 'paused' }
            return done('over')
          }
          const run = runOf(m, putBack(m, out.witness, inc.defs), k), broken = replay(m, laws, run)
          if (broken) { opts.progress?.(k, 'sat', Math.round(clock() - t0)); return done({law: broken.law, witness: broken.witness, depth: broken.steps, params: run.params, trace: run.trace.slice(0, broken.steps)}) }
          // (a model the interpreter refuses: the goal itself asked at this depth, below)
        }
        let goal
        try { goal = bmcGoal(m, laws, k) } catch { return done('over') }
        const f = fixed(goal.hyps)
        if (!f) { opts.progress?.(k, 'refuted', Math.round(clock() - t0)); continue }
        // The goal asked (relaxed or as it is), reduced: refuted, or a run that breaks a law, or neither (undefined).
        const ask = (hyps: C[]): 'refuted' | 'sat' | 'unknown' | BoundedRun => {
          const r = reduce(hyps)
          if (!r) return 'refuted'
          const out = growCdcl({name: goal.name, hyps: r.hyps}, new Map(), {nodes: 0, until}, {model: true, ...(wall !== undefined ? {wall} : {})})
          if ('tree' in out || out.why === REFUTED) return 'refuted'
          if (out.stuck !== 'sat' || !out.witness) return 'unknown'
          const run = runOf(m, putBack(m, {...out.witness, ...f.fixed}, r.defs), k), broken = replay(m, laws, run)
          return broken ? {law: broken.law, witness: broken.witness, depth: broken.steps, params: run.params, trace: run.trace.slice(0, broken.steps)} : 'sat'
        }
        const relaxed = useRelax && !inc ? relax(f.hyps) : undefined
        let got = relaxed ? ask(relaxed) : 'sat'
        if (got === 'sat') got = ask(f.hyps)
        // (out of its budget: this depth asked again next time; with a session, its query too, as it stands)
        opts.progress?.(k, typeof got === 'string' ? got : 'sat', Math.round(clock() - t0))
        if (got === 'unknown' && late()) { again = !!inc; return 'paused' }
        if (got === 'refuted') continue
        return done(typeof got === 'string' ? 'over' : got)
      }
      return done('over')
    })
  }
  return {run, depth: () => k}
}
