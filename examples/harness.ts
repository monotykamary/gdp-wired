// The examples' triple check. Every example is held to three independent witnesses:
//   1. the kernel: the prover's trees for every law, accepted by kernel.ts (and refused for every broken variant);
//   2. the runs: random runs of the interpreter and the generated JavaScript, which must agree step by step, with every
//      proven law holding in every state reached, and every broken variant actually broken by some run (a refused
//      proof alone could be the prover's weakness; a run that breaks the law is not);
//   3. Lean: lean-kernel/export-kernel.ts --examples <domain> sends the same trees to the Lean twin (checked on Modal).
// Decisions are sampled (given ⇒ then on every draw, a counterexample draw for a broken one); loops are run to the end,
// their invariants checked every turn and their rank seen to drop.
import {type C, type E, type Law, type Machine, type State, evalC, evalE, interpret, loadJs} from '../core/machine.ts'
import {type Decision, type LoopRule, type Rule, type StepLaw, type Verdict, proveDecision, proveLoop, proveRule, proveSteps} from '../core/dsl.ts'

// The builders' types are as wide as any example's; a case only needs what the harness reads.
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRule = Rule<any, any, any, any, any, any, any, any>
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyLoop = LoopRule<any, any, any>
export type Broken<T> = {name: string, why: string} & T
export type RuleCase = {kind: 'rule', name: string, about: string, rule: AnyRule, laws: Law[], steps?: StepLaw[], broken: Broken<{rule: AnyRule, laws: Law[], steps?: StepLaw[]}>[], bound?: number, depth?: number}
export type DecisionCase = {kind: 'decisions', name: string, about: string, decisions: Decision[], broken: Broken<{decision: Decision}>[], bound?: number}
export type LoopCase = {kind: 'loop', name: string, about: string, loop: AnyLoop, laws: Law[], broken: Broken<{loop: AnyLoop, laws: Law[]}>[], bound?: number}
export type Case = RuleCase | DecisionCase | LoopCase
export type Domain = {domain: string, about: string, cases: Case[]}

export const machineCase = (name: string, about: string, rule: AnyRule, laws: Law[], broken: Broken<{rule: AnyRule, laws: Law[], steps?: StepLaw[]}>[] = [], opts: {bound?: number, depth?: number, steps?: StepLaw[]} = {}): RuleCase => ({kind: 'rule', name, about, rule, laws, broken, ...opts})
export const decisionCase = (name: string, about: string, decisions: Decision[], broken: Broken<{decision: Decision}>[] = [], opts: {bound?: number} = {}): DecisionCase => ({kind: 'decisions', name, about, decisions, broken, ...opts})
export const loopCase = (name: string, about: string, loop: AnyLoop, laws: Law[], broken: Broken<{loop: AnyLoop, laws: Law[]}>[] = [], opts: {bound?: number} = {}): LoopCase => ({kind: 'loop', name, about, loop, laws, broken, ...opts})

export type Finding = {case: string, item: string, check: 'kernel' | 'runs' | 'counterexample', ok: boolean, detail: string}

let seed = 1
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
const empty: State = {scalars: {}, maps: {}}
const verdictText = (v: Verdict) => (v.proven ? (v.checked ? 'proven, kernel accepts' : 'proven, KERNEL REJECTS') : `not proven (${v.goal}: ${v.stuck})`)

// --- machines -----------------------------------------------------------------------------------------------------------

// Whether a request is allowed: the assumption, read with the request's queries and the step's flags decided.
function allowed(m: Machine, run: ReturnType<typeof interpret>, params: Record<string, number>, st: State, input: Record<string, number>): boolean {
  if (!m.assume) return true
  const env: Record<string, number> = {...params, ...input, ...run.queries(params, st, input)}
  for (const [name, c] of Object.entries(m.step.flags ?? {})) env[`?${name}`] = evalC(c, env, st, m) ? 1 : 0
  return evalC(m.assume, env, st, m)
}
const lawHolds = (m: Machine, law: Law, params: Record<string, number>, st: State, bound: number): boolean => {
  if (!law.forall) return evalC(law.holds, params, st, m)
  const keys = new Set<number>(Array.from({length: bound + 2}, (_, i) => i))
  for (const cells of Object.values(st.maps)) for (const key of cells.keys()) keys.add(key)
  return [...keys].every(key => evalC(law.holds, {...params, [law.forall!]: key}, st, m))
}
const cellsOf = (st: State) => JSON.stringify(Object.fromEntries(Object.entries(st.maps).map(([n, cells]) => [n, [...cells.entries()].sort((a, b) => a[0] - b[0])])))

type Run = {steps: number, mismatch?: string, violation?: {law: string, params: Record<string, number>, trace: Record<string, number>[]}}
// A step law over its last k steps (k = steps, default 1): each step's `when` read with the state it started from, its
// request, queries and flags; `then` with the state before the first (plain names), the first request and its flags, the
// j-th request as input@j, and the state and maps after the last (primed names).
type Taken = {before: State, input: Record<string, number>, after: State}
function stepHolds(m: Machine, run: ReturnType<typeof interpret>, sl: StepLaw, params: Record<string, number>, window: Taken[]): boolean {
  const k = sl.steps ?? 1
  if (window.length < k) return true
  const taken = window.slice(-k)
  const envOf = ({before, input}: Taken) => {
    const env: Record<string, number> = {...params, ...input, ...run.queries(params, before, input)}
    for (const [name, c] of Object.entries(m.step.flags ?? {})) env[`?${name}`] = evalC(c, env, before, m) ? 1 : 0
    return env
  }
  const whens = sl.when === undefined ? [] : Array.isArray(sl.when) ? sl.when : [sl.when]
  if (whens.some((w, j) => !evalC(w, envOf(taken[j]!), taken[j]!.before, m))) return true
  const env = envOf(taken[0]!)
  taken.slice(1).forEach((t, j) => { for (const [n, val] of Object.entries(envOf(t))) if (m.inputs.includes(n)) env[`${n}@${j + 2}`] = val })
  const before = taken[0]!.before, after = taken[k - 1]!.after
  const both: State = {
    scalars: {...before.scalars, ...Object.fromEntries(Object.entries(after.scalars).map(([n, v]) => [`${n}'`, v]))},
    maps: {...before.maps, ...Object.fromEntries(Object.entries(after.maps).map(([n, cells]) => [`${n}'`, cells]))},
  }
  const m2: Machine = {...m, maps: {...m.maps, ...Object.fromEntries(Object.entries(m.maps ?? {}).map(([n, init]) => [`${n}'`, init]))}}
  return evalC(sl.then, env, both, m2)
}
// Random runs from the start: params and requests drawn by their kinds (and filtered by pre and assume), the prune order
// sent nondecreasing; the interpreter and the compiled code stepped side by side; every law checked in every state.
export function runRule(rule: AnyRule, laws: Law[], opts: {trials: number, depth: number, bound: number}, stepLaws: StepLaw[] = []): Run {
  const m = rule.machine, run = interpret(m), gen = loadJs(m), order = rule.orderedBy
  let steps = 0
  for (let trial = 0; trial < opts.trials; trial++) {
    const params = rule.randomParams(rand, opts.bound)
    if (m.pre && !evalC(m.pre, params, empty, m)) continue
    let st = run.init(params), g = gen.init(params)
    const trace: Record<string, number>[] = [], window: Taken[] = []
    for (const law of laws) if (!lawHolds(m, law, params, st, opts.bound)) return {steps, violation: {law: law.name, params, trace}}
    let t = 0
    for (let i = 0, tries = 0; i < opts.depth && tries < opts.depth * 20; tries++) {
      const input = rule.randomInput(rand, opts.bound)
      if (order) input[order] = t + rand(3)
      if (!allowed(m, run, params, st, input)) continue
      if (order) t = input[order]!
      const before = st
      st = run.step(params, st, input)
      g = gen.step(params, g, input)
      trace.push(input)
      window.push({before, input, after: st})
      if (window.length > 16) window.shift()
      i++, steps++
      if (JSON.stringify(g.scalars) !== JSON.stringify(st.scalars) || cellsOf(g) !== cellsOf(st)) return {steps, mismatch: `compiled ${JSON.stringify(g.scalars)} vs interpreted ${JSON.stringify(st.scalars)} after ${JSON.stringify(trace)}`}
      for (const law of laws) if (!lawHolds(m, law, params, st, opts.bound)) return {steps, violation: {law: law.name, params, trace: [...trace]}}
      for (const sl of stepLaws) if (!stepHolds(m, run, sl, params, window)) return {steps, violation: {law: sl.name, params, trace: [...trace]}}
    }
  }
  return {steps}
}

// --- decisions ----------------------------------------------------------------------------------------------------------

type Draw = {steps: number, counterexample?: Record<string, number>}
export function sampleDecision(d: Decision, opts: {trials: number, bound: number}): Draw {
  const m = d.rule.machine
  let steps = 0
  for (let i = 0; i < opts.trials; i++) {
    const env = {...d.rule.randomParams(rand, opts.bound), ...d.rule.randomInput(rand, opts.bound)}
    if (!d.given.every(c => evalC(c, env, empty, m))) continue
    steps++
    if (!evalC(d.then, env, empty, m)) return {steps, counterexample: env}
  }
  return {steps}
}

// --- loops --------------------------------------------------------------------------------------------------------------

const noMaps: Machine = {name: 'loop', params: [], inputs: [], state: {}, step: {}}
type LoopRun = {turns: number, violation?: string}
// Runs to the end: the invariants at the start and after every turn, the rank (a tuple, compared in order) dropping on
// every turn, and a run that never ends within `cap` turns is reported.
export function runLoop(l: AnyLoop, laws: Law[], opts: {trials: number, bound: number, cap: number}): LoopRun {
  const loop = l.loop, ranks = l.rankTerms
  let turns = 0
  const ev = (e: E, env: Record<string, number>) => evalE(e, env, empty, noMaps), ec = (c: C, env: Record<string, number>) => evalC(c, env, empty, noMaps)
  for (let trial = 0; trial < opts.trials; trial++) {
    const params = l.randomParams(rand, opts.bound)
    if (loop.pre && !ec(loop.pre, params)) continue
    let state = Object.fromEntries(Object.entries(loop.state).map(([n, e]) => [n, ev(e, params)]))
    const at = () => ({...params, ...state})
    for (const law of laws) if (!ec(law.holds, at())) return {turns, violation: `${law.name} fails at the start: ${JSON.stringify(at())}`}
    let n = 0
    while (ec(loop.while, at())) {
      if (++n > opts.cap) return {turns, violation: `no end after ${opts.cap} turns from ${JSON.stringify(params)}`}
      let input: Record<string, number> | undefined
      for (let tries = 0; tries < 200 && !input; tries++) { const cand = l.randomInput(rand, opts.bound); if (!loop.assume || ec(loop.assume, {...at(), ...cand})) input = cand }
      if (!input) break
      const before = ranks.map(r => ev(r, at()))
      const env = {...at(), ...input}
      state = {...state, ...Object.fromEntries(Object.entries(loop.body).map(([name, e]) => [name, ev(e, env)]))}
      turns++
      const after = ranks.map(r => ev(r, at()))
      const i = before.findIndex((b, j) => b !== after[j])
      if (i < 0 || after[i]! > before[i]!) return {turns, violation: `the rank ${JSON.stringify(before)} → ${JSON.stringify(after)} didn't drop`}
      for (const law of laws) if (!ec(law.holds, at())) return {turns, violation: `${law.name} fails after a turn: ${JSON.stringify(at())}`}
    }
  }
  return {turns}
}

// --- the check ----------------------------------------------------------------------------------------------------------

export function checkCase(c: Case, scale = 1): Finding[] {
  seed = 1 + c.name.length * 7919
  const out: Finding[] = []
  const note = (item: string, check: Finding['check'], ok: boolean, detail: string) => out.push({case: c.name, item, check, ok, detail})
  const bound = c.bound ?? 4
  if (c.kind === 'rule') {
    const depth = c.depth ?? 12
    const v = c.steps?.length ? proveSteps(c.rule, c.laws, c.steps) : proveRule(c.rule, c.laws)
    note('laws', 'kernel', v.proven && v.checked, verdictText(v))
    const r = runRule(c.rule, c.laws, {trials: 300 * scale, depth, bound}, c.steps)
    note('laws', 'runs', !r.violation && !r.mismatch && r.steps > 0, r.mismatch ?? (r.violation ? `${r.violation.law} broken: params ${JSON.stringify(r.violation.params)}, requests ${JSON.stringify(r.violation.trace)}` : `${r.steps} steps, every law held, compiled = interpreted`))
    for (const b of c.broken) {
      const bv = b.steps?.length ? proveSteps(b.rule, b.laws, b.steps) : proveRule(b.rule, b.laws)
      note(b.name, 'kernel', !bv.proven, verdictText(bv))
      let found: Run | undefined
      for (const [trials, d, bd] of [[400, depth, bound], [1500, depth * 2, 2], [1500, depth * 2, bound * 2]] as const) {
        const rb = runRule(b.rule, b.laws, {trials: trials * scale, depth: d, bound: bd}, b.steps)
        if (rb.mismatch) { found = rb; break }
        if (rb.violation) { found = rb; break }
      }
      note(b.name, 'counterexample', !!found?.violation, found?.violation ? `${found.violation.law} broken by params ${JSON.stringify(found.violation.params)}, requests ${JSON.stringify(found.violation.trace)}` : found?.mismatch ?? 'NO RUN BREAKS IT: true but unprovable, or the runs too short')
    }
  } else if (c.kind === 'decisions') {
    for (const d of c.decisions) {
      const v = proveDecision(d)
      note(d.name, 'kernel', v.proven && v.checked, verdictText(v))
      const s = sampleDecision(d, {trials: 20_000 * scale, bound})
      note(d.name, 'runs', !s.counterexample && s.steps > 0, s.counterexample ? `fails at ${JSON.stringify(s.counterexample)}` : `${s.steps} draws met given, then held on all`)
    }
    for (const b of c.broken) {
      const v = proveDecision(b.decision)
      note(b.name, 'kernel', !v.proven, verdictText(v))
      let s = sampleDecision(b.decision, {trials: 50_000 * scale, bound})
      if (!s.counterexample) s = sampleDecision(b.decision, {trials: 50_000 * scale, bound: bound * 4})
      note(b.name, 'counterexample', !!s.counterexample, s.counterexample ? `fails at ${JSON.stringify(s.counterexample)}` : 'NO DRAW BREAKS IT')
    }
  } else {
    const v = proveLoop(c.loop, c.laws)
    note('halts, invariants', 'kernel', v.proven && v.checked, verdictText(v))
    const r = runLoop(c.loop, c.laws, {trials: 300 * scale, bound, cap: 100_000})
    note('halts, invariants', 'runs', !r.violation && r.turns > 0, r.violation ?? `${r.turns} turns, every rank dropped, invariants held`)
    for (const b of c.broken) {
      const bv = proveLoop(b.loop, b.laws)
      note(b.name, 'kernel', !bv.proven, verdictText(bv))
      let r2 = runLoop(b.loop, b.laws, {trials: 1000 * scale, bound, cap: 10_000})
      if (!r2.violation) r2 = runLoop(b.loop, b.laws, {trials: 1000 * scale, bound: bound * 4, cap: 10_000})
      note(b.name, 'counterexample', !!r2.violation, r2.violation ?? 'NO RUN BREAKS IT')
    }
  }
  return out
}
