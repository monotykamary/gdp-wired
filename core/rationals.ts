// Rules over the rationals: params, inputs and state whose values are exact rationals (fees in fractions, tokens that
// refill by a fraction, ledgers in decimals), laws over them proven by linear arithmetic over ℚ, a decidable theory
// whose refutations are Farkas certificates. Nothing is scaled or encoded: 0.1 is 1/10, a third is 1/3, and the
// kernel's rows are the terms' own linear forms over a positive denominator.
//
//   const split = ratRule('fee split')
//     .params({amount: nonneg})
//     .state({fee: 0, payout: 0})
//     .step(({amount}) => ({fee: amount.times('0.025'), payout: amount.times('0.975')}))
//   proveRatRule(split, [split.law('the parts sum to the whole', ({fee, payout, amount}) => fee.plus(payout).eq(amount))])
//
// Untrusted, like dsl.ts: everything here compiles to kernel.ts's QMachine and QLaw, which the kernel checks (and
// Lean again, Rationals.lean). The terms are linear: × and ÷ by a constant only; a product of two unknowns is refused
// (nonlinear arithmetic over the reals is decidable but not by these certificates, and with transcendental functions
// it isn't). A rule is all rationals: a natural is a rational with integrality, and integer constraints mixed with
// rational ones are mixed-integer arithmetic, which these certificates (no cut) don't refute; rules over the naturals
// and integers stay in dsl.ts, where the cut is the integrality rule.
import {type QC, type QE, type QGoal, type QLaw, type QMachine, type Tree, checkQMachine, qObligations, qSubstC, qSubstE, qTrue} from '../kernel/kernel.ts'
import {growQ} from '../kernel/qprove.ts'
import {type Rat, Q0, q, qadd, qcmp, qeq, qmax, qmin, qmul, qparse, qshow, qsub} from './q.ts'

export type {Rat}
export type RatLike = RatTerm | number | string | bigint | Rat
const termOf = (x: RatLike): QE => (x instanceof RatTerm ? x.e : {op: 'const', q: qparse(x)})
const constOf = (x: RatLike, what: string): Rat => {
  if (x instanceof RatTerm) {
    if (x.e.op === 'const') return x.e.q
    throw new TypeError(`${what}: a product of two unknowns is nonlinear, outside linear arithmetic over ℚ (times and over take a constant)`)
  }
  return qparse(x)
}

// A rational-valued term: + and − exact, × and ÷ by a constant.
export class RatTerm {
  constructor(readonly e: QE) {}
  plus(b: RatLike): RatTerm { return new RatTerm({op: 'add', a: this.e, b: termOf(b)}) }
  minus(b: RatLike): RatTerm { return new RatTerm({op: 'sub', a: this.e, b: termOf(b)}) }
  times(k: RatLike): RatTerm { return new RatTerm({op: 'mul', k: constOf(k, 'times'), a: this.e}) }
  over(k: RatLike): RatTerm {
    const c = constOf(k, 'over')
    if (c.num === 0n) throw new RangeError('over: division by 0')
    return new RatTerm({op: 'mul', k: q(c.den, c.num), a: this.e})
  }
  negate(): RatTerm { return this.times(-1) }
  lt(b: RatLike): RatCond { return new RatCond({op: '<', a: this.e, b: termOf(b)}) }
  atMost(b: RatLike): RatCond { return new RatCond({op: '<=', a: this.e, b: termOf(b)}) }
  gt(b: RatLike): RatCond { return new RatCond({op: '<', a: termOf(b), b: this.e}) }
  atLeast(b: RatLike): RatCond { return new RatCond({op: '<=', a: termOf(b), b: this.e}) }
  eq(b: RatLike): RatCond { return new RatCond({op: '=', a: this.e, b: termOf(b)}) }
  ne(b: RatLike): RatCond { return this.eq(b).not() }
  min(b: RatLike): RatTerm { return rmin(this, b) }
  max(b: RatLike): RatTerm { return rmax(this, b) }
}
export class RatCond {
  constructor(readonly c: QC) {}
  and(...xs: RatCond[]): RatCond { return rall(this, ...xs) }
  or(...xs: RatCond[]): RatCond { return rany(this, ...xs) }
  not(): RatCond { return new RatCond({op: 'not', x: this.c}) }
  implies(b: RatCond): RatCond { return rany(this.not(), b) }
  iff(b: RatCond): RatCond { return rall(this.implies(b), b.implies(this)) }
}
export const rlit = (x: RatLike): RatTerm => new RatTerm(termOf(x))
export const ryes = new RatCond(qTrue)
export const rno = ryes.not()
export const rall = (...cs: RatCond[]): RatCond => (cs.length === 0 ? ryes : cs.reduce((a, b) => new RatCond({op: 'and', a: a.c, b: b.c})))
export const rany = (...cs: RatCond[]): RatCond => (cs.length === 0 ? rno : cs.reduce((a, b) => new RatCond({op: 'or', a: a.c, b: b.c})))
export const rmin = (a: RatLike, b: RatLike): RatTerm => new RatTerm({op: 'min', a: termOf(a), b: termOf(b)})
export const rmax = (a: RatLike, b: RatLike): RatTerm => new RatTerm({op: 'max', a: termOf(a), b: termOf(b)})
export const rwhen = (c: RatCond, then: RatLike, otherwise: RatLike): RatTerm => new RatTerm({op: 'if', c: c.c, then: termOf(then), else: termOf(otherwise)})

// The kinds: any rational, or one at least 0 (a param's precondition, an input's assumption).
export type RatKind = {kind: 'rat', nonneg: boolean}
export const rat: RatKind = {kind: 'rat', nonneg: false}
export const nonneg: RatKind = {kind: 'rat', nonneg: true}

type Terms<K extends string> = {[k in K]: RatTerm}
type Init<P extends string> = RatLike | ((p: Terms<P>) => RatLike)
const v = (name: string) => new RatTerm({op: 'var', name})
const terms = <K extends string>(names: readonly K[]): Terms<K> => Object.fromEntries(names.map(n => [n, v(n)])) as Terms<K>
const kindConds = (decl: Record<string, RatKind>): RatCond[] => Object.entries(decl).filter(([, k]) => k.nonneg).map(([n]) => v(n).atLeast(0))

export type RatLaw<S extends string, P extends string> = QLaw & {readonly __rat?: [S, P]}
export class RatRule<P extends string = never, I extends string = never, S extends string = never> {
  constructor(readonly name: string, private readonly p: Record<string, RatKind> = {}, private readonly i: Record<string, RatKind> = {},
    private readonly s: Record<string, Init<P>> = {}, private readonly stepFn?: (x: Terms<P | I | S>) => Partial<Record<S, RatLike>>,
    private readonly preFn?: (x: Terms<P>) => RatCond, private readonly assumeFn?: (x: Terms<P | I | S>) => RatCond) {}
  params<Q extends string>(decl: Record<Q, RatKind>): RatRule<Q, I, S> { return new RatRule<Q, I, S>(this.name, decl, this.i, this.s as never, this.stepFn as never, this.preFn as never, this.assumeFn as never) }
  inputs<J extends string>(decl: Record<J, RatKind>): RatRule<P, J, S> { return new RatRule<P, J, S>(this.name, this.p, decl, this.s, this.stepFn as never, this.preFn, this.assumeFn as never) }
  state<T extends string>(init: Record<T, Init<P>>): RatRule<P, I, T> { return new RatRule<P, I, T>(this.name, this.p, this.i, init, this.stepFn as never, this.preFn, this.assumeFn as never) }
  step(fn: (x: Terms<P | I | S>) => Partial<Record<S, RatLike>>): RatRule<P, I, S> { return new RatRule(this.name, this.p, this.i, this.s, fn, this.preFn, this.assumeFn) }
  pre(fn: (x: Terms<P>) => RatCond): RatRule<P, I, S> { return new RatRule(this.name, this.p, this.i, this.s, this.stepFn, fn, this.assumeFn) }
  assume(fn: (x: Terms<P | I | S>) => RatCond): RatRule<P, I, S> { return new RatRule(this.name, this.p, this.i, this.s, this.stepFn, this.preFn, fn) }
  get paramNames(): P[] { return Object.keys(this.p) as P[] }
  get inputNames(): I[] { return Object.keys(this.i) as I[] }
  get stateNames(): S[] { return Object.keys(this.s) as S[] }
  get machine(): QMachine {
    const names = [...this.paramNames, ...this.inputNames, ...this.stateNames]
    if (new Set(names).size !== names.length) throw new Error(`${this.name}: a name is declared twice`)
    const all = terms(names) as Terms<P | I | S>, ps = terms(this.paramNames)
    const state = Object.fromEntries(Object.entries(this.s).map(([n, init]) => [n, termOf(typeof init === 'function' ? (init as (p: Terms<P>) => RatLike)(ps) : init as RatLike)]))
    const out = this.stepFn ? this.stepFn(all) : {}
    for (const n of Object.keys(out)) if (!(n in this.s)) throw new Error(`${this.name}: the step sets ${n}, which is not in the state`)
    const step = Object.fromEntries(Object.entries(out).map(([n, t]) => [n, termOf(t as RatLike)]))
    const pre = rall(...kindConds(this.p), ...(this.preFn ? [this.preFn(ps)] : []))
    const assume = rall(...kindConds(this.i), ...(this.assumeFn ? [this.assumeFn(all)] : []))
    return {name: this.name, params: this.paramNames, inputs: this.inputNames, state, step, pre: pre.c, assume: assume.c}
  }
  // A law over the state and the params.
  law(name: string, fn: (x: Terms<P | S>) => RatCond): RatLaw<S, P> { return {name, holds: fn(terms([...this.paramNames, ...this.stateNames]) as Terms<P | S>).c} }
  // The rule run exactly: the states after each request, from params (each value a number, decimal text or fraction).
  run(params: Record<P, RatLike>, requests: Record<I, RatLike>[]): Record<S, string>[] {
    const r = interpretQ(this.machine), ps = Object.fromEntries(Object.entries(params).map(([n, x]) => [n, qparse(x as Exclude<RatLike, RatTerm>)]))
    let st = r.init(ps)
    const out = [st]
    for (const req of requests) {
      const input = Object.fromEntries(Object.entries(req).map(([n, x]) => [n, qparse(x as Exclude<RatLike, RatTerm>)]))
      if (!r.allowed(ps, st, input)) throw new Error(`${this.name}: the request ${JSON.stringify(req)} is not allowed (the rule's assumption)`)
      st = r.step(ps, st, input)
      out.push(st)
    }
    return out.map(s => Object.fromEntries(Object.entries(s).map(([n, x]) => [n, qshow(x)])) as Record<S, string>)
  }
}
export const ratRule = (name: string): RatRule => new RatRule(name)

// --- runtimes: exact, as the proofs read the terms --------------------------------------------------------------------

export type QEnv = Record<string, Rat>
export function evalQE(e: QE, env: QEnv): Rat {
  switch (e.op) {
    case 'var': { const x = env[e.name]; if (!x) throw new Error(`no value for ${e.name}`); return x }
    case 'const': return q(e.q.num, e.q.den)
    case 'add': return qadd(evalQE(e.a, env), evalQE(e.b, env))
    case 'sub': return qsub(evalQE(e.a, env), evalQE(e.b, env))
    case 'mul': return qmul(q(e.k.num, e.k.den), evalQE(e.a, env))
    case 'min': return qmin(evalQE(e.a, env), evalQE(e.b, env))
    case 'max': return qmax(evalQE(e.a, env), evalQE(e.b, env))
    case 'if': return evalQC(e.c, env) ? evalQE(e.then, env) : evalQE(e.else, env)
  }
}
export function evalQC(c: QC, env: QEnv): boolean {
  switch (c.op) {
    case '<=': return qcmp(evalQE(c.a, env), evalQE(c.b, env)) <= 0
    case '<': return qcmp(evalQE(c.a, env), evalQE(c.b, env)) < 0
    case '=': return qeq(evalQE(c.a, env), evalQE(c.b, env))
    case 'and': return evalQC(c.a, env) && evalQC(c.b, env)
    case 'or': return evalQC(c.a, env) || evalQC(c.b, env)
    case 'not': return !evalQC(c.x, env)
  }
}
export type QRuntime = {init: (params: QEnv) => QEnv, allowed: (params: QEnv, state: QEnv, input: QEnv) => boolean, step: (params: QEnv, state: QEnv, input: QEnv) => QEnv}
export function interpretQ(m: QMachine): QRuntime {
  return {
    init: params => ({...Object.fromEntries(Object.entries(m.state).map(([n, e]) => [n, evalQE(e, params)]))}),
    allowed: (params, state, input) => evalQC(m.assume ?? qTrue, {...params, ...state, ...input}),
    step: (params, state, input) => {
      const env = {...params, ...state, ...input}
      return {...state, ...Object.fromEntries(Object.entries(m.step).map(([n, e]) => [n, evalQE(e, env)]))}
    },
  }
}
// The same machine as generated JavaScript over bigint fractions (each value [num, den], reduced).
export function compileQJs(m: QMachine): string {
  const lit = (r: Rat) => `[${r.num}n, ${r.den}n]`
  const e = (t: QE): string => {
    switch (t.op) {
      case 'var': return `v[${JSON.stringify(t.name)}]`
      case 'const': return lit(q(t.q.num, t.q.den))
      case 'add': return `A(${e(t.a)}, ${e(t.b)})`
      case 'sub': return `S(${e(t.a)}, ${e(t.b)})`
      case 'mul': return `M(${lit(q(t.k.num, t.k.den))}, ${e(t.a)})`
      case 'min': return `(x => (y => C(x, y) <= 0 ? x : y)(${e(t.b)}))(${e(t.a)})`
      case 'max': return `(x => (y => C(x, y) <= 0 ? y : x)(${e(t.b)}))(${e(t.a)})`
      case 'if': return `(${c(t.c)} ? ${e(t.then)} : ${e(t.else)})`
    }
  }
  const c = (t: QC): string => {
    switch (t.op) {
      case '<=': return `(C(${e(t.a)}, ${e(t.b)}) <= 0)`
      case '<': return `(C(${e(t.a)}, ${e(t.b)}) < 0)`
      case '=': return `(C(${e(t.a)}, ${e(t.b)}) === 0)`
      case 'and': return `(${c(t.a)} && ${c(t.b)})`
      case 'or': return `(${c(t.a)} || ${c(t.b)})`
      case 'not': return `!${c(t.x)}`
    }
  }
  const obj = (r: Record<string, QE>) => `{${Object.entries(r).map(([n, t]) => `${JSON.stringify(n)}: ${e(t)}`).join(', ')}}`
  return `const G = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a }
const N = (n, d) => { if (d < 0n) { n = -n; d = -d } const g = G(n, d) || 1n; return [n / g, d / g] }
const A = (a, b) => N(a[0] * b[1] + b[0] * a[1], a[1] * b[1]), S = (a, b) => N(a[0] * b[1] - b[0] * a[1], a[1] * b[1])
const M = (a, b) => N(a[0] * b[0], a[1] * b[1]), C = (a, b) => { const d = a[0] * b[1] - b[0] * a[1]; return d < 0n ? -1 : d > 0n ? 1 : 0 }
return {
  init: v => (${obj(m.state)}),
  allowed: v => ${c(m.assume ?? qTrue)},
  step: v => ({...v.$state, ...${obj(m.step)}}),
}`
}
export function loadQJs(m: QMachine): QRuntime {
  type Pair = [bigint, bigint]
  // oxlint-disable-next-line typescript/no-implied-eval
  const made = new Function(compileQJs(m))() as {init: (v: Record<string, Pair>) => Record<string, Pair>, allowed: (v: Record<string, Pair>) => boolean, step: (v: Record<string, Pair | Record<string, Pair>>) => Record<string, Pair>}
  const to = (r: QEnv) => Object.fromEntries(Object.entries(r).map(([n, x]) => [n, [x.num, x.den] as Pair]))
  const from = (r: Record<string, Pair>): QEnv => Object.fromEntries(Object.entries(r).map(([n, [a, b]]) => [n, {num: a, den: b}]))
  return {
    init: params => from(made.init(to(params))),
    allowed: (params, state, input) => made.allowed({...to(params), ...to(state), ...to(input)}),
    step: (params, state, input) => from(made.step({...to(params), ...to(state), ...to(input), $state: to(state)})),
  }
}

// --- proving and refuting ---------------------------------------------------------------------------------------------

export type QProof = {trees: Record<string, {start: Tree, step: Tree}>}
export type QVerdict = {proven: boolean, checked: boolean, goal?: string, stuck?: 'sat' | 'unknown', why?: string,
  // A counterexample: the values (exact, as text) of a state where the laws hold and one step breaks a law (not
  // inductive: maybe unreachable), or of a run from the start that breaks one (`run`: params and requests).
  witness?: Record<string, string>, run?: {params: Record<string, string>, requests: Record<string, string>[]}, proof?: QProof}
const shown = (r: Record<string, Rat>) => Object.fromEntries(Object.entries(r).map(([n, x]) => [n, qshow(x)]))
// The machine unrolled d steps from the start: request j's inputs named <input>@j.
function unrolled(m: QMachine, d: number): {hyps: QC[], at: Record<string, QE>} {
  const hyps: QC[] = [m.pre ?? qTrue]
  let at: Record<string, QE> = {...m.state}
  for (let j = 0; j < d; j++) {
    const ren: Record<string, QE> = {...at, ...Object.fromEntries(m.inputs.map(i => [i, {op: 'var', name: `${i}@${j}`} as QE]))}
    hyps.push(qSubstC(m.assume ?? qTrue, ren))
    at = {...at, ...Object.fromEntries(Object.entries(m.step).map(([n, e]) => [n, qSubstE(e, ren)]))}
  }
  return {hyps, at}
}
// A run from the start that breaks a law, within `depth` requests: each unrolled goal decided over ℚ (exactly, so a
// model is a run), the run replayed by the interpreter, which must break the law too.
export function refuteQ(m: QMachine, laws: QLaw[], depth = 3, until = performance.now() + 2_000): QVerdict | undefined {
  const run = interpretQ(m)
  for (let d = 0; d <= depth; d++) {
    const {hyps, at} = unrolled(m, d)
    for (const law of laws) {
      const goal: QGoal = {name: `${law.name} @${d} steps`, hyps: [...hyps, {op: 'not', x: qSubstC(law.holds, at)}]}
      const out = growQ(goal, {until})
      if ('tree' in out || out.stuck !== 'sat' || !out.rational) continue
      const val = (n: string) => out.rational![n] ?? Q0
      const params = Object.fromEntries(m.params.map(p => [p, val(p)]))
      const requests = Array.from({length: d}, (_, j) => Object.fromEntries(m.inputs.map(i => [i, val(`${i}@${j}`)])))
      let st = run.init(params), ok = evalQC(m.pre ?? qTrue, params)
      for (const req of requests) { ok &&= run.allowed(params, st, req); st = run.step(params, st, req) }
      if (ok && !evalQC(law.holds, {...params, ...st})) return {proven: false, checked: false, goal: goal.name, stuck: 'sat', witness: shown({...params, ...st}), run: {params: shown(params), requests: requests.map(shown)}}
    }
  }
  return undefined
}
// Each law by induction: its start and step goals grown by the search, the trees checked by the kernel.
export function proveQMachine(m: QMachine, laws: QLaw[], opts: {ms?: number} = {}): QVerdict {
  const until = performance.now() + (opts.ms ?? 20_000), trees: QProof['trees'] = {}
  for (const law of laws) {
    const goals = qObligations(m, laws, law), got: Partial<{start: Tree, step: Tree}> = {}
    for (const which of ['start', 'step'] as const) {
      const out = growQ(goals[which], {until})
      if (!('tree' in out)) {
        const w = out.rational ? shown(Object.fromEntries(Object.entries(out.rational).filter(([n]) => !n.includes('@')))) : undefined
        return {proven: false, checked: false, goal: goals[which].name, stuck: out.stuck, ...(out.why ? {why: out.why} : {}), ...(w ? {witness: w} : {})}
      }
      got[which] = out.tree
    }
    trees[law.name] = got as {start: Tree, step: Tree}
  }
  return {proven: true, checked: checkQMachine(m, laws, trees), proof: {trees}}
}
// A rule's laws: refuted by a run from the start if one breaks them within `depth` requests, else proven by induction
// (or not, with the step that breaks one from where they all hold).
export function proveRatRule(r: RatRule<string, string, string>, laws: QLaw[], opts: {depth?: number, ms?: number} = {}): QVerdict {
  const m = r.machine
  return refuteQ(m, laws, opts.depth ?? 3) ?? proveQMachine(m, laws, opts)
}
