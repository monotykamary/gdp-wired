// The conformance generator: random terms and conditions over every operation of E and C (the op lists must name every
// op, or this file doesn't type-check), concrete inputs and map cells, and the reference value from evalE and evalC.
// core/conformance.test.ts holds every consumer of terms to it; lean-kernel/conformance.ts writes its cases for Lean.
import {type C, type E, type Law, type Machine, type State, evalC, evalE, interpret, n as k, x as v} from './machine.ts'
import {type Goal, type KInduction, type Loop, type QC, type QE, type QGoal, type QMachine, type Recur, type Tree, checkKInduction, kInductionStart, kInductionSteps, recurGoal, stepLawObligations, trueC} from '../kernel/kernel.ts'
import {type KindProof, proveKInduction} from './kind.ts'
import type {Step} from './solver.ts'
import {type Rat, q} from './q.ts'
import {evalQC, evalQE} from './rationals.ts'
import {grow} from '../kernel/prove.ts'
import {findNeverEnds} from './nonterm.ts'
import {type Callable, type Measure, type Nat, define, natural, when} from './data.ts'

export const E_OPS = ['var', 'const', 'add', 'sub', 'mul', 'prod', 'min', 'max', 'if', 'get'] as const satisfies readonly E['op'][]
export const C_OPS = ['<', '<=', '=', 'and', 'or', 'not', 'flag'] as const satisfies readonly C['op'][]
type Covers<T, L extends readonly unknown[]> = [Exclude<T, L[number]>] extends [never] ? true : false
// A quantified flag ('all') is a whole flag the kernel closes, not a term: its own tests are kernel/sets.test.ts.
export const coverage: [Covers<E['op'], typeof E_OPS>, Covers<Exclude<C['op'], 'all'>, typeof C_OPS>] = [true, true]

let seed = Number(process.env.FUZZ_SEED ?? 777)
export const reseed = (s: number) => { seed = s }
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
const pick = <T>(xs: readonly T[]): T => xs[rand(xs.length)]!
export const VARS = ['a', 'b', 'c'] as const, CELLS = 4, INIT = 2

// A random term: every op equally likely where depth allows; map keys are clamped below CELLS, so every read lands on a
// fixed cell; the flag f is a condition of the step (absent inside f's own definition).
export const seen: Record<string, number> = {}
export function term(d: number, flag = true): E {
  const op = d <= 0 ? pick(['var', 'const'] as const) : pick(E_OPS)
  seen[op] = (seen[op] ?? 0) + 1
  switch (op) {
    case 'var': return {op, name: pick(VARS)}
    case 'const': return {op, value: rand(6)}
    case 'mul': return {op, k: rand(4), a: term(d - 1, flag)}
    case 'add': case 'sub': case 'min': case 'max': case 'prod': return {op, a: term(d - 1, flag), b: term(d - 1, flag)}
    case 'if': return {op, c: cond(d - 1, flag), then: term(d - 1, flag), else: term(d - 1, flag)}
    case 'get': return {op, map: 'M', key: {op: 'min', a: term(d - 1, flag), b: {op: 'const', value: CELLS - 1}}}
  }
}
export function cond(d: number, flag = true): C {
  const op = pick(flag ? C_OPS : C_OPS.filter(o => o !== 'flag'))
  seen[op] = (seen[op] ?? 0) + 1
  switch (op) {
    case '<': case '<=': case '=': return {op, a: term(d, flag), b: term(d, flag)}
    case 'and': case 'or': return {op, xs: Array.from({length: 1 + rand(3)}, () => cond(d - 1, flag))}
    case 'not': return {op, x: cond(d - 1, flag)}
    case 'flag': return {op, name: 'f'}
  }
}
// A case: the term and condition, the flag's definition, and concrete inputs and cells.
export type Case = {t: E, c: C, f: C, input: Record<string, number>, cells: number[]}
export const randomCase = (depth: number): Case => ({
  t: term(depth), c: cond(depth - 1), f: cond(1, false),
  input: Object.fromEntries(VARS.map(v => [v, rand(7)])), cells: Array.from({length: CELLS}, () => rand(7)),
})
export const machineOf = (k: Case): Machine => ({
  name: 'conformance', params: [], inputs: [...VARS], state: {out: {op: 'const', value: 0}, ok: {op: 'const', value: 0}}, maps: {M: INIT},
  step: {flags: {f: k.f}, state: {out: k.t, ok: {op: 'if', c: k.c, then: {op: 'const', value: 1}, else: {op: 'const', value: 0}}}},
})
export const stateOf = (k: Case): State => ({scalars: {out: 0, ok: 0}, maps: {M: new Map(k.cells.map((v, i) => [i, v]))}})
// The reference: evalE and evalC with the flag decided first, as both runtimes do.
export function reference(k: Case): {value: number, holds: boolean, flag: boolean} {
  const m = machineOf(k), st = stateOf(k)
  const flag = evalC(k.f, k.input, st, m)
  const env = {...k.input, '?f': flag ? 1 : 0}
  return {value: evalE(k.t, env, st, m), holds: evalC(k.c, env, st, m), flag}
}
// Flags inlined (the kernel takes no flags): f's reads become its condition.
export const inlineE = (t: E, f: C): E => {
  switch (t.op) {
    case 'var': case 'const': return t
    case 'mul': return {...t, a: inlineE(t.a, f)}
    case 'add': case 'sub': case 'min': case 'max': case 'prod': return {...t, a: inlineE(t.a, f), b: inlineE(t.b, f)}
    case 'if': return {op: 'if', c: inlineC(t.c, f), then: inlineE(t.then, f), else: inlineE(t.else, f)}
    case 'get': return {...t, key: inlineE(t.key, f)}
  }
}
export const inlineC = (c: C, f: C): C => {
  switch (c.op) {
    case '<': case '<=': case '=': return {...c, a: inlineE(c.a, f), b: inlineE(c.b, f)}
    case 'and': case 'or': return {op: c.op, xs: c.xs.map(x => inlineC(x, f))}
    case 'not': return {op: 'not', x: inlineC(c.x, f)}
    case 'flag': return f
    case 'all': throw new Error('conformance terms have no quantified flag')
  }
}

// --- nontermination certificates (kernel.ts's checkRecur, NonTerm.lean's never_ends_of) -------------------------------

// Random loops over a counter x and a second value y, a param p and an input w, from families that run forever from
// some start (x climbs past a guard; x wraps below a bound; w chosen equal to x) and families that always halt (x falls
// to a guard); each with the certificate core/nonterm.ts finds where it finds one, and its tampered twins:
//   - the set not closed: true (every state, where the guard can fail), or a lasso's set less one of its states, so the
//     cycle doesn't close;
//   - the set not reached: a start whose stem ends outside it, a stem turn the guard or the assumption refuses.
// The reference (`recurReference`) is evalE and evalC: the stem replayed, then the witnessed turn taken again and again.
export type RecurCase = {loop: Loop, recur: Recur, what: string, family: string}
export function randomLoop(): {loop: Loop, family: string} {
  const c = rand(4), j = rand(3), m = 1 + rand(4), family = pick(['climb', 'wrap', 'choose', 'fall'] as const)
  const base = {params: ['p'], inputs: ['w'], state: {x: v('p'), y: k(rand(3))}}
  switch (family) {
    case 'climb': return {family, loop: {...base, name: `climb ${c} ${j}`, while: {op: '<=', a: k(c), b: v('x')}, body: {x: {op: 'add', a: v('x'), b: k(j)}, y: {op: 'add', a: v('y'), b: v('w')}}, assume: {op: '<=', a: v('w'), b: k(1)}}}
    case 'wrap': return {family, loop: {...base, name: `wrap ${m}`, while: {op: '<=', a: v('y'), b: k(m + 2)}, body: {x: {op: 'if', c: {op: '<=', a: k(m), b: v('x')}, then: k(0), else: {op: 'add', a: v('x'), b: k(1)}}}}}
    case 'choose': return {family, loop: {...base, name: `choose ${c}`, while: {op: '<=', a: k(1), b: v('x')}, body: {x: v('w')}, assume: {op: '<=', a: v('w'), b: {op: 'add', a: v('x'), b: k(c)}}}}
    case 'fall': return {family, loop: {...base, name: `fall ${c}`, while: {op: '<=', a: k(c + 1), b: v('x')}, body: {x: {op: 'sub', a: v('x'), b: k(1 + j)}}, pre: {op: '<=', a: v('p'), b: k(40)}}}
  }
}
// The reference: the start and the stem by evalE and evalC, then `turns` witnessed turns, each allowed and in the set.
export function recurReference(l: Loop, r: Recur, turns = 60): boolean {
  if (!Object.keys(r.wit).every(n => l.inputs.includes(n))) return false
  const names = [...l.params, ...l.inputs, ...Object.keys(l.state)], none: State = {scalars: {}, maps: {}}
  const m: Machine = {name: l.name, params: l.params, inputs: l.inputs, state: {}, step: {}}
  let env: Record<string, number> = Object.fromEntries(names.map(n => [n, r.start[n] ?? 0]))
  if (l.pre && !evalC(l.pre, env, none, m)) return false
  env = {...env, ...Object.fromEntries(Object.entries(l.state).map(([n, e]) => [n, evalE(e, env, none, m)]))}
  const turn = (input: Record<string, number>): boolean => {
    const at = {...env, ...input}
    if (!evalC(l.while, at, none, m) || (l.assume && !evalC(l.assume, at, none, m))) return false
    env = {...at, ...Object.fromEntries(Object.entries(l.body).map(([n, e]) => [n, evalE(e, at, none, m)]))}
    return true
  }
  for (const t of r.stem) if (!turn(Object.fromEntries(l.inputs.map(n => [n, t[n] ?? 0])))) return false
  for (let i = 0; i <= turns; i++) {
    if (!evalC(r.set, env, none, m)) return false
    if (i < turns && !turn(Object.fromEntries(l.inputs.map(n => [n, r.wit[n] ? evalE(r.wit[n]!, env, none, m) : 0])))) return false
  }
  return true
}
// A regression, fixed (runs/ranks/suite3-usual's lean-nonterm, made again with FUZZ_SEED=8, cases 0 and 1): the
// certificate the search found for `climb 0 2`, whose tree cuts rows by 2, and its twin with the set made every state.
// The twin's tree is the found one's, which doesn't refute the twin's goal: kernel.ts refuses it, and Lean must too. The
// exporter once wrote that tree against the twin's goal, where a cut's row isn't even, so its quotient as -0.5: no Lean
// term, and the check failed to elaborate rather than compute false. Now a tree is written against a goal it refutes.
export function recurRegressions(): RecurCase[] {
  const loop = JSON.parse(LOOP) as Loop, found = JSON.parse(FOUND) as Recur
  return [
    {loop, family: 'climb', what: 'found', recur: found},
    {loop, family: 'climb', what: 'the set not closed: every state', recur: {...found, set: trueC}},
  ]
}
const LOOP = "{\"params\":[\"p\"],\"inputs\":[\"w\"],\"state\":{\"x\":{\"op\":\"var\",\"name\":\"p\"},\"y\":{\"op\":\"const\",\"value\":0}},\"name\":\"climb 0 2\",\"while\":{\"op\":\"<=\",\"a\":{\"op\":\"const\",\"value\":0},\"b\":{\"op\":\"var\",\"name\":\"x\"}},\"body\":{\"x\":{\"op\":\"add\",\"a\":{\"op\":\"var\",\"name\":\"x\"},\"b\":{\"op\":\"const\",\"value\":2}},\"y\":{\"op\":\"add\",\"a\":{\"op\":\"var\",\"name\":\"y\"},\"b\":{\"op\":\"var\",\"name\":\"w\"}}},\"assume\":{\"op\":\"<=\",\"a\":{\"op\":\"var\",\"name\":\"w\"},\"b\":{\"op\":\"const\",\"value\":1}}}"
const FOUND = "{\"start\":{\"p\":1},\"stem\":[],\"set\":{\"op\":\"and\",\"xs\":[{\"op\":\"=\",\"a\":{\"op\":\"const\",\"value\":1},\"b\":{\"op\":\"var\",\"name\":\"p\"}},{\"op\":\"=\",\"a\":{\"op\":\"const\",\"value\":0},\"b\":{\"op\":\"var\",\"name\":\"y\"}}]},\"wit\":{\"w\":{\"op\":\"var\",\"name\":\"y\"}},\"tree\":{\"split\":{\"x\":-1},\"yes\":{\"split\":{\"1\":-1,\"y\":1},\"yes\":{\"split\":{\"1\":1,\"p\":-1},\"yes\":{\"split\":{\"1\":-1,\"p\":1},\"yes\":{\"split\":{\"y\":-2},\"yes\":{\"leaf\":[{\"kind\":\"input\",\"index\":8},{\"kind\":\"input\",\"index\":9},{\"kind\":\"cut\",\"of\":1,\"g\":2},{\"kind\":\"combine\",\"a\":0,\"b\":2,\"ma\":1,\"mb\":1}]},\"no\":{\"leaf\":[{\"kind\":\"input\",\"index\":4},{\"kind\":\"cut\",\"of\":0,\"g\":2},{\"kind\":\"input\",\"index\":7},{\"kind\":\"combine\",\"a\":1,\"b\":2,\"ma\":1,\"mb\":1}]}},\"no\":{\"leaf\":[{\"kind\":\"input\",\"index\":3},{\"kind\":\"input\",\"index\":5},{\"kind\":\"combine\",\"a\":0,\"b\":1,\"ma\":1,\"mb\":1}]}},\"no\":{\"leaf\":[{\"kind\":\"input\",\"index\":2},{\"kind\":\"input\",\"index\":3},{\"kind\":\"combine\",\"a\":1,\"b\":0,\"ma\":1,\"mb\":1}]}},\"no\":{\"leaf\":[{\"kind\":\"input\",\"index\":1},{\"kind\":\"input\",\"index\":5},{\"kind\":\"combine\",\"a\":0,\"b\":1,\"ma\":1,\"mb\":1}]}},\"no\":{\"leaf\":[{\"kind\":\"input\",\"index\":0},{\"kind\":\"input\",\"index\":5},{\"kind\":\"combine\",\"a\":0,\"b\":1,\"ma\":1,\"mb\":1}]}}}"
// The cases (the search on the counted clock, so the same seed gives the same cases): each loop's certificate where the search finds one (else one forged: the guard as the set, w := 0), and
// its tampered twins, each named by what was changed.
export function recurCases(n: number, ms = 300): RecurCase[] {
  const out: RecurCase[] = [...recurRegressions()]
  for (let i = 0; i < n; i++) {
    const {loop, family} = randomLoop()
    const f = findNeverEnds(loop, {ms, seed: 1 + i, counted: 1000})
    if (!f.recur) {
      out.push({loop, family, what: 'forged: the guard as the set', recur: {start: {p: 30}, stem: [], set: loop.while, wit: {w: k(0)}, tree: {leaf: []}}})
      continue
    }
    const r = f.recur
    out.push({loop, family, what: 'found', recur: r})
    // (a tampered set is kept only where it isn't closed: the prover finds a state of it whose turn leaves it)
    const open = (set: C) => !('tree' in grow(recurGoal(loop, {set, wit: r.wit})))
    if (open(trueC)) out.push({loop, family, what: 'the set not closed: every state', recur: {...r, set: trueC}})
    for (let p = 0; p <= 40; p++) {
      const t = {...r, start: {...r.start, p}}
      if (!recurReference(loop, t, 0)) { out.push({loop, family, what: 'the set not reached: a start whose stem ends outside it', recur: t}); break }
    }
    const refused = {...r, stem: [{w: 1000}, ...r.stem], start: {...r.start, p: 0}}
    if (!recurReference(loop, refused, 0)) out.push({loop, family, what: 'the set not reached: a stem turn the guard or the assumption refuses', recur: refused})
    if (f.lasso && r.set.op === 'or' && r.set.xs.length > 1 && open({op: 'or', xs: r.set.xs.slice(0, -1)})) out.push({loop, family, what: "a lasso's cycle that doesn't close: its set less one state", recur: {...r, set: {op: 'or', xs: r.set.xs.slice(0, -1)}}})
  }
  return out
}

// --- rings of functions by well-founded recursion (core/data.ts's termination, Data.lean's wf_fix_unique_ring) -------
//
// Random rings of two functions over naturals, from families whose runs end and families that run forever from some
// start, each written twice: by core/data.ts's `define`, and as the reference, a JavaScript twin run with fuel that
// records every call within the ring (from the caller's arguments to the callee's).
//   - down: f(0) = c, f(p + 1) = g(p); g passes n round (g(n) = f(n)) or lowers it (g(0) = c, g(p + 1) = f(p)): ends
//   - up: f as down, g(n) = f(n + k), k ≥ 1: never ends from f(1)
//   - late: f(n) = g(n) from n ≥ L, else f(0) = c, f(p + 1) = f(p); g(n) = f(n): never ends from f(L)
//   - lateDown: late, but g lowers n (g(0) = c, g(p + 1) = f(p)): ends
//   - pair: f(0, m) = m, f(p + 1, m) = g(m, p); g(x, y) = f(x, y): ends (n + m falls at each call of f)
//   - swapKeep: f(0, m) = m, f(p + 1, m) = g(m, p + 1); g(x, y) = f(x, y): never ends from f(1, 1)
// A ring taken must end on the reference's runs, a ring that runs forever must be refused, and the measures of one taken,
// tampered (the functions' measures swapped; each function's constant dropped; every component's coefficients negated),
// must be refused by core/data.ts's checkMeasures wherever a call of the reference's runs doesn't lower them.
export type RingCase = {name: string, family: string, fns: [Callable, Callable], ends: boolean, arity: number, run: (at: number, args: number[], fuel: {n: number}, calls: RingCall[]) => number, lean: (fm: string, gm: string) => string}
export type RingCall = {from: number, to: number, s: number[], t: number[]}
let ringSeq = 0
export function ringCase(): RingCase {
  const family = pick(['down', 'up', 'late', 'lateDown', 'pair', 'swapKeep'] as const), c = rand(3), kUp = 1 + rand(2), L = 3 + rand(10), lowers = rand(2) === 1
  const id = `ring${++ringSeq}${family}`, fName = `${id}F`, gName = `${id}G`
  const N = (x: unknown) => x as Nat
  let f: Callable, g: Callable
  // the reference: each function a step reading the other through `call`, out of fuel past `fuel.n` calls
  type Js = (args: number[], call: (to: number, args: number[]) => number) => number
  let js: [Js, Js], lean: (fm: string, gm: string) => string
  const fDown: Js = ([n], call) => (n! === 0 ? c : call(1, [n! - 1]))
  const gDown: Js = ([n], call) => (lowers ? (n! === 0 ? c : call(0, [n! - 1])) : call(0, [n!]))
  const leanDown = `def ${fName} (n : Nat) : Nat := match n with | 0 => ${c} | p + 1 => ${gName} p`
  const leanG = lowers ? `def ${gName} (n : Nat) : Nat := match n with | 0 => ${c} | p + 1 => ${fName} p` : `def ${gName} (n : Nat) : Nat := ${fName} n`
  const two = (fd: string, fm: string, gd: string, gm: string) => `mutual\n${fd}\ntermination_by ${fm}\ndecreasing_by all_goals (simp_all [lexLt] <;> omega)\n${gd}\ntermination_by ${gm}\ndecreasing_by all_goals (simp_all [lexLt] <;> omega)\nend`
  switch (family) {
    case 'down':
      f = define(fName, {n: natural}, natural, ({n}) => N(n).match({zero: () => c, succ: ({pred}) => N(g(pred))}))
      g = lowers ? define(gName, {n: natural}, natural, ({n}) => N(n).match({zero: () => c, succ: ({pred}) => N(f(pred))})) : define(gName, {n: natural}, natural, ({n}) => N(f(n)))
      js = [fDown, gDown]; lean = (fm, gm) => two(leanDown, fm, leanG, gm)
      break
    case 'up':
      f = define(fName, {n: natural}, natural, ({n}) => N(n).match({zero: () => c, succ: ({pred}) => N(g(pred))}))
      g = define(gName, {n: natural}, natural, ({n}) => N(f(N(n).plus(kUp))))
      js = [fDown, ([n], call) => call(0, [n! + kUp])]; lean = () => ''
      break
    case 'late': case 'lateDown': {
      const down = family === 'lateDown'
      f = define(fName, {n: natural}, natural, ({n}) => when(N(n).atLeast(L), N(g(n)), N(n).match({zero: () => c, succ: ({pred}) => N(f(pred))})))
      g = down ? define(gName, {n: natural}, natural, ({n}) => N(n).match({zero: () => c, succ: ({pred}) => N(f(pred))})) : define(gName, {n: natural}, natural, ({n}) => N(f(n)))
      js = [([n], call) => (n! >= L ? call(1, [n!]) : n! === 0 ? c : call(0, [n! - 1])), down ? ([n], call) => (n! === 0 ? c : call(0, [n! - 1])) : ([n], call) => call(0, [n!])]
      lean = (fm, gm) => two(`def ${fName} (n : Nat) : Nat := if ${L} ≤ n then ${gName} n else match n with | 0 => ${c} | p + 1 => ${fName} p`, fm, `def ${gName} (n : Nat) : Nat := match n with | 0 => ${c} | p + 1 => ${fName} p`, gm)
      break
    }
    case 'pair': case 'swapKeep': {
      const keep = family === 'swapKeep'
      f = define(fName, {n: natural, m: natural}, natural, ({n, m}) => N(n).match({zero: () => N(m), succ: ({pred}) => N(keep ? g(m, n) : g(m, pred))}))
      g = define(gName, {x: natural, y: natural}, natural, ({x, y}) => N(f(x, y)))
      js = [([n, m], call) => (n! === 0 ? m! : call(1, keep ? [m!, n!] : [m!, n! - 1])), ([x, y], call) => call(0, [x!, y!])]
      lean = (fm, gm) => two(`def ${fName} (n m : Nat) : Nat := match n with | 0 => m | p + 1 => ${gName} m p`, fm, `def ${gName} (x y : Nat) : Nat := ${fName} x y`, gm)
      break
    }
  }
  const run = (at: number, args: number[], fuel: {n: number}, calls: RingCall[]): number => {
    const call = (from: number) => (to: number, as: number[]): number => {
      if (--fuel.n < 0) throw new RangeError('out of fuel')
      calls.push({from, to, s: [...argsOf(from)], t: as})
      return go(to, as)
    }
    const stack: number[][] = []
    const argsOf = (_from: number) => stack.at(-1)!
    const go = (i: number, as: number[]): number => { stack.push(as); try { return js[i]!(as, call(i)) } finally { stack.pop() } }
    return go(at, args)
  }
  return {name: id, family, fns: [f!, g!], ends: family === 'down' || family === 'lateDown' || family === 'pair', arity: family === 'pair' || family === 'swapKeep' ? 2 : 1, run, lean: lean!}
}
// The reference's runs from f and g at every start up to 16 (each argument), within `fuel` calls: whether all end, and
// the calls they make.
export function ringReference(r: RingCase, fuel = 4000): {ends: boolean, calls: RingCall[]} {
  const calls: RingCall[] = []
  let ends = true
  const starts = r.arity === 1 ? Array.from({length: 17}, (_, n) => [n]) : Array.from({length: 17 * 17}, (_, i) => [i % 17, Math.floor(i / 17)])
  for (const at of [0, 1]) for (const s of starts) { try { r.run(at, s, {n: fuel}, calls) } catch (e) { if (!(e instanceof RangeError)) throw e; ends = false } }
  return {ends, calls}
}
// Whether measures (each function's, as core/data.ts reads them: lexicographic, each component truncated at 0) fall at
// every call the reference recorded.
export function ringLowers(ms: Measure[], calls: RingCall[]): boolean {
  const val = (c: Measure['comps'][number], xs: number[]) => Math.max(0, c.coef.reduce((a, k, i) => a + k * xs[i]!, c.c))
  return calls.every(e => {
    for (const [j, c] of ms[e.to]!.comps.entries()) { const a = val(c, e.t), b = val(ms[e.from]!.comps[j]!, e.s); if (a < b) return true; if (a > b) return false }
    return false
  })
}
// The tampered measures of a ring taken, each named.
export function tamperedMeasures(ms: Measure[]): {what: string, ms: Measure[]}[] {
  const neg = (m: Measure): Measure => ({comps: m.comps.map(c => ({coef: c.coef.map(k => -k), c: -c.c}))})
  return [
    {what: 'swapped between the functions', ms: [ms[1]!, ms[0]!]},
    {what: "each function's constants dropped", ms: ms.map(m => ({comps: m.comps.map(c => ({...c, c: 0}))}))},
    {what: 'negated', ms: ms.map(neg)},
  ]
}

// --- rationals (kernel.ts's rational section, Rationals.lean) -------------------------------------------------------
// Random terms and conditions over every op of QE and QC (the lists must name every op), rational values with small
// numerators and denominators of either sign, and the reference: core/rationals.ts's evalQE and evalQC, exact.
export const QE_OPS = ['var', 'const', 'add', 'sub', 'mul', 'min', 'max', 'if'] as const satisfies readonly QE['op'][]
export const QC_OPS = ['<', '<=', '=', 'and', 'or', 'not'] as const satisfies readonly QC['op'][]
export const qcoverage: [Covers<QE['op'], typeof QE_OPS>, Covers<QC['op'], typeof QC_OPS>] = [true, true]
export const randRat = (): Rat => q(rand(13) - 6, 1 + rand(4))
export function qterm(d: number): QE {
  const op = d <= 0 ? pick(['var', 'const'] as const) : pick(QE_OPS)
  seen[`q${op}`] = (seen[`q${op}`] ?? 0) + 1
  switch (op) {
    case 'var': return {op, name: pick(VARS)}
    case 'const': return {op, q: randRat()}
    case 'mul': return {op, k: randRat(), a: qterm(d - 1)}
    case 'add': case 'sub': case 'min': case 'max': return {op, a: qterm(d - 1), b: qterm(d - 1)}
    case 'if': return {op, c: qcond(d - 1), then: qterm(d - 1), else: qterm(d - 1)}
  }
}
export function qcond(d: number): QC {
  const op = pick(QC_OPS)
  seen[`q${op}`] = (seen[`q${op}`] ?? 0) + 1
  switch (op) {
    case '<': case '<=': case '=': return {op, a: qterm(d), b: qterm(d)}
    case 'and': case 'or': return {op, a: qcond(d - 1), b: qcond(d - 1)}
    case 'not': return {op, x: qcond(d - 1)}
  }
}
export type QCase = {t: QE, c: QC, env: Record<string, Rat>}
export const randomQCase = (depth: number): QCase => ({t: qterm(depth), c: qcond(depth - 1), env: Object.fromEntries(VARS.map(x => [x, randRat()]))})
export const qreference = (k: QCase): {value: Rat, holds: boolean} => ({value: evalQE(k.t, k.env), holds: evalQC(k.c, k.env)})
export const qmachineOf = (k: QCase): QMachine => ({name: 'qconformance', params: [], inputs: [...VARS], state: {out: {op: 'const', q: q(0)}, ok: {op: 'const', q: q(0)}},
  step: {out: k.t, ok: {op: 'if', c: k.c, then: {op: 'const', q: q(1)}, else: {op: 'const', q: q(0)}}}})
// The goals a case gives the kernel: every variable fixed at its value, with the claim (the term's value, the
// condition's truth) negated, which no point satisfies; and the claim itself, which the case's values satisfy.
export function qgoals(k: QCase): {proven: QGoal[], models: QGoal[]} {
  const ref = qreference(k)
  const fixed: QC[] = VARS.map(x => ({op: '=', a: {op: 'var', name: x}, b: {op: 'const', q: k.env[x]!}}))
  const claims: [string, QC][] = [['value', {op: '=', a: k.t, b: {op: 'const', q: ref.value}}], ['truth', ref.holds ? k.c : {op: 'not', x: k.c}]]
  return {proven: claims.map(([w, c]) => ({name: w, hyps: [...fixed, {op: 'not', x: c}]})), models: claims.map(([w, c]) => ({name: `not ${w}`, hyps: [...fixed, c]}))}
}
// A tree's tampered twins, each refused by the kernel (and by Lean): a multiplier made 0 or negative, a cut (no cut
// over the rationals), an input out of range, a combination that names itself; every leaf at once.
export function qtampered(tree: Tree): {what: string, tree: Tree}[] {
  const each = (f: (steps: Step[]) => Step[] | undefined): Tree | undefined => {
    let changed = false
    const go = (t: Tree): Tree => {
      if ('leaf' in t) { const s = f(t.leaf); if (s) changed = true; return {leaf: s ?? t.leaf} }
      return {split: t.split, yes: go(t.yes), no: go(t.no)}
    }
    const out = go(tree)
    return changed ? out : undefined
  }
  const firstCombine = (steps: Step[]) => steps.findIndex(s => s.kind === 'combine')
  const out: {what: string, tree: Tree | undefined}[] = [
    {what: 'a multiplier negated', tree: each(steps => { const i = firstCombine(steps); return i < 0 ? undefined : steps.map((s, j) => (j === i && s.kind === 'combine' ? {...s, ma: -s.ma} : s)) })},
    {what: 'a multiplier 0', tree: each(steps => { const i = firstCombine(steps); return i < 0 ? undefined : steps.map((s, j) => (j === i && s.kind === 'combine' ? {...s, mb: 0} : s)) })},
    {what: 'a cut', tree: each(steps => [...steps, {kind: 'cut', of: steps.length - 1, g: 1}])},
    {what: 'an input out of range', tree: each(steps => steps.map(s => (s.kind === 'input' ? {...s, index: s.index + 1000} : s)))},
    {what: 'a combination of itself', tree: each(steps => { const i = firstCombine(steps); return i < 0 ? undefined : steps.map((s, j) => (j === i && s.kind === 'combine' ? {...s, a: j} : s)) })},
  ]
  return out.flatMap(x => (x.tree ? [{what: x.what, tree: x.tree}] : []))
}

// --- k-induction certificates (kernel.ts's checkKInduction, KInd.lean's checkKInd) --------------------------------------

// Random machines with a law that is k-inductive for one least k: a shift register (x1 := w, each next the one before,
// the law about the last: k = its length), a rotation (each register the next, the last the first: k = their number),
// each start and request at most c, some with a map written and a second law the first doesn't need; the certificate
// core/kind.ts finds, and its tampered twins, each with kernel.ts's answer: the same certificate for k + 1; a base depth
// left out; the step's tree for k given as k − 1's (the law k-inductive only at k); the step's tree for k given as
// k + 1's, beside a certificate for k + 1; the law read stricter. `lean`: the twin as KInd.lean's certificate (its k,
// the base depths it keeps, its law), for lean-kernel/conformance.ts --kind.
export type KindTamper = {what: string, kl: KInduction, proof: KindProof, lean?: {k: number, base: number[], law?: C}}
export type KindCase = {m: Machine, laws: Law[], law: Law, family: string, kl: KInduction, proof: KindProof, start: Goal, tampers: KindTamper[]}
export function randomKindMachine(): {m: Machine, laws: Law[], law: Law, family: string} {
  const family = pick(['shift', 'rotate'] as const), d = 1 + rand(4), c = 1 + rand(5), xs = Array.from({length: d}, (_, i) => `x${i + 1}`)
  const withMap = rand(2) === 1, second = rand(2) === 1
  const state: Record<string, E> = Object.fromEntries(xs.map(x => [x, k(rand(c + 1))])), step: Record<string, E> = {}
  if (family === 'shift') { step.x1 = v('w'); for (let i = 1; i < d; i++) step[xs[i]!] = v(xs[i - 1]!) }
  else for (let i = 0; i < d; i++) step[xs[i]!] = v(xs[(i + 1) % d]!)
  if (second) { state.y = k(0); step.y = {op: 'add', a: v('y'), b: v('w')} }
  const m: Machine = {name: `${family} ${d} ${c}`, params: [], inputs: ['w'], state, step: {state: step, ...(withMap ? {maps: {M: {key: v('w'), value: v(xs[0]!)}}} : {})},
    ...(withMap ? {maps: {M: 0}} : {}), assume: {op: '<=', a: v('w'), b: k(c)}}
  const law: Law = {name: 'bounded', holds: {op: '<=', a: v(family === 'shift' ? xs[d - 1]! : 'x1'), b: k(c)}}
  return {m, laws: second ? [{name: 'y counts', holds: {op: '<=', a: k(0), b: v('y')}}] : [], law, family}
}
// The reference: random runs from the start (each request allowed), the law read by evalC at every state.
export function kindReference(m: Machine, law: Law, runs = 30, steps = 12): boolean {
  const it = interpret(m)
  for (let r = 0; r < runs; r++) {
    let st = it.init({})
    for (let j = 0; j <= steps; j++) {
      if (!evalC(law.holds, {}, st, m)) return false
      try { st = it.step({}, st, {w: rand(8)}) } catch (e) { if (e instanceof RangeError) continue; throw e }
    }
  }
  return true
}
export function kindCases(n: number, ms = 3000): KindCase[] {
  const out: KindCase[] = []
  const stepOf = (m: Machine, laws: Law[], kl: KInduction) => stepLawObligations(m, laws, {}, kInductionSteps(m, kl).at(-1)!)[0]!.name
  for (let i = 0; i < n; i++) {
    const {m, laws, law, family} = randomKindMachine()
    const f = proveKInduction(m, laws, law, {ms, from: 1})
    if (!f.proven || !f.checked || !f.proof || !f.kl) throw new Error(`${m.name}: no k-induction found (${f.why})`)
    const kl = f.kl, kk = kl.k, proof = f.proof, ls = f.laws!, all = Array.from({length: kk - 1}, (_, j) => j)
    const tampers: KindTamper[] = [{what: `k said to be ${kk + 1}`, kl: {law, k: kk + 1}, proof, lean: {k: kk + 1, base: all}}]
    if (kk > 1) {
      const baseName = stepLawObligations(m, ls, {}, kInductionSteps(m, kl)[kk - 2]!)[0]!.name
      tampers.push({what: `the base of depth ${kk - 1} left out`, kl, proof: {...proof, trees: Object.fromEntries(Object.entries(proof.trees).filter(([name]) => name !== baseName))}, lean: {k: kk, base: all.slice(0, -1)}})
      const lower: KInduction = {law, k: kk - 1}
      tampers.push({what: `k-inductive only at k = ${kk}: the step's tree for ${kk} given for ${kk - 1}`, kl: lower, proof: {...proof, trees: {...proof.trees, [stepOf(m, ls, lower)]: proof.trees[stepOf(m, ls, kl)]!}}, lean: {k: kk - 1, base: all.slice(0, -1)}})
    }
    const up = proveKInduction(m, laws, law, {ms, from: kk + 1, to: kk + 1})
    if (up.proven && up.proof) {
      const higher: KInduction = {law, k: kk + 1}
      tampers.push({what: `the step's tree for k = ${kk} in a certificate for ${kk + 1}`, kl: higher, proof: {...up.proof, trees: {...up.proof.trees, [stepOf(m, ls, higher)]: proof.trees[stepOf(m, ls, kl)]!}}})
    }
    const le = law.holds as {a: E, b: {value: number}}, stricter: C = {op: '<=', a: le.a, b: k(Math.max(0, le.b.value - 1))}
    // (Lean's twin of this one: refused, the certificate with its law changed; accepted, a certificate of its own)
    const strict: KindTamper = {what: 'the law read stricter', kl: {law: {...law, holds: stricter}, k: kk}, proof}
    tampers.push(kindAnswer({m, laws: ls}, strict) ? strict : {...strict, lean: {k: kk, base: all, law: stricter}})
    out.push({m, laws: ls, law, family, kl, proof, start: kInductionStart(m, kl, {}), tampers})
  }
  return out
}
// kernel.ts's answer (a refusal by an error is a refusal).
export const kindAnswer = (c: {m: Machine, laws: Law[]}, t: {kl: KInduction, proof: KindProof}): boolean => { try { return checkKInduction(c.m, c.laws, t.kl, t.proof) } catch { return false } }
