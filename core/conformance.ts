// The conformance generator: random terms and conditions over every operation of E and C (the op lists must name every
// op, or this file doesn't type-check), concrete inputs and map cells, and the reference value from evalE and evalC.
// core/conformance.test.ts holds every consumer of terms to it; lean-kernel/conformance.ts writes its cases for Lean.
import {type C, type E, type Machine, type State, evalC, evalE} from './machine.ts'
import {type Loop, type Recur, recurGoal, trueC} from '../kernel/kernel.ts'
import {grow} from '../kernel/prove.ts'
import {findNeverEnds} from './nonterm.ts'

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
const v = (name: string): E => ({op: 'var', name}), k = (value: number): E => ({op: 'const', value})
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
// The cases: each loop's certificate where the search finds one (else one forged: the guard as the set, w := 0), and
// its tampered twins, each named by what was changed.
export function recurCases(n: number, ms = 300): RecurCase[] {
  const out: RecurCase[] = []
  for (let i = 0; i < n; i++) {
    const {loop, family} = randomLoop()
    const f = findNeverEnds(loop, {ms, seed: 1 + i})
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
