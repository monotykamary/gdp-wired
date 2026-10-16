// The conformance generator: random terms and conditions over every operation of E and C (the op lists must name every
// op, or this file doesn't type-check), concrete inputs and map cells, and the reference value from evalE and evalC.
// core/conformance.test.ts holds every consumer of terms to it; lean-kernel/conformance.ts writes its cases for Lean.
import {type C, type E, type Machine, type State, evalC, evalE} from './machine.ts'

export const E_OPS = ['var', 'const', 'add', 'sub', 'mul', 'prod', 'min', 'max', 'if', 'get'] as const satisfies readonly E['op'][]
export const C_OPS = ['<', '<=', '=', 'and', 'or', 'not', 'flag'] as const satisfies readonly C['op'][]
type Covers<T, L extends readonly unknown[]> = [Exclude<T, L[number]>] extends [never] ? true : false
export const coverage: [Covers<E['op'], typeof E_OPS>, Covers<C['op'], typeof C_OPS>] = [true, true]

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
  }
}
