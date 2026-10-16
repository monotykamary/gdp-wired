// Invariant and rank synthesis as GPU kernels (Houdini). A candidate is a linear form over the state and params,
// Σ c·v <= d. A round looks at every point of a box (params, a state, a request): a point whose state satisfies every
// candidate still alive (the region Houdini assumes), and whose step breaks one, kills that candidate. Rounds repeat
// until nothing dies; what is left is inductive inside the box, and the kernel then proves it for real (the box is
// only a filter). Ranks: a candidate max(0, Σ c·v - d) dies at a point where the loop runs (and its invariants hold)
// but the rank doesn't drop. Histories: every request sequence from the start; a candidate a reachable state breaks
// is false, so it dies.
//
// Kernels (each emitted as WGSL for Handwired's runner, Chrome or Dawn, and as JavaScript for the CPU twin):
//   region   a thread takes 24 consecutive points and reports, as a bit mask, those in the region (invariants only)
//   kill     a thread takes CHUNK points (for invariants, from the list of region points) and one block of 24
//            candidates, and reports which of them die as a bit mask (an f32 holds 24 bits exactly)
import {type C, type E, type Law, type Machine, compileFunction} from '../core/machine.ts'
import type {Loop} from '../kernel/kernel.ts'
import {type Target, expressions} from '../search/compile.ts'

export type Form = {coef: Record<string, number>, d: number} // Σ coef[v]·v <= d (a rank: max(0, Σ coef[v]·v - d))
export type Box = Record<string, number> // every param, state variable and input: its largest value (from 0)
export type Problem = {
  kind: 'invariant' | 'rank' | 'history'
  params: string[], state: string[], inputs: string[]
  init?: Record<string, E>, depth?: number // histories: the start, and how many requests
  next: Record<string, E>, flags: Record<string, C>
  pre?: C, assume?: C, guard?: C // guard: a loop's condition and the invariants it already has (ranks)
}
export const fromMachine = (m: Machine): Problem => ({kind: 'invariant', init: m.state, params: m.params, state: Object.keys(m.state), inputs: m.inputs,
  next: {...Object.fromEntries(Object.keys(m.state).map(n => [n, {op: 'var', name: n} as E])), ...m.step.state}, flags: m.step.flags ?? {}, pre: m.pre, assume: m.assume})
export const fromLoop = (l: Loop, laws: Law[] = []): Problem => ({kind: 'rank', params: l.params, state: Object.keys(l.state), inputs: l.inputs,
  next: {...Object.fromEntries(Object.keys(l.state).map(n => [n, {op: 'var', name: n} as E])), ...l.body}, flags: {},
  pre: l.pre, assume: l.assume, guard: {op: 'and', xs: [l.while, ...laws.map(law => law.holds)]}})

export const varsOf = (p: Problem) => [...p.state, ...p.params] // the forms' variables, in this order
export const order = (p: Problem) => [...p.params, ...p.state, ...p.inputs] // a box point's digits, lowest first
const historyDigits = (p: Problem) => [...p.params, ...Array.from({length: p.depth!}, () => p.inputs).flat()]
export const points = (p: Problem, box: Box) => (p.kind === 'history' ? historyDigits(p) : order(p)).reduce((acc, v) => acc * (box[v]! + 1), 1)

export const HEADER = 4, CHUNK = 64, BLOCK = 24
export const blocks = (K: number) => Math.ceil(K / BLOCK)
// [base, count, K, words, coefficients (K × (|vars| + 1), as i32), alive bits, then a list of points (kill, invariants)]
export function tables(p: Problem, forms: Form[], alive: Uint32Array, base = 0, count = 0, list?: Uint32Array): Uint32Array {
  const vs = varsOf(p), width = vs.length + 1
  const out = new Uint32Array(HEADER + forms.length * width + alive.length + (list?.length ?? 0))
  const i32 = new Int32Array(out.buffer)
  out.set([base, count, forms.length, alive.length])
  forms.forEach((f, j) => { vs.forEach((v, i) => (i32[HEADER + j * width + i] = f.coef[v] ?? 0)); i32[HEADER + j * width + vs.length] = f.d })
  out.set(alive, HEADER + forms.length * width)
  if (list) out.set(list, HEADER + forms.length * width + alive.length)
  return out
}

type Kernel = 'region' | 'kill'
// The body of `region(index) -> bool` or `kill(index, block) -> u32`.
export function emit(p: Problem, box: Box, K: number, kernel: Kernel, target: Target): string {
  const w = target === 'wgsl'
  const prefix = (n: string) => (p.params.includes(n) ? `p_${n}` : p.inputs.includes(n) ? `i_${n}` : `s_${n}`)
  const {ex, cx, u} = expressions({name: '', params: p.params, inputs: p.inputs, state: {}, step: {}} as Machine, target, prefix)
  const vs = varsOf(p), width = vs.length + 1
  const T = (i: string) => (w ? `bitcast<i32>(tables[${i}])` : `T[${i}]`)
  const I = (s: string) => (w ? `i32(${s})` : s)
  const decl = (n: string, init: string, mutable = false) => (w ? `${mutable ? 'var' : 'let'} ${n} = ${init};` : `${mutable ? 'let' : 'const'} ${n} = ${init};`)
  const digit = (v: string) => [decl(prefix(v), `rest % ${u(box[v]! + 1)}`), w ? `rest = rest / ${u(box[v]! + 1)};` : `rest = Math.floor(rest / ${box[v]! + 1});`]
  const alive = (j: string) => (w ? `((tables[aliveAt + ${j} / 32u] >> (${j} % 32u)) & 1u) == 1u` : `((A[aliveAt + (${j} >>> 5)] >>> (${j} & 31)) & 1) === 1`)
  const form = (j: string, val: (v: string) => string) => `(${vs.map((v, i) => `${T(`${HEADER} + ${j} * ${width} + ${i}`)} * ${val(v)}`).join(' + ')})`
  const dAt = (j: string) => T(`${HEADER} + ${j} * ${width} + ${vs.length}`)
  const now = (v: string) => I(prefix(v)), after = (v: string) => I(p.state.includes(v) ? `n_${v}` : prefix(v))
  const next = () => [...Object.entries(p.flags).map(([f, c]) => decl(`f_${f}`, cx(c))), ...p.state.map(v => decl(`n_${v}`, ex(p.next[v]!)))]
  const lines: string[] = [decl('rest', 'index', true), decl('K', u(K)), decl('aliveAt', w ? `${HEADER}u + K * ${width}u` : `${HEADER} + K * ${width}`)]
  const fail = kernel === 'region' ? 'false' : u(0)
  if (kernel === 'kill') lines.push(decl('j0', w ? `block * ${BLOCK}u` : `block * ${BLOCK}`), decl('mask', u(0), true))
  // Over this thread's block: each alive candidate for which `bad` holds gets its bit.
  const overBlock = (bad: string) => w
    ? `for (var q = 0u; q < ${BLOCK}u; q++) { let j = j0 + q; if (j >= K) { break; } if (${alive('j')} && ${bad}) { mask = mask | (1u << q); } }`
    : `for (let q = 0; q < ${BLOCK}; q++) { const j = j0 + q; if (j >= K) break; if (${alive('j')} && ${bad}) mask |= 1 << q; }`
  if (p.kind === 'history') {
    // The params, then each step's request; a request the assumption rules out ends the history.
    for (const v of p.params) lines.push(...digit(v))
    if (p.pre) lines.push(`if (!${cx(p.pre)}) { return ${fail}; }`)
    for (const v of p.state) lines.push(decl(prefix(v), ex(p.init![v]!), true))
    const check = overBlock(`${form('j', now)} > ${dAt('j')}`)
    lines.push(check, w ? `for (var t = 0u; t < ${p.depth}u; t++) {` : `for (let t = 0; t < ${p.depth}; t++) {`)
    for (const v of p.inputs) lines.push(...digit(v))
    if (p.assume) lines.push(`if (!${cx(p.assume)}) { return mask; }`)
    lines.push(...next(), ...p.state.map(v => `${prefix(v)} = n_${v};`), check, '}', 'return mask;')
  } else {
    for (const v of order(p)) lines.push(...digit(v))
    for (const c of [p.pre, p.assume, p.guard]) if (c) lines.push(`if (!${cx(c)}) { return ${fail}; }`)
    if (kernel === 'region') {
      lines.push(w ? `for (var j = 0u; j < K; j++) { if (${alive('j')} && ${form('j', now)} > ${dAt('j')}) { return false; } }` : `for (let j = 0; j < K; j++) { if (${alive('j')} && ${form('j', now)} > ${dAt('j')}) return false; }`, 'return true;')
    } else if (p.kind === 'invariant') {
      lines.push(...next(), overBlock(`${form('j', after)} > ${dAt('j')}`), 'return mask;')
    } else {
      const r = (val: (v: string) => string) => (w ? `max(0, ${form('j', val)} - ${dAt('j')})` : `Math.max(0, ${form('j', val)} - ${dAt('j')})`)
      lines.push(...next(), overBlock(`!(${r(after)} < ${r(now)})`), 'return mask;')
    }
  }
  return lines.map(l => `  ${l}`).join('\n')
}

const bindings = `
struct Params { count: u32, a: u32, b: u32, c: u32 }
@group(0) @binding(0) var<uniform> params: Params;
@group(0) @binding(1) var<storage, read> tables: array<u32>;
@group(0) @binding(2) var<storage, read> unused: array<u32>;
@group(0) @binding(3) var<storage, read_write> counts: array<f32>;`

export function wgsl(p: Problem, box: Box, K: number, kernel: Kernel): string {
  if (kernel === 'region') return `${bindings}
fn region(index: u32) -> bool {
${emit(p, box, K, 'region', 'wgsl')}
}
@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) id: vec3<u32>) {
  let i: u32 = id.x;
  if (i >= params.count) { return; }
  _ = unused[0];
  let first = tables[0] + i * ${BLOCK}u;
  var mask = 0u;
  for (var q = 0u; q < ${BLOCK}u; q++) { if (first + q >= tables[1]) { break; } if (region(first + q)) { mask = mask | (1u << q); } }
  counts[i] = f32(mask);
}`
  // kill: thread i takes chunk i / blocks and block i % blocks; invariants read their points from the list.
  const listed = p.kind === 'invariant'
  return `${bindings}
fn kill(index: u32, block: u32) -> u32 {
${emit(p, box, K, 'kill', 'wgsl')}
}
@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) id: vec3<u32>) {
  let i: u32 = id.x;
  if (i >= params.count) { return; }
  _ = unused[0];
  let listAt = ${HEADER}u + ${K}u * ${varsOf(p).length + 1}u + tables[3];
  let block = i % ${blocks(K)}u;
  let first = tables[0] + (i / ${blocks(K)}u) * ${CHUNK}u;
  var mask = 0u;
  for (var off = 0u; off < ${CHUNK}u; off++) {
    if (first + off >= tables[1]) { break; }
    mask = mask | kill(${listed ? 'tables[listAt + first + off - tables[0]]' : 'first + off'}, block);
  }
  counts[i] = f32(mask);
}`
}

// The CPU twins: the same bodies over the same tables (T: the i32 view, A: the u32 view).
export function js(p: Problem, box: Box, K: number) {
  return {
    region: compileFunction<(index: number, T: Int32Array, A: Uint32Array) => boolean>(['index', 'T', 'A'], emit(p, box, K, 'region', 'js')),
    kill: compileFunction<(index: number, block: number, T: Int32Array, A: Uint32Array) => number>(['index', 'block', 'T', 'A'], emit(p, box, K, 'kill', 'js')),
  }
}
