// More kernel kinds, beside compile.ts's (whose interface stays as it is):
//   nonincreasing  ranks that never go up where the loop runs: max(0, form' - d) <= max(0, form - d)
//   rankPair       pairs (r1, r2) compared in order: a pair dies where (r1', r2') is not below (r1, r2)
//   mapRegion      for machines with maps: which box points satisfy every candidate alive at the key k and at each
//                  map's written key (a candidate about a map holds at every key)
//   mapKill        over those points, the candidates the step breaks at k
// A map machine's box point tracks two cells per map: M at the arbitrary key k, and M at the key the step writes;
// when the two keys are equal the cells must be equal (the guard). Reads in the step must be at the written key (or at
// k); the write lands on k exactly when the keys are equal. Each kernel is emitted as WGSL and as JavaScript.
import {type C, type E, type Machine, compileFunction, ite, noQuantifier, pointWrite, same, unreachable, x} from '../../core/machine.ts'
import {type Target, expressions} from '../search/compile.ts'
import {type Box, type Problem, BLOCK, CHUNK, HEADER, blocks, order, varsOf} from './compile.ts'

export type MoreKind = 'nonincreasing' | 'rankPair' | 'mapRegion' | 'mapKill'
// A map problem is a Problem whose state includes `${M}_k` per map and whose inputs include `${M}_w`, with `k` a param.
export type MapProblem = Problem & {maps: string[], swap: Record<string, string>}

// A machine with maps as a Problem over tracked cells.
export function fromMapMachine(m: Machine): MapProblem {
  const maps = Object.keys(m.maps ?? {})
  const writes = m.step.maps ?? {}
  const keyOf = (M: string) => (writes[M] ? pointWrite(writes[M]!, 'the synthesizer').key : undefined)
  const sub = (e: E): E => {
    switch (e.op) {
      case 'var': case 'const': return e
      case 'mul': return {...e, a: sub(e.a)}
      case 'if': return {op: 'if', c: subC(e.c), then: sub(e.then), else: sub(e.else)}
      case 'get': {
        if (JSON.stringify(e.key) === JSON.stringify(x('k'))) return x(`${e.map}_k`)
        if (keyOf(e.map) && JSON.stringify(e.key) === JSON.stringify(keyOf(e.map))) return x(`${e.map}_w`)
        throw new Error(`a read of ${e.map} at a key that is neither k nor the key the step writes`)
      }
      case 'add': case 'sub': case 'min': case 'max': case 'prod': return {...e, a: sub(e.a), b: sub(e.b)}
      default: return unreachable(e)
    }
  }
  const subC = (c: C): C => c.op === 'flag' ? c : c.op === 'all' ? noQuantifier('the synthesizer') : c.op === 'not' ? {op: 'not', x: subC(c.x)} : c.op === 'and' || c.op === 'or' ? {op: c.op, xs: c.xs.map(subC)} : {...c, a: sub(c.a), b: sub(c.b)}
  const scalars = Object.keys(m.state)
  const next: Record<string, E> = Object.fromEntries(scalars.map(n => [n, sub(m.step.state?.[n] ?? x(n))]))
  for (const M of maps) {
    const w = writes[M]
    const pw = w && pointWrite(w, 'the synthesizer')
    next[`${M}_k`] = pw ? ite(same(sub(pw.key), x('k')), sub(pw.value), x(`${M}_k`)) : x(`${M}_k`)
  }
  const consistent = maps.filter(M => writes[M]).map(M => ({op: 'or', xs: [{op: 'not', x: same(sub(pointWrite(writes[M]!, 'the synthesizer').key), x('k'))}, same(x(`${M}_w`), x(`${M}_k`))]}) as C)
  const guard: C | undefined = consistent.length ? {op: 'and', xs: consistent} : undefined
  return {
    kind: 'invariant', maps, init: m.state,
    params: [...m.params, 'k'], state: [...scalars, ...maps.map(M => `${M}_k`)], inputs: [...m.inputs, ...maps.filter(M => writes[M]).map(M => `${M}_w`)],
    next, flags: Object.fromEntries(Object.entries(m.step.flags ?? {}).map(([f, c]) => [f, subC(c)])), pre: m.pre, assume: m.assume, guard,
    swap: Object.fromEntries(maps.filter(M => writes[M]).map(M => [`${M}_k`, `${M}_w`])),
  }
}

// Coefficients per candidate: one form (V + 1 numbers), or two for a pair. Tables: [base, count, K, words,
// coefficients, alive bits, then a list of points (mapKill)].
export const widthOf = (p: Problem, kind: MoreKind) => (varsOf(p).length + 1) * (kind === 'rankPair' ? 2 : 1)
export function moreTables(p: Problem, kind: MoreKind, coefs: Int32Array, K: number, alive: Uint32Array, base = 0, count = 0, list?: Uint32Array): Uint32Array {
  const out = new Uint32Array(HEADER + coefs.length + alive.length + (list?.length ?? 0))
  out.set([base, count, K, alive.length])
  new Int32Array(out.buffer).set(coefs, HEADER)
  out.set(alive, HEADER + coefs.length)
  if (list) out.set(list, HEADER + coefs.length + alive.length)
  void p, kind
  return out
}

export function emitMore(p: Problem, box: Box, K: number, kind: MoreKind, target: Target): string {
  const w = target === 'wgsl'
  const prefix = (n: string) => (p.params.includes(n) ? `p_${n}` : p.inputs.includes(n) ? `i_${n}` : `s_${n}`)
  const {ex, cx, u} = expressions({name: '', params: p.params, inputs: p.inputs, state: {}, step: {}} as Machine, target, prefix)
  const vs = varsOf(p), V = vs.length, width = widthOf(p, kind)
  const T = (i: string) => (w ? `bitcast<i32>(tables[${i}])` : `T[${i}]`)
  const I = (s: string) => (w ? `i32(${s})` : s)
  const decl = (n: string, init: string, mutable = false) => (w ? `${mutable ? 'var' : 'let'} ${n} = ${init};` : `${mutable ? 'let' : 'const'} ${n} = ${init};`)
  const digit = (v: string) => [decl(prefix(v), `rest % ${u(box[v]! + 1)}`), w ? `rest = rest / ${u(box[v]! + 1)};` : `rest = Math.floor(rest / ${box[v]! + 1});`]
  const alive = (j: string) => (w ? `((tables[aliveAt + ${j} / 32u] >> (${j} % 32u)) & 1u) == 1u` : `((A[aliveAt + (${j} >>> 5)] >>> (${j} & 31)) & 1) === 1`)
  const at = (j: string, slot: number, i: number) => T(`${HEADER} + ${j} * ${width} + ${slot * (V + 1) + i}`)
  const form = (j: string, slot: number, val: (v: string) => string) => `(${vs.map((v, i) => `${at(j, slot, i)} * ${val(v)}`).join(' + ')})`
  const dAt = (j: string, slot: number) => at(j, slot, V)
  const rank = (j: string, slot: number, val: (v: string) => string) => (w ? `max(0, ${form(j, slot, val)} - ${dAt(j, slot)})` : `Math.max(0, ${form(j, slot, val)} - ${dAt(j, slot)})`)
  const now = (v: string) => I(prefix(v)), after = (v: string) => I(p.state.includes(v) ? `n_${v}` : prefix(v))
  const swap = (p as MapProblem).swap ?? {}
  const swapped = (v: string) => I(prefix(swap[v] ?? v))
  const fail = kind === 'mapRegion' ? 'false' : u(0)
  const lines: string[] = [decl('rest', 'index', true), decl('K', u(K)), decl('aliveAt', w ? `${HEADER}u + K * ${width}u` : `${HEADER} + K * ${width}`)]
  if (kind !== 'mapRegion') lines.push(decl('j0', w ? `block * ${BLOCK}u` : `block * ${BLOCK}`), decl('mask', u(0), true))
  for (const v of order(p)) lines.push(...digit(v))
  for (const c of [p.pre, p.assume, p.guard]) if (c) lines.push(`if (!${cx(c)}) { return ${fail}; }`)
  const overBlock = (bad: string) => w
    ? `for (var q = 0u; q < ${BLOCK}u; q++) { let j = j0 + q; if (j >= K) { break; } if (${alive('j')} && ${bad}) { mask = mask | (1u << q); } }`
    : `for (let q = 0; q < ${BLOCK}; q++) { const j = j0 + q; if (j >= K) break; if (${alive('j')} && ${bad}) mask |= 1 << q; }`
  if (kind === 'mapRegion') {
    // Every candidate alive holds at k and, for a candidate about a map, at the key the step writes.
    const bad = `${form('j', 0, now)} > ${dAt('j', 0)} || ${form('j', 0, swapped)} > ${dAt('j', 0)}`
    lines.push(w ? `for (var j = 0u; j < K; j++) { if (${alive('j')} && (${bad})) { return false; } }` : `for (let j = 0; j < K; j++) { if (${alive('j')} && (${bad})) return false; }`, 'return true;')
    return lines.map(l => `  ${l}`).join('\n')
  }
  lines.push(...Object.entries(p.flags).map(([f, c]) => decl(`f_${f}`, cx(c))), ...p.state.map(v => decl(`n_${v}`, ex(p.next[v]!))))
  if (kind === 'mapKill') lines.push(overBlock(`${form('j', 0, after)} > ${dAt('j', 0)}`))
  else if (kind === 'nonincreasing') lines.push(overBlock(`${rank('j', 0, after)} > ${rank('j', 0, now)}`))
  else lines.push(overBlock(`!(${rank('j', 0, after)} < ${rank('j', 0, now)} || (${rank('j', 0, after)} == ${rank('j', 0, now)} && ${rank('j', 1, after)} < ${rank('j', 1, now)}))`))
  lines.push('return mask;')
  return lines.map(l => `  ${l}`).join('\n')
}

const bindings = `
struct Params { count: u32, a: u32, b: u32, c: u32 }
@group(0) @binding(0) var<uniform> params: Params;
@group(0) @binding(1) var<storage, read> tables: array<u32>;
@group(0) @binding(2) var<storage, read> unused: array<u32>;
@group(0) @binding(3) var<storage, read_write> counts: array<f32>;`

export function wgslMore(p: Problem, box: Box, K: number, kind: MoreKind): string {
  if (kind === 'mapRegion') return `${bindings}
fn region(index: u32) -> bool {
${emitMore(p, box, K, kind, 'wgsl')}
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
  const listed = kind === 'mapKill'
  return `${bindings}
fn kill(index: u32, block: u32) -> u32 {
${emitMore(p, box, K, kind, 'wgsl')}
}
@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) id: vec3<u32>) {
  let i: u32 = id.x;
  if (i >= params.count) { return; }
  _ = unused[0];
  let listAt = ${HEADER}u + ${K}u * ${widthOf(p, kind)}u + tables[3];
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

export function jsMore(p: Problem, box: Box, K: number, kind: MoreKind) {
  return kind === 'mapRegion'
    ? {region: compileFunction<(index: number, T: Int32Array, A: Uint32Array) => boolean>(['index', 'T', 'A'], emitMore(p, box, K, kind, 'js'))}
    : {kill: compileFunction<(index: number, block: number, T: Int32Array, A: Uint32Array) => number>(['index', 'block', 'T', 'A'], emitMore(p, box, K, kind, 'js'))}
}
