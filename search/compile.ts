// Counterexample search as a GPU kernel: every params × request sequence up to a depth, values within 0..bound, one
// candidate per index. The machine and its law compile to straight-line u32 code (what the forked Handwired's word
// operations would emit), once as WGSL and once as JavaScript for the CPU baseline. Nothing here is trusted: whatever
// the kernel reports is replayed by the interpreter before it is shown.
import {type C, type E, type Law, type Machine, compileFunction, evalC, interpret} from '../core/machine.ts'
import {type Watched, allowed, isStepLaw, watch} from '../core/watch.ts'

export type Space = {depth: number, bound: number}
export const NONE = 0xffffffff

export function size(m: Machine, s: Space) {
  const base = s.bound + 1
  return base ** m.params.length * base ** (m.inputs.length * s.depth)
}

// Index → params and the request at each step (params are the lowest digits, then step 1's inputs, and so on).
export function decode(m: Machine, s: Space, index: number) {
  const base = s.bound + 1
  let rest = index
  const digit = () => { const d = rest % base; rest = Math.floor(rest / base); return d }
  const params = Object.fromEntries(m.params.map(p => [p, digit()]))
  const trace = Array.from({length: s.depth}, () => Object.fromEntries(m.inputs.map(name => [name, digit()])))
  return {params, trace}
}

// Replays a candidate with the interpreter, the law (or step law) read along the run by core/watch.ts: the depth at
// which it fails (0 = at the start), or undefined.
export function replay(m: Machine, law: Watched, s: Space, index: number): {params: Record<string, number>, trace: Record<string, number>[]} | undefined {
  const {params, trace} = decode(m, s, index)
  const run = interpret(m)
  if (m.pre && !evalC(m.pre, params, {scalars: {}, maps: {}}, m)) return undefined
  let st = run.init(params)
  const on = watch(m, run, law, params, s.bound)
  if (!on.start(st)) return {params, trace: []}
  for (const [t, input] of trace.entries()) {
    if (!allowed(m, run, params, st, input)) return undefined
    const before = st
    st = run.step(params, st, input)
    if (!on.step(before, input, st)) return {params, trace: trace.slice(0, t + 1)}
  }
  return undefined
}
export function fitsU32(m: Machine, law: Watched, s: Space): void {
  const limit = 2 ** 32 - 1
  const vars: Record<string, number> = {}, cells: Record<string, number> = {...m.maps}
  for (const name of [...m.params, ...m.inputs]) vars[name] = s.bound
  if (law.forall) vars[law.forall] = s.bound + 1
  // A step law's later requests are inputs too.
  if (isStepLaw(law)) for (let j = 2; j <= (law.steps ?? 1); j++) for (const name of m.inputs) vars[`${name}@${j}`] = s.bound
  const up = (e: E): number => {
    let v: number
    switch (e.op) {
      case 'var': v = vars[e.name]!; break
      case 'const': v = e.value; break
      case 'add': v = up(e.a) + up(e.b); break
      case 'sub': v = up(e.a); up(e.b); break
      case 'mul': v = e.k * up(e.a); break
      case 'prod': v = up(e.a) * up(e.b); break
      case 'min': v = Math.min(up(e.a), up(e.b)); break
      case 'max': v = Math.max(up(e.a), up(e.b)); break
      case 'if': upC(e.c); v = Math.max(up(e.then), up(e.else)); break
      case 'get': up(e.key); v = cells[e.map]!; break
    }
    if (!(v <= limit)) throw new Error(`${m.name}: at depth ${s.depth} and bound ${s.bound}, a value could pass 2^32 - 1, where the GPU search's u32 code would wrap`)
    return v
  }
  const upC = (c: C): void => { if (c.op === 'not') upC(c.x); else if (c.op === 'and' || c.op === 'or') c.xs.forEach(upC); else if (c.op !== 'flag') (up(c.a), up(c.b)) }
  for (const [name, e] of Object.entries(m.state)) vars[name] = up(e)
  if (m.pre) upC(m.pre)
  // A law is read at every state; a step law's `then` once the state's bounds are in, its primed names at those bounds.
  const read = () => {
    if (!isStepLaw(law)) return upC(law.holds)
    for (const name of Object.keys(m.state)) vars[`${name}'`] = vars[name]!
    for (const map of Object.keys(m.maps ?? {})) cells[`${map}'`] = cells[map]!
    upC(law.then)
    for (const c of law.when === undefined ? [] : Array.isArray(law.when) ? law.when : [law.when]) upC(c)
  }
  read()
  for (let t = 0; t < s.depth; t++) {
    if (m.assume) upC(m.assume)
    for (const c of Object.values(m.step.flags ?? {})) upC(c)
    const next = Object.entries(m.step.state ?? {}).map(([name, e]) => [name, up(e)] as const)
    const written = Object.entries(m.step.maps ?? {}).map(([map, w]) => (up(w.key), [map, up(w.value)] as const))
    for (const [name, v] of next) vars[name] = Math.max(vars[name]!, v)
    for (const [map, v] of written) cells[map] = Math.max(cells[map]!, v)
    read()
  }
}

export type Target = 'wgsl' | 'js'
// Terms and conditions as u32 code (∸ truncates; a read past the stored cells is the map's initial value).
export function expressions(m: Machine, target: Target, name: (n: string) => string, K = 0) {
  const u = (n: number) => (target === 'wgsl' ? `${n}u` : String(n))
  const sel = (c: string, a: string, b: string) => (target === 'wgsl' ? `select(${b}, ${a}, ${c})` : `(${c} ? ${a} : ${b})`)
  const ex = (e: E): string => {
    switch (e.op) {
      case 'var': return name(e.name)
      case 'const': return u(e.value)
      case 'add': return `(${ex(e.a)} + ${ex(e.b)})`
      case 'sub': { const a = ex(e.a), b = ex(e.b); return sel(`${a} >= ${b}`, `(${a} - ${b})`, u(0)) }
      case 'mul': return `(${u(e.k)} * ${ex(e.a)})`
      case 'prod': return `(${ex(e.a)} * ${ex(e.b)})`
      case 'min': return target === 'wgsl' ? `min(${ex(e.a)}, ${ex(e.b)})` : `Math.min(${ex(e.a)}, ${ex(e.b)})`
      case 'max': return target === 'wgsl' ? `max(${ex(e.a)}, ${ex(e.b)})` : `Math.max(${ex(e.a)}, ${ex(e.b)})`
      case 'if': return sel(cx(e.c), ex(e.then), ex(e.else))
      case 'get': { const key = ex(e.key); return sel(`${key} < ${u(K)}`, `m_${e.map}[${target === 'wgsl' ? `min(${key}, ${u(K - 1)})` : key}]`, u(m.maps![e.map]!)) }
    }
  }
  const cx = (c: C): string => {
    switch (c.op) {
      case '<': return `(${ex(c.a)} < ${ex(c.b)})`
      case '<=': return `(${ex(c.a)} <= ${ex(c.b)})`
      case '=': return `(${ex(c.a)} == ${ex(c.b)})`
      case 'and': return `(${c.xs.map(cx).join(' && ')})`
      case 'or': return `(${c.xs.map(cx).join(' || ')})`
      case 'not': return `(!${cx(c.x)})`
      case 'flag': return `f_${c.name}`
    }
  }
  return {ex, cx, sel, u}
}

// The body of `candidate(index)`: the first depth at which the law fails, or NONE.
export function emit(m: Machine, law: Law, s: Space, target: Target): string {
  const K = s.bound + 1 // cells 0..bound are stored; every key above holds the map's initial value
  fitsU32(m, law, s)
  const isVar = (e: E) => e.op === 'var' && (m.params.includes(e.name) || m.inputs.includes(e.name))
  for (const w of Object.values(m.step.maps ?? {})) if (!isVar(w.key)) throw new Error('the GPU search writes maps only at a param or input key')
  const name = (n: string) => (m.params.includes(n) ? `p_${n}` : m.inputs.includes(n) ? `i_${n}` : n === law.forall ? 'kk' : `s_${n}`)
  const {ex, cx, u} = expressions(m, target, name, K)
  const decl = (n: string, init: string, mutable = true) => (target === 'wgsl' ? `${mutable ? 'var' : 'let'} ${n}: u32 = ${init};` : `${mutable ? 'let' : 'const'} ${n} = ${init};`)
  const lines: string[] = []
  lines.push(decl('rest', 'index'))
  for (const p of m.params) lines.push(decl(`p_${p}`, `rest % ${u(K)}`, false), `rest = ${target === 'wgsl' ? 'rest / ' + u(K) : `Math.floor(rest / ${K})`};`)
  if (m.pre) lines.push(`if (!${cx(m.pre)}) { return ${u(NONE)}; }`)
  for (const [n, e] of Object.entries(m.state)) lines.push(decl(`s_${n}`, ex(e)))
  for (const [map, init] of Object.entries(m.maps ?? {})) lines.push(target === 'wgsl' ? `var m_${map}: array<u32, ${K}>; for (var j = 0u; j < ${K}u; j++) { m_${map}[j] = ${init}u; }` : `const m_${map} = new Array(${K}).fill(${init});`)
  const check = (depth: string) => law.forall
    ? `for (${target === 'wgsl' ? 'var kk = 0u' : 'let kk = 0'}; kk <= ${u(K)}; kk++) { if (!${cx(law.holds)}) { return ${depth}; } }`
    : `if (!${cx(law.holds)}) { return ${depth}; }`
  lines.push(check(u(0)))
  const body: string[] = []
  for (const i of m.inputs) body.push(decl(`i_${i}`, `rest % ${u(K)}`, false), `rest = ${target === 'wgsl' ? 'rest / ' + u(K) : `Math.floor(rest / ${K})`};`)
  if (m.assume) body.push(`if (!${cx(m.assume)}) { return ${u(NONE)}; }`)
  for (const [f, c] of Object.entries(m.step.flags ?? {})) body.push(target === 'wgsl' ? `let f_${f}: bool = ${cx(c)};` : `const f_${f} = ${cx(c)};`)
  const next = Object.entries(m.step.state ?? {}), writes = Object.entries(m.step.maps ?? {})
  for (const [n, e] of next) body.push(decl(`n_${n}`, ex(e), false))
  for (const [map, w] of writes) body.push(decl(`w_${map}`, ex(w.value), false))
  for (const [n] of next) body.push(`s_${n} = n_${n};`)
  for (const [map, w] of writes) body.push(`m_${map}[${ex(w.key)}] = w_${map};`)
  body.push(check(target === 'wgsl' ? 't + 1u' : 't + 1'))
  lines.push(`for (${target === 'wgsl' ? 'var t = 0u' : 'let t = 0'}; t < ${u(s.depth)}; t++) {`, ...body.map(l => `  ${l}`), '}', `return ${u(NONE)};`)
  return lines.map(l => `  ${l}`).join('\n')
}

// A thread takes CHUNK consecutive candidates and reports the least (depth, offset) that fails, as depth·CHUNK + offset + 1.
export const CHUNK = 256
export function wgsl(m: Machine, law: Law, s: Space): string {
  return `
struct Params { count: u32, a: u32, b: u32, c: u32 }
@group(0) @binding(0) var<uniform> params: Params;
@group(0) @binding(1) var<storage, read> tables: array<u32>;
@group(0) @binding(2) var<storage, read> unused: array<u32>;
@group(0) @binding(3) var<storage, read_write> counts: array<f32>;
fn candidate(index: u32) -> u32 {
${emit(m, law, s, 'wgsl')}
}
@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) id: vec3<u32>) {
  let i: u32 = id.x;
  if (i >= params.count) { return; }
  _ = unused[0];
  let first = tables[0] + i * ${CHUNK}u;
  var best = 0xffffffffu;
  for (var off = 0u; off < ${CHUNK}u; off++) {
    if (first + off >= tables[1]) { break; }
    let depth = candidate(first + off);
    if (depth != 0xffffffffu) { best = min(best, depth * ${CHUNK}u + off); }
  }
  counts[i] = select(f32(best + 1u), 0.0, best == 0xffffffffu);
}`
}
export function js(m: Machine, law: Law, s: Space): (index: number) => number {
  return compileFunction<(index: number) => number>(['index'], emit(m, law, s, 'js'))
}
