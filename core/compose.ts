// Composition: machines built from machines. Each combinator returns a plain Machine, so every capability (laws by
// induction, step laws, k-step laws, progress, the runtimes, the Lean twin) applies to what it builds, and nothing here
// is trusted: a proof is about the machine built, and the combinators are tested against runs of their parts.
//   product(a, b)      both step on every request (their params and inputs shared by name)
//   interleave(a, b)   one of them steps on each request, `turn` picking which
//   refinement(impl, spec, {relation, witness, stutter})
//                      impl refines spec: the spec, sent the request `witness` names for each of impl's, always allows it,
//                      and `relation` holds of the two states at every step (a forward simulation); where `stutter`
//                      holds, impl's step is one the spec doesn't see, and the spec stays
//   ghost(m, vars)     state that watches the machine without changing it: what happened before ("ever", "count") and
//                      totals across a map's keys ("total"), for laws about whole histories
//   steps(m, k)        k steps of m as one: the spec of a refinement that takes several steps for one of impl's
// Each side's state, maps and flags are renamed a_x and b_x; params and inputs keep their names.
import {type C, type E, type Law, type Machine, type MapUpdate, all, any, bit, not, same, unreachable, x} from './machine.ts'
import {type StepLaw, type Subst, substC, substE} from '../kernel/kernel.ts'
import {nameQuantifiers} from './dsl.ts'

function rename(e: E, prefix: string, m: Machine, inputs: Record<string, E>): E {
  switch (e.op) {
    case 'var': return m.params.includes(e.name) ? e : m.inputs.includes(e.name) ? (inputs[e.name] ?? e) : x(`${prefix}${e.name}`)
    case 'const': return e
    case 'mul': return {...e, a: rename(e.a, prefix, m, inputs)}
    case 'if': return {op: 'if', c: renameC(e.c, prefix, m, inputs), then: rename(e.then, prefix, m, inputs), else: rename(e.else, prefix, m, inputs)}
    case 'get': return {op: 'get', map: m.inputMaps?.includes(e.map) ? e.map : `${prefix}${e.map}`, key: rename(e.key, prefix, m, inputs)}
    case 'add': case 'sub': case 'min': case 'max': case 'prod': return {...e, a: rename(e.a, prefix, m, inputs), b: rename(e.b, prefix, m, inputs)}
    default: return unreachable(e)
  }
}
function renameC(c: C, prefix: string, m: Machine, inputs: Record<string, E>): C {
  if (c.op === 'flag') return {op: 'flag', name: `${prefix}${c.name}`}
  if (c.op === 'not') return {op: 'not', x: renameC(c.x, prefix, m, inputs)}
  if (c.op === 'and' || c.op === 'or') return {op: c.op, xs: c.xs.map(y => renameC(y, prefix, m, inputs))}
  if (c.op === 'all') return {...c, key: `${prefix}${c.key}`, ...(c.keys ? {keys: c.keys.map(k => `${prefix}${k}`)} : {}), c: renameC(c.c, prefix, m, inputs)} // the keys renamed with their side
  return {...c, a: rename(c.a, prefix, m, inputs), b: rename(c.b, prefix, m, inputs)}
}
// A condition (or law) of one side, read in the composed machine.
export const side = (m: Machine, prefix: 'a_' | 'b_', c: C): C => renameC(c, prefix, m, {})

// One side renamed; `stays` (if given) is when its state doesn't move: each update and write keeps the old value then.
function renamed(m: Machine, p: string, inputs: Record<string, E>, stays?: C) {
  if (m.history) throw new Error(`${m.name}: a machine with a history is composed as its plain machine (historyMachine)`)
  const keep = (now: E, old: E): E => (stays ? {op: 'if', c: stays, then: old, else: now} : now)
  return {
    state: Object.fromEntries(Object.entries(m.state).map(([n, e]) => [`${p}${n}`, rename(e, p, m, {})])),
    maps: Object.fromEntries(Object.entries(m.maps ?? {}).map(([n, v]) => [`${p}${n}`, v])),
    step: {
      flags: Object.fromEntries(Object.entries(m.step.flags ?? {}).map(([n, c]) => [`${p}${n}`, renameC(c, p, m, inputs)])),
      state: Object.fromEntries(Object.entries(m.step.state ?? {}).map(([n, e]) => [`${p}${n}`, keep(rename(e, p, m, inputs), x(`${p}${n}`))])),
      maps: Object.fromEntries(Object.entries(m.step.maps ?? {}).map(([n, w]) => {
        if ('each' in w) return [`${p}${n}`, {each: `${p}${w.each}`, value: keep(rename(w.value, p, m, inputs), {op: 'get', map: `${p}${n}`, key: x(`${p}${w.each}`)})}]
        const key = rename(w.key, p, m, inputs)
        return [`${p}${n}`, {key, value: keep(rename(w.value, p, m, inputs), {op: 'get', map: `${p}${n}`, key})}]
      })),
    },
    assume: m.assume ? renameC(m.assume, p, m, inputs) : undefined,
  }
}
const join = (a: ReturnType<typeof renamed>, b: ReturnType<typeof renamed>) => ({
  state: {...a.state, ...b.state}, maps: {...a.maps, ...b.maps},
  step: {flags: {...a.step.flags, ...b.step.flags}, state: {...a.step.state, ...b.step.state}, maps: {...a.step.maps, ...b.step.maps}},
})
// The maps requests carry: shared by name, as inputs are.
const carriedBy = (...ms: Machine[]) => { const names = [...new Set(ms.flatMap(m => m.inputMaps ?? []))]; return names.length ? {inputMaps: names} : {} }
const conj = (cs: (C | undefined)[]): C | undefined => { const xs = cs.filter((c): c is C => c !== undefined); return xs.length ? all(...xs) : undefined }

// a and b stepped by the same requests. `bInputs` rewrites what b sees (other tenants' requests as no-ops, say).
export function product(a: Machine, b: Machine, opts: {name?: string, params?: string[], inputs?: string[], bInputs?: Record<string, E>, assume?: C} = {}): Machine {
  const A = renamed(a, 'a_', {}), B = renamed(b, 'b_', opts.bInputs ?? {})
  const assume = conj([A.assume, B.assume, opts.assume]), pre = conj([a.pre, b.pre])
  return {
    name: opts.name ?? `${a.name} | ${b.name}`,
    params: [...new Set([...a.params, ...b.params, ...(opts.params ?? [])])],
    inputs: [...new Set([...a.inputs, ...b.inputs, ...(opts.inputs ?? [])])],
    ...join(A, B), ...carriedBy(a, b),
    ...(assume ? {assume} : {}),
    ...(pre ? {pre} : {}),
  }
}

// One of a and b steps on each request: a when turn = 0, b when turn = 1; the other keeps its state and maps. Each
// side's assumption is about its own turns only.
export function interleave(a: Machine, b: Machine, opts: {name?: string, turn?: string} = {}): Machine {
  const turn = opts.turn ?? 'turn'
  if ([...a.params, ...a.inputs, ...b.params, ...b.inputs].includes(turn)) throw new Error(`interleave: ${turn} is already a name of ${a.name} or ${b.name}`)
  const isA = same(x(turn), {op: 'const', value: 0}), isB = same(x(turn), {op: 'const', value: 1})
  const A = renamed(a, 'a_', {}, isB), B = renamed(b, 'b_', {}, isA)
  const pre = conj([a.pre, b.pre])
  return {
    name: opts.name ?? `${a.name} || ${b.name}`,
    params: [...new Set([...a.params, ...b.params])],
    inputs: [...new Set([...a.inputs, ...b.inputs, turn])],
    ...join(A, B), ...carriedBy(a, b),
    assume: all(bit(turn), ...(A.assume ? [any(not(isA), A.assume)] : []), ...(B.assume ? [any(not(isB), B.assume)] : [])),
    ...(pre ? {pre} : {}),
  }
}

// impl refines spec. The machine is impl and spec side by side, the spec sent, at each of impl's requests, the request
// `witness` names (a term per spec input over impl's request, the params and both states, a_ and b_ names). The spec's
// assumption is not assumed there: the step law `allowed` proves the spec allows every request it is sent. `relation`
// (conditions over both states) holds at the start and after every step: the laws, proven by induction. With the
// precondition: impl's is assumed, and the spec's, if any, is a law (it holds of every impl's params).
// So every run of impl is matched, step by step, by a run of the spec that its own rules allow, related by `relation`.
export function refinement(impl: Machine, spec: Machine, opts: {relation: Law[], witness: Record<string, E>, stutter?: C, name?: string}): {machine: Machine, laws: Law[], stepLaws: StepLaw[]} {
  if (!spec.inputs.every(i => i in opts.witness)) throw new Error(`refinement: name every input of ${spec.name} (${spec.inputs.join(', ')})`)
  if ((spec.inputMaps ?? []).some(mp => !(impl.inputMaps ?? []).includes(mp))) throw new Error(`refinement: a map ${spec.name}'s requests carry is one ${impl.name}'s carry too (shared by name)`)
  const A = renamed(impl, 'a_', {}), B = renamed(spec, 'b_', opts.witness, opts.stutter)
  // A step the spec doesn't see needs no request it allows.
  const allowedBy = B.assume && opts.stutter ? any(opts.stutter, B.assume) : B.assume
  const machine: Machine = {
    name: opts.name ?? `${impl.name} refines ${spec.name}`,
    params: [...new Set([...impl.params, ...spec.params])],
    inputs: impl.inputs,
    ...join(A, B), ...carriedBy(impl, spec),
    ...(A.assume ? {assume: A.assume} : {}),
    ...(impl.pre ? {pre: impl.pre} : {}),
  }
  const laws = [...opts.relation, ...(spec.pre ? [{name: `${spec.name}'s precondition`, holds: spec.pre}] : [])]
  const stepLaws: StepLaw[] = allowedBy ? [{name: `${spec.name} allows the request it is sent`, then: allowedBy}] : []
  return {machine, laws, stepLaws}
}

// A refinement's two sides as machines in its composite's names (for lean-kernel/Refine.lean, which builds the composite
// from them): the implementation's parts named a_x, the spec's b_x, the spec's inputs b_<input> (which the composite
// never reads: the witness stands for them there).
export function refinementSides(impl: Machine, spec: Machine): {impl: Machine, spec: Machine} {
  const named = (m: Machine, p: string, inputs: Record<string, E>, inputNames: string[]): Machine => {
    const R = renamed(m, p, inputs)
    return {name: m.name, params: m.params, inputs: inputNames, state: R.state, maps: R.maps, step: R.step, ...(m.inputMaps?.length ? {inputMaps: m.inputMaps} : {}), ...(R.assume ? {assume: R.assume} : {}), ...(m.pre ? {pre: m.pre} : {})}
  }
  return {impl: named(impl, 'a_', {}, impl.inputs), spec: named(spec, 'b_', Object.fromEntries(spec.inputs.map(i => [i, x(`b_${i}`)])), spec.inputs.map(i => `b_${i}`))}
}

// "a and b agree" in a product of a machine with another of its shape: every scalar equal, every map equal at every key.
export function agree(a: Machine): Law[] {
  return [
    ...Object.keys(a.state).map(n => ({name: `a.${n} = b.${n}`, holds: same(x(`a_${n}`), x(`b_${n}`))})),
    ...Object.keys(a.maps ?? {}).map(n => ({name: `a.${n}[k] = b.${n}[k]`, holds: same({op: 'get', map: `a_${n}`, key: x('k')}, {op: 'get', map: `b_${n}`, key: x('k')}), forall: 'k'})),
  ]
}

// --- several steps as one --------------------------------------------------------------------------------------------

// k steps of m in a row as one step: the j-th request read as <input>@s<j> (j from 1), each step skipped where its input
// skip@s<j> is 1. Each step reads the state the one before it left (its flags decided there, every map read over the
// writes before), so several writes to one map become one write at every key, its key compared with theirs (which the
// runtimes decide on breakpoints). Its assumption: each step not skipped is one m allows. As the spec of a refinement,
// the witness names each step's request and when it is skipped.
export function steps(m: Machine, k: number): Machine {
  if (!Number.isInteger(k) || k < 1) throw new Error('steps: k is a whole number at least 1')
  if (m.history || m.inputMaps?.length) throw new Error(`steps: ${m.name} has a history or maps a request carries (not taken here)`)
  const at = (name: string, j: number) => `${name}@s${j}`
  let vars: Record<string, E> = Object.fromEntries(Object.keys(m.state).map(n => [n, x(n)]))
  let maps: Record<string, (key: E) => E> = Object.fromEntries(Object.keys(m.maps ?? {}).map(map => [map, (key: E): E => ({op: 'get', map, key})]))
  const allowed: C[] = [], written = new Set<string>()
  for (let j = 1; j <= k; j++) {
    const skip: C = same(x(at('skip', j)), {op: 'const', value: 1})
    const sub: Subst = {vars: {...vars, ...Object.fromEntries(m.inputs.map(i => [i, x(at(i, j))]))}, maps, flags: {}}
    for (const [f, c] of Object.entries(m.step.flags ?? {})) sub.flags[f] = substC(c, sub)
    if (m.assume) allowed.push(any(skip, substC(m.assume, sub)))
    const kept = (now: E, old: E): E => ({op: 'if', c: skip, then: old, else: now})
    const nextVars = {...vars}
    for (const [n, e] of Object.entries(m.step.state ?? {})) nextVars[n] = kept(substE(e, sub), vars[n]!)
    const nextMaps = {...maps}
    for (const [map, w] of Object.entries(m.step.maps ?? {}) as [string, MapUpdate][]) {
      written.add(map)
      const old = maps[map]!
      if ('each' in w) nextMaps[map] = (key: E) => kept(substE(w.value, {...sub, vars: {...sub.vars, [w.each]: key}}), old(key))
      else { const wk = substE(w.key, sub), wv = substE(w.value, sub); nextMaps[map] = (key: E) => kept({op: 'if', c: same(key, wk), then: wv, else: old(key)}, old(key)) }
    }
    vars = nextVars
    maps = nextMaps
  }
  const each = 'k$steps'
  return nameQuantifiers({
    name: `${m.name}, ${k} steps at once`, params: m.params,
    inputs: Array.from({length: k}, (_, i) => [...m.inputs.map(n => at(n, i + 1)), at('skip', i + 1)]).flat(),
    state: m.state, ...(m.maps ? {maps: m.maps} : {}),
    step: {
      state: Object.fromEntries(Object.keys(m.step.state ?? {}).map(n => [n, vars[n]!])),
      ...(written.size ? {maps: Object.fromEntries([...written].map(map => [map, {each, value: maps[map]!(x(each))}]))} : {}),
    },
    assume: all(...Array.from({length: k}, (_, i) => bit(at('skip', i + 1))), ...allowed),
    ...(m.pre ? {pre: m.pre} : {}),
  })
}

// --- ghosts ------------------------------------------------------------------------------------------------------------

// Ghost state: variables that watch m without changing it. Each starts at a term over the params and moves at every step
// by a term over the state before it, the request and the flags; nothing of m reads them (their names are new), so m's
// runs are the ghosted machine's runs with the ghosts dropped, and a law about a ghost is a law about m's history.
export type Ghost = {start: E, step: E}
export function ghost(m: Machine, vars: Record<string, Ghost>): Machine {
  const taken = [...m.params, ...m.inputs, ...Object.keys(m.state), ...Object.keys(m.maps ?? {}), ...Object.keys(m.step.flags ?? {})]
  for (const name of Object.keys(vars)) if (taken.includes(name)) throw new Error(`ghost: ${name} is already a name of ${m.name}`)
  if (m.history) throw new Error(`${m.name}: ghosts go on a machine without a history (its sums are ghosts of that kind already)`)
  return {
    ...m,
    state: {...m.state, ...Object.fromEntries(Object.entries(vars).map(([n, g]) => [n, g.start]))},
    step: {...m.step, state: {...m.step.state, ...Object.fromEntries(Object.entries(vars).map(([n, g]) => [n, g.step]))}},
  }
}
// Whether `cond` has held at some step so far (read where the step reads: the state before, the request, the flags).
export const ever = (name: string, cond: C): Ghost => ({start: {op: 'const', value: 0}, step: {op: 'if', c: cond, then: {op: 'const', value: 1}, else: x(name)}})
// How many steps so far `cond` held at.
export const count = (name: string, cond: C): Ghost => ({start: {op: 'const', value: 0}, step: {op: 'add', a: x(name), b: {op: 'if', c: cond, then: {op: 'const', value: 1}, else: {op: 'const', value: 0}}}})
// The total of a map over every key: the map must start at 0 everywhere (so finitely many keys are nonzero), and each
// step writes one key, so the total moves by the value written less the value it replaces. That difference is pushed
// through the written term where its shape gives it (old + d adds d; old ∸ d takes min(d, old); an if moves each way
// by its branch's), so a proof needs no fact about the total beyond the law it is about; any other term falls back to
// total ∸ old + new (exact, since the total is at least any one cell).
export function total(m: Machine, map: string, name: string): Ghost {
  if ((m.maps ?? {})[map] !== 0) throw new Error(`total: ${map} must start at 0 at every key`)
  const w = m.step.maps?.[map]
  if (!w) return {start: {op: 'const', value: 0}, step: x(name)}
  if ('each' in w) throw new Error(`total: ${map} is written at every key at once, which no one step's difference describes`)
  const old: E = {op: 'get', map, key: w.key}, t = x(name), same = (a: E) => JSON.stringify(a) === JSON.stringify(old)
  const moved = (e: E): E => {
    if (same(e)) return t
    if (e.op === 'add' && same(e.a)) return {op: 'add', a: t, b: e.b}
    if (e.op === 'add' && same(e.b)) return {op: 'add', a: t, b: e.a}
    if (e.op === 'sub' && same(e.a)) return {op: 'sub', a: t, b: {op: 'min', a: e.b, b: old}}
    if (e.op === 'if') return {op: 'if', c: e.c, then: moved(e.then), else: moved(e.else)}
    return {op: 'add', a: {op: 'sub', a: t, b: old}, b: e}
  }
  return {start: {op: 'const', value: 0}, step: moved(w.value)}
}
