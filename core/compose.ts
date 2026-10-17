// Composition: machines built from machines. Each combinator returns a plain Machine, so every capability (laws by
// induction, step laws, k-step laws, progress, the runtimes, the Lean twin) applies to what it builds, and nothing here
// is trusted: a proof is about the machine built, and the combinators are tested against runs of their parts.
//   product(a, b)      both step on every request (their params and inputs shared by name)
//   interleave(a, b)   one of them steps on each request, `turn` picking which
//   refinement(impl, spec, {relation, witness})
//                      impl refines spec: the spec, sent the request `witness` names for each of impl's, always allows it,
//                      and `relation` holds of the two states at every step (a forward simulation)
// Each side's state, maps and flags are renamed a_x and b_x; params and inputs keep their names.
import {type C, type E, type Law, type Machine, all, any, bit, not, same, unreachable, x} from './machine.ts'
import type {StepLaw} from '../kernel/kernel.ts'

function rename(e: E, prefix: string, m: Machine, inputs: Record<string, E>): E {
  switch (e.op) {
    case 'var': return m.params.includes(e.name) ? e : m.inputs.includes(e.name) ? (inputs[e.name] ?? e) : x(`${prefix}${e.name}`)
    case 'const': return e
    case 'mul': return {...e, a: rename(e.a, prefix, m, inputs)}
    case 'if': return {op: 'if', c: renameC(e.c, prefix, m, inputs), then: rename(e.then, prefix, m, inputs), else: rename(e.else, prefix, m, inputs)}
    case 'get': return {op: 'get', map: `${prefix}${e.map}`, key: rename(e.key, prefix, m, inputs)}
    case 'add': case 'sub': case 'min': case 'max': case 'prod': return {...e, a: rename(e.a, prefix, m, inputs), b: rename(e.b, prefix, m, inputs)}
    default: return unreachable(e)
  }
}
function renameC(c: C, prefix: string, m: Machine, inputs: Record<string, E>): C {
  if (c.op === 'flag') return {op: 'flag', name: `${prefix}${c.name}`}
  if (c.op === 'not') return {op: 'not', x: renameC(c.x, prefix, m, inputs)}
  if (c.op === 'and' || c.op === 'or') return {op: c.op, xs: c.xs.map(y => renameC(y, prefix, m, inputs))}
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
const conj = (cs: (C | undefined)[]): C | undefined => { const xs = cs.filter((c): c is C => c !== undefined); return xs.length ? all(...xs) : undefined }

// a and b stepped by the same requests. `bInputs` rewrites what b sees (other tenants' requests as no-ops, say).
export function product(a: Machine, b: Machine, opts: {name?: string, params?: string[], inputs?: string[], bInputs?: Record<string, E>, assume?: C} = {}): Machine {
  const A = renamed(a, 'a_', {}), B = renamed(b, 'b_', opts.bInputs ?? {})
  const assume = conj([A.assume, B.assume, opts.assume]), pre = conj([a.pre, b.pre])
  return {
    name: opts.name ?? `${a.name} | ${b.name}`,
    params: [...new Set([...a.params, ...b.params, ...(opts.params ?? [])])],
    inputs: [...new Set([...a.inputs, ...b.inputs, ...(opts.inputs ?? [])])],
    ...join(A, B),
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
    ...join(A, B),
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
export function refinement(impl: Machine, spec: Machine, opts: {relation: Law[], witness: Record<string, E>, name?: string}): {machine: Machine, laws: Law[], stepLaws: StepLaw[]} {
  if (!spec.inputs.every(i => i in opts.witness)) throw new Error(`refinement: name every input of ${spec.name} (${spec.inputs.join(', ')})`)
  const A = renamed(impl, 'a_', {}), B = renamed(spec, 'b_', opts.witness)
  const allowedBy = B.assume
  const machine: Machine = {
    name: opts.name ?? `${impl.name} refines ${spec.name}`,
    params: [...new Set([...impl.params, ...spec.params])],
    inputs: impl.inputs,
    ...join(A, B),
    ...(A.assume ? {assume: A.assume} : {}),
    ...(impl.pre ? {pre: impl.pre} : {}),
  }
  const laws = [...opts.relation, ...(spec.pre ? [{name: `${spec.name}'s precondition`, holds: spec.pre}] : [])]
  const stepLaws: StepLaw[] = allowedBy ? [{name: `${spec.name} allows the request it is sent`, then: allowedBy}] : []
  return {machine, laws, stepLaws}
}

// "a and b agree" in a product of a machine with another of its shape: every scalar equal, every map equal at every key.
export function agree(a: Machine): Law[] {
  return [
    ...Object.keys(a.state).map(n => ({name: `a.${n} = b.${n}`, holds: same(x(`a_${n}`), x(`b_${n}`))})),
    ...Object.keys(a.maps ?? {}).map(n => ({name: `a.${n}[k] = b.${n}[k]`, holds: same({op: 'get', map: `a_${n}`, key: x('k')}, {op: 'get', map: `b_${n}`, key: x('k')}), forall: 'k'})),
  ]
}
