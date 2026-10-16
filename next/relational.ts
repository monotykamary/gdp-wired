// Relational laws: two machines (or two runs of one) side by side, stepped by the same requests, as one machine whose
// state is both states. Migration safety is "a and b agree on every history"; tenant isolation is "what B sees is the
// same whether or not anyone else acts". Both become ordinary laws of the product, proven by the same induction.
import {type C, type E, type Law, type Machine, all, ite, same, unreachable, x} from '../core/machine.ts'

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

// a and b stepped by the same requests. `bInputs` rewrites what b sees, e.g. other tenants' requests as no-ops.
export function product(a: Machine, b: Machine, opts: {name?: string, params?: string[], inputs?: string[], bInputs?: Record<string, E>, assume?: C} = {}): Machine {
  const side = (m: Machine, p: string, inputs: Record<string, E>) => ({
    state: Object.fromEntries(Object.entries(m.state).map(([n, e]) => [`${p}${n}`, rename(e, p, m, {})])),
    maps: Object.fromEntries(Object.entries(m.maps ?? {}).map(([n, v]) => [`${p}${n}`, v])),
    step: {
      flags: Object.fromEntries(Object.entries(m.step.flags ?? {}).map(([n, c]) => [`${p}${n}`, renameC(c, p, m, inputs)])),
      state: Object.fromEntries(Object.entries(m.step.state ?? {}).map(([n, e]) => [`${p}${n}`, rename(e, p, m, inputs)])),
      maps: Object.fromEntries(Object.entries(m.step.maps ?? {}).map(([n, w]) => [`${p}${n}`, {key: rename(w.key, p, m, inputs), value: rename(w.value, p, m, inputs)}])),
    },
  })
  const A = side(a, 'a_', {}), B = side(b, 'b_', opts.bInputs ?? {})
  const assumes = [a.assume, b.assume, opts.assume].filter((c): c is C => c !== undefined)
  const pres = [a.pre, b.pre].filter((c): c is C => c !== undefined)
  return {
    name: opts.name ?? `${a.name} | ${b.name}`,
    params: [...new Set([...a.params, ...b.params, ...(opts.params ?? [])])],
    inputs: [...new Set([...a.inputs, ...b.inputs, ...(opts.inputs ?? [])])],
    state: {...A.state, ...B.state}, maps: {...A.maps, ...B.maps},
    step: {flags: {...A.step.flags, ...B.step.flags}, state: {...A.step.state, ...B.step.state}, maps: {...A.step.maps, ...B.step.maps}},
    ...(assumes.length ? {assume: all(...assumes)} : {}),
    ...(pres.length ? {pre: all(...pres)} : {}),
  }
}

// "a and b agree": every scalar equal, and every map equal at every key.
export function agree(a: Machine): Law[] {
  return [
    ...Object.keys(a.state).map(n => ({name: `a.${n} = b.${n}`, holds: same(x(`a_${n}`), x(`b_${n}`))})),
    ...Object.keys(a.maps ?? {}).map(n => ({name: `a.${n}[k] = b.${n}[k]`, holds: same({op: 'get', map: `a_${n}`, key: x('k')}, {op: 'get', map: `b_${n}`, key: x('k')}), forall: 'k'})),
  ]
}
void ite
