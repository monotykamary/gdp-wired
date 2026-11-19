import {types} from 'node:util'
import type {Law, Machine} from '../../core/machine.ts'
import {isSourceBound} from '../../core/source-check.ts'
import {scope} from '../../kernel/kernel.ts'

function refuse(detail: string): never { throw new Error(detail) }
const isObject = (v: unknown): v is object => v !== null && typeof v === 'object'

// Never look up a source property (including array elements) or serialize a
// caller-supplied object. Reject proxies before any reflective operation.
function snapshot(machine: object, law: object): string {
  if (Object.getPrototypeOf(Array.prototype) !== Object.prototype) refuse('Unexpected array prototype chain.')
  if (Object.getOwnPropertyDescriptor(Object.prototype, 'toJSON') ||
      Object.getOwnPropertyDescriptor(Array.prototype, 'toJSON')) refuse('Inherited toJSON is not supported.')
  const active = new Set<object>()
  let nodes = 0
  const copy = (v: unknown, depth: number): unknown => {
    if (++nodes > 250_000 || depth > 256) return refuse('Source data exceeds the snapshot bound.')
    if (v === null || typeof v === 'string' || typeof v === 'boolean' ||
        typeof v === 'number' && Number.isFinite(v) && !Object.is(v, -0)) return v
    if (!isObject(v) || types.isProxy(v)) return refuse('Source must contain only passive JSON data; omit absent optional fields.')
    if (active.has(v)) return refuse('Source data must not be cyclic.')
    const array = Array.isArray(v), proto: unknown = Object.getPrototypeOf(v)
    if (array ? proto !== Array.prototype && proto !== null : proto !== Object.prototype && proto !== null)
      return refuse('Unexpected source prototype.')
    active.add(v)
    const keys = Reflect.ownKeys(v)
    const out = (array ? Object.setPrototypeOf([], null) : Object.create(null)) as Record<string, unknown>
    const length = array ? Object.getOwnPropertyDescriptor(v, 'length')!.value as number : 0
    // An array has exactly its length descriptor and one enumerable data
    // descriptor per index. Reject holes, symbols and extra own properties.
    if (array && keys.length !== length + 1) return refuse('Source arrays must be dense and have no extra properties.')
    let i = 0
    for (const key of keys) {
      if (array && key === 'length') continue
      if (typeof key !== 'string' || key === 'toJSON' || array && key !== String(i++))
        return refuse('Unsupported source property.')
      const d = Object.getOwnPropertyDescriptor(v, key)!
      if (!d.enumerable || !Object.hasOwn(d, 'value')) return refuse('Source properties must be enumerable own data.')
      out[key] = copy(d.value, depth + 1)
    }
    active.delete(v)
    return out
  }
  const pair: unknown[] = [copy(machine, 0), copy(law, 0)]
  Object.setPrototypeOf(pair, null)
  return JSON.stringify(pair)
}

type Row = Record<string, unknown>
const record = (v: unknown): v is Row => isObject(v) && !Array.isArray(v)
const fields = (v: unknown, required: string[], optional: string[] = []): v is Row =>
  record(v) && required.every(k => Object.hasOwn(v, k)) && Object.keys(v).every(k => required.includes(k) || optional.includes(k))
// These labels may be printed in comments. Do not let one supply Lean syntax.
function label(v: unknown): v is string {
  if (typeof v !== 'string' || v.includes('/-') || v.includes('-/')) return false
  for (const c of v) {
    const point = c.codePointAt(0)!
    if (point < 0x20 || point >= 0x7f && point <= 0x9f || point === 0x2028 || point === 0x2029) return false
  }
  return true
}
const nat = (v: unknown): boolean => typeof v === 'number' && Number.isSafeInteger(v) && v >= 0
const list = (v: unknown, valid: (a: unknown) => boolean): boolean => Array.isArray(v) && v.every(valid)
const table = (v: unknown, valid: (a: unknown) => boolean): boolean =>
  record(v) && Object.entries(v).every(([key, x]) => label(key) && valid(x))
const emptyList = (v: unknown): boolean => Array.isArray(v) && v.length === 0
const emptyTable = (v: unknown): boolean => record(v) && Object.keys(v).length === 0
const optional = (v: Row, key: string, valid: (a: unknown) => boolean): boolean => !Object.hasOwn(v, key) || valid(v[key])

// Validate the closed natural-number source fragment, not just its opcodes.
// No primitive failure, carried maps, history, derived values, external facts,
// native functions, or alternate law binders may reach either recognizer.
function admissible(m: unknown, law: unknown): boolean {
  if (!fields(m, ['name', 'params', 'inputs', 'state', 'step'], ['maps', 'pre', 'assume', 'inputMaps', 'facts', 'fns', 'leasts', 'relations']) ||
      !fields(law, ['name', 'holds'], ['forall', 'keys', 'some', 'stated']) ||
      !fields(m.step, [], ['state', 'maps', 'flags'])) return false
  const maps = Object.hasOwn(m, 'maps') ? m.maps : {}
  function term(v: unknown): boolean {
    if (!record(v) || !Object.hasOwn(v, 'op')) return false
    switch (v.op) {
      case 'var': return fields(v, ['op', 'name']) && label(v.name)
      case 'const': return fields(v, ['op', 'value']) && nat(v.value)
      case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'tup':
        return fields(v, ['op', 'a', 'b']) && term(v.a) && term(v.b)
      case 'mul': return fields(v, ['op', 'k', 'a']) && nat(v.k) && term(v.a)
      case 'proj': return fields(v, ['op', 'k', 'a']) && (v.k === 0 || v.k === 1) && term(v.a)
      case 'if': return fields(v, ['op', 'c', 'then', 'else']) && cond(v.c) && term(v.then) && term(v.else)
      case 'get': return fields(v, ['op', 'map', 'key']) && label(v.map) && record(maps) && Object.hasOwn(maps, v.map) && term(v.key)
      default: return false
    }
  }
  function cond(v: unknown): boolean {
    if (!record(v) || !Object.hasOwn(v, 'op')) return false
    switch (v.op) {
      case '<': case '<=': case '=': return fields(v, ['op', 'a', 'b']) && term(v.a) && term(v.b)
      case 'and': case 'or': return fields(v, ['op', 'xs']) && list(v.xs, cond)
      case 'not': return fields(v, ['op', 'x']) && cond(v.x)
      case 'flag': return fields(v, ['op', 'name']) && label(v.name)
      default: return false
    }
  }
  const write = (v: unknown) =>
    (fields(v, ['each', 'value']) && label(v.each) || fields(v, ['key', 'value']) && term(v.key)) && term(v.value)
  return label(m.name) && label(law.name) && list(m.params, label) && list(m.inputs, label) && table(maps, nat) &&
    table(m.state, term) && optional(m.step, 'state', v => table(v, term)) && optional(m.step, 'maps', v => table(v, write)) &&
    optional(m.step, 'flags', v => table(v, cond)) && optional(m, 'pre', cond) && optional(m, 'assume', cond) &&
    optional(m, 'inputMaps', emptyList) && optional(m, 'facts', emptyList) && optional(m, 'fns', emptyTable) &&
    optional(m, 'leasts', emptyTable) && optional(m, 'relations', v => table(v, a => list(a, label))) &&
    optional(law, 'forall', v => label(v) && v.length > 0) && optional(law, 'keys', emptyList) && optional(law, 'some', emptyList) &&
    cond(law.holds) && optional(law, 'stated', v => cond(v) && JSON.stringify(v) === JSON.stringify(law.holds))
}

export function admitAggregateSource(machine: Machine, law: Law): string {
  if (!isObject(machine) || !isObject(law) || types.isProxy(machine) || types.isProxy(law))
    return refuse('Source machine and invariant must be passive data.')
  // These identities matter before copying: the marker deliberately survives
  // without a native journal. This adapter only certifies an unmarked model.
  if (isSourceBound(machine, [law])) return refuse('Source-bound machines and laws are not supported; this adapter checks models only.')
  const input = snapshot(machine, law)
  const [m, l] = JSON.parse(input) as [Machine, Law]
  if (!admissible(m, l)) return refuse('Unsupported source machine or invariant.')
  // Scope the exact, uninstrumented data the worker will parse, before either
  // recognizer. The retained, instrumented family is a separate obligation.
  scope(m, [l])
  return input
}
