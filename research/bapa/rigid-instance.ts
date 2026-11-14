// Experimental finite-instance validation only. This is NOT a new kernel
// acceptance path or the source-to-emitted-machine proof bridge.
export type RigidTerm = {variable: string} | {call: string, args: readonly RigidTerm[]}
export type RigidAtom = {relation: string, args: readonly RigidTerm[]}
export type RigidSymbol = {args: readonly string[], result?: string} // omitted result = Boolean relation
export type RigidBinder = {name: string, sort: string}
export type RigidAxiom = {name: string, forall: readonly [RigidBinder, RigidBinder], exists: RigidBinder, body: readonly RigidAtom[]}
export type RigidSignature = {
  sorts: Readonly<Record<string, string>> // sort -> immutable size parameter
  symbols: Readonly<Record<string, RigidSymbol>>
  axioms: readonly RigidAxiom[]
}
type Table = {readonly dimensions: readonly number[], readonly values: readonly number[]}
export type RigidWitness = {readonly name: string, readonly axiom: string, readonly args: readonly string[], readonly result: string, readonly table: Table}
const validationToken = Symbol('validated rigid instance')
const validatedInstances = new WeakSet<object>()
const own = (o: object, k: PropertyKey) => Object.prototype.hasOwnProperty.call(o, k)
function fail(s: string): never { throw new Error(`rigid instance: ${s}`) }
const record = (x: unknown, what: string): Record<string, unknown> => {
  if (!x || typeof x !== 'object' || Array.isArray(x) || (Object.getPrototypeOf(x) !== Object.prototype && Object.getPrototypeOf(x) !== null)) fail(`${what} must be a JSON object`)
  return x as Record<string, unknown>
}
const nat = (x: unknown, what: string): number => {
  if (typeof x !== 'number' || !Number.isSafeInteger(x) || x < 0) fail(`${what} must be a safe natural`)
  return x as number
}
const name = (x: unknown, what: string): string => {
  if (typeof x !== 'string' || !/^[A-Za-z_][A-Za-z0-9_$]*$/.test(x) || ['__proto__', 'constructor', 'prototype'].includes(x)) fail(`${what} is not a permitted name`)
  return x as string
}
const exactKeys = (x: Record<string, unknown>, allowed: readonly string[], what: string) => {
  if (Object.keys(x).some(k => !allowed.includes(k))) fail(`${what} has an unknown field`)
}
const cells = (dims: readonly number[]): number => {
  if (dims.some(n => n === 0)) return 0
  let n = 1
  for (const d of dims) { if (n > Number.MAX_SAFE_INTEGER / d) fail('table cardinality passes safe integers'); n *= d }
  // A serialized JS array cannot represent more cells, even if the sorts can.
  if (n > 0xffffffff) fail('table exceeds the representable array length')
  return n
}
const lookup = (t: Table, args: readonly number[]): number => {
  if (args.length !== t.dimensions.length) fail('wrong arity')
  let i = 0
  for (let k = 0; k < args.length; k++) {
    const a = nat(args[k], 'lookup coordinate'), d = t.dimensions[k]!
    if (a >= d) fail('lookup coordinate outside its sort')
    i = i * d + a
  }
  return t.values[i]!
}

/** Binding consumes JSON text, never an interpretation callback or mutable table.
 * checkpoint is cancellation only: it cannot provide relation/function values.
 * A cancelled/invalid validation never returns a partially bound instance. */
export function validateRigidInstance(signature: RigidSignature, serialized: string, checkpoint: () => void): ValidatedRigidInstance {
  if (typeof serialized !== 'string' || typeof checkpoint !== 'function') fail('serialized JSON and a cancellation checkpoint are required')
  checkpoint()
  // Snapshot model declarations too; bindings cannot be retargeted afterwards.
  const sig = JSON.parse(JSON.stringify(signature)) as RigidSignature
  const sr = record(sig.sorts, 'sorts'), sy = record(sig.symbols, 'symbols')
  const sorts = Object.keys(sr)
  for (const s of sorts) { name(s, 'sort'); name(sr[s], 'size parameter') }
  const input = record(JSON.parse(serialized), 'input'); exactKeys(input, ['params', 'tables'], 'input')
  const rawParams = record(input.params, 'params'), rawTables = record(input.tables, 'tables')
  const parameterNames = [...new Set(Object.values(sig.sorts))]
  exactKeys(rawParams, parameterNames, 'params'); exactKeys(rawTables, Object.keys(sy), 'tables')
  const params: Record<string, number> = Object.create(null)
  for (const p of parameterNames) params[p] = nat(rawParams[p], `parameter ${p}`)
  const size = (s: string): number => own(sig.sorts, s) ? params[sig.sorts[s]!]! : fail(`undeclared sort ${s}`)
  let work = 0
  const tick = () => { if ((work++ & 255) === 0) checkpoint() }
  const tables: Record<string, Table> = Object.create(null)
  for (const [symbol, raw] of Object.entries(sy)) {
    name(symbol, 'symbol'); const d = record(raw, `symbol ${symbol}`); exactKeys(d, ['args', 'result'], `symbol ${symbol}`)
    if (!Array.isArray(d.args) || d.args.length === 0 || d.args.some(s => typeof s !== 'string' || !own(sig.sorts, s))) fail(`invalid argument sorts for ${symbol}`)
    if (d.result !== undefined && (typeof d.result !== 'string' || !own(sig.sorts, d.result))) fail(`invalid result sort for ${symbol}`)
    const dimensions = Object.freeze((d.args as string[]).map(size)), count = cells(dimensions), rawValues = rawTables[symbol]
    if (!Array.isArray(rawValues) || rawValues.length !== count) fail(`table ${symbol} must have exactly ${count} cells`)
    const values = rawValues.map((x, i) => {
      tick(); const value = nat(x, `${symbol}[${i}]`)
      if (d.result === undefined ? value > 1 : value >= size(d.result as string)) fail(`cell ${symbol}[${i}] is outside its result kind`)
      return value
    })
    tables[symbol] = Object.freeze({dimensions, values: Object.freeze(values)})
  }
  if (!Array.isArray(sig.axioms)) fail('axioms must be an array')
  const taken = new Set([...Object.keys(sy), ...sorts, ...parameterNames]), seenAxioms = new Set<string>(), witnesses: RigidWitness[] = []
  for (const ax of sig.axioms) {
    name(ax.name, 'axiom'); if (seenAxioms.has(ax.name)) fail(`duplicate axiom ${ax.name}`); seenAxioms.add(ax.name)
    if (!Array.isArray(ax.forall) || ax.forall.length !== 2 || !Array.isArray(ax.body)) fail(`axiom ${ax.name} requires two universal binders and a conjunction`)
    const bindings = [...ax.forall, ax.exists], variables: Record<string, string> = Object.create(null)
    for (const b of bindings) {
      if (!b || typeof b !== 'object') fail(`invalid binder in ${ax.name}`)
      name(b.name, 'binder'); if (own(variables, b.name)) fail(`duplicate binder ${b.name}`)
      size(b.sort); variables[b.name] = b.sort
    }
    const typeOf = (t: RigidTerm): string => {
      const r = record(t, 'axiom term')
      if (own(r, 'variable')) {
        exactKeys(r, ['variable'], 'variable term')
        if (typeof r.variable !== 'string' || !own(variables, r.variable)) fail('unbound axiom variable')
        return variables[r.variable as string]!
      }
      exactKeys(r, ['call', 'args'], 'function term')
      if (typeof r.call !== 'string' || !own(sig.symbols, r.call)) fail('undeclared axiom function')
      const d = sig.symbols[r.call as string]!
      if (d.result === undefined || !Array.isArray(r.args) || r.args.length !== d.args.length) fail('axiom term must call a declared function at its arity')
      r.args.forEach((a, i) => { if (typeOf(a as RigidTerm) !== d.args[i]) fail('axiom function argument sort mismatch') })
      return d.result!
    }
    for (const atom of ax.body) {
      const r = record(atom, 'axiom atom'); exactKeys(r, ['relation', 'args'], 'axiom atom')
      if (typeof r.relation !== 'string' || !own(sig.symbols, r.relation)) fail('undeclared axiom relation')
      const d = sig.symbols[r.relation as string]!
      if (d.result !== undefined || !Array.isArray(r.args) || r.args.length !== d.args.length) fail('axiom atom must call a relation at its arity')
      r.args.forEach((a, i) => { if (typeOf(a as RigidTerm) !== d.args[i]) fail('axiom relation argument sort mismatch') })
    }
    const env: Record<string, number> = Object.create(null)
    const term = (t: RigidTerm): number => 'variable' in t ? env[t.variable]! : lookup(tables[t.call]!, t.args.map(term))
    const dimensions = Object.freeze(ax.forall.map((b: RigidBinder) => size(b.sort))), values: number[] = []
    cells(dimensions)
    for (let a = 0; a < dimensions[0]!; a++) for (let b = 0; b < dimensions[1]!; b++) {
      tick(); env[ax.forall[0].name] = a; env[ax.forall[1].name] = b
      let chosen: number | undefined
      for (let w = 0; w < size(ax.exists.sort); w++) {
        tick(); env[ax.exists.name] = w
        if (ax.body.every((atom: RigidAtom) => lookup(tables[atom.relation]!, atom.args.map(term)) === 1)) { chosen = w; break }
      }
      if (chosen === undefined) fail(`axiom ${ax.name} has no witness at (${a}, ${b})`)
      values.push(chosen) // ascending search: deterministic smallest witness
    }
    let symbol = `${ax.name}$choice`, suffix = 2
    while (taken.has(symbol)) symbol = `${ax.name}$choice${suffix++}`
    taken.add(symbol)
    witnesses.push(Object.freeze({name: symbol, axiom: ax.name, args: Object.freeze(ax.forall.map((b: RigidBinder) => b.sort)), result: ax.exists.sort, table: Object.freeze({dimensions, values: Object.freeze(values)})}))
  }
  checkpoint()
  return new RigidInstance(validationToken, JSON.stringify(sig), Object.freeze(params), Object.freeze(tables), Object.freeze(witnesses))
}

/** Read-only result, not yet a Machine/Rule or a theorem certificate. */
export type ValidatedRigidInstance = RigidInstance
export function assertValidatedRigidInstance(value: unknown): asserts value is ValidatedRigidInstance {
  if (!value || typeof value !== 'object' || !validatedInstances.has(value)) fail('expected an instance returned by validation')
}
class RigidInstance {
  readonly #tables: Readonly<Record<string, Table>>
  constructor(token: typeof validationToken, readonly schemaText: string, readonly params: Readonly<Record<string, number>>, tables: Readonly<Record<string, Table>>, readonly witnesses: readonly RigidWitness[]) {
    if (token !== validationToken) fail('instances must pass validation')
    this.#tables = tables; validatedInstances.add(this); Object.freeze(this)
  }
  read(symbol: string, args: readonly number[]): number {
    if (!own(this.#tables, symbol)) fail(`unknown rigid symbol ${symbol}`)
    return lookup(this.#tables[symbol]!, args)
  }
  witness(axiom: string, args: readonly number[]): number {
    const w = this.witnesses.find(x => x.axiom === axiom)
    if (!w) fail(`unknown axiom ${axiom}`)
    return lookup(w!.table, args)
  }
}
Object.freeze(RigidInstance.prototype)
