// The extractor's check (core/extract.ts): the rule an extraction prints is run beside the code it was read from, and
// any difference refuses the extraction. The code runs as it ships, compiled by TypeScript and loaded into a VM of its
// own (no require but the modules named, Date.now() the request's time, Math.random refused), with a counter at each
// branch arm (an if's two arms, a ternary's, each case and the switch's fall-through, the right side of && || ??), so
// the evidence says which of the code's branches the requests reached. The rule runs through its reference evaluator
// (`rule.interpreter()`) and the generated JavaScript (`rule.compiled()`), and the two are compared too. Requests:
// - runs from the start: the params, then requests drawn at random, near the boundaries (0, ±1, the code's constants,
//   the state's own values ±1, the params ±1, the edges of the safe integers) and with the time moving on or back;
// - single steps from states drawn at random (every value of each field's type, maps with a few keys): a rule's proof
//   is about every state, not only those reached;
// - single steps from the prover's own counterexamples: for each branch condition the rule reads, proveSteps is asked
//   to refute "the condition never holds", and the state and request it refutes it with are run on both sides.
// After each request, every state variable, every map cell, the method's result and whether the request was refused
// are compared. A value outside the safe integers in the code, where the rule's runtime refuses the step (it never
// rounds), is counted apart: the rule's claim stops at 2^53.
import ts from 'typescript'
// node:vm, through process.getBuiltinModule (Node 20.16 and later, Bun): the package's declarations stay free of Node's.
type Context = Record<string, unknown>
type VM = {createContext: (o: Context) => Context, runInContext: (code: string, ctx: Context, opts?: {timeout?: number, filename?: string}) => unknown, Script: new (code: string) => {runInContext: (ctx: Context, opts?: {timeout?: number}) => unknown}}
const proc = (globalThis as {process?: {getBuiltinModule?: (id: string) => unknown}}).process
const vmOf = (): VM => { const m = proc?.getBuiltinModule?.('node:vm'); if (!m) throw new Error('the check runs the code in node:vm (Node 20.16 or later, or Bun)'); return m as VM }
import {Int, Term, bool, int, intern, interned, nat, no, oneOf, str, type Kind, type Rule, type StepLaw, proveSteps} from './dsl.ts'
import {type Request, type State} from './machine.ts'
import {allowed} from './watch.ts'
import {type Arg, type Layout, type MapDecl, type Model, type Var, normalize, resolveIn, scriptKind} from './extract-read.ts'
import * as I from './extract-ir.ts'
import type {B, N} from './extract-ir.ts'
import type {Sorts} from './extract-print.ts'

type Raw = number | boolean | string
export type Arm = {label: string, where: string, pos: number}
export type Coverage = {arms: number, hit: number, missed: string[]}
export type Evidence = {
  runs: number, requests: number, fromStates: number, probes: {conditions: number, witnesses: number, steps: number},
  refusedBoth: number, outside: number, edge: number, edgeSample?: string, compiledAgreed: number, coverage: Coverage, ms: number, mismatch?: string,
}

// --- the code, instrumented and loaded ------------------------------------------------------------------------------
export function instrument(code: string, file: string, tail = '', extra: [number, string][] = []): {js: string, arms: Arm[]} {
  const sf = ts.createSourceFile(file, code, ts.ScriptTarget.ES2022, true, scriptKind(file))
  const arms: Arm[] = [], edits: [number, string][] = []
  const loc = (n: ts.Node) => { const {line, character} = sf.getLineAndCharacterOfPosition(n.getStart()); return `${file.split('/').pop()}:${line + 1}:${character + 1}` }
  const arm = (label: string, n: ts.Node) => { arms.push({label, where: loc(n), pos: n.getStart()}); return arms.length - 1 }
  const visit = (n: ts.Node) => {
    if (ts.isIfStatement(n)) {
      const t = arm('if: then', n)
      edits.push([n.thenStatement.getStart(), `{__cov(${t});`], [n.thenStatement.end, '}'])
      const e = arm('if: else', n)
      if (n.elseStatement) edits.push([n.elseStatement.getStart(), `{__cov(${e});`], [n.elseStatement.end, '}'])
      else edits.push([n.thenStatement.end, ` else {__cov(${e});}`])
    } else if (ts.isConditionalExpression(n)) {
      const t = arm('?: true', n), f = arm('?: false', n)
      edits.push([n.whenTrue.getStart(), `(__cov(${t}), `], [n.whenTrue.end, ')'], [n.whenFalse.getStart(), `(__cov(${f}), `], [n.whenFalse.end, ')'])
    } else if (ts.isSwitchStatement(n)) {
      for (const cl of n.caseBlock.clauses) {
        const i = arm(ts.isCaseClause(cl) ? `case ${cl.expression.getText()}` : 'default', cl)
        edits.push([cl.statements.pos, ` __cov(${i});`])
      }
      if (!n.caseBlock.clauses.some(ts.isDefaultClause)) { const i = arm('switch: no case', n); edits.push([n.caseBlock.getStart() + 1, ` default: __cov(${i}); break;`]) }
    } else if (ts.isBinaryExpression(n) && [ts.SyntaxKind.AmpersandAmpersandToken, ts.SyntaxKind.BarBarToken, ts.SyntaxKind.QuestionQuestionToken].includes(n.operatorToken.kind)) {
      const i = arm(`${n.operatorToken.getText()}: right side`, n)
      edits.push([n.right.getStart(), `(__cov(${i}), `], [n.right.end, ')'])
    }
    ts.forEachChild(n, visit)
  }
  visit(sf)
  edits.push(...extra)
  // Later positions first; at one position, in the order made reversed (a closing paren before the next opening one).
  const order = edits.map((e, i) => [...e, i] as const).sort((a, b) => b[0] - a[0] || b[2] - a[2])
  let out = code
  for (const [pos, txt] of order) out = out.slice(0, pos) + txt + out.slice(pos)
  out += tail
  const js = ts.transpileModule(out, {compilerOptions: {module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2022, esModuleInterop: true, jsx: ts.JsxEmit.React}, fileName: file.replace(/\.js$/, '.ts').replace(/\.jsx$/, '.tsx')}).outputText
  return {js, arms}
}
export type Sandbox = {ctx: Context, counts: number[], call: (f: string, self: unknown, args: unknown[]) => {ok: true, value: unknown} | {ok: false, error: string}, setNow: (n: number) => void, get: (name: string) => unknown}
export function sandbox(code: string, file: string, expose: string[], modules: Record<string, unknown> = {}, init?: string, files: Record<string, string> = {}, extra: [number, string][] = []): Sandbox & {arms: Arm[]} {
  const vm = vmOf()
  const {js, arms} = instrument(code, file, init ? `\n;(globalThis as any).__gdpInit = () => (${init});\n` : '', extra)
  const counts = arms.map(() => 0)
  let now = 0
  const stub = (name: string) => new Proxy({}, {
    get: (_, k) => { if (k === '__esModule' || typeof k === 'symbol') return undefined; throw new Error(`the check loads no module ${name} (its ${String(k)} was read)`) },
    ownKeys: () => [],
  })
  const module = {exports: {} as Record<string, unknown>}
  const ctx = vm.createContext({
    __cov: (i: number) => { counts[i]!++ }, __now: () => now, module, exports: module.exports,
    // A relative import among the files given: loaded in this VM (not counted: the branches are the entry's). A module
    // the step doesn't name (React, for the component beside a reducer): a stub that throws when read, so a step that
    // reads it fails the check rather than running without it.
    require: (name: string) => (name in modules ? modules[name] : name.startsWith('.') && Object.keys(files).length ? load(ENTRY, name) : stub(name)),
    console: {log() {}, warn() {}, error() {}, info() {}, debug() {}},
  })
  // The files given, by their place beside the entry's; each loaded once.
  const ENTRY = `/v/${file.split('/').pop()}`, abs = Object.fromEntries(Object.entries(files).map(([p, c]) => [normalize(`/v/${p}`), c])), loaded = new Map<string, unknown>()
  const load = (from: string, spec: string): unknown => {
    const at = resolveIn(abs, from, spec)
    if (!at) throw new Error(`the check has no file for ${spec}`)
    if (loaded.has(at)) return loaded.get(at)
    const m = {exports: {} as Record<string, unknown>}
    loaded.set(at, m.exports)
    const js = ts.transpileModule(abs[at]!, {compilerOptions: {module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2022, esModuleInterop: true, jsx: ts.JsxEmit.React}, fileName: at.replace(/\.js$/, '.ts').replace(/\.jsx$/, '.tsx')}).outputText
    // A file that doesn't load here (it reads import.meta, a browser's globals): a stub that throws when read, so a step
    // that reads it fails the check rather than running without it.
    try {
      const f = vm.runInContext(`(function (module, exports, require) {${js}\n})`, ctx) as (m: unknown, e: unknown, r: unknown) => void
      f(m, m.exports, (s2: string) => (s2 in modules ? modules[s2] : s2.startsWith('.') ? load(at, s2) : stub(s2)))
    } catch (e) { const st = stub(`${spec} (${(e as Error).message})`); loaded.set(at, st); return st }
    loaded.set(at, m.exports)
    return m.exports
  }
  // The clock is the request's: Date.now() and new Date() read it.
  vm.runInContext('globalThis.Date = new Proxy(Date, {construct: (D, a) => (a.length ? new D(...a) : new D(__now())), get: (D, k) => (k === "now" ? () => __now() : D[k])}); Math.random = () => { throw new Error("Math.random in a step") }', ctx)
  vm.runInContext(`${js}\n;globalThis.__gdp = {${expose.map(n => { if (n === 'default') return 'default: module.exports.default'; const [h, ...rest] = n.split('.'); return `${JSON.stringify(n)}: (typeof ${h} !== 'undefined' ? ${h} : module.exports.${h})${rest.map(x => `.${x}`).join('')}` }).join(', ')}};`, ctx, {timeout: 2000, filename: file})
  const script = new vm.Script('globalThis.__r = (() => { try { return {ok: true, value: __gdp[__f].apply(__self, __args)} } catch (e) { return {ok: false, error: String(e && e.message || e)} } })()')
  const call = (f: string, self: unknown, args: unknown[]) => {
    Object.assign(ctx, {__f: f, __self: self, __args: args})
    script.runInContext(ctx, {timeout: 1000})
    return ctx.__r as {ok: true, value: unknown} | {ok: false, error: string}
  }
  return {ctx, counts, arms, call, setNow: n => { now = n }, get: name => vm.runInContext(`__gdp[${JSON.stringify(name)}]`, ctx)}
}

// --- snapshots: a state as its leaves and its maps' present keys ----------------------------------------------------
type Cells = Record<string, Record<string, Raw>>
export type Snap = {leaves: Record<string, Raw>, maps: Record<string, Cells>, lists?: Record<string, Raw[]>}
const isMap = (x: unknown): x is Map<unknown, unknown> => Object.prototype.toString.call(x) === '[object Map]'
class Outside extends Error {}
class Refused extends Error {}
// The code's value as a snapshot, by the layout; what the rule has no place for is a difference.
function snapOf(v: unknown, layout: Layout, m: Model, consts: (t: N | B | I.L) => Raw, out: Snap = {leaves: {}, maps: {}}, path = 'state'): Snap {
  switch (layout.k) {
    case 'scalar': {
      const sort = m.state.find(x => x.name === layout.name)?.sort
      // A Date: its time.
      if (sort?.k === 'num' && sort.date) { if (!isDateValue(v)) throw new Error(`${path} is ${JSON.stringify(v)}, not a Date`); v = (v as Date).getTime(); if (Number.isNaN(v)) throw new Outside(`${path} is an invalid Date (past ±8.64e15 ms)`) }
      if (sort?.k === 'num' && !(typeof v === 'number' && Number.isSafeInteger(v))) {
        if (typeof v === 'number') throw new Outside(`${path} is ${v}`)
        throw new Error(`${path} is ${JSON.stringify(v)}, not a number`)
      }
      if (sort?.k === 'bool' && typeof v !== 'boolean') throw new Error(`${path} is ${JSON.stringify(v)}, not a boolean`)
      if (sort?.k === 'choice' && !(typeof v === 'string' && sort.values.includes(v))) throw new Error(`${path} is ${JSON.stringify(v)}, not one of its literals`)
      if (sort?.k === 'str' && typeof v !== 'string') throw new Error(`${path} is ${JSON.stringify(v)}, not a string`)
      out.leaves[layout.name] = v as Raw
      return out
    }
    case 'rec': {
      if (typeof v !== 'object' || v === null) throw new Error(`${path} is ${JSON.stringify(v)}, not an object`)
      const own = Object.keys(v), want = layout.fields.map(([f]) => f).filter(f => !f.endsWith('()'))
      for (const k of own) if (!want.includes(k)) throw new Error(`${path} has a field ${k} the rule doesn't`)
      for (const [f, sub] of layout.fields) if (!f.endsWith('()')) snapOf((v as Record<string, unknown>)[f], sub, m, consts, out, `${path}.${f}`)
      return out
    }
    case 'map': {
      const d = m.maps.find(x => x.name === layout.name)!, cells: Cells = {}
      const entries: [unknown, unknown][] = isMap(v) ? [...v.entries()] : typeof v === 'object' && v !== null ? Object.entries(v) : (() => { throw new Error(`${path} is not a map`) })()
      for (const [k, x] of entries) {
        if (d.key === 'num' && !(typeof k === 'number' || (typeof k === 'string' && /^\d+$/.test(k)))) throw new Error(`${path} has a key ${String(k)} that isn't a natural`)
        if (d.key === 'str' && typeof k !== 'string') throw new Error(`${path} has a key ${String(k)} that isn't a string`)
        const cell: Record<string, Raw> = {}
        if (d.scalar) cell.value = checkCell(x, d.fields[0]!, `${path}[${String(k)}]`)
        else {
          if (typeof x !== 'object' || x === null) throw new Error(`${path}[${String(k)}] is ${JSON.stringify(x)}, not an object`)
          for (const kk of Object.keys(x)) if (!d.fields.some(f => f.name === kk)) throw new Error(`${path}[${String(k)}] has a field ${kk} the rule doesn't`)
          for (const f of d.fields) cell[f.name] = checkCell((x as Record<string, unknown>)[f.name], f, `${path}[${String(k)}].${f.name}`)
        }
        cells[String(k)] = cell
      }
      out.maps[d.name] = cells
      return out
    }
    case 'list': {
      const d = m.lists!.find(x => x.name === layout.name)!
      if (!Array.isArray(v)) throw new Error(`${path} is ${JSON.stringify(v)}, not an array`)
      // Every index an item (an array with holes, or more than its own indices, is not a list).
      if (Object.keys(v).length !== v.length) throw new Error(`${path} has holes or fields beside its items`)
      ;(out.lists ??= {})[d.name] = v.map((x, i) => checkCell(x, d.fields[0]!, `${path}[${i}]`))
      return out
    }
    case 'const': {
      const want = layout.value.s === 'str' ? (layout.value.e.op === 'slit' ? layout.value.e.value : undefined) : consts(layout.value.e)
      if (v !== want) throw new Error(`${path} is ${JSON.stringify(v)}, the constant ${JSON.stringify(want)} the rule takes it for`)
      return out
    }
  }
}
const isDateValue = (x: unknown): boolean => Object.prototype.toString.call(x) === '[object Date]'
function checkCell(x: unknown, f: Var, path: string): Raw {
  if (f.sort.k === 'num' && f.sort.date) { if (!isDateValue(x)) throw new Error(`${path} is ${JSON.stringify(x)}, not a Date`); x = (x as Date).getTime(); if (Number.isNaN(x)) throw new Outside(`${path} is an invalid Date (past ±8.64e15 ms)`) }
  if (f.sort.k === 'num') { if (typeof x === 'number' && Number.isSafeInteger(x)) return x; if (typeof x === 'number') throw new Outside(`${path} is ${x}`); throw new Error(`${path} is ${JSON.stringify(x)}, not a number`) }
  if (f.sort.k === 'bool') { if (typeof x === 'boolean') return x; throw new Error(`${path} is ${JSON.stringify(x)}, not a boolean`) }
  if (f.sort.k === 'choice') { if (typeof x === 'string' && f.sort.values.includes(x)) return x; throw new Error(`${path} is ${JSON.stringify(x)}`) }
  throw new Error(`${path}: a string cell`)
}
// A snapshot as the code's own value, built inside the sandbox's realm (its Maps are the code's Maps).
function valueOf(s: Snap, layout: Layout, m: Model, consts: (t: N | B | I.L) => Raw, ctx: Context): unknown {
  const tree = (l: Layout): unknown => {
    switch (l.k) {
      case 'scalar': { const sort = m.state.find(x => x.name === l.name)?.sort; return sort?.k === 'num' && sort.date ? {$date: s.leaves[l.name]} : s.leaves[l.name] }
      case 'rec': return Object.fromEntries(l.fields.filter(([f]) => !f.endsWith('()')).map(([f, sub]) => [f, tree(sub)]))
      case 'map': {
        const d = m.maps.find(x => x.name === l.name)!
        const dated = (f: Var, x: Raw) => (f.sort.k === 'num' && f.sort.date ? {$date: x} : x)
        const entries = Object.entries(s.maps[d.name] ?? {}).map(([k, c]) => [d.key === 'num' ? Number(k) : k, d.scalar ? dated(d.fields[0]!, c.value!) : Object.fromEntries(d.fields.map(f => [f.name, dated(f, c[f.name]!)]))])
        return {$map: d.js, entries}
      }
      case 'list': return s.lists?.[l.name] ?? []
      case 'const': return l.value.s === 'str' ? (l.value.e.op === 'slit' ? l.value.e.value : undefined) : consts(l.value.e)
    }
  }
  ctx.__in = JSON.stringify(tree(layout))
  return vmOf().runInContext('JSON.parse(__in, (k, v) => v && typeof v === "object" && v.$map ? (v.$map === "Map" ? new Map(v.entries) : Object.fromEntries(v.entries)) : v && typeof v === "object" && "$date" in v ? new Date(v.$date) : v)', ctx)
}
const showSnap = (s: Snap) => JSON.stringify({...s.leaves, ...Object.fromEntries(Object.entries(s.maps).map(([k, v]) => [k, v])), ...(s.lists ?? {})})
const sameSnap = (a: Snap, b: Snap): string | undefined => {
  for (const k of new Set([...Object.keys(a.leaves), ...Object.keys(b.leaves)])) if (a.leaves[k] !== b.leaves[k]) return `${k} is ${JSON.stringify(a.leaves[k])} in the code, ${JSON.stringify(b.leaves[k])} in the rule`
  for (const k of new Set([...Object.keys(a.maps), ...Object.keys(b.maps)])) {
    const x = a.maps[k] ?? {}, y = b.maps[k] ?? {}
    for (const key of new Set([...Object.keys(x), ...Object.keys(y)])) if (JSON.stringify(x[key]) !== JSON.stringify(y[key])) return `${k}[${key}] is ${JSON.stringify(x[key])} in the code, ${JSON.stringify(y[key])} in the rule`
  }
  for (const k of new Set([...Object.keys(a.lists ?? {}), ...Object.keys(b.lists ?? {})])) if (JSON.stringify(a.lists?.[k] ?? []) !== JSON.stringify(b.lists?.[k] ?? [])) return `${k} is ${JSON.stringify(a.lists?.[k] ?? [])} in the code, ${JSON.stringify(b.lists?.[k] ?? [])} in the rule`
  return undefined
}

// --- the rule's side ------------------------------------------------------------------------------------------------
export const kindOfVar = (v: Var, sorts: Sorts, at = v.name): Kind<unknown> => (v.sort.k === 'num' ? (sorts.get(at) === 'nat' ? nat : int) : v.sort.k === 'bool' ? bool : v.sort.k === 'choice' ? oneOf(...v.sort.values) : str()) as Kind<unknown>
const idText = (id: number): string | undefined => interned().find(([, n]) => n === id)?.[0]
function ruleSnap(r: Rule, m: Model, st: State, sorts: Sorts): Snap {
  const d = r.decode(st), leaves: Record<string, Raw> = {}, maps: Record<string, Cells> = {}
  for (const v of m.state) if (!m.outputs.includes(v.name)) leaves[v.name] = d[v.name] as Raw
  for (const md of m.maps) {
    const cells: Cells = {}
    for (const [k, c] of Object.entries((d[md.name] ?? {}) as Record<string, Record<string, Raw>>)) {
      if (!c.has) continue
      const key = md.key === 'str' ? idText(Number(k)) ?? `#${k}` : k
      cells[key] = Object.fromEntries(md.fields.map(f => [f.name, c[f.name]!]))
    }
    maps[md.name] = cells
  }
  const lists: Record<string, Raw[]> = {}
  for (const ld of m.lists ?? []) lists[ld.name] = (d[ld.name] ?? []) as Raw[]
  void sorts
  return {leaves, maps, ...(m.lists?.length ? {lists} : {})}
}
// A snapshot as a state of the rule (each variable and cell by its kind).
function ruleState(base: State, s: Snap, m: Model, sorts: Sorts): State {
  const scalars = {...base.scalars}, maps: Record<string, Map<number, number>> = Object.fromEntries(Object.entries(base.maps).map(([k]) => [k, new Map()]))
  for (const v of m.state) if (v.name in s.leaves) Object.assign(scalars, kindOfVar(v, sorts).encode(v.name, s.leaves[v.name]!))
  for (const d of m.maps) {
    const kind = cellKind(d, sorts)
    for (const [k, c] of Object.entries(s.maps[d.name] ?? {})) {
      const key = d.key === 'str' ? intern(k) : Number(k)
      for (const [part, x] of Object.entries(kind.encode(d.name, {has: true, ...c}))) if (x !== 0) (maps[part] ??= new Map()).set(key, x)
    }
  }
  // A list: its items at their indices, its length.
  for (const d of m.lists ?? []) {
    const kind = kindOfVar(d.fields[0]!, sorts, `${d.name}.$item`), xs = s.lists?.[d.name] ?? []
    scalars[`${d.name}_len`] = xs.length
    xs.forEach((x, i) => { for (const [part, y] of Object.entries(kind.encode(d.name, x))) if (y !== 0) (maps[part] ??= new Map()).set(i, y) })
  }
  return {...base, scalars, maps}
}
import {record} from './dsl.ts'
const cellKind = (d: MapDecl, sorts: Sorts) => record({has: bool, ...Object.fromEntries(d.fields.map(f => [f.name, kindOfVar(f, sorts, `${d.name}.${f.name}`)]))}) as Kind<unknown>

// --- values to draw -------------------------------------------------------------------------------------------------
type Rand = (n: number) => number
const seeded = (seed: number): Rand => { let x = seed >>> 0 || 1; return n => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * n) } }
const BIG = [Number.MAX_SAFE_INTEGER, Number.MAX_SAFE_INTEGER - 1, 2 ** 31, 2 ** 32]
function constantsOf(m: Model): number[] {
  const out = new Set<number>([0, 1])
  const go = (x: unknown): void => { if (x && typeof x === 'object') { const o = x as {op?: string, v?: unknown, k?: unknown}; if (o.op === 'const' && typeof o.v === 'number') out.add(o.v); if (typeof o.k === 'number') out.add(o.k); Object.values(o).forEach(go) } }
  go([m.writes, m.mapWrites, m.refuse, m.pre, m.init])
  return [...out]
}
function draw(sort: Var['sort'], sorts: Sorts, name: string, rand: Rand, near: number[], bound: number, strs: string[]): Raw {
  switch (sort.k) {
    case 'bool': return rand(2) === 1
    case 'choice': return sort.values[rand(sort.values.length)]!
    case 'str': return strs[rand(strs.length)]!
    case 'num': {
      const natural = sorts.get(name) === 'nat', pick = rand(10)
      let x: number
      if (pick < 4) x = rand(bound + 1) * (natural || rand(2) ? 1 : -1)
      else if (pick < 8 && near.length) { const b = near[rand(near.length)]!; x = b + rand(3) - 1 }
      else if (pick < 9) x = BIG[rand(BIG.length)]! * (natural || rand(2) ? 1 : -1)
      else x = -1 - rand(bound)
      // The code's domain is every safe integer: a natural input is drawn below 0 too (the code must refuse it).
      return x
    }
  }
}

// --- the check ------------------------------------------------------------------------------------------------------
export type CheckOptions = {runs?: number, depth?: number, states?: number, seed?: number, bound?: number, probes?: boolean, probeMs?: number, modules?: Record<string, unknown>, files?: Record<string, string>}
export function check(code: string, file: string, m: Model, r: Rule, sorts: Sorts, opts: CheckOptions & {given?: Record<string, 'nat' | 'int'>} = {}): Evidence {
  const t0 = performance.now(), rand = seeded(opts.seed ?? 7), bound = opts.bound ?? 12
  const isClass = m.shape === 'class', fns = m.shape === 'class' ? [m.entry] : [...new Set(m.events.map(e => e.call))]
  const box = sandbox(code, file, fns, opts.modules, m.initSource, opts.files, m.factory ? [[m.factory.at, m.factory.text]] : [])
  // An object a factory makes: its state is what its functions close over, read and set through the two functions the
  // check added to it.
  const stateOf = (self: unknown): unknown => (m.factory ? (box.call('$get', self, []) as {ok: boolean, value?: unknown}).value : self)
  const interp = r.interpreter(), gen = r.compiled(), machine = r.machine
  const ev: Evidence = {runs: 0, requests: 0, fromStates: 0, probes: {conditions: 0, witnesses: 0, steps: 0}, refusedBoth: 0, outside: 0, edge: 0, compiledAgreed: 0, coverage: {arms: box.arms.length, hit: 0, missed: []}, ms: 0}
  const consts = constantsOf(m), strs = ['a', 'b', 'c', '']
  const paramKinds = m.params.map(v => [v, kindOfVar(v, sorts)] as const), inputKinds = m.inputs.map(v => [v, kindOfVar(v, sorts)] as const)
  // A term over the params at their values (a constant field, a start).
  const evalAt = (env: Record<string, Raw>) => (t: N | B | I.L): Raw => evalTerm(t, env)
  const fail = (what: string): Evidence => { ev.mismatch = what; return finish() }
  // The arms of the code the step reads (the entry, its methods, the functions it inlines; a class's constructor too).
  const inSpan = (a: Arm) => !m.spans || m.spans.some(([s0, e0]) => a.pos >= s0 && a.pos < e0)
  const counted = box.arms.map((a, i) => [a, i] as const).filter(([a]) => inSpan(a))
  ev.coverage.arms = counted.length
  const finish = (): Evidence => {
    ev.coverage.hit = counted.filter(([, i]) => box.counts[i]! > 0).length
    ev.coverage.missed = counted.filter(([, i]) => box.counts[i] === 0).map(([a]) => `${a.label} at ${a.where}`)
    ev.ms = Math.round(performance.now() - t0)
    return ev
  }
  // One request, both sides, from a state given as a snapshot (and, for a class, the object).
  type Side = {snap: Snap, self?: object}
  const request = (params: Record<string, Raw>, inputs: Record<string, Raw>, e: (typeof m.events)[number]) => {
    const dateIn = (n: string) => { const x = m.inputs.find(v => v.name === n); return x?.sort.k === 'num' && x.sort.date ? vmOf().runInContext(`new Date(${Number(inputs[n])})`, box.ctx) : inputs[n] }
    const build = (a: Arg): unknown => (a.k === 'input' ? dateIn(a.name) : a.k === 'lit' ? a.value : a.k === 'rec' ? Object.fromEntries(a.fields.map(([f, x]) => [f, build(x)])) : a.k === 'lazy'
      ? Object.fromEntries([...m.inputs].filter(v => m.lazy?.get(v.name)?.prefix === a.prefix).map(v => [m.lazy!.get(v.name)!.field, inputs[v.name]]))
      : undefined)
    void params
    return e.args.map(build)
  }
  const draws = (st: Snap, params: Record<string, Raw>): number[] => [...consts, ...Object.values(st.leaves).filter((x): x is number => typeof x === 'number'), ...Object.values(params).filter((x): x is number => typeof x === 'number')]
  let lastNow = 1_000
  const drawRequest = (st: Snap, params: Record<string, Raw>) => {
    const e = m.events[rand(m.events.length)]!, near = draws(st, params), inputs: Record<string, Raw> = {}
    for (const v of m.inputs) {
      if (v.name in e.select) { inputs[v.name] = e.select[v.name]!; continue }
      if (v.note?.startsWith('Date.now()')) { const d = rand(6); lastNow = d === 0 ? Math.max(0, lastNow - rand(50)) : d === 1 ? rand(10_000) : lastNow + rand(d * 40); inputs[v.name] = lastNow; continue }
      const keys = Object.values(st.maps).flatMap(c => Object.keys(c))
      // An input given as a natural (domains) is drawn as one: the claim is for those, as the user said.
      const x = draw(v.sort, sorts, v.name, rand, near, bound, [...strs, ...keys])
      inputs[v.name] = opts.given?.[v.name] === 'nat' && typeof x === 'number' ? Math.abs(x) : x
    }
    return {e, inputs}
  }
  const ruleInputs = (inputs: Record<string, Raw>, e: (typeof m.events)[number]): Record<string, Raw> => {
    const used = new Set<string>()
    const walk = (a: Arg) => { if (a.k === 'input') used.add(a.name); else if (a.k === 'rec') a.fields.forEach(([, x]) => walk(x)); else if (a.k === 'lazy') for (const v of m.inputs) if (m.lazy?.get(v.name)?.prefix === a.prefix) used.add(v.name) }
    e.args.forEach(walk)
    for (const v of m.inputs) if (v.note?.startsWith('Date.now()')) used.add(v.name)
    // An input the event doesn't bring: its kind's first value (the rule reads it only under another event).
    return Object.fromEntries(m.inputs.map(v => [v.name, v.name in e.select ? e.select[v.name]! : used.has(v.name) ? inputs[v.name]! : v.sort.k === 'num' ? 0 : v.sort.k === 'bool' ? false : v.sort.k === 'choice' ? v.sort.values[0]! : '']))
  }
  // Steps the code and the rule from one state; undefined when they agree (the next state on both sides is returned
  // through `next`), else the difference.
  const step = (params: Record<string, Raw>, ps: Record<string, number>, side: Side, st: State, inputs: Record<string, Raw>, e: (typeof m.events)[number], next: {side?: Side, st?: State, stop?: boolean}, where: string): string | undefined => {
    const args = request(params, inputs, e), raw = ruleInputs(inputs, e)
    const nowVar = m.inputs.find(v => v.note?.startsWith('Date.now()'))
    if (nowVar) box.setNow(inputs[nowVar.name] as number)
    // The code.
    let code: {refused: string} | {snap: Snap, out?: Raw, self?: object} | {outside: string}
    try {
      if (isClass) {
        const self = side.self!, res = box.call('$method', self, [e.call, args])
        if (!res.ok) code = {refused: res.error}
        else code = {snap: snapOf(stateOf(self), m.layout, m, evalAt(params)), out: res.value as Raw, self}
      } else {
        const input = valueOf(side.snap, m.layout, m, evalAt(params), box.ctx), before = JSON.stringify(input, mapReplacer)
        const res = box.call(e.call, undefined, [input, ...args.slice(1)])
        if (JSON.stringify(input, mapReplacer) !== before) return `${where}: ${e.call} changed the state it was given`
        code = res.ok ? {snap: snapOf(res.value, m.layout, m, evalAt(params))} : {refused: res.error}
      }
    } catch (x) {
      if (x instanceof Outside) code = {outside: x.message}
      else return `${where}: the code's state after the request: ${(x as Error).message}`
    }
    // The rule.
    let rule: {refused: string} | {st: State} | {outside: string} = {refused: 'not run'}
    let enc: Request | undefined
    try { enc = r.encodeInput(raw as never, params as never) } catch (x) { rule = {refused: `outside the input's kind (${(x as Error).message})`} }
    if (enc) {
      try {
        if (!allowed(machine, interp, ps, st, enc)) throw new Refused('the assumption')
        const s1 = interp.step(ps, st, enc)
        rule = {st: s1}
        const s2 = gen.step(ps, gen.fork(st), enc)
        if (JSON.stringify(r.decode(s2)) !== JSON.stringify(r.decode(s1))) return `${where}: the rule's interpreter and its generated JavaScript differ (${JSON.stringify(r.decode(s1))} against ${JSON.stringify(r.decode(s2))})`
        ev.compiledAgreed++
      } catch (x) { rule = x instanceof Refused ? {refused: x.message} : /2\^53|safe integer/.test((x as Error).message) ? {outside: (x as Error).message} : {refused: (x as Error).message} }
    }
    const req = `${e.call}(${JSON.stringify(args).slice(1, -1)})${nowVar ? ` at ${inputs[nowVar.name]}` : ''}`
    const from = `from ${showSnap(side.snap)}${m.params.length ? ` with ${JSON.stringify(params)}` : ''}`
    if ('outside' in code || 'outside' in rule!) {
      // The code past the safe integers: the rule's runtime must refuse there too (it never rounds).
      next.stop = true
      if ('outside' in code) { if ('st' in rule!) return `${where}: ${req} ${from}: the code leaves the safe integers (${code.outside}) where the rule takes the step`; ev.outside++; return undefined }
      if ('refused' in code) { ev.refusedBoth++; return undefined }
      // The rule's runtime refuses a sum or a comparison past 2^53 where the code's values are still safe: the edge
      // its claim stops at, counted apart (a sample kept), not a difference in what the step computes.
      ev.edge++
      ev.edgeSample ??= `${req} ${from}`
      return undefined
    }
    if ('refused' in code && 'refused' in rule!) {
      // A refusal leaves the state as it was: the object the code threw from must be as it was too.
      if (isClass) { try { const after = snapOf(stateOf(side.self), m.layout, m, evalAt(params)), d = sameSnap(after, side.snap); if (d) return `${where}: ${req} ${from}: the code throws (${code.refused}) after changing the object: ${d}` } catch (x) { return `${where}: ${req} ${from}: the code throws after changing the object (${(x as Error).message})` } }
      ev.refusedBoth++
      return undefined
    }
    if ('refused' in code) return `${where}: ${req} ${from}: the code throws (${code.refused}), the rule takes the step`
    if ('refused' in rule!) return `${where}: ${req} ${from}: the rule refuses it (${rule.refused}), the code doesn't`
    const ruleSide = ruleSnap(r, m, (rule as {st: State}).st, sorts), diff = sameSnap(code.snap, ruleSide)
    if (diff) return `${where}: ${req} ${from}: ${diff}`
    if (isClass) {
      // The method's result, as the rule keeps it: a value, a record's fields, or a value and whether it is missing.
      const res = m.results?.[e.call], d = r.decode((rule as {st: State}).st)
      const bad = (what: string) => `${where}: ${req} ${from}: ${e.call} returns ${JSON.stringify(code.out)}, ${what}`
      if (res?.k === 'scalar' && d[res.name] !== code.out) return bad(`the rule's ${res.name} is ${JSON.stringify(d[res.name])}`)
      if (res?.k === 'rec') {
        const o = code.out as Record<string, unknown> | undefined
        if (typeof o !== 'object' || o === null || Object.keys(o).length !== res.fields.length) return bad('not a record of the fields the rule keeps')
        for (const [f, n] of res.fields) if (o[f] !== d[n]) return bad(`the rule's ${n} is ${JSON.stringify(d[n])}`)
      }
      if (res?.k === 'maybe') {
        const gone = code.out === (res.null ? null : undefined)
        if (gone !== d[res.missing]) return bad(`the rule's ${res.missing} is ${JSON.stringify(d[res.missing])}`)
        if (!gone && d[res.name] !== code.out) return bad(`the rule's ${res.name} is ${JSON.stringify(d[res.name])}`)
      }
    }
    next.side = {snap: code.snap, ...(code.self ? {self: code.self} : {})}
    next.st = (rule as {st: State}).st
    return undefined
  }
  // A class's object: made by its constructor, or set to a snapshot.
  const E = JSON.stringify(m.entry)
  if (isClass && !m.factory) vmOf().runInContext(`__gdp.$method = function (name, args) { return this[name](...args) }; __gdp.$new = function (...args) { return new __gdp[${E}](...args) }; __gdp.$at = function (fields) { return Object.assign(Object.create(__gdp[${E}].prototype), fields) }`, box.ctx)
  if (m.factory) vmOf().runInContext(`__gdp.$method = function (name, args) { return this[name](...args) }; __gdp.$new = function (...args) { return __gdp[${E}](...args) }; __gdp.$get = function () { return this.__gdpGet() }; __gdp.$at = function (fields, args) { const o = __gdp[${E}](...args); o.__gdpSet(fields); return o }`, box.ctx)
  const ctorValues = (params: Record<string, Raw>) => (m.ctorArgs ?? []).filter(n => !m.params.find(v => v.name === n)?.note?.startsWith('Date.now()')).map(n => (n.startsWith('$map:') ? vmOf().runInContext(n === '$map:Map' ? 'new Map()' : '({})', box.ctx) : params[n]))
  const objectAt = (snap: Snap, params: Record<string, Raw>): object => box.call('$at', undefined, [valueOf(snap, m.layout, m, evalAt(params), box.ctx), ctorValues(params)]).ok ? (box.ctx.__r as {value: object}).value : (() => { throw new Error(`could not make the object: ${(box.ctx.__r as {error?: string}).error}`) })()
  const drawParams = (): Record<string, Raw> => Object.fromEntries(m.params.map(v => [v.name, v.note?.startsWith('Date.now()') ? rand(10_000) : draw(v.sort, sorts, v.name, rand, consts, bound, strs)]))
  const start = (params: Record<string, Raw>): {side?: Side, st?: State, ps?: Record<string, number>, problem?: string} => {
    const ctorRefuses = (() => { const pre = evalTerm(m.pre, params); return pre !== true })()
    let ps: Record<string, number> | undefined
    try { ps = r.encodeParams(params as never) } catch { ps = undefined }
    if (isClass) {
      const now0 = m.params.find(v => v.note?.startsWith('Date.now()'))
      if (now0) box.setNow(params[now0.name] as number)
      // A Map the constructor is given: an empty one, made in the code's realm.
      const made = box.call('$new', undefined, (m.ctorArgs ?? []).filter(n => n !== now0?.name).map(n => (n.startsWith('$map:') ? vmOf().runInContext(n === '$map:Map' ? 'new Map()' : '({})', box.ctx) : params[n])))
      const ruleRefuses = ps === undefined || ctorRefuses
      if (!made.ok) return ruleRefuses ? {} : {problem: `new ${m.entry}(${JSON.stringify(params)}) throws (${made.error}), the rule's precondition holds`}
      if (ruleRefuses) return {problem: `new ${m.entry}(${JSON.stringify(params)}) is made, the rule's ${ps === undefined ? 'param kinds refuse' : 'precondition refuses'} it`}
      const st = interp.init(ps!)
      try { const snap = snapOf(stateOf(made.value), m.layout, m, evalAt(params)); const diff = sameSnap(snap, ruleSnap(r, m, st, sorts)); if (diff) return {problem: `new ${m.entry}(${JSON.stringify(params)}): ${diff}`}; return {side: {snap, self: made.value as object}, st, ps: ps!} }
      catch (x) { return {problem: `new ${m.entry}: ${(x as Error).message}`} }
    }
    const st = interp.init(ps ?? {}), snap = ruleSnap(r, m, st, sorts)
    // The code's own initial state (where the code gives it), against the rule's.
    if (m.initSource) {
      const made = vmOf().runInContext('(() => { try { return {ok: true, value: __gdpInit()} } catch (e) { return {ok: false, error: String(e)} } })()', box.ctx) as {ok: boolean, value?: unknown, error?: string}
      if (!made.ok) return {problem: `the initial state throws (${made.error})`}
      try { const diff = sameSnap(snapOf(made.value, m.layout, m, evalAt(params)), snap); if (diff) return {problem: `the initial state: ${diff}`} } catch (x) { return {problem: `the initial state: ${(x as Error).message}`} }
    }
    return {side: {snap}, st, ps: ps ?? {}}
  }
  const runs = opts.runs ?? 200, depth = opts.depth ?? 12
  for (let run = 0; run < runs; run++) {
    const params = drawParams(), s0 = start(params)
    if (s0.problem) return fail(`at the start: ${s0.problem}`)
    if (!s0.side) continue
    ev.runs++
    let side = s0.side, st = s0.st!
    for (let d = 0; d < depth; d++) {
      const {e, inputs} = drawRequest(side.snap, params), next: {side?: Side, st?: State, stop?: boolean} = {}
      const diff = step(params, s0.ps!, side, st, inputs, e, next, `run ${run + 1}, request ${d + 1}`)
      ev.requests++
      if (diff) return fail(diff)
      // Past the safe integers the two sides part by design: the run ends there.
      if (next.stop) break
      if (next.side) { side = next.side; st = next.st! }
    }
  }
  // Steps from drawn states.
  const drawSnap = (params: Record<string, Raw>): Snap => {
    const leaves: Record<string, Raw> = {}, maps: Record<string, Cells> = {}
    for (const v of m.state) if (!m.outputs.includes(v.name)) leaves[v.name] = draw(v.sort, sorts, v.name, rand, [...consts, ...Object.values(params).filter((x): x is number => typeof x === 'number')], bound, strs)
    for (const v of m.state) if (v.name in leaves && v.sort.k === 'num' && sorts.get(v.name) === 'nat' && (leaves[v.name] as number) < 0) leaves[v.name] = -(leaves[v.name] as number)
    for (const d of m.maps) {
      const cells: Cells = {}
      for (let i = rand(4); i > 0; i--) {
        const key = d.key === 'str' ? strs[rand(3)]! : String(rand(4))
        cells[key] = Object.fromEntries(d.fields.map(f => { let x = draw(f.sort, sorts, `${d.name}.${f.name}`, rand, consts, bound, strs); if (typeof x === 'number' && sorts.get(`${d.name}.${f.name}`) === 'nat') x = Math.abs(x); return [f.name, x] }))
      }
      maps[d.name] = cells
    }
    const lists: Record<string, Raw[]> = {}
    for (const d of m.lists ?? []) { const f = d.fields[0]!; lists[d.name] = Array.from({length: rand(4)}, () => { let x = draw(f.sort, sorts, `${d.name}.$item`, rand, consts, bound, strs); if (typeof x === 'number' && sorts.get(`${d.name}.$item`) === 'nat') x = Math.abs(x); return x }) }
    for (const v of m.state) if (v.name in leaves && v.sort.k === 'num' && Math.abs(leaves[v.name] as number) > Number.MAX_SAFE_INTEGER / 4) leaves[v.name] = rand(bound)
    // A Date's time within its range (a Date past it is invalid in the code: no state of the code holds one).
    for (const v of m.state) if (v.name in leaves && v.sort.k === 'num' && v.sort.date && Math.abs(leaves[v.name] as number) > 8.64e15) leaves[v.name] = rand(bound)
    for (const d of m.maps) for (const f of d.fields) if (f.sort.k === 'num' && f.sort.date) for (const c of Object.values(maps[d.name] ?? {})) if (Math.abs(c[f.name] as number) > 8.64e15) c[f.name] = rand(bound)
    return {leaves, maps, ...(m.lists?.length ? {lists} : {})}
  }
  const fromState = (params: Record<string, Raw>, snap: Snap, inputs: Record<string, Raw>, e: (typeof m.events)[number], where: string): string | undefined => {
    let ps: Record<string, number>
    try { ps = r.encodeParams(params as never) } catch { return undefined }
    if (evalTerm(m.pre, params) !== true) return undefined
    const st = ruleState(interp.init(ps), snap, m, sorts)
    const side: Side = {snap, ...(isClass ? {self: objectAt(snap, params)} : {})}
    return step(params, ps, side, st, inputs, e, {}, where)
  }
  for (let i = 0; i < (opts.states ?? 400); i++) {
    const params = drawParams(), snap = drawSnap(params), {e, inputs} = drawRequest(snap, params)
    const diff = fromState(params, snap, inputs, e, `drawn state ${i + 1}`)
    ev.fromStates++
    if (diff) return fail(diff)
  }
  // Steps from the prover's counterexamples: each condition of the step, refuted as "never holds".
  if (opts.probes !== false) {
    const conds = conditionsOf(m)
    for (const [i, c] of conds.entries()) {
      ev.probes.conditions++
      let law: StepLaw
      try { law = r.stepLaw(`probe ${i + 1}`, () => no, env => condAt(c, env as Record<string, unknown>)) } catch { continue }
      const v = proveSteps(r as never, [], [law], {search: false})
      if (v.proven || !v.witness) continue
      ev.probes.witnesses++
      const w = v.witness, params: Record<string, Raw> = {}, inputs: Record<string, Raw> = {}, leaves: Record<string, Raw> = {}
      let ok = true
      const dec = (vv: Var, k: Kind<unknown>, at: Record<string, Raw>) => { try { const x = k.decode(vv.name, Object.fromEntries(k.vars(vv.name).map(part => [part, w[part] ?? 0]))) as Raw; at[vv.name] = x } catch { ok = false } }
      for (const [vv, k] of paramKinds) dec(vv, k, params)
      for (const [vv, k] of inputKinds) dec(vv, k, inputs)
      for (const vv of m.state) dec(vv, kindOfVar(vv, sorts), leaves)
      if (!ok) continue
      const e = m.events.find(x => Object.entries(x.select).every(([n, val]) => inputs[n] === val)) ?? m.events[0]!
      const diff = fromState(params, {leaves, maps: Object.fromEntries(m.maps.map(d => [d.name, {}]))}, inputs, e, `the prover's witness for ${showCond(c)}`)
      ev.probes.steps++
      if (diff) return fail(diff)
    }
  }
  return finish()
}
const mapReplacer = (_: string, v: unknown) => (isMap(v) ? {$map: [...v.entries()]} : v)

// The conditions a step reads (each branch's, each refusal's), as a probe asks the prover to reach.
function conditionsOf(m: Model): B[] {
  const out: B[] = [], seen = new Set<string>()
  const add = (c: B) => { if (c.op === 'const') return; const k = I.keyOf(c); if (!seen.has(k) && !hasCell(c)) { seen.add(k); out.push(c, I.not(c)) } }
  const go = (x: unknown): void => {
    if (!x || typeof x !== 'object') return
    const o = x as {op?: string, c?: B}
    if ((o.op === 'ite' || o.op === 'kite') && o.c) add(o.c)
    Object.values(o).forEach(go)
  }
  go([m.writes, m.mapWrites])
  for (const d of m.refuse.op === 'or' ? m.refuse.xs : [m.refuse]) add(d)
  return out.slice(0, 48)
}
const hasCell = (c: B) => I.varsOf(c).maps.size > 0
const showCond = (c: B): string => JSON.stringify(c).replace(/"op":/g, '').slice(0, 120)
// A condition over the rule's env (the step law's `when`): the builders' own values, read from the env by name.
function condAt(c: B, env: Record<string, unknown>): ReturnType<Term['lt']> {
  const n = (e: N): Int => {
    switch (e.op) {
      case 'var': return Int.of(env[e.name] as Term | Int)
      case 'const': return Int.of(e.v)
      case 'add': return n(e.a).plus(n(e.b))
      case 'sub': return n(e.a).minus(n(e.b))
      case 'neg': return n(e.a).negate()
      case 'mulk': return n(e.a).times(e.k)
      case 'min': return n(e.a).min(n(e.b))
      case 'max': return n(e.a).max(n(e.b))
      case 'divk': return n(e.a).divBy(e.k)
      case 'modk': return Int.of(n(e.a).modBy(e.k))
      case 'ite': return Int.of(whenInt(b(e.c), n(e.a), n(e.b)))
      case 'mul': { const a = env[(e.a as {name?: string}).name ?? ''], bb = env[(e.b as {name?: string}).name ?? '']; if (a instanceof Term && bb instanceof Term) return Int.of(a.mul(bb)); throw new Error('a product in a probe') }
      case 'cell': throw new Error('a map cell in a probe')
    }
  }
  const l = (x: I.L): {is: (v: string) => ReturnType<Term['lt']>} => {
    if (x.op === 'var') return env[x.name] as never
    if (x.op === 'lit') return {is: (v: string) => (v === x.value ? yesC : noC)}
    if (x.op === 'ite') { const cc = b(x.c), a = l(x.a), bb = l(x.b); return {is: (v: string) => cc.and(a.is(v)).or(cc.not().and(bb.is(v)))} }
    throw new Error('a map cell in a probe')
  }
  const b = (x: B): ReturnType<Term['lt']> => {
    switch (x.op) {
      case 'const': return x.v ? yesC : noC
      case 'var': return env[x.name] as never
      case 'cmp': return x.rel === '<' ? n(x.a).lt(n(x.b)) : x.rel === '<=' ? n(x.a).atMost(n(x.b)) : n(x.a).eq(n(x.b))
      case 'and': return x.xs.map(b).reduce((p, y) => p.and(y))
      case 'or': return x.xs.map(b).reduce((p, y) => p.or(y))
      case 'not': return b(x.x).not()
      case 'ite': { const cc = b(x.c); return cc.and(b(x.a)).or(cc.not().and(b(x.b))) }
      case 'is': return l(x.l).is(x.value)
      case 'leq': { const a = x.a, bb = x.b; if (a.op === 'var' && bb.op === 'var') return (env[a.name] as {eq: (o: unknown) => never}).eq(env[bb.name]); throw new Error('a choice comparison in a probe') }
      case 'keq': { const s = (k: I.K): {eq: (o: unknown) => never} | string => (k.op === 'svar' ? env[k.name] as never : k.op === 'slit' ? k.value : (() => { throw new Error('a key in a probe') })()); const a = s(x.a), bb = s(x.b); return (typeof a === 'string' ? (bb as {eq: (o: unknown) => never}).eq(a) : a.eq(bb)) }
      case 'cell': throw new Error('a map cell in a probe')
    }
  }
  return b(c)
}
import {yes as yesC, no as noC, when as whenDsl} from './dsl.ts'
const whenInt = (c: ReturnType<Term['lt']>, a: Int, b: Int): Int => whenDsl(c, a, b)

// A term at concrete values (a constant field over the params, a start, the precondition).
export function evalTerm(t: N | B | I.L, env: Record<string, Raw>): Raw {
  const n = (e: N): number => {
    switch (e.op) {
      case 'var': return env[e.name] as number
      case 'const': return e.v
      case 'add': return n(e.a) + n(e.b)
      case 'sub': return n(e.a) - n(e.b)
      case 'neg': return -n(e.a)
      case 'mulk': return e.k * n(e.a)
      case 'mul': return n(e.a) * n(e.b)
      case 'min': return Math.min(n(e.a), n(e.b))
      case 'max': return Math.max(n(e.a), n(e.b))
      case 'divk': return Math.floor(n(e.a) / e.k)
      case 'modk': return ((n(e.a) % e.k) + e.k) % e.k
      case 'ite': return b(e.c) ? n(e.a) : n(e.b)
      case 'cell': throw new Error('a map cell at the start')
    }
  }
  const l = (x: I.L): string => (x.op === 'var' ? env[x.name] as string : x.op === 'lit' ? x.value : x.op === 'ite' ? (b(x.c) ? l(x.a) : l(x.b)) : (() => { throw new Error('a map cell') })())
  const b = (x: B): boolean => {
    switch (x.op) {
      case 'const': return x.v
      case 'var': return env[x.name] as boolean
      case 'cmp': return x.rel === '<' ? n(x.a) < n(x.b) : x.rel === '<=' ? n(x.a) <= n(x.b) : n(x.a) === n(x.b)
      case 'and': return x.xs.every(b)
      case 'or': return x.xs.some(b)
      case 'not': return !b(x.x)
      case 'ite': return b(x.c) ? b(x.a) : b(x.b)
      case 'is': return l(x.l) === x.value
      case 'leq': return l(x.a) === l(x.b)
      case 'keq': throw new Error('a key at the start')
      case 'cell': throw new Error('a map cell at the start')
    }
  }
  if (t.op === 'var') return env[t.name]!
  if (t.op === 'const') return t.v
  if (t.op === 'lit') return t.value
  if (t.op === 'ite') return b(t.c) ? evalTerm(t.a, env) : evalTerm(t.b, env)
  if (['add', 'sub', 'neg', 'mulk', 'mul', 'min', 'max', 'divk', 'modk', 'cell'].includes(t.op)) return n(t as N)
  return b(t as B)
}
