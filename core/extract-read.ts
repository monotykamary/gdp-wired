// The extractor's reader (core/extract.ts): TypeScript (or JavaScript) read through the compiler's own parser and type
// checker, and one step of it executed symbolically. A path is a condition (the branches taken), the locals, a heap of
// the objects and maps the step can reach, and the writes so far; branches fork paths and merge them again where they
// meet, so a step is one term per state variable, built by cases. What isn't in the subset is refused where it is, with
// the reason: nothing outside it is approximated. Nothing here is trusted either: the rule printed from what this reads
// is run against the code itself (core/extract-check.ts) before it is handed out.
import ts from 'typescript'
import * as I from './extract-ir.ts'
import type {B, K, L, N} from './extract-ir.ts'

export class Refusal extends Error {
  constructor(readonly where: string, readonly what: string) { super(`${where}: ${what}`) }
}

// --- sorts and shapes -----------------------------------------------------------------------------------------------
export type Sort = {k: 'num'} | {k: 'bool'} | {k: 'choice', values: string[]} | {k: 'str'}
export type Shape = Sort | {k: 'rec', fields: [string, Shape][]} | {k: 'map', key: 'num' | 'str', val: Shape, js: 'Map' | 'record'}
// A rule variable: its sort, and where it comes from.
export type Var = {name: string, sort: Sort, role: 'param' | 'input' | 'state', note?: string}
// A map of the state: its cells are records of `fields` (one, `value`, for a map of scalars) and `has` (the key holds one).
export type MapDecl = {name: string, key: 'num' | 'str', fields: Var[], scalar: boolean, js: 'Map' | 'record'}
// Where each of the code's values is in the rule: the state's tree, leaf by leaf.
export type Layout = {k: 'scalar', name: string} | {k: 'rec', fields: [string, Layout][]} | {k: 'map', name: string} | {k: 'const', value: Term}
export type Term = {s: 'num', e: N} | {s: 'bool', e: B} | {s: 'choice', e: L}
// How a request is made of the code: the call, and its arguments built from the rule's inputs.
export type Arg = {k: 'input', name: string} | {k: 'lit', value: string} | {k: 'rec', fields: [string, Arg][]} | {k: 'state'} | {k: 'lazy', prefix: string}
export type Event = {select: Record<string, string>, call: string, args: Arg[]}
export type MapWrite = {key: K, has: B, vals: Record<string, Term>}
export type Model = {
  name: string, shape: 'reducer' | 'functions' | 'class', file: string, entry: string,
  params: Var[], inputs: Var[], state: Var[], maps: MapDecl[],
  // The event: an input choosing the method, function or action type (undefined for a single one).
  event?: string,
  init: Record<string, Term>, writes: Record<string, Term>, mapWrites: Record<string, MapWrite>, outputs: string[],
  refuse: B, pre: B, layout: Layout, events: Event[], notes: string[],
  // Where the hoisted terms' names come from: the code's own locals.
  hints: WeakMap<object, string>,
  // For a class: how the object is made (its constructor's arguments, by param) and the fields that are constants.
  ctorArgs?: string[],
  // The inputs an untyped record grew (by its prefix and field), and the code's own initial state (its source text).
  lazy?: Map<string, {prefix: string, field: string}>,
  initSource?: string,
}

// --- values ---------------------------------------------------------------------------------------------------------
type V =
  | {t: 'num', e: N} | {t: 'bool', e: B} | {t: 'choice', e: L, values: string[]} | {t: 'str', e: K}
  | {t: 'ref', id: string} | {t: 'cell', map: string, key: K, gen: number} | {t: 'opt', has: B, v: V} | {t: 'undef'}
  // One of two objects by a condition: reads by cases, a write to each where it is the one (so aliasing is kept).
  | {t: 'phi', c: B, a: V, b: V}
type Rec = {k: 'rec', fields: Map<string, V>, origin: 'fresh' | 'input' | 'this' | 'shared', lazy?: {prefix: string}}
type MapObj = {k: 'map', base: string, decl: MapDecl, w?: {key: K, has: B, vals: Map<string, V>}, origin: 'fresh' | 'input' | 'this' | 'shared', gen: number}
type Obj = Rec | MapObj | {k: 'alias', to: V}
type Heap = Map<string, Obj>
type Path = {pc: B[], locals: Map<string, V>, heap: Heap, wrote: string[], nows: number}
type Flow = {live?: Path, rets: [Path, V][], breaks: Path[]}

const where = (n: ts.Node): string => {
  const sf = n.getSourceFile(), {line, character} = sf.getLineAndCharacterOfPosition(n.getStart())
  return `${sf.fileName.split('/').pop()}:${line + 1}:${character + 1}`
}
const refuse = (n: ts.Node, what: string): never => { throw new Refusal(where(n), what) }
const text = (n: ts.Node) => n.getText().replace(/\s+/g, ' ').slice(0, 60)

// --- the program ----------------------------------------------------------------------------------------------------
export function program(code: string, file: string): {sf: ts.SourceFile, checker: ts.TypeChecker} {
  const options: ts.CompilerOptions = {target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext, moduleResolution: ts.ModuleResolutionKind.Bundler, strict: true, noEmit: true, allowJs: true, checkJs: false, skipLibCheck: true, lib: ['lib.es2022.d.ts'], types: [], jsx: ts.JsxEmit.Preserve}
  const host = ts.createCompilerHost(options), getSourceFile = host.getSourceFile.bind(host), readFile = host.readFile.bind(host), fileExists = host.fileExists.bind(host)
  host.getSourceFile = (name, lang, ...rest) => (name === file ? ts.createSourceFile(name, code, lang, true, scriptKind(file)) : getSourceFile(name, lang, ...rest))
  host.readFile = name => (name === file ? code : readFile(name))
  host.fileExists = name => name === file || fileExists(name)
  const p = ts.createProgram([file], options, host)
  return {sf: p.getSourceFile(file)!, checker: p.getTypeChecker()}
}

export const scriptKind = (file: string): ts.ScriptKind => (/\.jsx$/.test(file) ? ts.ScriptKind.JSX : /\.tsx$/.test(file) ? ts.ScriptKind.TSX : /\.[cm]?js$/.test(file) ? ts.ScriptKind.JS : ts.ScriptKind.TS)
// The shape a type has in the subset.
export function shapeOf(t: ts.Type, checker: ts.TypeChecker, at: ts.Node): Shape {
  if (t.flags & (ts.TypeFlags.NumberLike)) return {k: 'num'}
  if (t.flags & ts.TypeFlags.BooleanLike) return {k: 'bool'}
  if (t.flags & ts.TypeFlags.StringLiteral) return {k: 'choice', values: [(t as ts.StringLiteralType).value]}
  if (t.flags & ts.TypeFlags.String) return {k: 'str'}
  if (t.isUnion()) {
    const parts = t.types
    if (parts.every(p => p.flags & ts.TypeFlags.BooleanLiteral)) return {k: 'bool'}
    if (parts.every(p => p.flags & ts.TypeFlags.NumberLiteral)) return {k: 'num'}
    if (parts.every(p => p.flags & ts.TypeFlags.StringLiteral)) return {k: 'choice', values: parts.map(p => (p as ts.StringLiteralType).value)}
    if (parts.some(p => p.flags & (ts.TypeFlags.Undefined | ts.TypeFlags.Null))) return refuse(at, `${checker.typeToString(t)}: a value that may be missing (a map's cell is how the subset holds one)`)
    return refuse(at, `${checker.typeToString(t)}: a union of other than string literals`)
  }
  if (t.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)) return refuse(at, `${text(at)} has no type the subset reads (any or unknown): annotate it`)
  if (t.flags & ts.TypeFlags.Object) {
    const sym = t.getSymbol() ?? t.aliasSymbol, name = sym?.getName()
    if (name === 'Map') {
      const [kt, vt] = checker.getTypeArguments(t as ts.TypeReference)
      if (!kt || !vt) return refuse(at, 'a Map without its key and value types')
      return {k: 'map', key: keySort(shapeOf(kt, checker, at), at), val: shapeOf(vt, checker, at), js: 'Map'}
    }
    if (checker.isArrayType(t) || checker.isTupleType(t)) return refuse(at, `${checker.typeToString(t)}: an array (lists are not in the subset yet)`)
    if (name === 'Set' || name === 'Date' || name === 'Promise') return refuse(at, `a ${name}`)
    const sidx = checker.getIndexInfoOfType(t, ts.IndexKind.String), nidx = checker.getIndexInfoOfType(t, ts.IndexKind.Number)
    if (sidx || nidx) {
      if (checker.getPropertiesOfType(t).length) return refuse(at, `${checker.typeToString(t)}: named fields beside an index signature`)
      return {k: 'map', key: sidx ? 'str' : 'num', val: shapeOf((sidx ?? nidx)!.type, checker, at), js: 'record'}
    }
    if (checker.getSignaturesOfType(t, ts.SignatureKind.Call).length) return refuse(at, `${checker.typeToString(t)}: a function value`)
    const fields: [string, Shape][] = checker.getPropertiesOfType(t).map(p => {
      if (p.flags & ts.SymbolFlags.Optional) refuse(at, `the optional field ${p.getName()} (a value that may be missing)`)
      if (p.flags & ts.SymbolFlags.Method) refuse(at, `the method ${p.getName()} in a value`)
      return [p.getName(), shapeOf(checker.getTypeOfSymbolAtLocation(p, at), checker, at)]
    })
    return {k: 'rec', fields}
  }
  return refuse(at, `${checker.typeToString(t)} is not in the subset`)
}
const keySort = (s: Shape, at: ts.Node): 'num' | 'str' => (s.k === 'num' ? 'num' : s.k === 'str' || s.k === 'choice' ? 'str' : refuse(at, 'a map keyed by other than numbers or strings'))

// --- the executor ---------------------------------------------------------------------------------------------------
type Callable = {decl: ts.FunctionLikeDeclaration, self?: string}
export type Setup = {
  checker: ts.TypeChecker, sf: ts.SourceFile,
  // The names the rule's variables are made under (state, inputs and params share one scope).
  names: Set<string>,
  vars: Map<string, Var>, maps: Map<string, MapDecl>,
  // Inputs an untyped (JavaScript) record grows as the code reads it: their sorts by how they are compared.
  lazySorts: Map<string, Sort>,
  // The class being read: its members by name.
  cls?: ts.ClassLikeDeclaration,
  // Date.now(): the input it reads (made on first use), or the param a constructor reads.
  now?: string, nowRole: 'input' | 'param',
  hints: WeakMap<object, string>,
  notes: Set<string>,
  // The inputs an untyped record grew, each with the record's prefix and its field.
  lazy: Map<string, {prefix: string, field: string}>,
  // While a constructor runs: `new Map()` and `{}` are a map that starts empty.
  ctor?: boolean,
}

export class Exec {
  throws: {pc: B[]}[] = []
  private depth = 0
  private ids = 0
  constructor(readonly s: Setup) {}
  fresh(base: string): string {
    const clean = base.replace(/^#/, '').replace(/[^A-Za-z0-9_]/g, '_').replace(/^(\d)/, '_$1') || 'x'
    let n = clean, i = 2
    while (this.s.names.has(n) || RESERVED.has(n)) n = `${clean}_${i++}`
    this.s.names.add(n)
    return n
  }
  newVar(base: string, sort: Sort, role: Var['role'], note?: string): Var {
    const v: Var = {name: this.fresh(base), sort, role, ...(note ? {note} : {})}
    this.s.vars.set(v.name, v)
    return v
  }
  id(prefix: string) { return `${prefix}#${++this.ids}` }

  // A variable's value by its sort.
  static valueOf(v: Var): V {
    switch (v.sort.k) {
      case 'num': return {t: 'num', e: I.nvar(v.name)}
      case 'bool': return {t: 'bool', e: I.bvar(v.name)}
      case 'choice': return {t: 'choice', e: {op: 'var', name: v.name, values: v.sort.values}, values: v.sort.values}
      case 'str': return {t: 'str', e: {op: 'svar', name: v.name}}
    }
  }
  // A map's cell field (before the step) by its sort.
  static cellOf(m: MapDecl, key: K, f: Var): V {
    switch (f.sort.k) {
      case 'num': return {t: 'num', e: {op: 'cell', map: m.name, key, field: f.name}}
      case 'bool': return {t: 'bool', e: {op: 'cell', map: m.name, key, field: f.name}}
      case 'choice': return {t: 'choice', e: {op: 'cell', map: m.name, key, field: f.name, values: f.sort.values}, values: f.sort.values}
      case 'str': throw new Error('a string in a map cell')
    }
  }
  static defaultOf(sort: Sort): V {
    switch (sort.k) {
      case 'num': return {t: 'num', e: I.num(0)}
      case 'bool': return {t: 'bool', e: I.F}
      case 'choice': return {t: 'choice', e: I.llit(sort.values[0]!, sort.values), values: sort.values}
      case 'str': return {t: 'str', e: {op: 'slit', value: ''}}
    }
  }

  // --- paths -----------------------------------------------------------------------------------------------------
  withCond(p: Path, c: B): Path { return {...p, pc: c.op === 'const' && c.v ? p.pc : [...p.pc, c]} }
  feasible(p: Path): boolean { return !p.pc.some(c => c.op === 'const' && !c.v) }
  // What holds on a path, by its conditions: a condition known there (one of them, or a part of one).
  known(p: Path, c: B): boolean {
    if (c.op === 'const') return c.v
    const flat = (x: B): B[] => (x.op === 'and' ? x.xs.flatMap(flat) : x.op === 'not' && x.x.op === 'or' ? x.x.xs.map(y => I.not(y)).flatMap(flat) : [x])
    const parts = p.pc.flatMap(flat)
    if (c.op === 'and') return c.xs.every(x => this.known(p, x))
    return parts.some(x => I.same(x, c))
  }
  merge(a: Path | undefined, b: Path | undefined, at: ts.Node): Path | undefined {
    if (!a || !this.feasible(a)) return b && this.feasible(b) ? b : undefined
    if (!b || !this.feasible(b)) return a
    let i = 0
    while (i < a.pc.length && i < b.pc.length && a.pc[i] === b.pc[i]) i++
    const ra = a.pc.slice(i), rb = b.pc.slice(i), prefix = a.pc.slice(0, i)
    const c = ra.length ? I.and(...ra) : I.not(I.and(...rb))
    const complementary = (ra.length === 1 && rb.length === 1 && I.same(ra[0]!, I.not(rb[0]!))) || !ra.length || !rb.length
    const pc = complementary ? prefix : [...prefix, I.or(I.and(...ra), I.and(...rb))]
    const pairs = new Map<string, string>(), heap: Heap = new Map()
    const locals = new Map<string, V>()
    for (const [n, va] of a.locals) { const vb = b.locals.get(n); if (vb) locals.set(n, this.mergeV(c, va, vb, a, b, heap, pairs, at)) }
    for (const id of new Set([...a.heap.keys(), ...b.heap.keys()])) {
      if (heap.has(id)) continue
      const oa = a.heap.get(id), ob = b.heap.get(id)
      heap.set(id, !oa ? ob! : !ob ? oa : this.mergeObj(c, oa, ob, a, b, heap, pairs, at))
    }
    return {pc, locals, heap, wrote: [...new Set([...a.wrote, ...b.wrote])], nows: Math.max(a.nows, b.nows)}
  }
  private deref(p: Path, v: V): V {
    while (v.t === 'ref') { const o = p.heap.get(v.id); if (o?.k !== 'alias') return v; v = o.to }
    return v
  }
  private mergeV(c: B, va: V, vb: V, a: Path, b: Path, heap: Heap, pairs: Map<string, string>, at: ts.Node): V {
    va = this.deref(a, va); vb = this.deref(b, vb)
    if (va.t === 'num' && vb.t === 'num') return {t: 'num', e: I.nite(c, va.e, vb.e)}
    if (va.t === 'bool' && vb.t === 'bool') return {t: 'bool', e: I.bite(c, va.e, vb.e)}
    if ((va.t === 'choice' || va.t === 'str') && (vb.t === 'choice' || vb.t === 'str')) {
      if (va.t === 'str' && vb.t === 'str') return {t: 'str', e: I.kite(c, va.e, vb.e)}
      const values = va.t === 'choice' ? va.values : (vb as {values: string[]}).values
      return {t: 'choice', e: I.lite(c, this.asChoice(va, values, at), this.asChoice(vb, values, at)), values}
    }
    if (va.t === 'undef' && vb.t === 'undef') return va
    if (va.t === 'opt' || vb.t === 'opt' || va.t === 'undef' || vb.t === 'undef') {
      const [ha, xa] = va.t === 'opt' ? [va.has, va.v] : va.t === 'undef' ? [I.F, undefined] : [I.T, va]
      const [hb, xb] = vb.t === 'opt' ? [vb.has, vb.v] : vb.t === 'undef' ? [I.F, undefined] : [I.T, vb]
      const v = !xa ? xb! : !xb ? xa : this.mergeV(c, xa, xb, a, b, heap, pairs, at)
      return {t: 'opt', has: I.bite(c, ha, hb), v}
    }
    if (va.t === 'cell' && vb.t === 'cell' && va.map === vb.map) {
      // Current on both paths (the map not set since it was read on either): current in the map merged.
      const ma = a.heap.get(va.map) as MapObj, mb = b.heap.get(vb.map) as MapObj
      if (va.gen !== ma.gen || vb.gen !== mb.gen) return refuse(at, 'a reference into a map read before the map was set')
      return {t: 'cell', map: va.map, key: I.kite(c, va.key, vb.key), gen: mergedGen(ma, mb)}
    }
    if (va.t === 'ref' && vb.t === 'ref' && va.id === vb.id) return va
    // Two objects by the path taken: a reference to each by the condition.
    const refs = ['ref', 'cell', 'phi']
    if (refs.includes(va.t) && refs.includes(vb.t)) return {t: 'phi', c, a: va, b: vb}
    return refuse(at, `a value that is a ${va.t} on one path and a ${vb.t} on another`)
  }
  private mergeObj(c: B, oa: Obj, ob: Obj, a: Path, b: Path, heap: Heap, pairs: Map<string, string>, at: ts.Node, two = false): Obj {
    if (oa.k === 'alias' && ob.k === 'alias') return {k: 'alias', to: this.mergeV(c, oa.to, ob.to, a, b, heap, pairs, at)}
    if (oa.k === 'rec' && ob.k === 'rec') {
      const fa = [...oa.fields.keys()].sort().join(), fb = [...ob.fields.keys()].sort().join()
      if (fa !== fb) return refuse(at, 'an object with other fields by the path taken')
      const origin = oa.origin === 'input' || ob.origin === 'input' ? 'input' : oa.origin === 'shared' || ob.origin === 'shared' ? 'shared' : oa.origin
      return {k: 'rec', origin, fields: new Map([...oa.fields].map(([f, v]) => [f, this.mergeV(c, v, ob.fields.get(f)!, a, b, heap, pairs, at)])), ...(oa.lazy ? {lazy: oa.lazy} : {})}
    }
    if (oa.k === 'map' && ob.k === 'map') {
      if (oa.base !== ob.base) return refuse(at, 'one of two maps by the path taken')
      const origin = oa.origin === 'input' || ob.origin === 'input' ? 'input' : oa.origin
      void two
      return {...oa, origin, gen: mergedGen(oa, ob), w: this.mergeW(c, oa, ob, at)}
    }
    return refuse(at, 'an object that is of another kind by the path taken')
  }
  private mergeW(c: B, oa: MapObj, ob: MapObj, at: ts.Node): MapObj['w'] { return this.mergeWrites(c, oa.decl, oa.w, ob.w, at) }
  mergeWrites(c: B, decl: MapDecl, wa: MapObj['w'], wb: MapObj['w'], at: ts.Node): MapObj['w'] {
    if (!wa && !wb) return undefined
    const base = (key: K) => this.baseCell(decl, key)
    const fill = (w: MapObj['w'], key: K) => w ?? {key, ...base(key)}
    const xa = fill(wa, (wa ?? wb)!.key), xb = fill(wb, (wb ?? wa)!.key)
    const vals = new Map([...xa.vals].map(([f, v]) => [f, this.mergeScalar(c, v, xb.vals.get(f)!, at)]))
    return {key: I.kite(c, xa.key, xb.key), has: I.bite(c, xa.has, xb.has), vals}
  }
  mergeScalar(c: B, a: V, b: V, at: ts.Node): V {
    if (a.t === 'num' && b.t === 'num') return {t: 'num', e: I.nite(c, a.e, b.e)}
    if (a.t === 'bool' && b.t === 'bool') return {t: 'bool', e: I.bite(c, a.e, b.e)}
    if (a.t === 'choice' && b.t === 'choice') return {t: 'choice', e: I.lite(c, a.e, b.e), values: a.values}
    return refuse(at, 'a map cell of another kind by the path taken')
  }
  baseCell(m: MapDecl, key: K): {has: B, vals: Map<string, V>} {
    return {has: {op: 'cell', map: m.name, key, field: 'has'}, vals: new Map(m.fields.map(f => [f.name, Exec.cellOf(m, key, f)]))}
  }
  asChoice(v: V, values: string[], at: ts.Node): L {
    if (v.t === 'choice') return v.e
    if (v.t === 'str' && v.e.op === 'slit') {
      if (!values.includes(v.e.value)) return refuse(at, `'${v.e.value}' is not one of ${values.map(x => `'${x}'`).join(', ')}`)
      return I.llit(v.e.value, values)
    }
    return refuse(at, 'a string that is not one of a union\'s literals')
  }

  // --- statements ------------------------------------------------------------------------------------------------
  block(stmts: readonly ts.Statement[], p: Path): Flow {
    const declared: string[] = []
    let live: Path | undefined = p
    const rets: [Path, V][] = [], breaks: Path[] = []
    for (const st of stmts) {
      if (!live) break
      if (ts.isVariableStatement(st)) for (const d of st.declarationList.declarations) for (const n of boundNames(d.name)) { if (live.locals.has(n) && !declared.includes(n)) refuse(d, `${n} shadows another ${n}`); declared.push(n) }
      if (ts.isFunctionDeclaration(st)) refuse(st, 'a function declared inside a step')
      const f = this.stmt(st, live)
      rets.push(...f.rets); breaks.push(...f.breaks)
      live = f.live
    }
    if (live) { live = {...live, locals: new Map(live.locals)}; for (const n of declared) live.locals.delete(n) }
    return {...(live ? {live} : {}), rets, breaks}
  }
  stmt(st: ts.Statement, p: Path): Flow {
    const none: Flow = {rets: [], breaks: []}
    if (ts.isBlock(st)) return this.block(st.statements, p)
    if (ts.isEmptyStatement(st)) return {...none, live: p}
    if (ts.isExpressionStatement(st)) { const [, q] = this.ev(st.expression, p); return {...none, live: q} }
    if (ts.isVariableStatement(st)) {
      if (!(st.declarationList.flags & (ts.NodeFlags.Const | ts.NodeFlags.Let))) refuse(st, 'var (let or const are in the subset)')
      let q = p
      for (const d of st.declarationList.declarations) {
        let v: V = {t: 'undef'}
        if (d.initializer) [v, q] = this.ev(d.initializer, q)
        q = this.bind(d.name, v, q)
      }
      return {...none, live: q}
    }
    if (ts.isReturnStatement(st)) {
      if (!st.expression) return {...none, rets: [[p, {t: 'undef'}]]}
      const [v, q] = this.ev(st.expression, p)
      return {...none, rets: [[q, v]]}
    }
    if (ts.isThrowStatement(st)) {
      if (impure(st.expression)) refuse(st, 'a throw whose argument has effects')
      if (p.wrote.length) refuse(st, `throws after writing ${p.wrote.join(', ')}: the code leaves its state changed where a rule's refusal leaves it as it was`)
      this.throws.push({pc: p.pc})
      return none
    }
    if (ts.isIfStatement(st)) {
      const [cv, q] = this.ev(st.expression, p), c = this.truthy(cv, st.expression)
      const [pt, pe] = this.narrow(st.expression, this.withCond(q, c), this.withCond(q, I.not(c)))
      const ft = this.feasible(pt) ? this.stmt(st.thenStatement, pt) : none
      const fe = !this.feasible(pe) ? none : st.elseStatement ? this.stmt(st.elseStatement, pe) : {...none, live: pe}
      const live = this.merge(ft.live, fe.live, st)
      return {...(live ? {live} : {}), rets: [...ft.rets, ...fe.rets], breaks: [...ft.breaks, ...fe.breaks]}
    }
    if (ts.isSwitchStatement(st)) return this.switch(st, p)
    if (ts.isBreakStatement(st)) { if (st.label) refuse(st, 'a labeled break'); return {...none, breaks: [p]} }
    if (ts.isForStatement(st) || ts.isForOfStatement(st) || ts.isForInStatement(st) || ts.isWhileStatement(st) || ts.isDoStatement(st)) return refuse(st, 'a loop (a rule\'s step is one bounded computation; a loop over the state is not in the subset)')
    if (ts.isTryStatement(st)) return refuse(st, 'try/catch (a refusal caught inside the step)')
    return refuse(st, `${ts.SyntaxKind[st.kind]} is not in the subset`)
  }
  private switch(st: ts.SwitchStatement, p: Path): Flow {
    const [dv, q] = this.ev(st.expression, p)
    const matches: B[] = []
    const conds = st.caseBlock.clauses.map(cl => {
      if (ts.isDefaultClause(cl)) return undefined
      if (impure(cl.expression)) refuse(cl, 'a case with effects')
      const [cv] = this.ev(cl.expression, q)
      const m = this.equal(dv, cv, cl.expression)
      const c = I.and(...matches.map(I.not), m)
      matches.push(m)
      return c
    })
    const none = I.not(I.or(...matches))
    let fall: Path | undefined
    const rets: [Path, V][] = [], ends: Path[] = []
    st.caseBlock.clauses.forEach((cl, i) => {
      const enter = this.merge(fall, this.withCond(q, conds[i] ?? none), cl)
      if (!enter) { fall = undefined; return }
      const f = this.block(cl.statements, enter)
      rets.push(...f.rets); ends.push(...f.breaks)
      fall = f.live
    })
    if (fall) ends.push(fall)
    if (!st.caseBlock.clauses.some(ts.isDefaultClause)) ends.push(this.withCond(q, none))
    const live = ends.reduceRight<Path | undefined>((acc, x) => this.merge(x, acc, st), undefined)
    return {...(live ? {live} : {}), rets, breaks: []}
  }
  // `if (!x)` and `if (x)` (x === undefined, x !== undefined) on a value that may be missing: x is known in the branch
  // where it is there.
  private narrow(e: ts.Expression, pt: Path, pe: Path): [Path, Path] {
    const strip = (x: ts.Expression): ts.Expression => (ts.isParenthesizedExpression(x) ? strip(x.expression) : x)
    let x = strip(e), present = true
    if (ts.isPrefixUnaryExpression(x) && x.operator === ts.SyntaxKind.ExclamationToken) { x = strip(x.operand); present = false }
    else if (ts.isBinaryExpression(x) && (x.right.kind === ts.SyntaxKind.UndefinedKeyword || (ts.isIdentifier(x.right) && x.right.text === 'undefined') || x.right.kind === ts.SyntaxKind.NullKeyword)) {
      const op = x.operatorToken.kind
      if (op === ts.SyntaxKind.EqualsEqualsEqualsToken || op === ts.SyntaxKind.EqualsEqualsToken) present = false
      else if (op !== ts.SyntaxKind.ExclamationEqualsEqualsToken && op !== ts.SyntaxKind.ExclamationEqualsToken) return [pt, pe]
      x = strip(x.left)
    }
    if (!ts.isIdentifier(x)) return [pt, pe]
    const v = pt.locals.get(x.text)
    if (v?.t !== 'opt') return [pt, pe]
    const set = (p: Path, there: boolean): Path => ({...p, locals: new Map(p.locals).set(x.text, there ? v.v : {t: 'undef'})})
    return present ? [set(pt, true), set(pe, false)] : [set(pt, false), set(pe, true)]
  }
  bind(name: ts.BindingName, v: V, p: Path): Path {
    if (ts.isIdentifier(name)) { this.hint(v, name.text); return {...p, locals: new Map(p.locals).set(name.text, v)} }
    if (ts.isObjectBindingPattern(name)) {
      let q = p
      for (const el of name.elements) {
        if (el.dotDotDotToken || el.initializer) refuse(el, 'a rest or default in a destructuring')
        const key = el.propertyName ? (ts.isIdentifier(el.propertyName) ? el.propertyName.text : refuse(el, 'a computed name in a destructuring')) : (el.name as ts.Identifier).text
        const [fv, q2] = this.field(v, key, el, q)
        q = this.bind(el.name, fv, q2)
      }
      return q
    }
    return refuse(name, 'an array destructuring')
  }
  private hint(v: V, name: string) {
    const e = v.t === 'num' || v.t === 'bool' || v.t === 'choice' ? v.e : undefined
    if (e && e.op !== 'var' && e.op !== 'const' && e.op !== 'lit' && !this.s.hints.has(e)) this.s.hints.set(e, name)
  }

  // --- expressions -----------------------------------------------------------------------------------------------
  truthy(v: V, at: ts.Node): B {
    switch (v.t) {
      case 'bool': return v.e
      case 'num': return I.not(I.cmp('=', v.e, I.num(0)))
      case 'choice': return v.values.includes('') ? I.not(I.is(v.e, '')) : I.T
      case 'str': return v.e.op === 'slit' ? (v.e.value ? I.T : I.F) : refuse(at, 'a string as a condition')
      case 'ref': case 'cell': case 'phi': return I.T
      case 'opt': return I.and(v.has, this.truthy(v.v, at))
      case 'undef': return I.F
    }
  }
  num(v: V, at: ts.Node, p: Path): N {
    if (v.t === 'num') return v.e
    if (v.t === 'opt' && this.known(p, v.has)) return this.num(v.v, at, p)
    if (v.t === 'opt') return refuse(at, `${text(at)} may be missing (undefined): give a default (?? 0) or check for it first`)
    return refuse(at, `${text(at)} is a ${v.t === 'bool' ? 'boolean' : v.t === 'choice' || v.t === 'str' ? 'string' : v.t === 'undef' ? 'undefined' : 'object'} where a number is read`)
  }
  private bool(v: V, at: ts.Node): B { return v.t === 'bool' ? v.e : refuse(at, `${text(at)} where a boolean is read`) }
  equal(a: V, b: V, at: ts.Node): B {
    if (a.t === 'num' && b.t === 'num') return I.cmp('=', a.e, b.e)
    if (a.t === 'bool' && b.t === 'bool') return I.or(I.and(a.e, b.e), I.and(I.not(a.e), I.not(b.e)))
    if (a.t === 'choice' && (b.t === 'choice' || b.t === 'str')) return I.leq(a.e, b.t === 'str' && b.e.op === 'slit' && !a.values.includes(b.e.value) ? I.llit(b.e.value, [...a.values, b.e.value]) : this.asChoice(b, a.values, at))
    if (b.t === 'choice' && a.t === 'str') return this.equal(b, a, at)
    if (a.t === 'str' && b.t === 'str') return I.keq(a.e, b.e)
    if (a.t === 'undef' || b.t === 'undef') {
      const o = a.t === 'undef' ? b : a
      return o.t === 'undef' ? I.T : o.t === 'opt' ? I.not(o.has) : I.F
    }
    return refuse(at, `a comparison of a ${a.t} with a ${b.t}`)
  }
  ev(e: ts.Expression, p: Path): [V, Path] {
    if (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isSatisfiesExpression(e) || ts.isTypeAssertionExpression(e)) return this.ev(e.expression, p)
    if (ts.isNonNullExpression(e)) {
      const [v, q] = this.ev(e.expression, p)
      if (v.t !== 'opt') return [v, q]
      if (!this.known(q, v.has)) return refuse(e, `${text(e.expression)}! where it may be missing`)
      return [v.v, q]
    }
    if (ts.isNumericLiteral(e)) {
      const x = Number(e.text)
      if (!Number.isSafeInteger(x)) return refuse(e, `${e.text}: a number that isn't a safe integer (the subset's numbers are integers)`)
      return [{t: 'num', e: I.num(x)}, p]
    }
    if (ts.isStringLiteral(e) || ts.isNoSubstitutionTemplateLiteral(e)) return [{t: 'str', e: {op: 'slit', value: e.text}}, p]
    if (e.kind === ts.SyntaxKind.TrueKeyword) return [{t: 'bool', e: I.T}, p]
    if (e.kind === ts.SyntaxKind.FalseKeyword) return [{t: 'bool', e: I.F}, p]
    if (e.kind === ts.SyntaxKind.NullKeyword) return refuse(e, 'null')
    if (e.kind === ts.SyntaxKind.ThisKeyword) { if (!p.heap.has('this')) refuse(e, 'this outside a class'); return [{t: 'ref', id: 'this'}, p] }
    if (ts.isIdentifier(e)) return this.name(e, p)
    if (ts.isPropertyAccessExpression(e) || ts.isElementAccessExpression(e)) return this.access(e, p)
    if (ts.isPrefixUnaryExpression(e)) return this.prefix(e, p)
    if (ts.isPostfixUnaryExpression(e)) {
      const [old, q] = this.ev(e.operand, p), n = this.num(old, e.operand, q)
      const q2 = this.assign(e.operand, {t: 'num', e: e.operator === ts.SyntaxKind.PlusPlusToken ? I.add(n, I.num(1)) : I.sub(n, I.num(1))}, q)
      return [{t: 'num', e: n}, q2]
    }
    if (ts.isBinaryExpression(e)) return this.binary(e, p)
    if (ts.isConditionalExpression(e)) {
      const [cv, q] = this.ev(e.condition, p), c = this.truthy(cv, e.condition)
      const [pt, pe] = this.narrow(e.condition, this.withCond(q, c), this.withCond(q, I.not(c)))
      if (!this.feasible(pt)) return this.ev(e.whenFalse, pe)
      if (!this.feasible(pe)) return this.ev(e.whenTrue, pt)
      const [va, qa] = this.ev(e.whenTrue, pt), [vb, qb] = this.ev(e.whenFalse, pe)
      return this.joinValues(c, qa, va, qb, vb, e)
    }
    if (ts.isObjectLiteralExpression(e)) return this.object(e, p)
    if (ts.isCallExpression(e)) return this.call(e, p)
    if (ts.isNewExpression(e)) return this.newExpr(e, p)
    if (ts.isArrayLiteralExpression(e)) return refuse(e, 'an array (lists are not in the subset yet)')
    if (ts.isTemplateExpression(e)) return refuse(e, 'a template string')
    if (ts.isArrowFunction(e) || ts.isFunctionExpression(e)) return refuse(e, 'a function value')
    if (ts.isTypeOfExpression(e)) return refuse(e, 'typeof')
    if (ts.isAwaitExpression(e)) return refuse(e, 'await (a step that waits interleaves with others)')
    return refuse(e, `${ts.SyntaxKind[e.kind]} is not in the subset`)
  }
  // Two values each on its path, as one value on the merged path.
  private joinValues(c: B, qa: Path, va: V, qb: Path, vb: V, at: ts.Node): [V, Path] {
    const tmp = '$join'
    const m = this.merge({...qa, locals: new Map(qa.locals).set(tmp, va)}, {...qb, locals: new Map(qb.locals).set(tmp, vb)}, at)!
    const v = m.locals.get(tmp)!
    m.locals.delete(tmp)
    void c
    return [v, m]
  }
  private name(e: ts.Identifier, p: Path): [V, Path] {
    const local = p.locals.get(e.text)
    if (local) return [local, p]
    if (e.text === 'undefined') return [{t: 'undef'}, p]
    if (e.text === 'Infinity' || e.text === 'NaN') return refuse(e, `${e.text} (the subset's numbers are integers)`)
    const sym = this.s.checker.getSymbolAtLocation(e)
    const decl = sym?.valueDeclaration ?? sym?.declarations?.[0]
    if (decl && ts.isVariableDeclaration(decl) && decl.initializer && decl.getSourceFile() === this.s.sf && ts.isVariableStatement(decl.parent.parent) && decl.parent.parent.parent === this.s.sf) {
      if (!(decl.parent.flags & ts.NodeFlags.Const)) return refuse(e, `${e.text}: a module-level let (state outside the step)`)
      if (ts.isArrowFunction(decl.initializer) || ts.isFunctionExpression(decl.initializer)) return refuse(e, `${e.text}: a function used as a value`)
      // A module-level const: its value, an object read-only (every call shares it).
      const id = `shared.${e.text}`
      if (p.heap.has(id)) return [{t: 'ref', id}, p]
      const [v, q] = this.ev(decl.initializer, {pc: [], locals: new Map(), heap: p.heap, wrote: [], nows: 0})
      if (v.t !== 'ref') return [v, p]
      const share = (heap: Heap, x: V): void => { if (x.t !== 'ref') return; const o = heap.get(x.id); if (o?.k === 'rec') { heap.set(x.id, {...o, origin: 'shared'}); for (const y of o.fields.values()) share(heap, y) } else if (o?.k === 'map') heap.set(x.id, {...o, origin: 'shared'}) }
      const heap = new Map(q.heap)
      share(heap, v)
      heap.set(id, {k: 'alias', to: v})
      return [{t: 'ref', id}, {...p, heap}]
    }
    if (decl && ts.isEnumMember(decl)) return refuse(e, 'an enum')
    if (sym?.declarations?.some(d => ts.isImportSpecifier(d) || ts.isImportClause(d) || ts.isNamespaceImport(d))) return refuse(e, `${e.text}: a name from another module (the extractor reads one file)`)
    if (decl && decl.getSourceFile() !== this.s.sf) return refuse(e, `${e.text}: a name from another module`)
    return refuse(e, `${e.text}: a name the step can't read`)
  }
  private prefix(e: ts.PrefixUnaryExpression, p: Path): [V, Path] {
    if (e.operator === ts.SyntaxKind.PlusPlusToken || e.operator === ts.SyntaxKind.MinusMinusToken) {
      const [old, q] = this.ev(e.operand, p), n = this.num(old, e.operand, q)
      const v: V = {t: 'num', e: e.operator === ts.SyntaxKind.PlusPlusToken ? I.add(n, I.num(1)) : I.sub(n, I.num(1))}
      return [v, this.assign(e.operand, v, q)]
    }
    const [v, q] = this.ev(e.operand, p)
    if (e.operator === ts.SyntaxKind.ExclamationToken) return [{t: 'bool', e: I.not(this.truthy(v, e.operand))}, q]
    if (e.operator === ts.SyntaxKind.MinusToken) return [{t: 'num', e: I.neg(this.num(v, e.operand, q))}, q]
    if (e.operator === ts.SyntaxKind.PlusToken) return [{t: 'num', e: this.num(v, e.operand, q)}, q]
    return refuse(e, 'a bitwise operator (it works on 32-bit integers)')
  }
  private binary(e: ts.BinaryExpression, p: Path): [V, Path] {
    const op = e.operatorToken.kind, S = ts.SyntaxKind
    if (op === S.EqualsToken) { const [v, q] = this.ev(e.right, p); return [v, this.assign(e.left, v, q)] }
    const compound: Partial<Record<ts.SyntaxKind, ts.SyntaxKind>> = {[S.PlusEqualsToken]: S.PlusToken, [S.MinusEqualsToken]: S.MinusToken, [S.AsteriskEqualsToken]: S.AsteriskToken}
    if (compound[op] !== undefined) {
      const [l, q] = this.ev(e.left, p), [r, q2] = this.ev(e.right, q)
      const v = this.arith(compound[op]!, l, r, e, q2)
      return [v, this.assign(e.left, v, q2)]
    }
    if (op === S.QuestionQuestionEqualsToken || op === S.BarBarEqualsToken || op === S.AmpersandAmpersandEqualsToken) return refuse(e, `${e.operatorToken.getText()} (an assignment by cases)`)
    if (op === S.AmpersandAmpersandToken || op === S.BarBarToken || op === S.QuestionQuestionToken) {
      const [l, q] = this.ev(e.left, p)
      const c = op === S.QuestionQuestionToken ? (l.t === 'opt' ? l.has : l.t === 'undef' ? I.F : I.T) : this.truthy(l, e.left)
      // The right side runs only where the left doesn't decide: its effects are on that path alone.
      const [runs, keeps] = op === S.AmpersandAmpersandToken ? [c, I.not(c)] : [I.not(c), c]
      if (runs.op === 'const' && !runs.v) return [op === S.QuestionQuestionToken && l.t === 'opt' ? l.v : l, q]
      const [r, qr] = this.ev(e.right, this.withCond(q, runs))
      const kept = op === S.QuestionQuestionToken && l.t === 'opt' ? l.v : l
      if (keeps.op === 'const' && !keeps.v) return [r, {...qr, pc: q.pc}]
      return this.joinValues(runs, qr, r, this.withCond(q, keeps), kept, e)
    }
    const [l, q] = this.ev(e.left, p), [r, q2] = this.ev(e.right, q)
    const n = (x: V, at: ts.Expression) => this.num(x, at, q2)
    if (op === S.LessThanToken) return [{t: 'bool', e: I.cmp('<', n(l, e.left), n(r, e.right))}, q2]
    if (op === S.LessThanEqualsToken) return [{t: 'bool', e: I.cmp('<=', n(l, e.left), n(r, e.right))}, q2]
    if (op === S.GreaterThanToken) return [{t: 'bool', e: I.cmp('<', n(r, e.right), n(l, e.left))}, q2]
    if (op === S.GreaterThanEqualsToken) return [{t: 'bool', e: I.cmp('<=', n(r, e.right), n(l, e.left))}, q2]
    if (op === S.EqualsEqualsEqualsToken || op === S.EqualsEqualsToken) return [{t: 'bool', e: this.equal(l, r, e)}, q2]
    if (op === S.ExclamationEqualsEqualsToken || op === S.ExclamationEqualsToken) return [{t: 'bool', e: I.not(this.equal(l, r, e))}, q2]
    if (op === S.PlusToken || op === S.MinusToken || op === S.AsteriskToken || op === S.PercentToken) return [this.arith(op, l, r, e, q2), q2]
    if (op === S.SlashToken) return refuse(e, 'a division (its result may be a fraction): Math.floor(x / k) for a constant k is in the subset')
    if (op === S.AsteriskAsteriskToken) return refuse(e, 'a power')
    if (op === S.CommaToken) return [r, q2]
    if (op === S.InKeyword || op === S.InstanceOfKeyword) return refuse(e, e.operatorToken.getText())
    return refuse(e, `${e.operatorToken.getText()} (bitwise operators work on 32-bit integers)`)
  }
  private arith(op: ts.SyntaxKind, l: V, r: V, e: ts.BinaryExpression, p: Path): V {
    const S = ts.SyntaxKind
    if (op === S.PlusToken && (l.t === 'str' || r.t === 'str' || l.t === 'choice' || r.t === 'choice')) return refuse(e, 'a string concatenation')
    const a = this.num(l, e.left, p), b = this.num(r, e.right, p)
    if (op === S.PlusToken) return {t: 'num', e: I.add(a, b)}
    if (op === S.MinusToken) return {t: 'num', e: I.sub(a, b)}
    if (op === S.AsteriskToken) return {t: 'num', e: I.mul(a, b)}
    if (op !== S.PercentToken) return refuse(e, 'an operator not in the subset')
    if (b.op !== 'const' || b.v < 1) return refuse(e, 'a remainder by other than a positive constant')
    return {t: 'num', e: I.modk(b.v, a)}
  }
  private object(e: ts.ObjectLiteralExpression, p: Path): [V, Path] {
    const t = this.s.checker.getTypeAtLocation(e)
    const isMap = !!(this.s.checker.getIndexInfoOfType(t, ts.IndexKind.String) || this.s.checker.getIndexInfoOfType(t, ts.IndexKind.Number)) && !this.s.checker.getPropertiesOfType(t).length
    let q = p
    if (isMap) {
      // A record keyed by strings or numbers, made by spreading another and setting keys: a copy of that map.
      let m: MapObj | undefined
      for (const prop of e.properties) {
        if (ts.isSpreadAssignment(prop)) {
          const [v, q2] = this.ev(prop.expression, q); q = q2
          const src = v.t === 'ref' ? q.heap.get(v.id) : undefined
          if (src?.k !== 'map' || m) return refuse(prop, 'a record made from other than one record it copies')
          m = {...src, origin: 'fresh'}
        } else if (ts.isPropertyAssignment(prop) && ts.isComputedPropertyName(prop.name)) {
          if (!m) return refuse(prop, 'a key set on a record that copies none')
          const [k, q2] = this.ev(prop.name.expression, q), [v, q3] = this.ev(prop.initializer, q2); q = q3
          const id = this.id('map')
          q = {...q, heap: new Map(q.heap).set(id, m)}
          q = this.mapSet(id, this.key(k, prop.name, m.decl), v, prop, q, false)
          m = q.heap.get(id) as MapObj
        } else return refuse(prop, 'a record entry not in the subset')
      }
      if (!m) return refuse(e, 'an empty record as a value (a map that starts with no entries is the state\'s, not a step\'s)')
      const id = this.id('map')
      return [{t: 'ref', id}, {...q, heap: new Map(q.heap).set(id, m)}]
    }
    const fields = new Map<string, V>()
    for (const prop of e.properties) {
      if (ts.isSpreadAssignment(prop)) {
        const [v, q2] = this.ev(prop.expression, q); q = q2
        const src = v.t === 'ref' ? this.obj(q, v.id) : undefined
        if (src?.k !== 'rec') return refuse(prop, 'a spread of other than an object')
        if (src.lazy) return refuse(prop, 'a spread of an untyped value')
        for (const [f, fv] of src.fields) fields.set(f, fv)
      } else if (ts.isPropertyAssignment(prop)) {
        const name = ts.isIdentifier(prop.name) || ts.isStringLiteral(prop.name) ? prop.name.text : refuse(prop, 'a computed field name on an object')
        const [v, q2] = this.ev(prop.initializer, q); q = q2
        fields.set(name, v)
      } else if (ts.isShorthandPropertyAssignment(prop)) {
        const [v, q2] = this.ev(prop.name, q); q = q2
        fields.set(prop.name.text, v)
      } else return refuse(prop, 'a method or accessor in an object')
    }
    const id = this.id('obj')
    return [{t: 'ref', id}, {...q, heap: new Map(q.heap).set(id, {k: 'rec', fields, origin: 'fresh'})}]
  }
  private obj(p: Path, id: string): Obj | undefined {
    let o = p.heap.get(id)
    while (o?.k === 'alias') { const to = o.to; if (to.t !== 'ref') return o; o = p.heap.get(to.id) }
    return o
  }
  private key(v: V, at: ts.Node, m: MapDecl): K {
    if (m.key === 'num') {
      if (v.t !== 'num') return refuse(at, 'a key of other than a number for a map keyed by numbers')
      return {op: 'num', e: v.e}
    }
    if (v.t === 'str') return v.e
    if (v.t === 'choice') return refuse(at, 'a key from a union of literals (give the key as a string input)')
    return refuse(at, 'a key of other than a string for a map keyed by strings')
  }
  // Two values within one path, by a condition.
  phiV(c: B, x: V, y: V, at: ts.Node): V {
    if (x.t === 'num' && y.t === 'num') return {t: 'num', e: I.nite(c, x.e, y.e)}
    if (x.t === 'bool' && y.t === 'bool') return {t: 'bool', e: I.bite(c, x.e, y.e)}
    if (x.t === 'choice' && y.t === 'choice') return {t: 'choice', e: I.lite(c, x.e, y.e), values: x.values}
    if ((x.t === 'choice' || x.t === 'str') && (y.t === 'choice' || y.t === 'str')) {
      if (x.t === 'str' && y.t === 'str') return {t: 'str', e: I.kite(c, x.e, y.e)}
      const values = x.t === 'choice' ? x.values : (y as {values: string[]}).values
      return {t: 'choice', e: I.lite(c, this.asChoice(x, values, at), this.asChoice(y, values, at)), values}
    }
    if (x.t === 'undef' && y.t === 'undef') return x
    if (x.t === 'opt' || y.t === 'opt' || x.t === 'undef' || y.t === 'undef') {
      const [hx, vx] = x.t === 'opt' ? [x.has, x.v] : x.t === 'undef' ? [I.F, undefined] : [I.T, x]
      const [hy, vy] = y.t === 'opt' ? [y.has, y.v] : y.t === 'undef' ? [I.F, undefined] : [I.T, y]
      return {t: 'opt', has: I.bite(c, hx, hy), v: !vx ? vy! : !vy ? vx : this.phiV(c, vx, vy, at)}
    }
    if (x.t === 'ref' && y.t === 'ref' && x.id === y.id) return x
    const refs = ['ref', 'cell', 'phi']
    if (refs.includes(x.t) && refs.includes(y.t)) return {t: 'phi', c, a: x, b: y}
    return refuse(at, `a value that is a ${x.t} or a ${y.t} by a condition`)
  }
  // A field of a value: a record's, a cell's (through its map), or one an untyped record grows.
  field(v: V, f: string, at: ts.Node, p: Path): [V, Path] {
    v = this.deref(p, v)
    if (v.t === 'phi') {
      const [fa, p1] = this.field(v.a, f, at, p), [fb, p2] = this.field(v.b, f, at, p1)
      return [this.phiV(v.c, fa, fb, at), p2]
    }
    if (v.t === 'opt') {
      if (this.known(p, v.has)) return this.field(v.v, f, at, p)
      return refuse(at, `${text(at)} reads a field of a value that may be missing`)
    }
    if (v.t === 'cell') {
      const mo = p.heap.get(v.map) as MapObj
      if (mo.gen !== v.gen) return refuse(at, `${text(at)}: a reference into ${mo.decl.name} read before the map was set`)
      const cell = this.readCell(mo, v.key)
      const x = cell.vals.get(f)
      return x ? [x, p] : refuse(at, `no field ${f}`)
    }
    if (v.t !== 'ref') return refuse(at, `${text(at)}: a field of a ${v.t}`)
    const o = this.obj(p, v.id)
    if (o?.k !== 'rec') return refuse(at, `${text(at)}: a field of a map`)
    const x = o.fields.get(f)
    if (x) return [x, p]
    if (o.lazy) {
      // Its sort: compared with literals, a choice among them; else its type where it has one (an XState event's
      // payload, typed by setup's types); else a number.
      const typed = (() => { const t = this.s.checker.getTypeAtLocation(at); if (t.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)) return undefined; const sh = shapeOf(t, this.s.checker, at); return sh.k === 'num' || sh.k === 'bool' || sh.k === 'choice' || sh.k === 'str' ? sh : undefined })()
      const path = `${o.lazy.prefix}${f}`, sort = this.s.lazySorts.get(path) ?? typed ?? {k: 'num'}
      // The same field read again (in another guard or action, say) is the same input.
      const seen = [...this.s.lazy].find(([, l]) => l.prefix === o.lazy!.prefix && l.field === f)?.[0]
      const nvar = seen ? this.s.vars.get(seen)! : this.newVar(path, sort, 'input'), nv = Exec.valueOf(nvar)
      this.s.lazy.set(nvar.name, {prefix: o.lazy.prefix, field: f})
      const fields = new Map(o.fields).set(f, nv)
      return [nv, {...p, heap: new Map(p.heap).set(v.id, {...o, fields})}]
    }
    if (v.id === 'this' && this.s.cls) {
      const member = this.s.cls.members.find(m => m.name && memberName(m.name) === f)
      if (member && ts.isGetAccessorDeclaration(member)) return this.inline({decl: member, self: 'this'}, [], at, p)
      if (member && ts.isMethodDeclaration(member)) return refuse(at, `the method ${f} as a value`)
    }
    return refuse(at, `${text(at)}: no field ${f} the step can read`)
  }
  readCell(m: MapObj, key: K): {has: B, vals: Map<string, V>} {
    const base = this.baseCell(m.decl, key)
    if (!m.w) return base
    const c = I.keq(key, m.w.key)
    return {has: I.bite(c, m.w.has, base.has), vals: new Map([...base.vals].map(([f, v]) => [f, this.mergeScalar(c, m.w!.vals.get(f)!, v, undefined as never)]))}
  }
  private access(e: ts.PropertyAccessExpression | ts.ElementAccessExpression, p: Path): [V, Path] {
    if (e.questionDotToken) return refuse(e, 'optional chaining')
    const [base, q] = this.ev(e.expression, p)
    if (ts.isPropertyAccessExpression(e)) {
      const f = memberName(e.name)
      if (base.t === 'ref') { const o = this.obj(q, base.id); if (o?.k === 'map') return refuse(e, `${f} of a map (get, set, has and delete are in the subset)`) }
      if (f === 'length') return refuse(e, 'length (lists and strings are not in the subset yet)')
      return this.field(base, f, e, q)
    }
    const arg = e.argumentExpression
    const b = this.deref(q, base)
    if (b.t === 'ref') {
      const o = this.obj(q, b.id)
      if (o?.k === 'map') {
        if (o.decl.js !== 'record') return refuse(e, 'a Map read with [ ] (get is how a Map is read)')
        const [k, q2] = this.ev(arg, q)
        return [this.mapGet(b.id, this.key(k, arg, o.decl), q2), q2]
      }
    }
    if (ts.isStringLiteral(arg)) return this.field(base, arg.text, e, q)
    return refuse(e, 'an index into other than a record keyed by strings or numbers')
  }
  private mapGet(id: string, key: K, p: Path): V {
    const m = this.obj(p, id) as MapObj, cell = this.readCell(m, key)
    if (m.decl.scalar) return {t: 'opt', has: cell.has, v: cell.vals.get('value')!}
    return {t: 'opt', has: cell.has, v: {t: 'cell', map: this.mapId(p, id), key, gen: m.gen}}
  }
  private mapId(p: Path, id: string): string {
    let o = p.heap.get(id)
    while (o?.k === 'alias' && o.to.t === 'ref') { id = o.to.id; o = p.heap.get(id) }
    return id
  }
  // A map written at a key: one key a step (a rule's map takes one write a step).
  mapSet(id: string, key: K, v: V | undefined, at: ts.Node, p: Path, track = true): Path {
    id = this.mapId(p, id)
    const m = p.heap.get(id) as MapObj
    if (m.origin === 'input') return refuse(at, `writes to ${m.decl.name} in the state it was given (React and Redux keep the old state; copy it first)`)
    if (m.origin === 'shared') return refuse(at, 'writes to a module-level map (every call shares it)')
    if (m.w && !I.same(m.w.key, key)) return refuse(at, `writes ${m.decl.name} at a second key in one step (a rule's map takes one write a step)`)
    let vals: Map<string, V>, has: B = I.T
    if (v === undefined) { vals = new Map(m.decl.fields.map(f => [f.name, Exec.defaultOf(f.sort)])); has = I.F }
    else if (m.decl.scalar) vals = new Map([['value', this.cellValue(v, m.decl.fields[0]!, at, p)]])
    else {
      const src = this.deref(p, v)
      let fields: Map<string, V>
      if (src.t === 'ref') { const o = this.obj(p, src.id); if (o?.k !== 'rec') return refuse(at, 'a map set to other than an object'); fields = o.fields }
      else if (src.t === 'cell') fields = this.readCell(p.heap.get(src.map) as MapObj, src.key).vals
      else return refuse(at, 'a map of objects set to other than an object')
      vals = new Map(m.decl.fields.map(f => { const x = fields.get(f.name); return [f.name, x ? this.cellValue(x, f, at, p) : refuse(at, `the value set has no ${f.name}`)] }))
      if (fields.size !== m.decl.fields.length) refuse(at, 'the value set has fields the map\'s values don\'t')
    }
    const gen = m.gen + 1, heap = new Map(p.heap).set(id, {...m, gen, w: {key, has, vals}})
    // The object set becomes the cell (a write through it later writes the map).
    if (v && !m.decl.scalar) { const src = v.t === 'ref' ? this.mapId(p, v.id) : undefined; if (src && heap.get(src)?.k === 'rec' && (heap.get(src) as Rec).origin === 'fresh') heap.set(src, {k: 'alias', to: {t: 'cell', map: id, key, gen}}) }
    return {...p, heap, wrote: track && m.origin === 'this' ? [...new Set([...p.wrote, m.decl.name])] : p.wrote}
  }
  private cellValue(v: V, f: Var, at: ts.Node, p: Path): V {
    switch (f.sort.k) {
      case 'num': return {t: 'num', e: this.num(v, at, p)}
      case 'bool': return {t: 'bool', e: this.bool(v, at)}
      case 'choice': return {t: 'choice', e: this.asChoice(v, f.sort.values, at), values: f.sort.values}
      case 'str': return refuse(at, 'a string in a map')
    }
  }
  // Assignment: to a local, a field (of this, or of an object the step made), a map's key, or through a cell.
  assign(target: ts.Expression, v: V, p: Path): Path {
    if (ts.isParenthesizedExpression(target)) return this.assign(target.expression, v, p)
    if (ts.isIdentifier(target)) {
      if (!p.locals.has(target.text)) return refuse(target, `${target.text}: an assignment to a name outside the step`)
      const sym = this.s.checker.getSymbolAtLocation(target), decl = sym?.valueDeclaration
      if (decl && ts.isVariableDeclaration(decl) && decl.parent.flags & ts.NodeFlags.Const) return refuse(target, `${target.text} is a const`)
      this.hint(v, target.text)
      return {...p, locals: new Map(p.locals).set(target.text, v)}
    }
    if (ts.isPropertyAccessExpression(target) || ts.isElementAccessExpression(target)) {
      const [base, q] = this.ev(target.expression, p)
      const b = this.deref(q, base)
      if (ts.isElementAccessExpression(target) && b.t === 'ref') {
        const o = this.obj(q, b.id)
        if (o?.k === 'map') {
          const [k, q2] = this.ev(target.argumentExpression, q)
          return this.mapSet(b.id, this.key(k, target.argumentExpression, o.decl), v, target, q2)
        }
      }
      const f = ts.isPropertyAccessExpression(target) ? memberName(target.name) : ts.isStringLiteral(target.argumentExpression) ? target.argumentExpression.text : refuse(target, 'an assignment through a computed key')
      return this.writeField(b, f, v, q, target)
    }
    return refuse(target, 'an assignment to other than a name, a field or a key')
  }
  // A field written: an object's, a cell's (its map's at the key), or each of two objects' where it is the one.
  private writeField(b: V, f: string, v: V, q: Path, target: ts.Node): Path {
      b = this.deref(q, b)
      if (b.t === 'opt') { if (!this.known(q, b.has)) return refuse(target, `${text(target)} writes a field of a value that may be missing`); return this.writeField(b.v, f, v, q, target) }
      if (b.t === 'phi') {
        const [oldA] = this.field(b.a, f, target, q), q1 = this.writeField(b.a, f, this.phiV(b.c, v, oldA, target), q, target)
        const [oldB] = this.field(b.b, f, target, q1)
        return this.writeField(b.b, f, this.phiV(b.c, oldB, v, target), q1, target)
      }
      if (b.t === 'cell') {
        const m = q.heap.get(b.map) as MapObj
        if (m.gen !== b.gen) return refuse(target, `a write through a reference into ${m.decl.name} read before the map was set`)
        const cell = this.readCell(m, b.key), fv = m.decl.fields.find(x => x.name === f) ?? refuse(target, `no field ${f}`)
        const vals = new Map(cell.vals).set(f, this.cellValue(v, fv, target, q))
        if (m.origin === 'input' || m.origin === 'shared') return refuse(target, `writes to ${m.decl.name} in ${m.origin === 'input' ? 'the state it was given (React and Redux keep the old state; copy it first)' : 'a module-level map every call shares'}`)
        if (m.w && !I.same(m.w.key, b.key)) return refuse(target, `writes ${m.decl.name} at a second key in one step`)
        const gen = m.gen
        return {...q, heap: new Map(q.heap).set(b.map, {...m, gen, w: {key: b.key, has: I.T, vals}}), wrote: m.origin === 'this' ? [...new Set([...q.wrote, m.decl.name])] : q.wrote}
      }
      if (b.t !== 'ref') return refuse(target, `an assignment to a field of a ${b.t}`)
      const id = this.mapId(q, b.id), o = q.heap.get(id)
      if (o?.k !== 'rec') return refuse(target, 'an assignment to a map\'s field')
      if (o.origin === 'input') return refuse(target, `writes ${text(target)} in the state it was given (React and Redux keep the old state, and a state returned as the same object reads as unchanged)`)
      if (o.origin === 'shared') return refuse(target, `writes ${text(target)}, a module-level object every call shares`)
      if (!o.fields.has(f)) return refuse(target, `a field ${f} the object doesn't have`)
      const old = o.fields.get(f)!
      if (old.t === 'ref' && v.t !== 'ref') return refuse(target, `${f} set to other than an object`)
      if (old.t === 'ref' && v.t === 'ref') { const om = this.obj(q, old.id); if (om?.k === 'map') return refuse(target, `${f}: a map replaced in a step (clearing every key is not in the subset yet)`) }
      const heap = new Map(q.heap).set(id, {...o, fields: new Map(o.fields).set(f, v)})
      return {...q, heap, wrote: o.origin === 'this' ? [...new Set([...q.wrote, f])] : q.wrote}
  }

  // --- calls -----------------------------------------------------------------------------------------------------
  private args(xs: readonly ts.Expression[], p: Path): [V[], Path] {
    const out: V[] = []
    let q = p
    for (const x of xs) { if (ts.isSpreadElement(x)) refuse(x, 'a spread argument'); const [v, q2] = this.ev(x, q); out.push(v); q = q2 }
    return [out, q]
  }
  private call(e: ts.CallExpression, p: Path): [V, Path] {
    if (e.questionDotToken) return refuse(e, 'optional chaining')
    const callee = e.expression
    if (ts.isPropertyAccessExpression(callee)) {
      const obj = callee.expression, m = memberName(callee.name)
      if (ts.isIdentifier(obj) && obj.text === 'Math' && !p.locals.has('Math')) return this.math(m, e, p)
      if (ts.isIdentifier(obj) && obj.text === 'Date' && m === 'now' && !p.locals.has('Date')) return this.now(e, p)
      if (ts.isIdentifier(obj) && obj.text === 'console' && !p.locals.has('console')) {
        if (e.arguments.some(impure)) return refuse(e, 'console output with effects')
        this.s.notes.add('console output is left out (it writes nothing the rule keeps)')
        return [{t: 'undef'}, p]
      }
      if (ts.isIdentifier(obj) && ['Number', 'Object', 'JSON', 'Array', 'String', 'Promise', 'performance'].includes(obj.text)) return refuse(e, `${obj.text}.${m}`)
      if (obj.kind === ts.SyntaxKind.ThisKeyword && this.s.cls) {
        const member = this.s.cls.members.find(x => x.name && memberName(x.name) === m)
        if (member && ts.isMethodDeclaration(member)) { const [args, q] = this.args(e.arguments, p); return this.inline({decl: member, self: 'this'}, args, e, q) }
      }
      const [base, q] = this.ev(obj, p), b = this.deref(q, base)
      const o = b.t === 'ref' ? this.obj(q, b.id) : undefined
      if (o?.k === 'map' && b.t === 'ref') {
        const [args, q2] = this.args(e.arguments, q)
        const k = () => this.key(args[0] ?? refuse(e, `${m} with no key`), e.arguments[0]!, o.decl)
        switch (m) {
          case 'get': return [this.mapGet(b.id, k(), q2), q2]
          case 'has': return [{t: 'bool', e: this.readCell(o, k()).has}, q2]
          case 'set': return [b, this.mapSet(b.id, k(), args[1] ?? refuse(e, 'set with no value'), e, q2)]
          case 'delete': { const had = this.readCell(o, k()).has; return [{t: 'bool', e: had}, this.mapSet(b.id, k(), undefined, e, q2)] }
          default: return refuse(e, `the map method ${m} (get, set, has and delete are in the subset)`)
        }
      }
      return refuse(e, `${text(callee)}: a method the subset doesn't read`)
    }
    if (ts.isIdentifier(callee)) {
      const sym = this.s.checker.getSymbolAtLocation(callee), decl = sym?.valueDeclaration
      const fn = decl && ts.isFunctionDeclaration(decl) ? decl : decl && ts.isVariableDeclaration(decl) && decl.initializer && (ts.isArrowFunction(decl.initializer) || ts.isFunctionExpression(decl.initializer)) ? decl.initializer : undefined
      if (fn && fn.getSourceFile() === this.s.sf) { const [args, q] = this.args(e.arguments, p); return this.inline({decl: fn}, args, e, q) }
      if (decl && decl.getSourceFile() !== this.s.sf) return refuse(e, `${callee.text}: a function from another module`)
      return refuse(e, `${callee.text}: a call the subset doesn't read`)
    }
    return refuse(e, 'a call the subset doesn\'t read')
  }
  private math(m: string, e: ts.CallExpression, p: Path): [V, Path] {
    if (m === 'floor' || m === 'ceil') {
      const a = e.arguments[0]
      const strip = (x: ts.Expression): ts.Expression => (ts.isParenthesizedExpression(x) ? strip(x.expression) : x)
      const d = a && strip(a)
      if (!d || e.arguments.length !== 1) return refuse(e, `Math.${m} of other than one argument`)
      if (ts.isBinaryExpression(d) && d.operatorToken.kind === ts.SyntaxKind.SlashToken) {
        const [x, q] = this.ev(d.left, p), [k, q2] = this.ev(d.right, q)
        const kn = this.num(k, d.right, q2)
        if (kn.op !== 'const' || kn.v < 1) return refuse(d.right, `Math.${m}(x / k) by other than a positive constant`)
        const xn = this.num(x, d.left, q2)
        return [{t: 'num', e: m === 'floor' ? I.divk(kn.v, xn) : I.neg(I.divk(kn.v, I.neg(xn)))}, q2]
      }
      // Of an integer, its value.
      const [x, q] = this.ev(d, p)
      return [{t: 'num', e: this.num(x, d, q)}, q]
    }
    if (m === 'min' || m === 'max') {
      if (e.arguments.length < 1) return refuse(e, `Math.${m}() of nothing`)
      const [args, q] = this.args(e.arguments, p), ns = args.map((a, i) => this.num(a, e.arguments[i]!, q))
      return [{t: 'num', e: ns.slice(1).reduce((acc, n) => (m === 'min' ? I.nmin(acc, n) : I.nmax(acc, n)), ns[0]!)}, q]
    }
    if (m === 'abs') {
      const [args, q] = this.args(e.arguments, p), x = this.num(args[0] ?? refuse(e, 'Math.abs()'), e.arguments[0]!, q)
      return [{t: 'num', e: I.nite(I.cmp('<', x, I.num(0)), I.neg(x), x)}, q]
    }
    if (m === 'random') return refuse(e, 'Math.random (a step the code takes differently each time)')
    return refuse(e, `Math.${m} (Math.min, Math.max, Math.abs, and Math.floor or Math.ceil of x / k are in the subset)`)
  }
  private now(e: ts.CallExpression, p: Path): [V, Path] {
    if (p.nows > 0) return refuse(e, 'Date.now() read twice in one step (the two reads may differ: read it once into a local)')
    if (!this.s.now) {
      this.s.now = this.fresh(this.s.nowRole === 'param' ? 'now0' : 'now')
      this.s.vars.set(this.s.now, {name: this.s.now, sort: {k: 'num'}, role: this.s.nowRole, note: this.s.nowRole === 'param' ? 'Date.now() when the object is made' : 'Date.now(): any time, not only one later than the last (the proof covers every clock)'})
    }
    return [{t: 'num', e: I.nvar(this.s.now)}, {...p, nows: p.nows + 1}]
  }
  private newExpr(e: ts.NewExpression, p: Path): [V, Path] {
    const c = e.expression
    if (ts.isIdentifier(c) && c.text === 'Map') {
      const a = e.arguments ?? []
      if (a.length !== 1) return refuse(e, 'a new Map in a step (clearing every key is not in the subset yet)')
      const [v, q] = this.ev(a[0]!, p), src = v.t === 'ref' ? this.obj(q, v.id) : undefined
      if (src?.k !== 'map') return refuse(e, 'a new Map of other than a map')
      const id = this.id('map')
      return [{t: 'ref', id}, {...q, heap: new Map(q.heap).set(id, {...src, origin: 'fresh'})}]
    }
    if (ts.isIdentifier(c) && c.text === 'Date') return refuse(e, 'new Date() (Date.now() is how the subset reads the time)')
    return refuse(e, `new ${text(c)}`)
  }
  // A function of the same module, or a method or getter of the class, run where it is called.
  inline(f: Callable, args: V[], at: ts.Node, p: Path): [V, Path] {
    if (++this.depth > 24) return refuse(at, 'calls nested too deep (recursion is not in the subset)')
    try {
      const d = f.decl
      if (ts.isMethodDeclaration(d) || ts.isFunctionDeclaration(d)) if (d.modifiers?.some(m => m.kind === ts.SyntaxKind.AsyncKeyword) || d.asteriskToken) return refuse(at, 'an async or generator function')
      if (!d.body) return refuse(at, 'a function without a body')
      let q: Path = {...p, locals: new Map()}
      d.parameters.forEach((param, i) => {
        if (param.dotDotDotToken) refuse(param, 'a rest parameter')
        let v = args[i]
        if (v === undefined) { if (!param.initializer) refuse(at, 'a call with fewer arguments than the function takes'); const [dv, q2] = this.ev(param.initializer!, q); v = dv; q = q2 }
        q = this.bind(param.name, v, q)
      })
      if (!ts.isBlock(d.body)) { const [v, q2] = this.ev(d.body, q); return [v, {...q2, locals: p.locals}] }
      const flow = this.block(d.body.statements, q)
      const outs: [Path, V][] = [...flow.rets, ...(flow.live ? [[flow.live, {t: 'undef'} as V] as [Path, V]] : [])]
      if (!outs.length) return [{t: 'undef'}, {...p, pc: [...p.pc, I.F]}]
      const [first, ...rest] = outs
      let [mp, mv] = first!
      for (const [rp, rv] of rest) [mv, mp] = this.joinValues(I.T, mp, mv, rp, rv, at)
      return [mv, {...mp, locals: p.locals}]
    } finally { this.depth-- }
  }
}

// A map set on one path and not the other: a generation of its own, so a reference read before either is stale.
const mergedGen = (a: MapObj, b: MapObj) => (a.gen === b.gen ? a.gen : Math.max(a.gen, b.gen) + 1)
// Names JavaScript itself declares, and those a rule's builders hand out beside the code's.
const RESERVED = new Set(['event', 'in', 'last', 'key', 'value', 'has', 'constructor', 'prototype', '__proto__', 'Math', 'Date', 'Int', 'when', 'min', 'max', 'all', 'any', 'not', 'yes', 'no', 'lit', 'intern', 'nat', 'int', 'bool', 'oneOf', 'str', 'record', 'rule', 'p', 'fromXState'])
export const memberName = (n: ts.PropertyName | ts.MemberName): string => (ts.isIdentifier(n) || ts.isPrivateIdentifier(n) || ts.isStringLiteral(n) || ts.isNumericLiteral(n) ? n.text : n.getText())
const boundNames = (n: ts.BindingName): string[] => (ts.isIdentifier(n) ? [n.text] : n.elements.flatMap(el => (ts.isOmittedExpression(el) ? [] : boundNames(el.name))))
// Whether an expression may have effects (an assignment, an increment, a call other than an error's constructor).
export function impure(e: ts.Node): boolean {
  let found = false
  const visit = (n: ts.Node) => {
    if (found) return
    if (ts.isBinaryExpression(n) && n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment && n.operatorToken.kind <= ts.SyntaxKind.LastAssignment) found = true
    else if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) && (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken)) found = true
    else if (ts.isCallExpression(n) && !(ts.isIdentifier(n.expression) && /Error$/.test(n.expression.text))) found = true
    else if (ts.isNewExpression(n) && !(ts.isIdentifier(n.expression) && /Error$/.test(n.expression.text))) found = true
    else if (ts.isPropertyAccessExpression(n) && !ts.isCallExpression(n.parent)) {
      // A getter may run code: only reads of plain names, `this.x` and `obj.x` are taken as pure.
      ts.forEachChild(n, visit)
    } else ts.forEachChild(n, visit)
  }
  visit(e)
  return found
}
export type {V, Path, Rec, MapObj, Heap, Flow}
