// The shapes the extractor reads (core/extract.ts): step functions over a state (a reducer `(state, action) => state`,
// `useReducer`'s, or several functions over one record, each an event), and classes whose methods write their fields
// (each public method an event, its arguments the request, its result kept as `<method>_result`). Each is executed
// symbolically (core/extract-read.ts) into a Model: the state's variables, where each sits in the code's own values,
// the step's writes, what the code refuses (its throws) and how a request is made of the code.
import ts from 'typescript'
import * as I from './extract-ir.ts'
import type {B} from './extract-ir.ts'
import {type Arg, type Event, Exec, type Heap, type Layout, type MapDecl, type MapObj, type Model, type Path, type Rec, Refusal, Retype, type Setup, type Shape, type Sort, type Term, type V, type Var, memberName, normalize, program, shapeOf} from './extract-read.ts'

export type ReadOptions = {
  entry: string,
  // Other files of the repository the entry's relative imports name (by their path beside the entry's).
  files?: Record<string, string>,
  // Sorts of untyped inputs (a JavaScript action's fields), by their path: found by the reader itself (Retype).
  typed?: Record<string, Sort>,
  // Several functions over one record, each an event (the entry is the first).
  functions?: string[],
  // The methods that are events (by default every public one).
  methods?: string[],
  // The initial state, where the code doesn't give one (a default parameter, useReducer's argument, `initialState`).
  init?: unknown,
}
const at0 = (sf: ts.SourceFile): ts.Node => sf.statements[0] ?? sf
const where = (n: ts.Node) => { const sf = n.getSourceFile(), {line, character} = sf.getLineAndCharacterOfPosition(n.getStart()); return `${sf.fileName.split('/').pop()}:${line + 1}:${character + 1}` }
const refuse = (n: ts.Node, what: string): never => { throw new Refusal(where(n), what) }

function setupOf(code: string, file: string, typed: Record<string, Sort> = {}, files: Record<string, string> = {}): Setup {
  const root = file.slice(0, file.length - (file.split('/').pop()!.length)), extra = Object.fromEntries(Object.entries(files).map(([p, c]) => [normalize(`${root}${p}`), c]))
  const {sf, checker} = program(code, file, extra)
  return {ours: f => f === sf || f.fileName in extra, checker, sf, names: new Set(), vars: new Map(), maps: new Map(), lazySorts: new Map(Object.entries(typed)), nowRole: 'input', hints: new WeakMap(), notes: new Set(), lazy: new Map()}
}

// The state's tree: a variable per scalar, a heap object per record, a map per keyed field.
function build(ex: Exec, shape: Shape, path: string[], heap: Heap, origin: Rec['origin'], at: ts.Node): {layout: Layout, v: V} {
  const name = path.join('_') || 'state'
  switch (shape.k) {
    case 'num': case 'bool': case 'choice': { const x = ex.newVar(name, shape, 'state'); return {layout: {k: 'scalar', name: x.name}, v: Exec.valueOf(x)} }
    // A string: compared for equality and set (str(), interned), nothing else read of it.
    case 'str': { const x = ex.newVar(name, shape, 'state'); return {layout: {k: 'scalar', name: x.name}, v: Exec.valueOf(x)} }
    case 'rec': {
      const fields = new Map<string, V>(), layout: [string, Layout][] = []
      for (const [f, s] of shape.fields) { const r = build(ex, s, [...path, f], heap, origin, at); fields.set(f, r.v); layout.push([f, r.layout]) }
      const id = path.length ? `${origin}.${path.join('.')}` : origin === 'this' ? 'this' : 'state'
      heap.set(id, {k: 'rec', fields, origin})
      return {layout: {k: 'rec', fields: layout}, v: {t: 'ref', id}}
    }
    case 'map': {
      const decl = mapDecl(ex, shape, name, at), id = `${origin}.${path.join('.')}`
      heap.set(id, {k: 'map', base: decl.name, decl, origin, gen: 0})
      return {layout: {k: 'map', name: decl.name}, v: {t: 'ref', id}}
    }
  }
}
function mapDecl(ex: Exec, shape: Extract<Shape, {k: 'map'}>, name: string, at: ts.Node): MapDecl {
  const scalar = shape.val.k !== 'rec'
  const fields: Var[] = shape.val.k === 'rec' ? shape.val.fields.map(([f, s]) => {
    if (s.k !== 'num' && s.k !== 'bool' && s.k !== 'choice') return refuse(at, `${name}: a map whose values hold ${s.k === 'str' ? 'a string' : 'a nested value'} in ${f}`)
    if (f === 'has') return refuse(at, `${name}: a map value with a field named has (the rule keeps whether a key is there under that name)`)
    return {name: f, sort: s, role: 'state'}
  }) : [{name: 'value', sort: shape.val.k === 'num' || shape.val.k === 'bool' || shape.val.k === 'choice' ? shape.val : refuse(at, `${name}: a map of ${shape.val.k === 'str' ? 'strings' : 'maps'}`), role: 'state'}]
  const decl: MapDecl = {name: ex.fresh(name), key: shape.key, fields, scalar, js: shape.js}
  ex.s.maps.set(decl.name, decl)
  return decl
}

// --- values back into the state's tree ------------------------------------------------------------------------------
type StateVal = {leaves: Map<string, V>, maps: Map<string, MapObj['w']>}
function materialize(ex: Exec, v: V, layout: Layout, p: Path, at: ts.Node, out: StateVal = {leaves: new Map(), maps: new Map()}): StateVal {
  const deref = (x: V): V => { while (x.t === 'ref') { const o = p.heap.get(x.id); if (o?.k !== 'alias') break; x = o.to } return x }
  v = deref(v)
  if (v.t === 'phi' && layout.k !== 'scalar') {
    // One of two objects by a condition: each side's state, by the condition.
    const a = materialize(ex, v.a, layout, p, at), b = materialize(ex, v.b, layout, p, at), both = mergeVals(ex, v.c, a, b, at)
    for (const [n, x] of both.leaves) out.leaves.set(n, x)
    for (const [n, w] of both.maps) out.maps.set(n, w)
    return out
  }
  switch (layout.k) {
    case 'scalar': {
      const sort = ex.s.vars.get(layout.name)!.sort
      if (v.t === 'opt') { if (!ex.known(p, v.has)) refuse(at, `${layout.name} may be set to undefined`); v = v.v }
      const ok = (sort.k === 'num' && v.t === 'num') || (sort.k === 'bool' && v.t === 'bool') || (sort.k === 'choice' && (v.t === 'choice' || v.t === 'str')) || (sort.k === 'str' && v.t === 'str')
      if (!ok) {
        // An untyped input written here: of this field's sort, and the step read again.
        const e = v.t === 'num' || v.t === 'bool' ? v.e : v.t === 'str' ? v.e : undefined
        const name = e && (e.op === 'var' || e.op === 'svar') ? e.name : undefined, lz = name ? ex.s.lazy.get(name) : undefined
        if (lz && !ex.s.lazySorts.has(`${lz.prefix}${lz.field}`)) throw new Retype(`${lz.prefix}${lz.field}`, sort)
        refuse(at, `${layout.name} is set to a ${v.t}`)
      }
      out.leaves.set(layout.name, sort.k === 'choice' ? {t: 'choice', e: ex.asChoice(v, sort.values, at), values: sort.values} : v)
      return out
    }
    case 'rec': {
      if (v.t === 'cell') return refuse(at, 'a state made of a map cell')
      const o = v.t === 'ref' ? p.heap.get(v.id) : undefined
      if (o?.k !== 'rec') return refuse(at, `returns ${v.t === 'undef' ? 'undefined' : 'other than the state\'s record'} on some path`)
      for (const f of o.fields.keys()) if (!layout.fields.some(([g]) => g === f)) refuse(at, `returns a state with a field ${f} its type doesn't have`)
      for (const [f, sub] of layout.fields) materialize(ex, o.fields.get(f) ?? refuse(at, `returns a state without ${f}`), sub, p, at, out)
      return out
    }
    case 'map': {
      const o = v.t === 'ref' ? p.heap.get(v.id) : undefined
      if (o?.k !== 'map' || o.base !== layout.name) return refuse(at, `${layout.name} is set to other than a copy of itself (a map replaced whole is not in the subset)`)
      out.maps.set(layout.name, o.w)
      return out
    }
    case 'const': return out
  }
}
const strip = (p: Path): Path => ({pc: p.pc, locals: new Map(), heap: new Map(), wrote: [], nows: p.nows})
// The condition that tells two paths apart (as Exec.merge reads it).
function split(a: Path, b: Path): B {
  let i = 0
  while (i < a.pc.length && i < b.pc.length && a.pc[i] === b.pc[i]) i++
  const ra = a.pc.slice(i), rb = b.pc.slice(i)
  return ra.length ? I.and(...ra) : I.not(I.and(...rb))
}
function mergeVals(ex: Exec, c: B, a: StateVal, b: StateVal, at: ts.Node): StateVal {
  const leaves = new Map([...a.leaves].map(([n, v]) => [n, ex.mergeScalar(c, v, b.leaves.get(n)!, at)]))
  const maps = new Map([...a.maps].map(([n, w]) => [n, ex.mergeWrites(c, ex.s.maps.get(n)!, w, b.maps.get(n), at)]))
  return {leaves, maps}
}
// Every way a step ends (each a path and its state), as one state by cases.
function joinAll(ex: Exec, outs: [Path, StateVal][], at: ts.Node): StateVal {
  if (!outs.length) return refuse(at, 'no path through the step returns')
  let [pa, acc] = outs.at(-1)!
  for (let i = outs.length - 2; i >= 0; i--) {
    const [p, sv] = outs[i]!
    acc = mergeVals(ex, split(p, pa), sv, acc, at)
    pa = ex.merge(strip(p), strip(pa), at)!
  }
  return acc
}
const termOf = (v: V): Term => (v.t === 'num' ? {s: 'num', e: v.e} : v.t === 'bool' ? {s: 'bool', e: v.e} : v.t === 'choice' ? {s: 'choice', e: v.e} : v.t === 'str' ? {s: 'str', e: v.e} : (() => { throw new Error(`a ${v.t} as a term`) })())
const sameTerm = (a: V, b: V) => (a.t === 'num' || a.t === 'bool' || a.t === 'choice' || a.t === 'str') && (b.t === 'num' || b.t === 'bool' || b.t === 'choice' || b.t === 'str') && I.same(a.e, b.e)
const refusalOf = (ex: Exec): B => I.or(...ex.throws.map(t => I.and(...t.pc)))

// --- the initial state, as the code writes it -----------------------------------------------------------------------
type Raw = number | boolean | string | {[k: string]: Raw} | typeof EMPTY
const EMPTY = Symbol('an empty map')
function constValue(e: ts.Expression, s: Setup): Raw {
  if (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isSatisfiesExpression(e)) return constValue(e.expression, s)
  if (ts.isNumericLiteral(e)) { const x = Number(e.text); return Number.isSafeInteger(x) ? x : refuse(e, `${e.text}: not a safe integer`) }
  if (ts.isPrefixUnaryExpression(e) && e.operator === ts.SyntaxKind.MinusToken) { const x = constValue(e.operand, s); return typeof x === 'number' ? -x : refuse(e, 'a negated non-number') }
  if (ts.isStringLiteral(e) || ts.isNoSubstitutionTemplateLiteral(e)) return e.text
  if (e.kind === ts.SyntaxKind.TrueKeyword) return true
  if (e.kind === ts.SyntaxKind.FalseKeyword) return false
  if (ts.isNewExpression(e) && ts.isIdentifier(e.expression) && e.expression.text === 'Map' && !e.arguments?.length) return EMPTY
  if (ts.isObjectLiteralExpression(e)) {
    const out: {[k: string]: Raw} = {}
    for (const p of e.properties) {
      if (ts.isPropertyAssignment(p) && (ts.isIdentifier(p.name) || ts.isStringLiteral(p.name))) out[p.name.text] = constValue(p.initializer, s)
      else if (ts.isShorthandPropertyAssignment(p)) out[p.name.text] = constValue(p.name, s)
      else if (ts.isSpreadAssignment(p)) { const x = constValue(p.expression, s); if (typeof x !== 'object') refuse(p, 'a spread of other than an object'); Object.assign(out, x) }
      else refuse(p, 'an initial state entry the subset doesn\'t read')
    }
    return out
  }
  if (ts.isPropertyAccessExpression(e)) {
    // A field of a const's object literal: that field's own initializer (the others aren't read).
    const lit = literalOf(e.expression, s)
    const prop = lit && ts.isObjectLiteralExpression(lit) ? lit.properties.find((x): x is ts.PropertyAssignment => ts.isPropertyAssignment(x) && x.name.getText() === e.name.text) : undefined
    if (!prop) return refuse(e, `${e.getText()}: an initial state the subset can't read (give it in init)`)
    return constValue(prop.initializer, s)
  }
  if (ts.isArrayLiteralExpression(e)) return refuse(e, 'an array (lists are not in the subset yet)')
  if (ts.isIdentifier(e)) {
    const decl = aliased(s, e)?.valueDeclaration
    if (decl && ts.isVariableDeclaration(decl) && decl.initializer && decl.parent.flags & ts.NodeFlags.Const) return constValue(decl.initializer, s)
    return refuse(e, `${e.text}: an initial state the subset can't read (give it in init)`)
  }
  return refuse(e, 'an initial state the subset can\'t read (give it in init)')
}
const aliased = (s: Setup, e: ts.Node): ts.Symbol | undefined => { const sym = s.checker.getSymbolAtLocation(e); return sym && sym.flags & ts.SymbolFlags.Alias ? s.checker.getAliasedSymbol(sym) : sym }
// An expression's object literal, through consts.
function literalOf(e: ts.Expression, s: Setup): ts.Expression | undefined {
  if (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isSatisfiesExpression(e)) return literalOf(e.expression, s)
  if (ts.isObjectLiteralExpression(e)) return e
  if (ts.isIdentifier(e)) { const d = aliased(s, e)?.valueDeclaration; return d && ts.isVariableDeclaration(d) && d.initializer && d.parent.flags & ts.NodeFlags.Const ? literalOf(d.initializer, s) : undefined }
  if (ts.isPropertyAccessExpression(e)) { const o = literalOf(e.expression, s); const p = o && ts.isObjectLiteralExpression(o) ? o.properties.find((x): x is ts.PropertyAssignment => ts.isPropertyAssignment(x) && x.name.getText() === e.name.text) : undefined; return p && literalOf(p.initializer, s) }
  return undefined
}
function initLeaves(raw: unknown, layout: Layout, s: Setup, at: ts.Node, out: Record<string, Term> = {}): Record<string, Term> {
  switch (layout.k) {
    case 'scalar': {
      const sort = s.vars.get(layout.name)!.sort
      if (sort.k === 'num' && typeof raw === 'number' && Number.isSafeInteger(raw)) out[layout.name] = {s: 'num', e: I.num(raw)}
      else if (sort.k === 'bool' && typeof raw === 'boolean') out[layout.name] = {s: 'bool', e: raw ? I.T : I.F}
      else if (sort.k === 'choice' && typeof raw === 'string' && sort.values.includes(raw)) out[layout.name] = {s: 'choice', e: I.llit(raw, sort.values)}
      else if (sort.k === 'str' && typeof raw === 'string') out[layout.name] = {s: 'str', e: {op: 'slit', value: raw}}
      else refuse(at, `the initial ${layout.name} (${String(raw)}) is not of its type`)
      return out
    }
    case 'rec':
      if (typeof raw !== 'object' || raw === null) return refuse(at, 'an initial state of another shape')
      for (const [f, sub] of layout.fields) initLeaves((raw as Record<string, unknown>)[f], sub, s, at, out)
      return out
    case 'map':
      if (raw !== EMPTY && !(typeof raw === 'object' && raw !== null && !Object.keys(raw).length) && !(raw instanceof Map && !raw.size)) refuse(at, `${layout.name} starts with entries (a map starts empty in the subset)`)
      return out
    case 'const': return out
  }
}

// An untyped state's shape from its initial value given (numbers, booleans, records of them).
function shapeOfRaw(raw: unknown, at: ts.Node, s: Setup): Shape {
  s.notes.add('the state is untyped: its type is the initial state\'s given')
  if (typeof raw === 'number') return {k: 'num'}
  if (typeof raw === 'boolean') return {k: 'bool'}
  if (typeof raw === 'object' && raw !== null && !(raw instanceof Map) && Object.keys(raw).length) return {k: 'rec', fields: Object.entries(raw).map(([f, x]) => [f, shapeOfRaw(x, at, s)])}
  return refuse(at, `an untyped state whose initial value (${JSON.stringify(raw)}) says no type: annotate it`)
}

// --- step functions -------------------------------------------------------------------------------------------------
function findFunction(sf: ts.SourceFile, name: string): ts.FunctionLikeDeclaration {
  for (const st of sf.statements) {
    if (ts.isFunctionDeclaration(st) && (st.name?.text === name || (name === 'default' && st.modifiers?.some(m => m.kind === ts.SyntaxKind.DefaultKeyword)))) return st
    if (ts.isVariableStatement(st)) for (const d of st.declarationList.declarations) if (ts.isIdentifier(d.name) && d.name.text === name && d.initializer) {
      const init = ts.isParenthesizedExpression(d.initializer) ? d.initializer.expression : d.initializer
      if (ts.isArrowFunction(init) || ts.isFunctionExpression(init)) return init
    }
    if (name === 'default' && ts.isExportAssignment(st) && (ts.isArrowFunction(st.expression) || ts.isFunctionExpression(st.expression))) return st.expression
    if (name === 'default' && ts.isExportAssignment(st) && ts.isIdentifier(st.expression)) return findFunction(sf, st.expression.text)
  }
  return refuse(at0(sf), `no function ${name} in the file`)
}
// The string literals the code compares a record's fields with (case labels, ===): those fields are choices.
function literalsOf(body: ts.Node, param: string, s?: Setup): Map<string, string[]> {
  const out = new Map<string, string[]>()
  const pathOf = (e: ts.Expression): string | undefined => {
    if (ts.isParenthesizedExpression(e)) return pathOf(e.expression)
    if (ts.isPropertyAccessExpression(e)) { if (ts.isIdentifier(e.expression) && e.expression.text === param) return e.name.text; const p = pathOf(e.expression); return p && `${p}_${e.name.text}` }
    return undefined
  }
  // A literal, or a const naming one (an action type from a constants module).
  const textOf = (lit: ts.Expression): string | undefined => {
    if (ts.isStringLiteral(lit) || ts.isNoSubstitutionTemplateLiteral(lit)) return lit.text
    if (s && (ts.isIdentifier(lit) || ts.isPropertyAccessExpression(lit))) { try { const v = constValue(lit, s); return typeof v === 'string' ? v : undefined } catch { return undefined } }
    return undefined
  }
  const add = (path: string | undefined, lit: ts.Expression) => { const t = textOf(lit); if (path && t !== undefined) { const xs = out.get(path) ?? []; if (!xs.includes(t)) xs.push(t); out.set(path, xs) } }
  const visit = (n: ts.Node) => {
    if (ts.isBinaryExpression(n) && [ts.SyntaxKind.EqualsEqualsEqualsToken, ts.SyntaxKind.ExclamationEqualsEqualsToken, ts.SyntaxKind.EqualsEqualsToken, ts.SyntaxKind.ExclamationEqualsToken].includes(n.operatorToken.kind)) { add(pathOf(n.left), n.right); add(pathOf(n.right), n.left) }
    if (ts.isSwitchStatement(n)) for (const cl of n.caseBlock.clauses) if (ts.isCaseClause(cl)) add(pathOf(n.expression), cl.expression)
    ts.forEachChild(n, visit)
  }
  visit(body)
  return out
}
const OTHER = '@@other'
// An argument as the request's inputs: a scalar is one input; a record (an action) is its fields, a union of records
// their fields together, with the field every member gives as a literal (`type`) a choice among them.
type ArgOf = {v: V, events: {select: Record<string, string>, arg: Arg}[], heap: [string, Rec][]}
function argOf(ex: Exec, param: ts.ParameterDeclaration, prefix: string, body: ts.Node): ArgOf {
  const s = ex.s, t = s.checker.getTypeAtLocation(param), pname = ts.isIdentifier(param.name) ? param.name.text : 'arg'
  const lits = ts.isIdentifier(param.name) ? literalsOf(body, param.name.text, s) : new Map<string, string[]>()
  // Untyped (JavaScript): its fields as the code reads them, numbers unless compared with string literals.
  if (t.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)) {
    for (const [path, xs] of lits) if (!s.lazySorts.has(`${prefix}${path}`)) s.lazySorts.set(`${prefix}${path}`, {k: 'choice', values: [...xs, OTHER]})
    const id = `input.${prefix}${pname}`
    s.notes.add(`${pname} is untyped: its fields are inputs as the code reads them (numbers, or a choice among the literals it is compared with and ${OTHER})`)
    const disc = [...lits.keys()].find(k => !k.includes('_'))
    const arg: Arg = {k: 'lazy', prefix}
    const events = disc ? [...lits.get(disc)!, OTHER].map(value => ({select: {[`$lazy:${prefix}${disc}`]: value}, arg})) : [{select: {}, arg}]
    return {v: {t: 'ref', id}, events, heap: [[id, {k: 'rec', fields: new Map(), origin: 'input', lazy: {prefix}}]]}
  }
  const members = t.isUnion() && t.types.every(m => m.flags & ts.TypeFlags.Object) ? t.types : [t]
  if (members.length === 1 && !(t.flags & ts.TypeFlags.Object)) {
    const sh = shapeOf(t, s.checker, param)
    if (sh.k === 'map' || sh.k === 'rec') throw new Error('unreachable')
    const x = ex.newVar(`${prefix}${pname}`, sortOf(sh, lits.get('') ?? []), 'input')
    return {v: Exec.valueOf(x), events: [{select: {}, arg: {k: 'input', name: x.name}}], heap: []}
  }
  // The fields of every member, by name; the discriminant: a field each member gives as one string literal.
  const fieldsOf = (m: ts.Type) => s.checker.getPropertiesOfType(m).map(p => [p.getName(), s.checker.getTypeOfSymbolAtLocation(p, param)] as const)
  const all = new Map<string, Shape>()
  for (const m of members) for (const [f, ft] of fieldsOf(m)) {
    const lit = ft.flags & ts.TypeFlags.StringLiteral
    const sh: Shape = lit ? {k: 'choice', values: [(ft as ts.StringLiteralType).value]} : shapeOf(ft, s.checker, param)
    const seen = all.get(f)
    if (!seen) all.set(f, sh)
    else if (seen.k === 'choice' && sh.k === 'choice') all.set(f, {k: 'choice', values: [...new Set([...seen.values, ...sh.values])]})
    else if (JSON.stringify(seen) !== JSON.stringify(sh)) refuse(param, `${pname}.${f} is of two types across the union (name them apart)`)
  }
  const disc = members.length > 1 ? [...all.keys()].find(f => members.every(m => { const ft = fieldsOf(m).find(([g]) => g === f)?.[1]; return ft && ft.flags & ts.TypeFlags.StringLiteral })) : undefined
  const heap: [string, Rec][] = [], vars = new Map<string, Var>()
  const make = (sh: Shape, path: string[], id: string): V => {
    if (sh.k === 'rec') {
      const fields = new Map(sh.fields.map(([f, fs]) => [f, make(fs, [...path, f], `${id}.${f}`)]))
      heap.push([id, {k: 'rec', fields, origin: 'input'}])
      return {t: 'ref', id}
    }
    if (sh.k === 'map') return refuse(param, `${pname}.${path.join('.')}: a map in a request`)
    const key = path.join('_')
    let sort: Sort = sh
    // A string field compared with literals (an action's `type: string`): a choice among them, and any other.
    if (sh.k === 'str' && lits.get(key)?.length) sort = {k: 'choice', values: [...lits.get(key)!, OTHER]}
    const x = ex.newVar(s.names.has(`${prefix}${key}`) ? `${prefix}${pname}_${key}` : `${prefix}${key}`, sort, 'input')
    vars.set(key, x)
    return Exec.valueOf(x)
  }
  const id = `input.${prefix}${pname}`, v = make({k: 'rec', fields: [...all]}, [], id)
  const template = (m: ts.Type | undefined): Arg => {
    const of = (sh: Shape, path: string[], present: (f: string) => boolean): Arg => (sh.k === 'rec'
      ? {k: 'rec', fields: sh.fields.filter(([f]) => path.length || present(f)).map(([f, fs]) => [f, of(fs, [...path, f], present)])}
      : {k: 'input', name: vars.get(path.join('_'))!.name})
    return of({k: 'rec', fields: [...all]}, [], f => !m || fieldsOf(m).some(([g]) => g === f))
  }
  const dv = disc && vars.get(disc)
  const events = dv && dv.sort.k === 'choice' ? members.map(m => {
    const lit = (s.checker.getTypeOfSymbolAtLocation(m.getProperty(disc!)!, param) as ts.StringLiteralType).value
    return {select: {[dv.name]: lit}, arg: template(m)}
  }) : (() => {
    // A string discriminant (`type: string`): each literal it is compared with, and another.
    const sv = [...vars.values()].find(x => x.sort.k === 'choice' && x.sort.values.includes(OTHER))
    return sv && sv.sort.k === 'choice' ? sv.sort.values.map(value => ({select: {[sv.name]: value}, arg: template(undefined)})) : [{select: {}, arg: template(undefined)}]
  })()
  return {v, events, heap}
}
const sortOf = (sh: Shape, lits: string[]): Sort => (sh.k === 'str' && lits.length ? {k: 'choice', values: [...lits, OTHER]} : sh.k === 'num' || sh.k === 'bool' || sh.k === 'choice' || sh.k === 'str' ? sh : (() => { throw new Error('a compound sort') })())

export function readFunctions(code: string, file: string, opts: ReadOptions): Model {
  // Read again while an untyped input turns out to be of another sort than a number.
  for (let typed = {...opts.typed}; ;) {
    try { return readFunctionsOnce(code, file, {...opts, typed}) } catch (e) { if (!(e instanceof Retype) || e.path in typed) throw e; typed = {...typed, [e.path]: e.sort} }
  }
}
function readFunctionsOnce(code: string, file: string, opts: ReadOptions): Model {
  const s = setupOf(code, file, opts.typed, opts.files), names = opts.functions ?? [opts.entry], fns = names.map(n => findFunction(s.sf, n))
  const first = fns[0]!, sp = first.parameters[0] ?? refuse(first, 'a step function takes the state first')
  // The initial state: given, a default parameter, useReducer's second argument, or `initialState`.
  let raw: unknown = opts.init, initSource: string | undefined, initExpr: ts.Expression | undefined
  if (raw === undefined) {
    initExpr = sp.initializer
    if (!initExpr) {
      const visit = (n: ts.Node) => { if (!initExpr && ts.isCallExpression(n) && ts.isIdentifier(n.expression) && n.expression.text === 'useReducer' && n.arguments[0] && ts.isIdentifier(n.arguments[0]) && names.includes(n.arguments[0].text)) { if (n.arguments.length > 2) refuse(n, 'useReducer with an init function'); initExpr = n.arguments[1] } ts.forEachChild(n, visit) }
      visit(s.sf)
    }
    if (!initExpr) for (const stmt of s.sf.statements) if (ts.isVariableStatement(stmt)) for (const d of stmt.declarationList.declarations) if (ts.isIdentifier(d.name) && d.name.text === 'initialState' && d.initializer) initExpr = d.initializer
    if (!initExpr) refuse(sp, 'no initial state: a default parameter, useReducer(reducer, initial), a const initialState, or init')
    raw = constValue(initExpr!, s)
    initSource = initExpr!.getText()
  }
  // The state's type: its own, or (untyped JavaScript) the initial state's.
  let st = s.checker.getTypeAtLocation(sp)
  if (st.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)) {
    if (initExpr) { st = s.checker.getBaseTypeOfLiteralType(s.checker.getTypeAtLocation(initExpr)); s.notes.add(`the state is untyped: its type is the initial state's (${s.checker.typeToString(st)})`) }
  }
  let shape = st.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown) && raw !== undefined ? shapeOfRaw(raw, sp, s) : shapeOf(st, s.checker, sp), untypedMap = false
  // Untyped and starting as {}: a record keyed by strings, of numbers (what [key] writes; the check runs it).
  if (shape.k === 'rec' && !shape.fields.length && typeof raw === 'object' && raw !== null && !Object.keys(raw).length) {
    const byNum = opts.typed?.['$key:state']?.k === 'num'
    shape = {k: 'map', key: byNum ? 'num' : 'str', val: {k: 'num'}, js: 'record'}
    s.notes.add(`the state starts as {} with no fields of its own: read as a record of numbers keyed by ${byNum ? 'numbers (as the step reads it)' : 'strings'}`)
    untypedMap = true
  }
  for (const [i, f] of fns.entries()) {
    const p0 = f.parameters[0] ?? refuse(f, `${names[i]} takes no state`)
    if (i > 0 && s.checker.typeToString(s.checker.getTypeAtLocation(p0)) !== s.checker.typeToString(s.checker.getTypeAtLocation(sp))) refuse(p0, `${names[i]} takes another state than ${names[0]}`)
  }
  const ex0 = new Exec(s), heap: Heap = new Map(), {layout, v: stateV} = build(ex0, shape, [], heap, 'input', sp)
  if (untypedMap) for (const d of s.maps.values()) d.untyped = true
  const init = initLeaves(raw, layout, s, sp)
  const multi = fns.length > 1, ev = multi ? ex0.newVar('fn', {k: 'choice', values: names}, 'input') : undefined
  const outs: [Path, StateVal][] = [], throws: B[] = [], events: Event[] = []
  for (const f of fns) (s.spans ??= []).push([f.getStart(), f.end])
  fns.forEach((f, i) => {
    const ex = new Exec(s), sel = ev ? I.is({op: 'var', name: ev.name, values: names}, names[i]!) : I.T
    const h: Heap = new Map(heap)
    let p: Path = {pc: sel.op === 'const' ? [] : [sel], locals: new Map(), heap: h, wrote: [], nows: 0}
    p = ex.bind(f.parameters[0]!.name, stateV, p)
    const combos: {select: Record<string, string>, args: Arg[]}[] = [{select: ev ? {[ev.name]: names[i]!} : {}, args: [{k: 'state'}]}]
    for (const param of f.parameters.slice(1)) {
      if (param.dotDotDotToken) refuse(param, 'a rest parameter')
      const a = argOf(ex, param, multi ? `${names[i]}_` : '', f.body ?? f)
      for (const [id, o] of a.heap) p.heap.set(id, o)
      p = ex.bind(param.name, a.v, p)
      const next = combos.flatMap(c => a.events.map(e => ({select: {...c.select, ...e.select}, args: [...c.args, e.arg]})))
      combos.splice(0, combos.length, ...next)
    }
    if (!f.body) refuse(f, 'a function without a body')
    let returned: [Path, V][]
    if (ts.isBlock(f.body!)) {
      const flow = ex.block(f.body.statements, p)
      if (flow.live) refuse(f, `${names[i]} returns nothing on some path`)
      returned = flow.rets
    } else { const [v, q] = ex.ev(f.body as ts.Expression, p); returned = [[q, v]] }
    for (const [rp, rv] of returned) outs.push([rp, materialize(ex, rv, layout, rp, f)])
    throws.push(refusalOf(ex))
    for (const c of combos) events.push({select: c.select, call: names[i]!, args: c.args})
  })
  // An untyped record's discriminant, chosen by name now that the variable is made.
  for (const e of events) for (const [k, value] of Object.entries(e.select)) if (k.startsWith('$lazy:')) {
    delete e.select[k]
    const v = [...s.lazy].find(([, l]) => `$lazy:${l.prefix}${l.field}` === k)
    if (v) e.select[v[0]] = value
  }
  const final = joinAll(ex0, outs, first)
  // A default export by its function's own name.
  const own = ts.isFunctionDeclaration(first) ? first.name?.text : ts.isVariableDeclaration(first.parent) && ts.isIdentifier(first.parent.name) ? first.parent.name.text : undefined
  return finish(s, {name: names[0] === 'default' ? own ?? 'reducer' : names[0]!, shape: multi ? 'functions' : 'reducer', file, entry: names.join(','), layout, init, final,
    refuse: I.or(...throws), pre: I.T, events, outputs: [], ...(ev ? {event: ev.name} : {}), ...(initSource ? {initSource} : {})})
}

function finish(s: Setup, m: {name: string, shape: Model['shape'], file: string, entry: string, layout: Layout, init: Record<string, Term>, final: StateVal, refuse: B, pre: B, events: Event[], outputs: string[], event?: string, ctorArgs?: string[], initSource?: string}): Model {
  const vars = [...s.vars.values()]
  const writes: Record<string, Term> = {}
  for (const [n, v] of m.final.leaves) if (!sameTerm(v, Exec.valueOf(s.vars.get(n)!))) writes[n] = termOf(v)
  const mapWrites: Model['mapWrites'] = {}
  for (const [n, w] of m.final.maps) if (w) mapWrites[n] = {key: w.key, has: w.has, vals: Object.fromEntries([...w.vals].map(([f, v]) => [f, termOf(v)]))}
  return {name: m.name, shape: m.shape, file: m.file, entry: m.entry, params: vars.filter(v => v.role === 'param'), inputs: vars.filter(v => v.role === 'input'), state: vars.filter(v => v.role === 'state'),
    maps: [...s.maps.values()], init: m.init, writes, mapWrites, outputs: m.outputs, refuse: m.refuse, pre: m.pre, layout: m.layout, events: m.events, notes: [...s.notes], hints: s.hints,
    ...(m.event ? {event: m.event} : {}), ...(m.ctorArgs ? {ctorArgs: m.ctorArgs} : {}), ...(s.lazy.size ? {lazy: s.lazy} : {}), ...(m.initSource ? {initSource: m.initSource} : {}), ...(s.spans ? {spans: s.spans} : {})}
}

// --- classes --------------------------------------------------------------------------------------------------------
function findClass(sf: ts.SourceFile, name: string): ts.ClassLikeDeclaration {
  for (const st of sf.statements) {
    if (ts.isClassDeclaration(st) && (st.name?.text === name || (name === 'default' && st.modifiers?.some(m => m.kind === ts.SyntaxKind.DefaultKeyword)))) return st
    if (ts.isVariableStatement(st)) for (const d of st.declarationList.declarations) if (ts.isIdentifier(d.name) && d.name.text === name && d.initializer && ts.isClassExpression(d.initializer)) return d.initializer
  }
  return refuse(at0(sf), `no class ${name} in the file`)
}
const has = (n: ts.Node, k: ts.SyntaxKind) => !!(ts.canHaveModifiers(n) && ts.getModifiers(n)?.some(m => m.kind === k))
const isMapInit = (e: ts.Expression | undefined): boolean => !!e && ((ts.isNewExpression(e) && ts.isIdentifier(e.expression) && e.expression.text === 'Map' && !e.arguments?.length) || (ts.isObjectLiteralExpression(e) && !e.properties.length) || ((ts.isAsExpression(e) || ts.isParenthesizedExpression(e)) && isMapInit(e.expression)))

export function readClass(code: string, file: string, opts: ReadOptions): Model {
  // Read twice: first with every field a state variable, to see which the methods write; then with the others as the
  // constants the constructor makes them.
  const written = attempt(code, file, opts, new Set()).written
  return attempt(code, file, opts, written).model
}
// The classes a class extends, the most derived first: each one the files read declare (a class made by a call, a
// mixin, or one from another module is refused where it is named).
function chainOf(s: Setup, cls: ts.ClassLikeDeclaration): ts.ClassLikeDeclaration[] {
  const chain = [cls]
  for (let c = cls; ;) {
    const h = c.heritageClauses?.find(x => x.token === ts.SyntaxKind.ExtendsKeyword)
    if (!h) return chain
    const e = h.types[0]!.expression
    if (!ts.isIdentifier(e) && !ts.isPropertyAccessExpression(e)) return refuse(h, `extends ${e.getText().slice(0, 60)}: a class a call makes (a mixin), not one the files read declare`)
    let sym = s.checker.getSymbolAtLocation(ts.isPropertyAccessExpression(e) ? e.name : e)
    if (sym && sym.flags & ts.SymbolFlags.Alias) sym = s.checker.getAliasedSymbol(sym)
    const decl = sym?.declarations?.find(ts.isClassLike)
    if (!decl) return refuse(h, `extends ${e.getText()}: no class of the files read (another module's, or not a class)`)
    if (!s.ours(decl.getSourceFile())) return refuse(h, `extends ${e.getText()}, a class from another module (not among the files read)`)
    if (chain.includes(decl)) return refuse(h, 'a class that extends itself')
    chain.push(decl); c = decl
  }
}
// What a method returns, kept: a value (`m_result`), a record of values (`m_result_<field>`), or a value that may be
// missing (`m_result`, and `m_result_missing` where it is null or undefined).
export type Result = {k: 'scalar', name: string} | {k: 'rec', fields: [string, string][]} | {k: 'maybe', name: string, missing: string, null: boolean}
function attempt(code: string, file: string, opts: ReadOptions, written: Set<string>): {model: Model, written: Set<string>} {
  const s = setupOf(code, file, {}, opts.files), cls = findClass(s.sf, opts.entry), first = written.size === 0
  s.cls = cls
  // `implements` is a type's only (nothing at run time); `extends` brings another class's fields and methods: each
  // member resolved statically, from the entry class up (this.m() the entry's own or the nearest inherited; super.m()
  // the nearest above the class it is written in).
  const chain = chainOf(s, cls)
  s.chain = chain
  if (chain.length > 1) s.notes.add(`${opts.entry} extends ${chain.slice(1).map(c => c.name?.text ?? '(a class)').join(', which extends ')}: its fields and methods are read with them, each method the nearest the object has`)
  const ownCtor = (c: ts.ClassLikeDeclaration) => c.members.find((m): m is ts.ConstructorDeclaration => ts.isConstructorDeclaration(m) && !!m.body)
  // The constructor the object is made with: the entry's, or the nearest it inherits.
  const ctorAt = chain.findIndex(ownCtor), ctor = ctorAt >= 0 ? ownCtor(chain[ctorAt]!) : undefined
  for (const c of chain) { const k = ownCtor(c); if (k && k.getSourceFile() === s.sf) (s.spans ??= []).push([k.getStart(), k.end]) }
  type Field = {name: string, shape: Shape, node: ts.Node, init?: ts.Expression, of: ts.ClassLikeDeclaration}
  const fields: Field[] = []
  const addField = (f: Field) => { if (fields.some(x => x.name === f.name)) refuse(f.node, `${f.name}: a field declared again in a class that extends one with it`); fields.push(f) }
  for (const c of [...chain].reverse()) {
    for (const m of c.members) {
      if (ts.isPropertyDeclaration(m)) {
        if (ts.isPrivateIdentifier(m.name)) refuse(m, `${m.name.text}: a #private field (the check reads the object's fields; \`private\` is in the subset)`)
        if (has(m, ts.SyntaxKind.StaticKeyword)) refuse(m, 'a static field (state shared by every object)')
        if (has(m, ts.SyntaxKind.AbstractKeyword) || has(m, ts.SyntaxKind.DeclareKeyword)) continue
        addField({name: memberName(m.name), shape: shapeOf(s.checker.getTypeAtLocation(m), s.checker, m), node: m, ...(m.initializer ? {init: m.initializer} : {}), of: c})
      } else if (ts.isSetAccessorDeclaration(m)) refuse(m, 'a setter')
      else if (ts.isMethodDeclaration(m) && ts.isPrivateIdentifier(m.name)) refuse(m, 'a #private method')
      else if (ts.isIndexSignatureDeclaration(m) || ts.isClassStaticBlockDeclaration(m)) refuse(m, 'a static block or index signature')
    }
    const k = ownCtor(c)
    for (const p of k?.parameters ?? []) if (ts.isParameterPropertyDeclaration(p, k!)) addField({name: (p.name as ts.Identifier).text, shape: shapeOf(s.checker.getTypeAtLocation(p), s.checker, p), node: p, of: c})
  }
  const ex0 = new Exec(s)
  const constant = (f: Field) => !first && !written.has(f.name) && f.shape.k !== 'map'
  // The state's variables first (so they keep the fields' names), then the params.
  const stateHeap: Heap = new Map(), thisFields = new Map<string, V>(), layout: [string, Layout][] = [], stateLayout: [string, Layout][] = []
  for (const f of fields) if (!constant(f)) { const r = build(ex0, f.shape, [f.name], stateHeap, 'this', f.node); thisFields.set(f.name, r.v); layout.push([f.name, r.layout]); stateLayout.push([f.name, r.layout]) }
  // The constructor, run over its arguments (the params): what each field starts at, and what it refuses (the pre). A
  // class that extends another runs the other's at super(...) (or, with no constructor of its own, first, with the
  // same arguments), then its own field initializers, then the rest of its constructor.
  s.nowRole = 'param'
  const ctorArgs: string[] = [], ctorHeap: Heap = new Map(), ctorFields = new Map<string, V>(fields.map(f => [f.name, {t: 'undef'}]))
  ctorHeap.set('this', {k: 'rec', fields: ctorFields, origin: 'fresh'})
  let cp: Path = {pc: [], locals: new Map(), heap: ctorHeap, wrote: [], nows: 0}
  const exC = new Exec(s)
  s.ctor = true
  const empty = new Set<string>(), mapArgs = new Map<string, string>()
  const setThis = (q: Path, f: string, v: V): Path => { const o = q.heap.get('this') as Rec; return {...q, heap: new Map(q.heap).set('this', {...o, fields: new Map(o.fields).set(f, v)})} }
  const argValues: V[] = []
  for (const p of ctor?.parameters ?? []) {
    if (!ts.isIdentifier(p.name)) refuse(p, 'a destructured constructor argument')
    const sh = shapeOf(s.checker.getTypeAtLocation(p), s.checker, p)
    // A Map given to the constructor: the field it becomes starts as that Map, taken here as empty (as callers make it).
    if (sh.k === 'map') { ctorArgs.push(`$map:${sh.js}`); argValues.push({t: 'undef'}); mapArgs.set((p.name as ts.Identifier).text, `$map:${sh.js}`); continue }
    if (sh.k !== 'num' && sh.k !== 'bool' && sh.k !== 'choice') refuse(p, `${p.name.getText()}: a constructor argument that isn't a number, a boolean, a union of literals or a Map`)
    if ((sh as Sort).k === 'num' && (sh as {date?: true}).date) refuse(p, `${p.name.getText()}: a Date given to the constructor (the object would share it with its caller)`)
    const x = exC.newVar(p.name.getText(), sh as Sort, 'param', 'a constructor argument')
    ctorArgs.push(x.name)
    argValues.push(Exec.valueOf(x))
  }
  // The statements of one constructor that set a map field (to an empty map, or to the Map given): a map that starts
  // empty, not a write.
  const mapInits = (k: ts.ConstructorDeclaration, locals: Map<string, V>) => (k.body?.statements ?? []).filter(st => {
    if (!ts.isExpressionStatement(st) || !ts.isBinaryExpression(st.expression) || st.expression.operatorToken.kind !== ts.SyntaxKind.EqualsToken) return true
    const l = st.expression.left
    if (!ts.isPropertyAccessExpression(l) || l.expression.kind !== ts.SyntaxKind.ThisKeyword) return true
    const f = fields.find(x => x.name === memberName(l.name))
    if (f?.shape.k !== 'map') return true
    const r = st.expression.right, rn = ts.isIdentifier(r) ? r.text : undefined, given = rn && locals.get(rn)?.t === 'undef' && k === ctor ? mapArgs.get(rn) : undefined
    if (given) {
      if ([...empty].some(x => x === f.name)) refuse(st, `${f.name} set twice`)
      if (s.notes.has(`maparg:${rn}`)) refuse(st, `the Map ${rn} given to two fields (one Map in two places)`)
      s.notes.add(`maparg:${rn}`)
      s.notes.add(`${f.name} is the Map given to the constructor (${rn}): it starts empty here, as the code's callers make it (\`new ${opts.entry}(new Map())\`); a Map given with entries, or changed by its caller after, is outside this rule`)
    } else if (!isMapInit(r)) refuse(st, `${f.name} starts with entries (a map starts empty in the subset)`)
    empty.add(f.name)
    return false
  })
  const fieldInits = (c: ts.ClassLikeDeclaration, q: Path): Path => {
    for (const f of fields) if (f.of === c && f.init) {
      if (f.shape.k === 'map') { if (!isMapInit(f.init)) refuse(f.init, `${f.name} starts with entries (a map starts empty in the subset)`); empty.add(f.name); continue }
      const [v, q2] = exC.ev(f.init, q)
      q = setThis(q2, f.name, v)
    }
    return q
  }
  const ends: Path[] = []
  const construct = (k: number, args: V[], q: Path, at: ts.Node): Path | undefined => {
    const c = chain[k]!, own = ownCtor(c)
    if (!own) {
      // No constructor of its own: the one above with the same arguments, then its field initializers.
      const q2 = k + 1 < chain.length ? construct(k + 1, args, q, at) : q
      return q2 && fieldInits(c, q2)
    }
    const outer = q.locals
    let r: Path = {...q, locals: new Map()}
    own.parameters.forEach((p, i) => {
      if (!ts.isIdentifier(p.name)) refuse(p, 'a destructured constructor argument')
      let v = args[i]
      if (v === undefined) { if (!p.initializer) refuse(at, 'super(...) with fewer arguments than the constructor takes'); const [dv, r2] = exC.ev(p.initializer!, r); v = dv; r = r2 }
      r = exC.bind(p.name, v, r)
    })
    const props = (x: Path) => own.parameters.reduce((y, p) => (ts.isParameterPropertyDeclaration(p, own) ? setThis(y, (p.name as ts.Identifier).text, y.locals.get((p.name as ts.Identifier).text)!) : y), x)
    const body = mapInits(own, r.locals)
    const sup = body.findIndex(st => ts.isExpressionStatement(st) && ts.isCallExpression(st.expression) && st.expression.expression.kind === ts.SyntaxKind.SuperKeyword)
    if (k + 1 < chain.length && sup < 0) refuse(own, 'a constructor of a class that extends another with no super(...) at its top level')
    const run = (stmts: readonly ts.Statement[], x: Path): Path | undefined => {
      const f = exC.block(stmts, x)
      if (f.rets.some(([, v]) => v.t !== 'undef')) refuse(own, 'a constructor that returns a value')
      ends.push(...f.rets.map(([p]) => ({...p, locals: outer})))
      return f.live
    }
    let live: Path | undefined
    if (k + 1 < chain.length) {
      const before = run(body.slice(0, sup), r)
      if (!before) return undefined
      const call = (body[sup] as ts.ExpressionStatement).expression as ts.CallExpression
      let at2 = before
      const sargs: V[] = []
      for (const a of call.arguments) { if (ts.isSpreadElement(a)) refuse(a, 'a spread argument'); const [v, q2] = exC.ev(a, at2); sargs.push(v); at2 = q2 }
      const above = construct(k + 1, sargs, at2, call)
      if (!above) return undefined
      live = run(body.slice(sup + 1), fieldInits(c, props({...above, locals: at2.locals})))
    } else live = run(body, fieldInits(c, props(r)))
    return live && {...live, locals: outer}
  }
  const made0 = construct(0, argValues, cp, ctor ?? cls)
  if (made0) ends.push(made0)
  const cend = ends.reduceRight<Path | undefined>((acc, x) => exC.merge(x, acc, ctor ?? cls), undefined) ?? refuse(ctor ?? cls, 'a constructor that always throws')
  s.ctor = false
  for (const n of [...s.notes]) if (n.startsWith('maparg:')) s.notes.delete(n)
  const pre = I.not(refusalOf(exC))
  const made = (cend.heap.get('this') as Rec).fields
  for (const f of fields) if (f.shape.k === 'map' && !empty.has(f.name)) refuse(f.node, `${f.name}: a map field must start as new Map() or {} (or the Map the constructor is given)`)
  // Each field's start, over the params: a state variable's init, or a constant field's value in every method.
  const init: Record<string, Term> = {}
  const startOf = (v: V, lay: Layout, at: ts.Node) => {
    const sv = materialize(exC, v, lay, cend, at)
    for (const [n, x] of sv.leaves) init[n] = termOf(x)
  }
  for (const [fname, lay] of layout) if (lay.k !== 'map') startOf(made.get(fname)!, lay, fields.find(f => f.name === fname)!.node)
  for (const f of fields) if (constant(f)) {
    const v = made.get(f.name)!
    if (v.t === 'undef' || v.t === 'opt') refuse(f.node, `${f.name} starts undefined`)
    if (v.t === 'ref') {
      // A constant object (a config): copied into each method's heap, each field a term over the params.
      const copy = (id: string): void => { const o = cend.heap.get(id); if (o?.k === 'rec') { stateHeap.set(id, {...o, origin: 'this'}); for (const x of o.fields.values()) if (x.t === 'ref') copy(x.id) } else refuse(f.node, `${f.name}: a constant map`) }
      copy(v.id)
    }
    thisFields.set(f.name, v)
    layout.push([f.name, constLayout(v, cend, f.node)])
  }
  s.now = undefined; s.nowRole = 'input'
  stateHeap.set('this', {k: 'rec', fields: thisFields, origin: 'this'})
  // The methods: each public one an event (the nearest of each name, through the classes it extends), run from the
  // state as variables.
  const seenNames = new Set<string>(), methods: ts.MethodDeclaration[] = []
  for (const c of chain) for (const m of c.members) {
    if (!ts.isMethodDeclaration(m) || seenNames.has(memberName(m.name))) continue
    if (!m.body && has(m, ts.SyntaxKind.AbstractKeyword)) continue
    seenNames.add(memberName(m.name))
    if (has(m, ts.SyntaxKind.StaticKeyword) || has(m, ts.SyntaxKind.PrivateKeyword) || has(m, ts.SyntaxKind.ProtectedKeyword)) continue
    if (!opts.methods || opts.methods.includes(memberName(m.name))) methods.push(m)
  }
  if (opts.methods) for (const n of opts.methods) if (!methods.some(m => memberName(m.name) === n)) {
    const st = chain.flatMap(c => c.members).find(m => ts.isMethodDeclaration(m) && memberName(m.name) === n && has(m, ts.SyntaxKind.StaticKeyword))
    refuse(st ?? cls, st ? `${n} is static (a function of the class, not a step of an object): the subset reads an object's methods` : `no public method ${n}`)
  }
  if (!methods.length) refuse(cls, 'a class with no public methods (no events)')
  const mnames = methods.map(m => memberName(m.name)), ev = ex0.newVar('method', {k: 'choice', values: mnames}, 'input'), evL = {op: 'var' as const, name: ev.name, values: mnames}
  const outputs: string[] = [], perMethod: {sel: B, sv: StateVal, refuse: B}[] = [], events: Event[] = []
  const results: Record<string, Result> = {}, outVars = new Map<string, Var[]>()
  const outVar = (name: string, sort: Sort, what: string) => { const x = ex0.newVar(name, sort, 'state', what); outputs.push(x.name); return x }
  for (const m of methods) {
    const name = memberName(m.name), sig = s.checker.getSignatureFromDeclaration(m)!, rt = s.checker.getReturnTypeOfSignature(sig)
    if (has(m, ts.SyntaxKind.AsyncKeyword) || m.asteriskToken) refuse(m, `${name}: an async or generator method (its steps interleave with others)`)
    if (rt.flags & (ts.TypeFlags.Void | ts.TypeFlags.Undefined)) continue
    const what = `what ${name} returned, at the step that called it (its default at others)`
    // A value that may be missing (T | null, T | undefined): the value, and whether it is missing.
    const parts = rt.isUnion() ? rt.types : [rt], missing = parts.filter(x => x.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined)), rest = parts.filter(x => !(x.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined)))
    if (missing.length && rest.length) {
      if (missing.length > 1) refuse(m, `${name} returns null or undefined (two ways missing)`)
      const rt1 = rest.length === 1 ? rest[0]! : rest.every(x => x.flags & ts.TypeFlags.BooleanLiteral) ? s.checker.getBooleanType() : undefined
      const sh = rt1 ? shapeOf(rt1, s.checker, m) : rest.every(x => x.flags & ts.TypeFlags.StringLiteral) ? {k: 'choice' as const, values: rest.map(x => (x as ts.StringLiteralType).value)} : refuse(m, `${name} returns ${s.checker.typeToString(rt)}`)
      if (sh.k !== 'num' && sh.k !== 'bool' && sh.k !== 'choice') refuse(m, `${name} returns ${s.checker.typeToString(rt)} (a result kept is a number, a boolean or a union of literals, or a record of them)`)
      if ((sh as {date?: true}).date) refuse(m, `${name} returns a Date (the caller would share it with the object)`)
      const x = outVar(`${name}_result`, sh as Sort, what), y = outVar(`${name}_result_missing`, {k: 'bool'}, `whether ${name} returned ${missing[0]!.flags & ts.TypeFlags.Null ? 'null' : 'undefined'}`)
      results[name] = {k: 'maybe', name: x.name, missing: y.name, null: !!(missing[0]!.flags & ts.TypeFlags.Null)}; outVars.set(name, [x, y])
      layout.push([`${name}()`, {k: 'scalar', name: x.name}])
      continue
    }
    const sh = shapeOf(rt, s.checker, m)
    if (sh.k === 'rec') {
      const vs = sh.fields.map(([f, fs]) => {
        if (fs.k !== 'num' && fs.k !== 'bool' && fs.k !== 'choice') return refuse(m, `${name} returns a record whose ${f} is ${fs.k === 'str' ? 'a string' : 'compound'}`)
        if ((fs as {date?: true}).date) return refuse(m, `${name} returns a record holding a Date (the caller would share it with the object)`)
        return [f, outVar(`${name}_result_${f}`, fs as Sort, `${what}: its ${f}`)] as const
      })
      results[name] = {k: 'rec', fields: vs.map(([f, x]) => [f, x.name])}; outVars.set(name, vs.map(([, x]) => x))
      layout.push([`${name}()`, {k: 'rec', fields: vs.map(([f, x]) => [f, {k: 'scalar', name: x.name}])}])
      continue
    }
    if (sh.k !== 'num' && sh.k !== 'bool' && sh.k !== 'choice') refuse(m, `${name} returns ${sh.k === 'str' ? 'a string' : 'a compound value'} (a result kept is a number, a boolean or a union of literals, or a record of them)`)
    if ((sh as {date?: true}).date) refuse(m, `${name} returns a Date (the caller would share it with the object)`)
    const x = outVar(`${name}_result`, sh as Sort, what)
    results[name] = {k: 'scalar', name: x.name}; outVars.set(name, [x])
    layout.push([`${name}()`, {k: 'scalar', name: x.name}])
  }
  for (const m of methods) if (m.getSourceFile() === s.sf) (s.spans ??= []).push([m.getStart(), m.end])
  for (const m of methods) {
    const name = memberName(m.name), ex = new Exec(s), sel = I.is(evL, name)
    let p: Path = {pc: [sel], locals: new Map(), heap: new Map(stateHeap), wrote: [], nows: 0}
    const args: Arg[] = []
    for (const param of m.parameters) {
      if (param.dotDotDotToken || !ts.isIdentifier(param.name)) refuse(param, 'a rest or destructured argument')
      const a = argOf(ex, param, `${name}_`, m.body ?? m)
      if (a.events.length !== 1) refuse(param, 'an argument that is a union of records')
      for (const [id, o] of a.heap) p.heap.set(id, o)
      p = ex.bind(param.name, a.v, p)
      args.push(a.events[0]!.arg)
    }
    if (!m.body) refuse(m, `${name} has no body`)
    const flow = ex.block(m.body!.statements, p)
    const outs: [Path, StateVal][] = [...flow.rets, ...(flow.live ? [[flow.live, {t: 'undef'} as V] as [Path, V]] : [])].map(([rp, rv]) => {
      const self = rp.heap.get('this') as Rec, sv: StateVal = {leaves: new Map(), maps: new Map()}
      for (const [f, lay] of stateLayout) materialize(ex, self.fields.get(f)!, lay, rp, m, sv)
      for (const [mn, xs] of outVars) {
        if (mn !== name) { for (const x of xs) sv.leaves.set(x.name, Exec.defaultOf(x.sort)); continue }
        const r = results[mn]!
        if (r.k === 'scalar') { sv.leaves.set(r.name, rv.t === 'undef' ? refuse(m, `${name} returns nothing on some path`) : outValue(ex, rv, xs[0]!, rp, m)); continue }
        if (r.k === 'maybe') {
          const missingKind = (x: V) => (x.t === 'undef' ? x.null === r.null : x.t === 'opt' ? !!x.null === r.null || (x.has.op === 'const' && x.has.v) : true)
          if (!missingKind(rv)) refuse(m, `${name} returns ${r.null ? 'undefined' : 'null'} where its type says ${r.null ? 'null' : 'undefined'}`)
          const has = rv.t === 'undef' ? I.F : rv.t === 'opt' ? rv.has : I.T, inner = rv.t === 'undef' ? undefined : rv.t === 'opt' ? rv.v : rv
          const there = inner ? outValue(ex, inner, xs[0]!, {...rp, pc: [...rp.pc, has]}, m) : Exec.defaultOf(xs[0]!.sort)
          sv.leaves.set(r.name, ex.mergeScalar(has, there, Exec.defaultOf(xs[0]!.sort), m))
          sv.leaves.set(r.missing, {t: 'bool', e: I.not(has)})
          continue
        }
        // A record returned: a fresh one (a field of the state's own objects would be shared with the caller).
        const d = rv.t === 'ref' ? rp.heap.get(rv.id) : undefined
        if (rv.t !== 'ref' || d?.k !== 'rec' || d.origin !== 'fresh') refuse(m, `${name} returns ${rv.t === 'ref' ? "an object of the state's own (the caller would share it)" : 'other than a record'}`)
        r.fields.forEach(([f, n], i) => sv.leaves.set(n, outValue(ex, (d as Rec).fields.get(f) ?? refuse(m, `${name} returns a record without ${f}`), xs[i]!, rp, m)))
      }
      return [rp, sv]
    })
    perMethod.push({sel, sv: joinAll(ex, outs, m), refuse: refusalOf(ex)})
    events.push({select: {[ev.name]: name}, call: name, args})
  }
  // The methods together: each variable by the method called.
  let final = perMethod.at(-1)!.sv
  for (let i = perMethod.length - 2; i >= 0; i--) final = mergeVals(ex0, perMethod[i]!.sel, perMethod[i]!.sv, final, cls)
  for (const xs of outVars.values()) for (const x of xs) init[x.name] = termOf(Exec.defaultOf(x.sort))
  const wrote = new Set<string>()
  for (const [f, lay] of layout) {
    const leaves: string[] = []
    const walk = (l: Layout) => { if (l.k === 'scalar') leaves.push(l.name); else if (l.k === 'rec') l.fields.forEach(([, x]) => walk(x)); else if (l.k === 'map') leaves.push(`map:${l.name}`) }
    walk(lay)
    if (leaves.some(n => (n.startsWith('map:') ? final.maps.get(n.slice(4)) !== undefined : !sameTerm(final.leaves.get(n)!, Exec.valueOf(s.vars.get(n)!))))) wrote.add(f)
  }
  const model = finish(s, {name: opts.entry, shape: 'class', file, entry: opts.entry, layout: {k: 'rec', fields: layout}, init, final, refuse: I.or(...perMethod.map(x => I.and(x.sel, x.refuse))), pre, events, outputs, event: ev.name, ctorArgs})
  model.results = results
  return {model, written: wrote}
}
function constLayout(v: V, p: Path, at: ts.Node): Layout {
  if (v.t === 'num') return {k: 'const', value: {s: 'num', e: v.e}}
  if (v.t === 'bool') return {k: 'const', value: {s: 'bool', e: v.e}}
  if (v.t === 'choice') return {k: 'const', value: {s: 'choice', e: v.e}}
  if (v.t === 'ref') { const o = p.heap.get(v.id); if (o?.k === 'rec') return {k: 'rec', fields: [...o.fields].map(([f, x]) => [f, constLayout(x, p, at)])} }
  return refuse(at, `a constant field holding a ${v.t}`)
}
function outValue(ex: Exec, v: V, x: Var, p: Path, at: ts.Node): V {
  if (v.t === 'opt') { if (!ex.known(p, v.has)) refuse(at, `${x.name} may be undefined`); v = v.v }
  if (x.sort.k === 'num' && v.t === 'num') return v
  if (x.sort.k === 'bool' && v.t === 'bool') return v
  if (x.sort.k === 'choice' && (v.t === 'choice' || v.t === 'str')) return {t: 'choice', e: ex.asChoice(v, x.sort.values, at), values: x.sort.values}
  return refuse(at, `returns a ${v.t} where its type says ${x.sort.k}`)
}

// --- Redux Toolkit slices -------------------------------------------------------------------------------------------
// createSlice({name, initialState, reducers, extraReducers}): each case reducer (and each builder.addCase of
// extraReducers) an event of its action type; it runs on a copy of the state (immer's draft, written in place), and the
// state after is the draft, or the value it returns. Writing the draft and returning another value is refused (immer
// throws there). The check runs the slice's own reducer (Redux Toolkit itself, in the check's modules).
const sliceOf = (sf: ts.SourceFile, name: string): ts.ObjectLiteralExpression | undefined => {
  for (const st of sf.statements) if (ts.isVariableStatement(st)) for (const d of st.declarationList.declarations) {
    if (!ts.isIdentifier(d.name) || d.name.text !== name || !d.initializer) continue
    const c = d.initializer
    if (ts.isCallExpression(c) && ts.isIdentifier(c.expression) && c.expression.text === 'createSlice' && c.arguments[0] && ts.isObjectLiteralExpression(c.arguments[0])) return c.arguments[0]
  }
  return undefined
}
export const isSlice = (code: string, entry: string) => new RegExp(`\\b${entry}\\s*=\\s*createSlice\\s*\\(`).test(code)
export function readSlice(code: string, file: string, opts: ReadOptions): Model {
  for (let typed = {...opts.typed}; ;) {
    try { return readSliceOnce(code, file, {...opts, typed}) } catch (e) { if (!(e instanceof Retype) || e.path in typed) throw e; typed = {...typed, [e.path]: e.sort} }
  }
}
function readSliceOnce(code: string, file: string, opts: ReadOptions): Model {
  const s = setupOf(code, file, opts.typed, opts.files), cfg = sliceOf(s.sf, opts.entry) ?? refuse(at0(s.sf), `no createSlice ${opts.entry} in the file`)
  const prop = (k: string) => cfg.properties.find((p): p is ts.PropertyAssignment | ts.ShorthandPropertyAssignment => (ts.isPropertyAssignment(p) || ts.isShorthandPropertyAssignment(p)) && p.name.getText() === k)
  // A shorthand entry's value: the variable it names (its initializer, for a const).
  const valueOf = (p: ts.PropertyAssignment | ts.ShorthandPropertyAssignment): ts.Expression => {
    if (ts.isPropertyAssignment(p)) return p.initializer
    const d = s.checker.getShorthandAssignmentValueSymbol(p)?.valueDeclaration
    return d && ts.isVariableDeclaration(d) && d.initializer && d.parent.flags & ts.NodeFlags.Const ? d.initializer : p.name
  }
  const nameP = prop('name'), initP = prop('initialState')
  if (!nameP || !initP) return refuse(cfg, 'a slice without a name or an initialState')
  const sliceName = constValue(valueOf(nameP), s)
  if (typeof sliceName !== 'string') return refuse(nameP, 'a slice name that is not a string')
  // Its value from the initializer; its type as written there (a declared CounterState, not its literals' types).
  const initExpr = valueOf(initP), raw = opts.init ?? constValue(initExpr, s)
  let st = s.checker.getTypeAtLocation(ts.isPropertyAssignment(initP) ? initP.initializer : initP.name)
  if (st.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)) st = s.checker.getBaseTypeOfLiteralType(st)
  const shape = st.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown) ? shapeOfRaw(raw, initExpr, s) : shapeOf(s.checker.getBaseTypeOfLiteralType(st), s.checker, initExpr)
  const ex0 = new Exec(s), heap: Heap = new Map(), {layout, v: stateV} = build(ex0, shape, [], heap, 'input', initExpr)
  const init = initLeaves(raw, layout, s, initExpr)
  // The cases: each reducer `key: (state, action) => ...` of type `name/key`; each addCase(creator, reducer).
  const cases: [string, ts.Expression][] = []
  const reducers = prop('reducers')
  const rv = reducers && valueOf(reducers)
  if (rv && !ts.isObjectLiteralExpression(rv)) refuse(rv, 'reducers given other than as an object of them')
  for (const p of (rv as ts.ObjectLiteralExpression | undefined)?.properties ?? []) {
    if (ts.isMethodDeclaration(p)) { cases.push([`${sliceName}/${p.name.getText()}`, p as never]); continue }
    if (!ts.isPropertyAssignment(p)) { refuse(p, 'a case reducer written other than key: function'); continue }
    const f = p.initializer
    if (!ts.isArrowFunction(f) && !ts.isFunctionExpression(f)) refuse(f, 'a case reducer with a prepare callback, or not a function')
    cases.push([`${sliceName}/${p.name.getText()}`, f])
  }
  const extra = prop('extraReducers')
  if (extra) {
    const fn = valueOf(extra)
    if (!ts.isArrowFunction(fn) && !ts.isFunctionExpression(fn)) return refuse(fn, 'extraReducers other than a builder callback')
    const builder = fn.parameters[0]?.name.getText() ?? ''
    // The action creator's type: a thunk's pending, fulfilled or rejected (createAsyncThunk's prefix), or createAction's.
    const typeOf = (a: ts.Expression): string => {
      if (ts.isPropertyAccessExpression(a) && ['pending', 'fulfilled', 'rejected'].includes(a.name.text) && ts.isIdentifier(a.expression)) {
        const d = s.checker.getSymbolAtLocation(a.expression)?.valueDeclaration
        const c = d && ts.isVariableDeclaration(d) ? d.initializer : undefined
        if (c && ts.isCallExpression(c) && ts.isIdentifier(c.expression) && c.expression.text === 'createAsyncThunk' && c.arguments[0]) { const pre = constValue(c.arguments[0], s); if (typeof pre === 'string') return `${pre}/${a.name.text}` }
      }
      if (ts.isIdentifier(a)) {
        const d = s.checker.getSymbolAtLocation(a)?.valueDeclaration, c = d && ts.isVariableDeclaration(d) ? d.initializer : undefined
        if (c && ts.isCallExpression(c) && ts.isIdentifier(c.expression) && c.expression.text === 'createAction' && c.arguments[0]) { const t = constValue(c.arguments[0], s); if (typeof t === 'string') return t }
      }
      const t = constValue(a, s)
      return typeof t === 'string' ? t : refuse(a, 'an addCase of an action creator the subset can\'t name')
    }
    const chain = (e: ts.Expression): void => {
      e = ts.isParenthesizedExpression(e) ? e.expression : e
      if (ts.isIdentifier(e) && e.text === builder) return
      if (!ts.isCallExpression(e) || !ts.isPropertyAccessExpression(e.expression)) return void refuse(e, 'extraReducers other than builder.addCase(...) calls')
      const m = e.expression.name.text
      if (m !== 'addCase') return void refuse(e, `builder.${m} (addCase is in the subset)`)
      chain(e.expression.expression)
      cases.push([typeOf(e.arguments[0]!), e.arguments[1]!])
    }
    const body = fn.body
    if (ts.isBlock(body)) for (const stmt of body.statements) { if (!ts.isExpressionStatement(stmt)) refuse(stmt, 'extraReducers other than builder calls'); else chain(stmt.expression) }
    else chain(body)
  }
  if (!cases.length) return refuse(cfg, 'a slice with no case reducers')
  const types = [...new Set(cases.map(([t]) => t)), OTHER]
  const ev = ex0.newVar('type', {k: 'choice', values: types}, 'input'), evL = {op: 'var' as const, name: ev.name, values: types}
  const outs: [B, StateVal][] = [], refusals: B[] = []
  // The draft: a copy of the state's objects, written in place.
  const draftOf = (h: Heap): {heap: Heap, v: V} => {
    const ids = new Map<string, string>(), out: Heap = new Map(h)
    const copy = (x: V): V => {
      if (x.t !== 'ref') return x
      const known = ids.get(x.id)
      if (known) return {t: 'ref', id: known}
      const o = h.get(x.id)!, id = `draft.${x.id}`
      ids.set(x.id, id)
      out.set(id, o.k === 'rec' ? {...o, origin: 'fresh', fields: new Map([...o.fields].map(([f, y]) => [f, copy(y)]))} : o.k === 'map' ? {...o, origin: 'fresh'} : o)
      return {t: 'ref', id}
    }
    return {heap: out, v: copy(stateV)}
  }
  for (const [, f] of cases) (s.spans ??= []).push([f.getStart(), f.end])
  for (const [type, f] of cases) {
    const ex = new Exec(s), sel = I.is(evL, type)
    const fn = f as ts.ArrowFunction | ts.FunctionExpression
    if (!ts.isArrowFunction(fn) && !ts.isFunctionExpression(fn) && !ts.isMethodDeclaration(fn)) { refuse(f, 'a case reducer that is not a function'); continue }
    const d = draftOf(heap), actionId = 'input.action'
    let p: Path = {pc: [sel], locals: new Map(), heap: new Map([...d.heap, [actionId, {k: 'rec', fields: new Map(), origin: 'input', lazy: {prefix: ''}}]]), wrote: [], nows: 0}
    if (fn.parameters[0]) p = ex.bind(fn.parameters[0].name, d.v, p)
    if (fn.parameters[1]) p = ex.bind(fn.parameters[1].name, {t: 'ref', id: actionId}, p)
    const ends: [Path, V][] = []
    if (fn.body && !ts.isBlock(fn.body)) { const [v, q] = ex.ev(fn.body as ts.Expression, p); ends.push([q, v]) }
    else { const flow = ex.block((fn.body as ts.Block).statements, p); ends.push(...flow.rets, ...(flow.live ? [[flow.live, {t: 'undef'} as V] as [Path, V]] : [])) }
    const written = (q: Path) => [...d.heap.keys()].some(id => id.startsWith('draft.') && q.heap.get(id) !== d.heap.get(id))
    const states: [Path, StateVal][] = ends.map(([q, v]) => {
      const self = v.t === 'ref' && v.id === (d.v as {id?: string}).id
      if (v.t !== 'undef' && !self && written(q)) refuse(fn, `the case reducer for ${type} writes the draft and returns another value (immer throws there)`)
      return [q, materialize(ex, v.t === 'undef' || self ? d.v : v, layout, q, fn)]
    })
    outs.push([sel, joinAll(ex, states, fn)])
    refusals.push(refusalOf(ex))
  }
  // Any other action: the state as it was (a slice's reducer passes it through).
  const same: StateVal = materialize(ex0, stateV, layout, {pc: [], locals: new Map(), heap, wrote: [], nows: 0}, cfg)
  let final = same
  for (let i = outs.length - 1; i >= 0; i--) final = mergeVals(ex0, outs[i]![0], outs[i]![1], final, cfg)
  // A request: {type, ...the fields the case reducers read of the action}.
  const fields: [string, Arg][] = [...s.lazy].filter(([, l]) => l.prefix === '').map(([n, l]) => [l.field, {k: 'input', name: n}])
  const events: Event[] = types.map(t => ({select: {[ev.name]: t}, call: `${opts.entry}.reducer`, args: [{k: 'state'}, {k: 'rec', fields: [['type', {k: 'lit', value: t}], ...fields.filter(([f]) => f !== 'type')]}]}))
  s.notes.add(`a Redux Toolkit slice: ${cases.length} case reducers on immer's draft, any other action passing the state through`)
  return finish(s, {name: opts.entry, shape: 'reducer', file, entry: opts.entry, layout, init, final, refuse: I.or(...refusals), pre: I.T, events, outputs: [], event: ev.name, initSource: initExpr.getText()})
}
