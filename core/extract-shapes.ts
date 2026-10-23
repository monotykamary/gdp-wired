// The shapes the extractor reads (core/extract.ts): step functions over a state (a reducer `(state, action) => state`,
// `useReducer`'s, or several functions over one record, each an event), and classes whose methods write their fields
// (each public method an event, its arguments the request, its result kept as `<method>_result`). Each is executed
// symbolically (core/extract-read.ts) into a Model: the state's variables, where each sits in the code's own values,
// the step's writes, what the code refuses (its throws) and how a request is made of the code.
import ts from 'typescript'
import * as I from './extract-ir.ts'
import type {B} from './extract-ir.ts'
import {type Arg, type Event, Exec, type Heap, type Layout, type MapDecl, type MapObj, type Model, type Path, type Rec, Refusal, type Setup, type Shape, type Sort, type Term, type V, type Var, memberName, program, shapeOf} from './extract-read.ts'

export type ReadOptions = {
  entry: string,
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

function setupOf(code: string, file: string): Setup {
  const {sf, checker} = program(code, file)
  return {checker, sf, names: new Set(), vars: new Map(), maps: new Map(), lazySorts: new Map(), nowRole: 'input', hints: new WeakMap(), notes: new Set(), lazy: new Map()}
}

// The state's tree: a variable per scalar, a heap object per record, a map per keyed field.
function build(ex: Exec, shape: Shape, path: string[], heap: Heap, origin: Rec['origin'], at: ts.Node): {layout: Layout, v: V} {
  const name = path.join('_') || 'state'
  switch (shape.k) {
    case 'num': case 'bool': case 'choice': { const x = ex.newVar(name, shape, 'state'); return {layout: {k: 'scalar', name: x.name}, v: Exec.valueOf(x)} }
    case 'str': return refuse(at, `${name}: a string in the state (strings are in the subset as map keys and inputs only)`)
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
      const ok = (sort.k === 'num' && v.t === 'num') || (sort.k === 'bool' && v.t === 'bool') || (sort.k === 'choice' && (v.t === 'choice' || v.t === 'str'))
      if (!ok) refuse(at, `${layout.name} is set to a ${v.t}`)
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
const termOf = (v: V): Term => (v.t === 'num' ? {s: 'num', e: v.e} : v.t === 'bool' ? {s: 'bool', e: v.e} : v.t === 'choice' ? {s: 'choice', e: v.e} : (() => { throw new Error(`a ${v.t} as a term`) })())
const sameTerm = (a: V, b: V) => (a.t === 'num' || a.t === 'bool' || a.t === 'choice') && (b.t === 'num' || b.t === 'bool' || b.t === 'choice') && I.same(a.e, b.e)
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
  if (ts.isIdentifier(e)) {
    const decl = s.checker.getSymbolAtLocation(e)?.valueDeclaration
    if (decl && ts.isVariableDeclaration(decl) && decl.initializer && decl.parent.flags & ts.NodeFlags.Const) return constValue(decl.initializer, s)
    return refuse(e, `${e.text}: an initial state the subset can't read (give it in init)`)
  }
  return refuse(e, 'an initial state the subset can\'t read (give it in init)')
}
function initLeaves(raw: unknown, layout: Layout, s: Setup, at: ts.Node, out: Record<string, Term> = {}): Record<string, Term> {
  switch (layout.k) {
    case 'scalar': {
      const sort = s.vars.get(layout.name)!.sort
      if (sort.k === 'num' && typeof raw === 'number' && Number.isSafeInteger(raw)) out[layout.name] = {s: 'num', e: I.num(raw)}
      else if (sort.k === 'bool' && typeof raw === 'boolean') out[layout.name] = {s: 'bool', e: raw ? I.T : I.F}
      else if (sort.k === 'choice' && typeof raw === 'string' && sort.values.includes(raw)) out[layout.name] = {s: 'choice', e: I.llit(raw, sort.values)}
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

// --- step functions -------------------------------------------------------------------------------------------------
function findFunction(sf: ts.SourceFile, name: string): ts.FunctionLikeDeclaration {
  for (const st of sf.statements) {
    if (ts.isFunctionDeclaration(st) && (st.name?.text === name || (name === 'default' && st.modifiers?.some(m => m.kind === ts.SyntaxKind.DefaultKeyword)))) return st
    if (ts.isVariableStatement(st)) for (const d of st.declarationList.declarations) if (ts.isIdentifier(d.name) && d.name.text === name && d.initializer) {
      const init = ts.isParenthesizedExpression(d.initializer) ? d.initializer.expression : d.initializer
      if (ts.isArrowFunction(init) || ts.isFunctionExpression(init)) return init
    }
    if (name === 'default' && ts.isExportAssignment(st) && (ts.isArrowFunction(st.expression) || ts.isFunctionExpression(st.expression))) return st.expression
  }
  return refuse(at0(sf), `no function ${name} in the file`)
}
// The string literals the code compares a record's fields with (case labels, ===): those fields are choices.
function literalsOf(body: ts.Node, param: string): Map<string, string[]> {
  const out = new Map<string, string[]>()
  const pathOf = (e: ts.Expression): string | undefined => {
    if (ts.isParenthesizedExpression(e)) return pathOf(e.expression)
    if (ts.isPropertyAccessExpression(e)) { if (ts.isIdentifier(e.expression) && e.expression.text === param) return e.name.text; const p = pathOf(e.expression); return p && `${p}_${e.name.text}` }
    return undefined
  }
  const add = (path: string | undefined, lit: ts.Expression) => { if (path && (ts.isStringLiteral(lit) || ts.isNoSubstitutionTemplateLiteral(lit))) { const xs = out.get(path) ?? []; if (!xs.includes(lit.text)) xs.push(lit.text); out.set(path, xs) } }
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
  const lits = ts.isIdentifier(param.name) ? literalsOf(body, param.name.text) : new Map<string, string[]>()
  // Untyped (JavaScript): its fields as the code reads them, numbers unless compared with string literals.
  if (t.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)) {
    for (const [path, xs] of lits) s.lazySorts.set(`${prefix}${path}`, {k: 'choice', values: [...xs, OTHER]})
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
  const s = setupOf(code, file), names = opts.functions ?? [opts.entry], fns = names.map(n => findFunction(s.sf, n))
  const first = fns[0]!, sp = first.parameters[0] ?? refuse(first, 'a step function takes the state first')
  const st = s.checker.getTypeAtLocation(sp), shape = shapeOf(st, s.checker, sp)
  for (const [i, f] of fns.entries()) {
    const p0 = f.parameters[0] ?? refuse(f, `${names[i]} takes no state`)
    if (s.checker.typeToString(s.checker.getTypeAtLocation(p0)) !== s.checker.typeToString(st)) refuse(p0, `${names[i]} takes another state than ${names[0]}`)
  }
  const ex0 = new Exec(s), heap: Heap = new Map(), {layout, v: stateV} = build(ex0, shape, [], heap, 'input', sp)
  // The initial state: given, a default parameter, useReducer's second argument, or `initialState`.
  let raw: unknown = opts.init, initSource: string | undefined
  if (raw === undefined) {
    let expr: ts.Expression | undefined = sp.initializer
    if (!expr) {
      const visit = (n: ts.Node) => { if (!expr && ts.isCallExpression(n) && ts.isIdentifier(n.expression) && n.expression.text === 'useReducer' && n.arguments[0] && ts.isIdentifier(n.arguments[0]) && names.includes(n.arguments[0].text)) { if (n.arguments.length > 2) refuse(n, 'useReducer with an init function'); expr = n.arguments[1] } ts.forEachChild(n, visit) }
      visit(s.sf)
    }
    if (!expr) for (const stmt of s.sf.statements) if (ts.isVariableStatement(stmt)) for (const d of stmt.declarationList.declarations) if (ts.isIdentifier(d.name) && d.name.text === 'initialState' && d.initializer) expr = d.initializer
    if (!expr) refuse(sp, 'no initial state: a default parameter, useReducer(reducer, initial), a const initialState, or init')
    raw = constValue(expr!, s)
    initSource = expr!.getText()
  }
  const init = initLeaves(raw, layout, s, sp)
  const multi = fns.length > 1, ev = multi ? ex0.newVar('fn', {k: 'choice', values: names}, 'input') : undefined
  const outs: [Path, StateVal][] = [], throws: B[] = [], events: Event[] = []
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
  return finish(s, {name: names[0] === 'default' ? 'reducer' : names[0]!, shape: multi ? 'functions' : 'reducer', file, entry: names.join(','), layout, init, final,
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
    ...(m.event ? {event: m.event} : {}), ...(m.ctorArgs ? {ctorArgs: m.ctorArgs} : {}), ...(s.lazy.size ? {lazy: s.lazy} : {}), ...(m.initSource ? {initSource: m.initSource} : {})}
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
function attempt(code: string, file: string, opts: ReadOptions, written: Set<string>): {model: Model, written: Set<string>} {
  const s = setupOf(code, file), cls = findClass(s.sf, opts.entry), first = written.size === 0
  s.cls = cls
  if (cls.heritageClauses?.length) refuse(cls, 'a class that extends another')
  const ctor = cls.members.find(ts.isConstructorDeclaration)
  type Field = {name: string, shape: Shape, node: ts.Node, init?: ts.Expression}
  const fields: Field[] = []
  for (const m of cls.members) {
    if (ts.isPropertyDeclaration(m)) {
      if (ts.isPrivateIdentifier(m.name)) refuse(m, `${m.name.text}: a #private field (the check reads the object's fields; \`private\` is in the subset)`)
      if (has(m, ts.SyntaxKind.StaticKeyword)) refuse(m, 'a static field (state shared by every object)')
      fields.push({name: memberName(m.name), shape: shapeOf(s.checker.getTypeAtLocation(m), s.checker, m), node: m, ...(m.initializer ? {init: m.initializer} : {})})
    } else if (ts.isSetAccessorDeclaration(m)) refuse(m, 'a setter')
    else if (ts.isMethodDeclaration(m) && ts.isPrivateIdentifier(m.name)) refuse(m, 'a #private method')
    else if (ts.isIndexSignatureDeclaration(m) || ts.isClassStaticBlockDeclaration(m)) refuse(m, 'a static block or index signature')
  }
  for (const p of ctor?.parameters ?? []) if (ts.isParameterPropertyDeclaration(p, ctor!)) fields.push({name: (p.name as ts.Identifier).text, shape: shapeOf(s.checker.getTypeAtLocation(p), s.checker, p), node: p})
  const ex0 = new Exec(s)
  const constant = (f: Field) => !first && !written.has(f.name) && f.shape.k !== 'map'
  // The state's variables first (so they keep the fields' names), then the params.
  const stateHeap: Heap = new Map(), thisFields = new Map<string, V>(), layout: [string, Layout][] = [], stateLayout: [string, Layout][] = []
  for (const f of fields) if (!constant(f)) { const r = build(ex0, f.shape, [f.name], stateHeap, 'this', f.node); thisFields.set(f.name, r.v); layout.push([f.name, r.layout]); stateLayout.push([f.name, r.layout]) }
  // The constructor, run over its arguments (the params): what each field starts at, and what it refuses (the pre).
  s.nowRole = 'param'
  const ctorArgs: string[] = [], ctorHeap: Heap = new Map(), ctorFields = new Map<string, V>(fields.map(f => [f.name, {t: 'undef'}]))
  ctorHeap.set('this', {k: 'rec', fields: ctorFields, origin: 'fresh'})
  let cp: Path = {pc: [], locals: new Map(), heap: ctorHeap, wrote: [], nows: 0}
  const exC = new Exec(s)
  s.ctor = true
  for (const p of ctor?.parameters ?? []) {
    if (!ts.isIdentifier(p.name)) refuse(p, 'a destructured constructor argument')
    const sh = shapeOf(s.checker.getTypeAtLocation(p), s.checker, p)
    if (sh.k !== 'num' && sh.k !== 'bool' && sh.k !== 'choice') refuse(p, `${p.name.getText()}: a constructor argument that isn't a number, a boolean or a union of literals`)
    const x = exC.newVar(p.name.getText(), sh as Sort, 'param', 'a constructor argument')
    ctorArgs.push(x.name)
    cp = exC.bind(p.name, Exec.valueOf(x), cp)
    if (ts.isParameterPropertyDeclaration(p, ctor!)) { const o = cp.heap.get('this') as Rec; cp = {...cp, heap: new Map(cp.heap).set('this', {...o, fields: new Map(o.fields).set(p.name.text, Exec.valueOf(x))})} }
  }
  const empty = new Set<string>()
  for (const f of fields) if (f.init) {
    if (f.shape.k === 'map') { if (!isMapInit(f.init)) refuse(f.init, `${f.name} starts with entries (a map starts empty in the subset)`); empty.add(f.name); continue }
    const [v, q] = exC.ev(f.init, cp); cp = q
    const o = cp.heap.get('this') as Rec
    cp = {...cp, heap: new Map(cp.heap).set('this', {...o, fields: new Map(o.fields).set(f.name, v)})}
  }
  const body = (ctor?.body?.statements ?? []).filter(st => {
    if (!ts.isExpressionStatement(st) || !ts.isBinaryExpression(st.expression) || st.expression.operatorToken.kind !== ts.SyntaxKind.EqualsToken) return true
    const l = st.expression.left
    if (!ts.isPropertyAccessExpression(l) || l.expression.kind !== ts.SyntaxKind.ThisKeyword) return true
    const f = fields.find(x => x.name === memberName(l.name))
    if (f?.shape.k !== 'map') return true
    if (!isMapInit(st.expression.right)) refuse(st, `${f.name} starts with entries (a map starts empty in the subset)`)
    empty.add(f.name)
    return false
  })
  const cflow = exC.block(body, cp)
  if (cflow.rets.some(([, v]) => v.t !== 'undef')) refuse(ctor!, 'a constructor that returns a value')
  const ends = [...cflow.rets.map(([p]) => p), ...(cflow.live ? [cflow.live] : [])]
  const cend = ends.reduceRight<Path | undefined>((acc, x) => exC.merge(x, acc, ctor ?? cls), undefined) ?? refuse(ctor ?? cls, 'a constructor that always throws')
  s.ctor = false
  const pre = I.not(refusalOf(exC))
  const made = (cend.heap.get('this') as Rec).fields
  for (const f of fields) if (f.shape.k === 'map' && !empty.has(f.name)) refuse(f.node, `${f.name}: a map field must start as new Map() or {}`)
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
  // The methods: each public one an event, run from the state as variables.
  const methods = cls.members.filter((m): m is ts.MethodDeclaration => ts.isMethodDeclaration(m) && !has(m, ts.SyntaxKind.StaticKeyword) && !has(m, ts.SyntaxKind.PrivateKeyword) && !has(m, ts.SyntaxKind.ProtectedKeyword))
    .filter(m => !opts.methods || opts.methods.includes(memberName(m.name)))
  if (opts.methods) for (const n of opts.methods) if (!methods.some(m => memberName(m.name) === n)) refuse(cls, `no public method ${n}`)
  if (!methods.length) refuse(cls, 'a class with no public methods (no events)')
  const mnames = methods.map(m => memberName(m.name)), ev = ex0.newVar('method', {k: 'choice', values: mnames}, 'input'), evL = {op: 'var' as const, name: ev.name, values: mnames}
  const outputs: string[] = [], perMethod: {sel: B, sv: StateVal, refuse: B}[] = [], events: Event[] = []
  const outVars = new Map<string, Var>()
  for (const m of methods) {
    const name = memberName(m.name), sig = s.checker.getSignatureFromDeclaration(m)!, rt = s.checker.getReturnTypeOfSignature(sig)
    if (has(m, ts.SyntaxKind.AsyncKeyword) || m.asteriskToken) refuse(m, `${name}: an async or generator method (its steps interleave with others)`)
    if (!(rt.flags & (ts.TypeFlags.Void | ts.TypeFlags.Undefined))) {
      const sh = shapeOf(rt, s.checker, m)
      if (sh.k !== 'num' && sh.k !== 'bool' && sh.k !== 'choice') refuse(m, `${name} returns ${sh.k === 'str' ? 'a string' : 'a compound value'} (a result kept is a number, a boolean or a union of literals)`)
      const x = ex0.newVar(`${name}_result`, sh as Sort, 'state', `what ${name} returned, at the step that called it (its default at others)`)
      outVars.set(name, x); outputs.push(x.name)
      layout.push([`${name}()`, {k: 'scalar', name: x.name}])
    }
  }
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
      for (const [mn, x] of outVars) sv.leaves.set(x.name, mn === name ? (rv.t === 'undef' ? refuse(m, `${name} returns nothing on some path`) : outValue(ex, rv, x, rp, m)) : Exec.defaultOf(x.sort))
      return [rp, sv]
    })
    perMethod.push({sel, sv: joinAll(ex, outs, m), refuse: refusalOf(ex)})
    events.push({select: {[ev.name]: name}, call: name, args})
  }
  // The methods together: each variable by the method called.
  let final = perMethod.at(-1)!.sv
  for (let i = perMethod.length - 2; i >= 0; i--) final = mergeVals(ex0, perMethod[i]!.sel, perMethod[i]!.sv, final, cls)
  for (const x of outVars.values()) init[x.name] = termOf(Exec.defaultOf(x.sort))
  const wrote = new Set<string>()
  for (const [f, lay] of layout) {
    const leaves: string[] = []
    const walk = (l: Layout) => { if (l.k === 'scalar') leaves.push(l.name); else if (l.k === 'rec') l.fields.forEach(([, x]) => walk(x)); else if (l.k === 'map') leaves.push(`map:${l.name}`) }
    walk(lay)
    if (leaves.some(n => (n.startsWith('map:') ? final.maps.get(n.slice(4)) !== undefined : !sameTerm(final.leaves.get(n)!, Exec.valueOf(s.vars.get(n)!))))) wrote.add(f)
  }
  const model = finish(s, {name: opts.entry, shape: 'class', file, entry: opts.entry, layout: {k: 'rec', fields: layout}, init, final, refuse: I.or(...perMethod.map(x => I.and(x.sel, x.refuse))), pre, events, outputs, event: ev.name, ctorArgs})
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
