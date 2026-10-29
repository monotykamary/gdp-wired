// The extractor's shared step IR and its executor: one structure for every language read through a native reader.
// A reader (core/py/reader.py: Python's own `ast`) lowers a module into the IR below, as JSON; this file executes the
// steps symbolically into the Model core/extract-read.ts defines (the TypeScript and Go front ends' own), and
// core/extract.ts's fromModel prints, builds and checks it. The check is core/extract-check.ts's `drive`: the code's
// side is a harness in the code's own language (core/py/harness.py) spoken to in JSON lines, which makes the object,
// sets it to a state, calls it with the rule's requests and prints every state. Nothing here is trusted: the rule is
// adopted only where the run of both agrees, and what the subset doesn't read is refused where a step reaches it.
//
// Where a language's semantics differ, the IR says so with explicit operations (the reader chooses them): an integer
// type's width and what it does past its range (`int`: none for an unbounded one, Python's; wrap, trap or ub for
// fixed ones, a later reader's), division's rounding (floor for Python's // and %, trunc for C's, Go's and Rust's),
// truthiness (`truthy`), a missing value (`none`, `opt`), a failure (`fail`: an exception, a panic, an error value,
// each the step's refusal or, with failures: 'kept', its result).
//
// What a caller states about the code's boundary, each printed in the notes and enforced by the check:
//   answers: a call of other code whose result is an input of the request (the check stubs it with that input);
//   skip:    a call left out (logging, an alert, a context manager): its value is kept only where nothing the rule
//            keeps reads it, and the check runs it as it is;
//   stores:  an object of other code held as a key-value store (a cache client): its get and set methods read and
//            write a map of the state, one per key template; its expiry, eviction and replication are left out, and the
//            check gives the code a store that keeps what is set.
import * as I from './extract-ir.ts'
import type {B, K, L, N} from './extract-ir.ts'
import {type Arg, type Event, type Layout, type MapDecl, type Model, Refusal, type Term, type Var, mergeWrites} from './extract-read.ts'
import {type Extraction, fromModel} from './extract.ts'
import type {Rule} from './dsl.ts'
import type {Sorts} from './extract-print.ts'
import {type CodeSide, type Coverage, type Evidence, type Snap, Outside, constantsOf, draw, drive} from './extract-check.ts'

// --- the IR (what a reader emits) -----------------------------------------------------------------------------------
export type SType =
  | {k: 'int' | 'float' | 'bool' | 'str' | 'none' | 'any' | 'lock'} | {k: 'choice', values: string[]} | {k: 'opt', of: SType}
  | {k: 'rec', name: string} | {k: 'map', key: SType, val: SType} | {k: 'list', of: SType} | {k: 'opaque', why: string}
export type Patch = {mod?: string, path?: string[], self?: string}
export type SX = {e: string, p: string, text?: string, [k: string]: unknown}
export type SS = {s: string, p: string, [k: string]: unknown}
export type SParam = {name: string, t: SType, dflt?: SX, kw?: boolean, self?: boolean, star?: number}
export type SFunc = {id: string, name: string, cls?: string, p: string, span: [string, number, number], params: SParam[], ret: SType, body: SS[], async?: boolean, static?: boolean, decorators: {name: string, text: string, p: string}[]}
export type SRec = {name: string, short: string, fields: {name: string, t: SType, dflt?: SX}[], methods: Record<string, string | null>, kinds: string[], own: boolean, module: string, p: string}
export type SModule = {lang: string, file: string, path: string, module: string, root: string, entries: ({k: 'class', rec: string} | {k: 'func', id: string} | {k: 'missing', name: string})[], recs: Record<string, SRec>, funcs: Record<string, SFunc>, error?: string}

export type StoreDecl = {get?: string[], set?: string[], delete?: string[], value?: 'int' | 'float' | 'str', attrs?: Record<string, null | boolean | number | string>, async?: Record<string, boolean>}
export type StepOptions = {
  // The class, or the functions (each a request), and the methods read (by default the public ones).
  entry: string | string[], methods?: string[],
  answers?: Record<string, string>, skip?: string[], stores?: Record<string, StoreDecl>,
  // A failure (an exception, a panic) is the step's refusal (the default), or its result kept: the step taken, the
  // state as it was, `failed` true (to state laws about when the code refuses).
  failures?: 'refuse' | 'kept',
  onError?: 'refuse' | 'discard',
  domains?: Record<string, 'nat' | 'int'>,
  check?: {runs?: number, depth?: number, states?: number, seed?: number, bound?: number, probes?: boolean}
}

// --- values ---------------------------------------------------------------------------------------------------------
type V =
  | {t: 'num', e: N} | {t: 'bool', e: B} | {t: 'str', e: K} | {t: 'choice', e: L}
  | {t: 'none'} | {t: 'opt', has: B, v: V}
  | {t: 'ref', id: string} | {t: 'cell', map: string, key: K}
  // A string made by a format with one hole (a store's key): its template and the hole's value.
  | {t: 'fmt', tpl: string, k: K}
  | {t: 'opaque', why: string}
  | {t: 'ext', q: string, text: string, patch?: Patch}
  | {t: 'fn', id: string, self?: V} | {t: 'cls', rec: string, patch?: Patch} | {t: 'builtin', n: string} | {t: 'lib', q: string}
  | {t: 'sattr', store: string, path: string}
  | {t: 'tuple', xs: V[]} | {t: 'lock'}
type Origin = 'state' | 'input' | 'fresh'
type Obj =
  | {k: 'rec', ty: string, f: Map<string, V>, origin: Origin, lazy?: string, moved?: boolean}
  | {k: 'map', decl: MapDecl, val: SType, w?: {key: K, has: B, vals: Map<string, V>}, origin: Origin}
  | {k: 'store', name: string}
type Path = {pc: B[], locals: Map<string, V>, heap: Map<string, Obj>, called: string[]}
type Flow = {live?: Path, rets: [Path, V][]}
// What the harness is told: where each leaf of the state is, how each argument is made, what each stub answers.
export type Leaf = {name: string, path: string[], kind: 'num' | 'bool' | 'str' | 'choice' | 'none' | 'map' | 'frame', float?: boolean, cls?: string, fields?: {name: string, float?: boolean}[], key?: 'num' | 'str', store?: string, tpl?: string}
export type PArg = {k: 'in', name: string, float?: boolean, z?: Raw} | {k: 'opt', none: string, v: PArg} | {k: 'rec', cls: string, f: [string, PArg][]} | {k: 'inert'} | {k: 'store', name: string} | {k: 'dflt'}
export type Answer = {key: string, patch: Patch, async: boolean, inputs: {name: string, none?: string, float?: boolean}, sort: string}
export type StepRead = {madeAt?: string, model: Model, leaves: Leaf[], args: Record<string, [string, PArg][]>, answers: Answer[], ctor: [string, PArg][], kept: boolean, arms: [string, number][], cls?: string, stores: Record<string, StoreDecl>, results: Record<string, 'none' | 'scalar' | 'maybe'>}

const where = (x: {p: string}) => x.p || '?'
const refuse = (x: {p: string} | string, what: string): never => { throw new Refusal(typeof x === 'string' ? x : where(x), what) }
const RESERVED = new Set(['rule', 'nat', 'int', 'bool', 'when', 'min', 'max', 'all', 'any', 'not', 'yes', 'no', 'lit', 'str', 'record', 'oneOf', 'intern', 'Int', 'forall'])
const keyV = (v: V | Obj): string => JSON.stringify(v, (_, x) => (x instanceof Map ? [...x.entries()] : x))
const constOf = (v: V): number | undefined => (v.t === 'num' && v.e.op === 'const' ? v.e.v : undefined)

// The sorts a type string names (an answer's): int, float, bool, str, a choice of quoted strings, each `| None`.
function sortOfText(s: string, at: string): {t: SType} {
  const parts = s.split('|').map(x => x.trim()).filter(Boolean), none = parts.includes('None'), rest = parts.filter(x => x !== 'None')
  const one = (): SType => {
    if (rest.length && rest.every(x => /^['"].*['"]$/.test(x))) return {k: 'choice', values: rest.map(x => x.slice(1, -1))}
    if (rest.length !== 1) return refuse(at, `the answer type ${JSON.stringify(s)} (int, float, bool, str or quoted strings, each with | None)`)
    const k = rest[0]!
    if (k === 'int' || k === 'float' || k === 'bool' || k === 'str') return {k}
    return refuse(at, `the answer type ${JSON.stringify(s)} (int, float, bool, str or quoted strings, each with | None)`)
  }
  const t = one()
  return {t: none ? {k: 'opt', of: t} : t}
}

// --- the executor ---------------------------------------------------------------------------------------------------
export class Stepper {
  readonly vars = new Map<string, Var>()
  readonly inputs: Var[] = []
  readonly params: Var[] = []
  readonly notes = new Set<string>()
  readonly refusals: B[] = []
  fails: B[] = []
  failPaths: Path[] = []
  readonly maps: MapDecl[] = []
  readonly answers = new Map<string, Answer>()
  readonly arms = new Set<string>()
  readonly hints = new WeakMap<object, string>()
  readonly lazy = new Map<string, {prefix: string, ty: string, args: [string, PArg][], vals: Map<string, V>}>()
  readonly initHeap = new Map<string, Obj>()
  readonly storeMaps = new Map<string, {store: string, tpl: string, id: string, decl: MapDecl}>()
  frames: string[] = []
  fieldNames = new Set<string>()
  readonly frozen = new Set<string>()
  now?: Var
  madeAt?: Var
  method = ''
  fresh = 0
  init = false
  constructor(readonly mod: SModule, readonly opts: StepOptions) {}

  rec(name: string, at: {p: string}): SRec { return this.mod.recs[name] ?? refuse(at, `${name}: a type the reader didn't read`) }
  newVar(name: string, sort: Var['sort'], role: Var['role'], note?: string): Var {
    let n = name.replace(/^_+/, '').replace(/[^\w$]/g, '_') || 'x'
    if (/^\d/.test(n)) n = `_${n}`
    // (a constructor's argument named as a field it sets: the field keeps the name, the argument is the initial one)
    if (role === 'param' && this.fieldNames.has(n)) n = `${n}0`
    while (this.vars.has(n) || RESERVED.has(n)) n = `${n}_`
    const v: Var = {name: n, sort, role, ...(note ? {note} : {})}
    this.vars.set(n, v)
    if (role === 'input') this.inputs.push(v)
    if (role === 'param') this.params.push(v)
    return v
  }
  valueOf(v: Var): V {
    return v.sort.k === 'num' ? {t: 'num', e: I.nvar(v.name)} : v.sort.k === 'bool' ? {t: 'bool', e: I.bvar(v.name)} : v.sort.k === 'choice' ? {t: 'choice', e: {op: 'var', name: v.name, values: v.sort.values}} : {t: 'str', e: {op: 'svar', name: v.name}}
  }
  // A scalar sort, or why the type isn't one.
  scalar(t: SType): Var['sort'] | undefined {
    return t.k === 'int' || t.k === 'float' ? {k: 'num'} : t.k === 'bool' ? {k: 'bool'} : t.k === 'str' ? {k: 'str'} : t.k === 'choice' ? {k: 'choice', values: t.values} : undefined
  }
  why(t: SType): string {
    if (t.k === 'opaque') return t.why
    if (t.k === 'any') return 'a value of no type the code states'
    if (t.k === 'list') return 'a list (lists are outside the Python subset)'
    if (t.k === 'map') return 'a dict'
    return t.k
  }
  // An input of a type: its variables, the value, and how the harness makes it.
  input(name: string, t: SType, at: {p: string}, p: Path, role: Var['role'] = 'input'): [V, PArg] {
    const s = this.scalar(t)
    if (s) { const v = this.newVar(name, s, role); return [this.valueOf(v), {k: 'in', name: v.name, z: zeroRaw(s), ...(t.k === 'float' ? {float: true} : {})}] }
    if (t.k === 'opt') {
      if (t.of.k === 'rec') {
        const none = this.newVar(`${name}_none`, {k: 'bool'}, role, `whether ${name} is None`)
        const [v, a] = this.input(name, t.of, at, p, role)
        return [{t: 'opt', has: I.not(I.bvar(none.name)), v}, {k: 'opt', none: none.name, v: a}]
      }
      const inner = this.scalar(t.of)
      if (!inner) return refuse(at, `${name}: an optional ${this.why(t.of)}`)
      const v = this.newVar(name, inner, role, `0 where ${name} is None`), none = this.newVar(`${name}_none`, {k: 'bool'}, role, `whether ${name} is None`)
      return [{t: 'opt', has: I.not(I.bvar(none.name)), v: this.valueOf(v)}, {k: 'opt', none: none.name, v: {k: 'in', name: v.name, z: zeroRaw(inner), ...(t.of.k === 'float' ? {float: true} : {})}}]
    }
    if (t.k === 'none') return [{t: 'none'}, {k: 'dflt'}]
    if (t.k === 'rec' && role === 'input') {
      // An object the caller gives: its fields read are inputs, each made where it is first read.
      const id = `in:${name}:${this.fresh++}`, args: [string, PArg][] = []
      p.heap.set(id, {k: 'rec', ty: t.name, f: new Map(), origin: 'input', lazy: name})
      this.lazy.set(id, {prefix: name, ty: t.name, args, vals: new Map()})
      return [{t: 'ref', id}, {k: 'rec', cls: t.name, f: args}]
    }
    // A value of another type: kept only where nothing the rule keeps reads it (the harness gives an inert one).
    return [{t: 'opaque', why: `${name}: ${this.why(t)}`}, {k: 'inert'}]
  }
  // The clock: one input a step.
  clock(at: {p: string}, p: Path): [V, Path] {
    if (p.called.includes('$now')) return refuse(at, 'the clock read twice in one step (the subset reads it once a step)')
    // (in the constructor, the time the object is made: a param)
    if (this.init) { this.madeAt ??= this.newVar('made_at', {k: 'num'}, 'param', 'Date.now() (here time.time()): the time the object is made'); return [{t: 'num', e: I.nvar(this.madeAt.name)}, {...p, called: [...p.called, '$now']}] }
    this.now ??= this.newVar('now', {k: 'num'}, 'input', 'Date.now() (here the clock, time.time()): the time of the request, an input')
    return [{t: 'num', e: I.nvar(this.now.name)}, {...p, called: [...p.called, '$now']}]
  }

  // --- paths ----------------------------------------------------------------------------------------------------------
  cond(p: Path): B { return I.and(...p.pc) }
  // (a negated disjunction as its negated parts, so a later test of one of them is decided)
  assume(p: Path, c: B): Path { const cs = c.op === 'not' && c.x.op === 'or' ? c.x.xs.map(I.not) : c.op === 'and' ? c.xs : [c]; const kept = cs.filter(x => !(x.op === 'const' && x.v)); return kept.length ? {...p, pc: [...p.pc, ...kept]} : p }
  // A failure of the code where c holds on this path (an exception raised): the step's refusal, or its result.
  fail(p: Path, c: B, at: {p: string}, what: string) {
    const w = I.and(this.cond(p), c)
    if (w.op === 'const' && !w.v) return
    if (this.init) { this.fails.push(w); return }
    // Failures kept with what the step wrote before them (the caller sees both): the path goes on to the step's end.
    if (this.opts.failures === 'kept' && this.opts.onError !== 'discard') { this.failPaths.push(this.assume(p, c)); this.fails.push(w); this.notes.add(`${this.method}: ${what} (${at.p}) is the step's failure, kept as its result (with what the step wrote before it)`); return }
    if (this.opts.onError !== 'discard' && this.changed(p)) refuse(at, `${what} after the state is written (the caller would see the object changed and the call failed; with onError: 'discard' the caller is taken to drop what a failed call wrote)`)
    this.fails.push(w)
    this.notes.add(`${this.method}: ${what} (${at.p}) is ${this.opts.failures === 'kept' ? 'the step\'s failure, kept as its result' : 'the step\'s refusal'}`)
  }
  changed(p: Path): boolean {
    for (const [id, o] of p.heap) {
      const i = this.initHeap.get(id)
      if (!i || (o.k === 'rec' && o.origin !== 'state') || (o.k === 'map' && o.origin !== 'state')) continue
      if (o.k === 'map' ? !!o.w : keyV(o) !== keyV(i)) return true
    }
    return false
  }
  join(ps: Path[], at: {p: string}): Path | undefined {
    if (!ps.length) return undefined
    let acc = ps.at(-1)!
    for (let i = ps.length - 2; i >= 0; i--) acc = this.merge(ps[i]!, acc, at)
    return acc
  }
  merge(a: Path, b: Path, at: {p: string}): Path {
    let k = 0
    while (k < a.pc.length && k < b.pc.length && I.same(a.pc[k]!, b.pc[k]!)) k++
    const c = I.and(...a.pc.slice(k)), pc = a.pc.slice(0, k)
    if (c.op === 'const') return c.v ? {...a, pc} : {...b, pc}
    const locals = new Map<string, V>()
    for (const [n, x] of a.locals) { const y = b.locals.get(n); if (y) { try { locals.set(n, this.ite(c, x, y, at)) } catch (e) { if (!(e instanceof Refusal)) throw e; locals.set(n, {t: 'opaque', why: e.what}) } } }
    const heap = new Map<string, Obj>()
    for (const [id, x] of a.heap) { const y = b.heap.get(id); heap.set(id, y ? this.mergeObj(c, x, y, at) : x) }
    for (const [id, y] of b.heap) if (!heap.has(id)) heap.set(id, y)
    return {pc, locals, heap, called: [...new Set([...a.called, ...b.called])]}
  }
  mergeObj(c: B, a: Obj, b: Obj, at: {p: string}): Obj {
    if (a === b) return a
    if (a.k === 'rec' && b.k === 'rec') {
      const f = new Map<string, V>()
      for (const [n, x] of a.f) { const y = b.f.get(n); f.set(n, y ? this.ite(c, x, y, at) : x) }
      for (const [n, y] of b.f) if (!f.has(n)) f.set(n, y)
      return {...a, f, moved: a.moved || b.moved}
    }
    if (a.k === 'map' && b.k === 'map') {
      const w = mergeWrites(c, a.w, b.w, key => this.baseCell(a.decl, key), (c2, x, y) => this.ite(c2, x, y, at))
      return {...a, ...(w ? {w} : {})}
    }
    if (a.k === 'store' && b.k === 'store') return a
    return refuse(at, 'an object of two kinds by a condition')
  }
  // A value by cases.
  ite(c: B, a: V, b: V, at: {p: string}): V {
    if (c.op === 'const') return c.v ? a : b
    if (a === b || keyV(a) === keyV(b)) return a
    if (a.t === 'opaque') return a
    if (b.t === 'opaque') return b
    if (a.t === 'num' && b.t === 'num') return {t: 'num', e: I.nite(c, a.e, b.e)}
    if (a.t === 'bool' && b.t === 'bool') return {t: 'bool', e: I.bite(c, a.e, b.e)}
    if (a.t === 'str' && b.t === 'str') return {t: 'str', e: I.kite(c, a.e, b.e)}
    if (a.t === 'choice' && b.t === 'choice') return {t: 'choice', e: I.lite(c, a.e, b.e)}
    if (a.t === 'choice' && b.t === 'str' && b.e.op === 'slit') return this.ite(c, a, {t: 'choice', e: I.llit(b.e.value, (a.e as {values: string[]}).values)}, at)
    if (b.t === 'choice' && a.t === 'str' && a.e.op === 'slit') return this.ite(c, {t: 'choice', e: I.llit(a.e.value, (b.e as {values: string[]}).values)}, b, at)
    if (a.t === 'none' && b.t === 'none') return a
    if (a.t === 'none') return b.t === 'opt' ? {t: 'opt', has: I.and(I.not(c), b.has), v: b.v} : {t: 'opt', has: I.not(c), v: b}
    if (b.t === 'none') return a.t === 'opt' ? {t: 'opt', has: I.and(c, a.has), v: a.v} : {t: 'opt', has: c, v: a}
    if (a.t === 'opt' || b.t === 'opt') {
      const oa = a.t === 'opt' ? a : {has: I.T, v: a}, ob = b.t === 'opt' ? b : {has: I.T, v: b}
      return {t: 'opt', has: I.bite(c, oa.has, ob.has), v: this.ite(c, oa.v, ob.v, at)}
    }
    if (a.t === 'tuple' && b.t === 'tuple' && a.xs.length === b.xs.length) return {t: 'tuple', xs: a.xs.map((x, i) => this.ite(c, x, b.xs[i]!, at))}
    if (a.t === 'ref' && b.t === 'ref') return refuse(at, 'one of two objects by a condition')
    return refuse(at, `a value that is a ${a.t} on one path and a ${b.t} on another`)
  }
  baseCell(d: MapDecl, key: K): {has: B, vals: Map<string, V>} {
    const vals = new Map<string, V>(d.fields.map(f => [f.name, f.sort.k === 'num' ? {t: 'num', e: {op: 'cell', map: d.name, key, field: f.name}} : f.sort.k === 'choice' ? {t: 'choice', e: {op: 'cell', map: d.name, key, field: f.name, values: f.sort.values}} : {t: 'bool', e: {op: 'cell', map: d.name, key, field: f.name}}]))
    return {has: {op: 'cell', map: d.name, key, field: 'has'}, vals}
  }

  // A value that may be None, read where the path has decided which (after `if x is None: return`).
  narrow(v: V, p: Path): V {
    if (v.t !== 'opt') return v
    const c = this.cond(p)
    if (I.and(c, I.not(v.has)).op === 'const') return this.narrow(v.v, p)
    if (I.and(c, v.has).op === 'const') return {t: 'none'}
    return v
  }
  // --- conversions ----------------------------------------------------------------------------------------------------
  // Python's truthiness, made explicit: a later reader's `if` reads a boolean only.
  truthy(v: V, at: {p: string}, p?: Path): B {
    switch (v.t) {
      case 'bool': return v.e
      case 'num': return I.not(I.cmp('=', v.e, I.num(0)))
      case 'str': return I.not(I.keq(v.e, {op: 'slit', value: ''}))
      case 'choice': return (v.e as {values: string[]}).values.includes('') ? I.not(I.is(v.e, '')) : I.T
      case 'none': return I.F
      case 'opt': return I.and(v.has, this.truthy(v.v, at, p))
      case 'ref': {
        // An object is true unless its class (or a base) defines __bool__ or __len__; a dict's truth is whether it is
        // empty, which the subset doesn't read.
        const o = (p?.heap ?? this.initHeap).get(v.id)
        if (o?.k === 'store') return I.T
        if (o?.k === 'rec' && this.plainTruth(o.ty)) return I.T
        return refuse(at, `${(at as SX).text ?? ''}: the truth of ${o?.k === 'map' ? 'a dict (whether it is empty)' : 'an object whose class may define __bool__ or __len__'}`)
      }
      case 'cell': case 'fmt': case 'fn': case 'cls': case 'lock': return I.T
      case 'builtin': case 'ext': case 'lib': case 'opaque': case 'sattr': case 'tuple': break
    }
    return refuse(at, `${(at as SX).text ?? ''}: the truth of ${v.t === 'opaque' ? v.why : `a ${v.t}`}`)
  }
  plainTruth(ty: string): boolean {
    const r = this.mod.recs[ty]
    return !!r && !('__bool__' in r.methods) && !('__len__' in r.methods) && !r.kinds.includes('typeddict') && !r.kinds.some(k => k.startsWith('outside-base:'))
  }
  // A number, where the code reads one (a failure where it is None: Python raises a TypeError).
  numOf(v: V, at: SX, p: Path): N {
    if (v.t === 'num') return v.e
    if (v.t === 'opt') { this.fail(p, I.not(v.has), at, `${at.text ?? 'a value'} is None where a number is read (a TypeError)`); return this.numOf(v.v, at, p) }
    if (v.t === 'none') { this.fail(p, I.T, at, `${at.text ?? 'a value'} is None where a number is read (a TypeError)`); return I.num(0) }
    if (v.t === 'bool') return refuse(at, `${at.text}: a boolean read as a number`)
    return refuse(at, `${at.text ?? ''}: ${v.t === 'opaque' ? v.why : `a ${v.t} where a number is read`}`)
  }
  keyOf(v: V, at: SX): K {
    if (v.t === 'num') return {op: 'num', e: v.e}
    if (v.t === 'str') return v.e
    if (v.t === 'choice' && v.e.op === 'lit') return {op: 'slit', value: v.e.value}
    return refuse(at, `${at.text ?? ''}: a key of ${v.t === 'opaque' ? v.why : `a ${v.t}`} (a map's keys are integers or strings)`)
  }

  // --- the program ----------------------------------------------------------------------------------------------------
  func(id: string, at: {p: string}): SFunc { return this.mod.funcs[id] ?? refuse(at, `${id}: no function the reader read`) }
  // A function or a method inlined: its parameters bound, its body run, its returns joined.
  callFunc(f: SFunc, self: V | undefined, args: V[], kw: [string, V][], at: SX, p0: Path, awaited: boolean): [V, Path] {
    if (f.async && !awaited) return refuse(at, `${f.name}: a coroutine made and not awaited`)
    if (this.frames.includes(f.id)) return refuse(at, `${f.name}: a recursive call`)
    for (const d of f.decorators) if (!['staticmethod', 'classmethod', 'property', 'override', 'typing.override', 'abstractmethod'].includes(d.name) && !this.skipped([d.name, d.text])) refuse(d, `@${d.text}: a decorator (one of other code changes what the method does; skip it to take it as transparent)`)
    for (const d of f.decorators) if (this.skipped([d.name, d.text])) this.notes.add(`@${d.text} on ${f.name}: taken as transparent (skip)`)
    this.arm(f.body)
    const locals = new Map<string, V>()
    const ps = f.params.filter(x => !x.star)
    let i = 0, q = p0
    for (const pa of ps) {
      let v: V | undefined
      if (pa.self && !f.static) v = self ?? refuse(at, `${f.name}: a method called without its object`)
      else if (!pa.kw && i < args.length) v = args[i++]
      else { const k = kw.find(([n]) => n === pa.name); if (k) v = k[1] }
      if (!v && pa.dflt) { const [d, q2] = this.ev(pa.dflt, q); v = d; q = q2 }
      if (!v) return refuse(at, `${f.name}(${pa.name}): an argument not given`)
      locals.set(pa.name, v)
    }
    if (i < args.length || kw.some(([n]) => !ps.some(x => x.name === n))) {
      if (f.params.some(x => x.star)) return refuse(at, `${f.name}: *args or **kwargs given`)
      return refuse(at, `${f.name}: more arguments than it takes`)
    }
    const saved = q.locals
    this.frames.push(f.id)
    let flow: Flow
    try { flow = this.block(f.body, {...q, locals}) } finally { this.frames.pop() }
    const rets: [Path, V][] = [...flow.rets, ...(flow.live ? [[flow.live, {t: 'none'} as V] as [Path, V]] : [])]
    if (!rets.length) return [{t: 'none'}, {...q, pc: [...q.pc, I.F], locals: saved}]
    const joined = this.join(rets.map(([r, v]) => ({...r, locals: new Map([['$ret', v]])})), at)!
    return [joined.locals.get('$ret')!, {...joined, locals: saved}]
  }

  // A branch arm the step runs: its first statement's line, counted by the harness's line events.
  arm(ss: SS[]) { const s0 = ss.find(x => x.s !== 'import'); if (s0) { const m = /^(.*):(\d+):\d+$/.exec(s0.p); if (m) this.arms.add(`${m[1]}:${m[2]}`) } }
  // --- statements -----------------------------------------------------------------------------------------------------
  block(ss: SS[], p: Path): Flow {
    let live: Path | undefined = p
    const rets: [Path, V][] = []
    for (const s of ss) {
      if (!live) break
      const f = this.stmt(s, live)
      rets.push(...f.rets)
      live = f.live
    }
    return {...(live ? {live} : {}), rets}
  }
  stmt(s: SS, p: Path): Flow {
    switch (s.s) {
      case 'expr': { const [, q] = this.ev(s.x as SX, p); return {live: q, rets: []} }
      case 'set': {
        // A local the subset can't compute, from an expression with no calls (nothing it could change): kept as a value
        // refused wherever the rule would read it.
        let r: [V, Path]
        try { r = this.ev(s.x as SX, p) } catch (e) { if (!(e instanceof Refusal) || (s.to as SX).e !== 'var' || !callFree(s.x as SX)) throw e; r = [{t: 'opaque', why: `${e.where}: ${e.what}`}, p] }
        return {live: this.assign(s.to as SX, r[0], s, r[1], s.t as SType | undefined), rets: []}
      }
      case 'if': {
        const [cv, q] = this.ev(s.c as SX, p)
        const c = this.truthy(cv, s.c as SX, q)
        if (!(c.op === 'const' && !c.v)) this.arm(s.then as SS[])
        if (!(c.op === 'const' && c.v)) this.arm(s.else as SS[])
        const t = c.op === 'const' && !c.v ? undefined : this.block(s.then as SS[], this.assume(q, c))
        const e = c.op === 'const' && c.v ? undefined : this.block(s.else as SS[], this.assume(q, I.not(c)))
        const lives = [t?.live, e?.live].filter((x): x is Path => !!x)
        const live = this.join(lives, s)
        return {...(live ? {live} : {}), rets: [...(t?.rets ?? []), ...(e?.rets ?? [])]}
      }
      case 'ret': {
        if (!s.x) return {rets: [[p, {t: 'none'}]]}
        const [v, q] = this.ev(s.x as SX, p)
        return {rets: [[q, v]]}
      }
      case 'fail': this.fail(p, I.T, s, String(s.why)); return {rets: []}
      case 'with': {
        let q = p
        for (const it of s.items as {x: SX, as?: SX}[]) {
          if (it.as) refuse(s, 'with ... as (a context manager\'s value)')
          if (it.x.e === 'call' && this.skipped(this.calleeNames(it.x))) { this.notes.add(`with ${it.x.text} (${it.x.p}): a context manager taken as transparent (skip)`); continue }
          const [v, q2] = this.ev(it.x, q)
          q = q2
          if (v.t !== 'lock') refuse(it.x, `with ${it.x.text}: a context manager (the subset reads a lock's, which makes the step atomic)`)
          this.notes.add(`${this.method}: the lock held (${it.x.p}): the step is atomic`)
        }
        return this.block(s.body as SS[], q)
      }
      case 'del': {
        const t = s.x as SX
        if (t.e !== 'idx') return refuse(s, `del ${t.text}: of other than a dict's item`)
        const [m, q] = this.ev(t.x as SX, p), [k, q2] = this.ev(t.i as SX, q)
        return {live: this.mapDel(m, this.keyOf(k, t), t, q2, true), rets: []}
      }
      case 'import': {
        const locals = new Map(p.locals)
        for (const [n, x] of Object.entries(s.names as Record<string, {mod: string, name?: string}>)) locals.set(n, {t: 'ext', q: x.name ? `${x.mod}.${x.name}` : x.mod, text: n, patch: {mod: x.mod, ...(x.name ? {path: [x.name]} : {})}})
        return {live: {...p, locals}, rets: []}
      }
      case 'no': return refuse(s, String(s.why))
    }
    return refuse(s, `a statement the subset doesn't read (${s.s})`)
  }
  // An assignment: to a local, to a field of an object, to a dict's item, or to a tuple of those.
  assign(to: SX, v: V, at: {p: string}, p: Path, t?: SType): Path {
    switch (to.e) {
      case 'var': {
        let x = v
        if (t && x.t === 'str' && t.k === 'choice' && x.e.op === 'slit') x = {t: 'choice', e: I.llit(x.e.value, t.values)}
        if (t && x.t === 'opaque' && this.scalar(t) === undefined) {} // (kept opaque)
        if (this.init && (to.n === 'self')) refuse(at, 'self rebound')
        return {...p, locals: new Map(p.locals).set(String(to.n), x)}
      }
      case 'tuple': {
        const xs = to.xs as SX[]
        if (v.t === 'opaque' && xs.every(y => y.e === 'var')) { let q = p; for (const y of xs) q = this.assign(y, v, at, q); return q }
        if (v.t !== 'tuple' || v.xs.length !== xs.length) return refuse(at, `${xs.length} names given ${v.t === 'tuple' ? `${v.xs.length} values` : `a ${v.t === 'opaque' ? v.why : v.t}`}`)
        let q = p
        xs.forEach((x, i) => { q = this.assign(x, v.xs[i]!, at, q) })
        return q
      }
      case 'get': {
        const [o, q] = this.ev(to.x as SX, p)
        return this.setField(o, String(to.f), v, to, q, t)
      }
      case 'idx': {
        const [m, q] = this.ev(to.x as SX, p), [k, q2] = this.ev(to.i as SX, q)
        return this.mapSet(m, this.keyOf(k, to.i as SX), v, to, q2)
      }
    }
    return refuse(at, `${to.text ?? to.e}: ${to.e === 'no' ? String(to.why) : 'an assignment the subset doesn\'t read'}`)
  }
  setField(o: V, f: string, v: V, at: SX, p: Path, t?: SType): Path {
    if (o.t === 'opt') { this.fail(p, I.not(o.has), at, `${at.text}: a field of None set (an AttributeError)`); return this.setField(o.v, f, v, at, this.assume(p, o.has), t) }
    if (o.t === 'cell') {
      const m = p.heap.get(o.map) as Extract<Obj, {k: 'map'}>
      const vals = this.cellOf(m, o.key, p, at)
      if (!vals.vals.has(f)) return refuse(at, `${at.text}: no field ${f} in the map's records`)
      return this.writeCell(o.map, m, o.key, vals.has, new Map(vals.vals).set(f, this.fit(v, m.decl.fields.find(x => x.name === f)!, at)), at, p)
    }
    if (o.t !== 'ref') return refuse(at, `${at.text}: a field set on ${o.t === 'opaque' ? o.why : `a ${o.t}`}`)
    const obj = p.heap.get(o.id)
    if (obj?.k !== 'rec') return refuse(at, `${at.text}: a field set on other than an object`)
    if (obj.origin === 'input') return refuse(at, `${at.text}: writes an object the caller gave (the caller's, not the state)`)
    if (obj.moved) return refuse(at, `${at.text}: writes an object already put in a map (one object in two places)`)
    if (obj.origin === 'state' && !this.init && !obj.f.has(f)) return refuse(at, `${at.text}: a field the constructor doesn't set (the state's fields are the constructor's)`)
    const old = obj.f.get(f)
    if (old?.t === 'opaque' && obj.origin === 'state' && !this.init) return refuse(at, `${at.text}: writes ${old.why}`)
    if (o.id === 'this' && this.frozen.has(f) && !this.init) return refuse(at, `${at.text}: writes a field the constructor sets to None (of no type the code states)`)
    if (this.init && t) this.declared.set(`${o.id}.${f}`, t)
    const heap = new Map(p.heap).set(o.id, {...obj, f: new Map(obj.f).set(f, v)})
    return {...p, heap}
  }
  declared = new Map<string, SType>()
  // A value as a cell's field holds it (a string literal of a choice field as the choice).
  fit(v: V, f: Var, at: SX): V {
    if (f.sort.k === 'choice' && v.t === 'str' && v.e.op === 'slit') { if (!f.sort.values.includes(v.e.value)) refuse(at, `${JSON.stringify(v.e.value)} is not one of ${f.name}'s literals`); return {t: 'choice', e: I.llit(v.e.value, f.sort.values)} }
    if (f.sort.k === 'num' && v.t !== 'num') return refuse(at, `${at.text}: a ${v.t === 'opaque' ? v.why : v.t} set where a number is held`)
    if (f.sort.k === 'bool' && v.t !== 'bool') return refuse(at, `${at.text}: a ${v.t === 'opaque' ? v.why : v.t} set where a boolean is held`)
    return v
  }

  // --- maps -----------------------------------------------------------------------------------------------------------
  mapObj(m: V, at: SX, p: Path): [string, Extract<Obj, {k: 'map'}>] {
    if (m.t !== 'ref') return refuse(at, `${at.text}: an item of ${m.t === 'opaque' ? m.why : `a ${m.t}`}`)
    const o = p.heap.get(m.id)
    if (o?.k !== 'map') return refuse(at, `${at.text}: an item of other than a dict`)
    if (o.origin === 'input') return refuse(at, `${at.text}: a dict the caller gave`)
    return [m.id, o]
  }
  cellOf(o: Extract<Obj, {k: 'map'}>, key: K, _p: Path, _at: SX): {has: B, vals: Map<string, V>} {
    const base = this.baseCell(o.decl, key)
    if (!o.w) return base
    const same = I.keq(key, o.w.key)
    return {has: I.bite(same, o.w.has, base.has), vals: new Map([...base.vals].map(([f, v]) => [f, this.ite(same, o.w!.vals.get(f)!, v, _at)]))}
  }
  writeCell(id: string, o: Extract<Obj, {k: 'map'}>, key: K, has: B, vals: Map<string, V>, at: SX, p: Path): Path {
    if (o.w && !I.same(o.w.key, key)) return refuse(at, `${at.text}: a second key of one map written in one step (the subset writes one a step)`)
    return {...p, heap: new Map(p.heap).set(id, {...o, w: {key, has, vals}})}
  }
  mapGet(m: V, k: K, at: SX, p: Path, missing: 'fail' | 'none' | V): [V, Path] {
    const [id, o] = this.mapObj(m, at, p)
    void id
    const c = this.cellOf(o, k, p, at)
    const value = (): V => (o.decl.scalar ? c.vals.get('value')! : {t: 'cell', map: id, key: k})
    if (missing === 'fail') { this.fail(p, I.not(c.has), at, `${at.text}: a key the dict doesn't hold (a KeyError)`); return [value(), this.assume(p, c.has)] }
    if (missing === 'none') return [o.decl.scalar ? {t: 'opt', has: c.has, v: value()} : {t: 'opt', has: c.has, v: value()}, p]
    return [this.ite(c.has, value(), missing, at), p]
  }
  mapSet(m: V, k: K, v: V, at: SX, p: Path): Path {
    const [id, o] = this.mapObj(m, at, p)
    if (o.decl.scalar) return this.writeCell(id, o, k, I.T, new Map([['value', this.fit(v, o.decl.fields[0]!, at)]]), at, p)
    // A record put in: a fresh one (made here), its fields copied into the cell, the object no longer written apart.
    if (v.t === 'cell' && v.map === id && I.same(v.key, k)) return p
    if (v.t !== 'ref') return refuse(at, `${at.text}: a ${v.t === 'opaque' ? v.why : v.t} put in a dict of records`)
    const r = p.heap.get(v.id)
    if (r?.k !== 'rec' || r.origin !== 'fresh') return refuse(at, `${at.text}: an object put in a dict that isn't made here (one object in two places)`)
    const vals = new Map<string, V>()
    for (const f of o.decl.fields) vals.set(f.name, this.fit(r.f.get(f.name) ?? refuse(at, `${at.text}: the record has no ${f.name}`), f, at))
    const q = this.writeCell(id, o, k, I.T, vals, at, p)
    return {...q, heap: new Map(q.heap).set(v.id, {...r, moved: true})}
  }
  mapDel(m: V, k: K, at: SX, p: Path, strict: boolean): Path {
    const [id, o] = this.mapObj(m, at, p), c = this.cellOf(o, k, p, at)
    if (strict) this.fail(p, I.not(c.has), at, `${at.text}: a key the dict doesn't hold deleted (a KeyError)`)
    return this.writeCell(id, o, k, I.F, new Map([...c.vals].map(([f, v]) => [f, (v.t === 'num' ? {t: 'num', e: I.num(0)} : v.t === 'bool' ? {t: 'bool', e: I.F} : v.t === 'choice' ? {t: 'choice', e: I.llit((v.e as {values: string[]}).values[0]!, (v.e as {values: string[]}).values)} : v) as V])), at, strict ? this.assume(p, c.has) : p)
  }
  mapDeclOf(name: string, t: SType, at: {p: string}): MapDecl {
    if (t.k !== 'map') return refuse(at, `${name}: ${this.why(t)}`)
    const key = t.key.k === 'int' ? 'num' : t.key.k === 'str' ? 'str' : refuse(at, `${name}: a dict keyed by ${this.why(t.key)} (keys are integers or strings)`)
    const cell = (n: string, ft: SType): Var => { const s = this.scalar(ft); if (!s || s.k === 'str') return refuse(at, `${name}: a dict of ${s?.k === 'str' ? 'strings' : this.why(ft)} (a cell holds integers, booleans and literals)`); return {name: n, sort: s, role: 'state'} }
    let fields: Var[], scalar = true
    if (t.val.k === 'rec') { const r = this.rec(t.val.name, at); fields = r.fields.map(f => cell(f.name, f.t)); scalar = false }
    else fields = [cell('value', t.val)]
    const v = this.newVar(name, {k: 'num'}, 'state')
    const d: MapDecl = {name: v.name, key, fields, scalar, js: 'Map'}
    this.maps.push(d)
    return d
  }

  // --- stores ---------------------------------------------------------------------------------------------------------
  storeMap(store: string, tpl: string, kn: boolean, at: SX, p: Path): [string, Extract<Obj, {k: 'map'}>] {
    const key = `${store}\u0000${tpl}`
    let sm = this.storeMaps.get(key)
    if (!sm) {
      for (const other of [...this.storeMaps.values()].filter(x => x.store === store)) if (!disjoint(other.tpl, tpl)) refuse(at, `${store}: the key templates ${JSON.stringify(other.tpl)} and ${JSON.stringify(tpl)} may name one key`)
      const decl = this.opts.stores?.[store] ?? {}
      const val: SType = decl.value === 'int' ? {k: 'int'} : decl.value === 'str' ? {k: 'str'} : {k: 'float'}
      const name = `${store}_${tpl.replace(/\{\}/g, '').replace(/[^A-Za-z0-9]+/g, '_').replace(/^_|_$/g, '')}`
      const d = this.mapDeclOf(name, {k: 'map', key: {k: kn ? 'int' : 'str'}, val}, at)
      const id = `store:${key}`
      sm = {store, tpl, id, decl: d}
      this.storeMaps.set(key, sm)
      this.initHeap.set(id, {k: 'map', decl: d, val, origin: 'state'})
      this.notes.add(`${store}: a store (stated): ${JSON.stringify(tpl)} keys held as ${d.name}, its expiry and eviction left out`)
    }
    if (!p.heap.has(sm.id)) p.heap.set(sm.id, this.initHeap.get(sm.id)!)
    return [sm.id, p.heap.get(sm.id) as Extract<Obj, {k: 'map'}>]
  }
  storeKey(v: V, at: SX): {tpl: string, k: K, kn: boolean} {
    if (v.t === 'fmt') return {tpl: v.tpl, k: v.k, kn: v.k.op === 'num'}
    if (v.t === 'str') return {tpl: '{}', k: v.e, kn: false}
    return refuse(at, `${at.text}: a store's key of ${v.t === 'opaque' ? v.why : `a ${v.t}`} (a string, or a format with one hole)`)
  }
  readonly storeAsync: Record<string, Record<string, boolean>> = {}
  storeCall(store: string, m: string, args: V[], kw: [string, V][], at: SX, p: Path, awaited: boolean): [V, Path] {
    const d = this.opts.stores?.[store] ?? {}
    const was = (this.storeAsync[store] ??= {})[m]
    if (was !== undefined && was !== awaited) return refuse(at, `${at.text}: the store's ${m} awaited at one call and not at another`)
    this.storeAsync[store]![m] = awaited
    const arg = (n: string, i: number) => kw.find(([k]) => k === n)?.[1] ?? args[i] ?? refuse(at, `${at.text}: the store's ${n} not given`)
    const kind = (d.get ?? ['get', 'async_get_cache', 'get_cache']).includes(m) ? 'get' : (d.set ?? ['set', 'async_set_cache', 'set_cache']).includes(m) ? 'set' : (d.delete ?? ['delete', 'delete_cache', 'async_delete_cache']).includes(m) ? 'delete' : refuse(at, `${at.text}: ${m}, a method of the store not stated as its get, set or delete`)
    const {tpl, k, kn} = this.storeKey(arg('key', 0), at)
    const [id, o] = this.storeMap(store, tpl, kn, at, p)
    if (kind === 'get') return this.mapGet({t: 'ref', id}, k, at, p, 'none')
    if (kind === 'delete') return [{t: 'none'}, this.mapDel({t: 'ref', id}, k, at, p, false)]
    const v = arg('value', 1)
    if (o.val.k === 'str' ? v.t !== 'str' : v.t !== 'num') return refuse(at, `${at.text}: a ${v.t === 'opaque' ? v.why : v.t} set in a store of ${o.val.k === 'float' ? 'numbers' : o.val.k}`)
    if (o.val.k === 'str') return refuse(at, `${at.text}: a store of strings (its cells hold numbers)`)
    return [{t: 'none'}, this.mapSet({t: 'ref', id}, k, v, at, p)]
  }

  // --- the boundary the caller states ---------------------------------------------------------------------------------
  calleeNames(x: SX): string[] {
    const f = x.f as SX
    const out: string[] = []
    if (typeof f.text === 'string') out.push(f.text)
    if (typeof f.q === 'string') out.push(f.q)
    if (f.e === 'get') out.push(String(f.f))
    if (f.e === 'fn') out.push(String(f.id))
    if (f.e === 'var') out.push(String(f.n))
    return out
  }
  match(list: string[] | undefined, names: string[]): string | undefined {
    return list?.find(e => names.some(n => n === e || n.startsWith(`${e}.`) || n.endsWith(`.${e}`) || n.endsWith(`.${e.replace(/^self\./, '')}`)))
  }
  skipped(names: string[]): boolean { return !!this.match(this.opts.skip, names) }
  // A call answered by the request: its result an input (one a step), the check stubbing the callee with it.
  answer(key: string, names: string[], patch: Patch | undefined, at: SX, p: Path, awaited: boolean): [V, Path] {
    if (!patch) return refuse(at, `${at.text}: an answered call the check can't stub`)
    if (p.called.includes(key)) return refuse(at, `${at.text}: ${key} called twice in one step (an answer is one a step)`)
    const q: Path = {...p, called: [...p.called, key]}
    const type = this.opts.answers![key]!
    let a = this.answers.get(key)
    const short = key.split('.').pop()!
    if (!a) {
      const {t} = sortOfText(type, at.p)
      const inner = t.k === 'opt' ? t.of : t, s = this.scalar(inner)!
      const v = this.newVar(short, s, 'input', `what ${names[0]} returns (stated: answers)`)
      const none = t.k === 'opt' ? this.newVar(`${short}_none`, {k: 'bool'}, 'input', `whether ${names[0]} returns None`).name : undefined
      a = {key, patch, async: awaited, inputs: {name: v.name, ...(none ? {none} : {}), ...(inner.k === 'float' ? {float: true} : {})}, sort: type}
      this.answers.set(key, a)
      this.notes.add(`${names[0]} (${at.p}): answered by the request (stated), its arguments not read`)
    } else if (a.async !== awaited) return refuse(at, `${at.text}: ${key} awaited at one call and not at another`)
    const vv = this.valueOf(this.vars.get(a.inputs.name)!)
    return [a.inputs.none ? {t: 'opt', has: I.not(I.bvar(a.inputs.none)), v: vv} : vv, q]
  }

  // --- expressions ----------------------------------------------------------------------------------------------------
  ev(x: SX, p: Path, awaited = false): [V, Path] {
    switch (x.e) {
      case 'int': return [{t: 'num', e: I.num(Number(x.v))}, p]
      case 'bool': return [{t: 'bool', e: x.v ? I.T : I.F}, p]
      case 'str': return [{t: 'str', e: {op: 'slit', value: String(x.v)}}, p]
      case 'none': return [{t: 'none'}, p]
      case 'var': { const v = p.locals.get(String(x.n)); if (!v) return refuse(x, `${String(x.n)}: a variable read before it is set`); return [this.narrow(v, p), p] }
      case 'fn': return [{t: 'fn', id: String(x.id)}, p]
      case 'cls': return [{t: 'cls', rec: String(x.rec), ...(x.patch ? {patch: x.patch as Patch} : {})}, p]
      case 'builtin': return [{t: 'builtin', n: String(x.n)}, p]
      case 'lib': return [{t: 'lib', q: String(x.q)}, p]
      case 'ext': return [{t: 'ext', q: String(x.q), text: String(x.text), ...(x.patch ? {patch: x.patch as Patch} : {})}, p]
      case 'no': return refuse(x, String(x.why))
      case 'await': {
        const inner = x.x as SX
        if (inner.e !== 'call') return refuse(x, `await ${inner.text ?? ''}: an await of other than a call`)
        return this.ev(inner, p, true)
      }
      case 'get': return this.get(x, p)
      case 'idx': {
        const [m, q] = this.ev(x.x as SX, p), [k, q2] = this.ev(x.i as SX, q)
        if (m.t === 'opaque') return [m, q2]
        return this.mapGet(m, this.keyOf(k, x.i as SX), x, q2, 'fail')
      }
      case 'neg': { const [v, q] = this.ev(x.x as SX, p); if (v.t === 'opaque') return [v, q]; return [{t: 'num', e: I.neg(this.numOf(v, x, q))}, q] }
      case 'not': { const [v, q] = this.ev(x.x as SX, p); if (v.t === 'opaque') return [v, q]; return [{t: 'bool', e: I.not(this.truthy(v, x, q))}, q] }
      case 'bin': return this.bin(x, p)
      case 'cmp': return this.compare(x, p)
      case 'and': case 'or': return this.boolOp(x, p)
      case 'ite': {
        const [cv, q] = this.ev(x.c as SX, p)
        if (cv.t === 'opaque') return [cv, q]
        const c = this.truthy(cv, x.c as SX, q)
        if (c.op === 'const') return this.ev((c.v ? x.a : x.b) as SX, q)
        const [a, qa] = this.ev(x.a as SX, this.assume(q, c)), [b, qb] = this.ev(x.b as SX, this.assume(q, I.not(c)))
        return [this.ite(c, a, b, x), this.merge(qa, qb, x)]
      }
      case 'tuple': {
        let q = p
        const xs: V[] = []
        for (const y of x.xs as SX[]) { const [v, q2] = this.ev(y, q); xs.push(v); q = q2 }
        return [{t: 'tuple', xs}, q]
      }
      case 'fstr': return this.fstr(x, p)
      case 'dict': {
        if ((x.keys as SX[]).length) return refuse(x, `${x.text ?? 'a dict literal'}: a dict literal with items (a record is made by its class)`)
        return [{t: 'opaque', why: '{} (an empty dict, a map only where a field declares its type)'}, p]
      }
      case 'list': return refuse(x, 'a list literal (lists are outside the Python subset)')
      case 'call': return this.call(x, p, awaited)
    }
    return refuse(x, `${x.text ?? x.e}: an expression the subset doesn't read`)
  }
  get(x: SX, p: Path): [V, Path] {
    const [o, q] = this.ev(x.x as SX, p), f = String(x.f)
    switch (o.t) {
      case 'opaque': return [{t: 'opaque', why: o.why}, q]
      case 'ext': return [{t: 'ext', q: `${o.q}.${f}`, text: `${o.text}.${f}`, ...(o.patch?.path ? {patch: {...o.patch, path: [...o.patch.path, f]}} : {})}, q]
      case 'none': this.fail(q, I.T, x, `${x.text}: a field of None (an AttributeError)`); return [{t: 'opaque', why: 'unreachable'}, {...q, pc: [...q.pc, I.F]}]
      case 'opt': { this.fail(q, I.not(o.has), x, `${x.text}: a field of None (an AttributeError)`); const [v2, q3] = this.get({...x, x: {e: 'var', n: '$v', p: x.p}}, {...this.assume(q, o.has), locals: new Map(q.locals).set('$v', o.v)}); return [v2, {...q3, locals: q.locals}] }
      case 'sattr': case 'ref': break
      case 'cell': {
        const m = q.heap.get(o.map) as Extract<Obj, {k: 'map'}>, c = this.cellOf(m, o.key, q, x)
        return [c.vals.get(f) ?? refuse(x, `${x.text}: no field ${f}`), q]
      }
      case 'cls': {
        const r = this.rec(o.rec, x), mid = r.methods[f]
        if (mid) return [{t: 'fn', id: mid}, q]
        return [{t: 'ext', q: `${o.rec}.${f}`, text: x.text ?? f, ...(o.patch?.path ? {patch: {...o.patch, path: [...o.patch.path, f]}} : {})}, q]
      }
      case 'bool': case 'builtin': case 'choice': case 'fmt': case 'fn': case 'lib': case 'lock': case 'num': case 'str': case 'tuple': return refuse(x, `${x.text}: a field of a ${o.t}`)
    }
    if (o.t === 'sattr') return this.storeAttr(o.store, o.path ? `${o.path}.${f}` : f, x, q)
    const obj = q.heap.get(o.id)
    if (obj?.k === 'store') return this.storeAttr(obj.name, f, x, q)
    if (obj?.k !== 'rec') return refuse(x, `${x.text}: a field of other than an object`)
    const r = this.rec(obj.ty, x)
    const v = obj.f.get(f)
    if (v) return [v, q]
    const mid = r.methods[f]
    if (mid !== undefined) {
      if (mid === null) return refuse(x, `${x.text}: a method of another module's class`)
      const fn = this.func(mid, x)
      if (fn.decorators.some(d => d.name === 'property')) return this.callFunc(fn, o, [], [], x, q, false)
      return [{t: 'fn', id: mid, self: fn.static ? undefined : o}, q]
    }
    if (obj.lazy) return this.lazyField(o.id, obj, f, x, q)
    return refuse(x, `${x.text}: no field ${f} (the object's fields are those its constructor sets)`)
  }
  // A field of an object the caller gives, made an input where it is first read.
  lazyField(id: string, obj: Extract<Obj, {k: 'rec'}>, f: string, x: SX, p: Path): [V, Path] {
    const r = this.rec(obj.ty, x), fd = r.fields.find(g => g.name === f)
    if (!fd) return refuse(x, `${x.text}: ${f}, a field ${r.short} doesn't declare`)
    const li = this.lazy.get(id)!
    const had = li.vals.get(f)
    if (had) { p.heap.set(id, {...obj, f: new Map(obj.f).set(f, had)}); return [had, p] }
    const [v, a] = this.input(`${li.prefix}_${f}`, fd.t, x, p)
    li.args.push([f, a]); li.vals.set(f, v)
    p.heap.set(id, {...obj, f: new Map(obj.f).set(f, v)})
    return [v, p]
  }
  storeAttr(store: string, path: string, x: SX, p: Path): [V, Path] {
    const attrs = this.opts.stores?.[store]?.attrs ?? {}
    if (path in attrs) {
      const v = attrs[path]!
      this.notes.add(`${store}.${path} is ${JSON.stringify(v)} (stated)`)
      return [v === null ? {t: 'none'} : typeof v === 'boolean' ? {t: 'bool', e: v ? I.T : I.F} : typeof v === 'number' ? {t: 'num', e: I.num(v)} : {t: 'str', e: {op: 'slit', value: v}}, p]
    }
    if (Object.keys(attrs).some(k => k.startsWith(`${path}.`))) return [{t: 'sattr', store, path}, p]
    return [{t: 'opaque', why: `${x.text}: an attribute of the store not stated`}, p]
  }
  bin(x: SX, p: Path): [V, Path] {
    const op = String(x.op)
    if (op === '/') return refuse(x, `${x.text}: a true division (a float; the subset reads math.floor or math.ceil of x / k, int(x / k), or x // k)`)
    const [a, q] = this.ev(x.x as SX, p), [b, q2] = this.ev(x.y as SX, q)
    if (a.t === 'opaque' || b.t === 'opaque') return [a.t === 'opaque' ? a : b, q2]
    if ((a.t === 'str' || a.t === 'fmt') && op === '+') return [{t: 'opaque', why: `${x.text}: strings joined`}, q2]
    if (a.t === 'str' && op === '%') return [{t: 'opaque', why: `${x.text}: a string formatted`}, q2]
    const na = this.numOf(a, x, q2), nb = this.numOf(b, x, q2)
    switch (op) {
      case '+': return [{t: 'num', e: I.add(na, nb)}, q2]
      case '-': return [{t: 'num', e: I.sub(na, nb)}, q2]
      case '*': return [{t: 'num', e: I.mul(na, nb)}, q2]
      case '//': case '%': {
        const k = constOf(b)
        if (k === undefined) return refuse(x, `${x.text}: a division by a value that isn't a constant`)
        if (k === 0) { this.fail(q2, I.T, x, `${x.text}: a division by zero (a ZeroDivisionError)`); return [{t: 'num', e: I.num(0)}, {...q2, pc: [...q2.pc, I.F]}] }
        const fl = this.floorDiv(na, k)
        return [{t: 'num', e: op === '//' ? fl : I.sub(na, I.mulk(k, fl))}, q2]
      }
    }
    return refuse(x, `${x.text}: ${op}`)
  }
  // ⌊a / k⌋ for a constant k (≠ 0): Python's // (and its float floor division at whole values).
  floorDiv(a: N, k: number): N { return k > 0 ? I.divk(k, a) : I.divk(-k, I.neg(a)) }
  compare(x: SX, p: Path): [V, Path] {
    const op = String(x.op)
    const [a, q] = this.ev(x.x as SX, p), [b, q2] = this.ev(x.y as SX, q)
    const out = (e: B): [V, Path] => [{t: 'bool', e}, q2]
    if (a.t === 'opaque' || b.t === 'opaque') return [a.t === 'opaque' ? a : b, q2]
    if (op === 'is' || op === 'is not') {
      const isNone = (v: V): B => (v.t === 'none' ? I.T : v.t === 'opt' ? I.not(v.has) : I.F)
      if (b.t !== 'none' && a.t !== 'none') return refuse(x, `${x.text}: an identity test of other than None`)
      const e = b.t === 'none' ? isNone(a) : isNone(b)
      return out(op === 'is' ? e : I.not(e))
    }
    if (op === 'in' || op === 'not in') {
      let e: B
      if (b.t === 'tuple') e = I.or(...b.xs.map(y => this.equal(a, y, x, q2)))
      else { const [, o] = this.mapObj(b, x, q2); e = this.cellOf(o, this.keyOf(a, x.x as SX), q2, x).has }
      return out(op === 'in' ? e : I.not(e))
    }
    if (op === '==' || op === '!=') { const e = this.equal(a, b, x, q2); return out(op === '==' ? e : I.not(e)) }
    if (a.t === 'str' || b.t === 'str' || a.t === 'choice' || b.t === 'choice') return refuse(x, `${x.text}: strings ordered (the subset compares them for equality)`)
    const na = this.numOf(a, x, q2), nb = this.numOf(b, x, q2)
    return out(op === '<' ? I.cmp('<', na, nb) : op === '<=' ? I.cmp('<=', na, nb) : op === '>' ? I.cmp('<', nb, na) : I.cmp('<=', nb, na))
  }
  equal(a: V, b: V, at: SX, p: Path): B {
    if (a.t === 'none' || b.t === 'none') { const o = a.t === 'none' ? b : a; return o.t === 'none' ? I.T : o.t === 'opt' ? I.not(o.has) : I.F }
    if (a.t === 'opt') return I.and(a.has, this.equal(a.v, b, at, p))
    if (b.t === 'opt') return I.and(b.has, this.equal(a, b.v, at, p))
    if (a.t === 'num' && b.t === 'num') return I.cmp('=', a.e, b.e)
    if (a.t === 'bool' && b.t === 'bool') return I.bite(a.e, b.e, I.not(b.e))
    if (a.t === 'str' && b.t === 'str') return I.keq(a.e, b.e)
    if (a.t === 'choice' && b.t === 'choice') return I.leq(a.e, b.e)
    if (a.t === 'choice' && b.t === 'str' && b.e.op === 'slit') return I.is(a.e, b.e.value)
    if (b.t === 'choice' && a.t === 'str' && a.e.op === 'slit') return I.is(b.e, a.e.value)
    if ((a.t === 'num' && b.t === 'str') || (a.t === 'str' && b.t === 'num')) return I.F
    return refuse(at, `${at.text}: ${a.t} == ${b.t}`)
  }
  // and / or: Python's give one of their operands (the first falsy, or the last; the first truthy, or the last).
  boolOp(x: SX, p: Path): [V, Path] {
    const xs = x.xs as SX[], isAnd = x.e === 'and'
    const go = (i: number, q: Path): [V, Path] => {
      const [v, q1] = this.ev(xs[i]!, q)
      if (i === xs.length - 1 || v.t === 'opaque') return [v, q1]
      const c = this.truthy(v, xs[i]!, q1)
      const stop = isAnd ? I.not(c) : c
      if (stop.op === 'const' && stop.v) return [v, q1]
      const [rest, q2] = go(i + 1, this.assume(q1, I.not(stop)))
      if (stop.op === 'const') return [rest, q2]
      // (the operand kept where it stops: an optional value is its value where it is truthy)
      const kept = !isAnd && v.t === 'opt' ? v.v : v
      return [this.ite(stop, kept, rest, x), this.merge(this.assume(q1, stop), q2, x)]
    }
    return go(0, p)
  }
  // An f-string: with one hole between literal text, a key a store reads by (its template); else a value kept only
  // where nothing reads it.
  fstr(x: SX, p: Path): [V, Path] {
    const parts = x.parts as (string | {x: SX, plain: boolean})[]
    let q = p, tpl = '', hole: K | undefined, n = 0, opaque = false
    for (const part of parts) {
      if (typeof part === 'string') { tpl += part.replace(/\{\}/g, '{ }'); continue }
      const [v, q2] = this.ev(part.x, q)
      q = q2
      n++
      if (!part.plain || n > 1 || !(v.t === 'str' || (v.t === 'num' && part.plain))) { opaque = true; continue }
      hole = v.t === 'str' ? v.e : {op: 'num', e: v.e}
      tpl += '{}'
    }
    if (opaque || !hole) return [{t: 'opaque', why: `${x.text}: a formatted string`}, q]
    return [{t: 'fmt', tpl, k: hole}, q]
  }
  call(x: SX, p: Path, awaited: boolean): [V, Path] {
    const fx = x.f as SX, names = this.calleeNames(x), args0 = x.args as SX[], kw0 = x.kw as [string, SX][]
    // The boundary first: an answered call, then a skipped one (neither's arguments read).
    const ans = this.match(Object.keys(this.opts.answers ?? {}), names)
    if (ans) {
      let patch: Patch | undefined
      if (fx.e === 'fn') patch = {mod: this.mod.module, path: [String(fx.id)]}
      else if (fx.e === 'get' && (fx.x as SX).e === 'var' && (fx.x as SX).n === 'self') patch = {self: String(fx.f)}
      else if (fx.e === 'get') {
        // A method of an object the caller gives, of another module's class: the class's method stubbed.
        const [o] = this.ev(fx.x as SX, p), obj = o.t === 'ref' ? p.heap.get(o.id) : undefined
        if (obj?.k === 'rec') { const r = this.rec(obj.ty, x); patch = {mod: r.module, path: [r.short, String(fx.f)]} }
        else { const [v] = this.ev(fx, p); if (v.t === 'ext' || v.t === 'cls') patch = v.patch }
      } else { const [o] = this.ev(fx, p); if (o.t === 'ext' || o.t === 'cls') patch = o.patch }
      return this.answer(ans, names, patch, x, this.argsRead(x, p), awaited)
    }
    if (this.skipped(names)) {
      this.notes.add(`${names[0]} (${x.p}): left out (stated: skip), run as it is by the check`)
      return [{t: 'opaque', why: `${x.text}: the value of a call left out (skip)`}, this.argsRead(x, p)]
    }
    // The callee and its object.
    let f: V, q = p
    if (fx.e === 'get') {
      const [o, q1] = this.ev(fx.x as SX, q)
      q = q1
      if (o.t === 'ref' && q.heap.get(o.id)?.k === 'map') return this.dictCall(o, String(fx.f), x, q)
      if (o.t === 'ref' && q.heap.get(o.id)?.k === 'store') return this.evArgs(x, q, (args, kw, q2) => this.storeCall((q.heap.get(o.id) as {name: string}).name, String(fx.f), args, kw, x, q2, awaited))
      if (o.t === 'sattr') return refuse(x, `${x.text}: a method of the store's ${o.path} (not stated)`)
      ;[f, q] = this.get(fx, q)
      if (o.t === 'opaque' && f.t === 'opaque') return refuse(x, `${x.text}: a call on ${o.why}`)
    } else [f, q] = this.ev(fx, q)
    switch (f.t) {
      case 'fn': { const fn = this.func(f.id, x); return this.evArgs(x, q, (args, kw, q2) => this.callFunc(fn, f.self, args, kw, x, q2, awaited)) }
      case 'cls': return this.evArgs(x, q, (args, kw, q2) => this.construct(f.rec, args, kw, x, q2))
      case 'builtin': return this.builtin(f.n, x, q)
      case 'lib': return this.lib(f.q, x, q)
      case 'ext': return refuse(x, `${x.text}: ${f.q}, other code (answer it, skip it, or read that module)`)
      case 'opaque': return refuse(x, `${x.text}: a call of ${f.why}`)
      case 'bool': case 'cell': case 'choice': case 'fmt': case 'lock': case 'none': case 'num': case 'opt': case 'ref': case 'sattr': case 'str': case 'tuple': break
    }
    void args0; void kw0
    return refuse(x, `${x.text}: a call of a ${f.t}`)
  }
  // The arguments of a call left to the boundary, read as far as the subset goes: the code evaluates them, so the fields
  // they read are inputs the check gives. An argument outside the subset that reaches none of the module's code and
  // not the object itself (other code's calls on other values) is taken as changing nothing of the state.
  argsRead(x: SX, p: Path): Path {
    let q = p
    for (const a of [...(x.args as SX[]), ...(x.kw as [string, SX][]).map(([, v]) => v)]) {
      try { q = this.ev(a, q)[1] } catch (e) { if (!(e instanceof Refusal) || !foreign(a)) throw e }
    }
    return q
  }
  evArgs<T>(x: SX, p: Path, k: (args: V[], kw: [string, V][], p: Path) => T): T {
    let q = p
    const args: V[] = [], kw: [string, V][] = []
    for (const a of x.args as SX[]) { const [v, q2] = this.ev(a, q); args.push(v); q = q2 }
    for (const [n, a] of x.kw as [string, SX][]) { const [v, q2] = this.ev(a, q); kw.push([n, v]); q = q2 }
    return k(args, kw, q)
  }
  dictCall(m: V, name: string, x: SX, p: Path): [V, Path] {
    return this.evArgs(x, p, (args, kw, q) => {
      if (kw.length) return refuse(x, `${x.text}: a dict's method given keywords`)
      const key = () => this.keyOf(args[0] ?? refuse(x, `${x.text}: no key`), (x.args as SX[])[0]!)
      if (name === 'get') return args.length > 1 ? this.mapGet(m, key(), x, q, args[1]!) : this.mapGet(m, key(), x, q, 'none')
      if (name === 'pop') {
        const k = key()
        const [v, q2] = args.length > 1 ? this.mapGet(m, k, x, q, args[1]!) : this.mapGet(m, k, x, q, 'fail')
        return [v, this.mapDel(m, k, x, q2, false)]
      }
      return refuse(x, `${x.text}: dict.${name} (the subset reads get, pop, [k], in and del)`)
    })
  }
  construct(rec: string, args: V[], kw: [string, V][], x: SX, p: Path): [V, Path] {
    const r = this.rec(rec, x)
    if (!r.kinds.includes('dataclass') || !r.own) return refuse(x, `${x.text}: ${r.short} made (the subset makes the module's own dataclasses)`)
    if (r.methods.__init__ || r.methods.__post_init__) return refuse(x, `${x.text}: ${r.short} has its own __init__ or __post_init__`)
    const f = new Map<string, V>()
    let i = 0, q = p
    for (const fd of r.fields) {
      let v = i < args.length ? args[i++] : kw.find(([n]) => n === fd.name)?.[1]
      if (!v && fd.dflt) { const [d, q2] = this.ev(fd.dflt, q); v = d; q = q2 }
      if (!v) return refuse(x, `${x.text}: ${fd.name} not given`)
      if (fd.t.k === 'choice' && v.t === 'str' && v.e.op === 'slit') v = {t: 'choice', e: I.llit(v.e.value, fd.t.values)}
      f.set(fd.name, v)
    }
    const id = `fresh:${this.fresh++}`
    return [{t: 'ref', id}, {...q, heap: new Map(q.heap).set(id, {k: 'rec', ty: rec, f, origin: 'fresh'})}]
  }
  builtin(n: string, x: SX, p: Path): [V, Path] {
    const a0 = (x.args as SX[])[0]
    // int(x / k): truncated toward zero.
    if (n === 'int' && a0?.e === 'bin' && a0.op === '/') return this.quotient(a0, p, 'trunc')
    return this.evArgs(x, p, (args, kw, q) => {
      if (kw.length) return refuse(x, `${x.text}: ${n} given keywords`)
      if (args.some(a => a.t === 'opaque') && ['str', 'repr', 'len', 'isinstance', 'round', 'int', 'float', 'bool'].includes(n)) return [{t: 'opaque', why: `${x.text}: of a value outside the subset`}, q]
      const v = args[0]
      switch (n) {
        case 'min': case 'max': {
          if (args.length < 2) return refuse(x, `${x.text}: ${n} of an iterable`)
          const ns = args.map(a => this.numOf(a, x, q))
          return [{t: 'num', e: ns.slice(1).reduce((acc, y) => (n === 'min' ? I.nmin(acc, y) : I.nmax(acc, y)), ns[0]!)}, q]
        }
        case 'abs': { const e = this.numOf(v!, x, q); return [{t: 'num', e: I.nite(I.cmp('<', e, I.num(0)), I.neg(e), e)}, q] }
        case 'int': case 'float':
          if (v?.t === 'str') return refuse(x, `${x.text}: a string parsed`)
          if (v?.t === 'bool') return [{t: 'num', e: I.nite(v.e, I.num(1), I.num(0))}, q]
          return [{t: 'num', e: this.numOf(v ?? {t: 'num', e: I.num(0)}, x, q)}, q]
        case 'bool': return [{t: 'bool', e: v ? this.truthy(v, x) : I.F}, q]
        case 'str': if (v?.t === 'str') return [v, q]; return [{t: 'opaque', why: `${x.text}: a value made a string`}, q]
        case 'repr': return [{t: 'opaque', why: `${x.text}: a repr`}, q]
      }
      return refuse(x, `${x.text}: ${n}() (a builtin outside the subset)`)
    })
  }
  quotient(d: SX, p: Path, round: 'floor' | 'ceil' | 'trunc'): [V, Path] {
    const [a, q] = this.ev(d.x as SX, p), [b, q2] = this.ev(d.y as SX, q), k = constOf(b)
    if (k === undefined) return refuse(d, `${d.text}: a division by a value that isn't a constant`)
    if (k === 0) { this.fail(q2, I.T, d, `${d.text}: a division by zero (a ZeroDivisionError)`); return [{t: 'num', e: I.num(0)}, {...q2, pc: [...q2.pc, I.F]}] }
    const n = this.numOf(a, d, q2), fl = this.floorDiv(n, k), ce = I.neg(this.floorDiv(I.neg(n), k))
    const lt = k > 0 ? I.cmp('<', n, I.num(0)) : I.cmp('<', I.num(0), n)
    return [{t: 'num', e: round === 'floor' ? fl : round === 'ceil' ? ce : I.nite(lt, ce, fl)}, q2]
  }
  lib(q0: string, x: SX, p: Path): [V, Path] {
    const a0 = (x.args as SX[])[0]
    if ((q0 === 'math.floor' || q0 === 'math.ceil') && a0?.e === 'bin' && a0.op === '/') return this.quotient(a0, p, q0 === 'math.floor' ? 'floor' : 'ceil')
    if (q0 === 'time.time' || q0 === 'time.monotonic' || q0 === 'time.perf_counter') { this.notes.add(`${q0}() is the request's time (an input, read once a step, at whole seconds: the claim is for those)`); return this.clock(x, p) }
    if (q0 === 'threading.Lock' || q0 === 'threading.RLock' || q0 === 'asyncio.Lock') return [{t: 'lock'}, p]
    return this.evArgs(x, p, (args, _kw, q) => {
      const v = args[0]
      if (v?.t === 'opaque') return [v, q]
      if (q0 === 'math.floor' || q0 === 'math.ceil') return [{t: 'num', e: this.numOf(v!, x, q)}, q]
      // Whole numbers are finite: isfinite holds, isnan and isinf don't (a float here is a whole value).
      if (q0 === 'math.isfinite') { this.numOf(v!, x, q); return [{t: 'bool', e: I.T}, q] }
      if (q0 === 'math.isnan' || q0 === 'math.isinf') { this.numOf(v!, x, q); return [{t: 'bool', e: I.F}, q] }
      return refuse(x, `${x.text}: ${q0}`)
    })
  }
}

// An expression that calls nothing (so evaluating it changes nothing).
const callFree = (x: unknown): boolean => {
  if (!x || typeof x !== 'object') return true
  const o = x as {e?: string}
  if (o.e === 'call' || o.e === 'await' || o.e === 'no') return false
  return Object.values(o).every(callFree)
}
// An expression that reaches none of the module's own code and not `self`.
const foreign = (x: unknown): boolean => {
  if (!x || typeof x !== 'object') return true
  const o = x as {e?: string, n?: string}
  if (o.e === 'fn' || (o.e === 'var' && o.n === 'self')) return false
  return Object.values(o).every(foreign)
}
// Two key templates name disjoint keys: they differ at some position of their fixed prefixes or of their fixed
// suffixes (a hole's value can be any string, so only those parts tell keys apart).
export function disjoint(a: string, b: string): boolean {
  if (a === b) return false
  const [pa, sa] = split(a), [pb, sb] = split(b)
  for (let i = 0; i < Math.min(pa.length, pb.length); i++) if (pa[i] !== pb[i]) return true
  for (let i = 1; i <= Math.min(sa.length, sb.length); i++) if (sa[sa.length - i] !== sb[sb.length - i]) return true
  return false
}
const split = (t: string): [string, string] => { const i = t.indexOf('{}'); return i < 0 ? [t, t] : [t.slice(0, i), t.slice(i + 2)] }

// --- a module's step: the class (or the functions) read into the Model -------------------------------------------------
export function readStep(mod: SModule, opts: StepOptions): StepRead {
  if (mod.error) refuse(mod.file, mod.error)
  const g = new Stepper(mod, opts), kept = opts.failures === 'kept', carried = kept && opts.onError !== 'discard'
  const entries = mod.entries
  for (const e of entries) if (e.k === 'missing') refuse(mod.file, `no class or function ${e.name} in ${mod.file}`)
  const cls = entries.length === 1 && entries[0]!.k === 'class' ? (entries[0] as {rec: string}).rec : undefined
  if (!cls && entries.some(e => e.k === 'class')) refuse(mod.file, 'a class read with other entries (one class, or functions)')
  const leaves: Leaf[] = [], ctor: [string, PArg][] = []
  const at = {p: `${mod.file}:1:1`}
  // --- the state: the object as its constructor makes it -----------------------------------------------------------
  const stateOf = new Map<string, V>()  // each leaf's value at the start (terms over the params)
  let pre: B = I.T
  const tree: {path: string[], v: V, t?: SType}[] = []
  if (cls) {
    const r = g.rec(cls, at)
    if (!r.own) refuse(at, `${r.short}: a class of another module`)
    const fresh: Path = {pc: [], locals: new Map(), heap: new Map([['this', {k: 'rec', ty: cls, f: new Map(), origin: 'state'}]]), called: []}
    g.init = true
    g.method = '__init__'
    let made: Path
    const initId = r.methods.__init__
    if (initId) {
      const fn = g.func(initId, at)
      // The fields it sets (named first: the state's names are the fields').
      const scan = (ss: SS[]) => { for (const st of ss) { const to = st.to as SX | undefined; if (st.s === 'set' && to?.e === 'get' && (to.x as SX).e === 'var' && (to.x as SX).n === 'self') g.fieldNames.add(String(to.f)); if (st.s === 'if') { scan(st.then as SS[]); scan(st.else as SS[]) } if (st.s === 'with') scan(st.body as SS[]) } }
      scan(fn.body)
      const args: V[] = []
      let p = fresh
      for (const pa of fn.params.filter(x => !x.self && !x.star)) {
        if (opts.stores?.[pa.name]) { const id = `store:${pa.name}`; p.heap.set(id, {k: 'store', name: pa.name}); g.initHeap.set(id, {k: 'store', name: pa.name}); args.push({t: 'ref', id}); ctor.push([pa.name, {k: 'store', name: pa.name}]); continue }
        if (pa.dflt && !g.scalar(pa.t.k === 'opt' ? pa.t.of : pa.t)) { ctor.push([pa.name, {k: 'dflt'}]); const [d, p2] = g.ev(pa.dflt, p); args.push(d); p = p2; continue }
        const [v, a] = g.input(pa.name, pa.t, fn, p, 'param')
        if (a.k === 'inert') refuse(fn, `${r.short}(${pa.name}): a constructor argument of ${g.why(pa.t)} (state it as a store, or give it a default)`)
        args.push(v); ctor.push([pa.name, a])
      }
      const [, p2] = g.callFunc(fn, {t: 'ref', id: 'this'}, args, [], {e: 'call', p: fn.p, text: `${r.short}()`}, p, false)
      made = p2
      if (ctor.length) g.notes.add(`${r.short} made by its constructor: its arguments are the rule's params`)
    } else if (r.kinds.includes('dataclass')) {
      const f = new Map<string, V>()
      let p = fresh
      for (const fd of r.fields) {
        if (fd.dflt) { const [d, p2] = g.ev(fd.dflt, p); f.set(fd.name, d); p = p2; g.declared.set(`this.${fd.name}`, fd.t); continue }
        const [v, a] = g.input(fd.name, fd.t, {p: r.p}, p, 'param')
        if (a.k === 'inert') refuse(r, `${r.short}.${fd.name}: a field of ${g.why(fd.t)}`)
        f.set(fd.name, v); ctor.push([fd.name, a]); g.declared.set(`this.${fd.name}`, fd.t)
      }
      if (r.methods.__post_init__) refuse(r, `${r.short}: __post_init__`)
      made = {...p, heap: new Map(p.heap).set('this', {k: 'rec', ty: cls, f, origin: 'state'})}
      g.notes.add(`${r.short}: a dataclass, made with its fields' defaults (the claim is for objects made so) and the others as params`)
    } else made = fresh
    pre = I.not(I.or(...g.fails))
    g.fails = []
    g.init = false
    const self = made.heap.get('this') as Extract<Obj, {k: 'rec'}>
    for (const [f, v] of self.f) tree.push({path: [f], v, ...(g.declared.get(`this.${f}`) ? {t: g.declared.get(`this.${f}`)} : {})})
    for (const fd of r.fields) if (!self.f.has(fd.name) && !r.kinds.includes('dataclass')) g.notes.add(`${r.short}.${fd.name}: declared on the class but not set by its constructor (left out)`)
    // Each field a leaf: a variable (two for an optional one), a nested object's own, a map, a store, or left out.
    const heap = new Map<string, Obj>()
    const fields = new Map<string, V>()
    const build = (path: string[], v: V, t: SType | undefined, into: Map<string, V>, initPath: Path) => {
      const name = path.join('_'), f = path.at(-1)!, decl = t ?? undefined
      const scalarT = decl && decl.k !== 'opt' ? decl : undefined
      const leaf = (kind: Leaf['kind'], vr: Var, float?: boolean) => { leaves.push({name: vr.name, path, kind, ...(float ? {float: true} : {})}); return vr }
      const isFloat = (decl?.k === 'float') || (decl?.k === 'opt' && decl.of.k === 'float')
      if (v.t === 'num' || v.t === 'bool' || v.t === 'str' || v.t === 'choice' || (v.t === 'none' && decl?.k === 'opt') || v.t === 'opt') {
        const inner: SType | undefined = decl?.k === 'opt' ? decl.of : scalarT
        const sort: Var['sort'] = inner && g.scalar(inner) ? g.scalar(inner)! : v.t === 'num' ? {k: 'num'} : v.t === 'bool' ? {k: 'bool'} : v.t === 'str' ? {k: 'str'} : v.t === 'choice' ? {k: 'choice', values: (v.e as {values: string[]}).values} : v.t === 'opt' && g.scalar({k: v.v.t === 'num' ? 'int' : v.v.t === 'bool' ? 'bool' : 'str'} as SType) ? (v.v.t === 'num' ? {k: 'num'} : v.v.t === 'bool' ? {k: 'bool'} : {k: 'str'}) : refuse(at, `${path.join('.')}: a field of no scalar type`)
        if (v.t === 'str' && sort.k === 'choice' && v.e.op === 'slit') v = {t: 'choice', e: I.llit(v.e.value, sort.values)}
        const optional = v.t === 'none' || v.t === 'opt' || decl?.k === 'opt'
        const vr = leaf(sort.k === 'num' ? 'num' : sort.k, g.newVar(name, sort, 'state'), isFloat)
        let cur: V = g.valueOf(vr)
        if (optional) {
          const nv = leaf('none', g.newVar(`${name}_none`, {k: 'bool'}, 'state', `whether ${path.join('.')} is None`))
          const has = I.not(I.bvar(nv.name))
          stateOf.set(nv.name, {t: 'bool', e: v.t === 'none' ? I.T : v.t === 'opt' ? I.not(v.has) : I.F})
          stateOf.set(vr.name, v.t === 'none' ? zeroOf(sort) : v.t === 'opt' ? v.v : v)
          cur = {t: 'opt', has, v: cur}
        } else stateOf.set(vr.name, v)
        into.set(f, cur)
        return
      }
      if (v.t === 'ref') {
        const o = initPath.heap.get(v.id)
        if (o?.k === 'store') { into.set(f, v); heap.set(v.id, o); return }
        if (o?.k === 'rec') {
          const sub = new Map<string, V>(), id = `state:${path.join('.')}`
          for (const [ff, vv] of o.f) build([...path, ff], vv, g.mod.recs[o.ty]?.fields.find(x => x.name === ff)?.t, sub, initPath)
          heap.set(id, {k: 'rec', ty: o.ty, f: sub, origin: 'state'})
          leaves.push({name: '', path, kind: 'frame', cls: o.ty})
          into.set(f, {t: 'ref', id})
          return
        }
      }
      if (v.t === 'opaque' && decl?.k === 'map' && /\{\}/.test(v.why)) {
        const d = g.mapDeclOf(name, decl, at), id = `state:${path.join('.')}`
        const vt = decl.val
        heap.set(id, {k: 'map', decl: d, val: vt, origin: 'state'})
        leaves.push({name: d.name, path, kind: 'map', key: d.key, ...(vt.k === 'rec' ? {cls: vt.name, fields: d.fields.map(x => ({name: x.name, ...(g.mod.recs[vt.name]!.fields.find(y => y.name === x.name)?.t.k === 'float' ? {float: true} : {})}))} : vt.k === 'float' ? {float: true} : {})})
        into.set(f, {t: 'ref', id})
        return
      }
      if (v.t === 'lock') { into.set(f, v); return }
      // A field the constructor sets to None, of no declared type: a constant (a method setting it is refused).
      if (v.t === 'none') { into.set(f, v); g.frozen.add(path.join('.')); leaves.push({name: '', path, kind: 'frame'}); return }
      into.set(f, {t: 'opaque', why: `${path.join('.')}: ${v.t === 'opaque' ? v.why : `a ${v.t}`}, a field outside the subset (left out of the rule)`})
      leaves.push({name: '', path, kind: 'frame'})
    }
    for (const {path, v, t} of tree) build(path, v, t, fields, made)
    heap.set('this', {k: 'rec', ty: cls, f: fields, origin: 'state'})
    for (const [id, o] of heap) g.initHeap.set(id, o)
  }
  // --- the requests: each method (or function) one -------------------------------------------------------------------
  const r = cls ? g.rec(cls, at) : undefined
  const chosen: SFunc[] = cls
    ? (opts.methods ?? Object.keys(r!.methods).filter(m => !m.startsWith('_') && r!.methods[m])).map(m => (r!.methods[m] ? g.func(r!.methods[m]!, at) : refuse(at, `no method ${r!.short}.${m} in ${mod.file}`)))
    : entries.map(e => g.func((e as {id: string}).id, at))
  if (!chosen.length) refuse(at, `${cls ? r!.short : 'the entry'} has no methods to read`)
  for (const f of chosen) if (f.decorators.some(d => d.name === 'property')) refuse(f, `${f.name}: a property (read, not called)`)
  const names = chosen.map(f => f.name)
  const ev = names.length > 1 ? g.newVar('method', {k: 'choice', values: names}, 'input') : undefined
  const evL: L | undefined = ev ? {op: 'var', name: ev.name, values: names} : undefined
  const events: Event[] = [], argsOf: Record<string, [string, PArg][]> = {}
  type Final = {sel: B, path: Path, out?: V, fails: B[]}
  const finals: Final[] = []
  for (const fn of chosen) {
    g.method = fn.name
    const sel = evL ? I.is(evL, fn.name) : I.T
    let p: Path = {pc: [sel], locals: new Map(), heap: new Map(g.initHeap), called: []}
    const args: V[] = [], pargs: [string, PArg][] = []
    for (const pa of fn.params.filter(x => !x.self && !x.star)) {
      const [v, a] = g.input(`${names.length > 1 ? `${fn.name}_` : ''}${pa.name}`, pa.t, fn, p)
      args.push(v); pargs.push([pa.name, a])
    }
    g.fails = []; g.failPaths = []
    const [out, q] = g.callFunc(fn, cls ? {t: 'ref', id: 'this'} : undefined, args, [], {e: 'call', p: fn.p, text: fn.name}, p, fn.async ?? false)
    p = g.failPaths.length ? g.join([q, ...g.failPaths], fn)! : q
    finals.push({sel, path: p, out, fails: g.fails})
    argsOf[fn.name] = pargs
  }
  // --- the methods together: each leaf by the method called ---------------------------------------------------------
  const state: Var[] = [], init: Record<string, Term> = {}, writes: Record<string, Term> = {}, mapWrites: Model['mapWrites'] = {}, outputs: string[] = []
  const stateLeaves = leaves.filter(l => l.kind !== 'frame' && l.kind !== 'map')
  const failedOf = (f: Final) => I.or(...f.fails)
  const anyFail = (f: Final) => I.and(f.sel, failedOf(f))
  const termOf = (v: V, at2: {p: string}): Term => {
    if (v.t === 'num') return {s: 'num', e: v.e}
    if (v.t === 'bool') return {s: 'bool', e: v.e}
    if (v.t === 'str') return {s: 'str', e: v.e}
    if (v.t === 'choice') return {s: 'choice', e: v.e}
    return refuse(at2, `a ${v.t === 'opaque' ? v.why : v.t} where the state holds a scalar`)
  }
  // The value of each leaf at a path's end (the object's fields, nested ones through their objects).
  const leafAt = (path: Path, l: Leaf, at2: {p: string}): Term => {
    let o = path.heap.get('this') as Extract<Obj, {k: 'rec'}>
    for (const seg of l.path.slice(0, -1)) {
      const v = o.f.get(seg)
      if (v?.t !== 'ref') return refuse(at2, `${l.path.join('.')}: a nested object replaced by a ${v?.t}`)
      o = path.heap.get(v.id) as Extract<Obj, {k: 'rec'}>
    }
    const f = l.kind === 'none' ? l.path.at(-1)! : l.path.at(-1)!
    const v = o.f.get(f) ?? refuse(at2, `${l.path.join('.')} unset`)
    const s = g.vars.get(l.name)!.sort
    if (l.kind === 'none') return {s: 'bool', e: v.t === 'none' ? I.T : v.t === 'opt' ? I.not(v.has) : I.F}
    const val = v.t === 'opt' ? v.v : v.t === 'none' ? zeroOf(s) : v
    return termOf(val.t === 'str' && s.k === 'choice' && val.e.op === 'slit' ? {t: 'choice', e: I.llit(val.e.value, s.values)} : val, at2)
  }
  for (const l of stateLeaves) {
    const v = g.vars.get(l.name)!
    state.push(v)
    init[v.name] = termOf(stateOf.get(v.name)!, at)
    let acc: Term | undefined
    for (let i = finals.length - 1; i >= 0; i--) {
      const f = finals[i]!
      let t = leafAt(f.path, l, {p: chosen[i]!.p})
      if (kept && !carried) t = iteTerm(failedOf(f), varTerm(v), t)
      acc = acc === undefined ? t : iteTerm(f.sel, t, acc)
    }
    if (acc && !I.same(acc.e, varTerm(v).e)) writes[v.name] = acc
  }
  // A one-object check: no object in two places of the state.
  for (const f of finals) {
    const seen = new Set<string>()
    const visit = (o: Extract<Obj, {k: 'rec'}>, path: string) => { for (const [k, v] of o.f) if (v.t === 'ref') { if (seen.has(v.id)) refuse(chosen[0]!.p, `${path}.${k}: one object in two places of the state`); seen.add(v.id); const x = f.path.heap.get(v.id); if (x?.k === 'rec') visit(x, `${path}.${k}`) } }
    const self = f.path.heap.get('this')
    if (self?.k === 'rec') visit(self, 'self')
  }
  // The maps (and the stores' maps).
  for (const d of g.maps) {
    const id = [...g.initHeap].find(([, o]) => o.k === 'map' && o.decl === d)?.[0]
    if (!id) continue
    const ws = finals.map(f => { const o = f.path.heap.get(id) as Extract<Obj, {k: 'map'}> | undefined; return o?.w })
    if (!ws.some(Boolean)) continue
    const key0 = ws.find(Boolean)!.key
    let acc: {key: K, has: B, vals: Record<string, Term>} | undefined
    for (let i = finals.length - 1; i >= 0; i--) {
      const base = (k: K) => { const c = g.baseCell(d, k); return {key: k, has: c.has, vals: Object.fromEntries([...c.vals].map(([f, v]) => [f, termOf(v, at)]))} }
      const w0 = ws[i]
      let w = w0 ? {key: w0.key, has: w0.has, vals: Object.fromEntries([...w0.vals].map(([f, v]) => [f, termOf(v, at)]))} : base(acc?.key ?? key0)
      if (kept && !carried && w0) { const fl = failedOf(finals[i]!), b = base(w.key); w = {key: w.key, has: I.bite(fl, b.has, w.has), vals: Object.fromEntries(Object.entries(w.vals).map(([f, t]) => [f, iteTerm(fl, b.vals[f]!, t)]))} }
      acc = acc === undefined ? w : {key: I.kite(finals[i]!.sel, w.key, acc.key), has: I.bite(finals[i]!.sel, w.has, acc.has), vals: Object.fromEntries(Object.entries(w.vals).map(([f, t]) => [f, iteTerm(finals[i]!.sel, t, acc!.vals[f]!)]))}
    }
    mapWrites[d.name] = acc!
  }
  // What each method returns, and whether it failed: the step's result.
  const results: Model['results'] = {}, resultKinds: StepRead['results'] = {}
  let failedVar: Var | undefined
  if (kept) { failedVar = g.newVar('failed', {k: 'bool'}, 'state', 'whether the step failed (an exception raised): the state is as it was'); }
  for (const [i, f] of finals.entries()) {
    const fn = chosen[i]!
    const out = f.out!
    let kind: 'none' | 'scalar' | 'maybe' = 'none', rv: Var | undefined, rn: Var | undefined
    if (out.t === 'num' || out.t === 'bool' || out.t === 'str' || out.t === 'choice' || out.t === 'opt') {
      const inner = out.t === 'opt' ? out.v : out
      if (inner.t === 'num' || inner.t === 'bool' || inner.t === 'str' || inner.t === 'choice') {
        const sort: Var['sort'] = inner.t === 'num' ? {k: 'num'} : inner.t === 'bool' ? {k: 'bool'} : inner.t === 'str' ? {k: 'str'} : {k: 'choice', values: (inner.e as {values: string[]}).values}
        rv = g.newVar(`${fn.name}_result`, sort, 'state', `what ${fn.name} returned, at the step that called it (its default at others)`)
        if (out.t === 'opt') { rn = g.newVar(`${fn.name}_result_none`, {k: 'bool'}, 'state', `whether ${fn.name} returned None`); kind = 'maybe' } else kind = 'scalar'
      }
    } else if (out.t !== 'none') g.notes.add(`${fn.name} returns ${out.t === 'opaque' ? out.why : `a ${out.t}`}: not kept`)
    resultKinds[fn.name] = kind
    const fields: [string, string][] = []
    if (failedVar) fields.push(['failed', failedVar.name])
    if (rv) { fields.push(['value', rv.name]); outputs.push(rv.name); state.push(rv); init[rv.name] = termOf(zeroOf(rv.sort), at) }
    if (rn) { fields.push(['none', rn.name]); outputs.push(rn.name); state.push(rn); init[rn.name] = {s: 'bool', e: I.F} }
    if (fields.length === 1 && !failedVar && rv && !rn) results[fn.name] = {k: 'scalar', name: rv.name}
    else if (fields.length) results[fn.name] = {k: 'rec', fields}
    ;(f as Final & {rv?: Var, rn?: Var}).rv = rv; (f as Final & {rv?: Var, rn?: Var}).rn = rn
  }
  for (const o of outputs) {
    const v = g.vars.get(o)!
    let acc: Term = init[o]!
    for (let i = finals.length - 1; i >= 0; i--) {
      const f = finals[i]! as Final & {rv?: Var, rn?: Var}
      const out = f.out!
      let t: Term = init[o]!
      if (f.rv?.name === o) t = termOf(out.t === 'opt' ? out.v : out, chosen[i]!)
      if (f.rn?.name === o) t = {s: 'bool', e: out.t === 'opt' ? I.not(out.has) : I.F}
      if (kept && (f.rv?.name === o || f.rn?.name === o)) t = iteTerm(failedOf(f), init[o]!, t)
      acc = iteTerm(f.sel, t, acc)
    }
    writes[o] = acc
    void v
  }
  if (failedVar) {
    outputs.push(failedVar.name); state.push(failedVar); init[failedVar.name] = {s: 'bool', e: I.F}
    writes[failedVar.name] = {s: 'bool', e: I.or(...finals.map(anyFail))}
  }
  const refuseB = I.or(...g.refusals, ...(kept ? [] : finals.map(anyFail)))
  // Inputs no term reads are still the request's (the check builds the arguments from them).
  const maps = g.maps.filter(d => [...g.initHeap.values()].some(o => o.k === 'map' && o.decl === d))
  const stores: StepRead['stores'] = Object.fromEntries(Object.entries(opts.stores ?? {}).map(([n, d]) => [n, {...d, async: g.storeAsync[n] ?? {}}]))
  for (const sm of g.storeMaps.values()) leaves.push({name: sm.decl.name, path: [], kind: 'map', key: sm.decl.key, store: sm.store, tpl: sm.tpl, ...(stores[sm.store]?.value !== 'int' ? {float: true} : {})})
  const layout: Layout = {k: 'rec', fields: state.filter(v => !outputs.includes(v.name)).map(v => [v.name, {k: 'scalar', name: v.name}] as [string, Layout])}
  for (const fn of chosen) {
    const used = new Set<string>()
    const walk = (a: PArg) => { if (a.k === 'in') used.add(a.name); else if (a.k === 'opt') { used.add(a.none); walk(a.v) } else if (a.k === 'rec') a.f.forEach(([, x]) => walk(x)) }
    argsOf[fn.name]!.forEach(([, a]) => walk(a))
    for (const a of g.answers.values()) { used.add(a.inputs.name); if (a.inputs.none) used.add(a.inputs.none) }
    if (g.now) used.add(g.now.name)
    events.push({select: ev ? {[ev.name]: fn.name} : {}, call: fn.name, args: [{k: 'rec', fields: [...used].map(n => [n, {k: 'input', name: n} as Arg])}]})
  }
  const laws: string[] = []
  for (const l of leaves) if (l.kind === 'none') { const base = l.name.replace(/_none$/, ''); if (g.vars.get(base)?.sort.k === 'num') laws.push(`r.law(${JSON.stringify(`${base}: a None one holds 0`)}, ({${base}, ${l.name}}) => any(${l.name}.not(), ${base}.eq(0)))`) }
  if (g.now) {
    const n = g.vars.get(g.now.name)!
    n.note = 'Date.now() (here time.time()): the time of the request, an input'
  }
  const left = leaves.filter(l => l.kind === 'frame' && !l.cls).map(l => l.path.join('.'))
  if (left.length) g.notes.add(`left out (outside the subset; the methods read don't touch them): ${left.join(', ')}`)
  // Inputs no term reads are left out of the rule (the harness gives them their sort's zero, or None).
  const read = new Set<string>()
  const mention = (t: object) => { for (const n of I.varsOf(t as N).vars) read.add(n) }
  for (const t of [...Object.values(writes), ...Object.values(init)]) mention(t.e)
  for (const w of Object.values(mapWrites)) { mention(w.has); mention(w.key); for (const t of Object.values(w.vals)) mention(t.e) }
  mention(refuseB); mention(pre)
  const unread = g.inputs.filter(v => !read.has(v.name) && v.name !== ev?.name)
  if (unread.length) g.notes.add(`read by the code but by no term of the rule (given their sort's zero, or None, by the check): ${unread.map(v => v.name).join(', ')}`)
  const inputs = g.inputs.filter(v => !unread.includes(v))
  for (const e of events) { const a = e.args[0] as {k: 'rec', fields: [string, Arg][]}; a.fields = a.fields.filter(([n]) => !unread.some(v => v.name === n)) }
  const model: Model = {
    kind: cls ? 'a class and its methods' : names.length > 1 ? 'functions, each a request' : 'a function, each call a request',
    name: cls ? g.rec(cls, at).short : names.length === 1 ? names[0]! : mod.module.split('.').pop()!, shape: 'class', file: mod.file, entry: cls ? g.rec(cls, at).short : names.join(', '),
    params: g.params, inputs, state, maps, init, writes, mapWrites, outputs,
    refuse: refuseB, pre, layout, events, notes: [...g.notes], hints: g.hints, ...(ev ? {event: ev.name} : {}), results, laws,
  }
  return {...(g.madeAt ? {madeAt: g.madeAt.name} : {}), model, leaves, args: argsOf, answers: [...g.answers.values()], ctor, kept, arms: [...g.arms].map(a => { const i = a.lastIndexOf(':'); return [a.slice(0, i), Number(a.slice(i + 1))] }), ...(cls ? {cls} : {}), stores, results: resultKinds}
}
const zeroRaw = (s: Var['sort']): Raw => (s.k === 'num' ? 0 : s.k === 'bool' ? false : s.k === 'choice' ? s.values[0]! : '')
const zeroOf = (s: Var['sort']): V => (s.k === 'num' ? {t: 'num', e: I.num(0)} : s.k === 'bool' ? {t: 'bool', e: I.F} : s.k === 'choice' ? {t: 'choice', e: I.llit(s.values[0]!, s.values)} : {t: 'str', e: {op: 'slit', value: ''}})
const varTerm = (v: Var): Term => (v.sort.k === 'num' ? {s: 'num', e: I.nvar(v.name)} : v.sort.k === 'bool' ? {s: 'bool', e: I.bvar(v.name)} : v.sort.k === 'choice' ? {s: 'choice', e: {op: 'var', name: v.name, values: v.sort.values}} : {s: 'str', e: {op: 'svar', name: v.name}})
function iteTerm(c: B, a: Term, b: Term): Term {
  if (a.s === 'num' && b.s === 'num') return {s: 'num', e: I.nite(c, a.e, b.e)}
  if (a.s === 'bool' && b.s === 'bool') return {s: 'bool', e: I.bite(c, a.e, b.e)}
  if (a.s === 'choice' && b.s === 'choice') return {s: 'choice', e: I.lite(c, a.e, b.e)}
  if (a.s === 'str' && b.s === 'str') return {s: 'str', e: I.kite(c, a.e, b.e)}
  throw new Refusal('?', 'a leaf of two sorts')
}

// --- the check: the code's side, a harness in its own language over JSON lines ----------------------------------------
type Raw = number | boolean | string
type FS = {mkdtempSync: (p: string) => string, rmSync: (p: string, o?: unknown) => void, openSync: (p: string, f: string) => number, closeSync: (fd: number) => void, readSync: (fd: number, b: Uint8Array, o: number, n: number, at: null) => number, writeSync: (fd: number, s: string) => number}
const proc = (globalThis as {process?: {getBuiltinModule?: (id: string) => unknown, env?: Record<string, string | undefined>}}).process
export const node = <T>(id: string): T => { const m = proc?.getBuiltinModule?.(id); if (!m) throw new Error(`the extractor runs the code's toolchain through ${id} (Node 20.16 or later, or Bun)`); return m as T }
// A harness: the command that starts it (it opens the two named pipes it is given) and what it is told first.
export type Harness = {cmd: string, args: string[], env?: Record<string, string>, hello: Record<string, unknown>}
export type StepEvidence = Evidence & {runMs: number}
export function checkStep(h: Harness, read: StepRead, r: Rule, sorts: Sorts, opts: StepOptions): StepEvidence {
  const o = opts.check ?? {}, m = read.model, bound = o.bound ?? 12
  const fs = node<FS>('node:fs'), cp = node<{execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string, spawn: (f: string, a: string[], o: Record<string, unknown>) => {kill: () => void}}>('node:child_process'), os = node<{tmpdir: () => string}>('node:os')
  const work = fs.mkdtempSync(`${os.tmpdir()}/gdp-stepcheck-`)
  let child: {kill: () => void} | undefined, wi = -1, ro = -1
  const empty = {runs: 0, requests: 0, fromStates: 0, probes: {conditions: 0, witnesses: 0, steps: 0}, refusedBoth: 0, outside: 0, edge: 0, compiledAgreed: 0, coverage: {arms: 0, hit: 0, missed: []}, ms: 0, runMs: 0}
  try {
    cp.execFileSync('mkfifo', [`${work}/in`, `${work}/out`], {})
    child = cp.spawn(h.cmd, [...h.args, `${work}/in`, `${work}/out`], {stdio: ['ignore', 'ignore', 'inherit'], env: {...proc?.env, ...h.env}})
    wi = fs.openSync(`${work}/in`, 'w'); ro = fs.openSync(`${work}/out`, 'r')
    const buf = new Uint8Array(1 << 20), dec = new TextDecoder()
    let pend = ''
    const line = (): string | undefined => {
      for (;;) {
        const k = pend.indexOf('\n')
        if (k >= 0) { const l = pend.slice(0, k); pend = pend.slice(k + 1); return l }
        const n = fs.readSync(ro, buf, 0, buf.length, null)
        if (n === 0) return undefined
        pend += dec.decode(buf.subarray(0, n), {stream: true})
      }
    }
    const ask = (cmd: Record<string, unknown>): Record<string, unknown> => {
      fs.writeSync(wi, `${JSON.stringify(cmd)}\n`)
      const l = line()
      if (l === undefined) throw new Error('the harness stopped')
      return JSON.parse(l) as Record<string, unknown>
    }
    const hi = ask({op: 'hello', ...h.hello, leaves: read.leaves, ctor: read.ctor, answers: read.answers, kept: read.kept, cls: read.cls ?? null, stores: read.stores, arms: read.arms, discard: opts.onError === 'discard'})
    if (hi.error) return {...empty, mismatch: `the code doesn't load with the check's harness: ${JSON.stringify(hi.error)}`}
    const num = (x: unknown, at: string): number => { const n = Number(x); if (typeof x === 'string' && Number.isSafeInteger(n) && String(n) === x) return n; throw new Outside(`${at} is ${String(x)}`) }
    const toSnap = (s: Record<string, unknown>): Snap => {
      const leaves: Record<string, Raw> = {}, maps: Snap['maps'] = {}
      for (const v of m.state) if (!m.outputs.includes(v.name)) leaves[v.name] = v.sort.k === 'num' ? num(s[v.name], v.name) : s[v.name] as Raw
      for (const d of m.maps) maps[d.name] = Object.fromEntries(Object.entries((s[d.name] ?? {}) as Record<string, Record<string, unknown>>).map(([k, c]) => [k, Object.fromEntries(d.fields.map(f => [f.name, f.sort.k === 'num' ? num(c[f.name], `${d.name}[${k}].${f.name}`) : c[f.name] as Raw]))]))
      return {leaves, maps}
    }
    const j = (x: Raw) => (typeof x === 'number' ? String(x) : x)
    const snapJson = (s: Snap): Record<string, unknown> => ({...Object.fromEntries(Object.entries(s.leaves).map(([k, v]) => [k, j(v)])), ...Object.fromEntries(Object.entries(s.maps).map(([k, cells]) => [k, Object.fromEntries(Object.entries(cells).map(([key, c]) => [key, Object.fromEntries(Object.entries(c).map(([f, x]) => [f, j(x)]))]))]))})
    const build = (a: PArg, inputs: Record<string, Raw>): unknown => (a.k === 'in' ? {in: inputs[a.name] ?? a.z ?? 0, ...(a.float ? {float: true} : {})} : a.k === 'opt' ? (inputs[a.none] === true ? {none: true} : build(a.v, inputs)) : a.k === 'rec' ? (a.f.length ? {rec: a.cls, f: Object.fromEntries(a.f.map(([f, x]) => [f, build(x, inputs)]))} : {inert: true}) : a.k === 'inert' ? {inert: true} : a.k === 'store' ? {store: a.name} : {dflt: true})
    const ctorArgs = (params: Record<string, Raw>) => read.ctor.map(([n, a]) => [n, build(a, params)])
    let now = 0, inputsNow: Record<string, Raw> = {}
    const answersOf = () => Object.fromEntries(read.answers.map(a => [a.key, a.inputs.none && inputsNow[a.inputs.none] === true ? {none: true} : {in: inputsNow[a.inputs.name] ?? 0, ...(a.inputs.float ? {float: true} : {})}]))
    let coverage: Coverage | undefined
    const r0 = performance.now()
    const side: CodeSide = {
      make: params => { const res = ask({op: 'new', a: ctorArgs(params), now: read.madeAt ? params[read.madeAt] : 0}); return res.err !== undefined ? {ok: false, error: JSON.stringify(res.err)} : {ok: true, value: res.id} },
      at: (s, params) => { const res = ask({op: 'at', a: ctorArgs(params), now: read.madeAt ? params[read.madeAt] : 0, state: snapJson(s)}); return res.bad ? undefined : res.id },
      snapOf: self => { const res = ask({op: 'get', id: self}); if (res.error) throw new Error(JSON.stringify(res.error)); return toSnap(res.state as Record<string, unknown>) },
      call: (self, e, args) => {
        const res = ask({op: 'call', id: self, m: e.call, a: args, now, answers: answersOf()}) as {out?: unknown, err?: string, frame?: string}
        if (res.frame) throw new Error(`the code changes ${res.frame}, a field the rule leaves out`)
        const kind = read.results[e.call] ?? 'none', failed = res.err !== undefined
        if (failed && !read.kept) return {ok: false, error: `raised: ${res.err}`}
        const value = (x: unknown): unknown => { const t = x as {n?: string, s?: string, o?: string} | null; if (t && typeof t === 'object') { if (t.n !== undefined) return num(t.n, `${e.call}'s result`); if (t.s !== undefined) return t.s; return `<${t.o}>` } return x }
        const out = res.out
        const rk = m.results?.[e.call]
        if (!rk) return {ok: true, value: undefined}
        if (rk.k === 'scalar') return {ok: true, value: value(out)}
        const o: Record<string, unknown> = {}
        for (const [f] of (rk as {fields: [string, string][]}).fields) {
          if (f === 'failed') o.failed = failed
          if (f === 'value') { const rv = m.state.find(v => v.name === (rk as {fields: [string, string][]}).fields.find(x => x[0] === 'value')![1])!; o.value = failed || out === null || out === undefined ? (rv.sort.k === 'num' ? 0 : rv.sort.k === 'bool' ? false : rv.sort.k === 'choice' ? rv.sort.values[0] : '') : value(out) }
          if (f === 'none') o.none = !failed && (out === null || out === undefined) && kind === 'maybe'
        }
        return {ok: true, value: o}
      },
      args: (inputs, e) => { inputsNow = inputs; return (read.args[e.call] ?? []).map(([n, a]) => [n, build(a, inputs)]) },
      setNow: n => { now = n },
      coverage: () => (coverage ??= closeAndCount()),
      drawSnap: rand => {
        const leaves: Record<string, Raw> = {}, maps: Snap['maps'] = {}
        const consts = constantsOf(m), strs = ['a', 'b', 'c', '']
        for (const v of m.state) {
          if (m.outputs.includes(v.name)) continue
          let x = draw(v.sort, sorts, v.name, rand, consts, bound, strs)
          if (typeof x === 'number' && sorts.get(v.name) === 'nat' && x < 0) x = -x
          if (typeof x === 'number' && Math.abs(x) > Number.MAX_SAFE_INTEGER / 4) x = rand(bound)
          leaves[v.name] = x
        }
        for (const l of read.leaves) if (l.kind === 'none' && leaves[l.name] === true) leaves[l.name.replace(/_none$/, '')] = g0(m, l.name.replace(/_none$/, ''))
        for (const d of m.maps) {
          const cells: Snap['maps'][string] = {}
          for (let i = rand(4); i > 0; i--) {
            const key = d.key === 'str' ? strs[rand(3)]! : String(rand(4))
            cells[key] = Object.fromEntries(d.fields.map(f => { let x = draw(f.sort, sorts, `${d.name}.${f.name}`, rand, consts, bound, strs); if (typeof x === 'number' && sorts.get(`${d.name}.${f.name}`) === 'nat') x = Math.abs(x); return [f.name, x] }))
          }
          maps[d.name] = cells
        }
        return {leaves, maps}
      },
      normalize: s => { for (const l of read.leaves) if (l.kind === 'none' && s.leaves[l.name] === true) s.leaves[l.name.replace(/_none$/, '')] = g0(m, l.name.replace(/_none$/, '')); return s },
    }
    function closeAndCount(): Coverage {
      const res = ask({op: 'coverage'}) as {hit?: [string, number][]}
      fs.closeSync(wi); wi = -1
      const hit = new Set((res.hit ?? []).map(([f, l]) => `${f}:${l}`))
      const arms = read.arms.map(([f, l]) => `${f}:${l}`)
      return {arms: arms.length, hit: arms.filter(a => hit.has(a)).length, missed: arms.filter(a => !hit.has(a)).map(a => `the arm at ${a}`)}
    }
    const ev = drive(m, r, sorts, side, o)
    return {...ev, runMs: Math.round(performance.now() - r0)}
  } catch (x) {
    return {...empty, mismatch: `the check's harness: ${(x as Error).message}`}
  } finally {
    if (wi >= 0) try { fs.closeSync(wi) } catch { /* closed */ }
    if (ro >= 0) try { fs.closeSync(ro) } catch { /* closed */ }
    try { child?.kill() } catch { /* gone */ }
    try { fs.rmSync(work, {recursive: true, force: true}) } catch { /* gone */ }
  }
}
// The value a None leaf holds in the rule (its sort's zero).
const g0 = (m: Model, name: string): Raw => { const v = m.state.find(x => x.name === name); return v?.sort.k === 'num' ? 0 : v?.sort.k === 'bool' ? false : v?.sort.k === 'choice' ? v.sort.values[0]! : '' }

// A front end's whole run: the module read, the model printed and built, the code run beside it.
export function extractStep(mod: SModule, h: (read: StepRead) => Harness, opts: StepOptions): Extraction & {read?: StepRead} {
  const notes: string[] = []
  let read: StepRead
  try { read = readStep(mod, opts) } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes}
    throw e
  }
  const x = fromModel(read.model, mod.file, opts.domains, notes, (rule, sorts) => checkStep(h(read), read, rule, sorts, opts))
  return {...x, read}
}
