// The extractor's Go front end (`extractGo`): a struct's methods read through Go's own parser and type checker
// (core/go/reader.go, go/ast and go/types, run with the Go toolchain), executed symbolically into the same Model the
// TypeScript reader makes (core/extract-read.ts), and printed, built and checked as that one is (core/extract.ts's
// fromModel). Only the reader and the check's runner are Go's: the check (core/extract-go-check.ts) builds the
// package as it ships with a generated harness beside it, drives the methods with the same requests as the rule, and
// prints every state as JSON for the comparison core/extract-check.ts makes. Nothing here is trusted either.
//
// The subset: a named struct of the package and the methods given (pointer or value receivers), the object starting
// at Go's zero value; fields of integer types (every width, signed and unsigned, named ones such as time.Duration),
// bool, string, *big.Int (an unbounded integer, nil a state of its own), nested structs (embedded ones too), maps from
// integers or strings to integers, booleans or structs of them, and slices of integers or booleans as lists; locals,
// assignments (=, :=, op=, ++, --, tuples), if, switch (with a tag or without, fallthrough, break), early returns,
// calls of the package's functions and methods (inlined), pointers to the state's objects (an interior pointer &x.f
// too: a write through one is a write to the object), errors.New and fmt.Errorf (a non-nil error), big.NewInt,
// new(big.Int) and big.Int's Add, Sub, Mul, Neg, Abs, Set, SetInt64, SetUint64, Cmp, Sign, Int64, IsInt64, the
// builtins len, append, delete, make, new, min, max and panic, conversions between integer types, a sync.Mutex's
// Lock with its deferred Unlock (one step is atomic in the rule), a context.Context argument only passed on to the
// package's own functions, and a pointer to another package's struct as an argument (its exported fields read as
// inputs, the package read from its source in the repo: core/go/reader.go's foreignPackage).
//
// Integers are exactly Go's. A result past its type's range wraps in Go: at 8, 16 and 32 bits the rule takes it modulo
// 2^n by cases (x + 1 past 2^32 − 1 is 0), as compare/term/c2ari.py takes C's unsigned arithmetic; at 64 bits the rule's
// numbers stop at ±2^53 (its runtime refuses past them, as for JavaScript's numbers), and a uint64 below 0, which Go
// would wrap to 2^64 − x, is refused. Division and remainder by a constant truncate toward zero, as Go's do; >> by a
// constant is a floor division, << a product, both wrapped. An error result that isn't nil, and a panic (explicit, a
// nil dereference, an index out of range, a write to a nil map), are the rule's refusals; the state must be as it was
// there (a write before them is refused) unless the caller discards what a failed call wrote (`onError: 'discard'`).
//
// Refused, each where it is with why: loops (a range over a map besides: Go's order is random), goroutines, channels,
// closures, defer (but a mutex's Unlock), recover, floats, strings beyond set and compared, bit operations, package
// variables (shared by every object), interfaces and type switches, generics, another module's code, a slice under a
// second name (two slices may share a backing array: append writes into it or not by its capacity), one object in
// two of the state's places or a pointer the caller gave kept in the state, a map replaced whole, two keys of one map
// or two writes of one list in one step.
import * as I from './extract-ir.ts'
import type {B, K, N} from './extract-ir.ts'
import {type Arg, type Event, type Layout, type MapDecl, type Model, Refusal, type Term, type Var, mergeOps, mergeWrites} from './extract-read.ts'
import {type Extraction, fromModel} from './extract.ts'
import {nonneg} from './extract-print.ts'
import {type GoCheckOptions, type GoLeaf, checkGo} from './extract-go-check.ts'

// --- the reader's JSON ----------------------------------------------------------------------------------------------
export type TT = {k: string, go?: string, generic?: boolean, name?: string, pkg?: string, own?: boolean, bits?: number, signed?: boolean, untyped?: boolean, elem?: number, key?: number,
  fields?: {name: string, t: number, embedded: boolean}[], xfields?: {name: string, t: number, embedded: boolean, exported: boolean}[], methods?: {name: string, ptr: boolean}[], params?: number[], results?: number[], elems?: number[], iface?: boolean, args?: number[], len?: number}
type GC = {int?: string, bool?: boolean, str?: string, float?: string, other?: string}
export type GX = {e: string, p: string, t: number, text: string, c?: GC, n?: string, o?: string, id?: string, x?: GX, y?: GX, op?: string, f?: GX, a?: GX[], k?: string, lo?: GX, hi?: GX, three?: boolean,
  path?: number[], indirect?: boolean, mptr?: boolean, mtype?: string, mpkg?: string, pkg?: string, builtin?: string, conv?: boolean, ell?: boolean, elts?: {field?: string, k?: GX, v: GX}[], i?: GX}
export type GS = {s: string, p: string, x?: GX, op?: string, l?: GX[], r?: GX[], c?: GX, then?: GS[], else?: GS, init?: GS, tag?: GX, cases?: {list?: GX[], default?: boolean, b: GS[], p: string}[],
  b?: GS[], specs?: {names: {name: string, id: string, t: number, c?: GC}[], v: GX[], const?: boolean, type?: boolean}[], tok?: string, label?: string, st?: GS}
export type GoParam = {name?: string, id?: string, t: number, variadic?: boolean, ts?: string}
export type GoFunc = {name: string, p: string, span: [number, number], recv?: {t: number, ptr: boolean, type: string, name?: string, id?: string}, generic?: boolean, params: GoParam[], results: GoParam[], body?: GS[]}
export type GoPkg = {package: string, files: {name: string, imports: {path: string, name: string, std: boolean}[]}[], funcs: GoFunc[], types: {name: string, t: number, p: string, span: [number, number]}[],
  consts: {name: string, t: number, c: GC, p: string}[], vars: {name: string, t: number, p: string, init?: GX}[], errors: string[], ttab: TT[]}

// --- values ---------------------------------------------------------------------------------------------------------
type IntTy = {bits: number, signed: boolean, t: number}
type Ptr = {k: 'nil'} | {k: 'obj', id: string, path: string[]} | {k: 'phi', c: B, a: Ptr, b: Ptr}
type GV =
  // A number (x.Cmp(y)'s and x.Sign()'s keep what they compare; len(s) of a string is read only against 0).
  | {t: 'num', e: N, ty: IntTy, cmp?: [N, N], slen?: K}
  // A slice of the state with an item appended, or its last taken off: only put back in its own place.
  | {t: 'push', id: string, x: GV} | {t: 'pop', id: string}
  | {t: 'bool', e: B}
  | {t: 'str', e: K}
  | {t: 'ptr', to: Ptr, elem: number}
  | {t: 'struct', ty: number, f: Map<string, GV>}
  | {t: 'err', is: B}
  | {t: 'map', id: string}
  | {t: 'list', id: string}
  | {t: 'tuple', xs: GV[]}
  | {t: 'nil'}
  | {t: 'opaque', why: string, ty: number}
type Origin = 'state' | 'input' | 'fresh'
type ListOp = {op: 'push', x: GV, when: B} | {op: 'pop', when: B} | {op: 'set', i: N, x: GV, when: B}
type Obj =
  | {k: 'struct', ty: number, f: Map<string, GV>, origin: Origin, lazy?: string}
  | {k: 'big', v: N, origin: Origin}
  | {k: 'map', decl: MapDecl, nil: B, w?: {key: K, has: B, vals: Map<string, GV>}, origin: Origin}
  | {k: 'list', decl: MapDecl, ops: ListOp[], origin: Origin}
type Path = {pc: B[], locals: Map<string, GV>, heap: Map<string, Obj>, locks: string[], defers: string[]}
type Ret = {p: Path, vs: GV[]}
type Place = {k: 'local', id: string, path: string[]} | {k: 'heap', ptr: GV, path: string[]}
type Flow = {live?: Path, rets: Ret[], brk: Path[], ft?: Path}

export type GoOptions = {
  // The struct, and the methods read (by default every method of it the package declares with a body).
  entry: string, methods?: string[],
  // What a failed call (an error result that isn't nil, or a panic) leaves: 'refuse' (the default) refuses a write to
  // the state before it, the object being the caller's to use after; 'discard' takes the caller to discard what the call
  // wrote (it keeps the object as it was before the call), and the check restores it so.
  onError?: 'refuse' | 'discard',
  domains?: Record<string, 'nat' | 'int'>,
  check?: GoCheckOptions,
}

const where = (x: {p: string}) => x.p || '?'
const refuse = (x: {p: string} | string, what: string): never => { throw new Refusal(typeof x === 'string' ? x : where(x), what) }
const TWO = (n: number) => 2 ** n

export class GoReader {
  readonly vars = new Map<string, Var>()
  readonly ranges = new Map<string, [number, number]>()
  readonly notes = new Set<string>()
  readonly refusals: B[] = []
  // The refusals where Go goes on and the rule's numbers stop (a uint64 below 0): the check counts them apart.
  readonly edges: B[] = []
  readonly leaves: GoLeaf[] = []
  readonly maps: MapDecl[] = []
  readonly lists: MapDecl[] = []
  readonly spans = new Map<string, [string, number, number]>()
  readonly hints = new WeakMap<object, string>()
  readonly inputs: Var[] = []
  private stack: string[] = []
  private fresh = 0
  readonly lazyInputs = new Map<string, {id: string, fields: [string, string][], sel: B}>()
  private stateOrigin = new Map<string, string>()
  method = ''
  constructor(readonly pkg: GoPkg, readonly opts: GoOptions) {}
  T(t: number): TT { return this.pkg.ttab[t] ?? {k: 'invalid'} }
  // (another package's types by its name, not the harness's alias for it)
  tname(t: number): string { const x = this.T(t); return x.go?.replace(/\bgdp_(?:\w*_)?(\w+)\./g, '$1.') ?? x.name ?? x.k }

  // --- types --------------------------------------------------------------------------------------------------------
  intTy(t: number): IntTy | undefined {
    const x = this.T(t)
    if (x.k !== 'int') return undefined
    return {bits: x.untyped ? 64 : x.bits ?? 64, signed: x.signed ?? true, t}
  }
  isBig(t: number): boolean { const x = this.T(t); return x.k === 'ext' && x.pkg === 'math/big' && x.name === 'Int' }
  isBigPtr(t: number): boolean { const x = this.T(t); return x.k === 'ptr' && this.isBig(x.elem!) }
  isContext(t: number): boolean { const x = this.T(t); return x.k === 'ext' && x.pkg === 'context' && x.name === 'Context' }
  isMutex(t: number): boolean { const x = this.T(t); return x.k === 'ext' && x.pkg === 'sync' && (x.name === 'Mutex' || x.name === 'RWMutex') }
  bigTy(t: number): IntTy { return {bits: 0, signed: true, t} }
  // An integer type's range (64 bits: the rule's numbers stop at 2^53 before Go's do).
  range(ty: IntTy): [number, number] {
    if (ty.bits === 0 || ty.bits >= 64) return ty.signed || ty.bits === 0 ? [-Infinity, Infinity] : [0, Infinity]
    return ty.signed ? [-TWO(ty.bits - 1), TWO(ty.bits - 1) - 1] : [0, TWO(ty.bits) - 1]
  }
  // The scalar sort a field of type t is in the rule, or why it isn't one.
  scalar(t: number): Var['sort'] | string {
    const x = this.T(t)
    if (x.k === 'int') return {k: 'num'}
    if (x.k === 'bool') return {k: 'bool'}
    if (x.k === 'string') return {k: 'str'}
    if (x.k === 'float') return `${this.tname(t)}: a float (a binary fraction that rounds; the subset reads integers)`
    return `${this.tname(t)}: a value outside the subset`
  }

  // Why a type is outside the subset, by what it is made of.
  whyType(t: number, depth = 0): string {
    const x = this.T(t)
    if (x.k === 'invalid') return "another module's type"
    if (x.k === 'ext' && x.iface) return 'an interface'
    if ((x.k === 'ext' || x.name) && x.pkg && !this.stdlib(x.pkg)) return "another module's type"
    if (x.k === 'ext' && x.pkg === 'time' && x.name === 'Time') return "the clock's time (time.Time is outside the subset)"
    if (x.k === 'error' || x.k === 'iface' || x.iface) return 'an interface'
    if (x.k === 'func') return 'a function'
    if (x.k === 'float') return 'a float'
    if (x.k === 'chan') return 'a channel'
    if ((x.k === 'ptr' || x.k === 'slice' || x.k === 'array' || x.k === 'map') && depth < 4) {
      const inner = x.k === 'map' ? [x.key!, x.elem!] : [x.elem!]
      for (const i of inner) { const w = this.whyType(i, depth + 1); if (w !== 'outside the subset') return x.k === 'map' ? `a map of ${w}` : x.k === 'ptr' ? w : `a ${x.k} of ${w}` }
    }
    if (x.k === 'ext') return `${x.go ?? x.name}, a type of the standard library outside the subset`
    return 'outside the subset'
  }
  // --- rule variables -----------------------------------------------------------------------------------------------
  newVar(name: string, sort: Var['sort'], role: Var['role'], note?: string): Var {
    let n = name.replace(/[^\w$]/g, '_')
    if (/^\d/.test(n)) n = `_${n}`
    while (this.vars.has(n) || RESERVED.has(n)) n = `${n}_`
    const v: Var = {name: n, sort, role, ...(note ? {note} : {})}
    this.vars.set(n, v)
    if (role === 'input') this.inputs.push(v)
    return v
  }
  valueOfVar(v: Var, ty?: IntTy): GV {
    if (v.sort.k === 'num') return {t: 'num', e: I.nvar(v.name), ty: ty ?? {bits: 64, signed: true, t: -1}}
    if (v.sort.k === 'bool') return {t: 'bool', e: I.bvar(v.name)}
    return {t: 'str', e: {op: 'svar', name: v.name}}
  }

  // --- the state: the struct's fields as variables, leaf by leaf ----------------------------------------------------
  // Each field of a subset type is a leaf (a variable, or a map or a list); one of another type is left out (the check
  // asks the code not to change it), and reading or writing it is refused where it is.
  buildStruct(t: number, path: string[], heap: Map<string, Obj>, at: {p: string}): Map<string, GV> {
    const x = this.T(t), out = new Map<string, GV>()
    for (const f of x.fields ?? []) {
      const fp = [...path, f.name], name = fp.join('_'), ft = this.T(f.t)
      const leaf = (kind: GoLeaf['kind'], v: Var, ty: number) => { this.leaves.push({name: v.name, path: fp, kind, t: ty, go: this.tname(ty)}); return v }
      if (ft.k === 'int') {
        const ty = this.intTy(f.t)!, v = leaf('int', this.newVar(name, {k: 'num'}, 'state'), f.t)
        this.ranges.set(v.name, this.range(ty))
        out.set(f.name, this.valueOfVar(v, ty))
      } else if (ft.k === 'bool') out.set(f.name, this.valueOfVar(leaf('bool', this.newVar(name, {k: 'bool'}, 'state'), f.t)))
      else if (ft.k === 'string') out.set(f.name, this.valueOfVar(leaf('str', this.newVar(name, {k: 'str'}, 'state'), f.t)))
      else if (this.isBigPtr(f.t)) {
        // A *big.Int: its value, and whether it is nil (Go's zero value).
        const v = leaf('big', this.newVar(name, {k: 'num'}, 'state', 'a *big.Int (its value; 0 where it is nil)'), f.t)
        const nil = leaf('bignil', this.newVar(`${name}_nil`, {k: 'bool'}, 'state', `whether ${fp.join('.')} is nil`), f.t)
        const id = `state:${fp.join('.')}`
        heap.set(id, {k: 'big', v: I.nvar(v.name), origin: 'state'})
        this.stateOrigin.set(id, fp.join('.'))
        out.set(f.name, {t: 'ptr', to: phiP(I.bvar(nil.name), {k: 'nil'}, {k: 'obj', id, path: []}), elem: ft.elem!})
      } else if (ft.k === 'struct' && (ft.own || !ft.name)) {
        out.set(f.name, {t: 'struct', ty: f.t, f: this.buildStruct(f.t, fp, heap, at)})
      } else if (ft.k === 'map' && this.mapOK(f.t)) {
        const decl = this.mapDecl(f.t, name), id = `state:${fp.join('.')}`
        const nil = leaf('mapnil', this.newVar(`${decl.name}_nil`, {k: 'bool'}, 'state', `whether ${fp.join('.')} is nil (a nil map holds no key, and a write to it panics)`), f.t)
        this.leaves.push({name: decl.name, path: fp, kind: 'map', t: f.t, go: this.tname(f.t)})
        heap.set(id, {k: 'map', decl, nil: I.bvar(nil.name), origin: 'state'})
        out.set(f.name, {t: 'map', id})
      } else if (ft.k === 'slice' && ['int', 'bool'].includes(this.T(ft.elem!).k)) {
        const decl: MapDecl = {name: this.newVar(name, {k: 'num'}, 'state').name, key: 'num', fields: [{name: '$item', sort: this.T(ft.elem!).k === 'int' ? {k: 'num'} : {k: 'bool'}, role: 'state'}], scalar: true, js: 'Map'}
        this.lists.push(decl)
        const it = this.intTy(ft.elem!)
        if (it) this.ranges.set(`${decl.name}.$item`, this.range(it))
        this.leaves.push({name: decl.name, path: fp, kind: 'list', t: f.t, go: this.tname(f.t)})
        const id = `state:${fp.join('.')}`
        heap.set(id, {k: 'list', decl, ops: [], origin: 'state'})
        out.set(f.name, {t: 'list', id})
      } else {
        out.set(f.name, {t: 'opaque', why: `${fp.join('.')} is a ${this.tname(f.t)}, a field outside the subset (left out of the rule)`, ty: f.t})
        this.leaves.push({name: '', path: fp, kind: 'frame', t: f.t, go: this.tname(f.t)})
      }
    }
    return out
  }
  mapOK(t: number): boolean {
    const x = this.T(t), kk = this.T(x.key!).k, v = this.T(x.elem!)
    if (kk !== 'int' && kk !== 'string') return false
    if (v.k === 'int' || v.k === 'bool') return true
    return v.k === 'struct' && (v.fields ?? []).every(f => ['int', 'bool'].includes(this.T(f.t).k))
  }
  mapDecl(t: number, name: string): MapDecl {
    const x = this.T(t), v = this.T(x.elem!), key = this.T(x.key!).k === 'int' ? 'num' : 'str'
    const n = this.newVar(name, {k: 'num'}, 'state').name
    const fields: Var[] = v.k === 'struct' ? (v.fields ?? []).map(f => ({name: f.name, sort: this.T(f.t).k === 'int' ? {k: 'num'} : {k: 'bool'}, role: 'state'} as Var)) : [{name: 'value', sort: v.k === 'int' ? {k: 'num'} : {k: 'bool'}, role: 'state'}]
    const decl: MapDecl = {name: n, key, fields, scalar: v.k !== 'struct', js: 'Map'}
    for (const f of fields) { const it = this.intTy(v.k === 'struct' ? v.fields!.find(g => g.name === f.name)!.t : x.elem!); if (it) this.ranges.set(`${n}.${f.name}`, this.range(it)) }
    this.maps.push(decl)
    return decl
  }

  // An input of an integer type: a request the code can't be given (past its type's range) is refused where `sel` (the
  // method called) holds, the claim being for the type's values.
  typedInput(x: Var, t: number, sel: B): IntTy | undefined {
    const it = this.intTy(t)
    if (!it) return undefined
    this.ranges.set(x.name, this.range(it))
    const [lo, hi] = this.range(it)
    if (Number.isFinite(hi)) this.refusals.push(I.and(sel, I.cmp('<', I.num(hi), I.nvar(x.name))))
    if (Number.isFinite(lo) && lo < 0) this.refusals.push(I.and(sel, I.cmp('<', I.nvar(x.name), I.num(lo))))
    else if (!it.signed) this.refusals.push(I.and(sel, I.cmp('<', I.nvar(x.name), I.num(0))))
    return it
  }

  // --- the functions --------------------------------------------------------------------------------------------------
  // The arguments of a method or a function: each an input (a pointer to a struct of the package a fresh object whose
  // fields read are inputs, a *big.Int one whose value is).
  bindParams(fn: GoFunc, sel: B, p0: Path): {p: Path, args: Arg[], params: {name: string, t: number, arg: Arg}[]} {
    const args: Arg[] = [], params: {name: string, t: number, arg: Arg}[] = []
    let p = p0
    if (fn.params.some(x => x.variadic)) refuse(fn, `${fn.name}: a variadic method`)
    // An input of an integer type: a request the code can't be given (past its type's range) is refused, the claim
    // being for the type's values.
    const typed = (x: Var, t: number) => this.typedInput(x, t, sel)
    for (const pa of fn.params) {
      const name = `${fn.name}_${pa.name ?? 'arg'}`, tt = this.T(pa.t), s = this.scalar(pa.t)
      let v: GV, arg: Arg
      if (typeof s !== 'string') {
        const x = this.newVar(name, s, 'input')
        v = this.valueOfVar(x, typed(x, pa.t)); arg = {k: 'input', name: x.name}
      } else if (this.isBigPtr(pa.t)) {
        const x = this.newVar(name, {k: 'num'}, 'input', 'a *big.Int argument (not nil: the claim is for calls that give one)')
        const id = `in:${x.name}`
        p.heap.set(id, {k: 'big', v: I.nvar(x.name), origin: 'input'})
        v = {t: 'ptr', to: {k: 'obj', id, path: []}, elem: tt.elem!}; arg = {k: 'input', name: x.name}
        this.notes.add(`${name}: a *big.Int argument, never nil here (the claim is for calls that give one)`)
      } else if (tt.k === 'ptr' && ((this.T(tt.elem!).k === 'struct' && this.T(tt.elem!).own) || this.T(tt.elem!).xfields)) {
        // (Another package's struct is read as data the same way: its exported fields, the only ones the package's code
        // can read; its methods stay that package's code, refused where they are called.)
        // A pointer to a struct the caller gives: its fields read are inputs (each made where it is first read).
        const id = `in:${name}`
        p.heap.set(id, {k: 'struct', ty: tt.elem!, f: new Map(), origin: 'input', lazy: name})
        this.lazyInputs.set(id, {id: name, fields: [], sel})
        v = {t: 'ptr', to: {k: 'obj', id, path: []}, elem: tt.elem!}; arg = {k: 'lazy', prefix: name}
        this.notes.add(`${name}: a *${this.tname(tt.elem!)} the caller gives, a fresh one for each call (its fields read are inputs; the claim is for calls that don't pass the object itself)`)
      } else if ((tt.k === 'struct' && tt.own) || tt.xfields) {
        // A struct the caller gives by value: the call's own copy, so a value here as a local struct is (no other name
        // reaches it, and writing it changes nothing the caller sees). Each field of a subset type an input (another
        // package's, its exported fields: all its code can set), the others left out, refused where they are read.
        const fields: [string, Arg][] = [], f = new Map<string, GV>()
        for (const fd of tt.fields ?? tt.xfields!.filter(x => x.exported)) {
          const fs = this.scalar(fd.t), fname = `${name}_${fd.name}`
          if (typeof fs === 'string') { f.set(fd.name, {t: 'opaque', why: `${pa.name}.${fd.name} of the argument: ${fs}`, ty: fd.t}); continue }
          const x = this.newVar(fname, fs, 'input')
          f.set(fd.name, this.valueOfVar(x, typed(x, fd.t))); fields.push([fd.name, {k: 'input', name: x.name}])
        }
        v = {t: 'struct', ty: pa.t, f}; arg = {k: 'rec', fields}
        this.notes.add(`${fn.name}(${pa.name ?? '_'}): a ${this.tname(pa.t)} given by value, its fields inputs`)
      } else if (this.isContext(pa.t)) {
        // A context.Context: the check gives context.Background(). Exact while the step never reads it: passed on to the
        // package's own functions only (its methods, Done, Err, Value, are another package's code; given to another
        // package's function, it is that function's: both refused where they are).
        v = {t: 'opaque', why: `${pa.name ?? 'the context'}, a context.Context read (the subset only passes one on to the package's own functions)`, ty: pa.t}; arg = {k: 'lit', value: 'context'}
        this.notes.add(`${fn.name}(${pa.name ?? '_'}): a context.Context, passed on to the package's own functions only (the claim is for any context, the step never reading it)`)
      } else return refuse(fn, `${fn.name}(${pa.name}): an argument of type ${pa.ts ?? this.tname(pa.t)} (${this.whyType(pa.t)})`)
      if (pa.id) p = this.bind(pa.id, v, fn, p)
      args.push(arg); params.push({name: pa.name ?? '', t: pa.t, arg})
    }
    return {p, args, params}
  }
  methodOf(type: string, name: string): GoFunc | undefined { return this.pkg.funcs.find(f => f.recv?.type === type && f.name === name) }
  funcOf(name: string): GoFunc | undefined { return this.pkg.funcs.find(f => !f.recv && f.name === name) }

  // --- paths ----------------------------------------------------------------------------------------------------------
  cond(p: Path): B { return I.and(...p.pc) }
  // A refusal (an error returned, a panic, a request the code can't be given) where c holds on this path.
  refuseWhere(p: Path, c: B, at: {p: string}, what: string, state = true) {
    const w = I.and(this.cond(p), c)
    if (w.op === 'const' && !w.v) return
    if (state && this.opts.onError !== 'discard' && this.changed(p)) refuse(at, `${what} after the state is written (the caller would see the object changed and the call failed; with onError: 'discard' the caller is taken to drop what a failed call wrote)`)
    this.refusals.push(w)
    if (!state) this.edges.push(w)
  }
  assume(p: Path, c: B): Path { return c.op === 'const' && c.v ? p : {...p, pc: [...p.pc, c]} }
  // Whether the step wrote the state on this path (structurally: a write of the value it had counts as none).
  changed(p: Path): boolean {
    for (const [id, o] of p.heap) {
      if (o.origin !== 'state') continue
      const init = this.init.get(id)
      if (!init) continue
      if (o.k === 'map' ? !!o.w || keyOfB(o.nil) !== keyOfB((init as typeof o).nil) : o.k === 'list' ? o.ops.length > 0 : keyOfObj(o) !== keyOfObj(init)) return true
    }
    return false
  }
  init = new Map<string, Obj>()

  // Paths joined where they meet: each value by cases on the condition that picks the first.
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
    if (a.locks.join() !== b.locks.join()) refuse(at, 'a mutex locked on one path and not on another')
    const locals = new Map<string, GV>()
    for (const [n, x] of a.locals) { const y = b.locals.get(n); if (y) locals.set(n, this.mergeV(c, x, y, at)) }
    const heap = new Map<string, Obj>()
    for (const [id, x] of a.heap) { const y = b.heap.get(id); heap.set(id, y ? this.mergeObj(c, x, y, at) : x) }
    for (const [id, y] of b.heap) if (!heap.has(id)) heap.set(id, y)
    return {pc, locals, heap, locks: a.locks, defers: [...new Set([...a.defers, ...b.defers])]}
  }
  mergeV(c: B, a: GV, b: GV, at: {p: string}): GV {
    if (a === b) return a
    if (a.t === 'num' && b.t === 'num') return {t: 'num', e: I.nite(c, a.e, b.e), ty: a.ty}
    if (a.t === 'bool' && b.t === 'bool') return {t: 'bool', e: I.bite(c, a.e, b.e)}
    if (a.t === 'str' && b.t === 'str') return {t: 'str', e: I.kite(c, a.e, b.e)}
    if (a.t === 'err' && b.t === 'err') return {t: 'err', is: I.bite(c, a.is, b.is)}
    const asPtr = (v: GV): Ptr | undefined => (v.t === 'ptr' ? v.to : v.t === 'nil' ? {k: 'nil'} : undefined)
    if ((a.t === 'ptr' || a.t === 'nil') && (b.t === 'ptr' || b.t === 'nil')) {
      const elem = a.t === 'ptr' ? a.elem : (b as {elem: number}).elem
      return {t: 'ptr', to: phiP(c, asPtr(a)!, asPtr(b)!), elem}
    }
    if ((a.t === 'err' && b.t === 'nil') || (a.t === 'nil' && b.t === 'err')) return {t: 'err', is: I.bite(c, a.t === 'err' ? a.is : I.F, b.t === 'err' ? b.is : I.F)}
    if (a.t === 'struct' && b.t === 'struct') {
      const f = new Map<string, GV>()
      for (const [n, x] of a.f) f.set(n, this.mergeV(c, x, b.f.get(n)!, at))
      return {t: 'struct', ty: a.ty, f}
    }
    if (a.t === 'tuple' && b.t === 'tuple') return {t: 'tuple', xs: a.xs.map((x, i) => this.mergeV(c, x, b.xs[i]!, at))}
    if ((a.t === 'map' && b.t === 'map') || (a.t === 'list' && b.t === 'list')) { if (a.id === b.id) return a; return refuse(at, 'one of two maps or slices by a condition') }
    if (a.t === 'opaque' && b.t === 'opaque' && a.why === b.why) return a
    if (keyOfV(a) === keyOfV(b)) return a
    return refuse(at, `a value that is a ${a.t} on one path and a ${b.t} on another`)
  }
  mergeObj(c: B, a: Obj, b: Obj, at: {p: string}): Obj {
    if (a === b) return a
    if (a.k === 'big' && b.k === 'big') return {...a, v: I.nite(c, a.v, b.v)}
    if (a.k === 'struct' && b.k === 'struct') {
      const f = new Map<string, GV>()
      for (const [n, x] of a.f) { const y = b.f.get(n); f.set(n, y ? this.mergeV(c, x, y, at) : x) }
      for (const [n, y] of b.f) if (!f.has(n)) f.set(n, y)
      return {...a, f}
    }
    if (a.k === 'map' && b.k === 'map') {
      const w = mergeWrites(c, a.w, b.w, key => this.baseCell(a.decl, key), (c2, x, y) => this.mergeV(c2, x, y, at))
      return {...a, nil: I.bite(c, a.nil, b.nil), ...(w ? {w} : {})}
    }
    if (a.k === 'list' && b.k === 'list') return {...a, ops: mergeOps(c, a.ops, b.ops)}
    return refuse(at, 'an object of two kinds by a condition')
  }
  baseCell(d: MapDecl, key: K): {has: B, vals: Map<string, GV>} {
    const cellN = (f: string): N => ({op: 'cell', map: d.name, key, field: f}), cellB = (f: string): B => ({op: 'cell', map: d.name, key, field: f})
    const vals = new Map<string, GV>(d.fields.map(f => [f.name, f.sort.k === 'num' ? {t: 'num', e: cellN(f.name), ty: {bits: 64, signed: true, t: -1}} as GV : {t: 'bool', e: cellB(f.name)} as GV]))
    return {has: cellB('has'), vals}
  }

  // --- objects through pointers ---------------------------------------------------------------------------------------
  // The cases a pointer is: each object (with the condition it is that one), and the condition it is nil.
  cases(p: Ptr, c: B = I.T): {nil: B, objs: {c: B, id: string, path: string[]}[]} {
    if (p.k === 'nil') return {nil: c, objs: []}
    if (p.k === 'obj') return {nil: I.F, objs: [{c, id: p.id, path: p.path}]}
    const a = this.cases(p.a, I.and(c, p.c)), b = this.cases(p.b, I.and(c, I.not(p.c)))
    return {nil: I.or(a.nil, b.nil), objs: [...a.objs, ...b.objs]}
  }
  // The value at a place inside an object (a field path into its nested structs).
  readObj(o: Obj, path: string[], at: {p: string}, p: Path, id: string): GV {
    if (o.k === 'big') { if (path.length) refuse(at, 'a field of a big.Int'); return refuse(at, 'a big.Int read as a value (it is used through its pointer)') }
    if (o.k !== 'struct') return refuse(at, 'a field of other than a struct')
    let v: GV | undefined = {t: 'struct', ty: o.ty, f: o.f}
    for (const seg of path) {
      if (v?.t !== 'struct') return refuse(at, `.${seg} of other than a struct`)
      v = v.f.get(seg) ?? this.lazyField(id, seg, v.ty, p, at)
    }
    return v!
  }
  writeObj(o: Obj, path: string[], x: GV, at: {p: string}): Obj {
    if (o.k !== 'struct') return refuse(at, 'a write into other than a struct')
    if (!path.length) { if (x.t !== 'struct') return refuse(at, 'a struct set to other than a struct'); return {...o, f: new Map(x.f)} }
    const set = (fs: Map<string, GV>, segs: string[]): Map<string, GV> => {
      const seg = segs[0]!, rest = segs.slice(1)
      const out = new Map(fs)
      if (!rest.length) { const old = fs.get(seg); if (old?.t === 'opaque') refuse(at, `writes ${old.why}`); out.set(seg, x); return out }
      const inner = fs.get(seg)
      if (inner?.t !== 'struct') return refuse(at, `.${seg} of other than a struct`)
      out.set(seg, {...inner, f: set(inner.f, rest)})
      return out
    }
    return {...o, f: set(o.f, path)}
  }
  // A field of an input struct, made an input where it is first read.
  lazyField(id: string, f: string, ty: number, p: Path, at: {p: string}): GV {
    const li = this.lazyInputs.get(id)
    const ft = (this.T(ty).fields ?? this.T(ty).xfields)?.find(x => x.name === f)
    if (!li || !ft) return refuse(at, `no field ${f}`)
    const s = this.scalar(ft.t)
    if (typeof s === 'string') {
      if (this.isBigPtr(ft.t)) {
        const v = this.newVar(`${li.id}_${f}`, {k: 'num'}, 'input', 'a *big.Int argument (not nil: the claim is for calls that give one)')
        li.fields.push([f, v.name])
        const oid = `in:${v.name}`
        p.heap.set(oid, {k: 'big', v: I.nvar(v.name), origin: 'input'})
        const g: GV = {t: 'ptr', to: {k: 'obj', id: oid, path: []}, elem: this.T(ft.t).elem!}
        ;(p.heap.get(id) as {f: Map<string, GV>}).f.set(f, g)
        return g
      }
      return refuse(at, `${f} of the argument: ${s}`)
    }
    const v = this.newVar(`${li.id}_${f}`, s, 'input')
    li.fields.push([f, v.name])
    const g = this.valueOfVar(v, this.typedInput(v, ft.t, li.sel))
    ;(p.heap.get(id) as {f: Map<string, GV>}).f.set(f, g)
    return g
  }
  // *p, read: by cases on the objects p may point to; nil panics.
  deref(v: GV, path: string[], at: {p: string}, p: Path): [GV, Path] {
    if (v.t === 'nil') { this.refuseWhere(p, I.T, at, 'a nil dereference'); return [{t: 'opaque', why: 'unreachable', ty: -1}, {...p, pc: [...p.pc, I.F]}] }
    if (v.t !== 'ptr') return refuse(at, `a dereference of a ${v.t}`)
    const cs = this.cases(v.to)
    this.refuseWhere(p, cs.nil, at, `a nil dereference (${at.p})`)
    const q = this.assume(p, I.not(cs.nil))
    if (!cs.objs.length) return [{t: 'opaque', why: 'unreachable', ty: -1}, q]
    let out: GV | undefined
    for (const o of [...cs.objs].reverse()) {
      const x = this.readObj(q.heap.get(o.id)!, [...o.path, ...path], at, q, o.id)
      out = out ? this.mergeV(o.c, x, out, at) : x
    }
    return [out!, q]
  }
  // A write through a pointer: to each object it may be, where it is that one.
  writeThrough(v: GV, path: string[], x: GV, at: {p: string}, p: Path): Path {
    if (v.t !== 'ptr') return refuse(at, `a write through a ${v.t}`)
    const cs = this.cases(v.to)
    this.refuseWhere(p, cs.nil, at, 'a nil dereference')
    const q = this.assume(p, I.not(cs.nil))
    const heap = new Map(q.heap)
    for (const o of cs.objs) {
      const obj = heap.get(o.id)!
      const old = this.readObj(obj, [...o.path, ...path], at, q, o.id)
      heap.set(o.id, this.writeObj(obj, [...o.path, ...path], this.mergeV(o.c, x, old, at), at))
    }
    return {...q, heap}
  }

  // --- places (what an assignment writes) -----------------------------------------------------------------------------
  // A place: a local (and a field path into its struct value), or a field path inside the object a pointer points to.
  place(x: GX, p: Path): [{k: 'local', id: string, path: string[]} | {k: 'heap', ptr: GV, path: string[]} | {k: 'blank'}, Path] {
    if (x.e === 'id') {
      if (x.n === '_') return [{k: 'blank'}, p]
      if (x.o !== 'var' || x.id?.startsWith('pkg:')) return refuse(x, `${x.text}: ${x.id?.startsWith('pkg:') ? 'a package variable (state every object shares)' : 'not a local'}`)
      return [{k: 'local', id: x.id!, path: []}, p]
    }
    if (x.e === 'star') { const [v, q] = this.ev(x.x!, p); return [{k: 'heap', ptr: v, path: []}, q] }
    if (x.e === 'sel' && x.k === 'field') {
      const segs = this.fieldPath(x)
      // Through the base: a pointer (or an embedded pointer on the way) makes the place the pointee's.
      const bt = this.T(x.x!.t)
      if (bt.k === 'ptr') { const [v, q] = this.ev(x.x!, p); return this.walkPath({k: 'heap', ptr: v, path: []}, this.T(bt.elem!), segs, x, q) }
      const [base, q] = this.place(x.x!, p)
      if (base.k === 'blank') return refuse(x, 'a field of _')
      return this.walkPath(base, bt, segs, x, q)
    }
    return refuse(x, `${x.text}: an assignment to other than a variable, a field or *p`)
  }
  // The field names a selection goes through (its embedded fields first).
  fieldPath(x: GX): {name: string, t: number}[] {
    let t = this.T(x.x!.t)
    if (t.k === 'ptr') t = this.T(t.elem!)
    const out: {name: string, t: number}[] = []
    for (const i of x.path ?? []) {
      const f = (t.fields ?? t.xfields)?.[i]
      if (!f) return refuse(x, `${x.text}: a field the struct's type doesn't list`)
      out.push(f)
      t = this.T(f.t)
      if (t.k === 'ptr' && out.length < (x.path ?? []).length) t = this.T(t.elem!)
    }
    return out
  }
  walkPath(base: {k: 'local', id: string, path: string[]} | {k: 'heap', ptr: GV, path: string[]}, _t: TT, segs: {name: string, t: number}[], x: GX, p: Path): [{k: 'local', id: string, path: string[]} | {k: 'heap', ptr: GV, path: string[]}, Path] {
    let cur = base, q = p
    segs.forEach((s, i) => {
      cur = {...cur, path: [...cur.path, s.name]}
      // An embedded pointer on the way: the rest is the pointee's.
      if (i < segs.length - 1 && this.T(s.t).k === 'ptr') { const [v, q2] = this.read(cur, x, q); q = q2; cur = {k: 'heap', ptr: v, path: []} }
    })
    return [cur, q]
  }
  read(pl: {k: 'local', id: string, path: string[]} | {k: 'heap', ptr: GV, path: string[]}, at: {p: string}, p: Path): [GV, Path] {
    if (pl.k === 'heap') return this.deref(pl.ptr, pl.path, at, p)
    let v = p.locals.get(pl.id) ?? refuse(at, `${(at as GX).text ?? ''}: a variable read before it is set`)
    for (const s of pl.path) { if (v.t !== 'struct') refuse(at, `.${s} of other than a struct`); v = (v as {f: Map<string, GV>}).f.get(s) ?? refuse(at, `no field ${s}`) }
    return [v, p]
  }
  write(pl: {k: 'local', id: string, path: string[]} | {k: 'heap', ptr: GV, path: string[]} | {k: 'blank'}, x: GV, at: {p: string}, p: Path): Path {
    if (pl.k === 'blank') return p
    this.secondName(x, at, p, pl)
    if (pl.k === 'heap') {
      this.keepsInState(pl, x, at, p)
      return this.writeThrough(pl.ptr, pl.path, x, at, p)
    }
    if (!pl.path.length) return {...p, locals: new Map(p.locals).set(pl.id, x)}
    const old = p.locals.get(pl.id) ?? refuse(at, 'a field of a variable not set')
    const set = (v: GV, segs: string[]): GV => {
      const s = segs[0]!, rest = segs.slice(1)
      if (v.t !== 'struct') return refuse(at, `.${s} of other than a struct`)
      const f = new Map(v.f)
      f.set(s, rest.length ? set(v.f.get(s)!, rest) : x)
      return {...v, f}
    }
    return {...p, locals: new Map(p.locals).set(pl.id, set(old, pl.path))}
  }
  // A slice or a map under a second name: refused (two slices may share a backing array; a map is a reference).
  secondName(x: GV, at: {p: string}, _p: Path, pl: {k: string, path?: string[]}) {
    if (x.t === 'list') refuse(at, 'a slice given a second name (two slices may share a backing array: append writes into it or not by its capacity)')
    if (x.t === 'map') refuse(at, 'a map given a second name (a map is a reference: a write through either is a write to both)')
    void pl
  }
  // A pointer stored into the state: to a fresh object only (one the state already holds would be in two places; one the
  // caller gave would be the caller's to change after the call).
  keepsInState(pl: {k: 'heap', ptr: GV, path: string[]}, x: GV, at: {p: string}, p: Path) {
    if (x.t !== 'ptr') return
    const into = this.cases(pl.ptr.t === 'ptr' ? pl.ptr.to : {k: 'nil'})
    if (!into.objs.some(o => p.heap.get(o.id)?.origin === 'state')) return
    for (const o of this.cases(x.to).objs) {
      const origin = p.heap.get(o.id)?.origin
      if (origin === 'input') refuse(at, 'the state keeps a pointer the caller gave (the caller may change its object after the call)')
      if (origin === 'state') refuse(at, `the state's ${this.stateOrigin.get(o.id) ?? 'object'} put in a second place of the state (one object in two places)`)
    }
  }

  // --- statements -----------------------------------------------------------------------------------------------------
  block(ss: GS[], p: Path): Flow {
    let live: Path | undefined = p
    const rets: Ret[] = [], brk: Path[] = []
    let ft: Path | undefined
    for (const s of ss) {
      if (!live) break
      if (s.s === 'branch' && s.tok === 'fallthrough') { ft = live; live = undefined; break }
      const f = this.stmt(s, live)
      rets.push(...f.rets); brk.push(...f.brk)
      live = f.live
    }
    return {...(live ? {live} : {}), rets, brk, ...(ft ? {ft} : {})}
  }
  stmt(s: GS, p: Path): Flow {
    switch (s.s) {
      case 'block': return this.block(s.b!, p)
      case 'empty': return {live: p, rets: [], brk: []}
      case 'expr': {
        const x = s.x!
        if (x.e === 'call' && x.builtin === 'panic') { const [, q] = this.args(x.a ?? [], p); this.refuseWhere(q, I.T, s, 'a panic'); return {rets: [], brk: []} }
        const [, q] = this.ev(x, p)
        return {live: q, rets: [], brk: []}
      }
      case 'incdec': {
        const [pl, q] = this.place(s.x!, p), [v, q2] = this.readPlace(pl, s, q)
        if (v.t !== 'num') return refuse(s, `${s.op} of a ${v.t}`)
        return {live: this.write(pl, this.arith(s.op === '++' ? '+' : '-', v, {t: 'num', e: I.num(1), ty: v.ty}, s, q2), s, q2), rets: [], brk: []}
      }
      case 'assign': return {live: this.assign(s, p), rets: [], brk: []}
      case 'decl': {
        let q = p
        for (const sp of s.specs ?? []) {
          if (sp.type) refuse(s, 'a type declared in a function')
          if (sp.const) continue
          if (sp.v.length && sp.v.length !== sp.names.length) {
            const [v, q2] = this.ev(sp.v[0]!, q)
            if (v.t !== 'tuple') refuse(s, 'a declaration of several from one value')
            q = q2
            sp.names.forEach((n, i) => { q = this.bind(n.id, (v as {xs: GV[]}).xs[i]!, s, q) })
            continue
          }
          sp.names.forEach((n, i) => {
            const e = sp.v[i]
            if (e) { const [v, q2] = this.ev(e, q); q = this.bind(n.id, this.convertTo(v, n.t, e), s, q2) }
            else { const [z, q2] = this.zero(n.t, s, q); q = this.bind(n.id, z, s, q2) }
          })
        }
        return {live: q, rets: [], brk: []}
      }
      case 'if': {
        let q = p
        if (s.init) { const f = this.stmt(s.init, q); if (!f.live) return f; q = f.live }
        const [c, q2] = this.ev(s.c!, q)
        if (c.t !== 'bool') return refuse(s.c!, `${s.c!.text}: a condition that isn't a boolean`)
        const t = c.e.op === 'const' && !c.e.v ? undefined : this.block(s.then!, this.assume(q2, c.e))
        const e = c.e.op === 'const' && c.e.v ? undefined : s.else ? this.stmt(s.else, this.assume(q2, I.not(c.e))) : {live: this.assume(q2, I.not(c.e)), rets: [], brk: []}
        return this.joinFlows([t, e], s)
      }
      case 'switch': return this.switchStmt(s, p)
      case 'return': return this.ret(s, p)
      case 'branch':
        if (s.tok === 'break' && !s.label) return {rets: [], brk: [p]}
        return refuse(s, `${s.tok}${s.label ? ` ${s.label}` : ''} (the subset reads break in a switch; loops and goto are outside it)`)
      case 'defer': {
        // A mutex's Unlock deferred after its Lock: the step is atomic in the rule.
        const x = s.x!
        if (x.e === 'call' && x.f?.e === 'sel' && x.f.k === 'method' && /^(R?Unlock)$/.test(x.f.n!) && this.isMutex(this.T(x.f.x!.t).k === 'ptr' ? this.T(x.f.x!.t).elem! : x.f.x!.t)) {
          const key = this.lockKey(x.f.x!, p)
          if (!p.locks.includes(key)) refuse(s, `defer ${x.text} without its Lock first`)
          return {live: {...p, defers: [...p.defers, key]}, rets: [], brk: []}
        }
        return refuse(s, 'defer (other than a mutex\'s Unlock after its Lock): it runs at the return, after the results are set')
      }
      case 'for': return refuse(s, 'a loop (for)')
      case 'range': {
        const xt = s.x ? this.T(s.x.t) : undefined
        return refuse(s, xt?.k === 'map' ? 'a range over a map (Go\'s iteration order is random, and loops are outside the subset)' : 'a loop (range)')
      }
      case 'go': return refuse(s, 'a goroutine (its steps interleave with others)')
      case 'select': case 'send': return refuse(s, 'a channel')
      case 'typeswitch': return refuse(s, 'a type switch (interfaces are outside the subset)')
      case 'labeled': return refuse(s, 'a label')
    }
    return refuse(s, `a statement the subset doesn't read (${s.s})`)
  }
  joinFlows(fs: (Flow | undefined)[], at: {p: string}): Flow {
    const lives = fs.flatMap(f => (f?.live ? [f.live] : []))
    const live = this.join(lives, at)
    return {...(live ? {live} : {}), rets: fs.flatMap(f => f?.rets ?? []), brk: fs.flatMap(f => f?.brk ?? [])}
  }
  switchStmt(s: GS, p: Path): Flow {
    let q = p
    if (s.init) { const f = this.stmt(s.init, q); if (!f.live) return f; q = f.live }
    let tag: GV | undefined
    if (s.tag) { const [v, q2] = this.ev(s.tag, q); tag = v; q = q2 }
    // Each case's condition (none before it matched), the default's (none matched), evaluated in order.
    const conds: B[] = []
    let none: B = I.T
    for (const c of s.cases!) {
      if (c.default) { conds.push(I.F); continue }
      let any: B = I.F
      for (const e of c.list!) {
        const [v, q2] = this.ev(e, q)
        q = q2
        const m = tag ? this.equal(tag, v, e, q) : v.t === 'bool' ? v.e : refuse(e, 'a case that isn\'t a condition')
        any = I.or(any, m)
      }
      conds.push(I.and(none, any))
      none = I.and(none, I.not(any))
    }
    const di = s.cases!.findIndex(c => c.default)
    if (di >= 0) conds[di] = none
    const flows: Flow[] = []
    let carried: Path | undefined
    s.cases!.forEach((c, i) => {
      const entry = conds[i]!.op === 'const' && !(conds[i] as {v: boolean}).v ? undefined : this.assume(q, conds[i]!)
      const into = this.join([...(entry ? [entry] : []), ...(carried ? [carried] : [])], c)
      carried = undefined
      if (!into) return
      const f = this.block(c.b, into)
      flows.push({...(f.live ? {live: f.live} : {}), rets: f.rets, brk: []}, {rets: [], brk: [], ...(f.brk.length ? {live: this.join(f.brk, c)!} : {})})
      if (f.ft) { if (i === s.cases!.length - 1) refuse(c, 'fallthrough out of the last case'); carried = f.ft }
    })
    if (di < 0) flows.push({live: this.assume(q, none), rets: [], brk: []})
    return this.joinFlows(flows, s)
  }
  ret(s: GS, p: Path): Flow {
    const fn = this.frames.at(-1)!
    let vs: GV[] = [], q = p
    if (s.r!.length === 1 && fn.results.length > 1) {
      const [v, q2] = this.ev(s.r![0]!, q)
      if (v.t !== 'tuple') return refuse(s, 'a return of one value from a function of several')
      vs = v.xs; q = q2
    } else if (!s.r!.length && fn.results.length) {
      // A bare return: the named results.
      for (const r of fn.results) { const v = q.locals.get(r.id!) ?? refuse(s, 'a bare return of an unnamed result'); vs.push(v) }
    } else {
      s.r!.forEach((e, i) => { const [v, q2] = this.ev(e, q); vs.push(this.convertTo(v, fn.results[i]!.t, e)); q = q2 })
    }
    return {rets: [{p: q, vs}], brk: []}
  }
  frames: GoFunc[] = []
  assign(s: GS, p: Path): Path {
    const l = s.l!, r = s.r!, op = s.op!
    if (op === '=' || op === ':=') {
      // v, ok := m[k]: the value and whether the map holds the key.
      if (l.length === 2 && r.length === 1 && r[0]!.e === 'index' && this.T(r[0]!.x!.t).k === 'map') {
        const [m, q] = this.ev(r[0]!.x!, p), [k, q2] = this.ev(r[0]!.i!, q)
        const cell = this.mapRead(m, k, r[0]!, q2)
        return this.assignTo(l, [cell.v, {t: 'bool', e: cell.has}], s, op, q2)
      }
      let vals: GV[] = [], q = p
      // Go evaluates the left side's indices and indirections, then the right side, then assigns: the subset reads
      // left sides without effects, so the right side first is the same.
      if (r.length === 1 && l.length > 1) {
        const [v, q2] = this.ev(r[0]!, q)
        if (v.t !== 'tuple' || v.xs.length !== l.length) return refuse(s, 'an assignment of several from one value')
        vals = v.xs; q = q2
      } else r.forEach((e, i) => { const [v, q2] = this.ev(e, q, l[i]); vals.push(this.convertTo(v, l[i]!.t, e)); q = q2 })
      return this.assignTo(l, vals, s, op, q)
    }
    // x op= y
    const bop = op.slice(0, -1)
    if (l[0]!.e === 'index' && this.T(l[0]!.x!.t).k === 'map') {
      const [m, q] = this.ev(l[0]!.x!, p), [k, q2] = this.ev(l[0]!.i!, q), cell = this.mapRead(m, k, l[0]!, q2), [y, q3] = this.ev(r[0]!, q2)
      return this.mapWrite(m, k, this.binop(bop, cell.v, y, s, q3), l[0]!, q3)
    }
    if (l[0]!.e === 'index') return refuse(s, `${op} on a slice's item (the subset sets an item: s[i] = x)`)
    const [pl, q] = this.place(l[0]!, p), [x, q2] = this.readPlace(pl, s, q), [y, q3] = this.ev(r[0]!, q2)
    return this.write(pl, this.binop(bop, x, y, s, q3), s, q3)
  }
  assignTo(l: GX[], vals: GV[], s: GS, op: string, p: Path): Path {
    let q = p
    l.forEach((x, i) => {
      const v = vals[i]!
      if (op === ':=' && x.e === 'id' && x.n !== '_' && !q.locals.has(x.id!)) { q = this.bind(x.id!, v, x, q); return }
      if (x.e === 'index') {
        const xt = this.T(x.x!.t)
        if (xt.k === 'map') { const [m, q2] = this.ev(x.x!, q), [k, q3] = this.ev(x.i!, q2); q = this.mapWrite(m, k, v, x, q3); return }
        if (xt.k === 'slice') { const [sv, q2] = this.ev(x.x!, q), [k, q3] = this.ev(x.i!, q2); q = this.listSet(sv, k, v, x, q3); return }
        return refuse(x, 'an index into other than a map or a slice')
      }
      // s = append(s, x) and s = s[:len(s)-1]: the list's push and pop, in its own place.
      if (v.t === 'list' || v.t === 'push' || v.t === 'pop') { q = this.listAssign(x, v, q); return }
      if (v.t === 'map') { q = this.mapAssign(x, v, q); return }
      const [pl, q2] = this.place(x, q)
      q = this.write(pl, v, x, q2)
    })
    return q
  }
  bind(id: string, v: GV, at: {p: string}, p: Path): Path {
    if (v.t === 'list' || v.t === 'map' || v.t === 'push' || v.t === 'pop') this.secondName(v.t === 'push' || v.t === 'pop' ? {t: 'list', id: v.id} : v, at, p, {k: 'local'})
    if (v.t === 'num' && v.slen) refuse(at, 'len of a string kept (it is read only against 0)')
    return {...p, locals: new Map(p.locals).set(id, v)}
  }
  readPlace(pl: {k: 'local', id: string, path: string[]} | {k: 'heap', ptr: GV, path: string[]} | {k: 'blank'}, at: {p: string}, p: Path): [GV, Path] {
    if (pl.k === 'blank') return refuse(at, '_ read')
    return this.read(pl, at, p)
  }
  lockKey(x: GX, p: Path): string {
    const [pl] = this.place(x, p)
    if (pl.k === 'local') return `local:${pl.id}.${pl.path.join('.')}`
    if (pl.k === 'heap' && pl.ptr.t === 'ptr' && pl.ptr.to.k === 'obj') return `${pl.ptr.to.id}.${[...pl.ptr.to.path, ...pl.path].join('.')}`
    return refuse(x, 'a mutex not of the object')
  }

  // --- expressions ----------------------------------------------------------------------------------------------------
  constOf(x: GX): GV | undefined {
    const c = x.c
    if (!c) return undefined
    if (c.int !== undefined) {
      const ty = this.intTy(x.t)
      if (!ty) {
        if (this.T(x.t).k === 'float') return refuse(x, `${x.text}: a float constant (the subset reads integers)`)
        return refuse(x, `${x.text}: an integer constant of type ${this.tname(x.t)}`)
      }
      const v = Number(c.int)
      if (!Number.isSafeInteger(v)) return refuse(x, `${x.text}: the constant ${c.int} is past 2^53 (the rule's numbers stop there)`)
      return {t: 'num', e: I.num(v), ty}
    }
    if (c.bool !== undefined) return {t: 'bool', e: c.bool ? I.T : I.F}
    if (c.str !== undefined) return {t: 'str', e: {op: 'slit', value: c.str}}
    if (c.float !== undefined) return refuse(x, `${x.text}: a float constant (the subset reads integers)`)
    return refuse(x, `${x.text}: a constant the subset doesn't read`)
  }
  ev(x: GX, p: Path, _target?: GX): [GV, Path] {
    const k = this.constOf(x)
    if (k) return [k, p]
    switch (x.e) {
      case 'id': {
        if (x.o === 'nil') return [{t: 'nil'}, p]
        if (x.o === 'var') {
          if (x.id?.startsWith('pkg:')) return this.pkgVar(x, p)
          const v = p.locals.get(x.id!)
          if (!v) return refuse(x, `${x.n}: a variable the step doesn't set before reading`)
          return [v, p]
        }
        return refuse(x, `${x.text}: a ${x.o} used as a value`)
      }
      case 'sel': {
        if (x.k === 'field') {
          const [pl, q] = this.place(x, p)
          if (pl.k === 'blank') return refuse(x, '_')
          const [v, q2] = this.read(pl, x, q)
          if (v.t === 'opaque') return refuse(x, v.why)
          return [v, q2]
        }
        if (x.k === 'qual') {
          if (x.pkg === 'math' && /^(Max|Min)(Int|Uint)\d*$/.test(x.n!)) return refuse(x, `${x.text}: a constant past 2^53`)
          return refuse(x, `${x.text}: ${x.pkg && !this.stdlib(x.pkg) ? "another module's" : 'a package-level'} ${x.o === 'var' ? 'variable' : 'value'} the subset doesn't read`)
        }
        return refuse(x, `${x.text}: a method used as a value`)
      }
      case 'paren': return this.ev(x.x!, p)
      case 'call': return this.call(x, p)
      case 'bin': return this.binary(x, p)
      case 'un': return this.unary(x, p)
      case 'star': { const [v, q] = this.ev(x.x!, p); return this.deref(v, [], x, q) }
      case 'comp': return this.composite(x, p)
      case 'index': {
        const xt = this.T(x.x!.t)
        const [b, q] = this.ev(x.x!, p), [i, q2] = this.ev(x.i!, q)
        if (xt.k === 'map') return [this.mapRead(b, i, x, q2).v, q2]
        if (xt.k === 'slice') return this.listGet(b, i, x, q2)
        return refuse(x, `${x.text}: an index into a ${this.tname(x.x!.t)}`)
      }
      case 'slice': {
        // s[:len(s)-1] of a slice of the state: its last item taken off (put back in s's own place).
        const [s, q] = this.ev(x.x!, p)
        const h = x.hi
        const isLenMinus1 = !x.lo && !x.three && h?.e === 'bin' && h.op === '-' && h.y?.c?.int === '1' && h.x?.e === 'call' && h.x.builtin === 'len' && h.x.a?.[0]?.text === x.x!.text
        if (s.t === 'list' && isLenMinus1) {
          const len = this.listLen(s, x, q)
          this.refuseWhere(q, I.cmp('<', len, I.num(1)), x, 'a slice out of range (a panic: s[:len(s)-1] of an empty s)')
          return [{t: 'pop', id: s.id}, this.assume(q, I.cmp('<=', I.num(1), len))]
        }
        return refuse(x, `${x.text}: a slice of a slice (it shares the backing array: a write through either is seen by both, and append writes into it or not by its capacity)`)
      }
      case 'funclit': return refuse(x, 'a closure')
      case 'assert': return refuse(x, 'a type assertion (interfaces are outside the subset)')
      case 'inst': return refuse(x, 'a generic function')
      case 'lit': return refuse(x, `${x.text}: a literal of type ${this.tname(x.t)}`)
    }
    return refuse(x, `${x.text}: an expression the subset doesn't read (${x.e})`)
  }
  stdlib(path: string): boolean { return !path.split('/')[0]!.includes('.') }
  pkgVar(x: GX, p: Path): [GV, Path] {
    const v = this.pkg.vars.find(y => `pkg:${y.name}` === x.id)
    if (v && this.T(v.t).k === 'error' && v.init?.e === 'call' && v.init.f?.e === 'sel' && ((v.init.f.pkg === 'errors' && v.init.f.n === 'New') || (v.init.f.pkg === 'fmt' && v.init.f.n === 'Errorf'))) {
      this.notes.add(`${x.n}: an error the package makes once (errors.New): read as an error that isn't nil`)
      return [{t: 'err', is: I.T}, p]
    }
    return refuse(x, `${x.n}: a package variable (state every object shares)`)
  }
  num(v: GV, at: {p: string}): N {
    if (v.t !== 'num') return refuse(at, `${(at as GX).text ?? ''}: a ${v.t} where a number is read`)
    if (v.slen) return refuse(at, 'len of a string read other than against 0 (strings are set and compared in the subset)')
    return v.e
  }
  bool(v: GV, at: {p: string}): B { if (v.t !== 'bool') return refuse(at, `${(at as GX).text ?? ''}: a ${v.t} where a condition is read`); return v.e }
  binary(x: GX, p: Path): [GV, Path] {
    const op = x.op!
    if (op === '&&' || op === '||') {
      const [a, q] = this.ev(x.x!, p), ab = this.bool(a, x.x!)
      // The right side runs only where the left doesn't decide: its panics and effects only there.
      const [b, q2] = this.ev(x.y!, this.assume(q, op === '&&' ? ab : I.not(ab)))
      const bb = this.bool(b, x.y!)
      const back = {...q2, pc: q.pc}
      return [{t: 'bool', e: op === '&&' ? I.and(ab, bb) : I.or(ab, bb)}, this.heapOnly(q, back, op === '&&' ? ab : I.not(ab), x)]
    }
    const [a, q] = this.ev(x.x!, p), [b, q2] = this.ev(x.y!, q)
    return [this.binop(op, a, b, x, q2), q2]
  }
  // After a side that ran under c: its writes where c holds.
  heapOnly(before: Path, after: Path, c: B, at: {p: string}): Path {
    if (after.heap === before.heap) return before
    return this.merge({...after, pc: [...before.pc, c]}, before, at)
  }
  binop(op: string, a: GV, b: GV, x: {p: string}, p: Path): GV {
    if (['==', '!='].includes(op)) { const e = this.equal(a, b, x, p); return {t: 'bool', e: op === '==' ? e : I.not(e)} }
    // len(s) of a string against 0: whether it is empty.
    const sl = (v: GV, k: GV) => (v.t === 'num' && v.slen && k.t === 'num' && !k.slen && k.e.op === 'const' && k.e.v === 0 ? v.slen : undefined)
    if (['==', '!=', '<', '<=', '>', '>='].includes(op) && (sl(a, b) || sl(b, a))) {
      const s = (sl(a, b) ?? sl(b, a))!, empty = I.keq(s, {op: 'slit', value: ''}), o = sl(a, b) ? op : ({'<': '>', '<=': '>=', '>': '<', '>=': '<='} as Record<string, string>)[op] ?? op
      // len(s) op 0, len(s) at least 0.
      return {t: 'bool', e: o === '==' || o === '<=' ? empty : o === '!=' || o === '>' ? I.not(empty) : o === '>=' ? I.T : I.F}
    }
    if (['<', '<=', '>', '>='].includes(op)) {
      if (a.t === 'str' || b.t === 'str') return refuse(x, 'strings ordered (strings are set and compared in the subset)')
      // x.Cmp(y) against 0, read as the comparison of x and y.
      const cmpOf = (v: GV, k: GV): [N, N] | undefined => (v.t === 'num' && v.cmp && k.t === 'num' && k.e.op === 'const' && k.e.v === 0 ? v.cmp : undefined)
      const ca = cmpOf(a, b), cb = cmpOf(b, a)
      let l: N, r: N
      let o = op
      if (ca) [l, r] = ca
      else if (cb) { [l, r] = cb; o = op === '<' ? '>' : op === '<=' ? '>=' : op === '>' ? '<' : '<=' }
      else { l = this.num(a, x); r = this.num(b, x) }
      return {t: 'bool', e: o === '<' ? I.cmp('<', l, r) : o === '<=' ? I.cmp('<=', l, r) : o === '>' ? I.cmp('<', r, l) : I.cmp('<=', r, l)}
    }
    if (['+', '-', '*', '/', '%', '<<', '>>'].includes(op)) {
      if (a.t === 'str') return refuse(x, 'strings joined (strings are set and compared in the subset)')
      return this.arith(op, a, b, x, p)
    }
    return refuse(x, `${op}: a bit operation (outside the subset)`)
  }
  equal(a: GV, b: GV, x: {p: string}, p?: Path): B {
    // A map of the state against nil: whether it is nil.
    if (a.t === 'map' && b.t === 'nil' && p) return this.mapObj(a, x as GX, p).nil
    if (a.t === 'nil' && b.t === 'map' && p) return this.mapObj(b, x as GX, p).nil
    if (a.t === 'num' && b.t === 'num') return I.cmp('=', this.num(a, x), this.num(b, x))
    if (a.t === 'bool' && b.t === 'bool') return I.or(I.and(a.e, b.e), I.and(I.not(a.e), I.not(b.e)))
    if (a.t === 'str' && b.t === 'str') return I.keq(a.e, b.e)
    if (a.t === 'err' && b.t === 'nil') return I.not(a.is)
    if (a.t === 'nil' && b.t === 'err') return I.not(b.is)
    if (a.t === 'err' && b.t === 'err') return refuse(x, 'two errors compared (an error is nil or not in the subset)')
    if ((a.t === 'ptr' || a.t === 'nil') && (b.t === 'ptr' || b.t === 'nil')) {
      if (a.t === 'nil' && b.t === 'nil') return I.T
      if (b.t === 'nil') return this.cases((a as {to: Ptr}).to).nil
      if (a.t === 'nil') return this.cases((b as {to: Ptr}).to).nil
      // Two pointers: the same object (and place), or both nil.
      const ca = this.cases((a as {to: Ptr}).to), cb = this.cases((b as {to: Ptr}).to)
      const same = ca.objs.flatMap(o => cb.objs.filter(q => q.id === o.id && q.path.join() === o.path.join()).map(q => I.and(o.c, q.c)))
      return I.or(I.and(ca.nil, cb.nil), ...same)
    }
    if ((a.t === 'list' || a.t === 'map') && b.t === 'nil') return refuse(x, `a ${a.t === 'list' ? 'slice' : 'map'} compared with nil (nil and empty are one ${a.t === 'list' ? 'list' : 'map'} in the subset)`)
    return refuse(x, `a ${a.t} compared with a ${b.t}`)
  }
  // Integer arithmetic at the type's width: the exact result, wrapped as Go wraps it (or refused, below).
  arith(op: string, a: GV, b: GV, x: {p: string}, p: Path): GV {
    if (a.t !== 'num' || b.t !== 'num') return refuse(x, `${op} of a ${a.t} and a ${b.t}`)
    this.num(a, x); this.num(b, x)
    const ty = a.ty.t >= 0 ? a.ty : b.ty
    let e: N
    switch (op) {
      case '+': e = I.add(a.e, b.e); break
      case '-': e = I.sub(a.e, b.e); break
      case '*': e = I.mul(a.e, b.e); break
      case '/': case '%': {
        if (b.e.op !== 'const') return refuse(x, `${op} by other than a constant`)
        if (b.e.v === 0) { this.refuseWhere(p, I.T, x, 'a division by zero'); return {t: 'num', e: I.num(0), ty} }
        const k = Math.abs(b.e.v), neg = b.e.v < 0
        // Go's quotient truncates toward zero (its remainder takes the dividend's sign).
        const nonneg = this.bounds(a.e)[0] >= 0
        const q = nonneg ? I.divk(k, a.e) : I.nite(I.cmp('<=', I.num(0), a.e), I.divk(k, a.e), I.neg(I.divk(k, I.neg(a.e))))
        // (0 − r, not −r: the printer's remainder is a natural's, which Int subtracts from)
        const r = nonneg ? I.modk(k, a.e) : I.nite(I.cmp('<=', I.num(0), a.e), I.modk(k, a.e), I.sub(I.num(0), I.modk(k, I.neg(a.e))))
        e = op === '/' ? (neg ? I.neg(q) : q) : r
        break
      }
      case '>>': {
        if (b.e.op !== 'const' || b.e.v < 0) return refuse(x, '>> by other than a constant')
        if (b.e.v >= 53) return refuse(x, `>> ${b.e.v} (past the rule's 2^53)`)
        e = I.divk(TWO(b.e.v), a.e); break
      }
      case '<<': {
        if (b.e.op !== 'const' || b.e.v < 0) return refuse(x, '<< by other than a constant')
        if (b.e.v >= 53) return refuse(x, `<< ${b.e.v} (past the rule's 2^53)`)
        e = I.mulk(TWO(b.e.v), a.e); break
      }
      default: return refuse(x, `${op}: outside the subset`)
    }
    return {t: 'num', e: this.wrap(e, ty, x, p), ty}
  }
  // The bounds a term's value is within, from its variables' types (a cell's too) and its constants.
  bounds(e: N): [number, number] {
    const r = (lo: number, hi: number): [number, number] => [lo, hi]
    switch (e.op) {
      case 'const': return r(e.v, e.v)
      case 'var': return this.ranges.get(e.name) ?? r(-Infinity, Infinity)
      case 'cell': return this.ranges.get(`${e.map}.${e.field}`) ?? r(-Infinity, Infinity)
      case 'add': { const a = this.bounds(e.a), b = this.bounds(e.b); return r(a[0] + b[0], a[1] + b[1]) }
      case 'sub': { const a = this.bounds(e.a), b = this.bounds(e.b); return r(a[0] - b[1], a[1] - b[0]) }
      case 'neg': { const a = this.bounds(e.a); return r(-a[1], -a[0]) }
      case 'mulk': { const a = this.bounds(e.a); return e.k >= 0 ? r(e.k * a[0], e.k * a[1]) : r(e.k * a[1], e.k * a[0]) }
      case 'mul': { const a = this.bounds(e.a), b = this.bounds(e.b), xs = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]].map(v => (Number.isNaN(v) ? 0 : v)); return r(Math.min(...xs), Math.max(...xs)) }
      case 'min': { const a = this.bounds(e.a), b = this.bounds(e.b); return r(Math.min(a[0], b[0]), Math.min(a[1], b[1])) }
      case 'max': { const a = this.bounds(e.a), b = this.bounds(e.b); return r(Math.max(a[0], b[0]), Math.max(a[1], b[1])) }
      case 'divk': { const a = this.bounds(e.a); return r(Math.floor(a[0] / e.k), Math.floor(a[1] / e.k)) }
      case 'modk': return r(0, e.k - 1)
      case 'ite': { const a = this.bounds(e.a), b = this.bounds(e.b); return r(Math.min(a[0], b[0]), Math.max(a[1], b[1])) }
    }
  }
  wrap(e: N, ty: IntTy, x: {p: string}, p: Path): N {
    if (ty.bits === 0) return e
    const [lo, hi] = this.range(ty), [blo0, bhi0] = this.bounds(e)
    if (blo0 >= lo && bhi0 <= hi) return e
    // Under the path's conditions (the linear arithmetic core/extract-print.ts proves naturals with): a bound that holds
    // there needs no wrap.
    const blo = blo0 >= lo || this.within(e, lo, 'lo', p) ? Math.max(blo0, lo) : blo0, bhi = bhi0 <= hi || this.within(e, hi, 'hi', p) ? Math.min(bhi0, hi) : bhi0
    if (blo >= lo && bhi <= hi) return e
    if (ty.bits >= 64) {
      // A uint64 below 0 wraps to 2^64 − x in Go, past the rule's numbers: refused. Past 2^53 above, the rule's
      // runtime refuses.
      if (!ty.signed && blo < 0) { this.refuseWhere(p, I.cmp('<', e, I.num(0)), x, `a ${this.tname(ty.t)} below 0 (Go wraps it to 2^64 − x, past the rule's numbers)`, false); this.notes.add(`${this.tname(ty.t)}: a result below 0 is refused (Go would wrap it past 2^53)`) }
      return e
    }
    // At 32 bits and fewer: modulo 2^n into the range, by cases on how many times it passed (as Go wraps).
    const m = TWO(ty.bits), k0 = Math.floor((blo - lo) / m), k1 = Math.floor((bhi - lo) / m)
    this.notes.add(`${this.tname(ty.t)}: a result past its range wraps modulo 2^${ty.bits}, as Go's does`)
    if (Number.isFinite(k0) && Number.isFinite(k1) && k1 - k0 <= 3) {
      // By cases from the bottom: e at least lo + k·2^n takes e − k·2^n.
      const less = (k: number): N => (k >= 0 ? I.sub(e, I.num(k * m)) : I.add(e, I.num(-k * m)))
      let acc: N = less(k0)
      for (let k = k0 + 1; k <= k1; k++) acc = I.nite(I.cmp('<=', I.num(lo + k * m), e), less(k), acc)
      return acc
    }
    // Many times over (a conversion from a wider type, a product): e − 2^n·⌊(e − lo)/2^n⌋, the value of the range
    // e is congruent to (a floor division, as the rule's divBy is).
    return I.sub(e, I.mulk(m, I.divk(m, I.add(e, I.num(-lo)))))
  }
  // Whether e is at least lo (or at most hi) on the path: its conditions and its variables' ranges as facts.
  within(e: N, b: number, side: 'lo' | 'hi', p: Path): boolean {
    if (!Number.isFinite(b)) return false
    const facts: B[] = [...p.pc]
    for (const n of I.varsOf(e).vars) { const r = this.ranges.get(n); if (r) { if (Number.isFinite(r[0])) facts.push(I.cmp('<=', I.num(r[0]), I.nvar(n))); if (Number.isFinite(r[1])) facts.push(I.cmp('<=', I.nvar(n), I.num(r[1]))) } }
    const ctx = {m: {refuse: I.F, pre: I.T} as Model, sorts: new Map<string, 'nat' | 'int'>(), atoms: facts}
    return nonneg(side === 'lo' ? I.sub(e, I.num(b)) : I.sub(I.num(b), e), ctx)
  }
  unary(x: GX, p: Path): [GV, Path] {
    if (x.op === '&') {
      const y = x.x!
      if (y.e === 'comp') { const [v, q] = this.composite(y, p); return this.alloc(v, y.t, q) }
      const [pl, q] = this.place(y, p)
      if (pl.k === 'heap' && pl.ptr.t === 'ptr') {
        const cs = this.cases(pl.ptr.to)
        this.refuseWhere(q, cs.nil, x, 'a nil dereference')
        return [{t: 'ptr', to: this.shift(pl.ptr.to, pl.path), elem: y.t}, this.assume(q, I.not(cs.nil))]
      }
      return refuse(x, `&${y.text}: a pointer to a local (the subset's pointers are to the state's objects and to new ones)`)
    }
    const [a, q] = this.ev(x.x!, p)
    if (x.op === '!') return [{t: 'bool', e: I.not(this.bool(a, x))}, q]
    if (x.op === '-') { if (a.t !== 'num') return refuse(x, `- of a ${a.t}`); return [{t: 'num', e: this.wrap(I.neg(a.e), a.ty, x, q), ty: a.ty}, q] }
    if (x.op === '+') return [a, q]
    return refuse(x, `${x.op}: ${x.op === '^' ? 'a bit operation' : 'outside the subset'}`)
  }
  shift(p: Ptr, path: string[]): Ptr {
    if (p.k === 'nil') return p
    if (p.k === 'obj') return {...p, path: [...p.path, ...path]}
    return {...p, a: this.shift(p.a, path), b: this.shift(p.b, path)}
  }
  alloc(v: GV, t: number, p: Path): [GV, Path] {
    const id = `new:${++this.fresh}`
    if (v.t !== 'struct') return refuse({p: ''}, 'new of other than a struct')
    return [{t: 'ptr', to: {k: 'obj', id, path: []}, elem: t}, {...p, heap: new Map(p.heap).set(id, {k: 'struct', ty: t, f: new Map(v.f), origin: 'fresh'})}]
  }
  composite(x: GX, p: Path): [GV, Path] {
    const tt = this.T(x.t)
    if (tt.k === 'struct') {
      let q = p
      const [z, q0] = this.zero(x.t, x, q)
      q = q0
      const f = new Map((z as {f: Map<string, GV>}).f)
      ;(x.elts ?? []).forEach((el, i) => {
        const name = el.field ?? tt.fields?.[i]?.name ?? refuse(x, 'a struct literal with more values than fields')
        const ft = tt.fields!.find(g => g.name === name)!
        const [v, q2] = this.ev(el.v, q)
        q = q2
        f.set(name, this.convertTo(v, ft.t, el.v))
      })
      return [{t: 'struct', ty: x.t, f}, q]
    }
    if ((tt.k === 'map' || tt.k === 'slice') && !(x.elts ?? []).length) return [{t: tt.k === 'map' ? 'map' : 'list', id: tt.k === 'map' ? 'new-map' : 'new-list'} as GV, p]
    return refuse(x, `${x.text}: a literal of a ${this.tname(x.t)} (the subset makes structs, and maps and slices empty)`)
  }
  // Go's zero value of a type.
  zero(t: number, at: {p: string}, p: Path): [GV, Path] {
    const tt = this.T(t)
    if (tt.k === 'int') return [{t: 'num', e: I.num(0), ty: this.intTy(t)!}, p]
    if (tt.k === 'bool') return [{t: 'bool', e: I.F}, p]
    if (tt.k === 'string') return [{t: 'str', e: {op: 'slit', value: ''}}, p]
    if (tt.k === 'ptr') return [{t: 'ptr', to: {k: 'nil'}, elem: tt.elem!}, p]
    if (tt.k === 'error') return [{t: 'err', is: I.F}, p]
    if (tt.k === 'struct') {
      const f = new Map<string, GV>()
      let q = p
      for (const g of tt.fields ?? []) {
        const s = this.scalar(g.t)
        if (typeof s === 'string' && !['ptr', 'struct', 'error'].includes(this.T(g.t).k)) { f.set(g.name, {t: 'opaque', why: `${g.name}: ${s}`, ty: g.t}); continue }
        const [v, q2] = this.zero(g.t, at, q); q = q2; f.set(g.name, v)
      }
      return [{t: 'struct', ty: t, f}, q]
    }
    return [{t: 'opaque', why: `a value of type ${this.tname(t)} (outside the subset)`, ty: t}, p]
  }
  // A value as the type it is assigned to: an untyped constant takes the type; an integer stays itself.
  convertTo(v: GV, t: number, _at: GX): GV {
    if (v.t === 'num') { const ty = this.intTy(t); if (ty) return {...v, ty} }
    if (v.t === 'nil') {
      const tt = this.T(t)
      if (tt.k === 'ptr') return {t: 'ptr', to: {k: 'nil'}, elem: tt.elem!}
      if (tt.k === 'error') return {t: 'err', is: I.F}
    }
    return v
  }

  // --- calls ----------------------------------------------------------------------------------------------------------
  args(xs: GX[], p: Path): [GV[], Path] {
    const out: GV[] = []
    let q = p
    for (const a of xs) { const [v, q2] = this.ev(a, q); out.push(v); q = q2 }
    return [out, q]
  }
  call(x: GX, p: Path): [GV, Path] {
    const f = x.f!
    if (x.conv) {
      const [v, q] = this.ev(x.a![0]!, p), ty = this.intTy(x.t)
      if (ty && v.t === 'num') return [{t: 'num', e: this.wrap(v.e, ty, x, q), ty}, q]
      return refuse(x, `${x.text}: a conversion to ${this.tname(x.t)} (the subset converts between integer types)`)
    }
    if (x.builtin) return this.builtin(x, p)
    if (f.e === 'sel' && f.k === 'qual') return this.stdCall(x, p)
    if (f.e === 'sel' && f.k === 'method') {
      // A method promoted from an embedded field: its receiver is that field (through the embedded fields on the way).
      let q = p, emb: Place | undefined, rt = this.T(f.x!.t), base = rt.k === 'ptr' ? rt.elem! : f.x!.t
      if ((f.path ?? []).length > 1) {
        let cur: Place
        if (rt.k === 'ptr') { const [v, q2] = this.ev(f.x!, q); q = q2; cur = {k: 'heap', ptr: v, path: []} } else { const [pl0, q2] = this.place(f.x!, q); q = q2; if (pl0.k === 'blank') return refuse(x, '_'); cur = pl0 }
        let t = this.T(base)
        for (const i of f.path!.slice(0, -1)) {
          const fd = t.fields?.[i] ?? refuse(x, `${x.text}: an embedded field the type doesn't list`)
          cur = {...cur, path: [...cur.path, fd.name]}
          base = fd.t; t = this.T(fd.t)
          if (t.k === 'ptr') { const [v, q2] = this.read(cur, x, q); q = q2; cur = {k: 'heap', ptr: v, path: []}; base = t.elem!; t = this.T(t.elem!) }
        }
        emb = cur; rt = this.T(base)
      }
      if (this.isBig(base)) { if (emb) return refuse(x, 'a big.Int method promoted from an embedded field'); return this.bigCall(x, p) }
      if (this.isMutex(base)) { if (emb) return refuse(x, `${x.text}: a mutex's method promoted from an embedded field (lock it by its field's name)`); return this.mutexCall(x, p) }
      if (f.mpkg && f.mpkg !== this.pkg.package) return refuse(x, `${x.text}: a method of ${f.mpkg} (another package's code)`)
      const decl = this.methodOf(f.mtype!, f.n!) ?? refuse(x, `${x.text}: no method ${f.mtype}.${f.n} declared with a body`)
      // The receiver: a pointer to the value (its place's address) or a copy of it.
      let recv: GV
      if (emb) {
        if (f.mptr) {
          if (emb.k !== 'heap' || emb.ptr.t !== 'ptr') return refuse(x, `${x.text}: a pointer method of a local value's embedded field (a pointer to a local)`)
          const cs = this.cases(emb.ptr.to)
          this.refuseWhere(q, cs.nil, x, 'a nil dereference'); q = this.assume(q, I.not(cs.nil))
          recv = {t: 'ptr', to: this.shift(emb.ptr.to, emb.path), elem: base}
        } else { const [v, q2] = this.read(emb, x, q); recv = v; q = q2 }
      } else if (f.mptr) {
        if (rt.k === 'ptr') { const [v, q2] = this.ev(f.x!, q); recv = v; q = q2 }
        else {
          const [pl, q2] = this.place(f.x!, q)
          q = q2
          if (pl.k === 'heap' && pl.ptr.t === 'ptr') { const cs = this.cases(pl.ptr.to); this.refuseWhere(q, cs.nil, x, 'a nil dereference'); q = this.assume(q, I.not(cs.nil)); recv = {t: 'ptr', to: this.shift(pl.ptr.to, pl.path), elem: base} }
          else return refuse(x, `${f.x!.text}.${f.n}(): a pointer method of a local value (its address is a pointer to a local)`)
        }
      } else {
        const [v, q2] = this.ev(f.x!, q)
        q = q2
        if (v.t === 'ptr') { const [d, q3] = this.deref(v, [], x, q); recv = d; q = q3 } else recv = v
      }
      const [as, q3] = this.args(x.a ?? [], q)
      return this.inline(decl, recv, as, x, q3)
    }
    if (f.e === 'id' && f.o === 'func') {
      const decl = this.funcOf(f.n!) ?? refuse(x, `${f.n}: a function with no body here`)
      const [as, q] = this.args(x.a ?? [], p)
      return this.inline(decl, undefined, as, x, q)
    }
    return refuse(x, `${x.text}: a call of a function value`)
  }
  inline(fn: GoFunc, recv: GV | undefined, args: GV[], at: GX, p: Path): [GV, Path] {
    if (fn.generic) return refuse(at, `${fn.name}: a generic function`)
    const key = `${fn.recv?.type ?? ''}.${fn.name}`
    if (this.stack.includes(key)) return refuse(at, `${fn.name}: a recursive call`)
    if (!fn.body) return refuse(at, `${fn.name} has no body`)
    if (fn.params.some(x => x.variadic)) return refuse(at, `${fn.name}: a variadic function`)
    this.spans.set(key, [fn.p.split(':')[0]!, fn.span[0], fn.span[1]])
    let q: Path = {...p, locals: new Map(p.locals), defers: []}
    if (fn.recv?.id && recv) q = this.bind(fn.recv.id, recv, at, q)
    fn.params.forEach((pa, i) => { if (pa.id) q = this.bind(pa.id, this.convertTo(args[i]!, pa.t, at), at, q) })
    for (const r of fn.results) if (r.id) { const [z, q2] = this.zero(r.t, at, q); q = this.bind(r.id, z, at, q2) }
    this.stack.push(key); this.frames.push(fn)
    let flow: Flow
    try { flow = this.block(fn.body, q) } finally { this.stack.pop(); this.frames.pop() }
    if (flow.brk.length) refuse(at, `${fn.name}: a break outside a switch`)
    const rets = [...flow.rets, ...(flow.live ? [{p: flow.live, vs: []}] : [])]
    if (flow.live && fn.results.length) refuse(at, `${fn.name}: a path with no return`)
    if (!rets.length) return [{t: 'opaque', why: 'no return', ty: -1}, {...p, pc: [...p.pc, I.F]}]
    // Deferred unlocks at the return.
    const done = rets.map(r => ({...r, p: {...r.p, locks: r.p.locks.filter(k => !r.p.defers.includes(k)), defers: p.defers}}))
    // The results, each by the path that returned it (kept as locals the join merges).
    const joined = this.join(done.map(r => ({...r.p, locals: new Map([...r.p.locals, ...r.vs.map((v, i) => [`$ret${i}`, v] as const)])})), at)!
    const vals = fn.results.map((_, i) => joined.locals.get(`$ret${i}`)!)
    const locals = new Map(p.locals)
    return [vals.length === 1 ? vals[0]! : {t: 'tuple', xs: vals}, {...joined, locals, defers: p.defers}]
  }
  builtin(x: GX, p: Path): [GV, Path] {
    const b = x.builtin!, a = x.a ?? []
    switch (b) {
      case 'len': {
        const at = this.T(a[0]!.t)
        if (at.k === 'string') { const [s, q] = this.ev(a[0]!, p); if (s.t !== 'str') refuse(x, 'len of a non-string'); return [{t: 'num', e: I.num(0), ty: this.intTy(x.t)!, slen: (s as {e: K}).e}, q] }
        if (at.k === 'slice') { const [s, q] = this.ev(a[0]!, p); return [{t: 'num', e: this.listLen(s, x, q), ty: this.intTy(x.t)!}, q] }
        if (at.k === 'map') return refuse(x, 'len of a map (the subset keeps no count of a map\'s keys)')
        return refuse(x, `len of a ${this.tname(a[0]!.t)}`)
      }
      case 'append': {
        if (a.length !== 2 || x.ell) return refuse(x, 'append of other than one item')
        const [s, q] = this.ev(a[0]!, p), [v, q2] = this.ev(a[1]!, q)
        if (s.t !== 'list') return refuse(x, 'append to other than a slice of the state')
        if (v.t === 'num' && v.slen) return refuse(a[1]!, 'len of a string read other than against 0')
        return [{t: 'push', id: s.id, x: v}, q2]
      }
      case 'delete': {
        const [m, q] = this.ev(a[0]!, p), [k, q2] = this.ev(a[1]!, q)
        return [{t: 'tuple', xs: []}, this.mapDelete(m, k, x, q2)]
      }
      case 'make': {
        const tt = this.T(x.t)
        if (tt.k === 'map' && a.length <= 2) return [{t: 'map', id: 'new-map'}, p]
        if (tt.k === 'slice') return refuse(x, 'make of a slice (a list starts empty: nil, and grows by append)')
        return refuse(x, `make of a ${this.tname(x.t)}`)
      }
      case 'new': {
        const et = this.T(x.t).elem!
        if (this.isBig(et)) return this.newBig(I.num(0), x.t, p)
        const [z, q] = this.zero(et, x, p)
        return this.alloc(z, et, q)
      }
      case 'min': case 'max': {
        const [vs, q] = this.args(a, p)
        let e = this.num(vs[0]!, x)
        for (const v of vs.slice(1)) e = b === 'min' ? I.nmin(e, this.num(v, x)) : I.nmax(e, this.num(v, x))
        return [{t: 'num', e, ty: this.intTy(x.t) ?? refuse(x, `${b} of other than integers`)}, q]
      }
      case 'panic': { const [, q] = this.args(a, p); this.refuseWhere(q, I.T, x, 'a panic'); return [{t: 'tuple', xs: []}, {...q, pc: [...q.pc, I.F]}] }
      case 'recover': return refuse(x, 'recover (a panic is a refusal in the subset)')
      case 'cap': return refuse(x, 'cap (a slice\'s capacity decides whether append shares its backing array)')
      case 'copy': return refuse(x, 'copy (between two slices)')
      case 'clear': return refuse(x, 'clear (a map or a slice emptied whole)')
    }
    return refuse(x, `${b}: a builtin the subset doesn't read`)
  }
  stdCall(x: GX, p: Path): [GV, Path] {
    const f = x.f!, path = f.pkg ?? '', n = f.n!
    if ((path === 'errors' && n === 'New') || (path === 'fmt' && n === 'Errorf')) {
      // An error: not nil. Its arguments are evaluated (they may panic), its text is not compared.
      let q = p
      for (const a of x.a ?? []) {
        if (a.e === 'call' && a.f?.e === 'sel' && a.f.n === 'String' && a.f.k === 'method' && (this.isBigPtr(a.f.x!.t) || this.isBig(a.f.x!.t))) { const [, q2] = this.ev(a.f.x!, q); q = q2; continue }
        if (a.c) continue
        const [, q2] = this.ev(a, q); q = q2
      }
      return [{t: 'err', is: I.T}, q]
    }
    if (path === 'math/big' && n === 'NewInt') { const [v, q] = this.ev(x.a![0]!, p); return this.newBig(this.num(v, x), x.t, q) }
    if (path === 'time' && n === 'Now') return refuse(x, 'time.Now(): the clock (the check can\'t set it for the code, and time.Time is outside the subset)')
    if (!this.stdlib(path)) return refuse(x, `${x.text}: a function of ${path} (another module's code)`)
    if (!path) return refuse(x, `${x.text}: a call on a value whose type isn't read here (another module's, beyond the packages the code imports)`)
    return refuse(x, `${x.text}: a function of the standard library the subset doesn't read`)
  }
  newBig(v: N, t: number, p: Path): [GV, Path] {
    const id = `new:${++this.fresh}`
    return [{t: 'ptr', to: {k: 'obj', id, path: []}, elem: this.T(t).k === 'ptr' ? this.T(t).elem! : t}, {...p, heap: new Map(p.heap).set(id, {k: 'big', v, origin: 'fresh'})}]
  }
  // A big.Int's value through a pointer (by cases; nil panics).
  bigVal(v: GV, at: GX, p: Path): [N, Path] {
    if (v.t !== 'ptr') return refuse(at, `${at.text}: a big.Int read through a ${v.t}`)
    const cs = this.cases(v.to)
    this.refuseWhere(p, cs.nil, at, `a nil *big.Int (${at.text})`)
    const q = this.assume(p, I.not(cs.nil))
    let out: N | undefined
    for (const o of [...cs.objs].reverse()) {
      const obj = q.heap.get(o.id)
      if (obj?.k !== 'big' || o.path.length) return refuse(at, 'a big.Int pointer to other than a big.Int')
      out = out === undefined ? obj.v : I.nite(o.c, obj.v, out)
    }
    return [out ?? I.num(0), q]
  }
  bigCall(x: GX, p: Path): [GV, Path] {
    const f = x.f!, n = f.n!
    const [z, q0] = this.ev(f.x!, p)
    const [as, q1] = this.args(x.a ?? [], q0)
    const vals: N[] = []
    let q = q1
    const ints = (k: number) => { for (let i = 0; i < k; i++) { const a = as[i]!; if (a.t === 'num') vals.push(a.e); else { const [v, q2] = this.bigVal(a, x.a![i]!, q); vals.push(v); q = q2 } } }
    const set = (e: N): [GV, Path] => {
      // z = e, z the receiver (its object written where z points), and z returned.
      const [, q2] = this.bigVal(z, f.x!, q)
      const cs = this.cases((z as {to: Ptr}).to), heap = new Map(q2.heap)
      for (const o of cs.objs) { const obj = heap.get(o.id) as {k: 'big', v: N, origin: Origin}; heap.set(o.id, {...obj, v: I.nite(o.c, e, obj.v)}) }
      return [z, {...q2, heap}]
    }
    const zt = this.bigTy(x.t)
    switch (n) {
      case 'Add': ints(2); return set(I.add(vals[0]!, vals[1]!))
      case 'Sub': ints(2); return set(I.sub(vals[0]!, vals[1]!))
      case 'Mul': ints(2); return set(I.mul(vals[0]!, vals[1]!))
      case 'Neg': ints(1); return set(I.neg(vals[0]!))
      case 'Abs': ints(1); return set(I.nmax(vals[0]!, I.neg(vals[0]!)))
      case 'Set': ints(1); return set(vals[0]!)
      case 'SetInt64': case 'SetUint64': return set(this.num(as[0]!, x))
      case 'Cmp': case 'CmpAbs': {
        const [a, q2] = this.bigVal(z, f.x!, q); q = q2; ints(1)
        const l = n === 'Cmp' ? a : I.nmax(a, I.neg(a)), r = n === 'Cmp' ? vals[0]! : I.nmax(vals[0]!, I.neg(vals[0]!))
        return [{t: 'num', e: I.nite(I.cmp('<', l, r), I.num(-1), I.nite(I.cmp('=', l, r), I.num(0), I.num(1))), ty: {bits: 64, signed: true, t: x.t}, cmp: [l, r]}, q]
      }
      case 'Sign': { const [a, q2] = this.bigVal(z, f.x!, q); return [{t: 'num', e: I.nite(I.cmp('<', a, I.num(0)), I.num(-1), I.nite(I.cmp('=', a, I.num(0)), I.num(0), I.num(1))), ty: {bits: 64, signed: true, t: x.t}, cmp: [a, I.num(0)]}, q2] }
      case 'Int64': case 'Uint64': {
        const [a, q2] = this.bigVal(z, f.x!, q)
        if (n === 'Uint64') this.refuseWhere(q2, I.cmp('<', a, I.num(0)), x, 'Uint64 of a big.Int below 0 (undefined: Go returns its low bits)', false)
        return [{t: 'num', e: a, ty: {bits: 64, signed: n === 'Int64', t: x.t}}, q2]
      }
      case 'IsInt64': { const [, q2] = this.bigVal(z, f.x!, q); return [{t: 'bool', e: I.T}, q2] }
      case 'String': return refuse(x, 'a big.Int as a string (outside an error\'s text)')
    }
    void zt
    return refuse(x, `${x.text}: big.Int's ${n} (outside the subset)`)
  }
  mutexCall(x: GX, p: Path): [GV, Path] {
    const f = x.f!, n = f.n!, key = this.lockKey(f.x!, p)
    if (n === 'Lock' || n === 'RLock') {
      if (p.locks.includes(key)) refuse(x, `${x.text}: the mutex is locked again in the same step (a deadlock)`)
      return [{t: 'tuple', xs: []}, {...p, locks: [...p.locks, key]}]
    }
    if (n === 'Unlock' || n === 'RUnlock') {
      if (!p.locks.includes(key)) refuse(x, `${x.text}: an unlock of a mutex not locked (a panic)`)
      return [{t: 'tuple', xs: []}, {...p, locks: p.locks.filter(k => k !== key)}]
    }
    return refuse(x, `${x.text}: a mutex's ${n}`)
  }

  // --- maps ---------------------------------------------------------------------------------------------------------
  mapObj(m: GV, at: GX, p: Path): Extract<Obj, {k: 'map'}> {
    if (m.t !== 'map' || !p.heap.has(m.id)) return refuse(at, `${at.text}: a map other than the state's`)
    return p.heap.get(m.id) as Extract<Obj, {k: 'map'}>
  }
  key(k: GV, d: MapDecl, at: GX): K {
    if (d.key === 'num') { if (k.t !== 'num') refuse(at, 'a map key of the wrong kind'); return {op: 'num', e: (k as {e: N}).e} }
    if (k.t !== 'str') return refuse(at, 'a map key of the wrong kind')
    return k.e
  }
  cellAt(o: Extract<Obj, {k: 'map'}>, key: K): {has: B, vals: Map<string, GV>} {
    const base = this.baseCell(o.decl, key)
    // A nil map holds no key (the invariant the rule keeps beside it).
    if (!o.w) return base
    const c = I.keq(key, o.w.key)
    return {has: I.bite(c, o.w.has, base.has), vals: new Map([...base.vals].map(([f, v]) => [f, this.mergeV(c, o.w!.vals.get(f)!, v, {p: ''})]))}
  }
  mapRead(m: GV, k: GV, at: GX, p: Path): {v: GV, has: B} {
    const o = this.mapObj(m, at, p), key = this.key(k, o.decl, at), cell = this.cellAt(o, key)
    // Missing: the value type's zero.
    const zeroOf = (v: GV): GV => (v.t === 'num' ? {...v, e: I.num(0)} : v.t === 'bool' ? {t: 'bool', e: I.F} : v)
    const vt = this.T(this.T(at.x!.t).elem!)
    const vals = new Map([...cell.vals].map(([f, v]) => {
      const it = this.intTy(vt.k === 'struct' ? vt.fields!.find(g => g.name === f)!.t : this.T(at.x!.t).elem!)
      const typed: GV = v.t === 'num' && it ? {...v, ty: it} : v
      return [f, this.mergeV(cell.has, typed, zeroOf(typed), at)] as const
    }))
    const v: GV = o.decl.scalar ? vals.get('value')! : {t: 'struct', ty: this.T(at.x!.t).elem!, f: new Map(vals)}
    return {v, has: cell.has}
  }
  mapWrite(m: GV, k: GV, v: GV, at: GX, p: Path): Path {
    const o = this.mapObj(m, at, p), key = this.key(k, o.decl, at)
    if (o.origin !== 'state') return refuse(at, 'a write to a map other than the state\'s')
    this.refuseWhere(p, o.nil, at, 'a write to a nil map (a panic)')
    const q = this.assume(p, I.not(o.nil))
    if (o.w && !I.same(o.w.key, key)) return refuse(at, `writes ${o.decl.name} at a second key in one step`)
    const vals = new Map<string, GV>(o.decl.scalar ? [['value', v]] : o.decl.fields.map(f => [f.name, (v as {f: Map<string, GV>}).f?.get(f.name) ?? refuse(at, 'a map value of the wrong kind')]))
    return {...q, heap: new Map(q.heap).set(m.t === 'map' ? m.id : '', {...o, w: {key, has: I.T, vals}})}
  }
  mapDelete(m: GV, k: GV, at: GX, p: Path): Path {
    const o = this.mapObj(m, at, p), key = this.key(k, o.decl, at)
    if (o.w && !I.same(o.w.key, key)) return refuse(at, `writes ${o.decl.name} at a second key in one step`)
    const vals = new Map<string, GV>(o.decl.fields.map(f => [f.name, f.sort.k === 'num' ? {t: 'num', e: I.num(0), ty: {bits: 64, signed: true, t: -1}} : {t: 'bool', e: I.F}]))
    return {...p, heap: new Map(p.heap).set((m as {id: string}).id, {...o, w: {key, has: I.F, vals}})}
  }
  // A map field set to a new empty map: where it is nil (the lazy start Go code makes), its nil flag cleared.
  mapAssign(x: GX, v: GV, p: Path): Path {
    if (v.t !== 'map' || v.id !== 'new-map') return refuse(x, 'a map given a second name (a map is a reference: a write through either is a write to both)')
    const [pl, q] = this.place(x, p)
    if (pl.k === 'blank') return q
    const [cur, q2] = this.readPlace(pl, x, q)
    if (cur.t !== 'map') return refuse(x, 'a new map kept other than in a map field of the state')
    const o = this.mapObj(cur, x, q2)
    // Only where it is nil: a map with keys replaced whole is outside the subset.
    const nilNow = o.nil
    if (!(nilNow.op === 'const' && nilNow.v) && !q2.pc.some(c => I.same(c, nilNow))) return refuse(x, `${o.decl.name} replaced whole (the subset sets a map once, where it is nil)`)
    return {...q2, heap: new Map(q2.heap).set(cur.id, {...o, nil: I.F})}
  }

  // --- lists (a slice of the state) -----------------------------------------------------------------------------------
  listObj(s: GV, at: GX, p: Path): Extract<Obj, {k: 'list'}> {
    if (s.t !== 'list' || !p.heap.has(s.id)) return refuse(at, `${at.text}: a slice other than the state's`)
    return p.heap.get(s.id) as Extract<Obj, {k: 'list'}>
  }
  listLen(s: GV, at: GX, p: Path): N {
    const o = this.listObj(s, at, p)
    if (o.ops.length) return refuse(at, `${o.decl.name} read after it is written in one step`)
    return I.nvar(`${o.decl.name}_len`)
  }
  listGet(s: GV, i: GV, at: GX, p: Path): [GV, Path] {
    const o = this.listObj(s, at, p), idx = this.num(i, at), len = this.listLen(s, at, p)
    const inside = I.and(I.cmp('<=', I.num(0), idx), I.cmp('<', idx, len))
    this.refuseWhere(p, I.not(inside), at, 'an index out of range (a panic)')
    const it = this.intTy(this.T(at.x!.t).elem!)
    const e = {op: 'cell', map: o.decl.name, key: {op: 'num', e: idx}, field: '$item'} as const
    return [o.decl.fields[0]!.sort.k === 'num' ? {t: 'num', e: e as N, ty: it!} : {t: 'bool', e: e as B}, this.assume(p, inside)]
  }
  listSet(s: GV, i: GV, v: GV, at: GX, p: Path): Path {
    const o = this.listObj(s, at, p), idx = this.num(i, at), len = this.listLen(s, at, p)
    const inside = I.and(I.cmp('<=', I.num(0), idx), I.cmp('<', idx, len))
    this.refuseWhere(p, I.not(inside), at, 'an index out of range (a panic)')
    const q = this.assume(p, inside)
    return {...q, heap: new Map(q.heap).set((s as {id: string}).id, {...o, ops: [{op: 'set', i: idx, x: v, when: I.T}]})}
  }
  // s = append(s, x) and s = s[:len(s)-1] in s's own place; any other slice put there is refused.
  listAssign(x: GX, v: GV, p: Path): Path {
    const [pl, q] = this.place(x, p)
    if (pl.k === 'blank') return q
    const [cur, q2] = this.readPlace(pl, x, q)
    if ((v.t !== 'push' && v.t !== 'pop') || cur.t !== 'list' || v.id !== cur.id) return refuse(x, 'a slice given a second name, or replaced whole (two slices may share a backing array: append writes into it or not by its capacity)')
    const o = this.listObj(cur, x, q2)
    if (o.ops.length) return refuse(x, `a second write to ${o.decl.name} in one step`)
    const it = o.decl.fields[0]!.sort.k
    if (v.t === 'push' && ((it === 'num' && v.x.t !== 'num') || (it === 'bool' && v.x.t !== 'bool'))) return refuse(x, 'an item of the wrong kind appended')
    return {...q2, heap: new Map(q2.heap).set(cur.id, {...o, ops: [v.t === 'push' ? {op: 'push', x: v.x, when: I.T} : {op: 'pop', when: I.T}]})}
  }
}
const RESERVED = new Set(['rule', 'nat', 'int', 'bool', 'when', 'min', 'max', 'all', 'any', 'not', 'yes', 'no', 'lit', 'str', 'record', 'oneOf', 'intern', 'Int', 'forall'])
const phiP = (c: B, a: Ptr, b: Ptr): Ptr => (c.op === 'const' ? (c.v ? a : b) : JSON.stringify(a) === JSON.stringify(b) ? a : {k: 'phi', c, a, b})
const keyOfB = (b: B) => I.keyOf(b)
const keyOfV = (v: GV): string => JSON.stringify(v, (_, x) => (x instanceof Map ? [...x.entries()] : x))
const keyOfObj = (o: Obj): string => JSON.stringify(o, (_, x) => (x instanceof Map ? [...x.entries()] : x))

// --- the model --------------------------------------------------------------------------------------------------------
export type GoRead = {model: Model, edges: B[], unsigned: string[], leaves: GoLeaf[], spans: [string, number, number][], entry: string, methods: {name: string, ptr: boolean, params: {name: string, t: number, arg: Arg}[], results: number[], err: boolean}[]}
export function readGo(pkg: GoPkg, opts: GoOptions): GoRead {
  const g = new GoReader(pkg, opts)
  const td = pkg.types.find(t => t.name === opts.entry) ?? refuse(pkg.files[0]?.name ?? '?', `no type ${opts.entry} in package ${pkg.package}`)
  const st = g.T(td.t)
  if (st.k !== 'struct') refuse(td, `${opts.entry} is a ${st.k === 'float' ? 'float' : st.k} type, not a struct (the subset reads a struct and its methods)`)
  if (st.args?.length || st.generic) refuse(td, `${opts.entry} is a generic type (its methods read a type parameter)`)
  if (pkg.funcs.some(f => f.recv?.type === opts.entry && f.generic)) refuse(td, `${opts.entry} is a generic type (its methods read a type parameter)`)
  // The state: the object, every field of a subset type a leaf.
  const heap = new Map<string, Obj>()
  const fields = g.buildStruct(td.t, [], heap, td)
  heap.set('this', {k: 'struct', ty: td.t, f: fields, origin: 'state'})
  for (const [id, o] of heap) g.init.set(id, o)
  const stateVars = [...g.vars.values()].filter(v => v.role === 'state')
  // The methods: each an event.
  const all = pkg.funcs.filter(f => f.recv?.type === opts.entry && f.body)
  const chosen = opts.methods ? opts.methods.map(n => all.find(f => f.name === n) ?? refuse(td, `no method ${opts.entry}.${n} with a body`)) : all.filter(f => /^[A-Z]/.test(f.name))
  if (!chosen.length) refuse(td, `${opts.entry} has no methods to read`)
  const names = chosen.map(f => f.name), ev = g.newVar('method', {k: 'choice', values: names}, 'input')
  const evL = {op: 'var' as const, name: ev.name, values: names}
  const outputs: string[] = [], results: Record<string, {k: 'scalar', name: string}> = {}
  type Final = {sel: B, leaves: Map<string, Term>, maps: Map<string, {key: K, has: B, vals: Record<string, Term>}>, lists: Map<string, ListOp[]>, out?: [string, Term]}
  const finals: Final[] = [], events: Event[] = [], methods: GoRead['methods'] = []
  for (const fn of chosen) {
    g.method = fn.name
    const sel = I.is(evL, fn.name)
    let p: Path = {pc: [sel], locals: new Map(), heap: new Map(heap), locks: [], defers: []}
    const bound = g.bindParams(fn, sel, p), args = bound.args, params = bound.params
    p = bound.p
    // The receiver.
    if (fn.recv?.id) p = g.bind(fn.recv.id, fn.recv.ptr ? {t: 'ptr', to: {k: 'obj', id: 'this', path: []}, elem: td.t} : {t: 'struct', ty: td.t, f: fields}, fn, p)
    const errAt = fn.results.length && g.T(fn.results.at(-1)!.t).k === 'error' ? fn.results.length - 1 : -1
    const kept = fn.results.filter((_, i) => i !== errAt)
    if (kept.length > 1) refuse(fn, `${fn.name} returns ${kept.length} values (a result kept is one value)`)
    for (const r of fn.results) if (r.id) { const [z, q] = g.zero(r.t, fn, p); p = g.bind(r.id, z, fn, q) }
    g.frames.push(fn)
    const key = `${opts.entry}.${fn.name}`
    g.spans.set(key, [fn.p.split(':')[0]!, fn.span[0], fn.span[1]])
    let flow: Flow
    try { flow = g.block(fn.body!, p) } finally { g.frames.pop() }
    if (flow.brk.length) refuse(fn, 'a break outside a switch')
    const rets = [...flow.rets, ...(flow.live ? [{p: flow.live, vs: []}] : [])]
    // An error returned: a refusal (where it isn't nil), the state as it was there.
    const ok: Ret[] = []
    for (const r of rets) {
      const done = {...r, p: {...r.p, locks: r.p.locks.filter(k => !r.p.defers.includes(k))}}
      if (done.p.locks.length) refuse(fn, `${fn.name} returns with a mutex locked`)
      if (errAt >= 0) {
        const e = done.vs[errAt]
        const is = !e ? I.F : e.t === 'err' ? e.is : e.t === 'nil' ? I.F : refuse(fn, `${fn.name} returns an error of another kind`)
        g.refuseWhere(done.p, is, fn, 'an error returned')
        if (!(is.op === 'const' && is.v)) ok.push({...done, p: g.assume(done.p, I.not(is))})
      } else ok.push(done)
    }
    if (!ok.length) refuse(fn, `${fn.name} always fails`)
    // The kept result: by the path that returned it (a local the join merges).
    const ri = fn.results.findIndex((_, i) => i !== errAt)
    const final = g.join(ok.map(r => (kept.length ? {...r.p, locals: new Map(r.p.locals).set('$ret', r.vs[ri]!)} : r.p)), fn)!, acc = final.locals.get('$ret')!
    let out: [string, Term] | undefined
    if (kept.length) {
      const s = g.scalar(fn.results[ri]!.t)
      if (typeof s === 'string') refuse(fn, `${fn.name} returns ${s}`)
      const x = g.newVar(`${fn.name}_result`, s as Var['sort'], 'state', `what ${fn.name} returned, at the step that called it (its default at others)`)
      outputs.push(x.name); results[fn.name] = {k: 'scalar', name: x.name}
      const it = g.intTy(fn.results[ri]!.t)
      if (it) g.ranges.set(x.name, g.range(it))
      out = [x.name, termOf(acc, fn)]
    }
    finals.push({sel, ...materialize(g, final, fn), ...(out ? {out} : {})})
    events.push({select: {[ev.name]: fn.name}, call: fn.name, args})
    methods.push({name: fn.name, ptr: !!fn.recv?.ptr, params, results: fn.results.map(r => r.t), err: errAt >= 0})
  }
  // The lazy inputs' records: the fields read.
  const lazy = g.lazyInputs
  const recOf = (a: Arg): Arg => (a.k === 'lazy' ? {k: 'rec', fields: (lazy.get(`in:${a.prefix}`)?.fields ?? []).map(([f, n]) => [f, {k: 'input', name: n} as Arg])} : a)
  for (const e of events) e.args = e.args.map(recOf)
  // (and the harness's: it makes the struct with the fields read)
  for (const mt of methods) mt.params = mt.params.map(pa => ({...pa, arg: recOf(pa.arg)}))
  // The methods together: each variable by the method called.
  const writes: Record<string, Term> = {}, init: Record<string, Term> = {}
  const leafVars = stateVars.filter(v => !g.lists.some(d => d.name === v.name) && !g.maps.some(d => d.name === v.name))
  for (const v of leafVars) {
    const zero: Term = v.sort.k === 'num' ? {s: 'num', e: I.num(0)} : v.sort.k === 'bool' ? {s: 'bool', e: v.name.endsWith('_nil') && g.leaves.some(l => l.name === v.name && (l.kind === 'bignil' || l.kind === 'mapnil')) ? I.T : I.F} : {s: 'str', e: {op: 'slit', value: ''}}
    init[v.name] = zero
    let acc: Term | undefined
    for (let i = finals.length - 1; i >= 0; i--) {
      const t = finals[i]!.leaves.get(v.name) ?? varTerm(v)
      acc = acc === undefined ? t : iteTerm(finals[i]!.sel, t, acc)
    }
    if (acc && !sameTerm(acc, varTerm(v))) writes[v.name] = acc
  }
  for (const o of outputs) {
    const v = g.vars.get(o)!
    init[o] = v.sort.k === 'num' ? {s: 'num', e: I.num(0)} : v.sort.k === 'bool' ? {s: 'bool', e: I.F} : {s: 'str', e: {op: 'slit', value: ''}}
    let acc: Term = init[o]!
    for (let i = finals.length - 1; i >= 0; i--) { const t = finals[i]!.out?.[0] === o ? finals[i]!.out![1] : init[o]!; acc = iteTerm(finals[i]!.sel, t, acc) }
    writes[o] = acc
  }
  const mapWrites: Model['mapWrites'] = {}
  for (const d of g.maps) {
    const ws = finals.map(f => f.maps.get(d.name))
    if (!ws.some(Boolean)) continue
    const key0 = ws.find(Boolean)!.key
    let acc: {key: K, has: B, vals: Record<string, Term>} | undefined
    for (let i = finals.length - 1; i >= 0; i--) {
      const w = ws[i] ?? (() => { const k = acc?.key ?? key0, c = g.baseCell(d, k); return {key: k, has: c.has, vals: Object.fromEntries([...c.vals].map(([f, v]) => [f, termOf(v, {p: ''})]))} })()
      acc = acc === undefined ? w : {key: I.kite(finals[i]!.sel, w.key, acc.key), has: I.bite(finals[i]!.sel, w.has, acc.has), vals: Object.fromEntries(Object.entries(w.vals).map(([f, t]) => [f, iteTerm(finals[i]!.sel, t, acc!.vals[f]!)]))}
    }
    mapWrites[d.name] = acc!
  }
  const listWrites: NonNullable<Model['listWrites']> = {}
  for (const d of g.lists) {
    const ops = finals.flatMap(f => (f.lists.get(d.name) ?? []).map(o => ({...o, when: I.and(f.sel, o.when)})))
    if (ops.length) listWrites[d.name] = ops.map(o => (o.op === 'pop' ? o : {...o, x: termOf(o.x, {p: ''})})) as NonNullable<Model['listWrites']>[string]
  }
  // What the rule reads or writes: the leaves no term mentions are left out (the check asks the code not to change them).
  const used = new Set<string>()
  const mention = (t: object) => { const r = I.varsOf(t as N); for (const n of r.vars) used.add(n); for (const n of r.maps) used.add(n) }
  for (const t of Object.values(writes)) mention(t.e)
  for (const [n, w] of Object.entries(mapWrites)) { used.add(n); mention(w.has); mention(w.key); for (const t of Object.values(w.vals)) mention(t.e) }
  for (const [n, ops] of Object.entries(listWrites)) { used.add(n); for (const o of ops) { mention(o.when); if (o.op !== 'pop') mention(o.x.e); if (o.op === 'set') mention(o.i) } }
  const refuseB = I.or(...g.refusals)
  mention(refuseB)
  for (const n of Object.keys(writes)) used.add(n)
  // A map's nil flag and a big.Int's go with their value.
  for (const l of g.leaves) {
    if (l.kind === 'bignil' && used.has(l.name.replace(/_nil$/, ''))) used.add(l.name)
    if (l.kind === 'big' && used.has(`${l.name}_nil`)) used.add(l.name)
    if (l.kind === 'mapnil' && used.has(l.name.replace(/_nil$/, ''))) used.add(l.name)
    if (l.kind === 'map' && used.has(`${l.name}_nil`)) used.add(l.name)
    if (l.kind === 'list' && used.has(`${l.name}_len`)) used.add(l.name)
  }
  const keepVar = (v: Var) => used.has(v.name) || outputs.includes(v.name)
  const state = [...leafVars.filter(keepVar), ...outputs.map(o => g.vars.get(o)!)]
  for (const n of Object.keys(init)) if (!state.some(v => v.name === n)) delete init[n]
  const leftOut = leafVars.filter(v => !keepVar(v)).map(v => v.name)
  const maps = g.maps.filter(d => used.has(d.name)), lists = g.lists.filter(d => used.has(d.name))
  for (const l of g.leaves) if (l.name && !state.some(v => v.name === l.name) && !maps.some(d => d.name === l.name) && !lists.some(d => d.name === l.name)) l.kind = 'frame'
  if (leftOut.length) g.notes.add(`left out (no method reads or writes them; the check asks the code not to change them): ${leftOut.join(', ')}`)
  for (const l of g.leaves) if (l.kind === 'frame' && !l.name) g.notes.add(`${l.path.join('.')}: a ${l.go}, outside the subset, left out (no method the rule reads touches it)`)
  // The laws every state of the code keeps: each fixed-width number within its type's range, a nil map holding no key.
  const laws: string[] = []
  for (const v of state) {
    const r = g.ranges.get(v.name)
    if (!r || v.sort.k !== 'num') continue
    const [lo, hi] = r
    if (Number.isFinite(hi)) laws.push(`r.law(${JSON.stringify(`${v.name} within its type's range`)}, ({${v.name}}) => ${v.name}.atMost(${hi}).and(${v.name}.atLeast(${lo})))`)
    else if (lo === 0) laws.push(`r.law(${JSON.stringify(`${v.name} within its type's range`)}, ({${v.name}}) => ${v.name}.atLeast(0))`)
  }
  for (const l of g.leaves) if (l.kind === 'big' && state.some(v => v.name === l.name)) laws.push(`r.law(${JSON.stringify(`${l.name}: a nil one holds 0`)}, ({${l.name}, ${l.name}_nil}) => any(${l.name}_nil.not(), ${l.name}.eq(0)))`)
  for (const d of maps) laws.push(`r.law(${JSON.stringify(`${d.name}: a nil map holds no key`)}, ({${d.name}, ${d.name}_nil}) => forall(k => any(${d.name}_nil.not(), ${d.name}.at(k).has.not())))`)
  const layout: Layout = {k: 'rec', fields: state.filter(v => !outputs.includes(v.name)).map(v => [v.name, {k: 'scalar', name: v.name}] as [string, Layout])}
  const model: Model = {
    name: opts.entry, shape: 'class', file: pkg.files[0]?.name ?? 'go', entry: opts.entry,
    params: [], inputs: g.inputs, state, maps, init, writes, mapWrites, outputs, ...(lists.length ? {lists, listWrites} : {}),
    refuse: refuseB, pre: I.T, layout, events, notes: [...g.notes], hints: g.hints, event: ev.name, results, laws,
  }
  // Unsigned inputs are naturals (the input's kind); a state variable's sort is the printer's to decide (a natural where
  // every write is proven one: a wrap by cases may not be, though it stays within the type, which its law says).
  const unsigned = [...g.ranges].filter(([n, [lo, hi]]) => lo === 0 && hi > 0 && g.inputs.some(v => v.name === n)).map(([n]) => n)
  return {model, edges: g.edges, unsigned, leaves: g.leaves.filter(l => l.kind === 'frame' || state.some(v => v.name === l.name) || maps.some(d => d.name === l.name) || lists.some(d => d.name === l.name)), spans: [...g.spans.values()], entry: opts.entry, methods}
}
const varTerm = (v: Var): Term => (v.sort.k === 'num' ? {s: 'num', e: I.nvar(v.name)} : v.sort.k === 'bool' ? {s: 'bool', e: I.bvar(v.name)} : {s: 'str', e: {op: 'svar', name: v.name}})
const sameTerm = (a: Term, b: Term) => I.same(a.e, b.e)
function iteTerm(c: B, a: Term, b: Term): Term {
  if (a.s === 'num' && b.s === 'num') return {s: 'num', e: I.nite(c, a.e, b.e)}
  if (a.s === 'bool' && b.s === 'bool') return {s: 'bool', e: I.bite(c, a.e, b.e)}
  if (a.s === 'str' && b.s === 'str') return {s: 'str', e: I.kite(c, a.e, b.e)}
  throw new Error('terms of two sorts')
}
function termOf(v: GV, at: {p: string}): Term {
  if (v.t === 'num') return {s: 'num', e: v.e}
  if (v.t === 'bool') return {s: 'bool', e: v.e}
  if (v.t === 'str') return {s: 'str', e: v.e}
  return refuse(at, `a ${v.t} where the rule keeps a number, a boolean or a string`)
}
// The state at a method's end, leaf by leaf (and the maps' and lists' writes), checking that no object of the state
// is in two of its places.
function materialize(g: GoReader, p: Path, at: {p: string}): {leaves: Map<string, Term>, maps: Map<string, {key: K, has: B, vals: Record<string, Term>}>, lists: Map<string, ListOp[]>} {
  const leaves = new Map<string, Term>(), maps = new Map<string, {key: K, has: B, vals: Record<string, Term>}>(), lists = new Map<string, ListOp[]>()
  const self = p.heap.get('this') as Extract<Obj, {k: 'struct'}>
  const seen = new Map<string, string>()
  for (const l of g.leaves) {
    if (l.kind === 'frame' || l.kind === 'bignil' || l.kind === 'mapnil') continue
    let v: GV | undefined = {t: 'struct', ty: self.ty, f: self.f}
    for (const s of l.path) v = v?.t === 'struct' ? v.f.get(s) : undefined
    if (!v) continue
    if (l.kind === 'big') {
      if (v.t !== 'ptr' && v.t !== 'nil') refuse(at, `${l.path.join('.')} set to other than a *big.Int`)
      const to: Ptr = v.t === 'nil' ? {k: 'nil'} : (v as {to: Ptr}).to, cs = g.cases(to)
      let val: N | undefined
      for (const o of [...cs.objs].reverse()) {
        const obj = p.heap.get(o.id)
        if (obj?.k !== 'big') refuse(at, `${l.path.join('.')} points to other than a big.Int`)
        // One object in two places of the state, or one the caller gave: refused (the rule keeps a value per field).
        const prev = seen.get(o.id)
        if (prev && prev !== l.name) refuse(at, `${l.path.join('.')} and ${prev} may be one big.Int (one object in two places of the state)`)
        seen.set(o.id, l.name)
        if (obj!.origin === 'input') refuse(at, `${l.path.join('.')} keeps the *big.Int the caller gave (the caller may change it after the call)`)
        // Where it isn't nil it is one of the objects: the last of them needs no condition.
        val = val === undefined ? (obj as {v: N}).v : I.nite(o.c, (obj as {v: N}).v, val)
      }
      // Unchanged (nil as it was, the same object with the same value): the variables themselves (a nil one holds 0).
      const same = I.same(cs.nil, I.bvar(`${l.name}_nil`)) && val !== undefined && I.same(val, I.nvar(l.name))
      leaves.set(l.name, {s: 'num', e: same ? I.nvar(l.name) : val === undefined ? I.num(0) : I.nite(cs.nil, I.num(0), val)})
      leaves.set(`${l.name}_nil`, {s: 'bool', e: cs.nil})
      continue
    }
    if (l.kind === 'map') {
      if (v.t !== 'map') continue
      const o = p.heap.get(v.id) as Extract<Obj, {k: 'map'}>
      leaves.set(`${l.name}_nil`, {s: 'bool', e: o.nil})
      if (o.w) maps.set(l.name, {key: o.w.key, has: o.w.has, vals: Object.fromEntries([...o.w.vals].map(([f, x]) => [f, termOf(x, at)]))})
      continue
    }
    if (l.kind === 'list') {
      if (v.t !== 'list') continue
      const o = p.heap.get(v.id) as Extract<Obj, {k: 'list'}>
      if (o.ops.length) lists.set(l.name, o.ops)
      continue
    }
    leaves.set(l.name, termOf(v, at))
  }
  return {leaves, maps, lists}
}

// --- running the reader -------------------------------------------------------------------------------------------------
type ChildProcess = {execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string}
type FS = {existsSync: (p: string) => boolean, mkdirSync: (p: string, o: unknown) => void, readFileSync: (p: string, e: string) => string}
const proc = (globalThis as {process?: {getBuiltinModule?: (id: string) => unknown, env?: Record<string, string | undefined>}}).process
export const node = <T>(id: string): T => { const m = proc?.getBuiltinModule?.(id); if (!m) throw new Error(`the Go front end runs Go through ${id} (Node 20.16 or later, or Bun)`); return m as T }
// The reader, built once per version of its source (into the system's temporary directory).
export function readerBinary(): string {
  const fs = node<FS>('node:fs'), cp = node<ChildProcess>('node:child_process'), os = node<{tmpdir: () => string}>('node:os'), crypto = node<{createHash: (a: string) => {update: (s: string) => {digest: (e: string) => string}}}>('node:crypto')
  const dir = new URL('./go/', import.meta.url).pathname
  const src = fs.readFileSync(`${dir}reader.go`, 'utf8'), h = crypto.createHash('sha256').update(src).digest('hex').slice(0, 12)
  const bin = `${os.tmpdir()}/gdp-goreader-${h}`
  if (!fs.existsSync(bin)) cp.execFileSync('go', ['build', '-o', bin, '.'], {cwd: dir, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], env: {...proc?.env, GOFLAGS: '-mod=mod', GOTOOLCHAIN: 'local'}})
  return bin
}
export function readGoPackage(dir: string): GoPkg {
  const cp = node<ChildProcess>('node:child_process')
  return JSON.parse(cp.execFileSync(readerBinary(), [dir], {encoding: 'utf8', maxBuffer: 1 << 29, stdio: ['ignore', 'pipe', 'pipe']})) as GoPkg
}

// --- the front end ---------------------------------------------------------------------------------------------------
// `dir`: the package's directory inside its module (the check builds it there, with the module's go.mod).
export type GoExtraction = Extraction & {leaves?: GoLeaf[]}
export function extractGo(dir: string, opts: GoOptions): GoExtraction {
  const notes: string[] = []
  let read: GoRead, pkg: GoPkg
  try {
    pkg = readGoPackage(dir)
    read = readGo(pkg, opts)
  } catch (e) {
    if (e instanceof Refusal) { const r = {ok: false, refusals: [{where: e.where, what: e.what}], notes}; snapshot(opts, r); return r }
    throw e
  }
  const file = `${read.entry}.go`
  const x = fromModel(read.model, file, {...unsignedDomains(read), ...opts.domains}, notes, (rule, sorts) => checkGo(dir, pkg, read, rule, sorts, opts))
  snapshot(opts, x)
  return {...x, leaves: read.leaves}
}
// (gen/go-shared: each extraction's rule, notes and refusals appended to $GDP_GO_SNAPSHOT, to compare the Go front end
// before and after it moves onto the shared executor)
function snapshot(opts: GoOptions, x: {source?: string, notes: string[], refusals: {where: string, what: string}[], ok: boolean}) {
  const f = proc?.env?.GDP_GO_SNAPSHOT
  if (f) node<{appendFileSync: (p: string, s: string) => void}>('node:fs').appendFileSync(f, `${JSON.stringify({entry: opts.entry, methods: opts.methods ?? null, ok: x.ok, source: x.source ?? null, notes: x.notes, refusals: x.refusals})}\n`)
}
// Unsigned numbers are naturals by their type (inputs and state alike); the rule's sorts say so.
function unsignedDomains(r: GoRead): Record<string, 'nat' | 'int'> {
  const out: Record<string, 'nat' | 'int'> = {}
  for (const n of r.unsigned) out[n] = 'nat'
  return out
}

// A function the corpus names (not a struct's method): read as far as the subset goes, for where and why it stops; a
// function the subset reads to its end is still not a step (a decision of its arguments, or writes to the caller's
// objects): refused so, with what it is.
export function probeGoFunc(pkg: GoPkg, name: string): {where: string, what: string} {
  const g = new GoReader(pkg, {entry: ''})
  const fn = g.funcOf(name)
  if (!fn) return {where: pkg.files[0]?.name ?? '?', what: `${name}: not a function the package declares with a body`}
  try {
    if (fn.generic) refuse(fn, `${name}: a generic function`)
    const bound = g.bindParams(fn, I.T, {pc: [], locals: new Map(), heap: new Map(), locks: [], defers: []})
    let p = bound.p
    for (const r of fn.results) if (r.id) { const [z, q] = g.zero(r.t, fn, p); p = g.bind(r.id, z, fn, q) }
    g.frames.push(fn)
    g.block(fn.body!, p)
  } catch (e) {
    if (e instanceof Refusal) return {where: e.where, what: e.what}
    throw e
  }
  const writes = fn.params.some(x => g.T(x.t).k === 'ptr')
  return {where: fn.p, what: `${name}: a function of its arguments${writes ? ' (the objects its pointers give are the caller\'s)' : ''}, not a step of a state the subset reads (a struct and its methods)`}
}
