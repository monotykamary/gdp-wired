// The extractor's Go front end (`extractGo`): a struct's methods read through Go's own parser and type checker
// (core/go/reader.go, go/ast and go/types, run with the Go toolchain), lowered here into the shared step IR and executed
// by the shared executor (core/extract-step.ts) into the same Model every front end makes, printed, built and checked
// as that one is (core/extract.ts's fromModel). The lowering decides what Go's types decide (which operation a node is,
// the width of an integer, a refusal that needs no execution); the executor does what the values decide. Only the
// reader, the lowering and the check's runner are Go's: the check (core/extract-go-check.ts) builds the package as it
// ships with a generated harness beside it, drives the methods with the same requests as the rule, and prints every
// state as JSON for the comparison core/extract-check.ts makes. Nothing here is trusted either.
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
import {type Arg, type Event, type Layout, type MapDecl, type Model, Refusal, type Term, type Var} from './extract-read.ts'
import {type Extraction, fromModel} from './extract.ts'
import {type IntTy, type Recipe, type SFunc, type SModule, type SS, type SX, type StepObj, type StepPath, type StepPtr, type StepValue, Stepper, iteTerm, mapWritesOf, phiP, rangeLaws, rangeOf, varTerm} from './extract-step.ts'
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
const refuse = (x: {p: string} | string, what: string): never => { throw new Refusal(typeof x === 'string' ? x : x.p || '?', what) }
type Path = StepPath
type V = StepValue

// --- the lowering: Go's JSON into the step IR, what the types decide decided here ------------------------------------
class Go {
  readonly g: Stepper
  readonly leaves: GoLeaf[] = []
  readonly funcs: Record<string, SFunc> = {}
  constructor(readonly pkg: GoPkg, readonly opts: GoOptions) {
    const mod: SModule = {lang: 'go', file: pkg.files[0]?.name ?? 'go', path: '', module: pkg.package, root: '', entries: [], recs: {}, funcs: this.funcs, split: false}
    this.g = new Stepper(mod, {entry: opts.entry, ...(opts.onError ? {onError: opts.onError} : {})})
    for (const f of pkg.funcs) this.funcs[`${f.recv?.type ?? ''}.${f.name}`] = this.fn(f)
  }
  T(t: number): TT { return this.pkg.ttab[t] ?? {k: 'invalid'} }
  // (another package's types by its name, not the harness's alias for it)
  tname(t: number): string { const x = this.T(t); return x.go?.replace(/\bgdp_(?:\w*_)?(\w+)\./g, '$1.') ?? x.name ?? x.k }
  intTy(t: number): IntTy | undefined { const x = this.T(t); return x.k === 'int' ? {bits: x.untyped ? 64 : x.bits ?? 64, signed: x.signed ?? true, t, name: this.tname(t)} : undefined }
  isBig(t: number): boolean { const x = this.T(t); return x.k === 'ext' && x.pkg === 'math/big' && x.name === 'Int' }
  isBigPtr(t: number): boolean { const x = this.T(t); return x.k === 'ptr' && this.isBig(x.elem!) }
  isContext(t: number): boolean { const x = this.T(t); return x.k === 'ext' && x.pkg === 'context' && x.name === 'Context' }
  isMutex(t: number): boolean { const x = this.T(t); return x.k === 'ext' && x.pkg === 'sync' && (x.name === 'Mutex' || x.name === 'RWMutex') }
  stdlib(path: string): boolean { return !path.split('/')[0]!.includes('.') }
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
      for (const i of x.k === 'map' ? [x.key!, x.elem!] : [x.elem!]) { const w = this.whyType(i, depth + 1); if (w !== 'outside the subset') return x.k === 'map' ? `a map of ${w}` : x.k === 'ptr' ? w : `a ${x.k} of ${w}` }
    }
    if (x.k === 'ext') return `${x.go ?? x.name}, a type of the standard library outside the subset`
    return 'outside the subset'
  }
  methodOf(type: string, name: string): GoFunc | undefined { return this.pkg.funcs.find(f => f.recv?.type === type && f.name === name) }
  funcOf(name: string): GoFunc | undefined { return this.pkg.funcs.find(f => !f.recv && f.name === name) }

  // --- expressions ----------------------------------------------------------------------------------------------------
  no(x: {p: string}, why: string, more: Record<string, unknown> = {}): SX { return {e: 'no', p: x.p, why, ...more} }
  at(x: GX): {p: string, text: string} { return {p: x.p, text: x.text} }
  // A value as the type it is assigned to: an untyped constant takes the type; an integer stays itself.
  as(v: SX, t: number): SX {
    const ty = this.intTy(t), k = this.T(t).k
    return ty || k === 'ptr' || k === 'error' ? {e: 'as', p: v.p, x: v, ...(ty ? {ity: ty} : {nil: k === 'ptr' ? 'ptr' : 'err'})} : v
  }
  // Go's zero value of a type.
  zero(t: number, at: {p: string}): SX {
    const tt = this.T(t)
    if (tt.k === 'int') return {e: 'int', p: at.p, v: 0, ity: this.intTy(t)}
    if (tt.k === 'bool') return {e: 'bool', p: at.p, v: false}
    if (tt.k === 'string') return {e: 'str', p: at.p, v: ''}
    if (tt.k === 'ptr') return {e: 'ptr0', p: at.p}
    if (tt.k === 'error') return {e: 'errv', p: at.p, is: false}
    if (tt.k === 'struct') {
      return {e: 'struct', p: at.p, ty: String(t), fields: (tt.fields ?? []).map(g => {
        const s = this.scalar(g.t)
        return [g.name, typeof s === 'string' && !['ptr', 'struct', 'error'].includes(this.T(g.t).k) ? {e: 'opaque', p: at.p, why: `${g.name}: ${s}`, firm: true} : this.zero(g.t, at)]
      })}
    }
    return {e: 'opaque', p: at.p, why: `a value of type ${this.tname(t)} (outside the subset)`, firm: true}
  }
  x(x: GX): SX {
    const at = this.at(x), c = x.c
    if (c) {
      if (c.int !== undefined) {
        const ty = this.intTy(x.t)
        if (!ty) return this.no(x, this.T(x.t).k === 'float' ? `${x.text}: a float constant (the subset reads integers)` : `${x.text}: an integer constant of type ${this.tname(x.t)}`)
        const v = Number(c.int)
        if (!Number.isSafeInteger(v)) return this.no(x, `${x.text}: the constant ${c.int} is past 2^53 (the rule's numbers stop there)`)
        return {e: 'int', ...at, v, ity: ty}
      }
      if (c.bool !== undefined) return {e: 'bool', ...at, v: c.bool}
      if (c.str !== undefined) return {e: 'str', ...at, v: c.str}
      return this.no(x, `${x.text}: ${c.float !== undefined ? 'a float constant (the subset reads integers)' : "a constant the subset doesn't read"}`)
    }
    switch (x.e) {
      case 'id': {
        if (x.o === 'nil') return {e: 'nil', ...at}
        if (x.o !== 'var') return this.no(x, `${x.text}: a ${x.o} used as a value`)
        if (!x.id?.startsWith('pkg:')) return {e: 'var', ...at, n: x.id, why: `${x.n}: a variable the step doesn't set before reading`}
        const v = this.pkg.vars.find(y => `pkg:${y.name}` === x.id), f = v?.init?.f
        if (v && this.T(v.t).k === 'error' && v.init?.e === 'call' && f?.e === 'sel' && ((f.pkg === 'errors' && f.n === 'New') || (f.pkg === 'fmt' && f.n === 'Errorf'))) return {e: 'errv', ...at, is: true, note: `${x.n}: an error the package makes once (errors.New): read as an error that isn't nil`}
        return this.no(x, `${x.n}: a package variable (state every object shares)`)
      }
      case 'sel':
        if (x.k === 'field') return {e: 'at', ...at, pl: this.place(x)}
        if (x.k === 'qual') return this.no(x, x.pkg === 'math' && /^(Max|Min)(Int|Uint)\d*$/.test(x.n!) ? `${x.text}: a constant past 2^53` : `${x.text}: ${x.pkg && !this.stdlib(x.pkg) ? "another module's" : 'a package-level'} ${x.o === 'var' ? 'variable' : 'value'} the subset doesn't read`)
        return this.no(x, `${x.text}: a method used as a value`)
      case 'paren': return this.x(x.x!)
      case 'call': return this.call(x)
      case 'bin': return {e: x.op === '&&' || x.op === '||' ? 'andalso' : 'binop', ...at, op: x.op, x: this.x(x.x!), y: this.x(x.y!)}
      case 'un': {
        if (x.op === '&') return x.x!.e === 'comp' ? {e: 'alloc', ...at, x: this.composite(x.x!)} : {e: 'addr', ...at, pl: this.place(x.x!), why: `&${x.x!.text}: a pointer to a local (the subset's pointers are to the state's objects and to new ones)`}
        return {e: 'unop', ...at, op: x.op, x: this.x(x.x!), why: `${x.op}: ${x.op === '^' ? 'a bit operation' : 'outside the subset'}`}
      }
      case 'star': return {e: 'deref', ...at, x: this.x(x.x!)}
      case 'comp': return this.composite(x)
      case 'index': {
        const xt = this.T(x.x!.t)
        if (xt.k === 'map') return this.midx(x)
        if (xt.k === 'slice') return {e: 'lidx', ...at, s: this.x(x.x!), i: this.x(x.i!), ty: this.intTy(xt.elem!)}
        return this.no(x, `${x.text}: an index into a ${this.tname(x.x!.t)}`, {pre: [this.x(x.x!), this.x(x.i!)]})
      }
      case 'slice': {
        // s[:len(s)-1] of a slice of the state: its last item taken off (put back in s's own place).
        const h = x.hi, ok = !x.lo && !x.three && h?.e === 'bin' && h.op === '-' && h.y?.c?.int === '1' && h.x?.e === 'call' && h.x.builtin === 'len' && h.x.a?.[0]?.text === x.x!.text
        return {e: 'pop', ...at, s: this.x(x.x!), ok, why: `${x.text}: a slice of a slice (it shares the backing array: a write through either is seen by both, and append writes into it or not by its capacity)`}
      }
      case 'funclit': return this.no(x, 'a closure')
      case 'assert': return this.no(x, 'a type assertion (interfaces are outside the subset)')
      case 'inst': return this.no(x, 'a generic function')
      case 'lit': return this.no(x, `${x.text}: a literal of type ${this.tname(x.t)}`)
    }
    return this.no(x, `${x.text}: an expression the subset doesn't read (${x.e})`)
  }
  midx(x: GX): SX {
    const mt = this.T(x.x!.t), vt = this.T(mt.elem!)
    const tys = Object.fromEntries((vt.k === 'struct' ? vt.fields! : [{name: 'value', t: mt.elem!}]).map(f => [f.name, this.intTy(f.t) ?? null]))
    return {e: 'midx', ...this.at(x), m: this.x(x.x!), k: this.x(x.i!), tys, sty: String(mt.elem!)}
  }
  // A place: a local (and a field path into its struct value), or a field path inside the object a pointer points to.
  place(x: GX): SX {
    if (x.e === 'id') {
      if (x.n === '_') return {e: 'blank', p: x.p}
      if (x.o !== 'var' || x.id?.startsWith('pkg:')) return this.no(x, `${x.text}: ${x.id?.startsWith('pkg:') ? 'a package variable (state every object shares)' : 'not a local'}`)
      return {e: 'var', ...this.at(x), n: x.id}
    }
    if (x.e === 'star') return {e: 'deref', ...this.at(x), x: this.x(x.x!)}
    if (x.e === 'sel' && x.k === 'field') {
      // The field names a selection goes through (its embedded fields first); through a pointer (or an embedded
      // pointer on the way) the place is the pointee's.
      let t = this.T(x.x!.t)
      const base = t.k === 'ptr' ? {e: 'deref', ...this.at(x), x: this.x(x.x!)} : this.place(x.x!)
      if (t.k === 'ptr') t = this.T(t.elem!)
      let cur: SX = base
      const path = x.path ?? []
      for (let i = 0; i < path.length; i++) {
        const f = (t.fields ?? t.xfields)?.[path[i]!]
        if (!f) return this.no(x, `${x.text}: a field the struct's type doesn't list`)
        cur = {e: 'fld', ...this.at(x), x: cur, f: f.name}
        t = this.T(f.t)
        if (t.k === 'ptr' && i < path.length - 1) { t = this.T(t.elem!); cur = {e: 'deref', ...this.at(x), x: {e: 'at', ...this.at(x), pl: cur, raw: true}} }
      }
      return cur
    }
    return this.no(x, `${x.text}: an assignment to other than a variable, a field or *p`)
  }
  composite(x: GX): SX {
    const tt = this.T(x.t), at = this.at(x)
    if (tt.k === 'struct') {
      const fields = (this.zero(x.t, x).fields as [string, SX][])
      ;(x.elts ?? []).forEach((el, i) => {
        const name = el.field ?? tt.fields?.[i]?.name
        fields.push(name === undefined ? ['', this.no(x, 'a struct literal with more values than fields')] : [name, this.as(this.x(el.v), tt.fields!.find(g => g.name === name)!.t)])
      })
      return {e: 'struct', ...at, ty: String(x.t), fields}
    }
    if ((tt.k === 'map' || tt.k === 'slice') && !(x.elts ?? []).length) return {e: tt.k === 'map' ? 'newmap' : 'newlist', ...at}
    return this.no(x, `${x.text}: a literal of a ${this.tname(x.t)} (the subset makes structs, and maps and slices empty)`)
  }
  call(x: GX): SX {
    const f = x.f!, at = this.at(x), a = x.a ?? []
    if (x.conv) return {e: 'conv', ...at, x: this.x(a[0]!), ity: this.intTy(x.t), why: `${x.text}: a conversion to ${this.tname(x.t)} (the subset converts between integer types)`}
    if (x.builtin) return this.builtin(x)
    if (f.e === 'sel' && f.k === 'qual') return this.std(x)
    if (f.e === 'sel' && f.k === 'method') {
      // A method promoted from an embedded field: its receiver is that field (through the embedded fields on the way).
      let rt = this.T(f.x!.t), base = rt.k === 'ptr' ? rt.elem! : f.x!.t, emb: SX | undefined
      if ((f.path ?? []).length > 1) {
        let cur: SX = rt.k === 'ptr' ? {e: 'deref', ...at, x: this.x(f.x!)} : this.place(f.x!), t = this.T(base)
        if (cur.e === 'blank') return this.no(x, '_')
        for (const i of f.path!.slice(0, -1)) {
          const fd = t.fields?.[i]
          if (!fd) return this.no(x, `${x.text}: an embedded field the type doesn't list`, {prepl: cur})
          cur = {e: 'fld', ...at, x: cur, f: fd.name}
          base = fd.t; t = this.T(fd.t)
          if (t.k === 'ptr') { cur = {e: 'deref', ...at, x: {e: 'at', ...at, pl: cur, raw: true}}; base = t.elem!; t = this.T(t.elem!) }
        }
        emb = cur; rt = this.T(base)
      }
      const after = emb ? {prepl: emb} : {}
      if (this.isBig(base)) return emb ? this.no(x, 'a big.Int method promoted from an embedded field', after) : this.big(x)
      if (this.isMutex(base)) return emb ? this.no(x, `${x.text}: a mutex's method promoted from an embedded field (lock it by its field's name)`, after) : {e: 'mutex', ...at, op: f.n, pl: this.place(f.x!)}
      if (f.mpkg && f.mpkg !== this.pkg.package) return this.no(x, `${x.text}: a method of ${f.mpkg} (another package's code)`, after)
      const decl = this.methodOf(f.mtype!, f.n!)
      if (!decl) return this.no(x, `${x.text}: no method ${f.mtype}.${f.n} declared with a body`, after)
      // The receiver: a pointer to the value (its place's address) or a copy of it.
      const recv: SX = emb
        ? (f.mptr ? {e: 'addr', ...at, k: 'addr', pl: emb, why: `${x.text}: a pointer method of a local value's embedded field (a pointer to a local)`} : {e: 'recv', p: x.p, k: 'rd', pl: emb})
        : f.mptr
          ? (rt.k === 'ptr' ? {e: 'recv', p: x.p, k: 'val0', x: this.x(f.x!)} : {e: 'addr', ...at, k: 'addr', pl: this.place(f.x!), why: `${f.x!.text}.${f.n}(): a pointer method of a local value (its address is a pointer to a local)`})
          : {e: 'recv', p: x.p, k: 'val', x: this.x(f.x!)}
      return {e: 'gcall', ...at, fn: `${decl.recv?.type ?? ''}.${decl.name}`, recv, args: this.args(a, decl)}
    }
    if (f.e === 'id' && f.o === 'func') {
      const decl = this.funcOf(f.n!)
      if (!decl) return this.no(x, `${f.n}: a function with no body here`)
      return {e: 'gcall', ...at, fn: `.${decl.name}`, args: this.args(a, decl)}
    }
    return this.no(x, `${x.text}: a call of a function value`)
  }
  args(a: GX[], decl: GoFunc): SX[] { return a.map((y, i) => (decl.params[i] ? this.as(this.x(y), decl.params[i]!.t) : this.x(y))) }
  builtin(x: GX): SX {
    const b = x.builtin!, a = x.a ?? [], at = this.at(x)
    switch (b) {
      case 'len': {
        const k = this.T(a[0]!.t).k
        if (k === 'string' || k === 'slice') return {e: 'len', ...at, k: k === 'string' ? 'str' : 'list', x: this.x(a[0]!), ity: this.intTy(x.t)}
        return this.no(x, k === 'map' ? 'len of a map (the subset keeps no count of a map\'s keys)' : `len of a ${this.tname(a[0]!.t)}`)
      }
      case 'append': return a.length !== 2 || x.ell ? this.no(x, 'append of other than one item') : {e: 'append', ...at, s: this.x(a[0]!), x: this.x(a[1]!), at1: this.at(a[1]!)}
      case 'delete': return {e: 'delete', ...at, m: this.x(a[0]!), k: this.x(a[1]!)}
      case 'make': {
        const k = this.T(x.t).k
        if (k === 'map' && a.length <= 2) return {e: 'newmap', ...at}
        return this.no(x, k === 'slice' ? 'make of a slice (a list starts empty: nil, and grows by append)' : `make of a ${this.tname(x.t)}`)
      }
      case 'new': { const et = this.T(x.t).elem!; return this.isBig(et) ? {e: 'bignew', ...at} : {e: 'alloc', ...at, x: this.zero(et, x)} }
      case 'min': case 'max': return {e: 'minmax', ...at, op: b, xs: a.map(y => this.x(y)), ity: this.intTy(x.t), why: `${b} of other than integers`}
      case 'panic': return {e: 'panic', ...at, args: a.map(y => this.x(y))}
      case 'recover': return this.no(x, 'recover (a panic is a refusal in the subset)')
      case 'cap': return this.no(x, 'cap (a slice\'s capacity decides whether append shares its backing array)')
      case 'copy': return this.no(x, 'copy (between two slices)')
      case 'clear': return this.no(x, 'clear (a map or a slice emptied whole)')
    }
    return this.no(x, `${b}: a builtin the subset doesn't read`)
  }
  std(x: GX): SX {
    const f = x.f!, path = f.pkg ?? '', n = f.n!, at = this.at(x)
    if ((path === 'errors' && n === 'New') || (path === 'fmt' && n === 'Errorf')) {
      // An error: not nil. Its arguments are evaluated (they may panic), its text is not compared.
      const pre = (x.a ?? []).flatMap(a => (a.e === 'call' && a.f?.e === 'sel' && a.f.n === 'String' && a.f.k === 'method' && (this.isBigPtr(a.f.x!.t) || this.isBig(a.f.x!.t)) ? [this.x(a.f.x!)] : a.c ? [] : [this.x(a)]))
      return {e: 'errv', ...at, is: true, pre}
    }
    if (path === 'math/big' && n === 'NewInt') return {e: 'bignew', ...at, x: this.x(x.a![0]!)}
    if (path === 'time' && n === 'Now') return this.no(x, 'time.Now(): the clock (the check can\'t set it for the code, and time.Time is outside the subset)')
    if (!this.stdlib(path)) return this.no(x, `${x.text}: a function of ${path} (another module's code)`)
    if (!path) return this.no(x, `${x.text}: a call on a value whose type isn't read here (another module's, beyond the packages the code imports)`)
    return this.no(x, `${x.text}: a function of the standard library the subset doesn't read`)
  }
  big(x: GX): SX {
    const f = x.f!, n = f.n!
    return {e: 'big', ...this.at(x), op: n, z: this.x(f.x!), args: (x.a ?? []).map(y => this.x(y)), ty: {bits: 64, signed: n !== 'Uint64', t: x.t, name: this.tname(x.t)}}
  }

  // --- statements -----------------------------------------------------------------------------------------------------
  body(ss: GS[], fn: GoFunc): SS[] { return ss.flatMap(s => this.s(s, fn)) }
  s(s: GS, fn: GoFunc): SS[] {
    const no = (why: string): SS[] => [{s: 'no', p: s.p, why}]
    switch (s.s) {
      case 'block': return this.body(s.b!, fn)
      case 'empty': return []
      case 'expr': {
        const x = s.x!
        if (x.e === 'call' && x.builtin === 'panic') return [{s: 'panic', p: s.p, args: (x.a ?? []).map(y => this.x(y))}]
        return [{s: 'expr', p: s.p, x: this.x(x)}]
      }
      case 'incdec': return [{s: 'incdec', p: s.p, op: s.op, to: this.place(s.x!)}]
      case 'assign': return [this.assign(s)]
      case 'decl': {
        const out: SS[] = []
        for (const sp of s.specs ?? []) {
          if (sp.type) return [...out, ...no('a type declared in a function')]
          if (sp.const) continue
          const to = sp.names.map(n => ({e: 'var', p: s.p, n: n.id, bind: 'always'}))
          if (sp.v.length && sp.v.length !== sp.names.length) { out.push({s: 'assign', p: s.p, to, one: this.x(sp.v[0]!), decl: true, why: 'a declaration of several from one value'}); continue }
          sp.names.forEach((n, i) => { const e = sp.v[i]; out.push({s: 'assign', p: s.p, to: [to[i]!], xs: [e ? this.as(this.x(e), n.t) : this.zero(n.t, s)]}) })
        }
        return out
      }
      case 'if': return [...(s.init ? this.s(s.init, fn) : []), {s: 'if', p: s.p, c: this.x(s.c!), then: this.body(s.then!, fn), else: s.else ? this.s(s.else, fn) : [], strict: `${s.c!.text}: a condition that isn't a boolean`, cp: s.c!.p}]
      case 'switch': return [...(s.init ? this.s(s.init, fn) : []), {s: 'switch', p: s.p, ...(s.tag ? {tag: this.x(s.tag)} : {}), cases: s.cases!.map(c => ({p: c.p, ...(c.default ? {default: true} : {list: c.list!.map(e => this.x(e))}), b: this.body(c.b, fn)}))}]
      case 'return': {
        const r = s.r!
        if (r.length === 1 && fn.results.length > 1) return [{s: 'ret', p: s.p, one: this.x(r[0]!), why: 'a return of one value from a function of several'}]
        if (!r.length && fn.results.length) return [{s: 'ret', p: s.p, bare: fn.results.map(x => x.id ?? null)}]
        return [{s: 'ret', p: s.p, xs: r.map((e, i) => this.as(this.x(e), fn.results[i]!.t))}]
      }
      case 'branch':
        if (s.tok === 'break' && !s.label) return [{s: 'break', p: s.p}]
        if (s.tok === 'fallthrough') return [{s: 'fallthrough', p: s.p}]
        return no(`${s.tok}${s.label ? ` ${s.label}` : ''} (the subset reads break in a switch; loops and goto are outside it)`)
      case 'defer': {
        // A mutex's Unlock deferred after its Lock: the step is atomic in the rule.
        const x = s.x!
        if (x.e === 'call' && x.f?.e === 'sel' && x.f.k === 'method' && /^(R?Unlock)$/.test(x.f.n!) && this.isMutex(this.T(x.f.x!.t).k === 'ptr' ? this.T(x.f.x!.t).elem! : x.f.x!.t)) return [{s: 'defer', p: s.p, pl: this.place(x.f.x!), text: x.text}]
        return no('defer (other than a mutex\'s Unlock after its Lock): it runs at the return, after the results are set')
      }
      case 'for': return no('a loop (for)')
      case 'range': return no(s.x && this.T(s.x.t).k === 'map' ? 'a range over a map (Go\'s iteration order is random, and loops are outside the subset)' : 'a loop (range)')
      case 'go': return no('a goroutine (its steps interleave with others)')
      case 'select': case 'send': return no('a channel')
      case 'typeswitch': return no('a type switch (interfaces are outside the subset)')
      case 'labeled': return no('a label')
    }
    return no(`a statement the subset doesn't read (${s.s})`)
  }
  // The targets of an assignment: a local bound (:= of a new name), a map's item, a slice's, or a place.
  target(x: GX, op: string): SX {
    if (op === ':=' && x.e === 'id' && x.n !== '_') return {e: 'var', ...this.at(x), n: x.id, bind: 'new'}
    if (x.e === 'index') {
      const k = this.T(x.x!.t).k
      if (k === 'map') return this.midx(x)
      if (k === 'slice') return {e: 'lidx', ...this.at(x), s: this.x(x.x!), i: this.x(x.i!)}
      return this.no(x, 'an index into other than a map or a slice')
    }
    return this.place(x)
  }
  assign(s: GS): SS {
    const l = s.l!, r = s.r!, op = s.op!
    if (op === '=' || op === ':=') {
      const to = l.map(x => this.target(x, op))
      // v, ok := m[k]: the value and whether the map holds the key.
      if (l.length === 2 && r.length === 1 && r[0]!.e === 'index' && this.T(r[0]!.x!.t).k === 'map') return {s: 'assign', p: s.p, to, mapok: this.midx(r[0]!)}
      // (Go evaluates the left side's indices and indirections, then the right side, then assigns: the subset reads
      // left sides without effects, so the right side first is the same.)
      if (r.length === 1 && l.length > 1) return {s: 'assign', p: s.p, to, one: this.x(r[0]!), why: 'an assignment of several from one value'}
      return {s: 'assign', p: s.p, to, xs: r.map((e, i) => this.as(this.x(e), l[i]!.t))}
    }
    // x op= y
    const bop = op.slice(0, -1)
    if (l[0]!.e === 'index' && this.T(l[0]!.x!.t).k === 'map') return {s: 'mopset', p: s.p, at: this.midx(l[0]!), op: bop, y: this.x(r[0]!)}
    if (l[0]!.e === 'index') return {s: 'no', p: s.p, why: `${op} on a slice's item (the subset sets an item: s[i] = x)`}
    return {s: 'opset', p: s.p, to: this.place(l[0]!), op: bop, y: this.x(r[0]!)}
  }
  fn(f: GoFunc): SFunc {
    // The named results start at their zero values.
    const zeros: SS[] = f.results.filter(r => r.id).map(r => ({s: 'assign', p: f.p, to: [{e: 'var', p: f.p, n: r.id, bind: 'always'}], xs: [this.zero(r.t, f)]}))
    let body: SS[] | undefined
    const go = this
    return {
      id: `${f.recv?.type ?? ''}.${f.name}`, name: f.name, p: f.p, span: [f.p.split(':')[0]!, f.span[0], f.span[1]], params: f.params.map(pa => ({name: pa.id ?? '', t: {k: 'any'}})), ret: {k: 'any'},
      get body() { return (body ??= [...zeros, ...go.body(f.body ?? [], f)]) }, decorators: [], ...(f.recv?.id ? {recv: f.recv.id} : {}), results: f.results.length,
      ...(f.generic ? {why: `${f.name}: a generic function`} : !f.body ? {late: `${f.name} has no body`} : f.params.some(x => x.variadic) ? {late: `${f.name}: a variadic function`} : {}),
    } as SFunc
  }

  // --- the state: the struct's fields as variables, leaf by leaf ------------------------------------------------------
  // Each field of a subset type is a leaf (a variable, or a map or a list); one of another type is left out (the check
  // asks the code not to change it), and reading or writing it is refused where it is.
  buildStruct(t: number, path: string[], heap: Map<string, StepObj>): Map<string, V> {
    const g = this.g, x = this.T(t), out = new Map<string, V>()
    for (const f of x.fields ?? []) {
      const fp = [...path, f.name], name = fp.join('_'), ft = this.T(f.t), id = `state:${fp.join('.')}`
      const leaf = (kind: GoLeaf['kind'], v: Var, ty: number) => { this.leaves.push({name: v.name, path: fp, kind, t: ty, go: this.tname(ty)}); return v }
      if (ft.k === 'int') {
        const ty = this.intTy(f.t)!, v = leaf('int', g.newVar(name, {k: 'num'}, 'state'), f.t)
        g.ints.set(v.name, ty)
        out.set(f.name, {t: 'num', e: I.nvar(v.name), ty})
      } else if (ft.k === 'bool') out.set(f.name, {t: 'bool', e: I.bvar(leaf('bool', g.newVar(name, {k: 'bool'}, 'state'), f.t).name)})
      else if (ft.k === 'string') out.set(f.name, {t: 'str', e: {op: 'svar', name: leaf('str', g.newVar(name, {k: 'str'}, 'state'), f.t).name}})
      else if (this.isBigPtr(f.t)) {
        // A *big.Int: its value, and whether it is nil (Go's zero value).
        const v = leaf('big', g.newVar(name, {k: 'num'}, 'state', 'a *big.Int (its value; 0 where it is nil)'), f.t)
        const nil = leaf('bignil', g.newVar(`${name}_nil`, {k: 'bool'}, 'state', `whether ${fp.join('.')} is nil`), f.t)
        heap.set(id, {k: 'big', v: I.nvar(v.name), origin: 'state'})
        g.stateOrigin.set(id, fp.join('.'))
        out.set(f.name, {t: 'ptr', to: phiP(I.bvar(nil.name), {k: 'nil'}, {k: 'obj', id, path: []})})
      } else if (ft.k === 'struct' && (ft.own || !ft.name)) out.set(f.name, {t: 'struct', ty: String(f.t), f: this.buildStruct(f.t, fp, heap)})
      else if (ft.k === 'map' && this.mapOK(f.t)) {
        const decl = this.mapDecl(f.t, name)
        const nil = leaf('mapnil', g.newVar(`${decl.name}_nil`, {k: 'bool'}, 'state', `whether ${fp.join('.')} is nil (a nil map holds no key, and a write to it panics)`), f.t)
        this.leaves.push({name: decl.name, path: fp, kind: 'map', t: f.t, go: this.tname(f.t)})
        heap.set(id, {k: 'map', decl, nil: I.bvar(nil.name), origin: 'state'})
        out.set(f.name, {t: 'map', id})
      } else if (ft.k === 'slice' && ['int', 'bool'].includes(this.T(ft.elem!).k)) {
        const decl: MapDecl = {name: g.newVar(name, {k: 'num'}, 'state').name, key: 'num', fields: [{name: '$item', sort: this.T(ft.elem!).k === 'int' ? {k: 'num'} : {k: 'bool'}, role: 'state'}], scalar: true, js: 'Map'}
        g.lists.push(decl)
        const it = this.intTy(ft.elem!)
        if (it) g.ints.set(`${decl.name}.$item`, it)
        this.leaves.push({name: decl.name, path: fp, kind: 'list', t: f.t, go: this.tname(f.t)})
        heap.set(id, {k: 'list', decl, ops: [], origin: 'state'})
        out.set(f.name, {t: 'list', id})
      } else {
        out.set(f.name, {t: 'opaque', why: `${fp.join('.')} is a ${this.tname(f.t)}, a field outside the subset (left out of the rule)`, firm: true})
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
    const n = this.g.newVar(name, {k: 'num'}, 'state').name
    const fs = v.k === 'struct' ? v.fields! : [{name: 'value', t: x.elem!}]
    const fields: Var[] = fs.map(f => ({name: f.name, sort: this.T(f.t).k === 'int' ? {k: 'num'} : {k: 'bool'}, role: 'state'} as Var))
    const decl: MapDecl = {name: n, key, fields, scalar: v.k !== 'struct', js: 'Map'}
    for (const f of fs) { const it = this.intTy(f.t); if (it) this.g.ints.set(`${n}.${f.name}`, it) }
    this.g.maps.push(decl)
    return decl
  }
  // An input of an integer type: a request the code can't be given (past its type's range) is refused where `sel` (the
  // method called) holds, the claim being for the type's values.
  input(x: Var, t: number, sel: B): V { return this.g.valueOfIn(x, this.intTy(t), sel) }
  // The arguments of a method or a function: each an input (a pointer to a struct of the package a fresh object whose
  // fields read are inputs, a *big.Int one whose value is).
  bindParams(fn: GoFunc, sel: B, p0: Path): {p: Path, args: Arg[], params: {name: string, t: number, arg: Arg}[]} {
    const g = this.g, args: Arg[] = [], params: {name: string, t: number, arg: Arg}[] = []
    let p = p0
    if (fn.params.some(x => x.variadic)) refuse(fn, `${fn.name}: a variadic method`)
    for (const pa of fn.params) {
      const name = `${fn.name}_${pa.name ?? 'arg'}`, tt = this.T(pa.t), s = this.scalar(pa.t)
      let v: V, arg: Arg
      if (typeof s !== 'string') { const x = g.newVar(name, s, 'input'); v = this.input(x, pa.t, sel); arg = {k: 'input', name: x.name} }
      else if (this.isBigPtr(pa.t)) {
        const x = g.newVar(name, {k: 'num'}, 'input', 'a *big.Int argument (not nil: the claim is for calls that give one)')
        p.heap.set(`in:${x.name}`, {k: 'big', v: I.nvar(x.name), origin: 'input'})
        v = {t: 'ptr', to: {k: 'obj', id: `in:${x.name}`, path: []}}; arg = {k: 'input', name: x.name}
        g.notes.add(`${name}: a *big.Int argument, never nil here (the claim is for calls that give one)`)
      } else if (tt.k === 'ptr' && ((this.T(tt.elem!).k === 'struct' && this.T(tt.elem!).own) || this.T(tt.elem!).xfields)) {
        // (Another package's struct is read as data the same way: its exported fields, the only ones the package's code
        // can read; its methods stay that package's code, refused where they are called.)
        // A pointer to a struct the caller gives: its fields read are inputs (each made where it is first read).
        const id = `in:${name}`, et = this.T(tt.elem!)
        p.heap.set(id, {k: 'rec', ty: String(tt.elem!), f: new Map(), origin: 'input', lazy: name})
        const recipes: Record<string, Recipe> = {}
        for (const fd of et.fields ?? et.xfields ?? []) {
          const fs = this.scalar(fd.t)
          recipes[fd.name] = typeof fs !== 'string' ? {k: fs.k as 'num' | 'bool' | 'str', ty: this.intTy(fd.t)} : this.isBigPtr(fd.t) ? {k: 'big'} : {k: 'no', why: `${fd.name} of the argument: ${fs}`}
        }
        g.lazyIn.set(id, {id: name, fields: [], sel, recipes})
        v = {t: 'ptr', to: {k: 'obj', id, path: []}}; arg = {k: 'lazy', prefix: name}
        g.notes.add(`${name}: a *${this.tname(tt.elem!)} the caller gives, a fresh one for each call (its fields read are inputs; the claim is for calls that don't pass the object itself)`)
      } else if ((tt.k === 'struct' && tt.own) || tt.xfields) {
        // A struct the caller gives by value: the call's own copy, so a value here as a local struct is (no other name
        // reaches it, and writing it changes nothing the caller sees). Each field of a subset type an input (another
        // package's, its exported fields: all its code can set), the others left out, refused where they are read.
        const fields: [string, Arg][] = [], f = new Map<string, V>()
        for (const fd of tt.fields ?? tt.xfields!.filter(x => x.exported)) {
          const fs = this.scalar(fd.t)
          if (typeof fs === 'string') { f.set(fd.name, {t: 'opaque', why: `${pa.name}.${fd.name} of the argument: ${fs}`, firm: true}); continue }
          const x = g.newVar(`${name}_${fd.name}`, fs, 'input')
          f.set(fd.name, this.input(x, fd.t, sel)); fields.push([fd.name, {k: 'input', name: x.name}])
        }
        v = {t: 'struct', ty: String(pa.t), f}; arg = {k: 'rec', fields}
        g.notes.add(`${fn.name}(${pa.name ?? '_'}): a ${this.tname(pa.t)} given by value, its fields inputs`)
      } else if (this.isContext(pa.t)) {
        // A context.Context: the check gives context.Background(). Exact while the step never reads it: passed on to the
        // package's own functions only (its methods, Done, Err, Value, are another package's code; given to another
        // package's function, it is that function's: both refused where they are).
        v = {t: 'opaque', why: `${pa.name ?? 'the context'}, a context.Context read (the subset only passes one on to the package's own functions)`, firm: true}; arg = {k: 'lit', value: 'context'}
        g.notes.add(`${fn.name}(${pa.name ?? '_'}): a context.Context, passed on to the package's own functions only (the claim is for any context, the step never reading it)`)
      } else return refuse(fn, `${fn.name}(${pa.name}): an argument of type ${pa.ts ?? this.tname(pa.t)} (${this.whyType(pa.t)})`)
      if (pa.id) p = g.bindLocal(pa.id, v, fn, p)
      args.push(arg); params.push({name: pa.name ?? '', t: pa.t, arg})
    }
    return {p, args, params}
  }
}

// --- the model --------------------------------------------------------------------------------------------------------
export type GoRead = {model: Model, edges: B[], unsigned: string[], leaves: GoLeaf[], spans: [string, number, number][], entry: string, methods: {name: string, ptr: boolean, params: {name: string, t: number, arg: Arg}[], results: number[], err: boolean}[]}
type ListOp = {op: 'push', x: V, when: B} | {op: 'pop', when: B} | {op: 'set', i: N, x: V, when: B}
export function readGo(pkg: GoPkg, opts: GoOptions): GoRead {
  const go = new Go(pkg, opts), g = go.g
  const td = pkg.types.find(t => t.name === opts.entry) ?? refuse(pkg.files[0]?.name ?? '?', `no type ${opts.entry} in package ${pkg.package}`)
  const st = go.T(td.t)
  if (st.k !== 'struct') refuse(td, `${opts.entry} is a ${st.k === 'float' ? 'float' : st.k} type, not a struct (the subset reads a struct and its methods)`)
  if (st.args?.length || st.generic) refuse(td, `${opts.entry} is a generic type (its methods read a type parameter)`)
  if (pkg.funcs.some(f => f.recv?.type === opts.entry && f.generic)) refuse(td, `${opts.entry} is a generic type (its methods read a type parameter)`)
  // The state: the object, every field of a subset type a leaf.
  const heap = new Map<string, StepObj>()
  const fields = go.buildStruct(td.t, [], heap)
  heap.set('this', {k: 'rec', ty: String(td.t), f: fields, origin: 'state'})
  for (const [id, o] of heap) g.initHeap.set(id, o)
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
    let p: Path = {pc: [sel], locals: new Map(), heap: new Map(heap), called: [], locks: [], defers: []}
    const bound = go.bindParams(fn, sel, p), args = bound.args, params = bound.params
    p = bound.p
    // The receiver.
    if (fn.recv?.id) p = g.bindLocal(fn.recv.id, fn.recv.ptr ? {t: 'ptr', to: {k: 'obj', id: 'this', path: []}} : {t: 'struct', ty: String(td.t), f: fields}, fn, p)
    const errAt = fn.results.length && go.T(fn.results.at(-1)!.t).k === 'error' ? fn.results.length - 1 : -1
    const kept = fn.results.filter((_, i) => i !== errAt)
    if (kept.length > 1) refuse(fn, `${fn.name} returns ${kept.length} values (a result kept is one value)`)
    const lowered = go.funcs[`${fn.recv?.type ?? ''}.${fn.name}`]!
    g.spans.set(`${opts.entry}.${fn.name}`, [fn.p.split(':')[0]!, fn.span[0], fn.span[1]])
    const flow = g.block(lowered.body, p)
    if (flow.brk?.length) refuse(fn, 'a break outside a switch')
    const rets: [Path, V[]][] = [...flow.rets.map(([q, v]) => [q, (v as {xs: V[]}).xs] as [Path, V[]]), ...(flow.live ? [[flow.live, []] as [Path, V[]]] : [])]
    // An error returned: a refusal (where it isn't nil), the state as it was there.
    const ok: [Path, V[]][] = []
    for (const [q0, vs] of rets) {
      const q = {...q0, locks: q0.locks.filter(k => !q0.defers.includes(k))}
      if (q.locks.length) refuse(fn, `${fn.name} returns with a mutex locked`)
      if (errAt >= 0) {
        const e = vs[errAt]
        const is = !e ? I.F : e.t === 'err' ? e.is : e.t === 'nil' ? I.F : refuse(fn, `${fn.name} returns an error of another kind`)
        g.refuseWhere(q, is, fn, 'an error returned')
        if (!(is.op === 'const' && is.v)) ok.push([g.assume(q, I.not(is)), vs])
      } else ok.push([q, vs])
    }
    if (!ok.length) refuse(fn, `${fn.name} always fails`)
    // The kept result: by the path that returned it (a local the join merges).
    const ri = fn.results.findIndex((_, i) => i !== errAt)
    const final = g.join(ok.map(([q, vs]) => (kept.length ? {...q, locals: new Map(q.locals).set('$ret', vs[ri]!)} : q)), fn)!, acc = final.locals.get('$ret')!
    let out: [string, Term] | undefined
    if (kept.length) {
      const s = go.scalar(fn.results[ri]!.t)
      if (typeof s === 'string') refuse(fn, `${fn.name} returns ${s}`)
      const x = g.newVar(`${fn.name}_result`, s as Var['sort'], 'state', `what ${fn.name} returned, at the step that called it (its default at others)`)
      outputs.push(x.name); results[fn.name] = {k: 'scalar', name: x.name}
      const it = go.intTy(fn.results[ri]!.t)
      if (it) g.ints.set(x.name, it)
      out = [x.name, termOf(acc, fn)]
    }
    finals.push({sel, ...materialize(go, final, fn), ...(out ? {out} : {})})
    events.push({select: {[ev.name]: fn.name}, call: fn.name, args})
    methods.push({name: fn.name, ptr: !!fn.recv?.ptr, params, results: fn.results.map(r => r.t), err: errAt >= 0})
  }
  // The lazy inputs' records: the fields read.
  const recOf = (a: Arg): Arg => (a.k === 'lazy' ? {k: 'rec', fields: (g.lazyIn.get(`in:${a.prefix}`)?.fields ?? []).map(([f, n]) => [f, {k: 'input', name: n} as Arg])} : a)
  for (const e of events) e.args = e.args.map(recOf)
  // (and the harness's: it makes the struct with the fields read)
  for (const mt of methods) mt.params = mt.params.map(pa => ({...pa, arg: recOf(pa.arg)}))
  // The methods together: each variable by the method called.
  const writes: Record<string, Term> = {}, init: Record<string, Term> = {}
  const leafVars = stateVars.filter(v => !g.lists.some(d => d.name === v.name) && !g.maps.some(d => d.name === v.name))
  for (const v of leafVars) {
    init[v.name] = v.sort.k === 'num' ? {s: 'num', e: I.num(0)} : v.sort.k === 'bool' ? {s: 'bool', e: v.name.endsWith('_nil') && go.leaves.some(l => l.name === v.name && (l.kind === 'bignil' || l.kind === 'mapnil')) ? I.T : I.F} : {s: 'str', e: {op: 'slit', value: ''}}
    let acc: Term | undefined
    for (let i = finals.length - 1; i >= 0; i--) {
      const t = finals[i]!.leaves.get(v.name) ?? varTerm(v)
      acc = acc === undefined ? t : iteTerm(finals[i]!.sel, t, acc)
    }
    if (acc && !I.same(acc.e, varTerm(v).e)) writes[v.name] = acc
  }
  for (const o of outputs) {
    const v = g.vars.get(o)!
    init[o] = v.sort.k === 'num' ? {s: 'num', e: I.num(0)} : v.sort.k === 'bool' ? {s: 'bool', e: I.F} : {s: 'str', e: {op: 'slit', value: ''}}
    let acc: Term = init[o]!
    for (let i = finals.length - 1; i >= 0; i--) acc = iteTerm(finals[i]!.sel, finals[i]!.out?.[0] === o ? finals[i]!.out![1] : init[o]!, acc)
    writes[o] = acc
  }
  const mapWrites: Model['mapWrites'] = {}
  for (const d of g.maps) { const w = mapWritesOf(g, d, finals.map(f => f.sel), finals.map(f => f.maps.get(d.name))); if (w) mapWrites[d.name] = w }
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
  for (const l of go.leaves) {
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
  for (const l of go.leaves) if (l.name && !state.some(v => v.name === l.name) && !maps.some(d => d.name === l.name) && !lists.some(d => d.name === l.name)) l.kind = 'frame'
  if (leftOut.length) g.notes.add(`left out (no method reads or writes them; the check asks the code not to change them): ${leftOut.join(', ')}`)
  for (const l of go.leaves) if (l.kind === 'frame' && !l.name) g.notes.add(`${l.path.join('.')}: a ${l.go}, outside the subset, left out (no method the rule reads touches it)`)
  // The laws every state of the code keeps: each fixed-width number within its type's range, a nil map holding no key.
  const laws = rangeLaws(state, g.ints)
  for (const l of go.leaves) if (l.kind === 'big' && state.some(v => v.name === l.name)) laws.push(`r.law(${JSON.stringify(`${l.name}: a nil one holds 0`)}, ({${l.name}, ${l.name}_nil}) => any(${l.name}_nil.not(), ${l.name}.eq(0)))`)
  for (const d of maps) laws.push(`r.law(${JSON.stringify(`${d.name}: a nil map holds no key`)}, ({${d.name}, ${d.name}_nil}) => forall(k => any(${d.name}_nil.not(), ${d.name}.at(k).has.not())))`)
  const layout: Layout = {k: 'rec', fields: state.filter(v => !outputs.includes(v.name)).map(v => [v.name, {k: 'scalar', name: v.name}] as [string, Layout])}
  const model: Model = {
    name: opts.entry, shape: 'class', file: pkg.files[0]?.name ?? 'go', entry: opts.entry,
    params: [], inputs: g.inputs, state, maps, init, writes, mapWrites, outputs, ...(lists.length ? {lists, listWrites} : {}),
    refuse: refuseB, pre: I.T, layout, events, notes: [...g.notes], hints: g.hints, event: ev.name, results, laws,
  }
  // Unsigned inputs are naturals (the input's kind); a state variable's sort is the printer's to decide (a natural where
  // every write is proven one: a wrap by cases may not be, though it stays within the type, which its law says).
  const unsigned = [...g.ints].filter(([n, ty]) => { const [lo, hi] = rangeOf(ty); return lo === 0 && hi > 0 && g.inputs.some(v => v.name === n) }).map(([n]) => n)
  return {model, edges: g.edges, unsigned, leaves: go.leaves.filter(l => l.kind === 'frame' || state.some(v => v.name === l.name) || maps.some(d => d.name === l.name) || lists.some(d => d.name === l.name)), spans: [...g.spans.values()], entry: opts.entry, methods}
}
function termOf(v: V, at: {p: string}): Term {
  if (v.t === 'num') return {s: 'num', e: v.e}
  if (v.t === 'bool') return {s: 'bool', e: v.e}
  if (v.t === 'str') return {s: 'str', e: v.e}
  return refuse(at, `a ${v.t} where the rule keeps a number, a boolean or a string`)
}
// The state at a method's end, leaf by leaf (and the maps' and lists' writes), checking that no object of the state
// is in two of its places.
function materialize(go: Go, p: Path, at: {p: string}): {leaves: Map<string, Term>, maps: Map<string, {key: K, has: B, vals: Record<string, Term>}>, lists: Map<string, ListOp[]>} {
  const g = go.g, leaves = new Map<string, Term>(), maps = new Map<string, {key: K, has: B, vals: Record<string, Term>}>(), lists = new Map<string, ListOp[]>()
  const self = p.heap.get('this') as Extract<StepObj, {k: 'rec'}>
  const seen = new Map<string, string>()
  for (const l of go.leaves) {
    if (l.kind === 'frame' || l.kind === 'bignil' || l.kind === 'mapnil') continue
    let v: V | undefined = {t: 'struct', ty: self.ty, f: self.f}
    for (const s of l.path) v = v?.t === 'struct' ? v.f.get(s) : undefined
    if (!v) continue
    if (l.kind === 'big') {
      if (v.t !== 'ptr' && v.t !== 'nil') refuse(at, `${l.path.join('.')} set to other than a *big.Int`)
      const cs = g.cases(v.t === 'nil' ? {k: 'nil'} : (v as {to: StepPtr}).to)
      let val: N | undefined
      for (const o of [...cs.objs].reverse()) {
        const obj = p.heap.get(o.id)
        if (obj?.k !== 'big') refuse(at, `${l.path.join('.')} points to other than a big.Int`)
        // One object in two places of the state, or one the caller gave: refused (the rule keeps a value per field).
        const prev = seen.get(o.id)
        if (prev && prev !== l.name) refuse(at, `${l.path.join('.')} and ${prev} may be one big.Int (one object in two places of the state)`)
        seen.set(o.id, l.name)
        if ((obj as {origin: string}).origin === 'input') refuse(at, `${l.path.join('.')} keeps the *big.Int the caller gave (the caller may change it after the call)`)
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
      const o = p.heap.get(v.id) as Extract<StepObj, {k: 'map'}>
      leaves.set(`${l.name}_nil`, {s: 'bool', e: o.nil!})
      if (o.w) maps.set(l.name, {key: o.w.key, has: o.w.has, vals: Object.fromEntries([...o.w.vals].map(([f, x]) => [f, termOf(x, at)]))})
      continue
    }
    if (l.kind === 'list') {
      if (v.t !== 'list') continue
      const o = p.heap.get(v.id) as Extract<StepObj, {k: 'list'}>
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
    try { read = readGo(pkg, opts) } catch (e) { if (e instanceof Refusal) capture({k: 'read', opts, pkg, refusal: {where: e.where, what: e.what}}); throw e }
    capture({k: 'read', opts, pkg, read})
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
// (gen/go-port: each reading's input, the reader's JSON, and its output appended to $GDP_GO_CAPTURE, for a differential
// test of the port that needs no Go)
function capture(x: Record<string, unknown>) {
  const f = proc?.env?.GDP_GO_CAPTURE
  if (f) node<{appendFileSync: (p: string, s: string) => void}>('node:fs').appendFileSync(f, `${JSON.stringify({...x, opts: x.opts ? {...(x.opts as object), check: undefined} : undefined})}\n`)
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
  const r = probe(pkg, name)
  capture({k: 'probe', pkg, name, out: r})
  return r
}
function probe(pkg: GoPkg, name: string): {where: string, what: string} {
  const go = new Go(pkg, {entry: ''}), fn = go.funcOf(name)
  if (!fn) return {where: pkg.files[0]?.name ?? '?', what: `${name}: not a function the package declares with a body`}
  try {
    if (fn.generic) refuse(fn, `${name}: a generic function`)
    const bound = go.bindParams(fn, I.T, {pc: [], locals: new Map(), heap: new Map(), called: [], locks: [], defers: []})
    go.g.block(go.funcs[`.${fn.name}`]!.body, bound.p)
  } catch (e) {
    if (e instanceof Refusal) return {where: e.where, what: e.what}
    throw e
  }
  const writes = fn.params.some(x => go.T(x.t).k === 'ptr')
  return {where: fn.p, what: `${name}: a function of its arguments${writes ? ' (the objects its pointers give are the caller\'s)' : ''}, not a step of a state the subset reads (a struct and its methods)`}
}
