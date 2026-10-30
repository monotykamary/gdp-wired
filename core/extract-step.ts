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
// The code's boundary, inferred unless `strict` (research/langs/DESIGN.md, "The boundary inferred"), each statement
// printed in the notes and enforced by the check; what the caller states wins:
//   answers: a call of other code whose result is an input of the request (the check stubs it with that input).
//            Inferred where its value is read, over its declared result type;
//   skip:    a call left out (logging, an alert, a context manager): its value is kept only where nothing the rule
//            keeps reads it, and the check runs it as it is. Inferred where nothing reads it;
//   stores:  an object of other code held as a key-value store (a cache client): its get and set methods read and
//            write a map of the state, one per key template; its expiry, eviction and replication are left out, and the
//            check gives the code a store that keeps what is set. Inferred for an injected dependency called by a key.
// Other code given a reference to the rule's state is refused unless stated; the module's own functions the subset
// can't read, writing none of the state, are taken as other code; `gdp: skip | answer [type] | strict` comments say
// it in the code.
import * as I from './extract-ir.ts'
import type {B, K, L, N} from './extract-ir.ts'
import {type Arg, type Event, type Layout, type MapDecl, type Model, Refusal, type Term, type Var, mergeOps, mergeWrites} from './extract-read.ts'
import {type Extraction, fromModel} from './extract.ts'
import type {Rule} from './dsl.ts'
import {type Sorts, nonneg} from './extract-print.ts'
import {type CodeSide, type Coverage, type Evidence, type Snap, Outside, constantsOf, draw, drive} from './extract-check.ts'

// --- the IR (what a reader emits) -----------------------------------------------------------------------------------
export type SType =
  | {k: 'int', bits?: number, signed?: boolean, unit?: string, atomic?: string, lock?: string, rs?: string} | {k: 'float' | 'bool' | 'str' | 'none' | 'any' | 'lock', atomic?: string, lock?: string}
  | {k: 'choice', values: string[], discs?: number[], enum?: string, sym?: boolean} | {k: 'opt', of: SType} | {k: 'res', of: SType}
  | {k: 'rec', name: string} | {k: 'map', key: SType, val: SType} | {k: 'list', of: SType} | {k: 'opaque', why: string}
// (store: a method of an injected dependency, stubbed on the object the check gives)
export type Patch = {mod?: string, path?: string[], self?: string, store?: string}
export type SX = {e: string, p: string, text?: string, [k: string]: unknown}
export type SS = {s: string, p: string, [k: string]: unknown}
// (inject: marked as an injected dependency by the language's own means, Spring's @Autowired, FastAPI's Depends)
export type SParam = {name: string, t: SType, dflt?: SX, kw?: boolean, self?: boolean, star?: number, inject?: boolean}
export type SFunc = {id: string, name: string, cls?: string, p: string, span: [string, number, number], params: SParam[], ret: SType, body: SS[], async?: boolean, static?: boolean, decorators: {name: string, text: string, p: string}[],
  // (a function inlined by id, Go's: its receiver's local, its results' count, why it can't be called: before the
  // recursion check, or after it)
  recv?: string, results?: number, why?: string, late?: string}
// (rets: the declared result types of its methods, another module's class's too: an inferred answer's type)
export type SRec = {name: string, short: string, fields: {name: string, t: SType, dflt?: SX, inject?: boolean}[], methods: Record<string, string | null>, kinds: string[], own: boolean, module: string, p: string, rets?: Record<string, SType>}
export type SModule = {lang: string, file: string, path: string, module: string, root: string, entries: ({k: 'class', rec: string} | {k: 'func', id: string} | {k: 'missing', name: string})[], recs: Record<string, SRec>, funcs: Record<string, SFunc>, enums?: Record<string, {values: string[], discs: number[], data: boolean}>, error?: string,
  // false: a condition the path takes is kept whole (a negated disjunction not split into its parts: Go's reader's);
  // 'nil-false': only nil and false are false (Ruby's), not Python's truthiness
  split?: boolean, truth?: 'nil-false',
  // false: the check can't stub a call (an answer, stated or inferred, is refused where it would be one)
  stubs?: boolean}

export type StoreDecl = {get?: string[], set?: string[], delete?: string[], value?: 'int' | 'float' | 'str', attrs?: Record<string, null | boolean | number | string>, async?: Record<string, boolean>}
export type StepOptions = {
  // The class, or the functions (each a request), and the methods read (by default the public ones). With no entry,
  // the module's one class whose public methods write its state, and those methods.
  entry?: string | string[], methods?: string[],
  answers?: Record<string, string>, skip?: string[], stores?: Record<string, StoreDecl>,
  // true: the boundary only as stated (answers, skip, stores), nothing inferred: any other call of other code refused
  strict?: boolean,
  // A failure (an exception, a panic) is the step's refusal (the default), or its result kept: the step taken, the
  // state as it was, `failed` true (to state laws about when the code refuses).
  failures?: 'refuse' | 'kept',
  onError?: 'refuse' | 'discard',
  domains?: Record<string, 'nat' | 'int'>,
  check?: {runs?: number, depth?: number, states?: number, seed?: number, bound?: number, probes?: boolean}
}

// --- values ---------------------------------------------------------------------------------------------------------
// An integer type's width (0: unbounded) and sign: where a number is one, its operations' overflow is the type's.
// (`name`: the type's name in the code, for the notes; `t`: the reader's own index of it)
// (`ub`: past its range is undefined behavior, C's and C++'s signed overflow: refused where it may be, never wrapped)
export type IntTy = {bits: number, signed: boolean, name?: string, t?: number, ub?: boolean}
// A number (with the comparison it is the sign of, x.Cmp(y); with the string it is the length of, read only against 0).
type V =
  | {t: 'num', e: N, ty?: IntTy, cmp?: [N, N], slen?: K} | {t: 'bool', e: B} | {t: 'str', e: K} | {t: 'choice', e: L}
  | {t: 'none'} | {t: 'opt', has: B, v: V}
  | {t: 'ref', id: string} | {t: 'cell', map: string, key: K}
  // A string made by a format with one hole (a store's key): its template and the hole's value.
  | {t: 'fmt', tpl: string, k: K}
  // (firm: a value merged only with itself, refused where a path would make it another; Go's)
  // (ask: the value of a call of other code left out by inference, answered by the next run where it is read)
  | {t: 'opaque', why: string, firm?: boolean, ask?: string, sattr?: {store: string, path: string}}
  // (ret: the callee's declared result type; recv: the object its method is called on)
  | {t: 'ext', q: string, text: string, patch?: Patch, ret?: SType, recv?: V}
  | {t: 'fn', id: string, self?: V, caps?: Map<string, V>} | {t: 'cls', rec: string, patch?: Patch} | {t: 'builtin', n: string} | {t: 'lib', q: string}
  | {t: 'sattr', store: string, path: string}
  | {t: 'tuple', xs: V[]} | {t: 'lock'}
  // A Result: Ok(v) where ok holds, Err(e) where it doesn't.
  | {t: 'res', ok: B, v: V, e: V}
  // A pointer by cases; a record by value; an error value (nil or not); nil; a map or a list of the heap, a list with an
  // item pushed or popped (put back only in its own place).
  | {t: 'ptr', to: Ptr} | {t: 'struct', ty: string, f: Map<string, V>} | {t: 'err', is: B} | {t: 'nil'}
  | {t: 'map', id: string} | {t: 'list', id: string} | {t: 'push', id: string, x: V} | {t: 'pop', id: string}
type Ptr = {k: 'nil'} | {k: 'obj', id: string, path: string[]} | {k: 'phi', c: B, a: Ptr, b: Ptr}
type ListOp = {op: 'push', x: V, when: B} | {op: 'pop', when: B} | {op: 'set', i: N, x: V, when: B}
type Place = {k: 'local', id: string, path: string[]} | {k: 'heap', ptr: V, path: string[]} | {k: 'blank'}
// How a field of a record the caller gives is made where it is first read.
export type Recipe = {k: 'num' | 'bool' | 'str', ty?: IntTy} | {k: 'big'} | {k: 'no', why: string}
type Origin = 'state' | 'input' | 'fresh'
type Obj =
  | {k: 'rec', ty: string, f: Map<string, V>, origin: Origin, lazy?: string, moved?: boolean}
  | {k: 'map', decl: MapDecl, val?: SType, nil?: B, w?: {key: K, has: B, vals: Map<string, V>}, origin: Origin}
  | {k: 'store', name: string}
  | {k: 'big', v: N, origin: Origin} | {k: 'list', decl: MapDecl, ops: ListOp[], origin: Origin}
// (locks held, and those deferred to the return)
type Path = {pc: B[], locals: Map<string, V>, heap: Map<string, Obj>, called: string[], locks: string[], defers: string[]}
type Flow = {live?: Path, rets: [Path, V][], brk?: Path[], ft?: Path}
export type {V as StepValue, Path as StepPath, Obj as StepObj, Ptr as StepPtr}
// What the harness is told: where each leaf of the state is, how each argument is made, what each stub answers.
export type Leaf = {t?: SType, name: string, path: string[], kind: 'num' | 'bool' | 'str' | 'choice' | 'none' | 'map' | 'frame', float?: boolean, cls?: string, fields?: {name: string, float?: boolean}[], key?: 'num' | 'str', store?: string, tpl?: string}
export type PArg = {k: 'in', name: string, float?: boolean, sym?: boolean, z?: Raw} | {k: 'opt', none: string, v: PArg} | {k: 'rec', cls: string, f: [string, PArg][]} | {k: 'inert'} | {k: 'store', name: string} | {k: 'dflt'}
// (how: 'inferred' from the callee's declared type, or 'tagged' by a gdp: comment; stated where absent)
// (at: the calls answered, each from its position to its end, `line:col`; ty: the call's type in the code's language)
export type Answer = {key: string, patch: Patch, async: boolean, inputs: {name: string, none?: string, float?: boolean}, sort: string, how?: string, at?: {p: string, end?: string, span?: [number, number]}[], ty?: string}
// (inject: the fields the harness sets to the store it gives, after the constructor: a field injected by a framework)
export type StepRead = {ints: Record<string, IntTy>, madeAt?: string, model: Model, leaves: Leaf[], args: Record<string, [string, PArg][]>, answers: Answer[], ctor: [string, PArg][], kept: boolean, arms: [string, number][], cls?: string, stores: Record<string, StoreDecl>, results: Record<string, 'none' | 'scalar' | 'maybe'>, inject?: string[]}

const where = (x: {p: string}) => x.p || '?'
const refuse = (x: {p: string} | string, what: string): never => { throw new Refusal(typeof x === 'string' ? x : where(x), what) }
const RESERVED = new Set(['rule', 'nat', 'int', 'bool', 'when', 'min', 'max', 'all', 'any', 'not', 'yes', 'no', 'lit', 'str', 'record', 'oneOf', 'intern', 'Int', 'forall'])
const keyV = (v: V | Obj): string => JSON.stringify(v, (_, x) => (x instanceof Map ? [...x.entries()] : x))
const LANG: Record<string, string> = {go: 'Go', rust: 'Rust', python: 'Python', c: 'C', cpp: 'C++', ruby: 'Ruby', elixir: 'Elixir', java: 'Java', kotlin: 'Kotlin'}
const tyName = (ty?: IntTy) => (ty ? (ty.bits ? `${ty.signed ? 'i' : 'u'}${ty.bits}` : ty.signed ? 'an Instant' : 'a Duration') : 'the number')
const constOf = (v: V): number | undefined => (v.t === 'num' && v.e.op === 'const' ? v.e.v : undefined)

// The sorts a type string names (an answer's): int, float, bool, str, a choice of quoted strings, each `| None`.
function sortOfText(s: string, at: string): {t: SType} {
  const parts = s.split('|').map(x => x.trim()).filter(Boolean), none = parts.includes('None'), rest = parts.filter(x => x !== 'None')
  const one = (): SType => {
    if (rest.length && rest.every(x => /^['"].*['"]$/.test(x))) return {k: 'choice', values: rest.map(x => x.slice(1, -1))}
    if (rest.length !== 1) return refuse(at, `the answer type ${JSON.stringify(s)} (int, float, bool, str or quoted strings, each with | None)`)
    const k = rest[0]!
    if (k === 'int' || k === 'float' || k === 'bool' || k === 'str') return {k}
    // (a fixed width, a compiled language's: u32, i64, usize, uint8, int32)
    const w = /^(u|i|uint|int)(8|16|32|64|128|size)$/.exec(k)
    if (w) return {k: 'int', bits: w[2] === 'size' ? 64 : Number(w[2]), signed: !w[1]!.startsWith('u')}
    return refuse(at, `the answer type ${JSON.stringify(s)} (int, float, bool, str or quoted strings, each with | None)`)
  }
  const t = one()
  return {t: none ? {k: 'opt', of: t} : t}
}

// --- the boundary inferred (types) ---------------------------------------------------------------------------------
// What a reading infers over its runs: the calls answered (their value read) and the module's own functions cut
// (their bodies outside the subset, writing none of the rule's state). Each refused run adds one, until a run reads.
export type Inferred = {answers: Map<string, SType>, cut: Map<string, string>}
type Tag = {k: 'skip' | 'answer' | 'strict', arg: string}
const TAG_DECO = /(?:^|\.)gdp[._]?(skip|answer|strict)$/i
// A call at the boundary: its key (an answer's input is named after its last part), what it is, its patch for the
// check, its declared result, the module's own function it is (cut), its object, its tag, and the refusal it was.
type Bound = {key: string, name: string, patch?: Patch, ret?: SType, own?: string, recv?: V, tag?: Tag, refusal: string, args?: false}
type Pend = Bound & {why: string, at: string, end?: string}
// A refusal as it leaves each function inlined: the function and its parameters holding the rule's state.
type Framed = Refusal & {frames?: {id: string, roots: string[]}[]}
// A type an answer takes: a scalar, or one with None.
const answerable = (t: SType): boolean => { const i = t.k === 'opt' ? t.of : t; return i.k === 'int' || i.k === 'float' || i.k === 'bool' || i.k === 'str' || i.k === 'choice' }
const typeText = (t: SType): string => (t.k === 'opt' ? `${typeText(t.of)} | None` : t.k === 'choice' ? t.values.map(v => JSON.stringify(v)).join(' | ') : t.k)
// A store's method by its name: one that reads, writes or deletes a key (async_, _cache and camel case aside).
const KEYED: Record<string, 'get' | 'set' | 'delete'> = Object.fromEntries([
  ...['get', 'getcache', 'find', 'findbyid', 'fetch', 'load', 'lookup', 'read'].map(n => [n, 'get']),
  ...['set', 'setcache', 'put', 'save', 'store', 'write', 'upsert'].map(n => [n, 'set']),
  ...['delete', 'deletecache', 'remove', 'deletebyid', 'del', 'evict', 'invalidate'].map(n => [n, 'delete'])])
const keyShape = (m: string): 'get' | 'set' | 'delete' | undefined => KEYED[m.replace(/^async_?|_?async$/gi, '').replace(/[_-]/g, '').toLowerCase()]

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
  // Each fixed-width variable's type (a number read from it overflows as the type does), and its range.
  readonly ints = new Map<string, IntTy>()
  readonly paramsOut: B[] = []
  now?: Var
  madeAt?: Var
  method = ''
  fresh = 0
  init = false
  // (inf: the boundary inferred so far, where the reading infers one; none: only what the caller states)
  constructor(readonly mod: SModule, readonly opts: StepOptions, readonly inf?: Inferred) {}

  rec(name: string, at: {p: string}): SRec { return this.mod.recs[name] ?? refuse(at, `${name}: a type the reader didn't read`) }
  newVar(name: string, sort: Var['sort'], role: Var['role'], note?: string): Var {
    let n = name.replace(/^[_@]+/, '').replace(/\?/g, '_p').replace(/!/g, '').replace(/[^\w$]/g, '_') || 'x'
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
    const ty = this.ints.get(v.name)
    return v.sort.k === 'num' ? {t: 'num', e: I.nvar(v.name), ...(ty ? {ty} : {})} : v.sort.k === 'bool' ? {t: 'bool', e: I.bvar(v.name)} : v.sort.k === 'choice' ? {t: 'choice', e: {op: 'var', name: v.name, values: v.sort.values}} : {t: 'str', e: {op: 'svar', name: v.name}}
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
    if (s) { const v = this.newVar(name, s, role); this.typed(v, t, role); return [this.valueOf(v), {k: 'in', name: v.name, z: zeroRaw(s), ...(t.k === 'float' ? {float: true} : {}), ...(t.k === 'choice' && t.sym ? {sym: true} : {})}] }
    if (t.k === 'opt') {
      if (t.of.k === 'rec') {
        const none = this.newVar(`${name}_none`, {k: 'bool'}, role, `whether ${name} is None`)
        const [v, a] = this.input(name, t.of, at, p, role)
        return [{t: 'opt', has: I.not(I.bvar(none.name)), v}, {k: 'opt', none: none.name, v: a}]
      }
      const inner = this.scalar(t.of)
      if (!inner) return refuse(at, `${name}: an optional ${this.why(t.of)}`)
      const v = this.newVar(name, inner, role, `0 where ${name} is None`), none = this.newVar(`${name}_none`, {k: 'bool'}, role, `whether ${name} is None`)
      this.typed(v, t.of, role)
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
  // A fixed-width integer variable: its type, and (for a request) a value outside it refused: the claim is for the
  // type's values.
  intTy(t: SType): IntTy | undefined { return t.k === 'int' && t.bits !== undefined ? {bits: t.bits, signed: t.signed ?? true} : undefined }
  typed(v: Var, t: SType | IntTy, role: Var['role'], sel = this.sel) {
    const ty = 'k' in t ? this.intTy(t) : t
    if (!ty) return
    this.ints.set(v.name, ty)
    const [lo, hi] = rangeOf(ty)
    if (role === 'state') return
    const x = I.nvar(v.name)
    // (a constructor's argument outside its type: no object is made with one, the rule's precondition says so)
    if (role === 'param') { const out = I.or(...(Number.isFinite(lo) ? [I.cmp('<', x, I.num(lo))] : []), ...(Number.isFinite(hi) ? [I.cmp('<', I.num(hi), x)] : [])); if (!(out.op === 'const' && !out.v)) this.paramsOut.push(out); return }
    if (Number.isFinite(hi)) this.refusals.push(I.and(sel, I.cmp('<', I.num(hi), x)))
    if (Number.isFinite(lo) && lo < 0) this.refusals.push(I.and(sel, I.cmp('<', x, I.num(lo))))
    else if (!ty.signed) this.refusals.push(I.and(sel, I.cmp('<', x, I.num(0))))
  }
  sel: B = I.T
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
  assume(p: Path, c: B): Path { if (this.mod.split === false) return c.op === 'const' && c.v ? p : {...p, pc: [...p.pc, c]}; const cs = c.op === 'not' && c.x.op === 'or' ? c.x.xs.map(I.not) : c.op === 'and' ? c.xs : [c]; const kept = cs.filter(x => !(x.op === 'const' && x.v)); return kept.length ? {...p, pc: [...p.pc, ...kept]} : p }
  // A failure of the code where c holds on this path (an exception raised): the step's refusal, or its result.
  fail(p: Path, c: B, at: {p: string}, what: string) {
    const w = I.and(this.cond(p), c)
    if (w.op === 'const' && !w.v) return
    if (this.init) { this.fails.push(w); return }
    // Failures kept with what the step wrote before them (the caller sees both): the path goes on to the step's end.
    if (this.opts.failures === 'kept' && this.opts.onError !== 'discard') { this.failPaths.push(this.assume(p, c)); this.fails.push(w); this.notes.add(`${this.method}: ${what} (${at.p}) is the step's failure, kept as its result (with what the step wrote before it)`); return }
    this.unwritten(p, at, what)
    this.fails.push(w)
    this.notes.add(`${this.method}: ${what} (${at.p}) is ${this.opts.failures === 'kept' ? 'the step\'s failure, kept as its result' : 'the step\'s refusal'}`)
  }
  // A failure after the step wrote the state: refused, but where the caller drops what a failed call wrote.
  unwritten(p: Path, at: {p: string}, what: string) { if (this.opts.onError !== 'discard' && this.changed(p)) refuse(at, `${what} after the state is written (the caller would see the object changed and the call failed; with onError: 'discard' the caller is taken to drop what a failed call wrote)`) }
  changed(p: Path): boolean {
    for (const [id, o] of p.heap) {
      const i = this.initHeap.get(id)
      if (!i || ('origin' in o && o.origin !== 'state')) continue
      if (o.k === 'map' ? !!o.w || (!!o.nil && I.keyOf(o.nil) !== I.keyOf((i as typeof o).nil!)) : o.k === 'list' ? o.ops.length > 0 : keyV(o) !== keyV(i)) return true
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
    if (a.locks.join() !== b.locks.join()) refuse(at, 'a mutex locked on one path and not on another')
    const locals = new Map<string, V>()
    for (const [n, x] of a.locals) { const y = b.locals.get(n); if (y) { try { locals.set(n, this.ite(c, x, y, at)) } catch (e) { if (!(e instanceof Refusal) || firm(x) || firm(y)) throw e; locals.set(n, {t: 'opaque', why: e.what}) } } }
    const heap = new Map<string, Obj>()
    for (const [id, x] of a.heap) { const y = b.heap.get(id); heap.set(id, y ? this.mergeObj(c, x, y, at) : x) }
    for (const [id, y] of b.heap) if (!heap.has(id)) heap.set(id, y)
    return {pc, locals, heap, called: [...new Set([...a.called, ...b.called])], locks: a.locks, defers: [...new Set([...a.defers, ...b.defers])]}
  }
  mergeObj(c: B, a: Obj, b: Obj, at: {p: string}): Obj {
    if (a === b) return a
    if (a.k === 'big' && b.k === 'big') return {...a, v: I.nite(c, a.v, b.v)}
    if (a.k === 'rec' && b.k === 'rec') {
      const f = new Map<string, V>()
      for (const [n, x] of a.f) { const y = b.f.get(n); f.set(n, y ? this.ite(c, x, y, at) : x) }
      for (const [n, y] of b.f) if (!f.has(n)) f.set(n, y)
      return {...a, f, moved: a.moved || b.moved}
    }
    if (a.k === 'map' && b.k === 'map') {
      const w = mergeWrites(c, a.w, b.w, key => this.baseCell(a.decl, key), (c2, x, y) => this.ite(c2, x, y, at))
      return {...a, ...(a.nil ? {nil: I.bite(c, a.nil, b.nil!)} : {}), ...(w ? {w} : {})}
    }
    if (a.k === 'list' && b.k === 'list') return {...a, ops: mergeOps(c, a.ops, b.ops)}
    if (a.k === 'store' && b.k === 'store') return a
    return refuse(at, 'an object of two kinds by a condition')
  }
  // A value by cases.
  ite(c: B, a: V, b: V, at: {p: string}): V {
    if (c.op === 'const') return c.v ? a : b
    if (a === b) return a
    // (a number keeps its type)
    if (a.t === 'num' && b.t === 'num') return {t: 'num', e: I.nite(c, a.e, b.e), ...(a.ty ? {ty: a.ty} : {})}
    if (firm(a) || firm(b)) return this.iteFirm(c, a, b, at)
    if (keyV(a) === keyV(b)) return a
    if (a.t === 'opaque') return a
    if (b.t === 'opaque') return b
    if (a.t === 'bool' && b.t === 'bool') return {t: 'bool', e: I.bite(c, a.e, b.e)}
    if (a.t === 'str' && b.t === 'str') return {t: 'str', e: I.kite(c, a.e, b.e)}
    if (a.t === 'choice' && b.t === 'choice') return {t: 'choice', e: I.lite(c, a.e, b.e)}
    if (a.t === 'choice' && b.t === 'str' && b.e.op === 'slit') return this.ite(c, a, {t: 'choice', e: I.llit(b.e.value, lvalues(a.e))}, at)
    if (b.t === 'choice' && a.t === 'str' && a.e.op === 'slit') return this.ite(c, {t: 'choice', e: I.llit(a.e.value, lvalues(b.e))}, b, at)
    if (a.t === 'none' && b.t === 'none') return a
    if (a.t === 'none') return b.t === 'opt' ? {t: 'opt', has: I.and(I.not(c), b.has), v: b.v} : {t: 'opt', has: I.not(c), v: b}
    if (b.t === 'none') return a.t === 'opt' ? {t: 'opt', has: I.and(c, a.has), v: a.v} : {t: 'opt', has: c, v: a}
    if (a.t === 'opt' || b.t === 'opt') {
      const oa = a.t === 'opt' ? a : {has: I.T, v: a}, ob = b.t === 'opt' ? b : {has: I.T, v: b}
      return {t: 'opt', has: I.bite(c, oa.has, ob.has), v: this.ite(c, oa.v, ob.v, at)}
    }
    if (a.t === 'res' && b.t === 'res') {
      // (an Err's value, and an Ok's error, are no value: the other side's is taken)
      const no = (x: B) => x.op === 'const' && !x.v, yes = (x: B) => x.op === 'const' && x.v
      return {t: 'res', ok: I.bite(c, a.ok, b.ok), v: no(a.ok) ? b.v : no(b.ok) ? a.v : this.ite(c, a.v, b.v, at), e: yes(a.ok) ? b.e : yes(b.ok) ? a.e : this.ite(c, a.e, b.e, at)}
    }
    if (a.t === 'tuple' && b.t === 'tuple' && a.xs.length === b.xs.length) return {t: 'tuple', xs: a.xs.map((x, i) => this.ite(c, x, b.xs[i]!, at))}
    if (a.t === 'ref' && b.t === 'ref') return refuse(at, 'one of two objects by a condition')
    return refuse(at, `a value that is a ${a.t} on one path and a ${b.t} on another`)
  }
  // Pointers, records by value, error values, nil, maps and lists: Go's merge (a firm value with another refused).
  iteFirm(c: B, a: V, b: V, at: {p: string}): V {
    if (a.t === 'err' && b.t === 'err') return {t: 'err', is: I.bite(c, a.is, b.is)}
    const asPtr = (v: V): Ptr | undefined => (v.t === 'ptr' ? v.to : v.t === 'nil' ? {k: 'nil'} : undefined)
    if ((a.t === 'ptr' || a.t === 'nil') && (b.t === 'ptr' || b.t === 'nil')) return {t: 'ptr', to: phiP(c, asPtr(a)!, asPtr(b)!)}
    if ((a.t === 'err' && b.t === 'nil') || (a.t === 'nil' && b.t === 'err')) return {t: 'err', is: I.bite(c, a.t === 'err' ? a.is : I.F, b.t === 'err' ? b.is : I.F)}
    if (a.t === 'struct' && b.t === 'struct') { const f = new Map<string, V>(); for (const [n, x] of a.f) f.set(n, this.ite(c, x, b.f.get(n)!, at)); return {t: 'struct', ty: a.ty, f} }
    if ((a.t === 'map' && b.t === 'map') || (a.t === 'list' && b.t === 'list')) { if (a.id === b.id) return a; return refuse(at, 'one of two maps or slices by a condition') }
    if (a.t === 'opaque' && b.t === 'opaque' && a.why === b.why) return a
    if (keyV(a) === keyV(b)) return a
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
    if (this.mod.truth === 'nil-false') return v.t === 'bool' ? v.e : v.t === 'none' ? I.F : v.t === 'opt' ? I.and(v.has, this.truthy(v.v, at, p)) : v.t === 'opaque' ? refuse(at, `${(at as SX).text ?? ''}: the truth of ${v.why}`) : I.T
    switch (v.t) {
      case 'bool': return v.e
      case 'num': return I.not(I.cmp('=', v.e, I.num(0)))
      case 'str': return I.not(I.keq(v.e, {op: 'slit', value: ''}))
      case 'choice': return lvalues(v.e).includes('') ? I.not(I.is(v.e, '')) : I.T
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
      case 'builtin': case 'ext': case 'lib': case 'opaque': case 'sattr': case 'tuple': case 'res': case 'ptr': case 'struct': case 'err': case 'nil': case 'map': case 'list': case 'push': case 'pop': break
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
  callFunc(f: SFunc, self: V | undefined, args: V[], kw: [string, V][], at: SX, p0: Path, awaited: boolean, caps?: Map<string, V>): [V, Path] {
    if (f.async && !awaited) return refuse(at, `${f.name}: a coroutine made and not awaited`)
    if (this.frames.includes(f.id)) return refuse(at, `${f.name}: a recursive call`)
    for (const d of f.decorators) {
      if (['staticmethod', 'classmethod', 'property', 'override', 'typing.override', 'abstractmethod'].includes(d.name) || (this.inf && TAG_DECO.test(d.name))) continue
      if (this.skipped([d.name, d.text])) this.notes.add(`@${d.text} on ${f.name}: taken as transparent (skip)`)
      else if (this.inf && this.tagAt(d.p)?.k !== 'strict') this.notes.add(`@${d.text} on ${f.name}: taken as transparent (inferred: the check runs the method as decorated)`)
      else refuse(d, `@${d.text}: a decorator (one of other code changes what the method does; skip it to take it as transparent)`)
    }
    this.arm(f.body)
    const locals = new Map<string, V>()
    const ps = f.params.filter(x => !x.star)
    let i = 0, q = p0
    for (const pa of ps) {
      let v: V | undefined
      if ((pa as {cap?: boolean}).cap) v = caps?.get(pa.name) ?? refuse(at, `${f.name}: ${pa.name} not captured`)
      else if (pa.self && !f.static) v = self ?? (i < args.length ? args[i++] : refuse(at, `${f.name}: a method called without its object`))
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
    try { flow = this.block(f.body, {...q, locals}) } catch (e) {
      if (e instanceof Refusal && this.inf) ((e as Framed).frames ??= []).push({id: f.id, roots: [...locals].filter(([, v]) => this.stateRef(v, q)).map(([n]) => n)})
      throw e
    } finally { this.frames.pop() }
    const rets: [Path, V][] = [...flow.rets, ...(flow.live ? [[flow.live, {t: 'none'} as V] as [Path, V]] : [])]
    if (!rets.length) return [{t: 'none'}, {...q, pc: [...q.pc, I.F], locals: saved}]
    const joined = this.join(rets.map(([r, v]) => ({...r, locals: new Map([['$ret', v]])})), at)!
    return [joined.locals.get('$ret')!, {...joined, locals: saved}]
  }

  // A branch arm the step runs: its first statement's line, counted by the harness's line events.
  arm(ss: SS[]) { const s0 = ss.find(x => x.s !== 'import' && !/:0:\d+$/.test(x.p)); if (s0) { const m = /^(.*):(\d+):\d+$/.exec(s0.p); if (m) this.arms.add(`${m[1]}:${m[2]}`) } }
  // --- statements -----------------------------------------------------------------------------------------------------
  block(ss: SS[], p: Path): Flow {
    let live: Path | undefined = p, ft: Path | undefined
    const rets: [Path, V][] = [], brk: Path[] = []
    for (const s of ss) {
      if (!live) break
      if (s.s === 'fallthrough') { ft = live; live = undefined; break }
      const f = this.stmt(s, live)
      rets.push(...f.rets)
      if (f.brk) brk.push(...f.brk)
      live = f.live
    }
    return {...(live ? {live} : {}), rets, ...(brk.length ? {brk} : {}), ...(ft ? {ft} : {})}
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
        const c = s.strict ? (cv.t === 'bool' ? cv.e : refuse({p: s.cp as string}, s.strict as string)) : this.truthy(cv, s.c as SX, q)
        if (!(c.op === 'const' && !c.v)) this.arm(s.then as SS[])
        if (!(c.op === 'const' && c.v)) this.arm(s.else as SS[])
        const t = c.op === 'const' && !c.v ? undefined : this.block(s.then as SS[], this.assume(q, c))
        const e = c.op === 'const' && c.v ? undefined : this.block(s.else as SS[], this.assume(q, I.not(c)))
        const lives = [t?.live, e?.live].filter((x): x is Path => !!x)
        const live = this.join(lives, s), brk = [...(t?.brk ?? []), ...(e?.brk ?? [])]
        return {...(live ? {live} : {}), rets: [...(t?.rets ?? []), ...(e?.rets ?? [])], ...(brk.length ? {brk} : {})}
      }
      case 'ret': {
        if (s.xs || s.one || s.bare) {
          // (Go's: each result, one call's several, or the named results)
          let vs: V[] = [], q = p
          if (s.one) { const [v, q2] = this.ev(s.one as SX, q); if (v.t !== 'tuple') return refuse(s, String(s.why)); vs = v.xs; q = q2 }
          else if (s.bare) for (const id of s.bare as (string | null)[]) vs.push((id ? q.locals.get(id) : undefined) ?? refuse(s, 'a bare return of an unnamed result'))
          else for (const e of s.xs as SX[]) { const [v, q2] = this.ev(e, q); vs.push(v); q = q2 }
          return {rets: [[q, {t: 'tuple', xs: vs}]]}
        }
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
          if (v.t === 'opaque' && v.ask) { this.notes.add(`with ${it.x.text} (${it.x.p}): a context manager of other code taken as transparent (inferred: the check runs it)`); continue }
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
        for (const [n, x] of Object.entries(s.names as Record<string, {mod: string, name?: string, ret?: SType}>)) locals.set(n, {t: 'ext', q: x.name ? `${x.mod}.${x.name}` : x.mod, text: n, patch: {mod: x.mod, ...(x.name ? {path: [x.name]} : {})}, ...(x.ret ? {ret: x.ret} : {})})
        return {live: {...p, locals}, rets: []}
      }
      case 'no': return refuse(s, String(s.why))
      case 'panic': { let q = p; for (const a of s.args as SX[]) q = this.ev(a, q)[1]; this.refuseWhere(q, I.T, s, (s.what as string | undefined) ?? 'a panic'); return {rets: []} }
      case 'incdec': {
        const [pl, q] = this.place(s.to as SX, p), [v, q2] = this.read(pl, s, q)
        if (v.t !== 'num') return refuse(s, `${s.op as string} of a ${v.t}`)
        return {live: this.write(pl, this.arith(s.op === '++' ? '+' : '-', v, {t: 'num', e: I.num(1), ty: v.ty}, s, q2), s, q2), rets: []}
      }
      case 'opset': { const [pl, q] = this.place(s.to as SX, p), [x, q2] = this.read(pl, s, q), [y, q3] = this.ev(s.y as SX, q2); return {live: this.write(pl, this.binop(String(s.op), x, y, s, q3), s, q3), rets: []} }
      case 'mopset': { const at = s.at as SX, [m, q] = this.ev(at.m as SX, p), [k, q2] = this.ev(at.k as SX, q), cell = this.mapRead(m, k, at, q2), [y, q3] = this.ev(s.y as SX, q2); return {live: this.mapWrite(m, k, this.binop(String(s.op), cell.v, y, s, q3), at, q3), rets: []} }
      case 'assign': return {live: this.assignGo(s, p), rets: []}
      case 'switch': return this.switchGo(s, p)
      case 'break': return {rets: [], brk: [p]}
      case 'defer': { const key = this.lockKey(s.pl as SX, p); if (!p.locks.includes(key)) refuse(s, `defer ${s.text as string} without its Lock first`); return {live: {...p, defers: [...p.defers, key]}, rets: []} }
    }
    return refuse(s, `a statement the subset doesn't read (${s.s})`)
  }
  // An assignment: to a local, to a field of an object, to a dict's item, or to a tuple of those.
  assign(to: SX, v: V, at: {p: string}, p: Path, t?: SType): Path {
    if (to.e === 'lock' || to.e === 'ref') return this.assign(to.x as SX, v, at, p, t)
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
    // (a literal written to a field of a choice is the choice's)
    const ft = this.declared.get(`${o.id}.${f}`) ?? this.mod.recs[obj.ty]?.fields.find(x => x.name === f)?.t, ct = ft?.k === 'opt' ? ft.of : ft
    if (ct?.k === 'choice' && v.t === 'str' && v.e.op === 'slit' && ct.values.includes(v.e.value)) v = {t: 'choice', e: I.llit(v.e.value, ct.values)}
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
    return this.writeCell(id, o, k, I.F, new Map([...c.vals].map(([f, v]) => [f, (v.t === 'num' ? {t: 'num', e: I.num(0)} : v.t === 'bool' ? {t: 'bool', e: I.F} : v.t === 'choice' ? {t: 'choice', e: I.llit(lvalues(v.e)[0]!, lvalues(v.e))} : v) as V])), at, strict ? this.assume(p, c.has) : p)
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
      const decl = this.storeDecl(store)
      const val: SType = decl.value === 'int' ? {k: 'int'} : decl.value === 'str' ? {k: 'str'} : {k: 'float'}
      const name = `${store}_${tpl.replace(/\{\}/g, '').replace(/[^A-Za-z0-9]+/g, '_').replace(/^_|_$/g, '')}`
      const d = this.mapDeclOf(name, {k: 'map', key: {k: kn ? 'int' : 'str'}, val}, at)
      const id = `store:${key}`
      sm = {store, tpl, id, decl: d}
      this.storeMaps.set(key, sm)
      this.initHeap.set(id, {k: 'map', decl: d, val, origin: 'state'})
      this.notes.add(`${store}: a store (${this.opts.stores?.[store] ? 'stated' : 'inferred: an injected dependency, read and written by a key'}): ${JSON.stringify(tpl)} keys held as ${d.name}, its expiry and eviction left out`)
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
  // A store's declaration: the caller's, with the methods inference reads as its get, set and delete added.
  readonly storeDecls = new Map<string, StoreDecl>()
  // (an injected dependency's type: its methods' declared results)
  readonly storeTypes = new Map<string, string>()
  // (the stores whose keys the rule holds: stated, or an injected dependency the class calls a key's method on)
  readonly storeKeyed = new Set<string>()
  readonly injectedFields: string[] = []
  // A constructor argument held as an injected dependency (a store): one its reader marks so, or one of no scalar type
  // (another module's class, a protocol, none stated) the class keeps in a field and calls methods on.
  injected(pa: SParam, init: SFunc, r: SRec): {keyed: boolean, ty?: string} | undefined {
    if (!this.inf) return undefined
    const t = pa.t.k === 'opt' ? pa.t.of : pa.t
    if (!pa.inject && (this.scalar(t) || ['lock', 'none', 'map', 'list'].includes(t.k) || (t.k === 'rec' && this.mod.recs[t.name]?.own && !this.mod.recs[t.name]!.kinds.includes('protocol')) || pa.dflt)) return undefined
    const fields: string[] = []
    const scan = (x: unknown) => { if (!x || typeof x !== 'object') return; const st = x as SS, to = st.to as SX | undefined, v = st.x as SX | undefined; if (st.s === 'set' && to?.e === 'get' && (to.x as SX).e === 'var' && (to.x as SX).n === 'self' && v?.e === 'var' && v.n === pa.name) fields.push(String(to.f)); Object.values(x).forEach(scan) }
    scan(init.body)
    const ms = this.callsOn(r, fields)
    if (!pa.inject && !ms.length) return undefined
    return {keyed: ms.some(m => !!keyShape(m)), ...(t.k === 'rec' ? {ty: t.name} : {})}
  }
  // The methods the class's code calls on its fields named (self.f.m(...)).
  callsOn(r: SRec, fields: string[]): string[] {
    const ms: string[] = []
    const walk = (x: unknown) => { if (!x || typeof x !== 'object') return; const o = x as SX, f = o.f as SX | undefined, fx = f?.x as SX | undefined; if (o.e === 'call' && f?.e === 'get' && fx?.e === 'get' && (fx.x as SX).e === 'var' && (fx.x as SX).n === 'self' && fields.includes(String(fx.f))) ms.push(String(f.f)); Object.values(o).forEach(walk) }
    for (const id of Object.values(r.methods)) if (id && this.mod.funcs[id]) walk(this.mod.funcs[id]!.body)
    return ms
  }
  storeDecl(store: string): StoreDecl {
    let d = this.storeDecls.get(store)
    if (!d) { d = {...this.opts.stores?.[store]}; this.storeDecls.set(store, d) }
    return d
  }
  storeCall(store: string, m: string, args: V[], kw: [string, V][], at: SX, p: Path, awaited: boolean): [V, Path] {
    const d = this.storeDecl(store)
    const arg = (n: string, i: number) => kw.find(([k]) => k === n)?.[1] ?? args[i] ?? refuse(at, `${at.text}: the store's ${n} not given`)
    const has = (n: string, i: number) => kw.some(([k]) => k === n) || args.length > i
    let kind: 'get' | 'set' | 'delete' | undefined = (d.get ?? ['get', 'async_get_cache', 'get_cache']).includes(m) ? 'get' : (d.set ?? ['set', 'async_set_cache', 'set_cache']).includes(m) ? 'set' : (d.delete ?? ['delete', 'delete_cache', 'async_delete_cache']).includes(m) ? 'delete' : undefined
    if (!kind && this.inf) {
      // (inferred: a method named as a key's get, set or delete, given a key that is a string or a format)
      const k = keyShape(m), key = kw.find(([n]) => n === 'key')?.[1] ?? args[0]
      if (k && key && (key.t === 'str' || key.t === 'fmt') && (k !== 'set' || has('value', 1))) { kind = k; (d[k] ??= []).push(m); this.notes.add(`${store}.${m}: read as the store's ${k} by a key (inferred from its name)`) }
      else {
        // (another method: an answer, or left out; of a store, one that may change what it holds, unless stated)
        if (this.storeKeyed.has(store) && !this.tagAt(at.p)) return refuse(at, `${at.text}: ${m}, a method of the store not stated as its get, set or delete (one that may change what it holds: state it, stores: {${store}: {get, set, delete}}, or skip it)`)
        const ty = this.storeTypes.get(store), ret = ty ? this.mod.recs[ty]?.rets?.[m] : undefined
        return this.boundary({...at, args: [], kw: []}, {key: `${store}.${m}`, name: `${store}.${m}`, patch: {store, path: [m]}, ...(ret ? {ret} : {}), args: false, refusal: `${at.text}: ${m}, a method of the store not stated as its get, set or delete`}, p, awaited)
      }
    }
    if (!kind) return refuse(at, `${at.text}: ${m}, a method of the store not stated as its get, set or delete`)
    const was = (this.storeAsync[store] ??= {})[m]
    if (was !== undefined && was !== awaited) return refuse(at, `${at.text}: the store's ${m} awaited at one call and not at another`)
    this.storeAsync[store]![m] = awaited
    const {tpl, k, kn} = this.storeKey(arg('key', 0), at)
    const [id, o] = this.storeMap(store, tpl, kn, at, p)
    if (kind === 'get') return this.mapGet({t: 'ref', id}, k, at, p, 'none')
    if (kind === 'delete') return [{t: 'none'}, this.mapDel({t: 'ref', id}, k, at, p, false)]
    const v = arg('value', 1)
    if (o.val!.k === 'str' ? v.t !== 'str' : v.t !== 'num') return refuse(at, `${at.text}: a ${v.t === 'opaque' ? v.why : v.t} set in a store of ${o.val!.k === 'float' ? 'numbers' : o.val!.k}`)
    if (o.val!.k === 'str') return refuse(at, `${at.text}: a store of strings (its cells hold numbers)`)
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
  // A call answered by the request: its result an input (one a step), the check stubbing the callee with it. Its type
  // is the caller's (a type string), a tag's, or the callee's declared one (inferred: `how` says which).
  answer(key: string, names: string[], patch: Patch | undefined, at: SX, p: Path, awaited: boolean, type: string | SType = this.opts.answers![key]!, how = 'stated'): [V, Path] {
    if (!patch && !at.end) return refuse(at, `${at.text}: an answered call the check can't stub`)
    if (this.mod.stubs === false) return refuse(at, `${at.text}: answered (${how}), but the ${LANG[this.mod.lang] ?? this.mod.lang} check can't stub a call yet`)
    if (p.called.includes(key)) return refuse(at, `${at.text}: ${key} called twice in one step (an answer is one a step)`)
    const q: Path = {...p, called: [...p.called, key]}
    // (where it is called: a compiled language's check stubs it there, its source rewritten)
    const site = {p: at.p, ...(at.end ? {end: String(at.end)} : {}), ...(at.span ? {span: at.span as [number, number]} : {})}
    let a = this.answers.get(key)
    const short = key.split(/\.|::/).pop()!
    if (!a) {
      const t = typeof type === 'string' ? sortOfText(type, at.p).t : type, text = typeof type === 'string' ? type : typeText(type)
      const inner = t.k === 'opt' ? t.of : t, s = this.scalar(inner)!
      const v = this.newVar(short, s, 'input', how === 'stated' ? `what ${names[0]} returns (stated: answers)` : `what ${names[0]} returns (${how}: any ${text})`)
      const none = t.k === 'opt' ? this.newVar(`${short}_none`, {k: 'bool'}, 'input', `whether ${names[0]} returns None`).name : undefined
      // (a result of a fixed width: within it, the claim is for the values its type holds)
      this.typed(v, inner, 'input')
      a = {key, patch: patch ?? {}, async: awaited, inputs: {name: v.name, ...(none ? {none} : {}), ...(inner.k === 'float' ? {float: true} : {})}, sort: text, ...(how === 'stated' ? {} : {how}), at: [], ...(at.ty ? {ty: String(at.ty)} : {})}
      this.answers.set(key, a)
      this.notes.add(how === 'stated' ? `${names[0]} (${at.p}): answered by the request (stated), its arguments not read` : `${names[0]} (${at.p}): answered by the request (${how}: its value is read; assumes ${names[0]} may return any ${text}), its arguments not read`)
    } else if (a.async !== awaited) return refuse(at, `${at.text}: ${key} awaited at one call and not at another`)
    // (a callee whose declared result is a fixed-width integer, the reader's `ity`: an answer is within it where it is read)
    if (at.ity && this.vars.get(a.inputs.name)!.sort.k === 'num') this.typed(this.vars.get(a.inputs.name)!, at.ity as IntTy, 'input', I.and(this.sel, this.cond(p)))
    if (!a.at!.some(x => x.p === site.p)) a.at!.push(site)
    const vv = this.valueOf(this.vars.get(a.inputs.name)!)
    return [a.inputs.none ? {t: 'opt', has: I.not(I.bvar(a.inputs.none)), v: vv} : vv, q]
  }

  // --- the boundary inferred ---------------------------------------------------------------------------------------
  // A call of code the subset doesn't read (another module's, an injected dependency's, or the module's own function
  // cut): tagged, else inferred. Its arguments are evaluated (the code does). Given a reference to the rule's state,
  // other code may change it: refused unless the caller states it. Its value read (a run refused where it is): the next
  // run answers it by the request, over its declared type; else it is left out, kept only where nothing reads it.
  readonly pend = new Map<string, Pend>()
  readonly entryIds = new Set<string>()
  boundary(x: SX, b: Bound, p: Path, awaited: boolean): [V, Path] {
    const tag = this.tagAt(x.p) ?? b.tag
    if (tag?.k === 'strict') return refuse(x, b.refusal)
    const [vals, q] = b.args === false ? [[], p] as [V[], Path] : this.argVals(x, p)
    // (a call a reader doesn't lower: the names its arguments mention, where the reader says; else taken as given it)
    const given = b.args === false && x.e === 'no' && !b.recv ? (x.names as string[] | undefined)?.some(n => { const v = q.locals.get(n); return !v || this.stateRef(v, q) }) ?? true : [b.recv, ...vals].some(v => v && this.stateRef(v, q))
    if (given && !tag && (!b.own || this.writesState(b.own, this.rootsOf(this.func(b.own, x), b.recv, vals, q))))
      return refuse(x, `${b.refusal}; it is given the rule's state, which ${b.own ? 'its code' : 'other code'} may change (if it doesn't, state it: skip: [${JSON.stringify(b.key.split('.').pop())}], or a \`gdp: skip\` comment on its line)`)
    const t = tag?.k === 'answer' ? (tag.arg ? tag.arg : b.ret && answerable(b.ret) ? b.ret : refuse(x, `${x.text}: tagged gdp: answer, and ${b.name} declares no type an answer takes: give it (gdp: answer float)`)) : this.inf!.answers.get(b.key)
    if (t) return this.answer(b.key, [b.name], b.patch, x, q, awaited, t, tag ? 'tagged' : 'inferred')
    const why = `${x.text ?? b.name}: the value of ${b.name}, other code left out`
    this.pend.set(why, {...b, why, at: x.p, ...(x.end ? {end: String(x.end)} : {})})
    this.notes.add(`${b.name} (${x.p}): left out (${tag ? 'tagged: gdp: skip' : 'inferred: nothing the rule keeps reads its value'}), run as it is by the check`)
    return [{t: 'opaque', why, ask: b.key}, q]
  }
  argVals(x: SX, p: Path): [V[], Path] {
    let q = p
    const out: V[] = []
    for (const a of [...((x.args as SX[] | undefined) ?? []), ...((x.kw as [string, SX][] | undefined) ?? []).map(([, v]) => v)]) {
      try { const [v, q2] = this.ev(a, q); out.push(v); q = q2 } catch (e) { if (!(e instanceof Refusal) || !foreign(a)) throw e; out.push({t: 'opaque', why: e.what}) }
    }
    return [out, q]
  }
  // A value that is (or holds) a reference to the rule's state: the object, its nested objects, maps, lists, stores.
  stateRef(v: V, p: Path): boolean {
    const st = (id: string) => { const o = p.heap.get(id); return id === 'this' || o?.k === 'store' || (!!o && 'origin' in o && o.origin === 'state') }
    switch (v.t) {
      case 'ref': case 'map': case 'list': return st(v.id)
      case 'cell': return st(v.map)
      case 'ptr': return this.cases(v.to).objs.some(c => st(c.id))
      case 'opt': return this.stateRef(v.v, p)
      case 'tuple': return v.xs.some(y => this.stateRef(y, p))
      case 'struct': return [...v.f.values()].some(y => this.stateRef(y, p))
      case 'fn': return !!v.self && this.stateRef(v.self, p)
      case 'ext': return !!v.recv && this.stateRef(v.recv, p)
      case 'bool': case 'builtin': case 'choice': case 'cls': case 'err': case 'fmt': case 'lib': case 'lock': case 'nil': case 'none': case 'num': case 'opaque': case 'pop': case 'push': case 'res': case 'sattr': case 'str': return false
    }
  }
  // The parameters of a function a call gives the rule's state (its receiver, its arguments).
  rootsOf(fn: SFunc, recv: V | undefined, args: V[], p: Path): Set<string> {
    const out = new Set<string>(), ps = fn.params.filter(x => !x.star)
    let i = 0
    for (const pa of ps) {
      const v = pa.self && !fn.static ? recv : args[i++]
      if (v && this.stateRef(v, p)) out.add(pa.name)
    }
    return out
  }
  // Whether a function may write the state its `roots` (parameters, then locals aliasing them) reach, read from the IR
  // alone: a write through one, a call of other code given one, a method called on one, or a statement or expression
  // the subset doesn't read. The module's own functions it calls are read the same way.
  writesState(id: string, roots: Set<string>, seen = new Set<string>()): boolean {
    if (!roots.size) return false
    const key = `${id}(${[...roots].sort().join()})`
    if (seen.has(key)) return false
    seen.add(key)
    const fn = this.mod.funcs[id]
    if (!fn) return true
    const rs = new Set(roots)
    const mentions = (x: unknown): boolean => { if (!x || typeof x !== 'object') return false; const o = x as SX; if (o.e === 'var' && rs.has(String(o.n))) return true; return Object.values(o).some(mentions) }
    const isVar = (x: unknown) => !!x && typeof x === 'object' && (x as SX).e === 'var'
    const targets = (s: SS): unknown[] => [s.to, ...((s.l as unknown[] | undefined) ?? []), s.pl, (s.at as SX | undefined)?.m, s.s === 'del' ? s.x : undefined].filter(Boolean)
    // (aliases first: a local set from a root's parts is one)
    for (let grew = true; grew;) {
      grew = false
      const scan = (x: unknown) => {
        if (!x || typeof x !== 'object') return
        const st = x as SS
        if ((st.s === 'set' || st.s === 'assign') && mentions(st.x ?? st.r)) for (const t of targets(st)) { const flat = (t as SX).e === 'tuple' ? (t as SX).xs as SX[] : [t as SX]; for (const y of flat) if (isVar(y) && !rs.has(String(y.n))) { rs.add(String(y.n)); grew = true } }
        Object.values(x).forEach(scan)
      }
      scan(fn.body)
    }
    const own = (f: SX): SFunc | undefined => {
      if (f.e === 'fn') return this.mod.funcs[String(f.id)]
      if (f.e === 'get' && isVar(f.x) && rs.has(String((f.x as SX).n))) {
        const r = Object.values(this.mod.recs).find(r => r.own && Object.values(r.methods).includes(fn.id))
        const mid = r?.methods[String(f.f)]
        return mid ? this.mod.funcs[mid] : undefined
      }
      return undefined
    }
    const calls = (c: SX): boolean => {
      const f = c.f as SX, args = [...((c.args as SX[] | undefined) ?? [])], kw = (c.kw as [string, SX][] | undefined) ?? []
      const target = f && own(f)
      if (!target) return (f?.e === 'get' && mentions(f.x)) || args.some(mentions) || kw.some(([, a]) => mentions(a))
      const sub = new Set<string>(), ps = target.params.filter(x => !x.star)
      let i = 0
      for (const pa of ps) {
        if (pa.self && !target.static) { if (f.e === 'get') sub.add(pa.name); continue }
        const a = args[i++] ?? kw.find(([n]) => n === pa.name)?.[1]
        if (a && mentions(a)) sub.add(pa.name)
      }
      return this.writesState(target.id, sub, seen)
    }
    const walk = (x: unknown): boolean => {
      if (!x || typeof x !== 'object') return false
      const o = x as SX & SS
      // (a statement or expression the subset doesn't read: where its reader names what it mentions, by those)
      if (o.s === 'no' || o.e === 'no') { if (!o.names || (o.names as string[]).some(n => rs.has(n))) return true }
      if (o.e === 'rmw' && mentions(o)) return true
      if (o.s && ['set', 'assign', 'del', 'incdec', 'opset', 'mopset'].includes(o.s) && targets(o).some(t => !isVar(t) && mentions(t))) return true
      if (o.e === 'call' && calls(o)) return true
      return Object.values(o).some(walk)
    }
    return walk(fn.body)
  }
  // The `gdp:` comments of the file read (skip, answer [type], strict), by line: on a call's line, they state its
  // boundary; on a function's line (or the line above it), every call of it. A decorator or annotation named
  // gdp.skip, gdp_skip or GdpSkip (answer, strict) states it for the function too.
  private tagLines = new Map<string, Map<number, Tag>>()
  tagAt(at: string): Tag | undefined {
    const m = this.inf && /^(.*):(\d+):\d+$/.exec(at)
    if (!m) return undefined
    let lines = this.tagLines.get(m[1]!)
    if (!lines) {
      lines = new Map()
      const src = sourceOf(this.mod, m[1]!) ?? ''
      src.split('\n').forEach((l, i) => { const t = /(?:#|\/\/|--|%)\s*gdp:\s*(skip|answer|strict)\b[ \t]*([^#\n]*)$/.exec(l); if (t) lines!.set(i + 1, {k: t[1] as Tag['k'], arg: t[2]!.trim()}) })
      this.tagLines.set(m[1]!, lines)
    }
    return lines.get(Number(m[2]))
  }
  fnTag(fn: SFunc): Tag | undefined {
    for (const d of fn.decorators) { const m = TAG_DECO.exec(d.name); if (m) return {k: m[1]!.toLowerCase() as Tag['k'], arg: /\(\s*['"](.*)['"]\s*\)/.exec(d.text)?.[1] ?? ''} }
    const [file, line] = fn.span
    return this.tagAt(`${file}:${line}:1`) ?? this.tagAt(`${file}:${line - 1}:1`)
  }
  // The module's own function called where the boundary is: its patch for the check (a method of the object: on it).
  ownPatch(fn: SFunc, self: V | undefined): Patch | undefined {
    if (!fn.cls) return {mod: this.mod.module, path: [fn.id]}
    if (self?.t === 'ref' && self.id === 'this') return {self: fn.name}
    const r = Object.values(this.mod.recs).find(r => r.methods[fn.name] === fn.id)
    return r ? {mod: r.module, path: [r.short, fn.name]} : undefined
  }
  ownCut(fn: SFunc, self: V | undefined, x: SX): Bound | undefined {
    const tag = this.fnTag(fn), lineTag = this.tagAt(x.p)
    if (!this.inf || tag?.k === 'strict' || lineTag?.k === 'strict' || !(this.inf.cut.has(fn.id) || tag || lineTag)) return undefined
    const why = this.inf.cut.get(fn.id)
    if (why) this.notes.add(`${fn.name}: the module's own code, outside the subset (${why}), and writing none of the rule's state: taken as other code where it is called (inferred)`)
    return {key: fn.id, name: fn.name, patch: this.ownPatch(fn, self), ret: fn.ret, own: fn.id, recv: self, tag, refusal: `${x.text}: ${fn.name}`}
  }
  // A refused run: what the next one infers, or the refusal (with the statement that would accept it). A value of
  // other code read is answered by its declared type (where the check can stub it); else the module's own function the
  // refusal is in (the innermost but the entries) is cut where it writes none of the rule's state.
  promote(e: Refusal): Refusal | undefined {
    let best: Pend | undefined
    for (const [why, pd] of this.pend) if (e.what.includes(why) && (!best || why.length > best.why.length)) best = pd
    let hint = ''
    if (best) {
      const t = best.ret && answerable(best.ret) ? best.ret : undefined
      if (t && (best.patch || best.end) && this.mod.stubs !== false) { this.inf!.answers.set(best.key, t); return undefined }
      const short = JSON.stringify(best.key.split('.').pop()), cant = this.mod.stubs === false ? `the ${LANG[this.mod.lang] ?? this.mod.lang} check can't stub a call yet` : !best.patch && !best.end ? 'the check can\'t stub it' : ''
      hint = `${best.refusal.replace(/ \(answer it, skip it, or read that module\)$/, '')} (${best.at}), whose value is read, and ${cant || (!best.ret || best.ret.k === 'any' ? 'it declares no type' : `it returns ${best.ret.k === 'rec' ? `an object (${this.mod.recs[best.ret.name]?.short ?? best.ret.name})` : this.why(best.ret)}`)}: ${cant ? 'read its code, or keep its value unread' : `state what it returns (answers: {${short}: 'int'}, or a \`gdp: answer int\` comment on its line)`}`
    }
    for (const id of (e as Framed).frames ?? []) {
      const fn = this.mod.funcs[id.id]
      if (!fn || this.inf!.cut.has(id.id) || this.entryIds.has(id.id) || this.fnTag(fn)?.k === 'strict' || this.writesState(id.id, new Set(id.roots))) continue
      this.inf!.cut.set(id.id, `${e.where}: ${e.what}`)
      return undefined
    }
    return hint ? new Refusal(e.where, `${e.what}; ${hint}`) : e
  }

  // --- expressions ----------------------------------------------------------------------------------------------------
  ev(x: SX, p: Path, awaited = false): [V, Path] {
    switch (x.e) {
      case 'int': { const ty = (x.ity as IntTy | undefined) ?? (x.ty ? this.intTy(x.ty as SType) : undefined); return [{t: 'num', e: I.num(Number(x.v)), ...(ty ? {ty} : {})}, p] }
      case 'unit': return [{t: 'none'}, p]
      case 'opaque': return [{t: 'opaque', why: String(x.why), ...(x.firm ? {firm: true} : {})}, p]
      case 'ref': case 'lock': return this.ev(x.x as SX, p)
      case 'copy': { const [v, q] = this.ev(x.x as SX, p); return this.copy(v, q, x) }
      case 'cast': return this.cast(x, p)
      case 'clock': return this.clock(x, p)
      case 'some': { const [v, q] = this.ev(x.x as SX, p); return [{t: 'opt', has: I.T, v}, q] }
      case 'ok': case 'err': { const [v, q] = this.ev(x.x as SX, p); return [{t: 'res', ok: x.e === 'ok' ? I.T : I.F, v: x.e === 'ok' ? v : {t: 'none'}, e: x.e === 'err' ? v : {t: 'none'}}, q] }
      case 'is': { const [v, q] = this.ev(x.x as SX, p); return [{t: 'bool', e: this.isOf(v, String(x.k), x)}, q] }
      case 'unwrap': { const [v, q] = this.ev(x.x as SX, p); return [this.inner(v, String(x.k), x), q] }
      case 'expect': {
        const [v, q] = this.ev(x.x as SX, p)
        const good = this.isOf(v, 'good', x)
        this.fail(q, I.not(good), x, `${x.text}: unwrap of ${v.t === 'res' ? 'an Err' : 'None'} (a panic)`)
        return [this.inner(v, 'good', x), this.assume(q, good)]
      }
      case 'opt_or': {
        const [v, q] = this.ev(x.x as SX, p)
        const good = this.isOf(v, 'good', x), val = this.inner(v, 'good', x)
        const [d, q2] = (x.d as SX).e === 'zero' ? [zeroLike(val), q] as [V, Path] : this.ev(x.d as SX, q)
        return [this.ite(good, val, d, x), q2]
      }
      // The bad case of a value `?` returns: an Err with its error, or None.
      case 'bad': { const [v, q] = this.ev(x.x as SX, p); return [v.t === 'res' ? {t: 'res', ok: I.F, v: {t: 'none'}, e: v.e} : {t: 'none'}, q] }
      case 'res_ok': { const [v, q] = this.ev(x.x as SX, p); return [v.t === 'res' ? {t: 'opt', has: v.ok, v: v.v} : v, q] }
      case 'variant': return [{t: 'choice', e: I.llit(String(x.v), x.values as string[])}, p]
      case 'closure': {
        const caps = new Map<string, V>()
        for (const n of x.caps as string[]) { const v = p.locals.get(n); if (v) caps.set(n, v) }
        return [{t: 'fn', id: String(x.id), caps}, p]
      }
      case 'new': {
        let q = p
        const f = new Map<string, V>()
        for (const [n, y] of x.fields as [string, SX][]) { const [v, q2] = this.ev(y, q); f.set(n, v); q = q2 }
        const r = this.rec(String(x.rec), x)
        for (const fd of r.fields) if (!f.has(fd.name)) return refuse(x, `${x.text}: ${fd.name} not given`)
        for (const fd of r.fields) { const v = f.get(fd.name)!; if (fd.t.k === 'choice' && v.t === 'str' && v.e.op === 'slit') f.set(fd.name, {t: 'choice', e: I.llit(v.e.value, fd.t.values)}); const ty = this.intTy(fd.t); if (ty && v.t === 'num' && !v.ty) f.set(fd.name, {...v, ty}) }
        const id = `fresh:${this.fresh++}`
        return [{t: 'ref', id}, {...q, heap: new Map(q.heap).set(id, {k: 'rec', ty: String(x.rec), f, origin: 'fresh'})}]
      }
      // An immutable update (Elixir's %{s | f: v}): a fresh copy of the record, the fields given set in it.
      case 'upd': {
        const [o, q] = this.ev(x.x as SX, p)
        let [c, q2] = this.copy(o, q, x)
        for (const [f, y] of x.fields as [string, SX][]) { const [v, q3] = this.ev(y, q2); q2 = this.setField(c, f, v, x, q3) }
        return [c, q2]
      }
      case 'rmw': return this.rmw(x, p)
      case 'bool': return [{t: 'bool', e: x.v ? I.T : I.F}, p]
      case 'str': return [{t: 'str', e: {op: 'slit', value: String(x.v)}}, p]
      case 'none': return [{t: 'none'}, p]
      case 'var': { const v = p.locals.get(String(x.n)); if (!v) return refuse(x, (x.why as string | undefined) ?? `${String(x.n)}: a variable read before it is set`); return [this.narrow(v, p), p] }
      case 'fn': return [{t: 'fn', id: String(x.id)}, p]
      case 'cls': return [{t: 'cls', rec: String(x.rec), ...(x.patch ? {patch: x.patch as Patch} : {})}, p]
      case 'builtin': return [{t: 'builtin', n: String(x.n)}, p]
      case 'lib': return [{t: 'lib', q: String(x.q)}, p]
      case 'ext': return [{t: 'ext', q: String(x.q), text: String(x.text), ...(x.patch ? {patch: x.patch as Patch} : {}), ...(x.ret ? {ret: x.ret as SType} : {})}, p]
      case 'no': {
        // (a call of other code a reader doesn't lower, `ext` its name: at the boundary, where it is inferred)
        if (x.ext && !x.pre && !x.prepl) {
          const names = [x.ext as string], ans = this.match(Object.keys(this.opts.answers ?? {}), names), patch = x.patch as Patch | undefined
          if (ans) return this.answer(ans, names, patch, x, x.args ? this.argsRead(x, p) : p, false)
          if (this.skipped(names)) { this.notes.add(`${names[0]} (${x.p}): left out (stated: skip), run as it is by the check`); return [{t: 'opaque', why: `${names[0]}: the value of a call left out (skip)`}, x.args ? this.argsRead(x, p) : p] }
          let q = p, recv: V | undefined
          if (x.recv && this.inf) [recv, q] = this.ev(x.recv as SX, q)
          if (this.inf) return this.boundary(x, {key: names[0]!, name: names[0]!, refusal: String(x.why), ...(x.args ? {} : {args: false}), ...(recv ? {recv} : {}), ...(x.ret ? {ret: x.ret as SType} : {}), ...(patch ? {patch} : {})}, q, false)
        }
        let q = p; for (const y of (x.pre as SX[] | undefined) ?? []) q = this.ev(y, q)[1]; if (x.prepl) this.place(x.prepl as SX, q); return refuse(x, String(x.why)) }
      case 'nil': return [{t: 'nil'}, p]
      case 'ptr0': return [{t: 'ptr', to: {k: 'nil'}}, p]
      case 'errv': { let q = p; for (const y of (x.pre as SX[] | undefined) ?? []) q = this.ev(y, q)[1]; if (x.note) this.notes.add(x.note as string); return [{t: 'err', is: x.is ? I.T : I.F}, q] }
      case 'struct': { let q = p; const f = new Map<string, V>(); for (const [n, y] of x.fields as [string, SX][]) { const [v, q2] = this.ev(y, q); f.set(n, v); q = q2 } return [{t: 'struct', ty: String(x.ty), f}, q] }
      case 'at': { const [pl, q] = this.place(x.pl as SX, p); if (pl.k === 'blank') return refuse(x, '_'); const [v, q2] = this.read(pl, x, q); if (v.t === 'opaque' && !x.raw) return refuse(x, v.why); return [v, q2] }
      case 'deref': { const [v, q] = this.ev(x.x as SX, p); return this.deref(v, [], x, q) }
      case 'as': { const [v, q] = this.ev(x.x as SX, p); if (v.t === 'num' && x.ity) return [{...v, ty: x.ity as IntTy}, q]; if (v.t === 'nil' && x.nil) return [x.nil === 'ptr' ? {t: 'ptr', to: {k: 'nil'}} : {t: 'err', is: I.F}, q]; return [v, q] }
      case 'conv': { const [v, q] = this.ev(x.x as SX, p), ty = x.ity as IntTy | undefined; if (ty && v.t === 'num') return [{t: 'num', e: this.wrap(v.e, ty.ub ? {bits: ty.bits, signed: ty.signed, name: ty.name, t: ty.t} : ty, x, q), ty}, q]; return refuse(x, v.t === 'opaque' && v.ask ? `${String(x.why)}: of ${v.why}` : String(x.why)) }
      case 'binop': { const [a, q] = this.ev(x.x as SX, p), [b, q2] = this.ev(x.y as SX, q); return [this.binop(String(x.op), a, b, x, q2), q2] }
      case 'andalso': {
        // The right side runs only where the left doesn't decide: its failures and effects only there.
        const and = x.op === '&&', [a, q] = this.ev(x.x as SX, p), ab = this.boolv(a, x.x as SX), c = and ? ab : I.not(ab)
        const [b, q2] = this.ev(x.y as SX, this.assume(q, c)), bb = this.boolv(b, x.y as SX)
        return [{t: 'bool', e: and ? I.and(ab, bb) : I.or(ab, bb)}, q2.heap === q.heap ? q : this.merge({...q2, pc: [...q.pc, c]}, q, x)]
      }
      case 'unop': {
        const [a, q] = this.ev(x.x as SX, p), op = String(x.op)
        if (op === '!') return [{t: 'bool', e: I.not(this.boolv(a, x))}, q]
        if (op === '-') { if (a.t !== 'num') return refuse(x, `- of a ${a.t}`); return [{t: 'num', e: this.wrap(I.neg(a.e), a.ty!, x, q), ty: a.ty}, q] }
        if (op === '+') return [a, q]
        return refuse(x, String(x.why))
      }
      case 'addr': {
        const [pl, q] = this.place(x.pl as SX, p)
        if (pl.k === 'heap' && pl.ptr.t === 'ptr') return [{t: 'ptr', to: this.shift(pl.ptr.to, pl.path)}, this.nonNil(pl.ptr.to, x, q, 'a nil dereference')[1]]
        return refuse(x, String(x.why))
      }
      case 'alloc': {
        const [v, q] = this.ev(x.x as SX, p), id = `new:${++this.fresh}`
        if (v.t !== 'struct') return refuse({p: ''}, 'new of other than a struct')
        return [{t: 'ptr', to: {k: 'obj', id, path: []}}, {...q, heap: new Map(q.heap).set(id, {k: 'rec', ty: v.ty, f: new Map(v.f), origin: 'fresh'})}]
      }
      case 'bignew': { if (!x.x) return this.newBig(I.num(0), p); const [v, q] = this.ev(x.x as SX, p); return this.newBig(this.numv(v, x), q) }
      case 'big': return this.bigCall(x, p)
      case 'mutex': return this.lockCall(x, p)
      case 'gcall': {
        const fn = this.func(String(x.fn), x), r = x.recv as SX | undefined
        let q = p, recv: V | undefined
        if (r?.e === 'addr') [recv, q] = this.ev(r, q)
        else if (r?.k === 'rd') { const [pl, q2] = this.place(r.pl as SX, q); [recv, q] = this.read(pl, x, q2) }
        else if (r) { const [v, q2] = this.ev(r.x as SX, q); q = q2; if (r.k === 'val' && v.t === 'ptr') [recv, q] = this.deref(v, [], x, q); else recv = v }
        const args: V[] = []
        for (const a of x.args as SX[]) { const [v, q2] = this.ev(a, q); args.push(v); q = q2 }
        return this.inline(fn, recv, args, x, q)
      }
      case 'len': {
        const [s, q] = this.ev(x.x as SX, p)
        if (x.k === 'str') { if (s.t !== 'str') refuse(x, 'len of a non-string'); return [{t: 'num', e: I.num(0), ty: x.ity as IntTy, slen: (s as {e: K}).e}, q] }
        return [{t: 'num', e: this.listLen(s, x, q), ty: x.ity as IntTy}, q]
      }
      case 'append': {
        const [s, q] = this.ev(x.s as SX, p), [v, q2] = this.ev(x.x as SX, q)
        if (s.t !== 'list') return refuse(x, 'append to other than a slice of the state')
        if (v.t === 'num' && v.slen) return refuse(x.at1 as SX, 'len of a string read other than against 0')
        return [{t: 'push', id: s.id, x: v}, q2]
      }
      case 'delete': { const [m, q] = this.ev(x.m as SX, p), [k, q2] = this.ev(x.k as SX, q); return [{t: 'tuple', xs: []}, this.mapDelete(m, k, x, q2)] }
      case 'newmap': return [{t: 'map', id: 'new-map'}, p]
      case 'newlist': return [{t: 'list', id: 'new-list'}, p]
      case 'minmax': {
        let q = p
        const vs: V[] = []
        for (const y of x.xs as SX[]) { const [v, q2] = this.ev(y, q); vs.push(v); q = q2 }
        let e = this.numv(vs[0]!, x)
        for (const v of vs.slice(1)) e = x.op === 'min' ? I.nmin(e, this.numv(v, x)) : I.nmax(e, this.numv(v, x))
        return [{t: 'num', e, ty: (x.ity as IntTy | undefined) ?? refuse(x, String(x.why))}, q]
      }
      case 'panic': { let q = p; for (const a of x.args as SX[]) q = this.ev(a, q)[1]; this.refuseWhere(q, I.T, x, (x.what as string | undefined) ?? 'a panic'); return [{t: 'tuple', xs: []}, {...q, pc: [...q.pc, I.F]}] }
      case 'midx': { const [b, q] = this.ev(x.m as SX, p), [i, q2] = this.ev(x.k as SX, q); return [this.mapRead(b, i, x, q2).v, q2] }
      case 'lidx': { const [b, q] = this.ev(x.s as SX, p), [i, q2] = this.ev(x.i as SX, q); return this.listGet(b, i, x, q2) }
      case 'pop': {
        const [s, q] = this.ev(x.s as SX, p)
        if (s.t === 'list' && x.ok) {
          const len = this.listLen(s, x, q)
          this.refuseWhere(q, I.cmp('<', len, I.num(1)), x, 'a slice out of range (a panic: s[:len(s)-1] of an empty s)')
          return [{t: 'pop', id: s.id}, this.assume(q, I.cmp('<=', I.num(1), len))]
        }
        return refuse(x, String(x.why))
      }
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
      case 'not': { const [v, q] = this.ev(x.x as SX, p); if (v.t === 'opaque') return [v, q]; if (x.strict && v.t !== 'bool') return refuse(x, `${x.text ?? '!'}: a bitwise not`); return [{t: 'bool', e: I.not(this.truthy(v, x, q))}, q] }
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
  // A value read by value (Rust's copies and moves): an object copied whole into a fresh one, a map's record too.
  copy(v: V, p: Path, at: SX): [V, Path] {
    if (v.t === 'cell') { const m = p.heap.get(v.map) as Extract<Obj, {k: 'map'}>, c = this.cellOf(m, v.key, p, at); const id = `fresh:${this.fresh++}`; return [{t: 'ref', id}, {...p, heap: new Map(p.heap).set(id, {k: 'rec', ty: (m.val as {name: string}).name, f: new Map(c.vals), origin: 'fresh'})}] }
    if (v.t === 'opt') { const [w, q] = this.copy(v.v, p, at); return [{...v, v: w}, q] }
    if (v.t !== 'ref') return [v, p]
    const o = p.heap.get(v.id)
    if (o?.k !== 'rec') return o?.k === 'map' ? refuse(at, `${at.text ?? ''}: a map copied whole`) : [v, p]
    let q = p
    const f = new Map<string, V>()
    for (const [n, w] of o.f) { const [c, q2] = this.copy(w, q, at); f.set(n, c); q = q2 }
    const id = `fresh:${this.fresh++}`
    return [{t: 'ref', id}, {...q, heap: new Map(q.heap).set(id, {k: 'rec', ty: o.ty, f, origin: 'fresh', ...(o.lazy && o.origin === 'input' ? {} : {})})}]
  }
  // Which of its cases a value is: Some / None, Ok / Err, good (Some or Ok) / bad.
  isOf(v: V, k: string, at: SX): B {
    if (v.t === 'opt') return k === 'some' || k === 'good' ? v.has : k === 'none' || k === 'bad' ? I.not(v.has) : refuse(at, `${at.text ?? ''}: an Option tested as ${k}`)
    if (v.t === 'none') return k === 'none' || k === 'bad' ? I.T : k === 'some' || k === 'good' ? I.F : refuse(at, `${at.text ?? ''}: None tested as ${k}`)
    if (v.t === 'res') return k === 'ok' || k === 'good' ? v.ok : k === 'err' || k === 'bad' ? I.not(v.ok) : refuse(at, `${at.text ?? ''}: a Result tested as ${k}`)
    if (v.t === 'opaque') return refuse(at, `${at.text ?? ''}: ${v.why}`)
    return k === 'some' || k === 'good' ? I.T : k === 'none' || k === 'bad' ? I.F : refuse(at, `${at.text ?? ''}: a ${v.t} tested as ${k}`)
  }
  inner(v: V, k: string, at: SX): V {
    if (v.t === 'opt') return v.v
    if (v.t === 'res') return k === 'err' ? v.e : v.v
    if (v.t === 'none') return {t: 'none'}
    if (v.t === 'opaque') return v
    return k === 'err' ? refuse(at, `${at.text ?? ''}: the Err of a value that is no Result`) : v
  }
  // An atomic's operation on the field it is: read, written, or both (one step is one call).
  rmw(x: SX, p: Path): [V, Path] {
    const place = x.place as SX, op = String(x.op), args = x.args as SX[]
    const [cur, q] = this.ev(place, p)
    if (cur.t !== 'num' && cur.t !== 'bool') return refuse(x, `${x.text}: an atomic of ${cur.t === 'opaque' ? cur.why : `a ${cur.t}`}`)
    this.notes.add(`${x.text} (${x.p}): an atomic read and written as the field it is (each request one step: the claim is for calls that don't interleave)`)
    const argv: V[] = []
    let q2 = q
    for (const a of args) { const [v, q3] = this.ev(a, q2); argv.push(v); q2 = q3 }
    const wrap = (e: N): V => { const ty = cur.t === 'num' ? cur.ty : undefined; return ty ? {t: 'num', e: this.wrap(e, ty, x, q2), ty} : {t: 'num', e} }
    const set = (v: V) => this.assign(place, v, x, q2)
    switch (op) {
      case 'load': return [cur, q2]
      case 'store': return [{t: 'none'}, set(argv[0]!)]
      case 'swap': return [cur, set(argv[0]!)]
      case 'fetch_add': case 'fetch_sub': return [cur, set(wrap(op === 'fetch_add' ? I.add(this.numOf(cur, x, q2), this.numOf(argv[0]!, x, q2)) : I.sub(this.numOf(cur, x, q2), this.numOf(argv[0]!, x, q2))))]
      case 'fetch_max': case 'fetch_min': return [cur, set({...cur, e: op === 'fetch_max' ? I.nmax(this.numOf(cur, x, q2), this.numOf(argv[0]!, x, q2)) : I.nmin(this.numOf(cur, x, q2), this.numOf(argv[0]!, x, q2))} as V)]
      case 'compare_exchange': case 'compare_exchange_weak': {
        const c = this.equal(cur, argv[0]!, x, q2)
        if (op === 'compare_exchange_weak') this.notes.add(`${x.text}: compare_exchange_weak read as compare_exchange (it may fail spuriously: the claim is for calls where it doesn't)`)
        return [{t: 'res', ok: c, v: cur, e: cur}, set(this.ite(c, argv[1]!, cur, x))]
      }
    }
    return refuse(x, `${x.text}: an atomic's ${op}`)
  }
  get(x: SX, p: Path): [V, Path] {
    const [o, q] = this.ev(x.x as SX, p), f = String(x.f)
    switch (o.t) {
      case 'opaque': if (o.sattr) return this.storeAttr(o.sattr.store, `${o.sattr.path}.${f}`, x, q); return [{t: 'opaque', why: o.why, ...(o.ask ? {ask: o.ask} : {})}, q]
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
        return [{t: 'ext', q: `${o.rec}.${f}`, text: x.text ?? f, ...(o.patch?.path ? {patch: {...o.patch, path: [...o.patch.path, f]}} : {}), ...(r.rets?.[f] ? {ret: r.rets[f]} : {})}, q]
      }
      case 'bool': case 'builtin': case 'choice': case 'fmt': case 'fn': case 'lib': case 'lock': case 'num': case 'str': case 'tuple': case 'res': case 'ptr': case 'struct': case 'err': case 'nil': case 'map': case 'list': case 'push': case 'pop': return refuse(x, `${x.text}: a field of a ${o.t}`)
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
      if (mid === null) return this.inf ? [{t: 'ext', q: `${r.name}.${f}`, text: x.text ?? f, patch: {mod: r.module, path: [r.short, f]}, recv: o, ...(r.rets?.[f] ? {ret: r.rets[f]} : {})}, q] : refuse(x, `${x.text}: a method of another module's class`)
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
    const attrs = this.storeDecl(store).attrs ?? {}
    if (path in attrs) {
      const v = attrs[path]!
      this.notes.add(`${store}.${path} is ${JSON.stringify(v)} (stated)`)
      return [v === null ? {t: 'none'} : typeof v === 'boolean' ? {t: 'bool', e: v ? I.T : I.F} : typeof v === 'number' ? {t: 'num', e: I.num(v)} : {t: 'str', e: {op: 'slit', value: v}}, p]
    }
    if (Object.keys(attrs).some(k => k.startsWith(`${path}.`))) return [{t: 'sattr', store, path}, p]
    return [{t: 'opaque', why: `${x.text}: an attribute of the store not stated${this.inf ? ` (where the rule reads it, state its value: stores: {${store}: {attrs: {${JSON.stringify(path)}: null}}})` : ''}`, ...(this.inf ? {sattr: {store, path}} : {})}, p]
  }
  bin(x: SX, p: Path): [V, Path] {
    const op = String(x.op)
    if (x.ovf) return this.fixed(x, p)
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
  // Arithmetic with an overflow the reader states (Rust's, later C's): the result's type is its operands', and what
  // happens past its range is the operation's: a trap (a panic: the step's failure), a wrap (modulo 2^bits), a
  // saturation, or an Option (checked). Division and remainder truncate toward zero; by zero they trap.
  fixed(x: SX, p: Path): [V, Path] {
    const op = String(x.op), ovf = String(x.ovf)
    const [a, q] = this.ev(x.x as SX, p), [b, q2] = this.ev(x.y as SX, q)
    if (a.t === 'opaque' || b.t === 'opaque') return [a.t === 'opaque' ? a : b, q2]
    const na = this.numOf(a, x, q2), nb = this.numOf(b, x, q2)
    const ty = (a.t === 'num' ? a.ty : undefined) ?? (b.t === 'num' ? b.ty : undefined) ?? (ovf === 'sat0' || ovf === 'checked0' ? {bits: 0, signed: false} : undefined)
    let e: N
    if (op === '+') e = I.add(na, nb)
    else if (op === '-') e = I.sub(na, nb)
    else if (op === '*') e = I.mul(na, nb)
    else if (op === '/' || op === '%') {
      const k = constOf(b)
      if (k === undefined) return refuse(x, `${x.text}: a division by a value that isn't a constant`)
      if (k === 0) { this.fail(q2, I.T, x, `${x.text}: a division by zero (a panic)`); return [{t: 'num', e: I.num(0), ...(ty ? {ty} : {})}, {...q2, pc: [...q2.pc, I.F]}] }
      e = op === '/' ? (k < 0 ? I.neg(this.quot(na, -k)) : this.quot(na, k)) : this.rem(na, Math.abs(k))
    } else return refuse(x, `${x.text}: ${op}`)
    const out = (n: N): V => ({t: 'num', e: n, ...(ty ? {ty} : {})})
    const [lo, hi] = ty ? rangeOf(ty) : [-Infinity, Infinity], [below, above] = this.past(e, lo, hi, q2)
    switch (ovf) {
      case 'trap': this.fail(q2, I.or(below, above), x, `${x.text}: past ${tyName(ty)}'s range (a panic: attempt to ${op === '+' ? 'add' : op === '-' ? 'subtract' : op === '*' ? 'multiply' : 'divide'} with overflow)`); return [out(e), this.assume(q2, I.not(I.or(below, above)))]
      case 'sat': return [out(Number.isFinite(lo) || Number.isFinite(hi) ? I.nite(below, I.num(lo), I.nite(above, I.num(hi), e)) : e), q2]
      case 'sat0': return [out(I.nmax(e, I.num(0))), q2]
      case 'checked': return [{t: 'opt', has: I.not(I.or(below, above)), v: out(e)}, q2]
      case 'checked0': return [{t: 'opt', has: I.cmp('<=', I.num(0), e), v: out(e)}, q2]
      case 'wrap': return [out(ty ? this.wrap(e, ty, x, q2) : e), q2]
    }
    return refuse(x, `${x.text}: an overflow mode ${ovf}`)
  }
  // `x as T`: an integer into another width (wrapped where it may not fit), a C-like enum's discriminant, a bool's 0 or 1.
  cast(x: SX, p: Path): [V, Path] {
    const [v, q] = this.ev(x.x as SX, p), t = x.ty as SType, ty = this.intTy(t)
    if (v.t === 'opaque') return [v, q]
    let e: N
    if (v.t === 'num') e = v.e
    else if (v.t === 'bool') e = I.nite(v.e, I.num(1), I.num(0))
    else if (v.t === 'choice') {
      const vals = lvalues(v.e), discs = (x.x as SX).discs as number[] | undefined ?? this.discsOf(vals)
      e = vals.reduceRight((acc: N, val, i) => I.nite(I.is(v.e, val), I.num(discs[i] ?? i), acc), I.num(0))
    } else return refuse(x, `${x.text}: a ${v.t} cast`)
    if (!ty) return [{t: 'num', e}, q]
    const from = v.t === 'num' ? v.ty : {bits: 8, signed: false}
    const [lo, hi] = rangeOf(ty), [flo, fhi] = from ? rangeOf(from) : [-Infinity, Infinity]
    if (flo >= lo && fhi <= hi) return [{t: 'num', e, ty}, q]
    // (a narrowing cast of a value of a wider type: within the target's range by its bounds and the path's facts, or
    // refused where it isn't)
    const out = I.or(...this.past(e, lo, hi, q))
    if (!(out.op === 'const' && !out.v)) { this.refusals.push(I.and(this.cond(q), out)); this.notes.add(`${x.text} (${x.p}): a narrowing cast, refused where the value doesn't fit (it truncates)`) }
    return [{t: 'num', e, ty}, this.assume(q, I.not(out))]
  }
  discsOf(values: string[]): number[] { for (const e of Object.values(this.mod.enums ?? {})) if (e.values.join() === values.join()) return e.discs; return values.map((_, i) => i) }
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
    let q = p, tpl = '', hole: K | undefined, n = 0, opaque = false, ask: V | undefined
    for (const part of parts) {
      if (typeof part === 'string') { tpl += part.replace(/\{\}/g, '{ }'); continue }
      const [v, q2] = this.ev(part.x, q)
      q = q2
      n++
      if (v.t === 'opaque' && v.ask) ask ??= v
      if (!part.plain || n > 1 || !(v.t === 'str' || (v.t === 'num' && part.plain))) { opaque = true; continue }
      hole = v.t === 'str' ? v.e : {op: 'num', e: v.e}
      tpl += '{}'
    }
    if (ask?.t === 'opaque') return [{t: 'opaque', why: `${x.text}: a formatted string (${ask.why})`, ask: ask.ask}, q]
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
      if (o.t === 'opaque' && f.t === 'opaque') return this.inf ? this.boundary(x, {key: names[0] ?? String(x.text), name: names[0] ?? String(x.text), refusal: `${x.text}: a call on ${o.why}`}, q, awaited) : refuse(x, `${x.text}: a call on ${o.why}`)
    } else [f, q] = this.ev(fx, q)
    switch (f.t) {
      case 'fn': {
        const fn = this.func(f.id, x)
        if ((fn as {generic?: boolean}).generic) return refuse(x, `${fn.name}: a generic function`)
        const cut = this.ownCut(fn, f.self, x)
        if (cut) return this.boundary(x, cut, q, !!fn.async)
        try { return this.evArgs(x, q, (args, kw, q2) => this.callFunc(fn, f.self, args, kw, x, q2, awaited || !fn.async, f.caps)) } catch (e) {
          // (refused before its body runs, an argument or the call itself: the function is where it may be cut)
          if (e instanceof Refusal && this.inf && !(e as Framed).frames?.length) (e as Framed).frames = [{id: fn.id, roots: f.self && this.stateRef(f.self, q) ? fn.params.filter(x => x.self).map(x => x.name) : []}]
          throw e
        }
      }
      case 'cls': {
        // (another module's class made: other code, at the boundary)
        const r = this.inf ? this.mod.recs[f.rec] : undefined
        if (r && !r.own) return this.boundary(x, {key: f.rec, name: names[0] ?? r.short, ...(f.patch ? {patch: f.patch} : {}), ret: {k: 'rec', name: f.rec}, refusal: `${x.text}: ${r.short} made (the subset makes the module's own dataclasses)`}, q, awaited)
        return this.evArgs(x, q, (args, kw, q2) => this.construct(f.rec, args, kw, x, q2))
      }
      case 'builtin': return this.builtin(f.n, x, q)
      case 'lib': return this.lib(f.q, x, q)
      case 'ext': {
        const refusal = `${x.text}: ${f.q}, other code (answer it, skip it, or read that module)`
        return this.inf ? this.boundary(x, {key: f.q, name: /\s/.test(names[0] ?? ' ') ? f.q : names[0]!, ...(f.patch ? {patch: f.patch} : {}), ...(f.ret ? {ret: f.ret} : {}), ...(f.recv ? {recv: f.recv} : {}), refusal}, q, awaited) : refuse(x, refusal)
      }
      case 'opaque': return this.inf ? this.boundary(x, {key: names[0] ?? String(x.text), name: names[0] ?? String(x.text), refusal: `${x.text}: a call of ${f.why}`}, q, awaited) : refuse(x, `${x.text}: a call of ${f.why}`)
      case 'bool': case 'cell': case 'choice': case 'fmt': case 'lock': case 'none': case 'num': case 'opt': case 'ref': case 'sattr': case 'str': case 'tuple': case 'res': case 'ptr': case 'struct': case 'err': case 'nil': case 'map': case 'list': case 'push': case 'pop': break
    }
    void args0; void kw0
    return refuse(x, `${x.text}: a call of a ${f.t}`)
  }
  // The arguments of a call left to the boundary, read as far as the subset goes: the code evaluates them, so the fields
  // they read are inputs the check gives. An argument outside the subset that reaches none of the module's code and
  // not the object itself (other code's calls on other values) is taken as changing nothing of the state.
  argsRead(x: SX, p: Path): Path { return this.argVals(x, p)[1] }
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
      if (name === 'contains_key') return [{t: 'bool', e: this.cellOf(this.mapObj(m, x, q)[1], key(), q, x).has}, q]
      if (name === 'insert') { const k = key(), [old, q2] = this.mapGet(m, k, x, q, 'none'); return [old, this.mapSet(m, k, args[1] ?? refuse(x, `${x.text}: no value`), x, q2)] }
      if (name === 'remove') { const k = key(), [old, q2] = this.mapGet(m, k, x, q, 'none'); return [old, this.mapDel(m, k, x, q2, false)] }
      if (name === 'get_mut') { const k = key(), [, o] = this.mapObj(m, x, q); if (o.decl.scalar) return refuse(x, `${x.text}: a reference to a map's number (the subset writes one through m.insert)`); return this.mapGet(m, k, x, q, 'none') }
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
      if (args.some(a => a.t === 'opaque') && ['str', 'repr', 'len', 'isinstance', 'round', 'int', 'float', 'bool'].includes(n)) { const ask = args.find(a => a.t === 'opaque' && a.ask) as {why: string, ask: string} | undefined; return [{t: 'opaque', why: `${x.text}: of a value outside the subset${ask ? ` (${ask.why})` : ''}`, ...(ask ? {ask: ask.ask} : {})}, q] }
      const v = args[0]
      switch (n) {
        case 'min': case 'max': {
          if (args.length < 2) return refuse(x, `${x.text}: ${n} of an iterable`)
          const ns = args.map(a => this.numOf(a, x, q))
          const ty = args.map(v => (v.t === 'num' ? v.ty : undefined)).find(Boolean)
          return [{t: 'num', e: ns.slice(1).reduce((acc, y) => (n === 'min' ? I.nmin(acc, y) : I.nmax(acc, y)), ns[0]!), ...(ty ? {ty} : {})}, q]
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

  // --- pointers into the state, value records, lists, error values and locks (Go's lowering's; C's and Rust's next) --
  // A pointer is by cases on the objects it may be (an interior one, &x.f, a path into it), or nil; a record held by
  // value is copied where it is assigned; an error value is nil or not; a list of the state is pushed, popped or set
  // once a step; a lock held until the deferred unlock at the return. Each failure is where it is (refuseWhere: the
  // step's refusal, the state as it was there), and each refusal text is the reader's own.
  readonly edges: B[] = []
  readonly lists: MapDecl[] = []
  readonly spans = new Map<string, [string, number, number]>()
  readonly stateOrigin = new Map<string, string>()
  readonly lazyIn = new Map<string, {id: string, fields: [string, string][], sel: B, recipes: Record<string, Recipe>}>()
  // A failure where c holds on this path, refused (the step's refusal); `state` false: one the code goes on past and
  // the rule's numbers stop at (an edge, counted apart by the check).
  refuseWhere(p: Path, c: B, at: {p: string}, what: string, state = true) {
    const w = I.and(this.cond(p), c)
    if (w.op === 'const' && !w.v) return
    if (state) this.unwritten(p, at, what)
    this.refusals.push(w)
    if (!state) this.edges.push(w)
  }
  // The cases a pointer is: each object (with the condition it is that one), and the condition it is nil.
  cases(p: Ptr, c: B = I.T): {nil: B, objs: {c: B, id: string, path: string[]}[]} {
    if (p.k === 'nil') return {nil: c, objs: []}
    if (p.k === 'obj') return {nil: I.F, objs: [{c, id: p.id, path: p.path}]}
    const a = this.cases(p.a, I.and(c, p.c)), b = this.cases(p.b, I.and(c, I.not(p.c)))
    return {nil: I.or(a.nil, b.nil), objs: [...a.objs, ...b.objs]}
  }
  // A pointer's cases, a failure (what) where it may be nil, and the path where it isn't.
  nonNil(to: Ptr, at: {p: string}, p: Path, what: string): [ReturnType<Stepper['cases']>, Path] { const cs = this.cases(to); this.refuseWhere(p, cs.nil, at, what); return [cs, this.assume(p, I.not(cs.nil))] }
  shift(p: Ptr, path: string[]): Ptr { return p.k === 'nil' ? p : p.k === 'obj' ? {...p, path: [...p.path, ...path]} : {...p, a: this.shift(p.a, path), b: this.shift(p.b, path)} }
  readObj(o: Obj, path: string[], at: {p: string}, p: Path, id: string): V {
    if (o.k === 'big') { if (path.length) refuse(at, 'a field of a big.Int'); return refuse(at, 'a big.Int read as a value (it is used through its pointer)') }
    if (o.k !== 'rec') return refuse(at, 'a field of other than a struct')
    let v: V = {t: 'struct', ty: o.ty, f: o.f}
    for (const seg of path) {
      if (v.t !== 'struct') return refuse(at, `.${seg} of other than a struct`)
      v = v.f.get(seg) ?? this.lazyFieldIn(id, seg, p, at)
    }
    return v
  }
  writeObj(o: Obj, path: string[], x: V, at: {p: string}): Obj {
    if (o.k !== 'rec') return refuse(at, 'a write into other than a struct')
    if (!path.length) { if (x.t !== 'struct') return refuse(at, 'a struct set to other than a struct'); return {...o, f: new Map(x.f)} }
    const set = (fs: Map<string, V>, segs: string[]): Map<string, V> => {
      const seg = segs[0]!, rest = segs.slice(1), out = new Map(fs)
      if (!rest.length) { const old = fs.get(seg); if (old?.t === 'opaque') refuse(at, `writes ${old.why}`); out.set(seg, x); return out }
      const inner = fs.get(seg)
      if (inner?.t !== 'struct') return refuse(at, `.${seg} of other than a struct`)
      out.set(seg, {...inner, f: set(inner.f, rest)})
      return out
    }
    return {...o, f: set(o.f, path)}
  }
  // A field of a record the caller gives, made an input where it is first read (by the reader's recipe for it).
  lazyFieldIn(id: string, f: string, p: Path, at: {p: string}): V {
    const li = this.lazyIn.get(id), r = li?.recipes[f]
    if (!li || !r) return refuse(at, `no field ${f}`)
    if (r.k === 'no') return refuse(at, r.why)
    let g: V
    if (r.k === 'big') {
      const v = this.newVar(`${li.id}_${f}`, {k: 'num'}, 'input', 'a *big.Int argument (not nil: the claim is for calls that give one)')
      li.fields.push([f, v.name])
      p.heap.set(`in:${v.name}`, {k: 'big', v: I.nvar(v.name), origin: 'input'})
      g = {t: 'ptr', to: {k: 'obj', id: `in:${v.name}`, path: []}}
    } else {
      const v = this.newVar(`${li.id}_${f}`, {k: r.k}, 'input')
      li.fields.push([f, v.name])
      g = this.valueOfIn(v, r.ty, li.sel)
    }
    ;(p.heap.get(id) as {f: Map<string, V>}).f.set(f, g)
    return g
  }
  // An input's value, its type's range kept (a request outside it refused where sel holds: the claim is for its values).
  valueOfIn(v: Var, ty: IntTy | undefined, sel: B): V {
    if (ty) this.typed(v, ty, 'input', sel)
    return v.sort.k === 'num' ? {t: 'num', e: I.nvar(v.name), ty: ty ?? {bits: 64, signed: true}} : this.valueOf(v)
  }
  // *x read: by cases on the objects x may point to; nil fails.
  deref(v: V, path: string[], at: {p: string}, p: Path): [V, Path] {
    if (v.t === 'nil') { this.refuseWhere(p, I.T, at, 'a nil dereference'); return [{t: 'opaque', why: 'unreachable', firm: true}, {...p, pc: [...p.pc, I.F]}] }
    if (v.t !== 'ptr') return refuse(at, `a dereference of a ${v.t}`)
    const [cs, q] = this.nonNil(v.to, at, p, `a nil dereference (${at.p})`)
    if (!cs.objs.length) return [{t: 'opaque', why: 'unreachable', firm: true}, q]
    let out: V | undefined
    for (const o of [...cs.objs].reverse()) { const x = this.readObj(q.heap.get(o.id)!, [...o.path, ...path], at, q, o.id); out = out ? this.ite(o.c, x, out, at) : x }
    return [out!, q]
  }
  // A write through a pointer: to each object it may be, where it is that one.
  writeThrough(v: V, path: string[], x: V, at: {p: string}, p: Path): Path {
    if (v.t !== 'ptr') return refuse(at, `a write through a ${v.t}`)
    const [cs, q] = this.nonNil(v.to, at, p, 'a nil dereference'), heap = new Map(q.heap)
    for (const o of cs.objs) {
      const obj = heap.get(o.id)!, pa = [...o.path, ...path]
      heap.set(o.id, this.writeObj(obj, pa, this.ite(o.c, x, this.readObj(obj, pa, at, q, o.id), at), at))
    }
    return {...q, heap}
  }
  // A place: a local (and a path into its record), or a path inside the object a pointer is.
  place(x: SX, p: Path): [Place, Path] {
    switch (x.e) {
      case 'blank': return [{k: 'blank'}, p]
      case 'var': return [{k: 'local', id: String(x.n), path: []}, p]
      case 'deref': { const [v, q] = this.ev(x.x as SX, p); return [{k: 'heap', ptr: v, path: []}, q] }
      case 'fld': { const [b, q] = this.place(x.x as SX, p); if (b.k === 'blank') return refuse(x, 'a field of _'); return [{...b, path: [...b.path, String(x.f)]}, q] }
    }
    return refuse(x, (x.why as string | undefined) ?? `${x.text}: an assignment to other than a variable, a field or *p`)
  }
  read(pl: Place, at: SX | SS | {p: string}, p: Path): [V, Path] {
    if (pl.k === 'blank') return refuse(at, '_ read')
    if (pl.k === 'heap') return this.deref(pl.ptr, pl.path, at, p)
    let v = p.locals.get(pl.id) ?? refuse(at, `${(at as SX).text ?? ''}: a variable read before it is set`)
    for (const s of pl.path) { if (v.t !== 'struct') refuse(at, `.${s} of other than a struct`); v = (v as {f: Map<string, V>}).f.get(s) ?? refuse(at, `no field ${s}`) }
    return [v, p]
  }
  write(pl: Place, x: V, at: {p: string}, p: Path): Path {
    if (pl.k === 'blank') return p
    this.secondName(x, at)
    if (pl.k === 'heap') { this.keepsInState(pl, x, at, p); return this.writeThrough(pl.ptr, pl.path, x, at, p) }
    if (!pl.path.length) return {...p, locals: new Map(p.locals).set(pl.id, x)}
    const set = (v: V, segs: string[]): V => {
      const s = segs[0]!, rest = segs.slice(1)
      if (v.t !== 'struct') return refuse(at, `.${s} of other than a struct`)
      return {...v, f: new Map(v.f).set(s, rest.length ? set(v.f.get(s)!, rest) : x)}
    }
    return {...p, locals: new Map(p.locals).set(pl.id, set(p.locals.get(pl.id) ?? refuse(at, 'a field of a variable not set'), pl.path))}
  }
  // A list or a map under a second name: refused (two slices may share a backing array; a map is a reference).
  secondName(x: V, at: {p: string}) {
    if (x.t === 'list') refuse(at, 'a slice given a second name (two slices may share a backing array: append writes into it or not by its capacity)')
    if (x.t === 'map') refuse(at, 'a map given a second name (a map is a reference: a write through either is a write to both)')
  }
  // A pointer stored into the state: to a fresh object only (one the state holds would be in two places; one the
  // caller gave the caller's to change after the call).
  keepsInState(pl: Extract<Place, {k: 'heap'}>, x: V, at: {p: string}, p: Path) {
    if (x.t !== 'ptr') return
    const into = this.cases(pl.ptr.t === 'ptr' ? pl.ptr.to : {k: 'nil'})
    if (!into.objs.some(o => (p.heap.get(o.id) as {origin?: Origin})?.origin === 'state')) return
    for (const o of this.cases(x.to).objs) {
      const origin = (p.heap.get(o.id) as {origin?: Origin})?.origin
      if (origin === 'input') refuse(at, 'the state keeps a pointer the caller gave (the caller may change its object after the call)')
      if (origin === 'state') refuse(at, `the state's ${this.stateOrigin.get(o.id) ?? 'object'} put in a second place of the state (one object in two places)`)
    }
  }
  bindLocal(id: string, v: V, at: {p: string}, p: Path): Path {
    if (v.t === 'list' || v.t === 'map' || v.t === 'push' || v.t === 'pop') this.secondName(v.t === 'push' || v.t === 'pop' ? {t: 'list', id: v.id} : v, at)
    if (v.t === 'num' && v.slen) refuse(at, 'len of a string kept (it is read only against 0)')
    return {...p, locals: new Map(p.locals).set(id, v)}
  }
  numv(v: V, at: SX | {p: string}): N {
    if (v.t !== 'num') return refuse(at, `${(at as SX).text ?? ''}: a ${v.t} where a number is read`)
    if (v.slen) return refuse(at, 'len of a string read other than against 0 (strings are set and compared in the subset)')
    return v.e
  }
  boolv(v: V, at: SX | {p: string}): B { if (v.t !== 'bool') return refuse(at, `${(at as SX).text ?? ''}: a ${v.t} where a condition is read`); return v.e }
  // A binary operation of the reader's language with fixed-width integers (Go's): comparisons, arithmetic wrapped.
  binop(op: string, a: V, b: V, x: {p: string}, p: Path): V {
    if (op === '==' || op === '!=') { const e = this.eq(a, b, x, p); return {t: 'bool', e: op === '==' ? e : I.not(e)} }
    // len(s) of a string against 0: whether it is empty.
    const sl = (v: V, k: V) => (v.t === 'num' && v.slen && k.t === 'num' && !k.slen && k.e.op === 'const' && k.e.v === 0 ? v.slen : undefined)
    const flip: Record<string, string> = {'<': '>', '<=': '>=', '>': '<', '>=': '<='}
    if (['<', '<=', '>', '>='].includes(op) && (sl(a, b) || sl(b, a))) {
      const s = (sl(a, b) ?? sl(b, a))!, empty = I.keq(s, {op: 'slit', value: ''}), o = sl(a, b) ? op : flip[op]!
      return {t: 'bool', e: o === '<=' ? empty : o === '>' ? I.not(empty) : o === '>=' ? I.T : I.F}
    }
    if (['<', '<=', '>', '>='].includes(op)) {
      if (a.t === 'str' || b.t === 'str') return refuse(x, 'strings ordered (strings are set and compared in the subset)')
      // x.Cmp(y) against 0, read as the comparison of x and y.
      const cmpOf = (v: V, k: V): [N, N] | undefined => (v.t === 'num' && v.cmp && k.t === 'num' && k.e.op === 'const' && k.e.v === 0 ? v.cmp : undefined)
      const ca = cmpOf(a, b), cb = cmpOf(b, a)
      let l: N, r: N, o = op
      if (ca) [l, r] = ca
      else if (cb) { [l, r] = cb; o = flip[op]! } else { l = this.numv(a, x); r = this.numv(b, x) }
      return {t: 'bool', e: o === '<' ? I.cmp('<', l, r) : o === '<=' ? I.cmp('<=', l, r) : o === '>' ? I.cmp('<', r, l) : I.cmp('<=', r, l)}
    }
    if (['+', '-', '*', '/', '%', '<<', '>>'].includes(op)) {
      if (a.t === 'str') return refuse(x, 'strings joined (strings are set and compared in the subset)')
      return this.arith(op, a, b, x, p)
    }
    return refuse(x, `${op}: a bit operation (outside the subset)`)
  }
  eq(a: V, b: V, x: {p: string}, p?: Path): B {
    if (a.t === 'map' && b.t === 'nil' && p) return this.mapAt(a, x as SX, p).nil!
    if (a.t === 'nil' && b.t === 'map' && p) return this.mapAt(b, x as SX, p).nil!
    if (a.t === 'num' && b.t === 'num') return I.cmp('=', this.numv(a, x), this.numv(b, x))
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
      return I.or(I.and(ca.nil, cb.nil), ...ca.objs.flatMap(o => cb.objs.filter(q => q.id === o.id && q.path.join() === o.path.join()).map(q => I.and(o.c, q.c))))
    }
    if ((a.t === 'list' || a.t === 'map') && b.t === 'nil') return refuse(x, `a ${a.t === 'list' ? 'slice' : 'map'} compared with nil (nil and empty are one ${a.t === 'list' ? 'list' : 'map'} in the subset)`)
    return refuse(x, `${a.t === 'opaque' && a.ask ? a.why : `a ${a.t}`} compared with a ${b.t}`)
  }
  // Integer arithmetic at the type's width: the exact result, wrapped as the type wraps it (or refused, at 64 bits).
  arith(op: string, a: V, b: V, x: {p: string}, p: Path): V {
    if (a.t !== 'num' || b.t !== 'num') return refuse(x, `${op} of a ${a.t} and a ${b.t}`)
    this.numv(a, x); this.numv(b, x)
    const ty = a.ty?.name !== undefined ? a.ty : b.ty!
    let e: N
    switch (op) {
      case '+': e = I.add(a.e, b.e); break
      case '-': e = I.sub(a.e, b.e); break
      case '*': e = I.mul(a.e, b.e); break
      case '/': case '%': {
        if (b.e.op !== 'const') return refuse(x, `${op} by other than a constant`)
        if (b.e.v === 0) { this.refuseWhere(p, I.T, x, 'a division by zero'); return {t: 'num', e: I.num(0), ty} }
        const k = Math.abs(b.e.v), q = this.quot(a.e, k)
        e = op === '/' ? (b.e.v < 0 ? I.neg(q) : q) : this.rem(a.e, k)
        break
      }
      case '>>': if (b.e.op !== 'const' || b.e.v < 0) return refuse(x, '>> by other than a constant'); if (b.e.v >= 53) return refuse(x, `>> ${b.e.v} (past the rule's 2^53)`); e = I.divk(2 ** b.e.v, a.e); break
      case '<<': if (b.e.op !== 'const' || b.e.v < 0) return refuse(x, '<< by other than a constant'); if (b.e.v >= 53) return refuse(x, `<< ${b.e.v} (past the rule's 2^53)`); if (ty.ub) this.refuseWhere(p, I.cmp('<', a.e, I.num(0)), x, `${(x as SX).text ? `${(x as SX).text}: ` : ''}a negative value shifted left (undefined behavior)`); e = I.mulk(2 ** b.e.v, a.e); break
      default: return refuse(x, `${op}: outside the subset`)
    }
    return {t: 'num', e: this.wrap(e, ty, x, p), ty}
  }
  // a / k and a % k truncated toward zero (the remainder takes the dividend's sign), for a constant k > 0: one case
  // where a's bounds say it is at least 0.
  quot(a: N, k: number): N { return this.bounds(a)[0] >= 0 ? I.divk(k, a) : I.nite(I.cmp('<=', I.num(0), a), I.divk(k, a), I.neg(I.divk(k, I.neg(a)))) }
  // (0 − r, not −r: the printer's remainder is a natural's, which Int subtracts from)
  rem(a: N, k: number): N { return this.bounds(a)[0] >= 0 ? I.modk(k, a) : I.nite(I.cmp('<=', I.num(0), a), I.modk(k, a), I.sub(I.num(0), I.modk(k, I.neg(a)))) }
  // The bounds a term's value is within, from its variables' types (a cell's too) and its constants.
  bounds(e: N): [number, number] {
    const r = (n: string): [number, number] => { const ty = this.ints.get(n); return ty ? rangeOf(ty) : [-Infinity, Infinity] }
    switch (e.op) {
      case 'const': return [e.v, e.v]
      case 'var': return r(e.name)
      case 'cell': return r(`${e.map}.${e.field}`)
      case 'add': { const a = this.bounds(e.a), b = this.bounds(e.b); return [a[0] + b[0], a[1] + b[1]] }
      case 'sub': { const a = this.bounds(e.a), b = this.bounds(e.b); return [a[0] - b[1], a[1] - b[0]] }
      case 'neg': { const a = this.bounds(e.a); return [-a[1], -a[0]] }
      case 'mulk': { const a = this.bounds(e.a); return e.k >= 0 ? [e.k * a[0], e.k * a[1]] : [e.k * a[1], e.k * a[0]] }
      case 'mul': { const a = this.bounds(e.a), b = this.bounds(e.b), xs = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]].map(v => (Number.isNaN(v) ? 0 : v)); return [Math.min(...xs), Math.max(...xs)] }
      case 'min': { const a = this.bounds(e.a), b = this.bounds(e.b); return [Math.min(a[0], b[0]), Math.min(a[1], b[1])] }
      case 'max': { const a = this.bounds(e.a), b = this.bounds(e.b); return [Math.max(a[0], b[0]), Math.max(a[1], b[1])] }
      case 'divk': { const a = this.bounds(e.a); return [Math.floor(a[0] / e.k), Math.floor(a[1] / e.k)] }
      case 'modk': return [0, e.k - 1]
      case 'ite': { const a = this.bounds(e.a), b = this.bounds(e.b); return [Math.min(a[0], b[0]), Math.max(a[1], b[1])] }
    }
  }
  // A result past its type's range: at 8, 16 and 32 bits modulo 2^n by cases (none where the bounds of the term or the
  // path's facts keep it within); at 64 bits the rule's numbers stop at ±2^53, and an unsigned one below 0 is refused.
  wrap(e: N, ty: IntTy, x: {p: string}, p: Path): N {
    if (ty.bits === 0) return e
    if (ty.ub) {
      const out = I.or(...this.past(e, ...rangeOf(ty), p))
      if (!(out.op === 'const' && !out.v)) { this.refuseWhere(p, out, x, `${(x as SX).text ? `${(x as SX).text}: ` : ''}past ${ty.name ?? tyName(ty)}'s range (signed overflow: undefined behavior)`); this.notes.add(`${ty.name ?? tyName(ty)}: a result past its range is refused (signed overflow is undefined behavior in ${LANG[this.mod.lang] ?? this.mod.lang})`) }
      return e
    }
    const [lo, hi] = rangeOf(ty), [blo0, bhi0] = this.bounds(e)
    if (blo0 >= lo && bhi0 <= hi) return e
    const blo = blo0 >= lo || this.within(e, lo, 'lo', p) ? Math.max(blo0, lo) : blo0, bhi = bhi0 <= hi || this.within(e, hi, 'hi', p) ? Math.min(bhi0, hi) : bhi0
    if (blo >= lo && bhi <= hi) return e
    const name = ty.name ?? tyName(ty), lang = LANG[this.mod.lang] ?? this.mod.lang
    if (ty.bits >= 64) {
      if (!ty.signed && blo < 0) { this.refuseWhere(p, I.cmp('<', e, I.num(0)), x, `a ${name} below 0 (${lang} wraps it to 2^64 − x, past the rule's numbers)`, false); this.notes.add(`${name}: a result below 0 is refused (${lang} would wrap it past 2^53)`) }
      return e
    }
    const m = 2 ** ty.bits, k0 = Math.floor((blo - lo) / m), k1 = Math.floor((bhi - lo) / m)
    this.notes.add(`${name}: a result past its range wraps modulo 2^${ty.bits}, as ${lang}'s does`)
    if (Number.isFinite(k0) && Number.isFinite(k1) && k1 - k0 <= 3) {
      // By cases from the bottom: e at least lo + k·2^n takes e − k·2^n.
      const less = (k: number): N => (k >= 0 ? I.sub(e, I.num(k * m)) : I.add(e, I.num(-k * m)))
      let acc: N = less(k0)
      for (let k = k0 + 1; k <= k1; k++) acc = I.nite(I.cmp('<=', I.num(lo + k * m), e), less(k), acc)
      return acc
    }
    // Many times over (a conversion from a wider type, a product): e − 2^n·⌊(e − lo)/2^n⌋.
    return I.sub(e, I.mulk(m, I.divk(m, I.add(e, I.num(-lo)))))
  }
  // Where e may be past [lo, hi] on the path: below and above, each false where the term's bounds or the path's facts
  // keep it within.
  past(e: N, lo: number, hi: number, p: Path): [B, B] {
    const [blo, bhi] = this.bounds(e)
    return [!Number.isFinite(lo) || blo >= lo || this.within(e, lo, 'lo', p) ? I.F : I.cmp('<', e, I.num(lo)), !Number.isFinite(hi) || bhi <= hi || this.within(e, hi, 'hi', p) ? I.F : I.cmp('<', I.num(hi), e)]
  }
  // Whether e is at least lo (or at most hi) on the path: its conditions and its variables' ranges as facts.
  within(e: N, b: number, side: 'lo' | 'hi', p: Path): boolean {
    if (!Number.isFinite(b)) return false
    const facts: B[] = [...p.pc]
    for (const n of I.varsOf(e).vars) { const ty = this.ints.get(n); if (ty) { const r = rangeOf(ty); if (Number.isFinite(r[0])) facts.push(I.cmp('<=', I.num(r[0]), I.nvar(n))); if (Number.isFinite(r[1])) facts.push(I.cmp('<=', I.nvar(n), I.num(r[1]))) } }
    return nonneg(side === 'lo' ? I.sub(e, I.num(b)) : I.sub(I.num(b), e), {m: {refuse: I.F, pre: I.T} as Model, sorts: new Map(), atoms: facts})
  }
  // --- maps with a nil state, lists, big integers, locks --------------------------------------------------------------
  mapAt(m: V, at: SX, p: Path): Extract<Obj, {k: 'map'}> {
    if (m.t !== 'map' || !p.heap.has(m.id)) return refuse(at, `${at.text}: a map other than the state's`)
    return p.heap.get(m.id) as Extract<Obj, {k: 'map'}>
  }
  mkey(k: V, d: MapDecl, at: SX): K {
    if (d.key === 'num') { if (k.t !== 'num') refuse(at, 'a map key of the wrong kind'); return {op: 'num', e: (k as {e: N}).e} }
    if (k.t !== 'str') return refuse(at, 'a map key of the wrong kind')
    return k.e
  }
  // A map's value at a key: its type's zero where the map doesn't hold it.
  mapRead(m: V, k: V, at: SX, p: Path): {v: V, has: B} {
    const o = this.mapAt(m, at, p), cell = this.cellOf(o, this.mkey(k, o.decl, at), p, at), tys = at.tys as Record<string, IntTy | null>
    const vals = new Map([...cell.vals].map(([f, v]) => {
      const it = tys[f], typed: V = v.t === 'num' && it ? {...v, ty: it} : v
      return [f, this.ite(cell.has, typed, typed.t === 'num' ? {...typed, e: I.num(0)} : typed.t === 'bool' ? {t: 'bool', e: I.F} : typed, at)] as const
    }))
    return {v: o.decl.scalar ? vals.get('value')! : {t: 'struct', ty: String(at.sty), f: new Map(vals)}, has: cell.has}
  }
  mapWrite(m: V, k: V, v: V, at: SX, p: Path): Path {
    const o = this.mapAt(m, at, p), key = this.mkey(k, o.decl, at)
    if (o.origin !== 'state') return refuse(at, 'a write to a map other than the state\'s')
    this.refuseWhere(p, o.nil!, at, 'a write to a nil map (a panic)')
    const q = this.assume(p, I.not(o.nil!))
    if (o.w && !I.same(o.w.key, key)) return refuse(at, `writes ${o.decl.name} at a second key in one step`)
    const vals = new Map<string, V>(o.decl.scalar ? [['value', v]] : o.decl.fields.map(f => [f.name, (v as {f?: Map<string, V>}).f?.get(f.name) ?? refuse(at, 'a map value of the wrong kind')]))
    return {...q, heap: new Map(q.heap).set((m as {id: string}).id, {...o, w: {key, has: I.T, vals}})}
  }
  mapDelete(m: V, k: V, at: SX, p: Path): Path {
    const o = this.mapAt(m, at, p), key = this.mkey(k, o.decl, at)
    if (o.w && !I.same(o.w.key, key)) return refuse(at, `writes ${o.decl.name} at a second key in one step`)
    const vals = new Map<string, V>(o.decl.fields.map(f => [f.name, f.sort.k === 'num' ? {t: 'num', e: I.num(0), ty: {bits: 64, signed: true}} : {t: 'bool', e: I.F}]))
    return {...p, heap: new Map(p.heap).set((m as {id: string}).id, {...o, w: {key, has: I.F, vals}})}
  }
  // A map field set to a new empty map where it is nil (the lazy start Go code makes): its nil flag cleared.
  mapAssign(x: SX, v: V, p: Path): Path {
    if (v.t !== 'map' || v.id !== 'new-map') return refuse(x, 'a map given a second name (a map is a reference: a write through either is a write to both)')
    const [pl, q] = this.place(x, p)
    if (pl.k === 'blank') return q
    const [cur, q2] = this.read(pl, x, q)
    if (cur.t !== 'map') return refuse(x, 'a new map kept other than in a map field of the state')
    const o = this.mapAt(cur, x, q2), nil = o.nil!
    if (!(nil.op === 'const' && nil.v) && !q2.pc.some(c => I.same(c, nil))) return refuse(x, `${o.decl.name} replaced whole (the subset sets a map once, where it is nil)`)
    return {...q2, heap: new Map(q2.heap).set(cur.id, {...o, nil: I.F})}
  }
  listObj(s: V, at: SX, p: Path): Extract<Obj, {k: 'list'}> {
    if (s.t !== 'list' || !p.heap.has(s.id)) return refuse(at, `${at.text}: a slice other than the state's`)
    return p.heap.get(s.id) as Extract<Obj, {k: 'list'}>
  }
  listLen(s: V, at: SX, p: Path): N {
    const o = this.listObj(s, at, p)
    if (o.ops.length) return refuse(at, `${o.decl.name} read after it is written in one step`)
    return o.decl.len !== undefined ? I.num(o.decl.len) : I.nvar(`${o.decl.name}_len`)
  }
  inside(s: V, i: V, at: SX, p: Path): [Extract<Obj, {k: 'list'}>, N, B] {
    const o = this.listObj(s, at, p), idx = this.numv(i, at), len = this.listLen(s, at, p), inside = I.and(I.cmp('<=', I.num(0), idx), I.cmp('<', idx, len))
    this.refuseWhere(p, I.not(inside), at, o.decl.len !== undefined ? `an index outside [0, ${o.decl.len}) (undefined behavior)` : 'an index out of range (a panic)')
    return [o, idx, inside]
  }
  listGet(s: V, i: V, at: SX, p: Path): [V, Path] {
    const [o, idx, inside] = this.inside(s, i, at, p), e = {op: 'cell', map: o.decl.name, key: {op: 'num', e: idx}, field: '$item'} as const
    return [o.decl.fields[0]!.sort.k === 'num' ? {t: 'num', e: e as N, ty: at.ty as IntTy} : {t: 'bool', e: e as B}, this.assume(p, inside)]
  }
  listSet(s: V, i: V, v: V, at: SX, p: Path): Path {
    const [o, idx, inside] = this.inside(s, i, at, p), q = this.assume(p, inside)
    if (o.decl.len !== undefined && o.ops.length) return refuse(at, `a second write to ${o.decl.name} in one step`)
    return {...q, heap: new Map(q.heap).set((s as {id: string}).id, {...o, ops: [{op: 'set', i: idx, x: v, when: I.T}]})}
  }
  // s = append(s, x) and s = s[:len(s)-1] in s's own place; any other list put there is refused.
  listAssign(x: SX, v: V, p: Path): Path {
    const [pl, q] = this.place(x, p)
    if (pl.k === 'blank') return q
    const [cur, q2] = this.read(pl, x, q)
    if ((v.t !== 'push' && v.t !== 'pop') || cur.t !== 'list' || v.id !== cur.id) return refuse(x, 'a slice given a second name, or replaced whole (two slices may share a backing array: append writes into it or not by its capacity)')
    const o = this.listObj(cur, x, q2)
    if (o.ops.length) return refuse(x, `a second write to ${o.decl.name} in one step`)
    const it = o.decl.fields[0]!.sort.k
    if (v.t === 'push' && ((it === 'num' && v.x.t !== 'num') || (it === 'bool' && v.x.t !== 'bool'))) return refuse(x, 'an item of the wrong kind appended')
    return {...q2, heap: new Map(q2.heap).set(cur.id, {...o, ops: [v.t === 'push' ? {op: 'push', x: v.x, when: I.T} : {op: 'pop', when: I.T}]})}
  }
  newBig(v: N, p: Path): [V, Path] {
    const id = `new:${++this.fresh}`
    return [{t: 'ptr', to: {k: 'obj', id, path: []}}, {...p, heap: new Map(p.heap).set(id, {k: 'big', v, origin: 'fresh'})}]
  }
  // A big integer's value through a pointer (by cases; nil fails).
  bigVal(v: V, at: SX, p: Path): [N, Path] {
    if (v.t !== 'ptr') return refuse(at, `${at.text}: a big.Int read through a ${v.t}`)
    const [cs, q] = this.nonNil(v.to, at, p, `a nil *big.Int (${at.text})`)
    let out: N | undefined
    for (const o of [...cs.objs].reverse()) {
      const obj = q.heap.get(o.id)
      if (obj?.k !== 'big' || o.path.length) return refuse(at, 'a big.Int pointer to other than a big.Int')
      out = out === undefined ? obj.v : I.nite(o.c, obj.v, out)
    }
    return [out ?? I.num(0), q]
  }
  bigCall(x: SX, p: Path): [V, Path] {
    const n = String(x.op), zx = x.z as SX, ax = x.args as SX[], ty = x.ty as IntTy
    const [z, q0] = this.ev(zx, p)
    const as: V[] = []
    let q = q0
    for (const a of ax) { const [v, q2] = this.ev(a, q); as.push(v); q = q2 }
    const vals: N[] = []
    const ints = (k: number) => { for (let i = 0; i < k; i++) { const a = as[i]!; if (a.t === 'num') vals.push(a.e); else { const [v, q2] = this.bigVal(a, ax[i]!, q); vals.push(v); q = q2 } } }
    // z = e, z the receiver (its object written where z points), and z returned.
    const set = (e: N): [V, Path] => {
      const [, q2] = this.bigVal(z, zx, q)
      const heap = new Map(q2.heap)
      for (const o of this.cases((z as {to: Ptr}).to).objs) { const obj = heap.get(o.id) as Extract<Obj, {k: 'big'}>; heap.set(o.id, {...obj, v: I.nite(o.c, e, obj.v)}) }
      return [z, {...q2, heap}]
    }
    const sign = (l: N, r: N): N => I.nite(I.cmp('<', l, r), I.num(-1), I.nite(I.cmp('=', l, r), I.num(0), I.num(1)))
    switch (n) {
      case 'Add': ints(2); return set(I.add(vals[0]!, vals[1]!))
      case 'Sub': ints(2); return set(I.sub(vals[0]!, vals[1]!))
      case 'Mul': ints(2); return set(I.mul(vals[0]!, vals[1]!))
      case 'Neg': ints(1); return set(I.neg(vals[0]!))
      case 'Abs': ints(1); return set(I.nmax(vals[0]!, I.neg(vals[0]!)))
      case 'Set': ints(1); return set(vals[0]!)
      case 'SetInt64': case 'SetUint64': return set(this.numv(as[0]!, x))
      case 'Cmp': case 'CmpAbs': {
        const [a, q2] = this.bigVal(z, zx, q); q = q2; ints(1)
        const l = n === 'Cmp' ? a : I.nmax(a, I.neg(a)), r = n === 'Cmp' ? vals[0]! : I.nmax(vals[0]!, I.neg(vals[0]!))
        return [{t: 'num', e: sign(l, r), ty, cmp: [l, r]}, q]
      }
      case 'Sign': { const [a, q2] = this.bigVal(z, zx, q); return [{t: 'num', e: sign(a, I.num(0)), ty, cmp: [a, I.num(0)]}, q2] }
      case 'Int64': case 'Uint64': {
        const [a, q2] = this.bigVal(z, zx, q)
        if (n === 'Uint64') this.refuseWhere(q2, I.cmp('<', a, I.num(0)), x, 'Uint64 of a big.Int below 0 (undefined: Go returns its low bits)', false)
        return [{t: 'num', e: a, ty}, q2]
      }
      case 'IsInt64': { const [, q2] = this.bigVal(z, zx, q); return [{t: 'bool', e: I.T}, q2] }
      case 'String': return refuse(x, 'a big.Int as a string (outside an error\'s text)')
    }
    return refuse(x, `${x.text}: big.Int's ${n} (outside the subset)`)
  }
  // A lock's key: the place it is (of the object, or a local).
  lockKey(x: SX, p: Path): string {
    const [pl] = this.place(x, p)
    if (pl.k === 'local') return `local:${pl.id}.${pl.path.join('.')}`
    if (pl.k === 'heap' && pl.ptr.t === 'ptr' && pl.ptr.to.k === 'obj') return `${pl.ptr.to.id}.${[...pl.ptr.to.path, ...pl.path].join('.')}`
    return refuse(x, 'a mutex not of the object')
  }
  lockCall(x: SX, p: Path): [V, Path] {
    const n = String(x.op), key = this.lockKey(x.pl as SX, p)
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
  // A function of the module inlined, its receiver and arguments bound by id (Go's): its returns joined, each result
  // by the path that returned it, the locks it deferred released at each.
  inline(fn: SFunc, recv: V | undefined, args: V[], at: SX, p: Path): [V, Path] {
    if (fn.why) return refuse(at, fn.why)
    if (this.frames.includes(fn.id)) return refuse(at, `${fn.name}: a recursive call`)
    if (fn.late) return refuse(at, fn.late)
    this.spans.set(fn.id, fn.span)
    let q: Path = {...p, locals: new Map(p.locals), defers: []}
    if (fn.recv && recv) q = this.bindLocal(fn.recv, recv, at, q)
    fn.params.forEach((pa, i) => { if (pa.name) q = this.bindLocal(pa.name, args[i]!, at, q) })
    this.frames.push(fn.id)
    let flow: Flow
    try { flow = this.block(fn.body, q) } finally { this.frames.pop() }
    if (flow.brk?.length) refuse(at, `${fn.name}: a break outside a switch`)
    const rets: [Path, V][] = [...flow.rets, ...(flow.live ? [[flow.live, {t: 'tuple', xs: []}] as [Path, V]] : [])]
    if (flow.live && fn.results) refuse(at, `${fn.name}: a path with no return`)
    if (!rets.length) return [{t: 'opaque', why: 'no return', firm: true}, {...p, pc: [...p.pc, I.F]}]
    const joined = this.join(rets.map(([r, v]) => ({...r, locks: r.locks.filter(k => !r.defers.includes(k)), defers: p.defers, locals: new Map([...r.locals, ...(v as {xs: V[]}).xs.map((x, i) => [`$ret${i}`, x] as const)])})), at)!
    const vals = Array.from({length: fn.results ?? 0}, (_, i) => joined.locals.get(`$ret${i}`)!)
    return [vals.length === 1 ? vals[0]! : {t: 'tuple', xs: vals}, {...joined, locals: new Map(p.locals), defers: p.defers}]
  }
  // An assignment of Go's: each value evaluated (or one of several results, or a map's item and whether it is held),
  // then each target in order: a local bound, a map's item, a list's, a list or a map put back in its place, a place.
  assignGo(s: SS, p: Path): Path {
    const to = s.to as SX[]
    if (s.mapok) { const at = s.mapok as SX, [m, q] = this.ev(at.m as SX, p), [k, q2] = this.ev(at.k as SX, q), cell = this.mapRead(m, k, at, q2); return this.assignTo(to, [cell.v, {t: 'bool', e: cell.has}], q2) }
    if (s.one) {
      const [v, q] = this.ev(s.one as SX, p)
      // (the results of a call left out: each one its value, kept only where nothing reads it)
      if (v.t === 'opaque' && v.ask) return s.decl ? to.reduce((q2, x) => this.bindLocal(String(x.n), v, s, q2), q) : this.assignTo(to, to.map(() => v), q)
      if (v.t !== 'tuple' || (!s.decl && v.xs.length !== to.length)) return refuse(s, String(s.why))
      return s.decl ? to.reduce((q2, x, i) => this.bindLocal(String(x.n), v.xs[i]!, s, q2), q) : this.assignTo(to, v.xs, q)
    }
    let q = p
    const vals: V[] = []
    for (const e of s.xs as SX[]) { const [v, q2] = this.ev(e, q); vals.push(v); q = q2 }
    return this.assignTo(to, vals, q)
  }
  assignTo(l: SX[], vals: V[], p: Path): Path {
    let q = p
    l.forEach((x, i) => {
      const v = vals[i]!
      if (x.bind && !(x.bind === 'new' && q.locals.has(String(x.n)))) { q = this.bindLocal(String(x.n), v, x, q); return }
      if (x.e === 'midx') { const [m, q2] = this.ev(x.m as SX, q), [k, q3] = this.ev(x.k as SX, q2); q = this.mapWrite(m, k, v, x, q3); return }
      if (x.e === 'lidx') { const [sv, q2] = this.ev(x.s as SX, q), [k, q3] = this.ev(x.i as SX, q2); q = this.listSet(sv, k, v, x, q3); return }
      if (x.e === 'no') return refuse(x, String(x.why))
      if (v.t === 'list' || v.t === 'push' || v.t === 'pop') { q = this.listAssign(x, v, q); return }
      if (v.t === 'map') { q = this.mapAssign(x, v, q); return }
      const [pl, q2] = this.place(x, q)
      q = this.write(pl, v, x, q2)
    })
    return q
  }
  // A switch: each case's condition (none before it matched; the default's, none matched), evaluated in order; a case
  // carried into the next by fallthrough, a break out of it joined after.
  switchGo(s: SS, p: Path): Flow {
    let q = p, tag: V | undefined
    if (s.tag) { const [v, q2] = this.ev(s.tag as SX, q); tag = v; q = q2 }
    const cases = s.cases as {list?: SX[], default?: boolean, b: SS[], p: string}[], conds: B[] = []
    let none: B = I.T
    for (const c of cases) {
      if (c.default) { conds.push(I.F); continue }
      let any: B = I.F
      for (const e of c.list!) { const [v, q2] = this.ev(e, q); q = q2; any = I.or(any, tag ? this.eq(tag, v, e, q) : v.t === 'bool' ? v.e : refuse(e, 'a case that isn\'t a condition')) }
      conds.push(I.and(none, any)); none = I.and(none, I.not(any))
    }
    const di = cases.findIndex(c => c.default)
    if (di >= 0) conds[di] = none
    const lives: Path[] = [], rets: [Path, V][] = []
    let carried: Path | undefined
    cases.forEach((c, i) => {
      const entry = conds[i]!.op === 'const' && !(conds[i] as {v: boolean}).v ? undefined : this.assume(q, conds[i]!)
      let into = this.join([...(entry ? [entry] : []), ...(carried ? [carried] : [])], c)
      // (entered and carried into: the join keeps that one or the other got here, which a later join reads)
      if (entry && carried && into) { let k = 0; while (k < entry.pc.length && k < carried.pc.length && I.same(entry.pc[k]!, carried.pc[k]!)) k++; into = this.assume(into, I.or(I.and(...entry.pc.slice(k)), I.and(...carried.pc.slice(k)))) }
      carried = undefined
      if (!into) return
      const f = this.block(c.b, into)
      if (f.live) lives.push(f.live)
      rets.push(...f.rets)
      if (f.brk?.length) lives.push(this.join(f.brk, c)!)
      if (f.ft) { if (i === cases.length - 1) refuse(c, 'fallthrough out of the last case'); carried = f.ft }
    })
    if (di < 0) lives.push(this.assume(q, none))
    const live = this.join(lives, s)
    return {...(live ? {live} : {}), rets}
  }
}

// A pointer by a condition (one case where both are the same).
export const phiP = (c: B, a: Ptr, b: Ptr): Ptr => (c.op === 'const' ? (c.v ? a : b) : JSON.stringify(a) === JSON.stringify(b) ? a : {k: 'phi', c, a, b})
// The values a merge keeps exact (Go's): refused, not made opaque, where two paths make them different.
const firm = (v: V): boolean => ['ptr', 'struct', 'err', 'nil', 'map', 'list', 'push', 'pop'].includes(v.t) || (v.t === 'opaque' && !!v.firm)
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
// What a refutation (or any request of the rule) assumes of the boundary inferred: each answer inferred or tagged
// that it gives a value, as "assumes `callee` may return v". A refutation that assumes none is the code's own.
export function assumed(x: {read?: StepRead}, request: Record<string, unknown> | undefined): string[] {
  const out: string[] = []
  for (const a of x.read?.answers ?? []) {
    if (!a.how || !request || !(a.inputs.name in request)) continue
    // (an integer of the prover's is a pair: x − x$neg; a boolean 0 or 1)
    const none = a.inputs.none && (request[a.inputs.none] === true || request[a.inputs.none] === 1), v = request[a.inputs.name], neg = request[`${a.inputs.name}$neg`]
    const shown = none ? 'None' : /^bool\b/.test(a.sort) ? String(v === true || v === 1) : typeof v === 'number' ? String(v - (typeof neg === 'number' ? neg : 0)) : JSON.stringify(v)
    out.push(`assumes \`${a.key.split('.').pop()}\` may return ${shown} (${a.how}: any ${a.sort})`)
  }
  return out
}
// The text of a file a position names (its name as the reader wrote it: absolute, under the root, or beside the file).
export function sourceOf(mod: {path: string, root: string}, file: string): string | undefined {
  const fs = node<{readFileSync: (f: string, e: string) => string}>('node:fs'), dir = mod.path.replace(/\/[^/]*$/, '')
  for (const f of [file.startsWith('/') ? file : '', mod.path.endsWith(`/${file}`) ? mod.path : '', `${mod.root}/${file}`, `${dir}/${file}`]) if (f) try { return fs.readFileSync(f, 'utf8') } catch { /* the next */ }
  return undefined
}
// The stubbing of a compiled language's check: each answered call's text (from its position to its end) replaced in
// its file by the harness's stub for that answer (in the code's language). Every file a call is answered in,
// rewritten, by its name in the positions; a call with no end (a reader that doesn't say) is a refusal of the check.
export function stubbed(read: StepRead, text: (file: string) => string | undefined, stub: (a: Answer, i: number, call: string) => string): Map<string, string> {
  const edits = new Map<string, [number, number, string][]>(), starts = new Map<string, number[]>()
  read.answers.forEach((a, i) => {
    for (const s of a.at ?? []) {
      // (its place: offsets where the reader gives them, a JVM reader's; else from its position to its end)
      const m = /^(.*):(\d+):(\d+)$/.exec(s.p), e = s.end && /^(\d+):(\d+)$/.exec(s.end)
      if (!m || (!e && !s.span)) throw new Refusal(s.p, `${a.key}: an answered call whose end the reader doesn't give (the check can't stub it)`)
      const [from, to] = s.span ?? [lineCol(m[1]!, Number(m[2]), Number(m[3])), lineCol(m[1]!, Number(e![1]), Number(e![2]))]
      ;(edits.get(m[1]!) ?? edits.set(m[1]!, []).get(m[1]!)!).push([from, to, stub(a, i, (text(m[1]!) ?? '').slice(from, to))])
    }
  })
  function lineCol(f: string, l: number, c: number): number {
    let ls = starts.get(f)
    if (!ls) { const t = text(f) ?? ''; ls = [0]; for (let k = 0; k < t.length; k++) if (t[k] === '\n') ls.push(k + 1); starts.set(f, ls) }
    return (ls[l - 1] ?? 0) + c - 1
  }
  const out = new Map<string, string>()
  for (const [f, es] of edits) {
    let t = text(f) ?? ''
    for (const [a, b, r] of es.sort((x, y) => y[0] - x[0])) t = t.slice(0, a) + r + t.slice(b)
    out.set(f, t)
  }
  return out
}
// The names a reader is asked for (none: the module's classes, for the entry inferred).
export const entryNames = (opts: {entry?: string | string[]}): string[] => (opts.entry === undefined ? [] : Array.isArray(opts.entry) ? opts.entry : [opts.entry])
// The module read into the rule. Unless strict, the boundary is inferred: each run that refuses where the subset's
// inference can go on (a value of other code read, the module's own code outside the subset) adds what the next run
// infers, until one reads (or refuses with what the caller would state to accept it).
export function readStep(mod: SModule, opts: StepOptions): StepRead {
  if (opts.strict) return readOnce(mod, opts, new Stepper(mod, opts))
  const inf: Inferred = {answers: new Map(), cut: new Map()}
  for (let n = 0; ; n++) {
    const g = new Stepper(mod, opts, inf)
    try { return readOnce(mod, opts, g) } catch (e) {
      if (!(e instanceof Refusal)) throw e
      const r = n < 256 ? g.promote(e) : e
      if (r) throw r
    }
  }
}
function readOnce(mod: SModule, opts: StepOptions, g: Stepper): StepRead {
  if (mod.error) refuse(mod.file ?? mod.root ?? '?', mod.error)
  const kept = opts.failures === 'kept', carried = kept && opts.onError !== 'discard'
  let entries = mod.entries
  for (const e of entries) if (e.k === 'missing') refuse(mod.file, `no class or function ${e.name} in ${mod.file}`)
  // No entry: the module's one class whose public methods write its state, and those methods.
  let writing: string[] | undefined
  if (!entryNames(opts).length) {
    if (!g.inf) refuse(mod.file, 'no entry (strict: name the class or the functions)')
    const pub = (r: SRec) => Object.keys(r.methods).filter(m => !m.startsWith('_') && r.methods[m] && g.writesState(r.methods[m]!, new Set(g.mod.funcs[r.methods[m]!]?.params.filter(x => x.self).map(x => x.name) ?? [])))
    const cands = entries.filter((e): e is {k: 'class', rec: string} => e.k === 'class' && pub(g.rec(e.rec, {p: mod.file})).length > 0)
    if (cands.length !== 1) refuse(mod.file, cands.length ? `several classes write their state (${cands.map(e => g.rec(e.rec, {p: mod.file}).short).join(', ')}): name one (entry)` : 'no class whose public methods write its state: name the entry (a class, or functions)')
    entries = cands
    writing = pub(g.rec(cands[0]!.rec, {p: mod.file}))
    g.notes.add(`the entry inferred: ${g.rec(cands[0]!.rec, {p: mod.file}).short}, the class whose public methods write its state${opts.methods ? '' : ` (${writing.join(', ')}; the others read it)`}`)
  }
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
    const fresh: Path = {pc: [], locals: new Map(), heap: new Map([['this', {k: 'rec', ty: cls, f: new Map(), origin: 'state'}]]), called: [], locks: [], defers: []}
    g.init = true
    g.method = '__init__'
    const r0 = g.refusals.length
    let made: Path
    const initId = r.methods.__init__
    if (initId) g.entryIds.add(initId)
    if (r.kinds.some(k => k.startsWith('generic:'))) refuse(r, `${r.short}: a generic type (its methods read a type parameter)`)
    const rustNew = mod.lang === 'rust' ? r.methods.new : undefined
    if (rustNew) g.entryIds.add(rustNew)
    if (mod.lang === 'rust' && rustNew) {
      // Rust: the object is what `new` returns, its arguments the rule's params (named after the fields' names).
      for (const f of r.fields) g.fieldNames.add(f.name)
      const fn = g.func(rustNew, at)
      const args: V[] = []
      let p = fresh
      for (const pa of fn.params.filter(x => !x.self)) {
        const [v, a] = g.input(pa.name, pa.t, fn, p, 'param')
        if (a.k === 'inert') refuse(fn, `${r.short}::new(${pa.name}): an argument of ${g.why(pa.t)}`)
        args.push(v); ctor.push([pa.name, a])
      }
      const [out, p2] = g.callFunc(fn, undefined, args, [], {e: 'call', p: fn.p, text: `${r.short}::new()`}, p, true)
      const obj = out.t === 'ref' ? p2.heap.get(out.id) : undefined
      if (obj?.k !== 'rec' || obj.ty !== cls) refuse(fn, `${r.short}::new returns ${out.t === 'ref' ? 'another object' : `a ${out.t}`} (the subset reads a new() that returns Self)`)
      made = {...p2, heap: new Map(p2.heap).set('this', {...(obj as Extract<Obj, {k: 'rec'}>), origin: 'state'})}
      if (ctor.length) g.notes.add(`${r.short} made by ${r.short}::new: its arguments are the rule's params`)
    } else if (mod.lang === 'rust') {
      if (!r.kinds.includes('default')) refuse(r, `${r.short}: no new() and no derived Default (the subset makes the object by one of them)`)
      const f = new Map<string, V>()
      for (const fd of r.fields) f.set(fd.name, defaultOf(fd.t, at))
      made = {...fresh, heap: new Map(fresh.heap).set('this', {k: 'rec', ty: cls, f, origin: 'state'})}
      g.notes.add(`${r.short}: made by its derived Default`)
    } else if (initId) {
      const fn = g.func(initId, at)
      // The fields it sets (named first: the state's names are the fields').
      const scan = (ss: SS[]) => { for (const st of ss) { const to = st.to as SX | undefined; if (st.s === 'set' && to?.e === 'get' && (to.x as SX).e === 'var' && (to.x as SX).n === 'self') g.fieldNames.add(String(to.f)); if (st.s === 'if') { scan(st.then as SS[]); scan(st.else as SS[]) } if (st.s === 'with') scan(st.body as SS[]) } }
      scan(fn.body)
      const args: V[] = [], kw: [string, V][] = []
      let p = fresh
      // (a keyword argument given as one)
      const give = (pa: SParam, v: V) => { if (pa.kw) kw.push([pa.name, v]); else args.push(v) }
      for (const pa of fn.params.filter(x => !x.self && !x.star)) {
        const dep = opts.stores?.[pa.name] ? undefined : g.injected(pa, fn, r)
        if (opts.stores?.[pa.name] || dep) {
          const id = `store:${pa.name}`; p.heap.set(id, {k: 'store', name: pa.name}); g.initHeap.set(id, {k: 'store', name: pa.name}); give(pa, {t: 'ref', id}); ctor.push([pa.name, {k: 'store', name: pa.name}])
          if (!dep || dep.keyed) g.storeKeyed.add(pa.name)
          if (dep?.ty) g.storeTypes.set(pa.name, dep.ty)
          if (dep) g.notes.add(`${r.short}(${pa.name}): an injected dependency (inferred: ${pa.inject ? 'marked so' : `of ${dep.ty ? g.mod.recs[dep.ty]?.short ?? dep.ty : 'no stated type'}, its methods called`}), the check giving one that ${dep.keyed ? 'keeps what is set' : 'answers its calls'}`)
          continue
        }
        if (pa.dflt && !g.scalar(pa.t.k === 'opt' ? pa.t.of : pa.t)) { ctor.push([pa.name, {k: 'dflt'}]); const [d, p2] = g.ev(pa.dflt, p); give(pa, d); p = p2; continue }
        const [v, a] = g.input(pa.name, pa.t, fn, p, 'param')
        if (a.k === 'inert') refuse(fn, `${r.short}(${pa.name}): a constructor argument of ${g.why(pa.t)} (state it as a store, or give it a default)`)
        give(pa, v); ctor.push([pa.name, a])
      }
      const [, p2] = g.callFunc(fn, {t: 'ref', id: 'this'}, args, kw, {e: 'call', p: fn.p, text: `${r.short}()`}, p, false)
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
    // (what the constructor refuses, a narrowing cast's value that doesn't fit, is the precondition's)
    pre = I.and(I.not(I.or(...g.fails)), I.not(I.or(...g.paramsOut)), I.not(I.or(...g.refusals.splice(r0))))
    g.fails = []
    g.init = false
    // (a field a framework injects, @Autowired or @Inject on it: the store the check gives, named by the field)
    for (const fd of g.inf ? r.fields.filter(f => f.inject && !(made.heap.get('this') as Extract<Obj, {k: 'rec'}>).f.has(f.name)) : []) {
      const id = `store:${fd.name}`, o: Obj = {k: 'store', name: fd.name}
      made.heap.set(id, o); g.initHeap.set(id, o); g.injectedFields.push(fd.name)
      ;(made.heap.get('this') as Extract<Obj, {k: 'rec'}>).f.set(fd.name, {t: 'ref', id})
      if (fd.t.k === 'rec') g.storeTypes.set(fd.name, fd.t.name)
      if (g.callsOn(r, [fd.name]).some(m => !!keyShape(m))) g.storeKeyed.add(fd.name)
      g.notes.add(`${r.short}.${fd.name}: an injected dependency (marked so), the check giving one`)
    }
    const self = made.heap.get('this') as Extract<Obj, {k: 'rec'}>
    for (const [f, v] of self.f) { const t = g.declared.get(`this.${f}`) ?? r.fields.find(x => x.name === f)?.t; tree.push({path: [f], v, ...(t && t.k !== 'any' ? {t} : {})}) }
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
        const sort: Var['sort'] = inner && g.scalar(inner) ? g.scalar(inner)! : v.t === 'num' ? {k: 'num'} : v.t === 'bool' ? {k: 'bool'} : v.t === 'str' ? {k: 'str'} : v.t === 'choice' ? {k: 'choice', values: lvalues(v.e)} : v.t === 'opt' && g.scalar({k: v.v.t === 'num' ? 'int' : v.v.t === 'bool' ? 'bool' : 'str'} as SType) ? (v.v.t === 'num' ? {k: 'num'} : v.v.t === 'bool' ? {k: 'bool'} : {k: 'str'}) : refuse(at, `${path.join('.')}: a field of no scalar type`)
        if (v.t === 'str' && sort.k === 'choice' && v.e.op === 'slit') v = {t: 'choice', e: I.llit(v.e.value, sort.values)}
        const optional = v.t === 'none' || v.t === 'opt' || decl?.k === 'opt'
        const vr = leaf(sort.k === 'num' ? 'num' : sort.k, g.newVar(name, sort, 'state'), isFloat)
        if (inner) g.typed(vr, inner, 'state')
        const lf = leaves[leaves.length - 1]!; if (decl) lf.t = decl
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
    ? (opts.methods ?? writing ?? Object.keys(r!.methods).filter(m => !m.startsWith('_') && r!.methods[m])).map(m => (r!.methods[m] ? g.func(r!.methods[m]!, at) : refuse(at, `no method ${r!.short}.${m} in ${mod.file}`)))
    : entries.map(e => g.func((e as {id: string}).id, at))
  if (!chosen.length) refuse(at, `${cls ? r!.short : 'the entry'} has no methods to read`)
  for (const f of chosen) g.entryIds.add(f.id)
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
    g.sel = sel
    let p: Path = {pc: [sel], locals: new Map(), heap: new Map(g.initHeap), called: [], locks: [], defers: []}
    const args: V[] = [], pargs: [string, PArg][] = []
    if ((fn as {recv?: string}).recv === 'value') refuse(fn, `${fn.name}: a method that takes self by value (it consumes the object)`)
    if ((fn as {generic?: boolean}).generic) refuse(fn, `${fn.name}: a generic method`)
    for (const pa of fn.params.filter(x => !x.self && !x.star)) {
      const [v, a] = g.input(`${names.length > 1 ? `${fn.name}_` : ''}${pa.name}`, pa.t, fn, p)
      args.push(v); pargs.push([pa.name, a])
    }
    g.fails = []; g.failPaths = []
    let [out, q] = g.callFunc(fn, cls ? {t: 'ref', id: 'this'} : undefined, args, [], {e: 'call', p: fn.p, text: fn.name}, p, fn.async ?? false)
    // A Result returned: its Err is the step's failure (Rust's error results, later Go's and Elixir's), its Ok the value.
    if (out.t === 'res') { g.fail(q, I.not(out.ok), fn, `${fn.name} returns an Err`); q = g.assume(q, out.ok); out = out.v }
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
    // (None holds its sort's zero: the value read where the field is Some, the zero elsewhere)
    const z = zeroOf(s), inOpt = (w: V): V => (v.t !== 'opt' ? w : w.t === 'num' && z.t === 'num' ? {t: 'num', e: I.nite(v.has, w.e, z.e)} : w.t === 'bool' && z.t === 'bool' ? {t: 'bool', e: I.bite(v.has, w.e, z.e)} : w.t === 'str' && z.t === 'str' ? {t: 'str', e: I.kite(v.has, w.e, z.e)} : w.t === 'choice' && z.t === 'choice' ? {t: 'choice', e: I.lite(v.has, w.e, z.e)} : w)
    const val = v.t === 'opt' ? inOpt(v.v) : v.t === 'none' ? z : v
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
    const ws = finals.map(f => { const w0 = (f.path.heap.get(id) as Extract<Obj, {k: 'map'}> | undefined)?.w; return w0 && {key: w0.key, has: w0.has, vals: Object.fromEntries([...w0.vals].map(([f2, v]) => [f2, termOf(v, at)]))} })
    // (a failure kept, the cell as it was there)
    const w = mapWritesOf(g, d, finals.map(f => f.sel), ws, (i, w2, base) => { if (!kept || carried) return w2; const fl = failedOf(finals[i]!), b = base(w2.key); return {key: w2.key, has: I.bite(fl, b.has, w2.has), vals: Object.fromEntries(Object.entries(w2.vals).map(([f, t]) => [f, iteTerm(fl, b.vals[f]!, t)]))} })
    if (w) mapWrites[d.name] = w
  }
  // What each method returns, and whether it failed: the step's result.
  const results: Model['results'] = {}, resultKinds: StepRead['results'] = {}
  let failedVar: Var | undefined
  if (kept) { failedVar = g.newVar('failed', {k: 'bool'}, 'state', 'whether the step failed (an exception raised): the state is as it was'); }
  for (const [i, f] of finals.entries()) {
    const fn = chosen[i]!
    const out = f.out!
    let kind: 'none' | 'scalar' | 'maybe' = 'none', rv: Var | undefined, rn: Var | undefined
    // (a result of other code left out by inference: the step's result is kept, so its value is read)
    const asked = out.t === 'opaque' ? out : out.t === 'opt' && out.v.t === 'opaque' ? out.v : undefined
    if (asked?.ask) refuse(fn, `${fn.name} returns ${asked.why} (a result the rule keeps)`)
    if (out.t === 'num' || out.t === 'bool' || out.t === 'str' || out.t === 'choice' || out.t === 'opt') {
      const inner = out.t === 'opt' ? out.v : out
      if (inner.t === 'num' || inner.t === 'bool' || inner.t === 'str' || inner.t === 'choice') {
        const sort: Var['sort'] = inner.t === 'num' ? {k: 'num'} : inner.t === 'bool' ? {k: 'bool'} : inner.t === 'str' ? {k: 'str'} : {k: 'choice', values: lvalues(inner.e)}
        rv = g.newVar(`${fn.name}_result`, sort, 'state', `what ${fn.name} returned, at the step that called it (its default at others)`)
        // (a kept result of a fixed-width type within its range: a law, as a field's is)
        const rt = g.intTy(fn.ret?.k === 'opt' || fn.ret?.k === 'res' ? fn.ret.of : fn.ret ?? {k: 'any'})
        if (rt) g.ints.set(rv.name, rt)
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
  const stores: StepRead['stores'] = Object.fromEntries([...new Set([...Object.keys(opts.stores ?? {}), ...g.storeDecls.keys()])].map(n => [n, {...g.storeDecl(n), async: g.storeAsync[n] ?? {}}]))
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
  // A fixed-width field within its type's range (every state of the code is).
  laws.push(...rangeLaws(state, g.ints))
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
  // A start that divides (a constructor's `limit / 2`): each quotient of the params a param of its own, which the
  // precondition fixes (k·q ≤ a < k·q + k) and the check computes from the others (a start reads the params alone,
  // and a quotient is no term over them).
  const pnames = new Set(g.params.map(v => v.name)), qs = new Map<string, Var>()
  const ok = (a: N) => { const r = I.varsOf(a); return !r.maps.size && [...r.vars].every(n => pnames.has(n)) }
  const qOf = (k: number, a: N): N => {
    const key = I.keyOf({k, a})
    let q = qs.get(key)
    if (!q) {
      q = g.newVar(`${[...I.varsOf(a).vars][0] ?? 'q'}_div${k}`, {k: 'num'}, 'param', `⌊${k === 1 ? '' : 'the start\'s dividend / '}${k}⌋ of the params (fixed by the precondition: a start divides)`)
      ;(q as Var & {derived?: N}).derived = {op: 'divk', k, a}
      qs.set(key, q)
      pre = I.and(pre, I.cmp('<=', I.mulk(k, I.nvar(q.name)), a), I.cmp('<', a, I.add(I.mulk(k, I.nvar(q.name)), I.num(k))))
    }
    return I.nvar(q.name)
  }
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const lift = (t: any): any => {
    if (Array.isArray(t)) return t.map(lift)
    if (!t || typeof t !== 'object') return t
    if ((t.op === 'divk' || t.op === 'modk') && t.k > 1) { const a = lift(t.a) as N; if (ok(a)) return t.op === 'divk' ? qOf(t.k, a) : I.sub(a, I.mulk(t.k, qOf(t.k, a))) }
    return Object.fromEntries(Object.entries(t).map(([k, v]) => [k, lift(v)]))
  }
  for (const [n, t] of Object.entries(init)) init[n] = lift(t) as Term
  pre = lift(pre) as B
  const model: Model = {
    kind: cls ? 'a class and its methods' : names.length > 1 ? 'functions, each a request' : 'a function, each call a request',
    name: cls ? g.rec(cls, at).short : names.length === 1 ? names[0]! : mod.module.split('.').pop()!, shape: 'class', file: mod.file, entry: cls ? g.rec(cls, at).short : names.join(', '),
    params: g.params, inputs, state, maps, init, writes, mapWrites, outputs,
    refuse: refuseB, pre, layout, events, notes: [...g.notes], hints: g.hints, ...(ev ? {event: ev.name} : {}), results, laws,
  }
  return {ints: Object.fromEntries(g.ints), ...(g.madeAt ? {madeAt: g.madeAt.name} : {}), model, leaves, args: argsOf, answers: [...g.answers.values()], ctor, kept, arms: [...g.arms].map(a => { const i = a.lastIndexOf(':'); return [a.slice(0, i), Number(a.slice(i + 1))] }), ...(cls ? {cls} : {}), stores, results: resultKinds, ...(g.injectedFields.length ? {inject: g.injectedFields} : {})}
}
// A type's range (64 bits and wider: the rule's numbers stop at ±2^53 before the type's do, and are refused there).
export const rangeOf = (ty: IntTy): [number, number] => (ty.bits === 0 || ty.bits >= 64 ? (ty.signed ? [-Infinity, Infinity] : [0, Infinity]) : ty.signed ? [-(2 ** (ty.bits - 1)), 2 ** (ty.bits - 1) - 1] : [0, 2 ** ty.bits - 1])
// A value of the same kind as v, its zero (unwrap_or_default).
const zeroLike = (v: V): V => (v.t === 'num' ? {t: 'num', e: I.num(0), ...(v.ty ? {ty: v.ty} : {})} : v.t === 'bool' ? {t: 'bool', e: I.F} : v.t === 'str' ? {t: 'str', e: {op: 'slit', value: ''}} : v.t === 'choice' ? {t: 'choice', e: I.llit(lvalues(v.e)[0]!, lvalues(v.e))} : {t: 'opaque', why: 'a default of no scalar kind'})
// A derived Default's value of a type (a Rust field's): 0, false, "", None, the first variant.
const defaultOf = (t: SType, at: {p: string}): V => {
  if (t.k === 'int' || t.k === 'float') return {t: 'num', e: I.num(0)}
  if (t.k === 'bool') return {t: 'bool', e: I.F}
  if (t.k === 'str') return {t: 'str', e: {op: 'slit', value: ''}}
  if (t.k === 'opt') return {t: 'none'}
  return refuse(at, `a Default of ${t.k} (the subset makes numbers, booleans, strings and Options)`)
}
// A choice term's values (an ite's are its branches').
const lvalues = (e: L): string[] => (e.op === 'ite' ? lvalues(e.a) : e.values)
const zeroRaw = (s: Var['sort']): Raw => (s.k === 'num' ? 0 : s.k === 'bool' ? false : s.k === 'choice' ? s.values[0]! : '')
const zeroOf = (s: Var['sort']): V => (s.k === 'num' ? {t: 'num', e: I.num(0)} : s.k === 'bool' ? {t: 'bool', e: I.F} : s.k === 'choice' ? {t: 'choice', e: I.llit(s.values[0]!, s.values)} : {t: 'str', e: {op: 'slit', value: ''}})
// A map's writes, the methods' together: each by the method called (where one writes none, the cell as it was).
type CellW = {key: K, has: B, vals: Record<string, Term>}
export function mapWritesOf(g: Stepper, d: MapDecl, sels: B[], ws: (CellW | undefined)[], fix: (i: number, w: CellW, base: (k: K) => CellW) => CellW = (_, w) => w): CellW | undefined {
  if (!ws.some(Boolean)) return undefined
  const key0 = ws.find(Boolean)!.key, base = (k: K): CellW => { const c = g.baseCell(d, k); return {key: k, has: c.has, vals: Object.fromEntries([...c.vals].map(([f, v]) => [f, {s: v.t === 'num' ? 'num' : v.t === 'choice' ? 'choice' : 'bool', e: (v as {e: N}).e} as Term]))} }
  let acc: CellW | undefined
  for (let i = sels.length - 1; i >= 0; i--) {
    const w = ws[i] ? fix(i, ws[i]!, base) : base(acc?.key ?? key0), c = sels[i]!
    acc = acc === undefined ? w : {key: I.kite(c, w.key, acc.key), has: I.bite(c, w.has, acc.has), vals: Object.fromEntries(Object.entries(w.vals).map(([f, t]) => [f, iteTerm(c, t, acc!.vals[f]!)]))}
  }
  return acc
}
// Each fixed-width variable within its type's range: a law every state of the code keeps.
export const rangeLaws = (state: Var[], ints: Map<string, IntTy>): string[] => state.flatMap(v => {
  const ty = ints.get(v.name), law = (b: string) => [`r.law(${JSON.stringify(`${v.name} within its type's range`)}, ({${v.name}}) => ${v.name}.${b})`]
  if (!ty || v.sort.k !== 'num') return []
  const [lo, hi] = rangeOf(ty)
  return Number.isFinite(hi) ? law(`atMost(${hi}).and(${v.name}.atLeast(${lo}))`) : lo === 0 ? law('atLeast(0)') : []
})
export const varTerm = (v: Var): Term => (v.sort.k === 'num' ? {s: 'num', e: I.nvar(v.name)} : v.sort.k === 'bool' ? {s: 'bool', e: I.bvar(v.name)} : v.sort.k === 'choice' ? {s: 'choice', e: {op: 'var', name: v.name, values: v.sort.values}} : {s: 'str', e: {op: 'svar', name: v.name}})
export function iteTerm(c: B, a: Term, b: Term): Term {
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
export type Harness = {cmd: string, args: string[], env?: Record<string, string>, hello: Record<string, unknown>, error?: string}
export type StepEvidence = Evidence & {runMs: number}
export function checkStep(h: Harness, read: StepRead, r: Rule, sorts: Sorts, opts: StepOptions): StepEvidence {
  const o = opts.check ?? {}, m = read.model, bound = o.bound ?? 12
  const fs = node<FS>('node:fs'), cp = node<{execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string, spawn: (f: string, a: string[], o: Record<string, unknown>) => {kill: () => void}}>('node:child_process'), os = node<{tmpdir: () => string}>('node:os')
  const work = fs.mkdtempSync(`${os.tmpdir()}/gdp-stepcheck-`)
  let child: {kill: () => void} | undefined, wi = -1, ro = -1
  const empty = {runs: 0, requests: 0, fromStates: 0, probes: {conditions: 0, witnesses: 0, steps: 0}, refusedBoth: 0, outside: 0, edge: 0, compiledAgreed: 0, coverage: {arms: 0, hit: 0, missed: []}, ms: 0, runMs: 0}
  try {
    if (h.error) return {...empty, mismatch: h.error}
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
    const hi = ask({op: 'hello', ...h.hello, leaves: read.leaves, ctor: read.ctor, answers: read.answers, kept: read.kept, cls: read.cls ?? null, stores: read.stores, arms: read.arms, discard: opts.onError === 'discard', ...(read.inject ? {inject: read.inject} : {})})
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
    const build = (a: PArg, inputs: Record<string, Raw>): unknown => (a.k === 'in' ? {in: inputs[a.name] ?? a.z ?? 0, ...(a.float ? {float: true} : {}), ...(a.sym ? {sym: true} : {})} : a.k === 'opt' ? (inputs[a.none] === true ? {none: true} : build(a.v, inputs)) : a.k === 'rec' ? (a.f.length ? {rec: a.cls, f: Object.fromEntries(a.f.map(([f, x]) => [f, build(x, inputs)]))} : {inert: true}) : a.k === 'inert' ? {inert: true} : a.k === 'store' ? {store: a.name} : {dflt: true})
    const ctorArgs = (params: Record<string, Raw>) => read.ctor.map(([n, a]) => [n, build(a, params)])
    let now = 0, inputsNow: Record<string, Raw> = {}
    // (an answer outside its type is no value the callee returns: the request is outside what the check compares)
    const answersOf = () => Object.fromEntries(read.answers.map(a => {
      const v = inputsNow[a.inputs.name] ?? 0, ty = read.ints[a.inputs.name], n = Number(v)
      if (ty && !(a.inputs.none && inputsNow[a.inputs.none] === true)) { const [lo, hi] = rangeOf(ty); if (n < lo || n > hi) throw new Outside(`${a.key} answers ${String(v)}, outside its type`) }
      return [a.key, a.inputs.none && inputsNow[a.inputs.none] === true ? {none: true} : {in: v, ...(a.inputs.float ? {float: true} : {})}]
    }))
    let coverage: Coverage | undefined
    const r0 = performance.now()
    const side: CodeSide = {
      make: params => { const res = ask({op: 'new', a: ctorArgs(params), now: read.madeAt ? params[read.madeAt] : 0}); return res.err !== undefined ? {ok: false, error: JSON.stringify(res.err)} : {ok: true, value: res.id} },
      at: (s, params) => { const res = ask({op: 'at', a: ctorArgs(params), now: read.madeAt ? params[read.madeAt] : 0, state: snapJson(s)}); return res.bad ? undefined : res.id },
      snapOf: self => { const res = ask({op: 'get', id: self}); if (res.error) throw new Error(JSON.stringify(res.error)); return toSnap(res.state as Record<string, unknown>) },
      call: (self, e, args) => {
        const res = ask({op: 'call', id: self, m: e.call, a: args, now, answers: answersOf()}) as {out?: unknown, err?: string, frame?: string, bad?: string}
        if (res.frame) throw new Error(`the code changes ${res.frame}, a field the rule leaves out`)
        if (res.bad !== undefined) return {ok: false, error: `the code can't be given it (${res.bad})`}
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
  const unsigned = Object.fromEntries([...read.model.inputs, ...read.model.params].filter(v => read.ints[v.name] && !read.ints[v.name]!.signed).map(v => [v.name, 'nat' as const]))
  const x = fromModel(read.model, mod.file, {...unsigned, ...opts.domains}, notes, (rule, sorts) => checkStep(h(read), read, rule, sorts, opts))
  return {...x, read}
}
