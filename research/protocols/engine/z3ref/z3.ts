/* eslint-disable */
// Z3 as the engine's oracle (exp/z3 only, research/protocols/engine/DESIGN.md "Z3 as the oracle"): a law's two goals
// (its start, and its step with every law of the set assumed) written as SMT-LIB with the laws universally quantified
// over the naturals, decided by Z3's MBQI, a model read back into a kernel witness (scalars, params and inputs by name,
// each map, carried map and function at every key its reads take over the model's elements). Untrusted: it chooses
// and drops candidates only; every verdict the engine returns is the kernel's prove() of the final set.
//
// The encoding is the kernel's own (kernel.ts's obligations): every name a natural, a map, a carried map and a function
// each an Int → Int function, naturals at every key; truncated subtraction; a plain or quantified flag a 0/1 name equal
// to its condition (a quantified one as a ∀); the state after the step a substitution over the state before (a write at
// one key an if over the key read, a write at every key its value at the key read); the conclusion at fresh names (the
// law's first key x#, its further keys by their own names).
import {Worker} from 'node:worker_threads'
import {type C, type E, type Law, type Machine} from '../../../../core/machine.ts'
import {type Subst, substC, substE} from '../../../../kernel/kernel.ts'

// --- the worker, called synchronously -------------------------------------------------------------------------------
let worker: Worker | undefined, head: Int32Array<SharedArrayBuffer> = new Int32Array(new SharedArrayBuffer(8)), body: Uint8Array<SharedArrayBuffer> = new Uint8Array(new SharedArrayBuffer(8))
const dec = new TextDecoder(), loaded = new Map<string, string>()
const boot = () => {
  const sab = new SharedArrayBuffer(8 + (1 << 25))
  head = new Int32Array(sab, 0, 2); body = new Uint8Array(sab, 8)
  worker = new Worker(new URL('./z3worker.ts', import.meta.url).pathname, {workerData: {sab}})
  worker.unref()
  if (Atomics.wait(head, 0, 0, 60_000) === 'timed-out') throw new Error('z3 worker did not start')
  Atomics.store(head, 0, 0)
  loaded.clear()
}
const call = (ctx: string, text: string, hardMs: number): string | undefined => {
  if (!worker) boot()
  Atomics.store(head, 0, 0)
  worker!.postMessage({ctx, text})
  if (Atomics.wait(head, 0, 0, hardMs) === 'timed-out') { void worker!.terminate(); worker = undefined; stats.restarts++; return undefined }
  const s = dec.decode(body.slice(0, head[1]!))
  Atomics.store(head, 0, 0)
  return s
}

// --- statistics -------------------------------------------------------------------------------------------------------
export const stats = {restarts: 0, rows: [] as {kind: string, ms: number, res: string}[], reasons: new Map<string, number>()}
export const z3Summary = () => {
  const ms = stats.rows.filter(r => r.kind === 'step').map(r => r.ms).sort((a, b) => a - b), all = stats.rows.map(r => r.ms).sort((a, b) => a - b)
  const cnt = (res: string) => stats.rows.filter(r => r.res === res).length
  const p = (xs: number[], f: number) => (xs.length ? xs[Math.min(xs.length - 1, Math.floor(f * xs.length))]! : 0)
  const mean = (xs: number[]) => (xs.length ? xs.reduce((a, b) => a + b, 0) / xs.length : 0)
  return {queries: stats.rows.length, step: ms.length, sat: cnt('sat'), unsat: cnt('unsat'), unknown: cnt('unknown'), meanMs: Math.round(mean(all)), p95Ms: Math.round(p(all, 0.95)),
    stepMeanMs: Math.round(mean(ms)), stepP95Ms: Math.round(p(ms, 0.95)), restarts: stats.restarts, reasons: JSON.stringify(Object.fromEntries(stats.reasons))}
}

// --- keys as radix sums -------------------------------------------------------------------------------------------------
// models.ts's encoding: a relation over two sorts at a·64 + b (b < 64). A map every read of which in the step is such a
// sum is a function of its digits, so Z3 matches its reads as tuples (EPR's shape) instead of solving 64a + b = 64c + d
// in integers, and an equality of two such sums is the equality of their digits. This assumes each lower digit below 64
// (the rules' assumptions and the views' frames say so); a key that isn't such a sum is read by div and mod.
const RADIX = 64
let arity = new Map<string, number>()
type Flat = {parts: [number, E][], c: number}
const flat = (e: E, k = 1, out: Flat = {parts: [], c: 0}): Flat => {
  if (e.op === 'add') { flat(e.a, k, out); flat(e.b, k, out) } else if (e.op === 'mul') flat(e.a, k * e.k, out)
  else if (e.op === 'const') out.c += k * e.value
  else out.parts.push([k, e])
  return out
}
const powerOf = (k: number): number => { let i = 0, v = 1; while (v < k) { v *= RADIX; i++ } return v === k ? i : -1 }
// The digits of a key over n places, the highest first (a constant's own digits where no term is), or undefined.
const digitsOf = (e: E, n: number): E[] | undefined => {
  const l = flat(e), ds: (E | undefined)[] = Array(n).fill(undefined)
  for (const [k, t] of l.parts) { const i = powerOf(k); if (i < 0 || i >= n || ds[i]) return undefined; ds[i] = t }
  if (l.c < 0) return undefined
  let c = l.c
  for (let i = 0; i < n && c; i++) { const d = i === n - 1 ? c : c % RADIX; if (d) { if (ds[i]) return undefined; ds[i] = {op: 'const', value: d} } c = (c - d) / RADIX }
  if (l.parts.length && !ds[n - 1]) return undefined
  return ds.reverse().map(d => d ?? {op: 'const', value: 0})
}
const topPower = (e: E): number => { const l = flat(e); let top = 0; for (const [k] of l.parts) { const i = powerOf(k); if (i < 0) return -1; top = Math.max(top, i) } return top }
const keyDigits = (map: string, key: E): E[] | undefined => { const n = arity.get(map) ?? 1; return n === 1 ? [key] : digitsOf(key, n) }
// (an equality of two radix sums of two digits or more: digit by digit)
const eqSplit = (a: E, b: E): [E, E][] | undefined => {
  const ta = topPower(a), tb = topPower(b), top = Math.max(ta, tb)
  if (top < 1 || ta < 0 || tb < 0 || top + 1 > Math.max(1, ...arity.values())) return undefined
  const da = digitsOf(a, top + 1), db = digitsOf(b, top + 1)
  return da && db ? da.map((d, i) => [d, db[i]!]) : undefined
}
type Read = {map: string, key: E, bound: string[]}
const arityOf = (reads: Read[], maps: string[]): Map<string, number> => {
  const out = new Map<string, number>()
  for (const mp of maps) {
    const rs = reads.filter(r => r.map === mp), tops = rs.map(r => topPower(r.key))
    out.set(mp, tops.some(t => t < 0) || !rs.length ? 1 : Math.max(...tops) + 1)
  }
  return out
}
// The digits a bound key splits into: n where every use of it is the whole key of a map of n digits, else 1.
const splitArity = (c: C, k: string): number => {
  let n = 0, bad = false
  const go = (u: E | C): void => {
    if (bad) return
    switch (u.op) {
      case 'var': if (u.name === k) bad = true; return
      case 'const': case 'flag': return
      case 'get': { const a = arity.get(u.map) ?? 1; if (u.key.op === 'var' && u.key.name === k) { if (a < 2 || (n && n !== a)) bad = true; else n = a; return } go(u.key); return }
      case 'if': go(u.c); go(u.then); go(u.else); return
      case 'mul': go(u.a); return
      case 'add': case 'sub': case 'min': case 'max': case 'prod': case '<': case '<=': case '=': go(u.a); go(u.b); return
      case 'and': case 'or': u.xs.forEach(go); return
      case 'not': go(u.x); return
      case 'all': if (![u.key, ...(u.keys ?? [])].includes(k)) go(u.c); return
    }
  }
  go(c)
  return bad ? 1 : Math.max(1, n)
}

// --- normal form: every bound key renamed apart (so a name is one sort's), a bare radix key split into its digits -------
let freshN = 0
const vr = (name: string): E => ({op: 'var', name})
function norm(c: C): C {
  switch (c.op) {
    case 'all': {
      const ren: Record<string, E> = {}, keys: string[] = [], lows: C[] = []
      for (const k of [c.key, ...(c.keys ?? [])]) {
        const n = splitArity(c.c, k)
        if (n < 2) { const nk = `${k}$${freshN++}`; ren[k] = vr(nk); keys.push(nk); continue }
        const id = freshN++, ds = Array.from({length: n}, (_, i) => `${k}$${id}d${n - 1 - i}`)
        ren[k] = ds.reduce<E>((acc, d, i) => (i === 0 ? vr(d) : {op: 'add', a: {op: 'mul', k: RADIX, a: acc}, b: vr(d)}), {op: 'const', value: 0})
        keys.push(...ds); lows.push(...ds.slice(1).map((d): C => ({op: '<', a: vr(d), b: {op: 'const', value: RADIX}})))
      }
      let body = norm(substC(c.c, {vars: ren, maps: {}, flags: {}}))
      if (lows.length) body = {op: 'or', xs: [{op: 'not', x: {op: 'and', xs: lows}}, body]}
      return {op: 'all', key: keys[0]!, ...(keys.length > 1 ? {keys: keys.slice(1)} : {}), c: body}
    }
    case 'not': return {op: 'not', x: norm(c.x)}
    case 'and': case 'or': return {op: c.op, xs: c.xs.map(norm)}
    default: return c
  }
}

// --- sorts: a class of names and places that only equality reads is an uninterpreted sort (Ivy's), the rest Int -------
// Places: each name (v:), each map's digits and value (m:M:i, m:M:v), each other term's (t:). A class is Int where
// arithmetic or a constant other than 0 reads it. Otherwise it is an uninterpreted sort (Ivy's): ordered where an order
// reads it (a total order le with a least element zero, the naturals' 0: x + 1 <= y is x < y, x < 1 is x = 0, so each
// such literal is the same over the naturals), plain where only equality does; x < 64 in a plain sort is the radix
// encoding's bound and reads as true. The kernel's naturals are a model of the ordered sort's axioms, so a goal
// refuted there is refuted over the naturals; a model's finite order is read back by rank. (GDP_Z3_SORTS=0: all Int.)
// (SUCC: the sort has t + c for small c, a successor function: x < succ x, and nothing between)
const ARITH = 1, LIT = 2, ORD = 4, ZERO = 8, SUCC = 16, SMALL = 4
class Sorts {
  parent = new Map<string, string>(); flag = new Map<string, number>(); n = 0; names = new Map<string, string>(); slot = new WeakMap<object, string>()
  find(a: string): string {
    let r = a
    for (let p = this.parent.get(r); p !== undefined && p !== r; p = this.parent.get(r)) r = p
    if (!this.parent.has(r)) this.parent.set(r, r)
    for (let x = a; x !== r;) { const nx: string = this.parent.get(x)!; this.parent.set(x, r); x = nx }
    return r
  }
  union(a: string, b: string) { const ra = this.find(a), rb = this.find(b); if (ra !== rb) { this.parent.set(ra, rb); this.flag.set(rb, (this.flag.get(rb) ?? 0) | (this.flag.get(ra) ?? 0)) } }
  mark(a: string, f: number) { const r = this.find(a); this.flag.set(r, (this.flag.get(r) ?? 0) | f) }
  fresh() { return this.find(`t:${this.n++}`) }
  sortOf(slot: string | undefined): string {
    if (slot === undefined) return 'Int'
    const r = this.find(slot)
    if ((this.flag.get(r) ?? 0) & (ARITH | LIT)) return 'Int'
    let s = this.names.get(r)
    if (!s) this.names.set(r, (s = `S${this.names.size}`))
    return s
  }
  ordered(sort: string): boolean { for (const [r, s] of this.names) if (s === sort) return !!((this.flag.get(r) ?? 0) & (ORD | ZERO | SUCC)); return false }
  succs = new Map<string, string>(); needSucc = new Set<string>()
  succ(sort: string): boolean { for (const [r, s] of this.names) if (s === sort) return !!((this.flag.get(r) ?? 0) & SUCC); return false }
  // (the sorts' names, every class read once)
  declared(): string[] { for (const k of [...this.parent.keys()]) this.sortOf(k); return [...new Set(this.names.values())] }
}
// A comparison's shape: two terms in an order (a + 1 <= b is a < b), a term against 0 (x = 0, 0 < x), a constant truth
// (x < 0), the radix bound (x < 64), or raw (arithmetic: Int).
type Cmp = {k: 'split', pairs: [E, E][]} | {k: 'rel', a: E, b: E, rel: 'le' | 'lt' | 'eq'} | {k: 'zero', t: E, rel: 'eq0' | 'gt0'} | {k: 'lit', t: E, rel: 'le' | 'ge' | 'eq', c: number} | {k: 'truth', value: boolean} | {k: 'bound', t: E} | {k: 'raw'}
const cmpShape = (c: Extract<C, {op: '<' | '<=' | '='}>): Cmp => {
  if (c.op === '=') { const sp = eqSplit(c.a, c.b); if (sp) return {k: 'split', pairs: sp} }
  const side = (e: E): {t?: E, k: number} | undefined => { const l = flat(e); if (!l.parts.length) return {k: l.c}; return l.parts.length === 1 && l.parts[0]![0] === 1 ? {t: l.parts[0]![1], k: l.c} : undefined }
  const A = side(c.a), B = side(c.b)
  if (!A || !B) return {k: 'raw'}
  if (A.t && B.t) {
    const d = B.k - A.k
    if (c.op === '<=') return d === 0 ? {k: 'rel', a: A.t, b: B.t, rel: 'le'} : d === -1 ? {k: 'rel', a: A.t, b: B.t, rel: 'lt'} : {k: 'raw'}
    if (c.op === '<') return d === 0 ? {k: 'rel', a: A.t, b: B.t, rel: 'lt'} : d === 1 ? {k: 'rel', a: A.t, b: B.t, rel: 'le'} : {k: 'raw'}
    return d === 0 ? {k: 'rel', a: A.t, b: B.t, rel: 'eq'} : {k: 'raw'}
  }
  if (A.t) { // t + k OP const: t OP v
    const v = B.k - A.k
    // (an upper bound at the radix or past it is the encoding's: x < 64, size <= 64)
    if (c.op === '<=') return v < 0 ? {k: 'truth', value: false} : v === 0 ? {k: 'zero', t: A.t, rel: 'eq0'} : v <= SMALL ? {k: 'lit', t: A.t, rel: 'le', c: v} : v >= RADIX - 1 && A.k === 0 ? {k: 'bound', t: A.t} : {k: 'raw'}
    if (c.op === '<') return v <= 0 ? {k: 'truth', value: false} : v === 1 ? {k: 'zero', t: A.t, rel: 'eq0'} : v <= SMALL + 1 ? {k: 'lit', t: A.t, rel: 'le', c: v - 1} : v >= RADIX && A.k === 0 ? {k: 'bound', t: A.t} : {k: 'raw'}
    return v < 0 ? {k: 'truth', value: false} : v === 0 ? {k: 'zero', t: A.t, rel: 'eq0'} : v <= SMALL ? {k: 'lit', t: A.t, rel: 'eq', c: v} : {k: 'raw'}
  }
  if (B.t) { // const OP t + k: v OP t
    const v = A.k - B.k
    if (c.op === '<=') return v <= 0 ? {k: 'truth', value: true} : v === 1 ? {k: 'zero', t: B.t, rel: 'gt0'} : v <= SMALL ? {k: 'lit', t: B.t, rel: 'ge', c: v} : {k: 'raw'}
    if (c.op === '<') return v < 0 ? {k: 'truth', value: true} : v === 0 ? {k: 'zero', t: B.t, rel: 'gt0'} : v < SMALL ? {k: 'lit', t: B.t, rel: 'ge', c: v + 1} : {k: 'raw'}
    return v < 0 ? {k: 'truth', value: false} : v === 0 ? {k: 'zero', t: B.t, rel: 'eq0'} : v <= SMALL ? {k: 'lit', t: B.t, rel: 'eq', c: v} : {k: 'raw'}
  }
  return {k: 'raw'}
}
// (t + c, c from 1 to SMALL: the c-th successor of t)
const succOf = (e: E): {t: E, c: number} | undefined => { if (e.op !== 'add') return undefined; const l = flat(e); return l.parts.length === 1 && l.parts[0]![0] === 1 && l.c >= 1 && l.c <= SMALL ? {t: l.parts[0]![1], c: l.c} : undefined }
const joinS = (s: Sorts, a: string | number, b: string | number) => {
  if (typeof a === 'string' && typeof b === 'string') s.union(a, b)
  else if (typeof a === 'string') s.mark(a, b === 0 ? ZERO : (b as number) <= SMALL ? ZERO | SUCC : LIT)
  else if (typeof b === 'string') s.mark(b, a === 0 ? ZERO : (a as number) <= SMALL ? ZERO | SUCC : LIT)
}
function inferE(s: Sorts, e: E): string | number {
  const r = ((): string | number => {
    switch (e.op) {
      case 'var': return s.find(`v:${e.name}`)
      case 'const': return e.value
      case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'mul': {
        const sc = succOf(e)
        if (sc) { const t = inferE(s, sc.t); if (typeof t === 'string') { s.mark(t, SUCC | ZERO); return t } }
        const t0 = s.fresh()
        if (e.op === 'min' || e.op === 'max') { joinS(s, inferE(s, e.a), t0); joinS(s, inferE(s, e.b), t0); return t0 }
        s.mark(t0, ARITH)
        for (const x of e.op === 'mul' ? [e.a] : [e.a, e.b]) { const t = inferE(s, x); if (typeof t === 'string') s.mark(t, ARITH) }
        return t0
      }
      case 'if': { inferC(s, e.c); const t0 = s.fresh(); joinS(s, inferE(s, e.then), t0); joinS(s, inferE(s, e.else), t0); return t0 }
      case 'get': {
        const ds = keyDigits(e.map, e.key)
        if (ds) ds.forEach((d, i) => joinS(s, inferE(s, d), s.find(`m:${e.map}:${i}`)))
        else { const k = inferE(s, e.key); if (typeof k === 'string') s.mark(k, ARITH); for (let i = 0; i < (arity.get(e.map) ?? 1); i++) s.mark(`m:${e.map}:${i}`, ARITH) }
        return s.find(`m:${e.map}:v`)
      }
    }
  })()
  if (typeof r === 'string') s.slot.set(e, r)
  return r
}
function inferC(s: Sorts, c: C): void {
  switch (c.op) {
    case '<': case '<=': case '=': {
      const sh = cmpShape(c)
      if (sh.k === 'split') { for (const [x, y] of sh.pairs) joinS(s, inferE(s, x), inferE(s, y)); return }
      if (sh.k === 'rel') { const a = inferE(s, sh.a), b = inferE(s, sh.b); joinS(s, a, b); if (sh.rel !== 'eq' && typeof a === 'string') s.mark(a, ORD); return }
      if (sh.k === 'zero') { const t = inferE(s, sh.t); if (typeof t === 'string') s.mark(t, ZERO); return }
      if (sh.k === 'lit') { const t = inferE(s, sh.t); if (typeof t === 'string') s.mark(t, ZERO | SUCC); return }
      if (sh.k === 'bound' || sh.k === 'truth') { inferE(s, sh.k === 'bound' ? sh.t : c.a); if (sh.k === 'truth') inferE(s, c.b); return }
      const a = inferE(s, c.a), b = inferE(s, c.b)
      joinS(s, a, b)
      if (c.op !== '=' && typeof a === 'string' && typeof b === 'string') s.mark(a, ORD)
      return
    }
    case 'and': case 'or': c.xs.forEach(y => inferC(s, y)); return
    case 'not': inferC(s, c.x); return
    case 'all': inferC(s, c.c); return
    case 'flag': return
  }
}

// --- SMT-LIB text -------------------------------------------------------------------------------------------------------
const q = (str: string) => `|${str.replace(/[|\\]/g, '_')}|`
const V = (n: string) => q(n), M = (n: string) => q(`${n}@m`)
const LE = (s: string) => q(`le$${s}`), ZE = (s: string) => q(`zero$${s}`)
const num = (k: number) => (k < 0 ? `(- ${-k})` : String(k))
let cur = new Sorts()
const sortOfTerm = (e: E): string => cur.sortOf(cur.slot.get(e))
// (a constant where a sort is wanted: 0 is the sort's zero)
const SU = (s: string) => q(`succ$${s}`)
// (a successor of a term no binder reads is a fresh constant just above it (lt t r, nothing between), so the sort's
// models stay finite; under a binder, the sort's successor function, whose axioms have only infinite models)
let boundNow: string[] = [], succNew: string[] = [], succAx: string[] = []
const succN = (s: string, t: string, c: number, ground = true): string => {
  if (!c) return t
  if (!ground) { cur.needSucc.add(s); return succN(s, `(${SU(s)} ${t})`, c - 1, false) }
  const key = `${s}|${t}`
  let r = cur.succs.get(key)
  if (!r) {
    r = q(`succ!${cur.succs.size}`)
    cur.succs.set(key, r)
    succNew.push(`(declare-const ${r} ${s})`)
    succAx.push(`(assert (not (${LE(s)} ${r} ${t})))(assert (forall ((y ${s})) (=> (not (${LE(s)} y ${t})) (${LE(s)} ${r} y))))`)
  }
  return succN(s, r, c - 1)
}
const groundE = (e: E) => { const f = new Set<string>(); walkT(e, [], f); return !boundNow.some(b => f.has(b)) }
const teAs = (e: E, sort: string): string => {
  if (sort === 'Int' || e.op !== 'const') return te(e)
  if (e.value === 0) return ZE(sort)
  if (e.value <= SMALL) return succN(sort, ZE(sort), e.value)
  throw new Error(`z3: the constant ${e.value} in sort ${sort}`)
}
function te(e: E): string {
  switch (e.op) {
    case 'var': return V(e.name)
    case 'const': return num(e.value)
    case 'add': { const sc = succOf(e); if (sc) { const s = sortOfTerm(sc.t); if (s !== 'Int') return succN(s, te(sc.t), sc.c, groundE(sc.t)) } return `(+ ${te(e.a)} ${te(e.b)})` }
    case 'sub': return `(monus ${te(e.a)} ${te(e.b)})`
    case 'mul': return `(* ${num(e.k)} ${te(e.a)})`
    case 'prod': return `(* ${te(e.a)} ${te(e.b)})`
    case 'min': case 'max': {
      const s = sortOfTerm(e)
      if (s === 'Int') return `(${e.op === 'min' ? 'mn' : 'mx'} ${te(e.a)} ${te(e.b)})`
      const a = teAs(e.a, s), b = teAs(e.b, s)
      return e.op === 'min' ? `(ite (${LE(s)} ${a} ${b}) ${a} ${b})` : `(ite (${LE(s)} ${a} ${b}) ${b} ${a})`
    }
    case 'if': { const s = sortOfTerm(e); return `(ite ${tc(e.c)} ${teAs(e.then, s)} ${teAs(e.else, s)})` }
    case 'get': return `(${M(e.map)} ${keyArgs(e.map, e.key)})`
  }
}
const keyArgs = (map: string, key: E): string => {
  const n = arity.get(map) ?? 1, ds = keyDigits(map, key)
  if (ds) return ds.map((d, i) => teAs(d, cur.sortOf(`m:${map}:${i}`))).join(' ')
  const k = te(key)
  return Array.from({length: n}, (_, j) => { const i = n - 1 - j; return i === n - 1 ? `(div ${k} ${RADIX ** i})` : `(mod (div ${k} ${RADIX ** i}) ${RADIX})` }).join(' ')
}
const bindAll = (keys: string[], c: string) => {
  const ints = keys.filter(k => cur.sortOf(`v:${k}`) === 'Int')
  return `(forall (${keys.map(k => `(${V(k)} ${cur.sortOf(`v:${k}`)})`).join(' ')}) ${ints.length ? `(=> (and ${ints.map(k => `(>= ${V(k)} 0)`).join(' ')}) ${c})` : c})`
}
function tc(c: C): string {
  switch (c.op) {
    case '<': case '<=': case '=': {
      const sh = cmpShape(c), raw = () => `(${c.op} ${te(c.a)} ${te(c.b)})`
      switch (sh.k) {
        case 'split': return `(and ${sh.pairs.map(([x, y]) => { const s = sortOfTerm(x.op === 'const' ? y : x); return `(= ${teAs(x, s)} ${teAs(y, s)})` }).join(' ')})`
        case 'truth': return sh.value ? 'true' : 'false'
        case 'bound': return sortOfTerm(sh.t) === 'Int' ? raw() : 'true'
        case 'zero': { const s = sortOfTerm(sh.t); return s === 'Int' ? raw() : sh.rel === 'eq0' ? `(= ${te(sh.t)} ${ZE(s)})` : `(not (= ${te(sh.t)} ${ZE(s)}))` }
        case 'lit': {
          const s = sortOfTerm(sh.t)
          if (s === 'Int') return raw()
          const t = te(sh.t), k = succN(s, ZE(s), sh.rel === 'ge' ? sh.c - 1 : sh.c)
          return sh.rel === 'eq' ? `(= ${t} ${k})` : sh.rel === 'le' ? `(${LE(s)} ${t} ${k})` : `(not (${LE(s)} ${t} ${k}))`
        }
        case 'rel': {
          const s = sortOfTerm(sh.a)
          if (s === 'Int') return raw()
          const a = te(sh.a), b = te(sh.b)
          return sh.rel === 'eq' ? `(= ${a} ${b})` : sh.rel === 'le' ? `(${LE(s)} ${a} ${b})` : `(not (${LE(s)} ${b} ${a}))`
        }
        case 'raw': return raw()
      }
      return raw()
    }
    case 'and': return c.xs.length ? `(and ${c.xs.map(tc).join(' ')})` : 'true'
    case 'or': return c.xs.length ? `(or ${c.xs.map(tc).join(' ')})` : 'false'
    case 'not': return `(not ${tc(c.x)})`
    case 'all': { const ks = [c.key, ...(c.keys ?? [])], was = boundNow; boundNow = [...was, ...ks]; try { return bindAll(ks, tc(c.c)) } finally { boundNow = was } }
    case 'flag': throw new Error(`z3: a flag left in a goal (${c.name})`)
  }
}
// The declarations of a sort: an ordered one's le (a total order) and its least element.
const declSort = (s: string) => {
  const le = LE(s), out = [`(declare-sort ${s} 0)`]
  if (cur.ordered(s)) out.push(`(declare-fun ${le} (${s} ${s}) Bool)(declare-const ${ZE(s)} ${s})(assert (forall ((a ${s})) (${le} a a)))(assert (forall ((a ${s}) (b ${s}) (c ${s})) (=> (and (${le} a b) (${le} b c)) (${le} a c))))(assert (forall ((a ${s}) (b ${s})) (=> (and (${le} a b) (${le} b a)) (= a b))))(assert (forall ((a ${s}) (b ${s})) (or (${le} a b) (${le} b a))))(assert (forall ((a ${s})) (${le} ${ZE(s)} a)))`)
  // (the successor: above its argument, and at or below everything above it)
  if (cur.needSucc.has(s)) out.push(`(declare-fun ${SU(s)} (${s}) ${s})(assert (forall ((a ${s})) (not (${le} (${SU(s)} a) a))))(assert (forall ((a ${s}) (b ${s})) (=> (not (${le} b a)) (${le} (${SU(s)} a) b))))`)
  return out.join('')
}
// The free names of a term, and every map read with the names bound where it is (its key enumerated over the model's
// elements at those).
function walkT(t: E | C, bound: string[], free: Set<string>, reads?: Read[]): void {
  const go = (u: E | C, b: string[]): void => {
    switch (u.op) {
      case 'var': if (!b.includes(u.name)) free.add(u.name); return
      case 'const': case 'flag': return
      case 'get': reads?.push({map: u.map, key: u.key, bound: b}); go(u.key, b); return
      case 'if': go(u.c, b); go(u.then, b); go(u.else, b); return
      case 'mul': go(u.a, b); return
      case 'add': case 'sub': case 'min': case 'max': case 'prod': case '<': case '<=': case '=': go(u.a, b); go(u.b, b); return
      case 'and': case 'or': u.xs.forEach(y => go(y, b)); return
      case 'not': go(u.x, b); return
      case 'all': go(u.c, [...b, u.key, ...(u.keys ?? [])]); return
    }
  }
  go(t, bound)
}
const lawC = (l: Law): C => (l.forall ? {op: 'all', key: l.forall, ...(l.keys?.length ? {keys: l.keys} : {}), c: l.holds} : l.holds)
// (a law's conclusion at fresh names, apart from every other law's: x#$c3 is the kernel's x#)
// (a fresh key read only as the whole key of maps of n > 1 digits is n fresh digits, the lower ones below 64, as a
// bound one is (norm); the witness has the key's own value from them)
const splitSkolems = new Map<string, string[]>()
const proven = (l: Law, i: number): C => {
  const ks = [l.forall, ...(l.keys ?? [])].filter((k): k is string => !!k), lows: C[] = [], vars: Record<string, E> = {}
  ks.forEach((k, j) => {
    const name = `${j ? k : `${k}#`}$c${i}`, n = splitArity(l.holds, k)
    if (n < 2) { vars[k] = vr(name); return }
    const ds = Array.from({length: n}, (_, d) => `${name}$d${n - 1 - d}`)
    splitSkolems.set(name, ds)
    vars[k] = ds.reduce<E>((acc, d, d2) => (d2 === 0 ? vr(d) : {op: 'add', a: {op: 'mul', k: RADIX, a: acc}, b: vr(d)}), {op: 'const', value: 0})
    lows.push(...ds.slice(1).map((d): C => ({op: '<', a: vr(d), b: {op: 'const', value: RADIX}})))
  })
  const body = substC(l.holds, {vars, maps: {}, flags: {}})
  return lows.length ? {op: 'or', xs: [{op: 'not', x: {op: 'and', xs: lows}}, body]} : body
}
const witnessName = (n: string) => n.replace(/\$c\d+$/, '')
const one: E = {op: 'const', value: 1}

// A machine's pieces, once: its flags as 0/1 names, their definitions, the substitution after the step, the start's,
// every map symbol and every read (for the model's cells).
type Parts = {arity: Map<string, number>, text: string, flags: Record<string, C>, defs: [string, C][], post: Subst, start: Subst, maps: string[], reads: Read[], names: string[]}
const partsOf = new WeakMap<Machine, Parts>()
function parts(m: Machine): Parts {
  let p = partsOf.get(m)
  if (p) return p
  const flags: Record<string, C> = Object.fromEntries(Object.keys(m.step.flags ?? {}).map(f => [f, {op: '=', a: {op: 'var', name: `?${f}`}, b: one} as C]))
  const fl: Subst = {vars: {}, maps: {}, flags}
  const defs: [string, C][] = Object.entries(m.step.flags ?? {}).map(([f, c]) => [f, substC(c, fl)])
  const post: Subst = {
    vars: Object.fromEntries(Object.entries(m.step.state ?? {}).map(([n, e]) => [n, substE(e, fl)])),
    maps: Object.fromEntries(Object.entries(m.step.maps ?? {}).map(([map, w]) => {
      if ('each' in w) { const value = substE(w.value, fl), each = w.each; return [map, (key: E): E => substE(value, {vars: {[each]: key}, maps: {}, flags: {}})] }
      const wk = substE(w.key, fl), wv = substE(w.value, fl)
      return [map, (key: E): E => ({op: 'if', c: {op: '=', a: key, b: wk}, then: wv, else: {op: 'get', map, key}})]
    })),
    flags: {},
  }
  const start: Subst = {vars: {...m.state}, maps: Object.fromEntries(Object.entries(m.maps ?? {}).map(([map, c]) => [map, () => ({op: 'const', value: c})])), flags: {}}
  const maps = [...Object.keys(m.maps ?? {}), ...(m.inputMaps ?? []), ...Object.keys(m.fns ?? {})]
  const reads: Read[] = [], sink = new Set<string>()
  for (const [, c] of defs) walkT(c, [], sink, reads)
  for (const e of Object.values(m.step.state ?? {})) walkT(e, [], sink, reads)
  for (const w of Object.values(m.step.maps ?? {})) { if ('each' in w) walkT(w.value, [w.each], sink, reads); else { walkT(w.key, [], sink, reads); walkT(w.value, [], sink, reads) } }
  if (m.assume) walkT(m.assume, [], sink, reads)
  for (const f of m.facts ?? []) walkT(lawC(f), [], sink, reads)
  p = {arity: arityOf(reads, maps), text: JSON.stringify(m), flags, defs, post, start, maps, reads, names: [...m.params, ...m.inputs, ...Object.keys(m.state)]}
  partsOf.set(m, p)
  return p
}
const header = '(reset)(set-option :produce-models true)(define-fun monus ((a Int) (b Int)) Int (ite (>= a b) (- a b) 0))(define-fun mn ((a Int) (b Int)) Int (ite (<= a b) a b))(define-fun mx ((a Int) (b Int)) Int (ite (>= a b) a b))'
const declMaps = (p: Parts) => p.maps.map(mp => {
  const n = p.arity.get(mp) ?? 1, ks = Array.from({length: n}, (_, i) => `k${i}`), args = ks.map((_, i) => cur.sortOf(`m:${mp}:${i}`)), val = cur.sortOf(`m:${mp}:v`)
  return `(declare-fun ${M(mp)} (${args.join(' ')}) ${val})${val === 'Int' ? `(assert (forall (${ks.map((k, i) => `(${k} ${args[i]})`).join(' ')}) (>= (${M(mp)} ${ks.join(' ')}) 0)))` : ''}`
}).join('')
const declare = (names: Iterable<string>) => [...names].map(n => { const s = cur.sortOf(`v:${n}`); return `(declare-const ${V(n)} ${s})${s === 'Int' ? `(assert (>= ${V(n)} 0))` : ''}` }).join('')
let sortsOn = process.env.GDP_Z3_SORTS !== '0'
// (for z3probe.ts's arbiter: the plain Int encoding, the kernel's own semantics but for the radix digits)
export const setSorts = (on: boolean) => { sortsOn = on; memo.clear(); bases.clear() }

// --- models -----------------------------------------------------------------------------------------------------------
type S = string | S[]
function parse(text: string): S[] {
  const out: S[] = [], stack: S[][] = [out]
  let i = 0
  while (i < text.length) {
    const ch = text[i]!
    if (ch === ';') { while (i < text.length && text[i] !== '\n') i++ }
    else if (ch === '(') { const l: S[] = []; stack[stack.length - 1]!.push(l); stack.push(l); i++ }
    else if (ch === ')') { stack.pop(); i++ }
    else if (/\s/.test(ch)) i++
    else if (ch === '|') { const j = text.indexOf('|', i + 1); stack[stack.length - 1]!.push(text.slice(i + 1, j)); i = j + 1 }
    else if (ch === '"') { const j = text.indexOf('"', i + 1); stack[stack.length - 1]!.push(text.slice(i, j + 1)); i = j + 1 }
    else { let j = i; while (j < text.length && !/[\s()]/.test(text[j]!)) j++; stack[stack.length - 1]!.push(text.slice(i, j)); i = j }
  }
  return out
}
type Model = {fns: Map<string, {args: string[], body: S}>, text: string}
function modelOf(text: string): Model {
  const fns = new Map<string, {args: string[], body: S}>()
  const top = parse(text), defs = (Array.isArray(top[0]) ? top[0] : top) as S[]
  for (const d of defs) if (Array.isArray(d) && d[0] === 'define-fun') fns.set(d[1] as string, {args: (d[2] as S[]).map(a => (a as S[])[0] as string), body: d[4]!})
  return {fns, text}
}
const element = (s: string): number | undefined => { const mt = /!val!(\d+)$/.exec(s); return mt ? Number(mt[1]) : undefined }
function evalS(md: Model, s: S, env: Map<string, number | boolean>, depth = 0): number | boolean {
  if (depth > 400) throw new Error('z3 model too deep')
  if (!Array.isArray(s)) {
    if (s === 'true') return true
    if (s === 'false') return false
    if (/^-?\d+$/.test(s)) return Number(s)
    if (env.has(s)) return env.get(s)!
    const el = element(s)
    if (el !== undefined) return el
    return apply(md, s, [], depth)
  }
  const [h, ...xs] = s as [string, ...S[]]
  const n = (x: S) => evalS(md, x, env, depth + 1) as number, b = (x: S) => evalS(md, x, env, depth + 1) as boolean
  switch (h) {
    case 'ite': return b(xs[0]!) ? evalS(md, xs[1]!, env, depth + 1) : evalS(md, xs[2]!, env, depth + 1)
    case '=': { const a = evalS(md, xs[0]!, env, depth + 1); return xs.slice(1).every(y => evalS(md, y, env, depth + 1) === a) }
    case '<=': return n(xs[0]!) <= n(xs[1]!)
    case '<': return n(xs[0]!) < n(xs[1]!)
    case '>=': return n(xs[0]!) >= n(xs[1]!)
    case '>': return n(xs[0]!) > n(xs[1]!)
    case 'and': return xs.every(b)
    case 'or': return xs.some(b)
    case 'not': return !b(xs[0]!)
    case '=>': return !b(xs[0]!) || b(xs[1]!)
    case '+': return xs.reduce<number>((a, y) => a + n(y), 0)
    case '-': return xs.length === 1 ? -n(xs[0]!) : xs.slice(1).reduce<number>((a, y) => a - n(y), n(xs[0]!))
    case '*': return xs.reduce<number>((a, y) => a * n(y), 1)
    case 'div': { const a = n(xs[0]!), d = n(xs[1]!); return d === 0 ? 0 : Math.floor(a / d) }
    case 'mod': { const a = n(xs[0]!), d = n(xs[1]!); return d === 0 ? a : ((a % d) + d) % d }
    case 'let': { const e2 = new Map(env); for (const bd of xs[0] as S[]) e2.set((bd as S[])[0] as string, evalS(md, (bd as S[])[1]!, env, depth + 1)); return evalS(md, xs[1]!, e2, depth + 1) }
    default: return apply(md, h, xs.map(y => evalS(md, y, env, depth + 1)), depth)
  }
}
function apply(md: Model, name: string, args: (number | boolean)[], depth: number): number | boolean {
  const f = md.fns.get(name)
  if (!f) return 0
  return evalS(md, f.body, new Map(f.args.map((a, i) => [a, args[i] ?? 0])), depth + 1)
}
const numeralsIn = (s: S, out: Set<number>): Set<number> => { if (Array.isArray(s)) s.forEach(y => numeralsIn(y, out)); else if (/^\d+$/.test(s)) out.add(Number(s)); else { const el = element(s); if (el !== undefined) out.add(el) } return out }

// A model as a kernel witness: every declared name (a law's fresh keys by the kernel's names), every flag, and each map
// at every key its reads take with their bound names over the model's elements (the names' values, 0, and each map's
// value at those), and at every key the model's own table names. An element of an uninterpreted sort is its index.
function witnessOf(md: Model, p: Parts, declared: Iterable<string>, lawReads: Read[]): Record<string, number> {
  const w: Record<string, number> = {}
  // (an ordered sort's elements by rank in its le: the naturals the kernel reads)
  const els0 = new Map<string, Set<number>>()
  for (const mt of md.text.matchAll(/([A-Za-z0-9_]+)!val!(\d+)/g)) { if (!els0.has(mt[1]!)) els0.set(mt[1]!, new Set()); els0.get(mt[1]!)!.add(Number(mt[2])) }
  const toRank = new Map<string, Map<number, number>>(), fromRank = new Map<string, Map<number, number>>()
  for (const [srt, ids] of els0) {
    if (!cur.ordered(srt)) continue
    const le = (a: number, b: number) => apply(md, `le$${srt}`, [a, b], 0) === true
    const order = [...ids].sort((a, b) => (a === b ? 0 : le(a, b) ? -1 : 1))
    toRank.set(srt, new Map(order.map((id, r) => [id, r]))); fromRank.set(srt, new Map(order.map((id, r) => [r, id])))
  }
  const out = (srt: string, v: number | boolean): number => (typeof v === 'boolean' ? (v ? 1 : 0) : toRank.get(srt)?.get(v) ?? v)
  const arg = (srt: string, v: number): number => fromRank.get(srt)?.get(v) ?? v
  const val = (n: string) => out(cur.sortOf(`v:${n}`), apply(md, q(n).slice(1, -1), [], 0))
  for (const n of declared) w[witnessName(n)] = val(n)
  for (const n of declared) { const ds = splitSkolems.get(n.replace(/\$d\d+$/, '')); if (ds && n.endsWith('$d0')) { const base = n.replace(/\$d0$/, ''); if (ds.every(d => d in w || [...declared].includes(d))) w[witnessName(base)] = ds.reduce((a, d) => a * RADIX + val(d), 0) } }
  const digits = (map: string, k: number): number[] => { const n = p.arity.get(map) ?? 1; return Array.from({length: n}, (_, j) => { const i = n - 1 - j; return arg(cur.sortOf(`m:${map}:${j}`), i === n - 1 ? Math.floor(k / RADIX ** i) : Math.floor(k / RADIX ** i) % RADIX) }) }
  const cell = (map: string, k: number) => Math.max(0, out(cur.sortOf(`m:${map}:v`), apply(md, `${map}@m`, digits(map, k), 0)))
  const consts = [...new Set(Object.entries(w).filter(([n]) => !n.startsWith('?')).map(([, v]) => v))]
  const els = new Set<number>([0, ...consts])
  for (const map of p.maps) for (const v of consts) { if (els.size >= 24) break; els.add(cell(map, v)) }
  const E2 = [...els].filter(v => v >= 0 && v <= 1_000_000).sort((a, b) => a - b).slice(0, 24)
  const evalKey = (e: E, env: Record<string, number>): number => {
    switch (e.op) {
      case 'var': return env[e.name] ?? w[e.name] ?? 0
      case 'const': return e.value
      case 'add': return evalKey(e.a, env) + evalKey(e.b, env)
      case 'sub': return Math.max(0, evalKey(e.a, env) - evalKey(e.b, env))
      case 'mul': return e.k * evalKey(e.a, env)
      case 'prod': return evalKey(e.a, env) * evalKey(e.b, env)
      case 'min': return Math.min(evalKey(e.a, env), evalKey(e.b, env))
      case 'max': return Math.max(evalKey(e.a, env), evalKey(e.b, env))
      case 'if': return evalCond(e.c, env) ? evalKey(e.then, env) : evalKey(e.else, env)
      case 'get': return cell(e.map, evalKey(e.key, env))
    }
  }
  const evalCond = (c: C, env: Record<string, number>): boolean => {
    switch (c.op) {
      case '<': return evalKey(c.a, env) < evalKey(c.b, env)
      case '<=': return evalKey(c.a, env) <= evalKey(c.b, env)
      case '=': return evalKey(c.a, env) === evalKey(c.b, env)
      case 'and': return c.xs.every(y => evalCond(y, env))
      case 'or': return c.xs.some(y => evalCond(y, env))
      case 'not': return !evalCond(c.x, env)
      case 'flag': return (w[`?${c.name}`] ?? 0) === 1
      case 'all': return true
    }
  }
  const keys = new Map<string, Set<number>>(p.maps.map(mp => [mp, new Set<number>()]))
  for (const r of [...p.reads, ...lawReads]) {
    const ks = keys.get(r.map)
    if (!ks) continue
    const free = new Set<string>()
    walkT(r.key, [], free)
    const bs = r.bound.filter(b => free.has(b)), dom = E2.length ** bs.length <= 4096 ? E2 : consts.filter(v => v <= 1_000_000).slice(0, Math.floor(4096 ** (1 / Math.max(1, bs.length))))
    const go = (i: number, env: Record<string, number>) => {
      if (ks.size >= 4096) return
      if (i === bs.length) { try { const k = evalKey(r.key, env); if (k >= 0 && k <= 1_000_000) ks.add(k) } catch { /* a key the model can't value */ } return }
      for (const v of dom) go(i + 1, {...env, [bs[i]!]: v})
    }
    go(0, {})
  }
  for (const mp of p.maps) {
    const f = md.fns.get(`${mp}@m`), ks = keys.get(mp)!
    if (f) {
      const ns = [...numeralsIn(f.body, new Set())].filter(k => k < RADIX).slice(0, 24), n = p.arity.get(mp) ?? 1
      const tuples = ns.length ** n <= 4096 ? Array.from({length: n}).reduce<number[]>(acc => acc.flatMap(k => ns.map(d => k * RADIX + d)), [0]) : []
      for (const k of tuples) if (ks.size < 8192) ks.add(k)
    }
    for (const k of ks) w[`${mp}[1:${k}]`] = cell(mp, k)
  }
  return w
}

// --- deciding ---------------------------------------------------------------------------------------------------------
export type Decided = {proven: true} | {proven: false, goal: string, stuck: 'sat', witness: Record<string, number>}
const lawText = new WeakMap<Law, string>()
const textOf = (l: Law) => { let t = lawText.get(l); if (t === undefined) lawText.set(l, (t = JSON.stringify([l.name, l.holds, l.forall ?? null, l.keys ?? null]))); return t }
const fast = (m: Machine, laws: Law[]) => !m.history && !(m.sums && Object.keys(m.sums).length) && !laws.some(l => l.some?.length)
const memo = new Map<string, Decided | 'unknown'>()
export let lastReason = ''
// A context's base, made once: its text (sorts, maps, names, flags, hypotheses), its names, its sorts and each goal's
// conclusion (normalized, at its fresh names, the sorts read off the base and every conclusion together).
type Base = {key: string, text: string, names: Set<string>, sorts: Sorts, concl: C[], goal: string[], reads: Read[], p: Parts}
const bases = new Map<string, Base>()
function makeBase(key: string, p: Parts, hyps: C[], defs: [string, C][], concl: C[], goal: string[], extraNames: string[], reads: Read[]): Base {
  const s = new Sorts()
  if (!sortsOn) s.mark('v:__all', ARITH)
  const nh = hyps.map(norm), nd = defs.map(([f, c]): [string, C] => [f, norm(c)]), nc = concl.map(norm)
  for (const c of [...nh, ...nd.map(([, c]) => c), ...nc]) inferC(s, c)
  for (const [f] of nd) s.mark(`v:?${f}`, LIT)
  // (GDP_Z3_SORTS=0: every class Int)
  if (!sortsOn) for (const k of [...s.parent.keys()]) s.union(k, 'v:__all')
  if (process.env.GDP_Z3_DEBUG) { const by = new Map<string, string[]>(); for (const k of s.parent.keys()) if (!k.startsWith('t:')) { const r = s.find(k); by.set(r, [...(by.get(r) ?? []), k]) } console.error('z3 sorts', [...by].map(([r, ks]) => `${s.flag.get(r) ?? 0}: ${ks.slice(0, 8).join(' ')}`).join(' | ')) }
  const names = new Set<string>(extraNames)
  for (const c of [...nh, ...nd.map(([, c]) => c)]) walkT(c, [], names)
  for (const [f] of nd) names.add(`?${f}`)
  cur = s
  succNew = []; succAx = []; boundNow = []
  const body = `${declMaps(p)}${declare(names)}` + nd.map(([f, c]) => `(assert (<= ${V(`?${f}`)} 1))(assert (= (= ${V(`?${f}`)} 1) ${tc(c)}))`).join('') + nh.map(h => `(assert ${tc(h)})`).join('')
  const text = `${header}${s.declared().map(declSort).join('')}${succNew.join('')}${body}${succAx.join('')}`
  const b: Base = {key, text, names, sorts: s, concl: nc, goal, reads, p}
  if (bases.size > 32) bases.clear()
  bases.set(key, b)
  return b
}
// (each goal asked in a fresh context, the base sent again, then pushed: Z3's MBQI diverged on goals asked in one
// context after others (push/pop over many goals), and found some models fresh only below a push; GDP_Z3_PUSH=0 leaves
// the push out)
const pushed = process.env.GDP_Z3_PUSH !== '0'
let pins: Record<string, number> | undefined
function ask(ctx: 'start' | 'step', b: Base, i: number, ms: number): Decided | 'unknown' {
  const t0 = performance.now(), concl = b.concl[i]!, goalName = b.goal[i]!
  cur = b.sorts; arity = b.p.arity
  const free = new Set<string>()
  walkT(concl, [], free)
  const fresh = [...free].filter(n => !b.names.has(n))
  const tmo = Math.max(50, Math.floor(ms))
  let res: Decided | 'unknown' = 'unknown', out: string | undefined
  try {
    const saved = new Map(cur.succs)
    succNew = []; succAx = []; boundNow = []
    const g = tc(concl)
    // (z3Pinned: a kernel witness's names and cells pinned, the plain Int encoding: is it a model of the goal?)
    let pin = ''
    if (pins) {
      const known = new Map([...b.names, ...fresh].map(n => [witnessName(n), n] as [string, string]))
      for (const [n, v] of Object.entries(pins)) {
        const br = n.indexOf('[')
        if (br < 0) { const nm = known.get(n); if (nm && cur.sortOf(`v:${nm}`) === 'Int') pin += `(assert (= ${V(nm)} ${v}))`; continue }
        const map = n.slice(0, br), key = keyValueOf(n, pins)
        if (key === undefined || !b.p.maps.includes(map)) continue
        const ar = b.p.arity.get(map) ?? 1, ds = Array.from({length: ar}, (_, j) => { const k2 = ar - 1 - j; return k2 === ar - 1 ? Math.floor(key / RADIX ** k2) : Math.floor(key / RADIX ** k2) % RADIX })
        pin += `(assert (= (${M(map)} ${ds.join(' ')}) ${v}))`
      }
    }
    const goal = `${declare(fresh)}${succNew.join('')}(assert (not ${g}))${succAx.join('')}${pin}`
    cur.succs = saved
    if (process.env.GDP_Z3_SAVE) require('node:fs').appendFileSync(process.env.GDP_Z3_SAVE, `;; ${goalName}\n${b.text}${pushed ? '(push 1)' : ''}${goal}(check-sat)\n`)
    out = call(ctx, `${b.text}${pushed ? '(push 1)' : ''}${goal}(set-option :timeout ${tmo})(check-sat)`, tmo + 5_000)
  } catch (e) { lastReason = `translate: ${String(e).slice(0, 120)}` }
  if (out === undefined) { if (!lastReason.startsWith('translate')) lastReason = 'hard timeout' }
  else if (/^\s*unsat/.test(out)) res = {proven: true}
  else if (/^\s*sat/.test(out)) {
    const mt = call(ctx, '(get-model)', 30_000)
    if (mt !== undefined && !mt.includes('(error')) {
      try { res = {proven: false, goal: goalName, stuck: 'sat', witness: witnessOf(modelOf(mt), b.p, [...b.names, ...fresh], b.reads)} } catch (e) { lastReason = `model: ${String(e).slice(0, 120)}` }
    } else lastReason = `model: ${String(mt).slice(0, 120)}`
  } else {
    const why = /\(error/.test(out) ? '' : call(ctx, '(get-info :reason-unknown)', 5_000) ?? 'hard timeout'
    lastReason = `${out.trim().slice(0, 100)} ${why.trim().slice(0, 100)}`
  }
  if (res === 'unknown') { const k = lastReason.replace(/\d+/g, '#').slice(0, 80); stats.reasons.set(k, (stats.reasons.get(k) ?? 0) + 1) }
  stats.rows.push({kind: ctx, ms: performance.now() - t0, res: res === 'unknown' ? 'unknown' : res.proven ? 'unsat' : 'sat'})
  return res
}
// The start goal of a law (the precondition and the facts; no law assumed).
function startGoal(m: Machine, law: Law, ms: number): Decided | 'unknown' {
  const p = parts(m), key = `start|${p.text}|${textOf(law)}`, was = memo.get(key)
  if (was && was !== 'unknown') return was
  arity = p.arity
  const b = bases.get(key) ?? makeBase(key, p, [...(m.facts ?? []).map(lawC), ...(m.pre ? [m.pre] : [])], [], [substC(proven(law, 0), p.start)], [`${law.name} @start`], m.params, readsOf([law]))
  const out = ask('start', b, 0, ms)
  memo.set(key, out)
  return out
}
// The step goal of law i, every law assumed before the step.
const setKeys = new WeakMap<Law[], string>(), setReads = new WeakMap<Law[], Read[]>()
const readsOf = (laws: Law[]): Read[] => { let r = setReads.get(laws); if (!r) { r = []; const sink = new Set<string>(); for (const l of laws) walkT(lawC(l), [], sink, r); const seen = new Set<string>(); r = r.filter(x => { const k = JSON.stringify([x.map, x.key, x.bound]); return !seen.has(k) && !!seen.add(k) }); setReads.set(laws, r) } return r }
function stepGoal(m: Machine, laws: Law[], i: number, ms: number): Decided | 'unknown' {
  const p = parts(m)
  let sk = setKeys.get(laws)
  if (sk === undefined) setKeys.set(laws, (sk = `step|${p.text}|${laws.map(textOf).join('\n')}`))
  const key = `${sk}|${i}`, was = memo.get(key)
  if (was && was !== 'unknown') return was
  arity = p.arity
  const b = bases.get(sk) ?? makeBase(sk, p, [...(m.facts ?? []).map(lawC), ...(m.pre ? [m.pre] : []), ...(m.assume ? [substC(m.assume, {vars: {}, maps: {}, flags: p.flags})] : []), ...laws.map(lawC)], p.defs,
    laws.map((l, j) => substC(proven(l, j), p.post)), laws.map(l => `${l.name} @step`), p.names, readsOf(laws))
  const out = ask('step', b, i, ms)
  if (memo.size > 50_000) memo.clear()
  memo.set(key, out)
  return out
}
// decideLaw's question by Z3: law i's start, then its step; undefined where Z3 can't say (unknown, a timeout, a shape
// it doesn't take: a history, sums, "there exists").
export function z3Decide(m: Machine, laws: Law[], i: number, ms = 1000): Decided | undefined {
  if (!fast(m, laws)) { lastReason = 'shape'; return undefined }
  const end = performance.now() + ms
  const s = startGoal(m, laws[i]!, ms)
  if (s === 'unknown') return undefined
  if (!s.proven) return s
  const t = stepGoal(m, laws, i, Math.max(50, end - performance.now()))
  return t === 'unknown' ? undefined : t
}
// The set's check: every law's two goals in order (the first refuted returned with its model), `unknown` at the first
// Z3 can't decide. Untrusted: a set it passes is then proven by the kernel.
export function z3Set(m: Machine, laws: Law[], ms = 1000, until = Infinity): {proven: true} | {proven: false, goal: string, witness: Record<string, number>} | {unknown: string} {
  if (!fast(m, laws)) return {unknown: 'shape'}
  for (let i = 0; i < laws.length; i++) {
    if (performance.now() > until) return {unknown: `${laws[i]!.name} @time`}
    const d = z3Decide(m, laws, i, ms)
    if (!d) return {unknown: `${laws[i]!.name} @?`}
    if (!d.proven) return {proven: false, goal: d.goal, witness: d.witness}
  }
  return {proven: true}
}
// Every failing law of a set at once (DuoAI's top-down step, Ivy's one check reporting every failure): the indices in
// `ask` whose step (or start) has a model, with the models; those undecided apart.
export function z3Failing(m: Machine, laws: Law[], ask: number[], ms = 1000, until = Infinity): {failed: Map<number, Record<string, number>>, unknown: number[]} {
  const failed = new Map<number, Record<string, number>>(), unknown: number[] = []
  for (const i of ask) {
    if (performance.now() > until) { unknown.push(i); continue }
    const d = z3Decide(m, laws, i, ms)
    if (!d) unknown.push(i)
    else if (!d.proven) failed.set(i, d.witness)
  }
  return {failed, unknown}
}

// A law's start goal alone (the top-down step's first cut: a cube false at a start is never a candidate).
export function z3Start(m: Machine, law: Law, ms = 1000): Decided | undefined {
  if (!fast(m, [law])) return undefined
  const s = startGoal(m, law, ms)
  return s === 'unknown' ? undefined : s
}
// The engine's goals written out for z3probe.ts's replay (GDP_Z3_DUMP): each machine and law set once, then each goal.
const dumped = new WeakMap<object, string>(), dumpedText = new Map<string, string>()
let dumpN = 0
export function dumpGoal(file: string, m: Machine, laws: Law[], i: number): void {
  const fs = require('node:fs') as typeof import('node:fs')
  const idOf = (o: object, kind: 'machine' | 'set', text: () => string) => {
    let id = dumped.get(o)
    if (id) return id
    const t = text()
    id = dumpedText.get(t)
    if (!id) { id = `${kind[0]}${dumpN++}`; dumpedText.set(t, id); fs.appendFileSync(file, `${JSON.stringify({id, [kind]: JSON.parse(t)})}\n`) }
    dumped.set(o, id)
    return id
  }
  const mid = idOf(m, 'machine', () => JSON.stringify(m)), sid = idOf(laws, 'set', () => JSON.stringify(laws))
  fs.appendFileSync(file, `${JSON.stringify({m: mid, s: sid, i})}\n`)
}

// A kernel model checked by Z3 (z3probe.ts's arbiter): law i's step in the plain Int encoding with the witness's names
// and cells pinned; unsat means the model breaks an assumed law or isn't a model of the goal (a spurious model).
const keyValueOf = (cell: string, w: Record<string, number>): number | undefined => {
  const inner = cell.slice(cell.indexOf('[') + 1, -1), parts: string[] = []
  let depth = 0, from = 0
  for (let i = 0; i < inner.length; i++) { const ch = inner[i]; if (ch === '[') depth++; else if (ch === ']') depth--; else if (ch === ',' && depth === 0) { parts.push(inner.slice(from, i)); from = i + 1 } }
  parts.push(inner.slice(from))
  let value = 0
  for (const part of parts.filter(Boolean)) { const at = part.lastIndexOf(':'), name = part.slice(0, at), coef = Number(part.slice(at + 1)); if (name === '1') value += coef; else if (name in w) value += coef * w[name]!; else return undefined }
  return value
}
export function z3Pinned(m: Machine, laws: Law[], i: number, witness: Record<string, number>, ms = 10_000): 'model' | 'spurious' | 'unknown' {
  const was = sortsOn
  setSorts(false); pins = witness
  try {
    const goal = String(Object.keys(witness).length) // (pinned goals are never memoized)
    void goal
    const p = parts(m)
    arity = p.arity
    const sk = `pin|${p.text}|${laws.map(textOf).join('\n')}`
    const b = bases.get(sk) ?? makeBase(sk, p, [...(m.facts ?? []).map(lawC), ...(m.pre ? [m.pre] : []), ...(m.assume ? [substC(m.assume, {vars: {}, maps: {}, flags: p.flags})] : []), ...laws.map(lawC)], p.defs,
      laws.map((l, j) => substC(proven(l, j), p.post)), laws.map(l => `${l.name} @step`), p.names, readsOf(laws))
    const out = ask('step', b, i, ms)
    return out === 'unknown' ? 'unknown' : out.proven ? 'spurious' : 'model'
  } finally { pins = undefined; setSorts(was) }
}
