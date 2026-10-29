// Untrusted: a fast decision of EPR-shaped goals (research/protocols/epr/DESIGN.md). The hypotheses read as a
// propositional abstraction: a composed key (a·N² + b·N + c) the tuple of its parts, compared by the parts' order and
// equality, never by arithmetic; a few-valued cell a finite variable; an ordered value (an epoch) a term of a total order;
// anything else an opaque atom. Every clause beside the hypotheses holds in every model of the goal, and finite values are
// capped above every constant they meet, so unsat here is unsat there. It answers unsat with its core (the hypotheses
// its refutation read: prove.ts proves the goal over those and widens the tree to the whole, which kernel.ts checks), or
// a model read back as the kernel's witness and judged on every hypothesis, or nothing.
import {type C, type E, type Machine, evalC} from '../core/machine.ts'
import {type Goal, canon, linear} from './kernel.ts'

// Each map's key pattern, as its rule reads it: the coefficients of a key Σ c·x of distinct names (Table 4096, 64, 1;
// Leader 1). A read at a key of another shape (an instance at a key of the wrong sort) is a cell of its own, by its key's
// text, with no congruence to the others: weaker, so still sound for a refutation. The conclusion must have the patterns.
export type Patterns = Record<string, number[]>

// The patterns of a rule: of each map's reads in the step, the assumption, the flags and the laws (not the kinds' laws,
// whose key is a whole key), the one with the most parts. A read keyed by a write-at-every-key's own name is left out.
export function patternsOf(m: Machine, laws: {name: string, holds: C}[]): Patterns {
  const out: Patterns = {}
  const each = new Set(Object.values(m.step.maps ?? {}).flatMap(w => ('each' in w ? [w.each] : [])))
  const scan = (o: unknown): void => {
    if (!o || typeof o !== 'object') return
    const x = o as {op?: string, map?: string, key?: E, args?: unknown}
    if (x.op === 'get' && !x.args && !(x.key!.op === 'var' && each.has(x.key!.name)) && !(m.fns && x.map! in m.fns)) { const t = tupleOf(x.key!); if (t && t.coefs.length > (out[x.map!]?.length ?? 0)) out[x.map!] = t.coefs }
    for (const y of Object.values(o)) scan(y)
  }
  scan(m.step); scan(m.assume)
  // (a function of one key: [0], its reads parts of the keys they're in, an uninterpreted function of a part)
  for (const f of Object.keys(m.fns ?? {})) out[f] = [0]
  for (const l of laws) if (!(l.name.startsWith('every ') && l.name.endsWith('of its kind'))) scan(l.holds)
  return out
}

type F = {k: 'v', v: number} | {k: 'and' | 'or', xs: F[]} | {k: 'not', x: F} | {k: 'c', b: boolean}
const T: F = {k: 'c', b: true}, Fa: F = {k: 'c', b: false}
const and = (xs: F[]): F => { const ys = xs.filter(x => !(x.k === 'c' && x.b)); return ys.some(x => x.k === 'c' && !x.b) ? Fa : ys.length === 0 ? T : ys.length === 1 ? ys[0]! : {k: 'and', xs: ys} }
const or = (xs: F[]): F => { const ys = xs.filter(x => !(x.k === 'c' && !x.b)); return ys.some(x => x.k === 'c' && x.b) ? T : ys.length === 0 ? Fa : ys.length === 1 ? ys[0]! : {k: 'or', xs: ys} }
const not = (x: F): F => (x.k === 'c' ? {k: 'c', b: !x.b} : x.k === 'not' ? x.x : {k: 'not', x})

// The functions of one key of the goal being decided (patterns [0]): a read f(x) of one at a part is a part, `f(x)`.
let fnMaps = new Set<string>()
const partName = (e: E): string | undefined => e.op === 'var' ? e.name
  : e.op === 'get' && fnMaps.has(e.map) && !(e as {args?: unknown}).args ? (n => (n === undefined ? undefined : `${e.map}(${n})`))(partName(e.key)) : undefined
// A key Σ c·x + d as its terms; undefined where it reads anything but parts under constant factors.
const linTerms = (e: E, k: number, out: [string, number][], d: {c: number}): boolean =>
  e.op === 'var' || e.op === 'get' ? (n => n !== undefined && (out.push([n, k]), true))(partName(e)) : e.op === 'const' ? ((d.c += k * e.value), true)
    : e.op === 'mul' ? linTerms(e.a, k * e.k, out, d) : e.op === 'add' ? linTerms(e.a, k, out, d) && linTerms(e.b, k, out, d) : false
// A radix tuple: distinct names, no constant, coefficients a chain (each a multiple of the next, the last 1); its parts in
// order (highest first) with each part's bound (the next coefficient's ratio; the top part none).
type Tuple = {coefs: number[], parts: string[], bounds: (number | undefined)[]}
function tupleOf(e: E): Tuple | undefined {
  const ts: [string, number][] = [], d = {c: 0}
  if (!linTerms(e, 1, ts, d) || d.c !== 0 || !ts.length || new Set(ts.map(t => t[0])).size !== ts.length) return undefined
  ts.sort((a, b) => b[1] - a[1])
  const coefs = ts.map(t => t[1])
  if (coefs.at(-1) !== 1 || coefs.some((c, i) => i + 1 < coefs.length && (c % coefs[i + 1]! !== 0 || c / coefs[i + 1]! < 2))) return undefined
  return {coefs, parts: ts.map(t => t[0]), bounds: coefs.map((c, i) => (i === 0 ? undefined : coefs[i - 1]! / c))}
}
const sameCoefs = (a: number[], b: number[]) => a.length === b.length && a.every((c, i) => c === b[i])

type Origin = number // a hypothesis' index, or -1 for a clause that holds in every model (an axiom)
export type Decision = {sat: false, core: number[]} | {sat: true, witness: Record<string, number>} | {unknown: string}

// `late`: true past the caller's end, checked between the steps and every 256 conflicts; then unknown.
export function decide(goal: Goal, patterns: Patterns, opts: {conflicts?: number, exact?: boolean, late?: () => boolean} = {}): Decision {
  fnMaps = new Set(Object.entries(patterns).filter(([, c]) => c.length === 1 && c[0] === 0).map(([f]) => f))
  try { return decide0(goal, patterns, opts) } finally { fnMaps = new Set() }
}
function decide0(goal: Goal, patterns: Patterns, opts: {conflicts?: number, exact?: boolean, late?: () => boolean}): Decision {
  // --- which hypotheses are EPR-shaped: every map read at a key of its map's pattern
  const shaped = goal.hyps.map(h => {
    let ok = true
    const walk = (o: unknown): void => {
      if (!ok || !o || typeof o !== 'object') return
      const x = o as {op?: string, map?: string, key?: E, args?: unknown}
      if (x.op === 'get' && fnMaps.has(x.map!)) { if (partName(x as E) === undefined) { ok = false; return } }
      else if (x.op === 'get') { const t = x.args ? undefined : tupleOf(x.key!), p = patterns[x.map!]; if (!t || !p || !sameCoefs(t.coefs, p)) { ok = false; return } }
      for (const v of Object.values(o)) walk(v)
    }
    walk(h)
    return ok
  })
  // (the conclusion's reads at keys of any radix shape: one of the wrong sort, Leader[k] <= Msg[k] with Msg a relation of
  // pairs, is a cell of its own, as in a hypothesis)
  const tupled = (o: unknown): boolean => { if (!o || typeof o !== 'object') return true; const x = o as {op?: string, map?: string, key?: E, args?: unknown}; if (x.op === 'get' && !fnMaps.has(x.map!) && (x.args || !tupleOf(x.key!))) return false; return Object.values(o).every(tupled) }
  if (!shaped.at(-1) && !tupled(goal.hyps.at(-1))) return {unknown: 'the conclusion is not EPR-shaped'}
  const hyps: (C | undefined)[] = goal.hyps
  const fits = (map: string, key: E) => { const t = tupleOf(key), p = patterns[map]; return t && p && sameCoefs(t.coefs, p) ? t : undefined }
  // --- names: a part is a name some read's key or a key equality reads; the rest are scalars
  const parts = new Set<string>(), fnParts: {f: string, n: string, a: string}[] = []
  const collectParts = (o: unknown): void => {
    if (!o || typeof o !== 'object') return
    const x = o as {op?: string, key?: E}
    if (x.op === 'get' && fnMaps.has((x as {map: string}).map)) { const n = partName(x as E), a = partName(x.key!); if (n && a) { parts.add(n); parts.add(a); fnParts.push({f: (x as {map: string}).map, n, a}) } }
    else if (x.op === 'get') fits((x as {map: string}).map, x.key!)?.parts.forEach(p => parts.add(p))
    for (const v of Object.values(o)) collectParts(v)
  }
  hyps.forEach(collectParts)
  // (and the names of a key equality between tuples of one shape: of several parts, or of one where the other side is a part)
  for (let grew = true; grew;) {
    grew = false
    const eqWalk = (o: unknown): void => {
      if (!o || typeof o !== 'object') return
      const c = o as C
      if (c.op === '=') {
        const ta = tupleOf(c.a), tb = tupleOf(c.b)
        if (ta && tb && sameCoefs(ta.coefs, tb.coefs) && (ta.parts.length > 1 || [...ta.parts, ...tb.parts].some(x => parts.has(x)))) for (const x of [...ta.parts, ...tb.parts]) if (!parts.has(x)) { parts.add(x); grew = true }
      }
      for (const y of Object.values(o)) eqWalk(y)
    }
    hyps.forEach(eqWalk)
  }
  // exact: a scalar or a cell a hypothesis bounds by a constant (M[t] <= 1, a kind's instance): its values are
  // 0 .. that bound exactly, no "cap or more", so it is compared with any finite term by cases, not ordered (a yes/no
  // that implies another, Leader[x] <= Voted[x]); the hypothesis is the origin of the clause that it takes one of them
  const ordMaps = new Set<string>(), ordScalars = new Set<string>()
  const bounded = new Map<string, {b: number, h: number}>()
  const unitWalk = (c: C | undefined, h: number): void => {
    if (!c) return
    if (c.op === 'and') { c.xs.forEach(x => unitWalk(x, h)); return }
    if ((c.op === '<=' || c.op === '<') && c.b.op === 'const' && (c.a.op === 'get' || c.a.op === 'var')) {
      const id = JSON.stringify(c.a), b = c.b.value - (c.op === '<' ? 1 : 0), had = bounded.get(id)
      if (b >= 0 && (!had || b < had.b)) bounded.set(id, {b, h})
    }
  }
  hyps.forEach((c, h) => unitWalk(c, h))
  // (one compared with a key part, or beside an ordered term, is of that sort: ordered, below, and not exact)
  const exactOf = (e: E): {b: number, h: number} | undefined => (e.op === 'get' ? (!ordMaps.has(e.map) ? bounded.get(JSON.stringify(e)) : undefined) : e.op === 'var' && !parts.has(e.name) && !ordScalars.has(e.name) ? bounded.get(JSON.stringify(e)) : undefined)
  // --- caps: a finite term's values are 0 .. cap, cap above every constant a comparison it is in has (so a larger value
  // decides every comparison the cap does: the terms are naturals with coefficients of one sign)
  const caps = new Map<string, number>()
  const termKey = (e: E): string | undefined => (e.op === 'var' && !parts.has(e.name) ? `s:${e.name}` : e.op === 'get' ? `c:${e.map}` : undefined)
  const capWalk = (o: unknown): void => {
    if (!o || typeof o !== 'object') return
    const c = o as C
    if (c.op === '<' || c.op === '<=' || c.op === '=') {
      const consts: number[] = [], keys: string[] = []
      let ex = 0
      const w = (e: E, k: number) => { if (e.op === 'const') consts.push(Math.abs(e.value)); else if (e.op === 'add') (w(e.a, k), w(e.b, k)); else if (e.op === 'mul') w(e.a, k * e.k); else if (e.op === 'if') (w(e.then, k), w(e.else, k)); else { const x = exactOf(e); if (x) ex += Math.abs(k) * x.b; const t = termKey(e); if (t) keys.push(t) } }
      w(c.a, 1); w(c.b, 1)
      // (and past what the exact terms beside can add: x <= Voted[k] with x at its cap is false at every larger x)
      const top = Math.max(1, ...consts) + ex + 1
      for (const k of keys) caps.set(k, Math.max(caps.get(k) ?? 1, top))
    }
    for (const v of Object.values(o)) capWalk(v)
  }
  hyps.forEach(capWalk)
  // ordered: a map's cells, or a scalar, compared with another non-constant term (an epoch with a node's epoch: Ivy's
  // total order, `le`), not only with constants (a yes/no, a choice, which stay finite)
  const leaves = (e: E, k: number, out: [E, number][]): void => {
    if (e.op === 'add') { leaves(e.a, k, out); leaves(e.b, k, out) } else if (e.op === 'mul') leaves(e.a, k * e.k, out)
    else if (e.op === 'if') { leaves(e.then, k, out); leaves(e.else, k, out) } else if (e.op !== 'const') out.push([e, k])
  }
  const ordWalk = (o: unknown): void => {
    if (!o || typeof o !== 'object') return
    const c = o as C
    const ofParts = (e: E) => tupleOf(e)?.parts.every(x => parts.has(x))
    if ((c.op === '<' || c.op === '<=' || c.op === '=') && !(ofParts(c.a) && ofParts(c.b))) {
      const ts: [E, number][] = []
      leaves(c.a, 1, ts); leaves(c.b, -1, ts)
      const hasPart = ts.some(([e]) => (n => n !== undefined && parts.has(n))(partName(e)))
      const nonPart = ts.filter(([e]) => (hasPart || !exactOf(e)) && ((e.op === 'get' && !fnMaps.has(e.map)) || (e.op === 'var' && !parts.has(e.name))))
      // (and every term beside an ordered one in a comparison: one value of the sort, an if-then-else's branches)
      const tn = ts.filter(([e]) => hasPart || !exactOf(e)), mixed = nonPart.length && tn.length > 1 && tn.some(t => t[1] > 0) && tn.some(t => t[1] < 0)
      const beside = nonPart.some(([e]) => (e.op === 'get' && ordMaps.has(e.map)) || (e.op === 'var' && ordScalars.has(e.name)))
      if (mixed || beside) for (const [e] of nonPart) { if (e.op === 'get' && !ordMaps.has(e.map)) { ordMaps.add(e.map); grew = true } else if (e.op === 'var' && !ordScalars.has(e.name)) { ordScalars.add(e.name); grew = true } }
    }
    for (const v2 of Object.values(o)) ordWalk(v2)
  }
  let grew = true
  while (grew) { grew = false; hyps.forEach(ordWalk) }

  // --- atoms
  const ids = new Map<string, number>(), names: string[] = ['']
  const atom = (key: string): F => { let v = ids.get(key); if (v === undefined) { v = names.length; ids.set(key, v); names.push(key) } return {k: 'v', v} }
  const eq = (x: string, y: string): F => (x === y ? T : atom(`eq ${x < y ? x : y} ${x < y ? y : x}`))
  // the ordered terms (every part among them), `le a b` a ≤ b
  const ords = new Set<string>(['k:0', ...[...parts].map(x => `p:${x}`)])
  const le = (a: string, b: string): F => (a === b ? T : atom(`le ${a} ${b}`))
  // a part under a bound, x < c: ¬(c ≤ x) in the order (below), the constant one of its terms
  const ltAt = (x: string, c: number): F => { if (c <= 0) return Fa; ords.add(`k:${c}`); return not(le(`k:${c}`, `p:${x}`)) }
  // a finite variable at a value: a scalar s:x, or a cell c:M(parts) of map M
  type Fin = {id: string, cap: number, exact?: number}
  const fins = new Map<string, Fin>(), cellsOf = new Map<string, {id: string, parts: string[]}[]>(), odd: {id: string, map: string, key: E}[] = []
  const finAt = (f: Fin, v: number): F => atom(`val ${f.id} ${v}`)
  const finOf = (e: E): Fin | undefined => {
    if ((e.op === 'get' && (ordMaps.has(e.map) || fnMaps.has(e.map))) || (e.op === 'var' && ordScalars.has(e.name))) return undefined
    const ex = exactOf(e), fin = (id: string, cap: number): Fin => (ex ? {id, cap: ex.b, exact: ex.h} : {id, cap})
    if (e.op === 'var' && !parts.has(e.name)) { const id = `s:${e.name}`; let f = fins.get(id); if (!f) fins.set(id, (f = fin(id, caps.get(id) ?? 1))); return f }
    if (e.op === 'get' && !(e as {args?: unknown}).args && !fits(e.map, e.key)) {
      const id = `c:${e.map}#${JSON.stringify(e.key)}`
      let f = fins.get(id)
      if (!f) { fins.set(id, (f = fin(id, caps.get(`c:${e.map}`) ?? 1))); odd.push({id, map: e.map, key: e.key}) }
      return f
    }
    if (e.op === 'get') {
      const t = tupleOf(e.key)!, id = `c:${e.map}(${t.parts.join(',')})`
      let f = fins.get(id)
      if (!f) { fins.set(id, (f = fin(id, caps.get(`c:${e.map}`) ?? 1))); if (!cellsOf.has(e.map)) cellsOf.set(e.map, []); cellsOf.get(e.map)!.push({id, parts: t.parts}) }
      return f
    }
    return undefined
  }
  const keyEqs: {p: F, a: Tuple, b: Tuple}[] = []
  const intervals: {p: F, kind: 'lo' | 'hi', X: string[], L: string[], coefs: number[]}[] = []
  // An ordered term: a part, an ordered scalar, an ordered cell (a tuple's, or one of its own at a key of the wrong
  // sort), a constant; `le a b` is a ≤ b.
  const ordCells = new Map<string, {id: string, parts: string[]}[]>(), ordOdd: {id: string, map: string, key: E}[] = []
  const ordOf = (e: E): string | undefined => {
    if (e.op === 'const') { const id = `k:${e.value}`; ords.add(id); return id }
    const pn = partName(e)
    if (pn !== undefined && parts.has(pn)) { ords.add(`p:${pn}`); return `p:${pn}` }
    if (e.op === 'var') { if (ordScalars.has(e.name)) { ords.add(`s:${e.name}`); return `s:${e.name}` } return undefined }
    if (e.op === 'get' && ordMaps.has(e.map) && !(e as {args?: unknown}).args) {
      const t = fits(e.map, e.key)
      const id = t ? `c:${e.map}(${t.parts.join(',')})` : `c:${e.map}#${JSON.stringify(e.key)}`
      if (!ords.has(id)) { ords.add(id); if (t) { if (!ordCells.has(e.map)) ordCells.set(e.map, []); ordCells.get(e.map)!.push({id, parts: t.parts}) } else ordOdd.push({id, map: e.map, key: e.key}) }
      return id
    }
    return undefined
  }
  // (a value: an ordered term plus a constant, `o`: the ring's n + 1)
  const ordCases = (e: E): {g: F, t: string, o: number}[] | undefined => {
    if (e.op === 'if') { const c = lit(e.c), a = ordCases(e.then), b = ordCases(e.else); return a && b ? [...a.map(x => ({...x, g: and([c, x.g])})), ...b.map(x => ({...x, g: and([not(c), x.g])}))] : undefined }
    if (e.op === 'add' && e.b.op === 'const') { const a = ordCases(e.a); return a?.map(x => ({...x, o: x.o + (e.b as {value: number}).value})) }
    if (e.op === 'add' && e.a.op === 'const') { const b = ordCases(e.b); return b?.map(x => ({...x, o: x.o + (e.a as {value: number}).value})) }
    const t = ordOf(e)
    return t ? [{g: T, t, o: 0}] : undefined
  }
  // t1 − t2 + d ⋈ 0 as order atoms (naturals: t1 < t2 is t1 + 1 ≤ t2), or undefined
  // (a constant side takes the offset: t + d ⋈ k:c is t ⋈ k:(c − d), nothing below 0; t1 = t2 + 1, the successor, is an atom
  // that implies t2 < t1 with no term between, one way only: a gap no term names leaves it unknown)
  const succs: {s: number, lo: string, hi: string}[] = []
  const ordAtom = (t1: string, t2: string, d: number, op: '<' | '<=' | '='): F | undefined => {
    const num = (x: string) => (x.startsWith('k:') ? Number(x.slice(2)) : undefined), n1 = num(t1), n2 = num(t2)
    if (n1 !== undefined && n2 !== undefined) { const x = n1 - n2 + d; return {k: 'c', b: op === '<' ? x < 0 : op === '<=' ? x <= 0 : x === 0} }
    if (n2 !== undefined && d !== 0) { const c = n2 - d; if (c < 0) return Fa; ords.add(`k:${c}`); return ordAtom(t1, `k:${c}`, 0, op) }
    if (n1 !== undefined && d !== 0) { const c = n1 + d; if (c < 0) return op === '=' ? Fa : T; ords.add(`k:${c}`); return ordAtom(`k:${c}`, t2, 0, op) }
    const D = op === '<' ? d + 1 : d
    if (op === '=') {
      if (d === 0) return and([le(t1, t2), le(t2, t1)])
      if (Math.abs(d) !== 1) return undefined
      const [lo, hi] = d === -1 ? [t2, t1] : [t1, t2], s = atom(`succ ${lo} ${hi}`) as {k: 'v', v: number}
      succs.push({s: s.v, lo, hi}); return s
    }
    return D === 0 ? le(t1, t2) : D === 1 ? not(le(t2, t1)) : undefined
  }
  const ordered = (ts: [E, number][], d: number, op: '<' | '<=' | '='): F | undefined => {
    let a: E, b: E, dd = d
    if (ts.length === 2 && ts[0]![1] === 1 && ts[1]![1] === -1) [a, b] = [ts[0]![0], ts[1]![0]]
    else if (ts.length === 2 && ts[0]![1] === -1 && ts[1]![1] === 1) [a, b] = [ts[1]![0], ts[0]![0]]
    else if (ts.length === 1 && ts[0]![1] === 1) { a = ts[0]![0]; if (-d < 0) return Fa; b = {op: 'const', value: -d}; dd = 0 }
    else if (ts.length === 1 && ts[0]![1] === -1) { b = ts[0]![0]; if (d < 0) return op === '<' || op === '<=' ? T : Fa; a = {op: 'const', value: d}; dd = 0 }
    else return undefined
    const ca = ordCases(a), cb = ordCases(b)
    if (!ca || !cb || ca.length * cb.length > 256) return undefined
    const out: F[] = []
    for (const x of ca) for (const y of cb) { const at = ordAtom(x.t, y.t, dd + x.o - y.o, op); if (!at) return undefined; out.push(and([x.g, y.g, at])) }
    return or(out)
  }
  // A term's cases: guard and value (a constant, or a finite variable); undefined: not finite.
  type Case = {g: F, n?: number, f?: Fin}
  const cases = (e: E): Case[] | undefined => {
    if (e.op === 'const') return [{g: T, n: e.value}]
    if (e.op === 'if') { const c = lit(e.c), a = cases(e.then), b = cases(e.else); return a && b ? [...a.map(x => ({...x, g: and([c, x.g])})), ...b.map(x => ({...x, g: and([not(c), x.g])}))] : undefined }
    const f = finOf(e)
    return f ? [{g: T, f}] : undefined
  }
  // The comparison's sides as Σ coef·term + const; finite where every term is finite and every coefficient one sign.
  // (a ∸ b is a − b where every term of b is a term of a, at least as often: never truncated, as the terms are naturals)
  const exactSub = (e: {a: E, b: E}): boolean => {
    const ta: [string, number][] = [], tb: [string, number][] = [], da = {c: 0}, db = {c: 0}
    if (!linTerms(e.a, 1, ta, da) || !linTerms(e.b, 1, tb, db) || db.c > da.c) return false
    const have = new Map<string, number>(); for (const [x, c] of ta) have.set(x, (have.get(x) ?? 0) + c)
    return tb.every(([x, c]) => (have.get(x) ?? 0) >= c)
  }
  const sum = (e: E, k: number, ts: [E, number][], d: {c: number}): boolean =>
    e.op === 'const' ? ((d.c += k * e.value), true) : e.op === 'add' ? sum(e.a, k, ts, d) && sum(e.b, k, ts, d) : e.op === 'mul' ? sum(e.a, k * e.k, ts, d)
      : e.op === 'sub' && exactSub(e as {a: E, b: E}) ? sum((e as {a: E}).a, k, ts, d) && sum((e as {b: E}).b, -k, ts, d) : (ts.push([e, k]), true)
  // (an opaque comparison that reads only key parts and constants: an instance at a key of the wrong sort, harmless; one
  // that reads a scalar or a cell is arithmetic the abstraction can't read: a counter, a sum, a product)
  const foreign = new Set<number>()
  const opaque = (c: C): F => {
    const a = atom(`op ${JSON.stringify(c)}`) as {k: 'v', v: number}
    let keyOnly = true
    const wk = (o: unknown): void => { if (!keyOnly || !o || typeof o !== 'object') return; const x = o as {op?: string, name?: string}; if ((x.op === 'get' && !fnMaps.has((x as E & {map: string}).map) && !ordMaps.has((x as E & {map: string}).map)) || (x.op === 'var' && !parts.has(x.name!) && !ordScalars.has(x.name!))) { keyOnly = false; return } for (const y of Object.values(o)) wk(y) }
    wk(c)
    if (!keyOnly) foreign.add(a.v)
    return a
  }
  const comparison = (c: Extract<C, {a: E}>): F => {
    // a key equality: two tuples of one shape
    if (c.op === '=') {
      const ta = tupleOf(c.a), tb = tupleOf(c.b)
      if (ta && tb && sameCoefs(ta.coefs, tb.coefs) && [...ta.parts, ...tb.parts].every(p => parts.has(p))) {
        const p = opaque(c); keyEqs.push({p, a: ta, b: tb}); return p
      }
    }
    const ts: [E, number][] = [], d = {c: 0}
    sum(c.a, 1, ts, d); sum(c.b, -1, ts, d)
    // a part under a bound: x < k, x <= k
    if (ts.length === 1 && ts[0]![0].op === 'var' && parts.has(ts[0]![0].name) && Math.abs(ts[0]![1]) === 1 && c.op !== '=') {
      const [[x, s]] = ts as [[{op: 'var', name: string}, number]], k = -d.c * s // s·x + d ⋈ 0
      const strict = c.op === '<'
      // s = 1: x + d < 0 → x < −d; x + d <= 0 → x < −d + 1. s = −1: −x + d < 0 → x > d → ¬(x < d + 1); <= : ¬(x < d)
      return s === 1 ? ltAt(x.name, strict ? k : k + 1) : not(ltAt(x.name, strict ? k + 1 : k))
    }
    // a tuple against a prefix of its chain: L <= X (lo), X < L + c (hi), c the prefix's last coefficient
    if (c.op !== '=' && ts.length && ts.every(([e]) => e.op === 'var' && parts.has(e.name))) {
      const merged = new Map<string, number>()
      for (const [e, k] of ts) merged.set((e as {name: string}).name, (merged.get((e as {name: string}).name) ?? 0) + k)
      const pos = [...merged].filter(t => t[1] > 0).sort((a, b) => b[1] - a[1]), neg = [...merged].filter(t => t[1] < 0).map(([x, k]): [string, number] => [x, -k]).sort((a, b) => b[1] - a[1])
      const k0 = d.c + (c.op === '<' ? 1 : 0) // the form Σ ≤ 0 over integers: P − Q + k0 ≤ 0
      const chainOf = (ts2: [string, number][]) => ts2.map(t => t[1])
      const isChain = (cs: number[]) => cs.length > 0 && cs.every((x, i) => i + 1 >= cs.length || (x % cs[i + 1]! === 0 && x / cs[i + 1]! >= 2))
      const prefix = (full: number[], pre: number[]) => pre.length < full.length && pre.every((x, i) => x === full[i])
      // lo: L − X ≤ 0, P = L (prefix), Q = X (tuple, ending in 1); hi: X − L − c + 1 ≤ 0, P = X, Q = L
      const lo = k0 === 0 && chainOf(neg).at(-1) === 1 && isChain(chainOf(neg)) && prefix(chainOf(neg), chainOf(pos))
      const hi = chainOf(pos).at(-1) === 1 && isChain(chainOf(pos)) && prefix(chainOf(pos), chainOf(neg)) && neg.length > 0 && k0 === 1 - neg.at(-1)![1]
      if (lo || hi) {
        const X = lo ? neg : pos, L = lo ? pos : neg, a = opaque(c)
        intervals.push({p: a, kind: lo ? 'lo' : 'hi', X: X.map(t => t[0]), L: L.map(t => t[0]), coefs: chainOf(X)})
        return a
      }
    }
    // ordered: a term against another, or a constant, one of them an ordered cell or scalar
    {
      const reads = (e: E): boolean => e.op === 'get' ? ordMaps.has(e.map) || fnMaps.has(e.map) : e.op === 'var' ? ordScalars.has(e.name) || parts.has(e.name) : e.op === 'if' ? reads(e.then) || reads(e.else) : e.op === 'add' ? reads(e.a) || reads(e.b) : false
      if (ts.some(([e]) => reads(e))) { const f = ordered(ts, d.c, c.op); if (f) return f }
    }
    // finite: every term finite, coefficients of one sign
    // (the terms not exact of one sign, the exact ones of any: a capped term at its cap decides it as any larger value)
    const cs = ts.length ? ts.map(([e]) => cases(e)) : [], loose = ts.filter((_, i) => !cs[i]?.every(y => y.n !== undefined || y.f!.exact !== undefined))
    if (ts.length && (loose.every(t => t[1] > 0) || loose.every(t => t[1] < 0))) {
      if (cs.every(Boolean)) {
        const holds = (v: number) => (c.op === '<' ? v < 0 : c.op === '<=' ? v <= 0 : v === 0)
        const out: F[] = []
        let combos = 0
        const go = (i: number, acc: number, g: F[]): boolean => {
          if (++combos > 4096) return false
          if (i === ts.length) { if (holds(acc + d.c)) out.push(and(g)); return true }
          for (const x of cs[i]!) {
            if (x.n !== undefined) { if (!go(i + 1, acc + ts[i]![1] * x.n, [...g, x.g])) return false; continue }
            for (let v = 0; v <= x.f!.cap; v++) if (!go(i + 1, acc + ts[i]![1] * v, [...g, x.g, finAt(x.f!, v)])) return false
          }
          return true
        }
        if (go(0, 0, [])) return or(out)
      }
    }
    if (!ts.length) return {k: 'c', b: c.op === '<' ? d.c < 0 : c.op === '<=' ? d.c <= 0 : d.c === 0}
    return opaque(c)
  }
  const lit = (c: C): F => {
    switch (c.op) {
      case 'and': return and(c.xs.map(lit))
      case 'or': return or(c.xs.map(lit))
      case 'not': return not(lit(c.x))
      case '<': case '<=': case '=': return comparison(c)
      case 'all': case 'flag': return opaque(c)
    }
  }
  const forms = hyps.map(h => (h ? lit(h) : undefined))
  // (an order over many terms is a cubic number of transitivity clauses: past 64 terms they are added lazily, those a
  // model breaks, below; past 512, the totality's pairs alone are too many, and the goal keeps the usual path)
  if (ords.size > 512) return {unknown: `${ords.size} ordered terms`}
  const lazy = ords.size > 64

  // --- clauses (literals: +v / −v), each with the hypotheses it stands for
  const clauses: {lits: number[], from: Origin}[] = []
  const add = (lits: number[], from: Origin) => { const s = new Set(lits); for (const l of s) if (s.has(-l)) return; clauses.push({lits: [...s], from}) }
  let fresh = 0
  const tseitin = (f: F, from: Origin): number => { // a literal equivalent to f
    if (f.k === 'v') return f.v
    if (f.k === 'not') return -tseitin(f.x, from)
    if (f.k === 'c') { const g = ++fresh + 1e6; add([f.b ? g : -g], -1); return g }
    const ls = f.xs.map(x => tseitin(x, from)), g = ++fresh + 1e6
    if (f.k === 'and') { for (const l of ls) add([-g, l], from); add([g, ...ls.map(l => -l)], from) } else { add([-g, ...ls], from); for (const l of ls) add([g, -l], from) }
    return g
  }
  const top = (f: F, from: Origin) => {
    if (f.k === 'and') { for (const x of f.xs) top(x, from); return }
    if (f.k === 'c') { if (!f.b) add([], from); return }
    if (f.k === 'or' && f.xs.every(x => x.k === 'v' || (x.k === 'not' && x.x.k === 'v'))) { add(f.xs.map(x => (x.k === 'v' ? x.v : -(x as {x: {v: number}}).x.v)), from); return }
    add([tseitin(f, from)], from)
  }
  forms.forEach((f, i) => { if (f) top(f, i) })
  // axioms: congruence of cells; a composed key's injectivity where its parts are under their bounds; one value per finite
  // variable; the order (below), whose transitivity is equality's and the bounds' too
  const v = (f: F) => (f.k === 'v' ? f.v : f.k === 'not' && f.x.k === 'v' ? -f.x.v : undefined)
  for (const {p, a, b} of keyEqs) {
    const pv = v(p)!, es = a.parts.map((x, i) => eq(x, b.parts[i]!))
    // equal parts: equal keys, always; equal keys with every part but the top under its bound: equal parts
    add([...es.map(e => (e.k === 'v' ? -e.v : 0)).filter(Boolean), pv], -1)
    const bounded = a.bounds.flatMap((bd, i) => (bd === undefined ? [] : [v(ltAt(a.parts[i]!, bd))!, v(ltAt(b.parts[i]!, bd))!]))
    for (const e of es) if (e.k === 'v') add([-pv, ...bounded.map(l => -l), e.v], -1)
  }
  // an interval of a prefix: equal prefixes give lo always and hi where X's low parts are under their bounds; lo and hi
  // with every part of X and L but the top under its bound give equal prefixes (a pair of one X and one L)
  const baseOf = (coefs: number[], i: number) => coefs[i - 1]! / coefs[i]!
  const pairs = new Map<string, {lo?: number, hi?: number, X: string[], L: string[], coefs: number[]}>()
  for (const iv of intervals) {
    const pe = iv.L.map((y, i) => eq(iv.X[i]!, y)), pv = v(iv.p)!
    const lowBounded = iv.X.flatMap((x, i) => (i >= iv.L.length ? [v(ltAt(x, baseOf(iv.coefs, i)))!] : []))
    add([...pe.filter(e => e.k === 'v').map(e => -(e as {v: number}).v), ...(iv.kind === 'hi' ? lowBounded.map(l => -l) : []), pv], -1)
    const key = `${iv.X.join(',')}|${iv.L.join(',')}`, pr = pairs.get(key) ?? {X: iv.X, L: iv.L, coefs: iv.coefs}
    pr[iv.kind] = pv; pairs.set(key, pr)
  }
  for (const pr of pairs.values()) {
    if (pr.lo === undefined || pr.hi === undefined) continue
    const bounded = [...pr.X.flatMap((x, i) => (i ? [v(ltAt(x, baseOf(pr.coefs, i)))!] : [])), ...pr.L.flatMap((y, i) => (i ? [v(ltAt(y, baseOf(pr.coefs, i)))!] : []))]
    for (const [i, y] of pr.L.entries()) { const e = eq(pr.X[i]!, y); if (e.k === 'v') add([-pr.lo, -pr.hi, ...bounded.map(l => -l), e.v], -1) }
  }
  for (const [, cells] of cellsOf) for (let i = 0; i < cells.length; i++) for (let j = i + 1; j < cells.length; j++) {
    const a = cells[i]!, b = cells[j]!, es = a.parts.map((x, k) => v(eq(x, b.parts[k]!)))
    const fa = fins.get(a.id)!, fb = fins.get(b.id)!, cap = Math.max(fa.cap, fb.cap)
    for (let val = 0; val <= cap; val++) {
      const la = val <= fa.cap ? v(finAt(fa, val))! : undefined, lb = val <= fb.cap ? v(finAt(fb, val))! : undefined
      const pre = es.filter((e): e is number => e !== undefined).map(e => -e)
      if (la !== undefined) add([...pre, -la, ...(lb !== undefined ? [lb] : [])], -1)
      if (lb !== undefined) add([...pre, -lb, ...(la !== undefined ? [la] : [])], -1)
    }
  }
  // the order: total, transitive, discrete, the constants in their order, every term at least 0, a part's equality its
  // order both ways, equal tuples equal ordered cells
  {
    const os = [...ords], num = (x: string) => (x.startsWith('k:') ? Number(x.slice(2)) : undefined)
    for (let i = 0; i < os.length; i++) for (let j = i + 1; j < os.length; j++) {
      const a = os[i]!, b = os[j]!, na = num(a), nb = num(b)
      add([v(le(a, b))!, v(le(b, a))!], -1)
      if (na !== undefined && nb !== undefined) { add([na <= nb ? v(le(a, b))! : -v(le(a, b))!], -1); add([nb <= na ? v(le(b, a))! : -v(le(b, a))!], -1) }
    }
    for (const x of os) if (x !== 'k:0') add([v(le('k:0', x))!], -1)
    // (the naturals are discrete: nothing between c and c + 1)
    for (const c of os.map(num).filter((n): n is number => n !== undefined)) if (ords.has(`k:${c + 1}`)) for (const x of os) if (!x.startsWith('k:')) add([v(le(x, `k:${c}`))!, v(le(`k:${c + 1}`, x))!], -1)
    if (!lazy) for (const a of os) for (const b of os) if (a !== b) for (const c of os) if (c !== a && c !== b) add([-v(le(a, b))!, -v(le(b, c))!, v(le(a, c))!], -1)
    const ordParts = os.filter(x => x.startsWith('p:')).map(x => x.slice(2))
    for (let i = 0; i < ordParts.length; i++) for (let j = i + 1; j < ordParts.length; j++) {
      const x = ordParts[i]!, y = ordParts[j]!, e = v(eq(x, y))!, a = v(le(`p:${x}`, `p:${y}`))!, b = v(le(`p:${y}`, `p:${x}`))!
      add([-e, a], -1); add([-e, b], -1); add([e, -a, -b], -1)
    }
    // a function's reads at equal parts are equal (Ackermann); a successor has nothing between it and its predecessor
    for (let i = 0; i < fnParts.length; i++) for (let j = i + 1; j < fnParts.length; j++) {
      const x = fnParts[i]!, y = fnParts[j]!
      if (x.f === y.f && x.n !== y.n) { const a = v(eq(x.a, y.a)), b = v(eq(x.n, y.n)); if (a !== undefined && b !== undefined) add([-a, b], -1) }
    }
    for (const {s, lo, hi} of succs) { add([-s, -v(le(hi, lo))!], -1); for (const z of ords) if (z !== lo && z !== hi) add([-s, v(le(z, lo))!, v(le(hi, z))!], -1) }
    for (const [, cells] of ordCells) for (let i = 0; i < cells.length; i++) for (let j = i + 1; j < cells.length; j++) {
      const a = cells[i]!, b = cells[j]!, pre = a.parts.map((x, k) => v(eq(x, b.parts[k]!))).filter((e): e is number => e !== undefined).map(e => -e)
      add([...pre, v(le(a.id, b.id))!], -1); add([...pre, v(le(b.id, a.id))!], -1)
    }
  }
  for (const f of fins.values()) {
    const ls = Array.from({length: f.cap + 1}, (_, val) => v(finAt(f, val))!)
    add(ls, f.exact ?? -1)
    for (let i = 0; i < ls.length; i++) for (let j = i + 1; j < ls.length; j++) add([-ls[i]!, -ls[j]!], -1)
  }

  // EPR-shaped: no comparison the abstraction can't read (a counter's arithmetic, a sum, a product) in any hypothesis
  if (opts.exact) { const tied = new Set([...keyEqs, ...intervals].map(k => (k.p as {v: number}).v)); const loose = [...foreign].filter(i => !tied.has(i)).length; if (loose) return {unknown: `${loose} comparisons outside the EPR shape`} }
  // --- the search
  // (a finite variable at 0 first: models with the least values, which break the fewest laws at keys nothing names)
  const first = new Set([...fins.values()].map(f => v(finAt(f, 0))!))
  if (opts.late?.()) return {unknown: 'past the deadline'}
  // (lazily: the transitivity a model breaks, added and the search again, at most 4,096 a round and 16 rounds; as each
  // holds in every model, a refutation stays one)
  let out = cdcl(clauses, opts.conflicts ?? 200_000, first, opts.late)
  for (let round = 0; lazy && out?.sat; round++) {
    const m = out.model, os = [...ords], at = (a: string, b: string) => a === b || m[v(le(a, b))!] === true, broken: number[][] = []
    for (const a of os) for (const b of os) if (a !== b && at(a, b)) for (const c of os) if (c !== a && c !== b && at(b, c) && !at(a, c) && broken.length < 4096) broken.push([-v(le(a, b))!, -v(le(b, c))!, v(le(a, c))!])
    if (!broken.length) break
    if (round === 16 || opts.late?.()) return {unknown: 'the order\'s transitivity, lazily, did not settle'}
    for (const c of broken) add(c, -1)
    out = cdcl(clauses, opts.conflicts ?? 200_000, first, opts.late)
  }
  if (out === undefined) return {unknown: 'the conflict budget ran out, or the deadline'}
  if (!out.sat) return {sat: false, core: [...out.core].filter(i => i >= 0).sort((a, b) => a - b)}
  // --- a model, read back: the ordered terms (the parts among them) by the model's order, each composed key the radix
  // sum of its parts, each cell and scalar its value; then judged on every hypothesis
  const val = (l: number) => out.model[l] === true
  const w: Record<string, number> = {}
  for (const f of fins.values()) {
    let x = 0
    for (let val2 = 0; val2 <= f.cap; val2++) if (val(v(finAt(f, val2))!)) x = val2
    if (f.id.startsWith('s:')) w[f.id.slice(2)] = x
  }
  // each group of equal terms the next value, a constant's group its own; odd where there is room before the next constant
  // (a key of the wrong sort, 2·64·x + y, then meets no cell 64·x' + y), and far apart past every constant (composed keys
  // of parts above every bound then don't meet)
  const ordVal = new Map<string, number>()
  {
    const leq = (a: string, b: string) => a === b || val(v(le(a, b))!)
    const os = [...ords].sort((a, b) => (leq(a, b) && !leq(b, a) ? -1 : leq(b, a) && !leq(a, b) ? 1 : 0))
    const groups: string[][] = []
    for (let i = 0; i < os.length;) { let j = i; while (j < os.length && leq(os[j]!, os[i]!) && leq(os[i]!, os[j]!)) j++; groups.push(os.slice(i, j)); i = j }
    const constOf = (g: string[]) => { const cs = [...new Set(g.filter(x => x.startsWith('k:')).map(x => Number(x.slice(2))))]; return cs.length > 1 ? NaN : cs[0] }
    let prev = -1, far = 0
    for (const [gi, g] of groups.entries()) {
      const c = constOf(g)
      if (Number.isNaN(c)) return {unknown: 'the model\'s order equates two constants'}
      let next = Infinity
      for (const h of groups.slice(gi + 1)) { const d = constOf(h); if (d !== undefined) { next = d; break } }
      let x = c ?? (next === Infinity && prev > 0 ? (1 << 24) * ++far + 997 * far + prev + 13 : prev + 1)
      if (c === undefined && next !== Infinity && x % 2 === 0 && x + 1 < next) x++
      if (x <= prev || x >= next) return {unknown: 'no values for the model\'s order'}
      for (const t of g) ordVal.set(t, x)
      prev = x
    }
    for (const [t, x] of ordVal) if (t.startsWith('p:') || t.startsWith('s:')) w[t.slice(2)] = x
  }
  const maps = new Map<string, Map<number, number>>()
  const cellVal = new Map<string, number>()
  for (const f of fins.values()) if (f.id.startsWith('c:')) { let x = 0; for (let val2 = 0; val2 <= f.cap; val2++) if (val(v(finAt(f, val2))!)) x = val2; cellVal.set(f.id, x) }
  for (const [mp, cells] of ordCells) for (const c of cells) { cellVal.set(c.id, ordVal.get(c.id) ?? 0); if (!cellsOf.has(mp)) cellsOf.set(mp, []); cellsOf.get(mp)!.push(c) }
  for (const o of ordOdd) { cellVal.set(o.id, ordVal.get(o.id) ?? 0); odd.push(o) }
  // every read of the goal, at its key's value under w: the abstraction's value where it has one, else 0
  const keyVal = (e: E): number | undefined => { const ts: [string, number][] = [], d = {c: 0}; if (!linTerms(e, 1, ts, d)) return undefined; let s = d.c; for (const [x, c] of ts) { if (w[x] === undefined) return undefined; s += c * w[x]! } return s }
  // (each function's table at its parts' values)
  for (const {f, n, a} of fnParts) { if (!maps.has(f)) maps.set(f, new Map()); maps.get(f)!.set(w[a]!, w[n]!) }
  // (and at a key of the wrong sort, a value of its own, the least unused: an injective function's instance there holds)
  const fnOdd = (o: unknown): void => {
    if (!o || typeof o !== 'object') return
    for (const y of Object.values(o)) fnOdd(y)
    const x = o as E
    if (x.op !== 'get' || !fnMaps.has(x.map) || partName(x) !== undefined) return
    const key = keyVal(x.key), t = maps.get(x.map) ?? new Map<number, number>()
    if (key === undefined || t.has(key)) return
    const used = new Set(t.values()); let u = 0; while (used.has(u)) u++
    maps.set(x.map, t.set(key, u))
  }
  goal.hyps.forEach(fnOdd)
  for (const [mp, cells] of cellsOf) for (const c of cells) {
    const key = c.parts.reduce((s, p, i) => s + w[p]! * (patterns[mp]![i] ?? 1), 0)
    if (!maps.has(mp)) maps.set(mp, new Map())
    maps.get(mp)!.set(key, cellVal.get(c.id)!)
  }
  // (a cell at a key of the wrong sort, where its key falls, unless a cell of the right sort is there: one cell, whose
  // value the hypotheses are judged with below)
  for (const o of odd) {
    const key = keyVal(o.key)
    if (key === undefined) continue
    if (!maps.has(o.map)) maps.set(o.map, new Map())
    if (!maps.get(o.map)!.has(key)) maps.get(o.map)!.set(key, cellVal.get(o.id)!)
  }
  const allMaps = new Set<string>()
  const scan = (o: unknown): void => { if (!o || typeof o !== 'object') return; const x = o as {op?: string, map?: string}; if (x.op === 'get') allMaps.add(x.map!); for (const y of Object.values(o)) scan(y) }
  goal.hyps.forEach(scan)
  const st = {scalars: {}, maps: Object.fromEntries([...allMaps].map(mp => [mp, maps.get(mp) ?? new Map<number, number>()]))}
  const m = {name: goal.name, params: [], inputs: [], state: {}, step: {}, maps: Object.fromEntries([...allMaps].map(mp => [mp, 0]))} as unknown as Machine
  const env = new Proxy({...w}, {get: (t, q: string) => t[q] ?? 0}) as Record<string, number>
  for (const [i, h] of goal.hyps.entries()) { try { if (!evalC(h, env, st, m)) { return {unknown: `the abstraction's model breaks hypothesis ${i}${shaped[i] ? '' : ' (not EPR-shaped)'}`} } } catch { return {unknown: 'the model could not be read'} } }
  // the kernel's witness: names, and each cell of the goal by its key's linear form
  const witness: Record<string, number> = {...w}
  const cellName = (o: unknown): void => {
    if (!o || typeof o !== 'object') return
    const x = o as {op?: string, map?: string, key?: E}
    if (x.op === 'get' && x.key) { const l = linear(x.key, new Map()), kv = keyVal(x.key); if (l && kv !== undefined) witness[`${x.map}[${canon(l)}]`] = st.maps[x.map!]?.get(kv) ?? 0 }
    for (const y of Object.values(o)) cellName(y)
  }
  goal.hyps.forEach(cellName)
  return {sat: true, witness}
}

// A small CDCL over clauses with origins: two watched literals, activity, learned clauses carrying the union of the
// origins they were resolved from, so a refutation's origins are its core. undefined: past the conflict budget.
function cdcl(input: {lits: number[], from: Origin}[], budget: number, trueFirst: Set<number> = new Set(), late?: () => boolean): {sat: true, model: boolean[]} | {sat: false, core: Set<number>} | undefined {
  let n = 0
  for (const c of input) for (const l of c.lits) n = Math.max(n, Math.abs(l))
  const idx = new Map<number, number>(), back: number[] = [0]
  const vid = (l: number) => { const a = Math.abs(l); let i = idx.get(a); if (i === undefined) { i = back.length; idx.set(a, i); back.push(a) } return l > 0 ? i : -i }
  type Cl = {lits: number[], from: Set<number>}
  const cls: Cl[] = input.map(c => ({lits: c.lits.map(vid), from: new Set([c.from])}))
  const nv = back.length, val = new Int8Array(nv), level = new Int32Array(nv), reason: (Cl | undefined)[] = Array(nv), act = new Float64Array(nv)
  const watch = new Map<number, Cl[]>()
  const wl = (l: number) => { let w = watch.get(l); if (!w) watch.set(l, (w = [])); return w }
  const valOf = (l: number) => (val[Math.abs(l)] === 0 ? 0 : (val[Math.abs(l)]! > 0) === (l > 0) ? 1 : -1)
  const trail: number[] = [], lim: number[] = []
  const assign = (l: number, r?: Cl) => { val[Math.abs(l)] = l > 0 ? 1 : -1; level[Math.abs(l)] = lim.length; reason[Math.abs(l)] = r; trail.push(l) }
  let qhead = 0
  const units: Cl[] = []
  for (const c of cls) {
    if (!c.lits.length) return {sat: false, core: c.from}
    if (c.lits.length === 1) units.push(c); else { wl(-c.lits[0]!).push(c); wl(-c.lits[1]!).push(c) }
  }
  const coreOf = (c: Cl): Set<number> => { // the origins of a conflict at level 0, through the reasons of its literals
    const out = new Set(c.from), seen = new Set<number>(), todo = c.lits.map(Math.abs)
    while (todo.length) { const x = todo.pop()!; if (seen.has(x)) continue; seen.add(x); const r = reason[x]; if (r) { for (const o of r.from) out.add(o); for (const l of r.lits) todo.push(Math.abs(l)) } }
    return out
  }
  for (const u of units) { const s = valOf(u.lits[0]!); if (s < 0) return {sat: false, core: coreOf(u)}; if (s === 0) assign(u.lits[0]!, u) }
  const propagate = (): Cl | undefined => {
    while (qhead < trail.length) {
      const l = trail[qhead++]!, ws = wl(l)
      for (let i = 0; i < ws.length; i++) {
        const c = ws[i]!
        if (c.lits[0] === -l) { c.lits[0] = c.lits[1]!; c.lits[1] = -l }
        if (valOf(c.lits[0]!) > 0) continue
        let moved = false
        for (let k = 2; k < c.lits.length; k++) if (valOf(c.lits[k]!) >= 0) { const t = c.lits[1]!; c.lits[1] = c.lits[k]!; c.lits[k] = t; wl(-c.lits[1]!).push(c); ws.splice(i--, 1); moved = true; break }
        if (moved) continue
        if (valOf(c.lits[0]!) < 0) { qhead = trail.length; return c }
        assign(c.lits[0]!, c)
      }
    }
    return undefined
  }
  let inc = 1, conflicts = 0
  for (;;) {
    const confl = propagate()
    if (confl) {
      if (++conflicts > budget || (conflicts % 256 === 0 && late?.())) return undefined
      if (!lim.length) return {sat: false, core: coreOf(confl)}
      // first UIP
      const seen = new Uint8Array(nv), learnt: number[] = [], from = new Set(confl.from)
      let p = 0, cnt = 0, c: Cl | undefined = confl, ti = trail.length - 1
      do {
        for (const q of c!.lits) {
          if (q === p) continue
          const x = Math.abs(q)
          if (!seen[x] && level[x]! > 0) { seen[x] = 1; act[x] = act[x]! + inc; if (level[x] === lim.length) cnt++; else learnt.push(q) }
          else if (!seen[x] && level[x] === 0 && reason[x]) { seen[x] = 1; for (const o of coreOf({lits: [q], from: new Set()})) from.add(o) }
        }
        while (!seen[Math.abs(trail[ti]!)]) ti--
        p = trail[ti--]!; c = reason[Math.abs(p)]; if (c) for (const o of c.from) from.add(o); cnt--
      } while (cnt > 0)
      learnt.unshift(-p)
      inc *= 1.05
      let bt = 0, bi = 1
      for (let i = 1; i < learnt.length; i++) if (level[Math.abs(learnt[i]!)]! > bt) { bt = level[Math.abs(learnt[i]!)]!; bi = i }
      if (learnt.length > 1) { const t = learnt[1]!; learnt[1] = learnt[bi]!; learnt[bi] = t }
      while (lim.length > bt) { const at = lim.pop()!; while (trail.length > at) { const x = Math.abs(trail.pop()!); val[x] = 0; reason[x] = undefined } }
      qhead = trail.length
      const nc: Cl = {lits: learnt, from}
      if (learnt.length > 1) { wl(-learnt[0]!).push(nc); wl(-learnt[1]!).push(nc) }
      assign(learnt[0]!, nc)
      continue
    }
    // decide: the most active unassigned variable, false first
    let best = 0, ba = -1
    for (let x = 1; x < nv; x++) if (val[x] === 0 && act[x]! > ba) { ba = act[x]!; best = x }
    if (!best) { const model: boolean[] = []; for (let x = 1; x < nv; x++) model[back[x]!] = val[x]! > 0; return {sat: true, model} }
    lim.push(trail.length)
    assign(trueFirst.has(back[best]!) ? best : -best)
  }
}
