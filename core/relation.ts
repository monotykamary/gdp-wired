// A loop's turn as its relation: the linear paths of one turn (kernel.ts's Loop), for a search that reads the relation
// rather than runs (core/cycles.ts's ranks found from the relation's counterexamples). Untrusted: what is found here is
// a candidate, and the kernel proves whatever is kept from it.
//
// A path is a conjunction of linear rows over the state, the params and the turn's inputs (each a natural), with the
// state after the turn linear in them: `while`, `assume` and the laws are put in disjunctive form, each `if` of the body
// decided by the values the path pins (pc = 3, t = 1: an equation of one variable) or split, each truncated difference
// a ∸ b split on a ≥ b (a − b, or 0 below it), min and max alike. A product of two variables stands for a natural of
// its own (the path is then larger than the turn: a search must check what it finds against the turn itself).
//
// Integers: two naturals that every row and every value reads only as their difference (u − w, as an integer slot is
// written: kernel.ts's pairs, the DSL's x and x$neg, compare/term's s and s$n), and whose values after the turn are a
// difference split both ways (u := P ∸ N, w := N ∸ P) or linear, are one integer, u − w: the path then needs no split
// for them (u − w becomes P − N exactly), and a rank over them is over the integer. Each is named by its first part.
import type {C, E, Law} from './machine.ts'
import type {Loop} from '../kernel/kernel.ts'
import {clock} from '../kernel/prove.ts'
import {type Lin, solve, work} from './solver.ts'

export type Path = {
  rows: Lin[] // each lin <= 0, over the integers (`ints`) and naturals (`nats`) of the relation
  pins: Record<string, number> // the raw values the path fixes (a location, a rule's index)
  post: Record<string, Lin> // each state integer and natural after the turn (the location's left out), over the same
}
export type Relation = {
  paths: Path[]
  ints: Map<string, [string, string]> // an integer: its name (the first part) and its two naturals
  nats: string[] // the naturals left as they are
  state: string[] // the state's integers and naturals (each a name of ints or nats), the location's left out
  params: string[] // the params' (likewise), those the paths read
  loc?: string // the state natural every path fixes before and after (a location), if one
  from: number[] // each path's location before and after (its value of loc), where there is one
  to: number[]
  exact: boolean // no product stood for by a natural
}

class Refused extends Error {}
type PP = {rows: Lin[], pins: Record<string, number>}
type Val = {lin: Lin} | {sub: [Lin, Lin]}
const id = (t: unknown) => JSON.stringify(t)
const canon = (l: Lin) => id(Object.keys(l).sort().map(x => [x, l[x]]))
const plus = (a: Lin, b: Lin, f = 1): Lin => { const o: Lin = {...a}; for (const x in b) { o[x] = (o[x] ?? 0) + f * b[x]!; if (!o[x]) delete o[x] } return o }
const times = (a: Lin, f: number): Lin => { const o: Lin = {}; if (f) for (const x in a) o[x] = a[x]! * f; return o }
const konst = (c: number): Lin => (c ? {1: c} : {})
const vars = (l: Lin) => Object.keys(l).filter(x => x !== '1')
const pinned = (l: Lin, pins: Record<string, number>): Lin => {
  let out: Lin | undefined
  for (const x in l) if (x !== '1' && x in pins) { out ??= {...l}; delete out[x]; out['1'] = (out['1'] ?? 0) + l[x]! * pins[x]!; if (!out['1']) delete out['1'] }
  return out ?? l
}

// Every alternative of a term under a path (the path extended by each split), and the term's linear value there.
function alts(e: E, p: PP, n: {left: number}): [PP, Lin][] {
  if (--n.left < 0) throw new Refused('too many paths')
  switch (e.op) {
    case 'var': return [[p, e.name in p.pins ? konst(p.pins[e.name]!) : {[e.name]: 1}]]
    case 'const': return [[p, konst(e.value)]]
    case 'add': return alts(e.a, p, n).flatMap(([q, a]) => alts(e.b, q, n).map(([r, b]): [PP, Lin] => [r, plus(a, b)]))
    case 'mul': return alts(e.a, p, n).map(([q, a]) => [q, times(a, e.k)])
    case 'sub': case 'min': case 'max':
      return alts(e.a, p, n).flatMap(([q, a]) => alts(e.b, q, n).flatMap(([r, b]): [PP, Lin][] => {
        const d = plus(a, b, -1), c = vars(d).length ? undefined : (d['1'] ?? 0)
        // a ≥ b: a − b, a's, b's; below: 0, b's, a's
        const ge = e.op === 'sub' ? d : e.op === 'max' ? a : b, lt = e.op === 'sub' ? {} : e.op === 'max' ? b : a
        if (c !== undefined) return [[r, c >= 0 ? ge : lt]]
        return [...row(r, times(d, -1)).map((s): [PP, Lin] => [s, ge]), ...row(r, plus(d, konst(1))).map((s): [PP, Lin] => [s, lt])]
      }))
    case 'prod': return alts(e.a, p, n).flatMap(([q, a]) => alts(e.b, q, n).map(([r, b]): [PP, Lin] => {
      if (!vars(a).length) return [r, times(b, a['1'] ?? 0)]
      if (!vars(b).length) return [r, times(a, b['1'] ?? 0)]
      return [r, {[`π(${[id(a), id(b)].sort().join('·')})`]: 1}]
    }))
    case 'if': return chain(e, p, n, alts)
    case 'get': throw new Refused('a map')
  }
}
// A row lin <= 0 added (none where the pins decide it: kept or dropped); an equation of one variable pins it.
function row(p: PP, l0: Lin): PP[] {
  const l = pinned(l0, p.pins), xs = vars(l)
  if (!xs.length) return (l['1'] ?? 0) <= 0 ? [p] : []
  return [{rows: [...p.rows, l], pins: p.pins}]
}
function equal(p: PP, d0: Lin): PP[] {
  const d = pinned(d0, p.pins), xs = vars(d)
  if (!xs.length) return (d['1'] ?? 0) === 0 ? [p] : []
  if (xs.length === 1 && Math.abs(d[xs[0]!]!) === 1) {
    const value = -(d['1'] ?? 0) * d[xs[0]!]!
    return value >= 0 ? [{rows: p.rows, pins: {...p.pins, [xs[0]!]: value}}] : []
  }
  return [{rows: [...p.rows, d, times(d, -1)], pins: p.pins}]
}
// The paths where c holds (positive) or fails, each extending p.
function assert(c: C, p: PP, positive: boolean, n: {left: number}): PP[] {
  switch (c.op) {
    case '<': case '<=': case '=':
      return alts(c.a, p, n).flatMap(([q, a]) => alts(c.b, q, n).flatMap(([r, b]) => {
        const d = plus(a, b, -1) // a − b
        if (c.op === '=') return positive ? equal(r, d) : [...row(r, plus(d, konst(1))), ...row(r, plus(times(d, -1), konst(1)))]
        const strict = (c.op === '<') === positive // positive <: d + 1 <= 0; not <=: b < a, −d + 1 <= 0
        return positive ? row(r, strict ? plus(d, konst(1)) : d) : row(r, strict ? plus(times(d, -1), konst(1)) : times(d, -1))
      }))
    case 'and': case 'or':
      // a conjunction holding, or a disjunction failing: each part in turn; else any part
      if ((c.op === 'and') === positive) return c.xs.reduce((ps: PP[], x) => ps.flatMap(q => assert(x, q, positive, n)), [p])
      {
        // (a part the pins decide true is the path itself: the others' paths are within it)
        const out: PP[] = []
        for (const x of c.xs) { const ys = assert(x, p, positive, n); if (ys.includes(p)) return [p]; out.push(...ys) }
        return [...new Map(out.map(q => [id([q.rows.map(canon), Object.entries(q.pins).sort((a, b) => (a[0] < b[0] ? -1 : 1))]), q])).values()]
      }
    case 'not': return assert(c.x, p, !positive, n)
    case 'flag': case 'all': throw new Refused('a flag')
  }
}
// The body's value of a state variable on a path: its ifs decided or split, a truncated difference at the top kept
// whole (an integer's part, if it is one).
// An if and the ifs of its else branches, one after another (a long chain of rules is no deeper a recursion).
function chain<T>(e: E, p: PP, n: {left: number}, leaf: (e: E, p: PP, n: {left: number}) => [PP, T][]): [PP, T][] {
  const out: [PP, T][] = []
  let cur = e, ps = [p]
  while (cur.op === 'if' && ps.length) {
    const c = cur.c, then = cur.then
    for (const q of ps) for (const r of assert(c, q, true, n)) out.push(...leaf(then, r, n))
    ps = ps.flatMap(q => assert(c, q, false, n))
    cur = cur.else
  }
  for (const q of ps) out.push(...leaf(cur, q, n))
  return out
}
function valueOf(e: E, p: PP, n: {left: number}): [PP, Val][] {
  if (e.op === 'if') return chain(e, p, n, valueOf)
  if (e.op === 'sub') return alts(e.a, p, n).flatMap(([q, a]) => alts(e.b, q, n).map(([r, b]): [PP, Val] => [r, {sub: [a, b]}]))
  return alts(e, p, n).map(([q, l]) => [q, {lin: l}])
}

// The relation of one turn, or undefined where it isn't linear in this sense (a map, a flag, past `cap` alternatives).
export function relationOf(l: Loop, laws: Law[] = [], cap = 4000): Relation | undefined {
  try { return build(l, laws, cap) } catch (e) { if (e instanceof Refused || e instanceof RangeError) return undefined; throw e }
}
function build(l: Loop, laws: Law[], cap: number): Relation {
  const n = {left: cap * 500}, state = Object.keys(l.state), prime = (x: string) => `${x}′`
  // the turn: while, the assumption and the laws, then each state variable's value after it
  type Raw = {p: PP, vals: Record<string, Val>}
  let ps: PP[] = [{rows: [], pins: {}}]
  for (const c of [l.while, ...(l.assume ? [l.assume] : []), ...laws.map(x => x.holds)]) ps = ps.flatMap(p => assert(c, p, true, n))
  let raws: Raw[] = ps.map(p => ({p, vals: {}}))
  for (const x of state) {
    const e = l.body[x] ?? {op: 'var', name: x}
    raws = raws.flatMap(r => valueOf(e, r.p, n).map(([p, v]) => ({p, vals: {...r.vals, [x]: v}})))
    if (raws.length > cap) throw new Refused('too many paths')
  }
  const isSub = (v: Val): v is {sub: [Lin, Lin]} => 'sub' in v
  const diff = (v: {sub: [Lin, Lin]}) => plus(v.sub[0], v.sub[1], -1)
  // Candidate integers among the state: two variables whose values are complementary differences, or both linear, on
  // every path (and complementary on one at least).
  const pairs = new Map<string, string>() // first part → second
  const taken = new Set<string>()
  for (const [i, x] of state.entries()) for (const y of state.slice(i + 1)) {
    if (taken.has(x) || taken.has(y)) continue
    let seen = false, ok = true
    for (const r of raws) {
      const a = r.vals[x]!, b = r.vals[y]!
      if (isSub(a) !== isSub(b)) { ok = false; break }
      if (isSub(a) && isSub(b)) { if (canon(diff(a)) !== canon(times(diff(b), -1))) { ok = false; break } seen = true }
    }
    if (ok && seen) { pairs.set(x, y); taken.add(x); taken.add(y) }
  }
  // The other truncated differences split (as `alts` splits them); `while` after the turn over primed names, pinned
  // where the value after is a constant.
  const splitAll = (rs: Raw[]): Raw[] => rs.flatMap(r => {
    let out: Raw[] = [{p: r.p, vals: {}}]
    for (const x of state) {
      const v = r.vals[x]!
      if (!isSub(v) || taken.has(x)) { out = out.map(o => ({p: o.p, vals: {...o.vals, [x]: v}})); continue }
      const d = diff(v)
      out = out.flatMap(o => [...row(o.p, times(d, -1)).map(p => ({p, vals: {...o.vals, [x]: {lin: d}}})), ...row(o.p, plus(d, konst(1))).map(p => ({p, vals: {...o.vals, [x]: {lin: {}}}}))])
    }
    if (out.length > cap) throw new Refused('too many paths')
    return out
  })
  raws = splitAll(raws).flatMap(r => {
    const pins = {...r.p.pins}
    for (const x of state) { const v = r.vals[x]!; if (!isSub(v)) { const c = pinned(v.lin, r.p.pins); if (!vars(c).length) pins[prime(x)] = c['1'] ?? 0 } }
    return assert(renameC(l.while, new Set(state), prime), {rows: r.p.rows, pins}, true, n).map(p => ({p, vals: r.vals}))
  })
  if (raws.length > cap) throw new Refused('too many paths')
  // Which naturals every form reads only as a difference: each name's coefficients over the forms, a pair's opposite.
  // A candidate pair that fails it has its differences split, and the forms are read again.
  let vec = new Map<string, string>()
  for (;;) {
    const forms: Lin[] = raws.flatMap(r => [...r.p.rows, ...state.map(x => { const v = r.vals[x]!; return pinned(isSub(v) ? diff(v) : v.lin, r.p.pins) })])
    const lists = new Map<string, string[]>()
    for (const [i, f] of forms.entries()) for (const x of vars(f)) { const list = lists.get(x) ?? []; list.push(`${i}:${f[x]}`); lists.set(x, list) }
    vec = new Map([...lists].map(([x, list]) => [x, list.join(',')]))
    const neg = (x: string) => (lists.get(x) ?? []).map(s => { const [i, c] = s.split(':'); return `${i}:${-Number(c)}` }).join(',')
    const bad = [...pairs].filter(([x, y]) => (vec.get(y) ?? '') !== neg(x) || (vec.get(prime(y)) ?? '') !== neg(prime(x)))
    if (!bad.length) { vec = new Map([...vec, ...[...lists.keys()].map(x => [`-${x}`, neg(x)] as [string, string])]); break }
    for (const [x, y] of bad) { pairs.delete(x); taken.delete(x); taken.delete(y) }
    raws = splitAll(raws)
  }
  // The params' and the inputs' integers: two names with opposite coefficients in every form, neither the state's.
  const ints = new Map<string, [string, string]>([...pairs].map(([x, y]) => [x, [x, y]]))
  const stateNames = new Set([...state, ...state.map(prime)])
  const others = [...vec.keys()].filter(x => !x.startsWith('-') && !stateNames.has(x)).sort()
  for (const x of others) {
    if (taken.has(x)) continue
    const y = others.find(z => z !== x && !taken.has(z) && vec.get(z) === vec.get(`-${x}`))
    if (y) { ints.set(x, [x, y]); taken.add(x); taken.add(y) }
  }
  const partOf = new Map<string, [string, number]>()
  for (const [name, [a, b]] of ints) {
    partOf.set(a, [name, 1]); partOf.set(b, [name, -1])
    if (stateNames.has(a)) { partOf.set(prime(a), [prime(name), 1]); partOf.set(prime(b), [prime(name), -1]) }
  }
  // a form over the naturals as one over the integers (each read once, at its first part)
  const conv = (f: Lin): Lin => {
    const o: Lin = {}
    for (const x in f) { const q = partOf.get(x); if (!q) o[x] = f[x]!; else if (q[1] > 0) o[q[0]] = f[x]! }
    return o
  }
  const seconds = new Set([...ints.values()].map(q => q[1]))
  const stateVars = state.filter(x => !seconds.has(x))
  const paths: Path[] = []
  for (const r of raws) {
    const post: Record<string, Lin> = {}, val = (x: string): Lin => { const v = r.vals[x]!; return pinned(isSub(v) ? diff(v) : v.lin, r.p.pins) }
    for (const x of stateVars) post[x] = conv(ints.has(x) ? (isSub(r.vals[x]!) ? val(x) : plus(val(x), val(ints.get(x)![1]), -1)) : val(x))
    // the primed names in the rows read through the values after the turn
    const through = (f: Lin): Lin => {
      let o: Lin = {}
      for (const x in f) o = x.endsWith('′') && stateVars.includes(x.slice(0, -1)) ? plus(o, times(post[x.slice(0, -1)]!, f[x]!)) : plus(o, {[x]: f[x]!})
      return o
    }
    paths.push({rows: r.p.rows.map(f => through(conv(f))), pins: r.p.pins, post})
  }
  const readOf = (p: Path) => [...p.rows.flatMap(vars), ...Object.values(p.post).flatMap(vars)]
  const nats = [...new Set([...paths.flatMap(readOf), ...stateVars])].filter(x => !ints.has(x)).sort()
  // the location: a state natural every path pins, its value after the turn a constant
  const loc = stateVars.find(x => !ints.has(x) && paths.length > 0 && paths.every(p => x in p.pins && !vars(p.post[x]!).length))
  const kept: Path[] = [], from: number[] = [], to: number[] = []
  for (const p of paths) {
    // a path no integer point satisfies is dropped
    const rows = [...p.rows, ...nats.filter(x => p.rows.some(f => x in f)).map((x): Lin => ({[x]: -1}))]
    if (p.rows.length && solve(rows.map(lin => ({lin, label: ''})), 4000).kind === 'refuted') continue
    if (loc) { from.push(p.pins[loc]!); to.push(p.post[loc]!['1'] ?? 0); delete p.post[loc] }
    kept.push(p)
  }
  const read = new Set(kept.flatMap(readOf))
  const nameOf = (x: string) => partOf.get(x)?.[0] ?? x
  return {paths: kept, ints, nats: nats.filter(x => x !== loc), state: stateVars.filter(x => x !== loc), params: [...new Set(l.params.map(nameOf))].filter(x => read.has(x)).sort(),
    ...(loc ? {loc} : {}), from, to, exact: ![...read].some(x => x.startsWith('π('))}
}
const renameE = (e: E, names: Set<string>, f: (x: string) => string): E => {
  switch (e.op) {
    case 'var': return names.has(e.name) ? {op: 'var', name: f(e.name)} : e
    case 'const': return e
    case 'add': case 'sub': case 'min': case 'max': case 'prod': return {...e, a: renameE(e.a, names, f), b: renameE(e.b, names, f)}
    case 'mul': return {...e, a: renameE(e.a, names, f)}
    case 'if': return {op: 'if', c: renameC(e.c, names, f), then: renameE(e.then, names, f), else: renameE(e.else, names, f)}
    case 'get': return {...e, key: renameE(e.key, names, f)}
  }
}
const renameC = (c: C, names: Set<string>, f: (x: string) => string): C => {
  switch (c.op) {
    case '<': case '<=': case '=': return {op: c.op, a: renameE(c.a, names, f), b: renameE(c.b, names, f)}
    case 'and': case 'or': return {op: c.op, xs: c.xs.map(x => renameC(x, names, f))}
    case 'not': return {op: 'not', x: renameC(c.x, names, f)}
    case 'flag': case 'all': return c
  }
}

// --- a path's generators --------------------------------------------------------------------------------------------
//
// A path's points, over the rationals, are its vertices plus the cone of its rays and lines (Minkowski–Weyl): a linear
// condition holds at every point if it holds at each vertex and its linear part doesn't fall along each ray (nor move
// along a line). Found by double description over the homogenized cone {(x, t): rows ≤ 0, t ≥ 0} (Motzkin), in
// integers: each generator's entries divided by their common divisor, a vertex (x, t) with t > 0 standing for x / t.
// The rows are integer rows (x < y is x + 1 ≤ y), so a condition proven over a path's rational points holds of its
// integer ones; past `cap` generators, entries past 2^53, or `until`, there are none.
export type Generators = {names: string[], vertices: number[][], rays: number[][], lines: number[][]} // each entry over names, then t
const bgcd = (a: bigint, b: bigint): bigint => { if (a < 0n) a = -a; if (b < 0n) b = -b; while (b) [a, b] = [b, a % b]; return a }
const norm = (x: bigint[]): bigint[] => { const g = x.reduce(bgcd, 0n); return g > 1n ? x.map(y => y / g) : x }
const dot = (a: bigint[], b: bigint[]) => a.reduce((s, x, i) => s + x * b[i]!, 0n)
export function generators(rows: Lin[], names: string[], nats: string[] = [], cap = 600, until = Infinity): Generators | undefined {
  const n = names.length, at = new Map(names.map((x, i) => [x, i]))
  const hs: bigint[][] = [...rows.map(r => { const h = Array.from({length: n + 1}, () => 0n); for (const [x, c] of Object.entries(r)) { if (x === '1') h[n] = BigInt(c); else h[at.get(x)!] = BigInt(c) } return h }),
    ...nats.filter(x => at.has(x)).map(x => { const h = Array.from({length: n + 1}, () => 0n); h[at.get(x)!] = -1n; return h }),
    Array.from({length: n + 1}, (_, i) => (i === n ? -1n : 0n))]
  let lines: bigint[][] = Array.from({length: n + 1}, (_, i) => Array.from({length: n + 1}, (_, j) => (i === j ? 1n : 0n)))
  let rays: {v: bigint[], zero: Set<number>}[] = []
  for (const [hi, h] of hs.entries()) {
    const li = lines.findIndex(l => dot(h, l) !== 0n)
    if (li >= 0) {
      let l = lines[li]!, s = dot(h, l)
      if (s > 0n) { l = l.map(x => -x); s = -s }
      lines = lines.filter((_, i) => i !== li).map(m => { const hm = dot(h, m); return hm === 0n ? m : norm(m.map((x, i) => s * x - hm * l[i]!)) })
      rays = rays.map(r => { const hr = dot(h, r.v); return hr === 0n ? {v: r.v, zero: new Set([...r.zero, hi])} : {v: norm(r.v.map((x, i) => -s * x + hr * l[i]!)), zero: new Set([...r.zero, hi])} })
      rays.push({v: norm(l), zero: new Set([...hs.keys()].filter(j => j < hi && dot(hs[j]!, l) === 0n))})
      continue
    }
    const val = rays.map(r => dot(h, r.v))
    const pos = rays.filter((_, i) => val[i]! > 0n), neg = rays.filter((_, i) => val[i]! < 0n), zero = rays.filter((_, i) => val[i]! === 0n)
    const next = [...zero.map(r => ({v: r.v, zero: new Set([...r.zero, hi])})), ...neg]
    const vp = new Map(pos.map(r => [r, dot(h, r.v)])), vn = new Map(neg.map(r => [r, dot(h, r.v)]))
    // (counted as work: a counted search's clock runs while the generators are made)
    work.n += 1 + ((rays.length + pos.length * neg.length) * (n + 1) >> 4)
    if (clock() > until) return undefined
    for (const p of pos) for (const q of neg) {
      // adjacent: no other ray is zero wherever both are
      const common = [...p.zero].filter(j => q.zero.has(j))
      if (rays.some(r => r !== p && r !== q && common.every(j => r.zero.has(j)))) continue
      const a = vp.get(p)!, b = -vn.get(q)!
      next.push({v: norm(p.v.map((x, i) => b * x + a * q.v[i]!)), zero: new Set([...common, hi])})
      if (next.length > cap) return undefined
    }
    rays = next
    if (rays.length > cap) return undefined
  }
  const safe = (x: bigint[]) => x.every(y => y <= BigInt(Number.MAX_SAFE_INTEGER) && -y <= BigInt(Number.MAX_SAFE_INTEGER))
  if (![...rays.map(r => r.v), ...lines].every(safe)) return undefined
  const num = (x: bigint[]) => x.map(Number)
  return {names, vertices: rays.filter(r => r.v[n]! > 0n).map(r => num(r.v)), rays: rays.filter(r => r.v[n]! === 0n).map(r => num(r.v)), lines: lines.map(num)}
}

// --- invariants: Houdini over the relation --------------------------------------------------------------------------
//
// Candidate atoms per location (each lin ≤ 0 over the relation's names), those that fail at a start dropped by the
// caller, then each path's points where its location's candidates hold (its generators) read through the turn: a
// candidate at the path's target that some point after the turn breaks is dropped, until none is. What is left is
// inductive over the relation (so over the loop, where the relation is exact); the kernel proves it again as laws.
export function houdini(rel: Relation, cands: Lin[][], locOf: (i: number) => [number, number], until: number): Lin[][] | undefined {
  const H = cands.map(cs => [...new Map(cs.map(c => [canon(c), c])).values()])
  // A path's rows with the candidates at its start: of the bounds on one name, only the tightest each way (the others
  // add no vertex).
  const tight = (cs: Lin[]): Lin[] => {
    const best = new Map<string, Lin>(), rest: Lin[] = []
    for (const c of cs) {
      const xs = vars(c)
      if (xs.length !== 1) { rest.push(c); continue }
      const x = xs[0]!, s = Math.sign(c[x]!), key = `${x}${s}`, b = (c['1'] ?? 0) / Math.abs(c[x]!), was = best.get(key)
      if (!was || b > (was['1'] ?? 0) / Math.abs(was[x]!)) best.set(key, c)
    }
    return [...best.values(), ...rest]
  }
  for (let round = 0, changed = true; changed && round < 50; round++) {
    changed = false
    for (const [i, p] of rel.paths.entries()) {
      if (clock() > until) return undefined
      const [a, b] = locOf(i)
      if (!H[b]!.length) continue
      const rows = [...p.rows, ...tight(H[a]!)]
      // (the names the candidates at the target read too: one the path reads nowhere is free there, a line)
      const ns = [...new Set([...rows.flatMap(vars), ...Object.values(p.post).flatMap(vars), ...H[b]!.flatMap(vars)])].sort()
      const g = generators(rows, ns, rel.nats, 600, until)
      if (!g) {
        // past the generators' cap: each candidate after the turn refuted by the integer solver, or dropped
        const nat = rel.nats.filter(x => ns.includes(x)).map((x): Lin => ({[x]: -1}))
        const through = (c: Lin): Lin => { let o: Lin = {}; for (const [y, k] of Object.entries(c)) o = plus(o, y !== '1' && p.post[y] ? times(p.post[y]!, k) : {[y]: k}); return o }
        const keep = H[b]!.filter(c => clock() < until && solve([...rows, ...nat, plus(konst(1), through(c), -1)].map(lin => ({lin, label: ''})), 4000).kind === 'refuted')
        if (keep.length < H[b]!.length) { H[b] = keep; changed = true }
        continue
      }
      if (!g.vertices.length) continue // no point: the path never runs where the candidates hold
      const at = (x: number[], t: number, c: Lin): number => {
        // c after the turn: each name through the path's value
        let s = t * (c['1'] ?? 0)
        for (const [y, k] of Object.entries(c)) {
          if (y === '1') continue
          const f = p.post[y]
          if (!f) { const j = ns.indexOf(y); s += k * (j < 0 ? 0 : x[j]!); continue }
          for (const [u, d] of Object.entries(f)) { const j = ns.indexOf(u); s += k * d * (u === '1' ? t : j < 0 ? 0 : x[j]!) }
        }
        return s
      }
      const keep = H[b]!.filter(c => g.vertices.every(x => at(x, x[ns.length]!, c) <= 0) && g.rays.every(x => at(x, 0, c) <= 0) && g.lines.every(x => at(x, 0, c) === 0))
      if (keep.length < H[b]!.length) { H[b] = keep; changed = true }
    }
  }
  return H
}
