// Untrusted: a fast decision of EPR-shaped goals (research/protocols/epr/DESIGN.md). The hypotheses read as a
// propositional abstraction: a composed key (a·N² + b·N + c) the tuple of its parts, compared by the parts' order and
// equality, never by arithmetic; a few-valued cell a finite variable; an ordered value (an epoch) a term of a total order;
// anything else an opaque atom. Every clause beside the hypotheses holds in every model of the goal, and finite values are
// capped above every constant they meet, so unsat here is unsat there. It answers unsat with its core (the hypotheses
// its refutation read: prove.ts proves the goal over those and widens the tree to the whole, which kernel.ts checks), or
// a model read back as the kernel's witness and judged on every hypothesis, or nothing.
import {type C, type E, type Machine, evalC} from '../core/machine.ts'
import {type Goal, canon, linear} from './kernel.ts'
import {type Constraint, type Lin, konst, plus, solve, times, v as tv} from '../core/solver.ts'
import {Simplex} from './simplex.ts'

// (a term's text, once per object: the decision asks it of the same terms many times)
const textsOf = new WeakMap<object, string>()
const textOfE = (o: object): string => { let s = textsOf.get(o); if (s === undefined) textsOf.set(o, (s = JSON.stringify(o))); return s }
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
// A model as a structure, for a caller that blocks it as a diagram (UPDR's): the goal's elements are the values of its
// parts and ordered terms (an epoch a cell holds), in their order, each an index 0 .. elements − 1; each part (a key's name, a function's read at one) and ordered scalar (a ring's size) is an element; each
// scalar a value; each map's cells the goal reads, at tuples of elements, with their values (a value of an ordered cell
// that is an element's, an epoch a node holds, as that element, else the number); each function's table, element to
// element. Two models equal up to the order's renaming give the same diagram.
export type Diagram = {elements: number, parts: Record<string, number>, scalars: Record<string, number>, cells: Record<string, {at: number[], value: number}[]>, fns: Record<string, [number, number][]>}
export type Decision = {sat: false, core: number[]} | {sat: true, witness: Record<string, number>, diagram: Diagram} | {unknown: string}

// `late`: true past the caller's end, checked between the steps and every 256 conflicts; then unknown.
export function decide(goal: Goal, patterns: Patterns, opts: {conflicts?: number, exact?: boolean, late?: () => boolean} = {}): Decision {
  fnMaps = new Set(Object.entries(patterns).filter(([, c]) => c.length === 1 && c[0] === 0).map(([f]) => f))
  // (a model whose order leaves no room between two near constants: again with the constants between them, below)
  // (a model the read-back breaks: once more without the other goals' theory lemmas, whose history chose that model)
  try {
    const d = decide0(goal, patterns, opts), d2 = 'unknown' in d && d.unknown === noRoom ? decide0(goal, patterns, {...opts, fill: true}) : d
    return 'unknown' in d2 && d2.unknown.startsWith(breaks) && lemmaCache.size ? decide0(goal, patterns, {...opts, fresh: true}) : d2
  } catch (e) { if (e === pastEnd) return {unknown: 'past the deadline'}; throw e } finally { fnMaps = new Set() }
}
// (thrown by `late` checked every 4,096 clauses and hypotheses read: a goal's clauses are quadratic in its terms)
const pastEnd = new Error('past the deadline')
// The theory's lemmas, by their atoms' names: each is arithmetic over the terms those names read (a part's value, a cell's
// at its key), so it holds in every goal that has those atoms, a round's other goals over the same set above all; each
// goal starts with those it has. At most 20,000, then begun again.
const lemmaCache = new Map<string, [string, boolean][]>()
const noRoom = 'no values for the model\'s order', breaks = 'the abstraction\'s model breaks'
function decide0(goal: Goal, patterns: Patterns, opts: {conflicts?: number, exact?: boolean, late?: () => boolean, fill?: boolean, fresh?: boolean}): Decision {
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
  let ticks = 0
  const tick = () => { if ((++ticks & 4095) === 0 && opts.late?.()) throw pastEnd }
  const fits = (map: string, key: E) => { const t = tupleOf(key), p = patterns[map]; return t && p && sameCoefs(t.coefs, p) ? t : undefined }
  // --- names: a part is a name some read's key or a key equality reads; the rest are scalars
  // (each function part once: its reads are many, its congruence pairs of parts)
  const parts = new Set<string>(), fnParts: {f: string, n: string, a: string}[] = [], fnSeen = new Set<string>()
  // (the goal's reads and comparisons, gathered in one walk, each shared node once: the walks below read these lists)
  const reads: Extract<E, {op: 'get'}>[] = [], comps: Extract<C, {a: E}>[] = [], seen = new WeakSet<object>()
  const gather = (o: unknown): void => {
    if (!o || typeof o !== 'object' || seen.has(o)) return
    seen.add(o); tick()
    const x = o as {op?: string, a?: unknown}
    if (x.op === 'get') reads.push(o as Extract<E, {op: 'get'}>)
    else if ((x.op === '<' || x.op === '<=' || x.op === '=') && x.a) comps.push(o as Extract<C, {a: E}>)
    for (const v of Object.values(o)) gather(v)
  }
  hyps.forEach(gather)
  for (const x of reads) {
    if (fnMaps.has(x.map)) { const n = partName(x), a = partName(x.key); if (n && a) { if (!fnSeen.has(n)) (fnSeen.add(n), fnParts.push({f: x.map, n, a})); parts.add(n); parts.add(a) } }
    else fits(x.map, x.key)?.parts.forEach(p => parts.add(p))
  }
  // (and the names of a key equality between tuples of one shape: of several parts, or of one where the other side is a part)
  const eqs = comps.flatMap(c => { if (c.op !== '=') return []; const ta = tupleOf(c.a), tb = tupleOf(c.b); return ta && tb && sameCoefs(ta.coefs, tb.coefs) ? [{ta, tb}] : [] })
  for (let grew = true; grew;) {
    grew = false
    for (const {ta, tb} of eqs) if (ta.parts.length > 1 || [...ta.parts, ...tb.parts].some(x => parts.has(x))) for (const x of [...ta.parts, ...tb.parts]) if (!parts.has(x)) { parts.add(x); grew = true }
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
      const id = textOfE(c.a), b = c.b.value - (c.op === '<' ? 1 : 0), had = bounded.get(id)
      if (b >= 0 && (!had || b < had.b)) bounded.set(id, {b, h})
    }
  }
  hyps.forEach((c, h) => unitWalk(c, h))
  // (one compared with a key part, or beside an ordered term, is of that sort: ordered, below, and not exact)
  const exactOf = (e: E): {b: number, h: number} | undefined => (e.op === 'get' ? (!ordMaps.has(e.map) ? bounded.get(textOfE(e)) : undefined) : e.op === 'var' && !parts.has(e.name) && !ordScalars.has(e.name) ? bounded.get(textOfE(e)) : undefined)
  // --- caps: a finite term's values are 0 .. cap, cap above every constant a comparison it is in has (so a larger value
  // decides every comparison the cap does: the terms are naturals with coefficients of one sign)
  const caps = new Map<string, number>()
  const termKey = (e: E): string | undefined => (e.op === 'var' && !parts.has(e.name) ? `s:${e.name}` : e.op === 'get' ? `c:${e.map}` : undefined)
  for (const c of comps) {
    {
      const consts: number[] = [], keys: string[] = []
      let ex = 0
      const w = (e: E, k: number) => { if (e.op === 'const') consts.push(Math.abs(e.value)); else if (e.op === 'add') (w(e.a, k), w(e.b, k)); else if (e.op === 'mul') w(e.a, k * e.k); else if (e.op === 'if') (w(e.then, k), w(e.else, k)); else { const x = exactOf(e); if (x) ex += Math.abs(k) * x.b; const t = termKey(e); if (t) keys.push(t) } }
      w(c.a, 1); w(c.b, 1)
      // (and past what the exact terms beside can add: x <= Voted[k] with x at its cap is false at every larger x)
      const top = Math.max(1, ...consts) + ex + 1
      for (const k of keys) caps.set(k, Math.max(caps.get(k) ?? 1, top))
    }
  }
  // ordered: a map's cells, or a scalar, compared with another non-constant term (an epoch with a node's epoch: Ivy's
  // total order, `le`), not only with constants (a yes/no, a choice, which stay finite)
  const leaves = (e: E, k: number, out: [E, number][]): void => {
    if (e.op === 'add') { leaves(e.a, k, out); leaves(e.b, k, out) } else if (e.op === 'mul') leaves(e.a, k * e.k, out)
    else if (e.op === 'if') { leaves(e.then, k, out); leaves(e.else, k, out) } else if (e.op !== 'const') out.push([e, k])
  }
  const ofParts = (e: E) => tupleOf(e)?.parts.every(x => parts.has(x))
  const ordComps = comps.filter(c => !(ofParts(c.a) && ofParts(c.b))).map(c => { const ts: [E, number][] = []; leaves(c.a, 1, ts); leaves(c.b, -1, ts); return ts })
  const ordWalk = (ts: [E, number][]): void => {
    {
      const hasPart = ts.some(([e]) => (n => n !== undefined && parts.has(n))(partName(e)))
      const nonPart = ts.filter(([e]) => (hasPart || !exactOf(e)) && ((e.op === 'get' && !fnMaps.has(e.map)) || (e.op === 'var' && !parts.has(e.name))))
      // (and every term beside an ordered one in a comparison: one value of the sort, an if-then-else's branches)
      const tn = ts.filter(([e]) => hasPart || !exactOf(e)), mixed = nonPart.length && tn.length > 1 && tn.some(t => t[1] > 0) && tn.some(t => t[1] < 0)
      const beside = nonPart.some(([e]) => (e.op === 'get' && ordMaps.has(e.map)) || (e.op === 'var' && ordScalars.has(e.name)))
      if (mixed || beside) for (const [e] of nonPart) { if (e.op === 'get' && !ordMaps.has(e.map)) { ordMaps.add(e.map); grew = true } else if (e.op === 'var' && !ordScalars.has(e.name)) { ordScalars.add(e.name); grew = true } }
    }
  }
  let grew = true
  while (grew) { grew = false; ordComps.forEach(ts => (tick(), ordWalk(ts))) }

  // --- atoms
  const ids = new Map<string, number>(), names: string[] = ['']
  const atom = (key: string): F => { let v = ids.get(key); if (v === undefined) { v = names.length; ids.set(key, v); names.push(key) } return {k: 'v', v} }
  // (the order's and equality's atoms by their two terms, without building their text again: the axioms ask them
  // quadratically and the transitivity cubically)
  const pairAtoms = (tag: string) => { const byA = new Map<string, Map<string, F>>(); return (a: string, b: string): F => { let in2 = byA.get(a); if (!in2) byA.set(a, (in2 = new Map())); let f = in2.get(b); if (!f) in2.set(b, (f = atom(`${tag} ${a} ${b}`))); return f } }
  const eqAt = pairAtoms('eq'), leAt = pairAtoms('le')
  const eq = (x: string, y: string): F => (x === y ? T : x < y ? eqAt(x, y) : eqAt(y, x))
  // the ordered terms (every part among them), `le a b` a ≤ b
  const ords = new Set<string>(['k:0', ...[...parts].map(x => `p:${x}`)])
  const le = (a: string, b: string): F => (a === b ? T : leAt(a, b))
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
      const id = `c:${e.map}#${textOfE(e.key)}`
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
    // (a function read at a key of the wrong sort, idn(64·m + n): a term of the order too, its value the read-back's)
    if (e.op === 'get' && fnMaps.has(e.map)) { const id = `c:${e.map}#${textOfE(e.key)}`; ords.add(id); return id }
    if (e.op === 'get' && ordMaps.has(e.map) && !(e as {args?: unknown}).args) {
      const t = fits(e.map, e.key)
      const id = t ? `c:${e.map}(${t.parts.join(',')})` : `c:${e.map}#${textOfE(e.key)}`
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
  const foreign = new Set<number>(), opaques = new Map<number, C>()
  const opaque = (c: C): F => {
    const a = atom(`op ${textOfE(c)}`) as {k: 'v', v: number}
    opaques.set(a.v, c)
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
  const forms = hyps.map(h => (tick(), h ? lit(h) : undefined))
  // the theory: each opaque comparison of key parts, ordered terms and composed keys (a part against 64·e + n, an
  // instance at a key of the wrong sort) as linear arithmetic over the ordered terms, which a model's order is checked
  // against below (each a term of the order, so its axioms hold)
  const tlin = (e: E): Lin | undefined => {
    if (e.op === 'const') return konst(e.value)
    if (e.op === 'add') { const a = tlin(e.a), b = tlin(e.b); return a && b ? plus(a, b) : undefined }
    if (e.op === 'mul') { const a = tlin(e.a); return a && times(a, e.k) }
    const t = ordOf(e)
    return t === undefined ? undefined : t.startsWith('k:') ? konst(Number(t.slice(2))) : tv(t)
  }
  const theory = [...opaques].filter(([x]) => !foreign.has(x)).flatMap(([x, c]) => {
    if (c.op !== '<' && c.op !== '<=' && c.op !== '=') return []
    const a = tlin(c.a), b = tlin(c.b)
    return a && b ? [{x, op: c.op, d: plus(a, times(b, -1))}] : []
  })
  // (an order over many terms is a cubic number of transitivity clauses: past 64 terms they are added lazily, those a
  // model breaks, below; past 512, the totality's pairs alone are too many, and the goal keeps the usual path)
  // (`fill`: the constants between two near ones too, so that discreteness counts the room between them: k:0 < x < y < k:2
  // has none, which the read-back meets)
  if (opts.fill) { const cs = [...ords].filter(x => x.startsWith('k:')).map(x => Number(x.slice(2))).sort((a, b) => a - b)
    for (let i = 0; i + 1 < cs.length; i++) if (cs[i + 1]! - cs[i]! <= 4) for (let c = cs[i]! + 1; c < cs[i + 1]!; c++) ords.add(`k:${c}`) }
  if (ords.size > 512) return {unknown: `${ords.size} ordered terms`}
  const lazy = ords.size > 64

  // --- clauses (literals: +v / −v), each with the hypotheses it stands for
  const clauses: {lits: number[], from: Origin}[] = []
  const add = (lits: number[], from: Origin) => { tick(); const s = new Set(lits); for (const l of s) if (s.has(-l)) return; clauses.push({lits: [...s], from}) }
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
  if (theory.length && !opts.fresh) for (const l of lemmaCache.values()) { const xs = l.map(([k, b]) => { const x = ids.get(k); return x === undefined ? undefined : b ? x : -x }); if (xs.every((x): x is number => x !== undefined)) add(xs, -1) }

  // EPR-shaped: no comparison the abstraction can't read (a counter's arithmetic, a sum, a product) in any hypothesis
  if (opts.exact) { const tied = new Set([...keyEqs, ...intervals].map(k => (k.p as {v: number}).v)); const loose = [...foreign].filter(i => !tied.has(i)).length; if (loose) return {unknown: `${loose} comparisons outside the EPR shape`} }
  // --- the search
  // (a finite variable at 0 first: models with the least values, which break the fewest laws at keys nothing names)
  const first = new Set([...fins.values()].map(f => v(finAt(f, 0))!))
  if (opts.late?.()) return {unknown: 'past the deadline'}
  // (lazily: the transitivity a model breaks, added and the search again, at most 4,096 a round and 16 rounds; as each
  // holds in every model, a refutation stays one)
  // (one solver, the lemmas added to it: the search goes on from what it learned)
  // (the order's atoms and the theory's comparisons keep the phase of the last model: a lemma then moves the next model
  // as little as it must, not to the search's first choices again)
  const kept = new Set([...ids].filter(([k]) => k.startsWith('le ')).map(([, x]) => x).concat(theory.map(t => t.x)))
  let solver = cdclSolver(clauses, first, kept)
  const lemma = (lits: number[]) => { const n0 = clauses.length; add(lits, -1); if (clauses.length > n0 && !solver.add(clauses.at(-1)!)) solver = cdclSolver(clauses, first, kept) }
  const search = (): ReturnType<typeof cdcl> | string => {
    let o = solver.solve(opts.conflicts ?? 200_000, opts.late)
    for (let round = 0; lazy && o?.sat; round++) {
      const m = o.model, os = [...ords], at = (a: string, b: string) => a === b || m[v(le(a, b))!] === true, broken: number[][] = []
      for (const a of os) for (const b of os) if (a !== b && at(a, b)) for (const c of os) if (c !== a && c !== b && at(b, c) && !at(a, c) && broken.length < 4096) broken.push([-v(le(a, b))!, -v(le(b, c))!, v(le(a, c))!])
      if (!broken.length) break
      if (round === 16 || opts.late?.()) return 'the order\'s transitivity, lazily, did not settle'
      for (const c of broken) lemma(c)
      o = solver.solve(opts.conflicts ?? 200_000, opts.late)
    }
    return o
  }
  // (the model's order, its groups of equal terms in order: the read-back's and the theory's)
  const groupsOf = (m: boolean[]): string[][] => {
    const leq = (a: string, b: string) => a === b || m[v(le(a, b))!] === true
    const os = [...ords].sort((a, b) => (leq(a, b) && !leq(b, a) ? -1 : leq(b, a) && !leq(a, b) ? 1 : 0)), groups: string[][] = []
    for (let i = 0; i < os.length;) { let j = i; while (j < os.length && leq(os[j]!, os[i]!) && leq(os[i]!, os[j]!)) j++; groups.push(os.slice(i, j)); i = j }
    return groups
  }
  // The theory's check of a model: its order (each group's terms equal, each group below the next, a successor the next
  // value), every ordered term a natural, each theory comparison as the model has it, solved over the integers. Sat: the
  // values, the read-back's; refuted: the model's literals its refutation reads, whose negation holds in every model (a
  // theory lemma, DPLL(T)'s), added and the search again.
  // (first over the theory's own terms, each pair as the model orders it, so that a lemma names them alone; then every
  // term, the model's order as its groups, for the values)
  const theoryTerms = [...new Set(theory.flatMap(t => Object.keys(t.d).filter(x => x !== '1')))]
  // (each comparison's literals: its own and its terms' order, among them and with the constants)
  const feasible: Set<string>[] = [], locals: number[][] = []
  const localOf = (ti: number, t: (typeof theory)[number], ks: string[]): number[] => {
    if (locals[ti]) return locals[ti]!
    const xs = Object.keys(t.d).filter(x => x !== '1'), out = [t.x]
    for (let i2 = 0; i2 < xs.length; i2++) for (const b of [...xs.slice(i2 + 1), ...ks]) for (const [p, q] of [[xs[i2]!, b], [b, xs[i2]!]]) { const x = v(le(p!, q!)); if (x !== undefined) out.push(x) }
    return (locals[ti] = out)
  }
  const jointLp = new Simplex(true)
  // (each pair's order atoms and its four rows, a ≤ b, b < a, b ≤ a, a < b, made once: the same rows every round, which
  // the simplex knows by their objects)
  const pairs0 = new Map<string, {ab: number, ba: number, rows: [Lin, Lin, Lin, Lin]}>()
  const pairOf = (a: string, b: string) => {
    const key = `${a}|${b}`
    let p = pairs0.get(key)
    if (!p) {
      const T = (t: string): Lin => (t.startsWith('k:') ? konst(Number(t.slice(2))) : tv(t))
      p = {ab: v(le(a, b))!, ba: v(le(b, a))!, rows: [plus(T(a), times(T(b), -1)), plus(plus(T(b), konst(1)), times(T(a), -1)), plus(T(b), times(T(a), -1)), plus(plus(T(a), konst(1)), times(T(b), -1))]}
      pairs0.set(key, p)
    }
    return p
  }
  type Checked = {val: Map<string, number>, exact?: () => Checked | {lemmas: number[][]} | undefined}
  const theoryCheck = (m: boolean[]): Checked | {lemmas: number[][]} | undefined => {
    const T = (t: string): Lin => (t.startsWith('k:') ? konst(Number(t.slice(2))) : tv(t))
    const theoryRows = (row: (lin: Lin, ls: number[]) => void) => {
      for (const t of theory) {
        const holds = m[t.x] === true
        if (t.op === '=') { if (holds) { row(t.d, [t.x]); row(times(t.d, -1), [t.x]) } continue }
        // a − b < 0 is a − b + 1 ≤ 0; its negation b − a ≤ 0; a − b ≤ 0's negation b − a + 1 ≤ 0
        if (holds) row(t.op === '<' ? plus(t.d, konst(1)) : t.d, [t.x])
        else row(t.op === '<' ? times(t.d, -1) : plus(times(t.d, -1), konst(1)), [-t.x])
      }
    }
    const lemmaOf = (r: ReturnType<typeof solve>, lits: number[][]): number[] | undefined => {
      if (r.kind !== 'refuted') return undefined
      const used = new Set<number>()
      for (const st of r.steps) if (st.kind === 'input') for (const l of lits[st.index]!) used.add(l)
      return used.size ? [...used].map(l => -l) : undefined
    }
    const pairRows = (row: (lin: Lin, ls: number[]) => void, a: string, b: string) => {
      const p = pairOf(a, b)
      if (m[p.ab] === true) row(p.rows[0], [p.ab]); else row(p.rows[1], [-p.ab])
      if (m[p.ba] === true) row(p.rows[2], [p.ba]); else row(p.rows[3], [-p.ba])
    }
    // (each comparison alone first, with its terms' order and the constants: a lemma of a few literals for each the
    // model breaks, all of them in one round; one the model reads as an earlier model did, feasible then, not again)
    {
      const ks = [...ords].filter(t => t.startsWith('k:')), lemmas: number[][] = []
      for (const [ti, t] of theory.entries()) {
        const local = localOf(ti, t, ks), seen = (feasible[ti] ??= new Set()), key = local.map(l => (m[l] === true ? '1' : '0')).join('')
        if (seen.has(key)) continue
        const rows: Constraint[] = [], lits: number[][] = [], row = (lin: Lin, ls: number[]) => { rows.push({lin, label: ''}); lits.push(ls) }
        const xs = Object.keys(t.d).filter(x => x !== '1')
        for (const x of xs) row(times(tv(x), -1), [])
        for (let i2 = 0; i2 < xs.length; i2++) { for (let j = i2 + 1; j < xs.length; j++) pairRows(row, xs[i2]!, xs[j]!); for (const k2 of ks) pairRows(row, xs[i2]!, k2) }
        const holds = m[t.x] === true
        if (t.op === '=') { if (holds) { row(t.d, [t.x]); row(times(t.d, -1), [t.x]) } else continue }
        else if (holds) row(t.op === '<' ? plus(t.d, konst(1)) : t.d, [t.x])
        else row(t.op === '<' ? times(t.d, -1) : plus(times(t.d, -1), konst(1)), [-t.x])
        const l = lemmaOf(solve(rows), lits)
        if (l) lemmas.push(l)
        else seen.add(key)
      }
      if (lemmas.length) return {lemmas}
    }
    {
      const rows: Constraint[] = [], lits: number[][] = [], row = (lin: Lin, ls: number[]) => { rows.push({lin, label: ''}); lits.push(ls) }
      // (the pairs of terms one comparison reads, and each with the constants)
      const ks = [...ords].filter(t => t.startsWith('k:')), pairs = new Map<string, [string, string]>()
      for (const t of theory) { const xs = Object.keys(t.d).filter(x => x !== '1'); for (const a of xs) for (const b of [...xs, ...ks]) if (a !== b) pairs.set(a < b ? `${a}|${b}` : `${b}|${a}`, a < b ? [a, b] : [b, a]) }
      // (with few ordered terms, every pair of them: a refutation through a term no comparison reads, a chain of the
      // order, is then a lemma of the pairs it needs, not of the whole order)
      const all = ords.size <= 48 ? [...ords] : []
      for (let i2 = 0; i2 < all.length; i2++) for (let j = i2 + 1; j < all.length; j++) { const a = all[i2]!, b = all[j]!; if (!(a.startsWith('k:') && b.startsWith('k:'))) pairs.set(a < b ? `${a}|${b}` : `${b}|${a}`, a < b ? [a, b] : [b, a]) }
      for (const t of new Set([...theoryTerms, ...all.filter(x => !x.startsWith('k:'))])) row(times(tv(t), -1), [])
      for (const [a, b] of pairs.values()) pairRows(row, a, b)
      // (and the successors the model holds among them, n1 = n + 1, both ways: the ring's next node)
      const tt = new Set([...theoryTerms, ...all])
      for (const x of succs) if (m[x.s] && (tt.has(x.lo) || tt.has(x.hi))) { row(plus(T(x.hi), times(plus(T(x.lo), konst(1)), -1)), [x.s]); row(plus(plus(T(x.lo), konst(1)), times(T(x.hi), -1)), [x.s]); for (const y of [x.lo, x.hi]) if (!tt.has(y) && !y.startsWith('k:')) row(times(tv(y), -1), []) }
      theoryRows(row)
      // (several lemmas a round: each refutation's theory rows set aside, the rest solved again, at most eight)
      // (each by the simplex first (kernel/simplex.ts, the CDCL search's, its tableau kept from round to round): its
      // conflict's rows refuted exactly (core/solver.ts), the lemma the literals that refutation reads; no answer, the
      // first time by elimination over them all, as before; feasible, or a conflict the floats misjudge, no more lemmas)
      const lemmas: number[][] = [], off = new Set<number>(), theoryLits = new Set(theory.flatMap(t => [t.x, -t.x]))
      for (let k = 0; k < 8; k++) {
        const keep = rows.map((_, i) => i).filter(i => !off.has(i)), sub = keep.map(i => rows[i]!), subLits = keep.map(i => lits[i]!)
        let r = jointLp.load(sub)
        if (r.kind === 'sat') r = jointLp.check()
        if (r.kind === 'sat') break
        const l = r.kind === 'conflict' ? lemmaOf(solve(r.rows.map(i => sub[i]!)), r.rows.map(i => subLits[i]!)) : k ? undefined : lemmaOf(solve(sub), subLits)
        if (!l) break
        lemmas.push(l)
        keep.forEach(i => { if (lits[i]!.some(x => theoryLits.has(x) && l.includes(-x))) off.add(i) })
      }
      if (lemmas.length) return {lemmas}
    }
    const rows: Constraint[] = [], lits: number[][] = [], row = (lin: Lin, ls: number[]) => { rows.push({lin, label: ''}); lits.push(ls) }
    const groups = groupsOf(m)
    for (const t of ords) if (!t.startsWith('k:')) row(times(tv(t), -1), [])
    for (const [gi, g] of groups.entries()) {
      for (const t of g.slice(1)) { row(plus(T(t), times(T(g[0]!), -1)), [v(le(t, g[0]!))!]); row(plus(T(g[0]!), times(T(t), -1)), [v(le(g[0]!, t))!]) }
      const h = groups[gi + 1]
      if (h) row(plus(plus(T(g[0]!), konst(1)), times(T(h[0]!), -1)), [-v(le(h[0]!, g[0]!))!])
    }
    for (const x of succs) if (m[x.s]) row(plus(T(x.hi), times(plus(T(x.lo), konst(1)), -1)), [x.s])
    theoryRows(row)
    // (the simplex first, as the joint check: a conflict's rows refuted exactly; its point the values where every term is
    // a natural there and every row holds exactly, with elimination's (as before) for a read-back they break; else
    // elimination over them all)
    let q = jointLp.load(rows)
    if (q.kind === 'sat') q = jointLp.check()
    if (q.kind === 'conflict') { const l = lemmaOf(solve(q.rows.map(i => rows[i]!)), q.rows.map(i => lits[i]!)); if (l) return {lemmas: [l]} }
    const exact = (): {val: Map<string, number>} | {lemmas: number[][]} | undefined => {
      const r = solve(rows)
      if (r.kind === 'sat') return {val: new Map([...ords].map(t => [t, t.startsWith('k:') ? Number(t.slice(2)) : r.witness[t] ?? 0]))}
      const l = lemmaOf(r, lits)
      return l && {lemmas: [l]}
    }
    if (q.kind === 'sat') {
      const at = (t: string) => { const j = jointLp.indexOf(t); return j === undefined ? 0 : jointLp.value(j) }
      const val = new Map([...ords].map(t => [t, t.startsWith('k:') ? Number(t.slice(2)) : Math.round(at(t))]))
      const ok = [...ords].every(t => t.startsWith('k:') || (Math.abs(at(t) - val.get(t)!) < 1e-6 && val.get(t)! >= 0))
        && rows.every(row => Object.entries(row.lin).reduce((x, [k, c]) => x + c * (k === '1' ? 1 : val.get(k) ?? 0), 0) <= 0)
      if (ok) return {val, exact}
    }
    return exact()
  }
  const outcome = (o: ReturnType<typeof search>): Decision | {model: boolean[]} => (typeof o === 'string' ? {unknown: o} : o === undefined ? {unknown: 'the conflict budget ran out, or the deadline'}
    : !o.sat ? {sat: false, core: [...o.core].filter(i => i >= 0).sort((a, b) => a - b)} : {model: o.model})
  // --- a model, read back: the ordered terms (the parts among them) by the model's order, each composed key the radix
  // sum of its parts, each cell and scalar its value; then judged on every hypothesis
  // (the read-back with the theory's values, where it checked the model; where they break a hypothesis, the order's own
  // grouping, as without one)
  const finish = (model: boolean[], theoryVal: Map<string, number> | undefined): Decision => {
    const val = (l: number) => model[l] === true
    const w: Record<string, number> = {}
    for (const f of fins.values()) {
      let x = 0
      for (let val2 = 0; val2 <= f.cap; val2++) if (val(v(finAt(f, val2))!)) x = val2
      if (f.id.startsWith('s:')) w[f.id.slice(2)] = x
    }
    // each group of equal terms the next value, a constant's group its own; odd where there is room before the next constant
    // (a key of the wrong sort, 2·64·x + y, then meets no cell 64·x' + y), and far apart past every constant (composed keys
    // of parts above every bound then don't meet)
    // (where the theory checked the model, its values)
    const ordVal = theoryVal ?? new Map<string, number>()
    if (!theoryVal) {
      const groups = groupsOf(model)
      const constOf = (g: string[]) => { const cs = [...new Set(g.filter(x => x.startsWith('k:')).map(x => Number(x.slice(2))))]; return cs.length > 1 ? NaN : cs[0] }
      // (a successor the model holds, n1 = n + 1, makes its two groups consecutive values: such a chain is one block, its
      // first group's value the next free one, or its constant's less the steps to it)
      const groupOf = new Map<string, number>(); groups.forEach((g, i) => g.forEach(t => groupOf.set(t, i)))
      const tight = new Set(succs.filter(x => val(x.s)).map(x => `${groupOf.get(x.lo)}>${groupOf.get(x.hi)}`))
      const tied = (i: number) => tight.has(`${i}>${i + 1}`)
      let prev = -1, far = 0
      for (const [gi, g] of groups.entries()) {
        const c = constOf(g)
        if (Number.isNaN(c)) return {unknown: 'the model\'s order equates two constants'}
        let next = Infinity
        for (const h of groups.slice(gi + 1)) { const d = constOf(h); if (d !== undefined) { next = d; break } }
        let x = c ?? (next === Infinity && prev > 0 ? (1 << 24) * ++far + 997 * far + prev + 13 : prev + 1)
        if (c === undefined && next !== Infinity && x % 2 === 0 && x + 1 < next) x++
        if (c === undefined && gi > 0 && tied(gi - 1)) x = prev + 1
        else if (c === undefined) { let k = gi; while (tied(k) && constOf(groups[k + 1]!) === undefined) k++; const d = tied(k) ? constOf(groups[k + 1]!) : undefined; if (d !== undefined) x = d - (k + 1 - gi) }
        if (x <= prev || x >= next || (gi > 0 && tied(gi - 1) && x !== prev + 1)) return {unknown: noRoom}
        for (const t of g) ordVal.set(t, x)
        prev = x
      }
    }
    for (const [t, x] of ordVal) if (t.startsWith('p:') || t.startsWith('s:')) w[t.slice(2)] = x
    const maps = new Map<string, Map<number, number>>()
    const cellVal = new Map<string, number>()
    for (const f of fins.values()) if (f.id.startsWith('c:')) { let x = 0; for (let val2 = 0; val2 <= f.cap; val2++) if (val(v(finAt(f, val2))!)) x = val2; cellVal.set(f.id, x) }
    for (const [mp, cells] of ordCells) for (const c of cells) { cellVal.set(c.id, ordVal.get(c.id) ?? 0); if (!cellsOf.has(mp)) cellsOf.set(mp, []); cellsOf.get(mp)!.push(c) }
    for (const o of ordOdd) { cellVal.set(o.id, ordVal.get(o.id) ?? 0); odd.push(o) }
    // every read of the goal, at its key's value under w: the abstraction's value where it has one, else 0
    const keyVal = (e: E): number | undefined => { const ts: [string, number][] = [], d = {c: 0}; if (!linTerms(e, 1, ts, d)) return undefined; let s = d.c; for (const [x, c] of ts) { if (w[x] === undefined) return undefined; s += c * w[x]! } return s }
    // (each function's table at its parts' values)
    for (const {f, n, a} of fnParts) { if (!maps.has(f)) maps.set(f, new Map()); maps.get(f)!.set(w[a]!, w[n]!) }
    // (and at a key of the wrong sort, a value of its own past every value the model gives: an injective function's
    // instance there holds, and a key it is a part of meets no cell of the right sort)
    let fresh2 = Math.max(0, ...Object.values(w), ...[...maps.values()].flatMap(t => [...t.values()]))
    // (a key that reads such a read, idn(64·idn(64·m + n) + n): its value from the tables so far, inner reads first)
    const valueAt = (e: E): number | undefined => {
      if (e.op === 'const') return e.value
      if (e.op === 'var') return w[e.name] ?? 0
      if (e.op === 'mul') { const a = valueAt(e.a); return a === undefined ? undefined : a * e.k }
      if (e.op === 'add') { const a = valueAt(e.a), b = valueAt(e.b); return a === undefined || b === undefined ? undefined : a + b }
      if (e.op === 'get' && fnMaps.has(e.map)) { const k = valueAt(e.key); return k === undefined ? undefined : maps.get(e.map)?.get(k) }
      return undefined
    }
    // (the reads gathered, the inner ones first: each read is gathered before the reads in its key)
    const fnOdd = (x: Extract<E, {op: 'get'}>): void => {
      tick()
      if (!fnMaps.has(x.map) || partName(x) !== undefined) return
      const key = keyVal(x.key) ?? valueAt(x.key), t = maps.get(x.map) ?? new Map<number, number>()
      if (key === undefined || t.has(key)) return
      maps.set(x.map, t.set(key, ordVal.get(`c:${x.map}#${textOfE(x.key)}`) ?? ++fresh2))
    }
    ;[...reads].reverse().forEach(fnOdd)
    for (const [mp, cells] of cellsOf) for (const c of cells) {
      const key = c.parts.reduce((s, p, i) => s + w[p]! * (patterns[mp]![i] ?? 1), 0)
      if (!maps.has(mp)) maps.set(mp, new Map())
      maps.get(mp)!.set(key, cellVal.get(c.id)!)
    }
    // (a cell at a key of the wrong sort, where its key falls, unless a cell of the right sort is there: one cell, whose
    // value the hypotheses are judged with below)
    for (const o of odd) {
      const key = keyVal(o.key) ?? valueAt(o.key)
      if (key === undefined) continue
      if (!maps.has(o.map)) maps.set(o.map, new Map())
      if (!maps.get(o.map)!.has(key)) maps.get(o.map)!.set(key, cellVal.get(o.id)!)
    }
    const allMaps = new Set<string>()
    for (const x of reads) allMaps.add(x.map)
    const st = {scalars: {}, maps: Object.fromEntries([...allMaps].map(mp => [mp, maps.get(mp) ?? new Map<number, number>()]))}
    const m = {name: goal.name, params: [], inputs: [], state: {}, step: {}, maps: Object.fromEntries([...allMaps].map(mp => [mp, 0]))} as unknown as Machine
    const env = new Proxy({...w}, {get: (t, q: string) => t[q] ?? 0}) as Record<string, number>
    for (const [i, h] of goal.hyps.entries()) { tick(); try { if (!evalC(h, env, st, m)) { return {unknown: `the abstraction's model breaks hypothesis ${i}${shaped[i] ? '' : ' (not EPR-shaped)'}`} } } catch { return {unknown: 'the model could not be read'} } }
    // the kernel's witness: names, and each cell of the goal by its key's linear form
    const witness: Record<string, number> = {...w}
    for (const x of reads) { tick(); const l = linear(x.key, new Map()), kv = keyVal(x.key); if (l && kv !== undefined) witness[`${x.map}[${canon(l)}]`] = st.maps[x.map]?.get(kv) ?? 0 }
    // the structure
    const values = [...new Set([...[...parts].map(x => w[x]), ...[...ordVal].filter(([t]) => !t.startsWith('k:') && !t.includes('#')).map(([, x]) => x)].filter((x): x is number => x !== undefined))].sort((a, b) => a - b), elem = new Map(values.map((x, i) => [x, i]))
    const diagram: Diagram = {elements: values.length, parts: {}, scalars: {}, cells: {}, fns: {}}
    for (const x of [...parts, ...ordScalars].sort()) if (w[x] !== undefined) diagram.parts[x] = elem.get(w[x]!)!
    for (const f of fins.values()) if (f.id.startsWith('s:')) diagram.scalars[f.id.slice(2)] = w[f.id.slice(2)] ?? 0
    for (const [mp, cells] of cellsOf) {
      const seen2 = new Set<string>(), out: {at: number[], value: number}[] = []
      for (const c of cells) {
        const at = c.parts.map(x => elem.get(w[x]!)!), id = at.join(','), value = cellVal.get(c.id)!
        if (!seen2.has(id)) { seen2.add(id); out.push({at, value: ordMaps.has(mp) ? elem.get(value) ?? value : value}) }
      }
      diagram.cells[mp] = out.sort((a, b) => { for (let i = 0; i < a.at.length; i++) if (a.at[i] !== b.at[i]) return a.at[i]! - b.at[i]!; return 0 })
    }
    for (const {f, n, a} of fnParts) { const t = (diagram.fns[f] ??= []), x = elem.get(w[a]!)!; if (!t.some(r => r[0] === x)) t.push([x, elem.get(w[n]!)!]) }
    for (const t of Object.values(diagram.fns)) t.sort((a, b) => a[0] - b[0])
    return {sat: true, witness, diagram}
  }
  // (the order's grouping first, as without a theory; where it breaks a hypothesis, the theory's rounds: lemmas the model
  // breaks, the search again, until the theory checks a model, its values the read-back's)
  let cur = outcome(search())
  if (!('model' in cur)) return cur
  let done = finish(cur.model, undefined)
  for (let round = 0; theory.length && 'unknown' in done && round < 256 && !opts.late?.(); round++) {
    let r = theoryCheck(cur.model)
    if (!r) break
    if ('val' in r) {
      done = finish(cur.model, r.val)
      // (the simplex's values breaking it: elimination's)
      if ('unknown' in done && r.exact) { r = r.exact(); if (r && 'val' in r) done = finish(cur.model, r.val) }
      if (r && !('val' in r)) { for (const l of r.lemmas) lemma(l); cur = outcome(search()); if (!('model' in cur)) return cur; done = finish(cur.model, undefined); continue }
      if ('unknown' in done) done = finish(cur.model, undefined)
      break
    }
    for (const l of r.lemmas) {
      lemma(l)
      const named = l.map((x): [string, boolean] => [names[Math.abs(x)]!, x > 0]), key = named.map(([k, b]) => (b ? '' : '¬') + k).sort().join('|')
      if (lemmaCache.size > 20_000) lemmaCache.clear()
      lemmaCache.set(key, named)
    }
    cur = outcome(search())
    if (!('model' in cur)) return cur
    done = finish(cur.model, undefined)
  }
  return done
}

// A small CDCL over clauses with origins: two watched literals, activity, learned clauses carrying the union of the
// origins they were resolved from, so a refutation's origins are its core. undefined: past the conflict budget.
type CdclOut = {sat: true, model: boolean[]} | {sat: false, core: Set<number>} | undefined
function cdcl(input: {lits: number[], from: Origin}[], budget: number, trueFirst: Set<number> = new Set(), late?: () => boolean): CdclOut {
  return cdclSolver(input, trueFirst).solve(budget, late)
}
// The CDCL as a solver clauses can be added to between its answers (a lemma a model breaks, lazily): each added at level
// 0, the search again from there with what it learned. `add` false: a clause over a variable it doesn't have.
function cdclSolver(input: {lits: number[], from: Origin}[], trueFirst: Set<number> = new Set(), keepPhase: Set<number> = new Set()): {solve: (budget: number, late?: () => boolean) => CdclOut, add: (c: {lits: number[], from: Origin}) => boolean} {
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
  const phase = new Int8Array(nv)
  const assign = (l: number, r?: Cl) => { val[Math.abs(l)] = l > 0 ? 1 : -1; level[Math.abs(l)] = lim.length; reason[Math.abs(l)] = r; trail.push(l) }
  let qhead = 0, fixed: CdclOut | 'none' = 'none'
  const units: Cl[] = []
  for (const c of cls) {
    if (!c.lits.length) { fixed = {sat: false, core: c.from}; break }
    if (c.lits.length === 1) units.push(c); else { wl(-c.lits[0]!).push(c); wl(-c.lits[1]!).push(c) }
  }
  const coreOf = (c: Cl): Set<number> => { // the origins of a conflict at level 0, through the reasons of its literals
    const out = new Set(c.from), seen = new Set<number>(), todo = c.lits.map(Math.abs)
    while (todo.length) { const x = todo.pop()!; if (seen.has(x)) continue; seen.add(x); const r = reason[x]; if (r) { for (const o of r.from) out.add(o); for (const l of r.lits) todo.push(Math.abs(l)) } }
    return out
  }
  for (const u of units) { if (fixed !== 'none') break; const s = valOf(u.lits[0]!); if (s < 0) { fixed = {sat: false, core: coreOf(u)}; break } if (s === 0) assign(u.lits[0]!, u) }
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
  // (the unassigned variables in a heap, the most active first, ties by the lower index: the choice a scan over them
  // makes, without the scan; an assigned one is dropped where it surfaces and put back when unassigned)
  const heap: number[] = [], at = new Int32Array(nv).fill(-1)
  const above = (a: number, b: number) => act[a]! > act[b]! || (act[a] === act[b] && a < b)
  const up = (i: number) => { const x = heap[i]!; while (i > 0) { const pi = (i - 1) >> 1, y = heap[pi]!; if (!above(x, y)) break; heap[i] = y; at[y] = i; i = pi } heap[i] = x; at[x] = i }
  const down = (i: number) => { const x = heap[i]!; for (;;) { let c = 2 * i + 1; if (c >= heap.length) break; if (c + 1 < heap.length && above(heap[c + 1]!, heap[c]!)) c++; if (!above(heap[c]!, x)) break; heap[i] = heap[c]!; at[heap[i]!] = i; i = c } heap[i] = x; at[x] = i }
  const push = (x: number) => { if (at[x]! >= 0) return; heap.push(x); at[x] = heap.length - 1; up(heap.length - 1) }
  const pop = (): number => { const x = heap[0]!, y = heap.pop()!; at[x] = -1; if (heap.length) { heap[0] = y; at[y] = 0; down(0) } return x }
  for (let x = 1; x < nv; x++) push(x)
  let inc = 1
  const backjump = (bt: number) => { while (lim.length > bt) { const to = lim.pop()!; while (trail.length > to) { const x = Math.abs(trail.pop()!); val[x] = 0; reason[x] = undefined; push(x) } } qhead = Math.min(qhead, trail.length) }
  const add = (c: {lits: number[], from: Origin}): boolean => {
    if (fixed !== 'none' && fixed?.sat === false) return true
    if (c.lits.some(l => !idx.has(Math.abs(l)))) return false
    backjump(0); fixed = 'none'
    const cl: Cl = {lits: c.lits.map(vid), from: new Set([c.from])}
    if (cl.lits.some(l => valOf(l) > 0)) return true
    const open = cl.lits.filter(l => valOf(l) === 0)
    if (!open.length) { fixed = {sat: false, core: coreOf(cl)}; return true }
    cl.lits = [...open, ...cl.lits.filter(l => valOf(l) < 0)]
    if (open.length === 1) assign(open[0]!, cl); else { wl(-cl.lits[0]!).push(cl); wl(-cl.lits[1]!).push(cl) }
    return true
  }
  const solve = (budget: number, late?: () => boolean): CdclOut => {
  if (fixed !== 'none') return fixed
  let conflicts = 0
  for (;;) {
    const confl = propagate()
    if (confl) {
      if (++conflicts > budget || (conflicts % 256 === 0 && late?.())) return undefined
      if (!lim.length) return (fixed = {sat: false, core: coreOf(confl)})
      // first UIP
      const seen = new Uint8Array(nv), learnt: number[] = [], from = new Set(confl.from)
      let p = 0, cnt = 0, c: Cl | undefined = confl, ti = trail.length - 1
      do {
        for (const q of c!.lits) {
          if (q === p) continue
          const x = Math.abs(q)
          if (!seen[x] && level[x]! > 0) { seen[x] = 1; act[x] = act[x]! + inc; if (at[x]! >= 0) up(at[x]!); if (level[x] === lim.length) cnt++; else learnt.push(q) }
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
      while (lim.length > bt) { const to = lim.pop()!; while (trail.length > to) { const x = Math.abs(trail.pop()!); val[x] = 0; reason[x] = undefined; push(x) } }
      qhead = trail.length
      const nc: Cl = {lits: learnt, from}
      if (learnt.length > 1) { wl(-learnt[0]!).push(nc); wl(-learnt[1]!).push(nc) }
      assign(learnt[0]!, nc)
      continue
    }
    // decide: the most active unassigned variable, false first
    let best = 0
    while (heap.length) { const x = pop(); if (val[x] === 0) { best = x; break } }
    if (!best) { const model: boolean[] = []; for (let x = 1; x < nv; x++) { model[back[x]!] = val[x]! > 0; if (keepPhase.has(back[x]!)) phase[x] = val[x]! } return {sat: true, model} }
    lim.push(trail.length)
    assign(phase[best] ? phase[best]! * best : trueFirst.has(back[best]!) ? best : -best)
  }
  }
  return {solve, add}
}
