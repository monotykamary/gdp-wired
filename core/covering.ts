// Covering invariants (untrusted candidate generation). A law of the shape "every item is covered by a total",
//   ∀k. G(k) ⇒ w(k) ≤ X        (an item's cost is at most a running total)
//   ∀k. G(k) ⇒ 1 ≤ X           (a member implies a positive count)
// is rarely inductive alone: the step that takes one item out of X needs the other items to fit in what is left. The
// helper that ties the total to the items is the filtered sum over every key,
//   Σk (G(k) ? w(k) : 0) ≤ X   (or = X, or with the plain sums of the other maps X is charged for on the left),
// and the law is that sum's own cover fact (one key's term is at most the sum) with the helper. This file reads the
// shape off the law's and the step's syntax alone and returns the helpers as candidate laws over sums the caller
// declares (core/dsl.ts's sums over a map's keys, which the kernel keeps exact: kernel.ts's sumMachine). Nothing here
// is believed: a caller hands the candidates to proveCandidateSeeds, which drops each one a state refutes and has the
// kernel check the kept family with the law. A wrong or useless candidate costs time, never a verdict.
import {type C, type E, type Law, type Machine} from './machine.ts'

type Lit = {c: C, neg: boolean}
const text = (u: unknown) => JSON.stringify(u)
const one: E = {op: 'const', value: 1}, zero: E = {op: 'const', value: 0}
const plus = (a: E, b: E): E => ({op: 'add', a, b})

// The law's body as clauses (a conjunction of disjunctions of literals), or undefined past `most` clauses or at a
// quantifier or a flag (no law of this shape reads one).
function clauses(c: C, neg: boolean, most: number): Lit[][] | undefined {
  switch (c.op) {
    case 'not': return clauses(c.x, !neg, most)
    case 'and': case 'or': {
      const parts = c.xs.map(x => clauses(x, neg, most))
      if (parts.some(p => !p)) return undefined
      if ((c.op === 'and') !== neg) { const out = (parts as Lit[][][]).flat(); return out.length > most ? undefined : out }
      let out: Lit[][] = [[]]
      for (const p of parts as Lit[][][]) {
        out = out.flatMap(a => p.map(b => [...a, ...b]))
        if (out.length > most) return undefined
      }
      return out
    }
    case '<': case '<=': case '=': return [[{c, neg}]]
    default: return undefined
  }
}

// What a term or a condition reads: plain names, and maps (with whether every read is at the key alone).
type Reads = {vars: Set<string>, maps: Set<string>, keyed: boolean, shaped: boolean}
function reads(t: E | C, key: string, r: Reads = {vars: new Set(), maps: new Set(), keyed: true, shaped: true}): Reads {
  switch (t.op) {
    case 'var': r.vars.add(t.name); break
    case 'const': break
    case 'get': r.maps.add(t.map); if (!(t.key.op === 'var' && t.key.name === key)) { r.keyed = false; reads(t.key, key, r) } break
    case 'mul': reads(t.a, key, r); break
    case 'add': case 'sub': case 'min': case 'max': case 'prod': reads(t.a, key, r); reads(t.b, key, r); break
    case 'if': reads(t.c, key, r); reads(t.then, key, r); reads(t.else, key, r); break
    case 'tup': case 'proj': r.shaped = false; break
    case '<': case '<=': case '=': reads(t.a, key, r); reads(t.b, key, r); break
    case 'and': case 'or': for (const x of t.xs) reads(x, key, r); break
    case 'not': reads(t.x, key, r); break
    default: r.shaped = false
  }
  return r
}

// A literal as lo ≤ hi, where it is one (¬(a < b) is b ≤ a; a < b over naturals is a + 1 ≤ b, kept for a constant a;
// ¬(X = 0) and ¬(0 = X) are 1 ≤ X).
function atMost(l: Lit): {lo: E, hi: E} | undefined {
  const c = l.c
  if (c.op === '<=' && !l.neg) return {lo: c.a, hi: c.b}
  if (c.op === '<' && l.neg) return {lo: c.b, hi: c.a}
  if (c.op === '<' && !l.neg && c.a.op === 'const') return {lo: {op: 'const', value: c.a.value + 1}, hi: c.b}
  if (c.op === '<=' && l.neg && c.b.op === 'const') return {lo: {op: 'const', value: c.b.value + 1}, hi: c.a}
  if (c.op === '=' && l.neg) {
    if (c.a.op === 'const' && c.a.value === 0) return {lo: one, hi: c.b}
    if (c.b.op === 'const' && c.b.value === 0) return {lo: one, hi: c.a}
  }
  return undefined
}
const litC = (l: Lit): C => (l.neg ? {op: 'not', x: l.c} : l.c)
const notLit = (l: Lit): C => (l.neg ? l.c : {op: 'not', x: l.c})

export type CoveringShape = {
  // The filtered sum's term at `key` (a term of the maps at that key alone), the map its name goes by, and the total
  // it is compared with; `unless`: the clause's other key-free literals (the helper holds where one does).
  key: string, map: string, term: E, total: E, unless: C[], plain: boolean
}
// The clauses of the law that have the shape, each read as guard, weight and total.
export function coveringShapes(m: Machine, law: Law): CoveringShape[] {
  const key = law.forall
  if (!key || law.keys?.length || law.some?.length || law.ex || law.finite !== undefined || law.witness) return []
  if (m.history || Object.keys(m.counts ?? {}).length || !m.maps) return []
  const cs = clauses(law.holds, false, 16)
  if (!cs) return []
  const stateMap = (name: string) => Object.hasOwn(m.maps!, name) && !(m.inputMaps ?? []).includes(name) && !Object.hasOwn(m.fns ?? {}, name)
  const scalar = (name: string) => Object.hasOwn(m.state, name) && !Object.hasOwn(m.sums ?? {}, name)
  // A term of the cells at the key alone (what a sum's term may read); a term of the state and params, with a state
  // variable (a total).
  const cellTerm = (t: E | C) => { const r = reads(t, key); return r.shaped && r.keyed && r.maps.size > 0 && r.vars.size === 0 && [...r.maps].every(stateMap) }
  const free = (t: E | C) => { const r = reads(t, key); return r.shaped && !r.vars.has(key) && r.maps.size === 0 }
  const total = (t: E) => free(t) && [...reads(t, key).vars].some(scalar)
  const out: CoveringShape[] = []
  for (const clause of cs) {
    const guard: C[] = [], unless: C[] = []
    let weight: E | undefined, tot: E | undefined, ok = true
    for (const l of clause) {
      if (cellTerm(l.c)) { guard.push(notLit(l)); continue }
      const le = atMost(l)
      if (le && total(le.hi) && !weight && !tot && cellTerm(le.lo)) { weight = le.lo; tot = le.hi; continue }
      // (a member implies a positive count: 1 ≤ X; two of them in one clause, 1 ≤ X or 1 ≤ Y, are covered by X + Y)
      if (le && total(le.hi) && le.lo.op === 'const' && le.lo.value === 1 && (!weight || text(weight) === text(one))) {
        weight = one; tot = tot ? plus(tot, le.hi) : le.hi; continue
      }
      if (free(l.c)) { unless.push(litC(l)); continue }
      ok = false; break
    }
    if (!ok || !weight || !tot) continue
    // (a count needs a guard to count by: with none, 1 ≤ X is no law about the cells)
    if (weight === one && !guard.length) continue
    const term: E = guard.length ? {op: 'if', c: guard.length === 1 ? guard[0]! : {op: 'and', xs: guard}, then: weight, else: zero} : weight
    const maps = [...reads(term, key).maps].sort()
    out.push({key, map: maps[0]!, term, total: tot, unless, plain: !guard.length && weight.op === 'get'})
  }
  return out
}

// The other maps a total is charged for: a state map of naturals starting at 0 whose cell the step adds to or takes
// from a state variable of the total (read as a value, not only as a condition), and that the shape's own term doesn't
// read. At most `most`, in the machine's order.
export function companions(m: Machine, shape: CoveringShape, most = 2): string[] {
  const mine = reads(shape.term, shape.key).maps, vars = [...reads(shape.total, shape.key).vars].filter(n => Object.hasOwn(m.state, n))
  const valued = new Set<string>()
  const values = (e: E): void => {
    switch (e.op) {
      case 'get': valued.add(e.map); break
      case 'mul': values(e.a); break
      case 'add': case 'sub': case 'min': case 'max': case 'prod': values(e.a); values(e.b); break
      case 'if': values(e.then); values(e.else); break
      default: break
    }
  }
  for (const n of vars) { const u = m.step.state?.[n]; if (u) values(u) }
  return Object.keys(m.maps ?? {}).filter(map => valued.has(map) && !mine.has(map) && m.maps![map] === 0 && !!m.step.maps?.[map] &&
    !(m.inputMaps ?? []).includes(map)).slice(0, most)
}

// The candidate helpers for a law, strongest first: for each shape and each set of companions, the sums on the left
// equal to the total, then at most it. `declare` makes a sum over every key of a term (given at a key) and returns its
// variable's name, or undefined where the kernel keeps no such sum for this machine (the candidate is then left out).
export type DeclareSum = (map: string, at: (key: E) => E, plain: boolean) => string | undefined
export function coveringSeeds(m: Machine, law: Law, declare: DeclareSum): Law[] {
  const out: Law[] = [], seen = new Set<string>()
  const subst = (t: E, from: string, to: E): E => JSON.parse(text(t), (_k, v) => (v && v.op === 'var' && v.name === from ? to : v)) as E
  let stem = 'covering'; while (text([m, law]).includes(`${stem} `)) stem += '$'
  for (const shape of coveringShapes(m, law)) {
    const own = declare(shape.map, k => subst(shape.term, shape.key, k), shape.plain)
    if (!own) continue
    const others = companions(m, shape).flatMap(map => { const s = declare(map, k => ({op: 'get', map, key: k}), true); return s ? [s] : [] })
    const sets: string[][] = [[]]
    for (const o of others) sets.push(...sets.map(s => [...s, o]))
    for (const set of sets.sort((a, b) => b.length - a.length)) {
      const left = set.reduce<E>((acc, s) => plus(acc, {op: 'var', name: s}), {op: 'var', name: own})
      for (const op of ['=', '<='] as const) {
        const tie: C = {op, a: left, b: shape.total}
        const holds: C = shape.unless.length ? {op: 'or', xs: [...shape.unless, tie]} : tie
        if (seen.has(text(holds))) continue
        seen.add(text(holds))
        out.push({name: `${stem} ${out.length}: ${[own, ...set].join(' + ')} ${op === '=' ? '=' : '≤'} its total`, holds})
      }
    }
  }
  return out
}

// The cell facts a covering sum leans on: the sum moves only as the step says while the cells it filters by keep to
// the states the rule reaches (a counted row is never idle again), which no helper over the sum states. For the maps
// the shapes' terms read and the maps written at the same key (a row's other columns): every pair of values, of two
// of those maps, that the syntax compares a cell with, as "no key holds both". Most are false and a short run or the
// candidate check drops them; the rest are what the sums' step goals read at the written key.
export function cellSeeds(m: Machine, law: Law, most = 160): Law[] {
  const shapes = coveringShapes(m, law)
  if (!shapes.length) return []
  const guards = new Set(shapes.flatMap(s => [...reads(s.term, s.key).maps]))
  const written = (map: string) => { const w = m.step.maps?.[map]; return !w ? undefined : 'each' in w ? 'each' : text(w.key) }
  const rows = new Set([...guards].map(written).filter(k => k !== undefined))
  const maps = Object.keys(m.maps ?? {}).filter(map => !(m.inputMaps ?? []).includes(map) && (guards.has(map) || rows.has(written(map) ?? ''))).slice(0, 8)
  const values = new Map(maps.map(map => [map, new Set([m.maps![map]!])]))
  JSON.parse(text([m.step, m.assume, law.holds]), (_k, v) => {
    if (v && v.op === '=') for (const [a, b] of [[v.a, v.b], [v.b, v.a]]) if (a?.op === 'get' && b?.op === 'const' && values.has(a.map)) values.get(a.map)!.add(b.value)
    return v
  })
  let stem = 'covering'; while (text([m, law]).includes(`${stem} `)) stem += '$'
  const key = `${stem}$cell`, out: Law[] = []
  const is = (map: string, value: number): C => ({op: '=', a: {op: 'get', map, key: {op: 'var', name: key}}, b: {op: 'const', value}})
  const lits = maps.flatMap(map => { const vs = [...values.get(map)!].sort((a, b) => a - b); return vs.length <= 4 ? vs.map(value => ({map, value})) : [] })
  for (let i = 0; i < lits.length; i++) for (let j = i + 1; j < lits.length; j++) {
    const a = lits[i]!, b = lits[j]!
    if (a.map === b.map || out.length >= most) continue
    out.push({name: `${stem} cell ${out.length}: no key has ${a.map} = ${a.value} and ${b.map} = ${b.value}`, forall: key,
      holds: {op: 'or', xs: [{op: 'not', x: is(a.map, a.value)}, {op: 'not', x: is(b.map, b.value)}]}})
  }
  return out
}
