// Accelerated cycles: recurrent sets from a loop's relation, not its runs, and stems into them from runs whose loops are
// taken n times at once. Untrusted, like core/nonterm.ts, whose search calls this: what is found here is a candidate
// set, its witness and a stem, and the kernel proves the set closed and the stem into it (kernel.ts's checkRecur,
// NonTerm.lean's never_ends_of).
//
// - Cycles. The relation's paths (core/relation.ts: one turn as linear paths, each from a location to a location) as a
//   graph; its closed walks (a location may come twice: x > 0 and x < 0 taken in turn), each by its least rotation, by
//   how many choices they make among a location's paths (at most `maxLen`; a chain of locations with one path out, as a
//   translated program's straight-line code, costs nothing) and at most 64 turns, a walk cut where its rows (each turn's
//   inputs left open) are refuted; a self-loop also twice over (a period of two: x := −x). Then the cycles the random
//   runs take, between two visits of a location, the commonest first.
// - A turn's inputs as terms of the state before it: a value a row pins (an equation in it), else a bound a row puts on
//   it (x < i0 gives i0 := x + 1, i0 >= 3 gives 3), else 0; or constants from a model of two rounds of the cycle. The
//   cycle is then one linear loop: its guard G (each turn's rows, read at the state the turns before it leave) and its
//   update U (affine in the state at the cycle's start).
// - Its n-fold run in closed form: an atom g ≤ 0 of G holds after every number n of turns where its value along the
//   run, g(Uⁿx), a polynomial in n for a translation or a triangular update (the differences core/discover.ts's
//   closedForm fits), has its differences at n = 0 all ≤ 0: Δ⁰g = g, Δ^{k+1}g = Δ^k g∘U − Δ^k g, each linear in x
//   (Σ C(n, k)·Δ^k g is g(Uⁿx)). For a geometric update (x := 2x) the differences repeat (Δ²g = Δ¹g) and the same set
//   holds. So the set R is G with each atom's differences up to degree 3, and Houdini drops a difference that isn't kept
//   by U (G's atoms are kept or the cycle is given up): R ∧ ¬a(Ux) refuted for each atom a, by the integer solver
//   (core/solver.ts). A constant difference above 0 gives the cycle up at once: g grows past 0.
// - The set of the loop: per turn j of the cycle, at its location, the states from which the rest of the cycle's turns
//   are allowed and end in R (R_j, the weakest precondition: the rest composed); the witness by location, or by R_j
//   where the cycle passes a location twice, its commonest value with no condition.
// - Stems (`stemsTo`): from the start's location to a part's, a path at a time or a self-loop that is a translation
//   taken n times at once, all linear, then run on the loop itself.
import {type C, type E, n as K, x as V} from './machine.ts'
import type {Loop} from '../kernel/kernel.ts'
import {type Path, type Relation, relationOf} from './relation.ts'
import {type Lin, canon, gcd, konst, plus, solve, subst, times, vars} from './solver.ts'

// `targets`: the set's parts, each a location and its rows over the relation's names (R_j), for a stem's search.
export type Target = {loc: number, rows: Lin[]}
export type Accelerated = {set: C, wit: Record<string, E>, cycle: number[], locs: number[], targets: Target[]}

const isConst = (l: Lin) => vars(l).length === 0
// (a row's coefficients divided by their common divisor, its constant rounded up: an integer row as tight as it goes)
const tight = (l: Lin): Lin => {
  const g = vars(l).reduce((s, x) => gcd(s, l[x]!), 0)
  if (g <= 1) return l
  const o: Lin = {}
  for (const x of vars(l)) o[x] = l[x]! / g
  const c = Math.ceil((l['1'] ?? 0) / g)
  if (c) o['1'] = c
  return o
}
const big = (l: Lin) => Object.values(l).some(c => !Number.isSafeInteger(c) || Math.abs(c) > 2 ** 40)

// rows lin <= 0 satisfiable over the integers (unknown counts as satisfiable: the kernel decides later)
const sat = (rows: Lin[]) => solve(rows.map(lin => ({lin, label: ''})), 3000).kind !== 'refuted'
const implied = (rows: Lin[], a: Lin) => solve([...rows, plus(times(a, -1), konst(1))].map(lin => ({lin, label: ''})), 3000).kind === 'refuted'

// `runs`: runs of the loop (params and each turn's inputs) whose cycles are tried first, the commonest first: each turn
// read as the relation's path it took (`io` replays them).
export type AccelOptions = {now: () => number, until: number, maxLen?: number, maxCycles?: number, runs?: {params: Record<string, number>, inputs: Record<string, number>[]}[], io?: StemIO}

// The candidates, one at a time (a generator: the caller tries each against the kernel and stops when one is proven).
export function* accelerated(l: Loop, opts: AccelOptions): Generator<Accelerated> {
  const rel = relOf(l)
  if (!rel) return
  const {now, until} = opts, maxLen = opts.maxLen ?? 6
  const S = rel.state, P = new Set(rel.params), Sset = new Set(S)
  const natState = S.filter(x => !rel.ints.has(x))
  const from = (i: number) => (rel.loc ? rel.from[i]! : 0), to = (i: number) => (rel.loc ? rel.to[i]! : 0)
  // Each path's inputs as terms of the state before it (a few choices each, the first the likeliest).
  const choices = rel.paths.map(p => inputChoices(p, Sset, P))
  // The cycles: closed walks of paths (a location may come twice: two turns at one location, taken in turn), each once
  // (its least rotation), with at most `maxLen` choices among a location's paths (a chain of locations with one path out,
  // as a translated program's straight-line code, is free) and at most 64 turns; the shortest first.
  let cycles: number[][] = []
  const byFrom = new Map<number, number[]>()
  rel.paths.forEach((_, i) => { const f = from(i); byFrom.set(f, [...(byFrom.get(f) ?? []), i]) })
  const cap = opts.maxCycles ?? 400
  const least = (seq: number[]) => seq.every((_, r) => r === 0 || cmp(seq, [...seq.slice(r), ...seq.slice(0, r)]) < 0)
  // (a turn costs 1 at a location of more than one path, 0 else; each location's least cost back to the cycle's start,
  // so a walk that can't come back within the budget is cut)
  const costAt = (loc: number) => ((byFrom.get(loc) ?? []).length > 1 ? 1 : 0)
  const back = (start: number): Map<number, number> => {
    const d = new Map<number, number>([[start, 0]]), queue = [start]
    while (queue.length) {
      const y = queue.shift()!
      for (let i = 0; i < rel.paths.length; i++) {
        if (to(i) !== y) continue
        const x = from(i), c = d.get(y)! + costAt(x)
        if (c < (d.get(x) ?? Infinity)) { d.set(x, c); if (costAt(x)) queue.push(x); else queue.unshift(x) }
      }
    }
    return d
  }
  const backs = new Map<number, Map<number, number>>()
  // (each walk's turns composed with their inputs left open, u@k: a walk whose rows are refuted is cut where it chose)
  const open = (sigma: Record<string, Lin>, i: number, k: number) => {
    const p = rel.paths[i]!, insAt = Object.fromEntries(Object.entries(symbolic(p, k, Sset, P)).map(([u, t]) => [u, subst(t, sigma)]))
    const sub = {...sigma, ...insAt}
    const rs = [...p.rows.map(f => subst(f, sub)), ...natState.map(x => times(sigma[x]!, -1)), ...Object.keys(insAt).filter(u => !rel.ints.has(u)).map(u => times(insAt[u]!, -1))]
    return {rs, post: Object.fromEntries(S.map(x => [x, subst(p.post[x] ?? {[x]: 1}, sub)]))}
  }
  const id0: Record<string, Lin> = Object.fromEntries(S.map(x => [x, {[x]: 1}]))
  let nodes = 20_000
  for (let budget = 0; budget <= maxLen && cycles.length < cap && nodes > 0; budget++) {
    for (let i = 0; i < rel.paths.length && cycles.length < cap && nodes > 0 && now() < until; i++) {
      const s0 = from(i)
      if (!backs.has(s0)) backs.set(s0, back(s0))
      const d = backs.get(s0)!
      const walk = (seq: number[], at: number, cost: number, sigma: Record<string, Lin>, rows: Lin[]) => {
        if (--nodes < 0 || cycles.length >= cap || now() > until) return
        if (at === s0 && cost === budget && least(seq) && sat(rows)) cycles.push(seq)
        if (seq.length >= 64) return
        const c = cost + costAt(at)
        if (c + (d.get(at) ?? Infinity) - costAt(at) > budget || c > budget) return
        for (const j of byFrom.get(at) ?? []) {
          if (j < seq[0]! || c + (d.get(to(j)) ?? Infinity) > budget) continue
          const {rs, post} = open(sigma, j, seq.length), all = [...rows, ...rs]
          if (all.some(big) || (costAt(at) && !sat(all))) continue
          walk([...seq, j], to(j), c, post, all)
        }
      }
      const c0 = costAt(s0), first = open(id0, i, 0)
      if (c0 + (d.get(to(i)) ?? Infinity) <= budget && sat(first.rs)) walk([i], to(i), c0, first.post, first.rs)
    }
  }
  cycles = cycles.sort((x, y) => x.length - y.length).slice(0, cap)
  // the runs' cycles: between two visits of a location, the paths taken (as their least rotation), by how often; after
  // the enumerated ones of at most 4 turns (at most 20,000 turns read)
  if (opts.runs && opts.io) {
    const count = new Map<string, {seq: number[], n: number}>()
    const byLoc = new Map<number, number[]>()
    rel.paths.forEach((_, i) => { byLoc.set(from(i), [...(byLoc.get(from(i)) ?? []), i]) })
    let budget = 20_000
    for (const r of opts.runs) {
      if (now() > until || budget <= 0) break
      let st = opts.io.start(r.params)
      const seq: number[] = []
      for (const input of r.inputs.slice(0, Math.min(budget, 1000))) {
        budget--
        const i = pathAt(rel, byLoc.get(rel.loc ? st[rel.loc] ?? 0 : 0) ?? [], st, input)
        if (i === undefined) break
        seq.push(i)
        const nx = opts.io.turn(st, input)
        if (!nx) break
        st = nx
      }
      const next = new Map<number, number>()
      for (let k = seq.length - 1; k >= 0; k--) {
        const j = next.get(from(seq[k]!))
        next.set(from(seq[k]!), k)
        if (j === undefined || j - k > 64) continue
        const c = seq.slice(k, j)
        const r0 = c.map((_, q) => [...c.slice(q), ...c.slice(0, q)]).sort(cmp)[0]!, key = r0.join(',')
        const e = count.get(key)
        if (e) e.n++; else count.set(key, {seq: r0, n: 1})
      }
    }
    const fromRuns = [...count.values()].sort((a, b) => b.n - a.n || a.seq.length - b.seq.length).slice(0, 60).map(e => e.seq)
    const keys = new Set(fromRuns.map(c => c.join(','))), short = cycles.filter(c => c.length <= 4)
    const shortKeys = new Set(short.map(c => c.join(',')))
    cycles = [...short, ...fromRuns.filter(c => !shortKeys.has(c.join(','))), ...cycles.filter(c => c.length > 4 && !keys.has(c.join(',')))]
  }
  const tried = new Set<string>()
  for (const cyc of cycles) {
    for (const reps of cyc.length === 1 ? [1, 2] : [1]) {
      const seq = Array.from({length: reps}, () => cyc).flat()
      // the choices of inputs: constants from a model of two rounds of the cycle (the constants the same in each), then
      // each path's first choice of terms, then one path at a time its others
      const sets: Ins[][] = []
      const sym = seq.map((pi, j) => symbolic(rel.paths[pi]!, j, Sset, P))
      if (sym.some(x => Object.values(x).some(t => vars(t).some(v => v.includes('@'))))) {
        const two = compose(rel, [...seq, ...seq].map((path, j) => ({path, ins: sym[j % seq.length]!})), natState)
        const m = two && solve(two.rows.map(lin => ({lin, label: ''})), 3000)
        if (m && m.kind === 'sat') sets.push(sym.map(x => Object.fromEntries(Object.entries(x).map(([u, t]) => [u, subst(t, Object.fromEntries(vars(t).filter(v => v.includes('@')).map(v => [v, konst(Math.round(m.witness[v] ?? 0))])))]))))
      }
      sets.push(seq.map(pi => choices[pi]![0]!))
      seq.forEach((pi, j) => { for (let c = 1; c < choices[pi]!.length; c++) sets.push(seq.map((qi, k) => choices[qi]![k === j ? c : 0]!)) })
      for (const ins of sets) {
        if (now() > until) return
        const key = `${seq.join(',')}|${JSON.stringify(ins)}`
        if (tried.has(key)) continue
        tried.add(key)
        const out = candidate(rel, seq, ins, natState, from, l, () => now() > until)
        if (out) yield {...out, cycle: seq, locs: seq.map(from)}
      }
    }
  }
}

// The path a turn takes: its pins (the location, the rule) and its rows hold at the state and the turn's inputs.
function pathAt(rel: Relation, among: number[], st: Record<string, number>, input: Record<string, number>): number | undefined {
  const at = {...st, ...input}
  const value = (x: string) => { const pair = rel.ints.get(x); return pair ? (at[pair[0]] ?? 0) - (at[pair[1]] ?? 0) : (at[x] ?? 0) }
  for (const i of among) {
    const p = rel.paths[i]!
    if (Object.entries(p.pins).some(([n, v]) => !n.endsWith('′') && n in at && at[n] !== v)) continue
    if (p.rows.every(f => vars(f).reduce((s, x) => s + f[x]! * value(x), f['1'] ?? 0) <= 0)) return i
  }
  return undefined
}
const rels = new WeakMap<Loop, Relation | undefined>()
function relOf(l: Loop): Relation | undefined {
  if (rels.has(l)) return rels.get(l)
  // (a path that reads a product, which the relation stands for by a natural of its own, is left out: the search keeps
  // to the linear paths, and the kernel checks what it finds against the loop itself)
  let r = relationOf(l)
  if (r && !r.exact) {
    const lin = (p: Path) => ![...p.rows.flatMap(vars), ...Object.values(p.post).flatMap(vars)].some(x => x.startsWith('π('))
    const keep = r.paths.map(lin)
    r = {...r, paths: r.paths.filter((_, i) => keep[i]), from: r.from.filter((_, i) => keep[i]), to: r.to.filter((_, i) => keep[i]), nats: r.nats.filter(x => !x.startsWith('π(')), exact: true}
  }
  const out = r && r.paths.length ? r : undefined
  rels.set(l, out)
  return out
}

// --- inputs ---------------------------------------------------------------------------------------------------------

// Each input of a path: a term over the state and params before the turn (or, `sym`, a constant still to be chosen,
// named u@j for the cycle's turn j).
type Ins = Record<string, Lin>
function inputsOf(p: Path, S: Set<string>, P: Set<string>): string[] {
  const read = [...new Set([...p.rows.flatMap(vars), ...Object.values(p.post).flatMap(vars)])]
  return read.filter(x => !S.has(x) && !P.has(x)).sort()
}
// The terms a path's rows suggest for u: an equation (rows f and −f, u's coefficient ±1) over known names, else the
// bounds a row puts on u (a constant rounded inward, or a term where u's coefficient is ±1).
function optionsFor(rows: Lin[], u: string, known: (x: string) => boolean): {eqs: Lin[], bounds: Lin[]} {
  const eqs: Lin[] = [], lows: Lin[] = [], highs: Lin[] = []
  const keys = new Set(rows.map(canon))
  for (const f of rows) {
    const c = f[u]
    if (c === undefined) continue
    const rest = plus(f, {[u]: c}, -1)
    if (!vars(rest).every(known)) continue
    if (Math.abs(c) === 1 && keys.has(canon(times(f, -1)))) { eqs.push(times(rest, -1 / c)); continue }
    if (isConst(rest)) { const b = -(rest['1'] ?? 0) / c; (c < 0 ? lows : highs).push(konst(c < 0 ? Math.ceil(b) : Math.floor(b))) }
    else if (Math.abs(c) === 1) (c < 0 ? lows : highs).push(times(rest, -1 / c))
  }
  return {eqs, bounds: [...lows, ...highs]}
}
const unique = (ls: Lin[]) => [...new Map(ls.map(t => [canon(t), t])).values()]
// Up to three choices of a path's inputs as terms: per input, the alt-th of its options that leaves the path's rows
// satisfiable (each input read with those chosen before it put in).
function inputChoices(p: Path, S: Set<string>, P: Set<string>): Ins[] {
  const inputs = inputsOf(p, S, P)
  if (!inputs.length) return [{}]
  const known = (x: string) => S.has(x) || P.has(x)
  const pick = (alt: number): Ins => {
    const ins: Ins = {}
    let rows = p.rows
    for (const u of inputs) {
      const o = optionsFor(rows, u, known), opts = unique(o.eqs.length ? o.eqs : [...o.bounds, {}])
      const ok = opts.filter(t => { const rs = rows.map(f => subst(f, {[u]: t})); return !rs.some(f => isConst(f) && (f['1'] ?? 0) > 0) && sat(rs) })
      const from = ok.length ? ok : opts
      ins[u] = from[Math.min(alt, from.length - 1)]!
      rows = rows.map(f => subst(f, {[u]: ins[u]!}))
    }
    return ins
  }
  const out = new Map<string, Ins>()
  for (let a = 0; a < 3; a++) { const x = pick(a); out.set(JSON.stringify(x), x) }
  return [...out.values()]
}
// A path's inputs at the cycle's turn j with the constants left open: an equation's term where its rows give one, else
// u@j.
function symbolic(p: Path, j: number, S: Set<string>, P: Set<string>): Ins {
  const ins: Ins = {}
  let rows = p.rows
  const known = (x: string) => S.has(x) || P.has(x) || x.includes('@')
  for (const u of inputsOf(p, S, P)) {
    const o = optionsFor(rows, u, known)
    ins[u] = o.eqs[0] ?? {[`${u}@${j}`]: 1}
    rows = rows.map(f => subst(f, {[u]: ins[u]!}))
  }
  return ins
}

// --- one cycle --------------------------------------------------------------------------------------------------------

type Step = {path: number, ins: Ins}
// Turns j.. of the cycle composed from a state x (identity at j): the rows over x, and the state after them over x.
function compose(rel: Relation, steps: Step[], natState: string[]): {rows: Lin[], post: Record<string, Lin>} | undefined {
  let sigma: Record<string, Lin> = Object.fromEntries(rel.state.map(x => [x, {[x]: 1}]))
  const rows: Lin[] = []
  for (const s of steps) {
    const p = rel.paths[s.path]!
    const insAt: Record<string, Lin> = Object.fromEntries(Object.entries(s.ins).map(([u, t]) => [u, subst(t, sigma)]))
    const sub = {...sigma, ...insAt}
    for (const f of p.rows) rows.push(subst(f, sub))
    for (const x of natState) rows.push(times(sigma[x]!, -1))
    // (a natural input's term is a natural)
    for (const u in insAt) if (!rel.ints.has(u)) rows.push(times(insAt[u]!, -1))
    const next: Record<string, Lin> = {}
    for (const x of rel.state) next[x] = subst(p.post[x] ?? {[x]: 1}, sub)
    sigma = next
    if (Object.values(sigma).some(big) || rows.some(big)) return undefined
  }
  return {rows: dedupe(rows.map(tight).filter(f => !(isConst(f) && (f['1'] ?? 0) <= 0))), post: sigma}
}
const dedupe = (rows: Lin[]) => [...new Map(rows.map(f => [canon(f), f])).values()]

// (`late`: the time is up; a candidate half made is given up)
function candidate(rel: Relation, seq: number[], ins: Ins[], natState: string[], from: (i: number) => number, l: Loop, late: () => boolean): Omit<Accelerated, 'cycle' | 'locs'> | undefined {
  const steps: Step[] = seq.map((path, j) => ({path, ins: ins[j]!}))
  const whole = compose(rel, steps, natState)
  if (!whole) return undefined
  const G = whole.rows, U = whole.post
  if (G.some(f => isConst(f) && (f['1'] ?? 0) > 0) || !sat(G)) return undefined
  // the differences of each atom of G along U, up to degree 3
  const opt: Lin[] = []
  for (const g of G) {
    let d = g
    for (let k = 1; k <= 3; k++) {
      const next = plus(subst(d, U), d, -1)
      if (isConst(next)) { if ((next['1'] ?? 0) > 0) return undefined; break } // (a constant > 0: g grows past 0)
      if (canon(next) === canon(d)) break
      opt.push(tight(next)); d = next
    }
  }
  // Houdini: G must be kept by U; a difference not kept is dropped
  let R = dedupe([...G, ...opt])
  const must = new Set(G.map(canon))
  for (let round = 0; round < 12; round++) {
    if (late()) return undefined
    const bad = R.filter(a => !implied(R, subst(a, U)))
    if (!bad.length) break
    if (bad.some(a => must.has(canon(a)))) return undefined
    const drop = new Set(bad.map(canon))
    R = R.filter(a => !drop.has(canon(a)))
  }
  if (R.some(a => !implied(R, subst(a, U))) || !sat(R)) return undefined
  // R without what the rest of it implies (a smaller goal for the kernel)
  R = irredundant(R, late)
  if (late()) return undefined
  // per turn j: R_j, the rest of the cycle from turn j allowed and ending in R
  const Rs: Lin[][] = steps.map((_, j) => {
    if (j === 0) return R
    const rest = compose(rel, steps.slice(j), natState)!
    return irredundant(dedupe([...rest.rows, ...R.map(a => tight(subst(a, rest.post)))].filter(f => !(isConst(f) && (f['1'] ?? 0) <= 0))), late)
  })
  if (late()) return undefined
  if (Rs.some(r => !sat(r))) return undefined
  // as the loop's condition and witness
  const intOf = (x: string) => rel.ints.get(x)
  const term = (f: Lin): {p: E, n: E} => {
    let p: E = K(0), n: E = K(0)
    const add = (e: E, k: number, to: 'p' | 'n') => { const t: E = k === 1 ? e : {op: 'mul', k, a: e}; if (to === 'p') p = isZ(p) ? t : {op: 'add', a: p, b: t}; else n = isZ(n) ? t : {op: 'add', a: n, b: t} }
    for (const x of vars(f).sort()) {
      const c = f[x]!, pair = intOf(x)
      if (pair) { add(V(pair[0]), Math.abs(c), c > 0 ? 'p' : 'n'); add(V(pair[1]), Math.abs(c), c > 0 ? 'n' : 'p') } else add(V(x), Math.abs(c), c > 0 ? 'p' : 'n')
    }
    const k = f['1'] ?? 0
    if (k) add(K(Math.abs(k)), 1, k > 0 ? 'p' : 'n')
    return {p, n}
  }
  const atom = (f: Lin): C => { const t = term(f); return {op: '<=', a: t.p, b: t.n} }
  const conj = (xs: C[]): C => (xs.length === 1 ? xs[0]! : {op: 'and', xs})
  const pcIs = (j: number): C[] => (rel.loc ? [{op: '=', a: V(rel.loc), b: K(from(seq[j]!))}] : [])
  const parts = Rs.map((r, j) => conj([...pcIs(j), ...r.map(atom)]))
  const set: C = parts.length === 1 ? parts[0]! : {op: 'or', xs: parts}
  // the witness: each input of the loop per turn
  const distinctLocs = new Set(seq.map(from)).size === seq.length
  const conds = parts.map((c, j) => (distinctLocs ? conj(pcIs(j).length ? pcIs(j) : [c]) : c))
  const valueAt = (j: number, n: string): E => {
    const p = rel.paths[seq[j]!]!
    if (n in p.pins) return K(p.pins[n]!)
    const u = steps[j]!.ins
    for (const [x, pair] of rel.ints) if (pair[0] === n || pair[1] === n) {
      const t = u[x]
      if (!t) return K(0)
      const v = term(t)
      return pair[0] === n ? sub(v.p, v.n) : sub(v.n, v.p)
    }
    const t = u[n]
    if (!t) return K(0)
    const v = term(t)
    return sub(v.p, v.n)
  }
  const wit: Record<string, E> = {}
  for (const n of l.inputs) {
    const vals = seq.map((_, j) => valueAt(j, n)), keys = vals.map(v => JSON.stringify(v))
    if (keys.every(k => k === keys[0])) { wit[n] = vals[0]!; continue }
    // (the commonest value last, with no condition: a state of any part whose turn takes it matches no other's; a
    // state matched by another part's condition is in that part, whose turn keeps it in the set too)
    const tally = new Map<string, number>()
    for (const k of keys) tally.set(k, (tally.get(k) ?? 0) + 1)
    const common = [...tally].sort((a, b) => b[1] - a[1])[0]![0]
    let e = vals[keys.indexOf(common)]!
    for (let j = vals.length - 1; j >= 0; j--) if (keys[j] !== common) e = {op: 'if', c: conds[j]!, then: vals[j]!, else: e}
    wit[n] = e
  }
  return {set, wit, targets: Rs.map((rows, j) => ({loc: from(seq[j]!), rows}))}
}
const cmp = (a: number[], b: number[]) => { for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return a[i]! - b[i]!; return 0 }
const isZ = (e: E) => e.op === 'const' && e.value === 0
const sub = (a: E, b: E): E => (isZ(b) ? a : isZ(a) ? K(0) : {op: 'sub', a, b})

function irredundant(rows: Lin[], late: () => boolean): Lin[] {
  let out = rows
  for (let i = out.length - 1; i >= 0 && !late(); i--) {
    const rest = out.filter((_, j) => j !== i)
    if (rest.length && implied(rest, out[i]!)) out = rest
  }
  return out
}

// --- stems --------------------------------------------------------------------------------------------------------------
//
// A run from the start into one of the set's parts, found over the relation with its loops accelerated: a path at a
// time from the start's location (each turn's inputs constants still to be chosen, u@k), or a self-loop whose turn is a
// translation x := x + δ (its inputs terms of the state) taken n@k ≥ 1 times at once: its rows at the first and the
// last of those turns (a convex guard holds between them), the state after it x + n·δ, all linear in the params, the
// constants and the counts. Each prefix is pruned where its rows are refuted (core/solver.ts); where a part's rows are
// satisfiable with the prefix's, the model's params, constants and counts are run on the loop itself (`turn`), turn by
// turn: the stem is what that run takes, for the caller to cut where it enters the set and check.
type Env = Record<string, number>
export type StemIO = {start: (params: Env) => Env, turn: (st: Env, input: Env) => Env | undefined}
// `report.exhausted`: the search ran to its end within its time and calls (no part reached within its depth), as opposed
// to not applying (a start it doesn't read linearly) or being cut short.
export function* stemsTo(l: Loop, targets: Target[], io: StemIO, opts: {now: () => number, until: number, depth?: number, calls?: number, report?: {exhausted: boolean}}): Generator<{params: Env, stem: Env[]}> {
  const found = relOf(l)
  if (!found) return
  const rel: Relation = found
  const {now, until} = opts, depth = opts.depth ?? 8
  let calls = opts.calls ?? 400
  const S = rel.state, P = new Set(rel.params), Sset = new Set(S)
  const natState = S.filter(x => !rel.ints.has(x))
  // the params as integers (a pair x, x$n or x$neg is x − x$n), and the start's state over them
  const pairOf = new Map<string, [string, number]>(), paramInts: [string, string | undefined][] = []
  for (const x of l.params) for (const sfx of ['$n', '$neg']) if (l.params.includes(x + sfx)) { pairOf.set(x, [x, 1]); pairOf.set(x + sfx, [x, -1]); paramInts.push([x, x + sfx]) }
  for (const x of l.params) if (!pairOf.has(x)) { pairOf.set(x, [x, 1]); paramInts.push([x, undefined]) }
  const linRaw = (e: E): Lin | undefined => {
    switch (e.op) {
      case 'var': return {[e.name]: 1}
      case 'const': return konst(e.value)
      case 'add': { const a = linRaw(e.a), b = linRaw(e.b); return a && b && plus(a, b) }
      case 'mul': { const a = linRaw(e.a); return a && times(a, e.k) }
      case 'sub': case 'prod': case 'min': case 'max': case 'if': case 'get': return undefined
    }
  }
  const toInts = (raw: Lin): Lin | undefined => {
    const o: Lin = konst(raw['1'] ?? 0), seen = new Map<string, number>()
    for (const r of vars(raw)) {
      const q = pairOf.get(r)
      if (!q) return undefined
      const c = raw[r]! * q[1]
      if (seen.has(q[0]) && seen.get(q[0]) !== c) return undefined
      seen.set(q[0], c)
    }
    for (const [x, c] of seen) {
      const pair = paramInts.find(p => p[0] === x)!
      // (a pair read whole: both parts, opposite; one part alone is not the integer)
      if (pair[1] && vars(raw).filter(r => pairOf.get(r)?.[0] === x).length !== 2) return undefined
      o[x] = c
    }
    return o
  }
  const startOf = (x: string): Lin | undefined => {
    const pair = rel.ints.get(x)
    if (!pair) { const e = l.state[x]; const r = e && linRaw(e); return r && toInts(r) }
    const ep = l.state[pair[0]], en = l.state[pair[1]]
    if (!ep || !en) return undefined
    if (ep.op === 'sub' && en.op === 'sub' && JSON.stringify(ep.a) === JSON.stringify(en.b) && JSON.stringify(ep.b) === JSON.stringify(en.a)) {
      const a = linRaw(ep.a), b = linRaw(ep.b)
      return a && b && toInts(plus(a, b, -1))
    }
    const a = linRaw(ep), b = linRaw(en)
    return a && b && toInts(plus(a, b, -1))
  }
  const sigma0: Record<string, Lin> = {}
  for (const x of S) { const v = startOf(x); if (!v) return; sigma0[x] = v }
  const locE = rel.loc ? l.state[rel.loc] : undefined
  if (rel.loc && locE?.op !== 'const') return
  const startLoc = locE?.op === 'const' ? locE.value : 0
  const from = (i: number) => (rel.loc ? rel.from[i]! : 0), to = (i: number) => (rel.loc ? rel.to[i]! : 0)
  // the self-loops that are translations, with their inputs as terms
  type Loopy = {path: number, ins: Ins, delta: Lin}
  const loops = new Map<number, Loopy[]>()
  rel.paths.forEach((p, i) => {
    if (from(i) !== to(i)) return
    for (const ins of inputChoices(p, Sset, P)) {
      const c = compose(rel, [{path: i, ins}], natState)
      if (!c) continue
      const delta: Lin = {}
      let ok = true
      for (const x of S) { const d = plus(c.post[x]!, {[x]: 1}, -1); if (!isConst(d)) { ok = false; break } if (d['1']) delta[x] = d['1'] }
      if (ok && Object.keys(delta).length) { loops.set(from(i), [...(loops.get(from(i)) ?? []), {path: i, ins, delta}]); break }
    }
  })
  const natParams = paramInts.filter(p => !p[1]).map(p => p[0])
  type Seg = {path: number, ins: Ins, n?: string}
  const solveRows = (rows: Lin[]) => { calls--; return solve(rows.map(lin => ({lin, label: ''})), 3000) }
  const evalLin = (f: Lin, env: Env, w: Env) => {
    let v = f['1'] ?? 0
    for (const x of vars(f)) { const pair = rel.ints.get(x); v += f[x]! * (x.includes('@') ? (w[x] ?? 0) : pair ? (env[pair[0]] ?? 0) - (env[pair[1]] ?? 0) : (env[x] ?? 0)) }
    return v
  }
  const rawInput = (p: Path, ins: Ins, env: Env, w: Env): Env => {
    const out: Env = {}
    for (const n of l.inputs) out[n] = 0
    for (const [u, t] of Object.entries(ins)) {
      const v = Math.round(evalLin(t, env, w)), pair = rel.ints.get(u)
      if (pair) { out[pair[0]] = Math.max(v, 0); out[pair[1]] = Math.max(-v, 0) } else out[u] = Math.max(v, 0)
    }
    for (const [n, v] of Object.entries(p.pins)) if (l.inputs.includes(n)) out[n] = v
    return out
  }
  const concrete = (segs: Seg[], w: Env): {params: Env, stem: Env[]} | undefined => {
    const params: Env = {}
    for (const [x, neg] of paramInts) { const v = Math.round(w[x] ?? 0); if (neg) { params[x] = Math.max(v, 0); params[neg] = Math.max(-v, 0) } else params[x] = Math.max(v, 0) }
    let st = io.start(params)
    const stem: Env[] = []
    let left = 200_000
    for (const s of segs) {
      const times = s.n ? Math.round(w[s.n] ?? 1) : 1
      if (times > 100_000) return undefined
      for (let k = 0; k < times; k++) {
        if (--left < 0) return undefined
        const input = rawInput(rel.paths[s.path]!, s.ins, st, w), nx = io.turn(st, input)
        if (!nx) return undefined
        stem.push(input); st = nx
      }
    }
    return {params, stem}
  }
  const base = natParams.map(x => ({[x]: -1}) as Lin)
  // each location's distance (in turns) to a part of the set: the search goes nearest first, and no further than the
  // depth allows
  const dist = new Map<number, number>(targets.map(t => [t.loc, 0]))
  for (let changed = true; changed;) {
    changed = false
    for (let i = 0; i < rel.paths.length; i++) { const d = dist.get(to(i)); if (d !== undefined && (dist.get(from(i)) ?? Infinity) > d + 1) { dist.set(from(i), d + 1); changed = true } }
  }
  if (!dist.has(startLoc)) { if (opts.report) opts.report.exhausted = true; return }
  const maxDepth = Math.max(depth, dist.get(startLoc)! + depth)
  const outs = new Map<number, number[]>()
  for (let i = 0; i < rel.paths.length; i++) if (dist.has(to(i))) outs.set(from(i), [...(outs.get(from(i)) ?? []), i])
  for (const xs of outs.values()) xs.sort((a, b) => dist.get(to(a))! - dist.get(to(b))!)
  function* dfs(loc: number, sigma: Record<string, Lin>, rows: Lin[], segs: Seg[], k: number, lastLoop: boolean): Generator<{params: Env, stem: Env[]}> {
    if (calls <= 0 || now() > until) return
    for (const t of targets) if (t.loc === loc) {
      const m = solveRows([...rows, ...t.rows.map(f => subst(f, sigma))])
      if (m.kind === 'sat') { const c = concrete(segs, m.witness); if (c) yield c }
    }
    if (segs.length + (dist.get(loc) ?? Infinity) > maxDepth) return
    const step = (i: number, ins: Ins, n?: {name: string, delta: Lin}) => {
      const p = rel.paths[i]!
      const insAt = Object.fromEntries(Object.entries(ins).map(([u, t]) => [u, subst(t, sigma)]))
      const sub = {...sigma, ...insAt}
      const rs = [...p.rows.map(f => subst(f, sub)), ...natState.map(x => times(sigma[x]!, -1)), ...Object.keys(insAt).filter(u => !rel.ints.has(u)).map(u => times(insAt[u]!, -1))]
      let post: Record<string, Lin>
      if (n) {
        // the last turn's rows: at sigma + (n − 1)·δ
        const last = Object.fromEntries(S.map(x => [x, plus(plus(sigma[x]!, times({[n.name]: 1}, n.delta[x] ?? 0)), konst(-(n.delta[x] ?? 0)))]))
        const insLast = Object.fromEntries(Object.entries(ins).map(([u, t]) => [u, subst(t, last)]))
        rs.push(...p.rows.map(f => subst(f, {...last, ...insLast})), ...natState.map(x => times(last[x]!, -1)), plus(konst(1), {[n.name]: -1}))
        post = Object.fromEntries(S.map(x => [x, plus(sigma[x]!, times({[n.name]: 1}, n.delta[x] ?? 0))]))
      } else post = Object.fromEntries(S.map(x => [x, subst(p.post[x] ?? {[x]: 1}, sub)]))
      return {rs, post}
    }
    // a self-loop accelerated, then each path out
    if (!lastLoop) for (const lp of loops.get(loc) ?? []) {
      const name = `n@${k}`, {rs, post} = step(lp.path, lp.ins, {name, delta: lp.delta})
      const all = [...rows, ...rs]
      if (solveRows(all).kind === 'refuted') continue
      yield* dfs(loc, post, all, [...segs, {path: lp.path, ins: lp.ins, n: name}], k + 1, true)
    }
    for (const i of outs.get(loc) ?? []) {
      if (segs.length + 1 + dist.get(to(i))! > maxDepth) continue
      const p = rel.paths[i]!, ins: Ins = {}
      for (const [u, t] of Object.entries(symbolic(p, k, Sset, P))) ins[u] = Object.fromEntries(Object.entries(t).map(([x, c]) => [x.includes('@') ? x.replace(/@\d+$/, `@${k}`) : x, c]))
      const {rs, post} = step(i, ins)
      const all = [...rows, ...rs]
      if (all.some(big) || solveRows(all).kind === 'refuted') continue
      yield* dfs(to(i), post, all, [...segs, {path: i, ins}], k + 1, false)
    }
  }
  yield* dfs(startLoc, sigma0, [...base], [], 0, false)
  if (opts.report && calls > 0 && now() <= until) opts.report.exhausted = true
}
