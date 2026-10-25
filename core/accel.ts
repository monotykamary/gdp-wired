// Accelerated cycles: recurrent sets from a loop's relation, not its runs, and stems into them from runs whose loops are
// taken n times at once. Untrusted, like core/nonterm.ts, whose search calls this: what is found here is a candidate
// set, its witness and a stem, and the kernel proves the set closed and the stem into it (kernel.ts's checkRecur,
// NonTerm.lean's never_ends_of).
//
// - Cycles. The relation's paths (core/relation.ts: one turn as linear paths, each from a location to a location) as a
//   graph; its closed walks (a location may come twice: x > 0 and x < 0 taken in turn), each by its least rotation, by
//   how many choices they make among a location's paths (at most `maxLen`; a chain of locations with one path out, as a
//   translated program's straight-line code, costs nothing) and at most 64 turns, a walk cut where its rows (each turn's
//   inputs left open) are refuted; a self-loop also twice over (a period of two: x := −x). An inner loop (a self-loop,
//   or a cycle of two turns, whose turn is a translation with a metering function: `accelerate`) is one more choice at
//   its location, taken to its end at once: its count the metering function's value, linear in the state. Then the
//   cycles the random runs take, between two visits of a location, the commonest first.
// - A turn's inputs as terms of the state before it: a value a row pins (an equation in it), else a bound a row puts on
//   it (x < i0 gives i0 := x + 1, i0 >= 3 gives 3), else 0; or constants from a model of two rounds of the cycle; or a
//   bound the rest of the cycle puts on it (`lookahead`). The cycle is then one linear loop: its guard G (each turn's
//   rows, read at the state the turns before it leave) and its update U (affine in the state at the cycle's start).
// - Its n-fold run in closed form (the engine below): an atom g ≤ 0 of G holds after every number n of turns where its
//   value along the run, g(Uⁿx), a polynomial in n for a translation or a triangular update, has its differences at
//   n = 0 all ≤ 0: Δ⁰g = g, Δ^{k+1}g = Δ^k g∘U − Δ^k g, each linear in x (Σ C(n, k)·Δ^k g is g(Uⁿx)). For a geometric
//   update (x := 2x) the differences repeat (Δ²g = Δ¹g) and the same set holds. So the set R is G with each atom's
//   differences up to degree 3, and Houdini drops a difference that isn't kept by U (G's atoms are kept or the cycle is
//   given up): R ∧ ¬a(Ux) refuted for each atom a, by the integer solver (core/solver.ts). A constant difference above 0
//   gives the cycle up at once: g grows past 0.
// - The set of the loop: per step j of the cycle, at its location, the states from which the rest of the cycle's steps
//   are allowed and end in R (R_j, the weakest precondition: the rest composed; an inner loop's at each of its turns);
//   the witness by location, or by R_j where the cycle passes a location twice, its commonest value with no condition.
// - Products with a turn's input (x·u, which the relation leaves out): the loop's cases with x fixed (`fixedCases`), the
//   set holding x so.
// - Stems (`stemsTo`): from the start's location to a part's, a path at a time or a self-loop with a closed form taken
//   many times at once (a translation n times, any other 2 to 16), all linear, then run on the loop itself; `deepen`
//   searches again at twice and four times the depth.
import {type C, type E, n as K, x as V} from './machine.ts'
import type {Loop} from '../kernel/kernel.ts'
import {type Path, type Relation, relationOf} from './relation.ts'
import {type Lin, canon, gcd, konst, linOfE, plus, solve, subst, times, vars} from './solver.ts'
import {type Rat, Q0, Q1, bgcd, q, qadd, qdiv, qmul, qsub} from './q.ts'

// --- closed forms -------------------------------------------------------------------------------------------------------
//
// The one engine for what a loop does after n turns (discover's closed forms, the cycles' differences, the stems' and the
// inner loops' n-fold turns): a sequence of linear forms v₀, v₁, … (a form g read after n turns of an affine update U,
// g(Uⁿx), or the numbers a function's values are) as Σ c·C(n, k)·rⁿ over the integer roots r of the shortest linear
// recurrence every given term meets, each root to its multiplicity (rⁿ read as [n = k] at r = 0), each c a linear form
// over the rationals, written with integer coefficients over `den`. Undefined where the recurrence is longer than
// `order` or its characteristic polynomial has a root that isn't an integer (Fibonacci's). A translation's forms have
// the root 1 (k ≤ 1: linear in n), a polynomial update's 1 to the degree, a triangular system's its diagonal's, a
// geometric one (x := 2·x) its ratio; a form of an affine update meets its recurrence everywhere once it meets it at the
// first terms (`exact`), numbers only where every window of them does.
export type ClosedForm = {terms: {r: number, k: number, c: Lin}[], den: number}
type QV = Map<string, Rat>
const qv = (l: Lin): QV => new Map(Object.entries(l).filter(([, c]) => c).map(([x, c]) => [x, q(c)]))
const qvAdd = (a: QV, b: QV, f: Rat): QV => { const o = new Map(a); for (const [x, c] of b) { const s = qadd(o.get(x) ?? Q0, qmul(c, f)); if (s.num) o.set(x, s); else o.delete(x) } return o }
// The unknowns of A·u = B (each right-hand side a form), by elimination over the rationals; undefined where they aren't
// one solution.
function solveQ(A: Rat[][], B: QV[], m: number): QV[] | undefined {
  const rows = A.map((r, i) => ({a: [...r], b: B[i]!})), piv: number[] = []
  let at = 0
  for (let j = 0; j < m; j++) {
    const p = rows.findIndex((r, i) => i >= at && r.a[j]!.num !== 0n)
    if (p < 0) return undefined
    const r = rows[p]!
    rows[p] = rows[at]!; rows[at] = r
    const inv = qdiv(Q1, r.a[j]!)
    r.a = r.a.map(x => qmul(x, inv)); r.b = qvAdd(new Map(), r.b, inv)
    for (const [i, o] of rows.entries()) if (i !== at && o.a[j]!.num !== 0n) { const f = o.a[j]!; o.a = o.a.map((x, c) => qsub(x, qmul(f, r.a[c]!))); o.b = qvAdd(o.b, r.b, qsub(Q0, f)) }
    piv.push(at++)
  }
  return rows.slice(at).every(r => r.b.size === 0) ? piv.map(i => rows[i]!.b) : undefined
}
const choose = (n: number, k: number): bigint => { let c = 1n; for (let i = 0; i < k; i++) c = c * BigInt(n - i) / BigInt(i + 1); return c }
const basis = (r: number, k: number, n: number): Rat => (r === 0 ? (n === k ? Q1 : Q0) : q(choose(n, k) * BigInt(r) ** BigInt(n)))
// The integer roots of Σ P[i]·tⁱ to their multiplicities, all of them, or undefined.
function intRoots(P: bigint[]): {r: number, mult: number}[] | undefined {
  let p = [...P]
  const out: {r: number, mult: number}[] = []
  const take = (r: bigint): boolean => {
    const n = p.length - 1, b: bigint[] = new Array(n)
    let acc = 0n
    for (let i = n; i >= 1; i--) { acc = acc * r + p[i]!; b[i - 1] = acc }
    if (acc * r + p[0]! !== 0n) return false
    p = b
    const e = out.find(x => x.r === Number(r))
    if (e) e.mult++; else out.push({r: Number(r), mult: 1})
    return true
  }
  while (p.length > 1 && p[0] === 0n) take(0n)
  const c = p[0]! < 0n ? -p[0]! : p[0]!
  if (p.length > 1 && c > 10n ** 12n) return undefined
  for (let d = 1n; p.length > 1 && d * d <= c; d++) {
    if (c % d) continue
    for (const r of [d, -d, c / d, -c / d]) while (p.length > 1 && take(r));
  }
  return p.length === 1 && out.every(x => Math.abs(x.r) <= 2 ** 20) ? out : undefined
}
export function closedForm(terms: Lin[], exact: boolean, order = 6): ClosedForm | undefined {
  const vs = terms.map(qv)
  if (vs.every(v => v.size === 0)) return {terms: [], den: 1}
  for (let m = 1; m <= order; m++) {
    const windows = exact ? 1 : vs.length - 2 * m
    if (vs.length < m + 1 || windows < 1) return undefined
    // v[n + m] = Σ a_i·v[n + i], each coordinate of each window an equation
    const A: Rat[][] = [], B: QV[] = []
    for (let n = 0; n < (exact ? 1 : vs.length - m); n++) for (const x of new Set(vs.slice(n, n + m + 1).flatMap(v => [...v.keys()]))) {
      A.push(vs.slice(n, n + m).map(v => v.get(x) ?? Q0)); B.push(new Map([['1', vs[n + m]!.get(x) ?? Q0]]))
    }
    const a = solveQ(A, B.map(b => new Map([...b].filter(([, c]) => c.num))), m)
    if (!a) continue
    // tᵐ − Σ a_i·tⁱ over the integers
    const as = a.map(f => f.get('1') ?? Q0), L = as.reduce((l, x) => l / bgcd(l, x.den) * x.den, 1n)
    const roots = intRoots([...as.map(x => -x.num * (L / x.den)), L])
    if (!roots) return undefined
    const bs = roots.flatMap(({r, mult}) => Array.from({length: mult}, (_, k) => ({r, k})))
    const c = solveQ(Array.from({length: m}, (_, n) => bs.map(b => basis(b.r, b.k, n))), vs.slice(0, m), m)
    if (!c) return undefined
    let den = 1n
    for (const f of c) for (const x of f.values()) den = den / bgcd(den, x.den) * x.den
    const out: ClosedForm['terms'] = []
    for (const [j, f] of c.entries()) {
      const l: Lin = {}
      for (const [x, y] of f) { const v = Number(y.num * (den / y.den)); if (!Number.isSafeInteger(v)) return undefined; l[x] = v }
      if (Object.keys(l).length) out.push({...bs[j]!, c: l})
    }
    return Number.isSafeInteger(Number(den)) ? {terms: out, den: Number(den)} : undefined
  }
  return undefined
}
// g, g∘U, g∘U², … (count of them)
export const iterates = (g: Lin, U: Record<string, Lin>, count: number): Lin[] => { const out = [g]; while (out.length < count) out.push(subst(out.at(-1)!, U)); return out }
// g(Uⁿx) in closed form
export const nfold = (g: Lin, U: Record<string, Lin>, order = 6): ClosedForm | undefined => closedForm(iterates(g, U, order + 1), true, order)
// A closed form that is a polynomial in n: its coefficients by k in the binomial basis C(n, k) (over den), or undefined.
export const polyOf = (f: ClosedForm): Lin[] | undefined => {
  if (f.terms.some(t => t.r !== 1)) return undefined
  const out: Lin[] = []
  for (const t of f.terms) out[t.k] = t.c
  return Array.from({length: out.length}, (_, k) => out[k] ?? {})
}
// A closed form at a count n: a linear form (over the rationals where den doesn't divide it; a form of integer iterates
// is integral).
export const closedAt = (f: ClosedForm, n: number): Lin => {
  let o: Lin = {}
  for (const t of f.terms) o = plus(o, times(t.c, Number(basis(t.r, t.k, n).num)))
  return times(o, 1 / f.den)
}
// A loop's n-fold turn where it is a translation (every state form's closed form linear in n, so the turns are x + n·δ)
// and its guard G (rows over the turn's start) holds on an interval: each atom of G is linear in n along the turns, so
// it holds at every turn from 0 to n − 1 where it holds at the first and the last (conditional acceleration). And its
// metering function: where an atom a of G rises by exactly 1 a turn (a(x + δ) = a(x) + 1), the guard fails after
// 1 − a(x) turns at most, exactly that many where the rest of G holds throughout: the count, linear in x.
export type Accel = {delta: Record<string, number>, meter?: Lin}
export function accelerate(G: Lin[], U: Record<string, Lin>, S: string[]): Accel | undefined {
  const delta: Record<string, number> = {}
  for (const x of S) {
    const f = nfold({[x]: 1}, U, 2), p = f && polyOf(f)
    if (!p || p.length > 2 || f!.den !== 1 || vars(p[1] ?? {}).length) return undefined
    if (p[1]?.['1']) delta[x] = p[1]['1']
  }
  if (!Object.keys(delta).length) return undefined
  const rise = (a: Lin) => vars(a).reduce((s, x) => s + a[x]! * (delta[x] ?? 0), 0)
  const m = G.find(a => rise(a) === 1)
  return {delta, ...(m ? {meter: plus(konst(1), m, -1)} : {})}
}

// `targets`: the set's parts, each a location and its rows over the relation's names (R_j), for a stem's search.
export type Target = {loc: number, rows: Lin[]}
// `cases`: the set's parts, each at its location (the location's variable pinned) with its rows, for a closure by cases.
export type Accelerated = {set: C, wit: Record<string, E>, cycle: number[], locs: number[], targets: Target[], cases?: {pins: [string, number][], cond: C}[]}

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
// `until` is read each time (a getter may move it: the caller's time spent on a candidate need not count against the
// search for the next one).
export type AccelOptions = {now: () => number, until: number, maxLen?: number, maxCycles?: number, runs?: {params: Record<string, number>, inputs: Record<string, number>[]}[], io?: StemIO}

// The candidates, one at a time (a generator: the caller tries each against the kernel and stops when one is proven):
// the relation's cycles, then those of its cases where a state value that a product reads with a turn's input is fixed
// (`fixedCases`), which have 30% of the time where there are any.
export function* accelerated(l: Loop, opts: AccelOptions): Generator<Accelerated> {
  const rel = relOf(l), fixed = fixedCases(l), {now} = opts, t0 = now()
  if (rel) yield* cyclesOf(l, rel, fixed.length ? {...opts, get until() { return t0 + (opts.until - t0) * 0.7 }} : opts, [])
  for (const f of fixed) { if (now() > opts.until) return; yield* cyclesOf(l, f.rel, {now, get until() { return opts.until }, ...(opts.maxLen ? {maxLen: opts.maxLen} : {})}, f.pins) }
}
// (`pins`: rows every part of the set keeps, the fixed values of a case)
function* cyclesOf(l: Loop, rel: Relation, opts: AccelOptions, pins: Lin[]): Generator<Accelerated> {
  const {now} = opts, maxLen = opts.maxLen ?? 6
  const S = rel.state, P = new Set(rel.params), Sset = new Set(S), NP = rel.paths.length
  const natState = S.filter(x => !rel.ints.has(x))
  // Each path's inputs as terms of the state before it (a few choices each, the first the likeliest).
  const choices = rel.paths.map(p => inputChoices(p, Sset, P))
  const from = (i: number) => (i >= NP ? loops[i - NP]!.loc : rel.loc ? rel.from[i]! : 0), to = (i: number) => (i >= NP ? loops[i - NP]!.loc : rel.loc ? rel.to[i]! : 0)
  const loops: Inner[] = []
  // The cycles: closed walks of paths (a location may come twice: two turns at one location, taken in turn), each once
  // (its least rotation), with at most `maxLen` choices among a location's paths (a chain of locations with one path out,
  // as a translated program's straight-line code, is free) and at most 64 turns; the shortest first.
  // (`fewest`: the fewest choices a walk makes, so a deeper search finds only walks the first didn't)
  const enumerate = (ids: number, fewest = 0, upTo = maxLen, cap = opts.maxCycles ?? 400): number[][] => {
  let cycles: number[][] = []
  // (those with an inner loop counted out apart, at most 60, after the rest)
  const counted: number[][] = []
  const byFrom = new Map<number, number[]>()
  for (let i = 0; i < ids; i++) { const f = from(i); byFrom.set(f, [...(byFrom.get(f) ?? []), i]) }
  const least = (seq: number[]) => seq.every((_, r) => r === 0 || cmp(seq, [...seq.slice(r), ...seq.slice(0, r)]) < 0)
  // (a turn costs 1 at a location of more than one path, 0 else; each location's least cost back to the cycle's start,
  // so a walk that can't come back within the budget is cut)
  const costAt = (loc: number) => ((byFrom.get(loc) ?? []).length > 1 ? 1 : 0)
  const back = (start: number): Map<number, number> => {
    const d = new Map<number, number>([[start, 0]]), queue = [start]
    while (queue.length) {
      const y = queue.shift()!
      for (let i = 0; i < NP; i++) {
        if (to(i) !== y) continue
        const x = from(i), c = d.get(y)! + costAt(x)
        if (c < (d.get(x) ?? Infinity)) { d.set(x, c); if (costAt(x)) queue.push(x); else queue.unshift(x) }
      }
    }
    return d
  }
  const backs = new Map<number, Map<number, number>>()
  // (a self-loop that counts a value by ±1 towards a bound its rows put on it)
  const counters = new Map<number, {x: string, delta: number, lo?: number, hi?: number} | undefined>()
  const counter = (j: number) => {
    if (counters.has(j)) return counters.get(j)
    const p = rel.paths[j]!, bounds = boundsOf(p.rows)
    let out: {x: string, delta: number, lo?: number, hi?: number} | undefined
    for (const x of S) {
      const e = p.post[x], delta = e?.['1'] ?? 0, b = bounds.get(x)
      if (!e || vars(e).length !== 1 || e[x] !== 1 || Math.abs(delta) !== 1 || (delta > 0 ? b?.hi : b?.lo) === undefined) continue
      out = {x, delta, ...(b!.lo !== undefined ? {lo: b!.lo} : {}), ...(b!.hi !== undefined ? {hi: b!.hi} : {})}
      break
    }
    counters.set(j, out)
    return out
  }
  // (each walk's turns composed with their inputs left open, u@k: a walk whose rows are refuted is cut where it chose; an
  // inner loop with its own inputs)
  const open = (sigma: Record<string, Lin>, i: number, k: number) => (i >= NP ? stepTurn(rel, natState, {inner: loops[i - NP]!}, sigma) : turn(rel, natState, i, sigma, symbolic(rel.paths[i]!, k, Sset, P), k))
  const id0: Record<string, Lin> = Object.fromEntries(S.map(x => [x, {[x]: 1}]))
  let nodes = 20_000
  for (let budget = fewest; budget <= upTo && cycles.length < cap && nodes > 0; budget++) {
    for (let i = 0; i < NP && cycles.length < cap && nodes > 0 && now() < opts.until; i++) {
      const s0 = from(i)
      if (!backs.has(s0)) backs.set(s0, back(s0))
      const d = backs.get(s0)!
      // (`inner`: the self-loop just taken as many times as its rows allow, not taken again at once)
      const walk = (seq: number[], at: number, cost: number, sigma: Record<string, Lin>, rows: Lin[], inner?: number) => {
        if (--nodes < 0 || cycles.length >= cap || now() > opts.until) return
        if (at === s0 && cost === budget && least(seq) && sat(rows)) { if (!seq.some((x, q) => q > 0 && x === seq[q - 1] && to(x) === from(x) && x < NP)) cycles.push(seq); else if (counted.length < 60) counted.push(seq) }
        if (seq.length >= 64) return
        const c = cost + costAt(at)
        if (c + (d.get(at) ?? Infinity) - costAt(at) > budget || c > budget) return
        for (const j of byFrom.get(at) ?? []) {
          if (j === inner || j < seq[0]! || (j >= NP && j === seq.at(-1)) || c + (d.get(to(j)) ?? Infinity) > budget) continue
          const {rs, post} = open(sigma, j, seq.length), all = [...rows, ...rs]
          if (all.some(big) || (costAt(at) && !sat(all))) continue
          walk([...seq, j], to(j), c, post, all)
          // An inner loop: a self-loop that counts x by ±1 up or down to a bound of its rows, from a value the walk has
          // set (x := 0, then x := x + 1 while x < 12: KnapsackDP's), taken as many times as that, as one choice, where
          // that is 2 to 24 times; the walk goes on from there.
          const cl = j < NP && to(j) === at && j !== seq.at(-1) && counted.length < 60 ? counter(j) : undefined, k0 = cl && sigma[cl.x]
          if (cl && k0 && isConst(k0)) {
            const k = k0['1'] ?? 0, r = cl.delta > 0 ? (cl.hi ?? -Infinity) - k + 1 : k - (cl.lo ?? Infinity) + 1
            if (r >= 2 && r <= 24 && seq.length + r < 64) {
              let sg = sigma, rws = rows
              for (let q = 0; q < r; q++) { const more = open(sg, j, seq.length + q); sg = more.post; rws = [...rws, ...more.rs] }
              nodes--
              if (!rws.some(big) && sat(rws)) walk([...seq, ...Array.from({length: r}, () => j)], at, c, sg, rws, j)
            }
          }
        }
      }
      const c0 = costAt(s0), first = open(id0, i, 0)
      if (c0 + (d.get(to(i)) ?? Infinity) <= budget && sat(first.rs)) walk([i], to(i), c0, first.post, first.rs)
    }
  }
  cycles = cycles.sort((x, y) => x.length - y.length).slice(0, cap)
  return [...cycles.filter(c => c.length <= 6), ...counted.sort((x, y) => x.length - y.length), ...cycles.filter(c => c.length > 6)]
  }
  let cycles = enumerate(NP)
  // the runs' cycles: between two visits of a location, the paths taken (as their least rotation), by how often; after
  // the enumerated ones of at most 4 turns (at most 20,000 turns read)
  if (opts.runs && opts.io) {
    const count = new Map<string, {seq: number[], n: number}>()
    const byLoc = new Map<number, number[]>()
    rel.paths.forEach((_, i) => { byLoc.set(from(i), [...(byLoc.get(from(i)) ?? []), i]) })
    let budget = 20_000
    for (const r of opts.runs) {
      if (now() > opts.until || budget <= 0) break
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
  const stepOf = (pi: number, ins: Ins): Step => (pi >= NP ? {inner: loops[pi - NP]!} : {path: pi, ins})
  // (`look`: the lookahead's choices too, or only them)
  const tryAll = function* (cycs: number[][], look: 'no' | 'only' | 'yes'): Generator<Accelerated> {
    for (const cyc0 of cycs) {
      // (a cycle with a product: its turn first, where its product is read at the cycle's start; one such turn at most)
      const prodAt = cyc0.flatMap((pi, j) => (pi < NP && readsPi(rel.paths[pi]!) ? [j] : []))
      if (prodAt.length > 1) continue
      const cyc = prodAt.length ? [...cyc0.slice(prodAt[0]!), ...cyc0.slice(0, prodAt[0]!)] : cyc0
      for (const reps of cyc.length === 1 && !prodAt.length ? [1, 2] : [1]) {
        const seq = Array.from({length: reps}, () => cyc).flat()
        const firsts = seq.map(pi => (pi >= NP ? {} : choices[pi]![0]!))
        // the choices of inputs: constants from a model of two rounds of the cycle (the constants the same in each), then
        // each path's first choice of terms, then one path at a time its others, then one input at a time a bound the rest
        // of the cycle puts on it (`lookahead`)
        const sets: Ins[][] = []
        if (look === 'only') sets.push(...lookahead(rel, seq.map((pi, j) => stepOf(pi, firsts[j]!)), natState, Sset, P))
        else {
          const sym = seq.map((pi, j) => (pi >= NP ? {} : symbolic(rel.paths[pi]!, j, Sset, P)))
          if (sym.some(x => Object.values(x).some(t => vars(t).some(v => v.includes('@'))))) {
            const two = compose(rel, [...seq, ...seq].map((pi, j) => stepOf(pi, sym[j % seq.length]!)), natState)
            const m = two && solve(two.rows.map(lin => ({lin, label: ''})), 3000)
            if (m && m.kind === 'sat') sets.push(sym.map(x => Object.fromEntries(Object.entries(x).map(([u, t]) => [u, subst(t, Object.fromEntries(vars(t).filter(v => v.includes('@')).map(v => [v, konst(Math.round(m.witness[v] ?? 0))])))]))))
          }
          sets.push(firsts)
          seq.forEach((pi, j) => { if (pi < NP) for (let c = 1; c < choices[pi]!.length; c++) sets.push(seq.map((qi, k) => (k === j ? choices[pi]![c]! : firsts[k]!))) })
          if (look === 'yes') sets.push(...lookahead(rel, seq.map((pi, j) => stepOf(pi, firsts[j]!)), natState, Sset, P))
        }
        for (const ins of sets) {
          if (now() > opts.until) return
          const key = `${seq.join(',')}|${JSON.stringify(ins)}`
          if (tried.has(key)) continue
          tried.add(key)
          const out = candidate(rel, seq.map((pi, j) => stepOf(pi, ins[j]!)), natState, l, () => now() > opts.until, pins)
          if (out) yield {...out, cycle: seq, locs: seq.map(from)}
        }
      }
    }
  }
  // The relation's cycles, then the cycles with an inner loop taken to its end, then the lookahead's choices on the first
  yield* tryAll(cycles, 'no')
  if (now() > opts.until) return
  // The inner loops: a self-loop or a cycle of two turns at a location whose turn, with its inputs' choices, is a
  // translation with a metering function (core/accel.ts's `accelerate`), taken to its end as one step of a walk; each
  // named NP + k among the paths.
  let tries = 2000
  for (let i = 0; i < NP && loops.length < 40 && tries > 0 && now() < opts.until; i++) {
    const at = rel.loc ? rel.from[i]! : 0
    if (readsPi(rel.paths[i]!)) continue
    const tails = rel.loc && rel.to[i] !== at ? rel.paths.flatMap((_, j) => (rel.from[j] === rel.to[i] && rel.to[j] === at && j !== i ? [j] : [])) : []
    for (const ps of [...(!rel.loc || rel.to[i] === at ? [[i]] : []), ...tails.map(j => [i, j])]) {
      if (ps.some(j => readsPi(rel.paths[j]!))) continue
      const combos: Ins[][] = ps.length === 1 ? choices[i]!.map(c => [c]) : choices[i]!.flatMap(a => choices[ps[1]!]!.map(b => [a, b]))
      for (const ins of combos.slice(0, 9)) {
        if (--tries < 0) break
        const c = compose(rel, ps.map((path, j) => ({path, ins: ins[j]!})), natState), a = c && accelerate(c.rows, c.post, S)
        if (c && a?.meter && sat(c.rows)) { loops.push({loc: at, paths: ps, ins, rows: c.rows, acc: {delta: a.delta, meter: a.meter}}); break }
      }
    }
  }
  if (loops.length) yield* tryAll(enumerate(NP + loops.length).filter(c => c.some(i => i >= NP)), 'yes')
  if (now() < opts.until) yield* tryAll(cycles, 'only')
  // Deeper, in the time left: walks of up to 16 choices, at most 5,000 of them (hqr's cycle of 25 turns makes 16), each
  // tried with its first inputs.
  if (now() < opts.until && maxLen < DEEP) yield* tryAll(enumerate(NP, maxLen + 1, DEEP, 5000), 'no')
}
const DEEP = 16
// The choices one input at a time of a turn's that the rest of the cycle bounds: the cycle from that turn on (its other
// inputs as chosen), the bounds its rows put on the input, as terms of the state at that turn (x ≤ u gives x), the
// first three that leave the rows satisfiable; at most 12.
function lookahead(rel: Relation, steps: Step[], natState: string[], S: Set<string>, P: Set<string>): Ins[][] {
  const out: Ins[][] = []
  for (const [j, s] of steps.entries()) {
    if (!('path' in s)) continue
    for (const u of inputsOf(rel.paths[s.path]!, S, P)) {
      if (out.length >= 12) return out
      const name = `${u}@look`, rot = [{path: s.path, ins: {...s.ins, [u]: {[name]: 1}}}, ...steps.slice(j + 1), ...steps.slice(0, j)]
      const c = compose(rel, rot, natState)
      if (!c) continue
      const {bounds} = optionsFor(c.rows, name, x => S.has(x) || P.has(x))
      const ok = unique(bounds).filter(t => sat(c.rows.map(f => subst(f, {[name]: t}))))
      for (const t of ok.slice(0, 3)) out.push(steps.map((x, k) => (k === j ? {...s.ins, [u]: t} : 'path' in x ? x.ins : {})))
    }
  }
  return out
}

// The path a turn takes: its pins (the location, the rule) and its rows hold at the state and the turn's inputs.
function pathAt(rel: Relation, among: number[], st: Record<string, number>, input: Record<string, number>): number | undefined {
  const at = {...st, ...input}
  const value = (x: string) => { if (isPi(x)) return piValue(rel, x, at); const pair = rel.ints.get(x); return pair ? (at[pair[0]] ?? 0) - (at[pair[1]] ?? 0) : (at[x] ?? 0) }
  for (const i of among) {
    const p = rel.paths[i]!
    if (Object.entries(p.pins).some(([n, v]) => !n.endsWith('′') && n in at && at[n] !== v)) continue
    if (p.rows.every(f => vars(f).reduce((s, x) => s + f[x]! * value(x), f['1'] ?? 0) <= 0)) return i
  }
  return undefined
}
// (the relation as built, products and all, and as kept: each built once a loop)
const raws = new WeakMap<Loop, Relation | undefined>(), rels = new WeakMap<Loop, Relation | undefined>()
const rawOf = (l: Loop): Relation | undefined => { if (!raws.has(l)) raws.set(l, relationOf(l)); return raws.get(l) }
// The loop's relation and its cases with a value fixed, built (once a loop): a caller may build them before the search,
// and not count the time against it.
export const relationBuilt = (l: Loop): boolean => { relOf(l); fixedCases(l); return !!rels.get(l) }
function relOf(l: Loop): Relation | undefined {
  if (!rels.has(l)) rels.set(l, kept(l, rawOf(l)))
  return rels.get(l)
}
// (a path that reads a product, which the relation stands for by a natural of its own, is kept where each product is
// of two values of the state or params, x := x·y: a cycle may take it as its first turn, the product read at the
// cycle's start (`piFacts`); a product of a turn's input is left out. The kernel checks what is found against the loop
// itself.)
function kept(l: Loop, r: Relation | undefined): Relation | undefined {
  if (r && !r.exact) {
    const known = new Set([...l.params, ...Object.keys(l.state)])
    const ok = (x: string) => !isPi(x) || piParts(x)?.every(f => vars(f).every(n => known.has(n))) === true
    const keep = r.paths.map(p => [...p.rows.flatMap(vars), ...Object.values(p.post).flatMap(vars)].every(ok))
    r = {...r, paths: r.paths.filter((_, i) => keep[i]), from: r.from.filter((_, i) => keep[i]), to: r.to.filter((_, i) => keep[i])}
  }
  return r && r.paths.length ? r : undefined
}
// A product of a state value (or a param) and a turn's input (RandomHard's arg2 = arg3·x) is linear where the value is fixed:
// the loop's cases at x = 1, 0, −1 and 2 (an integer x, x$n or x$neg; a natural at 1, 0 and 2), each the relation of the
// loop whose condition fixes x first (its products then a constant times the input), the set holding x fixed (`pins`).
// At most two such values.
const fixes = new WeakMap<Loop, {rel: Relation, pins: Lin[]}[]>()
function fixedCases(l: Loop): {rel: Relation, pins: Lin[]}[] {
  const hit = fixes.get(l)
  if (hit) return hit
  const out: {rel: Relation, pins: Lin[]}[] = [], raw = rawOf(l), S = new Set([...Object.keys(l.state), ...l.params]), I = new Set(l.inputs), xs = new Set<string>()
  for (const p of raw && !raw.exact ? raw.paths : []) for (const n of [...p.rows.flatMap(vars), ...Object.values(p.post).flatMap(vars)]) {
    const fs = isPi(n) ? piParts(n) : undefined
    if (!fs) continue
    const [a, b] = fs.map(vars) as [string[], string[]]
    for (const [f, g] of [[a, b], [b, a]] as const) if (f.length === 1 && S.has(f[0]!) && g.some(x => I.has(x))) xs.add(f[0]!.replace(/\$(n|neg)$/, ''))
  }
  for (const x of [...xs].filter(x => S.has(x)).slice(0, 2)) {
    const twin = [`${x}$n`, `${x}$neg`].find(t => S.has(t))
    for (const c of twin ? [1, 0, -1, 2] : [1, 0, 2]) {
      const vals: [string, number][] = twin ? [[x, Math.max(c, 0)], [twin, Math.max(-c, 0)]] : [[x, c]]
      const r = kept(l, relationOf({...l, while: {op: 'and', xs: [...vals.map(([n, v]): C => ({op: '=', a: V(n), b: K(v)})), l.while]}}))
      if (!r) continue
      const pins = r.ints.has(x) ? [{[x]: 1, 1: -c}, {[x]: -1, 1: c}] : vals.flatMap(([n, v]) => [{[n]: 1, ...konst(-v)}, {[n]: -1, ...konst(v)}])
      out.push({rel: r, pins})
    }
  }
  fixes.set(l, out)
  return out
}

// --- products ---------------------------------------------------------------------------------------------------------
//
// A product the relation names π(a·b) (core/relation.ts: two of the loop's naturals, each one value or a part of an
// integer's pair) is, where the set decides the sign of each integer it reads, ±X·Y over the relation's integers, or 0
// (a pair's other part). Its facts are those of X·Y from the set's bounds on X and Y (McCormick's: (X − l)(Y − m) ≥ 0
// for lower bounds l, m, and likewise for the upper ones; a square's tangents (X − c)² ≥ 0), linear in the product's
// name: what a Houdini check of the set needs to keep x := x·y.
const isPi = (x: string) => x.startsWith('π(')
// (the two factors, linear in the loop's names)
const piParts = (x: string): [Lin, Lin] | undefined => {
  const m = /^π\((.*)·(.*)\)(#\d+)?$/.exec(x)
  if (!m) return undefined
  try { return [JSON.parse(m[1]!) as Lin, JSON.parse(m[2]!) as Lin] } catch { return undefined }
}
const piSeen = new WeakMap<Path, boolean>()
const readsPi = (p: Path) => { let out = piSeen.get(p); if (out === undefined) piSeen.set(p, (out = [...p.rows.flatMap(vars), ...Object.values(p.post).flatMap(vars)].some(isPi))); return out }
// (a turn's products named for the turn: values of their own, as the search over several turns reads them)
const fresh = (l: Lin, k: number): Lin => { if (!vars(l).some(isPi)) return l; const o: Lin = {}; for (const x in l) o[isPi(x) ? `${x}#${k}` : x] = l[x]!; return o }
const freshPath = (p: Path, k: number): Path => (readsPi(p) ? {...p, rows: p.rows.map(f => fresh(f, k)), post: Object.fromEntries(Object.entries(p.post).map(([x, f]) => [x, fresh(f, k)]))} : p)
// A product's value in a run (its factors' raw values multiplied).
const piValue = (rel: Relation, x: string, at: Record<string, number>): number => {
  const ev = (f: Lin) => vars(f).reduce((acc, n) => acc + f[n]! * (at[n] ?? 0), f['1'] ?? 0)
  const raw = (n: string) => { const fs = piParts(n); return fs ? ev(fs[0]) * ev(fs[1]) : at[n] ?? 0 }
  const pair = rel.ints.get(x)
  return pair ? raw(pair[0]) - raw(pair[1]) : raw(x)
}
// The bounds the rows put on one integer each.
function boundsOf(R: Lin[]): Map<string, {lo?: number, hi?: number}> {
  const out = new Map<string, {lo?: number, hi?: number}>()
  for (const f of R) {
    const xs = vars(f)
    if (xs.length !== 1) continue
    const x = xs[0]!, a = f[x]!, b = f['1'] ?? 0, e = out.get(x) ?? {}
    if (a > 0) e.hi = Math.min(e.hi ?? Infinity, Math.floor(-b / a)); else e.lo = Math.max(e.lo ?? -Infinity, Math.ceil(-b / a))
    out.set(x, e)
  }
  return out
}
// The facts of the products among `names`, given the set's rows R.
function piFacts(rel: Relation, R: Lin[], names: string[]): Lin[] {
  const pis = [...new Set(names.filter(isPi))]
  if (!pis.length) return []
  const bounds = boundsOf(R), sign = (X: string) => { const b = bounds.get(X); return b?.lo !== undefined && b.lo >= 0 ? 1 : b?.hi !== undefined && b.hi <= 0 ? -1 : 0 }
  const partOf = new Map<string, [string, 1 | -1]>()
  for (const [X, [p, n]] of rel.ints) { partOf.set(p, [X, 1]); partOf.set(n, [X, -1]) }
  // a raw factor over the relation's names (a part of an integer's pair ±X, or 0, where the bounds decide its sign), at
  // most one name in it
  const factor = (f: Lin): Lin | undefined => {
    let o: Lin = konst(f['1'] ?? 0)
    for (const r of vars(f)) {
      const q = partOf.get(r)
      if (!q) { o = plus(o, {[r]: f[r]!}); continue }
      const s = sign(q[0])
      if (!s) return undefined
      if (s === q[1]) o = plus(o, {[q[0]]: f[r]! * q[1]})
    }
    return vars(o).length <= 1 ? o : undefined
  }
  const out: Lin[] = []
  for (const N of pis) {
    const pair = rel.ints.get(N), terms: [string, number][] = pair ? [[pair[0], 1], [pair[1], -1]] : [[N, 1]]
    // N = lin + Σ c·X·Y, by product
    const prods = new Map<string, {X: string, Y: string, c: number}>()
    let lin: Lin = {}, ok = true
    for (const [raw, c0] of terms) {
      const fs = piParts(raw), a = fs && factor(fs[0]), b = fs && factor(fs[1])
      if (!a || !b) { ok = false; break }
      const ka = a['1'] ?? 0, kb = b['1'] ?? 0, xa = vars(a)[0], xb = vars(b)[0]
      lin = plus(lin, konst(c0 * ka * kb))
      if (xb) lin = plus(lin, {[xb]: c0 * ka * b[xb]!})
      if (xa) lin = plus(lin, {[xa]: c0 * kb * a[xa]!})
      if (xa && xb) { const [X, Y] = [xa, xb].sort() as [string, string], key = `${X}*${Y}`, e = prods.get(key) ?? {X, Y, c: 0}; e.c += c0 * a[xa]! * b[xb]!; prods.set(key, e) }
    }
    const live = [...prods.values()].filter(e => e.c)
    if (!ok || live.length > 1) continue
    if (!live.length) { out.push(plus({[N]: 1}, lin, -1), plus(lin, {[N]: 1}, -1)); continue }
    const {X, Y, c} = live[0]!
    if (Math.abs(c) !== 1) continue
    // rows over p = X·Y, then p := c·N
    const rows: Lin[] = [], bx = bounds.get(X) ?? {}, by = bounds.get(Y) ?? {}
    const lower = (u: number, v: number) => rows.push({[X]: v, [Y]: u, 1: -u * v, p: -1}) // p ≥ v·X + u·Y − u·v: (X − u)(Y − v) ≥ 0
    const upper = (u: number, v: number) => rows.push({[X]: -v, [Y]: -u, 1: u * v, p: 1}) // p ≤ v·X + u·Y − u·v: (X − u)(v − Y) ≥ 0 read with u a lower, v an upper bound
    if (X === Y) {
      rows.push({p: -1})
      for (const b of [bx.lo, bx.hi]) if (b !== undefined && Number.isFinite(b)) rows.push({[X]: 2 * b, 1: -b * b, p: -1})
    } else {
      if (bx.lo !== undefined && by.lo !== undefined) lower(bx.lo, by.lo)
      if (bx.hi !== undefined && by.hi !== undefined) lower(bx.hi, by.hi)
      if (bx.lo !== undefined && by.hi !== undefined) upper(bx.lo, by.hi)
      if (bx.hi !== undefined && by.lo !== undefined) rows.push({[X]: -by.lo, [Y]: -bx.hi, 1: bx.hi * by.lo, p: 1})
    }
    // (p = c·(N − lin))
    for (const f of rows) {
      const rest: Lin = {}
      for (const x in f) if (x !== 'p') rest[x] = f[x]!
      const o = plus(rest, plus({[N]: 1}, lin, -1), f.p! * c)
      if (!Object.values(o).some(v => !Number.isFinite(v))) out.push(o)
    }
  }
  return out
}

// --- inputs ---------------------------------------------------------------------------------------------------------

// Each input of a path: a term over the state and params before the turn (or, `sym`, a constant still to be chosen,
// named u@j for the cycle's turn j).
type Ins = Record<string, Lin>
function inputsOf(p: Path, S: Set<string>, P: Set<string>): string[] {
  const read = [...new Set([...p.rows.flatMap(vars), ...Object.values(p.post).flatMap(vars)])]
  return read.filter(x => !S.has(x) && !P.has(x) && !isPi(x)).sort()
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

// A step of a cycle: a path taken once with its inputs, or an inner loop taken to its end at once (`Inner`: its paths
// from its location back to it, their inputs, its turn's rows over the turn's start, its translation and metering
// function).
type Inner = {loc: number, paths: number[], ins: Ins[], rows: Lin[], acc: Required<Accel>}
type Step = {path: number, ins: Ins} | {inner: Inner}
// A turn of path i from the state sigma (each state name's form), its inputs' forms over the turn's start: its rows (a
// natural's term a natural), and the state after; with `k`, the turn's products named for the turn k (`freshPath`).
function turn(rel: Relation, natState: string[], i: number, sigma: Record<string, Lin>, ins: Ins, k?: number): {rs: Lin[], post: Record<string, Lin>} {
  const p = k === undefined ? rel.paths[i]! : freshPath(rel.paths[i]!, k), insAt = Object.fromEntries(Object.entries(ins).map(([u, t]) => [u, subst(t, sigma)])), sub = {...sigma, ...insAt}
  return {rs: [...p.rows.map(f => subst(f, sub)), ...natState.map(x => times(sigma[x]!, -1)), ...Object.keys(insAt).filter(u => !rel.ints.has(u)).map(u => times(insAt[u]!, -1))],
    post: Object.fromEntries(rel.state.map(x => [x, subst(p.post[x] ?? {[x]: 1}, sub)]))}
}
// A step from sigma. An inner loop's: its count m = meter(sigma) at least 1, its turn's rows at the first and the last
// of its turns (sigma + (m − 1)·δ: each row is linear in the turn's number, so it holds between), the state after
// sigma + m·δ, all linear in sigma.
function stepTurn(rel: Relation, natState: string[], s: Step, sigma: Record<string, Lin>): {rs: Lin[], post: Record<string, Lin>} {
  if ('path' in s) return turn(rel, natState, s.path, sigma, s.ins)
  const {rows, acc} = s.inner, m = subst(acc.meter, sigma)
  const shift = (t: Lin) => Object.fromEntries(rel.state.map(x => [x, plus(sigma[x]!, times(t, acc.delta[x] ?? 0))]))
  const last = shift(plus(m, konst(-1)))
  return {rs: [plus(konst(1), m, -1), ...rows.map(f => subst(f, sigma)), ...rows.map(f => subst(f, last))], post: shift(m)}
}
// Steps j.. of the cycle composed from a state x (identity at j): the rows over x, and the state after them over x.
function compose(rel: Relation, steps: Step[], natState: string[]): {rows: Lin[], post: Record<string, Lin>} | undefined {
  let sigma: Record<string, Lin> = Object.fromEntries(rel.state.map(x => [x, {[x]: 1}]))
  const rows: Lin[] = []
  for (const [j, s] of steps.entries()) {
    if (j > 0 && 'path' in s && readsPi(rel.paths[s.path]!)) return undefined
    const t = stepTurn(rel, natState, s, sigma)
    rows.push(...t.rs)
    sigma = t.post
    if (Object.values(sigma).some(big) || rows.some(big)) return undefined
  }
  return {rows: dedupe(rows.map(tight).filter(f => !(isConst(f) && (f['1'] ?? 0) <= 0))), post: sigma}
}
const dedupe = (rows: Lin[]) => [...new Map(rows.map(f => [canon(f), f])).values()]

// (`late`: the time is up; a candidate half made is given up; `pins`: rows each part keeps, a case's fixed values)
function candidate(rel: Relation, steps: Step[], natState: string[], l: Loop, late: () => boolean, pins: Lin[]): Omit<Accelerated, 'cycle' | 'locs'> | undefined {
  const whole = compose(rel, steps, natState)
  if (!whole) return undefined
  const G = dedupe([...whole.rows, ...pins]), U = whole.post
  if (G.some(f => isConst(f) && (f['1'] ?? 0) > 0) || G.some(f => vars(f).some(isPi)) || !sat(G)) return undefined
  // the differences of each atom of G along U, up to degree 3 (none past a product: it is read at the cycle's start): the
  // iterates g, g∘U, … of the closed forms' engine, differenced; a constant last difference above 0 gives the cycle up (g
  // grows past 0)
  const opt: Lin[] = []
  for (const g of G) {
    let d = g
    for (let k = 1; k <= 3; k++) {
      const next = plus(subst(d, U), d, -1)
      if (vars(next).some(isPi)) break
      if (isConst(next)) { if ((next['1'] ?? 0) > 0) return undefined; break }
      if (canon(next) === canon(d)) break
      opt.push(tight(next)); d = next
    }
  }
  // A product in U (x := x·y): an atom is kept where R and the product's facts imply it after U; and bounds on each
  // factor, x ≥ c for c up to 32 (x ≤ −c where G puts x below 0), which the product's facts read, are among the atoms
  // Houdini tries (complInterv's x ≥ 4 for y := (x + 1)² > 9), the weakest that does kept.
  const piU = [...new Set(Object.values(U).flatMap(vars).filter(isPi))]
  const keeps = (rs: Lin[], a: Lin) => { const after = subst(a, U); return implied(piU.length ? [...rs, ...piFacts(rel, rs, vars(after))] : rs, after) }
  const pool: Lin[] = []
  if (piU.length) {
    const partOf = new Map<string, string>()
    for (const [X, [p, n]] of rel.ints) { partOf.set(p, X); partOf.set(n, X) }
    const xs = [...new Set(piU.flatMap(n => { const pair = rel.ints.get(n); return (pair ? [pair[0], pair[1]] : [n]).flatMap(r => (piParts(r) ?? []).flatMap(vars)) }).map(r => partOf.get(r) ?? r))]
    for (const x of xs) {
      const dir = implied(G, {[x]: -1}) ? 1 : implied(G, {[x]: 1}) ? -1 : 1
      for (const c of [0, 1, 2, 3, 4, 8, 16, 32]) { const b: Lin = {[x]: -dir, ...konst(c)}; if (sat([...G, b])) pool.push(b) }
    }
  }
  // Houdini: G must be kept by U; a difference not kept is dropped
  let R = dedupe([...G, ...opt, ...pool])
  const must = new Set(G.map(canon))
  for (let round = 0; round < 12; round++) {
    if (late()) return undefined
    const bad = R.filter(a => !keeps(R, a))
    if (!bad.length) break
    if (bad.some(a => must.has(canon(a)))) return undefined
    const drop = new Set(bad.map(canon))
    R = R.filter(a => !drop.has(canon(a)))
  }
  if (R.some(a => !keeps(R, a)) || !sat(R)) return undefined
  // (the factors' bounds the set keeps: each left out, the strongest first, where the rest is kept without it)
  for (const b of [...pool].reverse()) {
    if (late()) return undefined
    const key = canon(b), rest = R.filter(a => canon(a) !== key)
    if (rest.length < R.length && !must.has(key) && rest.every(a => keeps(rest, a))) R = rest
  }
  // R without what the rest of it implies (a smaller goal for the kernel)
  R = irredundant(R, late)
  if (late()) return undefined
  // per step j: R_j, the rest of the cycle from step j allowed and ending in R (an inner loop's, at each of its turns'
  // starts with a turn of it left: the same state after it)
  const restOf = (rows: Lin[], post: Record<string, Lin>, to: Lin[]) => irredundant(dedupe([...rows, ...pins, ...to.map(a => tight(subst(a, post)))].filter(f => !(isConst(f) && (f['1'] ?? 0) <= 0))), late)
  const Rs: Lin[][] = steps.map((_, j) => {
    if (j === 0) return R
    const rest = compose(rel, steps.slice(j), natState)!
    return restOf(rest.rows, rest.post, R)
  })
  if (late()) return undefined
  // The parts: a location, its rows, the path a state there takes and its inputs. An inner loop's turns after its first,
  // each twice: the rest of the loop's turn then another of its turns (R_j), or then the step after it (R_{j+1}).
  type Part = {loc: number, rows: Lin[], path: number, ins: Ins}
  const locOf = (i: number) => (rel.loc ? rel.from[i]! : 0)
  const parts: Part[] = []
  for (const [j, s] of steps.entries()) {
    if ('path' in s) { parts.push({loc: locOf(s.path), rows: Rs[j]!, path: s.path, ins: s.ins}); continue }
    const {paths, ins} = s.inner
    parts.push({loc: s.inner.loc, rows: Rs[j]!, path: paths[0]!, ins: ins[0]!})
    for (let t = 1; t < paths.length; t++) {
      const rest = compose(rel, paths.slice(t).map((path, k) => ({path, ins: ins[t + k]!})), natState)
      if (!rest) return undefined
      for (const to of [Rs[j]!, Rs[(j + 1) % steps.length]!]) parts.push({loc: locOf(paths[t]!), rows: restOf(rest.rows, rest.post, to), path: paths[t]!, ins: ins[t]!})
    }
  }
  if (late()) return undefined
  if (parts.some(p => !sat(p.rows))) return undefined
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
  const pcIs = (j: number): C[] => (rel.loc ? [{op: '=', a: V(rel.loc), b: K(parts[j]!.loc)}] : [])
  const full = parts.map((r, j) => conj([...pcIs(j), ...r.rows.map(atom)]))
  // the witness: each input of the loop per part
  // (a part is told by its location, and where the cycle comes back to a location, by an atom of its rows that each
  // other part there refutes: a short condition, which the body's reads of the witness multiply less; its full rows
  // where no atom tells it apart)
  const tell = (j: number): C => {
    if (!rel.loc) return full[j]!
    const others = parts.flatMap((r, k) => (k !== j && r.loc === parts[j]!.loc ? [r.rows] : []))
    const atoms: Lin[] = []
    for (const r of others) {
      if (atoms.some(a => !sat([...r, a]))) continue
      const a = parts[j]!.rows.find(f => !sat([...r, f]))
      if (!a) return full[j]!
      atoms.push(a)
    }
    return conj([...pcIs(j), ...atoms.map(atom)])
  }
  const conds = parts.map((_, j) => tell(j))
  // Where each part is at a location of its own, the set is written by slots: the parts' k-th atoms, one comparison of
  // two if-chains over the locations (the same set). The kernel reads an if only down the branch the case decides, so
  // the set after the turn costs it the next part's atoms, not every part's (TermComp's tqli: its check 10.4 s to 4.5
  // s). Not where parts share a location: their conditions in each chain cost more than they save (s1).
  const slotted = (): C => {
    const width = Math.max(...parts.map(r => r.rows.length)), chain = (pick: (j: number) => E): E => conds.reduceRight<E>((acc, c, j) => (isZ(pick(j)) && isZ(acc) ? acc : {op: 'if', c, then: pick(j), else: acc}), K(0))
    const slots: C[] = []
    for (let k = 0; k < width; k++) {
      const ts = parts.map(r => (r.rows[k] ? term(r.rows[k]!) : {p: K(0), n: K(0)}))
      slots.push({op: '<=', a: chain(j => ts[j]!.p), b: chain(j => ts[j]!.n)})
    }
    return {op: 'and', xs: [{op: 'or', xs: conds}, ...slots]}
  }
  const set: C = parts.length > 1 && rel.loc && new Set(parts.map(p => p.loc)).size === parts.length ? slotted() : parts.length === 1 ? full[0]! : {op: 'or', xs: full}
  const valueAt = (j: number, n: string): E => {
    const p = rel.paths[parts[j]!.path]!
    if (n in p.pins) return K(p.pins[n]!)
    const u = parts[j]!.ins
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
    const vals = parts.map((_, j) => valueAt(j, n)), keys = vals.map(v => JSON.stringify(v))
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
  return {set, wit, targets: parts.map(p => ({loc: p.loc, rows: p.rows})), ...(rel.loc ? {cases: parts.map((p, j) => ({pins: [[rel.loc!, p.loc]] as [string, number][], cond: full[j]!}))} : {})}
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
export function* stemsTo(l: Loop, targets: Target[], io: StemIO, opts: {now: () => number, until: number, depth?: number, calls?: number, report?: {exhausted: boolean}, deepen?: boolean}): Generator<{params: Env, stem: Env[]}> {
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
    if (!pair) { const e = l.state[x]; const r = e && linOfE(e); return r && toInts(r) }
    const ep = l.state[pair[0]], en = l.state[pair[1]]
    if (!ep || !en) return undefined
    if (ep.op === 'sub' && en.op === 'sub' && JSON.stringify(ep.a) === JSON.stringify(en.b) && JSON.stringify(ep.b) === JSON.stringify(en.a)) {
      const a = linOfE(ep.a), b = linOfE(ep.b)
      return a && b && toInts(plus(a, b, -1))
    }
    const a = linOfE(ep), b = linOfE(en)
    return a && b && toInts(plus(a, b, -1))
  }
  const sigma0: Record<string, Lin> = {}
  for (const x of S) { const v = startOf(x); if (!v) return; sigma0[x] = v }
  const locE = rel.loc ? l.state[rel.loc] : undefined
  if (rel.loc && locE?.op !== 'const') return
  const startLoc = locE?.op === 'const' ? locE.value : 0
  const from = (i: number) => (rel.loc ? rel.from[i]! : 0), to = (i: number) => (rel.loc ? rel.to[i]! : 0)
  // the self-loops whose n-fold turn has a closed form (the engine's), with their inputs as terms: a translation's taken
  // n@k times at once (`delta`), any other's (x := 2·x, a doubling loop; a polynomial update) 2, 4, 8 or 16 times at
  // once, the state after each count its closed form at that count
  type Loopy = {path: number, ins: Ins, delta?: Lin, closed?: Record<string, ClosedForm>}
  const loops = new Map<number, Loopy[]>()
  rel.paths.forEach((p, i) => {
    if (from(i) !== to(i) || readsPi(p)) return
    for (const ins of inputChoices(p, Sset, P)) {
      const c = compose(rel, [{path: i, ins}], natState)
      if (!c) continue
      const a = accelerate(c.rows, c.post, S)
      if (a) { loops.set(from(i), [...(loops.get(from(i)) ?? []), {path: i, ins, delta: a.delta}]); break }
      const closed: Record<string, ClosedForm> = {}
      for (const x of S) { const f = nfold({[x]: 1}, c.post, 4); if (!f) break; closed[x] = f }
      if (Object.keys(closed).length === S.length && S.some(x => canon(c.post[x]!) !== canon({[x]: 1}))) { loops.set(from(i), [...(loops.get(from(i)) ?? []), {path: i, ins, closed}]); break }
    }
  })
  const natParams = paramInts.filter(p => !p[1]).map(p => p[0])
  type Seg = {path: number, ins: Ins, n?: string, times?: number}
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
      const times = s.n ? Math.round(w[s.n] ?? 1) : s.times ?? 1
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
  // (`deepen`: the depth, then twice and four times it, with the calls given, 4 and 16 times them, a stem yielded once)
  let maxDepth = 0, shallow = -1
  const outs = new Map<number, number[]>()
  for (let i = 0; i < rel.paths.length; i++) if (dist.has(to(i))) outs.set(from(i), [...(outs.get(from(i)) ?? []), i])
  for (const xs of outs.values()) xs.sort((a, b) => dist.get(to(a))! - dist.get(to(b))!)
  function* dfs(loc: number, sigma: Record<string, Lin>, rows: Lin[], segs: Seg[], k: number, lastLoop: boolean): Generator<{params: Env, stem: Env[]}> {
    if (calls <= 0 || now() > until) return
    for (const t of targets) if (t.loc === loc) {
      const m = solveRows([...rows, ...t.rows.map(f => subst(f, sigma))])
      if (m.kind === 'sat' && segs.length > shallow) { const c = concrete(segs, m.witness); if (c) yield c }
    }
    if (segs.length + (dist.get(loc) ?? Infinity) > maxDepth) return
    const step = (i: number, ins: Ins, n?: {name: string, delta: Lin}) => {
      const {rs, post} = turn(rel, natState, i, sigma, ins, k)
      if (!n) return {rs, post}
      // the last turn's rows: at sigma + (n − 1)·δ
      const p = rel.paths[i]!, last = Object.fromEntries(S.map(x => [x, plus(plus(sigma[x]!, times({[n.name]: 1}, n.delta[x] ?? 0)), konst(-(n.delta[x] ?? 0)))]))
      const insLast = Object.fromEntries(Object.entries(ins).map(([u, t]) => [u, subst(t, last)]))
      rs.push(...p.rows.map(f => subst(f, {...last, ...insLast})), ...natState.map(x => times(last[x]!, -1)), plus(konst(1), {[n.name]: -1}))
      return {rs, post: Object.fromEntries(S.map(x => [x, plus(sigma[x]!, times({[n.name]: 1}, n.delta[x] ?? 0))]))}
    }
    // a self-loop accelerated, then each path out
    if (!lastLoop) for (const lp of loops.get(loc) ?? []) {
      if (lp.closed) {
        // each count: its turns' rows (each turn's state the closed form at its number), the state after at the count
        let rs: Lin[] = []
        for (let c = 1, at = sigma; c <= 16; c++) {
          rs = [...rs, ...turn(rel, natState, lp.path, at, lp.ins).rs]
          at = Object.fromEntries(S.map(x => [x, subst(closedAt(lp.closed![x]!, c), sigma)]))
          if (![2, 4, 8, 16].includes(c)) continue
          const all = [...rows, ...rs]
          if (all.some(big) || Object.values(at).some(big) || solveRows(all).kind === 'refuted') break
          yield* dfs(loc, at, all, [...segs, {path: lp.path, ins: lp.ins, times: c}], k + 1, true)
        }
        continue
      }
      const name = `n@${k}`, {rs, post} = step(lp.path, lp.ins, {name, delta: lp.delta!})
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
  for (const r of opts.deepen ? [1, 2, 4] : [1]) {
    const d = r * depth
    calls = (opts.calls ?? 400) * r * r
    maxDepth = Math.max(d, dist.get(startLoc)! + d)
    yield* dfs(startLoc, sigma0, [...base], [], 0, false)
    if (calls <= 0 || now() > until) return
    shallow = maxDepth
  }
  if (opts.report) opts.report.exhausted = true
}
