// Interpolants from the kernel's refutations. Nothing here is trusted: an interpolant is a candidate (a law to prove,
// or a power relation's conjunct for core/tpa.ts), and whatever is answered from one is checked elsewhere.
//
// Given hypotheses A and B that can't all hold, an interpolant is a condition I over the names they share with
// A ⊨ I and I ∧ B refuted. The kernel's tree for A ∧ B (kernel/cdcl.ts's, else prove.ts's) gives one, McMillan's way:
// - B is renamed apart from A (every name of B's that A reads too gets a copy, n#b), and each shared name is tied to its
//   copy (n = n#b, read as B's), so each row of a leaf belongs to one side: a hypothesis' facts to its side, the path's
//   atoms, the naturals and a term column's rows to the side whose names they read (A's names first);
// - at a leaf, its derivation replayed with each row's A part beside it (an input of A's is all A part, a combination
//   adds the parts, a cut divides the A part where the rest has no variable, and the rest where the A part has none,
//   else the leaf has no interpolant here): the last row is a positive constant, A gives `A part <= 0` and B the rest,
//   so the A part reads only shared names and `A part <= 0` is the leaf's interpolant;
// - a split on an atom of A's: the two sides' interpolants or-ed; on an atom of B's: and-ed.
// The interpolant is over A's names (the shared ones), as a condition the kernel reads.
import type {C, E, Law, Machine, Request} from './machine.ts'
import {type Goal, type Path, type Tree, atomOf, canon, columnTerm, falseC, leafConstraints, stepLawObligations, substC, substE, trueC} from '../kernel/kernel.ts'
import {type Lin, type Step, env, linOfE, plus, solve, vars} from './solver.ts'
import {litVar} from '../kernel/reader.ts'
import {namesOf, showC} from './exists.ts'
import {type Dag, REFUTED, type Refuted, cdclSession, growCdcl} from '../kernel/cdcl.ts'
import {clock, grow} from '../kernel/prove.ts'
import {relax, replay, runOf, tidier} from './bmc.ts'
import {isF, isT, simpC} from './nonterm.ts'

export type Interpolated = {itp: C, tree?: Tree} | {sat: Record<string, number>} | {unknown: string}

const v = (name: string): E => ({op: 'var', name}), k = (value: number): E => ({op: 'const', value})
// A linear form as `Σ pos ≤ Σ neg + c` over naturals (columns read as their terms).
const term = (name: string): E => (name.startsWith('⟦') ? columnTerm(name) ?? v(name) : v(name))
export function linLe(l: Lin): C {
  const pos: E[] = [], neg: E[] = []
  for (const x of vars(l)) { const c = l[x]!; (c > 0 ? pos : neg).push(Math.abs(c) === 1 ? term(x) : {op: 'mul', k: Math.abs(c), a: term(x)}) }
  const c = -(l['1'] ?? 0)
  if (c > 0) neg.push(k(c)); else if (c < 0) pos.push(k(-c))
  const sum = (xs: E[]): E => (xs.length ? xs.reduce((a, b) => ({op: 'add', a, b})) : k(0))
  return {op: '<=', a: sum(pos), b: sum(neg)}
}
const or = (a: C, b: C): C => (isT(a) || isT(b) ? trueC : isF(a) ? b : isF(b) ? a : JSON.stringify(a) === JSON.stringify(b) ? a : {op: 'or', xs: [a, b]})
const and = (a: C, b: C): C => (isF(a) || isF(b) ? falseC : isT(a) ? b : isT(b) ? a : JSON.stringify(a) === JSON.stringify(b) ? a : {op: 'and', xs: [a, b]})

// A ∧ B asked of the kernel's search: an interpolant over `shared` (names A and B both read; any other name B reads that
// A reads too is B's own), a model of both (A's names, and B's own as n#b), or why neither came.
export function interpolate(a: C[], b: C[], shared: string[], budget: {until: number, wall?: number}): Interpolated {
  const aNames = new Set(a.flatMap(namesOf)), share = new Set(shared)
  const ren: Record<string, E> = {}
  for (const n of new Set(b.flatMap(namesOf))) if (aNames.has(n)) ren[n] = v(`${n}#b`)
  const sub = {vars: ren, maps: {}, flags: {}}
  const ties: C[] = [...share].filter(n => ren[n]).map(n => ({op: '=', a: v(n), b: v(`${n}#b`)}))
  const goal: Goal = {name: 'an interpolant', hyps: [...a, ...b.map(c => substC(c, sub)), ...ties]}
  // CDCL's DAG first (no tree unfolded, no leaf read again); where it gives none, the tree's
  if (useDag) {
    const d = growCdcl(goal, new Map(), {nodes: 0, until: budget.until}, {model: true, dag: true, ...(useClausal ? {clausal: true, sideOf: (i: number) => (i < a.length ? 0 : 1)} : {}), ...(budget.wall !== undefined ? {wall: budget.wall} : {})}) as Refuted
    if (d.dag) { const itp = fromDag(goal, d.dag, i => i < a.length, 50_000, useClausal && useStrong); if (itp) return {itp} } else if (!('tree' in d)) {
      if (d.stuck === 'sat' && d.witness) return {sat: d.witness}
      if (budget.wall !== undefined) return {unknown: d.why ?? d.stuck}
    }
  }
  const out = refute(goal, budget)
  if (!('tree' in out)) return out.stuck === 'sat' && out.witness ? {sat: out.witness} : {unknown: out.why ?? out.stuck}
  const itp = fromTree(goal, out.tree, i => i < a.length, budget.wall)
  return itp ? {itp, tree: out.tree} : {unknown: 'a leaf with no interpolant'}
}
// The kernel's tree for a goal (CDCL's, else, with no wall stop, the plain search's within the budget), or its model.
export function refute(goal: Goal, budget: {until: number, wall?: number}): ReturnType<typeof grow> {
  const out = growCdcl(goal, new Map(), {nodes: 0, until: budget.until}, budget.wall !== undefined ? {wall: budget.wall} : {})
  if ('tree' in out || out.stuck === 'sat' || budget.wall !== undefined) return out
  return grow(goal, new Map(), {nodes: 0, until: budget.until})
}

type Side = 'A' | 'B' | 'S' | undefined
const nameMemo = new WeakMap<C, string[]>()
const namesIn = (c: C): string[] => { let out = nameMemo.get(c); if (!out) nameMemo.set(c, (out = namesOf(c))); return out }
// The sides of names: a name only A's hypotheses read is A's own, only B's B's own, both shared ('S'); a term column is
// its term's names' (undefined where they mix A's own and B's own), and so is a linear form.
function sidesOf(goal: Goal, isA: (hyp: number) => boolean) {
  const aNames = new Set<string>(), bNames = new Set<string>()
  goal.hyps.forEach((h, i) => { for (const n of namesIn(h)) (isA(i) ? aNames : bNames).add(n) })
  const colMemo = new Map<string, Side>()
  const join = (sides: Side[]): Side => {
    if (sides.includes(undefined)) return undefined
    const a = sides.includes('A'), b = sides.includes('B')
    return a && b ? undefined : a ? 'A' : b ? 'B' : 'S'
  }
  const nameSide = (n: string): Side => {
    // (a gate's or a column's of kernel/cdcl.ts's clausal mode: its side the hypothesis' that wrote it)
    if (n.startsWith('τ') || n.startsWith('ϰ')) return isA(Number(n.slice(1, n.indexOf('_')))) ? 'A' : 'B'
    if (!n.startsWith('⟦')) return aNames.has(n) ? (bNames.has(n) ? 'S' : 'A') : bNames.has(n) ? 'B' : 'S'
    if (colMemo.has(n)) return colMemo.get(n)
    const t = columnTerm(n), out = join((t ? namesOf(t) : []).map(nameSide))
    colMemo.set(n, out)
    return out
  }
  return {nameSide, linSide: (l: Lin): Side => join(vars(l).map(nameSide))}
}
// A leaf's derivation replayed with each row's A part beside it (`row(k)`: the k-th row and whether it is A's): an
// input of A's is all A part, a combination adds the parts, a cut divides the A part where the rest has no variable, and
// the rest where the A part has none (else undefined). The last row is a positive constant, A gives `A part <= 0` and B
// the rest, so where the A part reads only shared names, `A part <= 0` is the leaf's interpolant.
// Where a cut mixes the parts, the rows the derivation reads refuted again over the rationals (core/solver.ts's
// elimination with no cut, which Farkas' lemma says finds a refutation wherever they have no rational solution): every
// leaf whose rows the simplex found infeasible has one, and it needs no cut.
function replayA(steps: Step[], row: (k: number) => {lin: Lin, a: boolean} | undefined, nameSide: (n: string) => Side): C | undefined {
  const out = replay1(steps, row, nameSide)
  if (out || !steps.some(s => s.kind === 'cut')) return out
  const used = [...new Set(steps.flatMap(s => (s.kind === 'input' ? [s.index] : [])))], rows = used.map(row)
  if (rows.some(r => !r)) return undefined
  const q = solve(rows.map(r => ({lin: r!.lin, label: ''})), 20_000, false)
  return q.kind === 'refuted' ? replay1(q.steps.map(s => (s.kind === 'input' ? {...s, index: used[s.index]!} : s)), row, nameSide) : undefined
}
function replay1(steps: Step[], row: (k: number) => {lin: Lin, a: boolean} | undefined, nameSide: (n: string) => Side): C | undefined {
  const tot: Lin[] = [], ap: Lin[] = []
  const plus = (x: Lin, mx: number, y: Lin, my: number): Lin => {
    const o: Lin = {}
    for (const n in x) o[n] = (o[n] ?? 0) + mx * x[n]!
    for (const n in y) o[n] = (o[n] ?? 0) + my * y[n]!
    for (const n in o) if (o[n] === 0) delete o[n]
    return o
  }
  const cut = (l: Lin, g: number): Lin => { const o: Lin = {}; for (const n of vars(l)) o[n] = l[n]! / g; const c = Math.ceil((l['1'] ?? 0) / g); if (c) o['1'] = c; return o }
  for (const s of steps) {
    if (s.kind === 'input') {
      const r = row(s.index)
      if (!r) return undefined
      tot.push(r.lin); ap.push(r.a ? r.lin : {})
    } else if (s.kind === 'combine') {
      tot.push(plus(tot[s.a]!, s.ma, tot[s.b]!, s.mb)); ap.push(plus(ap[s.a]!, s.ma, ap[s.b]!, s.mb))
    } else {
      const t0 = tot[s.of]!, a0 = ap[s.of]!, b0 = plus(t0, 1, a0, -1), t1 = cut(t0, s.g)
      const aVars = vars(a0).length > 0, bVars = vars(b0).length > 0
      if (aVars && bVars) return undefined
      tot.push(t1); ap.push(!bVars ? cut(a0, s.g) : plus(t1, 1, cut(b0, s.g), -1))
    }
  }
  const p = ap.at(-1)
  if (!p || vars(p).some(n => nameSide(n) !== 'S')) return undefined
  if (!vars(p).length) return (p['1'] ?? 0) > 0 ? falseC : trueC
  return linLe(p)
}
// The interpolant of CDCL's refutation DAG itself (kernel/cdcl.ts's `dag`), McMillan's way over resolution: at a leaf
// (a theory conflict) its derivation replayed as above, a row of a hypothesis of A's an A row, another (the trail's
// atoms, the naturals, the term columns) by its names, an atom over shared names A's; the leaf's interpolant is that
// part with the leaf's own literals over shared names beside it (B's rows may need them). A resolution on an atom of
// B's own and-s its parents' interpolants, on any other or-s them. Each node once (the DAG's sharing kept); none where
// an atom or a cut mixes A's own and B's own, or past `maxNodes` of the formula.
// `strong` (a clausal DAG, whose theory leaves read the trail's atoms alone): McMillan's own system, the strongest, in
// place of that one (its dual, the weakest): A's clause the or of its literals over shared names, B's true; a theory
// leaf the A part of its derivation, an atom over shared names B's; a resolution on an atom of A's own or-s, any other
// and-s.
export function fromDag(goal: Goal, dag: Dag, isA: (hyp: number) => boolean, maxNodes = 50_000, strong = false): C | undefined {
  const {nameSide, linSide} = sidesOf(goal, isA), memo = new Map<number, C | undefined>()
  let made = 0
  const at = (i: number): C | undefined => {
    if (i < 0) return undefined
    if (memo.has(i)) return memo.get(i)
    const n = dag.nodes[i]!
    let out: C | undefined
    if ('res' in n) {
      const side = linSide(n.on), y = side === undefined ? undefined : at(n.res[0]), z = y && at(n.res[1])
      out = z && ((strong ? side !== 'A' : side === 'B') ? and(y!, z) : or(y!, z))
    } else if ('hyp' in n) {
      // (a hypothesis' clause, the clausal mode's: A's has none; B's, the shared literals it rests on; strong, A's the or
      // of its shared literals, B's none)
      const shared = n.lits.filter(([lin]) => linSide(lin) === 'S')
      out = strong ? (isA(n.hyp) ? shared.map(([lin, holds]) => linLe(atomOf(lin, !holds).lin)).reduceRight<C>((acc, c) => or(c, acc), falseC) : trueC)
        : isA(n.hyp) ? falseC : shared.map(([lin, holds]) => linLe(atomOf(lin, holds).lin)).reduceRight<C>((acc, c) => and(c, acc), trueC)
    } else if (strong) {
      out = n.src && replayA(n.steps, k => { const lin = n.inputs[k], side = lin && linSide(lin); return side === undefined || !lin ? undefined : {lin, a: side === 'A'} }, nameSide)
    } else {
      const p = n.src && replayA(n.steps, k => {
        const lin = n.inputs[k], h = n.src![k]
        if (!lin || h === undefined) return undefined
        if (h >= 0) return {lin, a: isA(h)}
        const side = linSide(lin)
        return side === undefined ? undefined : {lin, a: side !== 'B'}
      }, nameSide)
      const shared = (n.lits ?? []).filter(([lin]) => linSide(lin) === 'S').map(([lin, holds]) => linLe(atomOf(lin, holds).lin))
      out = p && shared.reduceRight((acc, c) => and(c, acc), p)
    }
    if (out && ++made > maxNodes) out = undefined
    memo.set(i, out)
    return out
  }
  const out = at(dag.top)
  return out && simpC(out)
}

// The interpolant of a refutation tree of `goal` whose hypotheses `isA` holds of are A's, the rest B's: over the names
// both read (shared). A name only A's hypotheses read is A's own, only B's B's own; a term column is its term's names'.
// A path atom over shared names alone is A's, and the leaf's interpolant keeps it (B's facts may read it), so a split on
// it, as on one of A's own, or-s its sides; a split on one of B's own and-s them.
export function fromTree(goal: Goal, tree: Tree, isA: (hyp: number) => boolean, wall?: number): C | undefined {
  const {nameSide, linSide} = sidesOf(goal, isA)
  const walk = (t: Tree, path: Path, kept: C[]): C | undefined => {
    if ('leaf' in t) { if (wall !== undefined && performance.now() > wall) return undefined; const p = leaf(t.leaf, path); return p && kept.reduceRight((acc, c) => and(c, acc), p) }
    const side = linSide(t.split)
    if (side === undefined) return undefined
    const key = canon(t.split)
    const keep = (holds: boolean): C[] => (side === 'S' ? [...kept, linLe(holds ? t.split : {...Object.fromEntries(vars(t.split).map(x => [x, -t.split[x]!])), 1: 1 - (t.split['1'] ?? 0)})] : kept)
    const yes = walk(t.yes, new Map(path).set(key, {lin: t.split, holds: true}), keep(true))
    if (!yes) return undefined
    const no = walk(t.no, new Map(path).set(key, {lin: t.split, holds: false}), keep(false))
    if (!no) return undefined
    return side === 'B' ? and(yes, no) : or(yes, no)
  }
  const leaf = (steps: Extract<Tree, {leaf: unknown}>['leaf'], path: Path): C | undefined => {
    const rows = leafConstraints(goal, path)
    return replayA(steps, k => {
      const r = rows[k]
      if (!r) return undefined
      const src = r.src
      let side: Side
      if (src && 'fact' in src) side = isA(src.fact) ? 'A' : 'B'
      else if (src && 'nat' in src) side = nameSide(src.nat) === 'B' ? 'B' : 'A'
      else if (src && 'term' in src) side = nameSide(src.term)
      else if (!src || 'atom' in src) side = linSide(r.lin)
      return side === undefined ? undefined : {lin: r.lin, a: side !== 'B'}
    }, nameSide)
  }
  const out = walk(tree, new Map(), [])
  return out && simpC(out)
}

// --- interpolation over the unrolling (McMillan's IMC) -------------------------------------------------------------
//
// The reachable states over-approximated by interpolants of bounded refutations. At depth k (2, 3, ...) R starts as the
// start state; the goal is R, then k steps of the rule, then the law broken (the kernel's own k-step goal,
// stepLawObligations, its `when` R) with a step from a state that breaks the law staying put (so "broken after k" is
// "broken within k"). Refuted, A (R and the first step) and B (the rest) give an interpolant I over the state after
// one step: every state one step from R is in I, and from none of I is the law broken within k − 1 steps. I within R
// (I ∧ ¬R refuted) is a fixed point: R holds at the start and after every step from it, and the law holds wherever
// R does, so R is an invariant for the kernel to prove (the caller's answer). Else R ∨ I is the next R. A model where R
// is the start alone is a run of k steps that breaks the law (taken by the interpreter, as core/bmc.ts's); a model
// past the start may be spurious, and the depth grows.

// GDP_IMC_RELAX=0: the goals as the kernel writes them (each pair normalized at each step).
const useRelax = env.GDP_IMC_RELAX !== '0'
// GDP_ITP_DAG=0: interpolants from the unfolded tree alone.
const useDag = env.GDP_ITP_DAG !== '0', useClausal = env.GDP_ITP_CLAUSAL === '1', useStrong = env.GDP_ITP_STRONG === '1', useSession = env.GDP_IMC_SESSION === '1'

export type ImcResult = {inv: C, k: number, parts: number} | {run: {params: Record<string, number>, trace: Request[]}, k: number} | {why: string, k: number}
export type ImcOptions = {until: number, wall?: number, kinds?: C[], from?: number, to?: number, progress?: (k: number, what: string, info: Record<string, number>) => void}

// The machine whose steps from a state that breaks the law stay put. A step's truncated difference (an integer's pair
// normalized, a ∸ b) stays one, of its parts kept or stepped (n ∸ n$neg is n for a normalized pair), so core/bmc.ts's
// `relax` still reads the pair.
export function stutter(m: Machine, law: Law): Machine {
  const bad: C = {op: 'not', x: law.holds}
  const keep = (n: string, e: E): E => {
    const pn = n.endsWith('$neg') ? n.slice(0, -4) : `${n}$neg`
    if (e.op === 'sub' && pn in m.state) {
      const [a, b] = n.endsWith('$neg') ? [v(n), v(pn)] : [v(n), v(pn)]
      return {op: 'sub', a: {op: 'if', c: bad, then: a, else: e.a}, b: {op: 'if', c: bad, then: b, else: e.b}}
    }
    return {op: 'if', c: bad, then: v(n), else: e}
  }
  const state = Object.fromEntries(Object.keys(m.state).map(n => [n, keep(n, m.step.state?.[n] ?? v(n))]))
  return {...m, step: {...m.step, state}, ...(m.assume ? {assume: {op: 'or', xs: [bad, m.assume]}} : {})}
}
// A goal's hypotheses by the step they belong to: a state name n~j is step j's, a request's name n@j step j's, the
// first step's request (its plain names) step 1's, the start state step 0's.
export function byStep(m: Machine, hyps: C[]): number[] {
  const state = new Set(Object.keys(m.state)), inputs = new Set(m.inputs)
  const stepOf = (n: string): number => { const r = /[~@](\d+)$/.exec(n); return r ? Number(r[1]) : inputs.has(n) ? 1 : state.has(n) ? 0 : 0 }
  return hyps.map(h => Math.max(0, ...namesOf(h).map(stepOf)))
}
// The kernel's k-step goal (`when` before the first step, `then` after the last, primed names) asked for an interpolant
// at the state after the first step: over the names n~1 (k > 1), a condition every state one step from `when` meets and
// from which no k − 1 steps reach a state where `then` fails; or a model of the goal, or why neither came.
// (`exact`: a model of the integers relaxed, core/bmc.ts's `relax`, may be no model of the goal, and its refutation may
// cut where the exact one doesn't; the goal itself is then asked)
export function cutInterpolant(m: Machine, when: C, then: C, k: number, budget: {until: number, wall?: number}, exact = false): Interpolated {
  const g = stepLawObligations(m, [], {}, {name: 'an interpolant', when, then, steps: k})[0]!
  const relaxed = useRelax ? relax(g.hyps) : undefined, hyps = relaxed ?? g.hyps
  const ask = (hs: C[]) => { const st = byStep(m, hs); return interpolate(hs.filter((_, i) => st[i]! <= 1), hs.filter((_, i) => st[i]! > 1), Object.keys(m.state).map(n => `${n}~1`), budget) }
  const out = ask(hyps)
  return exact && relaxed && ('sat' in out || ('unknown' in out && out.unknown === 'a leaf with no interpolant')) ? ask(g.hyps) : out
}
const startOf = (m: Machine): C => ({op: 'and', xs: Object.entries(m.state).map(([n, e]): C => ({op: '=', a: v(n), b: e}))})

export function imc(m: Machine, law: Law, opts: ImcOptions): ImcResult {
  const out = imcSearch(m, law, opts).run(opts.until, opts.wall)
  return out === 'paused' ? {why: 'the budget', k: 0} : out
}
// The same search, resumable (compare/chc/kind.ts's turns): each run goes on from the depth and the R it stopped at,
// until `until` on the counted clock or `wall`, and is 'paused' there (the query it was asking asked again next time).
export function imcSearch(m: Machine, law: Law, opts: Omit<ImcOptions, 'until' | 'wall'> = {}) {
  const plain = !(Object.keys(m.maps ?? {}).length || Object.keys(m.step.flags ?? {}).length || m.params.length || m.history || m.inputMaps?.length)
  if (plain && useSession) return imcSession(m, law, opts)
  const m2 = stutter(m, law), names = Object.keys(m.state), start = startOf(m)
  const back = {vars: Object.fromEntries(names.map(n => [`${n}~1`, v(n)])), maps: {}, flags: {}}
  const then = substC(law.holds, {vars: Object.fromEntries(names.map(n => [n, v(`${n}'`)])), maps: {}, flags: {}})
  let k = Math.max(2, opts.from ?? 2), rs: C[] = [start]
  const run = (until: number, wall?: number): ImcResult | 'paused' => {
    if (!plain) return {why: 'not a plain machine', k: 0}
    const over = () => clock() > until || (wall !== undefined && performance.now() > wall), budget = {until, ...(wall !== undefined ? {wall} : {})}
    for (; k <= Math.min(64, opts.to ?? 64); k++, rs = [start]) {
      for (;;) {
        if (over()) return 'paused'
        const r: C = rs.length === 1 ? start : {op: 'or', xs: rs}
        const out = cutInterpolant(m2, opts.kinds?.length ? {op: 'and', xs: [r, ...opts.kinds]} : r, then, k, budget)
        if ('sat' in out) {
          opts.progress?.(k, 'sat', {parts: rs.length})
          if (rs.length > 1) break
          const found = runOf(m, out.sat, k), broken = replay(m, [law], found)
          if (broken) return {run: {params: found.params, trace: found.trace.slice(0, broken.steps)}, k}
          break
        }
        if ('unknown' in out) { if (over()) return 'paused'; return {why: out.unknown, k} }
        const I = substC(out.itp, back)
        // I within R: the fixed point.
        const inR = growCdcl({name: 'an interpolant within', hyps: [I, {op: 'not', x: r}]}, new Map(), {nodes: 0, until}, {model: true, ...(wall !== undefined ? {wall} : {})})
        const within = !('tree' in inR) && inR.why === REFUTED
        opts.progress?.(k, within ? 'fixed' : 'refuted', {parts: rs.length})
        if (within) return {inv: r, k, parts: rs.length}
        if (!('tree' in inR) && inR.stuck === 'unknown') { if (over()) return 'paused'; return {why: 'containment unknown', k} }
        rs.push(I)
      }
    }
    return {why: 'no depth left', k: 64}
  }
  return {run}
}

// --- IMC on one unrolling ----------------------------------------------------------------------------------------------
//
// McMillan's own loop (Golem's IMC.cc: the frontier, not the states reached so far, is the next query's start), on one
// unrolling kept in one CDCL session (kernel/cdcl.ts's clausal mode) from query to query and depth to depth: each step's
// hypotheses written once in names that stay (the state before the first step the machine's own names, after step j
// n~j; the first step's request its plain names, step j's input@j), relaxed and tidied as core/bmc.ts's are; the law
// broken after step k a hypothesis behind act@k, each frontier one behind a selector of its own (both read as
// decisions alone). A query assumes its frontier's selector and its depth's act; the steps' clauses and every clause
// learned stay. Its refutation's DAG ends in the clause of those two assumptions, the frontier's A's own and the depth's
// B's own, so its interpolant (A: the frontier, the kinds and the first step; B: the rest) is one of the query as asked.
// The states reached so far, as the frontiers' disjunction, are a second session's: each frontier's negation once, the
// next interpolant behind a selector, refuted where it lies within them (the fixed point).
// The state values a law and the assumption read, and those their updates read (the cone of influence, as core/bmc.ts's).
function liveOf(m: Machine, law: Law): Set<string> {
  const live = new Set<string>(), read = (xs: (C | E)[]) => [...new Set(xs.flatMap(x => namesOf(x as C)))].filter(n => n in m.state)
  for (const todo = read([law.holds, ...(m.assume ? [m.assume] : [])]); todo.length;) { const n = todo.pop()!; if (live.has(n)) continue; live.add(n); todo.push(...read([m.step.state?.[n] ?? v(n)])) }
  return live
}
// Step j's hypotheses in an unrolling's names (the state before step 1 the machine's own names, after step j n~j; step
// j's request input@j, step 1's plain): its assumption and each live value's update, relaxed and tidied as core/bmc.ts's.
const stateAt = (m: Machine, j: number) => ({vars: Object.fromEntries(Object.keys(m.state).map(n => [n, v(j ? `${n}~${j}` : n)])), maps: {}, flags: {}})
const topOf = (c: C): C[] => (c.op === 'and' ? c.xs.flatMap(topOf) : [c])
function stepHyps(m: Machine, live: Set<string>, j: number, tidy: (cs: C[]) => C[]): C[] {
  const at = {vars: {...stateAt(m, j - 1).vars, ...Object.fromEntries(m.inputs.map(i => [i, v(j === 1 ? i : `${i}@${j}`)]))}, maps: {}, flags: {}}
  const raw: C[] = [...(m.assume ? [substC(m.assume, at)] : []), ...[...live].map((n): C => ({op: '=', a: v(`${n}~${j}`), b: substE(m.step.state?.[n] ?? v(n), at)}))]
  return tidy((relax(raw) ?? raw).map(simpC).flatMap(topOf)).flatMap(topOf).filter(c => !isT(c))
}
export function imcSession(m: Machine, law: Law, opts: Omit<ImcOptions, 'until' | 'wall'> = {}) {
  const m2 = stutter(m, law), names = Object.keys(m.state), start = startOf(m)
  const goal: Goal = {name: 'an unrolling', hyps: []}, isA: boolean[] = []
  const quiet = (n: string) => n.startsWith('sel@') || n.startsWith('act@')
  const session = cdclSession(goal, new Map(), {model: true, dag: true, clausal: true, quiet, sideOf: h => (isA[h] ? 0 : 1)})
  const add = (c: C, a: boolean) => { if (!isT(c)) { goal.hyps.push(c); isA.push(a) } }
  const back = {vars: Object.fromEntries(names.map(n => [`${n}~1`, v(n)])), maps: {}, flags: {}}
  const live = liveOf(m, law), tidy = tidier(new Set())
  let steps = 0
  const stepTo = (k: number) => { for (; steps < k;) { const j = ++steps; for (const c of stepHyps(m2, live, j, tidy)) add(c, j === 1) } }
  for (const c of opts.kinds ?? []) add(c, true)
  const one: E = {op: 'const', value: 1}, guard = (s: string, c: C): C => ({op: 'or', xs: [{op: '<=', a: one, b: v(s)}, c]}), off = (s: string): C => ({op: '<=', a: one, b: v(s)})
  let nSel = 0, act = 0
  // The query: the frontier at its depth. An interpolant (over the state's names), a model (a run where the frontier is
  // the start), or why neither came.
  const ask = (frontier: number, k: number, budget: {until: number, wall?: number}): Interpolated => {
    stepTo(k)
    if (act !== k) { if (act) add(off(`act@${act}`), false); act = k; add(guard(`act@${k}`, substC({op: 'not', x: law.holds}, stateAt(m, k))), false) }
    const out = session.run({nodes: 0, until: budget.until}, budget.wall, [{[`act@${k}`]: 1}, {[`sel@${frontier}`]: 1}]) as Refuted
    if ('tree' in out) return {unknown: 'a tree'}
    if (out.why === REFUTED) {
      if (!out.dag) return {unknown: 'no DAG'}
      const itp = fromDag(goal, out.dag, h => isA[h]!, 200_000, useStrong)
      return itp ? {itp: substC(itp, back)} : {unknown: 'a leaf with no interpolant'}
    }
    return out.stuck === 'sat' && out.witness ? {sat: out.witness} : {unknown: out.why ?? out.stuck}
  }
  const frontierOf = (c: C): number => { const i = ++nSel; add(guard(`sel@${i}`, c), true); return i }
  // The states reached at this depth, and the frontier the next query starts from.
  let k = Math.max(2, opts.from ?? 2), parts = 0, rs: C[] = [], front = 0
  let within: ReturnType<typeof cdclSession> | undefined, wgoal: Goal = {name: 'within', hyps: []}, nq = 0
  const fresh = () => { rs = [start]; parts = 1; if (front) add(off(`sel@${front}`), true); front = frontierOf(start); wgoal = {name: 'within', hyps: [{op: 'not', x: start}]}; within = cdclSession(wgoal, new Map(), {model: true, clausal: true, quiet: n => n.startsWith('q@')}) }
  const run = (until: number, wall?: number): ImcResult | 'paused' => {
    const over = () => clock() > until || (wall !== undefined && performance.now() > wall), budget = {until, ...(wall !== undefined ? {wall} : {})}
    if (!front) fresh()
    for (; k <= Math.min(64, opts.to ?? 64); k++, fresh()) {
      for (;;) {
        if (over()) return 'paused'
        const out = ask(front, k, budget)
        if ('sat' in out) {
          opts.progress?.(k, 'sat', {parts})
          if (parts > 1) break
          const found = runOf(m, out.sat, k), broken = replay(m, [law], found)
          if (broken) return {run: {params: found.params, trace: found.trace.slice(0, broken.steps)}, k}
          break
        }
        if ('unknown' in out) { if (over()) return 'paused'; return {why: out.unknown, k} }
        if (env.GDP_IMC_CHECK === '1') {
          // (a check, for debugging: each step from the frontier lands in the interpolant, and none from it breaks the law
          // within k − 1 steps; each asked of the kernel's own goals)
          const F = rs.at(-1)!, prime = (c: C) => substC(c, {vars: Object.fromEntries(names.map(n => [n, v(`${n}'`)])), maps: {}, flags: {}})
          const g1 = stepLawObligations(m2, [], {}, {name: 'A ⊨ I', when: {op: 'and', xs: [F, ...(opts.kinds ?? [])]}, then: prime(out.itp), steps: 1})[0]!
          const g2 = stepLawObligations(m2, [], {}, {name: 'I ∧ B', when: out.itp, then: prime(law.holds), steps: k - 1})[0]!
          const r1 = growCdcl(g1, new Map(), {nodes: 0}, {model: true}), r2 = k > 1 ? growCdcl(g2, new Map(), {nodes: 0}, {model: true}) : r1
          const ok = (r: ReturnType<typeof growCdcl>) => ('tree' in r ? 'tree' : r.why === REFUTED ? 'ok' : r.stuck)
          console.error(JSON.stringify({check: true, k, parts, aImpliesI: ok(r1), iAndB: ok(r2)}))
        }
        // The interpolant within the states reached: the fixed point.
        const q = `q@${++nq}`
        wgoal.hyps.push({op: 'or', xs: [{op: '<=', a: one, b: v(q)}, out.itp]})
        const inR = within!.run({nodes: 0, until}, wall, [{[q]: 1}])
        const fixed = !('tree' in inR) && inR.why === REFUTED
        opts.progress?.(k, fixed ? 'fixed' : 'refuted', {parts})
        if (fixed) return {inv: rs.length === 1 ? rs[0]! : {op: 'or', xs: rs}, k, parts}
        if (!('tree' in inR) && inR.stuck === 'unknown') { if (over()) return 'paused'; return {why: 'containment unknown', k} }
        wgoal.hyps.push(off(q), {op: 'not', x: out.itp})
        rs.push(out.itp); parts++
        add(off(`sel@${front}`), true)
        front = frontierOf(out.itp)
      }
    }
    return {why: 'no depth left', k: 64}
  }
  return {run}
}

// --- The invariant made small ------------------------------------------------------------------------------------------
//
// IMC's invariant R (its frontiers' disjunction) is inductive and keeps the law, but large: the kernel's proof of its
// step reads every frontier at once. Its information made a few clauses (PDR at one frame, R the oracle that
// generalizes): a state the clauses and the law allow, one step from which breaks one of them (a counterexample to
// induction), lies outside R (R is inductive, and within them); its values as a cube of bounds, the bounds R's
// refutation rests on (the assumptions it needed) are a cube no state of R is in: its negation, a clause. Until each
// clause and the law hold after every step from where they all hold: then their conjunction is an inductive invariant,
// each clause a law for the kernel to prove. Each query is of one of two sessions (kernel/cdcl.ts's clausal mode): the
// step from where the kinds, the law and the clauses hold, each target's negation after it behind a selector; and R.
// Undefined where a query is left unknown, or R doesn't refute a counterexample (never, R being inductive).
export function compress(m: Machine, law: Law, R: C, kinds: C[], budget: {until: number, wall?: number}, maxClauses = 200): C[] | undefined {
  const live = liveOf(m, law), one: E = {op: 'const', value: 1}
  const sGoal: Goal = {name: 'a step from the clauses', hyps: [...kinds, law.holds, ...stepHyps(m, live, 1, tidier(new Set()))]}
  const oGoal: Goal = {name: 'the invariant', hyps: [R, ...kinds]}
  const quiet = (n: string) => n.startsWith('t@')
  const S = cdclSession(sGoal, new Map(), {model: true, clausal: true, quiet}), O = cdclSession(oGoal, new Map(), {model: true, clausal: true})
  const after = stateAt(m, 1), clauses: C[] = [], targets: {c: C, sel: string}[] = []
  // (R's atoms, each linear form once)
  const atomsR: Lin[] = [], seenA = new Set<string>(), seenC = new Set<object>()
  const atomsOf = (c: C): void => {
    if (seenC.has(c)) return
    seenC.add(c)
    if (c.op === 'not') return atomsOf(c.x)
    if (c.op === 'and' || c.op === 'or') return c.xs.forEach(atomsOf)
    if (c.op !== '<=' && c.op !== '<' && c.op !== '=') return
    const a = linOfE(c.a), b = linOfE(c.b)
    if (!a || !b) return
    const d = plus(a, b, -1)
    for (const lin of c.op === '<=' ? [d] : c.op === '<' ? [plus(d, {1: 1}, 1)] : [d, plus({}, d, -1)]) { if (!vars(lin).length) continue; const [key] = litVar({lin, holds: true}); if (!seenA.has(key)) { seenA.add(key); atomsR.push(lin) } }
  }
  atomsOf(R)
  const target = (c: C) => { const sel = `t@${targets.length}`; targets.push({c, sel}); sGoal.hyps.push({op: 'or', xs: [{op: '<=', a: one, b: v(sel)}, {op: 'not', x: substC(c, after)}]}) }
  target(law.holds)
  for (let i = 0; i < targets.length;) {
    if (clock() > budget.until || (budget.wall !== undefined && performance.now() > budget.wall)) return undefined
    const out = S.run({nodes: 0, until: budget.until}, budget.wall, [{[targets[i]!.sel]: 1}]) as Refuted
    if (!('tree' in out) && out.why === REFUTED) { i++; continue }
    if ('tree' in out || out.stuck !== 'sat' || !out.witness) { if (env.GDP_SMALL_TRACE) console.error('cti query', 'tree' in out ? 'tree' : out.stuck); return undefined }
    // The counterexample read by R's atoms (a name no row read: 0), each atom as it holds there an assumption of R's
    // session: R is a combination of its atoms, so where they hold as there, R doesn't.
    const w = out.witness, cube = atomsR.map(lin => { let x = lin['1'] ?? 0; for (const n of vars(lin)) x += lin[n]! * Math.max(0, Math.round(w[n] ?? 0)); return x <= 0 ? lin : atomOf(lin, false).lin })
    const o = O.run({nodes: 0, until: budget.until}, budget.wall, cube) as Refuted
    if ('tree' in o || o.why !== REFUTED || !o.assumed?.length) { if (env.GDP_SMALL_TRACE) console.error('oracle', 'tree' in o ? 'tree' : o.stuck, o.assumed); return undefined }

    // The bounds R needs, fewer: each dropped where R still refutes the rest (its own refutation's assumptions kept).
    let core = o.assumed.map(q => cube[q]!)
    for (let j = 0; j < core.length && core.length > 1;) {
      const rest = core.filter((_, q) => q !== j), o2 = O.run({nodes: 0, until: budget.until}, budget.wall, rest) as Refuted
      if (!('tree' in o2) && (o2 as {why?: string}).why === REFUTED && o2.assumed?.length) core = o2.assumed.map(q => rest[q]!); else j++
    }
    // (each bound's negation: n <= x fails where n >= x + 1, n >= x where n <= x − 1)
    const clause: C = {op: 'or', xs: core.map(lin => linLe(atomOf(lin, false).lin))}
    if (env.GDP_SMALL_TRACE) console.error('clause', clauses.length, o.assumed.length, '→', core.length, 'of', cube.length, env.GDP_SMALL_TRACE === '2' ? showC(clause) : '')
    clauses.push(clause); sGoal.hyps.push(clause); target(clause)
    if (clauses.length > maxClauses) return undefined
    i = 0
  }
  return clauses
}
