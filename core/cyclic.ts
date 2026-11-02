// Cyclic proofs found. Untrusted: an instance states the nodes and their uses, kernel/prove.ts grows a tree for every
// goal, and kernel/cyclic.ts checks the whole. The instances are today's induction rules said as one rule, each a
// graph of sequents whose back-edges lower a rank:
//   - a recurrence's lemmas (`recur`): f a map read at x, its two equations facts, each lemma a node at rank (0, x)
//     using every lemma at x − 1; each law between two points a node at rank (1, y), using itself at y − 1 and the lemmas
//     (whose rank, (0, ·), is below)
//   - a machine's laws: the run as maps over time, each state variable s read at time t as s@[t], each input as i@[t],
//     each map M at key k as M@[t + k·Ω] (Ω above the run's length T); the start and every step are facts (each at the
//     time it gives, a step only up to T); each
//     law is a node at rank (t), using every law at t − 1 (a law about every key at the keys the machine's proof names)
//   - a fold over trees: the tree as a table of nodes, a node's children numbered below it (any tree can be), each law a
//     node at rank (n) using every law at both children
// Beyond those, a node may use any node at any terms (nested, mutual, two ranks in order): `proveCyclic` takes the nodes
// as they are given (examples/cyclic.ts).
//
// Translated (machineNodes, recurNodes, foldNodes given the usual proof; core/translate.ts): what the usual route proved,
// made a cyclic proof from its trees rather than searched. The facts are the instance's as above (Bridge.lean's
// cycCanon, recFacts, the fold's table); the nodes, in this order:
//   - machines, laws l_0..l_{L-1}: node i < L the law at t, rank (t, 1), hyps the precondition, t <= T, T < Ω (cycMOk's
//     node), facts the start and the step at t and each map's at the keys it reads, uses node L + i (guard 1 <= t) and
//     node 2L + i (guard t <= 0), its tree made (`carry`). Node L + i the law after a step from t − 1, rank (t, 0):
//     hyps the precondition, 1 <= t, t <= T, T < Ω and the request's assumption at t − 1, facts the functions' at the
//     keys the usual proof names, uses the laws at t − 1 at those keys (guard 0 <= 0), its conclusion the law at the
//     state the step gives over the cells at t − 1 (a write's reads at its key read at the key read), its tree the usual
//     step tree. Node 2L + i the law at the start, rank (0, 0): the usual start goal, k# as k, its tree the usual one.
//     Only the facts and uses the usual tree reads are kept.
//   - then each step law s_j (proveStepLaws): node 3L + 2j after its k steps, rank (t, 0), the usual step law's goal over
//     the cells at t − k..t − 1 (hyps the precondition, k <= t, t <= T, T < Ω, the assumption and `when` at each step's
//     time, the state's equations after each step but the last that the usual tree reads; uses the laws at each of those
//     times; the times t − n at once, over a map one step back at a time, t − 1 − 1), and node
//     3L + 2j + 1 the step law itself, rank (t, 2): hyps the precondition, k <= t, t <= T, T < Ω and `when` at each
//     step's time, its conclusion `then` with plain names at t − k, primed ones at t and a later step's request (i@j) at
//     its time, facts the step at t − k + 1..t (and the maps' at t), its one use node 3L + 2j, its tree made (`carry`).
//     Over several steps a later step reads a map as the usual goal's term over the cells at t − k (its laws there a
//     use only where they read no map), the step law's node reading each cell back to t − k through the maps' steps (its
//     tree carried on its goal sliced first).
//   - a machine with flags that hold at every key is read as its sk machine, the usual goals' closing hypotheses the
//     closing facts at their time (`qflagFacts`); a request allowed (`allowTranslated`) two nodes after the laws'.
//   - a loop's halting (`loopNodes`): its machine's laws and its liveness's step laws as above (kernel.ts's
//     loopObligations); a liveness's certificate is its step laws' proof and its helpful requests' allowed nodes, the
//     claim about runs that never end read from them as from the usual trees (kernel/prove.ts's proveLiveness).
//   - recurrences, lemmas n, laws between b: nodes 0..n+b−1 as above (their trees made), using also node 2n + 2b + i
//     (the lemma at the start, guard x <= 0; a law between at y = x, guard y <= x); nodes n + b.. the lemma (law between)
//     after a step, the usual step goal with x as x − 1, fx as f(x − 1) (y, fy likewise, fx as f(x)); then the start
//     nodes, rank (0, 0, 0) and (1, 0, 0).
//   - folds, laws L: node i the law at a node n, rank (n, 1), using node L + i (guard Kind[n] = 1) and node 2L + i (guard
//     Kind[n] = 0); node L + i from its children, rank (n, 0), hyps n < N, Kind[n] = 1, both children below n and the
//     assumption at n, uses the laws at both children; node 2L + i at a leaf, rank (n, 0).
//
// The switches (the environment; a user needs none): GDP_CERT=usual, the usual trees as every certificate (the fallback
// and the baseline); GDP_CERT_SEARCH=1, a search where a translation fails, within GDP_CERT_MS (10,000 ms); GDP_CYCLIC=1,
// the cross-check (every proof made again as a cyclic proof, a differing verdict throwing; GDP_CYCLIC_LAX=1 only logs it;
// GDP_CYCLIC_ROUTE=translate|search|both, its route). Diagnostics: GDP_CYCLIC_LOG=1, the `cyclic: {...}` lines
// research/cyclic/ratios.ts reads; GDP_CYCLIC_PROF=1, where each proof's time went; GDP_CYCLIC_SLICE=0, every goal grown
// whole; GDP_CYCLIC_DEBUG=1, each goal grown.
import {type C, type E, type Law, type Machine, atMost as le, get, n as k, plus as add, same as eq, walk, x as v} from './machine.ts'
import type {Fold, Goal, Instances, Loop, StepLaw, Subst, Tree} from '../kernel/kernel.ts'
import {assumed, boundOf, foldObligations, livenessParts, loopLiveness, loopMachine, loopObligations, obligations, stepLawObligations, substC, substE, witnessesOf} from '../kernel/kernel.ts'
import {type CNode, type Cyclic, type Fact, type Use, baseHyps, descentGoal, instHyps, mainGoal, premiseGoal, refuseCyclic} from '../kernel/cyclic.ts'
import {cellProducts, clock, counted, fullRate, grow, profile, usedHyps, widen, withDeadline, withinDeadline} from '../kernel/prove.ts'
import {type Reads, type Renamer, type TStats, carry, decide, readsFirst, renamer, translate, tstats} from './translate.ts'
import {env} from './solver.ts'

// What only the search reads: `opaque`, terms it reads as variables of their own in the node's goal (the trees are the
// goal's still: see `widen`); `variants`, the node stated otherwise (fewer facts, other uses), each tried in turn where
// the node isn't proven, a `weak` one (a conclusion that holds outright) leaving no other node to use it.
// `slice`: its goals grown first on what they read (`slice`, `reached`), as the instances below ask; others are grown whole.
// `main`: the node's tree already made (a usual proof's, translated: core/translate.ts), taken as it is, its goal not grown;
// `carry`: its tree made by core/translate.ts's `carry` from its goal (grown as any other where that fails); `sliced`,
// from its goal sliced first (`carried`).
export type NodeSpec = Omit<CNode, 'uses' | 'main'> & {uses: Omit<Use, 'premises' | 'descent'>[], opaque?: E[], variants?: NodeSpec[], weak?: boolean, slice?: boolean, main?: Tree, carry?: boolean | 'sliced'}
export type CyclicVerdict = {proven: true, checked: boolean, proof: Cyclic, why?: string} | {proven: false, checked: false, node: string, goal: string, stuck: string}

const less1 = (a: E): E => ({op: 'sub', a, b: k(1)})
export const and = (...xs: C[]): C => (xs.length === 1 ? xs[0]! : {op: 'and', xs})
export const implies = (a: C, b: C): C => ({op: 'or', xs: [{op: 'not', x: a}, b]})
const yes: C = le(k(0), k(0))
export const vars = (s: Record<string, E>): Subst => ({vars: s, maps: {}, flags: {}})
// A map's cell at time u and key k, in the run's one map over both: u + k·Ω, where Ω is above the run's length T, so
// that no two (u, k) with u <= T meet (u < Ω). Linear in u, and two keys' cells differ by (k − k')·Ω.
const omega = v('O$')
export const pair = (u: E, key: E): E => add(u, {op: 'prod', a: key, b: omega})

// Every goal grown, then the whole checked by the kernel.
// GDP_CYCLIC_PROF=1: each comparison's line also has where the cyclic proof's time went, by goal kind (main, premise,
// descent, the kernel's check): ms, goals, hypotheses, solver and row ms.
export const cyclicProf: Record<string, {ms: number, n: number, hyps: number, solveMs: number, rowsMs: number}> = {}
const profOn = () => env.GDP_CYCLIC_PROF === '1'
export function timedKind<T>(kind: string, hyps: number, f: () => T): T {
  if (!profOn()) return f()
  const was = profile.on, s0 = profile.solveMs, r0 = profile.rowsMs, t0 = performance.now()
  profile.on = true
  try { return f() } finally {
    profile.on = was
    const p = (cyclicProf[kind] ??= {ms: 0, n: 0, hyps: 0, solveMs: 0, rowsMs: 0})
    p.ms += performance.now() - t0; p.n++; p.hyps += hyps; p.solveMs += profile.solveMs - s0; p.rowsMs += profile.rowsMs - r0
  }
}
// Each goal grown first on what it reads: its node's hypotheses and its own last ones (a use's guard, the conclusion
// negated) kept whole, and of the rest (the facts at the node's terms, the uses) only the parts it reaches: a
// conjunction's conjuncts (under a guard, as a step's equations are, one per state variable) each a part of its own; an
// equation that gives a cell (a state variable's value at t, a function's at a key) reached when its cell is, and then
// its terms' cells and its guard's; any other part reached when it shares a cell with what is, or reads none. The
// weaker goal's tree is the whole goal's (`widen`); where the weaker goal isn't refuted, the whole is grown as before.
// GDP_CYCLIC_SLICE=0 grows the whole goal only.
// A cell by what it may be equal to: a run's map read at time u and any key (two keys the prover may prove equal) is
// one, by its map and u; a function's read at any key is one, by the function; a run's other reads are themselves.
const cellsIn = (t: unknown, out = new Set<string>()): Set<string> => {
  walk(t, o => {
    const map = o.map as string
    if (o.op === 'get') { const key = o.key as E; out.add(key.op === 'add' && key.b.op === 'prod' && JSON.stringify(key.b.b) === JSON.stringify(omega) ? `${map}@${JSON.stringify(key.a)}` : map.endsWith('@') ? JSON.stringify(o) : map) }
  })
  return out
}
// A hypothesis' parts: through its conjunctions and its guarded parts (¬g ∨ x), each part with the guards it is under;
// and the hypothesis rebuilt from some of them (each part dropped weakens it).
type Part = {c: C, guards: C[]}
function partsOf(c: C, guards: C[] = [], out: Part[] = []): Part[] {
  if (c.op === 'and') c.xs.forEach(x => partsOf(x, guards, out))
  else if (c.op === 'or' && c.xs.length === 2 && c.xs[0]!.op === 'not') partsOf(c.xs[1]!, [...guards, c.xs[0]!], out)
  else out.push({c, guards})
  return out
}
function rebuild(c: C, keep: (j: number) => boolean, at = {j: 0}): C | undefined {
  if (c.op === 'and') { const xs = c.xs.flatMap(x => { const y = rebuild(x, keep, at); return y ? [y] : [] }); return xs.length ? and(...xs) : undefined }
  if (c.op === 'or' && c.xs.length === 2 && c.xs[0]!.op === 'not') { const b = rebuild(c.xs[1]!, keep, at); return b && {op: 'or', xs: [c.xs[0]!, b]} }
  return keep(at.j++) ? c : undefined
}
// The hypotheses with a part the goal reaches (whole ones included).
export function reached(g: Goal, whole: (i: number) => boolean): Set<number> { return slice(g, whole, true) as Set<number> }
// `join: false`: no equation joins the conclusion (the goal's layout kept: core/translate.ts's `carry` reads it).
export function slice(g: Goal, whole: (i: number) => boolean, hypsOnly?: false, join?: boolean): (Goal & {from: number[][]}) | undefined
export function slice(g: Goal, whole: (i: number) => boolean, hypsOnly: true): Set<number>
export function slice(g: Goal, whole: (i: number) => boolean, hypsOnly = false, join = true): (Goal & {from: number[][]}) | Set<number> | undefined {
  const reach = new Set<string>(), parts = g.hyps.map(h => partsOf(h))
  const pieces: (Part & {i: number, j: number, gives?: string, cells: Set<string>})[] = []
  g.hyps.forEach((h, i) => {
    if (whole(i)) { cellsIn(h, reach); return }
    parts[i]!.forEach(({c, guards}, j) => {
      // (an equation between two reads, a law's, gives neither: it is reached by either)
      const gives = c.op === '=' && c.a.op === 'get' && c.b.op !== 'get' ? [...cellsIn(c.a)][0] : undefined, cells = cellsIn(c.op === '=' && gives ? c.b : c)
      for (const x of guards) cellsIn(x, cells)
      pieces.push({c, guards, i, j, gives, cells})
    })
  })
  const kept = new Set<number>()
  for (let grew = true; grew;) {
    grew = false
    for (const [q, p] of pieces.entries()) {
      if (kept.has(q) || (p.gives ? !reach.has(p.gives) : p.cells.size && ![...p.cells].some(c => reach.has(c)))) continue
      kept.add(q); grew = true
      for (const c of p.cells) reach.add(c)
      if (p.gives) reach.add(p.gives)
    }
  }
  if (hypsOnly) return new Set(g.hyps.flatMap((_, i) => (whole(i) || pieces.some((p, q) => p.i === i && kept.has(q)) ? [i] : [])))
  // The equations that give a cell the conclusion reads (a step's, the start's) join the conclusion, under their guards:
  // the prover splits the conclusion's atoms first, as the usual rule does a law read after the step.
  const last = g.hyps.length - 1, concl = whole(last) ? cellsIn(g.hyps[last]) : new Set<string>()
  const joins = (p: typeof pieces[number]) => join && !!p.gives && concl.has(p.gives)
  if (kept.size === pieces.length && !pieces.some(joins)) return undefined
  const stays = new Set<string>(), joined: C[] = []
  for (const [q, p] of pieces.entries()) if (kept.has(q)) { if (joins(p)) joined.push(p.guards.reduceRight<C>((acc, x) => ({op: 'or', xs: [x, acc]}), p.c)); else stays.add(`${p.i}:${p.j}`) }
  const from: number[][] = [], joinedFrom = [...new Set(pieces.flatMap((p, q) => (kept.has(q) && joins(p) ? [p.i] : [])))]
  const hyps = g.hyps.flatMap((h, i) => {
    const r = whole(i) || parts[i]!.every((_, j) => stays.has(`${i}:${j}`)) ? h : rebuild(h, j => stays.has(`${i}:${j}`))
    if (r) from.push([i])
    return r ? [r] : []
  })
  if (joined.length) { hyps[hyps.length - 1] = and(hyps.at(-1)!, ...joined); from[from.length - 1]!.push(...joinedFrom) }
  return {name: g.name, hyps, from}
}
const withProducts = <T>(f: () => T): T => { const was = cellProducts.on; cellProducts.on = true; try { return f() } finally { cellProducts.on = was } }
let sliceNow = false
const sliceOn = () => sliceNow && env.GDP_CYCLIC_SLICE !== '0'
// Trees already grown, by their goal (a node met again: a recurrence's lemmas in its laws between, a machine proven again),
// with the facts and uses a node's own goal kept.
// (Each route its own: `proveCyclic(..., cache)`, so that one route's trees don't time another's.)
type Grown = Map<string, {tree: Tree, insts?: number[], uses?: number[]}>
const searched: Grown = new Map()
export const translatedCache: Grown = new Map()
type Stuck = {proven: false, checked: false, node: string, goal: string, stuck: string}
// `order`: the order the nodes are grown in, by default those with a weak variant first (a variant that uses a weak node
// is passed over).
// `made`: the first nodes already made (a proof of the same facts whose nodes these specs begin with), taken as they are.
export function proveCyclic(facts: Fact[], specs: NodeSpec[], order0?: number[], grownBefore: Grown = searched, st: TStats = tstats(), made: CNode[] = []): CyclicVerdict {
  const order = (order0 ?? [...specs.keys()].sort((i, j) => Number(!specs[i]!.variants?.some(x => x.weak)) - Number(!specs[j]!.variants?.some(x => x.weak)))).filter(i => i >= made.length)
  const nodes: CNode[] = [...made], shapes = [...specs], weak = new Set<number>()
  let later: number | undefined, refuted = false
  // A goal's tree, and the hypotheses its leaves read (of the whole goal, a weaker goal's read through where they came from).
  const grown = (g: Goal, node: string, own: (i: number) => boolean): {tree: Tree, from: Goal, used: () => Set<number>} | Stuck => {
    const was = cellProducts.on, kind = g.name.endsWith('its rank below') ? 'descent' : g.name.includes(': use of node') ? 'premise' : 'main'
    cellProducts.on = true
    try {
      const sliced = sliceOn() ? slice(g, own) : undefined, part = sliced && hide(sliced)
      if (part) {
        // (within two seconds: a weaker goal no easier than the whole is left to the whole)
        const t0 = performance.now(), p = timedKind(`${kind} sliced`, part.hyps.length, () => grow(part, new Map(), {nodes: 0, until: clock() + Math.min(2_000, later ?? 2_000)}))
        if (env.GDP_CYCLIC_DEBUG) console.error(`[cyc] ${g.name}: ${part.hyps.length} hyps${part !== sliced ? ' (opaque)' : ''}, ${'tree' in p ? `${p.nodes} nodes` : p.stuck}, ${Math.round(performance.now() - t0)} ms`)
        if ('tree' in p) return {tree: p.tree, from: part, used: () => new Set([...usedHyps(part, p.tree)].flatMap(i => part.from[i]!))}
        if (part !== sliced) {
          const q = timedKind(`${kind} sliced`, sliced.hyps.length, () => grow(sliced, new Map(), {nodes: 0, until: clock() + Math.min(2_000, later ?? 2_000)}))
          if ('tree' in q) return {tree: q.tree, from: sliced, used: () => new Set([...usedHyps(sliced, q.tree)].flatMap(i => sliced.from[i]!))}
        }
      }
      const o = timedKind(kind, g.hyps.length, () => grow(g, new Map(), {nodes: 0, until: clock() + (later ?? Math.max(20_000, 1_000 * g.hyps.length))}))
      return 'tree' in o ? {tree: o.tree, from: g, used: () => usedHyps(g, o.tree)} : {proven: false, checked: false, node, goal: g.name, stuck: o.stuck}
    } finally { cellProducts.on = was }
  }
  // The tree made the goal's own (a weaker goal's widened), or grown on the goal itself where that fails.
  const own = (r: {tree: Tree, from: Goal}, g: Goal): Tree | undefined => (r.from === g ? r.tree : timedKind('widen', 0, () => widen(r.from, g, r.tree, opaqueOf.get(r.from))))
  const whole = (g: Goal, node: string, mine: (i: number) => boolean): Tree | Stuck => {
    const key = JSON.stringify(g.hyps), before = grownBefore.get(key)
    if (before) return before.tree
    const r = grown(g, node, mine)
    if ('proven' in r) return r
    const t = own(r, g) ?? (() => { const o = grow(g); return 'tree' in o ? o.tree : undefined })()
    if (!t) return {proven: false, checked: false, node, goal: g.name, stuck: 'unknown'}
    if (grownBefore.size >= 4096) grownBefore.clear()
    grownBefore.set(key, {tree: t})
    return t
  }
  // A goal with the node's opaque terms read as variables (z$0, z$1, ...), remembered with them for `widen`.
  const opaqueOf = new WeakMap<Goal, Record<string, E>>()
  let hidden: E[] = []
  const hide = <G extends Goal>(g: G): G => {
    if (!hidden.length) return g
    let text = JSON.stringify(g.hyps)
    const names: Record<string, E> = {}
    hidden.forEach((e, i) => { const id = JSON.stringify(e); if (text.includes(id)) { text = text.replaceAll(id, JSON.stringify(v(`z$${i}`))); names[`z$${i}`] = e } })
    if (!Object.keys(names).length) return g
    const out = {...g, hyps: JSON.parse(text) as C[]}
    opaqueOf.set(out, names)
    return out
  }
  // A node's tree made from its goal (core/translate.ts's `carry`): first on the goal sliced (its facts' parts the
  // conclusion and the uses reach: a step's equations for state the law doesn't read, whose choices `carry` would
  // otherwise split at every leaf, left out), the tree then the whole goal's (`widen`); else on the whole goal.
  const carried = (n1: Omit<CNode, 'uses' | 'main'> & {uses: NodeSpec['uses']}, first: boolean): Tree | undefined => {
    const g = mainGoal(facts, shapes, n1), h0 = n1.hyps.length, base = baseHyps(facts, n1).length, last = g.hyps.length - 1
    const part = first && sliceOn() ? slice(g, i => i < h0 || i >= base, false, false) : undefined
    if (part) {
      const nf = part.from.filter(f => f[0]! >= h0 && f[0]! < base).length, nu = part.from.filter(f => f[0]! >= base && f[0]! < last).length
      const tree = carry(part, nf, nu, st, clock() + 2_000), wide = tree && timedKind('widen', 0, () => widen(part, g, tree))
      if (env.GDP_CYCLIC_DEBUG) console.error(`[carry] ${n1.name}: ${part.hyps.length} of ${g.hyps.length} hyps, ${tree ? (wide ? 'carried, widened' : 'carried, not widened') : 'not carried'}`)
      if (wide) return wide
    }
    return carry(g, n1.insts.length, n1.uses.length, st, clock() + 2_000)
  }
  // A node's goal grown; then the node keeps only the facts and uses its tree reads (the fewer, the fewer hypotheses its
  // goal has for the kernel to read at every leaf, and the fewer uses to prove below); then each use's goals.
  const attempt = ({opaque, variants: _v, weak: _w, slice: sl, main: given0, carry: made, ...n0}: NodeSpec): CNode | Stuck => {
    hidden = opaque ?? []
    sliceNow = !!sl
    // A goal's own hypotheses: the node's, and those after its facts and uses.
    const n1 = {...n0, insts: n0.insts.filter(p => facts[p.fact])}
    const given = given0 ?? (made ? timedKind('carry', 0, () => withProducts(() => carried(n1, made === 'sliced'))) : undefined)
    if (made && !given0) { if (given) st.carried++; else st.uncarried++ }
    const base = baseHyps(facts, n1).length, mine = (tail: number) => (i: number) => i < n1.hyps.length || i >= base + tail
    const g = given ? undefined : mainGoal(facts, shapes, n1), key = g ? JSON.stringify(g.hyps) : '', before = g && grownBefore.get(key)
    let n = n1, main: Tree | undefined = given, src: {tree: Tree, from: Goal} | undefined
    if (!g) { /* the tree given */ }
    else if (before) { n = {...n1, insts: before.insts?.map(i => n1.insts[i]!) ?? n1.insts, uses: before.uses?.map(j => n1.uses[j]!) ?? n1.uses}; main = before.tree; src = {tree: main, from: mainGoal(facts, shapes, n)} }
    else {
      // First the node with only the facts and uses its goal reaches, its goal grown as it is (within two seconds).
      const h0 = n1.hyps.length, keep = sliceOn() ? reached(g, mine(n1.uses.length)) : undefined
      const n2 = keep && {...n1, insts: n1.insts.filter((_, i) => keep.has(h0 + i)), uses: n1.uses.filter((_, j) => keep.has(base + j))}
      if (n2 && (n2.insts.length < n1.insts.length || n2.uses.length < n1.uses.length)) {
        const g2 = mainGoal(facts, shapes, n2), part = hide(g2)
        const p = timedKind('main selected', g2.hyps.length, () => withProducts(() => grow(part, new Map(), {nodes: 0, until: clock() + Math.min(2_000, later ?? 2_000)})))
        if (env.GDP_CYCLIC_DEBUG) console.error(`[cyc] ${g.name}: ${g2.hyps.length} of ${g.hyps.length} hyps selected, ${'tree' in p ? `${p.nodes} nodes` : p.stuck}`)
        const t = 'tree' in p ? own({tree: p.tree, from: part}, g2) : undefined
        if (t && 'tree' in p) { n = n2; main = t; src = {tree: p.tree, from: part} }
      }
      // Then the whole node, its goal sliced; it keeps the facts and uses its tree reads.
      if (!main) {
        const r = grown(g, n1.name, mine(n1.uses.length))
        if ('proven' in r) return r
        const used = sliceOn() ? timedKind('used', 0, r.used) : undefined
        const trim = used ? {...n1, insts: n1.insts.filter((_, i) => used.has(h0 + i)), uses: n1.uses.filter((_, j) => used.has(base + j))} : n1
        const g2 = trim.insts.length < n1.insts.length || trim.uses.length < n1.uses.length ? mainGoal(facts, shapes, trim) : g
        const t2 = own(r, g2)
        main = t2 ?? own(r, g) ?? (() => { const o = grow(g); return 'tree' in o ? o.tree : undefined })()
        if (!main) return {proven: false, checked: false, node: n1.name, goal: g.name, stuck: 'unknown'}
        if (t2) n = trim
        src = {tree: r.tree, from: r.from}
      }
      if (grownBefore.size >= 4096) grownBefore.clear()
      grownBefore.set(key, {tree: main, insts: n.insts.map(p => n1.insts.indexOf(p)), uses: n.uses.map(u => n1.uses.indexOf(u))})
    }
    hidden = []
    // Each use's goals; where one isn't proven with the facts the node kept, again with all of them.
    const usesOf = (n: Omit<CNode, 'uses' | 'main'> & {uses: NodeSpec['uses']}): Use[] | Stuck => {
      const nb = baseHyps(facts, n).length, mine2 = (i: number) => i < n.hyps.length || i >= nb, out: Use[] = []
      for (const u of n.uses) {
        const m = shapes[u.node]
        if (!m) return {proven: false, checked: false, node: n.name, goal: `use of node ${u.node}`, stuck: 'no such node'}
        const premises: Tree[] = []
        for (const [i, c] of m.hyps.entries()) {
          const t = whole(premiseGoal(facts, n, u, c, i), n.name, mine2)
          if ('proven' in t && env.GDP_CYCLIC_DEBUG) console.error(`[premise] ${n.name}: use of node ${u.node}, its hypothesis ${i} (${t.stuck}): ${JSON.stringify(substC(c, vars(u.subst)))}`)
          if ('proven' in t) return t
          premises.push(t)
        }
        const descent = whole(descentGoal(facts, n, u, m), n.name, mine2)
        if ('proven' in descent) return descent
        out.push({...u, premises, descent})
      }
      return out
    }
    const uses = usesOf(n)
    if (!('proven' in uses)) return {...n, uses, main: main!}
    if (n.insts.length === n1.insts.length || !src) return uses
    const n3 = {...n, insts: n1.insts}, main3 = own(src, mainGoal(facts, shapes, n3)), uses3 = main3 ? usesOf(n3) : uses
    return main3 && !('proven' in uses3) ? {...n3, uses: uses3, main: main3} : uses
  }
  for (const i of order) {
    let failed: Stuck | undefined
    for (const [j, spec] of [specs[i]!, ...(specs[i]!.variants ?? [])].entries()) {
      // (a variant after the first within a few seconds a goal, one second once a node is refuted: a variant the first
      // wasn't proven by is seldom needed, and seldom proves a node where another is refuted)
      // (a translated node's goals, its uses' among them, within four: past that its translation isn't kept, the usual
      // trees are)
      later = j ? (refuted ? 1_000 : 3_000) : spec.main || spec.carry ? 4_000 : undefined
      if (spec.uses.some(u => weak.has(u.node))) continue
      const r = attempt(spec)
      if ('proven' in r) { failed ??= r; if (r.stuck === 'sat') refuted = true; continue }
      nodes[i] = r; shapes[i] = spec; failed = undefined
      if (spec.weak) weak.add(i)
      break
    }
    if (failed || !nodes[i]) return failed ?? {proven: false, checked: false, node: specs[i]!.name, goal: specs[i]!.name, stuck: 'unknown'}
  }
  // (GDP_CYCLIC_PROF: the nodes made before, checked again within the whole, timed apart too)
  if (profOn() && made.length) timedKind('check, of the nodes made before', 0, () => refuseCyclic({facts, nodes: made}))
  const proof: Cyclic = {facts, nodes}, why = timedKind('check', 0, () => refuseCyclic(proof))
  return {proven: true, checked: why === undefined, proof, ...(why ? {why} : {})}
}

// Hypotheses as their conjuncts, each a hypothesis of its own: a node used with them proves each premise apart, a goal
// as small as the conjunct (a premise that is a conjunction of disjunctions, refuted against itself, would be split
// case by case through every conjunct), and the rows its goal has are the same.
const conjuncts = (cs: C[]): C[] => cs.flatMap(c => (c.op === 'and' ? conjuncts(c.xs) : [c]))
// An instance's nodes, and their variants, grown first on what their goals read.
const sliced = (specs: NodeSpec[]): NodeSpec[] => specs.map(sp => ({...sp, slice: true, ...(sp.variants ? {variants: sp.variants.map(x => ({...x, slice: true}))} : {})}))

// A law's keys (its key at every value, then its further keys); the tuples of terms a proof's instances name it at; the
// fresh key k# a usual proof proves a law about every key at, as the law's own key.
const keysOf = (l: Law): string[] => [...(l.forall ? [l.forall] : []), ...(l.keys ?? [])]
const tuples = (inst: Instances, l: Law): E[][] => { const ks = keysOf(l), flat = inst[l.name] ?? []; return ks.length ? Array.from({length: Math.floor(flat.length / ks.length)}, (_, i) => flat.slice(i * ks.length, (i + 1) * ks.length)) : [[]] }
const freshOf = (laws: Law[]): Record<string, E> => Object.fromEntries(laws.flatMap(x => (x.forall ? [[`${x.forall}#`, v(x.forall)]] : [])))
// The facts of a machine's functions (laws about every key of them), as cyclic facts.
const factOf = (l: Law): Fact => ({name: l.name, keys: keysOf(l), holds: l.holds})

// --- recurrences ----------------------------------------------------------------------------------------------------

// A recurrence f(0) = zero, f(x + 1) = next(x, f(x)), its further arguments fixed (plain variables here, as along the
// recursion), and the functions it reads with their facts. Each lemma reads x and fx; each law between two points x, fx,
// y, fy (for x <= y).
export type RecurCase = {name: string, args: string[], zero: E, next: E, lemmas: {name: string, holds: C}[], between: {name: string, holds: C}[], facts: Law[]}
// A usual proof of a machine's laws (kernel/prove.ts's proveLaws): the machine, its laws, the instances and trees.
export type UsualProof = {m: Machine, laws: Law[], proof: {instances: Record<string, Instances>, trees: Record<string, Tree>}}
// `usual`: the usual proofs of the lemmas (the recurrence run as a machine from x = 0) and of the laws between (y from x),
// translated (`translatedRecur` below), or no nodes with why not.
export function recurNodes(r: RecurCase, usual?: {lemmas?: UsualProof, between?: UsualProof}, st: TStats = tstats()): {facts: Fact[], specs: NodeSpec[], why?: string} {
  const f = `${r.name}$`, x = v('x'), y = v('y'), kk = v('k$')
  const facts: Fact[] = [
    {name: `${r.name}(0)`, keys: [], holds: eq(get(f, k(0)), r.zero)},
    {name: `${r.name}(x + 1)`, keys: ['k$'], holds: eq(get(f, add(kk, k(1))), substE(r.next, vars({x: kk, prev: get(f, kk)})))},
    ...r.facts.map(factOf),
  ]
  const at = (t: E) => vars({x: t, fx: get(f, t)})
  const n = r.lemmas.length
  const lemmaUses = (to: E, guard: C) => r.lemmas.map((_, j) => ({node: j, subst: {x: to}, guard}))
  const specs: NodeSpec[] = r.lemmas.map(l => ({
    name: `${r.name}: ${l.name}`, hyps: [], concl: substC(l.holds, at(x)), rank: [k(0), x],
    insts: [{fact: 0, at: []}, {fact: 1, at: [less1(x)]}], uses: lemmaUses(less1(x), le(k(1), x)),
  }))
  // A law between two points: for every x <= y, by induction on y from x, the lemmas at x, at y and at y − 1.
  for (const b of r.between) specs.push({
    name: `${r.name}: ${b.name}`, hyps: [], rank: [k(1), y],
    concl: implies(le(x, y), substC(b.holds, vars({x, fx: get(f, x), y, fy: get(f, y)}))),
    insts: [{fact: 1, at: [less1(y)]}],
    uses: [...r.between.map((_, j) => ({node: n + j, subst: {y: less1(y)}, guard: le(add(x, k(1)), y)})), ...lemmaUses(x, yes), ...lemmaUses(y, yes), ...lemmaUses(less1(y), le(k(1), y))],
  })
  // Each lemma and law twice, as a machine's laws are: at x (rank (0, x, 1)),
  // from f(0) or from the lemma after a step to x, rank (0, x, 0), read at next(x − 1, f(x − 1)) (the usual rule's step
  // goal) and using every lemma at x − 1; a law between x and y likewise at y (rank (1, y, ·)), after a step to y using
  // the laws at y − 1 and the lemmas at x and y − 1.
  const b = r.between.length, step = (e: E) => substE(r.next, vars({x: less1(e), prev: get(f, less1(e))}))
  const atStep = (l: {holds: C}) => substC(l.holds, vars({x, fx: step(x)}))
  const lemmaAfter = r.lemmas.map((l): NodeSpec => {
    const name = `${r.name}: ${l.name}, after a step`, hyps = [le(k(1), x)]
    return {name, hyps, concl: atStep(l), rank: [k(0), x, k(0)], insts: [], uses: lemmaUses(less1(x), yes), variants: [{name, hyps, concl: yes, rank: [k(0), x, k(0)], insts: [], uses: [], weak: true}]}
  })
  const betweenAfter = r.between.map((l): NodeSpec => {
    const name = `${r.name}: ${l.name}, after a step`, hyps = [le(add(x, k(1)), y)]
    return {name, hyps, concl: substC(l.holds, vars({x, fx: get(f, x), y, fy: step(y)})), rank: [k(1), y, k(0)], insts: [],
      uses: [...r.between.map((_, j) => ({node: n + j, subst: {y: less1(y)}, guard: yes})), ...lemmaUses(x, yes), ...lemmaUses(less1(y), yes)],
      variants: [{name, hyps, concl: yes, rank: [k(1), y, k(0)], insts: [], uses: [], weak: true}]}
  })
  const own = specs.map((sp, i): NodeSpec => {
    const lemma = i < n, a: NodeSpec = {...sp, rank: [...sp.rank, k(1)], insts: lemma ? sp.insts : [{fact: 1, at: [less1(y)]}],
      uses: lemma ? [{node: n + b + i, subst: {}, guard: le(k(1), x)}] : [{node: 2 * n + b + (i - n), subst: {}, guard: le(add(x, k(1)), y)}, ...lemmaUses(x, yes), ...lemmaUses(y, yes)],
      variants: [{...sp, rank: [...sp.rank, k(1)]}]}
    return a
  })
  if (usual) return {facts, ...translatedRecur()}
  const all = withReads(facts, [...own, ...lemmaAfter, ...betweenAfter])
  for (const [i, a] of all.slice(0, n + b).entries()) { const o = shared(facts, a, all[n + b + i]!.concl); if (o.length) all[i] = {...a, opaque: o} }
  return {facts, specs: sliced(all.map(sp => (sp.variants ? {...sp, variants: withReads(facts, sp.variants, all)} : sp)))}

  // The usual proofs translated, as a machine's are: each lemma and law between three nodes. At x (at y), as above, its
  // goal grown: from f(0) or the lemma at the start (x <= 0), or after a step to x (1 <= x). After a step, rank (0, x, 0):
  // the usual step goal with x as x − 1 and fx as f(x − 1), the lemmas at x − 1 its uses; a law between likewise at y − 1
  // (rank (1, y, 0)), fx as f(x), its uses the lemmas at x (the usual machine's facts) and at y − 1 and the laws between
  // at y − 1 (each antecedent x <= y − 1 split first). At the start, rank (0, 0, 0) and (1, 0, 0): the usual start goal,
  // fx0 as f(0) (a start that reads a function), fx as f(x).
  function translatedRecur(): {specs: NodeSpec[], why?: string} {
    const lemmaAfterT: NodeSpec[] = [], betweenAfterT: NodeSpec[] = [], lemmaStart: NodeSpec[] = [], betweenStart: NodeSpec[] = []
    const made: Made[] = [], N = 2 * n + 2 * b
    const factIx = (name: string) => facts.findIndex((q, i) => i >= 2 && q.name === name)
    // A usual goal's hypotheses: the machine's facts at the instances, its precondition and assumption, the laws assumed.
    const layout = (u: UsualProof, i: number) => {
      const g = obligations(u.m, u.laws, u.proof.instances, i), inst = u.proof.instances[u.laws[i]!.name] ?? {}
      const fs = (u.m.facts ?? []).flatMap(q => { const ks = [...(q.forall ? [q.forall] : []), ...(q.keys ?? [])], flat = inst[q.name] ?? []; return ks.length ? Array.from({length: Math.floor(flat.length / ks.length)}, (_, j) => ({fact: q, at: flat.slice(j * ks.length, (j + 1) * ks.length)})) : [{fact: q, at: [] as E[]}] })
      const np = u.m.pre ? 1 : 0, na = u.m.assume ? 1 : 0
      return {g0: g[0]!, g1: g[1]!, t0: u.proof.trees[g[0]!.name], t1: u.proof.trees[g[1]!.name], fs, np, na, ok: g[0]!.hyps.length === fs.length + np + 1 && g[1]!.hyps.length === fs.length + np + na + u.laws.length + 1}
    }
    const last = (g: Goal) => (g.hyps.at(-1) as Extract<C, {op: 'not'}>).x
    if (n) {
      const u = usual!.lemmas
      if (!u || u.laws.map(l => l.name).join('\0') !== r.lemmas.map(l => l.name).join('\0') || u.laws.some(l => l.forall)) return {specs: [], why: 'lemmas: no usual proof of these lemmas'}
      const sigma = vars({x: less1(x), fx: get(f, less1(x))}), sigma0 = vars({fx0: get(f, k(0))}), ren = renamer({s: sigma}), ren0 = renamer({s: sigma0})
      for (const [i] of r.lemmas.entries()) {
        const lay = layout(u, i)
        if (!lay.ok || !lay.t0 || !lay.t1) return {specs: [], why: `${r.lemmas[i]!.name}: a usual goal of another shape`}
        const used1 = usedHyps(lay.g1, lay.t1), used0 = usedHyps(lay.g0, lay.t0), insts1: NodeSpec['insts'] = [], insts0: NodeSpec['insts'] = []
        for (const [q, p] of lay.fs.entries()) {
          const zeroFact = p.fact.name.startsWith('fx0 is '), ix = zeroFact ? 0 : factIx(p.fact.name)
          for (const [used, out, s] of [[used1, insts1, sigma], [used0, insts0, sigma0]] as const) {
            if (!used.has(q)) continue
            if (ix < 0 || (zeroFact && s === sigma)) return {specs: [], why: `${p.fact.name}: no fact of the recurrence's`}
            out.push({fact: ix, at: p.at.map(e => substE(e, s))})
          }
        }
        const pre = u.m.pre ? [substC(u.m.pre, sigma)] : []
        lemmaAfterT.push({name: `${r.name}: ${r.lemmas[i]!.name}, after a step`, hyps: [le(k(1), x), ...pre, ...(u.m.assume ? [substC(u.m.assume, sigma)] : [])], concl: substC(last(lay.g1), sigma), rank: [k(0), x, k(0)],
          insts: insts1, uses: lemmaUses(less1(x), yes).filter((_, j) => used1.has(lay.fs.length + lay.np + lay.na + j))})
        lemmaStart.push({name: `${r.name}: ${r.lemmas[i]!.name}, at the start`, hyps: u.m.pre ? [u.m.pre] : [], concl: substC(last(lay.g0), sigma0), rank: [k(0), k(0), k(0)], insts: insts0, uses: []})
        made.push({g: lay.g1, tree: lay.t1, node: n + b + i, ren}, {g: lay.g0, tree: lay.t0, node: N + i, ren: ren0})
      }
    }
    if (b) {
      const u = usual!.between, lemmaAt = (name: string) => r.lemmas.findIndex(l => `${l.name} at x` === name)
      if (!u || u.laws.slice(n).map(l => l.name).join('\0') !== r.between.map(l => l.name).join('\0') || u.laws.some(l => l.forall)) return {specs: [], why: 'between: no usual proof of these laws'}
      const sigma = vars({y: less1(y), fy: get(f, less1(y)), fx: get(f, x)}), sigma0 = vars({fx: get(f, x)}), ren = renamer({s: sigma}), ren0 = renamer({s: sigma0})
      for (const [i] of r.between.entries()) {
        const lay = layout(u, n + i)
        if (!lay.ok || !lay.t0 || !lay.t1) return {specs: [], why: `${r.between[i]!.name}: a usual goal of another shape`}
        const used1 = usedHyps(lay.g1, lay.t1), used0 = usedHyps(lay.g0, lay.t0)
        const parts = (used: Set<number>, s: Subst, after: boolean): {insts: NodeSpec['insts'], uses: NodeSpec['uses']} | undefined => {
          const insts: NodeSpec['insts'] = [], uses: NodeSpec['uses'] = []
          for (const [q, p] of lay.fs.entries()) {
            if (!used.has(q)) continue
            const j = lemmaAt(p.fact.name), ix = factIx(p.fact.name)
            if (j >= 0) uses.push({node: j, subst: {x}, guard: yes})
            else if (ix >= 0) insts.push({fact: ix, at: p.at.map(e => substE(e, s))})
            else return undefined
          }
          if (after) for (const [j] of u.laws.entries()) if (used.has(lay.fs.length + lay.np + lay.na + j)) uses.push(j < n ? {node: j, subst: {x: less1(y)}, guard: yes} : {node: j, subst: {y: less1(y)}, guard: yes})
          return {insts, uses}
        }
        const p1 = parts(used1, sigma, true), p0 = parts(used0, sigma0, false)
        if (!p1 || !p0) return {specs: [], why: `${r.between[i]!.name}: a fact of no recurrence's`}
        const pre = u.m.pre ? [substC(u.m.pre, sigma)] : []
        betweenAfterT.push({name: `${r.name}: ${r.between[i]!.name}, after a step`, hyps: [le(add(x, k(1)), y), ...pre, ...(u.m.assume ? [substC(u.m.assume, sigma)] : [])], concl: substC(last(lay.g1), sigma), rank: [k(1), y, k(0)], ...p1})
        betweenStart.push({name: `${r.name}: ${r.between[i]!.name}, at the start`, hyps: u.m.pre ? [u.m.pre] : [], concl: substC(last(lay.g0), sigma0), rank: [k(1), k(0), k(0)], ...p0})
        made.push({g: lay.g1, tree: lay.t1, node: 2 * n + b + i, ren, decide: p1.uses.flatMap(us => (us.node >= n && us.node < n + b ? [le(x, less1(y))] : []))}, {g: lay.g0, tree: lay.t0, node: N + n + i, ren: ren0})
      }
    }
    const carried = own.map((sp, i): NodeSpec => ({...sp, variants: undefined, carry: true, uses: [...sp.uses, i < n ? {node: N + i, subst: {}, guard: le(x, k(0))} : {node: N + i, subst: {}, guard: le(y, x)}]}))
    const rest = [...lemmaAfterT, ...betweenAfterT, ...lemmaStart, ...betweenStart], all = [...withReads(facts, carried, [...carried, ...rest]), ...rest]
    for (const [i, a] of all.slice(0, n + b).entries()) { const o = [...new Set([...shared(facts, a, all[n + b + i]!.concl), ...shared(facts, a, all[N + i]!.concl)].map(e => JSON.stringify(e)))].map(e => JSON.parse(e) as E); if (o.length) all[i] = {...a, opaque: o} }
    const until = withinDeadline(clock() + 10_000)
    return translateMade(facts, all, made, st, until)
  }
}

// Function facts at the keys a node's goal reads them at: each fact about every key of a function read f[k] (the key
// alone) at each key f is read at, twice over (a fact's own reads give more keys).
function withReads(facts: Fact[], specs: NodeSpec[], nodes: NodeSpec[] = specs): NodeSpec[] {
  const simple = facts.flatMap((f, i) => {
    if (f.keys.length !== 1) return []
    const reads = [...JSON.stringify(f.holds).matchAll(/"op":"get","map":"([^"]+)","key":\{"op":"var","name":"([^"]+)"\}/g)].filter(m => m[2] === f.keys[0])
    return reads.map(m => ({fact: i, map: m[1]!}))
  })
  if (!simple.length) return specs
  const readsIn = (t: unknown, map: string): E[] => { const out: E[] = []; walk(t, o => { if (o.op === 'get' && o.map === map) out.push(o.key as E) }); return out }
  return specs.map(n => {
    const insts = [...n.insts], seen = new Set(insts.map(p => JSON.stringify(p)))
    for (let round = 0; round < 2; round++) {
      const goal = [n.hyps, n.concl, insts.map(p => substC(facts[p.fact]!.holds, vars(Object.fromEntries(facts[p.fact]!.keys.map((key, i) => [key, p.at[i]!]))))), n.uses.map(u => substC(nodes[u.node]!.concl, vars(u.subst)))]
      for (const s of simple) for (const key of readsIn(goal, s.map)) {
        const p = {fact: s.fact, at: [key]}, id = JSON.stringify(p)
        if (!seen.has(id)) { seen.add(id); insts.push(p) }
      }
    }
    return {...n, insts}
  })
}

// --- machines -------------------------------------------------------------------------------------------------------

// The machines this instance covers: no history (its plain machine is one: kernel.ts's historyMachine), and no law that
// reads a map at a key read from a map of the state (a table of nodes: a node's fold at its child), whose cells a run's maps put at keys
// the prover would have to prove equal through products (`machineNodes` proves those laws far slower than the usual
// rule, past its budget: research/cyclic/probe.ts).
export const cyclicMachine = (m: Machine, laws: Law[] = []): boolean => uncoveredWhy(m, laws) === undefined
// Why a machine's laws are no instance's (undefined where they are one).
export const uncoveredWhy = (m: Machine, laws: Law[] = []): string | undefined => {
  const maps = Object.keys(m.maps ?? {})
  const nested = (t: unknown): boolean => { let found = false; const walk = (x: unknown, inKey: boolean): void => { if (found || !x || typeof x !== 'object') return; const o = x as Record<string, unknown>; if (o.op === 'get' && inKey && maps.includes(o.map as string)) { found = true; return } if (o.op === 'get') { walk(o.key, true); return } for (const val of Object.values(o)) walk(val, inKey) }; walk(t, false); return found }
  return m.history ? 'a history' : laws.some(l => nested(l.holds)) ? 'a law reading a map at a key read from a map' : undefined
}

// A loop's halting as a machine's (kernel.ts's loopObligations: the loop's machine, its laws, and its liveness's step
// laws: each turn stays or gets there, the rank kept only with its region; some region holds; each turn, helpful, gets
// there or lowers the rank), its usual trees given: the laws' nodes and the step laws' after them, as machineNodes
// translates any machine's step laws (each law's instances none: a loop's laws are about no key).
export function loopNodes(l: Loop, laws: Law[], rank: E | E[], trees: Record<string, Tree>, st: TStats = tstats()): {facts: Fact[], specs: NodeSpec[], why?: string} {
  loopObligations(l, laws, rank)
  const m = loopMachine(l), {stay, cover, helps} = livenessParts(m, loopLiveness(l, rank)), instances = Object.fromEntries(laws.map(x => [x.name, {}]))
  const lawGoals = obligations(m, laws, instances), steps = [stay, cover, ...helps].map(sl => { const goal = stepLawObligations(m, laws, {}, sl)[0]!; return {sl, inst: {}, goal, tree: trees[goal.name]!} })
  if (lawGoals.some(g => !trees[g.name]) || steps.some(x => !x.tree)) return {facts: [], specs: [], why: 'a goal without its usual tree'}
  return machineNodes(m, laws, instances, {trees: Object.fromEntries(lawGoals.map(g => [g.name, trees[g.name]!])), steps}, st)
}

// The run as maps over time: names at time u read as their maps there.
function trace(m: Machine) {
  const maps = [...Object.keys(m.maps ?? {}), ...(m.inputMaps ?? [])]
  const at = (u: E): Subst => ({
    vars: Object.fromEntries([...Object.keys(m.state), ...m.inputs].map(n => [n, get(`${n}@`, u)])),
    maps: Object.fromEntries(maps.map(map => [map, (key: E) => get(`${map}@`, pair(u, key))])), flags: {},
  })
  return {at}
}
// Every map read at `from` (the same term) read at `to`.
const readsAt = <T extends E | C>(t: T, from: E, to: E): T => {
  const id = JSON.stringify(from)
  const walk = (x: unknown): unknown => {
    if (Array.isArray(x)) return x.map(walk)
    if (!x || typeof x !== 'object') return x
    const o = x as Record<string, unknown>
    if (o.op === 'get' && JSON.stringify(o.key) === id) return {...o, key: to}
    return Object.fromEntries(Object.entries(o).map(([key, val]) => [key, walk(val)]))
  }
  return walk(t) as T
}
// A machine's flags, each its condition over the frame before the step (through the flags before it).
const flagsOf = (m: Machine): Record<string, C> => {
  const out: Record<string, C> = {}
  for (const [f, c] of Object.entries(m.step.flags ?? {})) out[f] = substC(c, {vars: {}, maps: {}, flags: out})
  return out
}

// `usual`: the usual proof's trees (kernel/prove.ts's proveLaws, at these instances): the nodes are then the translated
// instance (see `translatedNodes` below), or none with why not.
// `steps`: one-step step laws to prove too, each with the usual proof's goal and tree (kernel/prove.ts's proveStepLaws).
export type UsualStep = {sl: StepLaw, inst: Instances, goal: Goal, tree: Tree}
// `lawsMade`: the laws' nodes are made already (their trees not translated again).
// A machine with flags that hold at every key is read as its sk machine (`skMachine`), the flags' closing conditions facts
// of the run (`qflagFacts`, BridgeRules.lean's cycQFacts): the usual goals' closing hypotheses (kernel.ts's `closing`)
// are those facts at the time before the step (`closings`).
export function machineNodes(given: Machine, laws: Law[], instances: Record<string, Instances>, usual?: {trees: Record<string, Tree>, steps?: UsualStep[], lawsMade?: boolean}, st: TStats = tstats()): {facts: Fact[], specs: NodeSpec[], why?: string} {
  const quant = hasQuantified(given), m = skMachine(given)
  const {at} = trace(m), flags = flagsOf(m), inline = (t: C) => substC(t, {vars: {}, maps: {}, flags})
  const t = v('t$'), T = v('T$'), u = v('u$'), key = v('k$')
  const inlineE = (e: E) => substE(e, {vars: {}, maps: {}, flags})
  const now = (c: C, when: E) => substC(c, at(when)), nowE = (e: E, when: E) => substE(inlineE(e), at(when))
  const state = Object.keys(m.state), mapNames = Object.keys(m.maps ?? {})
  // The start and a step, each stated at the time u it gives (a start at u <= 0, a step at 1 <= u <= T from u − 1), so a
  // node reads them at its own time t: the cells they give are the cells it reads, with no key to prove equal.
  const start = le(u, k(0)), stepped = and(le(k(1), u), le(u, T)), prev = less1(u)
  const facts: Fact[] = [
    {name: `${m.name}: the start`, keys: ['u$'], holds: implies(start, and(yes, ...state.map(s => eq(get(`${s}@`, u), m.state[s]!))))},
    {name: `${m.name}: a step`, keys: ['u$'], holds: implies(stepped, and(yes, ...(m.assume ? [now(inline(m.assume), prev)] : []), ...state.map(s => eq(get(`${s}@`, u), nowE(m.step.state?.[s] ?? v(s), prev)))))},
    ...mapNames.flatMap((map): Fact[] => {
      const w = m.step.maps?.[map], cell = (when: E) => get(`${map}@`, pair(when, key))
      // A write at one key: where the key is the write's, the value with every read at the write's key read at the key
      // instead (the same cell there), so the cells the step gives are at the key the node reads.
      const next: E = !w ? cell(prev) : 'each' in w ? substE(substE(w.value, {vars: {[w.each]: key}, maps: {}, flags}), at(prev))
        : {op: 'if', c: eq(key, nowE(w.key, prev)), then: substE(readsAt(inlineE(w.value), inlineE(w.key), key), at(prev)), else: cell(prev)}
      return [
        {name: `${m.name}: ${map} at the start`, keys: ['u$', 'k$'], holds: implies(start, eq(cell(u), k(m.maps![map]!)))},
        {name: `${m.name}: ${map} at a step`, keys: ['u$', 'k$'], holds: implies(stepped, eq(cell(u), next))},
        {name: `${m.name}: ${map}'s cells are naturals`, keys: ['u$', 'k$'], holds: le(k(0), cell(u))},
      ]
    }),
    ...(m.facts ?? []).map(factOf),
    // That a state variable's value at a time is a natural holds of every model: read at the node's time, it makes the
    // value a column of its own (a value read only inside a product would be none, and no two reads of it equal).
    ...state.map((s): Fact => ({name: `${m.name}: ${s} is a natural`, keys: ['u$'], holds: le(k(0), get(`${s}@`, u))})),
    {name: `${m.name}: params are naturals`, keys: [], holds: and(yes, ...m.params.map(x => le(k(0), v(x))))},
    ...(quant ? qflagFacts(given) : []),
  ]
  const fi = (name: string) => facts.findIndex(f => f.name === name)
  const closings = (inst: Instances, u: E, frame: Subst) => closingsAt(given, laws, facts, inst, u, frame)
  // Every law at time u, at the keys the proof names it at, each key's term read by `key`, under `guard`.
  const lawUses = (inst: Instances, u: E, key: (e: E) => E, guard: C): NodeSpec['uses'] => laws.flatMap((l2, j) => tuples(inst, l2).map(ts => ({node: j, subst: {'t$': u, ...Object.fromEntries(keysOf(l2).map((kn, r) => [kn, key(ts[r]!)]))}, guard})))
  // The usual proof's fresh key k# of a law about every key, the node's own k; the functions' facts at the keys the
  // proof names, over a frame; the state the step gives over the frame before it, a write's reads at its key read at the
  // key read instead (as the map's step fact has them: the same cells there).
  const fresh = freshOf(laws), mapOmega = mapNames.length ? [{op: '<', a: T, b: omega} as C] : []
  const fnInsts = (inst: Instances, frame: Subst) => (m.facts ?? []).flatMap(f => tuples(inst, f).map(ts => ({fact: fi(f.name), at: ts.map(e => substE(substE(e, vars(fresh)), frame))})))
  const upd: Subst = {flags: {}, vars: Object.fromEntries(state.map(st => [st, inlineE(m.step.state?.[st] ?? v(st))])), maps: Object.fromEntries(mapNames.map(map => [map, (kk: E): E => {
    const w = m.step.maps?.[map]
    return !w ? get(map, kk) : 'each' in w ? substE(inlineE(w.value), vars({[w.each]: kk})) : {op: 'if', c: eq(kk, inlineE(w.key)), then: readsAt(inlineE(w.value), inlineE(w.key), kk), else: get(map, kk)}
  }]))}
  // The run's facts at time t: the start and the step (Bridge.lean's cycCanon has them so).
  const run = (when: E): NodeSpec['insts'] => [{fact: 0, at: [when]}, {fact: 1, at: [when]}]
  const nexts = new Map(state.flatMap(s => { const e = m.step.state?.[s]; return e && !(e.op === 'var' && e.name === s) ? [[JSON.stringify(inlineE(e)), get(`${s}@`, t)] as const] : [] }))
  const afterStep = (e: E): E => {
    const walk = (x: unknown): unknown => (Array.isArray(x) ? x.map(walk) : !x || typeof x !== 'object' ? x
      : nexts.get(JSON.stringify(x)) ?? Object.fromEntries(Object.entries(x).map(([key, val]) => [key, walk(val)])))
    return nexts.size ? walk(e) as E : e
  }
  // A map read at the node's time t at key e: that map's start, step and natural facts at (t, e).
  const mapInsts = (c: unknown): NodeSpec['insts'] => cellsAt(m, facts, c)
  // Each law twice: at time t, rank (t, 1), and after
  // a step from t − 1, rank (t, 0), the law read at the state the step gives (the usual rule's step goal, over the run's
  // cells at t − 1). The law at t is the start's at t = 0, and after t's step else: the step's equations carry the law
  // after the step to the state at t. The law after the step uses every law at t − 1, at the keys the machine's proof
  // assumes them at, with the functions' facts at the keys it names, as the usual rule's goal does.
  function stepNodes(single: NodeSpec[]): NodeSpec[] {
    const L = laws.length, pre = at(less1(t)), one = le(k(1), t), omegaHyp = mapOmega
    const over = (e: E, frame: Subst) => substE(substE(e, vars(fresh)), frame)
    const naturals = (when: E) => state.map(st => ({fact: fi(`${m.name}: ${st} is a natural`), at: [when]}))
    const params = {fact: fi(`${m.name}: params are naturals`), at: []}
    // The law at t first with the start's and the step's facts alone, then with the functions' facts at the keys the
    // machine's proof names (read at t: the start's case), then as one node whose goal is the whole step (its uses the
    // laws at t − 1), for a law after the step that isn't proven (that node then holds outright, a weak variant).
    const nowNodes = laws.map((l, i): NodeSpec => {
      const concl = substC(l.holds, at(t)), inst = instances[l.name] ?? {}
      const hyps = [...(m.pre ? [m.pre] : []), le(t, T), ...omegaHyp], uses = [{node: L + i, subst: {}, guard: one}]
      const lean = [...run(t), ...mapInsts(concl), ...naturals(t), params]
      const fns = fnInsts(inst, at(t))
      return {name: `${m.name}: ${l.name}`, hyps, concl, rank: [t, k(1)], insts: lean, uses,
        variants: [...(fns.length ? [{name: `${m.name}: ${l.name}`, hyps, concl, rank: [t, k(1)], insts: [...lean, ...fns], uses}] : []), {...single[i]!, rank: [t, k(1)]}]}
    })
    const stepNodes = laws.map((l): NodeSpec => {
      const inst = instances[l.name] ?? {}, concl = substC(substC(substC(l.holds, vars(fresh)), upd), pre)
      const uses = lawUses(inst, less1(t), e => over(e, pre), one)
      // (the request the step assumes a hypothesis of its own, which the law at t has from the step's fact: the step's
      // equations are no hypothesis of this goal)
      const hyps = [...(m.pre ? [m.pre] : []), one, le(t, T), ...omegaHyp, ...(m.assume ? [now(inline(m.assume), less1(t))] : [])], name = `${m.name}: ${l.name}, after a step`
      return {name, hyps, concl, rank: [t, k(0)], insts: [...fnInsts(inst, pre), ...naturals(less1(t)), params], uses,
        variants: [{name, hyps, concl: yes, rank: [t, k(0)], insts: [], uses: [], weak: true}]}
    })
    // The law at t reads the law after the step and the step's facts at t: the terms they share (the state the step
    // gives) are opaque to its search, so that it carries the one to the other without splitting the step's cases.
    for (const [i, a] of nowNodes.entries()) { const o = shared(facts, a, stepNodes[i]!.concl); if (o.length) a.opaque = o }
    return [...nowNodes, ...stepNodes]
  }
  if (usual) return {facts, ...translatedNodes()}
  const specs: NodeSpec[] = laws.map(l => {
    const inst = instances[l.name] ?? {}
    // Terms over the frame before the step (the machine's proof proves a law about every key at a fresh key k#: here
    // the node's own k).
    const pre = at(less1(t)), before = (e: E) => substE(substE(e, vars(fresh)), pre)
    // A function's fact also at its keys with the terms the step gives a state variable (the usual proof reads the state
    // after the step so) as that variable's cell at t, where it then reads the function where the law at t does: at the
    // key its own reads are at, not one the prover would have to prove equal to it.
    const fnReads = (x: unknown): string[] => { const out: string[] = []; walk(x, o => { if (o.op === 'get' && !(o.map as string).endsWith('@')) out.push(JSON.stringify(o)) }); return out }
    const concl = substC(l.holds, at(t)), reads = new Set(fnReads(concl))
    const after = (e: E) => substE(afterStep(substE(e, vars(fresh))), pre)
    const both = <T>(tuple: E[], make: (ks: E[]) => T, read: (x: T) => unknown): T[] => {
      const a = make(tuple.map(before)), b = make(tuple.map(after))
      return JSON.stringify(a) === JSON.stringify(b) || !fnReads(read(b)).some(c => reads.has(c)) ? [a] : [a, b]
    }
    // The laws at the step before, at the keys the machine's proof assumes them at.
    const uses = lawUses(inst, less1(t), before, le(k(1), t))
    // The functions' facts at the keys the proof names, over the frame before the step (at t = 0, the start's).
    const factInsts = (m.facts ?? []).flatMap(f => {
      const ks = keysOf(f), flat = inst[f.name] ?? [], fact = fi(f.name)
      if (!ks.length) return [{fact, at: []}]
      return Array.from({length: Math.floor(flat.length / ks.length)}, (_, i) => both(flat.slice(i * ks.length, (i + 1) * ks.length), at => ({fact, at}),
        p => substC(f.holds, vars(Object.fromEntries(ks.map((kn, q) => [kn, p.at[q]!])))))).flat()
    })
    const useConcls = uses.map(us => substC(substC(laws[us.node]!.holds, at(t)), vars(us.subst)))
    const base = mapInsts([concl, useConcls])
    return {
      name: `${m.name}: ${l.name}`, hyps: [...(m.pre ? [m.pre] : []), le(t, T), ...(mapNames.length ? [{op: '<', a: T, b: omega} as C] : [])], concl, rank: [t],
      insts: [...run(t), ...factInsts, ...base, ...state.map(st => ({fact: fi(`${m.name}: ${st} is a natural`), at: [t]})), {fact: fi(`${m.name}: params are naturals`), at: []}], uses,
    }
  })
  const searchedSpecs = sliced(stepNodes(specs))
  if (!quant) return {facts, specs: searchedSpecs}
  // (searched, with flags at every key: each node reads the closing facts where the run's step before it and its own time
  // are)
  const close = closingInsts(given, facts, Object.values(instances), [t, less1(t)], laws)
  const withClose = (sp: NodeSpec): NodeSpec => ({...sp, insts: [...sp.insts, ...close], ...(sp.variants ? {variants: sp.variants.map(withClose)} : {})})
  return {facts, specs: searchedSpecs.map(withClose)}

  // The usual proof translated (core/translate.ts): each law three nodes. At t, rank (t, 1), as above (Bridge.lean's
  // cycMOk reads it), its goal grown: it carries the law at the start or after t's step to the cells at t through the
  // start's and the step's equations. After a step from t − 1, rank (t, 0): the usual step goal over the run's cells at
  // t − 1 (each hypothesis of it read so: the functions' facts at the keys the usual proof names, the precondition, the
  // request's assumption, every law at t − 1 at those keys, each a use guarded by 0 <= 0, its descent from 1 <= t), its
  // tree the usual one's renamed. At the start, rank (0, 0): the usual start goal (the law at the start's values), the
  // law's fresh key k# its own k, its tree the usual one's. Only the facts and uses the usual tree reads are kept.
  function translatedNodes(): {specs: NodeSpec[], why?: string} {
    const L = laws.length, pre = at(less1(t)), one = le(k(1), t), omegaHyp = mapOmega
    const sigma: Subst = {vars: {...pre.vars, ...fresh}, maps: pre.maps, flags: {}}
    const ren = renamer({s: sigma, cells: Object.fromEntries([...mapNames, ...(m.inputMaps ?? [])].map(map => [map, {to: `${map}@`, at: less1(t)}]))}), ren0 = renamer({s: vars(fresh)})
    const goals = new Map(obligations(given, laws, instances).map(g => [g.name, g]))
    // (`upd`: the usual step goal's conclusion but for a write's reads at its key, which the translation reads at the key
    // read where the usual path has the two keys equal: two cells over time then split apart, `close`)
    // A step law's condition with its primed names read as given, its flags inlined (over the frame before the step).
    const primedOf = (c: C, s0: Subst): C => substC(c, {...s0, flags})
    const nows: NodeSpec[] = [], afters: NodeSpec[] = [], starts: NodeSpec[] = [], made: Made[] = []
    // A write's key and the keys the usual conclusion reads its map at (each a condition if(K = W, ...)).
    const wkeys = new Set(mapNames.flatMap(map => { const w = m.step.maps?.[map]; return w && !('each' in w) ? [JSON.stringify(inlineE(w.key))] : [] }))
    const readsOf = (c: C): Reads => {
      const out: Reads = [], seen = new Set<string>()
      walk(c, x => {
        const o = x as E
        if (o.op === 'if' && o.c.op === '=' && wkeys.has(JSON.stringify(o.c.b))) { const id = JSON.stringify([o.c.a, o.c.b]); if (!seen.has(id)) { seen.add(id); out.push({k: o.c.a, w: o.c.b}) } }
      })
      return out
    }
    for (const [i, l] of laws.entries()) {
      const g0 = goals.get(`${l.name} @start`), g1 = goals.get(`${l.name} @step`), t0 = g0 && usual!.trees[g0.name], t1 = g1 && usual!.trees[g1.name]
      if (!g0 || !g1 || !t0 || !t1) return {specs: [], why: `${l.name}: no usual tree`}
      const inst = instances[l.name] ?? {}, nf = assumed(m.facts ?? [], inst).length, np = m.pre ? 1 : 0, na = m.assume ? 1 : 0
      const uses = lawUses(inst, less1(t), e => substE(e, sigma), yes)
      const fn1 = fnInsts(inst, pre), fn0 = fnInsts(inst, vars({})), cl = closings(inst, less1(t), pre), nb = nf + np + na + uses.length
      if (g1.hyps.length !== nb + cl.length + 1 || g0.hyps.length !== nf + np + 1 || fn1.length !== nf) return {specs: [], why: `${l.name}: a usual goal of another shape`}
      const used1 = usedHyps(g1, t1), used0 = usedHyps(g0, t0), last = (g: Goal) => (g.hyps.at(-1) as Extract<C, {op: 'not'}>).x
      const concl = substC(l.holds, at(t))
      afters.push({name: `${m.name}: ${l.name}, after a step`, hyps: conjuncts([...(m.pre ? [m.pre] : []), one, le(t, T), ...omegaHyp, ...(m.assume ? [now(inline(m.assume), less1(t))] : [])]),
        concl: substC(substC(substC(l.holds, vars(fresh)), upd), pre), rank: [t, k(0)], insts: [...fn1.filter((_, q) => used1.has(q)), ...cl.filter((_, j) => used1.has(nb + j))], uses: uses.filter((_, j) => used1.has(nf + np + na + j))})
      starts.push({name: `${m.name}: ${l.name}, at the start`, hyps: conjuncts(m.pre ? [m.pre] : []), concl: substC(last(g0), vars(fresh)), rank: [k(0), k(0)], insts: [...fn0.filter((_, q) => used0.has(q))], uses: []})
      nows.push({name: `${m.name}: ${l.name}`, hyps: [...(m.pre ? [m.pre] : []), le(t, T), ...omegaHyp], concl, rank: [t, k(1)], insts: [...run(t), ...mapInsts(concl)],
        uses: [{node: L + i, subst: {}, guard: one}, {node: 2 * L + i, subst: {}, guard: le(t, k(0))}], carry: true})
      // (the closing facts' time t − 1 <= T decided too: their rows are then the closing hypotheses')
      made.push({g: g1, tree: t1, node: L + i, ren, decide: [one, ...(cl.length ? [le(less1(t), T)] : [])], reads: readsOf(last(g1))}, {g: g0, tree: t0, node: 2 * L + i, ren: ren0})
    }
    // One-step step laws (`usual.steps`), each two nodes after the laws' (core/cyclic.ts's header has their shape): after a
    // step from t − 1, rank (t, 0), the usual step law's goal over the run's cells at t − 1 (its `when` and the request's
    // assumption hypotheses, the laws at t − 1 at its keys uses), the state after it the step's terms; and the step law
    // itself, rank (t, 2), over the cells at t − 1 and at t (a primed name at t), carried from the first by the step's
    // facts at t, its hypotheses the precondition, 1 <= t <= T, T < Ω and `when` at t − 1.
    const stepSpecs: NodeSpec[] = []
    for (const [q, u] of (usual!.steps ?? []).entries()) {
      const {sl, inst, goal: g, tree} = u, whens = sl.when === undefined ? [] : Array.isArray(sl.when) ? sl.when : [sl.when], K = sl.steps ?? 1
      // (k steps: the state after each step a cell at its time, a map read after a step the usual goal's term over the
      // cells at t − k, the step's writes, a map a later request carries (c@j) its cells at its time)
      const carried = m.inputMaps ?? [], overMaps = K > 1 && mapNames.length > 0
      // The times: over a map, one step back at a time (t − 1 − 1, as a step's fact reads the time before it: the cells it
      // gives are the frames' own, with no key to prove equal); else t − n at once (BridgeRules.lean's cycKOk reads both).
      // (one step back at a time, a time t − n is a term n deep and a premise's slice follows each state's cell back
      // through every step's fact before it: the budget rule's 32 steps took 39 s against its usual proof's 1.5 s)
      const time = overMaps ? tBack : tSub
      const laterMaps = Object.fromEntries(Array.from({length: K - 1}, (_, j) => j + 2).flatMap(j => carried.map(c => [`${c}@${j}`, {to: `${c}@`, at: time(K - j + 1)}] as const)))
      // The times the steps start from (t − k, ..., t − 1), and the frames: the state before step j its cells at t − k + j − 1
      // (n~j the state after step j, at t − k + j), its request read there (i@j).
      const frame: Subst = {vars: {...at(time(K)).vars, ...Object.fromEntries(Array.from({length: K}, (_, j) => j + 1).flatMap(j => [
        ...(j >= 2 ? m.inputs.map(i => [`${i}@${j}`, get(`${i}@`, time(K - j + 1))] as const) : []),
        ...(j < K ? state.map(n => [`${n}~${j}`, get(`${n}@`, time(K - j))] as const) : []),
      ]))}, maps: K === 1 ? pre.maps : {...at(time(K)).maps, ...Object.fromEntries(Object.entries(laterMaps).map(([n, c]) => [n, (kk: E) => get(c.to, pair(c.at, kk))]))}, flags: {}}
      const sig: Subst = K === 1 ? sigma : frame, renK = K === 1 ? ren : renamer({s: frame, cells: {...Object.fromEntries([...mapNames, ...carried].map(map => [map, {to: `${map}@`, at: time(K)}])), ...laterMaps}})
      // (the usual goal's hypotheses: the precondition, the facts at the instances, then each step's laws, assumption and
      // `when`, and after each step but the last its state's equations)
      const nf = assumed(m.facts ?? [], inst).length, np = m.pre ? 1 : 0, na = m.assume ? 1 : 0, nl = assumed(laws, inst).length
      const lawsAt = (back: number) => lawUses(inst, time(back), e => substE(e, at(time(back))), yes)
      const perStep = Array.from({length: K}, (_, j) => lawsAt(K - j)), fn1 = fnInsts(inst, sig)
      // (a flag at every key: each step's closing hypotheses the closing facts at its time)
      // (its keys over the frame: a key may read a later step's request, a flag read at a later step's witness)
      const cls = Array.from({length: K}, (_, j) => closings(inst, time(K - j), K === 1 ? at(time(K - j)) : {vars: {...frame.vars, ...at(time(K - j)).vars}, maps: {...frame.maps, ...at(time(K - j)).maps}, flags: {}})), nc = cls[0]!.length
      // Each step's block: its laws, its assumption, its when, its closing hypotheses, then (but after the last) its
      // state's equations.
      const blocks: number[] = []
      let pos = np + nf
      for (let j = 0; j < K; j++) { blocks.push(pos); pos += nl + na + (whens[j] ? 1 : 0) + nc + (j < K - 1 ? state.length : 0) }
      if (g.hyps.length !== pos + 1 || fn1.length !== nf || perStep.some(us => us.length !== nl)) return {specs: [], why: `${sl.name}: a usual goal of another shape`}
      const used = usedHyps(g, tree), last = (g.hyps.at(-1) as Extract<C, {op: 'not'}>).x
      const assumes = Array.from({length: K}, (_, j) => (m.assume ? [now(inline(m.assume), time(K - j))] : [])).flat()
      const when = whens.map((w, j) => now(inline(w), time(K - j)))
      // Over a map, a later step reads it as the usual goal's terms over the cells at t − k: each later step's laws (a use
      // at its time) must read no map so, and its assumption, `when` and closing hypotheses are the usual goal's renamed
      // (hypotheses of the node after the steps, which the step law's facts back to t − k give).
      const renamed = (i: number) => substC(g.hyps[i]!, frame), later0: C[] = []
      if (overMaps) for (let j = 1; j < K; j++) {
        const b0 = blocks[j]!
        for (const [r, us] of perStep[j]!.entries()) if (used.has(b0 + r) && JSON.stringify(substC(nows[us.node]!.concl, vars(us.subst))) !== JSON.stringify(renamed(b0 + r))) return {specs: [], why: `${sl.name}: a law read over a map after a step`}
        for (let r = nl; r < nl + na + (whens[j] ? 1 : 0) + nc; r++) if (used.has(b0 + r)) later0.push(renamed(b0 + r))
      }
      const bounds = [...(m.pre ? [m.pre] : []), le(k(K), t), le(t, T), ...omegaHyp]
      const after = K === 1 ? substC(primedOf(sl.then, {vars: Object.fromEntries(state.map(st2 => [`${st2}'`, inlineE(m.step.state?.[st2] ?? v(st2))])), maps: Object.fromEntries(mapNames.map(map => [`${map}'`, upd.maps[map]!])), flags: {}}), pre) : substC(last, frame)
      const later = Object.fromEntries(Array.from({length: K - 1}, (_, j) => j + 2).flatMap(j => m.inputs.map(i => [`${i}@${j}`, get(`${i}@`, time(K - j + 1))] as const)))
      const cells = substC(primedOf(sl.then, {vars: {...later, ...Object.fromEntries(state.map(st2 => [`${st2}'`, get(`${st2}@`, t)]))}, maps: {...Object.fromEntries(mapNames.map(map => [`${map}'`, (kk: E) => get(`${map}@`, pair(t, kk))])), ...frame.maps}, flags: {}}), at(time(K)))
      const a = 3 * L + 2 * q, steps = Array.from({length: K - 1}, (_, j) => ({fact: 1, at: [time(K - j - 1)]}))
      // (the state after each step but the last its equations, hypotheses here as in the usual goal: the step's facts at
      // those times give them where the step law is, `steps` below)
      // (those the usual tree reads: each is a premise of this node where the step law uses it, and over a map one that
      // reads the map after a step is proven through the map's cells back to t − k)
      const eqs = blocks.slice(0, K - 1).flatMap((b0, j) => { const e0 = b0 + nl + na + (whens[j] ? 1 : 0) + nc; return g.hyps.slice(e0, e0 + state.length).flatMap((h, r) => (used.has(e0 + r) ? [substC(h, frame)] : [])) })
      const closed = cls.flatMap((c, j) => (overMaps && j ? [] : c.filter((_, r) => used.has(blocks[j]! + nl + na + (whens[j] ? 1 : 0) + r))))
      const own = overMaps ? [...assumes.slice(0, na), ...when.slice(0, whens[0] ? 1 : 0), ...later0] : [...assumes, ...when]
      stepSpecs.push({name: `${m.name}: ${sl.name}, after ${K === 1 ? 'a step' : `${K} steps`}`, hyps: conjuncts([...bounds, ...own, ...eqs]), concl: after, rank: [t, k(0)],
        insts: [...fn1.filter((_, r) => used.has(np + r)), ...closed], uses: perStep.flatMap((us, j) => us.filter((_, r) => used.has(blocks[j]! + r)))})
      // (over a map, each cell the step law and its `when`s read back to t − k, and the closing facts at each later time)
      const back: NodeSpec['insts'] = []
      if (overMaps) cellChain(m, facts, Array.from({length: K + 1}, (_, j) => time(K - j)), back)([cells, when, later0, instHyps(facts, [...run(t), ...steps, ...cls.slice(1).flat()])])
      stepSpecs.push({name: `${m.name}: ${sl.name}`, hyps: [...bounds, ...when], concl: cells, rank: [t, k(2)],
        insts: [...run(t), ...steps, ...(overMaps ? [...back, ...cls.slice(1).flat()] : mapInsts(cells))], uses: [{node: a, subst: {}, guard: yes}], carry: overMaps ? 'sliced' : true})
      // (each time decided at least the steps before it first: t ∸ j is then t − j)
      // (and each closing fact's time at most T)
      made.push({g, tree, node: a, ren: renK, decide: [...Array.from({length: K}, (_, j) => le(k(j + 1), t)), ...(nc ? Array.from({length: K}, (_, j) => le(time(j + 1), T)) : [])], reads: K === 1 ? readsOf(last) : []})
    }
    const all = [...nows, ...afters, ...starts, ...stepSpecs]
    for (const [i, a] of nows.entries()) { const o = [...new Set([...shared(facts, a, afters[i]!.concl), ...shared(facts, a, starts[i]!.concl)].map(e => JSON.stringify(e)))].map(e => JSON.parse(e) as E); if (o.length) a.opaque = o }
    // (a translation is bounded by a minute: a step law over 32 steps has a goal of 32 frames at every leaf)
    const until = withinDeadline(clock() + 60_000)
    // (after a step, 1 <= t decided first: t ∸ 1 is then t − 1, and a cell read at a key over the cells at t − 1 has a
    // linear form)
    return translateMade(facts, all, usual!.lawsMade ? made.filter(x => x.node >= 3 * L) : made, st, until)
  }
}

// Each usual tree made a node's (`made`: the usual goal and tree, the node, the renamer, the conditions decided first,
// the reads a write's key decides first), the node's tree then given (`main`); or why one isn't.
type Made = {g: Goal, tree: Tree, node: number, ren: Renamer, decide?: C[], reads?: Reads}
function translateMade(facts: Fact[], all: NodeSpec[], made: Made[], st: TStats, until: number): {specs: NodeSpec[], why?: string} {
  return counting(until, end => {
    for (const x of made) {
      const whole = mainGoal(facts, all, all[x.node]!)
      const tree = timedKind('translate', 0, () => withProducts(() => decide(whole, x.decide ?? [], wp => readsFirst(whole, x.reads ?? [], x.ren, (p, swaps) => translate(x.g, whole, x.tree, x.ren, st, end, new Map(), p, swaps), st, end, wp), st, end)))
      if (!tree) return {specs: [], why: `${all[x.node]!.name}: not translated`}
      all[x.node] = {...all[x.node]!, main: tree}
    }
    return {specs: sliced(all)}
  })
}
// A translation on the cost model's clock (kernel/prove.ts's `counted` with `full`): its budget the time from now to
// `until`, counted, translate.ts counting each leaf's rows as it reads them, so a large tree's translation stops at its
// budget on any machine. (On wall time alone it ran past it: the bound was read only where a leaf was grown again, and
// ledger/tigerbeetle/transfers' 21,108 leaves took 92.7 s, the law then past the real-world corpus's 150 s.)
const counting = <T>(until: number, f: (end: number) => T): T => { const ms = Math.max(0, until - clock()); return counted(fullRate, () => f(clock() + ms), true) }

// The terms (not a read, a variable or a constant) of a conclusion that a node's facts read too, largest first; none
// inside a product (a product of a term's linear form is no linear form).
function shared(facts: Fact[], a: NodeSpec, concl: C): E[] {
  const inst = instHyps(facts, a.insts), theirs = JSON.stringify(inst), seen = new Set<string>(), out: E[] = [], factors = new Set<string>()
  const inProducts = (x: unknown, under = false): void => {
    if (!x || typeof x !== 'object') return
    if (Array.isArray(x)) { x.forEach(y => inProducts(y, under)); return }
    const o = x as E
    if (under) factors.add(JSON.stringify(o))
    for (const val of Object.values(o)) inProducts(val, under || o.op === 'prod')
  }
  inProducts([concl, inst])
  const walk = (x: unknown): void => {
    if (!x || typeof x !== 'object') return
    if (Array.isArray(x)) { x.forEach(walk); return }
    const o = x as E, id = JSON.stringify(o)
    if (['if', 'add', 'sub', 'min', 'max', 'mul', 'prod'].includes(o.op) && theirs.includes(id) && !factors.has(id)) { if (!seen.has(id)) { seen.add(id); out.push(o) } return }
    for (const val of Object.values(o)) walk(val)
  }
  walk(concl)
  return out.sort((x, y) => JSON.stringify(y).length - JSON.stringify(x).length)
}

// --- step laws and k-step laws over the run -----------------------------------------------------------------------

// A k-step law (or a step law, k = 1) as a node over the machine's run (BridgeRules.lean's cycKOk, cyc_kstep_sound
// carries it to the law): the run's last k steps up to time t, each time one step back from the next (t − 1, t − 1 − 1,
// …), as a step's fact reads the time before it, so the cells a step gives are those the next one reads. The first state
// at t − k, the j-th request at t − (k − j), the state after the last at t.
export const tBack = (n: number): E => (n === 0 ? v('t$') : less1(tBack(n - 1)))
// The same times read t − n at once (BridgeRules.lean's tSub; core/translate.ts's step laws over several steps).
export const tSub = (n: number): E => (n === 0 ? v('t$') : {op: 'sub', a: v('t$'), b: k(n)})
// `then` over the run (BridgeRules.lean's kσ and kRd): the primed names at t, each later request's inputs (input@j) and
// the maps it carries (map@j) at its time, the plain names at t − k.
export function kStepAt(m: Machine, k: number, time: (n: number) => E = tBack): Subst {
  const {at} = trace(m), first = at(time(k)), last = at(time(0))
  const vars: Record<string, E> = {...first.vars}, maps: Record<string, (key: E) => E> = {...first.maps}
  for (const x of Object.keys(m.state)) vars[`${x}'`] = last.vars[x]!
  for (const map of Object.keys(m.maps ?? {})) maps[`${map}'`] = last.maps[map]!
  for (let j = 1; j < k; j++) {
    const a = at(time(k - j))
    for (const i of m.inputs) vars[`${i}@${j + 1}`] = a.vars[i]!
    for (const c of m.inputMaps ?? []) maps[`${c}@${j + 1}`] = a.maps[c]!
  }
  return {vars, maps, flags: {}}
}
// A k-step law's `when`s, one per step (none: 0 <= 0), its flags inlined, as Lean's SKStep has them.
export const kWhens = (m: Machine, sl: StepLaw): C[] => {
  const ws = sl.when === undefined ? [] : Array.isArray(sl.when) ? sl.when : [sl.when], flags = flagsOf(m)
  return Array.from({length: sl.steps ?? 1}, (_, j) => (ws[j] ? substC(ws[j]!, {vars: {}, maps: {}, flags}) : yes))
}
// The nodes of the step laws, after the laws' (`laws` the machine's, `lawNodes` their nodes, the first L at time t, as
// machineNodes makes them). Each node: the precondition, k <= t <= T, T < Ω and each step's `when` at its time;
// the run's facts at the times it reads (each step's, each map cell's step back from where it is read, the functions'
// facts at the keys the usual proof names), every law at each state but the last (at the keys it names), and `then`.
export function stepLawNodes(m: Machine, laws: Law[], steps: {law: StepLaw, instances: Instances}[], facts: Fact[], lawNodes: NodeSpec[], time: (n: number) => E = tBack): NodeSpec[] {
  const rank = lawNodes[0]?.rank.length ?? 2
  const {at} = trace(m), flags = flagsOf(m), inline = (c: C) => substC(c, {vars: {}, maps: {}, flags})
  const t = v('t$'), T = v('T$'), mapNames = Object.keys(m.maps ?? {}), traced = [...mapNames, ...(m.inputMaps ?? [])], state = Object.keys(m.state)
  const fi = (name: string) => facts.findIndex(f => f.name === name)
  const specs = steps.map(({law: sl, instances: inst}): NodeSpec => {
    const K = sl.steps ?? 1, times = Array.from({length: K + 1}, (_, j) => time(K - j))
    const hyps: C[] = [...(m.pre ? [m.pre] : []), le(k(K), t), le(t, T), ...(traced.length ? [{op: '<', a: T, b: omega} as C] : []),
      ...kWhens(m, sl).map((w, j) => substC(w, at(times[j]!)))]
    const concl = substC(inline(sl.then), kStepAt(m, K, time))
    // Every law at each state but the last, at the keys the proof names there.
    const uses: NodeSpec['uses'] = times.slice(0, K).flatMap(u => laws.flatMap((l, i) => tuples(inst, l).map(ts => ({
      node: i, subst: {'t$': u, ...Object.fromEntries(keysOf(l).map((kn, q) => [kn, substE(ts[q]!, at(u))]))}, guard: yes}))))
    const insts: NodeSpec['insts'] = [
      ...times.slice(1).map(u => ({fact: fi(`${m.name}: a step`), at: [u]})),
      ...times.flatMap(u => state.map(st => ({fact: fi(`${m.name}: ${st} is a natural`), at: [u]}))),
      {fact: fi(`${m.name}: params are naturals`), at: []},
      ...(m.facts ?? []).flatMap(f => tuples(inst, f).map(ts => ({fact: fi(f.name), at: ts.map(e => substE(e, at(times[0]!)))}))),
    ]
    const cellFacts = cellChain(m, facts, times, insts)
    cellFacts([hyps, concl, uses.map(us => substC(laws[us.node]!.holds, {...at(us.subst['t$']!), vars: {...at(us.subst['t$']!).vars, ...Object.fromEntries(Object.entries(us.subst).filter(([n]) => n !== 't$'))}}))])
    for (const p of [...insts]) if (p.fact === fi(`${m.name}: a step`)) cellFacts(substC(facts[p.fact]!.holds, vars({'u$': p.at[0]!})))
    return {name: `${m.name}: ${sl.name}`, hyps, concl, rank: rank === 1 ? [t] : [t, ...Array.from({length: rank - 1}, () => k(2))], insts: insts.filter(p => p.fact >= 0), uses}
  })
  return sliced(withReads(facts, specs, [...lawNodes, ...specs]))
}

// Each map cell `x` reads at the node's time t: that map's start, its step and that its cells are naturals there.
function cellsAt(m: Machine, facts: Fact[], x: unknown): NodeSpec['insts'] {
  const mapNames = Object.keys(m.maps ?? {}), t = JSON.stringify(v('t$')), fi = (name: string) => facts.findIndex(f => f.name === name)
  const out: NodeSpec['insts'] = [], seen = new Set<string>()
  walk(x, o => {
    if (o.op === 'get' && typeof o.map === 'string' && o.map.endsWith('@') && mapNames.includes(o.map.slice(0, -1))) {
      const key = o.key as E
      if (key.op === 'add' && JSON.stringify(key.a) === t && key.b.op === 'prod') {
        const map = o.map.slice(0, -1), cell = key.b.a, id = `${map}:${JSON.stringify(cell)}`
        if (!seen.has(id)) { seen.add(id); out.push(...['at the start', 'at a step', '\'s cells are naturals'].map(what => ({fact: fi(`${m.name}: ${map}${what.startsWith('\'') ? what : ` ${what}`}`), at: [key.a, cell]}))) }
      }
    }
  })
  return out
}
// Each map cell a node reads at one of `times` (the first the earliest), pushed to `insts`: that map's step there (at a
// time after the first) and that its cells are naturals, then the same of the cells those facts read, back to the first
// time: the cells a step gives read back to the run's cells where the node starts.
function cellChain(m: Machine, facts: Fact[], times: E[], insts: NodeSpec['insts']): (x: unknown) => void {
  const mapNames = Object.keys(m.maps ?? {}), traced = [...mapNames, ...(m.inputMaps ?? [])], fi = (name: string) => facts.findIndex(f => f.name === name)
  // (a time read either way, t − n or one step back at a time: a step's fact at t − 1 reads t − 1 − 1)
  const norm = (u: E): E => (u.op === 'sub' && u.b.op === 'const' && u.a.op === 'sub' && u.a.b.op === 'const' ? norm({op: 'sub', a: u.a.a, b: k(u.a.b.value + u.b.value)}) : u)
  const seen = new Set<string>(), ix = new Map(times.map((u, j) => [JSON.stringify(norm(u)), j]))
  const cellFacts = (x: unknown): void => {
    if (!x || typeof x !== 'object') return
    if (Array.isArray(x)) { x.forEach(cellFacts); return }
    const o = x as Record<string, unknown>
    if (o.op === 'get' && typeof o.map === 'string' && o.map.endsWith('@') && traced.includes(o.map.slice(0, -1))) {
      const key = o.key as E
      if (key.op === 'add' && key.b.op === 'prod' && JSON.stringify(key.b.b) === JSON.stringify(omega)) {
        const j = ix.get(JSON.stringify(norm(key.a))), map = o.map.slice(0, -1), id = `${map}:${JSON.stringify(key)}`, u = key.a, cell = key.b.a
        if (j !== undefined && !seen.has(id) && mapNames.includes(map)) {
          seen.add(id)
          const more = [...(j > 0 ? ['at a step'] : []), '\'s cells are naturals'].map(what => ({fact: fi(`${m.name}: ${map}${what.startsWith('\'') ? what : ` ${what}`}`), at: [u, cell]}))
          insts.push(...more)
          for (const p of more) cellFacts(substC(facts[p.fact]!.holds, vars({'u$': p.at[0]!, 'k$': p.at[1]!})))
        }
      }
    }
    for (const val of Object.values(o)) cellFacts(val)
  }
  return cellFacts
}

// A request allowed (BridgeRules.lean's cycAOk, cyc_allow_sound carries it to the claim): from every reachable state,
// every request meeting `w` (a helpful request's region and terms), carrying empty sets, is one the machine allows. A node
// at time t, the request the run takes at t the claim's (no step reads it): the precondition, t <= T, T < Ω, `w` at t,
// each carried map's cell the assumption reads at t 0, every law at t (rank (t, 2) above theirs), the run's facts at t;
// its conclusion the assumption at t, flags inlined.
export function allowNode(m: Machine, laws: Law[], inst: Instances, w: C, facts: Fact[], lawNodes: NodeSpec[], name: string, extra: NodeSpec['insts'] = []): NodeSpec {
  const {at} = trace(m), flags = flagsOf(m), t = v('t$'), T = v('T$'), mapNames = Object.keys(m.maps ?? {}), carried = m.inputMaps ?? []
  const traced = [...mapNames, ...carried], state = Object.keys(m.state), now = at(t)
  const fi = (n: string) => facts.findIndex(f => f.name === n)
  const tuplesOf = (l: Law) => tuples(inst, l)
  const concl = substC(substC(m.assume ?? yes, {vars: {}, maps: {}, flags}), now)
  // Each carried cell the conclusion and the facts given at t read there (a flag's body at its witness, say): 0 (the
  // request carries empty sets).
  const zeros: C[] = [], seen = new Set<string>()
  walk([concl, instHyps(facts, extra)], o => {
    if (o.op === 'get' && typeof o.map === 'string' && o.map.endsWith('@') && carried.includes(o.map.slice(0, -1))) {
      const id = JSON.stringify(o)
      if (!seen.has(id)) { seen.add(id); zeros.push(eq(o as E, k(0))) }
    }
  })
  const hyps: C[] = [...(m.pre ? [m.pre] : []), le(t, T), ...(traced.length ? [{op: '<', a: T, b: omega} as C] : []), substC(w, now), ...zeros]
  const uses: NodeSpec['uses'] = laws.flatMap((l, i) => tuplesOf(l).map(ts => ({node: i, subst: Object.fromEntries(keysOf(l).map((kn, q) => [kn, substE(ts[q]!, now)])), guard: yes})))
  const insts: NodeSpec['insts'] = [{fact: fi(`${m.name}: the start`), at: [t]}, {fact: fi(`${m.name}: a step`), at: [t]},
    ...state.map(st => ({fact: fi(`${m.name}: ${st} is a natural`), at: [t]})), {fact: fi(`${m.name}: params are naturals`), at: []},
    ...(m.facts ?? []).flatMap(f => tuplesOf(f).map(ts => ({fact: fi(f.name), at: ts.map(e => substE(e, now))}))), ...extra]
  insts.push(...cellsAt(m, facts, [hyps, concl, uses.map(us => substC(laws[us.node]!.holds, {...now, vars: {...now.vars, ...us.subst}}))]))
  const rank = lawNodes[0]?.rank.length ?? 2
  const spec: NodeSpec = {name, hyps, concl, rank: [t, ...Array.from({length: rank - 1}, () => k(2))], insts: insts.filter(p => p.fact >= 0), uses}
  return sliced(withReads(facts, [spec], [...lawNodes, spec]))[0]!
}

// A request allowed, translated (proveProgress's goal `<name>: the request is allowed`, kernel.ts's progressObligations,
// read at time t), two nodes after the laws' (`lawNodes`, rank (t, 1) the laws at t): the usual goal over the cells at
// t, the request's terms as it reads them, rank (t, 2): its hypotheses the precondition, t <= T, T < Ω, `when` at t and
// the closing hypotheses no closing fact gives (each a conjunct), the laws at t at the keys it names its uses, the
// functions' and the closing facts its facts, its tree the usual one's; then the request allowed itself, rank (t, 3)
// (BridgeRules.lean's cycAOk: `w` the region, the request's terms and its witnesses at t, its conclusion the assumption
// at t), carried from the first by the request's equations.
export function allowTranslated(given: Machine, laws: Law[], inst: Instances, p: {when: C, request: Record<string, E>}, usual: {goal: Goal, tree: Tree}, facts: Fact[], lawNodes: NodeSpec[], name: string, st: TStats): {specs: NodeSpec[], why?: string} {
  const m = skMachine(given), {at} = trace(m), t = v('t$'), T = v('T$'), now = at(t), mapNames = Object.keys(m.maps ?? {})
  const fi = (n: string) => facts.findIndex(f => f.name === n), tuplesOf = (l: Law) => tuples(inst, l)
  const g = usual.goal, used = usedHyps(g, usual.tree), renamed = (c: C) => substC(c, now)
  const fns = (m.facts ?? []).flatMap(f => tuplesOf(f).map(ts => ({fact: fi(f.name), at: ts.map(e => substE(e, now))})))
  const uses: NodeSpec['uses'] = laws.flatMap((l, i) => tuplesOf(l).map(ts => ({node: i, subst: Object.fromEntries(keysOf(l).map((kn, q) => [kn, substE(ts[q]!, now)])), guard: yes})))
  const cl = closingsAt(given, laws, facts, inst, t, now), nf = fns.length, np = m.pre ? 1 : 0
  if (g.hyps.length !== nf + np + uses.length + 1 + cl.length + 1 || !m.assume) return {specs: [], why: `${name}: a usual goal of another shape`}
  // (a closing hypothesis the closing fact at t gives as it is, a fact; one whose body reads the request, a hypothesis)
  const nb = nf + np + uses.length + 1, closeFacts: NodeSpec['insts'] = [], closeHyps: C[] = []
  for (const [j, q] of cl.entries()) {
    if (!used.has(nb + j)) continue
    if (JSON.stringify(instHyps(facts, [q])[0]) === JSON.stringify(renamed(g.hyps[nb + j]!))) closeFacts.push(q); else closeHyps.push(renamed(g.hyps[nb + j]!))
  }
  const omegaHyp = mapNames.length ? [{op: '<', a: T, b: omega} as C] : [], base = [...(m.pre ? [m.pre] : []), le(t, T), ...omegaHyp]
  const flags = flagsOf(m), terms: NodeSpec = {name: `${name}, its terms`, hyps: conjuncts([...base, renamed(p.when), ...closeHyps]), concl: renamed((g.hyps.at(-1) as Extract<C, {op: 'not'}>).x), rank: [t, k(2)],
    insts: [...fns.filter((_, q) => used.has(q)), ...closeFacts], uses: uses.filter((_, j) => used.has(nf + np + j))}
  const w = and(p.when, reqTS(Object.entries(p.request)), reqTS([]))
  const allowed: NodeSpec = {name, hyps: [...base, renamed(w)], concl: renamed(substC(m.assume, {vars: {}, maps: {}, flags})), rank: [t, k(3)],
    insts: closeHyps.length ? cl : [], uses: [{node: lawNodes.length, subst: {}, guard: yes}], carry: true}
  const all = [...lawNodes, terms, allowed], whole = mainGoal(facts, all, terms), until = withinDeadline(clock() + 10_000)
  const ren = renamer({s: now, cells: Object.fromEntries(mapNames.map(map => [map, {to: `${map}@`, at: t}]))})
  const tree = counting(until, end => timedKind('translate', 0, () => withProducts(() => decide(whole, closeFacts.length ? [le(t, T)] : [], wp => translate(g, whole, usual.tree, ren, st, end, new Map(), wp), st, end))))
  if (!tree) return {specs: [], why: `${terms.name}: not translated`}
  return {specs: sliced([{...terms, main: tree}, allowed])}
}

// A goal's closing hypotheses (kernel.ts's `closing`, in its order: each flag 0 or 1, its body at each key the proof
// names, its body failing at the witness) as the closing facts at time u, the keys read over `frame` (a law's fresh key
// its own k).
function closingsAt(given: Machine, laws: Law[], facts: Fact[], inst: Instances, u: E, frame: Subst): NodeSpec['insts'] {
  const fi = (n: string) => facts.findIndex(f => f.name === n), fresh = vars(freshOf(laws))
  return quantifiedOf(given).flatMap(([f, qf]) => {
    const n = boundOf(qf).length, flat = inst[`?${f}`] ?? []
    return [{fact: fi(`${given.name}: ?${f} is 0 or 1`), at: [u]},
      ...Array.from({length: Math.floor(flat.length / n)}, (_, j) => ({fact: fi(`${given.name}: ?${f} is 0 or its body holds`), at: [u, ...flat.slice(j * n, (j + 1) * n).map(e => substE(substE(e, fresh), frame))]})),
      {fact: fi(`${given.name}: ?${f} is 1 or its body fails at the witness`), at: [u]}]
  })
}

// --- flags that hold at every key ------------------------------------------------------------------------------------

// A machine with flags that hold at every key, read as its sk machine (BridgeRules.lean's SMachine.sk): each such flag
// ?f and its witnesses inputs a request names, a read of the flag `?f = 1`; the closing conditions facts of the run
// (`qflagFacts`). Untrusted: BridgeRules.lean's cycQMOk checks the facts against the machine.
const quantifiedOf = (m: Machine) => Object.entries(m.step.flags ?? {}).filter((e): e is [string, Extract<C, {op: 'all'}>] => e[1].op === 'all')
export const hasQuantified = (m: Machine): boolean => quantifiedOf(m).length > 0
export function skMachine(m: Machine): Machine {
  const q = quantifiedOf(m)
  if (!q.length) return m
  const flags = Object.fromEntries(Object.entries(m.step.flags ?? {}).map(([f, c]) => [f, c.op === 'all' ? eq(v(`?${f}`), k(1)) : c]))
  return {...m, inputs: [...m.inputs, ...q.map(([f]) => `?${f}`), ...q.flatMap(([f, c]) => witnessesOf(f, c))], step: {...m.step, flags}}
}
// Each flag's closing conditions at each time u <= T (BridgeRules.lean's cycQFacts): 0 or 1; 0, or its body at every
// value of its keys; 1, or its body failing at the witness.
export function qflagFacts(m: Machine): Fact[] {
  const {at} = trace(skMachine(m)), u = v('u$'), T = v('T$')
  const upTo = (c: C): C => implies(le(u, T), substC(c, at(u)))
  return quantifiedOf(m).flatMap(([f, q]): Fact[] => {
    const fv = v(`?${f}`), keys = boundOf(q), wits = witnessesOf(f, q)
    return [
      {name: `${m.name}: ?${f} is 0 or 1`, keys: ['u$'], holds: upTo(le(fv, k(1)))},
      {name: `${m.name}: ?${f} is 0 or its body holds`, keys: ['u$', ...keys], holds: upTo({op: 'or', xs: [eq(fv, k(0)), q.c]})},
      {name: `${m.name}: ?${f} is 1 or its body fails at the witness`, keys: ['u$'],
        holds: upTo({op: 'or', xs: [eq(fv, k(1)), {op: 'not', x: substC(q.c, vars(Object.fromEntries(keys.map((key, i) => [key, v(wits[i]!)]))))}]})},
    ]
  })
}
// The closing facts at the times a node reads the run (each flag's at its time, its body at the keys the usual proof
// closes it at, read there).
export function closingInsts(m: Machine, facts: Fact[], insts: Instances[], times: E[], laws: Law[] = []): NodeSpec['insts'] {
  // (a law's fresh key k#, which the usual proof's keys may read, the node's own k)
  const fresh = vars(freshOf(laws))
  const {at} = trace(skMachine(m)), fi = (n: string) => facts.findIndex(f => f.name === n), out: NodeSpec['insts'] = [], seen = new Set<string>()
  const push = (p: NodeSpec['insts'][number]) => { const id = JSON.stringify(p); if (p.fact >= 0 && !seen.has(id)) { seen.add(id); out.push(p) } }
  for (const [f, q] of quantifiedOf(m)) {
    const n = boundOf(q).length
    for (const u of times) {
      push({fact: fi(`${m.name}: ?${f} is 0 or 1`), at: [u]})
      push({fact: fi(`${m.name}: ?${f} is 1 or its body fails at the witness`), at: [u]})
      for (const inst of insts) {
        const flat = inst[`?${f}`] ?? []
        for (let i = 0; i + n <= flat.length; i += n) push({fact: fi(`${m.name}: ?${f} is 0 or its body holds`), at: [u, ...flat.slice(i, i + n).map(e => substE(substE(e, fresh), at(u)))]})
      }
    }
  }
  return out
}
// The laws' nodes of a machine with such flags (searched): machineNodes, which reads it as its sk machine.
export const qflagNodes = (m: Machine, laws: Law[], instances: Record<string, Instances>): {facts: Fact[], specs: NodeSpec[], why?: string} => machineNodes(m, laws, instances)

// --- folds over trees -----------------------------------------------------------------------------------------------

// The tree as a table of nodes below its size N: a node n is a leaf (Kind[n] = 0) whose values come from its inputs,
// or a node (Kind[n] = 1) with children Left[n], Right[n] numbered below n, its values from theirs and its inputs.
// `usual`: the usual proof's trees (kernel.ts's foldObligations), translated (`translatedFold` below), or no nodes with why not.
export function foldNodes(f: Fold, laws: Law[], usual?: Record<string, Tree>, st: TStats = tstats()): {facts: Fact[], specs: NodeSpec[], why?: string} {
  const n = v('n$'), N = v('N$'), names = Object.keys(f.leaf)
  const at = (i: E): Subst => vars(Object.fromEntries([...names, ...f.inputs].map(x => [x, get(`${x}@`, i)])))
  const kind = (i: E) => get('Kind@', i), left = (i: E) => get('Left@', i), right = (i: E) => get('Right@', i)
  const side = (child: E, p: string) => Object.fromEntries(names.map(x => [`${p}${x}`, get(`${x}@`, child)]))
  const nodeAt = (i: E): Subst => vars({...Object.fromEntries(f.inputs.map(x => [x, get(`${x}@`, i)])), ...side(left(i), 'l_'), ...side(right(i), 'r_')})
  const assume = (i: E) => (f.assume ? [substC(f.assume, at(i))] : [])
  const facts: Fact[] = [{name: `${f.name}: the table`, keys: ['n$'], holds: implies({op: '<', a: n, b: N}, and(le(kind(n), k(1)),
    implies(eq(kind(n), k(0)), and(yes, ...assume(n), ...names.map(x => eq(get(`${x}@`, n), substE(f.leaf[x]!, at(n)))))),
    implies(eq(kind(n), k(1)), and({op: '<', a: left(n), b: n}, {op: '<', a: right(n), b: n}, ...assume(n), ...names.map(x => eq(get(`${x}@`, n), substE(f.node[x]!, nodeAt(n)))))))) },
  // Each value a natural (true of every model), so a value read only inside a product is a column of its own.
  {name: `${f.name}: values are naturals`, keys: ['n$'], holds: and(yes, ...names.map(x => le(k(0), get(`${x}@`, n))))},
  {name: `${f.name}: params are naturals`, keys: [], holds: and(yes, ...f.params.map(x => le(k(0), v(x))))}]
  const specs: NodeSpec[] = laws.map(l => ({
    name: `${f.name}: ${l.name}`, hyps: [...(f.pre ? [f.pre] : []), {op: '<', a: n, b: N}], concl: substC(l.holds, at(n)), rank: [n],
    insts: [{fact: 0, at: [n]}, ...[n, left(n), right(n)].map(i => ({fact: 1, at: [i]})), {fact: 2, at: []}],
    uses: laws.flatMap((_, j) => [left, right].map(c => ({node: j, subst: {'n$': c(n)}, guard: eq(kind(n), k(1))}))),
  }))
  // Each law twice, as a machine's are: at a node n, rank (n, 1), from the
  // table's leaf case or from the law at a node from its children, rank (n, 0), the law read at the values the node's
  // case gives (the usual rule's node goal, over the table's cells at its children), using every law at both children.
  const L = laws.length, hyps = [...(f.pre ? [f.pre] : []), {op: '<', a: n, b: N} as C], inner = eq(kind(n), k(1))
  const valuesAt = vars({...Object.fromEntries(f.inputs.map(x => [x, get(`${x}@`, n)])), ...Object.fromEntries(names.map(x => [x, substE(f.node[x]!, nodeAt(n))]))})
  const fromChildren = laws.map((l): NodeSpec => {
    const name = `${f.name}: ${l.name}, from its children`, h = [...hyps, inner]
    return {name, hyps: h, concl: substC(l.holds, valuesAt), rank: [n, k(0)], insts: [{fact: 0, at: [n]}, ...[left(n), right(n)].map(i => ({fact: 1, at: [i]})), {fact: 2, at: []}],
      uses: laws.flatMap((_, j) => [left, right].map(c => ({node: j, subst: {'n$': c(n)}, guard: yes}))), variants: [{name, hyps: h, concl: yes, rank: [n, k(0)], insts: [], uses: [], weak: true}]}
  })
  const atNode = laws.map((l, i): NodeSpec => {
    const a: NodeSpec = {name: `${f.name}: ${l.name}`, hyps, concl: substC(l.holds, at(n)), rank: [n, k(1)], insts: [{fact: 0, at: [n]}, {fact: 1, at: [n]}, {fact: 2, at: []}],
      uses: [{node: L + i, subst: {}, guard: inner}], variants: [{...specs[i]!, rank: [n, k(1)]}]}
    const o = shared(facts, a, fromChildren[i]!.concl)
    return o.length ? {...a, opaque: o} : a
  })
  if (usual) return {facts, ...translatedFold()}
  return {facts, specs: sliced([...atNode, ...fromChildren])}

  // The usual proof translated, as a machine's is: each law three nodes. At a node, as above, its goal grown: from the
  // law at a leaf (Kind[n] = 0) or from its children (Kind[n] = 1). From its children, rank (n, 0): the usual node goal
  // over the table (an input as its cell at n, l_x and r_x as x at Left[n] and Right[n]), the laws at both children its
  // uses (each child below n a hypothesis, which the table at n gives where the node is used), the assumption at n
  // too. At a leaf, rank (n, 0): the usual leaf goal at n.
  function translatedFold(): {specs: NodeSpec[], why?: string} {
    const goals = new Map(foldObligations(f, laws).map(g => [g.name, g])), sigma = nodeAt(n), sigma0 = at(n), ren = renamer({s: sigma}), ren0 = renamer({s: sigma0})
    const na = (f.pre ? 1 : 0) + (f.assume ? 1 : 0), last = (g: Goal) => (g.hyps.at(-1) as Extract<C, {op: 'not'}>).x
    const kids: NodeSpec[] = [], leaves: NodeSpec[] = [], made: Made[] = []
    for (const [i, l] of laws.entries()) {
      const g0 = goals.get(`${l.name} @leaf`), g1 = goals.get(`${l.name} @node`), t0 = g0 && usual![g0.name], t1 = g1 && usual![g1.name]
      if (!g0 || !g1 || !t0 || !t1 || g0.hyps.length !== na + 1 || g1.hyps.length !== na + 2 * L + 1) return {specs: [], why: `${l.name}: no usual tree, or one of another shape`}
      const used1 = usedHyps(g1, t1)
      kids.push({name: `${f.name}: ${l.name}, from its children`, hyps: [...hyps, inner, {op: '<', a: left(n), b: n}, {op: '<', a: right(n), b: n}, ...(f.assume ? [substC(f.assume, sigma0)] : [])], concl: substC(last(g1), sigma), rank: [n, k(0)], insts: [],
        uses: laws.flatMap((_, j) => [left, right].map(c => ({node: j, subst: {'n$': c(n)}, guard: yes}))).filter((_, q) => used1.has(na + q))})
      leaves.push({name: `${f.name}: ${l.name}, at a leaf`, hyps: [...hyps, eq(kind(n), k(0)), ...(f.assume ? [substC(f.assume, sigma0)] : [])], concl: substC(last(g0), sigma0), rank: [n, k(0)], insts: [], uses: []})
      made.push({g: g1, tree: t1, node: L + i, ren}, {g: g0, tree: t0, node: 2 * L + i, ren: ren0})
    }
    const carried = atNode.map((a, i): NodeSpec => {
      const b: NodeSpec = {...a, variants: undefined, carry: true, uses: [...a.uses, {node: 2 * L + i, subst: {}, guard: eq(kind(n), k(0))}]}
      const o = [...new Set([...shared(facts, b, kids[i]!.concl), ...shared(facts, b, leaves[i]!.concl)].map(e => JSON.stringify(e)))].map(e => JSON.parse(e) as E)
      return {...b, opaque: o.length ? o : undefined}
    })
    const all = [...carried, ...kids, ...leaves], until = withinDeadline(clock() + 10_000)
    return translateMade(facts, all, made, st, until)
  }
}

// --- the cyclic route beside the usual one (GDP_CYCLIC=1) -------------------------------------------------------------

// With GDP_CYCLIC=1, every proof the instances above cover is made again as a cyclic proof, and a verdict that differs
// throws (GDP_CYCLIC_LAX=1 only prints it, to measure a whole run): the suite run so shows the rules are instances. Each comparison is printed to stderr as a line `cyclic: {...}`.
let quiet = 0
export const cyclicOn = () => quiet === 0 && env.GDP_CYCLIC === '1'
// The `cyclic: {...}` lines research/cyclic/ratios.ts reads, printed only with GDP_CYCLIC=1 (the cross-check) or
// GDP_CYCLIC_LOG=1 (supercomputer/run.py sets it): a user's proofs print nothing.
export const cycLog = (o: object) => { if (env.GDP_CYCLIC === '1' || env.GDP_CYCLIC_LOG === '1') console.error(`cyclic: ${JSON.stringify(o)}`) }
// A search's many trial proofs (core/discover.ts, core/infer.ts) aren't compared: what it finds is proven again.
export const quietly = <T>(f: () => T): T => { quiet++; try { return f() } finally { quiet-- } }
// GDP_CYCLIC_ROUTE: `translate` (the default) makes the cyclic proof of what the usual route proved by translating the
// usual proof (`translated`, core/translate.ts), searching it as 0.18.0 did where the translation isn't proven or there
// is none (`route` fallback, searched); `search` searches every one; `both` translates and then also searches, each timed
// apart (`searchMs`, `searchCyclic`), and both verdicts must agree with the usual one.
export type Translated = (st: TStats) => {verdict?: CyclicVerdict, why?: string}
// A translated proof by what it was made from (the machine, its laws and instances; a recurrence's or fold's case): a
// proof made again (a rule proven twice, as the suite does) is the one made and checked before (the same proof: the
// kernel's check is a function of it, and nothing changes a proof once made). The key's time is GDP_CYCLIC_PROF's `key`.
const proofsMade = new Map<string, Cyclic>()
// `base`: the key of a proof made before whose nodes these begin with (a machine's laws, for its step laws), reused where
// its facts are these.
export function translatedProof(key: () => string, build: (reused: boolean) => {facts: Fact[], specs: NodeSpec[], why?: string}, st: TStats, base?: () => string): {verdict?: CyclicVerdict, why?: string} {
  const k0 = timedKind('key', 0, key), had = proofsMade.get(k0)
  if (had) { st.cached++; return {verdict: {proven: true, checked: true, proof: had}} }
  const b = base && proofsMade.get(timedKind('key', 0, base)), {facts, specs, why} = build(!!b)
  if (why) return {why}
  const made = b && b.nodes.length <= specs.length && JSON.stringify(b.facts) === JSON.stringify(facts) ? b.nodes : []
  if (b && !made.length) return translatedProof(key, () => build(false), st)
  const v = proveCyclic(facts, specs, undefined, translatedCache, st, made)
  if (v.proven && v.checked) { if (proofsMade.size >= 1024) proofsMade.clear(); proofsMade.set(k0, v.proof) }
  return {verdict: v}
}
export const routeOf = () => env.GDP_CYCLIC_ROUTE ?? 'translate'
const none = (): CyclicVerdict => ({proven: false, checked: false, node: '', goal: 'no instance searched', stuck: 'unknown'})
// The cyclic proof of what the usual route proved: translated, else (`fallback`, or `searched` where nothing is
// translated) searched, within `until` where it is given; with why the translation wasn't proven.
// A translation within the certificate's budget (GDP_CERT_MS) or four times the usual proof's time, whichever is longer
// (`translateMs`): one that will fail is cut there, not at its goals' own bounds.
// `floor`: the least a translation is given (a step law's certificate passes its own, stepCertFloor).
export const translateMs = (usualMs = 0, floor = certMs()): number => Math.max(floor, 4 * usualMs)
// A step law's: four times its usual proof's time, at least a quarter second (GDP_CERT_STEP_MS). Its usual trees are
// the certificate where the translation isn't made, checked by kernel.ts as every certificate is, so a translation that
// will fail costs at most that. (With GDP_CERT_MS's 10 s as the floor, from 0.19.0, every step law whose translation
// fails waited it out, and twice from 0.20.0, together and then alone: a statechart's 19 step laws, proven in 0.35 s,
// took 55 s to certify, every one of the failed laws' certificates its usual trees in the end.)
export const stepCertFloor = (): number => Number(env.GDP_CERT_STEP_MS ?? 250)
function cyclicOf(translated: Translated | undefined, run: () => CyclicVerdict, st: TStats, until?: number, usualMs?: number, floor?: number): {out: CyclicVerdict, how: string, why?: string} {
  let how = 'searched', why: string | undefined
  if (translated) {
    const r = withDeadline(clock() + translateMs(usualMs, floor), () => translated(st))
    if (r.verdict?.proven && r.verdict.checked) return {out: r.verdict, how: 'translated'}
    how = 'fallback'; why = r.why ?? (r.verdict && !r.verdict.proven ? `${r.verdict.goal}: ${r.verdict.stuck}` : r.verdict?.why)
  }
  return {out: until === undefined ? run() : withDeadline(until, run), how, ...(why ? {why} : {})}
}
// GDP_CYCLIC_PROF=1: where the proof's time went, by goal kind, in its line.
const profLine = () => (profOn() ? {prof: Object.fromEntries(Object.entries(cyclicProf).map(([key, p]) => [key, Object.fromEntries(Object.entries(p).map(([f, x]) => [f, Math.round(x)]))]))} : {})
export function crossCyclic(kind: string, name: string, usual: boolean, run0: (() => CyclicVerdict) | undefined, usualMs?: number, translated?: Translated): void {
  const run = run0 ?? none
  for (const key of Object.keys(cyclicProf)) delete cyclicProf[key]
  // (a search within GDP_CERT_MS: one cut by it, or none to make where the translation fails, leaves the proof uncovered,
  // not differing)
  const route = routeOf(), st = tstats(), t0 = performance.now(), until = clock() + certMs()
  const {out, how, why} = cyclicOf(route !== 'search' && usual ? translated : undefined, run, st, until, usualMs)
  const ms = Math.round(performance.now() - t0), cyclic = out.proven && out.checked
  if (usual && !cyclic && (!run0 || clock() > until)) { uncovered(kind, name, `no cyclic proof found${run0 ? ` within ${certMs()} ms` : ''}${why ? ` (not translated: ${why})` : ''}`); return }
  const prof = profLine()
  let search: {searchMs: number, searchCyclic: boolean} | undefined
  if (route === 'both' && run0) { const s0 = performance.now(), o = run0(); search = {searchMs: Math.round(performance.now() - s0), searchCyclic: o.proven && o.checked} }
  cycLog({kind, name, usual, cyclic, ms, ...(usualMs === undefined ? {} : {usualMs: Math.round(usualMs)}), route: how, ...(how !== 'searched' ? st : {}), ...(why ? {fellBack: why} : {}), ...search, ...prof, ...(out.proven ? {nodes: out.proof.nodes.length, ...(out.why ? {why: out.why} : {})} : {goal: out.goal, stuck: out.stuck})})
  const lax = env.GDP_CYCLIC_LAX === '1'
  if (cyclic !== usual && !lax) throw new Error(`cyclic route: ${kind} ${name} is ${cyclic ? 'proven' : 'not proven'} as a cyclic proof, ${usual ? 'proven' : 'not proven'} the usual way${out.proven ? (out.why ? ` (${out.why})` : '') : ` (${out.goal}: ${out.stuck})`}`)
  if (search && search.searchCyclic !== usual && !lax) throw new Error(`cyclic route: ${kind} ${name} is ${search.searchCyclic ? 'proven' : 'not proven'} as a cyclic proof searched, ${usual ? 'proven' : 'not proven'} the usual way`)
}

// The certificate of every proof the instances above cover is the cyclic one (GDP_CERT=usual: the usual trees, as
// before 0.19.0), translated from the usual proof and checked by kernel/cyclic.ts; the usual trees are then the
// translation's input, not checked again (kernel/prove.ts, core/dsl.ts). Where no cyclic proof is made, the caller
// checks the usual trees and counts the proof uncovered (`why`). With GDP_CERT_SEARCH=1 (off by default: a search costs
// seconds a proof) a proof the translation doesn't cover is searched first, within GDP_CERT_MS (10 s by default). Each
// logs a line `cyclic: {..., cert: true}` (cycLog).
export const certMode = () => env.GDP_CERT !== 'usual'
export const certOn = () => quiet === 0 && certMode()
export const certSearch = () => env.GDP_CERT_SEARCH === '1'
export const certMs = () => Number(env.GDP_CERT_MS ?? 10_000)
// A proof of a kind no cyclic instance covers, or whose cyclic proof wasn't made, counted (`cyclic: {..., uncovered:
// true, why}`): its certificate the usual trees.
export const uncovered = (kind: string, name: string, why: string): void => cycLog({kind, name, uncovered: true, why})
export function certCyclic(kind: string, name: string, translated: Translated | undefined, run0: (() => CyclicVerdict) | undefined, usualMs?: number, floor?: number): {checked: boolean, proof?: Cyclic, why: string} {
  for (const key of Object.keys(cyclicProf)) delete cyclicProf[key]
  const st = tstats(), t0 = performance.now(), until = clock() + certMs()
  const {out, how, why} = cyclicOf(translated, (translated && !certSearch() ? undefined : run0) ?? none, st, until, usualMs, floor)
  const checked = out.proven && out.checked
  cycLog({kind, name, cert: true, usual: true, cyclic: checked, ms: Math.round(performance.now() - t0), ...(usualMs === undefined ? {} : {usualMs: Math.round(usualMs)}), route: how, ...(how !== 'searched' ? st : {}), ...(why ? {fellBack: why} : {}), ...profLine()})
  const late = clock() > until ? ` within ${certMs()} ms` : ''
  return {checked, ...(out.proven ? {proof: out.proof} : {}), why: checked ? '' : `no cyclic proof found${late}${why ? ` (not translated: ${why})` : ''}`}
}

// The step laws' searched nodes after the laws' (stepLawNodes over the sk machine), with the flags' closing facts read
// where each node reads the run on a machine with flags that hold at every key: what GDP_CERT=cyclic's search and the
// Lean export's (lean-kernel/emit.ts) both try.
export function searchedStepNodes(m: Machine, laws: Law[], steps: {law: StepLaw, instances: Instances}[], facts: Fact[], lawNodes: NodeSpec[]): NodeSpec[] {
  const q = hasQuantified(m)
  return stepLawNodes(skMachine(m), laws, steps, facts, lawNodes).map((sp, i) => {
    if (!q) return sp
    const more = closingInsts(m, facts, [steps[i]!.instances], Array.from({length: (steps[i]!.law.steps ?? 1) + 1}, (_, j) => tBack(j)))
    const add = (x: NodeSpec): NodeSpec => ({...x, insts: [...x.insts, ...more], ...(x.variants ? {variants: x.variants.map(add)} : {})})
    return add(sp)
  })
}

// Live.lean's reqC: each input named by its term, two parts per and.
export const reqTS = (req: [string, E][]): C => (req.length ? {op: 'and', xs: [{op: '=', a: {op: 'var', name: req[0]![0]}, b: req[0]![1]}, reqTS(req.slice(1))]} : {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}})
// Witnesses for a helpful request's free inputs, for its allowed goal: all free first, then each free input fixed to 0, a
// state variable or a param (a history's query, say, which its relations bound), the first combination that proves.
export function withWitness<R>(m: Machine, request: Record<string, E>, attempt: (wit: [string, E][]) => R | undefined): {wit: [string, E][], out: R} | undefined {
  const free = m.inputs.filter(i => !(i in request))
  const cands: (E | undefined)[] = [undefined, {op: 'const', value: 0}, ...Object.keys(m.state).map(v => ({op: 'var', name: v}) as E), ...m.params.map(v => ({op: 'var', name: v}) as E)]
  const combos: [string, E][][] = [[]]
  if (free.length <= 2) {
    const go = (i: number, acc: [string, E][]) => { if (i === free.length) { if (acc.length) combos.push(acc); return } for (const c of cands) go(i + 1, c ? [...acc, [free[i]!, c]] : acc) }
    go(0, [])
  }
  for (const wit of combos) { const out = attempt(wit); if (out !== undefined) return {wit, out} }
  return undefined
}
