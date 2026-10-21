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
import type {C, E, Law, Machine} from './machine.ts'
import type {Fold, Goal, Instances, Subst, Tree} from '../kernel/kernel.ts'
import {substC, substE} from '../kernel/kernel.ts'
import {type CNode, type Cyclic, type Fact, type Use, descentGoal, mainGoal, premiseGoal, refuseCyclic} from '../kernel/cyclic.ts'
import {cellProducts, grow} from '../kernel/prove.ts'

export type NodeSpec = Omit<CNode, 'uses' | 'main'> & {uses: Omit<Use, 'premises' | 'descent'>[]}
export type CyclicVerdict = {proven: true, checked: boolean, proof: Cyclic, why?: string} | {proven: false, checked: false, node: string, goal: string, stuck: string}

const v = (name: string): E => ({op: 'var', name})
const k = (value: number): E => ({op: 'const', value})
const add = (a: E, b: E): E => ({op: 'add', a, b})
const less1 = (a: E): E => ({op: 'sub', a, b: k(1)})
const get = (map: string, key: E): E => ({op: 'get', map, key})
const le = (a: E, b: E): C => ({op: '<=', a, b})
const eq = (a: E, b: E): C => ({op: '=', a, b})
const and = (...xs: C[]): C => (xs.length === 1 ? xs[0]! : {op: 'and', xs})
const implies = (a: C, b: C): C => ({op: 'or', xs: [{op: 'not', x: a}, b]})
const yes: C = le(k(0), k(0))
const vars = (s: Record<string, E>): Subst => ({vars: s, maps: {}, flags: {}})
// A map's cell at time u and key k, in the run's one map over both: u + k·Ω, where Ω is above the run's length T, so
// that no two (u, k) with u <= T meet (u < Ω). Linear in u, and two keys' cells differ by (k − k')·Ω.
const omega = v('O$')
export const pair = (u: E, key: E): E => add(u, {op: 'prod', a: key, b: omega})

// Every goal grown, then the whole checked by the kernel.
export function proveCyclic(facts: Fact[], specs: NodeSpec[]): CyclicVerdict {
  const nodes: CNode[] = []
  const grown = (g: Goal, node: string): Tree | {proven: false, checked: false, node: string, goal: string, stuck: string} => {
    const was = cellProducts.on
    cellProducts.on = true
    let o: ReturnType<typeof grow>
    try { o = grow(g) } finally { cellProducts.on = was }
    return 'tree' in o ? o.tree : {proven: false, checked: false, node, goal: g.name, stuck: o.stuck}
  }
  for (const n of specs) {
    const main = grown(mainGoal(facts, specs, n), n.name)
    if ('proven' in main) return main
    const uses: Use[] = []
    for (const u of n.uses) {
      const m = specs[u.node]
      if (!m) return {proven: false, checked: false, node: n.name, goal: `use of node ${u.node}`, stuck: 'no such node'}
      const premises: Tree[] = []
      for (const [i, c] of m.hyps.entries()) { const t = grown(premiseGoal(facts, n, u, c, i), n.name); if ('proven' in t) return t; premises.push(t) }
      const descent = grown(descentGoal(facts, n, u, m), n.name)
      if ('proven' in descent) return descent
      uses.push({...u, premises, descent})
    }
    nodes.push({...n, uses, main})
  }
  const proof: Cyclic = {facts, nodes}, why = refuseCyclic(proof)
  return {proven: true, checked: why === undefined, proof, ...(why ? {why} : {})}
}

// The facts of a machine's functions (laws about every key of them), as cyclic facts.
const factOf = (l: Law): Fact => ({name: l.name, keys: [...(l.forall ? [l.forall] : []), ...(l.keys ?? [])], holds: l.holds})

// --- recurrences ----------------------------------------------------------------------------------------------------

// A recurrence f(0) = zero, f(x + 1) = next(x, f(x)), its further arguments fixed (plain variables here, as along the
// recursion), and the functions it reads with their facts. Each lemma reads x and fx; each law between two points x, fx,
// y, fy (for x <= y).
export type RecurCase = {name: string, args: string[], zero: E, next: E, lemmas: {name: string, holds: C}[], between: {name: string, holds: C}[], facts: Law[]}
export function recurNodes(r: RecurCase): {facts: Fact[], specs: NodeSpec[]} {
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
  return {facts, specs: withReads(facts, specs)}
}

// Function facts at the keys a node's goal reads them at: each fact about every key of a function read f[k] (the key
// alone) at each key f is read at, twice over (a fact's own reads give more keys).
function withReads(facts: Fact[], specs: NodeSpec[]): NodeSpec[] {
  const simple = facts.flatMap((f, i) => {
    if (f.keys.length !== 1) return []
    const reads = [...JSON.stringify(f.holds).matchAll(/"op":"get","map":"([^"]+)","key":\{"op":"var","name":"([^"]+)"\}/g)].filter(m => m[2] === f.keys[0])
    return reads.map(m => ({fact: i, map: m[1]!}))
  })
  if (!simple.length) return specs
  const readsIn = (t: unknown, map: string): E[] => { const out: E[] = []; const walk = (x: unknown): void => { if (x && typeof x === 'object') { const o = x as Record<string, unknown>; if (o.op === 'get' && o.map === map) out.push(o.key as E); for (const val of Object.values(o)) walk(val) } }; walk(t); return out }
  return specs.map(n => {
    const insts = [...n.insts], seen = new Set(insts.map(p => JSON.stringify(p)))
    for (let round = 0; round < 2; round++) {
      const goal = [n.hyps, n.concl, insts.map(p => substC(facts[p.fact]!.holds, vars(Object.fromEntries(facts[p.fact]!.keys.map((key, i) => [key, p.at[i]!]))))), n.uses.map(u => substC(specs[u.node]!.concl, vars(u.subst)))]
      for (const s of simple) for (const key of readsIn(goal, s.map)) {
        const p = {fact: s.fact, at: [key]}, id = JSON.stringify(p)
        if (!seen.has(id)) { seen.add(id); insts.push(p) }
      }
    }
    return {...n, insts}
  })
}

// --- machines -------------------------------------------------------------------------------------------------------

// The machines this instance covers: no history, no flag holding at every key, and no law that reads a map at a key
// read from a map of the state (a table of nodes: a node's fold at its child), whose cells a run's maps put at keys
// the prover would have to prove equal through products (`machineNodes` proves those laws far slower than the usual
// rule, past its budget: research/cyclic/probe.ts).
export const cyclicMachine = (m: Machine, laws: Law[] = []): boolean => {
  const maps = Object.keys(m.maps ?? {})
  const nested = (t: unknown): boolean => { let found = false; const walk = (x: unknown, inKey: boolean): void => { if (found || !x || typeof x !== 'object') return; const o = x as Record<string, unknown>; if (o.op === 'get' && inKey && maps.includes(o.map as string)) { found = true; return } if (o.op === 'get') { walk(o.key, true); return } for (const val of Object.values(o)) walk(val, inKey) }; walk(t, false); return found }
  return !m.history && !Object.values(m.step.flags ?? {}).some(c => c.op === 'all') && !laws.some(l => nested(l.holds))
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

export function machineNodes(m: Machine, laws: Law[], instances: Record<string, Instances>): {facts: Fact[], specs: NodeSpec[]} {
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
  ]
  const fi = (name: string) => facts.findIndex(f => f.name === name)
  const keysOf = (l: Law) => [...(l.forall ? [l.forall] : []), ...(l.keys ?? [])]
  // A map read at the node's time t at key e: that map's start, step and natural facts at (t, e).
  const mapInsts = (c: unknown): NodeSpec['insts'] => {
    const out: NodeSpec['insts'] = [], seen = new Set<string>()
    const walk = (x: unknown): void => {
      if (!x || typeof x !== 'object') return
      const o = x as Record<string, unknown>
      if (o.op === 'get' && typeof o.map === 'string' && o.map.endsWith('@') && mapNames.includes(o.map.slice(0, -1))) {
        const kk = o.key as E
        if (kk.op === 'add' && JSON.stringify(kk.a) === JSON.stringify(t) && kk.b.op === 'prod') {
          const read = kk.b.a, id = JSON.stringify(read), map = o.map.slice(0, -1)
          if (!seen.has(`${map}:${id}`)) { seen.add(`${map}:${id}`); out.push(...['at the start', 'at a step', '\'s cells are naturals'].map(what => ({fact: fi(`${m.name}: ${map}${what.startsWith('\'') ? what : ` ${what}`}`), at: [t, read]}))) }
        }
      }
      for (const val of Object.values(o)) walk(val)
    }
    walk(c)
    return out
  }
  const specs: NodeSpec[] = laws.map(l => {
    const inst = instances[l.name] ?? {}
    // Terms over the frame before the step (the machine's proof proves a law about every key at a fresh key k#: here
    // the node's own k).
    const fresh = Object.fromEntries(laws.flatMap(x => (x.forall ? [[`${x.forall}#`, v(x.forall)]] : [])))
    const pre = at(less1(t)), before = (e: E) => substE(substE(e, vars(fresh)), pre)
    // The laws at the step before, at the keys the machine's proof assumes them at.
    const uses: NodeSpec['uses'] = laws.flatMap((l2, j) => {
      const ks = keysOf(l2)
      if (!ks.length) return [{node: j, subst: {'t$': less1(t)}, guard: le(k(1), t)}]
      const flat = inst[l2.name] ?? []
      return Array.from({length: Math.floor(flat.length / ks.length)}, (_, i) => ({node: j, subst: {'t$': less1(t), ...Object.fromEntries(ks.map((kn, q) => [kn, before(flat[i * ks.length + q]!)]))}, guard: le(k(1), t)}))
    })
    // The functions' facts at the keys the proof names, over the frame before the step (at t = 0, the start's).
    const factInsts = (m.facts ?? []).flatMap(f => {
      const ks = keysOf(f), flat = inst[f.name] ?? []
      if (!ks.length) return [{fact: fi(f.name), at: []}]
      return Array.from({length: Math.floor(flat.length / ks.length)}, (_, i) => ({fact: fi(f.name), at: flat.slice(i * ks.length, (i + 1) * ks.length).map(before)}))
    })
    const concl = substC(l.holds, at(t))
    const useConcls = uses.map(us => substC(substC(laws[us.node]!.holds, at(t)), vars(us.subst)))
    const base = mapInsts([concl, useConcls])
    return {
      name: `${m.name}: ${l.name}`, hyps: [...(m.pre ? [m.pre] : []), le(t, T), ...(mapNames.length ? [{op: '<', a: T, b: omega} as C] : [])], concl, rank: [t],
      insts: [{fact: 0, at: [t]}, {fact: 1, at: [t]}, ...factInsts, ...base, ...state.map(st => ({fact: fi(`${m.name}: ${st} is a natural`), at: [t]})), {fact: fi(`${m.name}: params are naturals`), at: []}], uses,
    }
  })
  return {facts, specs}
}

// --- folds over trees -----------------------------------------------------------------------------------------------

// The tree as a table of nodes below its size N: a node n is a leaf (Kind[n] = 0) whose values come from its inputs,
// or a node (Kind[n] = 1) with children Left[n], Right[n] numbered below n, its values from theirs and its inputs.
export function foldNodes(f: Fold, laws: Law[]): {facts: Fact[], specs: NodeSpec[]} {
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
  return {facts, specs}
}

// --- the cyclic route beside the usual one (GDP_CYCLIC=1) -------------------------------------------------------------

// With GDP_CYCLIC=1, every proof the instances above cover is made again as a cyclic proof, and a verdict that differs
// throws: the suite run so shows the rules are instances. Each comparison is printed to stderr as a line `cyclic: {...}`.
const env = () => (globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env
let quiet = 0
export const cyclicOn = () => quiet === 0 && env()?.GDP_CYCLIC === '1'
// A search's many trial proofs (core/discover.ts, core/infer.ts) aren't compared: what it finds is proven again.
export const quietly = <T>(f: () => T): T => { quiet++; try { return f() } finally { quiet-- } }
export function crossCyclic(kind: string, name: string, usual: boolean, run: () => CyclicVerdict, usualMs?: number): void {
  const t0 = performance.now(), out = run(), ms = Math.round(performance.now() - t0)
  const cyclic = out.proven && out.checked
  console.error(`cyclic: ${JSON.stringify({kind, name, usual, cyclic, ms, ...(usualMs === undefined ? {} : {usualMs: Math.round(usualMs)}), ...(out.proven ? {nodes: out.proof.nodes.length, ...(out.why ? {why: out.why} : {})} : {goal: out.goal, stuck: out.stuck})})}`)
  if (cyclic !== usual) throw new Error(`cyclic route: ${kind} ${name} is ${cyclic ? 'proven' : 'not proven'} as a cyclic proof, ${usual ? 'proven' : 'not proven'} the usual way${out.proven ? (out.why ? ` (${out.why})` : '') : ` (${out.goal}: ${out.stuck})`}`)
}
