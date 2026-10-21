// Cycles found: cyclic proofs (kernel/cyclic.ts) whose shape nobody wrote. core/cyclic.ts's builders fix each node's
// rank (x, t, n) and its back-edges (x − 1, t − 1, the children); here they are searched for, untrusted, and the kernel
// checks the proof as it checks any. From claims (sequents over the facts: hypotheses and a conclusion, no rank, no
// back-edge):
//   - the facts that define a function by equations (f(k) = body, or f(0) = z and f(k + 1) = body, a function of several
//     arguments read at their pairing, core/dsl.ts's argsKey) are run: values, and at each claim's samples the calls its
//     goal makes, so a false claim comes back with the point that breaks it
//   - the facts at the terms the goal reads (and those their bodies read, twice over); back-edges: a claim at the
//     arguments of any call the goal reads (n + 11, f(n + 11), (m − 1, ack(m, n − 1))), its guard where it may be used
//     (its hypotheses there and its rank there below), so each premise and each descent is its guard's
//   - ranks from the runs: each sampled call a back-edge makes is an edge that must drop, and the rank, linear over the
//     claim's variables (101 − n, a + b), an integer LP (solver.ts, its rows generated from the violated ones), by
//     successive elimination (Bradley–Manna–Sipma): each component drops on every edge it can and never rises, the edges
//     it keeps left to the next, so (m, n) for Ackermann
//   - where a claim's goal is stuck: its constants abstracted (g(x, 0) to g(x, a), the conclusion fitted exactly to the
//     values) into a companion below it (rank first by level); or companions beside it about what its goal reads,
//     bounds fitted to the values, Houdini over them (one whose goal fails is dropped, the rest proven again)
// The claims are nodes of the proof as they were given; what was found are the companions, the ranks and the uses.
//
// Loops (kernel.ts's Loop) the same way: `findRank` takes the rank from the loop's runs (each turn an edge), and where
// the kernel's halting goals need an invariant, inferLaws finds it with the descent as step laws (the loop's own
// liveness), the verdict loopObligations' with the rank and the laws found.
//
// Functions a rule reads (fns, known to the kernel by their facts): `cycleLemmas` fits lemmas to their JavaScript's
// values (a constant on a region, a line, bounds), proves them from the facts as cyclic claims (Houdini), and proves the
// laws with them as facts.
import type {C, E, Law, Machine} from './machine.ts'
import {fnValue, pairedArgs} from './machine.ts'
import type {Goal, Loop, Subst, Tree} from '../kernel/kernel.ts'
import {check, livenessParts, loopLiveness, loopMachine, loopObligations, substC, substE} from '../kernel/kernel.ts'
import {type Cyclic, type Fact, factsAvoid, lexLt} from '../kernel/cyclic.ts'
import {type NodeSpec, proveCyclic} from './cyclic.ts'
import {type Lin, solve} from './solver.ts'
import {grow, proveLaws, proveStepLaws, withDeadline} from '../kernel/prove.ts'
import {inferLaws} from './infer.ts'
import type {StepLaw} from '../kernel/kernel.ts'

export type Claim = {name: string, hyps?: C[], concl: C}
export type CycleOptions = {ms?: number, depth?: number, values?: Record<string, (...xs: number[]) => number>,
  // Every claim may be dropped (lemma candidates): the verdict is about those kept.
  houdini?: boolean, generalize?: boolean}
export type CycleFound = {ranks: Record<string, string>, companions: string[], uses: number}
export type CycleVerdict = {proven: boolean, checked: boolean, proof?: Cyclic, specs?: NodeSpec[], kept?: string[], found?: CycleFound,
  goal?: string, stuck?: string, witness?: Record<string, number>, why?: string}

// --- terms ----------------------------------------------------------------------------------------------------------

const v = (name: string): E => ({op: 'var', name}), k = (value: number): E => ({op: 'const', value})
const add = (a: E, b: E): E => ({op: 'add', a, b}), sub = (a: E, b: E): E => ({op: 'sub', a, b})
const get = (map: string, key: E): E => ({op: 'get', map, key})
const le = (a: E, b: E): C => ({op: '<=', a, b}), eqC = (a: E, b: E): C => ({op: '=', a, b})
const and = (...xs: C[]): C => (xs.length === 1 ? xs[0]! : {op: 'and', xs})
const yes: C = le(k(0), k(0))
const vs = (s: Record<string, E>): Subst => ({vars: s, maps: {}, flags: {}})
const id = (t: unknown) => JSON.stringify(t)
export const pairE = (a: E, b: E): E => { const s = add(a, b); return add({op: 'prod', a: s, b: s}, b) }
export const argsKey = (args: E[]): E => args.slice(1).reduce(pairE, args[0]!)

// Σ coef·x + c as a term over the naturals: the negative part subtracted (truncated, as the kernel reads sub).
export const linE = (coef: Record<string, number>, c: number): E => {
  const pos: E[] = [], neg: E[] = []
  if (c > 0) pos.push(k(c))
  for (const [x, a] of Object.entries(coef)) if (a) (a > 0 ? pos : neg).push(Math.abs(a) === 1 ? v(x) : {op: 'mul', k: Math.abs(a), a: v(x)})
  if (c < 0) neg.push(k(-c))
  const sum = (xs: E[]) => xs.reduce((s, x) => add(s, x))
  return !pos.length ? k(0) : !neg.length ? sum(pos) : sub(sum(pos), sum(neg))
}
export const showE = (e: E): string => {
  switch (e.op) {
    case 'var': return e.name
    case 'const': return String(e.value)
    case 'add': return `${showE(e.a)} + ${showE(e.b)}`
    case 'sub': return `${showE(e.a)} − ${e.b.op === 'add' || e.b.op === 'sub' ? `(${showE(e.b)})` : showE(e.b)}`
    case 'mul': return `${e.k}·${e.a.op === 'var' || e.a.op === 'const' ? showE(e.a) : `(${showE(e.a)})`}`
    case 'prod': return `(${showE(e.a)})·(${showE(e.b)})`
    case 'min': case 'max': return `${e.op}(${showE(e.a)}, ${showE(e.b)})`
    case 'if': return `if ${showC(e.c)} then ${showE(e.then)} else ${showE(e.else)}`
    case 'get': { const as = pairedArgs(e.key, 2), as3 = as && pairedArgs(e.key, 3); return `${e.map}(${(as3 ?? as ?? [e.key]).map(showE).join(', ')})` }
  }
}
export const showC = (c: C): string => {
  switch (c.op) {
    case '<': case '<=': case '=': return `${showE(c.a)} ${c.op === '<=' ? '≤' : c.op} ${showE(c.b)}`
    case 'and': return c.xs.map(x => (x.op === 'or' ? `(${showC(x)})` : showC(x))).join(' ∧ ')
    case 'or': return c.xs.map(showC).join(' ∨ ')
    case 'not': return `¬(${showC(c.x)})`
    case 'flag': return `?${c.name}`
    case 'all': return `∀${c.key}. ${showC(c.c)}`
  }
}
const walk = (t: unknown, f: (o: Record<string, unknown>) => void): void => {
  if (Array.isArray(t)) { for (const x of t) walk(x, f); return }
  if (!t || typeof t !== 'object') return
  const o = t as Record<string, unknown>
  f(o)
  for (const x of Object.values(o)) walk(x, f)
}
const readsOf = (t: unknown): Extract<E, {op: 'get'}>[] => { const out: Extract<E, {op: 'get'}>[] = []; walk(t, o => { if (o.op === 'get') out.push(o as never) }); return out }
const varsOf = (t: unknown): string[] => { const out = new Set<string>(); walk(t, o => { if (o.op === 'var') out.add(o.name as string) }); return [...out].sort() }
const constsOf = (t: unknown): number[] => { const out: number[] = []; walk(t, o => { if (o.op === 'const') out.push(o.value as number) }); return out }

// --- the facts as equations, run ------------------------------------------------------------------------------------

// An equation f(pattern) = body of a fact: each argument of the pattern a key, a key plus a constant, or a constant,
// the body reading the keys alone.
type Eqn = {fact: number, map: string, pat: E[], body: E}
type Ctx = {eqs: Map<string, Eqn[]>, arity: Map<string, number>, values: Record<string, (...xs: number[]) => number>, memo: Map<string, number>, fuel: number, depth: number}
const patArg = (e: E, keys: string[]): string | undefined => (e.op === 'var' && keys.includes(e.name) ? e.name : e.op === 'add' && e.a.op === 'var' && keys.includes(e.a.name) && e.b.op === 'const' ? e.a.name : undefined)
function equations(facts: Fact[]): {eqs: Map<string, Eqn[]>, arity: Map<string, number>} {
  const eqs = new Map<string, Eqn[]>(), arity = new Map<string, number>()
  for (const [i, f] of facts.entries()) {
    for (const part of f.holds.op === 'and' ? f.holds.xs : [f.holds]) {
      if (part.op !== '=') continue
      for (const [lhs, body] of [[part.a, part.b], [part.b, part.a]] as const) {
        if (lhs.op !== 'get') continue
        let n = 4
        while (n > 1 && !pairedArgs(lhs.key, n)) n--
        const pat = pairedArgs(lhs.key, n)!, bound = pat.map(a => patArg(a, f.keys))
        if (!pat.every((a, j) => bound[j] || a.op === 'const') || new Set(bound.filter(Boolean)).size !== bound.filter(Boolean).length) continue
        if (!varsOf(body).every(x => bound.includes(x))) continue
        if ((arity.get(lhs.map) ?? n) !== n) continue
        arity.set(lhs.map, n)
        eqs.set(lhs.map, [...(eqs.get(lhs.map) ?? []), {fact: i, map: lhs.map, pat, body}])
        break
      }
    }
  }
  return {eqs, arity}
}
const argsOf = (cx: Pick<Ctx, 'arity'>, r: Extract<E, {op: 'get'}>): E[] => pairedArgs(r.key, cx.arity.get(r.map) ?? 1) ?? [r.key]
// The equation's bindings at numbers, or undefined where its pattern doesn't match.
const matchNums = (e: Eqn, xs: number[]): Record<string, number> | undefined => {
  const out: Record<string, number> = {}
  for (const [j, p] of e.pat.entries()) {
    const x = xs[j]!
    if (p.op === 'const') { if (p.value !== x) return undefined }
    else if (p.op === 'var') out[p.name] = x
    else if (p.op === 'add' && p.a.op === 'var' && p.b.op === 'const') { if (x < p.b.value) return undefined; out[p.a.name] = x - p.b.value }
  }
  return out
}
function callF(cx: Ctx, map: string, xs: number[]): number | undefined {
  const key = `${map}(${xs.join(',')})`, got = cx.memo.get(key)
  if (got !== undefined) return got
  const f = cx.values[map]
  if (f) { let out: number | undefined; try { out = f(...xs) } catch { out = undefined } if (out === undefined || !Number.isSafeInteger(out) || out < 0) return undefined; cx.memo.set(key, out); return out }
  if (cx.fuel <= 0 || cx.depth >= 400) return undefined
  for (const e of cx.eqs.get(map) ?? []) {
    const env = matchNums(e, xs)
    if (!env) continue
    cx.fuel--; cx.depth++
    const out = ev(cx, e.body, env)
    cx.depth--
    if (out !== undefined) cx.memo.set(key, out)
    return out
  }
  return undefined
}
type Rec = {out: Set<string>, depth: number}
function ev(cx: Ctx, e: E, env: Record<string, number>, rec?: Rec): number | undefined {
  const two = (a: E, b: E, f: (x: number, y: number) => number) => { const x = ev(cx, a, env, rec), y = ev(cx, b, env, rec); return x === undefined || y === undefined ? undefined : f(x, y) }
  switch (e.op) {
    case 'var': return env[e.name]
    case 'const': return e.value
    case 'add': return two(e.a, e.b, (x, y) => x + y)
    case 'sub': return two(e.a, e.b, (x, y) => Math.max(0, x - y))
    case 'min': return two(e.a, e.b, Math.min)
    case 'max': return two(e.a, e.b, Math.max)
    case 'prod': return two(e.a, e.b, (x, y) => x * y)
    case 'mul': { const x = ev(cx, e.a, env, rec); return x === undefined ? undefined : e.k * x }
    case 'if': { const c = evC(cx, e.c, env, rec); return c === undefined ? undefined : ev(cx, c ? e.then : e.else, env, rec) }
    case 'get': {
      const xs: number[] = []
      for (const a of argsOf(cx, e)) { const x = ev(cx, a, env, rec); if (x === undefined) return undefined; xs.push(x) }
      const out = callF(cx, e.map, xs)
      if (rec) {
        rec.out.add(`${e.map}(${xs.join(',')})`)
        if (rec.depth > 0) for (const q of cx.eqs.get(e.map) ?? []) { const at = matchNums(q, xs); if (at) { ev(cx, q.body, at, {out: rec.out, depth: rec.depth - 1}); break } }
      }
      return out
    }
  }
}
function evC(cx: Ctx, c: C, env: Record<string, number>, rec?: Rec): boolean | undefined {
  switch (c.op) {
    case '<': case '<=': case '=': { const a = ev(cx, c.a, env, rec), b = ev(cx, c.b, env, rec); return a === undefined || b === undefined ? undefined : c.op === '<' ? a < b : c.op === '<=' ? a <= b : a === b }
    case 'and': { let out: boolean | undefined = true; for (const x of c.xs) { const y = evC(cx, x, env, rec); if (y === false) return false; if (y === undefined) out = undefined } return out }
    case 'or': { let out: boolean | undefined = false; for (const x of c.xs) { const y = evC(cx, x, env, rec); if (y === true) return true; if (y === undefined) out = undefined } return out }
    case 'not': { const y = evC(cx, c.x, env, rec); return y === undefined ? undefined : !y }
    case 'flag': case 'all': return undefined
  }
}
const allTrue = (cx: Ctx, cs: C[], env: Record<string, number>): boolean | undefined => evC(cx, and(yes, ...cs), env)

// --- instances and back-edges ---------------------------------------------------------------------------------------

type Node = {name: string, hyps: C[], concl: C, vars: string[], level: number, given: boolean}
// The fact's keys at a read's arguments, for an equation of it (a key plus a constant at an argument u + c is u, at any
// other term t is t − c).
const bindAt = (facts: Fact[], e: Eqn, args: E[]): E[] | undefined => {
  const at: Record<string, E> = {}
  for (const [j, p] of e.pat.entries()) {
    const t = args[j]!
    if (p.op === 'const') { if (id(t) !== id(p)) return undefined }
    else if (p.op === 'var') at[p.name] = t
    else if (p.op === 'add' && p.a.op === 'var' && p.b.op === 'const') at[p.a.name] = t.op === 'add' && t.b.op === 'const' && t.b.value === p.b.value ? t.a : sub(t, p.b)
  }
  const keys = facts[e.fact]!.keys
  return keys.every(x => x in at) ? keys.map(x => at[x]!) : undefined
}
function instancesFor(facts: Fact[], cx: Ctx, n: Node, depth: number): {insts: NodeSpec['insts'], reads: Extract<E, {op: 'get'}>[]} {
  const insts: NodeSpec['insts'] = facts.flatMap((f, i) => (f.keys.length ? [] : [{fact: i, at: []}]))
  const seen = new Set(insts.map(id)), readSeen = new Set<string>(), reads: Extract<E, {op: 'get'}>[] = []
  // A plain fact about every key of one function, read at its key alone: at each key the goal reads that function at.
  const single = facts.flatMap((f, i) => (f.keys.length === 1 && !cx.eqs.size ? readsOf(f.holds).filter(r => id(r.key) === id(v(f.keys[0]!))).map(r => ({fact: i, map: r.map})) : []))
  let front = readsOf([n.hyps, n.concl])
  for (let d = 0; d <= depth; d++) {
    const next: Extract<E, {op: 'get'}>[] = []
    for (const r of front) {
      if (readSeen.has(id(r))) continue
      readSeen.add(id(r)); reads.push(r)
      if (d === depth) continue
      for (const q of cx.eqs.get(r.map) ?? []) {
        const at = bindAt(facts, q, argsOf(cx, r))
        if (!at) continue
        const p = {fact: q.fact, at}
        if (!seen.has(id(p))) { seen.add(id(p)); insts.push(p) }
        next.push(...readsOf(substE(q.body, vs(Object.fromEntries(facts[q.fact]!.keys.map((x, j) => [x, at[j]!]))))))
      }
      for (const s of single) if (s.map === r.map) { const p = {fact: s.fact, at: [r.key]}; if (!seen.has(id(p))) { seen.add(id(p)); insts.push(p) } }
    }
    front = next
  }
  return {insts, reads}
}
type Cand = {node: number, subst: Record<string, E>}
// Each node m used at the arguments of a call the goal reads of the function m's conclusion reads.
function usesFor(facts: Fact[], cx: Ctx, nodes: Node[], i: number, reads: Extract<E, {op: 'get'}>[]): Cand[] {
  const n = nodes[i]!, out: Cand[] = [], seen = new Set<string>()
  for (const [j, m] of nodes.entries()) {
    if (m.level > n.level) continue
    for (const mr of readsOf(m.concl)) {
      const P = argsOf(cx, mr)
      if (!P.some(p => p.op === 'var' && m.vars.includes(p.name))) continue
      for (const r of reads) {
        if (r.map !== mr.map) continue
        const A = argsOf(cx, r)
        if (A.length !== P.length) continue
        const s: Record<string, E> = {}
        let ok = true
        for (const [q, p] of P.entries()) {
          if (p.op === 'var' && m.vars.includes(p.name)) { if (s[p.name] && id(s[p.name]) !== id(A[q])) ok = false; else s[p.name] = A[q]! }
          else if (id(p) !== id(A[q])) ok = false
        }
        for (const x of m.vars) if (!(x in s)) { if (n.vars.includes(x)) s[x] = v(x); else ok = false }
        if (!ok || (j === i && m.vars.every(x => id(s[x]) === id(v(x)))) || !factsAvoid(facts, s)) continue
        const c = {node: j, subst: s}
        if (!seen.has(id(c))) { seen.add(id(c)); out.push(c) }
      }
    }
  }
  return out
}

// --- samples, edges, ranks ------------------------------------------------------------------------------------------

type Env = Record<string, number>
const grid = (names: string[], bound: number): Env[] => {
  const out: Env[] = [], total = (bound + 1) ** names.length
  for (let i = 0; i < total; i++) { let rest = i; out.push(Object.fromEntries(names.map(x => { const d = rest % (bound + 1); rest = Math.floor(rest / (bound + 1)); return [x, d] }))) }
  return out
}
const boundFor = (d: number, big: number) => (d === 0 ? 0 : Math.min([0, 400, 40, 12, 6][Math.min(d, 4)]!, Math.max(24, 2 * big + 20)))
type Sampled = {env: Env, calls: Set<string>}
function samplesOf(cx: Ctx, n: Node, depth: number, big: number): {ok: Sampled[], broken?: Env} {
  const ok: Sampled[] = []
  for (const env of grid(n.vars, boundFor(n.vars.length, big))) {
    cx.fuel = 20_000
    if (allTrue(cx, n.hyps, env) !== true) continue
    const calls = new Set<string>(), c = evC(cx, n.concl, env, {out: calls, depth})
    if (c === undefined) continue
    if (!c) return {ok, broken: env}
    ok.push({env, calls})
  }
  return {ok}
}
type Edge = {from: number, to: number, s: Env, t: Env}
// The LP's unknowns for node n's coefficient at its j-th variable and its constant: its own, or shared by the nodes of a
// strongly connected component positionally (fewer unknowns: elimination grows with them).
type Naming = (n: number, j: number | 'b') => string
const own = (nodes: Node[]): Naming => (n, j) => (j === 'b' ? `b:${n}` : `a:${n}:${nodes[n]!.vars[j]}`)
const shared: Naming = (_n, j) => (j === 'b' ? 'b:*' : `a:*:${j}`)
// r_n(σ) as a row over the LP's unknowns.
const rankRow = (n: number, nodes: Node[], s: Env, name: Naming, scale = 1): Lin => {
  let out: Lin = {[name(n, 'b')]: scale}
  for (const [j, x] of nodes[n]!.vars.entries()) if (s[x]) out = plus(out, {[name(n, j)]: scale * s[x]!})
  return out
}
const plus = (a: Lin, b: Lin): Lin => { const o: Lin = {...a}; for (const [x, c] of Object.entries(b)) { o[x] = (o[x] ?? 0) + c; if (!o[x]) delete o[x] } return o }
const valueAt = (l: Lin, w: Record<string, number>) => Object.entries(l).reduce((s, [x, c]) => s + c * (x === '1' ? 1 : w[x] ?? 0), 0)
// An integer solution of every row (lin <= 0) of `must` and `pool`, the pool's rows added as they are violated. Its
// unknowns are bounded, the coefficients first to naturals (a rank with no subtraction, which no truncation bends), then
// either sign, each bound doubled up to 4 and the constants' first small, then up to the samples' size: the first found
// is small (x + y, not 33·x + y; total − cur, not 26 − cur), and a rank the samples' size bounds is left to the next
// component (two phases: (x, y)). A fit's coefficients (c:) go up to 128.
function lp(must: Lin[], pool: Lin[], until: number, scale = 1, signs: boolean[] = [true, false]): Record<string, number> | undefined {
  const unknowns = [...new Set([...must, ...pool].flatMap(l => Object.keys(l)).filter(x => x !== '1'))]
  const fit = unknowns.some(x => x.startsWith('c:')), bounds = fit ? [1, 2, 4, 16, 128] : [1, 2, 4]
  const stage = (natural: boolean, bound: number, wide: boolean): Record<string, number> | undefined => {
    const rows = [...must]
    for (const x of unknowns) {
      const b = x.startsWith('b:') ? (wide ? bound * scale : bound) : bound
      rows.push({[x]: 1, 1: -b}, natural ? {[x]: -1} : {[x]: -1, 1: -b})
    }
    for (let round = 0; round < 40 && performance.now() < until; round++) {
      const out = solve(rows.map(lin => ({lin, label: ''})), 4000)
      if (out.kind !== 'sat') break
      const bad = pool.filter(l => valueAt(l, out.witness) > 0).sort((a, b) => valueAt(b, out.witness) - valueAt(a, out.witness))
      if (!bad.length) return out.witness
      rows.push(...bad.slice(0, 6))
    }
    return undefined
  }
  // The widest box first: where it has no solution, none of the smaller has.
  if (!stage(signs.at(-1)!, bounds.at(-1)!, true)) return undefined
  for (const natural of signs) for (const bound of bounds) for (const wide of [false, true]) { const w = stage(natural, bound, wide); if (w) return w }
  return undefined
}
type Comp = Record<string, number>
// Lexicographic ranks over the edges (each from a node at a sample to a node at its arguments), every component >= 0
// at every sample: Bradley–Manna–Sipma's successive elimination, each component the sum of one solution per edge it can
// make drop. An edge no component makes drop is left (its use's guard keeps it where the rank drops, if anywhere).
function lexRanks(idx: number[], nodes: Node[], samples: Sampled[][], edges: Edge[], name: Naming, until: number): {comps: Comp[], left: number} {
  const points = [...new Map(idx.flatMap(n => samples[n]!.map(s => { const l = rankRow(n, nodes, s.env, name, -1); return [id(l), l] as const }))).values()]
  const delta = (e: Edge): Lin => plus(rankRow(e.to, nodes, e.t, name), rankRow(e.from, nodes, e.s, name, -1))
  const scale = 1 + Math.max(0, ...idx.flatMap(n => samples[n]!.flatMap(s => Object.values(s.env))))
  let left = [...new Map(edges.map(e => { const l = delta(e); return [id(l), l] as const })).values()]
  const comps: Comp[] = []
  while (left.length && comps.length < 4 && performance.now() < until) {
    let sum: Comp = {}
    const strict = (l: Lin) => valueAt(l, sum) < 0
    // One try per pattern of signs (which unknowns an edge raises and lowers): edges alike drop alike, mostly.
    const tried = new Set<string>(), sign = (l: Lin) => id(Object.keys(l).filter(x => x !== '1').sort().map(x => `${x}${Math.sign(l[x]!)}`))
    for (const l of left) {
      if (strict(l) || performance.now() > until || tried.has(sign(l)) || tried.size > 40) continue
      tried.add(sign(l))
      const w = lp([plus(l, {1: 1})], [...left, ...points], until, scale)
      if (w) sum = plus(sum, w) as Comp
    }
    if (!Object.keys(sum).length) break
    // The component divided by its entries' common divisor (each edge's drop stays a positive integer).
    const g = Object.values(sum).reduce((a, b) => gcd(a, Math.abs(b)), 0)
    if (g > 1) sum = Object.fromEntries(Object.entries(sum).map(([x, c]) => [x, c / g]))
    comps.push(sum)
    const kept = left.filter(l => !strict(l))
    if (kept.length === left.length) break
    left = kept
  }
  return {comps, left: left.length}
}
const gcd = (a: number, b: number): number => (b === 0 ? a : gcd(b, a % b))
const compE = (c: Comp, n: number, node: Node, name: Naming): E => linE(Object.fromEntries(node.vars.map((x, j) => [x, c[name(n, j)] ?? 0])), c[name(n, 'b')] ?? 0)
// Strongly connected components (Tarjan), each node's component's index.
function sccs(graph: number[][]): number[] {
  const index: number[] = [], low: number[] = [], on: boolean[] = [], stack: number[] = [], comp: number[] = []
  let next = 0, count = 0
  const visit = (u: number): void => {
    index[u] = low[u] = next++; stack.push(u); on[u] = true
    for (const w of graph[u]!) { if (index[w] === undefined) { visit(w); low[u] = Math.min(low[u]!, low[w]!) } else if (on[w]) low[u] = Math.min(low[u]!, index[w]!) }
    if (low[u] === index[u]) { let w: number; do { w = stack.pop()!; on[w] = false; comp[w] = count } while (w !== u); count++ }
  }
  for (let u = 0; u < graph.length; u++) if (index[u] === undefined) visit(u)
  return comp
}

// --- the search ---------------------------------------------------------------------------------------------------

type Built = {specs: NodeSpec[], ranks: E[][], uses: number} | {broken: {node: string, env: Env}} | {why: string}
function build(facts: Fact[], cx: Ctx, nodes: Node[], depth: number, big: number, until: number): Built {
  const inst = nodes.map(n => instancesFor(facts, cx, n, depth))
  const samples: Sampled[][] = []
  for (const n of nodes) { const s = samplesOf(cx, n, depth, big); if (s.broken) return {broken: {node: n.name, env: s.broken}}; samples.push(s.ok) }
  const cands = nodes.map((_, i) => usesFor(facts, cx, nodes, i, inst[i]!.reads))
  const edges: Edge[] = [], active = cands.map(cs => cs.map(() => false))
  for (const [i, cs] of cands.entries()) for (const [u, c] of cs.entries()) {
    const m = nodes[c.node]!, mr = readsOf(m.concl)
    for (const s of samples[i]!) {
      cx.fuel = 20_000
      const t: Env = {}
      let ok = true
      for (const x of m.vars) { const val = ev(cx, c.subst[x]!, s.env); if (val === undefined) { ok = false; break } t[x] = val }
      if (!ok || allTrue(cx, m.hyps, t) !== true) continue
      const called = mr.some(r => { const xs = argsOf(cx, r).map(a => ev(cx, a, t)); return xs.every(x => x !== undefined) && s.calls.has(`${r.map}(${xs.join(',')})`) })
      // A node at the very point it is (a read of f((x − 1) + 1) at f(x)) is no back-edge.
      if (!called || (c.node === i && m.vars.every(x => t[x] === s.env[x]))) continue
      active[i]![u] = true
      edges.push({from: i, to: c.node, s: s.env, t})
    }
  }
  // Components of the uses: a use into a component below drops by the first part of the rank, the component's height;
  // within a component, by the ranks the runs give (shared by its nodes first, then each its own).
  const graph = nodes.map((_, i) => [...new Set(cands[i]!.filter((_, u) => active[i]![u]).map(c => c.node))].filter(j => j !== i))
  const comp = sccs(graph), height: number[] = []
  const heightOf = (c: number): number => (height[c] ??= Math.max(0, ...nodes.flatMap((_, i) => (comp[i] === c ? graph[i]!.filter(j => comp[j] !== c).map(j => heightOf(comp[j]!) + 1) : []))))
  const parts = new Map<number, E[]>()
  for (const c of new Set(comp)) {
    const idx = nodes.flatMap((_, i) => (comp[i] === c ? [i] : [])), within = edges.filter(e => comp[e.from] === c && comp[e.to] === c)
    if (!within.length) { for (const i of idx) parts.set(i, []); continue }
    let best = {...lexRanks(idx, nodes, samples, within, shared, until), name: shared}
    if (best.left && idx.length > 1 && idx.length <= 4) { const o = lexRanks(idx, nodes, samples, within, own(nodes), until); if (o.left < best.left) best = {...o, name: own(nodes)} }
    if (!best.comps.length) return {why: 'no linear rank, in order, drops on any call the runs make'}
    for (const i of idx) parts.set(i, best.comps.map(cp => compE(cp, i, nodes[i]!, best.name)))
  }
  const width = Math.max(0, ...[...parts.values()].map(p => p.length)), tiers = graph.some(g => g.length)
  const ranks = nodes.map((_, i) => [...(tiers ? [k(heightOf(comp[i]!))] : []), ...parts.get(i)!, ...Array.from({length: width - parts.get(i)!.length}, () => k(0))])
  let uses = 0
  const specs: NodeSpec[] = nodes.map((n, i) => ({
    name: n.name, hyps: n.hyps, concl: n.concl, rank: ranks[i]!, insts: inst[i]!.insts,
    uses: cands[i]!.filter((_, u) => active[i]![u]).map(c => {
      uses++
      const m = nodes[c.node]!, s = vs(c.subst)
      return {node: c.node, subst: c.subst, guard: and(...m.hyps.map(h => substC(h, s)), lexLt(ranks[c.node]!.map(r => substE(r, s)), ranks[i]!))}
    }),
  }))
  return {specs, ranks, uses}
}

// Exact integer fits: Σ c·x + c0 = value at every sample (rows generated from the violated ones).
function fitExact(names: string[], points: {env: Env, value: number}[], until: number): {coef: Record<string, number>, c: number} | undefined {
  if (!points.length) return undefined
  const row = (p: {env: Env, value: number}, sign: number): Lin => { const l: Lin = {'b:c': sign, 1: -sign * p.value}; for (const x of names) if (p.env[x]) l[`c:${x}`] = sign * p.env[x]!; return l }
  const pool = points.flatMap(p => [row(p, 1), row(p, -1)])
  const w = lp(pool.slice(0, 2 * Math.min(points.length, names.length + 2)), pool, until, 1 + Math.max(...points.map(p => p.value)), [false])
  return w && {coef: Object.fromEntries(names.map(x => [x, w[`c:${x}`] ?? 0])), c: w['b:c'] ?? 0}
}

// A claim's constants abstracted: each read whose argument is a constant read at a fresh variable there, the
// conclusion (an equation with that read on one side) fitted exactly to the values over the claim's variables and the
// new ones. The companion is below the claim (its rank's first component), which uses it at the constants.
function abstracted(cx: Ctx, n: Node, i: number, big: number, until: number): Node | undefined {
  const c = n.concl
  if (c.op !== '=') return undefined
  for (const [read, other] of [[c.a, c.b], [c.b, c.a]] as const) {
    if (read.op !== 'get') continue
    const args = argsOf(cx, read)
    if (args.length < 2 || !args.some(a => a.op === 'const')) continue
    const fresh = args.map((a, j) => (a.op === 'const' ? `${read.map}${j}$${i}` : undefined))
    const general = get(read.map, argsKey(args.map((a, j) => (fresh[j] ? v(fresh[j]!) : a))))
    const names = [...n.vars, ...fresh.filter((x): x is string => !!x)].sort()
    if (!varsOf(other).every(x => n.vars.includes(x))) continue
    const points: {env: Env, value: number}[] = []
    for (const env of grid(names, boundFor(names.length, big))) {
      cx.fuel = 20_000
      if (allTrue(cx, n.hyps, env) !== true) continue
      const val = ev(cx, general, env)
      if (val !== undefined) points.push({env, value: val})
    }
    const fit = fitExact(names, points, until)
    if (!fit) continue
    return {name: `${n.name}, its constants as variables`, hyps: n.hyps, concl: eqC(general, linE(fit.coef, fit.c)), vars: names, level: n.level - 1, given: false}
  }
  return undefined
}
// Companions beside the claims, about each function of one argument their goals read: first by analogy (another
// function under a claim's own bound, f(x) ≤ 2x giving g(x) ≤ 2x), then every bound fitted to the values (for each
// slope from 0 to 3 the tightest constant, above and below, or the line when one fits exactly).
function beside(cx: Ctx, facts: Fact[], nodes: Node[], big: number, until: number, analog: boolean): Node[] {
  const out: Node[] = [], maps = new Set<string>()
  for (const n of nodes) for (const r of instancesFor(facts, cx, n, 1).reads) if ((cx.arity.get(r.map) ?? 1) === 1 && (cx.eqs.has(r.map) || cx.values[r.map])) maps.add(r.map)
  for (const map of [...maps].sort()) {
    const x = `x$${map}`, read = get(map, v(x)), pts: {env: Env, value: number}[] = []
    for (let q = 0; q <= boundFor(1, big); q++) { cx.fuel = 20_000; const val = callF(cx, map, [q]); if (val !== undefined) pts.push({env: {[x]: q}, value: val}) }
    if (pts.length < 4) continue
    const holds = (c: C) => pts.every(p => evC(cx, c, p.env) === true)
    const mk = (concl: C): Node => ({name: `${map}: ${showC(concl)}`, hyps: [], concl, vars: [x], level: nodes[0]!.level, given: false})
    if (analog) {
      for (const n of nodes) {
        const c = n.concl
        if ((c.op !== '<=' && c.op !== '=' && c.op !== '<') || n.vars.length !== 1 || n.hyps.length) continue
        const at = vs({[n.vars[0]!]: v(x)}), swap = (t: E): E => (t.op === 'get' && readsOf(c).length === 1 && id(t) === id(readsOf(c)[0]) ? read : substE(t, at))
        if (readsOf(c).length !== 1 || readsOf(c)[0]!.map === map || id(readsOf(c)[0]!.key) !== id(v(n.vars[0]!))) continue
        const cand: C = {op: c.op, a: swap(c.a), b: swap(c.b)}
        if (holds(cand)) out.push(mk(cand))
      }
      continue
    }
    const fit = fitExact([x], pts, until)
    if (fit) { out.push(mk(eqC(read, linE(fit.coef, fit.c)))); continue }
    for (const c of [0, 1, 2, 3]) {
      const d = Math.max(...pts.map(p => p.value - c * p.env[x]!)), lo = Math.min(...pts.map(p => p.value - c * p.env[x]!))
      // An upper constant only where it is one: the values reach it in the samples' last half.
      if (c > 0 || pts.slice(pts.length >> 1).some(p => p.value === d)) out.push(mk(d >= 0 ? le(read, linE({[x]: c}, d)) : le(add(read, k(-d)), linE({[x]: c}, 0))))
      if (c > 0) out.push(mk(lo >= 0 ? le(linE({[x]: c}, lo), read) : le(linE({[x]: c}, 0), add(read, k(-lo)))))
    }
  }
  return [...new Map(out.map(n => [n.name, n])).values()]
}

const trace = !!(globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env?.CYCLES_TRACE
export function findCycles(facts: Fact[], claims: Claim[], opts: CycleOptions = {}): CycleVerdict {
  const t0 = performance.now(), until = t0 + (opts.ms ?? 10_000), depth = opts.depth ?? 1
  const {eqs, arity} = equations(facts)
  const cx: Ctx = {eqs, arity, values: opts.values ?? {}, memo: new Map(), fuel: 20_000, depth: 0}
  const big = Math.max(0, ...constsOf([facts.map(f => f.holds), claims]).filter(c => c <= 1000))
  const given: Node[] = claims.map(c => ({name: c.name, hyps: c.hyps ?? [], concl: c.concl, vars: varsOf([c.hyps ?? [], c.concl]), level: 1, given: !opts.houdini}))
  let last: CycleVerdict = {proven: false, checked: false, why: 'nothing tried'}
  // One set of nodes, Houdini over those that may be dropped: each failing one dropped and the rest proven again.
  const attempt = (start: Node[], depth: number): CycleVerdict => {
    let nodes = start
    for (let round = 0; round <= start.length && nodes.length && performance.now() < until; round++) {
      const b = withDeadline(until, () => build(facts, cx, nodes, depth, big, until))
      if ('broken' in b) {
        const at = nodes.find(n => n.name === b.broken.node)!
        if (at.given) return {proven: false, checked: false, goal: at.name, stuck: 'sat', witness: b.broken.env, why: 'the facts, run, break it'}
        nodes = nodes.filter(n => n !== at); continue
      }
      if ('why' in b) return {proven: false, checked: false, why: b.why}
      if (trace) for (const sp of b.specs) console.error(`[cycles] ${sp.name}: rank (${sp.rank.map(showE).join(', ')}), ${sp.insts.length} instances, uses ${sp.uses.map(u => `${u.node}@{${Object.entries(u.subst).map(([x, t]) => `${x} := ${showE(t)}`).join(', ')}}`).join(' ')}`)
      const out = withDeadline(until, () => proveCyclic(facts, b.specs))
      if (trace) console.error(`[cycles] ${out.proven ? 'proven' : `${out.node}: ${out.goal} ${out.stuck}`} at ${Math.round(performance.now() - t0)} ms`)
      if (out.proven) {
        const found: CycleFound = {ranks: Object.fromEntries(nodes.map((n, i) => [n.name, `(${b.ranks[i]!.map(showE).join(', ')})`])), companions: nodes.filter(n => !n.given && !claims.some(c => c.name === n.name)).map(n => `${showC(n.concl)}${n.hyps.length ? ` where ${showC(and(...n.hyps))}` : ''}`), uses: b.uses}
        return {proven: true, checked: out.checked, proof: out.proof, specs: b.specs, kept: nodes.map(n => n.name), found, ...(out.why ? {why: out.why} : {})}
      }
      const at = nodes.find(n => n.name === out.node)
      if (!at || at.given) return {proven: false, checked: false, goal: out.goal, stuck: out.stuck}
      nodes = nodes.filter(n => n !== at)
    }
    return {proven: false, checked: false, why: performance.now() >= until ? 'out of time' : 'every candidate dropped'}
  }
  // The claims alone, with the facts at the terms they read and then at those the facts read; their constants as
  // variables; companions beside them by analogy, then every bound.
  const tries: [number, () => Node[]][] = [
    [depth, () => given], [depth + 1, () => given],
    ...(opts.generalize === false ? [] : [
      [depth, () => given.flatMap((n, i) => { const g = abstracted(cx, n, i, big, until); return g ? [n, g] : [n] })],
      [depth + 1, () => [...given, ...beside(cx, facts, given, big, until, true)]],
      [depth + 1, () => [...given, ...beside(cx, facts, given, big, until, false)]],
    ] as [number, () => Node[]][]),
  ]
  const tried = new Set<string>()
  for (const [d, t] of tries) {
    if (performance.now() >= until) break
    const nodes = t()
    if (tried.has(id([d, nodes.map(n => n.name)]))) continue
    tried.add(id([d, nodes.map(n => n.name)]))
    const out = attempt(nodes, d)
    if (out.proven || out.stuck === 'sat' && out.why) return out
    last = out
  }
  return last
}

// --- loops ----------------------------------------------------------------------------------------------------------

export type RankVerdict = {proven: boolean, checked: boolean, rank?: E[], laws?: Law[], found?: {rank: string, laws: string[]}, trees?: Record<string, Tree>, goal?: string, stuck?: string, witness?: Record<string, number>, why?: string}
const seeded = (seed: number) => { let x = seed; return (n: number) => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * n) } }
const goalsProven = (goals: Goal[]): {trees: Record<string, Tree>} | {goal: string, stuck: string, witness?: Record<string, number>} => {
  const trees: Record<string, Tree> = {}
  for (const g of goals) {
    const out = grow(g)
    if (!('tree' in out) || !check(g, out.tree)) return {goal: g.name, stuck: 'tree' in out ? 'the kernel refused the tree' : out.stuck, ...('witness' in out && out.witness ? {witness: out.witness} : {})}
    trees[g.name] = out.tree
  }
  return {trees}
}
// A loop's rank from its runs: random params (the precondition's), turns with random inputs (the assumption's), each
// turn that stays in the loop an edge; then the kernel's halting goals, with invariants inferLaws finds for them where
// the rank needs one.
export function findRank(l: Loop, laws: Law[] = [], opts: {ms?: number} = {}): RankVerdict {
  const t0 = performance.now(), until = t0 + (opts.ms ?? 10_000), rand = seeded(23)
  const cx: Ctx = {eqs: new Map(), arity: new Map(), values: {}, memo: new Map(), fuel: Infinity, depth: 0}
  const state = Object.keys(l.state), names = [...state, ...l.params].sort()
  const node: Node = {name: l.name, hyps: [], concl: yes, vars: names, level: 0, given: true}
  const points = new Map<string, Env>(), edges = new Map<string, Edge>()
  for (const bound of [2, 4, 8, 16, 32]) for (let trial = 0; trial < 40 && performance.now() < t0 + 1000; trial++) {
    const ps = Object.fromEntries(l.params.map(p => [p, rand(bound + 1)]))
    if (l.pre && evC(cx, l.pre, ps) !== true) continue
    let st: Env = {}
    for (const s of state) { const x = ev(cx, l.state[s]!, ps); if (x === undefined) break; st[s] = x }
    for (let turn = 0; turn < 300; turn++) {
      const here = {...ps, ...st}
      if (evC(cx, l.while, here) !== true) break
      points.set(id(here), here)
      let inp: Env | undefined
      for (let tries = 0; tries < 20 && !inp; tries++) { const i = Object.fromEntries(l.inputs.map(x => [x, rand(bound + 1)])); if (!l.assume || evC(cx, l.assume, {...here, ...i}) === true) inp = i }
      if (!inp) break
      const next: Env = {...st}
      for (const [s, e] of Object.entries(l.body)) { const x = ev(cx, e, {...here, ...inp}); if (x !== undefined) next[s] = x }
      const there = {...ps, ...next}
      if (evC(cx, l.while, there) === true) edges.set(id([here, there]), {from: 0, to: 0, s: here, t: there})
      st = next
    }
  }
  const samples: Sampled[][] = [[...points.values()].map(env => ({env, calls: new Set()}))]
  const {comps} = lexRanks([0], [node], samples, [...edges.values()], shared, until)
  if (!comps.length) return {proven: false, checked: false, why: `no linear rank, in order, drops on every turn of ${edges.size} sampled`}
  const rank = comps.map(c => compE(c, 0, node, shared)), text = `(${rank.map(showE).join(', ')})`
  const first = withDeadline(until, () => goalsProven(loopObligations(l, laws, rank)))
  if ('trees' in first) return {proven: true, checked: true, rank, laws: [], found: {rank: text, laws: []}, trees: first.trees}
  // Invariants the rank needs: the descent as the loop's step laws, inferLaws's candidates chosen by its counterexamples.
  const m = loopMachine(l), {stay, cover, helps} = livenessParts(m, loopLiveness(l, rank))
  const ms = until - performance.now()
  if (ms > 300) {
    const inf = inferLaws(m, laws, [stay, cover, ...helps] as StepLaw[], {ms})
    const kept = inf.found.filter(f => !f.law.forall && !f.law.keys?.length), more = kept.map(f => f.law)
    if (inf.proven && more.length) {
      const all = [...laws, ...more], again = withDeadline(until + 5000, () => goalsProven(loopObligations(l, all, rank)))
      if ('trees' in again) return {proven: true, checked: true, rank, laws: more, found: {rank: text, laws: kept.map(f => f.text)}, trees: again.trees}
    }
  }
  return {proven: false, checked: false, rank, found: {rank: text, laws: []}, goal: first.goal, stuck: first.stuck, ...(first.witness ? {witness: first.witness} : {}), why: `rank ${text} from the runs; no invariant found that it needs`}
}

// --- functions a rule reads -----------------------------------------------------------------------------------------

// Lemmas about the functions a machine reads (those with facts and JavaScript, one argument): from the values, each a
// constant on a region below or above a threshold (a constant of the facts or the rule, ±1), a line, or bounds; proven
// from the facts as cyclic claims (Houdini: one not proven dropped), then the laws with those kept as facts, each
// dropped in turn where the laws don't need it.
export type LemmaFound = {law: Law, text: string}
export function cycleLemmas(m: Machine, laws: Law[], stepLaws: StepLaw[] = [], opts: {ms?: number} = {}): {proven: boolean, checked: boolean, machine?: Machine, found: LemmaFound[], why?: string} {
  const until = performance.now() + (opts.ms ?? 10_000)
  const fns = Object.entries(m.fns ?? {}).filter(([, f]) => !f.recur && (f.arity ?? 1) === 1)
  if (!fns.length || !m.facts?.length) return {proven: false, checked: false, found: [], why: 'no function known by its facts'}
  const facts: Fact[] = m.facts.map(f => ({name: f.name, keys: [...(f.forall ? [f.forall] : []), ...(f.keys ?? [])], holds: f.holds}))
  const values: Record<string, (x: number) => number> = {}
  for (const [name, f] of fns) values[name] = (q: number) => fnValue(f, q)
  const ts = [...new Set(constsOf([m, laws, stepLaws]).filter(c => c >= 0 && c <= 1000).flatMap(c => [c - 1, c, c + 1]).filter(c => c >= 0))].sort((a, b) => a - b)
  const big = Math.max(24, ...ts), x = 'k$', claims: Claim[] = []
  for (const [name] of fns) {
    const f = values[name]
    if (!f) continue
    const vals: number[] = []
    for (let q = 0; q <= 2 * big + 20; q++) { let y: number; try { y = f(q) } catch { break } if (!Number.isSafeInteger(y) || y < 0) break; vals.push(y) }
    if (vals.length < 4) continue
    const read = get(name, v(x)), pts = vals.map((value, q) => ({env: {[x]: q}, value}))
    const line = fitExact([x], pts, until)
    if (line) claims.push({name: `${name}(k) = ${showE(linE({k: line.coef[x]!}, line.c))}`, concl: eqC(read, linE(line.coef, line.c))})
    for (const t of ts) {
      if (t >= vals.length) continue
      const below = vals.slice(0, t + 1), above = pts.slice(t)
      if (below.every(y => y === below[0])) claims.push({name: `${name}(k) = ${below[0]} for k ≤ ${t}`, hyps: [le(v(x), k(t))], concl: eqC(read, k(below[0]!))})
      const fit = above.length >= 4 && fitExact([x], above, until)
      if (fit && (fit.coef[x] !== line?.coef[x] || fit.c !== line?.c)) claims.push({name: `${name}(k) = ${showE(linE({k: fit.coef[x]!}, fit.c))} for k ≥ ${t}`, hyps: [le(k(t), v(x))], concl: eqC(read, linE(fit.coef, fit.c))})
    }
    const top = Math.max(...vals)
    if (vals.slice(vals.length >> 1).includes(top)) claims.push({name: `${name}(k) ≤ ${top}`, concl: le(read, k(top))})
  }
  const unique = [...new Map(claims.map(c => [c.name, c])).values()]
  if (!unique.length) return {proven: false, checked: false, found: [], why: 'no lemma fits the values'}
  const out = findCycles(facts, unique, {ms: Math.max(0, until - performance.now()) * 0.6, values, houdini: true, generalize: false})
  if (!out.proven || !out.checked || !out.kept?.length) return {proven: false, checked: false, found: [], why: out.why ?? 'no lemma proven'}
  const asLaw = (c: Claim): LemmaFound => ({law: {name: c.name, forall: x, holds: c.hyps?.length ? {op: 'or', xs: [{op: 'not', x: and(...c.hyps)}, c.concl]} : c.concl}, text: c.name})
  let found = unique.filter(c => out.kept!.includes(c.name)).map(asLaw)
  const proveWith = (fs: LemmaFound[]) => {
    const mm: Machine = {...m, facts: [...m.facts!, ...fs.map(f => f.law)]}
    const r = withDeadline(until, () => (stepLaws.length ? proveStepLaws(mm, laws, stepLaws) : proveLaws(mm, laws)))
    return {ok: r.proven && r.checked, machine: mm}
  }
  let best = proveWith(found)
  if (!best.ok) return {proven: false, checked: false, found: [], why: `lemmas proven (${found.map(f => f.text).join('; ')}), the laws not with them`}
  for (const f of [...found]) {
    if (performance.now() >= until) break
    const rest = found.filter(g => g !== f), again = proveWith(rest)
    if (again.ok) (found = rest, best = again)
  }
  return {proven: true, checked: true, machine: best.machine, found}
}
