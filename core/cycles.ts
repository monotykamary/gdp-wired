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
import type {C, E, Law, Machine, Request, State} from './machine.ts'
import {compileFunction, evalC as evalMC, evalE as evalME, fnValue, interpret, pairedArgs} from './machine.ts'
import type {Goal, Liveness, Loop, Subst, Tree} from '../kernel/kernel.ts'
import {check, livenessHelpful, livenessParts, loopLiveness, loopMachine, loopObligations, substC, substE} from '../kernel/kernel.ts'
import {type Cyclic, type Fact, checkCyclic, factsAvoid, lexLt} from '../kernel/cyclic.ts'
import {type NodeSpec, proveCyclic} from './cyclic.ts'
import {type Lin, refuteFast, solve, work} from './solver.ts'
import {clock, grow, proveLaws, proveLiveness, proveStepLaws, withDeadline} from '../kernel/prove.ts'
import {inferLaws} from './infer.ts'
import {type Generators, type Relation, generators, houdini, relationOf} from './relation.ts'
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
    case 'prod': { const f = (t: E) => (t.op === 'var' || t.op === 'const' || t.op === 'get' ? showE(t) : `(${showE(t)})`); return `${f(e.a)}·${f(e.b)}` }
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
function lp(must: Lin[], pool: Lin[], until: number, scale = 1, signs: boolean[] = [true, false], whole = false): Record<string, number> | undefined {
  const unknowns = [...new Set([...must, ...pool].flatMap(l => Object.keys(l)).filter(x => x !== '1'))]
  const fit = unknowns.some(x => x.startsWith('c:')), bounds = fit ? [1, 2, 4, 16, 128] : [1, 2, 4]
  const stage = (natural: boolean, bound: number, wide: boolean): Record<string, number> | undefined => {
    const rows = [...must]
    for (const x of unknowns) {
      const b = x.startsWith('b:') ? (wide ? bound * scale : bound) : bound
      rows.push({[x]: 1, 1: -b}, natural ? {[x]: -1} : {[x]: -1, 1: -b})
    }
    for (let round = 0; round < 40 && clock() < until; round++) {
      const out = solve(rows.map(lin => ({lin, label: ''})), 4000)
      if (out.kind !== 'sat') break
      const bad = pool.filter(l => valueAt(l, out.witness) > 0).sort((a, b) => valueAt(b, out.witness) - valueAt(a, out.witness))
      if (!bad.length) return out.witness
      rows.push(...bad.slice(0, 6))
    }
    return undefined
  }
  // The widest box first: where it has no solution, none of the smaller has. Past it, a rank's rows (homogeneous in the
  // unknowns, the drop's constant aside) are solved exactly over the rationals, the solution scaled to whole numbers.
  // (a path's generators, `whole`: the LP over the rationals alone, its least Σ|u| as small a rank as the boxes find)
  if (whole && !fit) return exactLp(must, pool, until, whole)
  if (!stage(signs.at(-1)!, bounds.at(-1)!, true)) return fit ? undefined : exactLp(must, pool, until, whole)
  for (const natural of signs) for (const bound of bounds) for (const wide of [false, true]) { const w = stage(natural, bound, wide); if (w) return w }
  return undefined
}

// --- an exact LP ----------------------------------------------------------------------------------------------------

// Rationals over BigInt, always reduced, the denominator positive.
type Q = {n: bigint, d: bigint}
const bgcd = (a: bigint, b: bigint): bigint => { if (a < 0n) a = -a; if (b < 0n) b = -b; while (b) [a, b] = [b, a % b]; return a }
const q = (n: bigint, d = 1n): Q => { if (d < 0n) (n = -n, d = -d); const g = bgcd(n, d) || 1n; return g === 1n ? {n, d} : {n: n / g, d: d / g} }
const Q0 = q(0n)
const qadd = (a: Q, b: Q): Q => (a.d === b.d ? q(a.n + b.n, a.d) : q(a.n * b.d + b.n * a.d, a.d * b.d))
const qsub = (a: Q, b: Q): Q => qadd(a, {n: -b.n, d: b.d})
// The primal simplex on a tableau whose basis is feasible: minimize cost·y over T·y = rhs (the last column), y >= 0,
// Bland's rule (the smallest column that improves, the smallest basis index among ties), only `open` columns entering.
// Fraction-free: each row integers over one positive denominator (its entries n[j] / d), the reduced costs a row of
// the same kind, each row divided by its entries' common divisor after a pivot (no divisor per entry).
type XRow = {n: bigint[], d: bigint}
const reduce = (r: XRow): XRow => { let g = r.d; for (const x of r.n) { if (g === 1n) break; if (x) g = bgcd(g, x) } return g > 1n ? {n: r.n.map(x => x / g), d: r.d / g} : r }
// row r minus f times the pivot row (its pivot entry pv > 0 at column e): r's entry at e becomes 0
const eliminate = (r: XRow, piv: XRow, e: number): XRow => {
  const f = r.n[e]!, pv = piv.n[e]!
  if (!f) return r
  return reduce({n: r.n.map((x, j) => x * pv - f * piv.n[j]!), d: r.d * pv})
}
function pivotOn(T: XRow[], z: XRow | undefined, leave: number, e: number): XRow | undefined {
  let L = T[leave]!
  if (L.n[e]! < 0n) L = {n: L.n.map(x => -x), d: L.d}
  T[leave] = reduce({n: L.n, d: L.n[e]!})
  const piv = {n: L.n, d: 1n}
  for (let r = 0; r < T.length; r++) if (r !== leave && T[r]!.n[e]) T[r] = eliminate(T[r]!, piv, e)
  return z && eliminate(z, piv, e)
}
function simplex(T: XRow[], basis: number[], cost: bigint[], open: (j: number) => boolean, until: number): boolean {
  const cols = cost.length
  let z: XRow = {n: [...cost, 0n], d: 1n}
  for (const [i, b] of basis.entries()) if (cost[b]) z = eliminate(z, {n: T[i]!.n, d: 1n}, b)
  for (let it = 0; it < 5000; it++) {
    // (each pivot counted as work, as the solver's rows are: a counted search's clock runs while it solves)
    work.n += 1 + ((T.length * cols) >> 6)
    if (clock() > until) return false
    let enter = -1
    for (let j = 0; j < cols && enter < 0; j++) if (z.n[j]! < 0n && open(j)) enter = j
    if (enter < 0) return true
    let leave = -1
    for (const [i, row] of T.entries()) {
      const a = row.n[enter]!
      if (a <= 0n) continue
      if (leave < 0) { leave = i; continue }
      // row's rhs / a against the best's (the denominators cancel)
      const L = T[leave]!, lhs = row.n[cols]! * L.n[enter]!, rhs = L.n[cols]! * a
      if (lhs < rhs || (lhs === rhs && basis[i]! < basis[leave]!)) leave = i
    }
    if (leave < 0) return false // unbounded: not for an objective bounded below
    z = pivotOn(T, z, leave, enter)!
    basis[leave] = enter
  }
  return false
}
// The rows (lin <= 0) over free unknowns, solved exactly: Σ|u| least (each u as p − q, p, q >= 0), two phases. The
// rational solution scaled by its denominators' least common multiple and divided by its numerators' common divisor;
// kept only if every row holds of it exactly (a row with a positive constant, a drop of at least 1, holds of any
// multiple at least 1 of a solution; one with a negative constant may not).
// The same LP in floating point first (the floats only pick the point): each coefficient read back as the nearest
// fraction of small denominator, scaled to whole numbers and kept only where every row holds of it exactly; else the
// exact simplex below (where the floats find no point, none is looked for again). Over hundreds of rows the floats are what makes the search affordable (the exact tableau's
// reductions dominated it).
const nearFraction = (x: number, most = 10_000): [number, number] => {
  // continued fractions: the last convergent within the denominator bound
  let [h0, h1, k0, k1, y] = [0, 1, 1, 0, x]
  for (let i = 0; i < 40; i++) {
    const a = Math.floor(y), h2 = a * h1 + h0, k2 = a * k1 + k0
    if (k2 > most) break
    ;[h0, h1, k0, k1] = [h1, h2, k1, k2]
    if (Math.abs(x - h1 / k1) < 1e-12 || Math.abs(y - a) < 1e-12) break
    y = 1 / (y - a)
  }
  return [h1, k1]
}
const lpTrace = !!(globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env?.LP_TRACE
function floatSolve(rows: Lin[], until: number, equil = true, again = true): Record<string, number> | 'infeasible' | undefined {
  const xs = [...new Set(rows.flatMap(l => Object.keys(l)).filter(x => x !== '1'))].sort(), n = xs.length, m = rows.length
  const cols = 2 * n + 2 * m, T: Float64Array[] = [], basis: number[] = [], eps = 1e-9
  for (const [i, l] of rows.entries()) {
    let rhs = -(l['1'] ?? 0)
    const sign = rhs < 0 ? -1 : 1
    rhs *= sign
    // (each row scaled to its largest entry 1: a vertex's coordinates reach 2^31, the drop's constant is 1)
    const row = new Float64Array(cols + 1), big = (equil && Math.max(Math.abs(rhs), ...xs.map(x => Math.abs(l[x] ?? 0)))) || 1
    for (const [j, x] of xs.entries()) { const c = sign * (l[x] ?? 0) / big; if (c) (row[j] = c, row[n + j] = -c) }
    row[2 * n + i] = sign
    if (sign < 0) { row[2 * n + m + i] = 1; basis.push(2 * n + m + i) } else basis.push(2 * n + i)
    row[cols] = rhs / big
    T.push(row)
  }
  const art = (j: number) => j >= 2 * n + m
  // minimize cost·y, the reduced costs kept as a row: the most negative enters (Dantzig's rule), Bland's after a run of
  // degenerate pivots (no cycling)
  const run = (cost: (j: number) => number, open: (j: number) => boolean): boolean => {
    const z = new Float64Array(cols + 1)
    for (let j = 0; j < cols; j++) z[j] = cost(j)
    for (const [i, b] of basis.entries()) { const c = cost(b); if (c) for (let j = 0; j <= cols; j++) z[j]! -= c * T[i]![j]! }
    let stalled = 0
    for (let it = 0; it < 10 * (m + cols); it++) {
      // (each pivot counted as work, an eighth of the exact simplex's: a counted search's clock runs while it solves)
      work.n += 1 + ((T.length * cols) >> 9)
      if ((it & 63) === 0 && clock() > until) return false
      let enter = -1
      if (stalled < 50) { let low = -eps; for (let j = 0; j < cols; j++) if (z[j]! < low && open(j)) { low = z[j]!; enter = j } }
      else for (let j = 0; j < cols; j++) if (z[j]! < -eps && open(j)) { enter = j; break }
      if (enter < 0) return true
      let leave = -1, best = Infinity
      for (let r = 0; r < T.length; r++) {
        const a = T[r]![enter]!
        if (a > eps) { const ratio = T[r]![cols]! / a; if (ratio < best - eps || (Math.abs(ratio - best) <= eps && basis[r]! < basis[leave]!)) { best = ratio; leave = r } }
      }
      if (leave < 0) return false
      stalled = best <= eps ? stalled + 1 : 0
      const p = T[leave]!, pv = p[enter]!
      for (let j = 0; j <= cols; j++) p[j]! /= pv
      for (let r = 0; r < T.length; r++) if (r !== leave) { const f = T[r]![enter]!; if (f !== 0) { const row = T[r]!; for (let j = 0; j <= cols; j++) row[j]! -= f * p[j]! } }
      const f = z[enter]!
      if (f !== 0) for (let j = 0; j <= cols; j++) z[j]! -= f * p[j]!
      basis[leave] = enter
    }
    return false
  }
  if (!run(j => (art(j) ? 1 : 0), () => true)) return undefined
  // (no point: the artificials' least sum clearly above zero, which the exact simplex is not asked again)
  if (T.some((row, i) => art(basis[i]!) && row[cols]! > 1e-6)) return 'infeasible'
  if (T.some((row, i) => art(basis[i]!) && row[cols]! > 1e-9)) return undefined
  for (let i = T.length - 1; i >= 0; i--) {
    if (!art(basis[i]!)) continue
    let j = -1
    for (let c = 0; c < 2 * n + m; c++) if (Math.abs(T[i]![c]!) > eps) { j = c; break }
    if (j < 0) { T.splice(i, 1); basis.splice(i, 1); continue }
    const p = T[i]!, pv = p[j]!
    for (let c = 0; c <= cols; c++) p[c]! /= pv
    for (let r = 0; r < T.length; r++) if (r !== i) { const f = T[r]![j]!; if (f !== 0) { const row = T[r]!; for (let c = 0; c <= cols; c++) row[c]! -= f * p[c]! } }
    basis[i] = j
  }
  if (!run(j => (j < 2 * n ? 1 : 0), j => !art(j))) return undefined
  const val = (j: number) => { const i = basis.indexOf(j); return i < 0 ? 0 : T[i]![cols]! }
  const u = xs.map((_, j) => val(j) - val(n + j))
  // read back: tiny values kept or as 0 (a coefficient 1/2^31 against a bound of the int range is one, or the floats'
  // error), each the nearest fraction, the whole scaled to
  // integers, with and without their common divisor; the first that every row holds of exactly
  for (const [snap, most] of [[0, 10_000], [1e-7, 10_000], [1e-7, 1_000_000], [0, 2 ** 32]] as const) {
    const fr = u.map(x => (Math.abs(x) <= snap ? [0, 1] : nearFraction(Math.abs(x), most)) as [number, number])
    let lcm = 1n
    for (const [, d] of fr) lcm = lcm / bgcd(lcm, BigInt(d)) * BigInt(d)
    const ints = u.map((x, j) => BigInt(Math.sign(x) * fr[j]![0]) * (lcm / BigInt(fr[j]![1]))), g = ints.reduce((a, b) => bgcd(a, b), 0n) || 1n
    for (const div of g > 1n ? [g, 1n] : [1n]) {
      const w: Record<string, number> = {}
      let safe = true
      for (const [j, x] of xs.entries()) { const c = ints[j]! / div; if (c > BigInt(Number.MAX_SAFE_INTEGER) || -c > BigInt(Number.MAX_SAFE_INTEGER)) safe = false; else if (c) w[x] = Number(c) }
      if (safe && holdsExactly(rows, w)) return w
    }
  }
  // Else the tiny values as 0 exactly, the LP solved again over the rest: within the tolerance a coefficient of 2^−31
  // against a vertex at 2^31 is a drop of 1 the exact rows don't allow.
  const zero = new Set(xs.filter((_, j) => u[j] !== 0 && Math.abs(u[j]!) <= 1e-7))
  if (!again || !zero.size) return undefined
  const fewer = floatSolve(rows.map(r => Object.fromEntries(Object.entries(r).filter(([x]) => !zero.has(x)))), until, equil, false)
  return fewer && fewer !== 'infeasible' && holdsExactly(rows, fewer) ? fewer : undefined
}
// Every row (lin <= 0) at w, in BigInt: products past 2^53 read exactly.
const holdsExactly = (rows: Lin[], w: Record<string, number>): boolean => rows.every(l => {
  let s = 0n
  for (const x in l) s += BigInt(l[x]!) * (x === '1' ? 1n : BigInt(w[x] ?? 0))
  return s <= 0n
})
function exactSolve(rows: Lin[], until: number): Record<string, number> | undefined {
  // (the rows scaled to their largest entry first, then as they are: either way the tolerance may hide what a row of a
  // vertex at 2^31 says, a coefficient 2^−31 read as 0 or 0 as 2^−31; infeasible where both say so)
  const t0 = performance.now(), first = floatSolve(rows, until), second = first && first !== 'infeasible' ? first : floatSolve(rows, until, false)
  const fast = second && second !== 'infeasible' ? second : first === 'infeasible' && second === 'infeasible' ? 'infeasible' : undefined
  if (lpTrace) console.error(`[lp] ${rows.length} rows ${new Set(rows.flatMap(l => Object.keys(l))).size} unknowns: ${fast === undefined ? 'undefined' : fast === 'infeasible' ? 'infeasible' : 'found'} ${Math.round(performance.now() - t0)} ms`)
  if (fast === 'infeasible') return undefined
  if (fast) return fast
  // (no point read back, or the two disagree: a refutation over the rationals, Farkas' rows picked by the floats and
  // checked by elimination on them, which the exact simplex below would take far longer to give; else the exact simplex)
  if (refuteFast(rows.map(lin => ({lin, label: ''})), 2_000, false)?.kind === 'refuted') return undefined
  const xs = [...new Set(rows.flatMap(l => Object.keys(l)).filter(x => x !== '1'))].sort(), n = xs.length, m = rows.length
  // Columns: p (n), q (n), a slack per row (m), an artificial per row (m); the right-hand side last.
  const cols = 2 * n + 2 * m, T: XRow[] = [], basis: number[] = []
  for (const [i, l] of rows.entries()) {
    let rhs = -(l['1'] ?? 0)
    const sign = rhs < 0 ? -1 : 1
    rhs *= sign
    const row: bigint[] = Array.from({length: cols + 1}, () => 0n)
    for (const [j, x] of xs.entries()) { const c = sign * (l[x] ?? 0); if (c) (row[j] = BigInt(c), row[n + j] = BigInt(-c)) }
    row[2 * n + i] = BigInt(sign)
    if (sign < 0) { row[2 * n + m + i] = 1n; basis.push(2 * n + m + i) } else basis.push(2 * n + i)
    row[cols] = BigInt(rhs)
    T.push({n: row, d: 1n})
  }
  const art = (j: number) => j >= 2 * n + m
  const phase1 = Array.from({length: cols}, (_, j) => (art(j) ? 1n : 0n))
  if (!simplex(T, basis, phase1, () => true, until)) return undefined
  if (T.some((row, i) => art(basis[i]!) && row.n[cols])) return undefined // infeasible
  // An artificial left in the basis at zero: pivoted out on any other column, or its row dropped (redundant).
  for (let i = T.length - 1; i >= 0; i--) {
    if (!art(basis[i]!)) continue
    const j = T[i]!.n.findIndex((x, c) => c < 2 * n + m && x !== 0n)
    if (j < 0) { T.splice(i, 1); basis.splice(i, 1); continue }
    pivotOn(T, undefined, i, j)
    basis[i] = j
  }
  const phase2 = Array.from({length: cols}, (_, j) => (j < 2 * n ? 1n : 0n))
  if (!simplex(T, basis, phase2, j => !art(j), until)) return undefined
  const val = (j: number): Q => { const i = basis.indexOf(j); return i < 0 ? Q0 : q(T[i]!.n[cols]!, T[i]!.d) }
  const u = xs.map((_, j) => qsub(val(j), val(n + j)))
  let lcm = 1n
  for (const r of u) lcm = lcm / bgcd(lcm, r.d) * r.d
  const ints = u.map(r => r.n * (lcm / r.d)), g = ints.reduce((a, b) => bgcd(a, b), 0n) || 1n
  const w: Record<string, number> = {}
  for (const [j, x] of xs.entries()) { const c = Number(ints[j]! / g); if (!Number.isSafeInteger(c)) return undefined; if (c) w[x] = c }
  return holdsExactly(rows, w) ? w : undefined
}
// exactSolve over `must` and the pool's rows, the pool's added as they are violated (the most violated first). The
// solution is found on the smaller half of the runs (each row's size its largest coefficient, a sample's value or a
// turn's change) and kept only where it holds of all of them: a coefficient the runs' size forces (32·x + y where x
// reaches 33, a reset y := x − 1 in the runs) grows with the runs, and is refused, where one a turn's change forces
// (11·x + 2·y, six tokens for a coin and a coin for five) is the same on both.
// `whole`: rows that are facts, not samples (a path's generators, core/relation.ts), solved over all of them.
function exactLp(must: Lin[], pool: Lin[], until: number, whole = false): Record<string, number> | undefined {
  const size = (l: Lin) => { let m = 0; for (const x in l) if (x !== '1') m = Math.max(m, Math.abs(l[x]!)); return m }
  const sizes = pool.map(size), half = sizes.reduce((a, b) => Math.max(a, b), 0) / 2, small = whole ? pool : pool.filter((_, i) => sizes[i]! <= half), rows = [...must]
  for (let round = 0; round < 40 && clock() < until; round++) {
    const w = exactSolve(rows, until)
    if (!w) return undefined
    // The twelve most violated, in one pass.
    const bad: [number, Lin][] = []
    for (const l of small) {
      const x = valueAt(l, w)
      if (x <= 0 || (bad.length === 12 && x <= bad[11]![0])) continue
      bad.push([x, l]); bad.sort((p, q) => q[0] - p[0]); if (bad.length > 12) bad.pop()
    }
    if (!bad.length) return pool.every(l => valueAt(l, w) <= 0) ? w : undefined
    rows.push(...bad.map(b => b[1]))
  }
  return undefined
}
type Comp = Record<string, number>
// Lexicographic ranks over the edges (each from a node at a sample to a node at its arguments), every component >= 0
// at every sample: Bradley–Manna–Sipma's successive elimination, each component the sum of one solution per edge it can
// make drop. An edge no component makes drop is left (its use's guard keeps it where the rank drops, if anywhere).
// `onEdges`: each component a natural only where an edge compares it (at its ends), not at every sample: a rank the
// kernel reads truncated (n·n − i, 0 past the square, where no call is made). `weak`: edges the rank must not raise but
// need not lower (a liveness's steps other than its helpful requests'), each dropped once a component lowers it.
function lexRanks(idx: number[], nodes: Node[], samples: Sampled[][], edges: Edge[], name: Naming, until: number, onEdges = false, weak: Edge[] = []): {comps: Comp[], left: number} {
  const ends = onEdges ? edges.flatMap(e => [[e.from, e.s], [e.to, e.t]] as [number, Env][]) : idx.flatMap(n => samples[n]!.map(s => [n, s.env] as [number, Env]))
  const points = [...new Map(ends.map(([n, env]) => { const l = rankRow(n, nodes, env, name, -1); return [id(l), l] as const })).values()]
  const delta = (e: Edge): Lin => plus(rankRow(e.to, nodes, e.t, name), rankRow(e.from, nodes, e.s, name, -1))
  // (a loop, not a spread: tens of thousands of samples' values overflow the stack as arguments)
  let scale = 1
  for (const n of idx) for (const s of samples[n]!) for (const x of Object.values(s.env)) if (x + 1 > scale) scale = x + 1
  let left = [...new Map(edges.map(e => { const l = delta(e); return [id(l), l] as const })).values()]
  let keep = [...new Map(weak.map(e => { const l = delta(e); return [id(l), l] as const })).values()].filter(l => !left.some(x => id(x) === id(l)))
  const comps: Comp[] = []
  while (left.length && comps.length < 4 && clock() < until) {
    let sum: Comp = {}
    const strict = (l: Lin) => valueAt(l, sum) < 0
    // One try per pattern of signs (which unknowns an edge raises and lowers): edges alike drop alike, mostly.
    const tried = new Set<string>(), sign = (l: Lin) => id(Object.keys(l).filter(x => x !== '1').sort().map(x => `${x}${Math.sign(l[x]!)}`))
    for (const l of left) {
      if (strict(l) || clock() > until || tried.has(sign(l)) || tried.size > 40) continue
      tried.add(sign(l))
      const w = lp([plus(l, {1: 1})], [...left, ...keep, ...points], until, scale)
      if (w) sum = plus(sum, w) as Comp
    }
    if (!Object.keys(sum).length) break
    // The component divided by its entries' common divisor (each edge's drop stays a positive integer).
    const g = Object.values(sum).reduce((a, b) => gcd(a, Math.abs(b)), 0)
    if (g > 1) sum = Object.fromEntries(Object.entries(sum).map(([x, c]) => [x, c / g]))
    comps.push(sum)
    const kept = left.filter(l => !strict(l))
    keep = keep.filter(l => !strict(l))
    if (kept.length === left.length) break
    left = kept
  }
  return {comps, left: left.length}
}
const gcd = (a: number, b: number): number => (b === 0 ? a : gcd(b, a % b))
// The same over named naturals and the edges of runs alone (core/data.ts: a recursive function's calls, each from its
// parameters' sizes to its arguments'): each component's coefficient per variable and its constant. Several nodes (a
// ring of functions calling each other, each its own names; `nodes`), each its own coefficients and constant per
// component (a rank per location: (size(x), 1) at one function, (size(x), 0) at the one it calls with x). Its budget,
// `ms`, is read on the shared clock (kernel/prove.ts's `clock`): counted work inside a counted search, its pivots counted
// as the solver's rows are, so a counted search's verdict doesn't depend on the machine's speed.
export function ranksOfRuns(vars: string[], points: Env[], edges: {s: Env, t: Env}[], ms = 1000): {comps: {coef: Record<string, number>, c: number}[], left: number} {
  const r = ranksOfCalls([vars], points.map(env => ({node: 0, env})), edges.map(e => ({from: 0, to: 0, s: e.s, t: e.t})), ms)
  return {comps: r.comps.map(c => c[0]!), left: r.left}
}
export function ranksOfCalls(nodes: string[][], points: {node: number, env: Env}[], edges: {from: number, to: number, s: Env, t: Env}[], ms = 1000): {comps: {coef: Record<string, number>, c: number}[][], left: number} {
  const ns: Node[] = nodes.map((vars, i) => ({name: `runs ${i}`, hyps: [], concl: yes, vars, level: 0, given: true}))
  const name = nodes.length === 1 ? shared : own(ns), idx = nodes.map((_, i) => i)
  const {comps, left} = lexRanks(idx, ns, nodes.map((_, i) => points.filter(p => p.node === i).map(p => ({env: p.env, calls: new Set<string>()}))), edges, name, clock() + ms)
  return {comps: comps.map(c => ns.map((nd, n) => ({coef: Object.fromEntries(nd.vars.map((x, j) => [x, c[name(n, j)] ?? 0])), c: c[name(n, 'b')] ?? 0}))), left}
}
const compE = (c: Comp, n: number, node: Node, name: Naming): E => unfeat(linE(Object.fromEntries(node.vars.map((x, j) => [x, c[name(n, j)] ?? 0])), c[name(n, 'b')] ?? 0))
// Ranks of degree 2: a product of two of a node's variables (a square too) a further variable of the LP, its value at
// each sample the product's, one product at a time (a sparse template: with every product at once, the runs fit a rank
// of many small parts that no turn past them keeps). The rank found is linear in it, the product read back as the term
// it is (x·y as prod(x, y)), which the kernel takes as a monomial, its goals the same linear goals over it (with its
// products of rows and squares, Positivstellensatz of degree 2, where they need more).
const featSep = '·'
const products = (names: string[]): [string, string][] => names.flatMap((a, i) => names.slice(i).map(b => [a, b] as [string, string]))
const featName = ([a, b]: [string, string]) => `${a}${featSep}${b}`
const withFeat = (env: Env, p: [string, string] | undefined): Env => (p && env[p[0]] !== undefined && env[p[1]] !== undefined ? {...env, [featName(p)]: env[p[0]]! * env[p[1]]!} : env)
// (linE builds sums, differences and multiples of variables and constants only)
const unfeat = (e: E): E => {
  if (e.op === 'var') { const [a, b] = e.name.split(featSep); return b === undefined ? e : {op: 'prod', a: v(a!), b: v(b)} }
  if (e.op === 'add' || e.op === 'sub') return {...e, a: unfeat(e.a), b: unfeat(e.b)}
  return e.op === 'mul' ? {...e, a: unfeat(e.a)} : e
}
// The products of two variables a term reads, each as its sorted pair.
const productsIn = (t: unknown): [string, string][] => {
  const out = new Map<string, [string, string]>()
  walk(t, o => { if (o.op === 'prod') { const a = o.a as E, b = o.b as E; if (a.op === 'var' && b.op === 'var') { const p = [a.name, b.name].sort() as [string, string]; out.set(id(p), p) } } })
  return [...out.values()]
}
// The nodes, samples and edges with one product of two variables per node a variable (none where `ps[i]` is undefined).
const withProducts = (nodes: Node[], samples: Sampled[][], edges: Edge[], ps: ([string, string] | undefined)[]) => ({
  nodes: nodes.map((n, i) => (ps[i] ? {...n, vars: [...n.vars, featName(ps[i]!)]} : n)),
  samples: samples.map((ss, i) => ss.map(s => ({...s, env: withFeat(s.env, ps[i])}))),
  edges: edges.map(e => ({...e, s: withFeat(e.s, ps[e.from]), t: withFeat(e.t, ps[e.to])})),
})
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
// `quad`: ranks of degree 2, the product of those two variables a further one of each node that has both.
function build(facts: Fact[], cx: Ctx, nodes: Node[], depth: number, big: number, until: number, quad?: [string, string]): Built {
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
    const q = quad ? withProducts(nodes, samples, within, nodes.map(n => (n.vars.includes(quad[0]) && n.vars.includes(quad[1]) ? quad : undefined))) : {nodes, samples, edges: within}
    let best = {...lexRanks(idx, q.nodes, q.samples, q.edges, shared, until, !!quad), name: shared}
    if (best.left && idx.length > 1 && idx.length <= 4) { const o = lexRanks(idx, q.nodes, q.samples, q.edges, own(q.nodes), until, !!quad); if (o.left < best.left) best = {...o, name: own(q.nodes)} }
    for (const i of idx) parts.set(i, best.comps.map(cp => compE(cp, i, q.nodes[i]!, best.name)))
  }
  const width = Math.max(0, ...[...parts.values()].map(p => p.length)), tiers = graph.some(g => g.length)
  const ranks = nodes.map((_, i) => [...(tiers ? [k(heightOf(comp[i]!))] : []), ...parts.get(i)!, ...Array.from({length: width - parts.get(i)!.length}, () => k(0))])
  let uses = 0
  const specs: NodeSpec[] = nodes.map((n, i) => ({
    name: n.name, hyps: n.hyps, concl: n.concl, rank: ranks[i]!, insts: inst[i]!.insts,
    // (a use at a rank that is this node's own, term for term, never applies: its guard is false, so it is left out)
    uses: cands[i]!.filter((c, u) => active[i]![u] && id(ranks[c.node]!.map(r => substE(r, vs(c.subst)))) !== id(ranks[i])).map(c => {
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
const nodeOf = (c: Claim, level: number, given: boolean): Node => ({name: c.name, hyps: c.hyps ?? [], concl: c.concl, vars: varsOf([c.hyps ?? [], c.concl]), level, given})
// The facts at the terms a claim's goal reads (and at those the facts read, `depth` times over): what the search gives
// each node, for a caller building nodes of its own (research/frontier's today, the builders' shape).
export function claimInstances(facts: Fact[], claim: Claim, depth = 2): NodeSpec['insts'] {
  const {eqs, arity} = equations(facts)
  return instancesFor(facts, {eqs, arity, values: {}, memo: new Map(), fuel: 0, depth: 0}, nodeOf(claim, 0, true), depth).insts
}
export function findCycles(facts: Fact[], claims: Claim[], opts: CycleOptions = {}): CycleVerdict {
  const t0 = clock(), until = t0 + (opts.ms ?? 10_000), depth = opts.depth ?? 1
  const {eqs, arity} = equations(facts)
  const cx: Ctx = {eqs, arity, values: opts.values ?? {}, memo: new Map(), fuel: 20_000, depth: 0}
  const big = Math.max(0, ...constsOf([facts.map(f => f.holds), claims]).filter(c => c <= 1000))
  const given: Node[] = claims.map(c => nodeOf(c, 1, !opts.houdini))
  let last: CycleVerdict = {proven: false, checked: false, why: 'nothing tried'}
  // One set of nodes, Houdini over those that may be dropped: each failing one dropped and the rest proven again.
  // One set of nodes, built and proven: the verdict, or the node that failed (a broken one: the runs refute it).
  type Tried = {proven: CycleVerdict} | {failed: Node, verdict: CycleVerdict}
  const once = (nodes: Node[], depth: number, quad?: [string, string]): Tried => {
    const b = withDeadline(until, () => build(facts, cx, nodes, depth, big, until, quad))
    if ('broken' in b) { const at = nodes.find(n => n.name === b.broken.node)!; return {failed: at, verdict: {proven: false, checked: false, goal: at.name, stuck: 'sat', witness: b.broken.env, why: 'the facts, run, break it'}} }
    if ('why' in b) return {failed: nodes[0]!, verdict: {proven: false, checked: false, why: b.why}}
    if (trace) for (const sp of b.specs) console.error(`[cycles] ${sp.name}: rank (${sp.rank.map(showE).join(', ')}), ${sp.insts.length} instances, uses ${sp.uses.map(u => `${u.node}@{${Object.entries(u.subst).map(([x, t]) => `${x} := ${showE(t)}`).join(', ')}}`).join(' ')}`)
    const out = withDeadline(until, () => proveCyclic(facts, b.specs))
    if (trace) console.error(`[cycles] ${out.proven ? 'proven' : `${out.node}: ${out.goal} ${out.stuck}`} at ${Math.round(clock() - t0)} ms`)
    if (!out.proven) { const at = nodes.find(n => n.name === out.node) ?? nodes[0]!; return {failed: at, verdict: {proven: false, checked: false, goal: out.goal, stuck: out.stuck}} }
    const found: CycleFound = {ranks: Object.fromEntries(nodes.map((n, i) => [n.name, `(${b.ranks[i]!.map(showE).join(', ')})`])), companions: nodes.filter(n => !n.given && !claims.some(c => c.name === n.name)).map(n => `${showC(n.concl)}${n.hyps.length ? ` where ${showC(and(...n.hyps))}` : ''}`), uses: b.uses}
    return {proven: {proven: true, checked: out.checked, proof: out.proof, specs: b.specs, kept: nodes.map(n => n.name), found, ...(out.why ? {why: out.why} : {})}}
  }
  // Houdini over the nodes that may be dropped (each that fails, dropped, the rest proven again); then each companion
  // dropped in turn where the rest are proven without it (only what the claims need is kept).
  const attempt = (start: Node[], depth: number, quad?: [string, string]): CycleVerdict => {
    let nodes = start, done: CycleVerdict | undefined
    for (let round = 0; round <= start.length && nodes.length && clock() < until && !done; round++) {
      const t = once(nodes, depth, quad)
      if ('proven' in t) { done = t.proven; break }
      if (t.failed.given) return t.verdict
      nodes = nodes.filter(n => n !== t.failed)
    }
    if (!done) return {proven: false, checked: false, why: clock() >= until ? 'out of time' : 'every candidate dropped'}
    if (opts.houdini) return done
    for (const c of nodes.filter(n => !n.given)) {
      if (clock() >= until) break
      const rest = nodes.filter(n => n !== c), t = once(rest, depth, quad)
      if ('proven' in t && t.proven.checked) (nodes = rest, done = t.proven)
    }
    return done
  }
  // The claims alone, with the facts at the terms they read and then at those the facts read; their constants as
  // variables; companions beside them by analogy, then every bound; then ranks of degree 2, over each product of two
  // variables the claims read (up(i, n) = up(i + 1, n) while i < n·n: n·n − i).
  const quads = productsIn(given.map(n => [n.hyps, n.concl])).filter(([a, b]) => given.some(n => n.vars.includes(a) && n.vars.includes(b)))
  const tries: [number, () => Node[], [string, string]?][] = [
    [depth, () => given], [depth + 1, () => given],
    ...(opts.generalize === false ? [] : [
      [depth, () => given.flatMap((n, i) => { const g = abstracted(cx, n, i, big, until); return g ? [n, g] : [n] })],
      [depth + 1, () => [...given, ...beside(cx, facts, given, big, until, true)]],
      [depth + 1, () => [...given, ...beside(cx, facts, given, big, until, false)]],
    ] as [number, () => Node[]][]),
    ...quads.flatMap(p => [[depth, () => given, p], [depth + 1, () => given, p]] as [number, () => Node[], [string, string]][]),
  ]
  const tried = new Set<string>()
  for (const [d, t, quad] of tries) {
    if (clock() >= until) break
    const nodes = t()
    if (tried.has(id([d, nodes.map(n => n.name), quad]))) continue
    tried.add(id([d, nodes.map(n => n.name), quad]))
    const out = attempt(nodes, d, quad)
    if (out.proven || out.stuck === 'sat' && out.why) return out
    last = out
  }
  return last
}

// --- loops: ranks from the relation ------------------------------------------------------------------------------
//
// The runs reach some turns and miss others: an input an equation pins, fresh values bounded together, a start the
// runs' small values never take; and a rank fitted to them may read a start value it has no business reading. Here
// the rank comes from the loop's relation instead (core/relation.ts): its linear paths over the integers its pairs of
// naturals are, each path's generators (vertices, rays, lines), so a linear condition at every point of a path is
// finitely many rows over the rank's coefficients, an LP (Podelski–Rybalchenko's, with the generators in place of
// Farkas' multipliers). No sample is needed, and nothing outside the relation is read.
//
// The rank: blocks in order (Bradley–Manna–Sipma), each strict on the paths it can be and kept by the rest, each a
// nested rank of depth 1 to 3 (Leike–Heizmann: f₁ drops by 1, fⱼ + fⱼ₋₁ drops by 1, the last ≥ 0: a multiphase rank,
// y + 1 then x for x := x + y; y := y − 1), linear per location (the natural every path fixes: the program counter),
// coefficients shared by the locations first, then each its own over the names live there. A block's kernel terms
// are fⱼ + 1 read truncated, in order: on a path it is strict on, the first fⱼ that is ≥ 0 drops and those before it
// stay 0; on one it keeps (each fⱼ' ≤ fⱼ), none rises. (Of depth 1, f ≥ 1 where it drops, and f itself: the same rank,
// its least constant.) The kernel proves the halting goals with it, as with any rank.
type GPath = {from: number, to: number, gens: Generators, post: Record<string, Lin>, rows: Lin[]}
type Template = {depth: number, own: boolean, tag: string, names: string[]} // names: a shared template's (the component's live names)
const plusL = (a: Lin, b: Lin, f = 1): Lin => { const o: Lin = {...a}; for (const x in b) { o[x] = (o[x] ?? 0) + f * b[x]!; if (!o[x]) delete o[x] } return o }
const konstL = (c: number): Lin => (c ? {1: c} : {})
const scaleL = (a: Lin, f: number): Lin => { const o: Lin = {}; if (f) for (const x in a) o[x] = a[x]! * f; return o }
// A form over the relation's names as the kernel's term (an integer's coefficient on its two parts), read truncated.
const termOf = (rel: Relation, f: Lin): E => {
  const coef: Record<string, number> = {}
  for (const [x, a] of Object.entries(f)) { if (x === '1') continue; const p = rel.ints.get(x); if (p) { coef[p[0]] = a; coef[p[1]] = -a } else coef[x] = a }
  return linE(coef, f['1'] ?? 0)
}
export function rankOfRelation(l: Loop, laws: Law[], until: number): {rank: E[], text: string, blocks: number[]} | {why: string} {
  const rel = relationOf(l, laws)
  return rel ? relationRank(l, rel, until) : {why: 'the turn is not linear (a map, a flag, or past the paths\' cap)'}
}
// `extra`: atoms (each ≤ 0) that hold at each location (by its index among the locations' values), read as rows of the
// paths that leave it.
// The locations (the values of the location natural, sorted; one with none), and the names each location's rank may
// read: those its paths' rows read, and what the values after read of the names read where the paths go (live).
const locations = (rel: Relation) => {
  const values = rel.loc ? [...new Set([...rel.from, ...rel.to])].sort((a, b) => a - b) : [0]
  const fromOf = (i: number) => (rel.loc ? values.indexOf(rel.from[i]!) : 0), toOf = (i: number) => (rel.loc ? values.indexOf(rel.to[i]!) : 0)
  const names = new Set([...rel.state, ...rel.params]), live = values.map(() => new Set<string>())
  for (const [i, p] of rel.paths.entries()) for (const r of p.rows) for (const x of Object.keys(r)) if (names.has(x)) live[fromOf(i)]!.add(x)
  for (let grew = true; grew;) {
    grew = false
    for (const [i, p] of rel.paths.entries()) for (const x of live[toOf(i)]!) for (const y of p.post[x] ? Object.keys(p.post[x]!) : [x]) if (names.has(y) && !live[fromOf(i)]!.has(y)) { live[fromOf(i)]!.add(y); grew = true }
  }
  return {values, fromOf, toOf, names, at: live.map(s => [...s].sort())}
}
// A rank from a relation made elsewhere (core/data.ts: a ring of functions' calls, a location per function, each
// call's argument sizes bounded from its parameters' and fields'): per location, each component's linear form over the
// names (no regions: those read an atom, not a form).
export function rankOfPaths(name: string, rel: Relation, until: number): {forms: Lin[][], values: number[]} | {why: string} {
  const r = relationRank({name} as Loop, rel, until)
  if (!('rank' in r)) return r
  return r.forms ? {forms: r.forms, values: locations(rel).values} : {why: 'a rank by regions'}
}
// `inv`: for regions' own invariants, each location's candidates (by its index), the starts (a location's index and the
// values there) and how a set of bounds is narrowed to the tightest.
type RegionInv = {cands: Lin[][], starts: [number, Env][], tightest: (hs: Lin[]) => Lin[]}
function relationRank(l: Loop, rel: Relation, until: number, extra: Lin[][] = [], inv?: RegionInv): {rank: E[], text: string, blocks: number[], laws: Law[], texts: string[], forms?: Lin[][]} | {why: string} {
  const {values, fromOf, toOf, names, at} = locations(rel)
  const every = [...new Set(at.flat())].sort()
  const gpaths: GPath[] = []
  for (const [i, p] of rel.paths.entries()) {
    if (clock() > until) return {why: 'out of time on the relation'}
    const rows = [...p.rows, ...(extra[fromOf(i)] ?? [])]
    const ns = [...new Set([...rows.flatMap(r => Object.keys(r)), ...Object.values(p.post).flatMap(r => Object.keys(r)), ...every])].filter(x => x !== '1').sort()
    const gens = generators(rows, ns, rel.nats, 600, until)
    if (!gens) return {why: 'a path past the generators\' cap'}
    if (gens.vertices.length) gpaths.push({from: fromOf(i), to: toOf(i), gens, post: p.post, rows})
  }
  // A template's value at a generator (x, t), as a form over the unknowns; after the turn, through the path's values.
  const unknown = (tp: Template, j: number, n: number, x: string | 1) => (x === 1 ? `b:${tp.tag}${j}:${n}` : `a:${tp.tag}${j}:${tp.own ? n : '*'}:${x}`)
  // a node: a location, or one side of an atom at a location (regions, below)
  const nodeLoc: number[] = values.map((_, n) => n)
  const varsAt = (tp: Template, n: number) => (tp.own ? at[nodeLoc[n]!]! : tp.names)
  const fAt = (tp: Template, j: number, n: number, x: Env, t: number): Lin => {
    const out: Lin = {}
    for (const v of varsAt(tp, n)) if (x[v]) out[unknown(tp, j, n, v)] = x[v]!
    if (t) out[unknown(tp, j, n, 1)] = t
    return out
  }
  const postAt = (p: GPath, x: Env, t: number): Env => {
    const out: Env = {...x}
    for (const [v, f] of Object.entries(p.post)) { let s = 0; for (const [u, c] of Object.entries(f)) s += c * (u === '1' ? t : x[u] ?? 0); out[v] = s }
    return out
  }
  // Rows (≤ 0) saying h ≥ c at every point of the path: at each vertex h(x, t) ≥ c·t, along each ray h's linear part
  // ≥ 0, along each line = 0.
  const holds = (p: GPath, h: (x: Env, t: number) => Lin, c: number): Lin[] => {
    const env = (g: number[]) => Object.fromEntries(p.gens.names.map((x, i) => [x, g[i]!]))
    const tOf = (g: number[]) => g[p.gens.names.length]!
    // (each row once; one that reads no unknown and holds, along a name the template doesn't read, left out)
    const out = new Map<string, Lin>()
    for (const r of [
      ...p.gens.vertices.map(g => plusL(scaleL(h(env(g), tOf(g)), -1), {1: c * tOf(g)})),
      ...p.gens.rays.map(g => scaleL(h(env(g), 0), -1)),
      ...p.gens.lines.flatMap(g => [h(env(g), 0), scaleL(h(env(g), 0), -1)]),
    ]) if (Object.keys(r).some(x => x !== '1') || (r['1'] ?? 0) > 0) out.set(id(Object.keys(r).sort().map(x => [x, r[x]])), r)
    return [...out.values()]
  }
  const delta = (tp: Template, j: number, p: GPath) => (x: Env, t: number) => plusL(fAt(tp, j, p.from, x, t), fAt(tp, j, p.to, postAt(p, x, t), t), -1)
  const strictRows = (tp: Template, p: GPath): Lin[] => [
    ...holds(p, delta(tp, 0, p), 1),
    ...Array.from({length: tp.depth - 1}, (_, j) => holds(p, (x, t) => plusL(delta(tp, j + 1, p)(x, t), fAt(tp, j, p.from, x, t)), 1)).flat(),
    ...holds(p, (x, t) => fAt(tp, tp.depth - 1, p.from, x, t), tp.depth === 1 ? 1 : 0),
  ]
  const weakRows = (tp: Template, p: GPath): Lin[] => Array.from({length: tp.depth}, (_, j) => holds(p, delta(tp, j, p), 0)).flat()
  let scale = 1
  for (const p of gpaths) for (const g of p.gens.vertices) for (const x of g) if (Math.abs(x) + 1 > scale) scale = Math.abs(x) + 1
  const sat = (w: Record<string, number>, rows: Lin[]) => rows.every(r => valueAt(r, w) <= 0)
  // One block over the paths left: strict on all of them at once, else on as many as one after another allows.
  const block = (tp: Template, left: GPath[], greedy: boolean, until: number): {w: Record<string, number>, strict: GPath[]} | undefined => {
    // (each path's rows made once for the template)
    const strict = new Map(left.map(p => [p, strictRows(tp, p)])), weak = new Map<GPath, Lin[]>()
    const weakOf = (q: GPath) => { let r = weak.get(q); if (!r) weak.set(q, r = weakRows(tp, q)); return r }
    // all at once (a greedy try follows the same template's try of this, so it doesn't make it again)
    if (!greedy) { const all = lp(left.flatMap(p => strict.get(p)!), [], until, scale, undefined, true); return all && {w: all, strict: left} }
    const must: Lin[] = []
    let w: Record<string, number> | undefined
    for (const p of left) {
      if (clock() > until) break
      if (w && sat(w, strict.get(p)!)) continue
      const rows = strict.get(p)!, w2 = lp([...must, ...rows], left.filter(q => q !== p).flatMap(weakOf), until, scale, undefined, true)
      if (w2) { must.push(...rows); w = w2 }
    }
    return w && {w, strict: left.filter(p => sat(w, strict.get(p)!))}
  }
  // The locations' components: a path between two drops by the first part of the rank, the component's height; the
  // paths within each are ranked on their own (their locations are no other's, so the parts line up per location).
  const graph = values.map(() => new Set<number>())
  for (const p of gpaths) graph[p.from]!.add(p.to)
  const comp = sccs(graph.map(g => [...g])), height: number[] = []
  const heightOf = (c: number): number => (height[c] ??= Math.max(0, ...values.flatMap((_, n) => (comp[n] === c ? [...graph[n]!].filter(m => comp[m] !== c).map(m => heightOf(comp[m]!) + 1) : []))))
  // The paths of one component in order of blocks: each component a form per node.
  const ranked = (paths: GPath[], tag0: string, until: number): {parts: Lin[][], sizes: number[]} | {why: string} => {
    let left = paths
    const mine: Lin[][] = [], sizes: number[] = []
    // a shared template's names: those live where the component's paths begin or end
    const names = [...new Set(paths.flatMap(p => [...at[nodeLoc[p.from]!]!, ...at[nodeLoc[p.to]!]!]))].sort()
    while (left.length && mine.length < 16 && clock() < until) {
      const tag = `${tag0}${mine.length}.`
      // depth 1 first, all at once then one path after another; then deeper
      const order: [Template, boolean][] = [1, 2, 3].flatMap(depth => [false, true].flatMap(greedy => [false, true].map((own): [Template, boolean] => [{depth, own, tag, names}, greedy])))
      let found: {w: Record<string, number>, strict: GPath[], tp: Template} | undefined
      for (const [tp, greedy] of order) {
        if (found || clock() > until) break
        const t1 = clock(), b = block(tp, left, greedy, until)
        if (trace) console.error(`[cycles] ${l.name}: block ${tag} depth ${tp.depth}${tp.own ? ' own' : ''}${greedy ? ' greedy' : ''}: ${b ? b.strict.length : 'none'} of ${left.length} paths, ${Math.round(clock() - t1)} ms`)
        if (b && b.strict.length) found = {...b, tp}
      }
      if (!found) return {why: `no block of a nested rank per location is strict on any of the ${left.length} paths left (of ${gpaths.length})`}
      const {w, tp, strict} = found
      for (let j = 0; j < tp.depth; j++) mine.push(nodeLoc.map((_, n) => {
        const f: Lin = {}
        for (const x of varsAt(tp, n)) { const a = w[unknown(tp, j, n, x)] ?? 0; if (a) f[x] = a }
        return plusL(f, {1: (tp.depth === 1 ? 0 : 1) + (w[unknown(tp, j, n, 1)] ?? 0)})
      }))
      sizes.push(tp.depth)
      left = left.filter(p => !strict.includes(p))
    }
    if (left.length) return {why: clock() >= until ? 'out of time on the relation' : 'past 16 components'}
    return {parts: mine, sizes}
  }
  // Regions: a component with no rank, its locations split by atoms (one, then two at once): the atoms its paths read
  // (q < p: min(p, q); y ≥ 2: a sign) and the signs of what a path adds to a value (y := y + x: x ≥ 1). Each sign vector
  // at a location is a node of its own, the paths split by the signs before and after; the kernel's term reads the atoms
  // (if atom then f else g). With invariants (`inv`), each node's own first, by Houdini over every path of the relation
  // split the same way: disjunctive invariants (x ≤ −1 where x ≥ 1 fails, after x := 1 or x := −1), each a law
  // (pc = ℓ ∧ the signs → atom) the kernel proves inductive with the rest.
  const after1 = (p: GPath, a: Lin): Lin => { let o: Lin = {}; for (const [x, c] of Object.entries(a)) o = plusL(o, x !== '1' && p.post[x] ? scaleL(p.post[x]!, c) : {[x]: c}); return o }
  const side = (a: Lin, yes: boolean): Lin => (yes ? a : plusL({1: 1}, a, -1))
  const regionLaws: Law[] = [], regionTexts: string[] = []
  const regions = (c: number, paths: GPath[]): {parts: E[][], sizes: number[]} | undefined => {
    const seen = new Set<string>(), guards: Lin[] = [], deltas: Lin[] = []
    const add = (r: Lin, to: Lin[]) => {
      const key = [id(Object.keys(r).sort().map(x => [x, r[x]])), id(Object.keys(side(r, false)).sort().map(x => [x, side(r, false)[x]]))].sort().join()
      if (!seen.has(key)) { seen.add(key); to.push(r) }
    }
    for (const r of paths.flatMap(p => p.rows)) if (Object.keys(r).every(x => x === '1' || names.has(x)) && Object.keys(r).length >= 2) add(r, guards)
    for (const p of paths) for (const [x, f] of Object.entries(p.post)) {
      const d = plusL(f, {[x]: 1}, -1)
      if (Object.keys(d).some(y => y !== '1') && Object.keys(d).every(y => y === '1' || every.includes(y))) add(plusL({1: 1}, d, -1), deltas) // d ≥ 1, over live names
    }
    guards.sort((a, b) => Object.keys(b).length - Object.keys(a).length)
    // (the signs of what paths add first: fewer, and each a direction of progress; then the guards' atoms)
    const singles = [...deltas.slice(0, 4), ...guards.slice(0, 8)], few = singles.slice(0, 4)
    // (two atoms at once only with the regions' own invariants: without them, the relation's search is the first of
    // several, and one atom's regions are what it had)
    const tries: Lin[][] = [...singles.map(a => [a]), ...(inv ? few.flatMap((a, i) => few.slice(i + 1).map(b => [a, b])) : [])]
    if (trace) console.error(`[cycles] ${l.name}: component ${c}: ${tries.length} splits to try`)
    const locs = values.flatMap((_, n) => (comp[n] === c ? [n] : []))
    for (const [ai, as] of tries.entries()) {
      if (clock() > until) return undefined
      // (each try its share of the time left)
      const mine = clock() + (until - clock()) / Math.max(2, tries.length - ai)
      // (every location split, not only the component's: a disjunction an invariant needs is often made before it, x := 1
      // or x := −1 on the way in)
      const K = as.length, base = nodeLoc.length, node = (n: number, bits: number) => base + (n << K) + bits
      for (const n of values.keys()) for (let b = 0; b < 1 << K; b++) nodeLoc.push(n)
      const sides = (p: GPath, bits: number, after: boolean) => as.map((a, i) => side(after ? after1(p, a) : a, ((bits >> i) & 1) === 0))
      // (undefined where a path's generators aren't found, past their cap or the time: a path left out is no path ranked)
      const splitOf = (ps: GPath[], extra: (n: number) => Lin[] = () => []): GPath[] | undefined => {
        const out: GPath[] = []
        for (const p of ps) for (let b1 = 0; b1 < 1 << K; b1++) for (let b2 = 0; b2 < 1 << K; b2++) {
          const rows = [...p.rows, ...sides(p, b1, false), ...sides(p, b2, true), ...extra(node(p.from, b1))]
          // (over the path's names and any an atom reads beside them: a name missing would drop its coefficient)
          const ns = rows.some(r => Object.keys(r).some(x => x !== '1' && !p.gens.names.includes(x))) ? [...new Set([...p.gens.names, ...rows.flatMap(r => Object.keys(r).filter(x => x !== '1'))])].sort() : p.gens.names
          const gens = generators(rows, ns, rel.nats, 600, mine)
          if (!gens) return undefined
          if (gens.vertices.length) out.push({from: node(p.from, b1), to: node(p.to, b2), gens, post: p.post, rows})
        }
        return out
      }
      const conds = as.map(a => leC(rel, a))
      const term = (fs: Lin[], n: number, i = 0, bits = 0): E => (i === K ? termOf(rel, fs[node(n, bits)]!) : {op: 'if', c: conds[i]!, then: term(fs, n, i + 1, bits), else: term(fs, n, i + 1, bits | (1 << i))})
      const answer = (out: {parts: Lin[][], sizes: number[]}) => ({parts: out.parts.map(fs => values.map((_, n) => (locs.includes(n) ? term(fs, n) : k(0)))), sizes: out.sizes})
      // (with invariants to find, the split is ranked once, with its regions' own: more rows, no fewer ranks)
      if (!inv) {
        const split = splitOf(paths)
        if (!split) continue
        const out = ranked(split, `${c}.r${ai}.`, mine)
        if (trace) console.error(`[cycles] ${l.name}: component ${c} split by ${conds.map(showC).join(' and ')}: ${'parts' in out ? out.parts.length + ' parts' : out.why}`)
        if ('parts' in out) return answer(out)
        continue
      }
      // the nodes' invariants: Houdini over every path split, each node's candidates its location's, those false at a
      // start in its region dropped
      const N = values.length << K
      const split0 = splitOf(gpaths)
      if (!split0) continue
      const cands = Array.from({length: N}, (_, j) => {
        const n = j >> K, bits = j & ((1 << K) - 1)
        const here = inv.starts.filter(([m, env]) => m === n && as.every((a, i) => valueAt(side(a, ((bits >> i) & 1) === 0), env) <= 0))
        return (inv.cands[n] ?? []).filter(h => here.every(([, env]) => valueAt(h, env) <= 0))
      })
      const relSplit: Relation = {...rel, paths: split0.map(p => ({rows: p.rows, pins: {}, post: p.post}))}
      const H = houdini(relSplit, cands, i => [split0[i]!.from - base, split0[i]!.to - base], mine)
      if (trace && !H) console.error(`[cycles] ${l.name}: component ${c} split by ${conds.map(showC).join(' and ')}: Houdini out of time`)
      if (!H) continue
      const Ht = H.map(inv.tightest)
      const split = splitOf(paths, nd => Ht[nd - base] ?? [])
      if (!split) continue
      const out = ranked(split, `${c}.h${ai}.`, mine)
      if (trace) console.error(`[cycles] ${l.name}: component ${c} split by ${conds.map(showC).join(' and ')}, with ${Ht.flat().length} invariants of the regions: ${'parts' in out ? out.parts.length + ' parts' : out.why}`)
      if (!('parts' in out)) continue
      for (let j = 0; j < N; j++) for (const h of Ht[j]!) {
        const n = j >> K, bits = j & ((1 << K) - 1), atom = leC(rel, h)
        const not = [...(rel.loc ? [eqC(v(rel.loc), k(values[n]!))] : []), ...as.map((a, i) => leC(rel, side(a, ((bits >> i) & 1) === 0)))]
        regionLaws.push({name: `region invariant ${c}.${j}.${regionLaws.length}`, holds: {op: 'or', xs: [...not.map((x): C => ({op: 'not', x})), atom]}})
        regionTexts.push(`${not.map(showC).join(' ∧ ')} → ${showC(atom)}`)
      }
      return answer(out)
    }
    return undefined
  }
  const parts: E[][][] = [] // per component of the locations: its parts, each a term per location
  const lins: (Lin[][] | undefined)[] = [] // the same as forms, where no regions were needed
  const sizes: number[] = []
  for (const c of [...new Set(comp)].sort((a, b) => a - b)) {
    // (half the time left for the component as it is: the regions have the rest)
    const inner = gpaths.filter(p => comp[p.from] === c && comp[p.to] === c), out = ranked(inner, `${c}.`, clock() + (until - clock()) / 2)
    if ('parts' in out) { parts[c] = out.parts.map(fs => values.map((_, n) => termOf(rel, fs[n]!))); lins[c] = out.parts; sizes.push(...out.sizes); continue }
    const r = regions(c, inner)
    if (!r) return out
    parts[c] = r.parts
    lins[c] = undefined
    sizes.push(...r.sizes)
  }
  // per location, its component's parts in order (0 past them), the heights first where paths join components
  const width = Math.max(0, ...parts.map(p => p?.length ?? 0))
  const columns: E[][] = [...(gpaths.some(p => comp[p.from] !== comp[p.to]) ? [values.map((_, n) => termOf(rel, konstL(heightOf(comp[n]!))))] : []),
    ...Array.from({length: width}, (_, j) => values.map((_, n) => parts[comp[n]!]?.[j]?.[n] ?? k(0)))]
  const rank = columns.map(terms => {
    let e = terms.at(-1) ?? k(0)
    for (let n = terms.length - 2; n >= 0; n--) if (id(terms[n]) !== id(e)) e = {op: 'if', c: eqC(v(rel.loc!), k(values[n]!)), then: terms[n]!, else: e}
    return e
  })
  if (!rank.length) rank.push(k(0))
  const linear = [...new Set(comp)].every(c => lins[c] || !parts[c])
  const forms = linear ? [...(gpaths.some(p => comp[p.from] !== comp[p.to]) ? [values.map((_, n) => konstL(heightOf(comp[n]!)))] : []),
    ...Array.from({length: width}, (_, j) => values.map((_, n) => lins[comp[n]!]?.[j]?.[n] ?? {}))] : undefined
  return {rank, text: `(${rank.map(showE).join(', ')})`, blocks: sizes, laws: regionLaws, texts: regionTexts, ...(forms ? {forms} : {})}
}

// Invariants first, so a rank may assume them: atoms per location (each name's bounds at the constants the paths
// read, and the paths' own atoms over the state and params), those false at a start dropped (the loop's starts, run
// from random params), then Houdini over the relation (core/relation.ts). Each kept as a law at its location
// (pc ≠ ℓ ∨ atom), which the kernel proves inductive with the halting goals; then each dropped in turn where the
// relation's rank is still found without it (and those that leaned on it).
const leC = (rel: Relation, f: Lin): C => {
  const pos: E[] = [], neg: E[] = []
  for (const [x, a] of Object.entries(f)) {
    if (x === '1') { if (a > 0) pos.push(k(a)); else if (a < 0) neg.push(k(-a)); continue }
    const p = rel.ints.get(x), parts: [string, number][] = p ? [[p[0], a], [p[1], -a]] : [[x, a]]
    for (const [y, c] of parts) (c > 0 ? pos : neg).push(Math.abs(c) === 1 ? v(y) : {op: 'mul', k: Math.abs(c), a: v(y)})
  }
  const sum = (xs: E[]) => (xs.length ? xs.reduce((s, x) => add(s, x)) : k(0))
  return le(sum(pos), sum(neg))
}
// The relation's rank with invariants: Houdini's set, then each atom dropped in turn where the set without it, closed
// again (those that leaned on it dropped too), still gives a rank.
export function rankWithInvariants(l: Loop, laws: Law[], until: number): {rank: E[], text: string, laws: Law[], texts: string[]} | {why: string} {
  const rel = relationOf(l, laws)
  if (!rel) return {why: 'the turn is not linear'}
  const {values, fromOf, toOf, names, at} = locations(rel)
  const locOf = (i: number): [number, number] => [fromOf(i), toOf(i)]
  const consts = new Set([0, 1, -1])
  for (const p of rel.paths) for (const r of p.rows) { const c = r['1'] ?? 0, xs = Object.keys(r).filter(x => x !== '1'); if (Math.abs(c) <= 1_000_000) for (const d of xs.length === 1 ? [c / Math.abs(r[xs[0]!]!)] : [c]) if (Number.isInteger(d)) { consts.add(d); consts.add(-d); consts.add(d + 1); consts.add(d - 1); consts.add(-d + 1); consts.add(-d - 1) } }
  const K = [...consts].sort((a, b) => Math.abs(a) - Math.abs(b) || a - b).slice(0, 24)
  const atoms: Lin[] = [...new Map(rel.paths.flatMap(p => p.rows).filter(r => Object.keys(r).filter(x => x !== '1').length > 1 && Object.keys(r).every(x => x === '1' || names.has(x))).map(r => [id(Object.keys(r).sort().map(x => [x, r[x]])), r] as const)).values()]
  // per location, over the names live there: their bounds at the constants, then (a second try) the paths' atoms too
  // (and 1 ≤ 0: the location unreachable, where every path into it leaves from states the rest rule out)
  const bounds = values.map((_, n) => [{1: 1}, ...at[n]!.flatMap(x => K.flatMap((c): Lin[] => [plusL({[x]: 1}, konstL(-c)), plusL({[x]: -1}, konstL(c))]))])
  // and what a path's assignments leave where it goes: x := y + c with y kept, x − y = c there (KoAT2's 2 + X₄ = X₁)
  const copies = values.map((): Lin[] => [])
  for (const [i, p] of rel.paths.entries()) for (const [x, f] of Object.entries(p.post)) {
    const ys = Object.keys(f).filter(y => y !== '1')
    if (ys.length !== 1 || f[ys[0]!] !== 1 || ys[0] === x || !names.has(ys[0]!)) continue
    const y = ys[0]!, kept = p.post[y] ? id(p.post[y]) === id({[y]: 1}) : true
    if (kept) copies[toOf(i)]!.push(plusL({[x]: 1, [y]: -1}, konstL(-(f['1'] ?? 0))), plusL({[x]: -1, [y]: 1}, konstL(f['1'] ?? 0)))
  }
  const withAtoms = values.map((_, n) => [...bounds[n]!, ...atoms.filter(a => Object.keys(a).every(x => x === '1' || at[n]!.includes(x))), ...copies[n]!.filter(a => Object.keys(a).every(x => x === '1' || at[n]!.includes(x)))])
  // the starts: random params (the precondition's), the state they begin in
  const cx: Ctx = {eqs: new Map(), arity: new Map(), values: {}, memo: new Map(), fuel: Infinity, depth: 0}, rand = seeded(31)
  const starts: [number, Env][] = []
  for (let s = 0; s < 400; s++) {
    const big = [2, 8, 64, 1000, 1_000_000][s % 5]!, ps = Object.fromEntries(l.params.map(p => [p, rand(big + 1)]))
    if (l.pre && evC(cx, l.pre, ps) !== true) continue
    const st: Env = {...ps}
    for (const [x, e] of Object.entries(l.state)) st[x] = ev(cx, e, ps) ?? 0
    const n = rel.loc ? values.indexOf(st[rel.loc] ?? -1) : 0
    if (n < 0) continue
    starts.push([n, Object.fromEntries([...names].map(x => { const p = rel.ints.get(x); return [x, p ? st[p[0]]! - st[p[1]]! : st[x] ?? 0] }))])
  }
  const atStarts = (cs: Lin[][]) => cs.map((c, n) => c.filter(h => starts.every(([m, env]) => m !== n || valueAt(h, env) <= 0)))
  const asLaws = (H: Lin[][]): {laws: Law[], texts: string[]} => {
    const out: Law[] = [], texts: string[] = []
    for (const [n, hs] of H.entries()) for (const [i, h] of hs.entries()) {
      const atom = leC(rel, h)
      out.push({name: `invariant ${n}.${i}`, holds: rel.loc ? {op: 'or', xs: [{op: 'not', x: eqC(v(rel.loc), k(values[n]!))}, atom]} : atom})
      texts.push(`${rel.loc ? `${rel.loc} = ${values[n]} → ` : ''}${showC(atom)}`)
    }
    return {laws: out, texts}
  }
  // of the bounds on one name each way, the tightest (the others follow from it: the same set)
  const tightest = (hs: Lin[]): Lin[] => {
    // (a location no run reaches: 1 ≤ 0 alone)
    const never = hs.find(c => Object.keys(c).every(x => x === '1') && (c['1'] ?? 0) > 0)
    if (never) return [never]
    const best = new Map<string, Lin>(), rest: Lin[] = []
    for (const c of hs) {
      const xs = Object.keys(c).filter(x => x !== '1')
      if (xs.length !== 1) { rest.push(c); continue }
      const x = xs[0]!, key = `${x}${Math.sign(c[x]!)}`, b = (c['1'] ?? 0) / Math.abs(c[x]!), was = best.get(key)
      if (!was || b > (was['1'] ?? 0) / Math.abs(was[x]!)) best.set(key, c)
    }
    return [...best.values(), ...rest]
  }
  let H: Lin[][] = [], found: ReturnType<typeof relationRank> = {why: 'no invariant'}
  const t1 = clock()
  for (const [i, cands] of [bounds, withAtoms].entries()) {
    if (clock() > until) break
    const closed = houdini(rel, atStarts(cands), locOf, i ? until : clock() + (until - clock()) / 2)
    if (trace) console.error(`[cycles] ${l.name}: houdini round ${i}: ${closed ? closed.map(h => h.map(x => showC(leC(rel, x))).join(" ∧ ")).join(" | ") : "none"}`)
    if (!closed) continue
    // (with none at any location, the regions' own may still be found: the second try only)
    if (!closed.some(h => h.length) && !i) continue
    H = closed.map(tightest)
    found = relationRank(l, rel, i ? until : clock() + (until - clock()) / 2, H, {cands: atStarts(cands), starts, tightest})
    if ('rank' in found) break
    found = {why: `with ${H.flat().length} invariants: ${found.why}`}
  }
  if (!('rank' in found)) return found
  // fewer: a location's atoms at once, then one atom at a time, within ten times the first search's time
  const stop = Math.min(until, clock() + Math.max(500, 10 * (clock() - t1)))
  const without = (drop: (n: number, h: Lin) => boolean): boolean => {
    const fewer = houdini(rel, H.map((g, n) => g.filter(h => !drop(n, h))), locOf, stop)
    if (!fewer || fewer.flat().length === H.flat().length) return false
    // (no regions' own invariants here: they would only find again the ones dropped)
    const r = relationRank(l, rel, stop, fewer)
    if ('rank' in r) { H = fewer; found = r; return true }
    return false
  }
  for (const n of H.keys()) { if (clock() > stop) break; if (H[n]!.length) without(m => m === n) }
  for (const [n, hs] of H.map((h, n) => [n, [...h]] as const)) for (const h of hs) { if (clock() > stop) break; if (H[n]!.includes(h)) without((m, g) => m === n && g === h) }
  const at0 = asLaws(H)
  return {rank: found.rank, text: found.text, laws: [...at0.laws, ...found.laws], texts: [...at0.texts, ...found.texts]}
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
  const t0 = clock(), until = t0 + (opts.ms ?? 10_000), rand = seeded(23)
  const cx: Ctx = {eqs: new Map(), arity: new Map(), values: {}, memo: new Map(), fuel: Infinity, depth: 0}
  const state = Object.keys(l.state), names = [...state, ...l.params].sort()
  const node: Node = {name: l.name, hyps: [], concl: yes, vars: names, level: 0, given: true}
  const points = new Map<string, Env>(), edges = new Map<string, Edge>()
  for (const bound of [2, 4, 8, 16, 32]) for (let trial = 0; trial < 40 && clock() < t0 + 1000; trial++) {
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
  // (the runs' LP within 10% of the time: the relation's search below has its share)
  const {comps, left} = lexRanks([0], [node], samples, [...edges.values()], shared, Math.min(until, t0 + 0.1 * (opts.ms ?? 10_000)))
  // Ranks of degree 2 where the linear one leaves turns or the kernel refuses it (while i < N·M: N·M − i, where the runs
  // alone give 299 − i): one product of two variables at a time. The products the loop's own terms read first (a rank
  // of degree 2 measures what its terms of degree 2 bound), before the invariants; the others after them, within a
  // quarter of the time.
  const read = productsIn([l.while, l.body, l.state, l.pre ?? yes, l.assume ?? yes]).filter(([x, y]) => names.includes(x) && names.includes(y))
  const rest = products(names).filter(p => !read.some(r => id(r) === id(p)))
  const seen = new Set<string>()
  const quadratic = (ps: [string, string][], until: number): {rank: E[], verdict: ReturnType<typeof goalsProven>}[] => {
    const out: {rank: E[], verdict: ReturnType<typeof goalsProven>}[] = []
    for (const p of ps) {
      if (clock() > until) break
      const d = withProducts([node], samples, [...edges.values()], [p]), r = lexRanks([0], d.nodes, d.samples, d.edges, shared, until)
      if (!r.comps.length || r.left) continue
      const r2 = r.comps.map(c => compE(c, 0, d.nodes[0]!, shared))
      if (seen.has(id(r2))) continue
      seen.add(id(r2))
      const verdict = withDeadline(until, () => goalsProven(loopObligations(l, laws, r2)))
      if (trace) console.error(`[cycles] ${l.name}: degree 2 with ${featName(p)}: (${r2.map(showE).join(', ')}) ${'trees' in verdict ? 'proven' : verdict.goal}`)
      out.push({rank: r2, verdict})
      if ('trees' in verdict) break
    }
    return out
  }
  const done = (rank: E[], trees: Record<string, Tree>, more: Law[] = [], texts: string[] = []): RankVerdict =>
    ({proven: true, checked: true, rank, laws: more, found: {rank: `(${rank.map(showE).join(', ')})`, laws: texts}, trees})
  // The linear rank first, then those of degree 2 over the products the loop reads, each checked in turn.
  const linear = comps.map(c => compE(c, 0, node, shared))
  let tried: {rank: E[], verdict: ReturnType<typeof goalsProven>}[] = []
  if (comps.length && !left) {
    seen.add(id(linear))
    // (its check within 20% of the time: the relation's search below has its share)
    tried.push({rank: linear, verdict: withDeadline(Math.min(until, t0 + 0.2 * (opts.ms ?? 10_000)), () => goalsProven(loopObligations(l, laws, linear)))})
    if ('trees' in tried[0]!.verdict) return done(linear, tried[0]!.verdict.trees)
  }
  // The relation's rank (per location, in phases), within a third of the time left; then degree 2 over the products the loop
  // reads; then the relation's rank with invariants. (A search that throws, a stack too deep for a large loop say,
  // gives way to the rest.)
  const safely = <T extends object>(f: () => T): T | {why: string} => { try { return f() } catch (e) { return {why: `the relation's search threw: ${(e as Error).message.slice(0, 120)}`} } }
  const relT0 = clock(), rel = safely(() => rankOfRelation(l, laws, clock() + (until - clock()) / 3))
  let relWhy = 'rank' in rel ? `the kernel refused ${rel.text}` : rel.why
  if (trace) console.error(`[cycles] ${l.name}: the relation's rank ${'rank' in rel ? rel.text : rel.why} (from ${Math.round(relT0 - t0)} ms to ${Math.round(clock() - t0)} ms)`)
  if ('rank' in rel) {
    const k0 = performance.now(), verdict = withDeadline(until, () => goalsProven(loopObligations(l, laws, rel.rank)))
    if (trace) console.error(`[cycles] ${l.name}: the kernel on the relation's rank, ${Math.round(performance.now() - k0)} ms: ${'trees' in verdict ? 'proven' : `${verdict.goal} ${verdict.stuck}`}`)
    if ('trees' in verdict) return done(rel.rank, verdict.trees)
    relWhy = `the kernel refused ${rel.text.slice(0, 300)} at ${verdict.goal}`
  }
  tried.push(...quadratic(read, until))
  const won = tried.find(t => 'trees' in t.verdict)
  if (won && 'trees' in won.verdict) return done(won.rank, won.verdict.trees)
  if (!('rank' in rel)) {
    // invariants first: the relation's rank where they hold, with as few of them as it needs
    const inv = safely(() => rankWithInvariants(l, laws, clock() + (until - clock()) / 2))
    if (trace) console.error(`[cycles] ${l.name}: the relation's rank with invariants ${'rank' in inv ? `${inv.text} with ${inv.texts.join('; ')}` : inv.why}`)
    if ('rank' in inv) {
      const verdict = withDeadline(until, () => goalsProven(loopObligations(l, [...laws, ...inv.laws], inv.rank)))
      if ('trees' in verdict) return done(inv.rank, verdict.trees, inv.laws, inv.texts)
      if (trace) console.error(`[cycles] ${l.name}: the kernel refused ${inv.text} with ${inv.laws.length} invariants at ${verdict.goal}`)
      relWhy = `${relWhy}; with ${inv.laws.length} invariants, the kernel refused ${inv.text.slice(0, 300)} at ${verdict.goal}`
    } else relWhy = `${relWhy}; ${inv.why}`
  }
  if (!tried.length && comps.length) tried.push({rank: linear, verdict: withDeadline(until, () => goalsProven(loopObligations(l, laws, linear)))})
  // Invariants the rank needs: the descent as the loop's step laws, inferLaws's candidates chosen by its counterexamples
  // (within half the time left where products remain to be tried after them).
  const base = tried[0]
  if (base && !('trees' in base.verdict)) {
    const rank = base.rank, m = loopMachine(l), {stay, cover, helps} = livenessParts(m, loopLiveness(l, rank))
    const ms = (until - clock()) * (rest.length ? 0.5 : 1)
    if (ms > 300) {
      const inf = inferLaws(m, laws, [stay, cover, ...helps] as StepLaw[], {ms})
      const kept = inf.found.filter(f => !f.law.forall && !f.law.keys?.length), more = kept.map(f => f.law)
      if (inf.proven && more.length) {
        const all = [...laws, ...more], again = withDeadline(until + 5000, () => goalsProven(loopObligations(l, all, rank)))
        if ('trees' in again) return done(rank, again.trees, more, kept.map(f => f.text))
      }
    }
  }
  // (the products the loop doesn't read within a quarter of its time: a search that fails tries each of them)
  tried = quadratic(rest, Math.min(until, clock() + (opts.ms ?? 10_000) / 4))
  const late = tried.find(t => 'trees' in t.verdict)
  if (late && 'trees' in late.verdict) return done(late.rank, late.verdict.trees)
  if (!base || 'trees' in base.verdict) return {proven: false, checked: false, why: `no rank, linear or of degree 2, in order, drops on every turn of ${edges.size} sampled; the relation: ${relWhy}`}
  const text = `(${base.rank.map(showE).join(', ')})`, first = base.verdict
  return {proven: false, checked: false, rank: base.rank, found: {rank: text, laws: []}, goal: first.goal, stuck: first.stuck, ...(first.witness ? {witness: first.witness} : {}), why: `rank ${text} from the runs; no invariant found that it needs; the relation: ${relWhy}`}
}

// --- liveness: a rank found ------------------------------------------------------------------------------------------

// "From leads to to" with no rank stated (kernel.ts's Liveness with `rank: []`): the rank from the machine's runs. Random
// params and requests (the sampler's, the rule's kinds), a helpful request in its region half the time; each step from
// a state where `from` holds and `to` doesn't to another such is an edge: a helpful request's in its region must lower
// the rank, any other must not raise it (weak edges, kept until a component lowers them). The components linear over
// the state and params, in order, by the same elimination (the exact LP past the box); then the kernel's liveness goals
// (proveLiveness), with the invariants inferLaws finds where they need some. Nothing new is trusted.
export type Sampler = {params: (rand: (n: number) => number, bound: number) => Record<string, number>, input: (rand: (n: number) => number, bound: number, ps: Record<string, number>) => Request}
export type LeadsVerdict = {proven: boolean, checked: boolean, rank?: E[], laws?: Law[], found?: {rank: string, laws: string[]}, goal?: string, stuck?: string, witness?: Record<string, number>, why?: string}
export function findLeadsTo(m: Machine, laws: Law[], l: Liveness, sample: Sampler, opts: {ms?: number} = {}): LeadsVerdict {
  const t0 = clock(), until = t0 + (opts.ms ?? 10_000), rand = seeded(29), run = interpret(m)
  const names = [...Object.keys(m.state), ...m.params].sort(), helpful = livenessHelpful(l)
  const node: Node = {name: l.name, hyps: [], concl: yes, vars: names, level: 0, given: true}
  const env = (ps: Env, st: State): Env => ({...ps, ...st.scalars})
  const holds = (c: C, ps: Env, st: State) => { try { return evalMC(c, env(ps, st), st, m) } catch { return undefined } }
  const pending = (ps: Env, st: State) => holds(l.from, ps, st) === true && holds(l.to, ps, st) === false
  const points = new Map<string, Env>(), strong = new Map<string, Edge>(), weak = new Map<string, Edge>()
  for (const bound of [2, 4, 8, 16]) for (let trial = 0; trial < 20 && clock() < t0 + 1000; trial++) {
    let ps: Env
    try { ps = sample.params(rand, bound) } catch { continue }
    if (m.pre && holds(m.pre, ps, {scalars: {}, maps: {}}) !== true) continue
    let st: State
    try { st = run.init(ps) } catch { continue }
    for (let turn = 0; turn < 120; turn++) {
      const here = env(ps, st), was = pending(ps, st)
      if (was) points.set(id(here), here)
      // A helpful request in its region half the time (its named inputs at the state, the rest drawn), else any.
      const regions = helpful.filter(h => holds(h.when, ps, st) === true), h = regions.length && rand(2) ? regions[rand(regions.length)]! : undefined
      let next: State | undefined
      for (let tries = 0; tries < 20 && !next; tries++) {
        try {
          const input = sample.input(rand, bound, ps)
          if (h) for (const [x, t] of Object.entries(h.request)) input[x] = evalME(t, here, st, m)
          next = run.step(ps, st, input)
        } catch { /* refused: another */ }
      }
      if (!next) break
      if (was && pending(ps, next)) { const e = {from: 0, to: 0, s: here, t: env(ps, next)}; (h ? strong : weak).set(id([e.s, e.t]), e) }
      st = next
    }
  }
  // The trivial ranks first, where the runs allow them: the constant 0 (every helpful step in its region reaches `to` at
  // once: none sampled stays pending, which leaves the fit below nothing to fit), then each state variable alone (every
  // helpful step sampled that stays pending lowers it, and no other raises it), up to four of them. Rank 0 may take half
  // of what is left, each variable a quarter.
  const zero: E = {op: 'const', value: 0}, tried = new Map<string, ReturnType<typeof proveLiveness>>()
  const keeps = (x: string) => [...weak.values()].every(e => e.t[x]! <= e.s[x]!), lowers = (x: string) => [...strong.values()].every(e => e.t[x]! < e.s[x]!)
  const trivial: E[][] = [...(strong.size ? [] : [[zero]]), ...Object.keys(m.state).filter(x => keeps(x) && lowers(x)).slice(0, 4).map(name => [{op: 'var', name} as E])]
  const rankText = (rank: E[]) => `(${rank.map(showE).join(', ')})`
  for (const [i, rank] of trivial.entries()) {
    const ms = until - performance.now()
    if (ms < 200) break
    const v = withDeadline(performance.now() + ms * (i === 0 && !strong.size ? 0.5 : 0.25), () => proveLiveness(m, laws, {...l, rank}))
    if (v.proven && v.checked) return {proven: true, checked: true, rank, laws: [], found: {rank: rankText(rank), laws: []}}
    tried.set(id(rank), v)
  }
  const samples: Sampled[][] = [[...points.values()].map(env => ({env, calls: new Set()}))]
  const {comps, left} = lexRanks([0], [node], samples, [...strong.values()], shared, until, false, [...weak.values()])
  const noRank = `no linear rank, in order, that ${strong.size} helpful steps sampled lower and ${weak.size} others keep`
  const fitted = comps.length && !left ? comps.map(c => compE(c, 0, node, shared)) : undefined
  // Past the fit, the invariants a rank needs: the fitted one's, or else rank 0's where the runs allow it.
  const rank = fitted ?? (strong.size ? undefined : [zero])
  if (!rank) return {proven: false, checked: false, why: noRank}
  const text = rankText(rank), lv: Liveness = {...l, rank}
  const first = tried.get(id(rank)) ?? withDeadline(until, () => proveLiveness(m, laws, lv))
  if (first.proven && first.checked) return {proven: true, checked: true, rank, laws: [], found: {rank: text, laws: []}}
  const ms = until - clock()
  if (ms > 300) {
    const {stay, cover, helps} = livenessParts(m, lv), inf = inferLaws(m, laws, [stay, cover, ...helps], {ms})
    const kept = inf.found.filter(f => !f.law.forall && !f.law.keys?.length), more = kept.map(f => f.law)
    if (inf.proven && more.length) {
      const again = withDeadline(until + 5000, () => proveLiveness(m, [...laws, ...more], lv))
      if (again.proven && again.checked) return {proven: true, checked: true, rank, laws: more, found: {rank: text, laws: kept.map(f => f.text)}}
    }
  }
  const failed = first.failed ? {goal: first.failed.goal, stuck: first.failed.stuck, ...(first.failed.witness ? {witness: first.failed.witness} : {})} : {}
  if (!fitted) return {proven: false, checked: false, ...failed, why: `${noRank}; rank ${text}, which the runs allow, not proven, nor with the invariants found`}
  return {proven: false, checked: false, rank, found: {rank: text, laws: []}, ...failed, why: `rank ${text} from the runs; the kernel's goals not proven with it`}
}

// --- functions a rule reads -----------------------------------------------------------------------------------------

// Lemmas about the functions a machine reads (those with facts and JavaScript, one argument): from the values, each a
// constant on a region below or above a threshold (a constant of the facts or the rule, ±1), a line, or bounds; proven
// from the facts as cyclic claims (Houdini: one not proven dropped), then the laws with those kept as facts, each
// dropped in turn where the laws don't need it.
export type LemmaFound = {law: Law, text: string}
export function cycleLemmas(m: Machine, laws: Law[], stepLaws: StepLaw[] = [], opts: {ms?: number} = {}): {proven: boolean, checked: boolean, machine?: Machine, found: LemmaFound[], proof?: Cyclic, why?: string} {
  const until = clock() + (opts.ms ?? 10_000)
  const fns = Object.entries(m.fns ?? {}).filter(([, f]) => !f.recur && (f.arity ?? 1) === 1)
  const fns2 = Object.entries(m.fns ?? {}).filter(([, f]) => !f.recur && f.arity === 2 && f.call)
  if ((!fns.length && !fns2.length) || !m.facts?.length) return {proven: false, checked: false, found: [], why: 'no function known by its facts'}
  const facts: Fact[] = m.facts.map(f => ({name: f.name, keys: [...(f.forall ? [f.forall] : []), ...(f.keys ?? [])], holds: f.holds}))
  const values: Record<string, (...xs: number[]) => number> = {}
  for (const [name, f] of fns) values[name] = (q: number) => fnValue(f, q)
  for (const [name, f] of fns2) { const g = compileFunction<() => (a: number, b: number) => number>([], `return (${f.call})`)(); values[name] = (a: number, b: number) => g(a, b) }
  const ts = [...new Set(constsOf([m, laws, stepLaws]).filter(c => c >= 0 && c <= 1000).flatMap(c => [c - 1, c, c + 1]).filter(c => c >= 0))].sort((a, b) => a - b)
  const big = Math.max(24, ...ts), x = 'k$', y = 'j$', claims: Claim[] = []
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
  // A function of two arguments: over a grid of both, the line that fits exactly, and each bound by 0, either argument or
  // their sum plus the tightest constant (above, and below where it is one): a constant above only where the values
  // reach it below half the grid in both arguments (not the grid's own size).
  for (const [name] of fns2) {
    const f = values[name]!, B = Math.min(big, 24), pts: {env: Env, value: number}[] = []
    for (let a = 0; a <= B; a++) for (let b = 0; b <= B; b++) { let z: number; try { z = f(a, b) } catch { continue } if (Number.isSafeInteger(z) && z >= 0) pts.push({env: {[x]: a, [y]: b}, value: z}) }
    if (pts.length < 16) continue
    const read = get(name, argsKey([v(x), v(y)])), show = (l: Record<string, number>, c: number) => showE(linE(Object.fromEntries(Object.entries(l).map(([n, q]) => [n === x ? 'k' : 'j', q])), c))
    const line = fitExact([x, y], pts, until)
    if (line) { claims.push({name: `${name}(k, j) = ${show(line.coef, line.c)}`, concl: eqC(read, linE(line.coef, line.c))}); continue }
    for (const form of [{}, {[x]: 1}, {[y]: 1}, {[x]: 1, [y]: 1}] as Record<string, number>[]) {
      const at = (p: {env: Env}) => Object.entries(form).reduce((acc, [n, q]) => acc + q * p.env[n]!, 0)
      const d = Math.max(...pts.map(p => p.value - at(p))), lo = Math.min(...pts.map(p => p.value - at(p)))
      const reached = pts.some(p => p.value - at(p) === d && p.env[x]! <= B / 2 && p.env[y]! <= B / 2)
      if (Object.keys(form).length ? d <= 0 || reached : reached) claims.push({name: `${name}(k, j) ≤ ${show(form, d)}`, concl: d >= 0 ? le(read, linE(form, d)) : le(add(read, k(-d)), linE(form, 0))})
      if (Object.keys(form).length && lo >= 0) claims.push({name: `${name}(k, j) ≥ ${show(form, lo)}`, concl: le(linE(form, lo), read)})
    }
  }
  // Those of two arguments each proven alone (their keys are pairings, products: a goal that reads several such claims
  // at once is slow to refute), the rest together; the proof the nodes of each, side by side (no node of one uses
  // another's).
  const unique = [...new Map(claims.map(c => [c.name, c])).values()], two = (c: Claim) => m.fns?.[readsOf(c.concl)[0]?.map ?? '']?.arity === 2
  const proofs = new Map<string, Cyclic>()
  for (const c of unique.filter(two)) {
    if (clock() >= until) break
    const o = findCycles(facts, [c], {ms: Math.min(1000, (until - clock()) * 0.1), values, houdini: true, generalize: false})
    if (o.proven && o.checked && o.proof) proofs.set(c.name, o.proof)
  }
  const ones = unique.filter(c => !two(c))
  if (!ones.length && !proofs.size) return {proven: false, checked: false, found: [], why: unique.length ? 'no lemma proven' : 'no lemma fits the values'}
  const out: CycleVerdict = ones.length ? findCycles(facts, ones, {ms: Math.max(0, until - clock()) * 0.6, values, houdini: true, generalize: false}) : {proven: true, checked: true, kept: []}
  if ((!out.proven || !out.checked || !out.kept?.length) && !proofs.size) return {proven: false, checked: false, found: [], why: out.why ?? 'no lemma proven'}
  const kept = [...(out.proven && out.checked ? out.kept ?? [] : []), ...proofs.keys()]
  const sideBySide = (ps: Cyclic[]): Cyclic | undefined => {
    if (!ps.length) return undefined
    let at = 0
    const nodes = ps.flatMap(p => { const off = at; at += p.nodes.length; return p.nodes.map(n => ({...n, uses: n.uses.map(u => ({...u, node: u.node + off}))})) })
    return {facts: ps[0]!.facts, nodes}
  }
  const asLaw = (c: Claim): LemmaFound => {
    const holds: C = c.hyps?.length ? {op: 'or', xs: [{op: 'not', x: and(...c.hyps)}, c.concl]} : c.concl
    return {law: {name: c.name, forall: x, ...(varsOf(holds).includes(y) ? {keys: [y]} : {}), holds}, text: c.name}
  }
  let found = unique.filter(c => kept.includes(c.name)).map(asLaw)
  const proveWith = (fs: LemmaFound[]) => {
    const mm: Machine = {...m, facts: [...m.facts!, ...fs.map(f => f.law)]}
    const r = withDeadline(until, () => (stepLaws.length ? proveStepLaws(mm, laws, stepLaws) : proveLaws(mm, laws)))
    return {ok: r.proven && r.checked, machine: mm}
  }
  let best = proveWith(found)
  if (!best.ok) return {proven: false, checked: false, found: [], why: `lemmas proven (${found.map(f => f.text).join('; ')}), the laws not with them`}
  for (const f of [...found]) {
    if (clock() >= until) break
    const rest = found.filter(g => g !== f), again = proveWith(rest)
    if (again.ok) (found = rest, best = again)
  }
  const merged = sideBySide([...(out.proof && found.some(f => ones.some(c => c.name === f.text)) ? [out.proof] : []), ...found.flatMap(f => (proofs.has(f.text) ? [proofs.get(f.text)!] : []))])
  const proof = merged && checkCyclic(merged) ? merged : undefined
  return {proven: true, checked: true, machine: best.machine, found, ...(proof ? {proof} : {})}
}
