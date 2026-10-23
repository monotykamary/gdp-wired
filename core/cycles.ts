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
import {type Lin, solve} from './solver.ts'
import {grow, proveLaws, proveLiveness, proveStepLaws, withDeadline} from '../kernel/prove.ts'
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
    for (let round = 0; round < 40 && performance.now() < until; round++) {
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
  if (!stage(signs.at(-1)!, bounds.at(-1)!, true)) return fit ? undefined : exactLp(must, pool, until, whole)
  for (const natural of signs) for (const bound of bounds) for (const wide of [false, true]) { const w = stage(natural, bound, wide); if (w) return w }
  return undefined
}

// --- an exact LP ----------------------------------------------------------------------------------------------------

// Rationals over BigInt, always reduced, the denominator positive.
type Q = {n: bigint, d: bigint}
const bgcd = (a: bigint, b: bigint): bigint => { if (a < 0n) a = -a; if (b < 0n) b = -b; while (b) [a, b] = [b, a % b]; return a }
const q = (n: bigint, d = 1n): Q => { if (d < 0n) (n = -n, d = -d); const g = bgcd(n, d) || 1n; return g === 1n ? {n, d} : {n: n / g, d: d / g} }
const Q0 = q(0n), Q1 = q(1n)
const qadd = (a: Q, b: Q): Q => (a.d === b.d ? q(a.n + b.n, a.d) : q(a.n * b.d + b.n * a.d, a.d * b.d))
const qsub = (a: Q, b: Q): Q => qadd(a, {n: -b.n, d: b.d})
const qmul = (a: Q, b: Q): Q => (!a.n || !b.n ? Q0 : q(a.n * b.n, a.d * b.d))
const qdiv = (a: Q, b: Q): Q => q(a.n * b.d, a.d * b.n)
const qlt = (a: Q, b: Q) => a.n * b.d < b.n * a.d
// The primal simplex on a tableau whose basis is feasible: minimize cost·y over T·y = rhs (the last column), y >= 0,
// Bland's rule (the smallest column that improves, the smallest basis index among ties), only `open` columns entering.
function simplex(T: Q[][], basis: number[], cost: Q[], open: (j: number) => boolean, until: number): boolean {
  const cols = cost.length
  for (let it = 0; it < 5000; it++) {
    if (performance.now() > until) return false
    let enter = -1
    for (let j = 0; j < cols && enter < 0; j++) {
      if (!open(j) || basis.includes(j)) continue
      let r = cost[j]!
      for (const [i, b] of basis.entries()) if (T[i]![j]!.n && cost[b]!.n) r = qsub(r, qmul(cost[b]!, T[i]![j]!))
      if (r.n < 0n) enter = j
    }
    if (enter < 0) return true
    let leave = -1, best: Q | undefined
    for (const [i, row] of T.entries()) {
      if (row[enter]!.n <= 0n) continue
      const ratio = qdiv(row[cols]!, row[enter]!)
      if (!best || qlt(ratio, best) || (!qlt(best, ratio) && basis[i]! < basis[leave]!)) (best = ratio, leave = i)
    }
    if (leave < 0) return false // unbounded: not for an objective bounded below
    const p = T[leave]![enter]!
    T[leave] = T[leave]!.map(x => qdiv(x, p))
    for (const [i, row] of T.entries()) {
      if (i === leave || !row[enter]!.n) continue
      const f = row[enter]!
      T[i] = row.map((x, j) => qsub(x, qmul(f, T[leave]![j]!)))
    }
    basis[leave] = enter
  }
  return false
}
// The rows (lin <= 0) over free unknowns, solved exactly: Σ|u| least (each u as p − q, p, q >= 0), two phases. The
// rational solution scaled by its denominators' least common multiple and divided by its numerators' common divisor;
// kept only if every row holds of it exactly (a row with a positive constant, a drop of at least 1, holds of any
// multiple at least 1 of a solution; one with a negative constant may not).
function exactSolve(rows: Lin[], until: number): Record<string, number> | undefined {
  const xs = [...new Set(rows.flatMap(l => Object.keys(l)).filter(x => x !== '1'))].sort(), n = xs.length, m = rows.length
  // Columns: p (n), q (n), a slack per row (m), an artificial per row (m); the right-hand side last.
  const cols = 2 * n + 2 * m, T: Q[][] = [], basis: number[] = []
  for (const [i, l] of rows.entries()) {
    let rhs = -(l['1'] ?? 0)
    const sign = rhs < 0 ? -1 : 1
    rhs *= sign
    const row: Q[] = Array.from({length: cols + 1}, () => Q0)
    for (const [j, x] of xs.entries()) { const c = sign * (l[x] ?? 0); if (c) (row[j] = q(BigInt(c)), row[n + j] = q(BigInt(-c))) }
    row[2 * n + i] = q(BigInt(sign))
    if (sign < 0) { row[2 * n + m + i] = Q1; basis.push(2 * n + m + i) } else basis.push(2 * n + i)
    row[cols] = q(BigInt(rhs))
    T.push(row)
  }
  const art = (j: number) => j >= 2 * n + m
  const phase1 = Array.from({length: cols}, (_, j) => (art(j) ? Q1 : Q0))
  if (!simplex(T, basis, phase1, () => true, until)) return undefined
  if (T.some((row, i) => art(basis[i]!) && row[cols]!.n)) return undefined // infeasible
  // An artificial left in the basis at zero: pivoted out on any other column, or its row dropped (redundant).
  for (let i = T.length - 1; i >= 0; i--) {
    if (!art(basis[i]!)) continue
    const j = T[i]!.findIndex((x, c) => c < 2 * n + m && x.n !== 0n)
    if (j < 0) { T.splice(i, 1); basis.splice(i, 1); continue }
    const p = T[i]![j]!
    T[i] = T[i]!.map(x => qdiv(x, p))
    for (const [r, row] of T.entries()) if (r !== i && row[j]!.n) { const f = row[j]!; T[r] = row.map((x, c) => qsub(x, qmul(f, T[i]![c]!))) }
    basis[i] = j
  }
  const phase2 = Array.from({length: cols}, (_, j) => (j < 2 * n ? Q1 : Q0))
  if (!simplex(T, basis, phase2, j => !art(j), until)) return undefined
  const val = (j: number): Q => { const i = basis.indexOf(j); return i < 0 ? Q0 : T[i]![cols]! }
  const u = xs.map((_, j) => qsub(val(j), val(n + j)))
  let lcm = 1n
  for (const r of u) lcm = lcm / bgcd(lcm, r.d) * r.d
  const ints = u.map(r => r.n * (lcm / r.d)), g = ints.reduce((a, b) => bgcd(a, b), 0n) || 1n
  const w: Record<string, number> = {}
  for (const [j, x] of xs.entries()) { const c = Number(ints[j]! / g); if (!Number.isSafeInteger(c)) return undefined; if (c) w[x] = c }
  return rows.every(l => valueAt(l, w) <= 0) ? w : undefined
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
  for (let round = 0; round < 40 && performance.now() < until; round++) {
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
  const scale = 1 + Math.max(0, ...idx.flatMap(n => samples[n]!.flatMap(s => Object.values(s.env))))
  let left = [...new Map(edges.map(e => { const l = delta(e); return [id(l), l] as const })).values()]
  let keep = [...new Map(weak.map(e => { const l = delta(e); return [id(l), l] as const })).values()].filter(l => !left.some(x => id(x) === id(l)))
  const comps: Comp[] = []
  while (left.length && comps.length < 4 && performance.now() < until) {
    let sum: Comp = {}
    const strict = (l: Lin) => valueAt(l, sum) < 0
    // One try per pattern of signs (which unknowns an edge raises and lowers): edges alike drop alike, mostly.
    const tried = new Set<string>(), sign = (l: Lin) => id(Object.keys(l).filter(x => x !== '1').sort().map(x => `${x}${Math.sign(l[x]!)}`))
    for (const l of left) {
      if (strict(l) || performance.now() > until || tried.has(sign(l)) || tried.size > 40) continue
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
// parameters' sizes to its arguments'): each component's coefficient per variable and its constant.
export function ranksOfRuns(vars: string[], points: Env[], edges: {s: Env, t: Env}[], ms = 1000): {comps: {coef: Record<string, number>, c: number}[], left: number} {
  const node: Node = {name: 'runs', hyps: [], concl: yes, vars, level: 0, given: true}
  const {comps, left} = lexRanks([0], [node], [points.map(env => ({env, calls: new Set<string>()}))], edges.map(e => ({from: 0, to: 0, s: e.s, t: e.t})), shared, performance.now() + ms)
  return {comps: comps.map(c => ({coef: Object.fromEntries(vars.map((x, j) => [x, c[shared(0, j)] ?? 0])), c: c[shared(0, 'b')] ?? 0})), left}
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
  const t0 = performance.now(), until = t0 + (opts.ms ?? 10_000), depth = opts.depth ?? 1
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
    if (trace) console.error(`[cycles] ${out.proven ? 'proven' : `${out.node}: ${out.goal} ${out.stuck}`} at ${Math.round(performance.now() - t0)} ms`)
    if (!out.proven) { const at = nodes.find(n => n.name === out.node) ?? nodes[0]!; return {failed: at, verdict: {proven: false, checked: false, goal: out.goal, stuck: out.stuck}} }
    const found: CycleFound = {ranks: Object.fromEntries(nodes.map((n, i) => [n.name, `(${b.ranks[i]!.map(showE).join(', ')})`])), companions: nodes.filter(n => !n.given && !claims.some(c => c.name === n.name)).map(n => `${showC(n.concl)}${n.hyps.length ? ` where ${showC(and(...n.hyps))}` : ''}`), uses: b.uses}
    return {proven: {proven: true, checked: out.checked, proof: out.proof, specs: b.specs, kept: nodes.map(n => n.name), found, ...(out.why ? {why: out.why} : {})}}
  }
  // Houdini over the nodes that may be dropped (each that fails, dropped, the rest proven again); then each companion
  // dropped in turn where the rest are proven without it (only what the claims need is kept).
  const attempt = (start: Node[], depth: number, quad?: [string, string]): CycleVerdict => {
    let nodes = start, done: CycleVerdict | undefined
    for (let round = 0; round <= start.length && nodes.length && performance.now() < until && !done; round++) {
      const t = once(nodes, depth, quad)
      if ('proven' in t) { done = t.proven; break }
      if (t.failed.given) return t.verdict
      nodes = nodes.filter(n => n !== t.failed)
    }
    if (!done) return {proven: false, checked: false, why: performance.now() >= until ? 'out of time' : 'every candidate dropped'}
    if (opts.houdini) return done
    for (const c of nodes.filter(n => !n.given)) {
      if (performance.now() >= until) break
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
    if (performance.now() >= until) break
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
// stay 0; on one it keeps (each fⱼ' ≤ fⱼ), none rises. The kernel proves the halting goals with it, as with any rank.
type GPath = {from: number, to: number, gens: Generators, post: Record<string, Lin>}
type Template = {depth: number, own: boolean, tag: string}
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
function relationRank(l: Loop, rel: Relation, until: number, extra: Lin[][] = []): {rank: E[], text: string, blocks: number[]} | {why: string} {
  const values = rel.loc ? [...new Set([...rel.from, ...rel.to])].sort((a, b) => a - b) : [0]
  const fromOf = (i: number) => (rel.loc ? values.indexOf(rel.from[i]!) : 0), toOf = (i: number) => (rel.loc ? values.indexOf(rel.to[i]!) : 0)
  // the names each location's rank may read: those its paths' rows read, and what the values after read of the names
  // read where the paths go (live variables)
  const names = new Set([...rel.state, ...rel.params]), live = values.map(() => new Set<string>())
  for (const [i, p] of rel.paths.entries()) for (const r of p.rows) for (const x of Object.keys(r)) if (names.has(x)) live[fromOf(i)]!.add(x)
  for (let grew = true; grew;) {
    grew = false
    for (const [i, p] of rel.paths.entries()) for (const x of live[toOf(i)]!) for (const y of p.post[x] ? Object.keys(p.post[x]!) : [x]) if (names.has(y) && !live[fromOf(i)]!.has(y)) { live[fromOf(i)]!.add(y); grew = true }
  }
  const every = [...new Set(live.flatMap(s => [...s]))].sort(), at = live.map(s => [...s].sort())
  const gpaths: GPath[] = []
  for (const [i, p] of rel.paths.entries()) {
    if (performance.now() > until) return {why: 'out of time on the relation'}
    const rows = [...p.rows, ...(extra[fromOf(i)] ?? [])]
    const ns = [...new Set([...rows.flatMap(r => Object.keys(r)), ...Object.values(p.post).flatMap(r => Object.keys(r)), ...every])].filter(x => x !== '1').sort()
    const gens = generators(rows, ns, rel.nats)
    if (!gens) return {why: 'a path past the generators\' cap'}
    if (gens.vertices.length) gpaths.push({from: fromOf(i), to: toOf(i), gens, post: p.post})
  }
  // A template's value at a generator (x, t), as a form over the unknowns; after the turn, through the path's values.
  const unknown = (tp: Template, j: number, n: number, x: string | 1) => (x === 1 ? `b:${tp.tag}${j}:${n}` : `a:${tp.tag}${j}:${tp.own ? n : '*'}:${x}`)
  const varsAt = (tp: Template, n: number) => (tp.own ? at[n]! : every)
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
    return [
      ...p.gens.vertices.map(g => plusL(scaleL(h(env(g), tOf(g)), -1), {1: c * tOf(g)})),
      ...p.gens.rays.map(g => scaleL(h(env(g), 0), -1)),
      ...p.gens.lines.flatMap(g => [h(env(g), 0), scaleL(h(env(g), 0), -1)]),
    ]
  }
  const delta = (tp: Template, j: number, p: GPath) => (x: Env, t: number) => plusL(fAt(tp, j, p.from, x, t), fAt(tp, j, p.to, postAt(p, x, t), t), -1)
  const strictRows = (tp: Template, p: GPath): Lin[] => [
    ...holds(p, delta(tp, 0, p), 1),
    ...Array.from({length: tp.depth - 1}, (_, j) => holds(p, (x, t) => plusL(delta(tp, j + 1, p)(x, t), fAt(tp, j, p.from, x, t)), 1)).flat(),
    ...holds(p, (x, t) => fAt(tp, tp.depth - 1, p.from, x, t), 0),
  ]
  const weakRows = (tp: Template, p: GPath): Lin[] => Array.from({length: tp.depth}, (_, j) => holds(p, delta(tp, j, p), 0)).flat()
  const scale = 1 + Math.max(0, ...gpaths.flatMap(p => p.gens.vertices.flatMap(g => g.map(Math.abs))))
  const sat = (w: Record<string, number>, rows: Lin[]) => rows.every(r => valueAt(r, w) <= 0)
  // One block over the paths left: strict on all of them at once, else on as many as one after another allows.
  const block = (tp: Template, left: GPath[], greedy: boolean): {w: Record<string, number>, strict: GPath[]} | undefined => {
    const all = lp(left.flatMap(p => strictRows(tp, p)), [], until, scale, undefined, true)
    if (all) return {w: all, strict: left}
    if (!greedy) return undefined
    const must: Lin[] = []
    let w: Record<string, number> | undefined
    for (const p of left) {
      if (performance.now() > until) break
      if (w && sat(w, strictRows(tp, p))) continue
      const rows = strictRows(tp, p), w2 = lp([...must, ...rows], left.filter(q => q !== p).flatMap(q => weakRows(tp, q)), until, scale, undefined, true)
      if (w2) { must.push(...rows); w = w2 }
    }
    return w && {w, strict: left.filter(p => sat(w, strictRows(tp, p)))}
  }
  // The locations' components: a path between two drops by the first part of the rank, the component's height; the
  // paths within each are ranked on their own (their locations are no other's, so the parts line up per location).
  const graph = values.map(() => new Set<number>())
  for (const p of gpaths) graph[p.from]!.add(p.to)
  const comp = sccs(graph.map(g => [...g])), height: number[] = []
  const heightOf = (c: number): number => (height[c] ??= Math.max(0, ...values.flatMap((_, n) => (comp[n] === c ? [...graph[n]!].filter(m => comp[m] !== c).map(m => heightOf(comp[m]!) + 1) : []))))
  const parts: Lin[][][] = [] // per component of the locations: its parts, each a form per location
  const sizes: number[] = []
  for (const c of [...new Set(comp)].sort((a, b) => a - b)) {
    let left = gpaths.filter(p => comp[p.from] === c && comp[p.to] === c)
    const mine: Lin[][] = []
    while (left.length && mine.length < 8 && performance.now() < until) {
      const tag = `${c}.${mine.length}.`
      // depth 1 first, all at once then one path after another; then deeper
      const order: [Template, boolean][] = [1, 2, 3].flatMap(depth => [false, true].flatMap(greedy => [false, true].map((own): [Template, boolean] => [{depth, own, tag}, greedy])))
      let found: {w: Record<string, number>, strict: GPath[], tp: Template} | undefined
      for (const [tp, greedy] of order) {
        if (found || performance.now() > until) break
        const t1 = performance.now(), b = block(tp, left, greedy)
        if (trace) console.error(`[cycles] ${l.name}: block ${tag} depth ${tp.depth}${tp.own ? ' own' : ''}${greedy ? ' greedy' : ''}: ${b ? b.strict.length : 'none'} of ${left.length} paths, ${Math.round(performance.now() - t1)} ms`)
        if (b && b.strict.length) found = {...b, tp}
      }
      if (!found) return {why: `no block of a nested rank per location is strict on any of the ${left.length} paths left (of ${gpaths.length})`}
      const {w, tp, strict} = found
      for (let j = 0; j < tp.depth; j++) mine.push(values.map((_, n) => {
        const f: Lin = {}
        for (const x of varsAt(tp, n)) { const a = w[unknown(tp, j, n, x)] ?? 0; if (a) f[x] = a }
        return plusL(f, {1: 1 + (w[unknown(tp, j, n, 1)] ?? 0)})
      }))
      sizes.push(tp.depth)
      left = left.filter(p => !strict.includes(p))
    }
    if (left.length) return {why: performance.now() >= until ? 'out of time on the relation' : 'past 8 components'}
    parts[c] = mine
  }
  // per location, its component's parts in order (0 past them), the heights first where paths join components
  const width = Math.max(0, ...parts.map(p => p?.length ?? 0))
  const forms: Lin[][] = [...(gpaths.some(p => comp[p.from] !== comp[p.to]) ? [values.map((_, n) => konstL(heightOf(comp[n]!)))] : []),
    ...Array.from({length: width}, (_, j) => values.map((_, n) => parts[comp[n]!]?.[j]?.[n] ?? {}))]
  const rank = forms.map(fs => {
    const terms = fs.map(f => termOf(rel, f))
    let e = terms.at(-1) ?? k(0)
    for (let n = terms.length - 2; n >= 0; n--) if (id(terms[n]) !== id(e)) e = {op: 'if', c: eqC(v(rel.loc!), k(values[n]!)), then: terms[n]!, else: e}
    return e
  })
  if (!rank.length) rank.push(k(0))
  return {rank, text: `(${rank.map(showE).join(', ')})`, blocks: sizes}
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
  const values = rel.loc ? [...new Set([...rel.from, ...rel.to])].sort((a, b) => a - b) : [0]
  const locOf = (i: number): [number, number] => (rel.loc ? [values.indexOf(rel.from[i]!), values.indexOf(rel.to[i]!)] : [0, 0])
  const names = new Set([...rel.state, ...rel.params])
  const consts = new Set([0, 1, -1])
  for (const p of rel.paths) for (const r of p.rows) { const c = r['1'] ?? 0, xs = Object.keys(r).filter(x => x !== '1'); if (Math.abs(c) <= 1_000_000) for (const d of xs.length === 1 ? [c / Math.abs(r[xs[0]!]!)] : [c]) if (Number.isInteger(d)) { consts.add(d); consts.add(-d); consts.add(d + 1); consts.add(d - 1); consts.add(-d + 1); consts.add(-d - 1) } }
  const K = [...consts].sort((a, b) => Math.abs(a) - Math.abs(b) || a - b).slice(0, 24)
  const read = [...names].filter(x => rel.paths.some(p => p.rows.some(r => x in r) || Object.values(p.post).some(f => x in f))).sort()
  const atoms: Lin[] = [...new Map(rel.paths.flatMap(p => p.rows).filter(r => Object.keys(r).every(x => x === '1' || names.has(x)) && Object.keys(r).length > 1).map(r => [id(Object.keys(r).sort().map(x => [x, r[x]])), r] as const)).values()]
  let cands = values.map(() => [...read.flatMap(x => K.flatMap((c): Lin[] => [plusL({[x]: 1}, konstL(-c)), plusL({[x]: -1}, konstL(c))])), ...atoms])
  // the starts: random params (the precondition's), the state they begin in
  const cx: Ctx = {eqs: new Map(), arity: new Map(), values: {}, memo: new Map(), fuel: Infinity, depth: 0}, rand = seeded(31)
  for (let s = 0; s < 400; s++) {
    const big = [2, 8, 64, 1000, 1_000_000][s % 5]!, ps = Object.fromEntries(l.params.map(p => [p, rand(big + 1)]))
    if (l.pre && evC(cx, l.pre, ps) !== true) continue
    const st: Env = {...ps}
    for (const [x, e] of Object.entries(l.state)) st[x] = ev(cx, e, ps) ?? 0
    const n = rel.loc ? values.indexOf(st[rel.loc] ?? -1) : 0
    if (n < 0) continue
    const env = Object.fromEntries([...names].map(x => { const p = rel.ints.get(x); return [x, p ? st[p[0]]! - st[p[1]]! : st[x] ?? 0] }))
    cands[n] = cands[n]!.filter(c => valueAt(c, env) <= 0)
  }
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
    const best = new Map<string, Lin>(), rest: Lin[] = []
    for (const c of hs) {
      const xs = Object.keys(c).filter(x => x !== '1')
      if (xs.length !== 1) { rest.push(c); continue }
      const x = xs[0]!, key = `${x}${Math.sign(c[x]!)}`, b = (c['1'] ?? 0) / Math.abs(c[x]!), was = best.get(key)
      if (!was || b > (was['1'] ?? 0) / Math.abs(was[x]!)) best.set(key, c)
    }
    return [...best.values(), ...rest]
  }
  const closed = houdini(rel, cands, locOf, until)
  if (!closed || !closed.some(h => h.length)) return {why: 'no invariant'}
  let H = closed.map(tightest)
  const t1 = performance.now()
  let found = relationRank(l, rel, until, H)
  if (!('rank' in found)) return {why: `with ${H.flat().length} invariants: ${found.why}`}
  // fewer: a location's atoms at once, then one atom at a time, within ten times the first search's time
  const stop = Math.min(until, performance.now() + Math.max(500, 10 * (performance.now() - t1)))
  const without = (drop: (n: number, h: Lin) => boolean): boolean => {
    const fewer = houdini(rel, H.map((g, n) => g.filter(h => !drop(n, h))), locOf, stop)
    if (!fewer || fewer.flat().length === H.flat().length) return false
    const r = relationRank(l, rel, stop, fewer)
    if ('rank' in r) { H = fewer; found = r; return true }
    return false
  }
  for (const n of H.keys()) { if (performance.now() > stop) break; if (H[n]!.length) without(m => m === n) }
  for (const [n, hs] of H.map((h, n) => [n, [...h]] as const)) for (const h of hs) { if (performance.now() > stop) break; if (H[n]!.includes(h)) without((m, g) => m === n && g === h) }
  return {rank: found.rank, text: found.text, ...asLaws(H)}
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
  const {comps, left} = lexRanks([0], [node], samples, [...edges.values()], shared, until)
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
      if (performance.now() > until) break
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
    tried.push({rank: linear, verdict: withDeadline(until, () => goalsProven(loopObligations(l, laws, linear)))})
  }
  tried.push(...quadratic(read, until))
  const won = tried.find(t => 'trees' in t.verdict)
  if (won && 'trees' in won.verdict) return done(won.rank, won.verdict.trees)
  // The relation's rank (per location, in phases, its turns the relation's counterexamples), within half the time left.
  const rel = rankOfRelation(l, laws, performance.now() + (until - performance.now()) / 2)
  let relWhy = 'rank' in rel ? `the kernel refused ${rel.text}` : rel.why
  if (trace) console.error(`[cycles] ${l.name}: the relation's rank ${'rank' in rel ? rel.text : rel.why}`)
  if ('rank' in rel) {
    const verdict = withDeadline(until, () => goalsProven(loopObligations(l, laws, rel.rank)))
    if ('trees' in verdict) return done(rel.rank, verdict.trees)
    if (trace) console.error(`[cycles] ${l.name}: the kernel refused ${rel.text} at ${verdict.goal}`)
    relWhy = `the kernel refused ${rel.text.slice(0, 300)} at ${verdict.goal}`
  } else {
    // invariants first: the relation's rank where they hold, with as few of them as it needs
    const inv = rankWithInvariants(l, laws, performance.now() + (until - performance.now()) / 2)
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
    const ms = (until - performance.now()) * (rest.length ? 0.5 : 1)
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
  tried = quadratic(rest, Math.min(until, performance.now() + (opts.ms ?? 10_000) / 4))
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
  const t0 = performance.now(), until = t0 + (opts.ms ?? 10_000), rand = seeded(29), run = interpret(m)
  const names = [...Object.keys(m.state), ...m.params].sort(), helpful = livenessHelpful(l)
  const node: Node = {name: l.name, hyps: [], concl: yes, vars: names, level: 0, given: true}
  const env = (ps: Env, st: State): Env => ({...ps, ...st.scalars})
  const holds = (c: C, ps: Env, st: State) => { try { return evalMC(c, env(ps, st), st, m) } catch { return undefined } }
  const pending = (ps: Env, st: State) => holds(l.from, ps, st) === true && holds(l.to, ps, st) === false
  const points = new Map<string, Env>(), strong = new Map<string, Edge>(), weak = new Map<string, Edge>()
  for (const bound of [2, 4, 8, 16]) for (let trial = 0; trial < 20 && performance.now() < t0 + 1000; trial++) {
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
  const samples: Sampled[][] = [[...points.values()].map(env => ({env, calls: new Set()}))]
  const {comps, left} = lexRanks([0], [node], samples, [...strong.values()], shared, until, false, [...weak.values()])
  if (!comps.length || left) return {proven: false, checked: false, why: `no linear rank, in order, that ${strong.size} helpful steps sampled lower and ${weak.size} others keep`}
  const rank = comps.map(c => compE(c, 0, node, shared)), text = `(${rank.map(showE).join(', ')})`, lv: Liveness = {...l, rank}
  const first = withDeadline(until, () => proveLiveness(m, laws, lv))
  if (first.proven && first.checked) return {proven: true, checked: true, rank, laws: [], found: {rank: text, laws: []}}
  const ms = until - performance.now()
  if (ms > 300) {
    const {stay, cover, helps} = livenessParts(m, lv), inf = inferLaws(m, laws, [stay, cover, ...helps], {ms})
    const kept = inf.found.filter(f => !f.law.forall && !f.law.keys?.length), more = kept.map(f => f.law)
    if (inf.proven && more.length) {
      const again = withDeadline(until + 5000, () => proveLiveness(m, [...laws, ...more], lv))
      if (again.proven && again.checked) return {proven: true, checked: true, rank, laws: more, found: {rank: text, laws: kept.map(f => f.text)}}
    }
  }
  return {proven: false, checked: false, rank, found: {rank: text, laws: []}, ...(first.failed ? {goal: first.failed.goal, stuck: first.failed.stuck, ...(first.failed.witness ? {witness: first.failed.witness} : {})} : {}), why: `rank ${text} from the runs; the kernel's goals not proven with it`}
}

// --- functions a rule reads -----------------------------------------------------------------------------------------

// Lemmas about the functions a machine reads (those with facts and JavaScript, one argument): from the values, each a
// constant on a region below or above a threshold (a constant of the facts or the rule, ±1), a line, or bounds; proven
// from the facts as cyclic claims (Houdini: one not proven dropped), then the laws with those kept as facts, each
// dropped in turn where the laws don't need it.
export type LemmaFound = {law: Law, text: string}
export function cycleLemmas(m: Machine, laws: Law[], stepLaws: StepLaw[] = [], opts: {ms?: number} = {}): {proven: boolean, checked: boolean, machine?: Machine, found: LemmaFound[], proof?: Cyclic, why?: string} {
  const until = performance.now() + (opts.ms ?? 10_000)
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
    if (performance.now() >= until) break
    const o = findCycles(facts, [c], {ms: Math.min(1000, (until - performance.now()) * 0.1), values, houdini: true, generalize: false})
    if (o.proven && o.checked && o.proof) proofs.set(c.name, o.proof)
  }
  const ones = unique.filter(c => !two(c))
  if (!ones.length && !proofs.size) return {proven: false, checked: false, found: [], why: unique.length ? 'no lemma proven' : 'no lemma fits the values'}
  const out: CycleVerdict = ones.length ? findCycles(facts, ones, {ms: Math.max(0, until - performance.now()) * 0.6, values, houdini: true, generalize: false}) : {proven: true, checked: true, kept: []}
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
    if (performance.now() >= until) break
    const rest = found.filter(g => g !== f), again = proveWith(rest)
    if (again.ok) (found = rest, best = again)
  }
  const merged = sideBySide([...(out.proof && found.some(f => ones.some(c => c.name === f.text)) ? [out.proof] : []), ...found.flatMap(f => (proofs.has(f.text) ? [proofs.get(f.text)!] : []))])
  const proof = merged && checkCyclic(merged) ? merged : undefined
  return {proven: true, checked: true, machine: best.machine, found, ...(proof ? {proof} : {})}
}
