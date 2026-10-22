// Sanity: the observation table on research/frontier's cycle and lemma items, which findRank, findCycles, cycleLemmas,
// findLeadsTo and discover all prove today. `bun research/table/frontier.ts --item <id>` (`--list` prints the ids).
// Each item runs the existing search (its verdict and what it found) and then the table, sampled the way that search
// samples:
//   - loops (findRank's runs: params up to 2..32, 300 turns, seed 23): Q3 over the turns, in order (each class of
//     turns by its change, as a strict part, the rest weak), degree 2 with one product column at a time; the rank found
//     checked by the kernel's halting goals (loopObligations), alone and with Q2's bounds over the loop's states as laws
//   - claims over functions defined by equations (findCycles' grid: one variable 0..400, two 0..40, three 0..12): the
//     functions evaluated from their equations; a call the goal reads that no claim covers gets a companion claim, its
//     statement Q1 (an equation over its arguments and value) or else Q2 (the tightest bounds of value minus an
//     argument); then Q3 over the back-edges (a claim's arguments to those of the calls its function's body makes)
//   - rules reading functions known by their facts (cycleLemmas' values: one argument 0..2·big + 20, two on 0..24²):
//     Q1, Q2 over value minus argument(s), and Q5 split at the rule's constants ±1
//   - liveness (findLeadsTo's runs: helpful requests half the time): Q3 with the helpful turns strict, the others weak
//   - recurrences (discover's values, x = 0..40): Q1 over [1, x, x², x³, f] (closed forms), Q2 over f − s·x for the
//     slopes the values show, and over pairs of points (f(y) − f(x) for x ≤ y)
// One JSON line out: the existing search's verdict and found text, the table's answer, sizes and times.
import type {C, E, Law} from '../../core/machine.ts'
import {compileFunction, pairedArgs} from '../../core/machine.ts'
import type {Fact} from '../../kernel/cyclic.ts'
import {check, loopObligations, livenessHelpful, type Liveness, type Loop} from '../../kernel/kernel.ts'
import {grow, proveLiveness} from '../../kernel/prove.ts'
import {interpret, evalC as evalMC, evalE as evalME, type State} from '../../core/machine.ts'
import {type Claim, cycleLemmas, findCycles, findLeadsTo, findRank} from '../../core/cycles.ts'
import {discover} from '../../core/discover.ts'
import {claimCases, loopCases, ruleCases, liveCases, type Case, type LiveCase} from '../../examples/cycles.ts'
import {min, modBy, recur, rule, when, nat, oneOf} from '../../core/dsl.ts'
import {retries, retryLaws, retrySteps} from '../../examples/lemmas.ts'
import {type LpRow, type Pair, type Q, type Row, type Term, bounds, equalities, grammar, integral, lp, observe, showTerm} from './table.ts'

type Env = Record<string, number>
const args = process.argv.slice(2), opt = (k: string) => { const i = args.indexOf(k); return i < 0 ? undefined : args[i + 1] }
const seeded = (seed: number) => { let x = seed; return (n: number) => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * n) } }
const B = (x: number) => BigInt(x)

// --- an evaluator over the naturals (as the kernel reads them: subtraction truncated) -------------------------------------
type Call = {f: string, xs: number[]}
class Fuel extends Error {}
function ev(e: E, env: Env, call: (f: string, key: E, env: Env) => number): number {
  switch (e.op) {
    case 'var': { const v = env[e.name]; if (v === undefined) throw new Error(`no ${e.name}`); return v }
    case 'const': return e.value
    case 'add': return ev(e.a, env, call) + ev(e.b, env, call)
    case 'sub': return Math.max(0, ev(e.a, env, call) - ev(e.b, env, call))
    case 'mul': return e.k * ev(e.a, env, call)
    case 'prod': return ev(e.a, env, call) * ev(e.b, env, call)
    case 'min': return Math.min(ev(e.a, env, call), ev(e.b, env, call))
    case 'max': return Math.max(ev(e.a, env, call), ev(e.b, env, call))
    case 'if': return evc(e.c, env, call) ? ev(e.then, env, call) : ev(e.else, env, call)
    case 'get': return call(e.map, e.key, env)
  }
}
function evc(c: C, env: Env, call: (f: string, key: E, env: Env) => number): boolean {
  switch (c.op) {
    case '<': return ev(c.a, env, call) < ev(c.b, env, call)
    case '<=': return ev(c.a, env, call) <= ev(c.b, env, call)
    case '=': return ev(c.a, env, call) === ev(c.b, env, call)
    case 'and': return c.xs.every(x => evc(x, env, call))
    case 'or': return c.xs.some(x => evc(x, env, call))
    case 'not': return !evc(c.x, env, call)
    case 'all': case 'flag': throw new Error(`condition ${c.op}`)
  }
}
const noCall = (): number => { throw new Error('a call') }
const varsOf = (x: unknown): string[] => [...new Set([...JSON.stringify(x).matchAll(/"op":"var","name":"([^"]+)"/g)].map(m => m[1]!))].sort()

// --- Q3 in order: successive elimination ---------------------------------------------------------------------------------
// One component: an exact LP (table.ts's lp) over the rows of `strict` (drop ≥ 1, ≥ 0 before) and `weak` (no rise),
// coefficients within ±box when a box is given (findRank's box of 4 first, then none), solved on a spread of at most
// 40 rows with the violated ones added (constraint generation), the result checked on every row. With one location the
// constant is then the least that keeps every strict row's start ≥ 0 (0 where the coefficients alone do).
type Comp = {coefs: Map<string, bigint[]>, k: Map<string, bigint>}
let lpCalls = 0
const lexLog: string[] = []
function rankBox(strict: Pair[], weak: Pair[], locs: string[], n: number, box?: number): Comp | undefined {
  const L = locs.length, N = L * (n + 1), li = new Map(locs.map((l, i) => [l, i]))
  const rowsOf = (p: Pair, isStrict: boolean): LpRow[] => {
    const a: bigint[] = Array.from({length: N}, () => 0n), f = li.get(p.from)! * (n + 1), t = li.get(p.to)! * (n + 1)
    for (let j = 0; j < n; j++) { a[f + j]! += p.pre[j]!; a[t + j]! -= p.post[j]! }
    a[f + n]! += 1n; a[t + n]! -= 1n
    const out: LpRow[] = [{a, a0: 0n, b: isStrict ? 1n : 0n}]
    if (isStrict) { const g: bigint[] = Array.from({length: N}, () => 0n); for (let j = 0; j < n; j++) g[f + j] = p.pre[j]!; g[f + n] = 1n; out.push({a: g, a0: 0n, b: 0n}) }
    return out
  }
  const uniq = (rs: LpRow[]) => { const m = new Map<string, LpRow>(); for (const r of rs) m.set(`${r.a.join(',')}|${r.b}`, r); return [...m.values()] }
  const all = uniq([...strict.flatMap(p => rowsOf(p, true)), ...weak.flatMap(p => rowsOf(p, false))])
  if (!all.length) return undefined
  const boxRows: LpRow[] = box === undefined ? [] : Array.from({length: N}, (_, j) => j).filter(j => j % (n + 1) !== n).flatMap(j => {
    const e = (s: bigint) => Array.from({length: N}, (_, i) => (i === j ? s : 0n))
    return [{a: e(-1n), a0: 0n, b: B(-box)}, {a: e(1n), a0: 0n, b: B(-box)}]
  })
  let use = all.length <= 40 ? all : all.filter((_, i) => i % Math.ceil(all.length / 40) === 0)
  for (let round = 0; round < 25; round++) {
    lpCalls++
    const sol = lp([...use, ...boxRows], N)
    if (!sol) return undefined
    // the rational vertex rounded (then rounded up) to whole coefficients first (the box's integer search, as findRank's integer LP), the
    // constants taken up to the next whole number; else the vertex scaled to whole numbers
    const round = (x: Q): bigint => { const f = x.n / x.d - (x.n % x.d !== 0n && x.n < 0n ? 1n : 0n), r = x.n - f * x.d; return 2n * r >= x.d ? f + 1n : f }
    const ceil = (x: Q): bigint => { const f = x.n / x.d - (x.n % x.d !== 0n && x.n < 0n ? 1n : 0n); return x.n % x.d === 0n ? f : f + 1n }
    const rounded = sol.c.map((x, j) => (j % (n + 1) === n ? ceil(x) : round(x)))
    const z = integral(sol.c), scaled = z.length ? z : sol.c.map(() => 0n)
    const fit = (c: bigint[]): Comp | undefined => {
      if (c.every(x => x === 0n)) return undefined
      const coefs = new Map<string, bigint[]>(), k = new Map<string, bigint>()
      for (const [l, i] of li) { coefs.set(l, c.slice(i * (n + 1), i * (n + 1) + n)); k.set(l, c[i * (n + 1) + n]!) }
      if (L === 1) {
        const l = locs[0]!, cs = coefs.get(l)!
        let least: bigint | undefined
        for (const p of strict) { const v = cs.reduce((a, q, j) => a + q * p.pre[j]!, 0n); if (least === undefined || v < least) least = v }
        k.set(l, least === undefined || least >= 0n ? 0n : -least)
        c = [...cs, k.get(l)!]
      }
      const val = (r: LpRow) => r.a.reduce((acc, x, j) => acc + x * c[j]!, 0n)
      return all.every(r => val(r) >= r.b) ? {coefs, k} : undefined
    }
    const up = sol.c.map(x => ceil(x))
    const got = fit(rounded) ?? fit(up) ?? fit(scaled)
    if (got) return got
    const c = scaled, val = (r: LpRow) => r.a.reduce((acc, x, j) => acc + x * c[j]!, 0n)
    const bad = all.filter(r => val(r) < r.b)
    if (!bad.length) return undefined
    use = uniq([...use, ...bad.filter((_, i) => i % Math.max(1, Math.floor(bad.length / 15)) === 0).slice(0, 15)])
  }
  return undefined
}
// In order: all turns strict first; else each class of turns (by locations and which values fall, rise or stay) strict,
// the rest weak; the component found drops the turns it lowers (and the weak turns it lowers, as findLeadsTo), the rest
// go on. The box of 4 first, then none (as findRank).
function lex(pairs: Pair[], locs: string[], n: number, maxComps = 4, weak: Pair[] = []): Comp[] | undefined {
  for (const box of [4, undefined]) { const r = lexIn(pairs, locs, n, maxComps, box, dedupe(weak)); if (r) return r }
  return undefined
}
const valOf = (c: Comp, l: string, x: bigint[]) => c.coefs.get(l)!.reduce((a, q, j) => a + q * x[j]!, 0n) + c.k.get(l)!
function lexIn(pairs: Pair[], locs: string[], n: number, maxComps: number, box: number | undefined, weak0: Pair[]): Comp[] | undefined {
  let rest = dedupe(pairs), weak = weak0
  const comps: Comp[] = []
  while (rest.length) {
    if (comps.length >= maxComps) return undefined
    let got: Comp | undefined = rankBox(rest, weak, locs, n, box)
    if (!got) {
      const groups = new Map<string, Pair[]>()
      for (const p of rest) { const key = `${p.from}>${p.to}:${p.pre.map((x, j) => Math.sign(Number(x - p.post[j]!))).join(',')}`; groups.set(key, [...(groups.get(key) ?? []), p]) }
      const gs = [...groups.values()].sort((a, b) => b.length - a.length).slice(0, 16)
      for (const g of gs) { const s = new Set(g); got = rankBox(g, [...weak, ...rest.filter(p => !s.has(p))], locs, n, box); if (got) break }
    }
    if (!got) { lexLog.push(`box ${box ?? 'none'}: component ${comps.length + 1} not found, ${rest.length} turns left`); return undefined }
    const c = got
    const left = rest.filter(p => !(valOf(c, p.from, p.pre) - valOf(c, p.to, p.post) >= 1n && valOf(c, p.from, p.pre) >= 0n))
    if (left.length === rest.length) return undefined
    comps.push(c); rest = left
    weak = weak.filter(p => !(valOf(c, p.from, p.pre) - valOf(c, p.to, p.post) >= 1n))
  }
  return comps
}
// every pair lowers the tuple in order (some component drops by ≥ 1 from ≥ 0, those before it don't rise)
function lexHolds(comps: Comp[], pairs: Pair[]): number {
  let bad = 0
  for (const p of pairs) {
    let ok = false
    for (const c of comps) { const a = valOf(c, p.from, p.pre), b = valOf(c, p.to, p.post); if (a - b >= 1n && a >= 0n) { ok = true; break } if (b > a) break }
    if (!ok) bad++
  }
  return bad
}
function dedupe(ps: Pair[]): Pair[] { const m = new Map<string, Pair>(); for (const p of ps) m.set(`${p.from}|${p.to}|${p.pre.join(',')}|${p.post.join(',')}`, p); return [...m.values()] }
// a component as text and as a kernel term over the naturals (the negative part subtracted)
const colE = (c: string): E => { const m = /^(.+)·(.+)$/.exec(c); return m ? {op: 'prod', a: {op: 'var', name: m[1]!}, b: {op: 'var', name: m[2]!}} : {op: 'var', name: c} }
function compText(c: Comp, l: string, cols: string[]): string {
  const cs = c.coefs.get(l)!, k = c.k.get(l)!
  const parts = cs.flatMap((q, j) => (q ? [`${q === 1n ? '' : q === -1n ? '−' : `${q}·`}${cols[j]}`] : []))
  return [...parts, ...(k ? [String(k)] : [])].join(' + ').replace(/\+ −/g, '− ').replace(/\+ -/g, '− ') || '0'
}
function compE(c: Comp, l: string, cols: string[]): E {
  const cs = c.coefs.get(l)!, k = Number(c.k.get(l)!), pos: E[] = [], neg: E[] = []
  if (k > 0) pos.push({op: 'const', value: k})
  cs.forEach((q, j) => { const a = Number(q); if (!a) return; const t = Math.abs(a) === 1 ? colE(cols[j]!) : {op: 'mul' as const, k: Math.abs(a), a: colE(cols[j]!)}; (a > 0 ? pos : neg).push(t) })
  if (k < 0) neg.push({op: 'const', value: -k})
  const sum = (xs: E[]) => xs.reduce((s, x) => ({op: 'add', a: s, b: x}))
  return !pos.length ? {op: 'const', value: 0} : !neg.length ? sum(pos) : {op: 'sub', a: sum(pos), b: sum(neg)}
}
const showLin = (cs: [number, bigint][], k: bigint, op: string, names: string[]) => {
  const t = cs.map(([c, q]) => `${q === 1n ? '' : q === -1n ? '−' : `${q}·`}${names[c]}`).join(' + ').replace(/\+ −/g, '− ').replace(/\+ -/g, '− ')
  return op === '=' ? `${t} = ${-k}` : `${t} ≤ ${-k}`
}

// --- loops ------------------------------------------------------------------------------------------------------------
function loopTable(l: Loop) {
  const rand = seeded(23), state = Object.keys(l.state), names = [...state, ...l.params].sort()
  const points = new Map<string, Env>(), edges = new Map<string, [Env, Env]>()
  const t0 = performance.now()
  for (const bound of [2, 4, 8, 16, 32]) for (let trial = 0; trial < 40; trial++) {
    const ps: Env = Object.fromEntries(l.params.map(p => [p, rand(bound + 1)]))
    if (l.pre && !evc(l.pre, ps, noCall)) continue
    let st: Env = Object.fromEntries(state.map(s => [s, ev(l.state[s]!, ps, noCall)]))
    for (let turn = 0; turn < 300; turn++) {
      const here = {...ps, ...st}
      if (!evc(l.while, here, noCall)) break
      points.set(JSON.stringify(here), here)
      let inp: Env | undefined
      for (let tries = 0; tries < 20 && !inp; tries++) { const i = Object.fromEntries(l.inputs.map(x => [x, rand(bound + 1)])); if (!l.assume || evc(l.assume, {...here, ...i}, noCall)) inp = i }
      if (!inp) break
      const next: Env = {...st}
      for (const [s, e] of Object.entries(l.body)) next[s] = ev(e, {...here, ...inp}, noCall)
      const there = {...ps, ...next}
      if (evc(l.while, there, noCall)) edges.set(JSON.stringify([here, there]), [here, there])
      st = next
    }
  }
  const sampleMs = performance.now() - t0
  // Q2 over the loop's states: bounds of each variable and of each sum and difference of two (the invariants a rank needs)
  const rows: Row[] = [...points.values()].map(e => Object.fromEntries(names.map(x => [x, B(e[x]!)])))
  const terms = grammar(names, [], {upTo: 2}), tab = observe(terms, rows)
  const q2b = bounds(tab).map(b => ({term: terms[b.col]!, lo: b.lo, hi: b.hi}))
  const q2 = q2b.filter(b => b.lo > 0n).map(b => ({text: `${showTerm(b.term)} ≥ ${b.lo}`}))
  const tryRank = (cols: string[]) => {
    const vec = (e: Env) => cols.map(c => { const m = /^(.+)·(.+)$/.exec(c); return B(m ? e[m[1]!]! * e[m[2]!]! : e[c]!) })
    const pairs: Pair[] = [...edges.values()].map(([a, b]) => ({from: 'L', to: 'L', pre: vec(a), post: vec(b)}))
    return lex(pairs, ['L'], cols.length)
  }
  const tq = performance.now()
  // the kernel's halting goals for a rank, with Q2's bounds of the state's variables as laws (lower and upper), those
  // whose own goals fail dropped one at a time (Houdini, as findRank adds inferLaws' invariants); proven when every
  // goal is, with the laws left
  const cands: Law[] = q2b.filter(b => b.term.k === 'var' && state.includes((b.term as {name: string}).name)).flatMap(b => {
    const x = colE((b.term as {name: string}).name), out: Law[] = []
    if (b.lo > 0n) out.push({name: `${showTerm(b.term)} ≥ ${b.lo}`, holds: {op: '<=', a: {op: 'const', value: Number(b.lo)}, b: x}})
    out.push({name: `${showTerm(b.term)} ≤ ${b.hi}`, holds: {op: '<=', a: x, b: {op: 'const', value: Number(b.hi)}}})
    return out
  })
  const kernel = (cs: string[], c: Comp[]) => {
    const r = c.map(x => compE(x, 'L', cs))
    let laws = [...cands]
    for (;;) {
      const goals = loopObligations(l, laws, r)
      const bad = goals.find(g => { const o = grow(g); return !('tree' in o && check(g, o.tree)) })
      if (!bad) return laws.length ? `proven with ${laws.map(x => x.name).join(', ')}` : 'proven'
      const law = laws.find(x => bad.name.startsWith(x.name))
      if (!law) return `not proven (${bad.name})`
      laws = laws.filter(x => x !== law)
    }
  }
  // the linear rank first; where the kernel refuses it (or none fits), one product column at a time, the products the
  // loop's own terms read first (as findRank orders them), each fit checked by the kernel until one is proven
  const read = new Set([...JSON.stringify(l).matchAll(/"op":"prod","a":\{"op":"var","name":"([^"]+)"\},"b":\{"op":"var","name":"([^"]+)"\}/g)].map(m => [m[1]!, m[2]!].sort().join('·')))
  const products = names.flatMap((a, i) => names.slice(i).map(b => `${a}·${b}`)).sort((x, y) => Number(read.has(y)) - Number(read.has(x)))
  const answers: {rank: string, kernel: string, cols: number}[] = []
  const attempt = (cs: string[]) => { const c = tryRank(cs); if (!c) return false; const k = kernel(cs, c); answers.push({rank: `(${c.map(x => compText(x, 'L', cs)).join(', ')})`, kernel: k, cols: cs.length}); return k.startsWith('proven') }
  if (!attempt(names)) for (const p of products) { if (performance.now() - tq > 60_000) break; if (attempt([...names, p])) break }
  const queryMs = performance.now() - tq
  const won = answers.find(a => a.kernel.startsWith('proven'))
  return {rows: points.size, transitions: edges.size, cols: won?.cols ?? names.length, sampleMs: Math.round(sampleMs), queryMs: Math.round(queryMs), lps: lpCalls,
    answer: won ? won.rank : answers[0]?.rank ?? 'none', kernel: won?.kernel ?? answers[0]?.kernel ?? 'no rank fits', tried: answers.map(a => `${a.rank}: ${a.kernel}`), q2: q2.map(b => b.text).slice(0, 12)}
}

// --- functions defined by equations ----------------------------------------------------------------------------------------
// Each fact's equations f(pattern) = rhs, a pattern argument a variable, a variable plus a constant, or a constant.
type Pat = {kind: 'var', v: string} | {kind: 'plus', v: string, c: number} | {kind: 'const', c: number}
type Def = {f: string, pats: Pat[], rhs: E}
function defsOf(facts: Fact[]): Def[] {
  const out: Def[] = []
  const pat = (e: E): Pat | undefined => (e.op === 'var' ? {kind: 'var', v: e.name} : e.op === 'const' ? {kind: 'const', c: e.value} : e.op === 'add' && e.a.op === 'var' && e.b.op === 'const' ? {kind: 'plus', v: e.a.name, c: e.b.value} : undefined)
  const walk = (c: C) => {
    if (c.op === 'and') { c.xs.forEach(walk); return }
    if (c.op !== '=' || c.a.op !== 'get') return
    for (const n of [3, 2, 1]) {
      const as = pairedArgs(c.a.key, n), ps = as?.map(pat)
      if (as && ps && ps.every(Boolean)) { out.push({f: c.a.map, pats: ps as Pat[], rhs: c.b}); return }
    }
  }
  facts.forEach(f => walk(f.holds))
  // constants first (base cases), then shifted, then plain variables
  const w = (d: Def) => d.pats.reduce((s, p) => s + (p.kind === 'const' ? 0 : p.kind === 'plus' ? 1 : 2), 0)
  return out.sort((a, b) => w(a) - w(b))
}
function evaluator(defs: Def[], fuel = 200_000) {
  const memo = new Map<string, number>(), arity = new Map(defs.map(d => [d.f, d.pats.length]))
  let left = fuel
  const callKey = (f: string, key: E, env: Env, rec?: Call[]): number => {
    const as = pairedArgs(key, arity.get(f) ?? 1)!, xs = as.map(a => ev(a, env, (g, k2, e2) => callKey(g, k2, e2, rec)))
    rec?.push({f, xs})
    return value(f, xs)
  }
  const match = (d: Def, xs: number[]): Env | undefined => {
    const env: Env = {}
    for (const [i, p] of d.pats.entries()) {
      const x = xs[i]!
      if (p.kind === 'const') { if (x !== p.c) return undefined } else {
        const v = p.kind === 'var' ? x : x - p.c
        if (v < 0 || (p.v in env && env[p.v] !== v)) return undefined
        env[p.v] = v
      }
    }
    return env
  }
  const value = (f: string, xs: number[]): number => {
    const key = `${f}(${xs.join(',')})`, m = memo.get(key)
    if (m !== undefined) return m
    if (--left < 0) throw new Fuel('fuel')
    for (const d of defs) { if (d.f !== f) continue; const env = match(d, xs); if (!env) continue; const v = ev(d.rhs, env, (g, k2, e2) => callKey(g, k2, e2)); memo.set(key, v); return v }
    throw new Error(`no equation for ${key}`)
  }
  // the calls f's body makes at xs (one level down)
  const callsOf = (f: string, xs: number[]): Call[] => {
    for (const d of defs) { if (d.f !== f) continue; const env = match(d, xs); if (!env) continue; const rec: Call[] = []; ev(d.rhs, env, (g, k2, e2) => { const out: Call[] = []; const v = callKey(g, k2, e2, out); rec.push(...out); return v }); return rec }
    return []
  }
  // a top-level value or the calls at one point: the fuel counted afresh for each
  const top = <T>(f: () => T): T => { left = fuel; return f() }
  return {value: (f: string, xs: number[]) => top(() => value(f, xs)), callsOf: (f: string, xs: number[]) => top(() => callsOf(f, xs)), callKey}
}
const gridOf = (vars: string[], scale = 1): Env[] => {
  const top = Math.round((vars.length === 1 ? 400 : vars.length === 2 ? 40 : vars.length === 3 ? 12 : 6) * scale)
  return vars.reduce<Env[]>((acc, v) => acc.flatMap(e => Array.from({length: top + 1}, (_, i) => ({...e, [v]: i}))), [{}])
}
type CNode = {name: string, vars: string[], hyps: C[], f: string, args: E[], concl?: string}
function claimTable(c: Case) {
  const t0 = performance.now(), defs = defsOf(c.facts), E_ = evaluator(defs)
  const topCall = (cl: Claim): {f: string, key: E} | undefined => { let out: {f: string, key: E} | undefined; const find = (x: unknown) => { if (out || !x || typeof x !== 'object') return; const o = x as {op?: string, map?: string, key?: E}; if (o.op === 'get') { out = {f: o.map!, key: o.key!}; return } Object.values(o).forEach(find) }; find(cl.concl); return out }
  const arity = (f: string) => defs.find(d => d.f === f)!.pats.length
  const nodes: CNode[] = c.claims.map(cl => { const t = topCall(cl)!; return {name: cl.name, vars: varsOf([cl.concl, cl.hyps ?? []]), hyps: cl.hyps ?? [], f: t.f, args: pairedArgs(t.key, arity(t.f))!} })
  const companions: string[] = []
  // a companion for a function the claims don't read at plain variables (a call no claim covers): Q1 over its arguments
  // and value, else Q2's bounds of the value and of the value minus each argument
  const companion = (f: string): CNode => {
    const vs = Array.from({length: arity(f)}, (_, i) => `${f}$${i}`), rows: Row[] = []
    for (const env of gridOf(vs)) { try { rows.push({...Object.fromEntries(vs.map(v => [v, B(env[v]!)])), [f]: B(E_.value(f, vs.map(v => env[v]!)))}) } catch (e) { if (!(e instanceof Fuel) && !(e instanceof RangeError)) throw e } }
    const cols = [...vs, f], tab = observe(cols.map((name): Term => ({k: 'var', name})), rows)
    const eqs = equalities(tab).filter(l => l.coefs.some(([j]) => j === cols.length - 1))
    let text: string
    if (eqs.length) text = eqs.map(l => showLin(l.coefs, l.k, '=', cols)).join(', ')
    else {
      const ts: Term[] = [{k: 'var', name: f}, ...vs.map((v): Term => ({k: 'lin', terms: [[f, 1n], [v, -1n]]}))], tb = bounds(observe(ts, rows))
      text = tb.flatMap(b => [...(b.lo > 0n ? [`${showTerm(ts[b.col]!)} ≥ ${b.lo}`] : []), `${showTerm(ts[b.col]!)} ≤ ${b.hi}`]).join(', ')
    }
    companions.push(`${f}: ${text} (${rows.length} rows)`)
    const node: CNode = {name: `${f}$`, vars: vs, hyps: [], f, args: vs.map(v => ({op: 'var', name: v})), concl: text}
    nodes.push(node)
    return node
  }
  const width = 3
  const vec = (n: CNode, env: Env) => [...n.vars.map(v => B(env[v]!)), ...Array.from({length: width - n.vars.length}, () => 0n)]
  const matchNode = (n: CNode, call: Call): Env | undefined => {
    if (n.f !== call.f) return undefined
    const env: Env = {}
    for (const [i, a] of n.args.entries()) {
      const x = call.xs[i]!
      if (a.op === 'var') { if (a.name in env && env[a.name] !== x) return undefined; env[a.name] = x } else { try { if (ev(a, env, noCall) !== x) return undefined } catch { return undefined } }
    }
    return n.vars.every(v => v in env) && n.hyps.every(h => evc(h, env, noCall)) ? env : undefined
  }
  // back-edges: from a node at a grid point to the node whose call pattern a call its function's body makes there
  // matches (its hypotheses true there); companions made on the first grid only
  const edgesAt = (scale: number, grow: boolean): {pairs: Pair[], samples: number} => {
    const pairs: Pair[] = []
    let samples = 0
    for (let i = 0; i < nodes.length && i < 6; i++) {
      const n = nodes[i]!
      for (const env of gridOf(n.vars, scale)) {
        if (!n.hyps.every(h => evc(h, env, noCall))) continue
        let calls: Call[]
        try { const xs = n.args.map(a => ev(a, env, noCall)); calls = E_.callsOf(n.f, xs); E_.value(n.f, xs) } catch (e) { if (e instanceof Fuel || e instanceof RangeError) continue; throw e }
        samples++
        for (const call of calls) {
          let target: [CNode, Env] | undefined
          for (const m of nodes) { const e2 = matchNode(m, call); if (e2) { target = [m, e2]; break } }
          if (!target && grow && !nodes.some(m => m.f === call.f && m.args.every(a => a.op === 'var'))) { const m = companion(call.f); const e2 = matchNode(m, call); if (e2) target = [m, e2] }
          if (target) pairs.push({from: n.name, to: target[0].name, pre: vec(n, env), post: vec(target[0], target[1])})
        }
      }
    }
    return {pairs, samples}
  }
  const {pairs, samples} = edgesAt(1, true)
  const sampleMs = performance.now() - t0, tq = performance.now()
  // held out: the grid half again as wide, its edges the check on what the first grid fits (the kernel's place here)
  const held = edgesAt(1.5, false)
  const locs = nodes.map(n => n.name)
  const tried: string[] = []
  const name = (n: CNode, extra?: string) => [...n.vars, ...Array.from({length: width - n.vars.length}, () => '_'), ...(extra ? [extra] : [])]
  const show = (comps: Comp[], extra?: [CNode, string]) => nodes.filter(n => pairs.some(p => p.from === n.name)).map(n => `${n.name}: (${comps.map(q => compText(q, n.name, name(n, extra && extra[0] === n ? extra[1] : extra ? '_' : undefined))).join(', ')})`).join('; ')
  let answer = 'none', heldBad = -1
  const comps = lex(pairs, locs, width)
  if (comps) { heldBad = lexHolds(comps, held.pairs); tried.push(`${show(comps)}: ${heldBad} of ${held.pairs.length} held-out edges not lowered`); if (!heldBad) answer = show(comps) }
  if (answer === 'none') {
    // degree 2: a product of two of the first claim's variables as one more column
    const n = nodes[0]!, prodOf = (p: Pair, at: 'pre' | 'post', a: string, b: string) => ((at === 'pre' ? p.from : p.to) === n.name ? p[at][n.vars.indexOf(a)]! * p[at][n.vars.indexOf(b)]! : 0n)
    for (const [a, b] of n.vars.flatMap((a, i) => n.vars.slice(i).map(b => [a, b] as const))) {
      const ext = (ps: Pair[]) => ps.map(p => ({...p, pre: [...p.pre, prodOf(p, 'pre', a, b)], post: [...p.post, prodOf(p, 'post', a, b)]}))
      const c2 = lex(ext(pairs), locs, width + 1)
      if (!c2) continue
      const bad = lexHolds(c2, ext(held.pairs))
      tried.push(`${show(c2, [n, `${a}·${b}`])}: ${bad} of ${held.pairs.length} held-out edges not lowered`)
      if (!bad) { answer = show(c2, [n, `${a}·${b}`]); heldBad = 0; break }
    }
  }
  const queryMs = performance.now() - tq
  return {rows: samples, transitions: dedupe(pairs).length, heldOut: held.pairs.length, cols: width, sampleMs: Math.round(sampleMs), queryMs: Math.round(queryMs), lps: lpCalls, answer, tried, companions}
}

// --- rules reading functions known by their facts (their JavaScript) ---------------------------------------------------------
function ruleTable(r: {machine: {fns?: Record<string, {js: string, arity?: number, call?: string, recur?: unknown}>}}, consts: number[]) {
  const out: string[] = []
  const t0 = performance.now()
  let rowsN = 0, colsN = 0
  for (const [name, f] of Object.entries(r.machine.fns ?? {})) {
    if (f.recur) continue
    const ar = f.arity ?? 1
    const g = ar === 1 ? compileFunction<() => (k: number) => number>([], `return (${f.js})`)() : compileFunction<() => (a: number, b: number) => number>([], `return (${f.call})`)()
    const big = Math.max(0, ...consts.filter(c => c <= 1000))
    const vs = ar === 1 ? ['k'] : ['k', 'j']
    const pts = ar === 1 ? Array.from({length: 2 * big + 21}, (_, k) => [k]) : Array.from({length: 25 * 25}, (_, i) => [Math.floor(i / 25), i % 25])
    const rows: Row[] = pts.map(p => ({...Object.fromEntries(vs.map((v, i) => [v, B(p[i]!)])), [name]: B((g as (...a: number[]) => number)(...p))}))
    const cols = [...vs, name], tab = observe(cols.map((n): Term => ({k: 'var', name: n})), rows)
    rowsN += rows.length; colsN += cols.length
    const eqs = equalities(tab).filter(l => l.coefs.some(([j]) => j === cols.length - 1))
    for (const l of eqs) out.push(`${showLin(l.coefs, l.k, '=', cols)} (Q1)`)
    if (!eqs.length) {
      // Q2: the value, and the value minus each argument and minus their sum
      const ts: Term[] = [{k: 'var', name}, ...vs.map((v): Term => ({k: 'lin', terms: [[name, 1n], [v, -1n]]})), ...(vs.length > 1 ? [{k: 'lin', terms: [[name, 1n], ...vs.map((v): [string, bigint] => [v, -1n])]} as Term] : [])]
      colsN += ts.length
      for (const b of bounds(observe(ts, rows))) out.push(`${showTerm(ts[b.col]!)} ≤ ${b.hi} (Q2)`)
      // Q5 (one argument): split at k ≤ t for the rule's constants ±1, a part where the value is constant
      const ts5 = [...new Set(consts.flatMap(c => [c - 1, c, c + 1]).filter(c => c >= 0))].sort((a, b) => a - b)
      if (ar === 1) for (const t of ts5) {
        const lo = rows.filter(rw => rw.k! <= B(t)), hi = rows.filter(rw => rw.k! > B(t))
        const vals = new Set(lo.map(rw => rw[name]!))
        if (lo.length > 1 && vals.size === 1 && hi.length) out.push(`${name}(k) = ${[...vals][0]} for k ≤ ${t} (Q5)`)
      }
    }
  }
  // keep the Q5 constant region that is largest (the threshold furthest out)
  const q5 = out.filter(s => s.endsWith('(Q5)')), last = q5.at(-1)
  return {rows: rowsN, cols: colsN, sampleMs: 0, queryMs: Math.round(performance.now() - t0), answer: [...out.filter(s => !s.endsWith('(Q5)')), ...(last ? [last] : [])].join('; ') || 'none'}
}

// --- liveness -------------------------------------------------------------------------------------------------------------
function liveTable(c: LiveCase) {
  const m = c.r.machine, rand = seeded(29), run = interpret(m), names = [...Object.keys(m.state), ...m.params].sort(), helpful = livenessHelpful(c.live)
  const env = (ps: Env, st: State): Env => ({...ps, ...st.scalars})
  const holds = (x: C, ps: Env, st: State) => { try { return evalMC(x, env(ps, st), st, m) } catch { return undefined } }
  const pending = (ps: Env, st: State) => holds(c.live.from, ps, st) === true && holds(c.live.to, ps, st) === false
  const strong: Pair[] = [], weak: Pair[] = []
  const vec = (e: Env) => names.map(x => B(e[x]!))
  const t0 = performance.now()
  for (const bound of [2, 4, 8, 16]) for (let trial = 0; trial < 20; trial++) {
    let ps: Env
    try { ps = c.r.randomParams(rand, bound) } catch { continue }
    let st: State
    try { st = run.init(ps) } catch { continue }
    for (let turn = 0; turn < 120; turn++) {
      const here = env(ps, st), was = pending(ps, st)
      const regions = helpful.filter(h => holds(h.when, ps, st) === true), h = regions.length && rand(2) ? regions[rand(regions.length)]! : undefined
      let next: State | undefined
      for (let tries = 0; tries < 20 && !next; tries++) {
        try {
          const input = c.r.randomInput(rand, bound, ps) as Record<string, number>
          if (h) for (const [x, t] of Object.entries(h.request)) input[x] = evalME(t, here, st, m)
          next = run.step(ps, st, input as never)
        } catch { /* refused */ }
      }
      if (!next) break
      if (was && pending(ps, next)) (h ? strong : weak).push({from: 'L', to: 'L', pre: vec(here), post: vec(env(ps, next))})
      st = next
    }
  }
  const sampleMs = performance.now() - t0, tq = performance.now()
  // in order: the helpful turns strict, each component dropping some, the others (weak) never rising
  const comps = lex(strong, ['L'], names.length, 4, weak) ?? []
  const queryMs = performance.now() - tq
  const ok = comps.length > 0
  let kernel = 'no rank fits'
  if (ok) {
    const r = comps.map(q => compE(q, 'L', names)), laws = [...c.r.kindLaws().filter(k => !c.laws.some(l => l.name === k.name)), ...c.laws]
    const o = proveLiveness(m, laws, {...c.live, rank: r} as Liveness)
    kernel = o.proven && o.checked ? 'proven' : 'not proven'
  }
  return {rows: strong.length + weak.length, transitions: dedupe(strong).length + dedupe(weak).length, cols: names.length, sampleMs: Math.round(sampleMs), queryMs: Math.round(queryMs),
    answer: ok ? `(${comps.map(q => compText(q, 'L', names)).join(', ')})` : 'none', kernel}
}

// --- recurrences (discover's lemma track) -----------------------------------------------------------------------------------
function recurTable(d: {js: string | ((...a: number[]) => number)}) {
  const f = (typeof d.js === 'function' ? d.js : compileFunction<() => (x: number) => number>([], `return (${d.js})`)()) as (x: number) => number
  const t0 = performance.now(), rows: Row[] = []
  for (let x = 0; x <= 40; x++) { let y: number; try { y = f(x) } catch { break } rows.push({x: B(x), xx: B(x * x), xxx: B(x * x * x), f: B(y)}) }
  const out: string[] = []
  // Q1: closed forms over [1, x, x², x³, f] (an equation reading f)
  const cols = ['x', 'xx', 'xxx', 'f'], terms = grammar(cols, []), tab = observe(terms, rows), names = ['x', 'x²', 'x³', 'f(x)']
  const eqs = equalities(tab, [0, 1, 2, 3]).filter(l => l.coefs.some(([j]) => j === 3))
  for (const l of eqs) out.push(`${showLin(l.coefs, l.k, '=', names)} (Q1)`)
  // Q2: f and f − s·x for the slopes the values show (the gentlest three and the steepest, as discover takes them)
  const slopes = [...new Set(rows.slice(1).map((r, i) => Number(r.f! - rows[i]!.f!)).filter(s => s > 0))].sort((a, b) => a - b)
  const picked = [...new Set([...slopes.slice(0, 3), ...slopes.slice(-1)])]
  const q2: Term[] = [{k: 'var', name: 'f'}, ...picked.map((s): Term => ({k: 'lin', terms: [['f', 1n], ['x', B(-s)]]}))]
  const t2 = observe(q2, rows)
  if (!eqs.length) for (const b of bounds(t2)) out.push(`${b.lo} ≤ ${showTerm(q2[b.col]!).replace('f', 'f(x)')} ≤ ${b.hi} (Q2)`)
  // Q2 between two points (x ≤ y): f(y) − f(x)
  const pr: Row[] = []
  for (const a of rows) for (const b of rows) if (a.x! <= b.x!) pr.push({d: b.f! - a.f!})
  const tb = bounds(observe([{k: 'var', name: 'd'}], pr))[0]!
  if (!eqs.length) out.push(`f(y) − f(x) ≥ ${tb.lo} for x ≤ y (Q2 on pairs)`)
  return {rows: rows.length, pairs: pr.length, cols: terms.length + q2.length + 1, sampleMs: 0, queryMs: Math.round(performance.now() - t0), answer: out.join('; ')}
}

// --- the items ------------------------------------------------------------------------------------------------------------------
const consts = (x: unknown) => [...new Set([...JSON.stringify(x).matchAll(/"value":(\d+)/g)].map(m => Number(m[1])))]
const twos = () => recur('twos', {zero: 0, next: (x, y) => when(x.lt(5), y.plus(2), y)}, {})
const leftovers = () => recur('leftovers', {fns: {rem: modBy(7)}, zero: 0, next: (x, l, {rem}) => l.plus(rem(x))}, {})
const growing = () => recur('growing', {zero: 1, next: (_, d) => min(d.times(2), 64)}, {})
const squares = () => recur('squares', {zero: 0, next: (x, p) => p.plus(x.times(2)).plus(1)}, {})
const pyramid = () => recur('pyramid', {zero: 0, next: (x, p) => p.plus(x.plus(1).mul(x.plus(1)))}, {})
type LemmaItem = {r: {parts: {fns: [string, {js: string | ((...a: number[]) => number), recur?: unknown}][]}}, laws: Law[], steps?: never[]}
const lemmaItems: Record<string, () => LemmaItem> = {
  'retry with backoff': () => { const r = retries('states no lemma'); return {r, laws: retryLaws(r), steps: retrySteps(r)} as never },
  'two by two': () => { const r = rule('two by two').inputs({}).state({n: 0, v: 0}).fns({twos: twos()}).step(({n, twos}) => ({n: n.plus(1), v: twos(n.plus(1))})); return {r, laws: [r.law('the value is at most 10', ({v}) => v.atMost(10))]} as never },
  'leftover ledger': () => { const r = rule('leftover ledger').inputs({}).state({day: 0, total: 0}).fns({left: leftovers()}).step(({day, left}) => ({day: day.plus(1), total: left(day.plus(1))})); return {r, laws: [r.law('at most 6 a day so far', ({total, day}) => total.atMost(day.times(6)))]} as never },
  'escalation': () => { const r = rule('escalation').params({start: nat}).inputs({up: oneOf('stay', 'up')}).state({level: ({start}) => start}).fns({delay: growing()}).step(({up, level}) => ({level: when(up.is('up'), level.plus(1), level)})); return {r, laws: [r.law('never below the start', ({level, start}) => start.atMost(level)), r.law('the delay is at least where it started', ({level, start, delay}) => delay(start).atMost(delay(level)))]} as never },
  'area': () => { const r = rule('area').inputs({}).state({n: 0, a: 0}).fns({sq: squares()}).step(({n, sq}) => ({n: n.plus(1), a: sq(n.plus(1))})); return {r, laws: [r.law('the area is n·n', ({a, n}) => a.eq(n.mul(n)))]} as never },
  'pyramid': () => { const r = rule('pyramid').inputs({}).state({n: 0, a: 0}).fns({sq: pyramid()}).step(({n, sq}) => ({n: n.plus(1), a: sq(n.plus(1))})); return {r, laws: [r.law('six times the sum of the squares', ({a, n}) => a.times(6).eq(n.mul(n).mul(n).times(2).plus(n.mul(n).times(3)).plus(n)))]} as never },
}
type Run = () => Record<string, unknown>
const items = new Map<string, Run>()
const time = <T>(f: () => T): [T, number] => { const t = performance.now(), v = f(); return [v, Math.round(performance.now() - t)] }
for (const [c, ok] of claimCases()) if (ok) items.set(`cycle/${c.name}`, () => {
  const [out, ms] = time(() => findCycles(c.facts, c.claims))
  return {existing: {search: 'findCycles', proven: out.proven && out.checked, ms, found: out.found ? [...Object.entries(out.found.ranks).map(([n, r]) => `${n}: ${r}`), ...out.found.companions] : []}, table: claimTable(c)}
})
for (const [l, ok] of loopCases()) if (ok) items.set(`cycle/loop: ${l.loop.name}`, () => {
  const [out, ms] = time(() => findRank(l.loop, []))
  return {existing: {search: 'findRank', proven: out.proven && out.checked, ms, found: out.found ? [`rank ${out.found.rank}`, ...out.found.laws] : []}, table: loopTable(l.loop)}
})
for (const [{r, laws}, ok] of ruleCases()) if (ok) items.set(`cycle/rule: ${r.machine.name}`, () => {
  const [out, ms] = time(() => cycleLemmas(r.machine, laws))
  return {existing: {search: 'cycleLemmas', proven: out.proven && out.checked, ms, found: out.found.map(f => f.text)}, table: ruleTable(r as never, consts([r.machine, laws]))}
})
for (const [c, ok] of liveCases()) if (ok) items.set(`cycle/liveness: ${c.name}: ${c.live.name}`, () => {
  const laws = [...c.r.kindLaws().filter(k => !c.laws.some(l => l.name === k.name)), ...c.laws]
  const [out, ms] = time(() => findLeadsTo(c.r.machine, laws, c.live, {params: (rand, bound) => c.r.randomParams(rand, bound), input: (rand, bound, ps) => c.r.randomInput(rand, bound, ps)}))
  return {existing: {search: 'findLeadsTo', proven: out.proven && out.checked, ms, found: out.found ? [`rank ${out.found.rank}`, ...out.found.laws] : []}, table: liveTable(c)}
})
for (const [id, build] of Object.entries(lemmaItems)) items.set(`lemma/${id}`, () => {
  const {r, laws, steps} = build()
  const [out, ms] = time(() => discover(r as never, laws, steps ?? []))
  const found = Object.entries(out.found).flatMap(([n, f]) => [...(f.lemmas ?? []), ...(f.between ?? [])].map(t => `${n}: ${t}`))
  const tables = r.parts.fns.filter(([, d]) => d.recur).map(([n, d]) => ({fn: n, ...recurTable(d)}))
  return {existing: {search: 'discover', proven: out.verdict.proven && out.verdict.checked, ms, found}, table: tables}
})

if (args.includes('--list')) { for (const k of items.keys()) console.log(k); process.exit(0) }
const id = opt('--item')!, run = items.get(id)
if (!run) { console.log(JSON.stringify({item: id, error: 'no such item'})); process.exit(1) }
const t = performance.now()
console.log(JSON.stringify({item: id, ...run(), lexLog: lexLog.slice(0, 20), ms: Math.round(performance.now() - t)}))
