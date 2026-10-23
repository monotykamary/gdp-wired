// There exists: a law ∃ x. P(x) (core/machine.ts's Law with `some`: x a natural, or an integer as two, x and x$neg),
// proven through a witness. Nothing here is trusted: the kernel proves a plain law of a plain machine, and the Lean
// export states the existential again, proven by ⟨witness, proof⟩ (lean-kernel/Ghost.lean's some_updAll).
//   - a witness term (`terms`): a term of the state for each bound value; the law proven is P with the terms in place,
//     so at every reachable state the term's value is a witness
//   - a ghost (`ghost`): each bound value a state variable the machine gains, with a value at the start (over the
//     params) and after each step (over the state before, the request, the flags and the ghost's own value before);
//     the law proven is P over the ghosts. Read as a hypothesis, the law at the state before a step is P at the ghost's
//     value there: a fresh value for each existential and each step, the one the run carried, while the step's own
//     witness is the ghost's value after (Ghost.lean's sghost_reach: every reachable state of the machine is, outside
//     its ghosts, a reachable state of the machine with them, which no part of it reads)
// The prover finds the witness by counterexamples (the kernel's models of a goal it doesn't prove): candidates are 0, the
// params, the state, the values P's own atoms solve for (x = e, x <= e, x < e, as P reads them), and for a ghost its
// value before, shifts of it, the request's values and the state before; each is chosen to satisfy P at every
// counterexample so far, per case of the step (the conditions its updates split on: the request's clause, say).
// A law under a `forall` key takes witness terms only (a ghost per key would be a map).
import {type C, type E, type Law, type Machine, type SomeProof, type SomeWitness, type State, evalC, evalE, n as k, walk, x as v} from './machine.ts'
import {type Report, clock, proveLaw, proveLaws, withinDeadline} from '../kernel/prove.ts'
import {env} from './solver.ts'

type Env = Record<string, number>
// A bound value's naturals: [x], or an integer's [x, x$neg].
type Group = string[]
// A candidate for a group: one term per natural.
type Cand = E[]

const add = (a: E, b: E): E => (a.op === 'const' && a.value === 0 ? b : b.op === 'const' && b.value === 0 ? a : {op: 'add', a, b})
const sum = (es: E[]): E => es.reduce<E>((acc, e) => add(acc, e), k(0))
const sub = (a: E, b: E): E => (b.op === 'const' && b.value === 0 ? a : {op: 'sub', a, b})
const key = (x: unknown) => JSON.stringify(x)
export const namesOf = (t: E | C): string[] => [...new Set([...JSON.stringify(t).matchAll(/"op":"var","name":"([^"]+)"/g)].map(m => m[1]!))]
const readsMaps = (t: E | C): boolean => JSON.stringify(t).includes('"op":"get"')

// The groups of a law's bound naturals: an integer's x and x$neg together.
export function groupsOf(vars: string[]): Group[] {
  const out: Group[] = []
  for (const n of vars) if (!n.endsWith('$neg')) out.push(vars.includes(`${n}$neg`) ? [n, `${n}$neg`] : [n])
  for (const n of vars) if (n.endsWith('$neg') && !vars.includes(n.slice(0, -4))) out.push([n])
  return out
}

// Variables replaced by terms, structurally (Lean's substE/substC over variables: Kernel.lean), the rest as they are.
export function substVarsE(e: E, s: Record<string, E>): E {
  switch (e.op) {
    case 'var': return s[e.name] ?? e
    case 'const': return e
    case 'mul': return {...e, a: substVarsE(e.a, s)}
    case 'if': return {op: 'if', c: substVars(e.c, s), then: substVarsE(e.then, s), else: substVarsE(e.else, s)}
    case 'get': return {...e, key: substVarsE(e.key, s)}
    case 'add': case 'sub': case 'min': case 'max': case 'prod': return {...e, a: substVarsE(e.a, s), b: substVarsE(e.b, s)}
  }
}
export function substVars(c: C, s: Record<string, E>): C {
  switch (c.op) {
    case 'flag': return c
    case 'all': { const bound = [c.key, ...(c.keys ?? [])], inner = Object.fromEntries(Object.entries(s).filter(([n]) => !bound.includes(n))); return {...c, c: substVars(c.c, inner)} }
    case 'not': return {op: 'not', x: substVars(c.x, s)}
    case 'and': case 'or': return {op: c.op, xs: c.xs.map(y => substVars(y, s))}
    case '<': case '<=': case '=': return {...c, a: substVarsE(c.a, s), b: substVarsE(c.b, s)}
  }
}

// --- P's atoms, solved for a bound value -----------------------------------------------------------------------------

// A term linear in the bound naturals: their coefficients, and the rest as terms added (pos) and taken away (neg).
type Lin = {k: Record<string, number>, pos: E[], neg: E[]}
function lin(e: E, bound: Set<string>): Lin | undefined {
  const free = !namesOf(e).some(n => bound.has(n))
  switch (e.op) {
    case 'var': return bound.has(e.name) ? {k: {[e.name]: 1}, pos: [], neg: []} : {k: {}, pos: [e], neg: []}
    case 'const': return {k: {}, pos: e.value ? [e] : [], neg: []}
    case 'add': {
      const a = lin(e.a, bound), b = lin(e.b, bound)
      if (!a || !b) return undefined
      const out: Record<string, number> = {...a.k}
      for (const [n, c] of Object.entries(b.k)) out[n] = (out[n] ?? 0) + c
      return {k: out, pos: [...a.pos, ...b.pos], neg: [...a.neg, ...b.neg]}
    }
    case 'mul': {
      const a = lin(e.a, bound)
      if (!a) return undefined
      const scale = (es: E[]): E[] => es.map(x => (e.k === 1 ? x : {op: 'mul', k: e.k, a: x}))
      return {k: Object.fromEntries(Object.entries(a.k).map(([n, c]) => [n, c * e.k])), pos: scale(a.pos), neg: scale(a.neg)}
    }
    case 'sub': case 'min': case 'max': case 'prod': case 'if': case 'get': return free ? {k: {}, pos: [e], neg: []} : undefined
  }
}
// The atoms of P, each as Σ c·x ⋈ R+ − R− over the bound naturals.
type Atom = {op: '<' | '<=' | '=', k: Record<string, number>, plus: E[], minus: E[]}
function atomsOf(c: C, bound: Set<string>, out: Atom[] = []): Atom[] {
  switch (c.op) {
    case 'not': return atomsOf(c.x, bound, out)
    case 'and': case 'or': for (const y of c.xs) atomsOf(y, bound, out); return out
    case 'flag': case 'all': return out
    case '<': case '<=': case '=': {
      const a = lin(c.a, bound), b = lin(c.b, bound)
      if (!a || !b) return out
      const kk: Record<string, number> = {...a.k}
      for (const [n, x] of Object.entries(b.k)) kk[n] = (kk[n] ?? 0) - x
      for (const n of Object.keys(kk)) if (kk[n] === 0) delete kk[n]
      if (Object.keys(kk).length) out.push({op: c.op, k: kk, plus: [...b.pos, ...a.neg], minus: [...a.pos, ...b.neg]})
      return out
    }
  }
}
// The conjuncts of c that read a bound value, through and, and an or whose other parts read none (an implication's
// conclusion: a guard on the state).
function conjunctsOf(c: C, bound: Set<string>): C[] {
  const reads = (d: C) => namesOf(d).some(n => bound.has(n))
  if (c.op === 'and') return c.xs.flatMap(d => conjunctsOf(d, bound))
  if (c.op === 'or') { const rd = c.xs.filter(reads); if (rd.length === 1) return conjunctsOf(rd[0]!, bound) }
  return reads(c) ? [c] : []
}
// The values a group's atoms solve for, each with its neighbours: x = R+ − R− (or its negation), x + 1, x − 1.
function solved(atoms: Atom[], g: Group): Cand[] {
  const out: Cand[] = []
  for (const a of atoms) {
    const others = Object.keys(a.k).filter(n => !g.includes(n))
    if (others.length) continue
    const s = a.k[g[0]!] ?? 0
    if (Math.abs(s) !== 1 || (g.length === 2 && (a.k[g[1]!] ?? 0) !== -s) || (g.length === 1 && Object.keys(a.k).length !== 1)) continue
    const [hi, lo] = s === 1 ? [sum(a.plus), sum(a.minus)] : [sum(a.minus), sum(a.plus)]
    if (g.length === 2) out.push([hi, lo], [add(hi, k(1)), lo], [hi, add(lo, k(1))])
    else out.push([sub(hi, lo)], [add(sub(hi, lo), k(1))], [sub(sub(hi, lo), k(1))])
  }
  return out
}

// --- evaluating ∃ on a state ----------------------------------------------------------------------------------------

// Whether ∃ vars. P holds where env and st give every other value, with a witness: exact when the bound values are one
// natural or one integer read linearly (P's truth changes only next to the values its atoms solve for, so those, their
// neighbours, 0 and one past them are every case); otherwise found among those points, or undefined.
export function someHolds(body: C, vars: string[], env: Env, st: State, m: Machine): {holds: boolean, witness?: Env} | undefined {
  const groups = groupsOf(vars), bound = new Set(vars)
  const value = (e: E): number | undefined => { try { return evalE(e, env, st, m) } catch { return undefined } }
  const atoms = atomsOf(body, bound)
  const linearOnly = linearIn(body, bound)
  // A bound natural read as a map's key: the cells the maps hold, and one past them, are every case a read gives.
  const cells = new Set<number>()
  if (JSON.stringify(body).includes('"op":"get"')) for (const c of Object.values(st.maps)) for (const key of c.keys()) cells.add(key)
  const points = (g: Group): number[] => {
    const ps = new Set<number>([0, 1, ...cells, ...[...cells].map(c => c + 1)])
    for (const a of atoms) {
      const s = a.k[g[0]!] ?? 0, s2 = g.length === 2 ? (a.k[g[1]!] ?? 0) : 0
      if (!s || (g.length === 2 && s2 !== -s) || Object.keys(a.k).some(n => !g.includes(n))) continue
      const r = (sumOf(a.plus, value) ?? NaN) - (sumOf(a.minus, value) ?? NaN)
      if (!Number.isFinite(r)) continue
      for (const p of [Math.floor(r / s), Math.ceil(r / s)]) for (const d of [-1, 0, 1]) ps.add(p + d)
    }
    const xs = [...ps].filter(p => g.length === 2 || p >= 0)
    const hi = Math.max(...xs), lo = Math.min(...xs)
    return [...new Set([...xs, hi + 1, ...(g.length === 2 ? [lo - 1] : [])])].sort((a, b) => a - b)
  }
  const at = (g: Group, p: number): Env => (g.length === 2 ? {[g[0]!]: Math.max(p, 0), [g[1]!]: Math.max(-p, 0)} : {[g[0]!]: p})
  const test = (w: Env): boolean | undefined => { try { return evalC(body, {...env, ...w}, st, m) } catch { return undefined } }
  const lists = groups.map(points)
  let tried = 0, unknown = false
  const go = (i: number, w: Env): Env | undefined => {
    if (i === groups.length) { tried++; const t = test(w); if (t === undefined) unknown = true; return t ? w : undefined }
    for (const p of lists[i]!) { if (tried > 4096) return undefined; const hit = go(i + 1, {...w, ...at(groups[i]!, p)}); if (hit) return hit }
    return undefined
  }
  const hit = go(0, {})
  if (hit) return {holds: true, witness: hit}
  return groups.length === 1 && linearOnly && !unknown && tried <= 4096 ? {holds: false} : undefined
}
const sumOf = (es: E[], value: (e: E) => number | undefined): number | undefined => {
  let s = 0
  for (const e of es) { const x = value(e); if (x === undefined) return undefined; s += x }
  return s
}
// Every read of a bound natural is linear (through + and × by a constant only, up to an atom).
function linearIn(c: C, bound: Set<string>): boolean {
  switch (c.op) {
    case 'not': return linearIn(c.x, bound)
    case 'and': case 'or': return c.xs.every(y => linearIn(y, bound))
    case 'flag': return true
    case 'all': return !namesOf(c.c).some(n => bound.has(n))
    case '<': case '<=': case '=': return (lin(c.a, bound) !== undefined && lin(c.b, bound) !== undefined) || (onlyKeys(c.a, bound) && onlyKeys(c.b, bound))
  }
}
// Every read of a bound natural is a map's whole key (M[x]: piecewise constant, its pieces the cells).
function onlyKeys(e: E, bound: Set<string>): boolean {
  if (e.op === 'get' && e.key.op === 'var' && bound.has(e.key.name)) return true
  if (!namesOf(e).some(n => bound.has(n))) return true
  switch (e.op) {
    case 'var': case 'const': return false
    case 'add': case 'sub': case 'min': case 'max': case 'prod': return onlyKeys(e.a, bound) && onlyKeys(e.b, bound)
    case 'mul': return onlyKeys(e.a, bound)
    case 'if': return false
    case 'get': return false
  }
}

// --- choosing the witnesses -------------------------------------------------------------------------------------------

// A law's witness as chosen so far: terms (one candidate per group), or ghosts (a start per group, and per case of the
// step a candidate per group, -1 the case no condition picks).
type Pick = {mode: 'term', at: number[]} | {mode: 'ghost', start: number[], cases: Map<number, number[]>}
type Plan = {law: Law, groups: Group[], terms: Cand[][], starts: Cand[][], steps: Cand[][], pick: Pick, seen: {term: Env[], start: Env[], step: Map<number, {before: Env, after: Env}[]>}, given: boolean}

// The conditions a step splits on, in order: the if conditions along each update's else-chain.
function casesOf(m: Machine): C[] {
  const out = new Map<string, C>()
  for (const e of Object.values(m.step.state ?? {})) for (let t = e; t.op === 'if' && out.size < 64; t = t.else) if (!out.has(key(t.c))) out.set(key(t.c), t.c)
  return [...out.values()]
}
const caseAt = (cases: C[], env: Env, st: State, m: Machine): number => {
  for (const [i, c] of cases.entries()) { try { if (evalC(c, env, st, m)) return i } catch { return -1 } }
  return -1
}

function constantsOf(m: Machine): number[] {
  const out = new Set<number>([1, 2])
  walk(m.step, o => {
    if (o.op === 'const' && typeof o.value === 'number' && o.value > 0 && o.value <= 64) out.add(o.value)
    if (o.op === 'mul' && typeof o.k === 'number' && o.k > 1 && o.k <= 64) out.add(o.k)
  })
  return [...out].sort((a, b) => a - b).slice(0, 6)
}
const dedupe = (cs: Cand[]): Cand[] => [...new Map(cs.map(c => [key(c), c])).values()]
// The values of the machine's kinds a group may take: its naturals (an integer's two, x and x$neg), or a natural as an
// integer's positive part.
function valuesLike(g: Group, names: string[]): Cand[] {
  const out: Cand[] = []
  for (const n of names) {
    if (n.endsWith('$neg')) continue
    const neg = names.includes(`${n}$neg`)
    if (g.length === 2) out.push(neg ? [v(n), v(`${n}$neg`)] : [v(n), k(0)], ...(neg ? [[v(`${n}$neg`), v(n)]] : []))
    else out.push([v(n)])
  }
  return out
}

function planOf(m: Machine, law: Law): Plan {
  const vars = law.some!, groups = groupsOf(vars), bound = new Set(vars), atoms = atomsOf(law.holds, bound)
  const state = Object.keys(m.state), init: Record<string, E> = m.state
  const after: Record<string, E> = Object.fromEntries(state.map(n => [n, m.step.state?.[n] ?? v(n)]))
  const keyNames = law.forall ? [law.forall, ...(law.keys ?? [])] : []
  const shifts = constantsOf(m)
  const zero = (g: Group): Cand => g.map(() => k(0))
  const terms = groups.map(g => dedupe([...solved(atoms, g), zero(g), ...valuesLike(g, [...keyNames, ...state, ...m.params])]))
  // At the start: what P solves for over the start's values, 0, the params, the start's values.
  const starts = groups.map(g => dedupe([...solved(atoms, g).map(c => c.map(t => substVarsE(t, init))), zero(g), ...valuesLike(g, m.params), ...valuesLike(g, state).map(c => c.map(t => substVarsE(t, init)))]))
  // After a step: the ghost's value before, what P solves for over the state after, the request's values, shifts of
  // the value before, the state before, the params, 0.
  const steps = groups.map(g => {
    const own = g.length === 2 ? [v(g[0]!), v(g[1]!)] : [v(g[0]!)]
    const shifted: Cand[] = shifts.flatMap(d => (g.length === 2 ? [[add(own[0]!, k(d)), own[1]!], [own[0]!, add(own[1]!, k(d))]] : [[add(own[0]!, k(d))], [sub(own[0]!, k(d))]]))
    // (and the value before moved by one of the request's values, or of the state's: a witness that counts them)
    const by = (q: number, e: E): E => (q === 1 ? e : {op: 'mul', k: q, a: e})
    const moved: Cand[] = [1, 2, 3, 4].flatMap(q => valuesLike(g, [...m.inputs, ...state]).flatMap(c => (g.length === 2
      ? [[add(own[0]!, by(q, c[0]!)), add(own[1]!, by(q, c[1]!))], [add(own[0]!, by(q, c[1]!)), add(own[1]!, by(q, c[0]!))]]
      : [[add(own[0]!, by(q, c[0]!))], [sub(own[0]!, by(q, c[0]!))]])))
    const plain = dedupe([own, ...solved(atoms, g).map(c => c.map(t => substVarsE(t, after))), ...valuesLike(g, m.inputs), ...shifted, ...moved, ...valuesLike(g, [...state, ...m.params]), zero(g)])
    // (and the value before while it still works after the step, else one of those: P over the state after with every
    // ghost's value before as the condition, a witness that moves only when it must, a quotient's, say)
    if (readsMaps(law.holds)) return plain
    // (the condition: P's conjuncts that read this value and no other bound one, where there are some: a quotient's
    // range, say; else all of P)
    const mine = conjunctsOf(law.holds, bound).filter(c => { const ns = namesOf(c); return g.some(n => ns.includes(n)) && !ns.some(n => bound.has(n) && !g.includes(n)) })
    const keep = substVars(mine.length ? {op: 'and', xs: mine} : law.holds, after)
    return [...plain, ...plain.slice(1).map(t => t.map((x, j): E => ({op: 'if', c: keep, then: own[j]!, else: x})))]
  })
  const w = law.witness
  const given = !!(w?.terms || w?.ghost)
  // A witness given is the only one tried: the kernel proves the law with it or refuses it.
  if (w?.terms) groups.forEach((g, i) => { terms[i] = [g.map(n => w.terms![n] ?? k(0))] })
  if (w?.ghost) groups.forEach((g, i) => { starts[i] = [g.map(n => w.ghost![n]?.start ?? k(0))]; steps[i] = [g.map(n => w.ghost![n]?.step ?? v(n))] })
  return {law, groups, terms, starts, steps, pick: w?.ghost ? {mode: 'ghost', start: groups.map(() => 0), cases: new Map()} : {mode: 'term', at: groups.map(() => 0)}, seen: {term: [], start: [], step: new Map()}, given}
}

// The machine with every ghost the plans have chosen, and each law as the kernel proves it.
function built(m: Machine, plans: Plan[], cases: C[]): {machine: Machine, laws: Law[], ghosts: string[]} {
  const state = {...m.state}, step = {...m.step.state}, ghosts: string[] = []
  const laws = plans.map(p => {
    const {law} = p, ex: SomeProof = {vars: law.some!, body: law.holds}
    const plain: Law = {name: law.name, holds: law.holds, ...(law.forall ? {forall: law.forall} : {}), ...(law.keys ? {keys: law.keys} : {}), stated: law.stated ?? law.holds}
    if (p.pick.mode === 'term') {
      const pick = p.pick.at, sub: Record<string, E> = {}
      p.groups.forEach((g, i) => g.forEach((n, j) => { sub[n] = p.terms[i]![pick[i]!]![j]! }))
      return {...plain, holds: substVars(law.holds, sub), ex: {...ex, sub}}
    }
    const {start, cases: chosen} = p.pick
    p.groups.forEach((g, i) => g.forEach((n, j) => {
      state[n] = p.starts[i]![start[i]!]![j]!
      const dflt = p.steps[i]![chosen.get(-1)?.[i] ?? 0]![j]!
      step[n] = [...chosen.entries()].filter(([c]) => c >= 0).sort((a, b) => b[0] - a[0]).reduce<E>((acc, [c, at]) => ({op: 'if', c: cases[c]!, then: p.steps[i]![at[i]!]![j]!, else: acc}), dflt)
      ghosts.push(n)
    }))
    return {...plain, ex: {...ex, ghost: true as const}}
  })
  return {machine: {...m, state, step: {...m.step, state: step}}, laws, ghosts}
}

// A state's values for every name, 0 for a name it doesn't give (as the prover reads a model).
const total = (w: Env): Env => new Proxy(w, {get: (t, n) => (typeof n === 'string' ? (t[n] ?? 0) : undefined)})
const stOf = (w: Env, m: Machine): State => ({scalars: total(w), maps: Object.fromEntries(Object.keys(m.maps ?? {}).map(n => [n, new Map()])), defaults: {...m.maps}})
const evalOr = (e: E, env: Env, m: Machine): number | undefined => { try { return evalE(e, total(env), stOf(env, m), m) } catch { return undefined } }
const holdsOr = (c: C, env: Env, m: Machine): boolean | undefined => { try { return evalC(c, total(env), stOf(env, m), m) } catch { return undefined } }

// The candidates' indices, one per group, whose values satisfy `ok`: every group at the same index first (the lists
// are made alike, so one kind of witness for all: each quotient's, say), then one group moved from `from`, then in
// order of their sum (up to `cap` tried).
function firstFit(lists: Cand[][], ok: (cs: Cand[]) => boolean, from?: number[], cap = 20000): number[] | undefined {
  const n = lists.length, sizes = lists.map(l => l.length)
  const test = (pick: number[]) => ok(pick.map((x, j) => lists[j]![x]!))
  if (n > 1) {
    for (let x = 0; x < Math.min(...sizes); x++) { const pick = lists.map(() => x); if (test(pick)) return pick }
    if (from) for (let j = 0; j < n; j++) for (let x = 0; x < sizes[j]!; x++) { const pick = [...from]; pick[j] = x; if (test(pick)) return pick }
  }
  let tried = 0
  for (let s = 0; s <= sizes.reduce((a, b) => a + b, 0); s++) {
    const go = (i: number, left: number, at: number[]): number[] | undefined => {
      if (i === n - 1) { if (left >= sizes[i]!) return undefined; const pick = [...at, left]; if (++tried > cap) return undefined; return ok(pick.map((x, j) => lists[j]![x]!)) ? pick : undefined }
      for (let x = 0; x <= Math.min(left, sizes[i]! - 1); x++) { const hit = go(i + 1, left - x, [...at, x]); if (hit) return hit }
      return undefined
    }
    if (!n) return []
    const hit = go(0, s, [])
    if (hit || tried > cap) return hit
  }
  return undefined
}

export type SomeReport = Report & {laws?: Law[], machine?: Machine, ghosts?: string[], witnesses?: Record<string, string>, proof?: unknown}

// The laws with existentials proven through witnesses: chosen per law by the counterexamples the kernel gives, then the
// whole set proven as plain laws of the machine with its ghosts.
export function proveSome(m: Machine, laws: Law[], opts: {rounds?: number} = {}): SomeReport {
  const cases = casesOf(m), mapsRead = (l: Law) => readsMaps(l.holds) || !!m.maps || !!m.inputMaps
  // Each law's bound naturals named apart from the machine's names and from each other's (each may become a ghost).
  const taken = new Set([...m.params, ...m.inputs, ...Object.keys(m.state)])
  const plans = new Map<number, Plan>()
  laws.forEach((l, i) => {
    if (!l.some?.length) return
    const ren: Record<string, E> = {}
    for (const n of l.some) if (taken.has(n)) { let alt = `${n.replace(/\$neg$/, '')}~${i}`; if (n.endsWith('$neg')) alt += '$neg'; ren[n] = v(alt) }
    const named = Object.keys(ren).length ? {...l, holds: substVars(l.holds, ren), some: l.some.map(n => (ren[n] as {name: string} | undefined)?.name ?? n),
      ...(l.witness ? {witness: renamedWitness(l.witness, ren)} : {})} : l
    for (const n of named.some!) taken.add(n)
    plans.set(i, planOf(m, named))
  })
  const current = () => {
    const b = built(m, [...plans.values()], cases)
    const out = laws.map((l, i) => (plans.has(i) ? b.laws[[...plans.keys()].indexOf(i)]! : l))
    return {machine: b.machine, laws: out, ghosts: b.ghosts}
  }
  const rounds = opts.rounds ?? 24
  const log = env.GDP_EXISTS_LOG === '1'
  // Each law's witness until its goals are proven with every law assumed (choose); then the whole set, and where a
  // later choice broke a law proven before (a witness term is a hypothesis of every law), that law's again.
  const choose = (i: number, p: Plan, pass: number, first?: {goal: string, stuck: string, witness?: Record<string, number>}): SomeReport | undefined => {
    for (let round = 0; ; round++) {
      const now = current(), t0 = performance.now(), r: ReturnType<typeof proveLaw> = round === 0 && first ? {proven: false, ...first} : proveLaw(now.machine, now.laws, i)
      if (log) console.error(`exists: pass ${pass} round ${round} "${p.law.name}" ${p.pick.mode} ${describe(p, cases).slice(0, 160)}: ${r.proven ? 'proven' : `${r.goal} ${r.stuck}`} (${Math.round(performance.now() - t0)} ms)`)
      if (r.proven) return undefined
      const fail = (stuck: string): SomeReport => ({proven: false, nodes: 0, leaves: 0, checked: false, failed: {goal: r.goal, stuck, ...(r.witness ? {witness: r.witness} : {})}})
      // A witness given: the kernel proves the law with it, or refuses it here, with its counterexample.
      if (p.given) return {proven: false, nodes: 0, leaves: 0, checked: false, failed: {goal: r.goal, stuck: r.stuck, ...(r.witness ? {witness: r.witness} : {}), why: `the witness given for "${p.law.name}" does not prove it`}}
      if (withinDeadline(Infinity) <= clock()) return fail(`the deadline passed choosing a witness for "${p.law.name}" (${r.stuck})`)
      if (round >= rounds) return fail(`no witness found for "${p.law.name}" in ${rounds} rounds (${r.stuck}): name one (exists(kind, f, witness))`)
      if (r.stuck !== 'sat' || !r.witness) {
        if (p.pick.mode === 'term' && !p.law.forall && !p.given) { p.pick = {mode: 'ghost', start: p.groups.map(() => 0), cases: new Map()}; continue }
        return fail(r.stuck)
      }
      const w = r.witness, atStart = r.goal.endsWith('@start'), blind = mapsRead(p.law)
      // The state the goal fails at: the start (from the params), or the state after the step (from the state before,
      // the request and the flags), every ghost as the machine has it now.
      const env0 = {...w}
      if (p.law.forall) env0[p.law.forall] = w[`${p.law.forall}#`] ?? 0
      const st = atStart ? now.machine.state : Object.fromEntries(Object.keys(now.machine.state).map(n => [n, now.machine.step.state?.[n] ?? v(n)]))
      const after: Env = {...env0}
      for (const [n, e] of Object.entries(st)) { const x = evalOr(e, env0, now.machine); if (x !== undefined) after[n] = x }
      const at = (c: Cand[], g: Group[], env: Env): Env => Object.fromEntries(g.flatMap((gg, j) => gg.map((n, q) => [n, evalOr(c[j]![q]!, env, now.machine) ?? -1])))
      const sat = (vals: Env, env: Env) => !Object.values(vals).some(x => x < 0) && holdsOr(p.law.holds, {...env, ...vals}, now.machine) === true
      if (p.pick.mode === 'term') {
        p.seen.term.push(after)
        const old = p.pick.at
        const fit = blind ? nextBlind(p.terms, old) : firstFit(p.terms, cs => p.seen.term.every(e => sat(at(cs, p.groups, e), e)), old)
        if (fit && key(fit) !== key(old)) { p.pick = {mode: 'term', at: fit}; continue }
        if (!p.law.forall && !p.given) { p.pick = {mode: 'ghost', start: p.groups.map(() => 0), cases: new Map()}; continue }
        return fail(`no witness term found for "${p.law.name}" (${r.goal}): name one (exists(kind, f, witness))`)
      }
      if (atStart) {
        p.seen.start.push(after)
        const old = p.pick.start
        const fit = blind ? nextBlind(p.starts, old) : firstFit(p.starts, cs => p.seen.start.every(e => sat(at(cs, p.groups, e), e)), old)
        if (!fit || key(fit) === key(old)) return fail(`no witness at the start found for "${p.law.name}": name one (exists(kind, f, witness))`)
        p.pick.start = fit
        continue
      }
      const c = caseAt(cases, env0, stOf(env0, now.machine), now.machine), seen = p.seen.step.get(c) ?? []
      seen.push({before: env0, after})
      p.seen.step.set(c, seen)
      const old = p.pick.cases.get(c) ?? p.pick.cases.get(-1) ?? p.groups.map(() => 0)
      const fit = blind ? nextBlind(p.steps, old) : firstFit(p.steps, cs => seen.every(e => sat(at(cs, p.groups, e.before), e.after)), old)
      if (!fit || key(fit) === key(old)) return fail(`no witness after a step found for "${p.law.name}" (${cases[c] ? 'in one case of the step' : 'the step'}): name one (exists(kind, f, witness))`)
      p.pick.cases.set(c, fit)
    }
  }
  // Each law's witness from its two goals (choose), then the whole set; where a later choice broke a law proven before
  // (a witness term is a hypothesis of every law), that law's again from the whole set's counterexample, and so on.
  for (const [i, p] of plans) { const f = choose(i, p, 0); if (f) return f }
  for (let pass = 1; ; pass++) {
    const {machine, laws: plain, ghosts} = current(), t0 = performance.now()
    const out = proveLaws(machine, plain), done = {...out, laws: out.laws ?? plain, machine, ghosts, witnesses: Object.fromEntries([...plans.values()].map(p => [p.law.name, describe(p, cases)]))}
    if (log) console.error(`exists: pass ${pass} the whole set: ${out.proven ? 'proven' : `${out.failed?.goal} ${out.failed?.stuck}`} (${Math.round(performance.now() - t0)} ms)`)
    const j = out.proven || !out.failed || pass > 8 ? undefined : [...plans.keys()].find(k => out.failed!.goal.startsWith(`${laws[k]!.name} @`))
    if (j === undefined) return done
    const f = choose(j, plans.get(j)!, pass, out.failed!.stuck === 'sat' ? out.failed! : undefined)
    if (f) return f
  }
}
const renamedWitness = (w: SomeWitness, ren: Record<string, E>): SomeWitness => {
  const name = (n: string) => (ren[n] as {name: string} | undefined)?.name ?? n
  return {...(w.terms ? {terms: Object.fromEntries(Object.entries(w.terms).map(([n, t]) => [name(n), t]))} : {}),
    ...(w.ghost ? {ghost: Object.fromEntries(Object.entries(w.ghost).map(([n, g]) => [name(n), {start: g.start, step: substVarsE(g.step, ren)}]))} : {})}
}
// With no model to read (a law over maps), the next candidate in order, the first group's fastest.
function nextBlind(lists: Cand[][], at: number[]): number[] | undefined {
  const next = [...at]
  for (let i = 0; i < next.length; i++) { if (next[i]! + 1 < lists[i]!.length) { next[i]!++; return next } next[i] = 0 }
  return undefined
}

// How a law's witness reads, for the verdict.
function describe(p: Plan, cases: C[]): string {
  // (each bound value as w, or w1, w2, ...: its own name is the builder's)
  const names = new Map(p.groups.map((g, i) => [g[0]!, p.groups.length === 1 ? 'w' : `w${i + 1}`]))
  const rn = (e: E): E => substVarsE(e, Object.fromEntries(p.groups.flatMap(g => [[g[0]!, v(names.get(g[0]!)!)], ...(g[1] ? [[g[1], v(`${names.get(g[0]!)!}$neg`)]] : [])])))
  const show = (c: Cand) => (c.length === 2 ? `${showE(rn(c[0]!))} − ${showE(rn(c[1]!))}` : showE(rn(c[0]!)))
  const name = (g: Group) => names.get(g[0]!)!
  if (p.pick.mode === 'term') { const at = p.pick.at; return p.groups.map((g, i) => `${name(g)} = ${show(p.terms[i]![at[i]!]!)}`).join(', ') }
  const {start, cases: cs} = p.pick
  return p.groups.map((g, i) => `${name(g)} starts at ${show(p.starts[i]![start[i]!]!)}; after a step ${[...cs.entries()].filter(([c]) => c >= 0).map(([c, at]) => `${show(p.steps[i]![at[i]!]!)} where ${showC(cases[c]!)}`).join(', ')}${cs.size > (cs.has(-1) ? 1 : 0) ? ', else ' : ''}${show(p.steps[i]![cs.get(-1)?.[i] ?? 0]!)}`).join('; ')
}
export function showE(e: E): string {
  switch (e.op) {
    case 'var': return e.name
    case 'const': return String(e.value)
    case 'add': return `${showE(e.a)} + ${showE(e.b)}`
    case 'sub': return `(${showE(e.a)} ∸ ${showE(e.b)})`
    case 'mul': return `${e.k}·${showE(e.a)}`
    case 'prod': return `${showE(e.a)}·${showE(e.b)}`
    case 'min': case 'max': return `${e.op}(${showE(e.a)}, ${showE(e.b)})`
    case 'if': return `(${showC(e.c)} ? ${showE(e.then)} : ${showE(e.else)})`
    case 'get': return `${e.map}[${showE(e.key)}]`
  }
}
export function showC(c: C): string {
  switch (c.op) {
    case '<': case '<=': case '=': return `${showE(c.a)} ${c.op} ${showE(c.b)}`
    case 'and': return c.xs.map(showC).join(' ∧ ')
    case 'or': return `(${c.xs.map(showC).join(' ∨ ')})`
    case 'not': return `¬(${showC(c.x)})`
    case 'flag': return c.name
    case 'all': return `∀${c.key}. ${showC(c.c)}`
  }
}

// One law's two goals with its existentials' witnesses (core/infer.ts adds laws one at a time): the witnesses chosen
// for the whole set (proveSome), the law's goals proven over that machine.
export const someLaws = (laws: Law[]): boolean => laws.some(l => l.some?.length)
export type {SomeWitness}
