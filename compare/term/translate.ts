// An ARI integer transition system as a gdp-wired loop (kernel.ts's Loop, what `proveLoop` proves halts), the same
// statement: every run from the entrypoint, at any integers, ends.
//
// The state: `pc`, the location (its index), and each argument slot j as a pair of naturals (s<j>, s<j>$n), the integer
// s<j> − s<j>$n, at most one of them nonzero (every step writes P ∸ N and N ∸ P for the value P − N). The params are
// the entrypoint's integers, as pairs (a<j>, a<j>$n): every integer is one, so the loop starts where the task's runs
// do, at any integers. A turn's inputs: `t`, which of the rules leaving the location fires (its index among them), and
// the values the rule leaves free, as pairs (i<m>, i<m>$n). The assumption: the rule named is at the location and its
// guard holds of the state and the inputs; the loop runs while the location has a rule leaving it, and a state where
// no rule's guard holds has no turn (the run ends there, as the task's does). So every run of the task is a run of the
// loop and back, value for value: the loop halts from every start exactly when the task terminates.
//
// Each rule is planned first: a left-side variable names its slot (a repeated one, or a term, is an equation on the
// slot); an equation that gives a free variable as a term of known ones defines it (x' = x + 1, or solved for a
// variable with coefficient ±1); a variable left (a temporary, a post value with only bounds) becomes an input; the
// conjuncts not used as definitions are the guard. `exists` at the top of a guard binds inputs too. div and mod by a
// constant k take one input q each: the term is q (div) or e − k·q (mod), with 0 <= e − k·q < |k| in the guard.
// Products of two variables are kernel products (monomials). Refused, with the reason: exists under or/not, or binding
// a name the rule uses elsewhere; div/mod by a non-constant; ite and abs in a term; the parse's own refusals
// (ari.ts: a location inside a term, other sorts).
import {type Ari, type Env, type Rule, type Sx, Unsupported, evalInt, isNum, isVar, ruleVars} from './ari.ts'
import type {C, E} from '../../core/machine.ts'
import type {Loop} from '../../kernel/kernel.ts'

// --- terms, with the constants folded -------------------------------------------------------------------------------
const K = (value: number): E => ({op: 'const', value})
const V = (name: string): E => ({op: 'var', name})
const isK = (e: E, v?: number) => e.op === 'const' && (v === undefined || e.value === v)
// Folded exactly (in BigInt): a constant past 2^53, which the kernel's numbers can't hold, refuses the task.
const exact = (x: bigint): E => {
  if (x > BigInt(Number.MAX_SAFE_INTEGER) || -x > BigInt(Number.MAX_SAFE_INTEGER)) throw new Unsupported(`a constant past 2^53: ${x}`)
  return K(Number(x))
}
const add = (a: E, b: E): E => (isK(a, 0) ? b : isK(b, 0) ? a : a.op === 'const' && b.op === 'const' ? exact(BigInt(a.value) + BigInt(b.value)) : {op: 'add', a, b})
const sub = (a: E, b: E): E => (isK(b, 0) ? a : a.op === 'const' && b.op === 'const' ? K(Math.max(0, a.value - b.value)) : isK(a, 0) ? K(0) : {op: 'sub', a, b})
const mul = (k: number, a: E): E => (k === 0 || isK(a, 0) ? K(0) : k === 1 ? a : a.op === 'const' ? exact(BigInt(k) * BigInt(a.value)) : {op: 'mul', k, a})
const prod = (a: E, b: E): E => (a.op === 'const' ? mul(a.value, b) : b.op === 'const' ? mul(b.value, a) : {op: 'prod', a, b})
const and = (xs: C[]): C => { const ys = xs.flatMap(x => (x.op === 'and' ? x.xs : [x])); return ys.length === 1 ? ys[0]! : {op: 'and', xs: ys} }
const or = (xs: C[]): C => (xs.length === 1 ? xs[0]! : {op: 'or', xs})
const eqN = (a: E, b: E): C => ({op: '=', a, b})
const TRUE: C = {op: '<=', a: K(0), b: K(0)}

// An integer as a pair of naturals: p − n.
type I = {p: E, n: E}
const iconst = (k: bigint): I => {
  if (k > BigInt(Number.MAX_SAFE_INTEGER) || -k > BigInt(Number.MAX_SAFE_INTEGER)) throw new Unsupported(`a constant past 2^53: ${k}`)
  return k >= 0n ? {p: K(Number(k)), n: K(0)} : {p: K(0), n: K(Number(-k))}
}
const iadd = (x: I, y: I): I => ({p: add(x.p, y.p), n: add(x.n, y.n)})
const ineg = (x: I): I => ({p: x.n, n: x.p})
const ival = (x: I): number | undefined => (x.p.op === 'const' && x.n.op === 'const' ? x.p.value - x.n.value : undefined)
const iscale = (k: number, x: I): I => (k >= 0 ? {p: mul(k, x.p), n: mul(k, x.n)} : iscale(-k, ineg(x)))
const imul = (x: I, y: I): I => {
  const a = ival(x), b = ival(y)
  if (a !== undefined) return iscale(a, y)
  if (b !== undefined) return iscale(b, x)
  return {p: add(prod(x.p, y.p), prod(x.n, y.n)), n: add(prod(x.p, y.n), prod(x.n, y.p))}
}
// x ≤ y, x < y, x = y: p_x + n_y against p_y + n_x
const icmp = (op: '<' | '<=' | '=', x: I, y: I): C => ({op, a: add(x.p, y.n), b: add(y.p, x.n)})
const normal = (x: I): I => (isK(x.n, 0) || isK(x.p, 0) ? x : {p: sub(x.p, x.n), n: sub(x.n, x.p)})

// --- the plan of a rule -----------------------------------------------------------------------------------------------
export type Plan = {
  rule: Rule, from: number, to: number, local: number,
  slots: Map<string, number>, // left-side variable → its slot
  inputs: string[], // the variables a turn's inputs give, in input order (synthetic ones start with #)
  defs: [string, Sx][], // definitions, in order: each reads slots, inputs and earlier definitions
  guard: Sx[], // the conjuncts left
  features: string[],
}

export const varsOf = (s: Sx, out = new Set<string>()): Set<string> => {
  if (typeof s === 'string') { if (isVar(s)) out.add(s) } else s.forEach((x, i) => (i === 0 && typeof x === 'string' ? undefined : varsOf(x, out)))
  return out
}
// A linear form: coefficients by variable and a constant; undefined where a term isn't linear.
type Lin = {c: Map<string, bigint>, k: bigint}
export function lin(s: Sx): Lin | undefined {
  if (typeof s === 'string') return isNum(s) ? {c: new Map(), k: BigInt(s)} : isVar(s) ? {c: new Map([[s, 1n]]), k: 0n} : undefined
  const [op, ...xs] = s, ls = xs.map(lin)
  if (ls.some(l => !l)) return undefined
  const sum = (a: Lin, b: Lin, f: bigint): Lin => { const c = new Map(a.c); for (const [v, x] of b.c) c.set(v, (c.get(v) ?? 0n) + f * x); return {c, k: a.k + f * b.k} }
  const zero: Lin = {c: new Map(), k: 0n}
  if (op === '+') return (ls as Lin[]).reduce((a, b) => sum(a, b, 1n), zero)
  if (op === '-') return ls.length === 1 ? sum(zero, ls[0]!, -1n) : (ls as Lin[]).slice(1).reduce((a, b) => sum(a, b, -1n), ls[0]!)
  if (op === '*') {
    let acc: Lin = {c: new Map(), k: 1n}
    for (const l of ls as Lin[]) {
      if (acc.c.size && l.c.size) return undefined
      if (!l.c.size) acc = {c: new Map([...acc.c].map(([v, x]) => [v, x * l.k])), k: acc.k * l.k}
      else acc = {c: new Map([...l.c].map(([v, x]) => [v, x * acc.k])), k: l.k * acc.k}
    }
    return acc
  }
  return undefined
}
const linSx = (l: Lin): Sx => ['+', ...[...l.c].filter(([, x]) => x !== 0n).map(([v, x]): Sx => (x === 1n ? v : ['*', x < 0n ? ['-', String(-x)] : String(x), v])), l.k < 0n ? ['-', String(-l.k)] : String(l.k)]

// div and mod by constants, each an input q: div is q, mod is e − k·q, with 0 <= e − k·q < |k|.
function divmods(s: Sx, extra: Sx[], inputs: string[], seen: Map<string, string>): Sx {
  if (typeof s === 'string') return s
  const xs = s.map((x, i) => (i === 0 ? x : divmods(x, extra, inputs, seen)))
  if (xs[0] !== 'div' && xs[0] !== 'mod') return xs
  const [, e, d] = xs as [string, Sx, Sx], dl = lin(d!)
  if (!dl || dl.c.size || dl.k === 0n) throw new Unsupported('div or mod by a term that is not a nonzero constant')
  const key = JSON.stringify([e, d])
  let q = seen.get(key)
  if (!q) {
    q = `#q${seen.size}`
    seen.set(key, q)
    inputs.push(q)
    const rem: Sx = ['-', e!, ['*', d!, q]], abs = dl.k < 0n ? -dl.k : dl.k
    extra.push(['<=', '0', rem], ['<', rem, String(abs)])
  }
  return xs[0] === 'div' ? q : ['-', e!, ['*', d!, q]]
}

export function planRule(r: Rule, locs: string[], local: number): Plan {
  const features: string[] = []
  const slots = new Map<string, number>(), guard0: Sx[] = []
  r.lhs.forEach((a, j) => { if (typeof a === 'string' && isVar(a) && !slots.has(a)) slots.set(a, j); else guard0.push(['=', a, `#s${j}`]) })
  // exists at the top: its variables are the rule's own (no other use of the name)
  const used = new Set<string>([...r.lhs.flatMap(a => [...varsOf(a)]), ...r.rhs.flatMap(a => [...varsOf(a)])])
  const open = (s: Sx): Sx[] => {
    if (Array.isArray(s) && s[0] === 'exists') {
      features.push('exists')
      for (const b of s[1] as Sx[][]) {
        if (used.has(b[0] as string)) throw new Unsupported('exists binds a name the rule uses elsewhere')
        used.add(b[0] as string)
      }
      return open(s[2]!)
    }
    if (Array.isArray(s) && s[0] === 'and') return s.slice(1).flatMap(open)
    if (s === 'true') return []
    return [s]
  }
  const deep = (s: Sx): void => { if (Array.isArray(s)) { if (s[0] === 'exists') throw new Unsupported('exists under or or not'); if (s[0] === 'ite' || s[0] === 'abs') throw new Unsupported(`${s[0]} in a term`); s.forEach(deep) } }
  let guard = [...guard0, ...open(r.guard)]
  guard.forEach(deep); r.rhs.forEach(deep)
  if (guard.some(g => Array.isArray(g) && (g[0] === 'or'))) features.push('disjunction')
  // div and mod
  const inputs: string[] = [], extra: Sx[] = [], seen = new Map<string, string>()
  guard = guard.map(g => divmods(g, extra, inputs, seen))
  const rhs = r.rhs.map(a => divmods(a, extra, inputs, seen))
  if (seen.size) features.push('div/mod')
  guard.push(...extra)
  // definitions
  const {others} = ruleVars(r), defs: [string, Sx][] = []
  const known = new Set<string>([...slots.keys(), ...r.lhs.map((_, j) => `#s${j}`), ...inputs])
  const free = (v: string) => others.includes(v) && !known.has(v)
  const usedEq = new Set<number>()
  const define = (v: string, s: Sx) => { defs.push([v, s]); known.add(v) }
  for (;;) {
    let moved = false
    for (const [i, g] of guard.entries()) {
      if (usedEq.has(i) || !Array.isArray(g) || g[0] !== '=' || g.length !== 3) continue
      const [, a, b] = g as [string, Sx, Sx]
      const okTerm = (s: Sx, v: string) => [...varsOf(s)].every(x => x !== v && known.has(x))
      if (typeof a === 'string' && isVar(a) && free(a) && okTerm(b, a)) { define(a, b); usedEq.add(i); moved = true; continue }
      if (typeof b === 'string' && isVar(b) && free(b) && okTerm(a, b)) { define(b, a); usedEq.add(i); moved = true; continue }
      const l = lin(['-', a, b])
      if (!l) continue
      const unknown = [...l.c].filter(([x, c]) => c !== 0n && !known.has(x))
      if (unknown.length === 1 && free(unknown[0]![0]) && (unknown[0]![1] === 1n || unknown[0]![1] === -1n)) {
        const [v, c] = unknown[0]!, rest: Lin = {c: new Map([...l.c].filter(([x]) => x !== v).map(([x, y]) => [x, -y * c])), k: -l.k * c}
        define(v, linSx(rest)); usedEq.add(i); moved = true
      }
    }
    if (moved) continue
    // none: a free variable of an equation left becomes an input (a temporary before a post value)
    const inEq = guard.flatMap((g, i) => (usedEq.has(i) || !Array.isArray(g) || g[0] !== '=' ? [] : [...varsOf(g)].filter(free)))
    if (!inEq.length) break
    const rhsVars = new Set(rhs.flatMap(a => [...varsOf(a)]))
    const pick = inEq.find(v => !rhsVars.has(v)) ?? inEq[0]!
    inputs.push(pick); known.add(pick)
  }
  for (const v of others) if (!known.has(v)) { inputs.push(v); known.add(v) }
  if (inputs.some(v => !v.startsWith('#'))) features.push('nondeterminism')
  const left = guard.filter((_, i) => !usedEq.has(i))
  const nonlinear = [...left, ...defs.map(d => d[1]), ...rhs].some(s => { const st = [s]; while (st.length) { const x = st.pop()!; if (Array.isArray(x)) { if (x[0] === '*' && x.slice(1).filter(y => !lin(y) || lin(y)!.c.size).length > 1) return true; st.push(...x) } } return false })
  if (nonlinear) features.push('nonlinear')
  return {rule: {...r, rhs}, from: locs.indexOf(r.from), to: locs.indexOf(r.to), local, slots, inputs, defs, guard: left, features}
}

// `turns`: each rule's turn, the condition it fires on (its location and index, its guard), the assumption's parts.
export type Built = {loop: Loop, plans: Plan[], locs: string[], slots: number, fixed: Set<number>, dropped: Set<number>, nInputs: number, features: string[], turns: C[]}
// `starts`: the run starts at any of these locations (scc.ts's components), not only at the entrypoint.
export function build(t: Ari, name = 'task', opts: {starts?: string[], slice?: boolean} = {}): Built {
  const locs = [...t.funs.keys()], n = Math.max(0, ...t.funs.values())
  const counts = new Map<string, number>()
  const plans = t.rules.map(r => { const k = counts.get(r.from) ?? 0; counts.set(r.from, k + 1); return planRule(r, locs, k) })
  const nInputs = Math.max(0, ...plans.map(p => p.inputs.length))
  // A slot no rule changes (each rule's value for it is its own variable, through definitions) is a param: a value the
  // run starts with and keeps, read where the slot is.
  const same = (p: Plan, j: number): boolean => {
    if (j >= p.rule.rhs.length) return true
    let x: Sx = p.rule.rhs[j]!
    const defs = new Map(p.defs)
    for (let hop = 0; typeof x === 'string' && defs.has(x) && hop < 100; hop++) x = defs.get(x)!
    return typeof x === 'string' && (p.slots.get(x) === j || x === `#s${j}`)
  }
  // `slice` (scc.ts's components only): the slots no guard reads, directly or through the slots and definitions the
  // guards' slots are computed from, are left out; the rest run as they did (a rule's guard never reads them, and the
  // equations defining them are met by their definitions), so the loop halts exactly when the sliced one does.
  const dropped = new Set<number>()
  if (opts.slice) {
    const slotsIn = (p: Plan, sx: Sx, out = new Set<number>(), seen = new Set<string>()): Set<number> => {
      const defs = new Map(p.defs)
      for (const x of varsOf(sx)) {
        if (seen.has(x)) continue
        seen.add(x)
        if (x.startsWith('#s')) out.add(Number(x.slice(2)))
        else if (p.slots.has(x)) out.add(p.slots.get(x)!)
        else if (defs.has(x)) slotsIn(p, defs.get(x)!, out, seen)
      }
      return out
    }
    const keep = new Set<number>()
    for (const p of plans) for (const g of p.guard) for (const j of slotsIn(p, g)) keep.add(j)
    for (let grew = true; grew;) {
      grew = false
      for (const j of [...keep]) for (const p of plans) if (j < p.rule.rhs.length) for (const i of slotsIn(p, p.rule.rhs[j]!)) if (!keep.has(i)) { keep.add(i); grew = true }
    }
    for (let j = 0; j < n; j++) if (!keep.has(j)) dropped.add(j)
  }
  const fixed = new Set(Array.from({length: n}, (_, j) => j).filter(j => !dropped.has(j) && plans.every(p => same(p, j))))
  const slot = (j: number): I => (fixed.has(j) ? {p: V(`a${j}`), n: V(`a${j}$n`)} : {p: V(`s${j}`), n: V(`s${j}$n`)})
  const input = (m: number): I => ({p: V(`i${m}`), n: V(`i${m}$n`)})
  const intOf = (p: Plan) => {
    const memo = new Map<string, I>(), defs = new Map(p.defs)
    const go = (s: Sx): I => {
      if (typeof s === 'string') {
        if (isNum(s)) return iconst(BigInt(s))
        if (s.startsWith('#s')) return slot(Number(s.slice(2)))
        if (p.slots.has(s)) return slot(p.slots.get(s)!)
        const m = p.inputs.indexOf(s)
        if (m >= 0) return input(m)
        const d = defs.get(s)
        if (d === undefined) throw new Error(`${s}: neither slot, input nor definition`)
        if (!memo.has(s)) memo.set(s, go(d))
        return memo.get(s)!
      }
      const op = String(s[0]), xs = s.slice(1), ys = () => xs.map(go)
      switch (op) {
        case '+': return ys().reduce(iadd, iconst(0n))
        case '-': { const v = ys(); return v.length === 1 ? ineg(v[0]!) : v.slice(1).reduce((a, b) => iadd(a, ineg(b)), v[0]!) }
        case '*': return ys().reduce(imul, iconst(1n))
        default: throw new Unsupported(`the term ${String(op)}`)
      }
    }
    const cond = (s: Sx): C => {
      if (s === 'true') return TRUE
      if (s === 'false') return {op: 'not', x: TRUE}
      if (typeof s === 'string') throw new Unsupported(`a condition ${s}`)
      const op = String(s[0]), xs = s.slice(1)
      switch (op) {
        case 'and': return and(xs.map(cond))
        case 'or': return or(xs.map(cond))
        case 'not': return {op: 'not', x: cond(xs[0]!)}
        case '=>': return or([{op: 'not', x: cond(xs[0]!)}, cond(xs[1]!)])
        case 'distinct': { const v = xs.map(go); return and(v.flatMap((a, i) => v.slice(i + 1).map(b => ({op: 'not', x: icmp('=', a, b)} as C)))) }
      }
      const v = xs.map(go), pairs = v.slice(1).map((b, i) => [v[i]!, b] as const)
      const each = (f: (a: I, b: I) => C) => and(pairs.map(([a, b]) => f(a, b)))
      switch (op) {
        case '=': return each((a, b) => icmp('=', a, b))
        case '<': return each((a, b) => icmp('<', a, b))
        case '<=': return each((a, b) => icmp('<=', a, b))
        case '>': return each((a, b) => icmp('<', b, a))
        case '>=': return each((a, b) => icmp('<=', b, a))
        default: throw new Unsupported(`the condition ${String(op)}`)
      }
    }
    return {go, cond}
  }
  const fires = plans.map(p => and([eqN(V('pc'), K(p.from)), eqN(V('t'), K(p.local))]))
  const turns = plans.map((p, k) => and([fires[k]!, ...p.guard.map(intOf(p).cond)])), assume = or(turns)
  const body: Record<string, E> = {}
  const chain = (vals: (E | undefined)[], keep: E): E | undefined => {
    if (vals.every(v => v === undefined)) return undefined
    let e = keep
    for (let k = plans.length - 1; k >= 0; k--) if (vals[k] !== undefined) e = {op: 'if', c: fires[k]!, then: vals[k]!, else: e}
    return e
  }
  const pcE = chain(plans.map(p => (p.to === p.from ? undefined : K(p.to))), V('pc'))
  if (pcE) body.pc = pcE
  for (let j = 0; j < n; j++) {
    if (fixed.has(j) || dropped.has(j)) continue
    const vals = plans.map(p => {
      if (j >= p.rule.rhs.length) return undefined
      const v = normal(intOf(p).go(p.rule.rhs[j]!)), s = slot(j)
      return JSON.stringify(v) === JSON.stringify(s) ? undefined : v
    })
    const pe = chain(vals.map(v => v?.p), V(`s${j}`)), ne = chain(vals.map(v => v?.n), V(`s${j}$n`))
    if (pe) body[`s${j}`] = pe
    if (ne) body[`s${j}$n`] = ne
  }
  const active = [...new Set(plans.map(p => p.from))].sort((a, b) => a - b)
  const loop: Loop = {
    name, params: [...(opts.starts ? ['pc0'] : []), ...Array.from({length: n}, (_, j) => j).filter(j => !dropped.has(j)).flatMap(j => [`a${j}`, `a${j}$n`])],
    inputs: ['t', ...Array.from({length: nInputs}, (_, m) => [`i${m}`, `i${m}$n`]).flat()],
    state: {pc: opts.starts ? V('pc0') : K(locs.indexOf(t.entry)), ...Object.fromEntries(Array.from({length: n}, (_, j) => j).filter(j => !fixed.has(j) && !dropped.has(j)).map(j => [[`s${j}`, sub(V(`a${j}`), V(`a${j}$n`))], [`s${j}$n`, sub(V(`a${j}$n`), V(`a${j}`))]]).flat())},
    while: active.length === locs.length ? TRUE : or(active.map(a => eqN(V('pc'), K(a)))),
    body, assume,
  }
  if (!active.length) loop.while = {op: 'not', x: TRUE}
  if (opts.starts) loop.pre = or(opts.starts.map(l => eqN(V('pc0'), K(locs.indexOf(l)))))
  return {loop, plans, locs, slots: n, fixed, dropped, nInputs, features: [...new Set(plans.flatMap(p => p.features))].sort(), turns}
}

// A turn of the loop as the task's step: the rule it fires and the values of the rule's other variables (inputs, and
// the definitions computed from them), for the witness ari.ts checks.
export function stepOf(b: Built, ps: Record<string, number>, scalars0: Record<string, number>, input: Record<string, number>): {rule: number, others: Record<string, string>} {
  const scalars = {...scalars0}
  for (const j of b.fixed) { scalars[`s${j}`] = ps[`a${j}`]!; scalars[`s${j}$n`] = ps[`a${j}$n`]! }
  const k = b.plans.findIndex(p => p.from === scalars.pc && p.local === input.t)
  if (k < 0) throw new Error('no rule fires')
  const p = b.plans[k]!, env: Env = new Map()
  for (const [x, j] of p.slots) env.set(x, BigInt(scalars[`s${j}`]!) - BigInt(scalars[`s${j}$n`]!))
  for (let j = 0; j < b.slots; j++) env.set(`#s${j}`, BigInt(scalars[`s${j}`] ?? 0) - BigInt(scalars[`s${j}$n`] ?? 0))
  p.inputs.forEach((x, m) => env.set(x, BigInt(input[`i${m}`]!) - BigInt(input[`i${m}$n`]!)))
  for (const [x, s] of p.defs) env.set(x, evalInt(s, env))
  const others: Record<string, string> = {}
  for (const [x, v] of env) if (!x.startsWith('#') && !p.slots.has(x)) others[x] = String(v)
  return {rule: k, others}
}
