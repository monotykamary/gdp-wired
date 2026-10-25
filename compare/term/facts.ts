// Facts at locations: what every run from the entrypoint knows of each slot at each location, a constant or a residue
// (x ≡ c mod k; Granger's congruences, a constant being one mod 0), and the task rewritten with them. The same statement:
// each fact holds at every state a run reaches there (a fixpoint of the rules from the entrypoint, where every slot is
// any integer), so a value replaced by its constant, a rule whose guard the facts make false left out, and a location
// no run reaches left out, change no run.
//
// Where a guard reads a slot modulo k through a value of its own (`exists q. x − k·q = 1`, x % 2 as C translates it)
// and the facts there don't fix that residue, the locations of its strongly connected component are split by the
// residue: a copy per residue, each rule into a copy guarded by the residue it gives (`exists g. x' − k·g = r`), unless
// the facts at its source fix it (x' = x + 3 from an odd x). In a copy the residue is a fact, so the guard's own value
// is gone: ∃q φ(x − k·q) is ∃t ≡ r (mod k) φ(t), the disjunction of φ at one t of each interval its comparisons of t
// leave. Each run of the task is one of the split task's, the copy named by its values, and back: the same runs, so the
// same termination and the same runs that never end. A rank or a recurrent set then reads a residue as a location
// (Velroyen08-alternatingIncr's odd x climbing by 2; KroeningSharygina's x % 2), and a value fixed after the start as a
// constant (4BitCounterPointer's pointers).
//
// `lift` turns a lasso of the rewritten task back into the task's own steps (each rule its origin, the values replaced
// and left out given again), so ari.ts's evaluator replays it on the task as written.
import {type Ari, type Rule, type Step, type Sx, apply, isVar, ruleVars} from './ari.ts'
import {type Built, lin, varsOf} from './translate.ts'
import {check} from '../../kernel/kernel.ts'
import {grow} from '../../kernel/prove.ts'

type Cong = {c: bigint, k: bigint} // x ≡ c (mod k), 0 <= c < k; k = 0: x = c
const TOP: Cong = {c: 0n, k: 1n}
const abs = (x: bigint) => (x < 0n ? -x : x)
const gcd = (a: bigint, b: bigint): bigint => { a = abs(a); b = abs(b); while (b) [a, b] = [b, a % b]; return a }
const md = (x: bigint, k: bigint) => (k === 0n ? x : ((x % k) + k) % k)
const cong = (c: bigint, k: bigint): Cong => ({c: md(c, abs(k)), k: abs(k)})
const join = (a: Cong | null, b: Cong): Cong => (a ? cong(a.c, gcd(gcd(a.k, b.k), a.c - b.c)) : b)
const same = (a: Cong | null, b: Cong | null) => a === b || (!!a && !!b && a.c === b.c && a.k === b.k)
// a·x ≡ r (mod k) for x: a residue class, or null where none
function solve(a: bigint, r: bigint, k: bigint): Cong | null {
  if (k === 0n) return a === 0n ? (r === 0n ? TOP : null) : r % a === 0n ? {c: r / a, k: 0n} : null
  const g = gcd(a, k)
  if (md(r, g) !== 0n) return null
  const k2 = k / g
  if (k2 === 1n) return TOP
  let [x, y, s, t] = [md(a / g, k2), k2, 1n, 0n] // a/g's inverse mod k2
  while (y) { const q = x / y; [x, y] = [y, x - q * y]; [s, t] = [t, s - q * t] }
  return cong((r / g) * s, k2)
}
function meet(a: Cong, b: Cong): Cong | null {
  if (a.k === 0n) return b.k === 0n ? (a.c === b.c ? a : null) : md(a.c - b.c, b.k) === 0n ? a : null
  if (b.k === 0n) return meet(b, a)
  const x = solve(a.k, b.c - a.c, b.k) // a.c + a.k·m ≡ b.c (mod b.k)
  return x && cong(a.c + a.k * x.c, x.k === 0n ? 0n : a.k * x.k)
}
// Σ a·x + c over the variables' classes
const affine = (l: Lin, at: (v: string) => Cong): Cong =>
  [...l.c].reduce<Cong>((s, [v, a]) => { const x = at(v); return cong(s.c + a * x.c, gcd(s.k, a * x.k)) }, {c: l.k, k: 0n})

// The top-level conjuncts of a guard (through a top-level exists).
const conjuncts = (s: Sx): Sx[] => (Array.isArray(s) && s[0] === 'exists' ? conjuncts(s[2]!) : Array.isArray(s) && s[0] === 'and' ? s.slice(1).flatMap(conjuncts) : s === 'true' ? [] : [s])
// What a rule's guard says of its variables, given the left side's classes: each variable's class, or null where the
// guard can't hold.
type Lin = {c: Map<string, bigint>, k: bigint}
// The work the pass may do (a unit per variable read), past which the task is left as it is: a large program's facts
// would take longer than they could save.
class OutOfWork extends Error {}
let work = 0
const spend = (n: number) => { if ((work -= n) < 0) throw new OutOfWork() }
const nodes = (s: Sx): number => (typeof s === 'string' ? 1 : s.reduce<number>((n, x) => n + nodes(x), 1))
// A guard's equations, and a variable's two bounds where they meet (x ≥ c and x ≤ c: x = c), each l = 0.
function equations(r: Rule): Lin[] {
  const eqs: Lin[] = [], lo = new Map<string, bigint>(), hi = new Map<string, bigint>()
  for (const g of conjuncts(r.guard)) {
    if (!Array.isArray(g) || g.length !== 3 || !['=', '<=', '>=', '<', '>'].includes(g[0] as string)) continue
    const l = lin(['-', g[1]!, g[2]!]) // l ⋈ 0
    if (!l) continue
    const nz = [...l.c].filter(([, a]) => a !== 0n)
    if (g[0] === '=') { eqs.push({c: new Map(nz), k: l.k}); continue }
    if (nz.length !== 1 || abs(nz[0]![1]) !== 1n) continue
    const [v, a] = nz[0]!, b = -l.k * a, strict = g[0] === '<' || g[0] === '>' ? 1n : 0n
    if ((g[0] === '<=' || g[0] === '<') === (a > 0n)) hi.set(v, hi.has(v) && hi.get(v)! < b - strict ? hi.get(v)! : b - strict)
    else lo.set(v, lo.has(v) && lo.get(v)! > b + strict ? lo.get(v)! : b + strict)
  }
  for (const [v, h] of hi) if (lo.get(v) === h) eqs.push({c: new Map([[v, 1n]]), k: -h})
  return eqs
}
// What a rule's guard says of its variables, given the left side's classes: each variable's class, or null where the
// guard can't hold.
function derive(r: Rule, eqs: Lin[], at: Cong[]): Map<string, Cong> | null {
  spend(r.lhs.length + eqs.length)
  const env = new Map<string, Cong>(), get = (v: string) => env.get(v) ?? TOP
  const put = (v: string, c: Cong | null): boolean => { const m = c && meet(get(v), c); if (m) env.set(v, m); return !!m }
  for (const [j, a] of r.lhs.entries()) if (typeof a === 'string' && isVar(a) && !put(a, at[j]!)) return null
  for (let round = 0; round < 3; round++) {
    let moved = false
    for (const l of eqs) {
      // (a variable is known from the rest only where none of the rest is any integer with a coefficient ±1)
      let free: string | undefined, many = false
      for (const [v, a] of l.c) if ((a === 1n || a === -1n) && get(v).k === 1n) { if (free) { many = true; break } free = v }
      if (many) continue
      for (const [v, a] of l.c) {
        if (free && free !== v) continue
        let c = l.k, k = 0n
        spend(l.c.size)
        for (const [x, b] of l.c) if (x !== v) { const y = get(x); c += b * y.c; k = gcd(k, b * y.k) }
        const before = get(v)
        if (!put(v, solve(a, -c, k))) return null
        if (!same(before, get(v))) moved = true
      }
    }
    if (!moved) break
  }
  return env
}

// A guard's value of its own read only modulo k: q in atoms λ(x − k·q) ⋈ c alone, x a variable of the left side.
type Mod = {q: string, x: string, k: bigint}
function mods(r: Rule): Mod[] {
  const {lhs, others} = ruleVars(r), rhsVars = new Set(r.rhs.flatMap(a => [...varsOf(a)])), out: Mod[] = []
  const atoms = (s: Sx, acc: Sx[] = []): Sx[] => { if (Array.isArray(s)) { if (['<', '<=', '>', '>=', '='].includes(s[0] as string)) acc.push(s); else s.slice(s[0] === 'exists' ? 2 : 1).forEach(x => atoms(x, acc)) } return acc }
  const body = Array.isArray(r.guard) && r.guard[0] === 'exists' ? r.guard[2]! : r.guard, all = atoms(body)
  for (const q of others) {
    if (rhsVars.has(q)) continue
    let m: Mod | undefined, ok = true, n = 0
    for (const a of all) {
      if (!varsOf(a).has(q)) continue
      n++
      const l = a.length === 3 ? lin(['-', a[1]!, a[2]!]) : undefined, vs = l && [...l.c].filter(([, c]) => c !== 0n)
      if (!l || !vs || vs.length !== 2) { ok = false; break }
      const [x, ax] = vs.find(([v]) => v !== q) ?? ['', 0n], aq = l.c.get(q)!
      if (!lhs.includes(x) || ax === 0n || aq % ax !== 0n || -aq / ax < 2n || (m && (m.x !== x || m.k !== -aq / ax))) { ok = false; break }
      m = {q, x, k: -aq / ax}
    }
    // (every use of q is one of these atoms)
    const uses = (s: Sx): number => (typeof s === 'string' ? (s === q ? 1 : 0) : s.reduce<number>((t, y) => t + uses(y), 0))
    if (ok && m && uses(body) === n) out.push(m)
  }
  return out
}
// ∃q φ given x ≡ res (mod k): φ at one t ≡ res of each interval between its comparisons' points, t = x − k·q.
function eliminate(g: Sx, m: Mod, res: bigint): {guard: Sx, reps: bigint[]} {
  const points = new Set<bigint>()
  const atomT = (a: Sx[]) => { const l = lin(['-', a[1]!, a[2]!])!, lam = l.c.get(m.x)!; return {lam, c: l.k} } // λ·t + c ⋈ 0
  const walk = (s: Sx) => { if (!Array.isArray(s)) return; if (varsOf(s).has(m.q) && ['<', '<=', '>', '>=', '='].includes(s[0] as string)) { const {lam, c} = atomT(s); const p = -c / lam; points.add(p - 1n); points.add(p); points.add(p + 1n) } else s.forEach(walk) }
  walk(g)
  const zs = [...points].sort((a, b) => (a < b ? -1 : 1)), reps: bigint[] = []
  const up = (a: bigint) => a + md(res - a, m.k), down = (a: bigint) => a - md(a - res, m.k)
  if (!zs.length) reps.push(md(res, m.k))
  else {
    reps.push(down(zs[0]! - 1n))
    zs.forEach((z, i) => { if (md(z - res, m.k) === 0n) reps.push(z); const t = up(z + 1n); if (i === zs.length - 1 || t < zs[i + 1]!) reps.push(t) })
  }
  const at = (s: Sx, t: bigint): Sx => {
    if (!Array.isArray(s)) return s
    if (varsOf(s).has(m.q) && ['<', '<=', '>', '>=', '='].includes(s[0] as string)) {
      const {lam, c} = atomT(s), v = lam * t + c, op = s[0]
      return (op === '<' ? v < 0n : op === '<=' ? v <= 0n : op === '>' ? v > 0n : op === '>=' ? v >= 0n : v === 0n) ? 'true' : 'false'
    }
    return s.map(y => at(y, t))
  }
  const body = Array.isArray(g) && g[0] === 'exists' ? g[2]! : g
  const binders = Array.isArray(g) && g[0] === 'exists' ? (g[1] as Sx[][]).filter(b => b[0] !== m.q) : []
  const or = fold(['or', ...[...new Set(reps)].map(t => at(body, t))])
  return {guard: binders.length ? ['exists', binders, or] : or, reps: [...new Set(reps)]}
}
// Constants folded: a comparison of numbers decided, and/or/not simplified.
function fold(s: Sx): Sx {
  if (!Array.isArray(s)) return s
  const op = s[0], xs = op === 'exists' ? [s[1]!, fold(s[2]!)] : s.slice(1).map(fold)
  if (op === 'exists') return xs[1] === 'true' || xs[1] === 'false' ? xs[1]! : ['exists', ...xs]
  if (op === 'and' || op === 'or') {
    const unit = op === 'and' ? 'true' : 'false', zero = op === 'and' ? 'false' : 'true', ys = xs.filter(x => x !== unit)
    return ys.includes(zero) ? zero : ys.length === 0 ? unit : ys.length === 1 ? ys[0]! : [op, ...ys]
  }
  if (op === 'not') return xs[0] === 'true' ? 'false' : xs[0] === 'false' ? 'true' : ['not', xs[0]!]
  if (['<', '<=', '>', '>=', '='].includes(op as string) && xs.length === 2) {
    const l = lin(['-', xs[0]!, xs[1]!])
    if (l && [...l.c.values()].every(c => c === 0n)) { const v = l.k; return (op === '<' ? v < 0n : op === '<=' ? v <= 0n : op === '>' ? v > 0n : op === '>=' ? v >= 0n : v === 0n) ? 'true' : 'false' }
  }
  return [op!, ...xs]
}
const subst = (s: Sx, m: Map<string, bigint>): Sx => (typeof s === 'string' ? (m.has(s) ? (m.get(s)! < 0n ? ['-', String(-m.get(s)!)] : String(m.get(s)!)) : s) : s[0] === 'exists' ? [s[0], s[1]!, subst(s[2]!, m)] : s.map((x, i) => (i === 0 ? x : subst(x, m))))

// How a rule of the rewritten task came from the task's: its origin, the values it fixed, the guard's own values it left
// out (with the t of each to try), the residue values it added.
export type Origin = {rule: number, fixed: Map<string, bigint>, gone: (Mod & {reps: bigint[]})[], added: string[]}
// `consts`: each location's slots a constant at (where no location is split: the rewritten task's locations are the
// task's, in its order, so a loop built from either numbers them alike; facts.ts's certificates are made on the task's
// own loop, solve.ts's `onTask`).
export type Facts = {task: Ari, origins: Origin[], split: number, fixed: number, dropped: number, consts: Map<string, Map<number, bigint>>}

// `maxCopies`: the residues a location is split into at most (the product of its moduli); 1, none: a split task's
// certificates are its copies', which the task's own loop can't read (a residue is no term of the kernel's), so only a
// search of research's (solve.ts --split) splits.
export function facts(t: Ari, maxCopies = 1, budget = 3_000_000): Facts | undefined {
  work = budget
  try { return facts0(t, maxCopies) } catch (e) { if (e instanceof OutOfWork) return undefined; throw e }
}
function facts0(t: Ari, maxCopies: number): Facts | undefined {
  const arity = t.funs, locs = [...arity.keys()]
  const out = new Map<string, number[]>()
  t.rules.forEach((r, i) => out.set(r.from, [...(out.get(r.from) ?? []), i]))
  // The strongly connected components of the locations (Tarjan's).
  const comp = new Map<string, number>(), idx = new Map<string, number>(), low = new Map<string, number>(), stack: string[] = [], on = new Set<string>()
  let n = 0, nc = 0
  const visit = (v: string) => {
    idx.set(v, n); low.set(v, n++); stack.push(v); on.add(v)
    for (const i of out.get(v) ?? []) { const w = t.rules[i]!.to; if (!idx.has(w)) { visit(w); low.set(v, Math.min(low.get(v)!, low.get(w)!)) } else if (on.has(w)) low.set(v, Math.min(low.get(v)!, idx.get(w)!)) }
    if (low.get(v) === idx.get(v)) { for (;;) { const w = stack.pop()!; on.delete(w); comp.set(w, nc); if (w === v) break } nc++ }
  }
  for (const v of locs) if (!idx.has(v)) visit(v)
  // Facts per location and per residue copy, to a fixpoint: a node is a location and the residues it is split by.
  type Key = {slot: number, k: bigint}
  const splits = new Map<number, Key[]>() // component → the residues its locations are split by
  const at = new Map<string, Cong[]>(), nodeLoc = new Map<string, string>()
  const node = (l: string, res?: bigint[]) => { const nd = res ? `${l}~${res.join('~')}` : l; nodeLoc.set(nd, l); return nd }
  // The rule from a node, rewritten by its facts: for each successor node, the slots' classes after and the rule.
  type Edge = {node: string, out: Cong[], rule: Rule, origin: Origin}
  const memo = new Map<string, Edge[]>()
  const edges = (i: number, F: Cong[]): Edge[] => {
    const key = `${i}|${F.map(c => `${c.c}/${c.k}`).join(',')}|${splits.size}`, hit = memo.get(key)
    if (hit) return hit
    const e = edges0(i, F)
    memo.set(key, e)
    return e
  }
  // (each rule's equations and residues read once, at the work of its size)
  const lazy = <T>(f: (r: Rule) => T) => { const c: T[] = []; return (i: number): T => (c[i] ??= (spend(nodes(t.rules[i]!.guard)), f(t.rules[i]!))) }
  const modsOf = lazy(mods), eqsOf = lazy(equations)
  const edges0 = (i: number, F: Cong[]): Edge[] => {
    const r = t.rules[i]!, env = derive(r, eqsOf(i), F)
    if (!env) return []
    // the values fixed: a slot's by the facts at the node, a value of the rule's own by the guard too (∃v φ(v) is φ(c)
    // where φ says v = c; a slot's comparison the guard makes is kept)
    const lhsVars = new Set(r.lhs.filter(a => typeof a === 'string' && isVar(a)) as string[])
    const fixed = new Map([...env].filter(([v, c]) => c.k === 0n && (!lhsVars.has(v) || F[r.lhs.indexOf(v)]!.k === 0n)).map(([v, c]) => [v, c.c] as const))
    let guard = fixed.size ? fold(subst(r.guard, fixed)) : r.guard
    // the guard's own values read modulo a residue the node fixes
    const gone: Origin['gone'] = []
    for (const m of modsOf(i)) {
      const c = F[r.lhs.indexOf(m.x)]!
      if (fixed.has(m.x) || c.k % m.k !== 0n) continue
      const el = eliminate(guard, m, md(c.c, m.k))
      guard = fold(el.guard); gone.push({...m, reps: el.reps})
    }
    if (guard === 'false') return []
    spend(r.rhs.length)
    const rhs = fixed.size ? r.rhs.map(a => fold(subst(a, fixed))) : r.rhs
    const o = r.rhs.map(a => { const l = lin(a); return l ? affine(l, v => env.get(v) ?? TOP) : TOP })
    // the successor's copies, each guarded by its residue where the source doesn't fix it
    let opts: {res: bigint[], out: Cong[], checks: Sx[]}[] = [{res: [], out: o, checks: []}]
    for (const key of splits.get(comp.get(r.to)!) ?? []) {
      const fix = o[key.slot]!.k % key.k === 0n
      opts = opts.flatMap(p => Array.from({length: Number(key.k)}, (_, v) => BigInt(v)).flatMap(v => {
        const m = meet(p.out[key.slot]!, {c: v, k: key.k})
        return m ? [{res: [...p.res, v], out: p.out.map((x, j) => (j === key.slot ? m : x)), checks: fix ? p.checks : [...p.checks, ['=', ['-', rhs[key.slot]!, ['*', String(key.k), `res!${p.checks.length}`]], String(v)] as Sx]}] : []
      }))
    }
    return opts.map(p => {
      const added = p.checks.map((_, j) => `res!${j}`)
      let g = guard
      if (added.length) {
        const ex = Array.isArray(g) && g[0] === 'exists'
        g = ['exists', [...(ex ? g[1] as Sx[] : []), ...added.map(x => [x, 'Int'])], fold(['and', ex ? g[2]! : g, ...p.checks])]
      }
      const to = node(r.to, splits.has(comp.get(r.to)!) ? p.res : undefined)
      return {node: to, out: p.out, rule: {from: '', lhs: r.lhs, to, rhs, guard: g}, origin: {rule: i, fixed, gone, added}}
    })
  }
  const run = () => {
    at.clear()
    const start = node(t.entry), work = [start]
    at.set(start, Array.from({length: arity.get(t.entry)!}, () => TOP))
    while (work.length) {
      const nd = work.pop()!, F = at.get(nd)!
      for (const i of out.get(nodeLoc.get(nd)!) ?? []) for (const e of edges(i, F)) {
        const old = at.get(e.node), nw = old ? old.map((c, j) => join(c, e.out[j]!)) : e.out
        if (!old || nw.some((c, j) => !same(c, old[j]!))) { at.set(e.node, nw); work.push(e.node) }
      }
    }
  }
  run()
  // The residues to split by: a guard's value read modulo k of a slot whose residue the facts at its location don't fix,
  // in a component that cycles.
  for (const [i, r] of t.rules.entries()) {
    const c = comp.get(r.from)!
    for (const m of modsOf(i)) {
      const slot = r.lhs.indexOf(m.x), have = splits.get(c) ?? []
      const F = [...at].filter(([nd]) => nodeLoc.get(nd) === r.from).map(([, f]) => f[slot]!)
      if (!F.length || F.every(f => f.k % m.k === 0n) || have.some(h => h.slot === slot && h.k === m.k)) continue
      if (!t.rules.some(x => comp.get(x.from) === c && comp.get(x.to) === c)) continue
      if (have.reduce((p, h) => p * h.k, m.k) > BigInt(maxCopies)) continue
      splits.set(c, [...have, {slot, k: m.k}])
    }
  }
  if (splits.size) run()
  // The rewritten rules, from each node a run reaches.
  // (in the task's order: its locations as declared, each one's copies by residue, its rules as written)
  const order = [...at.keys()].sort((a, b) => locs.indexOf(nodeLoc.get(a)!) - locs.indexOf(nodeLoc.get(b)!) || (a < b ? -1 : a > b ? 1 : 0))
  const made: {rule: Rule, origin: Origin}[] = []
  for (const nd of order) for (const i of out.get(nodeLoc.get(nd)!) ?? []) for (const e of edges(i, at.get(nd)!)) made.push({rule: {...e.rule, from: nd}, origin: e.origin})
  made.sort((a, b) => a.origin.rule - b.origin.rule)
  const rules = made.map(m => m.rule), origins = made.map(m => m.origin), fixed = origins.reduce((n, o) => n + o.fixed.size, 0)
  const funs = splits.size ? new Map(order.map(nd => [nd, arity.get(nodeLoc.get(nd)!)!] as const)) : new Map(arity)
  const consts = new Map(splits.size ? [] : [...at].map(([nd, F]) => [nd, new Map(F.flatMap((c, j) => (c.k === 0n ? [[j, c.c] as const] : [])))] as const))
  const dropped = t.rules.length - new Set(origins.map(o => o.rule)).size
  if (!splits.size && !fixed && !dropped && order.length === arity.size) return undefined
  return {task: {funs, entry: t.entry, rules}, origins, split: splits.size, fixed, dropped, consts}
}

// A lasso's steps on the rewritten task as the task's own: the origin's index, the fixed values and each guard's own
// value left out given again (the first t that makes the step apply).
export function lift(t: Ari, f: Facts, start: string[], steps: Step[]): Step[] {
  let st = {loc: t.entry, vals: start.map(BigInt)}
  return steps.map(s => {
    const o = f.origins[s.rule]!, r = t.rules[o.rule]!
    const others: Record<string, string> = Object.fromEntries(Object.entries(s.others).filter(([v]) => !o.added.includes(v)))
    const {others: need} = ruleVars(r)
    for (const [v, c] of o.fixed) if (need.includes(v)) others[v] = String(c)
    const env = new Map(r.lhs.flatMap((a, j) => (typeof a === 'string' && isVar(a) ? [[a, st.vals[j]!] as const] : [])))
    let tries: Record<string, string>[] = [others]
    for (const m of o.gone) tries = tries.flatMap(x => m.reps.map(rep => ({...x, [m.q]: String((env.get(m.x)! - rep) / m.k)})))
    for (const x of tries) { const nx = apply(t, st, o.rule, x); if (typeof nx !== 'string') { st = nx; return {rule: o.rule, others: x} } }
    return {rule: o.rule, others}
  })
}

// The rules no state fires: each rule's turn (its location, its index, its guard over the loop's naturals) refuted by
// the kernel, its tree checked (kernel.ts's check), within `ms` in all. A rule left out that never fires changes no run.
// (A call summary's check, c2ari.py's turn back to a copy's entry, is such a rule where the summary holds: left in, a
// rank search reads its guard's disjunctions on every path.)
export function deadRules(b: Built, ms = 1500): Set<number> {
  const out = new Set<number>(), until = performance.now() + ms
  for (const [k, turn] of b.turns.entries()) {
    if (performance.now() > until) break
    const goal = {name: `rule ${k} never fires`, hyps: [turn]}
    const r = grow(goal, new Map(), {nodes: 0, until: Math.min(until, performance.now() + 100)})
    if ('tree' in r && check(goal, r.tree)) out.add(k)
  }
  return out
}
// The task (as `f` rewrote it, or as written) without those rules, its origins kept for `lift`.
export function without(t: Ari, f: Facts | undefined, dead: Set<number>): Facts {
  const base: Facts = f ?? {task: t, origins: t.rules.map((_, rule) => ({rule, fixed: new Map(), gone: [], added: []})), split: 0, fixed: 0, dropped: 0, consts: new Map()}
  const keep = base.task.rules.map((_, i) => !dead.has(i))
  return {...base, task: {...base.task, rules: base.task.rules.filter((_, i) => keep[i])}, origins: base.origins.filter((_, i) => keep[i]), dropped: base.dropped + dead.size}
}
