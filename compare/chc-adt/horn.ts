// CHC-COMP's ADT-LIA track (Horn clauses over algebraic datatypes and linear integer arithmetic) read as a TIP problem,
// so that gdp-wired's datatype prover (core/data.ts, through compare/tip/translate.ts) is what answers it.
//
// The idea: a satisfying assignment of a Horn system is a model, an interpretation of each predicate, and almost every
// task of the track is a functional program written as relations (`len(cons(h, t), n + 1) ← len(t, n)`). Read back as
// functions, the model is a program (each predicate the graph of a function, or a Bool function where no argument is
// computed from the others), and every clause of the system is a theorem about it: the clauses that define a predicate
// are its equations, a query is a TIP goal. What is proven, and checked, is every clause:
//   - `model`: each predicate's reading (its mode: which argument a function computes, or none), chosen so that every
//     clause can be run from its head's inputs; its function is the clauses' patterns compiled into matches, each
//     clause's guards and calls in the order its mode runs them. A case no clause covers is a default value (false for a
//     Bool function): the reading is a guess, never trusted;
//   - `laws`: each clause as a TIP goal over that program, ∀ vars. body ∧ constraint ⇒ head (a query's head false), each
//     predicate application replaced by its reading (`out = f(ins)`, or `p(args)`), then the variables an equation of its
//     hypotheses defines substituted away (∀x. x = t ∧ H ⇒ C is ∀. H[t/x] ⇒ C[t/x] where x isn't in t). Every law
//     proven (proveData's proof, which the kernel checks), the program is a model of every clause: sat. A function
//     whose termination core/data.ts doesn't prove is refused by the translation, as for TIP;
//   - `derive`, `checkDerivation`: unsat is a derivation of false, every node a clause with its variables valued, checked
//     against the clauses as written (tip.ts's evaluator: no gdp-wired code), as compare/chc's runs are.
// Refused, with the reason (`Unsupported`): a sort other than Int, Bool and the declared datatypes (parametric ones
// included), a clause no reading of its predicates can run (a variable neither its head's inputs nor its calls give).
import {type App, type Chc, type Clause, type Sx, Unsupported, parseHorn, parseSx} from '../chc/chc.ts'
import {type Tip, type V, evaluate, parseTip, sameV, show, substSx} from '../tip/tip.ts'

export type Horn = {chc: Chc<string>, tip: Tip, decls: string}
export function readHorn(text: string): Horn {
  const cmds = parseSx(text).filter((c): c is Sx[] => Array.isArray(c))
  const isData = (c: Sx[]) => c[0] === 'declare-datatypes' || c[0] === 'declare-datatype'
  const decls = cmds.filter(isData).map(show).join('\n')
  const tip = parseTip(`${decls}\n(prove true)`)
  for (const d of tip.datas.values()) if (d.params.length) throw new Unsupported(`a parametric datatype (${d.name})`)
  const sortOf = (s: Sx) => { if (s === 'Int' || s === 'Bool' || (typeof s === 'string' && tip.datas.has(s))) return s as string; throw new Unsupported(`the sort ${show(s)}`) }
  return {chc: parseHorn(text, sortOf, isData), tip, decls}
}

// --- terms ------------------------------------------------------------------------------------------------------------

const fv = (s: Sx, vars: Map<string, string>, out = new Set<string>()): Set<string> => {
  if (typeof s === 'string') { if (vars.has(s)) out.add(s); return out }
  s.forEach((x, i) => { if (i > 0 || Array.isArray(x)) fv(x, vars, out) })
  return out
}
const subst = (s: Sx, m: Map<string, Sx>): Sx => { let r = s; for (const [x, t] of m) r = substSx(r, x, t); return r }
// A let's bindings put in place (CHC-COMP's formatter writes them around a clause's conjuncts).
const noLets = (s: Sx): Sx => {
  if (typeof s === 'string') return s
  if (s[0] === 'let') return noLets(subst(s[2]!, new Map((s[1] as Sx[][]).map(b => [b[0] as string, noLets(b[1]!)]))))
  return s.map(noLets)
}
// Constant arithmetic folded, a negative constant factor written as a negation (TIP's translation reads a product's
// constant factor as a numeral).
const tidy = (s: Sx): Sx => {
  if (typeof s === 'string') return s
  const t = s.map((x, i) => (i === 0 ? x : tidy(x)))
  const k = (x: Sx): bigint | undefined => (typeof x === 'string' && /^\d+$/.test(x) ? BigInt(x) : Array.isArray(x) && x[0] === '-' && x.length === 2 ? (y => (y === undefined ? undefined : -y))(k(x[1]!)) : undefined)
  if (t[0] === '*' && t.length === 3) {
    const [a, b] = [t[1]!, t[2]!], ka = k(a), kb = k(b)
    if (ka !== undefined && kb !== undefined) return num(ka * kb)
    const [c, x] = ka !== undefined ? [ka, b] : kb !== undefined ? [kb, a] : [undefined, undefined]
    if (c !== undefined) return c === 1n ? x! : c === -1n ? ['-', x!] : c < 0n ? ['-', ['*', String(-c), x!]] : ['*', String(c), x!]
  }
  return t
}
const conj = (s: Sx): Sx[] => (Array.isArray(s) && s[0] === 'and' ? s.slice(1).flatMap(conj) : s === 'true' ? [] : [s])
const guardA = (g: Sx, rest: Sx): Sx => (rest === 'true' || g === 'false' || rest === 'false' ? and([g, rest]) : g === 'true' ? rest : ['ite', g, rest, 'false'])
const and = (xs: Sx[]): Sx => { const ys = xs.filter(x => x !== 'true'); return ys.includes('false') ? 'false' : !ys.length ? 'true' : ys.length === 1 ? ys[0]! : ['and', ...ys] }

// A term's sort in a clause: a variable's, a constructor's datatype, a selector's field, Int or Bool by its operator.
function sortIn(h: Horn, vars: Map<string, string>, s: Sx): string {
  if (typeof s === 'string') return vars.get(s) ?? (/^\d+$/.test(s) ? 'Int' : s === 'true' || s === 'false' ? 'Bool' : h.tip.ctorOf.get(s)?.data ?? '?')
  const op = s[0] as string, c = h.tip.ctorOf.get(op), sel = h.tip.selectorOf.get(op)
  if (c) return c.data
  if (sel) { const f = h.tip.datas.get(sel.data)!.ctors[sel.ctor]!.fields[sel.field]!.ty; return f.k === 'con' ? f.name : '?' }
  if (['+', '-', '*', 'div', 'mod', 'abs'].includes(op)) return 'Int'
  if (op === 'ite') return sortIn(h, vars, s[2]!)
  return 'Bool'
}
const isAdt = (h: Horn, sort: string) => h.tip.datas.has(sort)
const isCtorTerm = (h: Horn, vars: Map<string, string>, s: Sx): boolean => (typeof s === 'string' ? vars.has(s) || h.tip.ctorOf.has(s) : h.tip.ctorOf.has(s[0] as string))

// A clause normalized: its datatype equations solved by unification (constructors free, trees finite: a clash or a
// cycle makes it vacuous), the substitution of the clause's variables it found (`sub`), what is left of its constraint.
export type Norm = {index: number, clause: Clause<string>, vars: Map<string, string>, head: App | null, body: App[], cons: Sx[], sub: Map<string, Sx>}
export function normalize(h: Horn, c: Clause<string>, index: number): Norm | undefined {
  const sub = new Map<string, Sx>(), rest: Sx[] = []
  const walk = (t: Sx): Sx => { while (typeof t === 'string' && sub.has(t)) t = sub.get(t)!; return t }
  const occurs = (x: string, t: Sx): boolean => { t = walk(t); return typeof t === 'string' ? t === x : t.slice(1).some(a => occurs(x, a)) }
  const unify = (a: Sx, b: Sx): boolean => {
    a = walk(a); b = walk(b)
    if (show(a) === show(b)) return true
    if (typeof a === 'string' && c.vars.has(a)) { if (occurs(a, b)) return false; sub.set(a, b); return true }
    if (typeof b === 'string' && c.vars.has(b)) return unify(b, a)
    const ha = typeof a === 'string' ? a : a[0] as string, hb = typeof b === 'string' ? b : b[0] as string
    if (h.tip.ctorOf.has(ha) && h.tip.ctorOf.has(hb)) {
      if (ha !== hb) return false
      return (a as Sx[]).slice(1).every((x, i) => unify(x, (b as Sx[])[i + 1]!))
    }
    rest.push(['=', a, b]); return true
  }
  for (const k of c.constraint.map(noLets).map(tidy).flatMap(conj)) {
    if (Array.isArray(k) && k[0] === '=' && k.length === 3 && isAdt(h, sortIn(h, c.vars, k[1]!)) && isCtorTerm(h, c.vars, k[1]!) && isCtorTerm(h, c.vars, k[2]!)) { if (!unify(k[1]!, k[2]!)) return undefined } else rest.push(k)
  }
  const full = (t: Sx): Sx => { t = walk(t); return typeof t === 'string' ? t : t.map((x, i) => (i === 0 ? x : full(x))) }
  for (const x of [...sub.keys()]) sub.set(x, full(x))
  const vars = new Map([...c.vars].filter(([x]) => !sub.has(x)))
  const app = (a: App): App => ({pred: a.pred, args: a.args.map(t => subst(tidy(noLets(t)), sub))})
  return {index, clause: c, vars, head: c.head && app(c.head), body: c.body.map(app), cons: rest.map(t => subst(t, sub)), sub}
}

// --- the readings -----------------------------------------------------------------------------------------------------

// A predicate's mode: the argument its function computes from the others, -1 a Bool function of all of them, or -2
// false (never derived: a predicate read only on the way to false, such as the formatter's `ff`, whose clauses are then
// queries of their own).
export type Modes = Map<string, number>
// A clause run from its known variables: each step defines a variable, checks a guard, or matches a computed value
// against a pattern (a call's result that is a constructor term).
// `app`: the body application a call step derives (its index in the body).
type Step = ({k: 'def', x: string, e: Sx} | {k: 'guard', g: Sx} | {k: 'match', pat: Sx, e: Sx}) & {app?: number}
const call = (a: App, mode: number): Sx => { const ins = a.args.filter((_, i) => i !== mode); return ins.length ? [a.pred, ...ins] : a.pred }

// x's coefficient and the rest of a linear term, or undefined where it isn't linear.
type Lin = {c: Map<string, bigint>, k: bigint}
function lin(s: Sx, vars: Map<string, string>): Lin | undefined {
  if (typeof s === 'string') return /^\d+$/.test(s) ? {c: new Map(), k: BigInt(s)} : vars.has(s) ? {c: new Map([[s, 1n]]), k: 0n} : undefined
  const xs = s.slice(1).map(x => lin(x, vars))
  if (xs.some(x => !x)) return undefined
  const add = (a: Lin, b: Lin, m = 1n): Lin => { const c = new Map(a.c); for (const [v, n] of b.c) c.set(v, (c.get(v) ?? 0n) + m * n); return {c, k: a.k + m * b.k} }
  const scale = (a: Lin, m: bigint): Lin => ({c: new Map([...a.c].map(([v, n]) => [v, n * m])), k: a.k * m})
  if (s[0] === '+') return xs.reduce((a, b) => add(a!, b!))
  if (s[0] === '-') return xs.length === 1 ? scale(xs[0]!, -1n) : xs.slice(1).reduce((a, b) => add(a!, b!, -1n), xs[0])
  if (s[0] === '*') { const ks = xs.filter(x => !x!.c.size), vs = xs.filter(x => x!.c.size); if (vs.length > 1) return undefined; const m = ks.reduce((a, b) => a * b!.k, 1n); return vs.length ? scale(vs[0]!, m) : {c: new Map(), k: m} }
  return undefined
}
const num = (n: bigint): Sx => (n < 0n ? ['-', String(-n)] : String(n))
// e1 = e2 solved for the one unknown x in it, where its coefficient is ±1.
function solveFor(e1: Sx, e2: Sx, vars: Map<string, string>, known: Set<string>): {x: string, e: Sx} | undefined {
  const a = lin(e1, vars), b = lin(e2, vars)
  if (!a || !b) return undefined
  const c = new Map(a.c); for (const [v, n] of b.c) c.set(v, (c.get(v) ?? 0n) - n)
  const unknown = [...c].filter(([v, n]) => n !== 0n && !known.has(v))
  if (unknown.length !== 1 || (unknown[0]![1] !== 1n && unknown[0]![1] !== -1n)) return undefined
  const [x, cx] = unknown[0]!, k = a.k - b.k
  // cx·x + Σ c·v + k = 0, so x = −(Σ c·v + k)/cx
  const terms: Sx[] = [...c].filter(([v, n]) => v !== x && n !== 0n).map(([v, n]) => (-n * cx === 1n ? v : ['*', num(-n * cx), v]))
  if (k !== 0n || !terms.length) terms.push(num(-k * cx))
  return {x, e: terms.length === 1 ? terms[0]! : ['+', ...terms]}
}

// The steps that run a clause from `known` (its head's inputs; for a query, nothing: the variables it can't compute are
// chosen as the law's own, `free`), or why it can't be run.
export function schedule(h: Horn, n: Norm, modes: Modes, known: Set<string>, query = false): {steps: Step[], free: string[]} | string {
  const steps: Step[] = [], free: string[] = [], vars = n.vars
  const ready = (s: Sx) => [...fv(s, vars)].every(v => known.has(v))
  let pending: ({k: 'con', s: Sx} | {k: 'app', a: App, j: number})[] = [...n.cons.map(s => ({k: 'con' as const, s})), ...n.body.map((a, j) => ({k: 'app' as const, a, j}))]
  const bind = (x: string, e: Sx, app?: number) => { steps.push({k: 'def', x, e, app}); known.add(x) }
  for (;;) {
    let moved = false
    pending = pending.filter(p => {
      if (p.k === 'app') {
        const m = modes.get(p.a.pred)!
        if (!p.a.args.every((t, i) => i === m || ready(t))) return true
        const app = p.j
        // (a predicate read as false: the clause never applies)
        if (m === -2) { steps.push({k: 'guard', g: 'false'}); moved = true; return false }
        if (m < 0) { steps.push({k: 'guard', g: call(p.a, m), app}); moved = true; return false }
        const out = p.a.args[m]!, e = call(p.a, m)
        if (typeof out === 'string' && vars.has(out) && !known.has(out)) bind(out, e, app)
        else if (ready(out)) steps.push({k: 'guard', g: ['=', out, e], app})
        else if (isCtorTerm(h, vars, out)) { steps.push({k: 'match', pat: out, e, app}); for (const v of fv(out, vars)) known.add(v) } else return true
        moved = true; return false
      }
      const s = p.s
      if (ready(s)) { steps.push({k: 'guard', g: s}); moved = true; return false }
      // a Bool variable a conjunct states, or its negation
      const neg = Array.isArray(s) && s[0] === 'not' ? s[1]! : undefined
      if (typeof s === 'string' && vars.get(s) === 'Bool') { bind(s, 'true'); moved = true; return false }
      if (typeof neg === 'string' && vars.get(neg) === 'Bool' && !known.has(neg)) { bind(neg, 'false'); moved = true; return false }
      if (Array.isArray(s) && s[0] === '=' && s.length === 3) {
        for (const [x, e] of [[s[1]!, s[2]!], [s[2]!, s[1]!]] as const) if (typeof x === 'string' && vars.has(x) && !known.has(x) && ready(e)) { bind(x, e); moved = true; return false }
        const sol = solveFor(s[1]!, s[2]!, vars, known)
        if (sol) { bind(sol.x, sol.e); moved = true; return false }
      }
      return true
    })
    if (!pending.length) break
    if (moved) continue
    if (!query) return `clause ${n.index}: ${pending.length} conjunct(s) its inputs don't reach, e.g. ${show(pending[0]!.k === 'con' ? pending[0]!.s : [pending[0]!.a.pred, ...pending[0]!.a.args]).slice(0, 80)}`
    // a query: the first unknown variable a pending call reads (else any) is the law's own
    const reads = pending.flatMap(p => (p.k === 'app' ? p.a.args.filter((_, i) => i !== modes.get(p.a.pred)) : [p.s]))
    const x = reads.flatMap(t => [...fv(t, vars)]).find(v => !known.has(v))
    if (!x) return `clause ${n.index}: stuck`
    free.push(x); known.add(x)
  }
  return {steps, free}
}

// --- the program ------------------------------------------------------------------------------------------------------

// `runs`: each defining clause's input patterns and steps, by its index (what `derive` follows).
export type Run = {n: Norm, pats: Sx[], steps: Step[]}
// `drop`: a term with every call's dropped arguments left out (the program's functions take only those read).
// `nonneg`: the Int arguments every fact has nonnegative (`pred#i`), the domain a function's model is read on.
export type Program = {nonneg: Set<string>, drop: (t: Sx) => Sx, notes: string[], modes: Modes, norms: Norm[], text: string, tip: Tip, defaults: number, fns: Map<string, {args: string[], ret: string}>, runs: Map<number, Run>}
// A sort's default value: 0, false, or a constructor whose fields have one (a base case first).
function defaults(h: Horn): Map<string, Sx> {
  const d = new Map<string, Sx>([['Int', '0'], ['Bool', 'false']])
  for (let changed = true; changed;) {
    changed = false
    for (const dd of h.tip.datas.values()) {
      if (d.has(dd.name)) continue
      const c = dd.ctors.find(k => k.fields.every(f => f.ty.k === 'con' && d.has(f.ty.name)))
      if (c) { d.set(dd.name, c.fields.length ? [c.name, ...c.fields.map(f => d.get((f.ty as {name: string}).name)!)] : c.name); changed = true }
    }
  }
  return d
}

// The predicates' readings and the program they make. The strongly connected groups of predicates are taken callees
// first; each group's assignments of modes (the last argument computed first, then the others, then a Bool function,
// then false) are those under which every clause it heads runs, given its callees'. An assignment's cost: each case
// left to a default 1, each overlap of a clause that always applies with another 100 (almost never a function), each
// Bool function of two or more arguments 20 (a function that runs every clause is almost always the one meant, and its
// equations prove what a relation's don't), each predicate read as false 1,000 (only where nothing else runs). The
// assignment of the whole system: each group's cheapest in turn, then one group changed at a time, the groups after it
// cheapest again, kept where the whole costs less (a caller's clause may need a callee's other reading, as drop's
// `minus(C, G, 1)` needs C = G − 1). A system none runs is refused.
export function model(h: Horn): Program {
  const norms = h.chc.clauses.map((c, i) => normalize(h, c, i)).filter((n): n is Norm => !!n)
  const preds = [...h.chc.preds.keys()], calls = new Map(preds.map(p => [p, new Set<string>()]))
  for (const n of norms) if (n.head) for (const a of n.body) calls.get(n.head.pred)!.add(a.pred)
  const groups = sccs(preds, calls), modes: Modes = new Map(), dflt = defaults(h)
  // the predicates read only on the way to false: every clause whose body applies one heads false or another of them
  const toFalse = new Set(preds)
  for (let changed = true; changed;) {
    changed = false
    for (const n of norms) if (n.head && !toFalse.has(n.head.pred)) for (const a of n.body) if (toFalse.delete(a.pred)) changed = true
  }
  const fns = new Map<string, {args: string[], ret: string}>(), bodies = new Map<string, Sx>(), runs = new Map<number, Run>()
  const nonneg = nonnegative(h, norms)
  type Pick = {modes: number[], defaults: number, bodies: Map<string, Sx>, runs: Run[]}
  // each group's assignments that run, by its callees' modes, cheapest first; and why the first that fails does
  const memo = new Map<string, {ok: Pick[], why: string}>()
  const choices = (gi: number) => {
    const g = groups[gi]!, key = `${gi}|${[...new Set(g.flatMap(p => [...calls.get(p)!]))].filter(q => !g.includes(q)).map(q => modes.get(q)).join(',')}`
    let c = memo.get(key)
    if (c) return c
    const options = g.map(p => { const n = h.chc.preds.get(p)!.length; return [...Array.from({length: n}, (_, i) => n - 1 - i), -1, ...(toFalse.has(p) ? [-2] : [])] })
    const ok: Pick[] = [], total = options.reduce((a, o) => a * o.length, 1)
    let why = ''
    for (let k = 0; k < Math.min(total, 4096); k++) {
      let r = k
      const pick = options.map(o => { const m = o[r % o.length]!; r = Math.floor(r / o.length); return m })
      g.forEach((p, i) => modes.set(p, pick[i]!))
      const out = compileGroup(h, g, norms, modes, dflt, nonneg)
      if (typeof out === 'string') { why ||= out; continue }
      ok.push({modes: pick, ...out, defaults: out.defaults + 1000 * pick.filter(m => m === -2).length + 20 * g.filter((p, i) => pick[i] === -1 && h.chc.preds.get(p)!.length > 1).length})
    }
    c = {ok: ok.sort((a, b) => a.defaults - b.defaults), why}
    if (process.env.GDP_ADT_DEBUG) console.error(`[adt] ${key} ${g.join(',')}: ${ok.map(o => `${o.modes.join('/')}:${o.defaults}`).join(' ')} | ${why.slice(0, 200)}`)
    memo.set(key, c)
    return c
  }
  // greedy from group `from` on (each group its cheapest given its callees' modes, those before `from` as `prefix`
  // has them), then one change at a time: a group's other assignment, the groups after it greedy again, kept where the
  // whole costs less (a caller's clause may need a callee's other reading)
  const greedy = (prefix: Pick[], from: number, first?: Pick): {cost: number, picks: Pick[]} | string => {
    const picks = prefix.slice(0, from)
    picks.forEach((p, gi) => groups[gi]!.forEach((q, i) => modes.set(q, p.modes[i]!)))
    for (let gi = from; gi < groups.length; gi++) {
      const c = choices(gi), p = gi === from && first ? first : c.ok[0]
      if (!p) return `${groups[gi]!.join(', ')}: ${c.why}`
      groups[gi]!.forEach((q, i) => modes.set(q, p.modes[i]!))
      picks.push(p)
    }
    return {cost: picks.reduce((a, p) => a + p.defaults, 0), picks}
  }
  let best = greedy([], 0)
  if (typeof best === 'string') throw new Unsupported(`no reading runs every clause of ${best}`)
  for (let improved = true, rounds = 0; improved && rounds < 4 && best.cost > 0; rounds++) {
    improved = false
    for (let gi = 0; gi < groups.length && best.cost > 0; gi++) {
      groups.forEach((g, k) => { if (k < gi) g.forEach((q, i) => modes.set(q, (best as {picks: Pick[]}).picks[k]!.modes[i]!)) })
      for (const alt of choices(gi).ok) {
        if (alt === best.picks[gi]) continue
        const t = greedy(best.picks, gi, alt)
        if (typeof t !== 'string' && t.cost < best.cost) { best = t; improved = true }
      }
    }
  }
  const won: {cost: number, picks: Pick[]} = best
  // why each group read as false has no other reading
  const notes: string[] = []
  groups.forEach((g, gi) => {
    const p = won.picks[gi]!
    g.forEach((q, i) => modes.set(q, p.modes[i]!))
    for (const [q, b] of p.bodies) bodies.set(q, b)
    for (const r of p.runs) runs.set(r.n.index, r)
  })
  groups.forEach((g, gi) => { if (won.picks[gi]!.modes.includes(-2)) { const w = [...memo.entries()].find(([k]) => k.startsWith(`${gi}|`))?.[1].why; if (w) notes.push(w) } })
  const totalDefaults = won.picks.reduce((a, p, gi) => a + (p.defaults % 1000) % 20 % 100, 0)
  const name = (p: string) => p
  // The arguments no function reads (but to pass on to an argument no function reads) dropped, at every call: a call is
  // a map read at the pairing of its arguments, a polynomial whose degree doubles with each (kernel/kernel.ts reads it
  // multiplied out: 3 Int arguments 0.1 s, 4 past 10 s).
  const live = new Map<string, Set<number>>([...bodies.keys()].map(p => [p, new Set<number>()]))
  for (let changed = true; changed;) {
    changed = false
    for (const [p, b] of bodies) {
      const mine = live.get(p)!
      const visit = (t: Sx, used: boolean): void => {
        if (typeof t === 'string') { const m = /^%a(\d+)$/.exec(t); if (m && used && !mine.has(Number(m[1]))) { mine.add(Number(m[1])); changed = true } return }
        const f = live.get(t[0] as string)
        t.forEach((x, i) => { if (i > 0 || Array.isArray(x)) visit(x, used && (!f || f.has(i - 1))) })
      }
      visit(b, true)
    }
  }
  const drop = (t: Sx): Sx => {
    if (typeof t === 'string') return t
    const f = live.get(t[0] as string), xs = t.map(drop)
    if (!f) return xs
    const ys = xs.filter((_, i) => i === 0 || f.has(i - 1))
    return ys.length === 1 ? ys[0]! : ys
  }
  for (const [p, b] of bodies) bodies.set(p, drop(b))
  const sig = (p: string) => {
    const sorts = h.chc.preds.get(p)!, m = modes.get(p)!, keep = live.get(p)!
    const args = sorts.filter((_, i) => i !== m), ret = m < 0 ? 'Bool' : sorts[m]!
    fns.set(p, {args: args.filter((_, j) => keep.has(j)), ret})
    return [name(p), args.flatMap((s, j) => (keep.has(j) ? [[`%a${j}`, s]] : [])), ret] as Sx[]
  }
  const parts = groups.map(g => g.filter(p => modes.get(p)! > -2)).filter(g => g.length).map(g => (g.length === 1 && !calls.get(g[0]!)!.has(g[0]!) && !live.get(g[0]!)!.size ? show(['define-fun', ...sig(g[0]!), bodies.get(g[0]!)!]) : show(['define-funs-rec', g.map(sig), g.map(p => bodies.get(p)!)])))
  const text = `${h.decls}\n${parts.join('\n')}\n(prove true)`
  return {nonneg, notes, modes, norms, text, tip: parseTip(text), defaults: totalDefaults, fns, runs, drop}
}

// The Int arguments every derivable fact has nonnegative (`pred#i`): the greatest set such that each clause's head
// argument there is a sum of nonnegative terms (a constant ≥ 0, a variable a body application has at such an argument,
// one an equation or a lower bound of its constraint makes nonnegative, each with a coefficient ≥ 0). A size law of
// the least model (tip-adt-lia's naturals written as Int), never trusted: the program guards by it, the laws prove it.
export function nonnegative(h: Horn, norms: Norm[]): Set<string> {
  const out = new Set<string>()
  for (const [p, sorts] of h.chc.preds) sorts.forEach((s, i) => { if (s === 'Int') out.add(`${p}#${i}`) })
  const isNonneg = (t: Sx, vars: Map<string, string>, nn: Set<string>) => { const l = lin(t, vars); return !!l && l.k >= 0n && [...l.c].every(([v, c]) => c >= 0n && nn.has(v)) }
  for (let changed = true; changed;) {
    changed = false
    for (const n of norms) {
      if (!n.head) continue
      const nn = new Set<string>()
      for (const a of n.body) a.args.forEach((t, i) => { if (typeof t === 'string' && out.has(`${a.pred}#${i}`)) nn.add(t) })
      for (let more = true; more;) {
        more = false
        for (const k of n.cons) {
          if (!Array.isArray(k) || k.length !== 3) continue
          const [op, a, b] = k as [string, Sx, Sx]
          const add = (v: Sx) => { if (typeof v === 'string' && n.vars.get(v) === 'Int' && !nn.has(v)) { nn.add(v); more = true } }
          if (op === '=') { if (isNonneg(b, n.vars, nn)) add(a); if (isNonneg(a, n.vars, nn)) add(b) }
          if ((op === '>=' || op === '>') && isNonneg(b, n.vars, nn)) add(a)
          if ((op === '<=' || op === '<') && isNonneg(a, n.vars, nn)) add(b)
        }
      }
      n.head.args.forEach((t, i) => { const key = `${n.head!.pred}#${i}`; if (out.has(key) && !isNonneg(t, n.vars, nn)) { out.delete(key); changed = true } })
    }
  }
  return out
}

function sccs(nodes: string[], edges: Map<string, Set<string>>): string[][] {
  // Tarjan's, callees before callers
  const index = new Map<string, number>(), low = new Map<string, number>(), stack: string[] = [], on = new Set<string>(), out: string[][] = []
  let i = 0
  const visit = (v: string) => {
    index.set(v, i); low.set(v, i); i++; stack.push(v); on.add(v)
    for (const w of edges.get(v) ?? []) {
      if (!index.has(w)) { visit(w); low.set(v, Math.min(low.get(v)!, low.get(w)!)) } else if (on.has(w)) low.set(v, Math.min(low.get(v)!, index.get(w)!))
    }
    if (low.get(v) === index.get(v)) { const g: string[] = []; let w; do { w = stack.pop()!; on.delete(w); g.push(w) } while (w !== v); out.push(g.reverse()) }
  }
  for (const v of nodes) if (!index.has(v)) visit(v)
  return out
}

let fresh = 0
// Each predicate of a group as its function's body: the clauses it heads, their input patterns compiled into matches.
export function compileGroup(h: Horn, g: string[], norms: Norm[], modes: Modes, dflt: Map<string, Sx>, nonneg: Set<string>): {defaults: number, bodies: Map<string, Sx>, runs: Run[]} | string {
  let defaults = 0
  const bodies = new Map<string, Sx>(), runs: Run[] = []
  for (const p of g) {
    if (modes.get(p) === -2) continue
    const m = modes.get(p)!, sorts = h.chc.preds.get(p)!, ins = sorts.map((_, i) => i).filter(i => i !== m)
    const rows: Row[] = []
    for (const n of norms.filter(n => n.head?.pred === p)) {
      // inputs as patterns: a variable seen before, or an Int or Bool term, is a fresh one and an equation
      const vars = new Map(n.vars), seen = new Set<string>(), eqs: Sx[] = []
      const pat = (t: Sx, sort: string): Sx => {
        if (typeof t === 'string' && vars.has(t) && !seen.has(t)) { seen.add(t); return t }
        if (isAdt(h, sort) && Array.isArray(t) && h.tip.ctorOf.has(t[0] as string)) { const k = h.tip.datas.get(sort)!.ctors.find(c => c.name === t[0])!; return [t[0]!, ...t.slice(1).map((x, j) => pat(x, (k.fields[j]!.ty as {name: string}).name))] }
        if (isAdt(h, sort) && typeof t === 'string' && h.tip.ctorOf.has(t)) return t
        const x = `%f${fresh++}`; vars.set(x, sort); seen.add(x); eqs.push(['=', x, t]); return x
      }
      const pats = ins.map(i => pat(n.head!.args[i]!, sorts[i]!))
      const nn: Norm = {...n, vars, cons: [...eqs, ...n.cons]}
      const s = schedule(h, nn, modes, new Set(seen))
      if (typeof s === 'string') return `${p} at argument ${m}: ${s}`
      const result = m < 0 ? 'true' : n.head!.args[m]!
      if (![...fv(result, vars)].every(v => seen.has(v) || s.steps.some(st => (st.k === 'def' && st.x === v) || (st.k === 'match' && fv(st.pat, vars).has(v))))) return `${p} at argument ${m}: clause ${n.index}'s result isn't computed`
      // a call's input where every fact is nonnegative: a guard before it (no fact of it there: the clause doesn't apply)
      const steps = s.steps.flatMap(st => (st.app === undefined ? [st] : [...nn.body[st.app]!.args.flatMap((t, i): Step[] => (i !== modes.get(nn.body[st.app!]!.pred) && nonneg.has(`${nn.body[st.app!]!.pred}#${i}`) && !(typeof t === 'string' && /^\d+$/.test(t)) && !s.steps.some(d => d.k === 'def' && d.app !== undefined && fv(t, nn.vars).has(d.x)) ? [{k: 'guard', g: ['>=', t, '0']}] : [])), st]))
      rows.push({pats, bind: new Map(), steps, result, vars})
      runs.push({n: nn, pats, steps})
    }
    const d = m < 0 ? 'false' : dflt.get(sorts[m]!)!, out = compile(h, ins.map((_, i) => `%a${i}`), ins.map(i => sorts[i]!), rows, d, m < 0)
    defaults += out.defaults
    // its Int inputs that every fact has nonnegative, a guard first (a recursion that counts one down then ends at 0)
    const guard = and(ins.flatMap((i, j) => (nonneg.has(`${p}#${i}`) ? [['>=', `%a${j}`, '0']] : [])))
    bodies.set(p, guard === 'true' ? out.body : m < 0 ? guardA(guard, out.body) : ['ite', guard, out.body, d])
  }
  return {defaults, bodies, runs}
}

type Row = {pats: Sx[], bind: Map<string, Sx>, steps: Step[], result: Sx, vars: Map<string, string>}
function compile(h: Horn, args: Sx[], sorts: string[], rows: Row[], dflt: Sx, rel: boolean): {body: Sx, defaults: number} {
  // (a Bool function's case no clause covers is false, as the least model has it: no default)
  if (!rows.length) return {body: dflt, defaults: rel ? 0 : 1}
  const col = sorts.findIndex((s, i) => isAdt(h, s) && rows.some(r => isCtorTerm(h, r.vars, r.pats[i]!) && !(typeof r.pats[i] === 'string' && r.vars.has(r.pats[i] as string))))
  if (col < 0) {
    // every pattern a variable: each row's variables bound to the arguments, its steps, then its result
    const leaves = rows.map(r => {
      const bind = new Map(r.bind)
      r.pats.forEach((x, i) => bind.set(x as string, args[i]!))
      return leaf(h, r, bind, dflt)
    })
    if (rel) return {body: leaves.length === 1 ? leaves[0]!.a : ['or', ...leaves.map(l => l.a)], defaults: 0}
    // (the clauses that always apply last; one of them beside another of a different value is an overlap, almost never a
    // function: costed; beside one of the same value, the same function: that one left out)
    const always = leaves.find(l => l.a === 'true'), same = (l: {v: Sx}) => !!always && show(l.v) === show(always.v)
    const rest = leaves.filter(l => l.a !== 'true' && !same(l)), order = [...rest, ...(always ? [always] : [])]
    let body = dflt, defaults = 1
    for (const l of order.reverse()) { if (l.a === 'true') { body = l.v; defaults = 0 } else body = ['ite', l.a, l.v, body] }
    if (always) defaults += 100 * (rest.length + leaves.filter(l => l.a === 'true' && !same(l)).length)
    return {body, defaults}
  }
  const d = h.tip.datas.get(sorts[col]!)!
  let defaults = 0
  const cases = d.ctors.map(k => {
    const fs = k.fields.map(() => `%m${fresh++}`)
    const sub = rows.flatMap(r => {
      const p = r.pats[col]!, head = typeof p === 'string' ? p : p[0] as string
      const rest = r.pats.filter((_, i) => i !== col)
      if (typeof p === 'string' && r.vars.has(p)) {
        // a variable: bound to the constructor's value, its fields further columns of fresh variables
        const bind = new Map(r.bind).set(p, k.fields.length ? [k.name, ...fs] : k.name), vars = new Map(r.vars)
        const ws = k.fields.map(f => { const w = `%w${fresh++}`; vars.set(w, (f.ty as {name: string}).name); return w })
        ws.forEach((w, j) => bind.set(w, fs[j]!))
        return [{...r, vars, bind, pats: [...rest, ...ws]}]
      }
      return head === k.name ? [{...r, pats: [...rest, ...(Array.isArray(p) ? p.slice(1) : [])]}] : []
    })
    const c = compile(h, [...args.filter((_, i) => i !== col), ...fs], [...sorts.filter((_, i) => i !== col), ...k.fields.map(f => (f.ty as {name: string}).name)], sub, dflt, rel)
    defaults += c.defaults
    return [k.fields.length ? [k.name, ...fs] : k.name, c.body] as Sx
  })
  return {body: ['match', args[col]!, cases], defaults}
}
// A clause's leaf: whether it applies (its guards, its calls' results matching their patterns) and its value, each
// variable in place (the patterns' bindings, then each step's definition).
function leaf(h: Horn, r: Row, bind: Map<string, Sx>, dflt: Sx): {a: Sx, v: Sx} {
  const sub = (s: Sx, m: Map<string, Sx>) => { let t = s; for (let k = 0; k < 4 && [...fv(t, r.vars)].some(v => m.has(v)); k++) t = subst(t, m); return t }
  const go = (i: number, m: Map<string, Sx>): {a: Sx, v: Sx} => {
    if (i === r.steps.length) return {a: 'true', v: sub(r.result, m)}
    const st = r.steps[i]!
    if (st.k === 'def') return go(i + 1, new Map(m).set(st.x, sub(st.e, m)))
    // (a guard an if: what follows it, a call among it, is on its path, as core/data.ts's termination reads paths)
    if (st.k === 'guard') {
      const g = sub(st.g, m), key = show(g)
      if (m.has(`%g ${key}`)) return go(i + 1, m)
      const rest = go(i + 1, new Map(m).set(`%g ${key}`, 'true'))
      return {a: guardA(g, rest.a), v: rest.v}
    }
    // a match of a computed value against a constructor pattern: its variables bound where they are new, compared where not
    return matchPat(h, r, sub(st.e, m), st.pat, m, go, i + 1, dflt)
  }
  return go(0, bind)
}
function matchPat(h: Horn, r: Row, e: Sx, pat: Sx, m: Map<string, Sx>, go: (i: number, m: Map<string, Sx>) => {a: Sx, v: Sx}, next: number, dflt: Sx): {a: Sx, v: Sx} {
  if (typeof pat === 'string' && r.vars.has(pat)) {
    if (m.has(pat)) { const rest = go(next, m); return {a: guardA(['=', m.get(pat)!, e], rest.a), v: rest.v} }
    return go(next, new Map(m).set(pat, e))
  }
  const k = typeof pat === 'string' ? pat : pat[0] as string, {data} = h.tip.ctorOf.get(k)!, d = h.tip.datas.get(data)!
  const x = `%e${fresh++}`, fs = d.ctors.find(c => c.name === k)!.fields.map(() => `%m${fresh++}`)
  // the fields matched in turn (a nested pattern a nested match)
  let inner: {a: Sx, v: Sx}
  const subPats = Array.isArray(pat) ? pat.slice(1) : []
  const chain = (j: number, mm: Map<string, Sx>): {a: Sx, v: Sx} => (j === subPats.length ? go(next, mm) : matchPat(h, r, fs[j]!, subPats[j]!, mm, (_, m2) => chain(j + 1, m2), 0, dflt))
  inner = chain(0, m)
  const cases = (val: (o: {a: Sx, v: Sx}) => Sx, miss: Sx): Sx => ['match', x, d.ctors.map(c => [c.fields.length ? [c.name, ...(c.name === k ? fs : c.fields.map(() => `%m${fresh++}`))] : c.name, c.name === k ? val(inner) : miss] as Sx)]
  return {a: ['let', [[x, e]], cases(o => o.a, 'false')], v: ['let', [[x, e]], cases(o => o.v, dflt)]}
}

// --- the laws ---------------------------------------------------------------------------------------------------------

// A clause as a TIP goal over the program: ∀ vars. hyps ⇒ head, each application read by its mode, then each variable
// an equation of the hypotheses defines (x = t, x not in t) put in place. `sub`: what each variable eliminated is, in
// the variables left (a refutation's values give every variable of the clause).
// `trivial`: a hypothesis is false (an application of a predicate read as false): the clause holds as it is.
export type Law = {index: number, query: boolean, trivial: boolean, goal: Sx, vars: Map<string, string>, sub: Map<string, Sx>}
export function lawOf(h: Horn, pr: Program, n: Norm): Law {
  // (the head's call on the left: proveData proves f(c x) = e by unfolding, e = f(c x) not always at one unfolding)
  // (a function's model is its graph where its inputs are in its domain, those every fact has nonnegative so: outside
  // it the function is a default no clause gave)
  const dom = (a: App, m: number): Sx[] => a.args.flatMap((t, i) => (i !== m && pr.nonneg.has(`${a.pred}#${i}`) && !(typeof t === 'string' && /^\d+$/.test(t)) ? [['>=', t, '0']] : []))
  const read = (a: App, head = false): Sx => { const m = pr.modes.get(a.pred)!; return m === -2 ? 'false' : m < 0 ? call(a, m) : and([...dom(a, m), head ? ['=', call(a, m), a.args[m]!] : ['=', a.args[m]!, call(a, m)]]) }
  let hyps: Sx[] = [...n.body.flatMap(a => conj(pr.drop(read(a)))), ...n.cons], concl: Sx = n.head ? pr.drop(read(n.head, true)) : 'false'
  const vars = new Map(n.vars), sub = new Map<string, Sx>()
  const put = (x: string, t: Sx) => {
    const one = new Map([[x, t]])
    hyps = hyps.map(y => subst(y, one)); concl = subst(concl, one)
    for (const [y, u] of sub) sub.set(y, subst(u, one))
    sub.set(x, t); vars.delete(x)
  }
  // A defining clause in the variables its function computes: each its run defines from the head's inputs, by that
  // definition (the unfolded body then reads the very terms the hypotheses do: le(B − 1, A − 1), not le(C, D) beside
  // (C + 1) − 1).
  const run = pr.runs.get(n.index)
  if (run) for (const st of run.steps) if (st.k === 'def' && vars.has(st.x) && [...fv(st.e, run.n.vars)].every(v => vars.has(v) && v !== st.x)) put(st.x, pr.drop(subst(st.e, sub)))
  for (let changed = true; changed;) {
    changed = false
    for (let i = 0; i < hyps.length && !changed; i++) {
      const s = hyps[i]!
      if (!(Array.isArray(s) && s[0] === '=' && s.length === 3)) continue
      for (const [x, t] of [[s[1]!, s[2]!], [s[2]!, s[1]!]] as const) {
        if (changed || typeof x !== 'string' || !vars.has(x) || fv(t, vars).has(x)) continue
        hyps = hyps.filter((_, j) => j !== i); put(x, t); changed = true
      }
    }
  }
  // (a hypothesis made true by the substitutions, t = t, or stated twice, is left out)
  hyps = [...new Map(hyps.filter(y => !(Array.isArray(y) && y[0] === '=' && y.length === 3 && show(y[1]!) === show(y[2]!))).map(y => [show(y), y])).values()]
  const used = new Set<string>(); [...hyps, concl].forEach(s => fv(s, vars, used))
  for (const x of [...vars.keys()]) if (!used.has(x)) vars.delete(x)
  const trivial = hyps.includes('false'), query = concl === 'false'
  // a query's goal: a hypothesis it negates becomes its conclusion (TIP's goals are mostly H ⇒ C)
  if (concl === 'false' && hyps.length) {
    const j = Math.max(0, hyps.findLastIndex(x => Array.isArray(x) && x[0] === 'not'))
    const x = hyps[j]!
    concl = Array.isArray(x) && x[0] === 'not' ? x[1]! : ['not', x]
    hyps = hyps.filter((_, k) => k !== j)
  }
  const body: Sx = hyps.length ? ['=>', and(hyps), concl] : concl
  return {index: n.index, query, trivial, goal: vars.size ? ['forall', [...vars].map(([x, s]) => [x, s]), body] : body, vars, sub}
}

// --- derivations ------------------------------------------------------------------------------------------------------

// A derivation: a clause (its index in the system as written), its variables valued, a derivation of each body
// application.
export type Node = {clause: number, env: Map<string, V>, kids: Node[]}
// The clause's own variables valued from the normalized ones (the unification's substitution evaluated; a variable
// nothing reads, its sort's default).
const origEnv = (h: Horn, n: Norm, env: Map<string, V>): Map<string, V> => {
  const out = new Map<string, V>(), d = defaults(h)
  for (const [x, sort] of n.vars) if (!env.has(x)) env.set(x, evaluate(h.tip, d.get(sort)!, env))
  for (const x of n.clause.vars.keys()) out.set(x, n.sub.has(x) ? evaluate(h.tip, n.sub.get(x)!, env) : env.get(x)!)
  return out
}
// A derivation of p at its inputs, by its clauses run as their modes say (each call derived in turn): its output and
// the derivation, or undefined where no clause applies (a case the program leaves to its default) or fuel runs out.
export function derive(h: Horn, pr: Program, p: string, ins: V[], fuel = {n: 100_000}): {out: V, node: Node} | undefined {
  const m = pr.modes.get(p)!
  if (--fuel.n < 0 || m === -2) return undefined
  for (const n of pr.norms.filter(n => n.head?.pred === p)) {
    const r = pr.runs.get(n.index)!, env = new Map<string, V>()
    if (!r.pats.every((t, j) => matchV(h, r.n.vars, t, ins[j]!, env))) continue
    const kids = steps(h, pr, r.n, r.steps, env, fuel)
    if (!kids) continue
    return {out: m < 0 ? true : evaluate(h.tip, n.head!.args[m]!, env), node: {clause: n.index, env: origEnv(h, n, env), kids}}
  }
  return undefined
}
// A pattern (constructors and variables, each variable once) against a value.
function matchV(h: Horn, vars: Map<string, string>, t: Sx, v: V, env: Map<string, V>): boolean {
  if (typeof t === 'string' && vars.has(t)) { if (env.has(t)) return sameV(env.get(t)!, v); env.set(t, v); return true }
  const k = typeof t === 'string' ? t : t[0] as string
  return typeof v === 'object' && 'c' in v && v.c === k && (Array.isArray(t) ? t.slice(1).every((x, i) => matchV(h, vars, x, v.a[i]!, env)) : true)
}
// A clause's steps from its inputs' values: each call derived (its derivation the body application's), each guard
// evaluated; the derivations in body order, or undefined where a guard fails or a call has none.
function steps(h: Horn, pr: Program, n: Norm, sts: Step[], env: Map<string, V>, fuel: {n: number}): Node[] | undefined {
  const kids: Node[] = []
  try {
    for (const st of sts) {
      let v: V | undefined
      if (st.app !== undefined) {
        const a = n.body[st.app]!, m = pr.modes.get(a.pred)!
        const d = derive(h, pr, a.pred, a.args.filter((_, i) => i !== m).map(t => evaluate(h.tip, t, env)), fuel)
        if (!d) return undefined
        kids[st.app] = d.node; v = d.out
      }
      if (st.k === 'def') env.set(st.x, v ?? evaluate(h.tip, st.e, env))
      else if (st.k === 'guard') { if (st.app !== undefined ? (pr.modes.get(n.body[st.app]!.pred)! >= 0 && !sameV(v!, evaluate(h.tip, (st.g as Sx[])[1]!, env))) : evaluate(h.tip, st.g, env) !== true) return undefined } else if (!matchV(h, n.vars, st.pat, v!, env)) return undefined
    }
  } catch { return undefined }
  return kids.length === n.body.length && n.body.every((_, j) => kids[j]) ? kids : undefined
}
// A query's derivation from values of its law's variables (a refutation's): every variable of the clause valued (the
// law's eliminations evaluated over the program), then each body application derived where it says.
export function deriveQuery(h: Horn, pr: Program, law: Law, vals: Map<string, V>): Node | undefined {
  const n = pr.norms.find(x => x.index === law.index)!
  const env = new Map(vals)
  try { for (const [x, t] of law.sub) env.set(x, evaluate(pr.tip, t, vals)) } catch { return undefined }
  const kids: Node[] = []
  for (const a of n.body) {
    const m = pr.modes.get(a.pred)!
    let d
    try { d = derive(h, pr, a.pred, a.args.filter((_, i) => i !== m).map(t => evaluate(h.tip, t, env))) } catch { return undefined }
    if (!d || (m >= 0 && !sameV(d.out, evaluate(h.tip, a.args[m]!, env)))) return undefined
    kids.push(d.node)
  }
  for (const k of n.cons) { try { if (evaluate(h.tip, k, env) !== true) return undefined } catch { return undefined } }
  const node = {clause: n.index, env: origEnv(h, n, env), kids}
  if (!n.head) return node
  // a clause of a predicate read as false: a query that applies that predicate alone takes its derivation
  const heads = n.head.args.map(t => evaluate(h.tip, t, env))
  for (const q of pr.norms.filter(q => !q.head && q.body.length === 1 && q.body[0]!.pred === n.head!.pred)) {
    const qe = new Map<string, V>()
    if (!q.body[0]!.args.every((t, i) => matchV(h, q.vars, t, heads[i]!, qe))) continue
    try { if (q.cons.every(k => evaluate(h.tip, k, qe) === true)) return {clause: q.index, env: origEnv(h, q, qe), kids: [node]} } catch { continue }
  }
  return undefined
}

// A derivation checked against the clauses as written (tip.ts's evaluator over the datatypes alone, no gdp-wired code):
// each node's clause's constraint holds at its values, each body application's arguments are its derivation's head's,
// and the root is a query. Undefined where it holds, else what fails.
export function checkDerivation(h: Horn, root: Node): string | undefined {
  if (h.chc.clauses[root.clause]?.head !== null) return 'the root is not a query'
  const go = (d: Node, depth: number): string | undefined => {
    const c = h.chc.clauses[d.clause]
    if (!c) return `no clause ${d.clause}`
    if (depth > 100_000) return 'too deep'
    for (const x of c.vars.keys()) if (!d.env.has(x)) return `clause ${d.clause}: ${x} has no value`
    for (const k of c.constraint) if (evaluate(h.tip, k, d.env) !== true) return `clause ${d.clause}: ${show(k).slice(0, 80)} fails`
    if (d.kids.length !== c.body.length) return `clause ${d.clause}: ${d.kids.length} derivations for ${c.body.length} applications`
    for (const [j, a] of c.body.entries()) {
      const k = d.kids[j]!, kc = h.chc.clauses[k.clause]
      if (!kc?.head || kc.head.pred !== a.pred) return `clause ${d.clause}: application ${j} derived by a clause of another predicate`
      for (const [i, t] of a.args.entries()) if (!sameV(evaluate(h.tip, t, d.env), evaluate(h.tip, kc.head.args[i]!, k.env))) return `clause ${d.clause}: application ${j}'s argument ${i} isn't its derivation's`
      const bad = go(k, depth + 1)
      if (bad) return bad
    }
    return undefined
  }
  try { return go(root, 0) } catch (e) { return `evaluation: ${(e as Error).message.slice(0, 80)}` }
}
