// A linear CHC system as a gdp-wired rule. The state is where a derivation is (`loc`: start, one of the predicates, or
// error) and the predicate's arguments (Int arguments in i0, i1, ..., Bool ones in b0, b1, ...). Each request names a
// clause and brings a value for every variable the clause leaves free; a clause fires when the state is at its body's
// predicate (at start, for a fact) and its constraint holds, and then the state moves to its head (error, for a query).
// The law: error is never reached. Its proof is a proof that the system is satisfiable; a run that reaches error is a
// derivation of false.
//
// Each clause is planned first: a body argument that is a plain variable names that slot; an equality x = e whose x is
// still free defines x (so a clause's head values are terms of the state and the request, not values the request must
// guess); the variables left are the request's; div and mod by a constant k take one more request value q each, with
// k·q ≤ e ≤ k·q + k − 1. Nonlinear clauses (two predicates in a body) and sorts other than Int and Bool are refused.
import {type Chc, type Clause, type Sort, type Sx, Unsupported, evalSx, type Val} from './chc.ts'
import {Choice, Cond, Int, all, any, bool, choose, int, no, oneOf, rule, when, yes} from '../../core/dsl.ts'

type Bound = {kind: 'slot', sort: Sort, k: number} | {kind: 'def', sx: Sx} | {kind: 'input', sort: Sort, k: number}
export type Plan = {clause: Clause, bound: Map<string, Bound>, guard: Sx[], extra: Sx[], ints: number, divs: number}

const varsIn = (s: Sx, out = new Set<string>(), shadow = new Set<string>()): Set<string> => {
  if (typeof s === 'string') { if (!shadow.has(s)) out.add(s); return out }
  if (s[0] === 'let') {
    const inner = new Set(shadow)
    for (const b of s[1] as Sx[][]) { varsIn(b[1]!, out, shadow); inner.add(b[0] as string) }
    return varsIn(s[2]!, out, inner)
  }
  for (const x of s.slice(1)) varsIn(x, out, shadow)
  return out
}
// Every element, the head too: a let's first binding is a list in head position.
const countDivs = (s: Sx): number => (typeof s === 'string' ? 0 : s.reduce<number>((n, x) => n + countDivs(x), s[0] === 'div' || s[0] === 'mod' ? 1 : 0))
const constOf = (s: Sx): bigint | undefined => {
  try { const v = evalSx(s, new Map()); return typeof v === 'bigint' ? v : undefined } catch { return undefined }
}

export function plan(c: Clause, preds: Chc['preds']): Plan {
  if (c.body.length > 1) throw new Unsupported(`nonlinear: ${c.body.length} predicates in one body`)
  const bound = new Map<string, Bound>(), guard: Sx[] = [], extra: Sx[] = []
  const slotName = (sort: Sort, k: number) => `#${sort === 'Int' ? 'i' : 'b'}${k}`
  const slots = (pred: string) => { const n = {Int: 0, Bool: 0}; return preds.get(pred)!.map(s => ({sort: s, k: n[s]++})) }
  for (const app of c.body) slots(app.pred).forEach(({sort, k}, j) => {
    const a = app.args[j]!
    if (typeof a === 'string' && c.vars.has(a) && !bound.has(a)) bound.set(a, {kind: 'slot', sort, k})
    else extra.push(['=', a, slotName(sort, k)])
  })
  // Definitions, until none is left: x = e (either side) with x free and e not reaching x through the definitions.
  const reaches = (s: Sx, x: string, seen = new Set<string>()): boolean => [...varsIn(s)].some(v => v === x || (!seen.has(v) && bound.get(v)?.kind === 'def' && (seen.add(v), reaches((bound.get(v) as {sx: Sx}).sx, x, seen))))
  const free = (v: Sx): v is string => typeof v === 'string' && c.vars.has(v) && !bound.has(v)
  // A let around conjuncts (how CHC-COMP's formatter writes most transition relations): each binding becomes a
  // definition of its own (renamed apart), and the body's conjuncts are read as the clause's.
  let lets = 0
  const renamed = (s: Sx, names: Map<string, string>): Sx => {
    if (typeof s === 'string') return names.get(s) ?? s
    if (s[0] !== 'let') return s.map((x, i) => (i === 0 ? x : renamed(x, names)))
    const inner = new Map(names)
    for (const b of s[1] as Sx[][]) inner.delete(b[0] as string)
    return ['let', (s[1] as Sx[][]).map(b => [b[0]!, renamed(b[1]!, names)]), renamed(s[2]!, inner)]
  }
  const opened = (s: Sx): Sx[] => {
    if (Array.isArray(s) && s[0] === 'and') return s.slice(1).flatMap(opened)
    // A conjunct that is a binding's name is the binding's own conjuncts (often an equation that defines a variable).
    if (typeof s === 'string' && s.includes('@let')) { const d = bound.get(s); if (d?.kind === 'def') return opened(d.sx) }
    if (!Array.isArray(s) || s[0] !== 'let') return s === 'true' ? [] : [s]
    const names = new Map<string, string>()
    for (const b of s[1] as Sx[][]) {
      const fresh = `${b[0] as string}@let${lets++}`
      names.set(b[0] as string, fresh)
      bound.set(fresh, {kind: 'def', sx: b[1]!})
    }
    return opened(renamed(s[2]!, names))
  }
  let rest = c.constraint.flatMap(opened)
  for (let changed = true; changed;) {
    changed = false
    const next: Sx[] = []
    for (const s of rest) {
      let used = false
      if (Array.isArray(s) && s[0] === '=' && s.length === 3) {
        for (const [x, e] of [[s[1]!, s[2]!], [s[2]!, s[1]!]] as const) if (!used && free(x) && !reaches(e, x)) { bound.set(x, {kind: 'def', sx: e}); used = true }
      } else if (free(s) && c.vars.get(s) === 'Bool') { bound.set(s, {kind: 'def', sx: 'true'}); used = true } else if (Array.isArray(s) && s[0] === 'not' && free(s[1]!) && c.vars.get(s[1] as string) === 'Bool') { bound.set(s[1] as string, {kind: 'def', sx: 'false'}); used = true }
      if (used) changed = true
      else next.push(s)
    }
    rest = next
  }
  guard.push(...rest)
  const n = {Int: 0, Bool: 0}
  for (const [v, sort] of c.vars) if (!bound.has(v)) bound.set(v, {kind: 'input', sort, k: n[sort]++})
  const all: Sx[] = [...guard, ...extra, ...(c.head?.args ?? []), ...[...bound.values()].flatMap(b => (b.kind === 'def' ? [b.sx] : []))]
  return {clause: c, bound, guard, extra, ints: n.Int, divs: all.reduce<number>((k, s) => k + countDivs(s), 0)}
}

export type Built = ReturnType<typeof build>
export function build(chc: Chc, name = 'chc') {
  const predNames = [...chc.preds.keys()], loc = predNames.map((_, j) => `p${j}`)
  const locOf = (p: string) => loc[predNames.indexOf(p)]!
  const plans = chc.clauses.map(c => plan(c, chc.preds))
  const nInt = Math.max(0, ...[...chc.preds.values()].map(s => s.filter(x => x === 'Int').length))
  const nBool = Math.max(0, ...[...chc.preds.values()].map(s => s.filter(x => x === 'Bool').length))
  const inInt = Math.max(0, ...plans.map(p => p.ints + p.divs))
  const inBool = Math.max(0, ...plans.map(p => [...p.bound.values()].filter(b => b.kind === 'input' && b.sort === 'Bool').length))
  const range = (k: number, f: (j: number) => string) => Array.from({length: k}, (_, j) => f(j))
  const clauseNames = range(plans.length, j => `c${j}`) as [string, ...string[]]
  const r = rule(name)
    .inputs({c: oneOf(...clauseNames), ...Object.fromEntries(range(inInt, j => `x${j}`).map(k => [k, int])), ...Object.fromEntries(range(inBool, j => `y${j}`).map(k => [k, bool]))})
    .ints(Object.fromEntries(range(nInt, j => `i${j}`).map(k => [k, 0])))
    .state({...Object.fromEntries(range(nBool, j => `b${j}`).map(k => [k, bool.from(false)])), loc: oneOf('start', ...loc, 'error').from('start')})
    .step((env: Record<string, unknown>) => {
      const fires: Cond[] = [], heads: {loc: string, values: Record<string, Int | Cond>}[] = []
      plans.forEach((p, j) => {
        const side: Cond[] = []
        let nextDiv = p.ints
        const memo = new Map<string, Int | Cond>()
        const asInt = (v: Int | Cond, s: Sx): Int => { if (v instanceof Int) return v; throw new Unsupported(`an Int expected: ${JSON.stringify(s).slice(0, 60)}`) }
        const asCond = (v: Int | Cond, s: Sx): Cond => { if (v instanceof Cond) return v; throw new Unsupported(`a Bool expected: ${JSON.stringify(s).slice(0, 60)}`) }
        const tr = (s: Sx, scope: Map<string, Int | Cond>): Int | Cond => {
          if (typeof s === 'string') {
            if (s === 'true') return yes
            if (s === 'false') return no
            if (/^\d+$/.test(s)) { const v = Number(s); if (!Number.isSafeInteger(v)) throw new Unsupported(`the numeral ${s}`); return Int.of(v) }
            if (scope.has(s)) return scope.get(s)!
            const m = /^#([ib])(\d+)$/.exec(s)
            if (m) return env[`${m[1]}${m[2]}`] as Int | Cond
            const b = p.bound.get(s)
            if (!b) throw new Unsupported(`an unbound symbol ${s}`)
            if (b.kind === 'slot') return env[`${b.sort === 'Int' ? 'i' : 'b'}${b.k}`] as Int | Cond
            if (b.kind === 'input') return env[`${b.sort === 'Int' ? 'x' : 'y'}${b.k}`] as Int | Cond
            if (!memo.has(s)) memo.set(s, tr(b.sx, new Map()))
            return memo.get(s)!
          }
          const [op, ...xs] = s as [string, ...Sx[]]
          if (op === 'let') {
            const inner = new Map(scope)
            for (const b of xs[0] as Sx[][]) inner.set(b[0] as string, tr(b[1]!, scope))
            return tr(xs[1]!, inner)
          }
          const I = (k: number) => asInt(tr(xs[k]!, scope), xs[k]!), B = (k: number) => asCond(tr(xs[k]!, scope), xs[k]!)
          const pairs = (f: (a: Int, b: Int) => Cond) => all(...xs.slice(1).map((_, k) => f(I(k), I(k + 1))))
          switch (op) {
            case '+': return xs.slice(1).reduce<Int>((a, _, k) => a.plus(I(k + 1)), I(0))
            case '-': return xs.length === 1 ? I(0).negate() : xs.slice(1).reduce<Int>((a, _, k) => a.minus(I(k + 1)), I(0))
            case '*': {
              const ks = xs.map(constOf), vars = xs.filter((_, k) => ks[k] === undefined)
              if (vars.length > 1) throw new Unsupported('a product of two variables')
              const k = ks.reduce<bigint>((a, c) => a * (c ?? 1n), 1n)
              if (k > BigInt(Number.MAX_SAFE_INTEGER) || -k > BigInt(Number.MAX_SAFE_INTEGER)) throw new Unsupported('a coefficient too large')
              return vars.length ? asInt(tr(vars[0]!, scope), vars[0]!).times(Number(k)) : Int.of(Number(k))
            }
            case 'div': case 'mod': {
              const k = constOf(xs[1]!)
              if (k === undefined || k <= 0n) throw new Unsupported(`${op} by a non-constant or non-positive divisor`)
              const e = I(0), q = env[`x${nextDiv++}`] as Int, kq = q.times(Number(k))
              side.push(kq.atMost(e), e.atMost(kq.plus(Number(k) - 1)))
              return op === 'div' ? q : e.minus(kq)
            }
            case 'abs': { const e = I(0); return when(e.isNegative, e.negate(), e) }
            case '<=': return pairs((a, b) => a.atMost(b))
            case '<': return pairs((a, b) => a.lt(b))
            case '>=': return pairs((a, b) => a.atLeast(b))
            case '>': return pairs((a, b) => a.gt(b))
            case '=': case 'distinct': {
              const vs = xs.map(x => tr(x, scope))
              const eq = (a: Int | Cond, b: Int | Cond): Cond => (a instanceof Int ? a.eq(asInt(b, s)) : choose(a, asCond(b, s), asCond(b, s).not()))
              const c = op === '=' ? all(...vs.slice(1).map(v => eq(vs[0]!, v))) : all(...vs.flatMap((a, k) => vs.slice(k + 1).map(b => eq(a, b).not())))
              return c
            }
            case 'and': return all(...xs.map((_, k) => B(k)))
            case 'or': return any(...xs.map((_, k) => B(k)))
            case 'not': return B(0).not()
            case '=>': return any(B(0).not(), B(1))
            case 'xor': return choose(B(0), B(1).not(), B(1))
            case 'ite': {
              const c = B(0), a = tr(xs[1]!, scope), b = tr(xs[2]!, scope)
              return a instanceof Int ? when(c, a, asInt(b, s)) : choose(c, a, asCond(b, s))
            }
            default: throw new Unsupported(`the operator ${op}`)
          }
        }
        const top = new Map<string, Int | Cond>()
        const at = p.clause.body[0] ? locOf(p.clause.body[0].pred) : 'start'
        const conds = [...p.guard, ...p.extra].map(s => asCond(tr(s, top), s))
        const head = {loc: p.clause.head ? locOf(p.clause.head.pred) : 'error', values: {} as Record<string, Int | Cond>}
        if (p.clause.head) {
          const n = {Int: 0, Bool: 0}
          chc.preds.get(p.clause.head.pred)!.forEach((sort, k) => { head.values[`${sort === 'Int' ? 'i' : 'b'}${n[sort]++}`] = tr(p.clause.head!.args[k]!, top) })
        }
        fires.push(all((env.c as Choice<string>).is(clauseNames[j]!), (env.loc as Choice<string>).is(at), ...conds, ...side))
        heads.push(head)
      })
      const out: Record<string, unknown> = {}
      for (let k = 0; k < nInt; k++) out[`i${k}`] = fires.reduceRight<Int>((acc, f, j) => when(f, (heads[j]!.values[`i${k}`] as Int | undefined) ?? Int.of(0), acc), env[`i${k}`] as Int)
      for (let k = 0; k < nBool; k++) out[`b${k}`] = fires.reduceRight<Cond>((acc, f, j) => choose(f, (heads[j]!.values[`b${k}`] as Cond | undefined) ?? no, acc), env[`b${k}`] as Cond)
      out.loc = fires.reduceRight<unknown>((acc, f, j) => when(f, heads[j]!.loc as never, acc as never), env.loc)
      return out as never
    })
  const law = r.law('no clause derives false', (env: Record<string, unknown>) => (env.loc as Choice<string>).is('error').not())
  return {rule: r, law, plans, predNames, loc, clauseNames, nInt, nBool, inInt, inBool}
}

// A run the rule took, checked against the CHC itself (evalSx: no gdp-wired code): each step's clause, with its
// variables valued from the state before (the body's slots), the request (its free variables) and its definitions,
// satisfies its whole constraint and its body arguments, and its head arguments are the state after. The last step's
// clause is a query.
export type Step = {clause: number, input: Record<string, number | boolean | string>, before: Record<string, unknown>, after: Record<string, unknown>}
export function checkDerivation(b: Built, chc: Chc, steps: Step[]): string | undefined {
  if (!steps.length) return 'no steps'
  let where = 'start'
  for (const [n, s] of steps.entries()) {
    const p = b.plans[s.clause]!, c = p.clause, env = new Map<string, Val>()
    const val = (x: unknown): Val => (typeof x === 'boolean' ? x : BigInt(x as number))
    const at = c.body[0] ? b.loc[b.predNames.indexOf(c.body[0].pred)] : 'start'
    if (at !== where || s.before.loc !== where) return `step ${n}: clause ${s.clause} needs ${at}, the run is at ${where}`
    const slot = (sort: Sort, k: number, st: Record<string, unknown>) => val(st[`${sort === 'Int' ? 'i' : 'b'}${k}`])
    const pending = [...p.bound.entries()]
    for (const [v, bd] of pending) if (bd.kind === 'slot') env.set(v, slot(bd.sort, bd.k, s.before)); else if (bd.kind === 'input') env.set(v, val(s.input[`${bd.sort === 'Int' ? 'x' : 'y'}${bd.k}`]))
    for (let left = pending.filter(([, bd]) => bd.kind === 'def'); left.length;) {
      const ready = left.filter(([, bd]) => { try { evalSx((bd as {sx: Sx}).sx, env); return true } catch { return false } })
      if (!ready.length) return `step ${n}: definitions that never resolve`
      for (const [v, bd] of ready) env.set(v, evalSx((bd as {sx: Sx}).sx, env))
      left = left.filter(x => !ready.includes(x))
    }
    for (const k of c.constraint) if (evalSx(k, env) !== true) return `step ${n}: clause ${s.clause}'s constraint ${JSON.stringify(k).slice(0, 80)} fails`
    if (c.body[0]) {
      const ns = {Int: 0, Bool: 0}
      for (const [j, sort] of chc.preds.get(c.body[0].pred)!.entries()) if (evalSx(c.body[0].args[j]!, env) !== slot(sort, ns[sort]++, s.before)) return `step ${n}: body argument ${j} isn't the state`
    }
    if (c.head) {
      const ns = {Int: 0, Bool: 0}
      for (const [j, sort] of chc.preds.get(c.head.pred)!.entries()) if (evalSx(c.head.args[j]!, env) !== slot(sort, ns[sort]++, s.after)) return `step ${n}: head argument ${j} isn't the state after`
      where = b.loc[b.predNames.indexOf(c.head.pred)]!
    } else where = 'error'
    if (s.after.loc !== where) return `step ${n}: the rule went to ${String(s.after.loc)}, the clause to ${where}`
  }
  return where === 'error' ? undefined : 'the run does not end in a query'
}
