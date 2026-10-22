// TermComp's ARI format for integer transition systems (`(format LCTRS)`, `(theory Ints)`), read, and an evaluator of
// its rules on integer values (BigInt) that uses no gdp-wired code: what a nontermination witness is checked against.
//   - `(fun f (-> Int ... Int))` declares a location f with its arity; `(entrypoint f)` the start, at any integers;
//   - `(rule (f x̄) (g t̄) :guard φ)`: from f at x̄ to g at t̄ where φ holds; a variable that isn't one of x̄ (in t̄, in φ,
//     or bound by an `exists` in φ) takes any integer that satisfies φ (nondeterminism); no guard is `true`.
// The task: does every run from the entrypoint, at any integers, end? A rule applies at a state when values for its
// other variables make the guard true, so a run ends where none applies.
export type Sx = string | Sx[]
export type Rule = {from: string, lhs: Sx[], to: string, rhs: Sx[], guard: Sx}
export type Ari = {funs: Map<string, number>, entry: string, rules: Rule[]}

export class Unsupported extends Error {}

export function parseSx(text: string): Sx[] {
  const out: Sx[] = [], stack: Sx[][] = [out]
  for (const m of text.matchAll(/\s+|;[^\n]*|\(|\)|\|[^|]*\||[^\s()|;]+/g)) {
    const t = m[0]
    if (/^\s|^;/.test(t)) continue
    if (t === '(') { const l: Sx[] = []; stack.at(-1)!.push(l); stack.push(l) } else if (t === ')') {
      if (stack.length === 1) throw new Error('unbalanced )')
      stack.pop()
    } else stack.at(-1)!.push(t.startsWith('|') ? t.slice(1, -1) : t)
  }
  if (stack.length !== 1) throw new Error('unbalanced (')
  return out
}

export function parseAri(text: string): Ari {
  const funs = new Map<string, number>(), rules: Rule[] = []
  let entry: string | undefined
  for (const cmd of parseSx(text)) {
    if (!Array.isArray(cmd) || typeof cmd[0] !== 'string') throw new Unsupported(`a command ${JSON.stringify(cmd).slice(0, 60)}`)
    const head = cmd[0]
    if (head === 'format') { if (cmd[1] !== 'LCTRS') throw new Unsupported(`format ${String(cmd[1])}`) } else if (head === 'theory') {
      if (cmd[1] !== 'Ints') throw new Unsupported(`theory ${String(cmd[1])}`)
    } else if (head === 'fun') {
      const sig = cmd[2]
      if (!Array.isArray(sig) || sig[0] !== '->' || !sig.slice(1).every(s => s === 'Int')) {
        if (sig === 'Int') { funs.set(cmd[1] as string, 0); continue }
        throw new Unsupported(`the signature of ${String(cmd[1])}: ${JSON.stringify(sig)}`)
      }
      funs.set(cmd[1] as string, sig.length - 2)
    } else if (head === 'entrypoint') entry = cmd[1] as string
    else if (head === 'rule') {
      const app = (s: Sx): {f: string, args: Sx[]} => {
        if (typeof s === 'string' && funs.has(s)) return {f: s, args: []}
        if (Array.isArray(s) && typeof s[0] === 'string' && funs.has(s[0])) return {f: s[0], args: s.slice(1)}
        throw new Unsupported(`a rule's side that isn't a location applied: ${JSON.stringify(s).slice(0, 80)}`)
      }
      const l = app(cmd[1]!), r = app(cmd[2]!)
      let guard: Sx = 'true'
      for (let i = 3; i < cmd.length; i += 2) {
        if (cmd[i] === ':guard') guard = cmd[i + 1]!
        else throw new Unsupported(`rule attribute ${String(cmd[i])}`)
      }
      rules.push({from: l.f, lhs: l.args, to: r.f, rhs: r.args, guard})
    } else throw new Unsupported(`command ${head}`)
  }
  if (!entry || !funs.has(entry)) throw new Unsupported('no entrypoint')
  const used = (s: Sx): boolean => (typeof s === 'string' ? funs.has(s) : s.some(used))
  for (const r of rules) {
    if (r.lhs.length !== funs.get(r.from) || r.rhs.length !== funs.get(r.to)) throw new Unsupported(`a rule applies ${r.from} or ${r.to} to the wrong number of arguments`)
    if ([...r.lhs, ...r.rhs, r.guard].some(used)) throw new Unsupported('a location inside a term (a nested call: recursion)')
  }
  return {funs, entry, rules}
}

// --- the evaluator ----------------------------------------------------------------------------------------------------

const OPS = new Set(['and', 'or', 'not', '=>', '=', 'distinct', '<', '<=', '>', '>=', '+', '-', '*', 'div', 'mod', 'abs', 'ite', 'exists', 'true', 'false'])
export const isNum = (s: Sx): boolean => typeof s === 'string' && /^\d+$/.test(s)
export const isVar = (s: Sx): boolean => typeof s === 'string' && !isNum(s) && !OPS.has(s)
export type Env = Map<string, bigint>
// SMT-LIB's div and mod: the remainder is never negative.
const ediv = (a: bigint, b: bigint): bigint => { const q = a / b, r = a - q * b; return r < 0n ? (b > 0n ? q - 1n : q + 1n) : q }

export function evalInt(s: Sx, env: Env): bigint {
  if (typeof s === 'string') {
    if (isNum(s)) return BigInt(s)
    const v = env.get(s)
    if (v === undefined) throw new Error(`no value for ${s}`)
    return v
  }
  const op = String(s[0]), xs = s.slice(1), a = () => xs.map(x => evalInt(x, env))
  switch (op) {
    case '+': return a().reduce((p, q) => p + q, 0n)
    case '-': { const v = a(); return v.length === 1 ? -v[0]! : v.slice(1).reduce((p, q) => p - q, v[0]!) }
    case '*': return a().reduce((p, q) => p * q, 1n)
    case 'div': case 'mod': {
      const [p, q] = a() as [bigint, bigint]
      if (q === 0n) throw new Error('division by 0')
      const d = ediv(p, q)
      return op === 'div' ? d : p - q * d
    }
    case 'abs': { const v = evalInt(xs[0]!, env); return v < 0n ? -v : v }
    case 'ite': return evalBool(xs[0]!, env) ? evalInt(xs[1]!, env) : evalInt(xs[2]!, env)
    default: throw new Error(`not an integer term: ${JSON.stringify(s).slice(0, 60)}`)
  }
}
export function evalBool(s: Sx, env: Env): boolean {
  if (s === 'true') return true
  if (s === 'false') return false
  if (typeof s === 'string') throw new Error(`not a condition: ${s}`)
  const op = String(s[0]), xs = s.slice(1)
  switch (op) {
    case 'and': return xs.every(x => evalBool(x, env))
    case 'or': return xs.some(x => evalBool(x, env))
    case 'not': return !evalBool(xs[0]!, env)
    case '=>': return !evalBool(xs[0]!, env) || evalBool(xs[1]!, env)
    // exists: the witness names the bound variables' values (in env, under their names)
    case 'exists': return evalBool(xs[1]!, env)
    case 'distinct': { const v = xs.map(x => evalInt(x, env)); return new Set(v).size === v.length }
  }
  const v = xs.map(x => evalInt(x, env))
  const pairs = v.slice(1).map((q, i) => [v[i]!, q] as const)
  switch (op) {
    case '=': return pairs.every(([p, q]) => p === q)
    case '<': return pairs.every(([p, q]) => p < q)
    case '<=': return pairs.every(([p, q]) => p <= q)
    case '>': return pairs.every(([p, q]) => p > q)
    case '>=': return pairs.every(([p, q]) => p >= q)
    default: throw new Error(`not a condition: ${JSON.stringify(s).slice(0, 60)}`)
  }
}

// The variables a rule reads: its left side's, and the others (its nondeterministic values, those bound by exists too).
export function ruleVars(r: Rule): {lhs: string[], others: string[]} {
  const all = new Set<string>(), walk = (s: Sx) => { if (typeof s === 'string') { if (isVar(s)) all.add(s) } else if (s[0] === 'exists') { for (const b of s[1] as Sx[][]) all.add(b[0] as string); walk(s[2]!) } else s.forEach((x, i) => (i === 0 && typeof x === 'string' ? undefined : walk(x))) }
  r.lhs.forEach(walk); r.rhs.forEach(walk); walk(r.guard)
  const lhs = [...new Set(r.lhs.filter(isVar) as string[])]
  return {lhs, others: [...all].filter(v => !lhs.includes(v))}
}

// One step of a run: rule `rule` from (loc, vals), its other variables given; the state after, or why not.
export type State = {loc: string, vals: bigint[]}
export function apply(t: Ari, st: State, rule: number, others: Record<string, string>): State | string {
  const r = t.rules[rule]
  if (!r) return `no rule ${rule}`
  if (r.from !== st.loc) return `rule ${rule} is from ${r.from}, the run is at ${st.loc}`
  const env: Env = new Map()
  for (const [k, v] of Object.entries(others)) env.set(k, BigInt(v))
  for (const [j, a] of r.lhs.entries()) {
    if (typeof a === 'string' && isVar(a) && !env.has(a)) env.set(a, st.vals[j]!)
    else if (evalInt(a, env) !== st.vals[j]) return `rule ${rule}'s argument ${j} doesn't match`
  }
  const {others: need} = ruleVars(r)
  for (const v of need) if (!env.has(v)) return `rule ${rule}: no value for ${v}`
  if (!evalBool(r.guard, env)) return `rule ${rule}'s guard is false`
  return {loc: r.to, vals: r.rhs.map(a => evalInt(a, env))}
}

// A lasso: integers at the entrypoint, a stem of steps, then a cycle of steps (at least one) that comes back to the
// state it started from, so the cycle can repeat forever. Values are decimal strings (BigInt-safe).
export type Step = {rule: number, others: Record<string, string>}
export type Lasso = {start: string[], stem: Step[], cycle: Step[]}
export function checkLasso(t: Ari, w: Lasso): string | undefined {
  if (w.start.length !== t.funs.get(t.entry)) return 'the start has the wrong number of values'
  if (!w.cycle.length) return 'an empty cycle'
  let st: State = {loc: t.entry, vals: w.start.map(BigInt)}
  for (const [i, s] of w.stem.entries()) { const n = apply(t, st, s.rule, s.others); if (typeof n === 'string') return `stem step ${i}: ${n}`; st = n }
  const at = st
  for (const [i, s] of w.cycle.entries()) { const n = apply(t, st, s.rule, s.others); if (typeof n === 'string') return `cycle step ${i}: ${n}`; st = n }
  if (st.loc !== at.loc || st.vals.some((v, j) => v !== at.vals[j])) return 'the cycle does not come back to where it started'
  return undefined
}
