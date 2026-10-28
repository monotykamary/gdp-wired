// CHC-COMP's format (https://chc-comp.github.io/format.html), read: S-expressions, the predicates and their sorts, and
// each clause as its variables, the predicates its body applies, its constraint (a list of conjuncts) and its head (a
// predicate applied, or false). `parseChc` reads Int and Bool alone and refuses anything else with the reason;
// `parseHorn` is the same reader with the sorts and the commands it skips its caller's (compare/chc-adt reads datatypes).
export type Sx = string | Sx[]
export type Sort = 'Int' | 'Bool'
export type App = {pred: string, args: Sx[]}
export type Clause<S = Sort> = {vars: Map<string, S>, body: App[], constraint: Sx[], head: App | null}
export type Chc<S = Sort> = {preds: Map<string, S[]>, clauses: Clause<S>[]}

export class Unsupported extends Error {}

export function parseSx(text: string): Sx[] {
  const out: Sx[] = [], stack: Sx[][] = [out]
  const re = /\s+|;[^\n]*|\(|\)|\|[^|]*\||"(?:[^"]|"")*"|[^\s()|;"]+/g
  for (const m of text.matchAll(re)) {
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

const sortOf = (s: Sx): Sort => {
  if (s === 'Int' || s === 'Bool') return s
  throw new Unsupported(`the sort ${JSON.stringify(s)}`)
}
const conjuncts = (s: Sx): Sx[] => (Array.isArray(s) && s[0] === 'and' ? s.slice(1).flatMap(conjuncts) : s === 'true' ? [] : [s])

export const parseChc = (text: string): Chc => parseHorn(text, sortOf)
export function parseHorn<S>(text: string, sortOf: (s: Sx) => S, skip: (cmd: Sx[]) => boolean = () => false): Chc<S> {
  const preds = new Map<string, S[]>(), clauses: Clause<S>[] = []
  const appOf = (s: Sx): App | undefined => {
    if (typeof s === 'string') return preds.has(s) ? {pred: s, args: []} : undefined
    return typeof s[0] === 'string' && preds.has(s[0]) ? {pred: s[0], args: s.slice(1)} : undefined
  }
  for (const cmd of parseSx(text)) {
    if (!Array.isArray(cmd) || skip(cmd)) continue
    const [op] = cmd
    if (op === 'set-logic' || op === 'check-sat' || op === 'exit' || op === 'set-info' || op === 'set-option' || op === 'get-model') continue
    if (op === 'declare-fun') {
      const [, name, args, ret] = cmd as [string, string, Sx[], Sx]
      if (ret !== 'Bool') throw new Unsupported(`${name} returns ${JSON.stringify(ret)}`)
      preds.set(name, args.map(sortOf))
      continue
    }
    if (op !== 'assert') throw new Unsupported(`the command ${String(op)}`)
    let f = cmd[1]!
    const vars = new Map<string, S>()
    if (Array.isArray(f) && f[0] === 'forall') {
      for (const b of f[1] as Sx[][]) vars.set(b[0] as string, sortOf(b[1]!))
      f = f[2]!
    }
    let body: Sx[] = [], head: Sx = f
    if (Array.isArray(f) && f[0] === '=>') { body = conjuncts(f[1]!); head = f[2]! } else if (Array.isArray(f) && f[0] === 'not' && Array.isArray(f[1]) && f[1][0] === 'exists') {
      for (const b of f[1][1] as Sx[][]) vars.set(b[0] as string, sortOf(b[1]!))
      body = conjuncts(f[1][2]!); head = 'false'
    }
    const apps: App[] = [], constraint: Sx[] = []
    for (const c of body) { const a = appOf(c); if (a) apps.push(a); else constraint.push(c) }
    const h = head === 'false' ? null : appOf(head) ?? null
    if (head !== 'false' && !h) throw new Unsupported(`a head that applies no predicate: ${JSON.stringify(head).slice(0, 80)}`)
    clauses.push({vars, body: apps, constraint, head: h})
  }
  return {preds, clauses}
}

// A clause's constraint, evaluated on values (no gdp-wired code): what checks a run the rule took against the CHC.
export type Val = bigint | boolean
export function evalSx(s: Sx, env: Map<string, Val>): Val {
  if (typeof s === 'string') {
    if (s === 'true') return true
    if (s === 'false') return false
    if (/^\d+$/.test(s)) return BigInt(s)
    const v = env.get(s)
    if (v === undefined) throw new Error(`unbound ${s}`)
    return v
  }
  const [op, ...xs] = s as [string, ...Sx[]]
  if (op === 'let') {
    const inner = new Map(env)
    for (const b of xs[0] as Sx[][]) inner.set(b[0] as string, evalSx(b[1]!, env))
    return evalSx(xs[1]!, inner)
  }
  const i = (k: number) => evalSx(xs[k]!, env) as bigint, b = (k: number) => evalSx(xs[k]!, env) as boolean
  const all = xs.map(x => evalSx(x, env))
  const floorDiv = (a: bigint, k: bigint) => { const q = a / k; return a % k !== 0n && (a < 0n) !== (k < 0n) ? q - 1n : q }
  switch (op) {
    case '+': return (all as bigint[]).reduce((a, c) => a + c, 0n)
    case '-': return xs.length === 1 ? -i(0) : (all as bigint[]).slice(1).reduce((a, c) => a - c, all[0] as bigint)
    case '*': return (all as bigint[]).reduce((a, c) => a * c, 1n)
    case 'div': { const k = i(1); if (k <= 0n) throw new Error('div by a non-positive'); return floorDiv(i(0), k) }
    case 'mod': { const k = i(1); if (k <= 0n) throw new Error('mod by a non-positive'); return i(0) - k * floorDiv(i(0), k) }
    case 'abs': return i(0) < 0n ? -i(0) : i(0)
    case '<=': return all.slice(1).every((c, k) => (all[k] as bigint) <= (c as bigint))
    case '<': return all.slice(1).every((c, k) => (all[k] as bigint) < (c as bigint))
    case '>=': return all.slice(1).every((c, k) => (all[k] as bigint) >= (c as bigint))
    case '>': return all.slice(1).every((c, k) => (all[k] as bigint) > (c as bigint))
    case '=': return all.slice(1).every(c => c === all[0])
    case 'distinct': return new Set(all).size === all.length
    case 'and': return all.every(Boolean)
    case 'or': return all.some(Boolean)
    case 'not': return !b(0)
    case '=>': return !b(0) || b(1)
    case 'xor': return b(0) !== b(1)
    case 'ite': return b(0) ? evalSx(xs[1]!, env) : evalSx(xs[2]!, env)
    default: throw new Error(`the operator ${op}`)
  }
}
