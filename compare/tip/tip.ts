// TIP's format (Tons of Inductive Problems, tip-org/benchmarks: SMT-LIB 2.6 with `declare-datatype(s)`, polymorphism by
// `par`, `define-fun(s)-rec`, `match`, `lambda` and `@`, one `prove` goal), read; and an evaluator of a TIP program on
// values. It uses no gdp-wired code: solve.ts checks a counterexample against the TIP goal with it, and the translation
// against the TIP functions on random values.
export type Sx = string | Sx[]
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
export const show = (s: Sx): string => (typeof s === 'string' ? s : `(${s.map(show).join(' ')})`)

// --- types ------------------------------------------------------------------------------------------------------------

// A sort: a type variable, a datatype or builtin (Int, Bool) at its arguments, or a function sort.
export type Ty = {k: 'var', name: string} | {k: 'con', name: string, args: Ty[]} | {k: 'fun', args: Ty[], ret: Ty}
export const showTy = (t: Ty): string => (t.k === 'var' ? t.name : t.k === 'con' ? (t.args.length ? `(${t.name} ${t.args.map(showTy).join(' ')})` : t.name) : `(=> ${[...t.args, t.ret].map(showTy).join(' ')})`)
export const INT: Ty = {k: 'con', name: 'Int', args: []}, BOOL: Ty = {k: 'con', name: 'Bool', args: []}
export function tyOf(s: Sx, tvars: Set<string>): Ty {
  if (typeof s === 'string') return tvars.has(s) ? {k: 'var', name: s} : {k: 'con', name: s, args: []}
  if (s[0] === '=>') { const ts = s.slice(1).map(x => tyOf(x, tvars)); return {k: 'fun', args: ts.slice(0, -1), ret: ts.at(-1)!} }
  return {k: 'con', name: s[0] as string, args: s.slice(1).map(x => tyOf(x, tvars))}
}
export const substTy = (t: Ty, m: Map<string, Ty>): Ty => (t.k === 'var' ? (m.get(t.name) ?? t) : t.k === 'con' ? {k: 'con', name: t.name, args: t.args.map(a => substTy(a, m))} : {k: 'fun', args: t.args.map(a => substTy(a, m)), ret: substTy(t.ret, m)})
export const sameTy = (a: Ty, b: Ty): boolean => showTy(a) === showTy(b)
// One-way matching of a declared sort (its variables `vs`) against an actual one, into `m`; false where they differ.
export function matchTy(decl: Ty, actual: Ty, vs: Set<string>, m: Map<string, Ty>): boolean {
  if (decl.k === 'var' && vs.has(decl.name)) {
    const had = m.get(decl.name)
    if (had) return sameTy(had, actual)
    m.set(decl.name, actual); return true
  }
  if (decl.k === 'var') return actual.k === 'var' && actual.name === decl.name
  if (decl.k === 'con') return actual.k === 'con' && actual.name === decl.name && actual.args.length === decl.args.length && decl.args.every((a, i) => matchTy(a, actual.args[i]!, vs, m))
  return actual.k === 'fun' && actual.args.length === decl.args.length && decl.args.every((a, i) => matchTy(a, actual.args[i]!, vs, m)) && matchTy(decl.ret, actual.ret, vs, m)
}

// --- the program ------------------------------------------------------------------------------------------------------

export type DataDecl = {name: string, params: string[], ctors: {name: string, fields: {name: string, ty: Ty}[]}[]}
export type FunDecl = {name: string, params: string[], args: {name: string, ty: Ty}[], ret: Ty, body: Sx, group: string[]}
export type Tip = {
  datas: Map<string, DataDecl>, funs: Map<string, FunDecl>,
  ctorOf: Map<string, {data: string, index: number}>, selectorOf: Map<string, {data: string, ctor: number, field: number}>,
  goal: {params: string[], body: Sx}, asserts: Sx[], sorts: string[], consts: string[],
}

export function parseTip(text: string): Tip {
  const tip: Tip = {datas: new Map(), funs: new Map(), ctorOf: new Map(), selectorOf: new Map(), goal: undefined as never, asserts: [], sorts: [], consts: []}
  const dataDecl = (name: string, s: Sx) => {
    let params: string[] = [], body = s as Sx[]
    if (Array.isArray(s) && s[0] === 'par') { params = s[1] as string[]; body = s[2] as Sx[] }
    const tv = new Set(params)
    const ctors = body.map(c => (typeof c === 'string' ? {name: c, fields: []} : {name: c[0] as string, fields: (c.slice(1) as Sx[][]).map(f => ({name: f[0] as string, ty: tyOf(f[1]!, tv)}))}))
    tip.datas.set(name, {name, params, ctors})
    ctors.forEach((c, i) => { tip.ctorOf.set(c.name, {data: name, index: i}); c.fields.forEach((f, j) => tip.selectorOf.set(f.name, {data: name, ctor: i, field: j})) })
  }
  const sig = (name: string, s: Sx[], group: string[]): Omit<FunDecl, 'body'> => {
    // (par (a ..) ((args) ret)) or (args) ret
    if (s[0] === 'par' || (Array.isArray(s[0]) && s.length === 1 && (s[0] as Sx[])[0] === 'par')) {
      const p = (s[0] === 'par' ? s : s[0]) as Sx[]
      const params = p[1] as string[], inner = p[2] as Sx[], tv = new Set(params)
      return {name, params, args: (inner[0] as Sx[][]).map(a => ({name: a[0] as string, ty: tyOf(a[1]!, tv)})), ret: tyOf(inner[1]!, tv), group}
    }
    return {name, params: [], args: (s[0] as Sx[][]).map(a => ({name: a[0] as string, ty: tyOf(a[1]!, new Set())})), ret: tyOf(s[1]!, new Set()), group}
  }
  for (const cmd of parseSx(text)) {
    if (!Array.isArray(cmd)) continue
    const op = cmd[0]
    if (op === 'declare-datatype') dataDecl(cmd[1] as string, cmd[2]!)
    else if (op === 'declare-datatypes') {
      const heads = cmd[1] as Sx[][], bodies = cmd[2] as Sx[]
      heads.forEach((h, i) => dataDecl(h[0] as string, bodies[i]!))
    } else if (op === 'define-fun-rec' || op === 'define-fun') {
      const name = cmd[1] as string, rest = cmd.slice(2)
      const s = sig(name, rest.slice(0, -1), [name])
      tip.funs.set(name, {...s, body: rest.at(-1)!})
    } else if (op === 'define-funs-rec') {
      const sigs = cmd[1] as Sx[][], bodies = cmd[2] as Sx[], names = sigs.map(s => (s[0] === 'par' ? ((s[2] as Sx[])[0] as string) : (s[0] as string)))
      sigs.forEach((s, i) => {
        // (name (args) ret) or (par (a) (name (args) ret))
        const d = s[0] === 'par' ? sig(names[i]!, ['par', s[1]!, (s[2] as Sx[]).slice(1)], names) : sig(names[i]!, s.slice(1), names)
        tip.funs.set(names[i]!, {...d, body: bodies[i]!})
      })
    } else if (op === 'prove') {
      const g = cmd[1]!
      tip.goal = Array.isArray(g) && g[0] === 'par' ? {params: g[1] as string[], body: g[2]!} : {params: [], body: g}
    } else if (op === 'assert') tip.asserts.push(cmd[1]!)
    else if (op === 'declare-sort') tip.sorts.push(cmd[1] as string)
    else if (op === 'declare-const' || op === 'declare-fun') tip.consts.push(cmd[1] as string)
    else if (op === 'check-sat' || op === 'set-logic' || op === 'set-info' || op === 'set-option' || op === 'exit') continue
    else throw new Unsupported(`the command ${String(op)}`)
  }
  if (!tip.goal) throw new Unsupported('no prove goal')
  return tip
}

// --- values -----------------------------------------------------------------------------------------------------------

// A datatype's value (its constructor and fields), an integer, a boolean, a function. An element of a sort variable
// instantiated at the naturals is an integer here too.
export type V = {c: string, a: V[]} | bigint | boolean | {fn: (args: V[]) => V}
export class OutOfFuel extends Error {}
export const showV = (v: V): string => (typeof v === 'bigint' ? String(v) : typeof v === 'boolean' ? String(v) : 'fn' in v ? '<fn>' : v.a.length ? `(${v.c} ${v.a.map(showV).join(' ')})` : v.c)
export function sameV(a: V, b: V): boolean {
  if (typeof a === 'bigint' || typeof a === 'boolean' || typeof b === 'bigint' || typeof b === 'boolean') return a === b
  if ('fn' in a || 'fn' in b) throw new Error('equality of functions')
  return a.c === b.c && a.a.length === b.a.length && a.a.every((x, i) => sameV(x, b.a[i]!))
}

// Evaluate a TIP term. Quantifiers are not evaluated (a goal's are bound by the caller); `fuel` bounds the calls.
export function evaluate(tip: Tip, s: Sx, env: Map<string, V>, fuel = {n: 200_000}): V {
  const go = (s: Sx, env: Map<string, V>): V => {
    if (typeof s === 'string') {
      if (env.has(s)) return env.get(s)!
      if (s === 'true') return true
      if (s === 'false') return false
      if (/^\d+$/.test(s)) return BigInt(s)
      if (tip.ctorOf.has(s)) return {c: s, a: []}
      if (tip.funs.has(s)) { const f = tip.funs.get(s)!; return f.args.length ? {fn: args => call(s, args)} : call(s, []) }
      throw new Error(`unbound ${s}`)
    }
    const head = s[0]!
    if (Array.isArray(head)) {
      // (_ f T ..) applied: the instantiation doesn't matter to the values
      if (head[0] === '_' || head[0] === 'as') return go([head[1]!, ...s.slice(1)], env)
      throw new Error(`head ${show(head)}`)
    }
    const args = () => s.slice(1).map(x => go(x, env))
    switch (head) {
      case '_': case 'as': return go(s[1]!, env)
      case 'ite': return go(s[1]!, env) ? go(s[2]!, env) : go(s[3]!, env)
      case 'and': return s.slice(1).every(x => go(x, env) === true)
      case 'or': return s.slice(1).some(x => go(x, env) === true)
      case 'not': return !go(s[1]!, env)
      case '=>': { const xs = s.slice(1); for (const x of xs.slice(0, -1)) if (!go(x, env)) return true; return go(xs.at(-1)!, env) }
      case '=': { const xs = args(); return xs.every((x, i) => i === 0 || sameV(xs[0]!, x)) }
      case 'distinct': { const xs = args(); return xs.every((x, i) => xs.every((y, j) => j <= i || !sameV(x, y))) }
      case '+': return (args() as bigint[]).reduce((a, b) => a + b)
      case '-': { const xs = args() as bigint[]; return xs.length === 1 ? -xs[0]! : xs.reduce((a, b) => a - b) }
      case '*': return (args() as bigint[]).reduce((a, b) => a * b)
      case 'div': { const [a, b] = args() as bigint[]; return smtDiv(a!, b!) }
      case 'mod': { const [a, b] = args() as bigint[]; return a! - b! * smtDiv(a!, b!) }
      case '<': { const [a, b] = args() as bigint[]; return a! < b! }
      case '<=': { const [a, b] = args() as bigint[]; return a! <= b! }
      case '>': { const [a, b] = args() as bigint[]; return a! > b! }
      case '>=': { const [a, b] = args() as bigint[]; return a! >= b! }
      case 'let': {
        const e2 = new Map(env)
        for (const b of s[1] as Sx[][]) e2.set(b[0] as string, go(b[1]!, env))
        return go(s[2]!, e2)
      }
      case 'lambda': {
        const ps = (s[1] as Sx[][]).map(b => b[0] as string), body = s[2]!
        return {fn: (xs: V[]) => { const e2 = new Map(env); ps.forEach((p, i) => e2.set(p, xs[i]!)); return go(body, e2) }}
      }
      case '@': { const [f, ...xs] = args(); return (f as {fn: (a: V[]) => V}).fn(xs) }
      case 'match': {
        const v = go(s[1]!, env) as {c: string, a: V[]}
        for (const c of s[2] as Sx[][]) {
          const pat = c[0]!
          if (pat === '_') return go(c[1]!, env)
          const name = typeof pat === 'string' ? pat : pat[0] as string
          if (name !== v.c) continue
          const e2 = new Map(env)
          if (Array.isArray(pat)) pat.slice(1).forEach((b, i) => e2.set(b as string, v.a[i]!))
          return go(c[1]!, e2)
        }
        throw new Error(`no case for ${v.c}`)
      }
      case 'forall': case 'exists': throw new Error('a quantifier inside a term')
    }
    if (tip.ctorOf.has(head)) return {c: head, a: args()}
    if (tip.selectorOf.has(head)) {
      const sel = tip.selectorOf.get(head)!, v = go(s[1]!, env) as {c: string, a: V[]}
      if (v.c !== tip.datas.get(sel.data)!.ctors[sel.ctor]!.name) throw new Error(`selector ${head} at ${v.c}`)
      return v.a[sel.field]!
    }
    if (head.startsWith('is-') && tip.ctorOf.has(head.slice(3))) return (go(s[1]!, env) as {c: string}).c === head.slice(3)
    if (env.has(head)) return (env.get(head) as {fn: (a: V[]) => V}).fn(args())
    if (tip.funs.has(head)) return call(head, args())
    throw new Error(`unknown ${head}`)
  }
  const call = (name: string, xs: V[]): V => {
    if (--fuel.n < 0) throw new OutOfFuel('out of fuel')
    const f = tip.funs.get(name)!
    return go(f.body, new Map(f.args.map((a, i) => [a.name, xs[i]!])))
  }
  return go(s, env)
}
// SMT-LIB's div: the floor for a positive divisor, the ceiling for a negative one (the remainder never negative).
const smtDiv = (a: bigint, b: bigint): bigint => {
  if (b === 0n) throw new Error('division by zero')
  const q = a / b, r = a - q * b
  return r < 0n ? (b > 0n ? q - 1n : q + 1n) : q
}

// A goal's variables (outer foralls, and foralls under the conclusion of an implication) and the rest of it; an exists
// anywhere, or a forall elsewhere, is refused.
export function prenex(s: Sx): {vars: {name: string, ty: Sx}[], body: Sx} {
  if (Array.isArray(s) && s[0] === 'forall') {
    const inner = prenex(s[2]!)
    return {vars: [...(s[1] as Sx[][]).map(b => ({name: b[0] as string, ty: b[1]!})), ...inner.vars], body: inner.body}
  }
  if (Array.isArray(s) && s[0] === '=>') {
    const xs = s.slice(1), inner = prenex(xs.at(-1)!)
    for (const x of xs.slice(0, -1)) noQuant(x)
    return {vars: inner.vars, body: inner.vars.length ? ['=>', ...xs.slice(0, -1), inner.body] : s}
  }
  noQuant(s)
  return {vars: [], body: s}
}
// An existential at the goal's end (under its foralls and its implications' conclusions: ∀ v. H ⇒ ∃ x. B), and the goal
// with something else in its place (the goal's variables, its hypotheses, B's binders and body as the caller rewrites
// them). Undefined where there is none, or one elsewhere (refused as before, by prenex).
export function existential(s: Sx): {binders: {name: string, ty: Sx}[], body: Sx, with: (e: Sx) => Sx} | undefined {
  if (!Array.isArray(s)) return undefined
  if (s[0] === 'exists') return {binders: (s[1] as Sx[][]).map(b => ({name: b[0] as string, ty: b[1]!})), body: s[2]!, with: e => e}
  if (s[0] === 'forall' || s[0] === '=>') {
    const at = s.length - 1, inner = existential(s[at]!)
    return inner && {...inner, with: e => [...s.slice(0, at), inner.with(e)]}
  }
  return undefined
}
// s with each free occurrence of a name replaced by a term (a binder of the same name inside hides it).
export function substSx(s: Sx, name: string, by: Sx): Sx {
  if (typeof s === 'string') return s === name ? by : s
  if ((s[0] === 'forall' || s[0] === 'exists' || s[0] === 'lambda') && (s[1] as Sx[][]).some(b => b[0] === name)) return s
  if (s[0] === 'let' && (s[1] as Sx[][]).some(b => b[0] === name)) return ['let', (s[1] as Sx[][]).map(b => [b[0]!, substSx(b[1]!, name, by)]), s[2]!]
  if (s[0] === 'match') return ['match', substSx(s[1]!, name, by), (s[2] as Sx[][]).map(c => (Array.isArray(c[0]) && (c[0] as Sx[]).includes(name) ? c : [c[0]!, substSx(c[1]!, name, by)]))]
  return s.map((x, i) => (i === 0 ? x : substSx(x, name, by)))
}
function noQuant(s: Sx): void {
  if (!Array.isArray(s)) return
  if (s[0] === 'exists') throw new Unsupported('an existential goal')
  if (s[0] === 'forall') throw new Unsupported('a quantifier under a connective other than an implication\'s conclusion')
  s.forEach(noQuant)
}
