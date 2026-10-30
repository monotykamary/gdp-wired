// Laws in the code's own terms, one syntax for every language the extractor reads: a comment (`# gdp: law <name>:
// <expr>`, `// gdp: law ...`, `-- ` or `%`), an annotation (`@GdpLaw("<name>: <expr>")`, `@gdp.law(...)`, `@gdp_law ...`)
// or a Rust doc attribute (`#[doc = "gdp: law ..."]`), read from the code's text as the boundary's `gdp:` tags are
// (core/extract-step.ts), so a macro can emit the same text later. Each is parsed here into the builders' law
// (core/dsl.ts) through the extraction's names (Extraction.names: each rule variable's path in the code), never guessed:
// a name the code doesn't have is refused with the names it has.
//
// The law's view of a step, the same in every language (and what a typed law could target later): the state after the
// step by its fields (or after.x), the state before it as old(x) or before.x, the request's arguments by name, `result`
// (the method's) and `failed` (with failures: 'kept'), the constructor's arguments (params) where no field shadows them,
// an answered call as f(...). A law that reads only the state, placed outside any method, holds in every state; any other
// is a law of one step (of the method it is written on). Anything else is refused with why, never dropped, and a law is
// known by its name: two of one name in a rule are refused.
//
//   x <= cap and not failed            comparisons (< <= > >= == !=), + − and × a constant, // and % by one, and or not
//   failed implies spend >= budget     implies (=>), parentheses, min max abs, true false None (nil, null)
//   self.tokens <= self.capacity       the state by its fields (self., this., @ or a receiver's name, or bare)
//   result == (n <= old(tokens))       a request's arguments by name, `result`, `failed`, old(x) or before.x the state
//                                      before the step (a law reading any of these is a law of one step)
//   team.max_budget is None            None-ness (is None, is not None, == nil, != null), an object's fields
//   get_current_spend(...) >= 0        a call of other code answered by the request, by its name
//   counts[user] < limit, user in m    a map at a key as the code reads it (m.get(k), k in m, m[k] is None)
//   cache["hits:" + s] <= limit        a store at its key's template ("hits:" + s, f"hits:{s}")
//   forall k in budgets: budgets[k].spent <= budgets[k].limit       every key the map holds (at the top of the law)
//   mode == "closed", outcome == SLOW_ERROR, mode == :closed        a choice by its value
import {type Cond, Choice, Int, Str, Term, all, any, forall, no, not, yes} from './dsl.ts'
import type {Extraction, Name} from './extract.ts'

export type LawText = {name: string, expr: string, where?: string, line?: number, method?: string}
// A law read: an invariant (`law`) or a law of one step (`step`, for the method `method` where the rule has several).
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export type Built = {kind: 'law' | 'step', law: any, method?: string}
export class LawError extends Error {}

// --- reading the code's text -------------------------------------------------------------------------------------------
// Every law stated in a file's text, with its line.
const FORMS = [
  /(?:#|\/\/|--|%|\/\*|^\s*\*)\s*gdp:\s*law\s+([^:]+?)\s*(?::\s*(.+?))?\s*(?:\*\/)?\s*$/,
  /@(?:GdpLaw|gdp\.law|gdp_law)\s*\(?\s*(?:value\s*=\s*)?"((?:[^"\\]|\\.)*)"/,
  /#\[doc\s*=\s*"\s*gdp:\s*law\s+((?:[^"\\]|\\.)*)"\s*\]/,
  /@(?:GdpLaw|gdp\.law|gdp_law)\s*\(?\s*'((?:[^'\\]|\\.)*)'/,
]
export function lawsIn(text: string, where = ''): LawText[] {
  const out: LawText[] = []
  text.split('\n').forEach((l, i) => {
    for (const [k, re] of FORMS.entries()) {
      const m = re.exec(l)
      if (!m) continue
      const body = k === 0 ? (m[2] ? `${m[1]}: ${m[2]}` : m[1]!) : m[1]!.replace(/\\(.)/g, '$1').replace(/^\s*gdp:\s*law\s+/, '')
      const c = body.indexOf(':')
      out.push(c > 0 ? {name: body.slice(0, c).trim(), expr: body.slice(c + 1).trim(), where: `${where}:${i + 1}`, line: i + 1} : {name: body.trim(), expr: '', where: `${where}:${i + 1}`, line: i + 1})
      break
    }
  })
  return out
}

// --- the expression's syntax ---------------------------------------------------------------------------------------------
type Seg = {f: string} | {i: X} | {call: true, args?: string}
type X = {k: 'num', v: number} | {k: 'str', v: string, holes?: X[], parts?: string[]} | {k: 'bool', v: boolean} | {k: 'null'}
  | {k: 'path', head: string, segs: Seg[]} | {k: 'un', op: '-' | 'not', x: X}
  | {k: 'bin', op: string, a: X, b: X} | {k: 'old', x: X} | {k: 'fn', f: string, xs: X[]} | {k: 'forall', v: string, over: X, body: X}
const WORDS: Record<string, string> = {'->': '.', '::': '.', and: '&&', or: '||', not: '!', implies: '=>', '∧': '&&', '∨': '||', '¬': '!', '→': '=>', '==>': '=>', '≤': '<=', '≥': '>=', '≠': '!=', '∀': 'forall', AND: '&&', OR: '||', NOT: '!'}
function tokens(s: string): string[] {
  const out: string[] = [], re = /\s*(f?"(?:[^"\\]|\\.)*"|f?'(?:[^'\\]|\\.)*'|`[^`]*`|\d+(?:\.\d+)?|@?[A-Za-z_][\w?]*|->|::|==>|=>|<=|>=|==|!=|&&|\|\||\/\/|[-+*%/<>()[\],.:!∧∨¬→≤≥≠∀])/y
  let m: RegExpExecArray | null, at = 0
  while ((m = re.exec(s))) { out.push(WORDS[m[1]!] ?? m[1]!); at = re.lastIndex }
  if (s.slice(at).trim()) throw new LawError(`can't read ${JSON.stringify(s.slice(at).trim())}`)
  return out
}
export function parse(s: string): X {
  const t = tokens(s)
  let i = 0
  const peek = () => t[i], eat = (x?: string) => { const v = t[i++]; if (x !== undefined && v !== x) throw new LawError(`expected ${x} at ${JSON.stringify(v ?? 'the end')}`); return v! }
  const operand = (p = t[i - 1]) => p !== undefined && /^[\w@"'`)\]]/.test(p) && !['&&', '||', '!', '=>', 'forall', 'in', 'is'].includes(p)
  const top = (): X => {
    if (peek() === 'forall' || peek() === 'all' && t[i + 2] === 'in') { eat(); const v = eat(); eat('in'); const over = sum(); eat(':'); return {k: 'forall', v, over, body: top()} }
    const a = or()
    return peek() === '=>' ? (eat(), {k: 'bin', op: '=>', a, b: top()}) : a
  }
  // (a level of left-associative operators over the next level)
  const left = (ops: string[], next: () => X) => (): X => { let a = next(); while (ops.includes(peek()!)) { const op = eat(); a = {k: 'bin', op, a, b: next()} } return a }
  const or = left(['||'], () => and()), and = left(['&&'], () => neg())
  const neg = (): X => (peek() === '!' ? (eat(), {k: 'un', op: 'not', x: neg()}) : cmp())
  const cmp = (): X => {
    const a = sum(), op = peek()
    if (op === 'is') { eat(); const n = peek() === '!' ? (eat(), true) : false; const b = sum(); return n ? {k: 'un', op: 'not', x: {k: 'bin', op: '==', a, b}} : {k: 'bin', op: '==', a, b} }
    if (op === '!' && t[i + 1] === 'in') { eat(); eat(); return {k: 'un', op: 'not', x: {k: 'bin', op: 'in', a, b: sum()}} }
    if (op && ['<', '<=', '>', '>=', '==', '!=', 'in'].includes(op)) { eat(); return {k: 'bin', op, a, b: sum()} }
    return a
  }
  const sum = left(['+', '-'], () => prod()), prod = left(['*', '//', '/', '%'], () => unary())
  const unary = (): X => (peek() === '-' ? (eat(), {k: 'un', op: '-', x: unary()}) : atom())
  const atom = (): X => {
    const x = eat()
    if (x === undefined) throw new LawError('the expression ends early')
    if (x === '(') { const e = top(); eat(')'); return e }
    if (/^\d/.test(x)) { if (x.includes('.') && !/\.0+$/.test(x)) throw new LawError(`${x}: a number that isn't whole`); return {k: 'num', v: Number(x)} }
    if (/^f?["'`]/.test(x)) return str(x)
    if (x === ':' && /^[A-Za-z_]/.test(peek() ?? '') && !operand(t[i - 2])) return {k: 'str', v: eat()}
    if (['true', 'True'].includes(x)) return {k: 'bool', v: true}
    if (['false', 'False'].includes(x)) return {k: 'bool', v: false}
    if (['None', 'nil', 'null', 'undefined', 'NULL', 'nullptr'].includes(x)) return {k: 'null'}
    if (!/^@?[A-Za-z_]/.test(x)) throw new LawError(`unexpected ${JSON.stringify(x)}`)
    if (x === 'old' && peek() === '(') { eat(); const e = top(); eat(')'); return {k: 'old', x: e} }
    if (['min', 'max', 'abs'].includes(x) && peek() === '(') { eat(); const xs = [top()]; while (peek() === ',') { eat(); xs.push(top()) } eat(')'); return {k: 'fn', f: x, xs} }
    const p: X & {k: 'path'} = {k: 'path', head: x, segs: []}
    for (;;) {
      if (peek() === '.') { eat(); p.segs.push({f: eat()}) }
      else if (peek() === '[') { eat(); p.segs.push({i: top()}); eat(']') }
      else if (peek() === '(') {
        eat(); const from = i; let d = 1
        while (d && i < t.length) { const y = eat(); d += y === '(' ? 1 : y === ')' ? -1 : 0 }
        const inner = t.slice(from, i - 1).join('')
        p.segs.push({call: true, ...(inner && inner !== '...' ? {args: inner} : {})})
      }
      else break
    }
    if ((p.head === 'before' || p.head === 'after') && p.segs.length && 'f' in p.segs[0]!) { const q: X = {k: 'path', head: p.segs[0].f, segs: p.segs.slice(1)}; return p.head === 'before' ? {k: 'old', x: q} : q }
    return p
  }
  // A string: a literal, or a template (f"rl:{k}", `rl:${k}`, "rl:#{k}") as its text and holes.
  const str = (x: string): X => {
    const f = x.startsWith('f'), body = x.slice(f ? 2 : 1, -1)
    const re = f ? /\{([^}]*)\}/g : x.startsWith('`') ? /\$\{([^}]*)\}/g : /#\{([^}]*)\}/g, parts: string[] = [], holes: X[] = []
    let last = 0
    for (const m of body.matchAll(re)) { parts.push(body.slice(last, m.index)); holes.push(parse(m[1]!)); last = m.index! + m[0].length }
    return holes.length ? {k: 'str', v: '', parts: [...parts, body.slice(last)], holes} : {k: 'str', v: body.replace(/\\(.)/g, '$1')}
  }
  const e = top()
  if (i < t.length) throw new LawError(`unexpected ${JSON.stringify(t[i])}`)
  return e
}

// --- the law built on the rule ---------------------------------------------------------------------------------------------
// A value: a number (an integer of the builders'), a condition, a string, a choice, a literal string, None, a map's
// cell, a value that may be None (its flag beside it), a map, a key.
type V = {t: 'num', v: Int} | {t: 'cond', v: Cond} | {t: 'str', v: Str} | {t: 'choice', v: Choice<string>} | {t: 'lit', v: string, err?: LawError}
  | {t: 'null'} | {t: 'cell', rec: Record<string, unknown>, fields: string[]} | {t: 'opt', none: Cond, v?: V} | {t: 'map', n: Name, maps: Name[]} | {t: 'key', v: Term}
type Ctx = {b: Record<string, unknown>, a: Record<string, unknown>, step: boolean, method?: string, keys: Map<string, Term>, roles: Set<string>, methods: Set<string>}

// The law a text states, built on the extraction's rule through its names.
export function buildLaw(x: Extraction, l: LawText): Built {
  const names = x.names ?? [], r = x.rule as unknown as {law: (n: string, f: (e: never) => unknown) => unknown, stepLaw: (n: string, f: (b: never, a: never) => unknown, w?: (b: never) => Cond) => unknown}
  if (!r) throw new LawError('the extraction has no rule')
  if (!l.expr) throw new LawError(`${l.name}: a law is stated as <name>: <expr>`)
  const e = parse(l.expr)
  // A first reading finds what the law reads: a request, a result, the failure or the state before make it a step law.
  const probe: Ctx = {b: {}, a: {}, step: true, method: l.method, keys: new Map(), roles: new Set(), methods: new Set()}
  read(e, probe, names, true)
  // (a law on a method, the line above it, is a law of its step: the state after it, old(x) before)
  const step = !!l.method || ['input', 'answer', 'result', 'failed', 'clock', 'method', 'old'].some(k => probe.roles.has(k))
  const method = probe.methods.size === 1 ? [...probe.methods][0] : l.method
  if (probe.methods.size > 1) throw new LawError(`it reads the arguments of ${[...probe.methods].join(' and ')}: a law of one step is about one method`)
  const gate = step && method && names.some(n => n.role === 'method') ? method : undefined
  const body = (b: Record<string, unknown>, a: Record<string, unknown>) => read(e, {b, a, step, method, keys: new Map(), roles: new Set(), methods: new Set()}, names, false) as Cond
  if (!step) return {kind: 'law', law: r.law(l.name, (env: never) => body(env, env))}
  const mname = names.find(n => n.role === 'method')?.rule
  return {kind: 'step', ...(gate ? {method: gate} : {}), law: r.stepLaw(l.name, (b: never, a: never) => body(b, a), gate ? (b: never) => ((b as Record<string, unknown>)[mname!] as Choice<string>).is(gate) : undefined)}
}

// The expression read: its value (`dry`: only which names it reads, nothing built).
function read(e: X, c: Ctx, names: Name[], dry: boolean): unknown {
  if (e.k === 'forall') {
    const over = val(e.over, c, names, dry)
    if (over.t !== 'map') throw new LawError(`forall ${e.v} in ...: over a map (a dict, a Map, a hash)`)
    if (dry) { c.keys.set(e.v, new Term({op: 'const', value: 0})); return cond(val(e.body, c, names, true)) }
    return forall(k => { c.keys.set(e.v, k); const m = (c.step ? c.a : c.b)[over.n.rule] as {at: (k: Term) => Record<string, unknown>}; return (m.at(k).has as Cond).implies(cond(val(e.body, c, names, false))) })
  }
  return cond(val(e, c, names, dry))
}
const cond = (v: V): Cond => {
  if (v.t === 'cond') return v.v
  if (v.t === 'opt' && v.v?.t === 'cond') return v.v.v
  throw new LawError(`a ${v.t === 'num' ? 'number' : v.t} where a condition is read`)
}
const num = (v: V): Int => {
  if (v.t === 'num') return v.v
  if (v.t === 'opt' && v.v?.t === 'num') return v.v.v
  if (v.t === 'cell' && v.fields.length === 1) return Int.of(v.rec[v.fields[0]!] as Term)
  if (v.t === 'key') return Int.of(v.v)
  throw new LawError(`a ${v.t} where a number is read`)
}
// A value of the rule's environment as the law reads it.
const wrap = (x: unknown): V => (x instanceof Int ? {t: 'num', v: x} : x instanceof Term ? {t: 'num', v: Int.of(x)} : x instanceof Choice ? {t: 'choice', v: x} : x instanceof Str ? {t: 'str', v: x} : {t: 'cond', v: x as Cond})
const DRY: V = {t: 'num', v: Int.of(0)}

function val(e: X, c: Ctx, names: Name[], dry: boolean): V {
  const go = (x: X) => val(x, c, names, dry)
  switch (e.k) {
    case 'num': return {t: 'num', v: Int.of(e.v)}
    case 'bool': return {t: 'cond', v: e.v ? yes : no}
    case 'null': return {t: 'null'}
    case 'str': if (e.holes) throw new LawError('a string template outside a store\'s key'); return {t: 'lit', v: e.v}
    case 'old': { c.roles.add('old'); return val(e.x, {...c, a: c.b}, names, dry) }
    case 'fn': {
      const xs = e.xs.map(go)
      if (dry) return DRY
      if (e.f === 'abs') return {t: 'num', v: Int.of(num(xs[0]!).abs)}
      return {t: 'num', v: xs.slice(1).reduce((m, y) => (e.f === 'min' ? m.min(num(y)) : m.max(num(y))), num(xs[0]!))}
    }
    case 'un': { const v = go(e.x); if (dry) return v.t === 'cond' ? v : DRY; return e.op === '-' ? {t: 'num', v: num(v).negate()} : {t: 'cond', v: not(cond(v))} }
    case 'bin': {
      if (e.op === 'in') { const m = go(e.b); if (m.t !== 'map') throw new LawError('x in m: m a map'); const k = go(e.a); return dry ? {t: 'cond', v: yes} : {t: 'cond', v: cellOf(m, key(k), c).rec.has as Cond} }
      // (a name the rule doesn't have, compared with a choice: the choice's value, Outcome.SLOW_ERROR)
      const lit = (x: X): V => { try { return go(x) } catch (err) { if (x.k !== 'path' || !(err instanceof LawError) || !['==', '!='].includes(e.op)) throw err; return {t: 'lit', v: lastName(x) ?? '', err} } }
      const a = lit(e.a), b = lit(e.b)
      if (a.t === 'lit' && a.err && b.t === 'lit' && b.err) throw a.err
      if (['&&', '||', '=>'].includes(e.op)) return dry ? {t: 'cond', v: yes} : {t: 'cond', v: e.op === '&&' ? all(cond(a), cond(b)) : e.op === '||' ? any(cond(a), cond(b)) : cond(a).implies(cond(b))}
      if (dry) return ['+', '-', '*', '//', '/', '%'].includes(e.op) ? DRY : {t: 'cond', v: yes}
      if (e.op === '+' || e.op === '-') return {t: 'num', v: e.op === '+' ? num(a).plus(num(b)) : num(a).minus(num(b))}
      if (e.op === '*') { const k = constOf(e.a) ?? constOf(e.b); if (k === undefined) throw new LawError('× by a constant only (a product of two values is outside linear arithmetic)'); return {t: 'num', v: num(constOf(e.a) === undefined ? a : b).times(k)} }
      if (e.op === '//' || e.op === '/' || e.op === '%') { const k = constOf(e.b); if (!k || k < 1) throw new LawError(`${e.op} by a positive constant only`); return e.op === '%' ? {t: 'num', v: Int.of(num(a).modBy(k))} : {t: 'num', v: num(a).divBy(k)} }
      return {t: 'cond', v: compare(e.op, a, b, e)}
    }
    case 'path': return path(e, c, names, dry)
    case 'forall': return fail('forall ... in ...: at the top of the law only')
  }
  return fail('an expression of no kind')
}
// (a path's last name: a choice's value written as one, Outcome.SLOW_ERROR)
const lastName = (x: X & {k: 'path'}): string | undefined => (x.segs.length ? (x.segs.at(-1) as {f?: string}).f : x.head)
const constOf = (x: X): number | undefined => (x.k === 'num' ? x.v : x.k === 'un' && x.op === '-' && x.x.k === 'num' ? -x.x.v : undefined)
function compare(op: string, a: V, b: V, e: X & {k: 'bin'}): Cond {
  if (b.t === 'null' || a.t === 'null') {
    const o = a.t === 'null' ? b : a, none = o.t === 'opt' ? o.none : o.t === 'cell' ? not(o.rec.has as Cond) : undefined
    if (!none) throw new LawError(`${show(a.t === 'null' ? e.b : e.a)} is never None here (the rule holds no None for it)`)
    return op === '==' ? none : op === '!=' ? not(none) : fail(`${op} with None`)
  }
  const un = (v: V): V => (v.t === 'opt' && v.v ? v.v : v)
  a = un(a); b = un(b)
  // (a name the rule doesn't have is a choice's value only beside a choice)
  for (const [v, o] of [[a, b], [b, a]]) if (v!.t === 'lit' && v!.err && o!.t !== 'choice') throw v!.err
  const eq = (c: Cond) => (op === '==' ? c : op === '!=' ? not(c) : fail(`${op} of values that aren't numbers`))
  if (a.t === 'choice' || b.t === 'choice') {
    const [ch, o, ox] = a.t === 'choice' ? [a.v, b, e.b] : [(b as {v: Choice<string>}).v, a, e.a]
    if (o.t === 'choice') return eq(ch.eq(o.v))
    const lit = o.t === 'lit' ? o.v : ox.k === 'path' ? lastName(ox) : undefined
    if (lit === undefined || !ch.values.includes(lit)) throw new LawError(`${show(ox)} isn't one of ${ch.values.join(', ')}`)
    return eq(ch.is(lit))
  }
  if (a.t === 'str' || b.t === 'str') { const [s, o] = a.t === 'str' ? [a.v, b] : [(b as {v: Str}).v, a]; return eq(o.t === 'str' ? s.eq(o.v) : o.t === 'lit' ? s.eq(o.v) : fail('a string compared with what isn\'t one')) }
  if (a.t === 'cond' && b.t === 'cond') return eq(a.v.iff(b.v))
  const x = num(a), y = num(b)
  return op === '<' ? x.lt(y) : op === '<=' ? x.atMost(y) : op === '>' ? x.gt(y) : op === '>=' ? x.atLeast(y) : op === '==' ? x.eq(y) : x.ne(y)
}
const fail = (s: string): never => { throw new LawError(s) }
const show = (x: X): string => (x.k === 'path' ? [x.head, ...x.segs.map(s => ('f' in s ? `.${s.f}` : 'i' in s ? '[...]' : '(...)'))].join('') : x.k === 'str' ? JSON.stringify(x.v) : x.k)
// A map's key as the rule holds it: a string's id, a natural.
const key = (k: V): Term => (k.t === 'opt' && k.v ? key(k.v) : k.t === 'key' ? k.v : k.t === 'str' ? k.v.id : k.t === 'lit' ? fail('a literal key (the rule keys a map by the request\'s values)') : (() => { const n = num(k); return n.neg.e.op === 'const' && n.neg.e.value === 0 ? n.pos : n.clamped })())
function cellOf(m: V & {t: 'map'}, k: Term, c: Ctx): {rec: Record<string, unknown>, fields: string[]} {
  const map = (c.a[m.n.rule] ?? c.b[m.n.rule]) as {at: (k: Term) => Record<string, unknown>}
  return {rec: map.at(k), fields: m.n.map!.fields}
}

// A path: the longest prefix of it the code names (in the law's method first: its arguments shadow the fields, as in the
// code), then its fields, keys and calls.
function path(e: X & {k: 'path'}, c: Ctx, names: Name[], dry: boolean): V {
  if (c.keys.has(e.head) && !e.segs.length) return {t: 'key', v: c.keys.get(e.head)!}
  if (e.head === 'result' || e.head === 'failed') {
    const n = e.head === 'failed' ? names.find(x => x.role === 'failed') : results(names, c)
    if (!n) throw new LawError(e.head === 'failed' ? 'the rule keeps no failure (with failures: \'kept\' it does: `failures = "kept"` in gdp.toml or --failures kept)' : 'the method returns nothing the rule keeps')
    c.roles.add(n.role); if (n.method) c.methods.add(n.method)
    return rest(e.segs, leaf(n, c, dry), c, names, dry, e)
  }
  const explicit = ['self', 'this', 'state', 's'].includes(e.head) || e.head.startsWith('@')
  const parts = [e.head.replace(/^@/, ''), ...e.segs.map(s => ('f' in s ? s.f : undefined))]
  const heads = explicit && !e.head.startsWith('@') ? [parts.slice(1)] : [parts, ...(parts.length > 1 && parts[1] !== undefined ? [parts.slice(1)] : [])]
  for (const [hi, p] of heads.entries()) {
    const fields: string[] = []
    for (const s of p) { if (s === undefined) break; fields.push(s) }
    const skip = parts.length - p.length
    for (let n = fields.length; n > 0; n--) {
      const code = fields.slice(0, n).join('.'), next = e.segs[skip + n - 1]
      const hit = find(code, names, c, explicit || hi > 0, next !== undefined && 'call' in next)
      if (hit) {
        c.roles.add(hit.role); if (hit.method) c.methods.add(hit.method)
        // (an answered call is one value a step, whatever its arguments: written f(...) or f())
        if (hit.role === 'answer' && next && 'call' in next && next.args) throw new LawError(`${code}(${next.args}): an answered call's value is the request's, one a step: write it ${code}(...)`)
        const segs = e.segs.slice(skip + n - 1 + (hit.role === 'answer' && next && 'call' in next ? 1 : 0))
        return rest(segs, hit.map ? {t: 'map', n: hit, maps: names.filter(x => x.map && x.code === hit.code)} : leaf(hit, c, dry), c, names, dry, e)
      }
    }
  }
  // A method's argument by its method's name (charge.user), where several methods take one of that name.
  const m = names.find(n => n.role === 'input' && n.method === e.head && e.segs[0] && 'f' in e.segs[0] && n.code === e.segs[0].f)
  if (m) { c.roles.add('input'); c.methods.add(m.method!); return rest(e.segs.slice(1), leaf(m, c, dry), c, names, dry, e) }
  const known = [...new Set(names.filter(n => n.rule || n.none).map(n => (n.role === 'answer' ? `${n.code.split('.').pop()}()` : n.method && n.role === 'input' ? `${n.code} (${n.method})` : n.code)))]
  throw new LawError(`no ${show(e)} in the rule (its names: ${known.join(', ')})`)
}
// The name a code path is: the law's method's argument, a field of the state, a constructor's argument, an answered
// call (by its callee's last name), the rule's own name (as printed).
function find(code: string, names: Name[], c: Ctx, stateOnly: boolean, called: boolean): Name | undefined {
  const last = (n: Name) => n.code.split('.').pop() === code.split('.').pop() && (code.split('.').length === 1 || n.code.endsWith(code))
  const at = (n: Name) => n.code.replace(/^@/, '') === code
  const inputs = names.filter(n => n.role === 'input' && n.code === code)
  if (!stateOnly && !called && inputs.length) {
    const here = inputs.filter(n => n.method === c.method)
    if (here.length) return here[0]
    if (new Set(inputs.map(n => n.method)).size === 1) return inputs[0]
    throw new LawError(`${code} is an argument of ${inputs.map(n => n.method).join(', ')}: write the law on the method it is about (the line above it), or as <method>.${code}`)
  }
  return names.find(n => n.role === 'state' && at(n) && !called)
    ?? (stateOnly ? undefined : names.find(n => (n.role === 'param' || n.role === 'const' || n.role === 'clock') && n.code === code && !called))
    ?? names.find(n => n.role === 'answer' && last(n))
    ?? (stateOnly ? undefined : names.find(n => n.rule === code && !called))
}
const results = (names: Name[], c: Ctx): Name | undefined => {
  const rs = names.filter(n => n.role === 'result' && n.code === 'result')
  const r = rs.find(n => n.method === c.method) ?? (rs.length === 1 ? rs[0] : undefined)
  if (!r && rs.length > 1) throw new LawError(`result: of ${rs.map(n => n.method).join(', ')}: write the law on the method it is about (the line above it)`)
  return r
}
// A name's value: its variable in the environment (the state after the step where the law is a step's), its None-ness.
function leaf(n: Name, c: Ctx, dry: boolean): V {
  if (dry) return n.none && !n.rule ? {t: 'opt', none: yes} : n.none ? {t: 'opt', none: yes, v: DRY} : DRY
  if (n.role === 'const') return {t: 'num', v: Int.of(n.value!)}
  const env = c.step && (n.role === 'state' || n.role === 'result' || n.role === 'failed') ? c.a : c.b
  const get = (r: string) => { if (!(r in env) && !(r in c.b)) throw new LawError(`${n.code}: ${r} isn't in the rule's environment here`); return r in env ? env[r] : c.b[r] }
  const v = n.rule ? wrap(get(n.rule)) : undefined
  return n.none ? {t: 'opt', none: get(n.none) as Cond, ...(v ? {v} : {})} : v!
}
// The rest of a path: a map at a key (m[k], m.get(k)), a cell's field, has/contains/key? of a map.
function rest(segs: Seg[], v: V, c: Ctx, names: Name[], dry: boolean, e: X): V {
  for (let i = 0; i < segs.length; i++) {
    const s = segs[i]!
    if (v.t === 'map') {
      const isGet = 'f' in s && ['get', 'fetch', 'getOrDefault', 'lookup'].includes(s.f) && segs[i + 1] && 'call' in segs[i + 1]!
      const isHas = 'f' in s && ['has', 'contains', 'containsKey', 'has_key', 'key?', 'has_key?', 'include?'].includes(s.f)
      if (isGet || isHas) throw new LawError(`${show(e)}: write the key in brackets (m[k], or k in m)`)
      if (!('i' in s)) throw new LawError(`${show(e)}: a map is read at a key (m[k])`)
      const [m, k] = storeKey(v, s.i, c, names, dry)
      if (dry) { v = DRY; continue }
      const cell = cellOf(m, key(k), c)
      v = {t: 'cell', ...cell}
      continue
    }
    if (v.t === 'cell' && 'f' in s) { if (!v.fields.includes(s.f)) throw new LawError(`${show(e)}: its cells have ${v.fields.join(', ')}`); v = wrap(v.rec[s.f]); continue }
    if (dry) continue
    throw new LawError(`${show(e)}: can't read ${'f' in s ? `.${s.f}` : 'i' in s ? '[...]' : '(...)'} of a ${v.t}`)
  }
  return v
}
// A store's map by its key's template ("hits:" + s, f"hits:{s}"), and the key's value; any other map at the key read.
function storeKey(m: V & {t: 'map'}, k: X, c: Ctx, names: Name[], dry: boolean): [V & {t: 'map'}, V] {
  if (!m.n.map?.store) return [m, val(k, c, names, dry)]
  const parts: string[] = [], holes: X[] = []
  const flat = (x: X) => { if (x.k === 'bin' && x.op === '+') { flat(x.a); flat(x.b) } else if (x.k === 'str' && !x.holes) parts.push(x.v); else if (x.k === 'str') { x.parts!.forEach((p, i) => { parts.push(p); if (x.holes![i]) { holes.push(x.holes![i]!); parts.push('{}') } }) } else { holes.push(x); parts.push('{}') } }
  flat(k)
  const tpl = parts.join('')
  const hit = m.maps.find(x => x.map!.tpl === tpl) ?? (holes.length === 1 && tpl === '{}' && m.maps.length === 1 ? m.maps[0] : undefined)
  if (!hit || holes.length !== 1) throw new LawError(`${m.n.code}[${tpl}]: its keys are ${m.maps.map(x => JSON.stringify(x.map!.tpl!.replace('{}', '<key>'))).join(', ')}`)
  return [{t: 'map', n: hit, maps: [hit]}, val(holes[0]!, c, names, dry)]
}
