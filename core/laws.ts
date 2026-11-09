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
//   sum(balances) == total_supply      a map's cells summed over every key
//   failed implies spend >= budget     implies (=>), parentheses, min max abs, true false None (nil, null)
//   self.tokens <= self.capacity       the state by its fields (self., this., @ or a receiver's name, or bare)
//   result == (n <= old(tokens))       a request's arguments by name, `result`, `failed`, old(x) or before.x the state
//                                      before the step (a law reading any of these is a law of one step)
//   team.max_budget is None            None-ness (is None, is not None, == nil, != null), an object's fields
//   get_current_spend(...) >= 0        a call of other code answered by the request, by its name
//   counts[user] < limit, user in m    a map at a key as the code reads it (m.get(k), k in m, m[k] is None)
//   cache["hits:" + s] <= limit        a store at its key's template ("hits:" + s, f"hits:{s}")
//   forall k in budgets: budgets[k].spent <= budgets[k].limit       every key the map holds (at the top of the law)
//   forall o in old(asks): forall j in old(asks): o in asks or o.price <= j.price
//                                      every item of a list (o.price its field; `o in asks` whether that item is still
//                                      in it, the same item, not an equal one), at every two (or three) at once
//   mode == "closed", outcome == SLOW_ERROR, mode == :closed        a choice by its value
import {type Cond, Choice, Int, Str, Term, all, any, forall, no, not, yes} from './dsl.ts'
import type {Extraction, Name} from './extract.ts'
import {type AnyRule, type TwoRunLaw, agreement, isolation, noninterference} from './relational.ts'
import {type BusinessDays, type Calendar, CalendarError, businessDays} from './calendar.ts'
export {businessDays, type Calendar} from './calendar.ts'

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
type X = {k: 'num', v: number} | {k: 'str', v: string, holes?: X[], parts?: string[]} | {k: 'bool', v: boolean} | {k: 'null', absence?: 'null' | 'undefined'}
  | {k: 'path', head: string, segs: Seg[]} | {k: 'un', op: '-' | 'not', x: X}
  | {k: 'bin', op: string, a: X, b: X} | {k: 'old', x: X} | {k: 'fn', f: string, xs: X[]} | {k: 'forall', v: string, over: X, body: X}
  | {k: 'dur', v: number, text: string} | {k: 'bdur', v: number, text: string}
const WORDS: Record<string, string> = {'->': '.', '::': '.', and: '&&', or: '||', not: '!', implies: '=>', '∧': '&&', '∨': '||', '¬': '!', '→': '=>', '==>': '=>', '≤': '<=', '≥': '>=', '≠': '!=', '∀': 'forall', AND: '&&', OR: '||', NOT: '!'}
function tokens(s: string): string[] {
  const out: string[] = [], re = /\s*(f?"(?:[^"\\]|\\.)*"|f?'(?:[^'\\]|\\.)*'|`[^`]*`|0[xX][0-9a-fA-F]+[uUlL]*|0[bB][01]+[uUlL]*|\d+(?:\.\d+)?[uUlL]*|@?[A-Za-z_][\w?]*|->|::|==>|=>|<=|>=|==|!=|&&|\|\||\/\/|[-+*%/<>()[\],.:!∧∨¬→≤≥≠∀&|])/y
  let m: RegExpExecArray | null, at = 0
  while ((m = re.exec(s))) { out.push(WORDS[m[1]!] ?? m[1]!); at = re.lastIndex }
  if (s.slice(at).trim()) throw new LawError(`can't read ${JSON.stringify(s.slice(at).trim())}`)
  return out
}
// Durations, as many seconds: linear over the clock (a day is 86,400 s: the request's time counts seconds, with no
// time zone, leap second or daylight saving). A month, a year or the end of a day isn't a fixed number of seconds, so a
// law reading one is refused: state it in days. Business days are counted over a calendar (core/calendar.ts): only as
// elapsed between two times, `now - received <= 10 business days`.
const SECONDS: Record<string, number> = {ms: 0.001, millisecond: 0.001, milliseconds: 0.001, second: 1, seconds: 1, sec: 1, secs: 1, minute: 60, minutes: 60, min: 60, mins: 60,
  hour: 3600, hours: 3600, day: 86_400, days: 86_400, week: 604_800, weeks: 604_800}
const NOT_LINEAR = /^(months?|years?|quarters?|business|working|weekdays?|fortnights?)$/i
function seconds(unit: string): number {
  const u = unit.toLowerCase()
  if (NOT_LINEAR.test(u)) throw new LawError(`${unit}: not a fixed number of seconds (a month or a year has several lengths, a business day depends on the calendar): state it in days, hours or seconds, or count business days over a calendar (businessDays; in a law, now - t <= 10 business days)`)
  return SECONDS[u]!
}
// A duration in the clock's units ('s': time.time(), 'ms': Date.now()): duration('30 days') is 2,592,000.
export function duration(text: string, clock: 's' | 'ms' = 's'): number {
  const m = /^\s*(\d+)\s*(?:calendar\s+)?([A-Za-z]+)(?:\s+days?)?\s*$/.exec(text)
  if (!m) throw new LawError(`${text}: a duration is a whole number and a unit (30 days, 15 minutes)`)
  if (!Object.hasOwn(SECONDS, m[2]!.toLowerCase()) && !NOT_LINEAR.test(m[2]!)) throw new LawError(`${m[2]}: a unit of ${Object.keys(SECONDS).join(', ')}`)
  const v = Number(m[1]) * seconds(m[2]!) * (clock === 'ms' ? 1000 : 1)
  if (!Number.isInteger(v)) throw new LawError(`${text}: not a whole number of the clock's units`)
  return v
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
    const a = bor(), op = peek()
    if (op === 'is') { eat(); const n = peek() === '!' ? (eat(), true) : false; const b = sum(); return n ? {k: 'un', op: 'not', x: {k: 'bin', op: '==', a, b}} : {k: 'bin', op: '==', a, b} }
    if (op === '!' && t[i + 1] === 'in') { eat(); eat(); return {k: 'un', op: 'not', x: {k: 'bin', op: 'in', a, b: sum()}} }
    if (op && ['<', '<=', '>', '>=', '==', '!=', 'in'].includes(op)) { eat(); return {k: 'bin', op, a, b: bor()} }
    return a
  }
  // (x & K and x | K, a flag tested or set by a constant: below the comparisons, as Python's, so flags & K != 0 is (flags & K) != 0)
  const bor = left(['|'], () => band()), band = left(['&'], () => sum())
  const sum = left(['+', '-'], () => prod()), prod = left(['*', '//', '/', '%'], () => unary())
  const unary = (): X => (peek() === '-' ? (eat(), {k: 'un', op: '-', x: unary()}) : atom())
  const atom = (): X => {
    const x = eat()
    if (x === undefined) throw new LawError('the expression ends early')
    if (x === '(') { const e = top(); eat(')'); return e }
    if (/^\d/.test(x)) {
      if (x.includes('.') && !/\.0+$/.test(x)) throw new LawError(`${x}: a number that isn't whole`)
      // (a duration: 30 days, 15 minutes, in seconds until the clock's unit is known)
      const u = peek()?.toLowerCase(), calendar = u === 'calendar' && /^days?$/i.test(t[i + 1] ?? '')
      if ((u === 'business' || u === 'working') && /^days?$/i.test(t[i + 1] ?? '')) { eat(); eat(); return {k: 'bdur', v: Number(x), text: `${x} ${u} days`} }
      if (u && (calendar || Object.hasOwn(SECONDS, u) || NOT_LINEAR.test(u))) { eat(); if (calendar) eat(); return {k: 'dur', v: Number(x) * seconds(calendar ? 'days' : u), text: `${x} ${u}${calendar ? ' days' : ''}`} }
      // (C's and the others' hexadecimal and binary literals, an unsigned or long suffix)
      return {k: 'num', v: Number(x.replace(/[uUlL]+$/, ''))}
    }
    if (/^f?["'`]/.test(x)) return str(x)
    if (x === ':' && /^[A-Za-z_]/.test(peek() ?? '') && !operand(t[i - 2])) return {k: 'str', v: eat()}
    if (['true', 'True'].includes(x)) return {k: 'bool', v: true}
    if (['false', 'False'].includes(x)) return {k: 'bool', v: false}
    if (['None', 'nil', 'null', 'undefined', 'NULL', 'nullptr'].includes(x)) return {k: 'null', ...(x === 'null' || x === 'undefined' ? {absence: x} : {})}
    if (!/^@?[A-Za-z_]/.test(x)) throw new LawError(`unexpected ${JSON.stringify(x)}`)
    if (x === 'old' && peek() === '(') { eat(); const e = top(); eat(')'); return {k: 'old', x: e} }
    if (['min', 'max', 'abs', 'sum'].includes(x) && peek() === '(') { eat(); const xs = [top()]; while (peek() === ',') { eat(); xs.push(top()) } eat(')'); return {k: 'fn', f: x, xs} }
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
  | {t: 'null', absence?: 'null' | 'undefined'} | {t: 'cell', rec: Record<string, unknown>, fields: string[]} | {t: 'opt', none: Cond, v?: V, absence?: 'null' | 'undefined'} | {t: 'map', n: Name, maps: Name[], env?: Record<string, unknown>} | {t: 'key', v: Term}
// (bits: in a law of one step, which reads no function, each run of a mask's bits named by keys the law holds at every
// value of, with the facts that make them that run: ks the keys, used how many are taken, hyps the facts)
type Bits = {ks: Term[], used: number, hyps: Cond[]}
type Ctx = {strictOptional?: boolean, absence?: Record<string, 'null' | 'undefined'>, consts?: Record<string, number | string | boolean>, b: Record<string, unknown>, a: Record<string, unknown>, step: boolean, method?: string, keys: Map<string, Term>, roles: Set<string>, methods: Set<string>, clock?: number, bits?: Bits,
  // (business days: the calendar, and in a law of one step each time's week, a key: `pins` collects the times on a
  // first reading, then holds each one's pinned week and the guard on it)
  cal?: BusinessDays, pins?: Pins,
  // (a key bound over a list: the item there, its map in the state it was read in)
  items?: Map<string, {map: Record<string, unknown>, fields: string[]}>}

// The law a text states, built on the extraction's rule through its names.
// The extraction's names, with the request's time as `now` where the rule reads it and no name says so (a TypeScript
// class's Date.now()).
export function namesWithClock(x: Extraction): Name[] {
  const ns = x.names ?? [], ins = (x.rule as {parts?: {inputs: [string, unknown][]}} | undefined)?.parts?.inputs.map(([n]) => n) ?? []
  return ns.some(n => n.role === 'clock') || !ins.includes('now') || ns.some(n => n.code === 'now') ? ns : [...ns, {code: 'now', rule: 'now', role: 'clock'}]
}
type Pins = {times: {id: string, nat: boolean}[], at?: Map<string, Int>, guards?: Cond[]}
export type LawOpts = {clock?: number, calendar?: Calendar}
const calendarOf = (opts: LawOpts): BusinessDays | undefined => {
  if (!opts.calendar) return undefined
  try { return businessDays(opts.calendar, opts.clock === 1000 ? 'ms' : 's') } catch (e) { throw e instanceof CalendarError ? new LawError(`the calendar: ${e.message}`) : e }
}
export function buildLaw(x: Extraction, l: LawText, opts: LawOpts = {}): Built {
  const strictOptional = x.model?.standalone === true
  const absence: Record<string, 'null' | 'undefined'> = {}
  for (const r of Object.values(x.model?.results ?? {})) if (r.k === 'maybe') absence[r.missing] = r.null ? 'null' : 'undefined'
  const names = namesWithClock(x), r = x.rule as unknown as {law: (n: string, f: (e: never) => unknown) => unknown, stepLaw: (n: string, f: (b: never, a: never) => unknown, w?: (b: never) => Cond) => unknown}
  if (!r) throw new LawError('the extraction has no rule')
  if (!l.expr) throw new LawError(`${l.name}: a law is stated as <name>: <expr>`)
  const e = parse(l.expr)
  // A first reading finds what the law reads: a request, a result, the failure or the state before make it a step law.
  const cal = opts.clock === undefined ? undefined : calendarOf(opts)
  const probe: Ctx = {strictOptional, absence, consts: x.consts, b: {}, a: {}, step: true, method: l.method, keys: new Map(), roles: new Set(), methods: new Set(), clock: opts.clock, cal}
  read(e, probe, names, true)
  // (a law on a method, the line above it, is a law of its step: the state after it, old(x) before)
  const step = !!l.method || ['input', 'answer', 'result', 'failed', 'clock', 'method', 'old'].some(k => probe.roles.has(k))
  const method = probe.methods.size === 1 ? [...probe.methods][0] : l.method
  if (probe.methods.size > 1) throw new LawError(`it reads the arguments of ${[...probe.methods].join(' and ')}: a law of one step is about one method`)
  const gate = step && method && names.some(n => n.role === 'method') ? method : undefined
  const body0 = (b: Record<string, unknown>, a: Record<string, unknown>, pins?: Ctx['pins'], bits?: Bits) => read(e, {strictOptional, absence, consts: x.consts, b, a, step, method, keys: new Map(), roles: new Set(), methods: new Set(), clock: opts.clock, cal, pins, ...(bits ? {bits} : {})}, names, false) as Cond
  // (a step law's bit tests: read once to count the keys they take, then at every value of them, the facts implying it)
  const bitBody = (b: Record<string, unknown>, a: Record<string, unknown>): Cond | ReturnType<typeof forall> => {
    const count: Bits = {ks: [], used: 0, hyps: []}
    const plain = body0(b, a, undefined, count)
    if (!count.used) return plain
    if (count.used > 6) throw new LawError(`its bit tests take ${count.used} keys in a law of one step (at most 6: two runs of bits at a place above bit 0, three at bit 0)`)
    const at = (...ks: Term[]): Cond => { const bits: Bits = {ks, used: 0, hyps: []}; const out = body0(b, a, undefined, bits); return all(...bits.hyps).implies(out) }
    const n = count.used
    return n === 1 ? forall(k => at(k)) : n === 2 ? forall((k, j) => at(k, j)) : n === 3 ? forall((k, j, i) => at(k, j, i)) : n === 4 ? forall((k, j, i, h) => at(k, j, i, h)) : n === 5 ? forall((k, j, i, h, g) => at(k, j, i, h, g)) : forall((k, j, i, h, g, f) => at(k, j, i, h, g, f))
  }
  // (a law of one step reads no function, so business days there pin each time's week to a key, ∀w. guard → law)
  const body = (b: Record<string, unknown>, a: Record<string, unknown>) => (step && probe.roles.has('bdays') ? pinned(b, a, (bb, aa, p) => body0(bb, aa, p)) : bitBody(b, a))
  if (!step) return {kind: 'law', law: r.law(l.name, (env: never) => (x.quiet ? ((env as Record<string, Int>)[x.quiet]!.eq(0) as Cond).implies(body0(env, env)) : body0(env, env)))}
  const mname = names.find(n => n.role === 'method')?.rule
  return {kind: 'step', ...(gate ? {method: gate} : {}), law: r.stepLaw(l.name, (b: never, a: never) => body(b, a) as never, gate ? (b: never) => ((b as Record<string, unknown>)[mname!] as Choice<string>).is(gate) : undefined)}
}
// A law of one step over business days: read once to find its times, then held at every week of each (a key, two for
// a time that may be below 0), under the guards that only each time's own week meets.
function pinned(b: Record<string, unknown>, a: Record<string, unknown>, f: (b: Record<string, unknown>, a: Record<string, unknown>, pins: Pins | undefined) => Cond): Cond | ReturnType<typeof forall> {
  const pins: Pins = {times: []}
  f(b, a, pins)
  const n = pins.times.reduce((k, t) => k + (t.nat ? 1 : 2), 0)
  if (n > 6) throw new LawError('business days at more than 6 weeks at once (a time that may be below 0 takes two)')
  const g = (ks: Term[]): Cond => {
    const at = new Map<string, Int>(), guards: Cond[] = []
    let i = 0
    for (const t of pins.times) at.set(t.id, t.nat ? Int.of(ks[i++]!) : new Int(ks[i++]!, ks[i++]!))
    const out = f(b, a, {times: pins.times, at, guards})
    if ('forall' in out) throw new LawError('business days in a law over every key: not yet (state it at one key)')
    return all(...guards).implies(out)
  }
  const fs = [(k: Term) => g([k]), (k: Term, j: Term) => g([k, j]), (k: Term, j: Term, h: Term) => g([k, j, h]), (k: Term, j: Term, h: Term, m: Term) => g([k, j, h, m]),
    (k: Term, j: Term, h: Term, m: Term, o: Term) => g([k, j, h, m, o]), (k: Term, j: Term, h: Term, m: Term, o: Term, p: Term) => g([k, j, h, m, o, p])]
  return n ? forall(fs[n - 1] as never) : f(b, a, undefined)
}

// The expression read: its value (`dry`: only which names it reads, nothing built).
function read(e: X, c: Ctx, names: Name[], dry: boolean): unknown {
  if (e.k === 'forall') {
    // (forall a in X: forall b in Y: ...: at every two keys at once, each held by its map)
    const chain: (X & {k: 'forall'})[] = []
    let body: X = e
    while (body.k === 'forall') { chain.push(body); body = body.body }
    if (chain.length > 3) throw new LawError('forall ... in ...: at most three at once')
    c.items ??= new Map()
    const overs = chain.map(f => {
      const over = val(f.over, c, names, dry)
      if (over.t !== 'map') throw new LawError(`forall ${f.v} in ...: over a map (a dict, a Map, a hash) or a list`)
      return {over, env: f.over.k === 'old' || !c.step ? c.b : c.a}
    })
    if (dry) { for (const f of chain) c.keys.set(f.v, new Term({op: 'const', value: 0})); return cond(val(body, c, names, true), c.strictOptional) }
    const at = (ks: Term[]): Cond => {
      const held = overs.map((o, i) => {
        const m = o.env[o.over.n.rule] as {at: (k: Term) => Record<string, unknown>}
        c.keys.set(chain[i]!.v, ks[i]!)
        if (o.over.n.map?.ordered) c.items!.set(chain[i]!.v, {map: m.at(ks[i]!), fields: o.over.n.map.fields})
        return m.at(ks[i]!).has as Cond
      })
      return all(...held).implies(cond(val(body, c, names, false), c.strictOptional))
    }
    return chain.length === 1 ? forall(k => at([k])) : chain.length === 2 ? forall((k, j) => at([k, j])) : forall((k, j, i) => at([k, j, i]))
  }
  return cond(val(e, c, names, dry), c.strictOptional)
}
const cond = (v: V, strictOptional = false): Cond => {
  if (v.t === 'cond') return v.v
  if (v.t === 'opt' && v.v?.t === 'cond') return strictOptional ? all(not(v.none), v.v.v) : v.v.v
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
    case 'bdur': throw new LawError(`${e.text}: business days are elapsed between two times, compared: now - received <= ${e.v} business days`)
    case 'dur': if (c.clock === undefined) throw new LawError(`${e.text}: the clock's unit isn't known here (clock = "s" or "ms" in gdp.toml)`); if (!Number.isInteger(e.v * c.clock)) throw new LawError(`${e.text}: not a whole number of the clock's units`); return {t: 'num', v: Int.of(e.v * c.clock)}
    case 'bool': return {t: 'cond', v: e.v ? yes : no}
    case 'null': return {t: 'null', absence: e.absence}
    case 'str': if (e.holes) throw new LawError('a string template outside a store\'s key'); return {t: 'lit', v: e.v}
    case 'old': { c.roles.add('old'); return val(e.x, {...c, a: c.b}, names, dry) }
    case 'fn': {
      // sum(m): a map's cells summed over every key (one number a cell; a key it doesn't hold holds 0)
      if (e.f === 'sum') {
        const m = go(e.xs[0]!)
        if (m.t !== 'map' || e.xs.length !== 1) throw new LawError('sum(m): the sum of a map\'s cells, m a map')
        const fs = m.n.map!.fields
        if (fs.length !== 1) throw new LawError(`sum(${m.n.code}): its cells have ${fs.join(', ')} (the sum is of a map of numbers)`)
        if (dry) return DRY
        const map = ((m.env ?? c.a)[m.n.rule] ?? c.b[m.n.rule]) as {sum: (of: (cell: Record<string, unknown>) => unknown) => unknown}
        try {
          // (a map of integers: the sum of its cells' positive parts less the sum of their negative parts, each a sum of
          // naturals the kernel keeps exact)
          const one = (map as unknown as {at: (k: Term) => Record<string, unknown>}).at(new Term({op: 'const', value: 0}))[fs[0]!]
          if (one instanceof Int) {
            // (after the step: the sums over the map before it, as the state after it holds them, primed)
            const after = (m.env ?? c.a) === c.a && c.step && c.a !== c.b, src = (after ? c.b[m.n.rule] : map) as typeof map
            const sumOf = (part: 'pos' | 'neg') => { const t = src.sum(cell => (cell[fs[0]!] as Int)[part]) as Term; return after && t.e.op === 'var' ? new Term({op: 'var', name: `${t.e.name}'`}) : t }
            return {t: 'num', v: new Int(sumOf('pos'), sumOf('neg'))}
          }
          return {t: 'num', v: Int.of(map.sum(cell => cell[fs[0]!]) as Term)}
        } catch (x) {
          if (x instanceof TypeError) throw new LawError(`sum(${m.n.code}): a sum is of naturals, and ${m.n.code}'s cells are integers (a cell the code may set below 0): state them as naturals (domains, in gdp.toml) where the code never does`)
          throw x
        }
      }
      const xs = e.xs.map(go)
      if (c.strictOptional && xs.some(v => v.t === 'opt')) throw new LawError('arithmetic on an optional standalone value is not supported')
      if (dry) return DRY
      if (e.f === 'abs') return {t: 'num', v: Int.of(num(xs[0]!).abs)}
      return {t: 'num', v: xs.slice(1).reduce((m, y) => (e.f === 'min' ? m.min(num(y)) : m.max(num(y))), num(xs[0]!))}
    }
    case 'un': { const v = go(e.x); if (c.strictOptional && e.op === '-' && v.t === 'opt') throw new LawError('arithmetic on an optional standalone value is not supported'); if (dry) return v.t === 'cond' ? v : DRY; return e.op === '-' ? {t: 'num', v: num(v).negate()} : {t: 'cond', v: not(cond(v, c.strictOptional))} }
    case 'bin': {
      // (a comparison with x // k on one side, k a positive constant: the same comparison without the division, exact
      // over the integers (a <= x // k is k·a <= x; a < x // k is k·(a + 1) <= x), so it needs no function, which a law
      // of one step can't read)
      const flip: Record<string, string> = {'<': '>', '<=': '>=', '>': '<', '>=': '<=', '==': '==', '!=': '!='}
      if (flip[e.op] && (e.a.k === 'bdur' || e.b.k === 'bdur')) return {t: 'cond', v: businessCompare(e, flip, c, go, dry)}
      const divk = (x: X) => (x.k === 'bin' && x.op === '//' && (constOf(x.b) ?? 0) >= 1 ? x as X & {k: 'bin'} : undefined)
      if (flip[e.op] && (divk(e.b) || divk(e.a))) {
        // Inspect the original numerator before rewriting division into comparisons.
        if (c.strictOptional) for (const d of [divk(e.a), divk(e.b)]) if (d && go(d.a).t === 'opt') throw new LawError('arithmetic on an optional standalone value is not supported')
        const [op, lhs, d] = divk(e.b) ? [e.op, e.a, divk(e.b)!] : [flip[e.op]!, e.b, divk(e.a)!]
        const k = constOf(d.b)!, ka: X = {k: 'bin', op: '*', a: {k: 'num', v: k}, b: lhs}, ka1: X = {k: 'bin', op: '*', a: {k: 'num', v: k}, b: {k: 'bin', op: '+', a: lhs, b: {k: 'num', v: 1}}}
        const le = (a: X, b: X): X => ({k: 'bin', op: '<=', a, b}), lt = (a: X, b: X): X => ({k: 'bin', op: '<', a, b})
        // a ⋈ ⌊x/k⌋:  <= : k·a <= x;  < : k·(a+1) <= x;  >= : x < k·(a+1);  > : x < k·a;  == : both;  != : not both
        const x = d.a, eq: X = {k: 'bin', op: '&&', a: le(ka, x), b: lt(x, ka1)}
        const out: X = op === '<=' ? le(ka, x) : op === '<' ? le(ka1, x) : op === '>=' ? lt(x, ka1) : op === '>' ? lt(x, ka) : op === '==' ? eq : {k: 'un', op: 'not', x: eq}
        return go(out)
      }
      if (e.op === 'in') { const m = go(e.b); if (m.t !== 'map') throw new LawError('x in m: m a map'); const k = go(e.a); return dry ? {t: 'cond', v: yes} : {t: 'cond', v: cellOf(m, key(k), c).rec.has as Cond} }
      // (a name the rule doesn't have, compared with a choice: the choice's value, Outcome.SLOW_ERROR)
      const lit = (x: X): V => { try { return go(x) } catch (err) { if (x.k !== 'path' || !(err instanceof LawError) || !['==', '!='].includes(e.op)) throw err; return {t: 'lit', v: lastName(x) ?? '', err} } }
      const a = lit(e.a), b = lit(e.b)
      if (a.t === 'lit' && a.err && b.t === 'lit' && b.err) throw a.err
      if (['&&', '||', '=>'].includes(e.op)) return dry ? {t: 'cond', v: yes} : {t: 'cond', v: e.op === '&&' ? all(cond(a, c.strictOptional), cond(b, c.strictOptional)) : e.op === '||' ? any(cond(a, c.strictOptional), cond(b, c.strictOptional)) : cond(a, c.strictOptional).implies(cond(b, c.strictOptional))}
      if (c.strictOptional && ['+', '-', '*', '//', '/', '%', '&', '|'].includes(e.op) && [a, b].some(v => v.t === 'opt')) throw new LawError('arithmetic on an optional standalone value is not supported')
      if (dry) return ['+', '-', '*', '//', '/', '%', '&', '|'].includes(e.op) ? DRY : {t: 'cond', v: yes}
      // x & K and x | K with K a constant (a literal or a constant of the code): K's runs of ones, ((x div 2^lo) mod 2^n)·2^lo
      // each, as the extractor reads the code's (core/extract-step.ts's bitop); x | K is x + K − (x & K).
      if (e.op === '&' || e.op === '|') {
        const kOf = (v: V) => { if (v.t !== 'num') return undefined; const p = v.v.pos.e, n = v.v.neg.e; return p.op === 'const' && n.op === 'const' ? p.value - n.value : undefined }
        const [xv, k] = kOf(b) !== undefined ? [a, kOf(b)!] : kOf(a) !== undefined ? [b, kOf(a)!] : [a, undefined]
        if (k === undefined) throw new LawError(`${e.op} with a constant only (a bit operation of two values is outside linear arithmetic)`)
        const x = num(xv), andK = (kk: number): Int => {
          if (kk < 0) return x.minus(andK(-kk - 1))
          let out = Int.of(0), lo = 0
          for (let r = kk; r > 0;) { if (r % 2 === 0) { r /= 2; lo++; continue } let n = 0; while (r % 2 === 1) { r = (r - 1) / 2; n++ } out = out.plus(Int.of(run(lo, n)).times(2 ** lo)); lo += n }
          return out
        }
        // ((x div 2^lo) mod 2^n): an invariant's by the rule's functions; a step law's (which reads none) by keys q, m,
        // s at every value of which x ≡ q·2^(lo+n) + m·2^lo + s (mod 2^(lo+n), x's natural form pos + neg·(2^(lo+n) − 1)),
        // m < 2^n, s < 2^lo: m is the run
        function run(lo: number, n: number): Term {
          if (!c.bits) return x.divBy(2 ** lo).modBy(2 ** n)
          const take = () => c.bits!.ks[c.bits!.used++] ?? new Term({op: 'const', value: 0})
          const q = take(), m = take(), s0 = lo ? take() : undefined, nat = x.pos.plus(x.neg.times(2 ** (lo + n) - 1))
          let parts = q.times(2 ** (lo + n)).plus(m.times(2 ** lo))
          if (s0) parts = parts.plus(s0)
          c.bits!.hyps.push(nat.eq(parts), m.lt(2 ** n), ...(s0 ? [s0.lt(2 ** lo)] : []))
          return m
        }
        return {t: 'num', v: e.op === '&' ? andK(k) : x.plus(k).minus(andK(k))}
      }
      if (e.op === '+' || e.op === '-') return {t: 'num', v: e.op === '+' ? num(a).plus(num(b)) : num(a).minus(num(b))}
      if (e.op === '*') { const k = constOf(e.a) ?? constOf(e.b); if (k === undefined) throw new LawError('× by a constant only (a product of two values is outside linear arithmetic)'); return {t: 'num', v: num(constOf(e.a) === undefined ? a : b).times(k)} }
      if (e.op === '//' || e.op === '/' || e.op === '%') { const k = constOf(e.b); if (!k || k < 1) throw new LawError(`${e.op} by a positive constant only`); return e.op === '%' ? {t: 'num', v: Int.of(num(a).modBy(k))} : {t: 'num', v: num(a).divBy(k)} }
      return {t: 'cond', v: compare(e.op, a, b, e, c.strictOptional)}
    }
    case 'path': return path(e, c, names, dry)
    case 'forall': return fail('forall ... in ...: at the top of the law only')
  }
  return fail('an expression of no kind')
}
// `later - earlier ⋈ N business days`: the business days from earlier's day to later's (core/calendar.ts) ⋈ N. In a law
// of one step each time's week is a key (pinned, its guard collected); elsewhere it is divided out.
function businessCompare(e: X & {k: 'bin'}, flip: Record<string, string>, c: Ctx, go: (x: X) => V, dry: boolean): Cond {
  const [op, diff, n] = e.b.k === 'bdur' ? [e.op, e.a, e.b] : [flip[e.op]!, e.b, e.a as X & {k: 'bdur'}]
  if (diff.k !== 'bin' || diff.op !== '-') throw new LawError(`${n.text}: compared with the time elapsed between two times, later - earlier (now - received <= ${n.v} business days)`)
  if (c.clock === undefined) throw new LawError(`${n.text}: the clock's unit isn't known here (clock = "s" or "ms" in gdp.toml)`)
  if (!c.cal) throw new LawError(`${n.text}: business days need a calendar ([calendar] in gdp.toml: weekend = ["sat", "sun"], holidays = ["2026-12-25", ...], utc_offset = "-05:00")`)
  c.roles.add('bdays')
  const later = go(diff.a), earlier = go(diff.b)
  if ([later, earlier].some(v => v.t === 'opt')) throw new LawError(c.strictOptional ? 'arithmetic on an optional standalone value is not supported' : 'arithmetic on an optional value is not supported in calendar comparisons')
  if (dry) return yes
  const cal = c.cal, at = (x: X, v: V) => {
    const t = num(v), p = c.pins
    if (!p || !c.step) return t
    // (one key per time as it is read: the same text, in the state before or after the step)
    const id = `${JSON.stringify(x)}${c.a === c.b ? '@before' : ''}`
    if (!p.at) { if (!p.times.some(q => q.id === id)) p.times.push({id, nat: t.neg.e.op === 'const' && t.neg.e.value === 0}); return t }
    const pin = cal.pin(t, p.at.get(id)!)
    p.guards!.push(pin.guard)
    return pin.at
  }
  const d = cal.between(at(diff.b, earlier), at(diff.a, later))
  return op === '<' ? d.lt(n.v) : op === '<=' ? d.atMost(n.v) : op === '>' ? d.gt(n.v) : op === '>=' ? d.atLeast(n.v) : op === '==' ? d.eq(n.v) : d.ne(n.v)
}
// (a path's last name: a choice's value written as one, Outcome.SLOW_ERROR)
const lastName = (x: X & {k: 'path'}): string | undefined => (x.segs.length ? (x.segs.at(-1) as {f?: string}).f : x.head)
const constOf = (x: X): number | undefined => (x.k === 'num' ? x.v : x.k === 'un' && x.op === '-' && x.x.k === 'num' ? -x.x.v : undefined)
// Require the caller to choose source semantics, including on recursive unwrapping.
function compare(op: string, a: V, b: V, e: X & {k: 'bin'}, strictOptional: Ctx['strictOptional']): Cond {
  if (b.t === 'null' || a.t === 'null') {
    const literal = a.t === 'null' ? a : b as V & {t: 'null'}
    const o = a.t === 'null' ? b : a, none = o.t === 'opt' ? o.none : o.t === 'cell' ? not(o.rec.has as Cond) : undefined
    if (strictOptional && o.t === 'opt' && literal.absence && o.absence && literal.absence !== o.absence) return op === '==' ? no : op === '!=' ? yes : fail(`${op} with None`)
    if (!none) throw new LawError(`${show(a.t === 'null' ? e.b : e.a)} is never None here (the rule holds no None for it)`)
    return op === '==' ? none : op === '!=' ? not(none) : fail(`${op} with None`)
  }
  // A standalone optional value is absent regardless of its hidden scalar payload.
  // Keep the established law language of other frontends unchanged.
  if (strictOptional && (a.t === 'opt' || b.t === 'opt')) {
    const av = a.t === 'opt' ? a.v : a, bv = b.t === 'opt' ? b.v : b
    const present = all(a.t === 'opt' ? not(a.none) : yes, b.t === 'opt' ? not(b.none) : yes)
    if (op === '==' || op === '!=') {
      const absent = a.t === 'opt' && b.t === 'opt' && (!a.absence || !b.absence || a.absence === b.absence) ? all(a.none, b.none) : no
      const equal = any(absent, av && bv ? all(present, compare('==', av, bv, e, strictOptional)) : no)
      return op === '==' ? equal : not(equal)
    }
    return av && bv ? all(present, compare(op, av, bv, e, strictOptional)) : no
  }
  const un = (v: V): V => (v.t === 'opt' && v.v ? v.v : v)
  a = un(a); b = un(b)
  // (a name the rule doesn't have is a choice's value only beside a choice)
  for (const [v, o] of [[a, b], [b, a]]) if (v!.t === 'lit' && v!.err && o!.t !== 'choice') throw v!.err
  const eq = (c: Cond) => (op === '==' ? c : op === '!=' ? not(c) : fail(`${op} of values that aren't numbers`))
  if (a.t === 'choice' || b.t === 'choice') {
    const [ch, o, ox] = a.t === 'choice' ? [a.v, b, e.b] : [(b as {v: Choice<string>}).v, a, e.a]
    // Choice encodings are local to each domain: the same index can name
    // different strings. In standalone laws compare common names, not indices.
    if (o.t === 'choice') return eq(strictOptional
      ? any(...ch.values.filter(v => o.v.values.includes(v)).map(v => all(ch.is(v), o.v.is(v))))
      : ch.eq(o.v))
    const lit = o.t === 'lit' ? o.v : ox.k === 'path' ? lastName(ox) : undefined
    if (lit === undefined || !ch.values.includes(lit)) throw new LawError(`${show(ox)} isn't one of ${ch.values.join(', ')}`)
    return eq(ch.is(lit))
  }
  // A quantified map key and a string identity use the same id as m[identity].
  // This is equality of keys, not an ordering or coercion between strings and numbers.
  if (a.t === 'key' && b.t === 'str' || a.t === 'str' && b.t === 'key') return eq(key(a).eq(key(b)))
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
  const map = ((m.env ?? c.a)[m.n.rule] ?? c.b[m.n.rule]) as {at: (k: Term) => Record<string, unknown>}
  return {rec: map.at(k), fields: m.n.map!.fields}
}

// A path: the longest prefix of it the code names (in the law's method first: its arguments shadow the fields, as in the
// code), then its fields, keys and calls.
function path(e: X & {k: 'path'}, c: Ctx, names: Name[], dry: boolean): V {
  if (c.keys.has(e.head) && !e.segs.length) return {t: 'key', v: c.keys.get(e.head)!}
  // (an item of a list a forall is over: its fields)
  const item = c.items?.get(e.head)
  if (item && e.segs.length) return dry ? DRY : rest(e.segs, {t: 'cell', rec: item.map, fields: item.fields}, c, names, dry, e)
  if (c.keys.has(e.head) && dry) return DRY
  // (result and failed are the step's, unless the code has a name of its own so: a field named failed, read bare, is
  // that field, as self.failed always is)
  if (e.head === 'result' && e.segs[0] && 'f' in e.segs[0]) {
    const field = `result.${e.segs[0].f}`, rs = names.filter(n => n.role === 'result' && n.code === field)
    const hit = rs.find(n => n.method === c.method) ?? (rs.length === 1 ? rs[0] : undefined)
    if (hit) { c.roles.add('result'); if (hit.method) c.methods.add(hit.method); return rest(e.segs.slice(1), leaf(hit, c, dry), c, names, dry, e) }
    if (rs.length > 1) throw new LawError(`${field}: name the method it belongs to`)
  }
  if ((e.head === 'result' || e.head === 'failed') && !names.some(n => n.code === e.head && n.role !== 'failed' && n.role !== 'result')) {
    const n = e.head === 'failed' ? names.find(x => x.role === 'failed') : results(names, c)
    if (!n) throw new LawError(e.head === 'failed' ? 'the rule keeps no failure (with failures: \'kept\' it does: `failures = "kept"` in gdp.toml or --failures kept)' : 'the method returns nothing the rule keeps')
    c.roles.add(n.role); if (n.method) c.methods.add(n.method)
    return rest(e.segs, leaf(n, c, dry), c, names, dry, e)
  }
  // (a call answered per constant arguments, C's: f(em, BUS_OFF) its answer f_x_18, by the code's constants)
  const call0 = e.segs[0]
  if (call0 && 'call' in call0 && call0.args && names.some(x => x.role === 'answer' && x.code.startsWith(`${e.head}_`))) {
    const sig = splitArgs(call0.args).map(a => { const k = /^-?\d+$/.test(a) ? Number(a) : /^[A-Za-z_]\w*$/.test(a) ? c.consts?.[a] : undefined; return typeof k === 'number' ? String(k).replace('-', 'm') : 'x' }).join('_')
    const per = names.find(x => x.role === 'answer' && x.code === `${e.head}_${sig}`)
    if (!per) throw new LawError(`${e.head}(${call0.args}): no answer of the code for these arguments (its answers: ${names.filter(x => x.role === 'answer' && x.code.startsWith(`${e.head}_`)).map(x => x.code).join(', ')})`)
    c.roles.add(per.role)
    return rest(e.segs.slice(1), leaf(per, c, dry), c, names, dry, e)
  }
  // (self.x, this.x, state.x, @x: the state's x; a bare `state` or `s` is a name of the code's, a field named so)
  const explicit = (['self', 'this', 'state', 's'].includes(e.head) && e.segs.length > 0) || e.head.startsWith('@')
  const parts = [e.head.replace(/^@/, ''), ...e.segs.map(s => ('f' in s ? s.f : undefined))]
  // (s.x and state.x: the state's x, else a state the code names s or state, a C global's field)
  const heads = explicit && !e.head.startsWith('@') ? [parts.slice(1), ...(['s', 'state'].includes(e.head) ? [parts] : [])] : [parts, ...(parts.length > 1 && parts[1] !== undefined ? [parts.slice(1)] : [])]
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
        if (hit.role === 'answer' && next && 'call' in next && next.args) {
          // (a call answered per constant arguments, C's: f(em, BUS_OFF) its answer f_x_18, by the code's constants)
          const sig = splitArgs(next.args).map(a => { const k = /^-?\d+$/.test(a) ? Number(a) : /^[A-Za-z_]\w*$/.test(a) ? c.consts?.[a] : undefined; return typeof k === 'number' ? String(k).replace('-', 'm') : 'x' }).join('_')
          const per = names.find(x => x.role === 'answer' && x.code === `${code}_${sig}`)
          if (per) { c.roles.add(per.role); return rest(e.segs.slice(skip + n), leaf(per, c, dry), c, names, dry, e) }
          throw new LawError(`${code}(${next.args}): an answered call's value is the request's, one a step: write it ${code}(...)`)
        }
        const segs = e.segs.slice(skip + n - 1 + (hit.role === 'answer' && next && 'call' in next ? 1 : 0))
        // (a map read where it is named: old(m) is the map before the step wherever its cells are read, `k in old(m)`)
        return rest(segs, hit.map ? {t: 'map', n: hit, maps: names.filter(x => x.map && x.code === hit.code), env: c.a} : leaf(hit, c, dry), c, names, dry, e)
      }
    }
  }
  // A method's argument by its method's name (charge.user), where several methods take one of that name.
  // A constant of the module bound to a literal, by its name (a qualified one, C++'s A::K, by its path).
  const dotted = e.segs.every(g => 'f' in g) ? [e.head, ...e.segs.map(g => (g as {f: string}).f)].join('.') : undefined
  if (dotted && e.segs.length && c.consts?.[dotted] !== undefined) { const v = c.consts[dotted]!; return typeof v === 'number' ? {t: 'num', v: Int.of(v)} : typeof v === 'boolean' ? {t: 'cond', v: v ? yes : no} : {t: 'lit', v} }
  const k = c.consts?.[e.head]
  if (k !== undefined && !e.segs.length) return typeof k === 'number' ? {t: 'num', v: Int.of(k)} : typeof k === 'boolean' ? {t: 'cond', v: k ? yes : no} : {t: 'lit', v: k}
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
    // (a field of that name: the field, never another method's argument)
    const field = names.find(n => n.role === 'state' && at(n))
    if (field) return field
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
  return n.none ? {t: 'opt', none: get(n.none) as Cond, absence: c.strictOptional ? c.absence?.[n.none] ?? 'undefined' : undefined, ...(v ? {v} : {})} : v!
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
  return [{t: 'map', n: hit, maps: [hit], ...(m.env ? {env: m.env} : {})}, val(holes[0]!, c, names, dry)]
}

// --- citations ---------------------------------------------------------------------------------------------------------
// The clause a law answers: `# gdp: cite <law name>: <the clause, as text>` (a regulation's section, a policy's words),
// any number for one law, in any file of the target. Carried into the output and a certificate's meta, never into what
// is proven: whether the law is faithful to the clause is the reader's judgment, the citation only says which.
export type Cite = {law: string, text: string, where: string}
const CITE = /(?:#|\/\/|--|%|\/\*|^\s*\*)\s*gdp:\s*cite\s+([^:]+?)\s*:\s*(.+?)\s*(?:\*\/)?\s*$/
export function citesIn(text: string, where = ''): Cite[] {
  return text.split('\n').flatMap((l, i) => { const m = CITE.exec(l); return m ? [{law: m[1]!.trim(), text: m[2]!, where: `${where}:${i + 1}`}] : [] })
}

// --- laws about two runs -------------------------------------------------------------------------------------------------
// Three forms of a stated law (core/relational.ts), over the code's names:
//   <secret>[, ...] never reaches <visible>[, ...]      noninterference: the secret arguments (or params, answers) never
//                                                       change the visible fields or results, nor which calls fail
//   isolated by <owner> [seeing <name>[, ...]]          isolation: what the caller whose <owner> argument is B sees (the
//                                                       maps' cells at B, the results of B's calls, B's failures) is the
//                                                       same whatever the other callers do; by default every map, result
//   agrees with <Entry> [on <name>[, ...]]              a migration: this rule and <Entry> (another rule of the same
//                                                       target) keep the same fields after the same calls, fail alike
const TWO = [/^(.+?)\s+never\s+reach(?:es)?\s+(.+)$/i, /^isolated\s+by\s+([\w.]+)(?:\s+seeing\s+(.+))?$/i, /^agrees\s+with\s+([\w.]+)(?:\s+on\s+(.+))?$/i]
export const isTwoRuns = (expr: string): boolean => TWO.some(re => re.test(expr.trim()))
const list = (s: string | undefined): string[] => (s ? s.split(/\s*,\s*|\s+and\s+/).map(x => x.trim()).filter(Boolean) : [])
export function buildTwoRuns(x: Extraction, l: LawText, others: Record<string, Extraction> = {}): TwoRunLaw {
  const names = namesWithClock(x), e = l.expr.trim(), r = x.rule as AnyRule
  if (!r) throw new LawError('the extraction has no rule')
  const known = () => [...new Set(names.filter(n => n.rule).map(n => n.code))].join(', ')
  const ruleNames = (ns: Name[], code: string, roles: Name['role'][], what: string): string[] => {
    const hit = ns.filter(n => n.code.replace(/^@/, '') === code.replace(/^(self|this)\./, '') && roles.includes(n.role))
    if (!hit.length) throw new LawError(`no ${code} ${what} (its names: ${known()})`)
    return [...new Set(hit.flatMap(n => [n.rule, ...(n.none ? [n.none] : [])]).filter(Boolean))]
  }
  const STATE: Name['role'][] = ['state', 'result', 'failed']
  let m = TWO[0]!.exec(e)
  if (m) {
    const secret = list(m[1]).flatMap(c => ruleNames(names, c, ['input', 'param', 'answer', 'clock'], 'among the arguments, params or answered calls'))
    const visible = list(m[2]).flatMap(c => ruleNames(names, c, STATE, 'among the fields and results'))
    return {...noninterference(r, {secret, visible, name: l.name}), name: l.name}
  }
  if ((m = TWO[1]!.exec(e))) {
    const owners = names.filter(n => n.role === 'input' && n.code === m![1] && n.rule)
    if (!owners.length) throw new LawError(`no argument ${m[1]} (its names: ${known()})`)
    const method = names.find(n => n.role === 'method')?.rule, methods = new Set(owners.map(n => n.method))
    const key = (v: unknown): Term => (v instanceof Term ? v : v instanceof Int ? v.pos : (v as {id: Term}).id)
    // (a call is B's where its method takes the owner argument and it is B; with one rule input for every method, that)
    const owner = (env: Record<string, unknown>, b: Term): Cond => any(...owners.map(n => all(key(env[n.rule]).eq(b), ...(method && methods.size && n.method ? [(env[method] as Choice<string>).is(n.method)] : []))))
    const seen = m[2] ? list(m[2]).flatMap(c => ruleNames(names, c, STATE, 'among the fields and results')) : undefined
    const maps = new Set(names.filter(n => n.map).map(n => n.rule))
    const sees = seen?.filter(n => maps.has(n)), results = seen ? seen.filter(n => !maps.has(n)) : names.filter(n => n.role === 'result' || n.role === 'failed').flatMap(n => [n.rule, ...(n.none ? [n.none] : [])]).filter(Boolean)
    return {...isolation(r, {owner, ...(sees ? {sees} : {}), results: [...new Set(results)], name: l.name}), name: l.name}
  }
  if ((m = TWO[2]!.exec(e))) {
    const o = others[m[1]!]
    if (!o?.rule) throw new LawError(`no rule ${m[1]} read beside this one (${Object.keys(others).join(', ') || 'none'}): agrees with names another class of the same target`)
    const visible = m[2] ? list(m[2]).flatMap(c => { const mine = ruleNames(names, c, STATE, 'among the fields and results'); ruleNames(o.names ?? [], c, STATE, `in ${m![1]}`); return mine }) : undefined
    return {...agreement(o.rule as AnyRule, r, {...(visible ? {visible} : {}), name: l.name}), name: l.name}
  }
  throw new LawError('not a law about two runs')
}

// --- liveness: "whenever <from>, later <to>" ---------------------------------------------------------------------------
// `<from> leads to <to> by <rank>[, <rank>...] via <helpful>[; <helpful>...] [strongly]`, each helpful request
// `[<cond> ->] <method>(<arg> = <value>, ...)`: in every run that takes each helpful request (where its condition holds)
// infinitely often, a state where `from` holds is followed by one where `to` does (core/dsl.ts's leadsTo, proven by
// proveLeadsTo: no step raises the rank (in order) while `from` holds and `to` doesn't, except into `to`, and each helpful
// request lowers it or reaches `to`). `strongly`: strong fairness (a request taken wherever, infinitely often, it is
// allowed). The conditions and the rank read the state and the params; a helpful request's values are literals (true,
// false, a number, one of a choice's values) or terms of the state.
const LEADS = /^(.*?)\s+leads\s+to\s+(.*?)(?:\s+by\s+(.*?))?\s+via\s+(.*?)(\s+strongly)?\s*$/s
export const isLeadsTo = (expr: string): boolean => LEADS.test(expr.trim())
export function buildLeadsTo(x: Extraction, l: LawText, opts: {clock?: number} = {}): unknown {
  const m = LEADS.exec(l.expr.trim())
  if (!m) throw new LawError(`${l.name}: <from> leads to <to> [by <rank>] via <method>(<arg> = <value>, ...)`)
  const names = namesWithClock(x), r = x.rule as unknown as {leadsTo: (n: string, spec: unknown) => unknown}
  const model = x.model as unknown as {inputs: {name: string, sort: {k: string, values?: string[]}}[]} | undefined
  const sorts = (x as unknown as {sorts?: Map<string, string>}).sorts
  const ctxOf = (env: Record<string, unknown>): Ctx => ({consts: x.consts, b: env, a: env, step: false, keys: new Map(), roles: new Set(), methods: new Set(), clock: opts.clock})
  const stateOnly = (text: string, what: string) => {
    const e = parse(text), probe = ctxOf({})
    if (e.k === 'forall') read(e, probe, names, true); else val(e, probe, names, true)  // (what it reads: a bare yes/no field reads as one)
    if ([...probe.roles].some(k => ['input', 'answer', 'result', 'failed', 'old', 'method'].includes(k))) throw new LawError(`${what} reads the request or the step: it reads the state and the params`)
    return e
  }
  const from = stateOnly(m[1]!, 'its from'), to = stateOnly(m[2]!, 'its to')
  const ranks = (m[3] ? split(m[3], ',') : []).map(t => { const e = parse(t); val(e, ctxOf({}), names, true); return e })
  const mname = names.find(n => n.role === 'method')?.rule
  const helpful = split(m[4]!, ';').map(h => {
    const arrow = topIndex(h, '->')
    const when = arrow >= 0 ? stateOnly(h.slice(0, arrow), 'a helpful request\'s condition') : undefined
    const call = /^\s*(\w+)\s*\((.*)\)\s*$/s.exec(arrow >= 0 ? h.slice(arrow + 2) : h)
    if (!call) throw new LawError(`a helpful request is <method>(<arg> = <value>, ...): ${h.trim()}`)
    const method = call[1]!, args = call[2]!.trim() ? split(call[2]!, ',').map(a => { const eq = a.indexOf('='); if (eq < 0) throw new LawError(`${method}(${a.trim()}): <arg> = <value>`); return [a.slice(0, eq).trim(), a.slice(eq + 1).trim()] as [string, string] }) : []
    const ins = names.filter(n => n.role === 'input' && (n.method === method || !n.method))
    if (mname && !names.some(n => n.method === method)) {
      const ev = model?.inputs.find(v => v.name === mname)
      if (!ev?.sort.values?.includes(method)) throw new LawError(`no method ${method} (its methods: ${ev?.sort.values?.join(', ') ?? 'none'})`)
    }
    const vals = args.map(([a, v]) => {
      const n = ins.find(y => y.code === a) ?? (() => { throw new LawError(`${method}(${a}): no such argument (its arguments: ${ins.filter(y => y.method === method).map(y => y.code).join(', ')})`) })()
      if (!n.rule) throw new LawError(`${method}(${a}): an argument the rule doesn't keep`)
      return [n.rule, v, model?.inputs.find(y => y.name === n.rule)?.sort, sorts?.get(n.rule)] as const
    })
    return {when, method, vals}
  })
  const strongly = !!m[5]
  const term = (e: X, env: Record<string, unknown>): Term => { const v = val(e, ctxOf(env), names, false); const n = num(v); return n.clamped }
  const request = (h: (typeof helpful)[number]) => (env: Record<string, unknown>): Record<string, unknown> => {
    const out: Record<string, unknown> = {}
    if (mname) { const ev = model!.inputs.find(v => v.name === mname)!; out[mname] = ev.sort.values!.indexOf(h.method) }
    for (const [rule, text, sort, dom] of h.vals) {
      const lit = text.replace(/^["']|["']$/g, '')
      if (sort?.k === 'bool') { if (!['true', 'false', 'True', 'False'].includes(text)) throw new LawError(`${h.method}: ${rule} is a yes/no: true or false`); out[rule] = /^t/i.test(text) ? 1 : 0 }
      else if (sort?.k === 'choice') { const i = sort.values!.indexOf(lit); if (i < 0) throw new LawError(`${text} isn't one of ${sort.values!.join(', ')}`); out[rule] = i }
      else if (sort?.k === 'num' && dom !== 'int') out[rule] = /^\d+$/.test(text) ? Number(text) : term(parse(text), env)
      // (an integer: its two parts, the natural above 0 and the one below)
      else if (sort?.k === 'num') { const n = num(val(parse(text), ctxOf(env), names, false)); out[rule] = n.pos; out[`${rule}$neg`] = n.neg }
      else throw new LawError(`${h.method}: ${rule}, a ${sort?.k ?? 'value'}, isn't given in a helpful request (numbers, yes/no and choices are)`)
    }
    return out
  }
  return r.leadsTo(l.name, {
    from: (env: Record<string, unknown>) => read(from, ctxOf(env), names, false),
    to: (env: Record<string, unknown>) => read(to, ctxOf(env), names, false),
    ...(ranks.length ? {rank: (env: Record<string, unknown>) => ranks.map(e => term(e, env))} : {}),
    helpful: helpful.map(h => ({...(h.when ? {when: (env: Record<string, unknown>) => read(h.when!, ctxOf(env), names, false)} : {}), request: request(h)})),
    ...(strongly ? {fairness: 'strong'} : {}),
  })
}
// (the index of `tok` outside parentheses and quotes, or -1; a text split there)
function topIndex(s: string, tok: string): number {
  let depth = 0, q = ''
  for (let i = 0; i < s.length; i++) {
    const ch = s[i]!
    if (q) { if (ch === q) q = ''; continue }
    if (ch === '"' || ch === "'") q = ch
    else if (ch === '(' || ch === '[') depth++
    else if (ch === ')' || ch === ']') depth--
    else if (depth === 0 && s.startsWith(tok, i)) return i
  }
  return -1
}
function split(s: string, sep: string): string[] {
  const out: string[] = []
  let rest = s
  for (let i = topIndex(rest, sep); i >= 0; i = topIndex(rest, sep)) { out.push(rest.slice(0, i)); rest = rest.slice(i + sep.length) }
  return [...out, rest].map(t => t.trim()).filter(Boolean)
}

// (a call's arguments as written, split at the commas outside parentheses)
function splitArgs(s: string): string[] { const out: string[] = []; let d = 0, cur = ''; for (const ch of s) { if (ch === '(' || ch === '[') d++; else if (ch === ')' || ch === ']') d--; if (ch === ',' && !d) { out.push(cur.trim()); cur = '' } else cur += ch } if (cur.trim()) out.push(cur.trim()); return out }
