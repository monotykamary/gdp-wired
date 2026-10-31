// Effect's Schedule (3.x and 4.x) as a rule (`gdp-wired/effect`): a retry or repeat policy read from its source into
// one state machine, each step one of the schedule's decisions (continue after a delay, or stop). Every combinator is a
// fragment of that machine, its own state beside the others', and composes with any other: spaced, recurs, forever,
// exponential (its delay a `recur` function of the attempt, its lemmas proven by induction), fibonacci (its two
// numbers), linear, during, upTo, union/intersect (4.x: min/max), andThen (4.x: concat), whileInput/whileOutput and
// untilInput/untilOutput (4.x: while), addDelay, modifyDelay and jittered (each jittered delay an input bounded by
// its range). The rule's own state is what a law reads: `attempt` (decisions made), `retries` (those that continued),
// `delay` (the last delay decided), `elapsed` (when the last decision was made, from the first) and `done`; each step's
// inputs are `took` (how long the attempt before it ran) and, where the schedule reads it, its input (the error a
// retry feeds it). The check steps Effect's own schedule (4.x's Schedule.toStep, 3.x's step) beside the rule.
//
//   const x = extractEffect('./policy.ts', {entry: 'policy'})   // a schedule in a file, or fromSchedule(source, {effect})
//   proveRule(x.rule!, [x.rule!.law('the delay never exceeds the cap', ({delay}) => delay.atMost(5000))])
import ts from 'typescript'
import {type Cond, type FnDef, type Kind, type Rule, type Term, all, any, bool, lit, max, min, nat, no, oneOf, recur, rule, when, yes} from './dsl.ts'
import {type Law, type Rand, evalC, interpret, seeded} from './machine.ts'
import {Refusal, bare as strip, memberName, refuse, text} from './extract-read.ts'
import type {Name} from './extract.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Any = any
type Env = Record<string, Any>
// What a name is in the code: `Schedule.spaced`, `Duration.millis` (the module and the member), or undefined.
export type Api = (e: ts.Expression) => string | undefined
export type ReadCtx = {api: Api, checker: ts.TypeChecker, v4: boolean, params: Map<ts.Node, string>, sf: ts.SourceFile, bound?: Map<ts.Node, Frag>}

// --- the machine's parts ---------------------------------------------------------------------------------------------
// A fragment's step, given the rule's env, a reader of its state (its start, for a schedule entered fresh) and its
// context: how many times it was stepped before (from 0), how long since its first step, the schedule's input.
type Ctx = {attempt: Term, elapsed: Term, first: Cond}
type Res = {cont: Cond, delay: Term, out?: Term, next: Record<string, Any>}
type Frag = {step: (env: Env, get: (n: string) => Any, c: Ctx) => Res, names: string[], jitters?: string[]}
type Init = {kind: 'nat' | 'bool', init: number | boolean | ((p: Env) => Term)}
// What the reading builds beside the fragments: the rule's params, inputs, functions, assumptions, state and notes.
class Parts {
  params = new Map<string, Kind<unknown>>(); inputs = new Map<string, Kind<unknown>>(); fns: Record<string, FnDef> = {}
  assume: ((env: Env) => Cond)[] = []; state = new Map<string, Init>(); notes = new Set<string>(); jitters: {name: string, base: string, on: string, lo: [number, number], hi: [number, number]}[] = []
  inputType?: ts.Type; inputAt?: ts.Node; fields = new Map<string, Kind<unknown>>()
  private n = new Map<string, number>()
  fresh(stem: string) { const i = (this.n.get(stem) ?? 0) + 1; this.n.set(stem, i); return `${stem}${i}` }
  initOf(name: string, env: Env): Any { const s = this.state.get(name)!; return typeof s.init === 'function' ? s.init(env) : typeof s.init === 'boolean' ? (s.init ? yes : no) : lit(s.init) }
}

// A whole number of the schedule: a literal, or a param of the function that makes it (times a unit, for a duration).
type Num = {k: 'lit', v: number} | {k: 'param', name: string, scale: number}
const term = (n: Num, env: Env): Term => (n.k === 'lit' ? lit(n.v) : n.scale === 1 ? env[n.name] : env[n.name].times(n.scale))
const UNITS: Record<string, number> = {nano: 1e-6, nanos: 1e-6, micro: 1e-3, micros: 1e-3, milli: 1, millis: 1, second: 1000, seconds: 1000, minute: 60_000, minutes: 60_000, hour: 3_600_000, hours: 3_600_000, day: 86_400_000, days: 86_400_000, week: 604_800_000, weeks: 604_800_000}
const whole = (at: ts.Node, v: number, what: string): number => (Number.isSafeInteger(v) && v >= 0 ? v : refuse(at, `${what} is ${v}: a whole number of milliseconds, at least 0, is read (the rule counts milliseconds as naturals)`))

// --- the reader ------------------------------------------------------------------------------------------------------
export function readSchedule(e: ts.Expression, rc: ReadCtx, parts: Parts = new Parts()): {frag: Frag, parts: Parts} {
  return {frag: sched(e, rc, parts), parts}
}
function sched(e0: ts.Expression, rc: ReadCtx, P: Parts): Frag {
  const e = strip(e0)
  // A name: a schedule the file makes elsewhere (its value read where it is written).
  if (ts.isIdentifier(e)) {
    const d = rc.checker.getSymbolAtLocation(e)?.valueDeclaration, b = d && rc.bound?.get(d)
    if (b) { rc.bound!.delete(d!); return b }
    if (d && rc.bound && ts.isParameter(d) && rc.bound.has(d) === false && d.parent && ts.isArrowFunction(d.parent)) return refuse(e, `${e.text}: the schedule a function in a pipe is given, read twice (its state would step twice)`)
    if (d && ts.isVariableDeclaration(d) && d.initializer && d.getSourceFile() === rc.sf) return sched(d.initializer, rc, P)
    return refuse(e, `${e.text}: a schedule other than one written in this file`)
  }
  const api = ts.isPropertyAccessExpression(e) ? rc.api(e) : ts.isCallExpression(e) ? rc.api(e.expression) : undefined
  // x.pipe(f, g, ...): each a combinator given its other arguments (data-last).
  if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && memberName(e.expression.name) === 'pipe' && !api) {
    let f = sched(e.expression.expression, rc, P)
    for (const a of e.arguments) f = combinator(strip(a), f, rc, P)
    return f
  }
  const [m, op = ''] = api?.split('.') ?? []
  if (m !== 'Schedule') return refuse(e, `${text(e)}: not a schedule the reader reads (Schedule's constructors and combinators)`)
  if (ts.isPropertyAccessExpression(e)) {
    if (op === 'forever') return spacedFrag(P, {k: 'lit', v: 0})
    if (op === 'once') return recursFrag(P, {k: 'lit', v: 1})
    if (op === 'stop' && !rc.v4) return recursFrag(P, {k: 'lit', v: 0})
    return refuse(e, `Schedule.${op} (${READ})`)
  }
  const c = e as ts.CallExpression, a0 = c.arguments[0]
  switch (op) {
    case 'spaced': return spacedFrag(P, dur(a0, c, rc))
    case 'recurs': return recursFrag(P, count(a0, c, rc))
    case 'exponential': return expFrag(P, dur(a0, c, rc), c.arguments[1] ? factor(c.arguments[1], rc) : 2, c)
    case 'fibonacci': return fibFrag(P, dur(a0, c, rc))
    case 'linear': if (!rc.v4) return linearFrag(P, dur(a0, c, rc)); break
    case 'during': if (rc.v4) return duringFrag(P, dur(a0, c, rc)); break
    case 'fromDelay': case 'duration': return onceFrag(P, dur(a0, c, rc))
    case 'recurUpTo': if (!rc.v4) return upToFrag(spacedFrag(P, {k: 'lit', v: 0}), P, dur(a0, c, rc), undefined, true); break
    case 'min': case 'max': if (rc.v4) {
      const xs = a0 && ts.isArrayLiteralExpression(strip(a0)) ? (strip(a0) as ts.ArrayLiteralExpression).elements : refuse(c, `Schedule.${op} of other than an array written here`)
      if (!xs.length) return refuse(c, `Schedule.${op}([])`)
      return xs.slice(1).reduce((f, x) => both(op === 'min' ? 'union' : 'intersect', f, sched(x, rc, P), P), sched(xs[0]!, rc, P))
    } break
  }
  // A combinator given its schedule first (data-first): Schedule.union(a, b), Schedule.upTo(s, d).
  if (c.arguments.length >= 1 && COMBINATORS.has(op)) return combinator(c, sched(a0!, rc, P), rc, P, 1)
  return refuse(c, `Schedule.${op}${rc.v4 ? ' in Effect 4' : ' in Effect 3'} (${READ})`)
}
const READ = 'read: spaced, recurs, forever, once, exponential, fibonacci, linear (3.x), during (4.x), union, intersect, either, andThen (3.x), min, max, concat (4.x), upTo, whileInput, whileOutput, untilInput, untilOutput, check (3.x), while (4.x), addDelay, modifyDelay, jittered, jitteredWith (3.x), passthrough'
const COMBINATORS = new Set(['union', 'either', 'intersect', 'zipLeft', 'zipRight', 'andThen', 'concat', 'upTo', 'whileInput', 'whileOutput', 'untilInput', 'untilOutput', 'check', 'while', 'addDelay', 'modifyDelay', 'jittered', 'jitteredWith', 'passthrough'])
// A combinator applied to `self`: its call (data-last, `skip` 0) or its data-first call (`skip` 1: the schedule is its
// first argument).
function combinator(a: ts.Expression, self: Frag, rc: ReadCtx, P: Parts, skip = 0): Frag {
  // (a function of the schedule so far, written in the pipe: its body read with its parameter that schedule)
  if ((ts.isArrowFunction(a) || ts.isFunctionExpression(a)) && a.parameters.length === 1 && skip === 0) {
    const body = ts.isBlock(a.body) ? (a.body.statements.length === 1 && ts.isReturnStatement(a.body.statements[0]!) ? a.body.statements[0].expression : undefined) : a.body
    if (!body) return refuse(a, 'a function in a pipe other than one returning a schedule')
    ;(rc.bound ??= new Map()).set(a.parameters[0]!, self)
    return sched(body, rc, P)
  }
  const api = rc.api(ts.isCallExpression(a) ? a.expression : a) ?? ''
  const [m, op = ''] = api.split('.')
  if (m !== 'Schedule') return refuse(a, `${text(a)} in a schedule's pipe (${READ})`)
  // (a value given to pipe: Schedule.jittered, Schedule.passthrough)
  if (!ts.isCallExpression(a) || (skip === 1 && a.arguments.length === 1)) {
    if (op === 'jittered') return jitterFrag(self, P, [4, 5], [6, 5])
    if (op === 'passthrough') return {...self, step: (env, get, c) => ({...self.step(env, get, c), out: undefined})}
    return refuse(a, `Schedule.${op} given as a value (${READ})`)
  }
  const args = a.arguments.slice(skip), x = args[0]
  const other = () => sched(x ?? refuse(a, `Schedule.${op}() with no schedule`), rc, P)
  switch (op) {
    case 'union': case 'either': if (!rc.v4) return both('union', self, other(), P); break
    case 'intersect': case 'zipLeft': case 'zipRight': if (!rc.v4) return both('intersect', self, other(), P); break
    case 'andThen': case 'concat': if ((op === 'concat') === rc.v4) return andThenFrag(self, other(), P); break
    case 'upTo':
      if (!rc.v4) return upToFrag(self, P, dur(x, a, rc), undefined, true)
      if (x && ts.isObjectLiteralExpression(strip(x))) {
        const o = strip(x) as ts.ObjectLiteralExpression, get = (k: string) => (o.properties.find(p => ts.isPropertyAssignment(p) && memberName(p.name) === k) as ts.PropertyAssignment | undefined)?.initializer
        for (const p of o.properties) if (!ts.isPropertyAssignment(p) || !['duration', 'times'].includes(memberName(p.name))) refuse(p, `Schedule.upTo's ${text(p)} (duration and times are read)`)
        return upToFrag(self, P, get('duration') && dur(get('duration'), a, rc), get('times') && count(get('times'), a, rc), false)
      }
      return refuse(a, 'Schedule.upTo of other than {duration, times} written here')
    case 'whileInput': case 'untilInput': case 'whileOutput': case 'untilOutput': if (!rc.v4) return whileFrag(self, P, x, rc, op); break
    case 'check': if (!rc.v4) return whileFrag(self, P, x, rc, op); break
    case 'while': if (rc.v4) return whileFrag(self, P, x, rc, op); break
    case 'addDelay': case 'modifyDelay': return delayFrag(self, P, x, rc, op)
    case 'jitteredWith': if (!rc.v4) {
      const o = x && ts.isObjectLiteralExpression(strip(x)) ? strip(x) as ts.ObjectLiteralExpression : refuse(a, 'Schedule.jitteredWith of other than {min, max} written here')
      const get = (k: string, d: [number, number]): [number, number] => { const p = o.properties.find(q => ts.isPropertyAssignment(q) && memberName(q.name) === k) as ts.PropertyAssignment | undefined; return p ? ratio(p.initializer) : d }
      return jitterFrag(self, P, get('min', [4, 5]), get('max', [6, 5]))
    } break
  }
  return refuse(a, `Schedule.${op}${rc.v4 ? ' in Effect 4' : ' in Effect 3'} (${READ})`)
}

// A duration: 'N unit', a number of milliseconds, Duration.<unit>(n) of a literal or a param, a const of the file.
function dur(x: ts.Expression | undefined, at: ts.Node, rc: ReadCtx): Num {
  if (!x) return refuse(at, `${text(at)} with no duration`)
  const e = strip(x)
  if (ts.isStringLiteral(e) || ts.isNoSubstitutionTemplateLiteral(e)) {
    const m = /^\s*(\d+(?:\.\d+)?)\s*([a-z]+)\s*$/.exec(e.text)
    if (!m || !(m[2]! in UNITS)) return refuse(e, `the duration ${e.getText()} (a number and a unit, as Duration reads it)`)
    return {k: 'lit', v: whole(e, Number(m[1]) * UNITS[m[2]!]!, e.getText())}
  }
  if (ts.isCallExpression(e)) {
    const api = rc.api(e.expression) ?? '', unit = /^Duration\.(millis|seconds|minutes|hours|days|weeks)$/.exec(api)?.[1]
    if (unit) { const n = count(e.arguments[0], e, rc); return n.k === 'lit' ? {k: 'lit', v: whole(e, n.v * UNITS[unit]!, e.getText())} : {...n, scale: n.scale * UNITS[unit]!} }
    if (api === 'Duration.decode' || api === 'Duration.fromInputUnsafe') return dur(e.arguments[0], e, rc)
    return refuse(e, `the duration ${text(e)} (Duration.millis, seconds, minutes, hours, days or weeks, a number of milliseconds, or 'N unit')`)
  }
  if (ts.isPropertyAccessExpression(e) && rc.api(e) === 'Duration.zero') return {k: 'lit', v: 0}
  const n = count(e, at, rc)
  return n
}
// A whole number: a literal, a param of the function that makes the schedule, or a const of the file.
function count(x: ts.Expression | undefined, at: ts.Node, rc: ReadCtx): Num {
  if (!x) return refuse(at, `${text(at)} with no number`)
  const e = strip(x)
  if (ts.isNumericLiteral(e)) return {k: 'lit', v: whole(e, Number(e.text), e.text)}
  if (ts.isIdentifier(e)) {
    const d = rc.checker.getSymbolAtLocation(e)?.valueDeclaration
    const p = d && rc.params.get(d)
    if (p) return {k: 'param', name: p, scale: 1}
    if (d && ts.isVariableDeclaration(d) && d.initializer && ts.isVariableDeclarationList(d.parent) && d.parent.flags & ts.NodeFlags.Const) return count(d.initializer, at, rc)
  }
  return refuse(e, `${text(e)}: a number other than a literal, a const or a param of the function making the schedule`)
}
const factor = (x: ts.Expression, rc: ReadCtx): number => {
  const n = count(x, x, rc)
  return n.k === 'lit' && n.v >= 1 ? n.v : refuse(x, `an exponential's factor ${text(x)}: a whole number at least 1, written here, is read (another makes fractional delays)`)
}
// A fraction written as a decimal literal (jitter's bounds): [p, q] for p / q.
const ratio = (x: ts.Expression): [number, number] => {
  const e = strip(x)
  if (!ts.isNumericLiteral(e)) return refuse(e, `${text(e)}: a jitter's bound other than a number written here`)
  const [i = '', f = ''] = e.text.split('.'), q = 10 ** f.length
  return [Number(i + f), q]
}

// --- the fragments ---------------------------------------------------------------------------------------------------
const nat0 = (P: Parts, stem: string) => { const n = P.fresh(stem); P.state.set(n, {kind: 'nat', init: 0}); return n }
const flag = (P: Parts, stem: string, init = false) => { const n = P.fresh(stem); P.state.set(n, {kind: 'bool', init}); return n }
const leaf = (step: Frag['step']): Frag => ({step, names: []})

function spacedFrag(P: Parts, d: Num): Frag { void P; return leaf((env, _, c) => ({cont: yes, delay: term(d, env), out: c.attempt, next: {}})) }
function recursFrag(P: Parts, n: Num): Frag { void P; return leaf((env, _, c) => ({cont: c.attempt.lt(term(n, env)), delay: lit(0), out: c.attempt, next: {}})) }
function onceFrag(P: Parts, d: Num): Frag { void P; return leaf((env, _, c) => ({cont: c.attempt.eq(0), delay: when(c.attempt.eq(0), term(d, env), 0), next: {}})) }
function duringFrag(P: Parts, d: Num): Frag { void P; return leaf((env, _, c) => ({cont: c.elapsed.atMost(term(d, env)), delay: lit(0), out: c.elapsed, next: {}})) }
function linearFrag(P: Parts, d: Num): Frag {
  return leaf((env, _, c) => { const base = term(d, env), at = c.attempt.plus(1), delay = d.k === 'lit' ? at.times(d.v) : base.mul(at); void P; return {cont: yes, delay, out: delay, next: {}} })
}
// The exponential's delay: base·factor^attempt, a function defined by its recurrence on the attempt, its lemmas (at
// least the base; never shrinks) proven by induction when it is made.
const exps = new Map<string, FnDef>()
function expFrag(P: Parts, d: Num, f: number, at: ts.Node): Frag {
  void at
  const name = d.k === 'lit' ? `exponential_x${f}_b${d.v}` : `exponential_x${f}`
  let fd = exps.get(name)
  if (!fd) {
    fd = d.k === 'lit'
      ? recur(name, {zero: d.v, next: (_, p) => p.times(f)}, {'at least the base': (_, p) => p.atLeast(d.v)}, {'never shrinks': (_, p, __, q) => p.atMost(q)})
      : recur(name, {args: ['base'] as const, zero: ({base}) => base, next: (_, p) => p.times(f)}, {'at least the base': (_, p, {base}) => p.atLeast(base)}, {'never shrinks': (_, p, __, q) => p.atMost(q)}) as FnDef
    exps.set(name, fd)
  }
  P.fns[name] = fd
  P.notes.add(`an exponential's delay is ${name}(attempt), defined by its recurrence (base, then ×${f} a step); its lemmas (at least the base; never shrinks) are proven by induction and are its facts`)
  return leaf((env, _, c) => { const delay: Term = d.k === 'lit' ? env[name](c.attempt) : env[name](c.attempt, term(d, env)); return {cont: yes, delay, out: delay, next: {}} })
}
// Fibonacci: its two numbers in the state (one, one, two, three, ...), as Effect keeps them.
function fibFrag(P: Parts, d: Num): Frag {
  const a = P.fresh('fib_a'), b = P.fresh('fib_b')
  P.state.set(a, {kind: 'nat', init: 0}); P.state.set(b, {kind: 'nat', init: d.k === 'lit' ? d.v : (p: Env) => term(d, p)})
  return {names: [a, b], step: (_, get) => ({cont: yes, delay: get(b), out: get(b), next: {[a]: get(b), [b]: get(a).plus(get(b))}})}
}
// union: either goes on, the smaller delay of those that do; intersect: both go on, the larger delay.
function both(how: 'union' | 'intersect', l: Frag, r: Frag, P: Parts): Frag {
  void P
  return {names: [...l.names, ...r.names], jitters: [...l.jitters ?? [], ...r.jitters ?? []], step: (env, get, c) => {
    const x = l.step(env, get, c), y = r.step(env, get, c)
    const cont = how === 'union' ? any(x.cont, y.cont) : all(x.cont, y.cont)
    const delay = how === 'union' ? when(x.cont.and(y.cont), min(x.delay, y.delay), when(x.cont, x.delay, y.delay)) : max(x.delay, y.delay)
    return {cont, delay, next: {...x.next, ...y.next}}
  }}
}
// andThen: the first until it stops, then the second from its start (stepped at once, as Effect steps it), its own
// attempts and elapsed time counted from there.
function andThenFrag(l: Frag, r: Frag, P: Parts): Frag {
  const phase = flag(P, 'then'), n = nat0(P, 'then_n'), start = nat0(P, 'then_start')
  return {names: [...l.names, ...r.names, phase, n, start], jitters: [...l.jitters ?? [], ...r.jitters ?? []], step: (env, get, c) => {
    const inR: Cond = get(phase), now = env.$now as Term
    const x = l.step(env, get, c), fromStart = (k: string) => (r.names.includes(k) ? P.initOf(k, env) : get(k))
    const dl = (l.jitters ?? []).map(j => env[`${j}$on`] as Cond)
    const y0 = r.step(env, fromStart, {attempt: lit(0), elapsed: lit(0), first: yes}), d0 = (r.jitters ?? []).map(j => ({d: env[`${j}$d`], on: env[`${j}$on`] as Cond}))
    const y1 = r.step(env, get, {attempt: get(n), elapsed: now.minus(get(start)), first: get(n).eq(0)})
    // (a jitter of the second schedule jitters the delay of the step taken: from its start, or where it is)
    ;(r.jitters ?? []).forEach((j, i) => { env[`${j}$d`] = when(inR, env[`${j}$d`], d0[i]!.d); env[`${j}$on`] = when(inR, env[`${j}$on`], d0[i]!.on.and(inR.not(), x.cont.not())) })
    ;(l.jitters ?? []).forEach((j, i) => { env[`${j}$on`] = inR.not().and(dl[i]!) })
    const toR = inR.not().and(x.cont.not())
    const pick = <T>(a: T, b: T, cc: T): T => when(inR, a as Any, when(x.cont, b as Any, cc as Any))
    const next: Record<string, Any> = {}
    for (const k of l.names) next[k] = when(inR, get(k), x.next[k] ?? get(k))
    for (const k of r.names) next[k] = pick(y1.next[k] ?? get(k), get(k), y0.next[k] ?? P.initOf(k, env))
    for (const j of r.jitters ?? []) { const on = P.jitters.find(q => q.name === j)!.on; next[on] = env[`${j}$on`] }
    for (const j of l.jitters ?? []) { const on = P.jitters.find(q => q.name === j)!.on; next[on] = env[`${j}$on`] }
    next[phase] = inR.or(toR); next[n] = when(inR.or(toR), get(n).plus(1), get(n)); next[start] = when(toR, now, get(start))
    return {cont: pick(y1.cont, yes, y0.cont), delay: pick(y1.delay, x.delay, y0.delay), next}
  }}
}
// upTo: goes on while the elapsed time is within the duration (3.x: below it; 4.x: at most it) and, in 4.x, while it has
// been stepped fewer than `times` times.
function upToFrag(self: Frag, P: Parts, d: Num | undefined, times: Num | undefined, strict: boolean): Frag {
  void P
  return {...self, step: (env, get, c) => {
    const x = self.step(env, get, c)
    const within = d ? (strict ? c.elapsed.lt(term(d, env)) : c.elapsed.atMost(term(d, env))) : yes, few = times ? c.attempt.lt(term(times, env)) : yes
    return {...x, cont: all(x.cont, within, few)}
  }}
}
// jittered: the delay drawn between lo and hi times the delay (Effect's Random); in the rule an input of each step,
// assumed within the range rounded outward to whole milliseconds, the delay it jitters kept beside it.
function jitterFrag(self: Frag, P: Parts, lo: [number, number], hi: [number, number]): Frag {
  const j = P.fresh('jitter'), base = nat0(P, `${j}_base`), on = flag(P, `${j}_on`)
  P.inputs.set(j, nat)
  P.jitters.push({name: j, base, on, lo, hi})
  P.notes.add(`each jittered delay is an input (${j}), assumed between ${lo[0] / lo[1]} and ${hi[0] / hi[1]} times the delay it jitters, rounded outward to whole milliseconds: Effect draws a real number there, and a decision on the time (at most a whole number of milliseconds, as upTo and during make it) comes out the same with the run's times rounded up`)
  // (the range assumed where the jitter is drawn: the delay it jitters goes on, in a schedule the step takes)
  P.assume.push(env => { const d: Term = env[`${j}$d`] ?? lit(0), used: Cond = env[`${j}$on`] ?? no; return used.implies(all(d.times(lo[0]).atMost(env[j].times(lo[1]).plus(lo[1] - 1)), env[j].times(hi[1]).atMost(d.times(hi[0]).plus(hi[1] - 1)))) })
  return {names: [...self.names, base, on], jitters: [...self.jitters ?? [], j], step: (env, get, c) => {
    const x = self.step(env, get, c)
    env[`${j}$d`] = x.delay; env[`${j}$on`] = x.cont
    return {...x, delay: when(x.cont, env[j], x.delay), next: {...x.next, [base]: x.delay, [on]: x.cont}}
  }}
}
// while / whileInput / whileOutput / untilInput / untilOutput / check: goes on where the inner one does and the predicate
// holds of the input, the output or (4.x) the metadata.
function whileFrag(self: Frag, P: Parts, f: ts.Expression | undefined, rc: ReadCtx, op: string): Frag {
  const fn = f && strip(f)
  if (!fn || !(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn))) return refuse(f ?? fn!, `Schedule.${op} of other than a function written here`)
  return {...self, step: (env, get, c) => {
    const x = self.step(env, get, c)
    const ctx = callbackCtx(fn, rc, P, env, c, x, op)
    const v = body(fn, ctx), ok = asCond(v, fn)
    return {...x, cont: x.cont.and(/^until/.test(op) ? ok.not() : ok)}
  }}
}
// addDelay / modifyDelay: the delay the function gives (3.x: of the output and the delay; 4.x: of the metadata, as an
// effect), added to the delay or put in its place.
function delayFrag(self: Frag, P: Parts, f: ts.Expression | undefined, rc: ReadCtx, op: string): Frag {
  const fn = f && strip(f)
  if (!fn || !(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn))) return refuse(f ?? fn!, `Schedule.${op} of other than a function written here`)
  return {...self, step: (env, get, c) => {
    const x = self.step(env, get, c)
    const v = asDur(body(fn, callbackCtx(fn, rc, P, env, c, x, op)), fn)
    return {...x, delay: when(x.cont, op === 'addDelay' ? x.delay.plus(v) : v, x.delay)}
  }}
}

// --- the functions combinators are given: read as terms over the step ------------------------------------------------
type Val = {t: 'num', e: Term} | {t: 'dur', e: Term} | {t: 'bool', c: Cond} | {t: 'str', s: string} | {t: 'choice', e: Any} | {t: 'obj', field: (k: string, at: ts.Node) => Val} | {t: 'eff', v: Val}
type CbCtx = {rc: ReadCtx, P: Parts, env: Env, vars: Map<ts.Node, Val>}
function callbackCtx(fn: ts.ArrowFunction | ts.FunctionExpression, rc: ReadCtx, P: Parts, env: Env, c: Ctx, x: Res, op: string): CbCtx {
  const vars = new Map<ts.Node, Val>()
  const out = (at: ts.Node): Val => (x.out ? {t: 'dur', e: x.out} : refuse(at, `the output of this schedule (a combination, or one whose output isn't a number or a duration): ${op} reads it`))
  const input = (p: ts.ParameterDeclaration): Val => inputVal(p, rc, P, env)
  const ps = fn.parameters
  const bind = (p: ts.ParameterDeclaration | undefined, v: () => Val) => {
    if (!p) return
    if (ts.isIdentifier(p.name)) { vars.set(p, v()); return }
    if (ts.isObjectBindingPattern(p.name)) {
      const o = v()
      for (const el of p.name.elements) { const k = memberName((el.propertyName ?? el.name) as ts.PropertyName); vars.set(el, o.t === 'obj' ? o.field(k, el) : refuse(el, `${k} of a value with no fields`)) }
      return
    }
    refuse(p, `the parameter ${text(p)} (a name, or {fields} of the metadata)`)
  }
  if (rc.v4) {
    // 4.x's metadata: input, output, attempt (from 1), elapsed, duration (the delay).
    const p = ps[0]
    const meta: Val = {t: 'obj', field: (k, at) => k === 'input' ? (p ? inputVal(p, rc, P, env, 'input') : refuse(at, 'input')) : k === 'output' ? out(at) : k === 'attempt' ? {t: 'num', e: c.attempt.plus(1)} : k === 'elapsed' ? {t: 'dur', e: c.elapsed} : k === 'duration' ? {t: 'dur', e: x.delay}
      : refuse(at, `the metadata's ${k} (input, output, attempt, elapsed and duration are read)`)}
    bind(p, () => meta)
  } else if (op === 'whileInput' || op === 'untilInput') bind(ps[0], () => input(ps[0]!))
  else if (op === 'whileOutput' || op === 'untilOutput' || op === 'addDelay') bind(ps[0], () => out(ps[0]!))
  else if (op === 'check') { bind(ps[0], () => input(ps[0]!)); bind(ps[1], () => out(ps[1]!)) }
  else if (op === 'modifyDelay') { bind(ps[0], () => out(ps[0]!)); bind(ps[1], () => ({t: 'dur', e: x.delay})) }
  return {rc, P, env, vars}
}
// The schedule's input (a retry's error): a number, a boolean, a choice of strings, or an object whose fields read are
// those (a tagged error's _tag a choice of its cases' tags). Each is an input of the step.
function inputVal(p: ts.ParameterDeclaration, rc: ReadCtx, P: Parts, env: Env, sub?: string): Val {
  let t = rc.checker.getTypeAtLocation(p)
  if (sub) t = propType(rc.checker, t, sub, p) ?? refuse(p, `no type for the input of ${text(p)}`)
  P.inputType ??= t; P.inputAt ??= p
  // (an input first read while the rule is made: a stand-in, the rule made again with it)
  const scalar = (ty: ts.Type | ts.Type[], name: string, at: ts.Node): Val => {
    const k = kindOfType(ty, rc.checker, at)
    if (!P.inputs.has(name)) { P.inputs.set(name, k); P.fields.set(name, k) }
    const v = env[name] ?? (k === nat ? lit(0) : k === bool ? no : {is: () => no})
    return k === nat ? {t: 'num', e: v} : k === bool ? {t: 'bool', c: v} : {t: 'choice', e: v}
  }
  if (t.flags & (ts.TypeFlags.NumberLike | ts.TypeFlags.BooleanLike | ts.TypeFlags.StringLike) || (t.isUnion() && t.types.every(u => u.flags & (ts.TypeFlags.StringLiteral | ts.TypeFlags.BooleanLike)))) return scalar(t, 'input', p)
  return {t: 'obj', field: (k, at) => {
    const types = t.isUnion() ? t.types : [t]
    if (k === '_tag') {
      const tags = types.map(u => { const pt = propType(rc.checker, u, '_tag', at); return pt?.isStringLiteral() ? pt.value : undefined })
      if (tags.some(x => x === undefined)) return refuse(at, `_tag of an input whose cases aren't each tagged`)
      const name = 'input__tag'
      if (!P.inputs.has(name)) { const kd = oneOf(...new Set(tags as string[])) as Kind<unknown>; P.inputs.set(name, kd); P.fields.set('_tag', kd) }
      return {t: 'choice', e: env[name] ?? {is: () => no}}
    }
    const pts = types.map(u => propType(rc.checker, u, k, at))
    if (pts.some(x => !x)) return refuse(at, `the input's ${k}, which not every case of it has`)
    const name = `input_${k}`, v = scalar(pts as ts.Type[], name, at)
    P.fields.set(k, P.inputs.get(name)!)
    return v
  }}
}
// A property's type, through its symbol (the checker's public API).
const propType = (checker: ts.TypeChecker, t: ts.Type, k: string, at: ts.Node): ts.Type | undefined => { const p = t.getProperty(k); return p && checker.getTypeOfSymbolAtLocation(p, at) }
// The kind of an input's type (or of the union of several: a field each case of a union has).
const kindOfType = (t0: ts.Type | ts.Type[], checker: ts.TypeChecker, at: ts.Node): Kind<unknown> => {
  const ts0 = Array.isArray(t0) ? t0 : [t0], all = ts0.flatMap(t => (t.isUnion() ? t.types : [t]))
  if (all.every(t => t.flags & ts.TypeFlags.NumberLike)) return nat
  if (all.every(t => t.flags & ts.TypeFlags.BooleanLike)) return bool
  const lits = all.map(u => (u.isStringLiteral() ? u.value : undefined))
  if (lits.every(x => x !== undefined)) return oneOf(...new Set(lits as string[])) as Kind<unknown>
  return refuse(at, `the input's ${ts0.map(t => checker.typeToString(t)).join(' | ')} (a number, a boolean, a string literal or a tagged error is read)`)
}
const asCond = (v: Val, at: ts.Node): Cond => (v.t === 'bool' ? v.c : v.t === 'eff' ? asCond(v.v, at) : refuse(at, `${text(at)} gives other than a boolean`))
const asNum = (v: Val, at: ts.Node): Term => (v.t === 'num' || v.t === 'dur' ? v.e : refuse(at, `${text(at)} is other than a number`))
const asDur = (v: Val, at: ts.Node): Term => (v.t === 'dur' || v.t === 'num' ? v.e : v.t === 'eff' ? asDur(v.v, at) : v.t === 'str' ? lit(strDur(v.s, at)) : refuse(at, `${text(at)} gives other than a duration`))
const strDur = (s: string, at: ts.Node): number => { const m = /^\s*(\d+(?:\.\d+)?)\s*([a-z]+)\s*$/.exec(s); return m && m[2]! in UNITS ? whole(at, Number(m[1]) * UNITS[m[2]!]!, s) : refuse(at, `the duration '${s}'`) }
function body(fn: ts.ArrowFunction | ts.FunctionExpression, c: CbCtx): Val {
  const b = fn.body
  if (!ts.isBlock(b)) return val(b, c)
  const st = b.statements
  if (st.length !== 1 || !ts.isReturnStatement(st[0]!) || !st[0].expression) return refuse(b, 'a function body other than one return (write it as an expression)')
  return val(st[0].expression, c)
}
function val(e0: ts.Expression, c: CbCtx): Val {
  const e = strip(e0)
  if (ts.isNumericLiteral(e)) return {t: 'num', e: lit(whole(e, Number(e.text), e.text))}
  if (ts.isStringLiteral(e) || ts.isNoSubstitutionTemplateLiteral(e)) return {t: 'str', s: e.text}
  if (e.kind === ts.SyntaxKind.TrueKeyword) return {t: 'bool', c: yes}
  if (e.kind === ts.SyntaxKind.FalseKeyword) return {t: 'bool', c: no}
  if (ts.isIdentifier(e)) {
    const d = c.rc.checker.getSymbolAtLocation(e)?.valueDeclaration
    const v = d && (c.vars.get(d) ?? (ts.isBindingElement(d) ? c.vars.get(d) : undefined))
    if (v) return v
    const n = count(e, e, c.rc)
    return {t: 'num', e: term(n, c.env)}
  }
  if (ts.isPropertyAccessExpression(e)) {
    const api = c.rc.api(e)
    if (api === 'Duration.zero') return {t: 'dur', e: lit(0)}
    const o = val(e.expression, c)
    return o.t === 'obj' ? o.field(memberName(e.name), e) : refuse(e, `${text(e)}: a field of a value with no fields`)
  }
  if (ts.isPrefixUnaryExpression(e) && e.operator === ts.SyntaxKind.ExclamationToken) return {t: 'bool', c: asCond(val(e.operand, c), e.operand).not()}
  if (ts.isConditionalExpression(e)) {
    const k = asCond(val(e.condition, c), e.condition), a = val(e.whenTrue, c), b = val(e.whenFalse, c)
    if (a.t === 'bool' || b.t === 'bool') return {t: 'bool', c: when(k, asCond(a, e.whenTrue), asCond(b, e.whenFalse))}
    return {t: a.t === 'dur' || b.t === 'dur' ? 'dur' : 'num', e: when(k, a.t === 'str' ? asDur(a, e) : asNum(a, e.whenTrue), b.t === 'str' ? asDur(b, e) : asNum(b, e.whenFalse))}
  }
  if (ts.isBinaryExpression(e)) {
    const o = e.operatorToken.kind, K = ts.SyntaxKind
    if (o === K.AmpersandAmpersandToken || o === K.BarBarToken) { const a = asCond(val(e.left, c), e.left), b = asCond(val(e.right, c), e.right); return {t: 'bool', c: o === K.AmpersandAmpersandToken ? a.and(b) : a.or(b)} }
    const a = val(e.left, c), b = val(e.right, c)
    if (o === K.EqualsEqualsEqualsToken || o === K.ExclamationEqualsEqualsToken || o === K.EqualsEqualsToken || o === K.ExclamationEqualsToken) {
      const neg = o === K.ExclamationEqualsEqualsToken || o === K.ExclamationEqualsToken
      const eq = a.t === 'choice' && b.t === 'str' ? a.e.is(b.s) : b.t === 'choice' && a.t === 'str' ? b.e.is(a.s) : a.t === 'bool' && b.t === 'bool' ? a.c.iff(b.c) : asNum(a, e.left).eq(asNum(b, e.right))
      return {t: 'bool', c: neg ? eq.not() : eq}
    }
    const x = asNum(a, e.left), y = asNum(b, e.right), t = a.t === 'dur' || b.t === 'dur' ? 'dur' : 'num'
    if (o === K.MinusToken) return refuse(e, `${text(e)}: a subtraction (a natural's is truncated at 0, JavaScript's isn't)`)
    if (o === K.AsteriskToken) { const r = strip(e.right), l = strip(e.left); return {t, e: ts.isNumericLiteral(r) ? x.times(Number(r.text)) : ts.isNumericLiteral(l) ? y.times(Number(l.text)) : x.mul(y)} }
    if (o === K.PlusToken) return {t, e: x.plus(y)}
    const cmp = new Map<ts.SyntaxKind, () => Cond>([[K.LessThanToken, () => x.lt(y)], [K.LessThanEqualsToken, () => x.atMost(y)], [K.GreaterThanToken, () => x.gt(y)], [K.GreaterThanEqualsToken, () => x.atLeast(y)]]).get(o)
    if (cmp) return {t: 'bool', c: cmp()}
    return refuse(e, `${text(e)} (comparisons, + and * are read)`)
  }
  if (ts.isCallExpression(e)) {
    const api = c.rc.api(e.expression) ?? '', [m, op = ''] = api.split('.'), args = e.arguments.map(a => () => val(a, c))
    if (m === 'Effect' && op === 'succeed') return {t: 'eff', v: args[0]!()}
    if (m === 'Duration') {
      const d = (i: number) => asDur(args[i]!(), e.arguments[i]!)
      if (UNITS[op] !== undefined && op !== 'nanos' && op !== 'micros') { const n = asNum(args[0]!(), e.arguments[0]!); return {t: 'dur', e: UNITS[op] === 1 ? n : n.times(UNITS[op]!)} }
      if (op === 'toMillis' || op === 'decode' || op === 'fromInputUnsafe') return {t: 'dur', e: d(0)}
      if (op === 'sum') return {t: 'dur', e: d(0).plus(d(1))}
      if (op === 'min' || op === 'max') return {t: 'dur', e: (op === 'min' ? min : max)(d(0), d(1))}
      if (op === 'times') { const k = strip(e.arguments[1]!); return ts.isNumericLiteral(k) ? {t: 'dur', e: d(0).times(whole(k, Number(k.text), k.text))} : refuse(k, 'Duration.times by other than a whole number written here') }
      const cmp: Record<string, (a: Term, b: Term) => Cond> = {lessThan: (a, b) => a.lt(b), isLessThan: (a, b) => a.lt(b), lessThanOrEqualTo: (a, b) => a.atMost(b), isLessThanOrEqualTo: (a, b) => a.atMost(b), greaterThan: (a, b) => a.gt(b), isGreaterThan: (a, b) => a.gt(b), greaterThanOrEqualTo: (a, b) => a.atLeast(b), isGreaterThanOrEqualTo: (a, b) => a.atLeast(b)}
      if (cmp[op]) return {t: 'bool', c: cmp[op]!(d(0), d(1))}
    }
    if (api === '' && ts.isPropertyAccessExpression(e.expression) && ts.isIdentifier(e.expression.expression) && e.expression.expression.text === 'Math' && ['min', 'max'].includes(memberName(e.expression.name)) && args.length === 2) {
      const a = val(e.arguments[0]!, c), b = val(e.arguments[1]!, c)
      return {t: a.t === 'dur' || b.t === 'dur' ? 'dur' : 'num', e: (memberName(e.expression.name) === 'min' ? min : max)(asNum(a, e), asNum(b, e))}
    }
    return refuse(e, `${text(e)} in a schedule's function (Duration's arithmetic and comparisons, Math.min and max, Effect.succeed are read)`)
  }
  return refuse(e, `${text(e)} in a schedule's function`)
}

// --- the rule --------------------------------------------------------------------------------------------------------
export type ScheduleRule = {rule: Rule, notes: string[], names: Name[], jitters: Parts['jitters'], fields: Map<string, Kind<unknown>>, params: string[], v4: boolean}
// The schedule's machine: the fragment's state beside the schedule's own, one decision a step, nothing after it stops.
export function scheduleRule(frag: Frag, P: Parts, name: string, v4: boolean): ScheduleRule {
  // (made again while reading it finds inputs: a function given to a combinator reads the schedule's input)
  for (let i = 0; ; i++) { const n = P.inputs.size, s = makeRule(frag, P, name, v4); void s.rule.machine; if (P.inputs.size === n || i > 4) return s }
}
function makeRule(frag: Frag, P: Parts, name: string, v4: boolean): ScheduleRule {
  const st: Record<string, Any> = {attempt: 0, retries: 0, delay: 0, elapsed: 0, done: bool.from(false)}
  for (const [n, s] of P.state) st[n] = s.kind === 'bool' ? bool.from(s.init as boolean) : typeof s.init === 'function' ? s.init : s.init
  let r: Any = rule(name).params(Object.fromEntries(P.params)).inputs({took: nat, ...Object.fromEntries(P.inputs)})
  if (Object.keys(P.fns).length) r = r.fns(P.fns)
  r = r.state(st)
  // (the step's terms, made once per env: the assumption reads the jittered delays the step decides)
  const decide = (env: Env) => {
    const first = env.attempt.eq(0), now = when(first, 0, env.elapsed.plus(env.delay).plus(env.took))
    const e2 = Object.assign(Object.create(null), env, {$now: now}) as Env
    return {e2, now, x: frag.step(e2, k => e2[k], {attempt: env.attempt, elapsed: now, first})}
  }
  if (P.assume.length) r = r.assume((env: Env) => { const {e2} = decide(env); return all(...P.assume.map(a => a(e2))) })
  r = r.step((env: Env) => {
    const {x, now} = decide(env), live: Cond = env.done.not()
    const out: Record<string, Any> = {
      attempt: when(live, env.attempt.plus(1), env.attempt), retries: when(live.and(x.cont), env.retries.plus(1), env.retries),
      delay: when(live.and(x.cont), x.delay, env.delay), elapsed: when(live, now, env.elapsed), done: env.done.or(x.cont.not()),
    }
    for (const [n] of P.state) out[n] = n in x.next ? when(live, x.next[n], env[n]) : env[n]
    return out
  })
  const names: Name[] = [
    ...['attempt', 'retries', 'delay', 'elapsed', 'done'].map(n => ({code: n, rule: n, role: 'state' as const})),
    ...[...P.state.keys()].map(n => ({code: n, rule: n, role: 'state' as const})),
    ...[...P.params.keys()].map(n => ({code: n, rule: n, role: 'param' as const})),
    {code: 'took', rule: 'took', role: 'input'}, ...[...P.inputs.keys()].map(n => ({code: n.replace(/^input_/, 'input.'), rule: n, role: 'input' as const})),
  ]
  return {rule: r as Rule, notes: [...P.notes], names, jitters: P.jitters, fields: P.fields, params: [...P.params.keys()], v4}
}

// --- Effect's own schedule, stepped ---------------------------------------------------------------------------------
// One decision at `now` with `input`, the Random answering `randoms` in turn: whether it goes on, and its delay in
// milliseconds (a real number where jittered).
type Decide = (now: number, input: unknown, randoms: number[]) => {cont: boolean, delay: number}
export function stepper(E: Any, schedule: unknown): Decide {
  const {Effect} = E, v4 = 'TxRef' in E
  const rnd = (rs: number[]) => () => { const r = rs.shift(); if (r === undefined) throw new Error('the schedule drew more randoms than the rule has jitters'); return r }
  if (v4) {
    const step = Effect.runSync(E.Schedule.toStep(schedule)) as (now: number, input: unknown) => unknown
    return (now, input, rs) => {
      const next = rnd(rs), eff = E.Pull.matchEffect(step(now, input), {onSuccess: ([, d]: [unknown, unknown]) => Effect.succeed({cont: true, delay: E.Duration.toMillis(d)}), onDone: () => Effect.succeed({cont: false, delay: 0}), onFailure: Effect.failCause})
      return Effect.runSync(Effect.provideService(eff, E.Random.Random, {nextDoubleUnsafe: next, nextIntUnsafe: () => Math.floor(next() * 2 ** 31)}))
    }
  }
  const s = schedule as {initial: unknown, step: (now: number, input: unknown, state: unknown) => unknown}
  let state = s.initial
  const base = Effect.runSync(Effect.random)
  return (now, input, rs) => {
    const next = rnd(rs), random = Object.create(base, {next: {get: () => Effect.sync(next)}})
    const [st, , dec] = Effect.runSync(Effect.withRandom(s.step(now, input, state), random)) as [unknown, unknown, {_tag: string, intervals: unknown}]
    state = st
    return dec._tag === 'Done' ? {cont: false, delay: 0} : {cont: true, delay: E.ScheduleIntervals.start(dec.intervals) - now}
  }
}

// The rule beside Effect's schedule: `runs` runs of `depth` decisions, each attempt taking a drawn time, each input
// drawn, each jitter drawn within its range and Effect's Random answering what gives it. They must decide alike: go on
// together, with the same delay (within a millionth of a millisecond, a jittered delay being Effect's real number).
export function scheduleConforms(s: ScheduleRule, make: (params: Record<string, number>) => unknown, E: Any, opts: {runs?: number, depth?: number, seed?: number, params?: (rand: Rand) => Record<string, number>, input?: (rand: Rand) => unknown} = {}): {checked: number, failure?: string} {
  const rand = seeded(opts.seed ?? 1), r = s.rule as Any, g = r.compiled(), free = interpret({...r.machine, assume: undefined})
  let checked = 0
  for (let run = 0; run < (opts.runs ?? 100); run++) {
    const params = opts.params?.(rand) ?? Object.fromEntries(s.params.map(p => [p, rand(6)]))
    const ps = r.encodeParams(params), decide = stepper(E, make(params)), start = 1_000_000 + rand(1000)
    let st = g.init(ps)
    const sent: string[] = []
    for (let d = 0; d < (opts.depth ?? 12); d++) {
      const before = r.decode(st) as Record<string, number | boolean>
      if (before.done) break
      const took = rand(4) === 0 ? rand(2000) : rand(20), raw = opts.input ? {rule: {}, effect: opts.input(rand)} : drawInput(s, rand)
      // (Effect decides at the rule's time: the run's attempts taking what the rule's times leave, a jittered delay's
      // fraction of a millisecond among them)
      const now = d === 0 ? 0 : Number(before.elapsed) + Number(before.delay) + took
      const input: Record<string, unknown> = {took, ...raw.rule}
      // Each jitter: the delay it jitters (the rule run once with it at 0), then one it may take, and Effect's random.
      const randoms: number[] = []
      for (const j of s.jitters) {
        const probe = free.step(ps, st, r.encodeInput({...Object.fromEntries(s.jitters.map(k => [k.name, 0])), ...input}))
        const seen = r.decode(probe) as Record<string, number | boolean>
        if (!seen[j.on]) { input[j.name] = 0; continue }
        const base = Number(seen[j.base]), lo = Math.ceil(base * j.lo[0] / j.lo[1]), hi = Math.ceil(base * j.hi[0] / j.hi[1]) - 1
        const pick = base === 0 ? 0 : hi < lo ? lo : lo + rand(hi - lo + 1)
        input[j.name] = pick
        randoms.push(base === 0 ? 0 : (pick - base * j.lo[0] / j.lo[1]) / (base * (j.hi[0] / j.hi[1] - j.lo[0] / j.lo[1])))
      }
      sent.push(JSON.stringify(input))
      const at = `${Object.keys(params).length ? `with ${JSON.stringify(params)}, ` : ''}after ${sent.join(', ')}`
      let x: {cont: boolean, delay: number}
      try { x = decide(start + now, raw.effect, randoms) } catch (e) { return {checked, failure: `${at}: Effect's schedule fails (${(e as Error).message})`} }
      st = g.step(ps, st, r.encodeInput(input))
      const after = r.decode(st) as Record<string, number | boolean>
      if (Boolean(after.done) === x.cont) return {checked, failure: `${at}: Effect's schedule ${x.cont ? `goes on after ${x.delay} ms` : 'stops'}, the rule ${after.done ? 'stops' : `goes on after ${after.delay} ms`}`}
      if (x.cont && Math.abs(Number(after.delay) - x.delay) > 1e-6) return {checked, failure: `${at}: Effect's schedule waits ${x.delay} ms, the rule ${after.delay} ms`}
      checked++
    }
  }
  return {checked}
}
// A run of the rule (a refutation's) replayed on Effect's own schedule: each decision at the rule's time, each jitter
// answered so Effect draws the run's delay. ok where Effect decides as the rule did at every step.
export function replaySchedule(s: ScheduleRule, schedule: unknown, E: Any, run: {params: Record<string, number>, trace: Record<string, unknown>[]}): {ok: boolean, what: string} {
  const r = s.rule as Any, g = r.compiled(), free = interpret({...r.machine, assume: undefined}), ps = r.encodeParams(run.params), decide = stepper(E, schedule)
  let st = g.init(ps)
  const said: string[] = []
  for (const req of run.trace) {
    const before = r.decode(st) as Record<string, number | boolean>
    const now = Number(before.attempt) === 0 ? 0 : Number(before.elapsed) + Number(before.delay) + Number(req.took ?? 0)
    const randoms: number[] = []
    for (const j of s.jitters) {
      const seen = r.decode(free.step(ps, st, req)) as Record<string, number | boolean>
      if (!seen[j.on]) continue
      const base = Number(seen[j.base]), pick = Number(req[j.name] ?? 0)
      randoms.push(base === 0 ? 0 : Math.min(1 - 1e-12, Math.max(0, (pick - base * j.lo[0] / j.lo[1]) / (base * (j.hi[0] / j.hi[1] - j.lo[0] / j.lo[1])))))
    }
    const x = decide(1_000_000 + now, effectInput(s, req), randoms)
    st = g.step(ps, st, req)
    const after = r.decode(st) as Record<string, number | boolean>
    said.push(x.cont ? `goes on after ${+x.delay.toFixed(6)} ms` : 'stops')
    if (Boolean(after.done) === x.cont || (x.cont && Math.abs(Number(after.delay) - x.delay) > 1e-6)) return {ok: false, what: `Effect's schedule ${said.join(', ')}; the rule ${after.done ? 'stops' : `goes on after ${after.delay} ms`}`}
  }
  return {ok: true, what: `Effect's schedule, decision by decision: ${said.join(', ')}`}
}
// What Effect is fed for a request's input fields (decoded): the value, or an object of the fields read.
function effectInput(s: ScheduleRule, req: Record<string, unknown>): unknown {
  const vals: Record<string, unknown> = {}
  for (const [f, k] of s.fields) { const name = f === '_tag' ? 'input__tag' : f === 'input' ? 'input' : `input_${f}`; if (name in req) vals[f] = (k as Any).decode(name, req) }
  return 'input' in vals ? vals.input : vals
}
// A run of the rule where each jitter takes the edge of its range (its top, or its bottom), the attempts taking no time:
// the run a law about the jittered delay is broken by, where a random draw rarely lands (a jitter's range moves with the
// delay it jitters). The first state that breaks `law` ends it; undefined where none within `depth` decisions does.
export function jitterRun(s: ScheduleRule, law: Law, depth = 40, params: Record<string, number> = {}): {params: Record<string, number>, trace: Record<string, unknown>[]} | undefined {
  const r = s.rule as Any, m = r.machine, run = interpret(m), free = interpret({...m, assume: undefined}), ps = r.encodeParams(params)
  for (const edge of ['top', 'bottom'] as const) {
    let st = run.init(ps)
    const trace: Record<string, unknown>[] = []
    for (let d = 0; d < depth; d++) {
      const req: Record<string, unknown> = {took: 0, ...Object.fromEntries([...m.inputs].filter((i: string) => i !== 'took').map((i: string) => [i, 0]))}
      for (const j of s.jitters) {
        const seen = r.decode(free.step(ps, st, req)) as Record<string, number | boolean>, base = Number(seen[j.base])
        req[j.name] = !seen[j.on] || base === 0 ? 0 : edge === 'top' ? Math.ceil(base * j.hi[0] / j.hi[1]) - 1 : Math.ceil(base * j.lo[0] / j.lo[1])
      }
      try { st = run.step(ps, st, req) } catch { break }
      trace.push(req)
      if (!evalC(law.holds, {...ps}, st, m)) return {params, trace}
      if ((r.decode(st) as Record<string, unknown>).done) break
    }
  }
  return undefined
}
// An input of the schedule drawn from its kinds: the rule's values and what Effect is given (an object of its fields, a
// tagged error's _tag among them, or the value itself).
function drawInput(s: ScheduleRule, rand: Rand): {rule: Record<string, unknown>, effect: unknown} {
  const vals: Record<string, unknown> = {}, rule: Record<string, unknown> = {}
  for (const [f, k] of s.fields) {
    const v = (k as Any).sample(rand, 3)
    vals[f] = v; rule[f === '_tag' ? 'input__tag' : f === 'input' ? 'input' : `input_${f}`] = v
  }
  return {rule, effect: 'input' in vals ? vals.input : vals}
}

// What a refusal says when the source has no schedule where the reader looks.
export const notSchedule = (at: ts.Node) => new Refusal(at.getSourceFile().fileName, 'not a schedule')
export {Parts}
