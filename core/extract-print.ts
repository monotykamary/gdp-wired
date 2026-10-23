// From a Model (core/extract-shapes.ts) to a rule's source: which numbers are naturals, and the builder calls that make
// the rule, as text a user can read and keep. The rule core/extract.ts hands out is this text evaluated, so the source
// and the rule checked against the code are the same thing.
//
// Numbers: a variable is a natural where the code keeps it one: a param or input the code refuses below 0 (or given
// as one), a state variable that starts at 0 or more and is never written below (each subtraction proven at most what it
// subtracts from, by the library's own linear arithmetic, solver.ts, under the branch's conditions and the code's
// refusals); every other is an integer (two naturals, Int). A natural's a − b is printed as `a.minus(b)` (truncated)
// only where a ≥ b is proven, so it is the code's own subtraction.
import * as I from './extract-ir.ts'
import type {B, K, L, N} from './extract-ir.ts'
import type {MapDecl, Model, Term, Var} from './extract-read.ts'
import {Refusal} from './extract-read.ts'
import {type Constraint, type Lin, add, k as lk, le, lt, scale, solve, v as lv} from './solver.ts'

export type Sorts = Map<string, 'nat' | 'int'>
type Ctx = {m: Model, sorts: Sorts, atoms: B[]}

// --- naturals, by the solver ----------------------------------------------------------------------------------------
type Case = {lin: Lin, cons: Constraint[]}
const MAX_CASES = 64
let atomIds = 0
const atomNames = new Map<string, string>()
const atom = (x: object, prefix: string): string => {
  const key = I.keyOf(x)
  let n = atomNames.get(key)
  if (!n) { n = `${prefix}$${++atomIds}`; atomNames.set(key, n) }
  return n
}
function cases(e: N, ctx: Ctx): Case[] | undefined {
  const cross = (xs: Case[] | undefined, ys: Case[] | undefined, f: (a: Lin, b: Lin) => Lin, extra: (a: Lin, b: Lin) => Constraint[] = () => []): Case[] | undefined => {
    if (!xs || !ys || xs.length * ys.length > MAX_CASES) return undefined
    return xs.flatMap(a => ys.map(b => ({lin: f(a.lin, b.lin), cons: [...a.cons, ...b.cons, ...extra(a.lin, b.lin)]})))
  }
  switch (e.op) {
    case 'var': return [{lin: lv(e.name), cons: ctx.sorts.get(e.name) === 'nat' ? le(lk(0), lv(e.name)) : []}]
    case 'const': return [{lin: lk(e.v), cons: []}]
    case 'add': return cross(cases(e.a, ctx), cases(e.b, ctx), add)
    case 'sub': return cross(cases(e.a, ctx), cases(e.b, ctx), (a, b) => add(a, scale(b, -1)))
    case 'neg': return cases(e.a, ctx)?.map(c => ({lin: scale(c.lin, -1), cons: c.cons}))
    case 'mulk': return cases(e.a, ctx)?.map(c => ({lin: scale(c.lin, e.k), cons: c.cons}))
    case 'min': case 'max': {
      const lo = e.op === 'min'
      const a = cross(cases(e.a, ctx), cases(e.b, ctx), x => x, (x, y) => (lo ? le(x, y) : le(y, x)))
      const b = cross(cases(e.a, ctx), cases(e.b, ctx), (_, y) => y, (x, y) => (lo ? lt(y, x) : lt(x, y)))
      return a && b && a.length + b.length <= MAX_CASES ? [...a, ...b] : undefined
    }
    case 'ite': {
      const ca = cases(e.a, ctx), cb = cases(e.b, ctx), pc = linCond(e.c, ctx), nc = linCond(I.not(e.c), ctx)
      if (!ca || !cb || ca.length + cb.length > MAX_CASES) return undefined
      return [...ca.map(c => ({lin: c.lin, cons: [...c.cons, ...pc]})), ...cb.map(c => ({lin: c.lin, cons: [...c.cons, ...nc]}))]
    }
    case 'divk': {
      const t = atom(e, 'div')
      return cases(e.a, ctx)?.map(c => ({lin: lv(t), cons: [...c.cons, ...le(scale(lv(t), e.k), c.lin), ...le(c.lin, add(scale(lv(t), e.k), lk(e.k - 1)))]}))
    }
    case 'modk': { const t = atom(e, 'mod'); return [{lin: lv(t), cons: [...le(lk(0), lv(t)), ...le(lv(t), lk(e.k - 1))]}] }
    case 'mul': { const t = atom(e, 'mul'); return [{lin: lv(t), cons: natOK(e.a, ctx) && natOK(e.b, ctx) ? le(lk(0), lv(t)) : []}] }
    case 'cell': { const t = atom(e, 'cell'); return [{lin: lv(t), cons: ctx.sorts.get(`${e.map}.${e.field}`) === 'nat' ? le(lk(0), lv(t)) : []}] }
  }
}
// A condition's linear facts (none where it isn't a conjunction of comparisons of single cases).
function linCond(c: B, ctx: Ctx): Constraint[] {
  if (c.op === 'and') return c.xs.flatMap(x => linCond(x, ctx))
  if (c.op === 'not' && c.x.op === 'or') return c.x.xs.flatMap(x => linCond(I.not(x), ctx))
  if (c.op === 'not' && c.x.op === 'not') return linCond(c.x.x, ctx)
  if (c.op === 'cmp' || (c.op === 'not' && c.x.op === 'cmp')) {
    const x = c.op === 'cmp' ? c : (c.x as Extract<B, {op: 'cmp'}>), neg = c.op === 'not'
    const a = cases(x.a, ctx), b = cases(x.b, ctx)
    if (!a || !b || a.length !== 1 || b.length !== 1) return []
    const [p, q] = [a[0]!, b[0]!], base = [...p.cons, ...q.cons]
    if (!neg) return [...base, ...(x.rel === '<' ? lt(p.lin, q.lin) : x.rel === '<=' ? le(p.lin, q.lin) : [...le(p.lin, q.lin), ...le(q.lin, p.lin)])]
    if (x.rel === '<') return [...base, ...le(q.lin, p.lin)]
    if (x.rel === '<=') return [...base, ...lt(q.lin, p.lin)]
    return base
  }
  return []
}
// The facts at a place: the branch's conditions, and what the code's refusals rule out there (a refusal whose other
// conditions all hold here can't hold, or the step would be refused).
function factsAt(ctx: Ctx): Constraint[] {
  const out = ctx.atoms.flatMap(a => linCond(a, ctx))
  const known = (x: B) => ctx.atoms.some(a => I.same(a, x) || (a.op === 'and' && a.xs.some(y => I.same(y, x))))
  const refusals = ctx.m.refuse.op === 'or' ? ctx.m.refuse.xs : [ctx.m.refuse]
  for (const r of refusals) {
    const parts = r.op === 'and' ? r.xs : [r], open = parts.filter(x => !known(x))
    if (open.length === 1) out.push(...linCond(I.not(open[0]!), ctx))
  }
  out.push(...linCond(ctx.m.pre, ctx))
  return out
}
const refutes = (cons: Constraint[]) => solve(cons).kind === 'refuted'
// A term linear over atoms: each part that isn't linear (min, max, by cases, a division, a product, a map's cell) one
// atom by its structure, so a fact about a part and the term that reads it name the same atom.
function atomic(e: N, ctx: Ctx, side: Constraint[]): Lin {
  switch (e.op) {
    case 'var': if (ctx.sorts.get(e.name) === 'nat') side.push(...le(lk(0), lv(e.name))); return lv(e.name)
    case 'const': return lk(e.v)
    case 'add': return add(atomic(e.a, ctx, side), atomic(e.b, ctx, side))
    case 'sub': return add(atomic(e.a, ctx, side), scale(atomic(e.b, ctx, side), -1))
    case 'neg': return scale(atomic(e.a, ctx, side), -1)
    case 'mulk': return scale(atomic(e.a, ctx, side), e.k)
    case 'min': case 'max': case 'ite': case 'divk': case 'modk': case 'mul': case 'cell': {
      const t = atom(e, 'atom')
      if (natOK(e, {...ctx, atoms: []})) side.push(...le(lk(0), lv(t)))
      return lv(t)
    }
  }
}
function atomicCond(c: B, ctx: Ctx, side: Constraint[]): Constraint[] {
  if (c.op === 'and') return c.xs.flatMap(x => atomicCond(x, ctx, side))
  if (c.op === 'not' && c.x.op === 'or') return c.x.xs.flatMap(x => atomicCond(I.not(x), ctx, side))
  if (c.op === 'not' && c.x.op === 'not') return atomicCond(c.x.x, ctx, side)
  const x = c.op === 'cmp' ? c : c.op === 'not' && c.x.op === 'cmp' ? c.x : undefined
  if (!x) return []
  const a = atomic(x.a, ctx, side), b = atomic(x.b, ctx, side)
  if (c.op === 'cmp') return x.rel === '<' ? lt(a, b) : x.rel === '<=' ? le(a, b) : [...le(a, b), ...le(b, a)]
  return x.rel === '<' ? le(b, a) : x.rel === '<=' ? lt(b, a) : []
}
function atomicFacts(ctx: Ctx, side: Constraint[]): Constraint[] {
  const out = ctx.atoms.flatMap(a => atomicCond(a, ctx, side))
  const known = (x: B) => ctx.atoms.some(a => I.same(a, x) || (a.op === 'and' && a.xs.some(y => I.same(y, x))))
  for (const r of ctx.m.refuse.op === 'or' ? ctx.m.refuse.xs : [ctx.m.refuse]) {
    const parts = r.op === 'and' ? r.xs : [r], open = parts.filter(x => !known(x))
    if (open.length === 1) out.push(...atomicCond(I.not(open[0]!), ctx, side))
  }
  out.push(...atomicCond(ctx.m.pre, ctx, side))
  return out
}
export function nonneg(e: N, ctx: Ctx): boolean {
  const side: Constraint[] = [], lin = atomic(e, ctx, side), afacts = atomicFacts(ctx, side)
  if (refutes([...side, ...afacts, ...lt(lin, lk(0))])) return true
  const cs = cases(e, ctx)
  if (!cs) return false
  const facts = factsAt(ctx)
  return cs.every(c => refutes([...facts, ...c.cons, ...lt(c.lin, lk(0))]))
}
const withAtom = (ctx: Ctx, c: B): Ctx => ({...ctx, atoms: [...ctx.atoms, c]})
// A condition the place is already under (or under its negation): the branch it takes.
export const decided = (c: B, ctx: Ctx): boolean | undefined => (ctx.atoms.some(a => I.same(a, c)) ? true : ctx.atoms.some(a => I.same(a, I.not(c)) || I.same(I.not(a), c)) ? false : undefined)
// Whether a term is a natural at this place, every part of it too (so it prints over naturals).
export function natOK(e: N, ctx: Ctx): boolean {
  switch (e.op) {
    case 'var': return ctx.sorts.get(e.name) === 'nat'
    case 'const': return e.v >= 0
    case 'add': case 'mul': case 'min': return natOK(e.a, ctx) && natOK(e.b, ctx)
    case 'max': return natOK(e.a, ctx) || natOK(e.b, ctx)
    case 'sub': return natOK(e.a, ctx) && natOK(e.b, ctx) && nonneg(e, ctx)
    case 'neg': return false
    case 'mulk': return e.k >= 0 && natOK(e.a, ctx)
    case 'divk': return natOK(e.a, ctx)
    case 'modk': return true
    case 'ite': { const d = decided(e.c, ctx); if (d !== undefined) return natOK(d ? e.a : e.b, ctx); return natOK(e.a, withAtom(ctx, e.c)) && natOK(e.b, withAtom(ctx, I.not(e.c))) }
    case 'cell': return ctx.sorts.get(`${e.map}.${e.field}`) === 'nat'
  }
}

// Every number's sort: given ones kept; a param or input a natural if the code refuses it below 0, the time a natural;
// a state variable or a map's numbers naturals until a start or a write may be below 0.
export function sortsOf(m: Model, given: Record<string, 'nat' | 'int'> = {}): {sorts: Sorts, notes: string[]} {
  const sorts: Sorts = new Map(), notes: string[] = []
  const nums = (vs: Var[]) => vs.filter(v => v.sort.k === 'num')
  const ctx0 = (): Ctx => ({m, sorts, atoms: []})
  for (const v of [...nums(m.params), ...nums(m.inputs)]) {
    if (given[v.name]) { sorts.set(v.name, given[v.name]!); notes.push(`${v.name}: ${given[v.name] === 'nat' ? 'a natural' : 'an integer'}, as given`); continue }
    if (/^now(0)?(_\d+)?$/.test(v.name) && v.note?.startsWith('Date.now()')) { sorts.set(v.name, 'nat'); continue }
    // Refused below 0: no case of the step (or no params, for a param) takes it negative.
    const facts = v.role === 'param' ? linCond(m.pre, ctx0()) : []
    const refused = v.role === 'param' ? refutes([...facts, ...lt(lv(v.name), lk(0))]) : refusedBelowZero(m, v.name, ctx0())
    sorts.set(v.name, refused ? 'nat' : 'int')
    notes.push(refused ? `${v.name}: a natural (the code refuses it below 0)` : `${v.name}: an integer (the code takes any whole number)`)
  }
  const cellNums = m.maps.flatMap(d => d.fields.filter(f => f.sort.k === 'num').map(f => `${d.name}.${f.name}`))
  for (const v of nums(m.state)) sorts.set(v.name, given[v.name] ?? 'nat')
  for (const c of cellNums) sorts.set(c, given[c] ?? 'nat')
  for (let changed = true; changed;) {
    changed = false
    for (const v of nums(m.state)) {
      if (sorts.get(v.name) === 'int' || given[v.name]) continue
      const init = m.init[v.name], w = m.writes[v.name]
      if ((init && init.s === 'num' && !natOK(init.e, ctx0())) || (w && w.s === 'num' && !natOK(w.e, ctx0()))) { sorts.set(v.name, 'int'); changed = true }
    }
    for (const d of m.maps) for (const f of d.fields) {
      const n = `${d.name}.${f.name}`, w = m.mapWrites[d.name]?.vals[f.name]
      if (f.sort.k !== 'num' || sorts.get(n) === 'int' || given[n]) continue
      if (w && w.s === 'num' && !natOK(w.e, withAtom(ctx0(), m.mapWrites[d.name]!.has))) { sorts.set(n, 'int'); changed = true }
    }
  }
  for (const v of nums(m.state)) if (sorts.get(v.name) === 'int') notes.push(`${v.name}: an integer (a step may take it below 0, or it starts there)`)
  return {sorts, notes}
}
// x < 0 refused: for every event whose request brings x, a refusal of that event (its other conditions only the event's
// choice) whose condition holds wherever x < 0. So no step the rule takes reads a negative x.
function refusedBelowZero(m: Model, x: string, ctx: Ctx): boolean {
  const ds = m.refuse.op === 'or' ? m.refuse.xs : [m.refuse]
  const mentions = (a: import('./extract-read.ts').Arg): boolean => (a.k === 'input' ? a.name === x : a.k === 'rec' ? a.fields.some(([, y]) => mentions(y)) : false)
  const events = m.events.filter(e => e.args.some(mentions))
  if (!events.length) return false
  return events.every(e => ds.some(d => {
    const parts = d.op === 'and' ? d.xs : [d]
    const sel = parts.filter(p => p.op === 'is' && p.l.op === 'var'), own = parts.filter(p => !sel.includes(p))
    if (!sel.every(p => p.op === 'is' && p.l.op === 'var' && e.select[p.l.name] === p.value) || own.length !== 1) return false
    return refutes([...linCond(I.not(own[0]!), ctx), ...lt(lv(x), lk(0))])
  }))
}

// --- printing -------------------------------------------------------------------------------------------------------
export type Printer = {sorts: Sorts, m: Model, hoisted: Map<string, string>, choiceVars: Map<string, string>}
const q = (s: string) => `'${s.replace(/\\/g, '\\\\').replace(/'/g, "\\'")}'`
function pn(e: N, P: Printer, ctx: Ctx, mode: 'nat' | 'int', recv = false): string {
  const h = P.hoisted.get(I.keyOf(e))
  if (h) return mode === 'int' && recv && natOK(e, {...ctx, atoms: []}) ? `Int.of(${h})` : h
  const nat = mode === 'nat'
  const R = (x: N, c = ctx) => pn(x, P, c, nat ? 'nat' : 'int', true), A = (x: N, c = ctx) => pn(x, P, c, nat || natOK(x, c) ? 'nat' : 'int')
  switch (e.op) {
    case 'var': return !nat && recv && P.sorts.get(e.name) === 'nat' ? `Int.of(${e.name})` : e.name
    case 'const': return recv ? (nat ? `lit(${e.v})` : `Int.of(${e.v})`) : String(e.v)
    case 'add': return e.a.op === 'const' ? `${R(e.b)}.plus(${A(e.a)})` : `${R(e.a)}.plus(${A(e.b)})`
    case 'sub': return `${R(e.a)}.minus(${A(e.b)})`
    case 'neg': return `${pn(e.a, P, ctx, 'int', true)}.negate()`
    case 'mulk': return `${R(e.a)}.times(${e.k})`
    case 'mul':
      if (!(natOK(e.a, ctx) && natOK(e.b, ctx))) throw new Refusal(P.m.file, 'a product of two numbers that may be negative (Int multiplies only by constants)')
      return `${pn(e.a, P, ctx, 'nat', true)}.mul(${pn(e.b, P, ctx, 'nat')})`
    case 'min': return nat ? `min(${A(e.a)}, ${A(e.b)})` : `${R(e.a)}.min(${A(e.b)})`
    case 'max':
      if (nat) {
        const side = (x: N) => (natOK(x, ctx) ? pn(x, P, ctx, 'nat') : `${pn(x, P, ctx, 'int', true)}.clamped`)
        // max(0, x) is x where x is at least 0: Int's clamped.
        if (e.a.op === 'const' && e.a.v === 0) return side(e.b)
        if (e.b.op === 'const' && e.b.v === 0) return side(e.a)
        return `max(${side(e.a)}, ${side(e.b)})`
      }
      return `${R(e.a)}.max(${A(e.b)})`
    case 'divk': return `${R(e.a)}.divBy(${e.k})`
    case 'modk':
      // JavaScript's % takes the dividend's sign (-7 % 3 is -1); modBy is the remainder at least 0 (2): the same only
      // where the dividend is at least 0.
      if (!natOK(e.a, ctx) && !nonneg(e.a, ctx)) throw new Refusal(P.m.file, 'x % k where x may be negative (JavaScript\'s remainder takes the sign of x)')
      return `${pn(e.a, P, ctx, natOK(e.a, ctx) ? 'nat' : 'int', true)}.modBy(${e.k})`
    case 'ite': {
      const d = decided(e.c, ctx)
      if (d !== undefined) return pn(d ? e.a : e.b, P, ctx, mode, recv)
      const ca = withAtom(ctx, e.c), cb = withAtom(ctx, I.not(e.c))
      const side = (x: N, c: Ctx) => pn(x, P, c, nat ? 'nat' : natOK(x, c) ? 'nat' : 'int')
      return `when(${pb(e.c, P, ctx)}, ${side(e.a, ca)}, ${side(e.b, cb)})`
    }
    case 'cell': { const v = `${e.map}.at(${pk(e.key, P, ctx)}).${e.field}`; return !nat && recv && P.sorts.get(`${e.map}.${e.field}`) === 'nat' ? `Int.of(${v})` : v }
  }
}
// A number in its own mode at this place: a natural's terms where it is one, else Int's.
export const pnum = (e: N, P: Printer, ctx: Ctx, recv = false): string => pn(e, P, ctx, natOK(e, ctx) ? 'nat' : 'int', recv)
function pcmp(rel: '<' | '<=' | '=', a: N, b: N, P: Printer, ctx: Ctx): string {
  const op = rel === '<' ? 'lt' : rel === '<=' ? 'atMost' : 'eq', flip = rel === '<' ? 'gt' : rel === '<=' ? 'atLeast' : 'eq'
  const nat = natOK(a, ctx) && natOK(b, ctx)
  const [x, y, o] = a.op === 'const' && b.op !== 'const' ? [b, a, flip] : [a, b, op]
  return `${pn(x, P, ctx, nat ? 'nat' : 'int', true)}.${o}(${pn(y, P, ctx, nat || natOK(y, ctx) ? 'nat' : 'int')})`
}
export function pb(c: B, P: Printer, ctx: Ctx): string {
  const h = P.hoisted.get(I.keyOf(c))
  if (h) return h
  switch (c.op) {
    case 'const': return c.v ? 'yes' : 'no'
    case 'var': return c.name
    case 'cmp': return pcmp(c.rel, c.a, c.b, P, ctx)
    case 'and': return `all(${c.xs.map(x => pb(x, P, ctx)).join(', ')})`
    case 'or': return `any(${c.xs.map(x => pb(x, P, ctx)).join(', ')})`
    case 'not':
      if (c.x.op === 'cmp') {
        const {rel, a, b} = c.x
        return rel === '<' ? pcmp('<=', b, a, P, ctx) : rel === '<=' ? pcmp('<', b, a, P, ctx) : `${pcmp('=', a, b, P, ctx)}.not()`
      }
      if (c.x.op === 'and' && c.x.xs.length === 2) return `${pb(c.x.xs[0]!, P, ctx)}.implies(${pb(I.not(c.x.xs[1]!), P, ctx)})`
      if (c.x.op === 'or') return `all(${c.x.xs.map(x => pb(I.not(x), P, ctx)).join(', ')})`
      return `not(${pb(c.x, P, ctx)})`
    case 'ite': { const d = decided(c.c, ctx); if (d !== undefined) return pb(d ? c.a : c.b, P, ctx); return `when(${pb(c.c, P, ctx)}, ${pb(c.a, P, withAtom(ctx, c.c))}, ${pb(c.b, P, withAtom(ctx, I.not(c.c)))})` }
    case 'is': return `${pl(c.l, P, ctx)}.is(${q(c.value)})`
    case 'leq': return `${pl(c.a, P, ctx)}.eq(${pl(c.b, P, ctx)})`
    case 'keq': {
      const s = (k: K) => (k.op === 'svar' ? k.name : k.op === 'slit' ? q(k.value) : pk(k, P, ctx))
      return c.a.op === 'svar' ? `${c.a.name}.eq(${s(c.b)})` : c.b.op === 'svar' ? `${c.b.name}.eq(${s(c.a)})` : `${pk(c.a, P, ctx)}.eq(${pk(c.b, P, ctx)})`
    }
    case 'cell': return `${c.map}.at(${pk(c.key, P, ctx)}).${c.field}`
  }
}
// A choice: a literal is written as the choice's own value where nothing else gives the choice (`status.of('open')`).
export function pl(l: L, P: Printer, ctx: Ctx, bare = false): string {
  switch (l.op) {
    case 'var': return l.name
    case 'lit': {
      if (bare) return q(l.value)
      const w = P.choiceVars.get(l.values.join('\u0000'))
      if (!w) throw new Refusal(P.m.file, `a choice among ${l.values.join(', ')} with no variable of its own to name it by`)
      return `${w}.of(${q(l.value)})`
    }
    case 'ite': return `when(${pb(l.c, P, ctx)}, ${pl(l.a, P, ctx, l.b.op !== 'lit')}, ${pl(l.b, P, ctx, l.a.op !== 'lit' || l.b.op !== 'lit' ? l.a.op !== 'lit' : false)})`
    case 'cell': return `${l.map}.at(${pk(l.key, P, ctx)}).${l.field}`
  }
}
export function pk(k: K, P: Printer, ctx: Ctx): string {
  switch (k.op) {
    case 'num':
      if (!natOK(k.e, ctx)) throw new Refusal(P.m.file, 'a map key that may be negative (a rule\'s map is keyed by naturals)')
      return pn(k.e, P, ctx, 'nat')
    case 'svar': return `${k.name}.id`
    case 'slit': return `intern(${q(k.value)})`
    case 'kite': return `when(${pb(k.c, P, ctx)}, ${pk(k.a, P, ctx)}, ${pk(k.b, P, ctx)})`
  }
}
export function pterm(t: Term, P: Printer, ctx: Ctx, target?: string): string {
  if (t.s === 'num') return target && P.sorts.get(target) === 'nat' ? pn(t.e, P, ctx, 'nat') : target ? pn(t.e, P, ctx, 'int') : pnum(t.e, P, ctx)
  if (t.s === 'bool') return pb(t.e, P, ctx)
  if (t.s === 'str') return pstr(t.e, P, ctx, true)
  return pl(t.e, P, ctx, true)
}
// A string: a variable (a Str), a literal written whole, or one of two Strs by a condition.
function pstr(k: K, P: Printer, ctx: Ctx, top = false): string {
  if (k.op === 'svar') return k.name
  if (k.op === 'slit') { if (top) return q(k.value); throw new Refusal(P.m.file, `the literal '${k.value}' chosen by a condition (a string by cases is of two strings the rule holds)`) }
  if (k.op === 'kite') {
    const d = decided(k.c, ctx)
    if (d !== undefined) return pstr(d ? k.a : k.b, P, ctx, top)
    // A literal beside a string value is written as itself (when reads it as that string); two literals have none.
    const lits = (k.a.op === 'slit' ? 1 : 0) + (k.b.op === 'slit' ? 1 : 0)
    return `when(${pb(k.c, P, ctx)}, ${pstr(k.a, P, withAtom(ctx, k.c), lits < 2)}, ${pstr(k.b, P, withAtom(ctx, I.not(k.c)), lits < 2)})`
  }
  throw new Refusal(P.m.file, 'a number where a string is written')
}

// The kind of a variable, as the builders declare it.
export const kindOf = (v: Var, sorts: Sorts, at = v.name): string => {
  switch (v.sort.k) {
    case 'num': return sorts.get(at) === 'nat' ? 'nat' : 'int'
    case 'bool': return 'bool'
    case 'choice': return `oneOf(${v.sort.values.map(q).join(', ')})`
    case 'str': return 'str()'
  }
}
export const mapKind = (d: MapDecl, sorts: Sorts): string => `record({has: bool, ${d.fields.map(f => `${f.name}: ${kindOf(f, sorts, `${d.name}.${f.name}`)}`).join(', ')}})`
export const mapEmpty = (d: MapDecl): string => `{has: false, ${d.fields.map(f => `${f.name}: ${f.sort.k === 'num' ? '0' : f.sort.k === 'bool' ? 'false' : f.sort.k === 'choice' ? q(f.sort.values[0]!) : "''"}`).join(', ')}}`
export type {Ctx}
