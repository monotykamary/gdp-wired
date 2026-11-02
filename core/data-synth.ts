// Search only: invented folds are ordinary definitions; these equations are conjectures, never facts.
// The caller proves every one with the cyclic kernel before using it, and exports the folds with its proof.
import {Data, type DataLaw, type Fn, type Program, type Sort, type X, type Y, define, evalY, fnNamed, reduceX, samples, showY, wrap} from './data.ts'

const same = (a: unknown, b: unknown) => JSON.stringify(a) === JSON.stringify(b)
const variable = (name: string): X => ({op: 'var', name})
const walk = (t: unknown, f: (x: Record<string, unknown>) => void): void => {
  if (!t || typeof t !== 'object') return
  if (Array.isArray(t)) { t.forEach(x => walk(x, f)); return }
  f(t as Record<string, unknown>); Object.values(t).forEach(x => walk(x, f))
}
const replace = <T>(t: T, f: (x: X) => X | undefined): T => {
  const go = (x: unknown): unknown => {
    if (!x || typeof x !== 'object') return x
    if (Array.isArray(x)) return x.map(go)
    const changed = f(x as X)
    return changed ?? Object.fromEntries(Object.entries(x).map(([k, v]) => [k, go(v)]))
  }
  return go(t) as T
}
const substitute = <T>(t: T, sub: Map<string, X>): T => replace(t, x => x.op === 'var' ? sub.get(x.name) : undefined)
const free = (t: unknown) => { const out = new Set<string>(); walk(t, x => { if (x.op === 'var') out.add(x.name as string) }); return out }
const fieldSort = (p: Program, s: string | {data: string}): Sort => typeof s === 'string' ? s as Sort : p.datas.find(d => d.name === s.data)!
type Algebra = {observer: Fn, data: Data, at: number, payload: Sort, item: string, weight: X}
const zero = (f: Fn): X => f.ret === 'int' ? {op: 'int', value: 0} : {op: 'nat', value: 0}
const plus = (f: Fn, a: X, b: X): X => a.op === zero(f).op && 'value' in a && a.value === 0 ? b : b.op === zero(f).op && 'value' in b && b.value === 0 ? a : {op: f.ret === 'int' ? 'iadd' : 'add', a, b}
const sum = (f: Fn, xs: X[]) => xs.reduce((a, b) => plus(f, a, b), zero(f))

// Recognise an additive list algebra, including a guard around the recursive call (count), not just length.
// No equation is assumed from this recognition: a wrong guess can only leave its subsequent lemma unproved.
function algebra(p: Program, f: Fn): Algebra | undefined {
  if ((f.ret !== 'nat' && f.ret !== 'int') || f.params.some(q => q.sort === 'bool')) return
  const body = f.body()
  if (body.op !== 'match' || body.of.op !== 'var') return
  const at = f.params.findIndex(q => `${f.name}.${q.name}` === (body.of as {name: string}).name)
  const d = f.params[at]?.sort
  if (!(d instanceof Data) || d.abstract || d.ctors.length !== 2) return
  const ci = d.ctors.findIndex(c => c.fields.length === 2 && c.fields.filter(q => typeof q.sort === 'object' && q.sort.data === d.name).length === 1)
  if (ci < 0) return
  const ctor = d.ctors[ci]!, branch = body.cases[ci]!, ri = ctor.fields.findIndex(q => typeof q.sort === 'object' && q.sort.data === d.name), vi = 1 - ri
  if (!body.cases.every((c, i) => i === ci || same(reduceX(c.body), zero(f)))) return
  const recursive: X = {op: 'call', fn: f.name, args: f.params.map((q, i) => variable(i === at ? branch.binds[ri]! : `${f.name}.${q.name}`))}
  const weight = (x: X): {n: number, x: X} | undefined => {
    if (same(x, recursive)) return {n: 1, x: zero(f)}
    let calls = false; walk(x, t => { if (t.op === 'call' && t.fn === f.name) calls = true })
    if (!calls) return {n: 0, x}
    if (x.op === 'add' || x.op === 'iadd') { const a = weight(x.a), b = weight(x.b); return a && b ? {n: a.n + b.n, x: plus(f, a.x, b.x)} : undefined }
    if (x.op === 'if') { let inGuard = false; walk(x.c, t => { if (t.op === 'call' && t.fn === f.name) inGuard = true }); if (inGuard) return; const a = weight(x.then), b = weight(x.else); return a && b && a.n === b.n ? {n: a.n, x: {...x, then: a.x, else: b.x}} : undefined }
    return
  }
  const w = weight(branch.body)
  if (!w || w.n !== 1) return
  const allowed = new Set([branch.binds[vi]!, ...f.params.filter((_, i) => i !== at).map(q => `${f.name}.${q.name}`)])
  if ([...free(w.x)].some(v => !allowed.has(v))) return
  return {observer: f, data: d, at, payload: fieldSort(p, ctor.fields[vi]!.sort), item: branch.binds[vi]!, weight: w.x}
}

let serial = 0
const lifted = new WeakMap<Fn, Map<Data, Fn>>()
// Lift the same per-element weight over other container shapes, including a list of containers and mutual groups.
function lift(p: Program, a: Algebra): Map<Data, Fn> {
  const f = a.observer, out = new Map<Data, Fn>([[a.data, f]])
  const cache = lifted.get(f) ?? new Map<Data, Fn>(); lifted.set(f, cache)
  const contains = new Set<Data>([a.data])
  for (let changed = true; changed;) {
    changed = false
    for (const d of p.datas) if (!d.abstract && d !== a.payload && !contains.has(d) && d.ctors.some(c => c.fields.some(q => { const s = fieldSort(p, q.sort); return s === a.payload || s instanceof Data && contains.has(s) }))) { contains.add(d); changed = true }
  }
  for (const d of contains) if (d !== a.data) {
    const old = cache.get(d)
    if (old && fnNamed(old.name) === old) { out.set(d, old); continue }
    let name: string; do { name = `observer${++serial}` } while (fnNamed(name))
    const params = f.params.map((q, i) => ({name: `a${i}`, sort: i === a.at ? d : q.sort}))
    const made = define(name, Object.fromEntries(params.map(q => [q.name, q.sort])), f.ret, args => {
      const input = args[`a${a.at}`] as {x: X}
      const sub = new Map(f.params.map((q, i) => [`${f.name}.${q.name}`, (args[`a${i}`] as {x: X}).x]))
      const body: X = {op: 'match', data: d.name, of: input.x, cases: d.ctors.map(c => {
        const binds = c.fields.map((_, i) => `${name}field${i}`)
        const terms = c.fields.flatMap((q, i) => {
          const s = fieldSort(p, q.sort), v = variable(binds[i]!)
          if (s === a.payload) return [substitute(a.weight, new Map([...sub, [a.item, v]]))]
          const obs = s instanceof Data ? out.get(s) : undefined
          return obs ? [{op: 'call', fn: obs.name, args: params.map((_, j) => j === a.at ? v : (args[`a${j}`] as {x: X}).x)} as X] : []
        })
        return {binds, body: sum(f, terms)}
      })}
      return wrap(f.ret, body)
    }).fn
    out.set(d, made); cache.set(d, made)
  }
  return out
}

// Values filter conjectures, never certify them. Guarded candidates need witnesses on both sides of the guard.
function keep(l: DataLaw, guard?: Y): boolean {
  let yes = 0, no = 0
  const draws = samples(l.vars, l.params, 80, 19)
  // Independent RNG streams can miss equality guards. Also force scalar coincidences, with the
  // containers unchanged; these are adversarial samples, not assumptions of the proof.
  const scalars = l.vars.filter(v => v.sort === 'nat' || v.sort === 'int')
  const correlated = draws.flatMap(s => [0, 1, 2].map(n => ({...s, env: new Map([...s.env, ...scalars.map(v => [v.name, n] as const)])})))
  for (const s of [...draws, ...correlated]) {
    try { if (guard && !evalY(guard, s.env, s.params)) { no++; continue }; yes++; if (!evalY(l.holds, s.env, s.params)) return false } catch { return false }
  }
  return yes >= 8 && (!guard || no >= 8)
}
const families = new WeakMap<DataLaw, string>()
export const synthesizedObserver = (l: DataLaw): string | undefined => families.get(l)
export function synthesizedLemmas(p: Program): DataLaw[] {
  const out: DataLaw[] = [], seen = new Set<string>()
  let family = ''
  const emit = (vars: DataLaw['vars'], lhs: X, rhs: X, guard?: Y) => {
    if (same(lhs, rhs)) return
    const eq: Y = {op: '=', a: lhs, b: rhs}, holds: Y = guard ? {op: 'or', xs: [{op: 'not', x: guard}, eq]} : eq
    const text = JSON.stringify(holds)
    if (seen.has(text)) return
    seen.add(text)
    const names = free(holds), used = vars.filter(v => names.has(v.name))
    // All branch binders have been eliminated; no free symbol is silently omitted.
    if (names.size !== used.length) return
    const l: DataLaw = {name: showY(holds), vars: used, holds, params: [...p.params]}
    if (keep(l, guard)) { families.set(l, family); out.push(l) }
  }
  for (const f of p.fns) {
    const a = algebra(p, f)
    if (!a) continue
    family = f.name
    const observers = lift(p, a)
    for (const m of p.fns) {
      const observer = m.ret instanceof Data ? observers.get(m.ret) : undefined
      if (!observer || m === f || (m.decreases === undefined && !m.measure) || m.params.every(q => !(q.sort instanceof Data))) continue
      const vars = [...f.params.flatMap((q, i) => i === a.at ? [] : [{name: `o${i}`, sort: q.sort}]), ...m.params.map((q, i) => ({name: `v${i}`, sort: q.sort}))]
      const args = m.params.map((_, i) => variable(`v${i}`))
      const obsArgs = (value: X) => f.params.map((_, i) => i === a.at ? value : variable(`o${i}`))
      const observe = (of: Fn, value: X): X => ({op: 'call', fn: of.name, args: obsArgs(value)})
      const weights: X[] = [], parts: X[] = []
      const sub = new Map(f.params.map((q, i) => [`${f.name}.${q.name}`, variable(`o${i}`)]))
      for (const [i, q] of m.params.entries()) {
        const o = q.sort instanceof Data ? observers.get(q.sort) : undefined
        if (o) parts.push(observe(o, args[i]!))
        else if (q.sort === a.payload) weights.push(substitute(a.weight, new Map([...sub, [a.item, args[i]!]])))
      }
      if (!parts.length) continue
      const lhs = observe(observer, {op: 'call', fn: m.name, args}), rhs = sum(f, parts)
      emit(vars, lhs, sum(f, [...parts, ...weights]))
      if (weights.length) emit(vars, lhs, rhs)
      // Removing an element is additive only when its selection guard has a witness in the input.
      // Instantiate the observer's equality parameter with that element, then test its count is positive.
      for (const [wi, q] of m.params.entries()) if (q.sort === a.payload) for (const [pi, pq] of f.params.entries()) if (pi !== a.at && pq.sort === a.payload) for (const [di, dq] of m.params.entries()) if (dq.sort === a.data) {
        const count: X = {op: 'call', fn: f.name, args: obsArgs(args[di]!).map((v, i) => i === pi ? args[wi]! : v)}
        const guard: Y = {op: f.ret === 'int' ? 'i<' : '<', a: zero(f), b: count}
        emit(vars, sum(f, [lhs, ...weights]), rhs, guard)
        emit(vars, lhs, rhs, {op: 'not', x: guard})
      }
    }
    // A selector's result occurs in its input. This is the premise needed by a
    // guarded removal law (minimum-then-rest is one instance, not a named special case).
    const cons = a.data.ctors.findIndex(c => c.fields.length === 2 && c.fields.some(q => fieldSort(p, q.sort) === a.payload) && c.fields.some(q => fieldSort(p, q.sort) === a.data))
    if (cons < 0) continue
    for (const m of p.fns) {
      if (m === f || m.ret !== a.payload || m.decreases === undefined || m.params.filter(q => q.sort === a.data).length !== 1) continue
      const vars = m.params.map((q, i) => ({name: `s${i}`, sort: q.sort})), args = vars.map(v => variable(v.name))
      const result: X = {op: 'call', fn: m.name, args}
      let source = args[m.params.findIndex(q => q.sort === a.data)]!
      for (const [i, q] of m.params.entries()) if (q.sort === a.payload) source = {op: 'ctor', data: a.data.name, ctor: cons, args: a.data.ctors[cons]!.fields.map(q => fieldSort(p, q.sort) === a.payload ? args[i]! : source)}
      for (const [i, q] of f.params.entries()) {
        if (i === a.at || q.sort !== a.payload || f.params.length !== 2) continue
        const count: X = {op: 'call', fn: f.name, args: f.params.map((_, j) => j === a.at ? source : result)}
        const holds: Y = {op: f.ret === 'int' ? 'i<' : '<', a: zero(f), b: count}
        const l: DataLaw = {name: showY(holds), vars, holds, params: [...p.params]}
        if (keep(l)) { families.set(l, family); out.push(l) }
      }
    }
  }
  return out
}
