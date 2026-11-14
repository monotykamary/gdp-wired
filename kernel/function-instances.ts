// Opt-in UNTRUSTED search only. This module proposes ordinary Instances of
// existing guarded facts. It never adds a fact, proves a goal, or changes a rule.
import {argsKey, pairedArgs, type C, type E, type Law, type Machine} from '../core/machine.ts'
import {type Goal, type Instances} from './kernel.ts'
import {startWork} from '../core/work-admission.ts'

export type FunctionInstanceSpec = {
  sorts: Readonly<Record<string, string>>
  functions: Readonly<Record<string, {args: readonly string[], result?: string}>>
  maps?: Readonly<Record<string, {result: string, args?: readonly string[]}>>
  variables?: Readonly<Record<string, string>>
  limits?: {work?: number, candidates?: number, tuples?: number, depth?: number}
}
type Limits = {work: number, candidates: number, tuples: number, depth: number}
export type FunctionInstanceStats = {work: number, matched: number, generated: number, cyclic: boolean}
type Context = {spec: FunctionInstanceSpec, limits: Limits, stats: FunctionInstanceStats}
class Limited extends Error {}
let active: Context | undefined
const safeLimit = (n: number | undefined, fallback: number): number => {
  const value = n ?? fallback
  if (!Number.isSafeInteger(value) || value < 1) throw new Error('function-instantiation limits must be positive safe integers')
  return value
}
/** Synchronous, scoped, default OFF. Limits never become a successful partial
 * search: a cap returns not proven, and the previous context is always restored. */
export function withFunctionInstances<T>(source: FunctionInstanceSpec, run: () => T):
    {status: 'complete', value: T, stats: FunctionInstanceStats} |
    {status: 'limited', proven: false, checked: false, reason: string, stats: FunctionInstanceStats} {
  const spec = structuredClone(source), old = active
  const context: Context = {spec, limits: {work: safeLimit(spec.limits?.work, 500_000), candidates: safeLimit(spec.limits?.candidates, 32), tuples: safeLimit(spec.limits?.tuples, 256), depth: safeLimit(spec.limits?.depth, 4)}, stats: {work: 0, matched: 0, generated: 0, cyclic: false}}
  active = context
  try {
    for (const [sort, parameter] of Object.entries(spec.sorts)) if (!sort || typeof parameter !== 'string') throw new Error('invalid function-instantiation sort')
    for (const d of [...Object.values(spec.functions), ...Object.values(spec.maps ?? {})]) {
      if (d.result !== undefined && !(d.result in spec.sorts)) throw new Error('unknown result sort')
      if ('args' in d && d.args !== undefined && (!d.args.length || d.args.some(s => !(s in spec.sorts)))) throw new Error('unknown argument sort')
    }
    const value = run()
    if (value && typeof value === 'object' && 'then' in value) throw new Error('function-instantiation scope must be synchronous')
    return {status: 'complete', value, stats: {...context.stats}}
  } catch (error) {
    if (!(error instanceof Limited)) throw error
    return {status: 'limited', proven: false, checked: false, reason: error.message, stats: {...context.stats}}
  } finally { active = old }
}
const tick = (ctx: Context, n = 1): void => {
  if (n > ctx.limits.work - ctx.stats.work) throw new Limited('function-instantiation work limit')
  startWork('ticks', n, 'function fact instantiation')
  ctx.stats.work += n
}

type Read = {name: string, args: E[]}
type Fact = {law: Law, vars: string[], sorts: string[], patterns: Read[]}
type Candidate = {e: E, priority: number, depth: number}
type Binding = Map<string, E>

// Read exactly the already-supported argsKey encoding. Constant folding can
// erase its syntax; decode only canonical safe-natural constant images.
function callArgs(e: E, arity: number, ctx: Context): E[] | undefined {
  const direct = pairedArgs(e, arity)
  if (direct) return direct
  if (e.op !== 'const' || !Number.isSafeInteger(e.value) || e.value < 0) return undefined
  const out: E[] = []; let z = BigInt(e.value)
  for (let i = 1; i < arity; i++) {
    let lo = 0n, hi = z + 1n
    while (hi - lo > 1n) { tick(ctx); const mid = (lo + hi) / 2n; if (mid * mid <= z) lo = mid; else hi = mid }
    const b = z - lo * lo
    if (b > lo) return undefined
    out.unshift({op: 'const', value: Number(b)}); z = lo - b
  }
  out.unshift({op: 'const', value: Number(z)})
  return out
}
const children = (e: E): E[] => e.op === 'if' ? [e.then, e.else] : e.op === 'mul' || e.op === 'proj' ? [e.a] : e.op === 'get' ? [e.key] : 'a' in e ? [e.a, e.b] : []
function conditions(c: C, visitE: (e: E) => void, visitC?: (c: C) => void): void {
  visitC?.(c)
  if (c.op === 'all') return // no leaking locally bound variables
  if (c.op === 'and' || c.op === 'or') c.xs.forEach(x => conditions(x, visitE, visitC))
  else if (c.op === 'not') conditions(c.x, visitE, visitC)
  else if (c.op !== 'flag') { visitE(c.a); visitE(c.b) }
}
function factsOf(m: Machine, ctx: Context): Fact[] {
  const byParameter = new Map<string, string[]>()
  for (const [s, p] of Object.entries(ctx.spec.sorts)) byParameter.set(p, [...byParameter.get(p) ?? [], s])
  const facts: Fact[] = []
  for (const law of m.facts ?? []) {
    if (!law.forall || law.holds.op !== 'or' || law.holds.xs.length !== 2 || law.holds.xs[0]!.op !== 'not') continue
    tick(ctx)
    const guard = law.holds.xs[0]!.x, vars = [law.forall, ...law.keys ?? []], types = new Map<string, string>()
    conditions(guard, () => {}, c => {
      tick(ctx)
      if (c.op !== '<' || c.a.op !== 'var' || c.b.op !== 'var' || !vars.includes(c.a.name)) return
      const ss = byParameter.get(c.b.name)
      if (ss?.length === 1) types.set(c.a.name, ss[0]!)
    })
    if (vars.some(v => !types.has(v))) continue
    const patterns: Read[] = []
    const visit = (e: E): void => {
      tick(ctx)
      if (e.op === 'get') { const d = Object.hasOwn(ctx.spec.functions, e.map) ? ctx.spec.functions[e.map] : undefined, args = d && d.args.length === (m.fns?.[e.map]?.arity ?? 1) && callArgs(e.key, d.args.length, ctx); if (args) patterns.push({name: e.map, args}) }
      if (e.op === 'if') conditions(e.c, visit)
      children(e).forEach(visit)
    }
    conditions(law.holds, visit)
    if (patterns.length) facts.push({law, vars, sorts: vars.map(v => types.get(v)!), patterns})
  }
  return facts
}
/** An inactive/nonmatching machine takes the existing prover path untouched. */
export function hasFunctionInstances(m: Machine): boolean {
  return active !== undefined && !!m.facts?.some(f => f.forall && f.holds.op === 'or' && f.holds.xs[0]?.op === 'not') && Object.keys(active.spec.functions).some(name => Object.hasOwn(m.fns ?? {}, name))
}

export function extendFunctionInstances(m: Machine, input: Instances, goals: Goal[], legacy?: (machine: Machine, input: Instances, goals: Goal[]) => Instances): Instances {
  const ctx = active
  if (!ctx) return input
  const facts = factsOf(m, ctx)
  if (!facts.length) return legacy ? legacy(m, input, goals) : input
  const pools = new Map<string, Map<string, Candidate>>(Object.keys(ctx.spec.sorts).map(s => [s, new Map()]))
  const fingerprints = new WeakMap<object, string>(), identities = new Map<string, string>()
  const pack = (parts: (string | number)[]): string => {
    const chars = parts.reduce<number>((n, p) => n + (typeof p === 'string' ? p.length : 24), 0)
    tick(ctx, 1 + Math.ceil(chars / 32))
    return JSON.stringify(parts)
  }
  // Exact structural hash-consing, not recursive JSON-in-JSON strings (whose
  // escaping grows exponentially with depth). IDs are local deterministic
  // equality tokens, not hashes; distinct structures cannot collide.
  const intern = (parts: (string | number)[]): string => {
    const text = pack(parts), prior = identities.get(text)
    if (prior !== undefined) return prior
    const id = String(identities.size); identities.set(text, id); return id
  }
  const conditionKey = (c: C): string => {
    tick(ctx)
    const prior = fingerprints.get(c); if (prior !== undefined) return prior
    let id: string
    if (c.op === 'flag') id = intern(['C', c.op, c.name])
    else if (c.op === 'all') id = intern(['C', c.op, c.key, ...c.keys ?? [], c.finite ?? '', conditionKey(c.c)])
    else if (c.op === 'not') id = intern(['C', c.op, conditionKey(c.x)])
    else if (c.op === 'and' || c.op === 'or') id = intern(['C', c.op, ...c.xs.map(conditionKey)])
    else id = intern(['C', c.op, key(c.a), key(c.b)])
    fingerprints.set(c, id); return id
  }
  const key = (e: E): string => {
    tick(ctx)
    const prior = fingerprints.get(e); if (prior !== undefined) return prior
    const metadata = e.op === 'var' ? e.name : e.op === 'const' ? e.value : e.op === 'get' ? e.map : e.op === 'mul' || e.op === 'proj' ? e.k : ''
    const value = intern(['E', e.op, metadata, ...(e.op === 'if' ? [conditionKey(e.c)] : []), ...children(e).map(key)])
    fingerprints.set(e, value); return value
  }
  const add = (sort: string, e: E, priority: number, depth = 0): boolean => {
    const pool = pools.get(sort); if (!pool) return false
    const id = key(e), had = pool.get(id)
    if (had) { if (priority < had.priority) had.priority = priority; return false }
    if (pool.size >= ctx.limits.candidates) throw new Limited(`function-instantiation candidate limit for ${sort}`)
    tick(ctx); pool.set(id, {e, priority, depth}); return true
  }
  const reads: Read[] = []
  const variableSort = (name: string): string | undefined => {
    for (const n of [name, name.replace(/#$/, '')]) if (Object.hasOwn(ctx.spec.variables ?? {}, n)) return ctx.spec.variables![n]
    return undefined
  }
  // Nominal declaration metadata is a search filter, never a new hypothesis.
  // Legacy helpers can be instantiated at an entire encoded pair; do not feed
  // that pair back as an atomic-sort candidate and recursively amplify it.
  const compatible = (e: E, sort: string): boolean => {
    tick(ctx)
    if (e.op === 'var') { const s = variableSort(e.name); return s === undefined || s === sort }
    if (e.op === 'tup' || e.op !== 'const' && pairedArgs(e, 2)) return false
    if (e.op === 'if') return compatible(e.then, sort) && compatible(e.else, sort)
    if (e.op === 'get') {
      const fn = Object.hasOwn(ctx.spec.functions, e.map) ? ctx.spec.functions[e.map] : undefined
      const mp = ctx.spec.maps && Object.hasOwn(ctx.spec.maps, e.map) ? ctx.spec.maps[e.map] : undefined
      const d = fn ?? mp
      if (d?.result !== undefined && d.result !== sort) return false
      if (d?.args) { const xs = callArgs(e.key, d.args.length, ctx); if (!xs || !xs.every((x, i) => compatible(x, d.args![i]!))) return false }
    }
    return true
  }
  const seenExpressions = new Set<string>()
  const visit = (e: E): void => {
    tick(ctx)
    const id = key(e); if (seenExpressions.has(id)) return
    seenExpressions.add(id)
    if (e.op === 'var') { const s = variableSort(e.name); if (s) add(s, e, 1) }
    if (e.op === 'get') {
      const d = Object.hasOwn(ctx.spec.functions, e.map) ? ctx.spec.functions[e.map] : undefined
      if (d && Object.hasOwn(m.fns ?? {}, e.map) && d.args.length === (m.fns![e.map]!.arity ?? 1)) {
        const args = callArgs(e.key, d.args.length, ctx)
        if (args?.every((arg, i) => compatible(arg, d.args[i]!))) { reads.push({name: e.map, args}); args.forEach((arg, i) => add(d.args[i]!, arg, 0)); if (d.result) add(d.result, e, 1) }
      }
      const map = ctx.spec.maps && Object.hasOwn(ctx.spec.maps, e.map) ? ctx.spec.maps[e.map] : undefined; if (map && compatible(e, map.result)) add(map.result, e, 1)
    }
    if (e.op === 'if') scan(e.c)
    children(e).forEach(visit)
  }
  const seenConditions = new Set<string>()
  const scan = (c2: C): void => {
    tick(ctx)
    if (c2.op === 'all') return
    const id = conditionKey(c2); if (seenConditions.has(id)) return
    seenConditions.add(id)
    tick(ctx)
    if (c2.op === '<' && c2.a.op === 'var' && c2.b.op === 'var') {
      const parameter = c2.b.name
      const matches = Object.entries(ctx.spec.sorts).filter(([, p]) => p === parameter)
      if (matches.length === 1 && compatible(c2.a, matches[0]![0])) add(matches[0]![0], c2.a, 1)
    }
    if (c2.op === 'and' || c2.op === 'or') c2.xs.forEach(scan)
    else if (c2.op === 'not') scan(c2.x)
    else if (c2.op !== 'flag') { visit(c2.a); visit(c2.b) }
  }
  for (const goal of goals) goal.hyps.forEach(scan)
  // Generic sort-derived candidate, not an assertion of inhabitance. Original
  // guards stay in every instance of every fact, even for empty sorts.
  for (const sort of pools.keys()) add(sort, {op: 'const', value: 0}, 3)

  const functions = Object.entries(ctx.spec.functions).filter(([name, d]) => d.result && Object.hasOwn(m.fns ?? {}, name))
  const rank = new Map<string, number>(), visiting = new Set<string>()
  let cyclic = false
  const level = (sort: string): number => {
    tick(ctx)
    if (visiting.has(sort)) { cyclic = true; return 0 }
    if (rank.has(sort)) return rank.get(sort)!
    visiting.add(sort)
    const parents = functions.filter(([, d]) => d.result === sort).flatMap(([, d]) => d.args)
    const n = parents.length ? 1 + Math.max(...parents.map(level)) : 0
    visiting.delete(sort); rank.set(sort, n); return n
  }
  for (const sort of pools.keys()) level(sort)
  ctx.stats.cyclic ||= cyclic
  const ordered = functions.sort(([, a], [, b]) => rank.get(a.result!)! - rank.get(b.result!)!)
  const candidates = (sort: string) => [...pools.get(sort)!.values()].sort((a, b) => a.priority - b.priority)
  const cartesian = (ss: string[], consume: (xs: Candidate[]) => void): void => {
    const go = (i: number, xs: Candidate[]): void => {
      tick(ctx)
      if (i === ss.length) { consume(xs); return }
      for (const candidate of candidates(ss[i]!)) { tick(ctx); go(i + 1, [...xs, candidate]) }
    }
    go(0, [])
  }
  for (let round = 0; round < (cyclic ? ctx.limits.depth + 1 : 1); round++) {
    let changed = false
    for (const [name, d] of ordered) cartesian([...d.args], xs => {
      const depth = 1 + Math.max(...xs.map(x => x.depth))
      // Check limits before constructing a new application.
      if (cyclic && depth > ctx.limits.depth) throw new Limited('function-instantiation cyclic depth limit')
      tick(ctx, xs.length + 1)
      const e: E = {op: 'get', map: name, key: argsKey(xs.map(x => x.e))}
      changed = add(d.result!, e, 2, depth) || changed
    })
    if (!changed) break
  }

  const match = (pattern: E, term: E, variables: Set<string>, binding: Binding): boolean => {
    tick(ctx)
    if (pattern.op === 'var' && variables.has(pattern.name)) {
      const prior = binding.get(pattern.name)
      if (prior) return key(prior) === key(term)
      binding.set(pattern.name, term); return true
    }
    if (pattern.op !== term.op) return false
    if (pattern.op === 'if' || term.op === 'if') return key(pattern) === key(term) // conservative; no binder capture
    if (pattern.op === 'var' && term.op === 'var') return pattern.name === term.name
    if (pattern.op === 'const' && term.op === 'const') return pattern.value === term.value
    if (pattern.op === 'get' && term.op === 'get') {
      if (pattern.map !== term.map) return false
      const decl = Object.hasOwn(ctx.spec.functions, pattern.map) ? ctx.spec.functions[pattern.map] : undefined
      if (decl) {
        const pa = callArgs(pattern.key, decl.args.length, ctx), ta = callArgs(term.key, decl.args.length, ctx)
        if (pa && ta) return pa.every((p, i) => match(p, ta[i]!, variables, binding))
      }
    }
    if ((pattern.op === 'mul' && term.op === 'mul' || pattern.op === 'proj' && term.op === 'proj') && pattern.k !== term.k) return false
    const left = children(pattern), right = children(term)
    return left.length === right.length && left.every((p, i) => match(p, right[i]!, variables, binding))
  }
  const handled = new Set(facts.map(f => f.law))
  const other = (m.facts ?? []).filter(f => !handled.has(f))
  const out = {...(legacy && other.length ? legacy({...m, facts: other}, input, goals) : input)}
  for (const fact of facts) {
    const seen = new Set<string>(), priorEntries = input[fact.law.name] ?? [], n = fact.vars.length
    if (priorEntries.length % n) throw new Error('incomplete existing function-fact tuple')
    if (priorEntries.length / n > ctx.limits.tuples) throw new Limited(`function-instantiation existing tuple limit for ${fact.law.name}`)
    tick(ctx, priorEntries.length + 1)
    const entries = [...priorEntries]
    const tupleKey = (xs: E[]) => pack(xs.map(key))
    for (let i = 0; i < entries.length; i += n) seen.add(tupleKey(entries.slice(i, i + n)))
    const emit = (xs: E[], matched: boolean): void => {
      tick(ctx)
      const id = tupleKey(xs); if (seen.has(id)) return
      if (seen.size >= ctx.limits.tuples) throw new Limited(`function-instantiation tuple limit for ${fact.law.name}`)
      seen.add(id); entries.push(...xs); if (matched) ctx.stats.matched++; else ctx.stats.generated++
    }
    const variables = new Set(fact.vars), partials: Binding[] = [], partialKeys = new Set<string>()
    const bindingKey = (b: Binding) => pack(fact.vars.map(v => b.has(v) ? key(b.get(v)!) : ''))
    for (const pattern of fact.patterns) for (const read of reads) {
      tick(ctx)
      if (pattern.name !== read.name || pattern.args.length !== read.args.length) continue
      const binding: Binding = new Map()
      if (pattern.args.every((p, i) => match(p, read.args[i]!, variables, binding)) && binding.size) {
        const id = bindingKey(binding)
        if (partialKeys.has(id)) continue
        if (partials.length >= ctx.limits.tuples) throw new Limited('function-instantiation pattern limit')
        partialKeys.add(id); partials.push(binding)
      }
    }
    // Covering pattern sets: join compatible partial bindings, never changing a
    // repeated variable. Dedup/cap before retaining each candidate join.
    const joined: Binding[] = [new Map()], joinedKeys = new Set<string>([''])
    for (const partial of partials) {
      const count = joined.length
      for (let j = 0; j < count; j++) {
        tick(ctx)
        const prior = joined[j]!
        if ([...partial].some(([v, e]) => prior.has(v) && key(prior.get(v)!) !== key(e))) continue
        tick(ctx, prior.size + partial.size + 1)
        const merged = new Map([...prior, ...partial]), id = bindingKey(merged)
        if (joinedKeys.has(id)) continue
        if (joined.length >= ctx.limits.tuples) throw new Limited('function-instantiation pattern-set limit')
        joinedKeys.add(id); joined.push(merged)
        if (fact.vars.every(v => merged.has(v))) emit(fact.vars.map(v => merged.get(v)!), true)
      }
    }
    cartesian(fact.sorts, xs => emit(xs.map(x => x.e), false))
    out[fact.law.name] = entries
  }
  return out
}
