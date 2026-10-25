// Statecharts as rules: states (nested, each compound with its initial child and, if asked, the child it was last in),
// parallel regions, events with a payload, guarded transitions that set the chart's extended state, final states. A chart
// compiles to one plain rule, its step a choice among transitions, so everything proven about rules holds of charts and
// nothing here is trusted: the kernel proves the rule it builds.
//
//   const order = chart('order').context({retries: 0}).states({
//     new: {}, active: {states: {paid: {}, shipped: {}}, history: true}, refunded: {final: true}, delivered: {final: true},
//   })
//     .on('pay', {from: 'new', to: 'active'})
//     .on('ship', {from: 'active.paid', to: 'active.shipped'})
//     .on('refund', {from: 'active.paid', to: 'refunded'})
//     .on('deliver', {from: 'active.shipped', to: 'delivered'})
//   order.check() // every state reached (with the run that reaches it), none stuck, no event ambiguous
//
// Semantics, per region and per event: of the transitions whose source holds and whose guard holds, the one with the
// most specific source (an inner state over its parent) is taken, then the first declared; the regions react to the
// same event at once. A transition into a compound state enters its initial child, or the child it was last in when the
// compound keeps its history; `set` writes the extended state (a variable two regions both set takes the first region's).
import {type Kind, type ProveOptions, type Rule, type TermLike, type Verdict, Choice, Cond, Term, all, any, no, oneOf, proveRule, proveSteps, rule, when, yes} from './dsl.ts'
import {type Law, type Request, type State, interpret, numbersOf} from './machine.ts'
import {allowed} from './watch.ts'
import type {StepLaw} from '../kernel/kernel.ts'

// A state: a leaf, or a compound with its children (the first is the initial one unless `initial` names another).
export type StateNode = {states?: Record<string, StateNode>, initial?: string, history?: boolean, final?: boolean}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Obj = Record<string, any>
// What a guard, a `set` and a law's `before` read: params, payload, context, the event, whether a region is in a state,
// and a compound's history (the state it was last in, a full path: last('active').is('active.shipped')).
type Env<P, I, X> = P & I & X & {event: Choice<string>, in: (path: string) => Cond, last: (compound: string) => Choice<string>}
type After<X> = X & {in: (path: string) => Cond, last: (compound: string) => Choice<string>}
// Without `to`, an internal transition: the state stays as it is (nothing is exited or entered) and `set` runs. With
// `fresh`, the target is entered at its initial states all the way down, not where a compound keeping its history was
// last (as XState enters a state any way but through its history node).
export type Transition<P, I, X> = {from: string | string[], to?: string, fresh?: boolean, when?: (env: Env<P, I, X>) => Cond, set?: (env: Env<P, I, X>) => Partial<{[k in keyof X]: X[k] extends Choice<infer K> ? K | X[k] : TermLike | Cond | X[k]}>}

type Region = {name: string, field: string, leaves: string[], finals: Set<string>, compounds: Map<string, {initial: string, history: boolean}>}
type Placed<P, I, X> = Transition<P, I, X> & {event: string, region: string, sources: string[], depth: number, order: number}

export class Chart<P extends Obj = {}, I extends Obj = {}, X extends Obj = {}> {
  constructor(private readonly s: {name: string, params: Obj, inputs: Obj, context: Obj, outputs: Obj, regions: [string, StateNode][], on: [string, Transition<P, I, X>][], field?: string, events?: string[]}) {}
  private with(more: object): never { return new Chart({...this.s, ...more} as never) as never }

  params<K extends Record<string, Kind<unknown>>>(kinds: K): Chart<P & {[k in keyof K]: K[k] extends Kind<infer V> ? V : never}, I, X> { return this.with({params: {...this.s.params, ...kinds}}) }
  // The payload an event brings (every event brings the same fields; one reads those it needs).
  inputs<K extends Record<string, Kind<unknown>>>(kinds: K): Chart<P, I & {[k in keyof K]: K[k] extends Kind<infer V> ? V : never}, X> { return this.with({inputs: {...this.s.inputs, ...kinds}}) }
  // The extended state: a natural from a number, or any kind from `kind.from(init)`.
  context<T extends Record<string, number | {kind: Kind<unknown>, init: unknown}>>(init: T): Chart<P, I, X & {[k in keyof T]: T[k] extends {kind: Kind<infer V>} ? V : Term}> { return this.with({context: {...this.s.context, ...init}}) }
  // What each step decides, read after it (a command, a verdict): every output starts each step at its default, and a
  // transition taken may set it, so a step where none fires reads the default, never the last step's value. A default
  // is a number, a choice (`oneOf(...).from('denied')`) or a yes/no (`bool.from(false)`).
  outputs<T extends Record<string, number | {kind: Kind<unknown>, init: unknown}>>(init: T): Chart<P, I, X & {[k in keyof T]: T[k] extends {kind: Kind<infer V>} ? V : Term}> { return this.with({outputs: {...this.s.outputs, ...init}}) }
  // The events, in the order they are encoded (by default, the order they are first used in `on`).
  events(...names: string[]): Chart<P, I, X> { return this.with({events: names}) }
  // One region's states (a chart of one region names its states plainly: 'active.paid'); `field` names the state
  // variable the rule keeps them in (`state` by default).
  states(tree: Record<string, StateNode>, opts: {initial?: string, field?: string} = {}): Chart<P, I, X> { return this.with({regions: [['state', {states: tree, initial: opts.initial}]], field: opts.field}) }
  // Parallel regions, each with its own states, reacting to the same events: paths start with the region ('payment.paid').
  regions(regions: Record<string, StateNode>): Chart<P, I, X> { return this.with({regions: Object.entries(regions)}) }
  on(event: string, t: Transition<P, I, X>): Chart<P, I, X> { return this.with({on: [...this.s.on, [event, t]]}) }

  // --- the rule it compiles to -------------------------------------------------------------------------------------
  private built?: {rule: Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>, regions: Region[], placed: Placed<P, I, X>[], events: string[]}
  private build() {
    if (this.built) return this.built
    const s = this.s, single = s.regions.length === 1 && s.regions[0]![0] === 'state'
    if (!s.regions.length) throw new Error(`${s.name}: a chart needs states`)
    const regions: Region[] = s.regions.map(([name, root]) => {
      const leaves: string[] = [], finals = new Set<string>(), compounds = new Map<string, {initial: string, history: boolean}>()
      const walk = (path: string, node: StateNode) => {
        const kids = Object.entries(node.states ?? {})
        if (!kids.length) { leaves.push(path); if (node.final) finals.add(path); return }
        const initial = node.initial ?? kids[0]![0]
        if (!node.states![initial]) throw new Error(`${s.name}: ${path || name}'s initial state ${initial} isn't one of its states`)
        compounds.set(path, {initial, history: !!node.history})
        for (const [k, kid] of kids) {
          if (/[.*[\],:]/.test(k)) throw new Error(`${s.name}: the state name ${k} has a reserved character`)
          walk(path ? `${path}.${k}` : k, kid)
        }
      }
      walk('', root)
      return {name, field: single ? s.field ?? 'state' : name, leaves, finals, compounds}
    })
    // A path as the region and the state within it.
    const locate = (path: string): [Region, string] => {
      if (single) return [regions[0]!, path]
      const [head, ...rest] = path.split('.'), r = regions.find(x => x.name === head)
      if (!r) throw new Error(`${s.name}: ${path} names no region (${regions.map(x => x.name).join(', ')})`)
      return [r, rest.join('.')]
    }
    const under = (r: Region, path: string) => {
      const out = r.leaves.filter(l => path === '' || l === path || l.startsWith(`${path}.`))
      if (!out.length) throw new Error(`${s.name}: no state ${path} in ${r.name}`)
      return out
    }
    const used = [...new Set(s.on.map(([e]) => e))], events = s.events ?? used
    for (const e of used) if (!events.includes(e)) throw new Error(`${s.name}: the event ${e} isn't one of the events declared (${events.join(', ')})`)
    if (new Set(events).size !== events.length) throw new Error(`${s.name}: an event is declared twice`)
    if (!events.length) throw new Error(`${s.name}: a chart needs transitions`)
    const placed: Placed<P, I, X>[] = s.on.map(([event, t], order) => {
      const froms = (Array.isArray(t.from) ? t.from : [t.from]).map(locate), [to] = t.to === undefined ? froms[0]! : locate(t.to)
      if (froms.some(([r]) => r !== to)) throw new Error(`${s.name}: a transition on ${event} goes from one region to another (${t.to ?? [t.from].flat().join(", ")})`)
      if (t.to !== undefined) under(to, locate(t.to)[1])
      const sources = [...new Set(froms.flatMap(([r, p]) => under(r, p)))]
      return {...t, event, region: to.name, sources, depth: Math.min(...froms.map(([, p]) => (p === '' ? 0 : p.split('.').length))), order}
    })
    // Most specific source first, then the order declared: the first enabled in this order is taken.
    placed.sort((a, b) => b.depth - a.depth || a.order - b.order)
    const lastOf = (r: Region, c: string) => `${r.field}.last${c ? `.${c}` : ''}`
    const state: Obj = {}
    for (const r of regions) {
      const kind = oneOf(...r.leaves), enter = (path: string): string => { const c = r.compounds.get(path); return c ? enter(path ? `${path}.${c.initial}` : c.initial) : path }
      state[r.field] = kind.from(enter(''))
      for (const [c, {history}] of r.compounds) if (history && c) state[lastOf(r, c)] = kind.from(enter(c))
    }
    for (const [k, v] of Object.entries({...s.context, ...s.outputs})) state[k] = v
    const guardEnv = (env: Obj) => this.wrap(env) as Env<P, I, X>
    // Entering a path: a leaf, or a compound's last child (with history, unless fresh) or its initial one.
    const entered = (env: Obj, r: Region, path: string, fresh = false): Choice<string> => {
      const c = r.compounds.get(path), field = env[r.field] as Choice<string>
      if (!c) return field.of(path)
      if (c.history && path && !fresh) return env[lastOf(r, path)] as Choice<string>
      return entered(env, r, path ? `${path}.${c.initial}` : c.initial, fresh)
    }
    let built = rule(s.name).params(s.params as never).inputs({event: oneOf(...events), ...s.inputs} as never).state(state as never) as Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>
    // A set of a region's states as ranges of their indices (n <= 2, 3 <= n <= 4): a few comparisons, where one test per
    // state would be a disjunction the prover splits on; the whole region is no condition at all.
    const among = (env: Obj, r: Region, leaves: string[]): Cond => {
      const n = (env[r.field] as Choice<string>).index, ix = leaves.map(l => r.leaves.indexOf(l)).sort((a, b) => a - b), top = r.leaves.length - 1, ranges: [number, number][] = []
      for (const i of ix) { const last = ranges.at(-1); if (last && i === last[1] + 1) last[1] = i; else ranges.push([i, i]) }
      return any(...ranges.map(([a, b]) => (a === 0 && b === top ? yes : a === b ? n.eq(a) : a === 0 ? n.atMost(b) : b === top ? n.atLeast(a) : n.atLeast(a).and(n.atMost(b)))))
    }
    const regionOf = (t: Placed<P, I, X>) => regions.find(r => r.name === t.region)!
    built = built.flags((env: Obj) => Object.fromEntries(placed.map((t, i) => [`on${i}`, all(
      (env.event as Choice<string>).is(t.event), among(env, regionOf(t), t.sources), ...(t.when ? [t.when(guardEnv(env))] : []))]))) as never
    // A transition is taken when it is enabled and no transition before it in its region, on its event, from a state it
    // shares, is (transitions on other events are never enabled together).
    built = built.flags((env: Obj) => Object.fromEntries(placed.map((t, i) => [`take${i}`, all(env[`on${i}`] as Cond,
      ...placed.slice(0, i).flatMap((u, j) => (u.region === t.region && u.event === t.event && u.sources.some(l => t.sources.includes(l)) ? [(env[`on${j}`] as Cond).not()] : [])))]))) as never
    built = built.step((env: Obj) => {
      const out: Obj = {}
      for (const r of regions) {
        // The transitions taken in a region exclude one another, so those entering one state share a `when` (any of
        // them taken), and an internal one needs none (the state stays).
        out[r.field] = grouped(placed.map((t, i) => [t, i] as const).filter(([t]) => t.region === r.name && t.to !== undefined)
          .map(([t, i]) => ({i, region: r.name, value: entered(env, r, locate(t.to!)[1], t.fresh)})), env, env[r.field])
        for (const [c, {history}] of r.compounds) if (history && c) out[lastOf(r, c)] = when(any(...under(r, c).map(l => (out[r.field] as Choice<string>).is(l))), out[r.field], env[lastOf(r, c)])
      }
      // Context keeps its value where no transition taken sets it; an output falls back to its default.
      for (const k of [...Object.keys(s.context), ...Object.keys(s.outputs)]) {
        const sets = placed.map((t, i) => [t, i] as const).filter(([t]) => t.set).map(([t, i]) => ({i, region: t.region, value: t.set!(guardEnv(env))[k as keyof X] as unknown})).filter(x => x.value !== undefined)
        const base = k in s.outputs ? defaultOf(env[k], s.outputs[k], k) : env[k]
        if (sets.length || k in s.outputs) out[k] = grouped(sets.map(x => ({...x, value: typeof x.value === 'string' ? (env[k] as Choice<string>).of(x.value) : x.value})), env, base)
      }
      return out
    }) as never
    this.built = {rule: built, regions, placed, events}
    return this.built
  }
  // The rule the chart compiles to: its state is each region's state (`state`, or the region's name), each compound's
  // last child where it keeps its history, and the context; its inputs the event and the payload.
  get rule(): Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj> { return this.build().rule }
  // Whether a region is in a state (a compound: any state within it), for laws: chart.in(env, 'active').
  in(env: Obj, path: string): Cond {
    const {regions} = this.build(), single = regions.length === 1 && regions[0]!.name === 'state'
    const [head, ...rest] = single ? ['state', ...path.split('.')] : path.split('.'), r = regions.find(x => x.name === head)!
    const p = rest.join('.'), leaves = r.leaves.filter(l => p === '' || l === p || l.startsWith(`${p}.`))
    if (!leaves.length) throw new Error(`${this.s.name}: no state ${path}`)
    return any(...leaves.map(l => (env[r.field] as Choice<string>).is(l)))
  }
  // A compound's history: the state it was last in (its initial one before it was ever left), for laws: chart.last(env, 'active').
  last(env: Obj, compound: string): Choice<string> {
    const {regions} = this.build(), single = regions.length === 1 && regions[0]!.name === 'state'
    const [head, ...rest] = single ? ['state', ...compound.split('.')] : compound.split('.'), r = regions.find(x => x.name === head)!, c = rest.join('.')
    if (!r?.compounds.get(c)?.history) throw new Error(`${this.s.name}: ${compound} keeps no history`)
    return env[`${r.field}.last.${c}`] as Choice<string>
  }
  private wrap(env: Obj): Obj { return Object.assign(Object.create(null), env, {in: (p: string) => this.in(env, p), last: (c: string) => this.last(env, c)}) }
  law(name: string, f: (env: After<P & X>) => Cond): Law { return this.rule.law(name, (env: Obj) => f(this.wrap(env) as never)) }
  stepLaw(name: string, then: (before: Env<P, I, X>, after: After<X>) => Cond, when?: (before: Env<P, I, X>) => Cond): StepLaw {
    return this.rule.stepLaw(name, (b: Obj, a: Obj) => then(this.wrap(b) as never, this.wrap(a) as never), when && ((b: Obj) => when(this.wrap(b) as never)))
  }
  // What the chart keeps true by its construction: each compound's history is one of its own states. Proven beside the
  // laws `prove` and `check` are given (as a rule's kind laws are), since a law about entering a compound may need it.
  chartLaws(): Law[] {
    const {rule: r, regions} = this.build()
    return regions.flatMap(reg => [...reg.compounds].filter(([c, {history}]) => history && c).map(([c]) =>
      r.law(`${reg.name === 'state' ? '' : `${reg.name}.`}${c} remembers one of its own states`, (env: Obj) => any(...reg.leaves.filter(l => l.startsWith(`${c}.`)).map(l => (env[`${reg.field}.last.${c}`] as Choice<string>).is(l))))))
  }
  prove(laws: Law[] = [], stepLaws: StepLaw[] = [], opts: ProveOptions = {}): Verdict { const given = [...this.chartLaws(), ...laws]; return stepLaws.length ? proveSteps(this.rule, given, stepLaws, opts) : proveRule(this.rule, given, opts) }

  // --- the checks a chart's author expects -------------------------------------------------------------------------
  // reached: each state, with the first run from the start that reaches it (a breadth-first walk of the compiled rule
  // over every event and small payloads, `bound` the largest natural tried, under `params`), or `unreachable` where the
  // prover proves no run reaches it, or `unknown`. stuck: states with no transition out that aren't final. ambiguous:
  // two transitions of one region, as specific as each other, both enabled by one request (the first declared is taken;
  // the check names the pair and a request that enables both), each pair proven apart otherwise.
  check(opts: {params?: Obj, bound?: number, maxStates?: number} = {}): {ok: boolean, reached: Record<string, {run: Obj[]} | 'unreachable' | 'unknown'>, stuck: string[], ambiguous: {event: string, transitions: [number, number], verdict: Verdict}[]} {
    const {rule: r, regions, placed, events} = this.build(), m = r.machine, run = interpret(m), bound = opts.bound ?? 2
    const single = regions.length === 1 && regions[0]!.name === 'state', label = (reg: Region, l: string) => (single ? l : `${reg.name}.${l}`)
    const params = opts.params ? r.encodeParams(opts.params as never) : Object.fromEntries(m.params.map(p => [p, bound]))
    // Every request: each event, each payload variable over its range (a kind bounded by a small constant in full).
    const tops = new Map<string, number>()
    const conj = (c: typeof m.assume): NonNullable<typeof m.assume>[] => (c === undefined ? [] : c.op === 'and' ? c.xs.flatMap(conj) : [c])
    for (const c of conj(m.assume)) if ((c.op === '<' || c.op === '<=') && c.a.op === 'var' && c.b.op === 'const') tops.set(c.a.name, c.op === '<' ? c.b.value - 1 : c.b.value)
    const requests = m.inputs.reduce<Request[]>((acc, n) => acc.flatMap(t => Array.from({length: Math.min(tops.get(n) ?? bound, 15) + 1}, (_, i) => ({...t, [n]: i}))), [{}])
    const key = (st: State) => JSON.stringify([st.scalars, Object.entries(st.maps).map(([n, c]) => [n, [...c]])])
    const start = run.init(params), seen = new Map<string, {st: State, from?: string, by?: Request}>([[key(start), {st: start}]]), queue = [key(start)]
    const reachedAt = new Map<string, string>()
    const note = (k: string, st: State) => { for (const reg of regions) { const l = reg.leaves[st.scalars[reg.field]!]!; if (!reachedAt.has(label(reg, l))) reachedAt.set(label(reg, l), k) } }
    note(queue[0]!, start)
    // Breadth first, so each state's run is a shortest one; done once every state has one.
    const states = regions.reduce((n, reg) => n + reg.leaves.length, 0)
    while (queue.length && seen.size < (opts.maxStates ?? 20_000) && reachedAt.size < states) {
      const k = queue.shift()!, st = seen.get(k)!.st
      for (const req of requests) {
        if (!allowed(m, run, params, st, req)) continue
        const next = run.step(params, st, req), nk = key(next)
        if (seen.has(nk)) continue
        seen.set(nk, {st: next, from: k, by: req}); queue.push(nk); note(nk, next)
      }
    }
    const runTo = (k: string): Obj[] => { const out: Obj[] = []; for (let at = seen.get(k)!; at.by; at = seen.get(at.from!)!) out.unshift({...numbersOf(at.by), event: events[at.by.event as number]}); return out }
    // States no run reached: proven unreachable together (one may lean on another), else each on its own.
    const reached: Record<string, {run: Obj[]} | 'unreachable' | 'unknown'> = {}, missed: {name: string, law: Law}[] = []
    for (const reg of regions) for (const l of reg.leaves) {
      const name = label(reg, l), at = reachedAt.get(name)
      if (at) reached[name] = {run: runTo(at)}
      else missed.push({name, law: r.law(`${name} is never reached`, (env: Obj) => (env[reg.field] as Choice<string>).is(l).not())})
    }
    const proven = (v: Verdict) => v.proven && v.checked
    const allMissed = missed.length > 0 && proven(proveRule(r, [...this.chartLaws(), ...missed.map(x => x.law)], {search: false}))
    for (const x of missed) reached[x.name] = allMissed || proven(proveRule(r, [...this.chartLaws(), x.law], {search: false})) ? 'unreachable' : 'unknown'
    // A way out is a transition to a state: an internal one stays where it is.
    const stuck = regions.flatMap(reg => reg.leaves.filter(l => !reg.finals.has(l) && !placed.some(t => t.to !== undefined && t.region === reg.name && t.sources.includes(l))).map(l => label(reg, l)))
    // Pairs as specific as each other, on one event, from a state they share: proven never both enabled, all at once,
    // and only where that fails each on its own (to name the pair and the request).
    const pairs: {t: Placed<P, I, X>, u: Placed<P, I, X>, law: StepLaw}[] = []
    placed.forEach((t, i) => placed.forEach((u, j) => {
      if (j <= i || t.region !== u.region || t.event !== u.event || t.depth !== u.depth || !t.sources.some(l => u.sources.includes(l))) return
      pairs.push({t, u, law: r.stepLaw(`transitions ${t.order} and ${u.order} on ${t.event} are never both enabled`, (env: Obj) => all(env[`on${i}`] as Cond, env[`on${j}`] as Cond).not())})
    }))
    const ambiguous: {event: string, transitions: [number, number], verdict: Verdict}[] = []
    if (pairs.length && !proven(proveSteps(r, this.chartLaws(), pairs.map(x => x.law), {search: false})))
      for (const {t, u, law} of pairs) { const v = proveSteps(r, this.chartLaws(), [law], {search: false}); if (!proven(v)) ambiguous.push({event: t.event, transitions: [t.order, u.order], verdict: v}) }
    return {ok: !stuck.length && !ambiguous.length && Object.values(reached).every(x => x !== 'unknown'), reached, stuck, ambiguous}
  }
}
// The value a step writes: of the transitions taken, the first in order that writes one. Transitions of one region exclude
// one another, so consecutive ones of a region writing the same value share one `when` (any of them taken); the order
// between regions is kept.
function grouped(writes: {i: number, region: string, value: unknown}[], env: Obj, base: unknown): never {
  const keyOf = (v: unknown) => JSON.stringify(v instanceof Choice ? v.index.e : v instanceof Cond ? v.c : v instanceof Term ? v.e : v)
  const groups: {region: string, key: string, value: unknown, takes: Cond[]}[] = []
  for (const w of writes) {
    const key = keyOf(w.value)
    let g: (typeof groups)[number] | undefined
    for (let j = groups.length - 1; j >= 0 && groups[j]!.region === w.region; j--) if (groups[j]!.key === key) { g = groups[j]; break }
    if (g) g.takes.push(env[`take${w.i}`] as Cond)
    else groups.push({region: w.region, key, value: w.value, takes: [env[`take${w.i}`] as Cond]})
  }
  return groups.reduceRight<unknown>((acc, g) => when(any(...g.takes), g.value as never, acc as never), base) as never
}
export const chart = (name: string): Chart => new Chart({name, params: {}, inputs: {}, context: {}, outputs: {}, regions: [], on: []})
// An output's default as a value of its kind: a number, a choice's named value, or a yes/no.
function defaultOf(current: unknown, init: unknown, name: string): unknown {
  if (typeof init === 'number') return init
  const {kind, init: v} = init as {kind: Kind<unknown>, init: unknown}
  if (current instanceof Choice) return current.of(v as string)
  if (typeof v === 'boolean') return v ? yes : no
  if (typeof v === 'number') return v
  throw new Error(`the output ${name}'s default is a number, a choice or a yes/no, not ${String(v)} of ${kind.constructor.name}`)
}
