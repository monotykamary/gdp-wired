// XState machines as charts (core/chart.ts): `fromXState(machine, {guards, actions})` reads an XState v5 machine's
// config (states, nesting, a parallel root, history nodes, final states, transitions with named guards and actions) and
// builds the chart that runs the same way, so its laws are proven of the machine you ship. XState's guards and actions
// are JavaScript, so each one the machine names is given again in gdp-wired's terms: a guard as a condition, an action
// as the context it writes (or null, for one that writes none). `conforms(chart, machine, createActor)` then drives the
// real XState actor and the compiled rule with the same random events and compares every state and context, so a
// guard or an action given wrongly shows up as a run where the two part.
//
//   const machine = setup({guards: {canRetry: ...}, actions: {count: assign(...)}}).createMachine({...})
//   const c = fromXState(machine, {
//     guards: {canRetry: ({retries}) => retries.lt(2)},
//     actions: {count: ({retries}) => ({retries: retries.plus(1)}), notify: null},
//   })
//   c.check(); c.prove([c.law('retries stay within 2', ({retries}) => retries.atMost(2))])
//   conforms(c, machine, createActor) // {checked, failure?}
//
// An invoked actor and a timer are the world's: each answer of an actor (its done and its error) and each timer firing is
// an event from outside, named as XState names it (`xstate.done.actor.<id>`, `xstate.after.<delay>.<state id>`; v4's
// `done.invoke.<id>`, `xstate.after(<delay>)#<state id>`), taken only in the state that invoked or set it. Each comes
// once a visit, so every transition it takes must leave the state (or enter it again) and the last be unguarded; and one
// timer at a time (two fire in the order of their delays, which events from outside would not keep). Eventless (`always`)
// transitions and entry and exit actions that write the context are read into each transition as XState's macrostep:
// per state the machine is in, the exit actions (innermost first), the transition's, the entry actions (outermost
// first), then the eventless transitions of the state it lands in (innermost first, each guard on the context as it is
// then), again until none is enabled; the initial states' entry actions are the context's start.
// What a chart can't run the same way is refused when the chart is built, with the reason: a parallel state below the
// root, wildcard events, several targets at once, inline guards and actions, two regions writing the context on one
// event (XState runs their actions one after another; a chart's regions write in one step), a shallow history over
// nested states, eventless transitions or context-writing entry and exit actions in a parallel machine or beside a
// history node, eventless transitions that may run without end or that the machine takes at once from its start. So is
// every key it doesn't read, rather than dropped: a node or transition key outside the lists below (KEYS), an initial
// transition with actions, an event XState raises itself named in `on` (done, error, init).
// An XState v4 machine reads the same, its `cond` the guard v5 calls `guard` (a name, or {type, ...params}); v4's
// `in`, `strict`, `activities` and eventless `''` are refused with the rest. Each XState ignores the other's guard key,
// so a v5 machine with `cond` or a v4 one with `guard` is refused (a plain config is read by the key it uses).
import {type Kind, type Raw, Bool, Choice, Cond, Decimal, FixedWord, Int, Maybe, Rule, Str, Term, Variant, all, bool, int, lit, no, yes} from './dsl.ts'
import {type StateNode, Chart, chart} from './chart.ts'
import {type Machine, type Request, type State, evalC, seeded} from './machine.ts'
import {allowed} from './watch.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Obj = Record<string, any>
type XAction = string | {type: string, params?: unknown} | ((...args: never[]) => unknown)
type XTransition = string | {target?: string | string[], guard?: unknown, cond?: unknown, actions?: XAction | XAction[], reenter?: boolean, description?: string, [k: string]: unknown}
export type XNode = {
  id?: string, type?: 'atomic' | 'compound' | 'parallel' | 'final' | 'history', history?: 'shallow' | 'deep', initial?: string, target?: string,
  states?: Record<string, XNode>, on?: Record<string, XTransition | XTransition[] | undefined>, entry?: XAction | XAction[], exit?: XAction | XAction[],
  always?: unknown, after?: unknown, invoke?: unknown, onDone?: unknown, context?: unknown, [k: string]: unknown,
}
export type Guard = (env: Obj, params?: unknown) => Cond
export type Action = ((env: Obj, params?: unknown) => Obj) | null
export type Bridge = {
  params?: Record<string, Kind<unknown>>, inputs?: Record<string, Kind<unknown>>,
  // The context's kinds where the machine's initial context isn't plain numbers and booleans (or to override them).
  context?: Record<string, number | {kind: Kind<unknown>, init: unknown}>,
  guards?: Record<string, Guard>, actions?: Record<string, Action>, events?: string[],
  // Guards and actions written inline in the config, each given again by the function the config holds (what
  // gdp-wired/extract reads them as): `new Map([[machine.config.on.INC.actions, ({count}) => ({count: count.plus(1)})]])`.
  inline?: {guards?: ReadonlyMap<unknown, Guard>, actions?: ReadonlyMap<unknown, Action>},
  // Context fields the chart leaves out: no guard or action given here reads them (they reach only actors and effects
  // outside the machine, as gdp-wired/extract finds), so the chart is the machine with them projected away.
  ignore?: string[],
}

type Info = {node: XNode, segs: string[], parent?: Info, history?: {deep: boolean}}
// The keys read, and those that change nothing a run shows (descriptions, metadata, types, a final state's output, v4's
// action-order flags, which order no write to the context: those a transition makes run in order either way; v5's
// `reenter` and v4's `internal`, which change only which entry and exit actions run, and those write no context here).
// Any other is refused, by name, rather than dropped; some with the reason.
const KEYS = {
  node: new Set(['id', 'type', 'history', 'initial', 'target', 'states', 'on', 'entry', 'exit', 'invoke', 'after', 'always', 'description', 'meta', 'tags', 'output', 'data']),
  root: new Set(['context', 'version', 'types', 'schemas', 'schema', 'tsTypes', 'predictableActionArguments', 'preserveActionOrder']),
  transition: new Set(['target', 'guard', 'cond', 'actions', 'reenter', 'internal', 'description', 'meta']),
  // An invoked actor: what it is and the input it starts with are its own (outside the chart), its answers events.
  invoke: new Set(['id', 'src', 'input', 'systemId', 'onDone', 'onError']),
}
const WHY: Record<string, string> = {
  onDone: "a state's `onDone` (XState raises it when a final child is reached) has no chart counterpart",
  onSnapshot: "an invoked actor's `onSnapshot` has no chart counterpart", activities: "v4's `activities` have no chart counterpart", strict: "v4's `strict` (an event no state takes throws) has no chart counterpart",
  delimiter: 'a state path delimiter other than "."', onEntry: "v4's `onEntry`: write it as `entry`", onExit: "v4's `onExit`: write it as `exit`",
  in: "v4's `in` guard: write it as a named guard reading env.in(...)",
}
const keyCheck = (o: object, allowed: Set<string>, refuse: (what: string) => never, also?: Set<string>) => {
  for (const k of Object.keys(o)) if (!allowed.has(k) && !also?.has(k) && (o as Obj)[k] !== undefined) refuse(WHY[k] ?? `\`${k}\`, a key fromXState doesn't read (it would be dropped)`)
}
// Events XState raises itself (a done state or actor, an error, the start): a chart's events are only those sent.
const raised = (e: string) => e === '' || /^(xstate\.|done\.(state|invoke)\.|error\.(platform|execution|communication))/.test(e)
const list = <T>(x: T | T[] | undefined): T[] => (x === undefined ? [] : Array.isArray(x) ? x : [x])
// A machine (createMachine's or setup().createMachine's) or its config. Typed loosely: XState's own types are its own.
export type MachineLike = object
const configOf = (machine: MachineLike): XNode => ('config' in machine && machine.config && typeof machine.config === 'object' ? machine.config : machine) as XNode

// The XState a machine is of: v5's machines have getInitialSnapshot, v4's withConfig; a plain config says neither.
const versionOf = (machine: MachineLike): 4 | 5 | undefined => {
  const m = machine as {getInitialSnapshot?: unknown, withConfig?: unknown}
  return typeof m.getInitialSnapshot === 'function' ? 5 : typeof m.withConfig === 'function' ? 4 : undefined
}

export function fromXState(machine: MachineLike, opts: Bridge = {}): Chart<Obj, Obj, Obj> {
  const root = configOf(machine), name = root.id ?? 'machine', parallel = root.type === 'parallel', version = versionOf(machine)
  const refuse = (where: string, what: string): never => { throw new Error(`${name}: ${where || 'the machine'}: ${what}`) }
  const infos: Info[] = [], ids = new Map<string, Info>()
  const walk = (node: XNode, segs: string[], parent?: Info): Info => {
    const info: Info = {node, segs, parent}, where = segs.join('.')
    infos.push(info)
    ids.set(node.id ?? (segs.length ? `${name}.${where}` : name), info)
    keyCheck(node, KEYS.node, what => refuse(where, what), segs.length ? undefined : KEYS.root)
    if (node.type !== undefined && !['atomic', 'compound', 'parallel', 'final', 'history'].includes(node.type)) refuse(where, `the state type ${JSON.stringify(node.type)}`)
    if (node.initial !== undefined && typeof node.initial !== 'string') refuse(where, 'an initial transition given as an object (its actions have no chart counterpart): name the initial state')
    if (node.type !== 'history' && (node.history !== undefined || node.target !== undefined)) refuse(where, '`history` or `target` on a state that is not a history node')
    if (node.type === 'parallel' && segs.length) refuse(where, 'a parallel state below the root (a chart runs regions only at the top)')
    for (const [k, kid] of Object.entries(node.states ?? {})) walk(kid, [...segs, k], info)
    const hist = Object.entries(node.states ?? {}).filter(([, kid]) => kid.type === 'history')
    if (hist.length) {
      const deep = hist.every(([, h]) => h.history === 'deep'), kids = Object.entries(node.states!).filter(([, kid]) => kid.type !== 'history')
      if (!deep && kids.some(([, kid]) => Object.values(kid.states ?? {}).some(g => g.type !== 'history'))) refuse(where, 'a shallow history over nested states (a chart keeps the innermost state)')
      for (const [k, h] of hist) if (h.target !== undefined && h.target !== (node.initial ?? kids[0]?.[0])) refuse(`${where}.${k}`, 'a history with its own default target')
      info.history = {deep}
    }
    return info
  }
  walk(root, [])
  const pathOf = (i: Info) => i.segs.join('.')
  const descend = (from: Info, segs: string[], t: string): Info => segs.reduce<Info>((at, seg) => {
    const kid = infos.find(x => x.parent === at && x.segs.at(-1) === seg)
    return kid ?? refuse(pathOf(from), `no state ${t}`)
  }, from)
  // A target as XState reads it: #id(.path), .child(.path) from the state itself, or a sibling(.path).
  const resolve = (from: Info, t: string): {to: Info, viaHistory: boolean} => {
    let at: Info
    if (t.startsWith('#')) {
      const parts = t.slice(1).split('.')
      let k = parts.length
      while (k > 0 && !ids.has(parts.slice(0, k).join('.'))) k--
      if (!k) refuse(pathOf(from), `no state with the id in ${t}`)
      at = descend(ids.get(parts.slice(0, k).join('.'))!, parts.slice(k), t)
    } else if (t.startsWith('.')) at = descend(from, t.slice(1).split('.'), t)
    else at = descend(from.parent ?? from, t.split('.'), t)
    return at.node.type === 'history' ? {to: at.parent!, viaHistory: true} : {to: at, viaHistory: false}
  }

  // Guards and actions, named and given again.
  // v5's guard: a name or {type, params}; v4's cond: a name or {type, ...params}, its params the object's other keys.
  const guardOf = (where: string, g: unknown, v4 = false): Guard | undefined => {
    if (g === undefined) return undefined
    const given = opts.inline?.guards?.get(g)
    if (given) return env => given(env)
    const v4params = (o: Obj) => { const {type: _t, ...rest} = o; void _t; return Object.keys(rest).length ? rest : undefined }
    const [n, params] = typeof g === 'string' ? [g, undefined] : typeof g === 'object' && g && typeof (g as {type?: unknown}).type === 'string' ? [(g as {type: string}).type, v4 ? v4params(g as Obj) : (g as {params?: unknown}).params] : [undefined, undefined]
    if (n === undefined) return refuse(where, `an inline guard${typeof g === 'function' && (g as {type?: string}).type ? ` (${(g as {type?: string}).type})` : ''}: name it in setup({guards}) and give its condition in guards`)
    const f = opts.guards?.[n] ?? refuse(where, `the guard ${n}: give its condition in guards`)
    return env => f(env, params)
  }
  const actionsOf = (where: string, as: XAction[]): ((env: Obj) => Obj)[] => as.flatMap(a => {
    if (opts.inline?.actions?.has(a)) { const f = opts.inline.actions.get(a); return f ? [(env: Obj) => f(env)] : [] }
    const [n, params] = typeof a === 'string' ? [a, undefined] : typeof a === 'object' && a && typeof a.type === 'string' ? [a.type, a.params] : [undefined, undefined]
    if (n === undefined) return refuse(where, `an inline action${typeof a === 'function' && (a as {type?: string}).type ? ` (${(a as {type?: string}).type})` : ''}: name it in setup({actions}) and give the context it writes in actions`)
    if (!opts.actions || !(n in opts.actions)) return refuse(where, `the action ${n}: give the context it writes in actions (null if it writes none)`)
    const f = opts.actions[n]
    return f ? [(env: Obj) => f(env, params)] : []
  })
  // Several actions run one after another, each reading the context the one before wrote.
  const composed = (fs: ((env: Obj) => Obj)[]) => (fs.length ? (env: Obj) => {
    let cur = env
    const out: Obj = {}
    for (const f of fs) {
      const o = f(cur)
      Object.assign(out, o)
      cur = Object.assign(Object.create(null), cur, Object.fromEntries(Object.entries(o).map(([k, v]) => [k, typeof v === 'string' && cur[k] instanceof Choice ? (cur[k] as Choice<string>).of(v) : v])))
    }
    return out
  } : undefined)

  // The states, as a chart's.
  const nodeOf = (i: Info): StateNode => {
    const kids = infos.filter(x => x.parent === i && x.node.type !== 'history')
    if (!kids.length) return i.node.type === 'final' ? {final: true} : {}
    return {states: Object.fromEntries(kids.map(k => [k.segs.at(-1)!, nodeOf(k)])), ...(i.node.initial ? {initial: i.node.initial} : {}), ...(i.history ? {history: true} : {})}
  }
  const top = infos.filter(x => x.parent === infos[0])
  let c = chart(name).params((opts.params ?? {}) as never).inputs((opts.inputs ?? {}) as never).context(contextOf(root, opts.context, refuse, opts.ignore) as never) as unknown as Chart<Obj, Obj, Obj>
  if (parallel) {
    for (const r of top) if (!infos.some(x => x.parent === r && x.node.type !== 'history')) refuse(pathOf(r), 'a region with no states of its own')
    c = c.regions(Object.fromEntries(top.map(r => [r.segs[0]!, nodeOf(r)])))
  } else c = c.states(nodeOf(infos[0]!).states ?? {[STATELESS]: {}}, root.initial ? {initial: root.initial} : {})
  if (opts.events) c = c.events(...opts.events)

  // Entry and exit actions, each node's composed: those that write the context make each transition XState's macrostep
  // (below), as do eventless transitions.
  const entryOf = new Map<Info, ((env: Obj) => Obj) | undefined>(), exitOf = new Map<Info, ((env: Obj) => Obj) | undefined>()
  for (const i of infos) for (const k of ['entry', 'exit'] as const) (k === 'entry' ? entryOf : exitOf).set(i, composed(actionsOf(pathOf(i), list(i.node[k]))))

  // The transitions, in document order (the chart takes the most specific source first, then the first declared, as
  // XState does): each state's `on`, the answers of the actors it invokes (done and error, events from outside), the
  // timer its `after` sets (an event from outside too), and its eventless (`always`) transitions, read into the others.
  type Raw = {event: string, src: Info, o: Obj, where: string}
  const raws: Raw[] = [], alwaysOf = new Map<Info, {o: Obj, where: string}[]>()
  // A state's id as XState makes it (the machine's own id, '(machine)' where it has none, then the path).
  const nodeId = (i: Info) => i.node.id ?? (i.segs.length ? `${root.id ?? '(machine)'}.${pathOf(i)}` : root.id ?? '(machine)')
  const read = (where: string, t: unknown): Obj => {
    if (t === null || (typeof t !== 'string' && typeof t !== 'object')) refuse(where, `a transition given as ${typeof t === 'function' ? 'a function' : JSON.stringify(t)}`)
    const o = (typeof t === 'string' ? {target: t} : t) as Obj, targets = list(o.target)
    keyCheck(o, KEYS.transition, what => refuse(where, what))
    if (o.guard !== undefined && o.cond !== undefined) refuse(where, 'both `guard` and v4\'s `cond`')
    // (each XState reads its own and takes a transition with the other's unguarded: refused, not taken so)
    if (o.cond !== undefined && version === 5) refuse(where, 'v4\'s `cond` in an XState v5 machine, which doesn\'t read it (it takes this transition unguarded): name the guard in `guard`')
    if (o.guard !== undefined && version === 4) refuse(where, 'v5\'s `guard` in an XState v4 machine, which doesn\'t read it (it takes this transition unguarded): name the guard in `cond`')
    if (targets.length > 1) refuse(where, 'several targets at once')
    return o
  }
  const under = (a: Info, b: Info): boolean => a === b || (!!a.parent && under(a.parent, b))
  // A transition that leaves the state (or enters it again: XState stops the actors it invoked and its timer, and
  // starts them anew), as v5 reads `reenter` and v4 an external transition.
  const leaves = (i: Info, o: Obj): boolean => {
    if (o.target === undefined) return false
    const to = resolve(i, list(o.target)[0] as string).to
    if (!under(to, i)) return true
    return version === 5 ? o.reenter === true : o.internal !== true && !String(list(o.target)[0]).startsWith('.')
  }
  // An actor's answer and a timer come once a visit: each transition they take leaves the state (so a second answer of
  // the same visit, which can't come, is never read), and the last takes the event whatever the guards say.
  const once = (i: Info, ts: Obj[], where: string, what: string) => {
    if (ts.some(o => !leaves(i, o))) refuse(where, `${what} that doesn't leave the state (the answer comes once a visit; a chart would take it again)`)
    const last = ts.at(-1)!
    if (last.guard !== undefined || last.cond !== undefined) refuse(where, `${what} whose last transition is guarded (the answer, refused by every guard, comes once a visit; a chart would take it again)`)
  }
  const timed = infos.filter(i => i.node.after !== undefined)
  for (const i of infos) {
    for (const [event, spec] of Object.entries(i.node.on ?? {})) {
      const where = `${pathOf(i) || 'the root'} on ${event || '""'}`
      if (event.includes('*')) refuse(where, 'a wildcard event')
      if (raised(event)) refuse(where, event ? 'an event XState raises itself (a done, error or init event)' : "v4's eventless transition (`''`)")
      if (spec === undefined) refuse(where, 'a forbidden event (an undefined transition)')
      for (const t of list(spec as XTransition | XTransition[])) raws.push({event, src: i, o: read(where, t), where})
    }
    list(i.node.invoke as unknown).forEach((inv, k) => {
      const where = `${pathOf(i) || 'the root'}'s invoke${list(i.node.invoke).length > 1 ? ` ${k}` : ''}`
      if (!inv || typeof inv !== 'object' || Array.isArray(inv)) return refuse(where, 'an invoke given as other than {src, ...}')
      keyCheck(inv, KEYS.invoke, what => refuse(where, what))
      if (!version) return refuse(where, 'an invoke in a plain config: give the machine itself (the events its actors answer by are named by its XState)')
      const names = answers(version, nodeId(i), inv as Obj, k)
      for (const [key, event] of [['onDone', names.done], ['onError', names.error]] as const) {
        const spec = (inv as Obj)[key]
        if (spec === undefined) continue
        const ts = list(spec as XTransition | XTransition[]).map(t => read(`${where} ${key}`, t))
        once(i, ts, `${where} ${key}`, `an actor's ${key}`)
        for (const o of ts) raws.push({event, src: i, o, where: `${where} ${key}`})
      }
    })
    if (i.node.after !== undefined) {
      const where = `${pathOf(i) || 'the root'}'s after`, after = i.node.after as Record<string, unknown>
      if (!after || typeof after !== 'object' || Array.isArray(after)) refuse(where, '`after` given as other than {delay: transitions}')
      if (!version) refuse(where, '`after` in a plain config: give the machine itself (the event its timer sends is named by its XState)')
      const delays = Object.keys(after)
      // One timer at a time: two (in one state, or in a state and one within it) fire in the order of their delays, which
      // a chart taking each as an event from outside would not keep.
      if (delays.length > 1) refuse(where, `two timers in one state (${delays.join(', ')}): they fire in the order of their delays, which the chart would not keep`)
      const other = timed.find(j => j !== i && (under(j, i) || under(i, j)))
      if (other) refuse(where, `a timer in ${pathOf(i) || 'the root'} and another in ${pathOf(other) || 'the root'}, running at once: they fire in the order of their delays, which the chart would not keep`)
      for (const delay of delays) {
        const event = timer(version!, nodeId(i), delay)
        const ts = list(after[delay] as XTransition | XTransition[]).map(t => read(where, t))
        once(i, ts, where, 'a timer')
        for (const o of ts) raws.push({event, src: i, o, where})
      }
    }
    if (i.node.always !== undefined) alwaysOf.set(i, list(i.node.always as XTransition | XTransition[]).map(t => ({o: read(`${pathOf(i) || 'the root'}'s always`, t), where: `${pathOf(i) || 'the root'}'s always`})))
  }
  const guardOfO = (where: string, o: Obj) => (o.cond !== undefined ? guardOf(where, o.cond, true) : guardOf(where, o.guard))
  // Where a transition applies: its state; for the root, every top state but a final one (XState stops there), or in a
  // parallel machine the region its target is in (the first region, for one with no target).
  const fromOf = (i: Info, to: Info | undefined) => (i.segs.length ? pathOf(i) : parallel ? (to ? to.segs[0]! : top[0]!.segs[0]!) : top.length ? top.filter(x => x.node.type !== 'final' && x.node.type !== 'history').map(pathOf) : STATELESS)
  const macro = [...alwaysOf.values()].some(x => x.length) || infos.some(i => entryOf.get(i) || exitOf.get(i))
  const writers = new Map<string, Set<string>>()
  if (!macro) for (const {event, src: i, o, where} of raws) {
    const to = o.target === undefined ? undefined : resolve(i, list(o.target)[0] as string)
    const set = composed(actionsOf(where, list(o.actions))), when = guardOfO(where, o)
    const from = fromOf(i, to?.to)
    if (set) { const region = parallel ? String(list(from)[0]).split('.')[0]! : 'state'; writers.set(event, (writers.get(event) ?? new Set()).add(region)) }
    c = c.on(event, {from, ...(to ? {to: pathOf(to.to), fresh: !to.viaHistory} : {}), ...(when ? {when} : {}), ...(set ? {set: set as never} : {})})
  }
  else {
    // XState's macrostep, per state the machine is in: the transition's exit actions (innermost first), its own, the entry
    // actions of the states it enters (outermost first), then the eventless transitions of the state it lands in (the
    // innermost state's first, each guard read on the context as it is then), again until none is enabled.
    if (parallel) refuse('', 'a parallel machine with eventless transitions or entry or exit actions that write the context')
    if (!top.length) refuse('', 'a machine with no states, with eventless transitions or entry or exit actions that write the context')
    for (const i of infos) if (i.history) refuse(pathOf(i), 'a history node in a machine with eventless transitions or entry or exit actions that write the context')
    const leafOf = (i: Info): Info => { const kids = infos.filter(x => x.parent === i && x.node.type !== 'history'); if (!kids.length) return i; return leafOf(kids.find(k => k.segs.at(-1) === i.node.initial) ?? kids[0]!) }
    const leavesUnder = (i: Info): Info[] => { const kids = infos.filter(x => x.parent === i && x.node.type !== 'history'); return kids.length ? kids.flatMap(leavesUnder) : [i] }
    const chain = (i: Info): Info[] => (i.parent ? [i, ...chain(i.parent)] : [i])
    // The context after writes, read as a guard or an action reads it, in a state known statically.
    // A value written, as the context's own kind holds it (a literal as the choice or the string it is; a maybe's parts).
    const value = (was: unknown, v: unknown): unknown => (typeof v === 'string' && was instanceof Choice ? (was as Choice<string>).of(v) : typeof v === 'string' && was instanceof Str ? was.literal(v)
      : was instanceof Maybe && v instanceof Maybe ? new Maybe(v.present, value(was.inner, v.inner)) : was instanceof Maybe && v === null ? new Maybe(lit(0), was.inner)
        : typeof v === 'number' ? lit(v) : typeof v === 'boolean' ? (v ? yes : no) : v)
    // (With no state given, the state is the one the step starts in: the chart's own `in`.)
    const at = (env: Obj, writes: Obj, leaf?: Info): Obj => Object.assign(Object.create(null), env, Object.fromEntries(Object.entries(writes).map(([k, v]) => [k, value(env[k], v)])), leaf ? {
      in: (p: string) => { const t = infos.find(x => pathOf(x) === p) ?? refuse('', `no state ${p}`); return under(leaf, t) ? yes : no },
      last: () => refuse('', 'a history read in a machine with eventless transitions or entry or exit actions that write the context'),
    } : {})
    const run = (fs: ((env: Obj) => Obj)[], env: Obj, writes: Obj, leaf?: Info): Obj => { let w = writes; for (const f of fs) w = {...w, ...f(at(env, w, leaf))}; return w }
    type Variant = {conds: ((env: Obj) => Cond)[], apply: (env: Obj) => Obj, leaf: Info, exits?: boolean}
    // One microstep: transition o of state src, taken from leaf.
    const micro = (v: Variant, src: Info, o: Obj, where: string): Variant => {
      const fs = actionsOf(where, list(o.actions))
      if (o.target === undefined) return {...v, apply: env => run(fs, env, v.apply(env), v.leaf)}
      const {to: T, viaHistory} = resolve(src, list(o.target)[0] as string)
      if (viaHistory) refuse(where, 'a history target in a machine with eventless transitions or entry or exit actions that write the context')
      // The transition's domain, as XState computes it: the source, for a target within it that isn't re-entered; else
      // the nearest state above the target that holds the source.
      const internal = version === 5 ? o.reenter !== true : o.internal === true || String(list(o.target)[0]).startsWith('.')
      const D = internal && under(T, src) ? src : chain(T).slice(1).find(a => a !== src && under(src, a)) ?? infos[0]!
      const exited = chain(v.leaf).filter(n => n !== D && under(n, D))
      const entered: Info[] = chain(T).filter(n => n !== D && under(n, D)).reverse()
      for (let n = T; ;) { const kids = infos.filter(x => x.parent === n && x.node.type !== 'history'); if (!kids.length) break; n = kids.find(k => k.segs.at(-1) === n.node.initial) ?? kids[0]!; entered.push(n) }
      const all = [...exited.map(n => exitOf.get(n)), ...fs, ...entered.map(n => entryOf.get(n))].filter((f): f is (env: Obj) => Obj => !!f)
      const leaf = entered.at(-1) ?? leafOf(T)
      return {conds: v.conds, leaf, apply: env => run(all, env, v.apply(env), v.leaf), exits: v.exits || exited.some(n => exitOf.get(n))}
    }
    // The eventless transitions from where a microstep lands, until none is enabled (at most a few in a row).
    const settle = (v: Variant, depth: number): Variant[] => {
      const cands = chain(v.leaf).flatMap(n => (alwaysOf.get(n) ?? []).map(a => ({n, ...a})))
      if (!cands.length) return [v]
      if (depth >= 6) refuse(pathOf(v.leaf), 'eventless transitions that may run more than 6 times in a row')
      const out: Variant[] = [], prior: Guard[] = []
      const after = (env: Obj) => at(env, v.apply(env), v.leaf)
      for (const {n, o, where} of cands) {
        const g = guardOfO(where, o), before = [...prior]
        const taken: Variant = {...v, conds: [...v.conds, ...before.map(p => (env: Obj) => p(after(env)).not()), ...(g ? [(env: Obj) => g(after(env))] : [])]}
        out.push(...settle(micro(taken, n, o, where), depth + 1))
        if (!g) return out
        prior.push(g)
      }
      out.push({...v, conds: [...v.conds, ...prior.map(p => (env: Obj) => p(after(env)).not())]})
      if (out.length > 64) refuse(pathOf(v.leaf), 'eventless transitions with more than 64 ways through')
      return out
    }
    // The start: XState enters the initial states, runs their entry actions and then takes any eventless transition
    // enabled. Both are read on the initial context, which must decide them: an entry action's writes become the
    // context's start (each a value the initial context fixes), and no eventless transition may be enabled there.
    const start = leafOf(infos[0]!), path0 = chain(start).reverse()
    const initGuards = path0.flatMap(n => (alwaysOf.get(n) ?? []).map(a => guardOfO(a.where, a.o)))
    const entries0 = path0.map(n => entryOf.get(n)).filter((f): f is (env: Obj) => Obj => !!f)
    if (initGuards.length || entries0.length) {
      if (initGuards.some(g => !g)) refuse(pathOf(start), 'an eventless transition the machine takes at once from its initial state')
      const ctx0 = contextOf(root, opts.context, refuse, opts.ignore), env0: Obj = Object.create(null), kinds: Record<string, Kind<unknown> | undefined> = {}
      for (const [k, v] of Object.entries(ctx0)) {
        const {kind, init} = typeof v === 'number' ? {kind: undefined, init: v} : v
        if (typeof init === 'function') refuse(pathOf(start), 'entry actions or an eventless transition at the start, over a context the params make')
        kinds[k] = kind
        env0[k] = kind ? kind.build(k, part => lit(kind.encode(k, init as never)[part] ?? 0)) : lit(init as number)
      }
      const fixed = (o: Obj) => new Proxy(at(o, {}, start), {get: (x, k) => (typeof k === 'string' && !(k in x) ? refuse(pathOf(start), `entry actions or an eventless transition at the start that read ${k} (not the context)`) : x[k as string])})
      let writes: Obj = {}
      for (const f of entries0) writes = {...writes, ...f(fixed({...env0, ...Object.fromEntries(Object.entries(writes).map(([k, w]) => [k, value(env0[k], w)]))}))}
      const known: Obj = {}
      for (const [k, w] of Object.entries(writes)) {
        const x = value(env0[k], w)
        const raw = x instanceof Choice ? (x.index.val === undefined ? undefined : x.values[x.index.val]) : x instanceof Term ? x.val : x instanceof Cond ? x.ok : undefined
        if (raw === undefined) refuse(pathOf(start), `an initial state's entry action writes ${k} a value the initial context doesn't fix`)
        known[k] = kinds[k] ? {kind: kinds[k], init: raw} : raw
      }
      if (Object.keys(known).length) c = c.context(known as never) as unknown as Chart<Obj, Obj, Obj>
      const env = fixed({...env0, ...Object.fromEntries(Object.entries(writes).map(([k, w]) => [k, value(env0[k], w)]))})
      for (const g of initGuards) {
        const ok = g!(env).ok
        if (ok === undefined) refuse(pathOf(start), 'an eventless transition from the initial state whose guard the initial context doesn\'t decide')
        if (ok) refuse(pathOf(start), 'an eventless transition the machine takes at once from its initial state')
      }
    }
    for (const {event, src: i, o, where} of raws) {
      const to = o.target === undefined ? undefined : resolve(i, list(o.target)[0] as string)
      const when = guardOfO(where, o), from = fromOf(i, to?.to)
      // Per state the machine may be in: where the transition exits states whose exit actions write the context, or
      // lands where an eventless transition may be enabled, its macrostep by cases there; everywhere else one
      // transition (its writes and the state it lands in the same from each), after those (which take every case
      // where they are).
      const sources = i.segs.length ? leavesUnder(i) : top.filter(x => x.node.type !== 'final' && x.node.type !== 'history').flatMap(leavesUnder)
      let plain: Variant | undefined
      for (const leaf of sources) {
        const v0 = micro({conds: [], apply: () => ({}), leaf}, i, o, where)
        if (!v0.exits && !chain(v0.leaf).some(n => alwaysOf.get(n)?.length)) { plain ??= v0; continue }
        for (const v of settle(v0, 0)) {
          const conds = [...(when ? [when] : []), ...v.conds]
          c = c.on(event, {from, ...(o.target === undefined && v.leaf === leaf ? {} : {to: pathOf(v.leaf), fresh: true}),
            when: env => all(env.in(pathOf(leaf)), ...conds.map(f => f(env))), set: ((env: Obj) => v.apply(env)) as never})
        }
      }
      if (plain) {
        // (a transition with no target writes as its actions do from wherever it is taken: in the state it starts in)
        const p = plain, fs = actionsOf(where, list(o.actions)), apply = o.target === undefined ? (env: Obj) => run(fs, env, {}) : p.apply
        c = c.on(event, {from, ...(o.target === undefined ? {} : {to: pathOf(p.leaf), fresh: true}), ...(when ? {when} : {}), set: ((env: Obj) => apply(env)) as never})
      }
    }
  }
  for (const [event, regions] of writers) if (regions.size > 1) refuse(`on ${event}`, `regions ${[...regions].join(' and ')} both write the context (XState runs their actions one after another)`)
  return c
}

// The events XState sends a machine itself, by its version: an invoked actor's answers (done, error), named by the
// invocation's id (its own, or its index and the state's id), and a timer's.
const answers = (version: 4 | 5, nodeId: string, inv: Obj, k: number) => {
  const id = inv.id ?? (version === 5 ? `${k}.${nodeId}` : `${nodeId}:invocation[${k}]`)
  return version === 5 ? {done: `xstate.done.actor.${id}`, error: `xstate.error.actor.${id}`} : {done: `done.invoke.${id}`, error: `error.platform.${id}`}
}
const timer = (version: 4 | 5, nodeId: string, delay: string) => (version === 5 ? `xstate.after.${delay}.${nodeId}` : `xstate.after(${delay})#${nodeId}`)
// Every event a machine reacts to: those its states name in `on`, its actors' answers and its timers (each of these with
// the state it comes in: the world sends an answer only while its actor runs, a timer only while it is set).
export function eventsOf(machine: MachineLike): string[] { return eventsWhere(machine).map(([e]) => e) }
function eventsWhere(machine: MachineLike): [string, string[] | undefined][] {
  const root = configOf(machine), version = versionOf(machine), name = root.id ?? '(machine)', out: [string, string[] | undefined][] = []
  let segsNow: string[] = []
  const add = (e: string, only?: boolean) => { if (!out.some(([x]) => x === e)) out.push([e, only ? segsNow : undefined]) }
  const walk = (n: XNode, segs: string[]) => {
    const id = n.id ?? (segs.length ? `${name}.${segs.join('.')}` : name)
    segsNow = segs
    for (const e of Object.keys(n.on ?? {})) add(e)
    if (version) {
      list(n.invoke as Obj | Obj[] | undefined).forEach((inv, k) => { const a = answers(version, id, inv, k); if (inv.onDone !== undefined) add(a.done, true); if (inv.onError !== undefined) add(a.error, true) })
      for (const d of Object.keys((n.after ?? {}) as Obj)) add(timer(version, id, d), true)
    }
    for (const [k, kid] of Object.entries(n.states ?? {})) walk(kid, [...segs, k])
  }
  walk(root, [])
  return out
}

// A machine with no states (its root's transitions only): one state of the chart's, XState's value {} there.
const STATELESS = '(machine)'
function contextOf(root: XNode, given: Bridge['context'], refuse: (where: string, what: string) => never, ignore: string[] = []): Record<string, number | {kind: Kind<unknown>, init: unknown}> {
  const out: Record<string, number | {kind: Kind<unknown>, init: unknown}> = {}
  if (given) for (const k of ignore) if (k in given) refuse('', `the context's ${k} both given and left out`)
  if (root.context !== undefined && typeof root.context !== 'object') { if (!given) refuse('', 'a context computed by a function: give its kinds in context'); return {...given} }
  for (const [k, v] of Object.entries((root.context ?? {}) as Obj)) {
    if ((given && k in given) || ignore.includes(k)) continue
    if (typeof v === 'number' && Number.isSafeInteger(v)) out[k] = v >= 0 ? v : int.from(v)
    else if (typeof v === 'boolean') out[k] = bool.from(v)
    else refuse('', `the context's ${k} (${JSON.stringify(v)}): give its kind in context`)
  }
  return {...out, ...given}
}

const canonical = (v: unknown): string => (v && typeof v === 'object' ? `{${Object.keys(v).sort().map(k => `${k}:${canonical((v as Obj)[k])}`).join(',')}}` : JSON.stringify(v))

// The chart against the machine itself: random events (a payload from `payload`, if the events carry one) sent to a
// fresh XState actor and to the compiled rule, the state value and the context compared after every event.
export type XActor = {send: (e: never) => void, getSnapshot: () => {value: unknown, context?: unknown}}
export function conforms(c: Chart<Obj, Obj, Obj>, machine: MachineLike, createActor: (machine: never) => {start: () => XActor},
  opts: {runs?: number, depth?: number, seed?: number, params?: Obj, payload?: (event: string, rand: (n: number) => number) => Obj, beforeSend?: (event: string, payload: Obj) => void, context?: string[], event?: (type: string, payload: Obj) => Obj} = {}): {checked: number, failure?: string} {
  // Every event it reacts to: its states' `on`, its actors' answers and its timers (sent as XState's own events, so a
  // run takes them in any order the world could).
  const root = configOf(machine), where = eventsWhere(machine), events = where.map(([e]) => e)
  const value = (segs: string[]): unknown => segs.reduceRight<unknown>((acc, seg) => (acc === undefined ? seg : {[seg]: acc}), undefined)
  const r = c.rule, g = r.compiled(), ps = r.encodeParams((opts.params ?? {}) as never)
  const rand = seeded(opts.seed ?? 1)
  const valueOf = (d: Obj): unknown => {
    const nest = (path: string): unknown => path.split('.').reduceRight<unknown>((acc, seg) => (acc === undefined ? seg : {[seg]: acc}), undefined)
    if (root.type === 'parallel') return Object.fromEntries(Object.keys(root.states ?? {}).filter(k => root.states![k]!.type !== 'history').map(k => [k, nest(String(d[k]))]))
    return d.state === STATELESS ? {} : nest(String(d.state))
  }
  const contextKeys = opts.context ?? Object.keys((root.context && typeof root.context === 'object' ? root.context : {}) as Obj)
  let checked = 0
  for (let run = 0; run < (opts.runs ?? 100); run++) {
    const actor = createActor(machine as never).start() as XActor & {stop?: () => void}
    let st = g.init(ps)
    const sent: string[] = []
    for (let d = 0; d < (opts.depth ?? 12); d++) {
      // An answer or a timer only where its state is (XState stops an actor whose answer is unhandled).
      const now = actor.getSnapshot() as {matches?: (v: unknown) => boolean}
      const live = where.every(([, segs]) => !segs?.length) ? events : where.filter(([, segs]) => !segs?.length || now.matches?.(value(segs))).map(([e]) => e)
      if (!live.length) break
      const type = live[rand(live.length)]!, payload = opts.payload?.(type, rand) ?? {}
      sent.push(Object.keys(payload).length ? `${type}${JSON.stringify(payload)}` : type)
      opts.beforeSend?.(type, payload)
      actor.send((opts.event ? opts.event(type, payload) : {type, ...payload}) as never)
      st = g.step(ps, st, r.encodeInput({event: type, ...payload} as never))
      const snap = actor.getSnapshot() as {value: unknown, context?: Obj}, d2 = r.decode(st), want = valueOf(d2)
      if (canonical(snap.value) !== canonical(want)) { actor.stop?.(); return {checked, failure: `after ${sent.join(', ')}: XState is in ${JSON.stringify(snap.value)}, the chart in ${JSON.stringify(want)}`} }
      for (const k of contextKeys) if (JSON.stringify(snap.context?.[k]) !== JSON.stringify(d2[k])) { actor.stop?.(); return {checked, failure: `after ${sent.join(', ')}: XState's ${k} is ${JSON.stringify(snap.context?.[k])}, the chart's ${JSON.stringify(d2[k])}`} }
      checked++
      // XState v4, done (a final state at the top): its service takes no more events (and warns of each), nor does the
      // chart; the run ends there. (v5's actor ignores them quietly, as the chart does: its runs go on.)
      if ((snap as {done?: boolean}).done === true) break
    }
    // Its timers and actors stopped with it.
    actor.stop?.()
  }
  return {checked}
}

// --- model-based testing with @xstate/graph -------------------------------------------------------------------------
// Any proven rule or chart presented as XState v5 ActorLogic (getInitialSnapshot, transition, getPersistedSnapshot,
// restoreSnapshot) so @xstate/graph generates test paths from the proven rule and drives the real app along them, and
// counterexample runs (Verdict.run or search()) turned into XState event sequences for getPathsFromEvents.
// Typed structurally without importing xstate or @xstate/graph, keeping both out of the package's runtime dependencies.

// eslint-disable-next-line @typescript-eslint/no-explicit-any
export type RuleOrChart = Rule<any, any, any, any, any, any, any, any> | Chart<any, any, any>
export type RuleEvent = {readonly type: string, readonly [k: string]: unknown}
export type RuleSnapshot<C extends Record<string, unknown> = Record<string, unknown>> = {
  readonly status: 'active'
  readonly output: undefined
  readonly error: undefined
  readonly context: C
  readonly value?: unknown
  readonly defaults?: Readonly<Record<string, number>>
  readonly history?: readonly Record<string, number>[]
  readonly last?: number
}
export type RulePersistedSnapshot = {
  readonly status: 'active'
  readonly output: undefined
  readonly error: undefined
  readonly context: Record<string, unknown>
  readonly value?: unknown
  readonly defaults?: Readonly<Record<string, number>>
  readonly history?: readonly Record<string, number>[]
  readonly last?: number
  readonly state: {
    readonly scalars: Record<string, number>
    readonly maps: Record<string, [number, number][]>
    readonly defaults?: Record<string, number>
    readonly history?: Record<string, number>[]
    readonly last?: number
  }
  readonly params: Record<string, number>
}
export type ToLogicOptions<S extends RuleSnapshot = RuleSnapshot, E extends RuleEvent = RuleEvent> = {
  params?: Record<string, Raw>
  events?: readonly E[] | ((snapshot: S) => readonly E[])
  maxValue?: number
  eventField?: string
  eventType?: string
  compileHelpers?: boolean
}
export type RuleLogic<S extends RuleSnapshot = RuleSnapshot, E extends RuleEvent = RuleEvent> = {
  readonly config: {readonly name: string}
  readonly getInitialSnapshot: (actorScope?: unknown, input?: unknown) => S
  readonly transition: (snapshot: S, event: E, actorScope?: unknown) => S
  readonly getPersistedSnapshot: (snapshot: S, options?: unknown) => RulePersistedSnapshot
  readonly restoreSnapshot: (persistedState: {readonly status: string, readonly output?: unknown, readonly error?: unknown, readonly [k: string]: unknown}, actorScope?: unknown) => S
  readonly events: (snapshot: S) => E[]
  readonly serializeState: (snapshot: S) => string
  readonly stateMatcher: (snapshot: S, stateKey: string) => boolean
  readonly options: {
    readonly events: (snapshot: S) => E[]
    readonly serializeState: (snapshot: S) => string
    readonly stateMatcher: (snapshot: S, stateKey: string) => boolean
  }
}
export type RuleRun = {readonly params?: Record<string, number>, readonly trace: readonly Record<string, unknown>[]}
export type RunToEventsOptions = {eventField?: string, eventType?: string}

type AnyRule = Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>
type InternalState = {
  rule: AnyRule
  machine: Machine
  state: State
  params: Record<string, number>
  rawParams: Record<string, Raw>
}
const snapshotInternals = new WeakMap<object, InternalState>()

const sortKeys = <T extends Record<string, unknown>>(o: T): T =>
  Object.fromEntries(Object.keys(o).sort().map(k => [k, o[k]])) as T

const canonicalValue = (v: unknown): string => {
  if (v === null || typeof v !== 'object') return JSON.stringify(v)
  if (v instanceof Map) {
    const entries = [...v.entries()].map(([k, val]) => [canonicalValue(k), canonicalValue(val)] as const)
      .sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0))
    return `{"$map":[${entries.map(([k, val]) => `[${k},${val}]`).join(',')}]}`
  }
  if (v instanceof Set) {
    const items = [...v].map(canonicalValue).sort()
    return `{"$set":[${items.join(',')}]}`
  }
  if (Array.isArray(v)) return `[${v.map(canonicalValue).join(',')}]`
  const o = v as Record<string, unknown>
  const keys = Object.keys(o).filter(k => o[k] !== undefined).sort()
  return `{${keys.map(k => `${JSON.stringify(k)}:${canonicalValue(o[k])}`).join(',')}}`
}

// Canonical, key-order-independent serialization of a snapshot (scalars, maps with defaults, and logs included).
export function serializeState(snapshot: unknown): string {
  if (snapshot && typeof snapshot === 'object') {
    const internal = snapshotInternals.get(snapshot)
    if (internal) {
      const {machine: m, state: st} = internal
      const scalars = sortKeys(st.scalars)
      const maps: Record<string, {default: number, entries: [number, number][]}> = {}
      for (const name of Object.keys(st.maps).sort()) {
        const dflt = st.defaults && Object.hasOwn(st.defaults, name) ? st.defaults[name]! : m.maps?.[name] ?? 0
        const entries = [...st.maps[name]!.entries()].filter(([, v]) => v !== dflt).sort((a, b) => a[0] - b[0])
        maps[name] = {default: dflt, entries}
      }
      const payload: Record<string, unknown> = {scalars, maps}
      if (st.history !== undefined) payload.history = st.history.map(rec => sortKeys(rec))
      if (st.last !== undefined) payload.last = st.last
      return canonicalValue(payload)
    }
  }
  return canonicalValue(snapshot)
}

const isPlainObject = (x: unknown): x is Record<string, unknown> =>
  typeof x === 'object' && x !== null && Object.getPrototypeOf(x) === Object.prototype

const isChoiceKind = (name: string, kind: Kind<unknown>): Choice<string> | undefined => {
  const val = kind.value(name)
  return val instanceof Choice ? val : undefined
}

function resolveEventField(r: AnyRule, isChart: boolean, explicit?: string): {field?: string, choices?: readonly string[]} {
  const inputs = r.parts.inputs
  if (explicit !== undefined) {
    const found = inputs.find(([n]) => n === explicit)
    if (!found) throw new Error(`${r.name}: eventField ${explicit} is not an input`)
    const ch = isChoiceKind(found[0], found[1])
    if (!ch) throw new Error(`${r.name}: eventField ${explicit} must be a oneOf input`)
    return {field: explicit, choices: ch.values}
  }
  const prefer = isChart ? ['event'] : ['event', 'op']
  for (const cand of prefer) {
    const found = inputs.find(([n]) => n === cand)
    const ch = found ? isChoiceKind(found[0], found[1]) : undefined
    if (ch) return {field: found![0], choices: ch.values}
  }
  for (const [n, k] of inputs) {
    const ch = isChoiceKind(n, k)
    if (ch) return {field: n, choices: ch.values}
  }
  return {}
}

// Strip default-valued entries and copy every mutable container so states reached by different paths match canonically.
function normalizeState(m: Machine, st: State): State {
  const maps: Record<string, Map<number, number>> = {}
  for (const name of Object.keys(st.maps)) {
    const dflt = st.defaults && Object.hasOwn(st.defaults, name) ? st.defaults[name]! : m.maps?.[name] ?? 0
    const clean = new Map<number, number>()
    for (const [k, v] of [...st.maps[name]!.entries()].sort((a, b) => a[0] - b[0])) {
      if (v !== dflt) clean.set(k, v)
    }
    maps[name] = clean
  }
  const defaults: Record<string, number> = {}
  for (const [name, d] of Object.entries(st.defaults ?? {})) {
    if (d !== (m.maps?.[name] ?? 0)) defaults[name] = d
  }
  return {
    scalars: {...st.scalars},
    maps,
    ...(Object.keys(defaults).length ? {defaults} : {}),
    ...(st.history ? {history: st.history.map(rec => ({...rec}))} : {}),
    ...(st.last !== undefined ? {last: st.last} : {}),
  }
}

// Scalar variable names that encode finite/categorical/tagged kinds (not unbounded counters).
function boundedScalarNames(r: AnyRule): Set<string> {
  const out = new Set<string>()
  const walk = (name: string, val: unknown): void => {
    if (val instanceof Choice || val instanceof Bool) { out.add(name); return }
    if (val instanceof Str) { out.add(name); out.add(`${name}$len`); val.patterns.forEach((_, i) => out.add(`${name}$like${i}`)); return }
    if (val instanceof Maybe) { out.add(`${name}$some`); walk(name, val.inner); return }
    if (val instanceof Variant) {
      out.add(name)
      for (const c of val.kind.names) {
        const fields = val.cases[c] as Record<string, unknown>
        for (const [f, fv] of Object.entries(fields)) walk(`${name}.${c}.${f}`, fv)
      }
      return
    }
    if (val instanceof FixedWord) { for (const limb of val.limbs) if (limb.e.op === 'var') out.add(limb.e.name); return }
    if (isPlainObject(val)) for (const [f, fv] of Object.entries(val)) walk(`${name}.${f}`, fv)
  }
  for (const [n, k] of r.kindsOfState()) walk(n, k.value(n))
  return out
}

// Upper bound declared on an upTo(k) kind, if any.
function upToBound(name: string, kind: Kind<unknown>): number | undefined {
  for (const cond of kind.assume(name)) {
    const c = cond.c
    if (c.op === '<=' && c.a.op === 'var' && c.a.name === name && c.b.op === 'const') return c.b.value
    if (c.op === '<' && c.a.op === 'var' && c.a.name === name && c.b.op === 'const') return c.b.value - 1
  }
  return undefined
}

function collectNumbers(v: unknown, out: number[]): void {
  if (typeof v === 'number' && Number.isSafeInteger(v)) { out.push(v); return }
  if (Array.isArray(v)) { for (const x of v) collectNumbers(x, out); return }
  if (isPlainObject(v)) for (const x of Object.values(v)) collectNumbers(x, out)
}

function collectStrings(v: unknown, out: Set<string>): void {
  if (typeof v === 'string') { out.add(v); return }
  if (Array.isArray(v)) { for (const x of v) collectStrings(x, out); return }
  if (isPlainObject(v)) for (const x of Object.values(v)) collectStrings(x, out)
}

function stateNumerics(st: State, bounded: Set<string>, plainMaps: Set<string>): number[] {
  const out: number[] = []
  for (const [k, v] of Object.entries(st.scalars)) if (!bounded.has(k)) out.push(v)
  for (const name of plainMaps) {
    const cells = st.maps[name]
    if (!cells) continue
    for (const [k, v] of cells) { out.push(k); out.push(v) }
  }
  return out
}

function decodedStateOf(r: AnyRule, m: Machine, st: State, chartRef?: Chart<Obj, Obj, Obj>): {context: Record<string, unknown>, value?: unknown, plainMaps: Set<string>} {
  const decoded = r.decode(st) as Record<string, unknown>
  const owned = new Set<string>()
  for (const [n, k] of r.kindsOfCells()) for (const part of k.vars(n)) owned.add(part)
  for (const [n, val] of Object.entries(decoded)) {
    if (!Array.isArray(val)) continue
    for (const mp of Object.keys(m.maps ?? {})) {
      if (mp === n || mp.startsWith(`${n}.`) || mp.startsWith(`${n}^`) || mp.startsWith(`${n}$`)) owned.add(mp)
    }
  }
  const plainMaps = new Set<string>()
  for (const name of Object.keys(m.maps ?? {}).sort()) {
    if (owned.has(name)) continue
    plainMaps.add(name)
    const entries = [...(st.maps[name]?.entries() ?? [])].sort((a, b) => a[0] - b[0])
    decoded[name] = Object.fromEntries(entries.map(([k, v]) => [String(k), v]))
  }
  let value: unknown
  if (chartRef) {
    const regions = chartRef.regionFields()
    const nest = (path: string): unknown => path.split('.').reduceRight<unknown>((acc, seg) => (acc === undefined ? seg : {[seg]: acc}), undefined)
    if (regions.length === 1 && regions[0]!.name === 'state') {
      const s = String(decoded[regions[0]!.field])
      value = s === STATELESS ? {} : nest(s)
    } else {
      value = Object.fromEntries(regions.map(reg => [reg.name, nest(String(decoded[reg.field]))]))
    }
  }
  return {context: sortKeys(decoded), value, plainMaps}
}

function emptyOfVal(val: unknown): Raw {
  if (val instanceof Choice) return val.values[0]!
  if (val instanceof Bool) return false
  if (val instanceof Maybe) return null
  if (val instanceof Str) return ''
  if (val instanceof Variant) {
    const k = val.kind.names[0]!, fields = val.cases[k] as Record<string, unknown>
    return {[val.kind.tagKey]: k, ...Object.fromEntries(Object.entries(fields).map(([f, fv]) => [f, emptyOfVal(fv)]))}
  }
  if (isPlainObject(val)) return Object.fromEntries(Object.entries(val).map(([f, fv]) => [f, emptyOfVal(fv)]))
  return 0
}

function enumerateVal(name: string, val: unknown, kind: Kind<unknown> | undefined, natEdges: number[], intEdges: number[], strings: string[], maxValue: number, ceiling: number): Raw[] {
  if (val instanceof Choice) return [...val.values]
  if (val instanceof Bool) return [false, true]
  if (val instanceof Term) {
    const cap = kind ? upToBound(name, kind) : undefined
    if (cap === undefined) return natEdges
    const out = new Set<number>()
    for (const x of natEdges) if (x <= cap) out.add(x)
    if (cap <= 4) for (let i = 0; i <= cap; i++) out.add(i)
    else if (cap <= ceiling) out.add(cap)
    return [...out].sort((a, b) => a - b)
  }
  if (val instanceof Int) return intEdges
  if (val instanceof Decimal) {
    const unit = 1 / 10 ** val.places
    const out = new Set<number>([0, unit, 1, maxValue].filter(x => x <= ceiling))
    return [...out].sort((a, b) => a - b)
  }
  if (val instanceof Maybe) return [null, ...enumerateVal(name, val.inner, undefined, natEdges, intEdges, strings, maxValue, ceiling)]
  if (val instanceof Str) {
    const pool = new Set<string>(['', ...strings])
    for (const p of val.patterns) { pool.add(p.replaceAll('*', '')); pool.add(p.replaceAll('*', 'a')) }
    if (pool.size === 1) pool.add('a')
    return [...pool]
  }
  if (val instanceof Variant) {
    const out: Raw[] = []
    for (const c of val.kind.names) {
      const fields = Object.entries(val.cases[c] as Record<string, unknown>)
      const combos = cartesian(fields.map(([f, fv]) => [f, enumerateVal(`${name}.${c}.${f}`, fv, undefined, natEdges, intEdges, strings, maxValue, ceiling)]))
      for (const combo of combos) out.push({[val.kind.tagKey]: c, ...combo})
    }
    return out
  }
  if (val instanceof FixedWord) {
    const out = new Set<number>([0, 1, maxValue])
    return [...out].sort((a, b) => a - b)
  }
  if (isPlainObject(val)) {
    const fields = Object.entries(val)
    return cartesian(fields.map(([f, fv]) => [f, enumerateVal(`${name}.${f}`, fv, undefined, natEdges, intEdges, strings, maxValue, ceiling)]))
  }
  return [emptyOfVal(val)]
}

function cartesian(fields: [string, Raw[]][]): Record<string, Raw>[] {
  let acc: Record<string, Raw>[] = [{}]
  for (const [k, vs] of fields) {
    const next: Record<string, Raw>[] = []
    for (const row of acc) for (const v of vs) next.push({...row, [k]: v})
    acc = next
  }
  return acc
}

// Present any proven gdp-wired rule or chart as XState v5 ActorLogic for @xstate/graph model-based testing.
// Steps through rule.interpreter() (never the in-place compiled runtime), so graph traversal branches safely.
export function toLogic<S extends RuleSnapshot = RuleSnapshot, E extends RuleEvent = RuleEvent>(
  ruleOrChart: RuleOrChart,
  opts: ToLogicOptions<S, E> = {},
): RuleLogic<S, E> {
  const isChart = ruleOrChart instanceof Chart
  const chartRef = isChart ? ruleOrChart as Chart<Obj, Obj, Obj> : undefined
  const r: AnyRule = isChart ? chartRef!.rule : ruleOrChart as AnyRule
  const m = r.machine
  const maxValue = opts.maxValue ?? 2
  if (!Number.isSafeInteger(maxValue) || maxValue < 0) throw new RangeError(`${r.name}: maxValue must be a natural, not ${String(maxValue)}`)
  const interp = r.interpreter({compileHelpers: opts.compileHelpers})
  const {field: eventField, choices: eventChoices} = resolveEventField(r, isChart, opts.eventField)
  const eventType = opts.eventType ?? 'step'
  const bounded = boundedScalarNames(r)
  const listNames = new Set(r.parts.lists.map(([n]) => n))
  const listLenNames = new Set([...listNames].map(n => `${n}_len`))
  const listCarriedMaps = new Set(r.parts.lists.flatMap(([n, k, fs]) => [...k.vars(n), ...Object.keys(fs).map(f => `${n}$${f}`)]))
  const plainCarriedMaps = (m.inputMaps ?? []).filter(mp => !listCarriedMaps.has(mp))
  const userInputs = r.parts.inputs.filter(([n]) => !listLenNames.has(n))
  const choicesSet = eventChoices ? new Set(eventChoices) : undefined

  const resolveParams = (given?: Record<string, Raw>): {ps: Record<string, number>, rawParams: Record<string, Raw>} => {
    const rawParams = given ?? opts.params ?? (r.parts.params.length === 0 ? {} : undefined)
    if (!rawParams) throw new Error(`${r.name}: give params ({params: {...}}) for a rule with params`)
    const ps = r.encodeParams(rawParams as never)
    if (m.pre && !evalC(m.pre, ps, {scalars: {}, maps: {}}, m)) throw new RangeError(`${r.name}: params fail the rule's precondition`)
    return {ps, rawParams}
  }

  const makeSnap = (st: State, ps: Record<string, number>, rawParams: Record<string, Raw>): S => {
    const clean = normalizeState(m, st)
    const {context, value} = decodedStateOf(r, m, clean, chartRef)
    const snap: RuleSnapshot = {
      status: 'active',
      output: undefined,
      error: undefined,
      context,
      ...(value !== undefined ? {value} : {}),
      ...(clean.defaults && Object.keys(clean.defaults).length ? {defaults: sortKeys(clean.defaults)} : {}),
      ...(clean.history !== undefined ? {history: clean.history.map(rec => sortKeys(rec))} : {}),
      ...(clean.last !== undefined ? {last: clean.last} : {}),
    }
    snapshotInternals.set(snap, {rule: r, machine: m, state: clean, params: ps, rawParams})
    return snap as S
  }

  const getInitialSnapshot = (_actorScope?: unknown, input?: unknown): S => {
    const override = isPlainObject(input) ? input as Record<string, Raw> : undefined
    const {ps, rawParams} = resolveParams(override)
    return makeSnap(interp.init(ps), ps, rawParams)
  }

  const transition = (snapshot: S, event: E): S => {
    const internal = snapshotInternals.get(snapshot)
    if (!internal) throw new Error(`${r.name}: snapshot was not created by this logic (restore it with restoreSnapshot)`)
    if (!event || typeof event !== 'object' || typeof event.type !== 'string' || event.type === 'xstate.init') return snapshot
    if (eventField) {
      if (!choicesSet!.has(event.type)) return snapshot
    } else if (event.type !== eventType) {
      return snapshot
    }
    const rawInput: Record<string, unknown> = {}
    for (const [n, k] of userInputs) {
      if (n === eventField) { rawInput[n] = event.type; continue }
      rawInput[n] = event[n] !== undefined ? event[n] : k.empty()
    }
    for (const [n] of r.parts.lists) rawInput[n] = event[n] !== undefined ? event[n] : []
    for (const mp of plainCarriedMaps) {
      const v = event[mp]
      if (v === undefined) rawInput[mp] = new Map<number, number>()
      else if (v instanceof Map || v instanceof Set || Array.isArray(v)) rawInput[mp] = v
      else if (isPlainObject(v)) rawInput[mp] = new Map(Object.entries(v).map(([k, x]) => [Number(k), Number(x)]))
      else return snapshot
    }
    let encoded: Request
    try { encoded = r.encodeInput(rawInput as never, r.parts.params.length ? internal.rawParams as never : undefined) }
    catch { return snapshot }
    try {
      if (!allowed(m, interp, internal.params, internal.state, encoded)) return snapshot
      const next = interp.step(internal.params, internal.state, encoded)
      return makeSnap(next, internal.params, internal.rawParams)
    } catch (e) {
      if (e instanceof RangeError) return snapshot
      throw e
    }
  }

  const getPersistedSnapshot = (snapshot: S): RulePersistedSnapshot => {
    const internal = snapshotInternals.get(snapshot)
    if (!internal) throw new Error(`${r.name}: snapshot was not created by this logic`)
    const st = internal.state
    return {
      status: 'active',
      output: undefined,
      error: undefined,
      context: snapshot.context,
      ...(snapshot.value !== undefined ? {value: snapshot.value} : {}),
      ...(snapshot.defaults !== undefined ? {defaults: snapshot.defaults} : {}),
      ...(snapshot.history !== undefined ? {history: snapshot.history} : {}),
      ...(snapshot.last !== undefined ? {last: snapshot.last} : {}),
      state: {
        scalars: {...st.scalars},
        maps: Object.fromEntries(Object.entries(st.maps).map(([n, cells]) => [n, [...cells.entries()].sort((a, b) => a[0] - b[0])])),
        ...(st.defaults && Object.keys(st.defaults).length ? {defaults: {...st.defaults}} : {}),
        ...(st.history !== undefined ? {history: st.history.map(rec => ({...rec}))} : {}),
        ...(st.last !== undefined ? {last: st.last} : {}),
      },
      params: {...internal.params},
    }
  }

  const restoreSnapshot = (persisted: {readonly status: string, readonly output?: unknown, readonly error?: unknown, readonly [k: string]: unknown}): S => {
    const existing = snapshotInternals.get(persisted)
    if (existing) return makeSnap(existing.state, existing.params, existing.rawParams)
    const rawState = persisted.state as RulePersistedSnapshot['state'] | undefined
    if (!rawState || typeof rawState !== 'object' || !rawState.scalars || !rawState.maps) {
      throw new Error(`${r.name}: persisted snapshot is missing raw state (produce it with getPersistedSnapshot)`)
    }
    const ps = (persisted.params ?? {}) as Record<string, number>
    const rawParams = Object.fromEntries(r.parts.params.map(([n, k]) => [n, k.decode(n, ps)]))
    const st: State = {
      scalars: {...rawState.scalars},
      maps: Object.fromEntries(Object.entries(rawState.maps).map(([n, entries]) => [n, new Map(entries)])),
      ...(rawState.defaults ? {defaults: {...rawState.defaults}} : {}),
      ...(rawState.history ? {history: rawState.history.map(rec => ({...rec}))} : {}),
      ...(rawState.last !== undefined ? {last: rawState.last} : {}),
    }
    return makeSnap(st, {...ps}, rawParams)
  }

  // Default event enumerator: all oneOf choices and booleans; for naturals, the small edge set (0, 1, state/param
  // values, maxValue). Stops expanding states whose unbounded numeric values or log length exceed the ceiling so
  // graph traversal on unbounded rules terminates cleanly.
  const defaultEvents = (snapshot: S): E[] => {
    const internal = snapshotInternals.get(snapshot)
    if (!internal) return []
    const {state: st, params: ps, rawParams} = internal
    const {plainMaps} = decodedStateOf(r, m, st, chartRef)
    const initSt = normalizeState(m, interp.init(ps))
    const paramNums: number[] = []
    collectNumbers(rawParams, paramNums)
    const initStateNums = stateNumerics(initSt, bounded, plainMaps)
    const stateCeiling = Math.max(maxValue, ...initStateNums.map(x => Math.abs(x)))
    const curNums = stateNumerics(st, bounded, plainMaps)
    if (curNums.some(x => Math.abs(x) > stateCeiling)) return []
    if (st.history !== undefined && st.history.length >= Math.max(1, maxValue)) return []

    const ceiling = Math.max(stateCeiling, ...paramNums.map(x => Math.abs(x)))
    const natSet = new Set<number>([0])
    if (maxValue >= 1) natSet.add(1)
    natSet.add(maxValue)
    const decodedNums: number[] = [...paramNums]
    collectNumbers(snapshot.context, decodedNums)
    for (const x of [...curNums, ...decodedNums]) if (x >= 0 && x <= ceiling) natSet.add(x)
    const natEdges = [...natSet].sort((a, b) => a - b)

    const intSet = new Set<number>([0, maxValue, -maxValue])
    if (maxValue >= 1) { intSet.add(1); intSet.add(-1) }
    for (const x of decodedNums) if (Math.abs(x) <= ceiling) intSet.add(x)
    const intEdges = [...intSet].sort((a, b) => a - b)

    const strSet = new Set<string>()
    collectStrings(rawParams, strSet)
    collectStrings(snapshot.context, strSet)
    const strings = [...strSet].sort()

    const fieldDomains: [string, Raw[]][] = userInputs.map(([n, k]) => [
      n,
      enumerateVal(n, k.value(n), k, natEdges, intEdges, strings, maxValue, ceiling),
    ])
    for (const [n, k] of r.parts.lists) {
      const sampleItem = enumerateVal(n, k.value(n), k, natEdges, intEdges, strings, maxValue, ceiling)[0] ?? k.empty()
      fieldDomains.push([n, [[], [sampleItem]]])
    }
    for (const mp of plainCarriedMaps) fieldDomains.push([mp, [[], [0]]])

    return cartesian(fieldDomains).map(combo => {
      if (eventField) {
        const {[eventField]: t, ...rest} = combo
        return {type: typeof t === 'string' ? t : '', ...rest} as E
      }
      return {type: eventType, ...combo} as E
    })
  }

  const events = (snapshot: S): E[] => {
    if (opts.events === undefined) return defaultEvents(snapshot)
    return typeof opts.events === 'function' ? [...opts.events(snapshot)] : [...opts.events]
  }

  const stateMatcher = (snapshot: S, stateKey: string): boolean => {
    if (stateKey === '*') return true
    if (!chartRef) return false
    const regions = chartRef.regionFields()
    if (regions.length === 1 && regions[0]!.name === 'state') {
      const raw = snapshot.context[regions[0]!.field]
      const cur = typeof raw === 'string' ? raw : ''
      return cur === stateKey || cur.startsWith(`${stateKey}.`)
    }
    return regions.some(reg => {
      const raw = snapshot.context[reg.field]
      const cur = `${reg.name}.${typeof raw === 'string' ? raw : ''}`
      return cur === stateKey || cur.startsWith(`${stateKey}.`)
    })
  }

  const options = {events, serializeState: (s: S) => serializeState(s), stateMatcher}
  return {
    config: {name: r.name},
    getInitialSnapshot,
    transition,
    getPersistedSnapshot,
    restoreSnapshot,
    events,
    serializeState: options.serializeState,
    stateMatcher,
    options,
  }
}

// Convert a verdict's or search()'s counterexample run into XState event objects ready for model.getPathsFromEvents(events).
export function runToEvents(
  ruleOrChart: RuleOrChart,
  run: RuleRun | readonly Record<string, unknown>[],
  opts: RunToEventsOptions = {},
): RuleEvent[] {
  const isChart = ruleOrChart instanceof Chart
  const r: AnyRule = isChart ? ruleOrChart.rule : ruleOrChart as AnyRule
  const m = r.machine
  const trace = Array.isArray(run) ? (run as readonly Record<string, unknown>[]) : (run as RuleRun | undefined)?.trace
  if (!Array.isArray(trace)) throw new Error(`${r.name}: runToEvents expects a verdict/search run ({trace: [...]}) or a trace array`)
  const {field: eventField} = resolveEventField(r, isChart, opts.eventField)
  const eventType = opts.eventType ?? 'step'
  const listNames = new Set(r.parts.lists.map(([n]) => n))
  const listLenNames = new Set([...listNames].map(n => `${n}_len`))
  const listCarriedMaps = new Set(r.parts.lists.flatMap(([n, k, fs]) => [...k.vars(n), ...Object.keys(fs).map(f => `${n}$${f}`)]))
  const plainCarriedMaps = (m.inputMaps ?? []).filter(mp => !listCarriedMaps.has(mp))
  const userInputs = r.parts.inputs.filter(([n]) => !listLenNames.has(n))

  const readCell = (rawMap: unknown, key: number): number => {
    if (rawMap instanceof Map) return Number(rawMap.get(key) ?? 0)
    if (rawMap && typeof rawMap === 'object') return Number((rawMap as Record<string, unknown>)[String(key)] ?? 0)
    return 0
  }

  return trace.map(step => {
    const vars: Record<string, number> = {}
    for (const [k, v] of Object.entries(step)) if (typeof v === 'number') vars[k] = v
    const decoded: Record<string, unknown> = {}
    for (const [n, k] of userInputs) {
      const val = k.value(n)
      if (val instanceof Choice && typeof step[n] === 'string') { decoded[n] = step[n]; continue }
      if (val instanceof Str && typeof step[n] === 'string') { decoded[n] = step[n]; continue }
      for (const part of k.vars(n)) if (vars[part] === undefined) vars[part] = 0
      try { decoded[n] = k.decode(n, vars) }
      catch (e) {
        if (val instanceof Str) decoded[n] = `s${vars[n] ?? 0}`
        else throw e
      }
    }
    for (const [n, k] of r.parts.lists) {
      const len = Number(step[`${n}_len`] ?? 0)
      const parts = k.vars(n)
      decoded[n] = Array.from({length: len}, (_, i) => k.decode(n, Object.fromEntries(parts.map(p => [p, readCell(step[p], i)]))))
    }
    for (const mp of plainCarriedMaps) {
      const rawMap = step[mp]
      if (rawMap instanceof Map) {
        decoded[mp] = Object.fromEntries([...rawMap.entries()].sort((a, b) => Number(a[0]) - Number(b[0])).map(([k, v]) => [String(k), Number(v)]))
      } else if (rawMap && typeof rawMap === 'object') {
        decoded[mp] = Object.fromEntries(Object.entries(rawMap as Record<string, unknown>).sort((a, b) => Number(a[0]) - Number(b[0])).map(([k, v]) => [k, Number(v)]))
      }
    }
    if (eventField) {
      const {[eventField]: t, ...rest} = decoded
      return {type: String(t), ...rest}
    }
    return {type: eventType, ...decoded}
  })
}
