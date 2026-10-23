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
// What a chart can't run the same way is refused when the chart is built, with the reason: a parallel state below the
// root, eventless (`always`) and delayed (`after`) transitions, invoked actors and done events, wildcard events, several
// targets at once, inline guards and actions, entry and exit actions that write the context, two regions writing the
// context on one event (XState runs their actions one after another; a chart's regions write in one step), and a
// shallow history over nested states. So is every key it doesn't read, rather than dropped: a node or transition key
// outside the lists below (KEYS), an initial transition with actions, an event XState raises itself (done, error, init).
// An XState v4 machine reads the same, its `cond` the guard v5 calls `guard` (a name, or {type, ...params}); v4's
// `in`, `strict`, `activities` and eventless `''` are refused with the rest. Each XState ignores the other's guard key,
// so a v5 machine with `cond` or a v4 one with `guard` is refused (a plain config is read by the key it uses).
import {type Kind, Choice, type Cond, bool, int} from './dsl.ts'
import {type Chart, type StateNode, chart} from './chart.ts'

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
}

type Info = {node: XNode, segs: string[], parent?: Info, history?: {deep: boolean}}
// The keys read, and those that change nothing a run shows (descriptions, metadata, types, a final state's output, v4's
// action-order flags, which order no write to the context: those a transition makes run in order either way; v5's
// `reenter` and v4's `internal`, which change only which entry and exit actions run, and those write no context here).
// Any other is refused, by name, rather than dropped; some with the reason.
const KEYS = {
  node: new Set(['id', 'type', 'history', 'initial', 'target', 'states', 'on', 'entry', 'exit', 'description', 'meta', 'tags', 'output', 'data']),
  root: new Set(['context', 'version', 'types', 'schemas', 'schema', 'tsTypes', 'predictableActionArguments', 'preserveActionOrder']),
  transition: new Set(['target', 'guard', 'cond', 'actions', 'reenter', 'internal', 'description', 'meta']),
}
const WHY: Record<string, string> = {
  always: '`always` has no chart counterpart', after: '`after` has no chart counterpart', invoke: '`invoke` has no chart counterpart', onDone: '`onDone` has no chart counterpart',
  onError: '`onError` has no chart counterpart', activities: "v4's `activities` have no chart counterpart", strict: "v4's `strict` (an event no state takes throws) has no chart counterpart",
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
    const v4params = (o: Obj) => { const {type: _t, ...rest} = o; void _t; return Object.keys(rest).length ? rest : undefined }
    const [n, params] = typeof g === 'string' ? [g, undefined] : typeof g === 'object' && g && typeof (g as {type?: unknown}).type === 'string' ? [(g as {type: string}).type, v4 ? v4params(g as Obj) : (g as {params?: unknown}).params] : [undefined, undefined]
    if (n === undefined) return refuse(where, `an inline guard${typeof g === 'function' && (g as {type?: string}).type ? ` (${(g as {type?: string}).type})` : ''}: name it in setup({guards}) and give its condition in guards`)
    const f = opts.guards?.[n] ?? refuse(where, `the guard ${n}: give its condition in guards`)
    return env => f(env, params)
  }
  const actionsOf = (where: string, as: XAction[]): ((env: Obj) => Obj)[] => as.flatMap(a => {
    const [n, params] = typeof a === 'string' ? [a, undefined] : typeof a === 'object' && a && typeof a.type === 'string' ? [a.type, a.params] : [undefined, undefined]
    if (n === undefined) return refuse(where, `an inline action${typeof a === 'function' && (a as {type?: string}).type ? ` (${(a as {type?: string}).type})` : ''}: name it in setup({actions}) and give the context it writes in actions`)
    if (!opts.actions || !(n in opts.actions)) return refuse(where, `the action ${n}: give the context it writes in actions (null if it writes none)`)
    const f = opts.actions[n]
    return f ? [(env: Obj) => f(env, params)] : []
  })
  for (const i of infos) for (const k of ['entry', 'exit'] as const) if (actionsOf(pathOf(i), list(i.node[k])).length) refuse(pathOf(i), `${k} actions that write the context (a chart writes the context on transitions only)`)
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
  let c = chart(name).params((opts.params ?? {}) as never).inputs((opts.inputs ?? {}) as never).context(contextOf(root, opts.context, refuse) as never) as unknown as Chart<Obj, Obj, Obj>
  if (parallel) {
    for (const r of top) if (!infos.some(x => x.parent === r && x.node.type !== 'history')) refuse(pathOf(r), 'a region with no states of its own')
    c = c.regions(Object.fromEntries(top.map(r => [r.segs[0]!, nodeOf(r)])))
  } else c = c.states(nodeOf(infos[0]!).states ?? refuse('', 'no states'), root.initial ? {initial: root.initial} : {})
  if (opts.events) c = c.events(...opts.events)

  // The transitions, in document order (the chart takes the most specific source first, then the first declared, as
  // XState does).
  const writers = new Map<string, Set<string>>()
  for (const i of infos) for (const [event, spec] of Object.entries(i.node.on ?? {})) {
    const where = `${pathOf(i) || 'the root'} on ${event || '""'}`
    if (event.includes('*')) refuse(where, 'a wildcard event')
    if (raised(event)) refuse(where, event ? 'an event XState raises itself (a done, error or init event)' : "v4's eventless transition (`''`)")
    if (spec === undefined) refuse(where, 'a forbidden event (an undefined transition)')
    for (const t of list(spec as XTransition | XTransition[])) {
      if (t === null || (typeof t !== 'string' && typeof t !== 'object')) refuse(where, `a transition given as ${typeof t === 'function' ? 'a function' : JSON.stringify(t)}`)
      const o = typeof t === 'string' ? {target: t} : t, targets = list(o.target)
      keyCheck(o, KEYS.transition, what => refuse(where, what))
      if (o.guard !== undefined && o.cond !== undefined) refuse(where, 'both `guard` and v4\'s `cond`')
      // (each XState reads its own and takes a transition with the other's unguarded: refused, not taken so)
      if (o.cond !== undefined && version === 5) refuse(where, 'v4\'s `cond` in an XState v5 machine, which doesn\'t read it (it takes this transition unguarded): name the guard in `guard`')
      if (o.guard !== undefined && version === 4) refuse(where, 'v5\'s `guard` in an XState v4 machine, which doesn\'t read it (it takes this transition unguarded): name the guard in `cond`')
      if (targets.length > 1) refuse(where, 'several targets at once')
      const to = targets[0] === undefined ? undefined : resolve(i, targets[0])
      const set = composed(actionsOf(where, list(o.actions))), when = o.cond !== undefined ? guardOf(where, o.cond, true) : guardOf(where, o.guard)
      // Where it applies: its state; for the root, every top state but a final one (XState stops there), or in a
      // parallel machine the region its target is in (the first region, for one with no target).
      const from = i.segs.length ? pathOf(i) : parallel ? (to ? to.to.segs[0]! : top[0]!.segs[0]!) : top.filter(x => x.node.type !== 'final' && x.node.type !== 'history').map(pathOf)
      if (set) { const region = parallel ? String(list(from)[0]).split('.')[0]! : 'state'; writers.set(event, (writers.get(event) ?? new Set()).add(region)) }
      c = c.on(event, {from, ...(to ? {to: pathOf(to.to), fresh: !to.viaHistory} : {}), ...(when ? {when} : {}), ...(set ? {set: set as never} : {})})
    }
  }
  for (const [event, regions] of writers) if (regions.size > 1) refuse(`on ${event}`, `regions ${[...regions].join(' and ')} both write the context (XState runs their actions one after another)`)
  return c
}

function contextOf(root: XNode, given: Bridge['context'], refuse: (where: string, what: string) => never): Record<string, number | {kind: Kind<unknown>, init: unknown}> {
  const out: Record<string, number | {kind: Kind<unknown>, init: unknown}> = {}
  if (root.context !== undefined && typeof root.context !== 'object') { if (!given) refuse('', 'a context computed by a function: give its kinds in context'); return {...given} }
  for (const [k, v] of Object.entries((root.context ?? {}) as Obj)) {
    if (given && k in given) continue
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
  opts: {runs?: number, depth?: number, seed?: number, params?: Obj, payload?: (event: string, rand: (n: number) => number) => Obj} = {}): {checked: number, failure?: string} {
  const root = configOf(machine), events: string[] = []
  const walk = (n: XNode) => { for (const e of Object.keys(n.on ?? {})) if (!events.includes(e)) events.push(e); Object.values(n.states ?? {}).forEach(walk) }
  walk(root)
  const r = c.rule, g = r.compiled(), ps = r.encodeParams((opts.params ?? {}) as never)
  // dsl.ts's generator: the high bits of a linear congruence (the low ones repeat with a short period)
  let x = opts.seed ?? 1
  const rand = (k: number) => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * k) }
  const valueOf = (d: Obj): unknown => {
    const nest = (path: string): unknown => path.split('.').reduceRight<unknown>((acc, seg) => (acc === undefined ? seg : {[seg]: acc}), undefined)
    if (root.type === 'parallel') return Object.fromEntries(Object.keys(root.states ?? {}).filter(k => root.states![k]!.type !== 'history').map(k => [k, nest(String(d[k]))]))
    return nest(String(d.state))
  }
  const contextKeys = Object.keys((root.context && typeof root.context === 'object' ? root.context : {}) as Obj)
  let checked = 0
  for (let run = 0; run < (opts.runs ?? 100); run++) {
    const actor = createActor(machine as never).start()
    let st = g.init(ps)
    const sent: string[] = []
    for (let d = 0; d < (opts.depth ?? 12); d++) {
      const type = events[rand(events.length)]!, payload = opts.payload?.(type, rand) ?? {}
      sent.push(Object.keys(payload).length ? `${type}${JSON.stringify(payload)}` : type)
      actor.send({type, ...payload} as never)
      st = g.step(ps, st, r.encodeInput({event: type, ...payload} as never))
      const snap = actor.getSnapshot() as {value: unknown, context?: Obj}, d2 = r.decode(st), want = valueOf(d2)
      if (canonical(snap.value) !== canonical(want)) return {checked, failure: `after ${sent.join(', ')}: XState is in ${JSON.stringify(snap.value)}, the chart in ${JSON.stringify(want)}`}
      for (const k of contextKeys) if (JSON.stringify(snap.context?.[k]) !== JSON.stringify(d2[k])) return {checked, failure: `after ${sent.join(', ')}: XState's ${k} is ${JSON.stringify(snap.context?.[k])}, the chart's ${JSON.stringify(d2[k])}`}
      checked++
    }
  }
  return {checked}
}
