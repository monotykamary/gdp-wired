// Systems (research/distributed/DESIGN.md): handlers, their stores and message pools, and the environment, as one rule,
// so every prover takes a distributed system as it takes one process. Each combinator returns a plain Machine (or, from
// `system`, a Rule over it), and nothing here is trusted: a proof is about the rule built, and what it assumes of the
// network and the stores is the environment models named in it (`models`), each stating what it assumes.
//   system(name, parts)        one part steps per request (`act` picks which); maps of one name are one store, shared;
//                              a part with an `id` is every process of it at once: each scalar a map keyed by the
//                              process (a request's own locals), the request's process its input `id`
//   isolation(m, level)        a handler's one atomic step run as a transaction at an isolation level
//   delivery(m, pool, ...)     a handler's request taken from a message pool, exactly once or at least once
//   client(pool, fields)       the environment's sends: any message, at a fresh id
//   expiry(cells)              a store's key vanishes at any step: a TTL lapsed, an eviction
//   time()                     the true time `now`, rising by any amount at a step of the environment's
//   clocked(m, at, skew)       m reads its node's clock as the input `at`, within `skew` of the true time
//   expires(cells, at)         a store's key vanishes once the time has passed its expiry `at`, never before
//   asRule(m)                  a Machine as a Rule, for the provers' entries (proveRule, proveSteps)
// The handlers are any rules: extracted by the readers (a step of one process, its maps the stores it reads and writes)
// or written; a handler that awaits other services between its reads and writes is several steps (a `pc` scalar), the
// form `isolation` gives an atomic one.
import {type C, type E, type Law, type Machine, type MapUpdate, all, any, atMost, get, ite, n, not, plus, same, x} from './machine.ts'
import {type StepLaw, type Subst, substC, substE} from '../kernel/kernel.ts'
import {Cond, type Kind, type Rule, Term, nat, oneOf, rule} from './dsl.ts'
import {interpret, type Request} from './machine.ts'
import {allowed, watch} from './watch.ts'

// An environment model: what it assumes, and the stack's behaviour it was checked against (research/distributed/
// DESIGN.md, section 2: the documentation quoted; research/distributed/envcheck.py: each claim run on the stack).
export type Model = {name: string, assumes: string, checked: string}
const models = new WeakMap<object, Model[]>()
const modelled = (m: Machine, ...ms: Model[]): Machine => { models.set(m, [...(models.get(m) ?? []), ...ms]); return m }
// m made from `from`: the models it assumes, and the scalars it keeps shared (`sharedOf`), carried over.
const from = (m: Machine, src: Machine | Rule, ...ms: Model[]): Machine => { const sh = sharedOf.get(machineOf(src)); if (sh) sharedOf.set(m, sh); return modelled(m, ...(models.get(src) ?? []), ...ms) }
// m, stated to assume these models (a copy: what a written rule's inputs or steps assume of its environment).
export const assuming = (m: Machine | Rule, ...ms: Model[]): Machine => from({...machineOf(m)}, m, ...ms)
// The models a machine, or a system's rule, assumes.
export const modelsOf = (m: Machine | Rule): Model[] => models.get(m) ?? []

const mapValues = <A, B>(o: Record<string, A> | undefined, f: (a: A, k: string) => B): Record<string, B> => Object.fromEntries(Object.entries(o ?? {}).map(([k, a]) => [k, f(a, k)]))
// m's terms with scalars replaced (`vars`) and flags renamed.
function mapper(m: Machine, vars: Record<string, E>, flag: (f: string) => string) {
  const s: Subst = {vars, maps: {}, flags: mapValues(m.step.flags, (_c, f) => ({op: 'flag', name: flag(f)}) as C)}
  const E = (e: E) => substE(e, s), C = (c: C) => substC(c, s)
  return {E, C, W: (w: MapUpdate): MapUpdate => ('each' in w ? {each: w.each, value: E(w.value)} : {key: E(w.key), value: E(w.value)})}
}
const machineOf = (r: Machine | Rule): Machine => ('machine' in r ? r.machine : r)
// The scalars a machine reads that are the system's, not a process's: the true time, which lift keeps shared.
const sharedOf = new WeakMap<Machine, string[]>()
const plain = (m: Machine, what: string) => { if (m.history || m.sums || m.inputMaps?.length) throw new Error(`${what}: ${m.name} has a history, sums or carried maps (not taken here)`) }

// --- one process, every process ------------------------------------------------------------------------------------

// Every process of m at once: each scalar but `shared` a map keyed by the process `id` (an input), read and written at
// the request's process; m's maps stay as they are, shared. A process starts where m starts (a constant: a map's cells
// all start at one value).
export function lift(m: Machine, id: string, given: string[] = []): Machine {
  plain(m, 'lift')
  const shared = [...given, ...(sharedOf.get(m) ?? [])]
  const locals = Object.keys(m.state).filter(s => !shared.includes(s))
  for (const s of locals) {
    if (m.state[s]!.op !== 'const') throw new Error(`lift: ${m.name}'s ${s} starts at a term of the params; a process starts at constants`)
    if (s in (m.maps ?? {})) throw new Error(`lift: ${m.name}'s ${s} is a scalar and a map`)
  }
  // (an input named `id` is the process's own id, which m may read: a token, an owner)
  if ([...m.params, ...Object.keys(m.state), ...Object.keys(m.maps ?? {})].includes(id)) throw new Error(`lift: ${id} is already a name of ${m.name}`)
  const {E, C, W} = mapper(m, Object.fromEntries(locals.map(s => [s, get(s, x(id))])), f => f)
  const kept = (s: string) => !locals.includes(s)
  return {
    ...m, inputs: [...new Set([...m.inputs, id])],
    state: Object.fromEntries(Object.entries(m.state).filter(([s]) => kept(s))),
    maps: {...m.maps, ...Object.fromEntries(locals.map(s => [s, (m.state[s] as {value: number}).value]))},
    step: {
      flags: mapValues(m.step.flags, C),
      state: Object.fromEntries(Object.entries(m.step.state ?? {}).filter(([s]) => kept(s)).map(([s, e]) => [s, E(e)])),
      maps: {...mapValues(m.step.maps, W), ...Object.fromEntries(locals.filter(s => m.step.state?.[s]).map(s => [s, {key: x(id), value: E(m.step.state![s]!)}]))},
    },
    ...(m.assume ? {assume: C(m.assume)} : {}),
  }
}

// --- the system ----------------------------------------------------------------------------------------------------

export type Part = Machine | Rule | {rule: Machine | Rule, id?: string, shared?: string[]}
// The parts interleaved: at each request the part `act` names steps, the others keep their state. Params, inputs and
// stores (maps, scalars of parts without an id) are shared by name; each part's flags are its own (named part$flag),
// and its assumption is about its own steps. `kinds`: the inputs' kinds (by default naturals), for the runs' draws.
export function system(name: string, parts: Record<string, Part>, opts: {act?: string, kinds?: Record<string, Kind<unknown>>} = {}): Rule {
  const act = opts.act ?? 'act', names = Object.keys(parts)
  if (!names.length) throw new Error('system: no parts')
  const ps = names.map((p, i) => {
    const part = parts[p]!, spec = 'rule' in part && !('step' in part) && !('machine' in part) ? part : {rule: part as Machine | Rule}
    const given = machineOf(spec.rule)
    plain(given, 'system')
    const m = spec.id ? lift(given, spec.id, spec.shared) : given
    return {p, m, assumed: models.get(spec.rule) ?? models.get(given) ?? [], on: same(x(act), n(i)), ...mapper(m, {}, f => `${p}$${f}`)}
  })
  const scalars: Record<string, E> = {}, maps: Record<string, number> = {}
  for (const {m} of ps) {
    for (const [s, e] of Object.entries(m.state)) { if (s in scalars && JSON.stringify(scalars[s]) !== JSON.stringify(e)) throw new Error(`system: ${s} starts differently in two parts`); scalars[s] = e }
    for (const [mp, v] of Object.entries(m.maps ?? {})) { if (mp in maps && maps[mp] !== v) throw new Error(`system: store ${mp} starts at ${maps[mp]} and ${v}`); maps[mp] = v }
  }
  const params = [...new Set(ps.flatMap(q => q.m.params))], inputs = [...new Set([act, ...ps.flatMap(q => q.m.inputs)])]
  const clash = inputs.find(i => i in scalars || i in maps || params.includes(i))
  if (clash) throw new Error(`system: ${clash} is an input and a store or a param`)
  // A scalar: the active part's update, else kept. A map: the active part's write; at every key where some part writes at
  // every key, else at the active part's key (the last writer's, its value kept, where no writer is active).
  const state: Record<string, E> = {}, writes: Record<string, MapUpdate> = {}
  for (const s of Object.keys(scalars)) {
    const by = ps.filter(q => q.m.step.state?.[s])
    if (by.length) state[s] = by.reduceRight<E>((acc, q) => ite(q.on, q.E(q.m.step.state![s]!), acc), x(s))
  }
  for (const mp of Object.keys(maps)) {
    const by = ps.filter(q => q.m.step.maps?.[mp]).map(q => ({q, w: q.W(q.m.step.maps![mp]!)}))
    if (!by.length) continue
    if (by.some(b => 'each' in b.w)) {
      const k = `k$${mp}`
      const at = (w: MapUpdate): E => ('each' in w ? substE(w.value, {vars: {[w.each]: x(k)}, maps: {}, flags: {}}) : ite(same(x(k), w.key), w.value, get(mp, x(k))))
      writes[mp] = {each: k, value: by.reduceRight<E>((acc, {q, w}) => ite(q.on, at(w), acc), get(mp, x(k)))}
    } else {
      const point = by as {q: typeof ps[number], w: {key: E, value: E}}[]
      const key = point.slice(0, -1).reduceRight<E>((acc, {q, w}) => ite(q.on, w.key, acc), point.at(-1)!.w.key)
      writes[mp] = {key, value: point.reduceRight<E>((acc, {q, w}) => ite(q.on, w.value, acc), get(mp, key))}
    }
  }
  const flags = Object.assign({}, ...ps.map(q => Object.fromEntries(Object.entries(q.m.step.flags ?? {}).map(([f, c]) => [`${q.p}$${f}`, q.C(c)]))))
  const assume = ps.filter(q => q.m.assume).map(q => any(not(q.on), q.C(q.m.assume!)))
  const pres = ps.map(q => q.m.pre).filter((c): c is C => !!c)
  const m: Machine = {
    name, params, inputs, state: scalars, maps,
    step: {flags, state, maps: writes},
    ...(assume.length ? {assume: all(...assume)} : {}),
    ...(pres.length ? {pre: all(...pres)} : {}),
  }
  const ms = [...new Map(ps.flatMap(q => q.assumed).map(md => [md.name, md])).values()]
  const r = asRule(m, {[act]: oneOf(...names), ...opts.kinds})
  models.set(r, ms)
  return r
}

// --- a Machine as a Rule --------------------------------------------------------------------------------------------

// The same rule through the builders (its terms as they are), so proveRule, proveSteps and the runs take it. Every
// name is a natural unless `kinds` says otherwise (a choice, for the runs' draws); division by constants is kept.
export function asRule(m: Machine, kinds: Record<string, Kind<unknown>> = {}): Rule {
  plain(m, 'asRule')
  const ks = Object.keys(m.fns ?? {}).map(f => { const d = /^(?:div|mod)\$(\d+)$/.exec(f); if (!d) throw new Error(`asRule: ${m.name} reads ${f}, a function other than division by a constant`); return Number(d[1]) })
  const kindOf = (v: string) => kinds[v] ?? nat
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  let r: any = rule(m.name)
  if (m.params.length) r = r.params(Object.fromEntries(m.params.map(p => [p, kindOf(p)])))
  if (m.inputs.length) r = r.inputs(Object.fromEntries(m.inputs.map(i => [i, kindOf(i)])))
  // (a state variable given an integer's kind, x beside x$neg as Int keeps one, is that integer to the laws: both start at
  // constants)
  const ints = Object.keys(m.state).filter(v => kinds[v] && `${v}$neg` in m.state && m.state[v]!.op === 'const' && m.state[`${v}$neg`]!.op === 'const')
  const at = (v: string) => (m.state[v] as {value: number}).value
  r = r.state({...mapValues(Object.fromEntries(Object.entries(m.state).filter(([v]) => !ints.some(i => v === i || v === `${i}$neg`))), e => (e.op === 'const' ? e.value : () => new Term(e))),
    ...Object.fromEntries(ints.map(v => [v, kinds[v]!.from(at(v) - at(`${v}$neg`) as never)]))})
  // (a map given a kind of cells, its parts as the machine has them (m.has, m.value), is those cells to the laws)
  const cells = Object.entries(kinds).filter(([n, k]) => k.vars(n).length > 1 && k.vars(n).every(p => p in (m.maps ?? {})))
  const parts = new Set(cells.flatMap(([n, k]) => k.vars(n)))
  const plainMaps = Object.fromEntries(Object.entries(m.maps ?? {}).filter(([n]) => !parts.has(n)))
  if (Object.keys(plainMaps).length || cells.length) r = r.maps({...plainMaps, ...Object.fromEntries(cells.map(([n, k]) => [n, k.from(k.decode(n, Object.fromEntries(k.vars(n).map(p => [p, m.maps![p]!]))) as never)]))})
  if (m.step.flags && Object.keys(m.step.flags).length) r = r.flags(() => mapValues(m.step.flags, c => new Cond(c)))
  r = r.step(() => ({...mapValues(m.step.state, e => new Term(e)), ...mapValues(m.step.maps, (w, map) => ({map, ...w}))}))
  if (m.pre) r = r.pre(() => new Cond(m.pre!))
  if (m.assume) r = r.assume(() => new Cond(m.assume!))
  if (ks.length) r = r.dividesBy(...ks)
  return r as Rule
}

// --- isolation ------------------------------------------------------------------------------------------------------

export type Level = 'atomic' | 'read committed' | 'snapshot'
export const ISOLATION: Record<Level, Model> = {
  'atomic': {name: 'atomic', assumes: 'the handler runs as one step: no other step sees it half done',
    checked: 'PostgreSQL SERIALIZABLE (13.2.3), SELECT ... FOR UPDATE, UPDATE ... SET x = x + k; a Redis Lua script; asyncio code whose awaits never suspend'},
  'read committed': {name: 'read committed', assumes: 'each read of a store sees the latest committed value at its own step; the writes become visible together at commit; nothing is re-read at commit',
    checked: 'PostgreSQL READ COMMITTED (13.2.1): the lost update, envcheck.py'},
  'snapshot': {name: 'snapshot', assumes: 'every read sees the store as it was at the transaction start; a commit is refused (aborted$) when a cell it writes changed since then (first committer wins); writes to different cells never conflict (write skew allowed)',
    checked: 'PostgreSQL REPEATABLE READ (13.2.2): the refused commit and the write skew, envcheck.py'},
}
// A request's write of a cell, as it is and where it writes at all: an `if` whose branch is the cell itself is no write.
function writesWhen(v: E, cell: E): C | true | false {
  if (JSON.stringify(v) === JSON.stringify(cell)) return false
  if (v.op !== 'if') return true
  const a = writesWhen(v.then, cell), b = writesWhen(v.else, cell)
  if (a === true && b === true) return true
  const side = (w: C | boolean, c: C): C | false => (w === false ? false : w === true ? c : all(c, w))
  const xs = [side(a, v.c), side(b, not(v.c))].filter((c): c is C => c !== false)
  return xs.length ? any(...xs) : false
}
// m's one step (a request's) as a transaction of several: `pc$` 0 begins it (the request's inputs kept as in$<input>),
// then the reads (read committed: each store read site at its own step, inner ones first, as rd$<i>, a record's parts at one key one step; snapshot: all at
// the begin), then the commit, which computes m's step from what was read and writes it (snapshot: unless a cell it
// writes moved since the begin, aborted$ then 1), then done. m's scalars are the request's own (a result, a flag); its
// maps are the stores. 'atomic' is m itself. Each step reads only its own process's state and the stores, so
// `system(..., {h: {rule: isolation(m, level), id: 't'}})` runs any number of transactions at once.
export function isolation(m: Machine, level: Level): Machine {
  plain(m, 'isolation')
  if (level === 'atomic') return from({...m}, m, ISOLATION.atomic)
  const stores = new Set(Object.keys(m.maps ?? {}))
  const sites: {map: string, key: E, e: E}[] = [], seen = new Map<string, number>()
  const visitE = (e: E): void => {
    if (e.op === 'get') { visitE(e.key); if (stores.has(e.map)) { const j = JSON.stringify(e); if (!seen.has(j)) { seen.set(j, sites.length); sites.push({map: e.map, key: e.key, e}) } } return }
    if (e.op === 'if') { visitC(e.c); visitE(e.then); visitE(e.else); return }
    if ('a' in e) visitE(e.a)
    if ('b' in e) visitE(e.b)
  }
  const visitC = (c: C): void => {
    if (c.op === 'and' || c.op === 'or') c.xs.forEach(visitC)
    else if (c.op === 'not') visitC(c.x)
    else if (c.op === 'all') throw new Error(`isolation: ${m.name} reads every key at once (a quantified flag): not split here`)
    else if (c.op !== 'flag') { visitE(c.a); visitE(c.b) }
  }
  const pointWrites = Object.entries(m.step.maps ?? {}).map(([map, w]) => {
    if ('each' in w) throw new Error(`isolation: ${m.name} writes ${map} at every key: not split here`)
    return {map, ...w}
  })
  Object.values(m.step.flags ?? {}).forEach(visitC)
  Object.values(m.step.state ?? {}).forEach(visitE)
  for (const w of pointWrites) { visitE(w.key); visitE(w.value); if (level === 'snapshot') visitE(get(w.map, w.key)) }
  if (m.assume) visitC(m.assume)
  if (level === 'snapshot' && sites.some(s => JSON.stringify(s.e).includes('"op":"flag"'))) throw new Error(`isolation: ${m.name} reads a store at a key a flag decides: not split at a snapshot here`)
  const taken = new Set([...m.params, ...m.inputs, ...Object.keys(m.state), ...stores])
  for (const v of ['pc$', 'aborted$']) if (taken.has(v)) throw new Error(`isolation: ${v} is a name of ${m.name}`)
  // σ: what the commit reads: the kept inputs and what was read.
  const rd = (j: number) => `rd$${j}`, inp = (i: string) => `in$${i}`
  const sigma = (e: E): E => {
    if (e.op === 'var') return m.inputs.includes(e.name) ? x(inp(e.name)) : e
    if (e.op === 'get') { const j = seen.get(JSON.stringify(e)); return j !== undefined ? x(rd(j)) : get(e.map, sigma(e.key)) }
    if (e.op === 'if') return ite(sigmaC(e.c), sigma(e.then), sigma(e.else))
    if (e.op === 'const') return e
    if (e.op === 'mul') return {...e, a: sigma(e.a)}
    return {...e, a: sigma(e.a), b: sigma(e.b)}
  }
  const sigmaC = (c: C): C => {
    if (c.op === 'and' || c.op === 'or') return {op: c.op, xs: c.xs.map(sigmaC)}
    if (c.op === 'not') return not(sigmaC(c.x))
    if (c.op === 'flag' || c.op === 'all') return c
    return {...c, a: sigma(c.a), b: sigma(c.b)}
  }
  // (a record's parts at one key are one read: one GET returns the record)
  const groupOf = (st: {map: string, key: E}) => `${st.map.replace(/\.[^.]*$/, '')}|${JSON.stringify(st.key)}`, groups = [...new Set(sites.map(groupOf))], gi = (j: number) => groups.indexOf(groupOf(sites[j]!))
  const r = groups.length, snap = level === 'snapshot'
  const commit = snap ? 1 : r + 1, done = commit + 1
  const at = (k: number): C => same(x('pc$'), n(k))
  const valid = snap ? all(...pointWrites.map(w => { const on = writesWhen(w.value, get(w.map, w.key)); const cell = get(w.map, sigma(w.key)), was = sigma(get(w.map, w.key)); return on === false ? same(n(0), n(0)) : any(...(on === true ? [] : [not(sigmaC(on))]), same(cell, was)) })) : undefined
  const commits = valid ? all(at(commit), valid) : at(commit)
  const reads = snap ? x('pc$') : Array.from({length: r}, (_, j) => j + 1).reduceRight<E>((acc, j) => ite(at(j), n(j + 1), acc), x('pc$'))
  const state: Record<string, E> = {
    'pc$': ite(at(0), n(snap || !r ? commit : 1), ite(at(commit), n(done), reads)),
    ...Object.fromEntries(m.inputs.map(i => [inp(i), ite(at(0), x(i), x(inp(i)))])),
    ...Object.fromEntries(sites.map((s, j) => [rd(j), ite(at(snap ? 0 : gi(j) + 1), snap ? s.e : get(s.map, sigma(s.key)), x(rd(j)))])),
    ...mapValues(m.step.state, (e, s) => ite(commits, sigma(e), x(s))),
    ...(snap ? {'aborted$': ite(at(commit), valid!.op === 'and' && !valid!.xs.length ? n(0) : ite(valid!, n(0), n(1)), x('aborted$'))} : {}),
  }
  const maps: Record<string, MapUpdate> = Object.fromEntries(pointWrites.map(w => {
    const on = writesWhen(w.value, get(w.map, w.key)), key = sigma(w.key)
    const when = on === false ? undefined : on === true ? commits : all(commits, sigmaC(on))
    return [w.map, {key, value: when ? ite(when, sigma(w.value), get(w.map, key)) : get(w.map, key)}]
  }))
  const out: Machine = {
    name: `${m.name} (${level})`, params: m.params, inputs: m.inputs,
    state: {...m.state, 'pc$': n(0), ...Object.fromEntries(m.inputs.map(i => [inp(i), n(0)])), ...Object.fromEntries(sites.map((_s, j) => [rd(j), n(0)])), ...(snap ? {'aborted$': n(0)} : {})},
    ...(m.maps ? {maps: m.maps} : {}),
    step: {flags: mapValues(m.step.flags, sigmaC), state, maps},
    // (the request's assumption, at the begin: the inputs it keeps)
    ...(m.assume ? {assume: any(not(at(0)), m.assume)} : {}),
    ...(m.pre ? {pre: m.pre} : {}),
  }
  readsOf.set(out, groups.map(g => g.slice(0, g.indexOf('|'))))
  return from(out, m, ISOLATION[level])
}
// The stores a transaction reads, one per read step (read committed's; snapshot's are all at its begin).
export const readsOf = new WeakMap<Machine, string[]>()

// --- delivery -------------------------------------------------------------------------------------------------------

export type Delivery = 'exactly-once' | 'at-least-once'
export const DELIVERY: Record<Delivery, Model> = {
  'exactly-once': {name: 'exactly-once delivery', assumes: 'a message is taken by one handler step, once, and the take commits with the handler\'s writes (a transactional consume, an inbox row in the same transaction)',
    checked: 'a transactional consume (Kafka transactions, an inbox row in the handler\'s transaction)'},
  'at-least-once': {name: 'at-least-once delivery', assumes: 'a sent message may be delivered any number of times, in any order, including while an earlier delivery is still being handled (redelivery, duplicates, a retrying client whose earlier try may still run or may have applied)',
    checked: 'SQS standard queues, Kafka before an offset commit, Redis Streams (XAUTOCLAIM, envcheck.py)'},
}
// m's request taken from the message pool `pool`: each input in `fields` read from the message `msg` (an input): the
// pool's maps `${pool}` (1 once sent) and `${pool}_${field}`; `id`, an input that is the message's id itself (an
// idempotency key that is the message id). The request is one m may take only while the message was sent; exactly
// once also takes it (`${pool}_taken`). On a handler of several steps (pc$, isolation's), the message is taken at its
// begin.
export function delivery(m: Machine, pool: string, fields: string[], mode: Delivery, opts: {msg?: string, id?: string} = {}): Machine {
  plain(m, 'delivery')
  const msg = opts.msg ?? 'msg', bound = [...fields, ...(opts.id ? [opts.id] : [])]
  for (const f of bound) if (!m.inputs.includes(f)) throw new Error(`delivery: ${f} is no input of ${m.name}`)
  if ([...m.inputs, ...Object.keys(m.state)].includes(msg)) throw new Error(`delivery: ${msg} is already a name of ${m.name}`)
  const begin: C = 'pc$' in m.state ? same(x('pc$'), n(0)) : same(n(0), n(0))
  const vars = {...Object.fromEntries(fields.map(f => [f, get(`${pool}_${f}`, x(msg))])), ...(opts.id ? {[opts.id]: x(msg)} : {})}
  const {E, C, W} = mapper(m, vars, f => f), taken = `${pool}_taken`
  const guard = all(begin, ...[same(get(pool, x(msg)), n(1))], ...(mode === 'exactly-once' ? [same(get(taken, x(msg)), n(0))] : []))
  return from({
    ...m, name: `${m.name} (${mode} from ${pool})`, inputs: [...m.inputs.filter(i => !bound.includes(i)), msg],
    maps: {...m.maps, [pool]: 0, ...Object.fromEntries(fields.map(f => [`${pool}_${f}`, 0])), ...(mode === 'exactly-once' ? {[taken]: 0} : {})},
    step: {
      flags: mapValues(m.step.flags, C), state: mapValues(m.step.state, E),
      maps: {...mapValues(m.step.maps, W), ...(mode === 'exactly-once' ? {[taken]: {key: x(msg), value: ite(begin, n(1), get(taken, x(msg)))}} : {})},
    },
    assume: all(any(not(begin), guard), ...(m.assume ? [C(m.assume)] : [])),
  }, m, DELIVERY[mode])
}

// The environment's sends into `pool`: a message at a fresh id, its fields any values (the request's).
export const client = (pool: string, fields: string[], msg = 'msg'): Machine => ({
  name: `client of ${pool}`, params: [], inputs: [msg, ...fields.map(f => `${pool}_${f}$in`)], state: {},
  maps: {[pool]: 0, ...Object.fromEntries(fields.map(f => [`${pool}_${f}`, 0]))},
  step: {maps: {[pool]: {key: x(msg), value: n(1)}, ...Object.fromEntries(fields.map(f => [`${pool}_${f}`, {key: x(msg), value: x(`${pool}_${f}$in`)}]))}},
  assume: same(get(pool, x(msg)), n(0)),
})

// A retrying client is at-least-once delivery of its requests: each try a delivery, the next sent on a timeout.
export const RETRIES: Model = {name: 'a retrying client', assumes: 'a request may be tried again at any time, any number of times, while an earlier try is still running or after it applied (its reply lost to a timeout)',
  checked: 'urllib3 Retry after a read timeout (envcheck.py: one POST applied three times)'}
// A store's call fails: the code takes its failure path; a failed write may still have applied (a lost reply).
export const STORE_FAILS: Model = {name: 'store calls fail', assumes: 'any call to the store may raise, before it applied or after (its reply lost)',
  checked: 'redis-py\'s ConnectionError and TimeoutError (envcheck.py: a SET whose reply was lost, applied)'}
export const WRITES_FAIL: Model = {name: 'database writes fail', assumes: 'a create may raise before its insert committed or after (a receiver run after the INSERT raising)',
  checked: 'Django: post_save receivers and on_commit hooks raise after the INSERT; transaction.atomic rolls back before it'}

// --- stores that forget ---------------------------------------------------------------------------------------------

export const EXPIRY: Model = {name: 'keys expire', assumes: 'any key of the store may vanish at any step, whatever its TTL (the TTL lapsed while its holder still worked, or an eviction)',
  checked: 'Redis EX and maxmemory-policy volatile-lru (envcheck.py: a 30 s key evicted at once)'}
// A store's key reset to its start: `cells`, the maps of one store (a record's parts) and the value each holds when the
// key is absent.
export const expiry = (cells: Record<string, number>, key = 'key'): Machine => modelled({
  name: `expiry of ${Object.keys(cells).join(', ')}`, params: [], inputs: [key], state: {}, maps: cells,
  step: {maps: mapValues(cells, v => ({key: x(key), value: n(v)}))},
}, EXPIRY)

// --- time -----------------------------------------------------------------------------------------------------------

// The true time: a natural the environment raises by any amount (`dt`) at a step of its own. Nothing bounds how many
// other steps run between two of its steps, or how far one goes: a law that needs time to pass says so by its fairness
// (a helpful request {act: <time's part>, dt: 1}), and a timer is a step allowed once the time has passed its deadline.
export const TIME: Model = {name: 'time passes', assumes: 'one true time `now`, a natural that only rises, by any amount at a step of its own; nothing bounds how many other steps run between two of its steps',
  checked: 'the time reference: a store\'s clock for its TTLs (Redis\'s own), a node\'s monotonic clock (CLOCK_MONOTONIC) for its own timers'}
export const time = (now = 'now', by = 'dt'): Machine => modelled({name: 'time', params: [], inputs: [by], state: {[now]: n(0)}, step: {state: {[now]: plus(x(now), x(by))}}}, TIME)

// A node's clock within `skew` of the true time: m's request time (the input `at`, as the readers read time.time(),
// Instant::now() and the like) is any reading t with now − skew ≤ t ≤ now + skew. A reading need not rise from the
// last: more runs than a monotonic clock's, so a proof holds for those too. `skew` is a constant or a param's name (a
// param of the rule then); 0 is the time itself (`at` replaced by `now`, no longer an input); Infinity is no bound (the
// reading any natural).
export const SKEW = (skew: number | string): Model => ({name: `clock skew ${skew === Infinity ? 'unbounded' : `≤ ${skew}`}`,
  assumes: skew === Infinity ? 'a node\'s clock may read any time at all' : `every reading of a node's clock is within ${skew} of the true time, either way; readings need not rise`,
  checked: 'the deployment\'s bound (NTP or PTP discipline and its alarm, e.g. chrony\'s maxdistance): stated, not checked here'})
export function clocked(m: Machine, at: string, skew: number | string, now = 'now'): Machine {
  plain(m, 'clocked')
  if (!m.inputs.includes(at)) throw new Error(`clocked: ${at} is no input of ${m.name}`)
  if (now in (m.maps ?? {}) || m.inputs.includes(now) || m.params.includes(now)) throw new Error(`clocked: ${now} is a name of ${m.name} other than a scalar`)
  if (m.step.state?.[now]) throw new Error(`clocked: ${m.name} writes ${now}; the time is the environment's`)
  if (typeof skew === 'number' && skew !== Infinity && !(Number.isSafeInteger(skew) && skew >= 0)) throw new Error(`clocked: a skew is a natural, a param's name or Infinity`)
  const eps: E = typeof skew === 'string' ? x(skew) : n(skew as number), t = x(at), tn = x(now)
  const bound = skew === Infinity || skew === 0 ? [] : [atMost(t, plus(tn, eps)), atMost(tn, plus(t, eps))]
  // (no skew: the reading is the time itself, the input gone)
  const {E: S, C, W} = mapper(m, skew === 0 ? {[at]: tn} : {}, f => f), assume = m.assume && C(m.assume)
  const out: Machine = {
    ...m, params: typeof skew === 'string' && !m.params.includes(skew) ? [...m.params, skew] : m.params,
    inputs: skew === 0 ? m.inputs.filter(i => i !== at) : m.inputs,
    state: {...m.state, [now]: m.state[now] ?? n(0)},
    step: {flags: mapValues(m.step.flags, C), state: mapValues(m.step.state, S), maps: mapValues(m.step.maps, W)},
    ...(bound.length || assume ? {assume: all(...(assume ? [assume] : []), ...bound)} : {}),
    ...(m.pre ? {pre: m.pre} : {}),
  }
  from(out, m, SKEW(skew))
  sharedOf.set(out, [...new Set([...(sharedOf.get(m) ?? []), now])])
  return out
}

// Keys that expire at their time: a key of the store vanishes (each of `cells`, the record's parts, back to its value
// when absent; the expiry `at` too) at any step once the true time has reached its expiry, and never before. With no
// `key`, the cells are scalars (one record).
export const TTL: Model = {name: 'keys expire at their time', assumes: 'a key vanishes only once the store\'s clock (the true time) has reached its expiry, at any step after; never before (no eviction: maxmemory-policy noeviction, or no memory pressure)',
  checked: 'Redis PX: the key is there before its time and gone after (envcheck.py); under noeviction a write past maxmemory is refused (OOM), not evicted'}
export function expires(cells: Record<string, number>, at: string, opts: {key?: string, now?: string} = {}): Machine {
  const now = opts.now ?? 'now', all0 = {...cells, [at]: 0}, key = opts.key
  const m: Machine = key
    ? {name: `expiry of ${Object.keys(cells).join(', ')} at ${at}`, params: [], inputs: [key], state: {[now]: n(0)}, maps: all0,
      step: {maps: mapValues(all0, v => ({key: x(key), value: n(v)}))}, assume: atMost(get(at, x(key)), x(now))}
    : {name: `expiry of ${Object.keys(cells).join(', ')} at ${at}`, params: [], inputs: [], state: {...mapValues(all0, v => n(v)), [now]: n(0)},
      step: {state: mapValues(all0, v => n(v))}, assume: atMost(x(at), x(now))}
  sharedOf.set(m, [now])
  return modelled(m, TTL)
}

// --- a rule in its environment --------------------------------------------------------------------------------------

// What a project states of where its code runs (gdp.toml's `env`, or a `gdp: env` comment over the class), in words:
// an isolation level (atomic, serializable, read committed, snapshot, repeatable read), "keys expire", "retries" or
// "at-least-once". Unknown words are refused, never dropped.
export type Env = {isolation?: Level, expiry?: boolean, retries?: boolean, flow?: string[], apart?: boolean}
const WORDS: [RegExp, (e: Env) => void][] = [
  [/^(atomic|serializable|lua|one step|locked|for update)$/, e => { e.isolation = 'atomic' }],
  [/^read committed$/, e => { e.isolation = 'read committed' }],
  [/^(snapshot|repeatable read)$/, e => { e.isolation = 'snapshot' }],
  [/^(keys expire|expiry|ttl|eviction|keys evicted)$/, e => { e.expiry = true }],
  [/^(retries|retried|at-least-once|at least once|redelivery|duplicates)$/, e => { e.retries = true }],
  [/^(an object per call|objects apart|a process per call|one object per call)$/, e => { e.apart = true }],
]
export function envOf(text: string | string[]): Env {
  const e: Env = {}
  for (const w of (Array.isArray(text) ? text : [text]).flatMap(t => t.split(/\s*[,;]\s*|\s+and\s+/)).map(w => w.trim().replace(/\s+/g, ' ')).filter(Boolean)) {
    // (a call's flow: its methods in order, `acquire then release`)
    if (/^[\w.]+( then [\w.]+)+$/.test(w)) { e.flow = w.split(' then '); continue }
    const f = WORDS.find(([re]) => re.test(w.toLowerCase()))
    if (!f) throw new Error(`env: ${JSON.stringify(w)} is not an environment gdp-wired models (atomic, read committed, snapshot, keys expire, retries, a flow: <method> then <method>)`)
    f[1](e)
  }
  return e
}
export const envText = (e: Env): string => [e.isolation, e.expiry && 'keys expire', e.retries && 'retries', e.apart && 'an object per call', e.flow?.join(' then ')].filter(Boolean).join(', ')

// A rule (one handler: an extracted class's step, its maps the stores it reads and writes) as every call of it at once
// in its environment: each call a transaction at the isolation level (its locals the call's own), the stores' keys
// vanishing where they expire, retries any call again (a retried call is another call with the same request, which
// every call at once already has). The rule's laws are lifted with it: a law about the state holds of every call's
// locals; a law of one step holds of each call's commit, the state before it the store as the commit finds it (what
// the call read may be older), the request the one the call began with. `stores`: the maps that are a store's (the
// expiry's), each with its parts (a record's); `own`: the scalars that are a call's own (its result, its failure), the
// others the object's fields, which every call on it shares.
// A flow (env.flow: acquire then release) is what one call does: its methods in that order, each a step (or a
// transaction) of its own, the call ending where one fails (`failed`, the rule's failure kept). A call holds from its
// first method's success to its last method; where a key its first method wrote expires, every call holding by that
// key stops holding (its lease ran out), and `between` is the law that at most one call holds at once.
export type InEnv = {rule: Rule, models: Model[], reads: string[], part: string, act: string, id?: string, commit?: number, level: Level, flow?: string[], method?: string, methods?: number,
  law: (l: Law) => Law, step: (s: StepLaw) => StepLaw, between: (name: string, a: string, b: string) => Law}
// `oks`: the methods whose result says whether they did it (a lock's True), by their result's variable; `args`: each
// method's arguments by the code's name (a flow's call passes the same value to each of its methods that
// takes an argument of one name: the lock it acquires is the one it releases).
export type EnvOpts = {stores?: string[][], own?: string[], method?: {name: string, values: string[]}, failed?: string, args?: {method: string, code: string, rule: string}[], oks?: {method: string, rule: string}[]}
export function inEnv(r: Rule | Machine, env: Env, o: EnvOpts = {}): InEnv {
  let m = machineOf(r)
  const level = env.isolation ?? 'atomic', split = level !== 'atomic', flow = env.flow, lifted = split || !!flow, P = 'calls', act = 'act$', id = 'p$'
  const stores = o.stores ?? [], own = [...(o.own ?? [])], hk: Record<string, string> = {}
  if (flow) {
    const k = flow.length
    const is = (f: string): C => {
      if (!o.method) { if (k > 1) throw new Error(`a flow of ${k} methods, and the rule has one`); return same(n(0), n(0)) }
      const i = o.method.values.indexOf(f)
      if (i < 0) throw new Error(`${f} is no method of ${m.name} (${o.method.values.join(', ')})`)
      return same(x(o.method.name), n(i))
    }
    // (a method done: not failed, and where its result says whether it did it, that result true)
    const failedOk = o.failed && m.step.state?.[o.failed] ? [same(m.step.state[o.failed]!, n(0))] : []
    const oks = (o.oks ?? []).filter(r => flow.includes(r.method) && m.step.state?.[r.rule]).map(r => any(not(is(r.method)), not(same(m.step.state![r.rule]!, n(0)))))
    const done = failedOk.length || oks.length ? all(...failedOk, ...oks) : undefined, stage = x('stage$')
    for (const [map, w] of Object.entries(m.step.maps ?? {})) if ('key' in w) hk[map] = `hk$${map}`
    m = {...m, state: {...m.state, 'stage$': n(0), 'held$': n(0), ...Object.fromEntries(Object.values(hk).map(h => [h, n(0)]))},
      step: {...m.step, state: {...m.step.state,
        'stage$': done ? ite(done, plus(stage, n(1)), n(k)) : plus(stage, n(1)),
        'held$': ite(all(is(flow[0]!), ...(done ? [done] : [])), n(1), ite(is(flow[k - 1]!), n(0), x('held$'))),
        ...Object.fromEntries(Object.entries(hk).map(([map, h]) => [h, ite(is(flow[0]!), (m.step.maps![map] as {key: E}).key, x(h))]))}},
      assume: all(...(m.assume ? [m.assume] : []), atMost(plus(stage, n(1)), n(k)), any(...flow.map((f, j) => all(same(stage, n(j)), is(f)))))}
    // (an argument of one name, kept from the first method of the flow that takes it, its later methods given the same)
    const named = new Map<string, {method: string, rule: string}[]>()
    for (const a of o.args ?? []) if (flow.includes(a.method) && m.inputs.includes(a.rule)) named.set(a.code, [...(named.get(a.code) ?? []), a])
    const keeps: string[] = []
    for (const [code, as] of named) {
      const sorted = [...as].sort((a, b) => flow.indexOf(a.method) - flow.indexOf(b.method)), first = sorted[0]!, kept = `arg$${code}`
      if (sorted.length < 2 || kept in m.state) continue
      keeps.push(kept)
      m = {...m, state: {...m.state, [kept]: n(0)}, step: {...m.step, state: {...m.step.state, [kept]: ite(is(first.method), x(first.rule), x(kept))}},
        assume: all(m.assume!, ...sorted.slice(1).map(a => any(not(is(a.method)), same(x(a.rule), x(kept)))))}
    }
    own.push('stage$', 'held$', ...Object.values(hk), ...keeps)
    // (atomic: the calls holding each key, counted in the step that takes or gives it up, so the law is about every key)
    const rk = Object.values(m.step.maps ?? {}).find((w): w is {key: E, value: E} => 'key' in w)?.key
    if (!split && rk) {
      const d = get('done$', rk), took = all(is(flow[0]!), ...(done ? [done] : [])), gave = k > 1 ? all(is(flow[k - 1]!), same(x('held$'), n(1))) : same(n(0), n(1))
      m = {...m, maps: {...m.maps, 'done$': 0}, step: {...m.step, maps: {...m.step.maps, 'done$': {key: rk, value: ite(took, plus(d, n(1)), ite(gave, {op: 'sub', a: d, b: n(1)} as E, d))}}}}
    }
  }
  // (an object per call: the fields its methods write are the call's own, those it only reads the object's as made)
  if (env.apart) own.push(...Object.keys(m.state).filter(s => !own.includes(s) && m.step.state?.[s] && JSON.stringify(m.step.state[s]) !== JSON.stringify(x(s))))
  // (a field a call writes is read where the call commits, not where the code reads it: refused at a split level)
  const fields = Object.keys(m.state).filter(s => !own.includes(s)), written = fields.filter(s => m.step.state?.[s] && JSON.stringify(m.step.state[s]) !== JSON.stringify(x(s)))
  if (split && written.length) throw new Error(`a call writes the object's ${written.join(', ')}, which it reads at its commit only here: not modelled at ${level}`)
  const h = isolation(m, level)
  const commit = split ? (level === 'snapshot' ? 1 : readsOf.get(h)!.length + 1) : undefined
  // (a flow's call begins its next method after a commit)
  if (flow && split) h.step.state!['pc$'] = ite(same(x('pc$'), n(commit!)), n(0), h.step.state!['pc$']!)
  const parts: Record<string, Part> = {[P]: lifted ? {rule: h, id, shared: fields} : h}
  if (env.expiry) stores.forEach((cells, i) => {
    const e = expiry(Object.fromEntries(cells.map(c => [c, m.maps![c]!])), 'key$'), mine = cells.filter(c => hk[c])
    // (a lease runs out: the calls holding by the key expired hold no longer; a call's done work, a flow of one method, stays done)
    if (mine.length && flow!.length > 1) {
      e.maps = {...e.maps, 'held$': 0, ...Object.fromEntries(mine.map(c => [hk[c]!, 0]))}; e.step.maps!['held$'] = {each: 'q$', value: ite(any(...mine.map(c => same(get(hk[c]!, x('q$')), x('key$')))), n(0), get('held$', x('q$')))}
      if ('done$' in (m.maps ?? {})) { e.maps['done$'] = 0; e.step.maps!['done$'] = {key: x('key$'), value: n(0)} }
    }
    parts[`expiry${stores.length > 1 ? i : ''}`] = e
  })
  const sys = system(`${machineOf(r).name} (${envText(env) || 'atomic'})`, parts, {act})
  const ms = [...modelsOf(sys), ...(env.retries ? [RETRIES] : [])]
  models.set(sys, ms)
  const locals = Object.keys(m.state).filter(s => own.includes(s)), on = same(x(act), n(0))
  const flags = () => Object.fromEntries(Object.keys(m.step.flags ?? {}).map(g => [g, {op: 'flag', name: `${P}$${g}`} as C]))
  // (a call's own: its locals at its process `at`, before and after; its request as the call kept it)
  const mine = (at: E, before: boolean): Subst => {
    const vs: [string, E][] = [...locals.flatMap((s): [string, E][] => [[s, get(s, at)], [`${s}'`, get(`${s}'`, at)]]), ...(before && split ? m.inputs.map((i): [string, E] => [i, get(`in$${i}`, at)]) : [])]
    return {vars: lifted ? Object.fromEntries(vs) : {}, maps: {}, flags: flags()}
  }
  const law = (l: Law): Law => {
    if (!lifted || !locals.some(s => JSON.stringify(l.holds).includes(`"name":"${s}"`))) return l
    const k = 'p$k', holds = substC(l.holds, mine(x(k), false))
    return l.forall ? {...l, holds, keys: [...(l.keys ?? []), k]} : {...l, holds, forall: k}
  }
  const step = (s: StepLaw): StepLaw => {
    if ((s.steps ?? 1) !== 1) throw new Error(`env: a law of ${s.steps} steps is not lifted to every call at once`)
    const sub = mine(x(id), true), whens = s.when === undefined ? [] : Array.isArray(s.when) ? s.when : [s.when]
    const then = substC(s.then, sub)
    return {...s, then: level === 'snapshot' ? any(same(get("aborted$'", x(id)), n(1)), then) : then,
      when: all(on, ...(split ? [same(get('pc$', x(id)), n(commit!))] : []), ...whens.map(w => substC(w, sub)))}
  }
  const between = (name: string, a: string, b: string): Law => {
    if (!flow || flow[0] !== a || flow.at(-1) !== b) throw new Error(`between ${a} and ${b}: the call's flow is ${flow ? flow.join(' then ') : 'not stated'} (env: ${a} then ${b})`)
    if (!split && 'done$' in (m.maps ?? {})) return {name, holds: atMost(get('done$', x('k$d')), n(1)), forall: 'k$d'}
    const held = (p: string) => same(get('held$', x(p)), n(1))
    // (per lock: two calls holding by different keys hold different things)
    return {name, holds: any(not(held('p$a')), not(held('p$b')), same(x('p$a'), x('p$b')), ...Object.values(hk).map(k => not(same(get(k, x('p$a')), get(k, x('p$b')))))), forall: 'p$a', keys: ['p$b']}
  }
  return {rule: sys, models: ms, reads: split && level !== 'snapshot' ? readsOf.get(h)! : [], part: P, act, ...(lifted ? {id} : {}), ...(split ? {commit} : {}), level, ...(flow ? {flow} : {}), ...(o.method ? {method: o.method.name, methods: o.method.values.length} : {}), law, step, between}
}

// A run that breaks a law, shortened: steps dropped one at a time while the rest still breaks it (replayed on the
// interpreter, each request allowed where it is taken, the law read as the search reads it), cut at the first break.
export function shrinkRun<T extends {params: Record<string, number>, trace: Record<string, unknown>[]}>(r: Rule | Machine, w: Law | StepLaw, run: T): T {
  const m = machineOf(r), rt = interpret(m), params = run.params
  const bound = 2 + Math.max(0, ...[...Object.values(params), ...run.trace.flatMap(q => Object.values(q))].filter((v): v is number => typeof v === 'number'))
  // (the length of the prefix that breaks it, or 0)
  const breaks = (trace: Record<string, unknown>[]): number => {
    try {
      const on = watch(m, rt, w, params, bound)
      let st = rt.init(params)
      if (!on.start(st)) return 0
      for (const [i, q] of trace.entries()) {
        if (!allowed(m, rt, params, st, q as Request)) return 0
        const nx = rt.step(params, st, q as Request)
        if (!on.step(st, q as Request, nx)) return i + 1
        st = nx
      }
    } catch { return 0 }
    return 0
  }
  let trace = run.trace, at = breaks(trace)
  if (!at) return run
  trace = trace.slice(0, at)
  for (let changed = true; changed;) {
    changed = false
    for (let i = 0; i < trace.length; i++) {
      const t = [...trace.slice(0, i), ...trace.slice(i + 1)], b = breaks(t)
      if (b) { trace = t.slice(0, b); changed = true; i-- }
    }
  }
  return {...run, trace}
}

// Contention: runs of a system where every call passes one request, so the calls contend for one key; only which
// part steps, which of three calls, its method and the expiring key vary, searched breadth first (states seen once) to
// a depth, for each of a few requests drawn. A run found breaks the law on the interpreter, as the search's do. (The
// search's own runs draw each request apart: three calls on one lock are rare among them.)
export function contend(e: InEnv, w: Law | StepLaw, opts: {bases?: number, depth?: number, bound?: number, seed?: number, ms?: number, calls?: number} = {}) {
  const m = e.rule.machine, rt = interpret(m), bound = opts.bound ?? 2, until = performance.now() + (opts.ms ?? 3000), calls = opts.calls ?? 3
  let seed = opts.seed ?? 7
  const rand = (k: number) => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed % k }
  const free = new Set([e.act, ...(e.id ? [e.id] : []), ...(e.method ? [e.method] : []), 'key$'])
  const acts = ((e.rule as unknown as {parts?: {inputs: [string, {values?: string[]}][]}}).parts?.inputs.find(([i]) => i === e.act)?.[1].values ?? ['calls']).length
  const choices: Record<string, number>[] = []
  for (let a = 0; a < acts; a++) {
    if (a > 0) { for (let k = 0; k <= bound; k++) choices.push({[e.act]: a, 'key$': k}); continue }
    for (let p = 1; p <= (e.id ? calls : 1); p++) for (let mt = 0; mt < (e.method ? e.methods ?? 1 : 1); mt++) choices.push({[e.act]: 0, ...(e.id ? {[e.id]: p} : {}), ...(e.method ? {[e.method]: mt} : {})})
  }
  const key = (st: {scalars: Record<string, number>, maps: Record<string, Map<number, number>>}) => JSON.stringify([st.scalars, Object.entries(st.maps).map(([k, v]) => [k, [...v].filter(([, x]) => x !== 0).sort((a, b) => a[0] - b[0])])])
  for (let b = 0, tried = 0; b < (opts.bases ?? 12) && tried < 400 && performance.now() < until; tried++) {
    const params: Record<string, number> = Object.fromEntries(m.params.map(p => [p, rand(bound + 1)]))
    // (the request's values from 0 and 1: two arguments a flow keeps equal, two strings of one length, agree often)
    const base: Record<string, number> = Object.fromEntries(m.inputs.filter(i => !free.has(i)).map(i => [i, rand(2)]))
    let st0: ReturnType<typeof rt.init>
    try { st0 = rt.init(params) } catch { continue }
    const req = (c: Record<string, number>) => ({...base, ...Object.fromEntries(m.inputs.filter(i => !(i in base)).map(i => [i, 0])), ...c}) as Request
    if (!choices.some(c => { try { return allowed(m, rt, params, st0, req(c)) } catch { return false } })) continue
    b++
    const seen = new Set([key(st0)])
    let frontier = [{st: st0, trace: [] as Record<string, unknown>[]}]
    for (let d = 0; d < (opts.depth ?? 7) && frontier.length && performance.now() < until; d++) {
      const next: typeof frontier = []
      for (const {st, trace} of frontier) for (const c of choices) {
        const q = req(c)
        let nx: typeof st
        try { if (!allowed(m, rt, params, st, q)) continue; nx = rt.step(params, st, q) } catch { continue }
        if (!watch(m, rt, w, params, bound + 2).step(st, q, nx)) return {params, trace: [...trace, q]}
        const k = key(nx)
        if (seen.has(k) || seen.size > 200_000) continue
        seen.add(k)
        next.push({st: nx, trace: [...trace, q]})
      }
      frontier = next
    }
  }
  return undefined
}
