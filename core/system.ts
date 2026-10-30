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
//   asRule(m)                  a Machine as a Rule, for the provers' entries (proveRule, proveSteps)
// The handlers are any rules: extracted by the readers (a step of one process, its maps the stores it reads and writes)
// or written; a handler that awaits other services between its reads and writes is several steps (a `pc` scalar), the
// form `isolation` gives an atomic one.
import {type C, type E, type Machine, type MapUpdate, all, any, get, ite, n, not, same, x} from './machine.ts'
import {type Subst, substC, substE} from '../kernel/kernel.ts'
import {Cond, type Kind, type Rule, Term, nat, oneOf, rule} from './dsl.ts'

// An environment model: what it assumes, and the documented behaviour it was checked against.
export type Model = {name: string, assumes: string, checked: string}
const models = new WeakMap<object, Model[]>()
const modelled = (m: Machine, ...ms: Model[]): Machine => { models.set(m, [...(models.get(m) ?? []), ...ms]); return m }
// m, stated to assume these models (a copy: what a written rule's inputs or steps assume of its environment).
export const assuming = (m: Machine | Rule, ...ms: Model[]): Machine => modelled({...machineOf(m)}, ...(models.get(m) ?? []), ...ms)
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
const plain = (m: Machine, what: string) => { if (m.history || m.sums || m.inputMaps?.length) throw new Error(`${what}: ${m.name} has a history, sums or carried maps (not taken here)`) }

// --- one process, every process ------------------------------------------------------------------------------------

// Every process of m at once: each scalar but `shared` a map keyed by the process `id` (an input), read and written at
// the request's process; m's maps stay as they are, shared. A process starts where m starts (a constant: a map's cells
// all start at one value).
export function lift(m: Machine, id: string, shared: string[] = []): Machine {
  plain(m, 'lift')
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
  r = r.state(mapValues(m.state, e => (e.op === 'const' ? e.value : () => new Term(e))))
  if (m.maps && Object.keys(m.maps).length) r = r.maps(m.maps)
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
    checked: 'PostgreSQL SERIALIZABLE ("the same effect as running them one at a time in some order", docs 13.2.3) and SELECT ... FOR UPDATE; a Redis Lua script ("executed atomically", EVAL docs); Python asyncio code whose awaits do not suspend'},
  'read committed': {name: 'read committed', assumes: 'each read of a store sees the latest committed value at its own step; the writes become visible together at commit; nothing is re-read at commit',
    checked: 'PostgreSQL READ COMMITTED (docs 13.2.1: a statement sees data committed before it began); a value the code computed from an earlier SELECT and wrote back loses a concurrent update (research/distributed/envcheck.py: lost update reproduced on PostgreSQL)'},
  'snapshot': {name: 'snapshot', assumes: 'every read sees the store as it was at the transaction start; a commit is refused (aborted$) when a cell it writes changed since then (first committer wins); writes to different cells never conflict (write skew allowed)',
    checked: 'PostgreSQL REPEATABLE READ (docs 13.2.2: "could not serialize access due to concurrent update"); research/distributed/envcheck.py checks both the abort and the write skew'},
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
// then the reads (read committed: each store read site at its own step, inner ones first, as rd$<i>; snapshot: all at
// the begin), then the commit, which computes m's step from what was read and writes it (snapshot: unless a cell it
// writes moved since the begin, aborted$ then 1), then done. m's scalars are the request's own (a result, a flag); its
// maps are the stores. 'atomic' is m itself. Each step reads only its own process's state and the stores, so
// `system(..., {h: {rule: isolation(m, level), id: 't'}})` runs any number of transactions at once.
export function isolation(m: Machine, level: Level): Machine {
  plain(m, 'isolation')
  if (level === 'atomic') return modelled({...m}, ISOLATION.atomic)
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
  const r = sites.length, snap = level === 'snapshot'
  const commit = snap ? 1 : r + 1, done = commit + 1
  const at = (k: number): C => same(x('pc$'), n(k))
  const valid = snap ? all(...pointWrites.map(w => { const on = writesWhen(w.value, get(w.map, w.key)); const cell = get(w.map, sigma(w.key)), was = sigma(get(w.map, w.key)); return on === false ? same(n(0), n(0)) : any(...(on === true ? [] : [not(sigmaC(on))]), same(cell, was)) })) : undefined
  const commits = valid ? all(at(commit), valid) : at(commit)
  const reads = snap ? x('pc$') : Array.from({length: r}, (_, j) => j + 1).reduceRight<E>((acc, j) => ite(at(j), n(j + 1), acc), x('pc$'))
  const state: Record<string, E> = {
    'pc$': ite(at(0), n(snap || !r ? commit : 1), ite(at(commit), n(done), reads)),
    ...Object.fromEntries(m.inputs.map(i => [inp(i), ite(at(0), x(i), x(inp(i)))])),
    ...Object.fromEntries(sites.map((s, j) => [rd(j), ite(at(snap ? 0 : j + 1), snap ? s.e : get(s.map, sigma(s.key)), x(rd(j)))])),
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
  return modelled(out, ISOLATION[level])
}

// --- delivery -------------------------------------------------------------------------------------------------------

export type Delivery = 'exactly-once' | 'at-least-once'
export const DELIVERY: Record<Delivery, Model> = {
  'exactly-once': {name: 'exactly-once delivery', assumes: 'a message is taken by one handler step, once, and the take commits with the handler\'s writes (a transactional consume, an inbox row in the same transaction)',
    checked: 'Kafka transactions (read-process-write, isolation.level=read_committed); a broker alone gives at-least-once'},
  'at-least-once': {name: 'at-least-once delivery', assumes: 'a sent message may be delivered any number of times, in any order, including while an earlier delivery is still being handled (redelivery, duplicates, a retrying client whose earlier try may still run or may have applied)',
    checked: 'Amazon SQS standard queues ("more than one copy of a message might be delivered"), Kafka after a rebalance before the offset commit, Redis Streams pending entries re-delivered by XAUTOCLAIM, an HTTP client retrying a timed-out request the server applied (research/distributed/envcheck.py: the last two reproduced)'},
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
  return modelled({
    ...m, name: `${m.name} (${mode} from ${pool})`, inputs: [...m.inputs.filter(i => !bound.includes(i)), msg],
    maps: {...m.maps, [pool]: 0, ...Object.fromEntries(fields.map(f => [`${pool}_${f}`, 0])), ...(mode === 'exactly-once' ? {[taken]: 0} : {})},
    step: {
      flags: mapValues(m.step.flags, C), state: mapValues(m.step.state, E),
      maps: {...mapValues(m.step.maps, W), ...(mode === 'exactly-once' ? {[taken]: {key: x(msg), value: ite(begin, n(1), get(taken, x(msg)))}} : {})},
    },
    assume: all(any(not(begin), guard), ...(m.assume ? [C(m.assume)] : [])),
  }, DELIVERY[mode])
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
  checked: 'urllib3 Retry (requests, httpx-style clients) re-sends after a read timeout; research/distributed/envcheck.py: a server that applies, then stalls past the timeout, applies one request twice'}
// A store's call fails: the code takes its failure path; a failed write may still have applied (a lost reply).
export const STORE_FAILS: Model = {name: 'store calls fail', assumes: 'any call to the store may raise, before it applied or after (its reply lost)',
  checked: 'redis-py raises ConnectionError and TimeoutError (a socket timeout after the server ran the command); research/distributed/envcheck.py: a SET whose reply times out is applied'}
export const WRITES_FAIL: Model = {name: 'database writes fail', assumes: 'a create may raise before its insert committed or after (a receiver run after the INSERT raising)',
  checked: 'Django: post_save receivers run inside the save after the INSERT; transaction.atomic rolls back on an exception raised inside it'}

// --- stores that forget ---------------------------------------------------------------------------------------------

export const EXPIRY: Model = {name: 'keys expire', assumes: 'any key of the store may vanish at any step, whatever its TTL (the TTL lapsed while its holder still worked, or an eviction)',
  checked: 'Redis SET ... EX (the key is gone once the time passes) and maxmemory-policy volatile-lru ("evict ... keys with an expire set"): research/distributed/envcheck.py evicts a key long before its TTL'}
// A store's key reset to its start: `cells`, the maps of one store (a record's parts) and the value each holds when the
// key is absent.
export const expiry = (cells: Record<string, number>, key = 'key'): Machine => modelled({
  name: `expiry of ${Object.keys(cells).join(', ')}`, params: [], inputs: [key], state: {}, maps: cells,
  step: {maps: mapValues(cells, v => ({key: x(key), value: n(v)}))},
}, EXPIRY)
