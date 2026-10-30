// Laws about two runs (`gdp-wired/relational`): two runs of one rule, or of two rules, side by side as one rule, so a
// law comparing them is an ordinary law of that rule, proven by the same induction, search and kernel, and checked in
// Lean as any other. Nothing here is trusted: what is proven is a law of the rule built, and the rule built is the two
// rules' own steps, their names renamed (a_x for the first run's x, b_x for the second's).
//
//   noninterference(rule, {secret: ['diagnosis'], visible: ['status']})     two runs whose requests and params differ
//       only in the secret ones give the same visible state, and refuse the same requests: the secret never reaches
//       what the party sees
//   isolation(rule, {owner: 'user_id', sees: ['failures']})                 what tenant B sees (its cells, its requests'
//       results and refusals) is the same whether or not anyone else acts: run a takes every request, run b only B's
//   agreement(old, next)                                                    the two rules agree on every history: the
//       same state they share by name after every run of the same requests, and the same refusals (a migration)
//   proveTwoRuns(law)                                                       the verdict, its run (two runs) if broken
//
// Each works on a rule read from code (gdp-wired/extract, extract-py, ...) as on one written with the builders; the
// rule's own invariants (an extraction's `invariants`) are given to proveTwoRuns and hold of each run.
// `twoRuns` is the construction itself, for laws of another shape: laws over the a_ and b_ names, proven by proveRule
// or proveSteps on the rule it returns.
//
// Refusals: by default (`refusals: 'same'`) a request one run refuses and the other takes is a difference the law is
// about (an error is seen as much as a value): the runs then keep their state, and `split$`, which the law
// `the two runs refuse the same requests` holds at 0, marks it. `refusals: 'assumed'` only takes requests both allow.
//
// Two of the law's names are reserved in the rule built: a$ok and b$ok (each run allows the request), split$.
import {type Cond, Rule, Term, type Kind, type Law, type StepLaw, type Verdict, type ProveOptions, all, any, forall, nat, no, not, proveSteps, same, when, yes} from './dsl.ts'
import type {C, E} from './machine.ts'
import {proveLaws, proveStepLaws} from '../kernel/prove.ts'
import {type Certificate, type Document, type Json, fromInterchange, toInterchange} from '../interchange/format.ts'
import {checkCertificate} from '../interchange/check.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
export type AnyRule = Rule<any, any, any, any, any, any, any, any>
type Spec = ConstructorParameters<typeof Rule>[0]
type Env = Record<string, unknown>
const specOf = (r: AnyRule): Spec => (r as unknown as {spec: Spec}).spec
const v = (name: string) => new Term({op: 'var', name})

// One run's side: its prefix, its rule's spec and the params and inputs both runs read as one (kept by their names).
type Side = {p: 'a_' | 'b_', s: Spec, shared: Set<string>, own: Set<string>}
// The names a side declares that are its own in the rule built (renamed): state and its parts, maps, lists, cells,
// items, kinded values, flags, and the params and inputs not shared.
function ownNames(s: Spec, shared: Set<string>): Set<string> {
  const out = new Set<string>()
  const kindParts = (xs: [string, Kind<unknown>][] | undefined) => { for (const [n, k] of xs ?? []) { out.add(n); for (const p of k.vars(n)) out.add(p) } }
  for (const [n, k] of [...s.params, ...s.inputs]) if (!shared.has(n)) { out.add(n); for (const p of k.vars(n)) out.add(p) }
  for (const [n] of s.state) out.add(n)
  for (const [n] of s.maps) out.add(n)
  for (const n of s.lists ?? []) out.add(n)
  kindParts(s.cells); kindParts(s.items); kindParts(s.kinded)
  return out
}
// The rule's env as one side's callbacks read it: its own names without their prefix, the shared ones as they are.
function view(env: Env, sd: Side): Env {
  const o: Env = {}, other = sd.p === 'a_' ? 'b_' : 'a_'
  for (const [k, x] of Object.entries(env)) {
    if (k.startsWith(sd.p)) o[k.slice(2)] = x
    else if (!k.startsWith(other)) o[k] = x
  }
  return o
}
const sameKind = (k1: Kind<unknown>, k2: Kind<unknown>) => k1.constructor === k2.constructor && JSON.stringify(k1.vars('x')) === JSON.stringify(k2.vars('x'))
  && JSON.stringify(k1.assume('x').map(c => c.c)) === JSON.stringify(k2.assume('x').map(c => c.c))

export type TwoRunsOptions = {
  name?: string,
  // The params and inputs both runs read as one value (by name; each must be in both rules, of one kind). The others are
  // each run's own: a_x and b_x.
  shared?: string[],
  // Where run b doesn't take the request (it isn't one of b's requests): b keeps its state. Over the rule built's env.
  stays?: (env: Env) => Cond,
  // What else relates the two runs' requests and params (assumed at every request), over the rule built's env.
  given?: (env: Env) => Cond,
  refusals?: 'same' | 'assumed',
}
// Two runs side by side as one rule: a's step and b's on every request (b's unless `stays`), each over its own state.
export function twoRuns(a: AnyRule, b: AnyRule = a, opts: TwoRunsOptions = {}): AnyRule {
  const sa = specOf(a), sb = specOf(b), refusals = opts.refusals ?? 'same'
  for (const s of [sa, sb]) {
    const odd = (['record', 'seqs', 'seqTables', 'lists2', 'carried', 'nodes'] as const).filter(f => { const x = s[f]; return Array.isArray(x) ? x.length : !!x })
    if (odd.length || s.sums.length || s.queries.length) throw new Error(`twoRuns: ${s.name} has ${[...odd, ...(s.sums.length ? ['sums'] : []), ...(s.queries.length ? ['queries'] : [])].join(', ')}, which two runs side by side don't take yet`)
    for (const [n] of [...s.params, ...s.inputs, ...s.state, ...s.maps]) if (/^[ab]_/.test(n)) throw new Error(`twoRuns: ${s.name}'s ${n}: a_ and b_ name the two runs' own values`)
  }
  const kindsOf = (s: Spec) => new Map([...s.params, ...s.inputs])
  const ka = kindsOf(sa), kb = kindsOf(sb)
  const shared = new Set(opts.shared ?? [...ka.keys()].filter(n => kb.has(n)))
  for (const n of shared) {
    const x = ka.get(n), y = kb.get(n)
    if (!x || !y) throw new Error(`twoRuns: ${n} is shared but not a param or input of ${x ? sb.name : sa.name}`)
    if (!sameKind(x, y)) throw new Error(`twoRuns: ${n} is of another kind in ${sa.name} and ${sb.name}`)
    if (sa.params.some(([m]) => m === n) !== sb.params.some(([m]) => m === n)) throw new Error(`twoRuns: ${n} is a param of one rule and an input of the other`)
  }
  const A: Side = {p: 'a_', s: sa, shared, own: ownNames(sa, shared)}, B: Side = {p: 'b_', s: sb, shared, own: ownNames(sb, shared)}
  const sides = [A, B]
  const rn = (sd: Side, n: string) => (sd.own.has(n) ? sd.p + n : n)
  // (a part's name is its value's with a suffix: renamed with it)
  for (const sd of sides) for (const [n, k] of [...sd.s.params, ...sd.s.inputs, ...(sd.s.kinded ?? []), ...(sd.s.cells ?? []), ...(sd.s.items ?? [])]) {
    if (sd.own.has(n) && JSON.stringify(k.vars(sd.p + n)) !== JSON.stringify(k.vars(n).map(x => sd.p + x))) throw new Error(`twoRuns: ${n}'s parts aren't named after it`)
  }
  const once = <T>(xs: [string, T][]): [string, T][] => { const seen = new Set<string>(); return xs.filter(([n]) => !seen.has(n) && !!seen.add(n)) }
  const renamed = <T>(f: (s: Spec) => [string, T][] | undefined) => sides.flatMap(sd => (f(sd.s) ?? []).map(([n, t]) => [rn(sd, n), t] as [string, T]))
  const fns = once(sides.flatMap(sd => sd.s.fns ?? []))
  for (const [n, d] of fns) for (const sd of sides) { const o = (sd.s.fns ?? []).find(([m]) => m === n); if (o && o[1] !== d) throw new Error(`twoRuns: two functions named ${n}`) }
  const okOf = (sd: Side) => (env: Env): Cond => all(...sd.s.assume.map(f => f(view(env, sd) as never)))
  const stays = (env: Env): Cond => opts.stays?.(env) ?? no
  // Where each run takes the request: both allow it (or b stays and a allows it); else neither moves.
  const goA = (env: Env): Cond => (refusals === 'same' ? all(env['a$ok'] as Cond, any(stays(env), env['b$ok'] as Cond)) : yes)
  const goB = (env: Env): Cond => (refusals === 'same' ? all(not(stays(env)), env['a$ok'] as Cond, env['b$ok'] as Cond) : not(stays(env)))
  const spec: Spec = {
    name: opts.name ?? (a === b ? `${sa.name}, two runs` : `${sa.name} | ${sb.name}`),
    params: once(renamed(s => s.params)), inputs: once(renamed(s => s.inputs)),
    state: [...sides.flatMap(sd => sd.s.state.map(([n, init]) => [sd.p + n, typeof init === 'number' ? init : (pe: never) => init(view(pe, sd) as never)] as [string, number | ((p: never) => Term)])),
      ...(refusals === 'same' ? [['split$', 0] as [string, number]] : [])],
    maps: renamed(s => s.maps),
    lists: sides.flatMap(sd => (sd.s.lists ?? []).map(n => sd.p + n)),
    cells: renamed(s => s.cells), items: renamed(s => s.items), kinded: renamed(s => s.kinded),
    ...(fns.length ? {fns} : {}),
    facts: sides.flatMap(sd => (sd.s.facts ?? []).map(f => (env: never) => Object.fromEntries(Object.entries(f(view(env, sd) as never)).map(([n, c]) => [`${sd.p}${n}`, c])))),
    arith: new Set([...(sa.arith ?? []), ...(sb.arith ?? [])]),
    flags: [
      ...sides.flatMap(sd => sd.s.flags.map(f => (env: never) => Object.fromEntries(Object.entries(f(view(env, sd) as never)).map(([n, c]) => [sd.p + n, c])))),
      ...(refusals === 'same' ? [(env: never) => ({'a$ok': okOf(A)(env), 'b$ok': okOf(B)(env)})] : []),
    ],
    pre: sides.flatMap(sd => sd.s.pre.map(f => (p: never) => f(view(p, sd) as never))),
    assume: [
      ...(refusals === 'assumed' ? [(env: never) => all(okOf(A)(env), any(stays(env), okOf(B)(env)))] : []),
      ...(opts.given ? [(env: never) => opts.given!(env)] : []),
    ],
    sums: [], queries: [],
    step: (env: never) => {
      const out: Record<string, unknown> = {}
      for (const sd of sides) {
        const go = (sd === A ? goA : goB)(env), side = view(env, sd)
        for (const [k, w] of Object.entries(sd.s.step?.(side as never) ?? {})) {
          if (w === undefined) continue
          const key = sd.own.has(k) ? sd.p + k : k.startsWith(sd.p) && sd.own.has(k.slice(2)) ? k : undefined
          if (!key) throw new Error(`twoRuns: ${sd.s.name}'s step writes ${k}, which it doesn't declare`)
          out[key] = guarded(sd, key, w, go)
        }
      }
      if (refusals === 'same') out['split$'] = when(all(not(stays(env)), not((env['a$ok'] as Cond).iff(env['b$ok'] as Cond))), 1, env['split$'] as Term)
      return out
    },
  }
  return new Rule(spec) as AnyRule
}
// A run's write kept only where it takes the request (else the value before it).
function guarded(sd: Side, key: string, w: unknown, go: Cond): unknown {
  if (go === yes) return w
  const kept = (value: E, old: E): E => ({op: 'if', c: go.c, then: value, else: old})
  type MW = {map: string, key?: E, each?: string, value: E}
  const mapWrite = (m: MW) => ({...m, value: kept(m.value, {op: 'get', map: m.map, key: m.each ? {op: 'var', name: m.each} : m.key!}), concrete: undefined})
  if (typeof w === 'object' && w !== null && 'parts' in w) return {parts: Object.fromEntries(Object.entries((w as {parts: Record<string, MW>}).parts).map(([p, m]) => [p, mapWrite(m)]))}
  if (typeof w === 'object' && w !== null && 'map' in w) return mapWrite(w as MW)
  const kind = (sd.s.kinded ?? []).find(([n]) => sd.p + n === key)?.[1]
  if (kind) { const parts = kind.store(key, w); return kind.build(key, part => when(go, parts[part]!, v(part)) as Term) }
  return when(go, w as Term, v(key))
}

// --- the laws --------------------------------------------------------------------------------------------------------

// A law about two runs: the rule built, the laws (invariants) and step laws that state it, and laws that may help prove
// it (each equal in both runs: proveTwoRuns keeps those that hold together with it, Houdini's way).
export type TwoRunLaw = {name: string, rule: AnyRule, laws: Law[], stepLaws: StepLaw[], helpers: Law[], sides: [AnyRule, AnyRule], shared: string[], cites?: string[]}
type View = {scalars: string[], maps: string[]}
// What a run's state holds by name: its scalars (state and kinded values) and maps (plain or of a kind).
function stateNames(s: Spec): View {
  const parts = new Set([...(s.kinded ?? []), ...(s.cells ?? []), ...(s.items ?? [])].flatMap(([n, k]) => k.vars(n).filter(p => p !== n)))
  const lens = new Set([...(s.items ?? []).map(([n]) => `${n}_len`), ...(s.lists ?? []).map(n => `${n}_len`)])
  return {
    scalars: [...s.state.map(([n]) => n).filter(n => !parts.has(n) && !lens.has(n)), ...(s.kinded ?? []).map(([n]) => n)].filter((n, i, xs) => xs.indexOf(n) === i),
    maps: [...s.maps.map(([n]) => n).filter(n => !parts.has(n) && !(s.lists ?? []).includes(n)), ...(s.cells ?? []).map(([n]) => n)].filter((n, i, xs) => xs.indexOf(n) === i),
  }
}
// The two runs' values of a name, the same: a scalar, or a map at every key (or at `at`).
const sameIn = (env: Env, n: string, isMap: boolean, at?: Term): Cond | ((k: Term) => Cond) => {
  const x = env[`a_${n}`] as {at: (k: Term) => unknown}, y = env[`b_${n}`] as {at: (k: Term) => unknown}
  if (x === undefined || y === undefined) throw new Error(`no ${n} in both runs`)
  return !isMap ? same(x, y) : at ? same(x.at(at), y.at(at)) : (k: Term) => same(x.at(k), y.at(k))
}
function viewLaw(r: AnyRule, name: string, names: string[], maps: Set<string>, at?: (env: Env) => Term): Law {
  const ms = names.filter(n => maps.has(n) && !at), ss = names.filter(n => !ms.includes(n))
  return r.law(name, (env: Env) => {
    const flat = ss.map(n => sameIn(env, n, maps.has(n), at?.(env)) as Cond)
    return ms.length ? forall(k => all(...flat, ...ms.map(n => (sameIn(env, n, true) as (k: Term) => Cond)(k)))) : all(...flat)
  })
}
const refusalLaw = (r: AnyRule): Law => r.law('the two runs refuse the same requests', (env: Env) => (env['split$'] as Term).eq(0))
const unknownNames = (names: string[], v: View, what: string) => { const bad = names.filter(n => !v.scalars.includes(n) && !v.maps.includes(n)); if (bad.length) throw new Error(`${what}: no ${bad.join(', ')} in the rule's state (its names: ${[...v.scalars, ...v.maps].join(', ')})`) }

// The secret params and inputs never reach `visible`: two runs whose requests (and params) are the same but for the
// secret ones keep every visible value the same, and refuse the same requests. `visible` defaults to all the state that
// isn't secret itself.
export function noninterference(r: AnyRule, o: {secret: string[], visible?: string[], name?: string, refusals?: 'same' | 'assumed'}): TwoRunLaw {
  const s = specOf(r), names = [...s.params, ...s.inputs].map(([n]) => n), vw = stateNames(s)
  const bad = o.secret.filter(n => !names.includes(n))
  if (bad.length) throw new Error(`noninterference: ${bad.join(', ')} isn't a param or input of ${s.name} (its params and inputs: ${names.join(', ')})`)
  const visible = o.visible ?? [...vw.scalars, ...vw.maps]
  unknownNames(visible, vw, 'noninterference')
  const p = twoRuns(r, r, {name: `${s.name}: ${o.secret.join(', ')} secret`, shared: names.filter(n => !o.secret.includes(n)), refusals: o.refusals})
  const maps = new Set(vw.maps), name = o.name ?? `${o.secret.join(', ')} never reaches ${visible.join(', ')}`
  return {name, rule: p, laws: [viewLaw(p, name, visible, maps), ...(o.refusals === 'assumed' ? [] : [refusalLaw(p)])], stepLaws: [],
    helpers: [...vw.scalars, ...vw.maps].filter(n => !visible.includes(n)).map(n => viewLaw(p, `${n} is the same in both runs`, [n], maps)), sides: [r, r], shared: names.filter(n => !o.secret.includes(n))}
}

// Tenant isolation: what the tenant `B` sees is the same whatever the others do. A request is B's where its owner (an
// input, a string's id or a natural) is B (a new param, `tenant`), or where `owner(env, B)` holds; run a takes every
// request, run b only B's. B sees the
// cells of `sees` (maps keyed by the owner) at B, the scalars of `results` after each of B's requests, and whether
// B's requests are refused. `sees` defaults to every map, `results` to none.
export function isolation(r: AnyRule, o: {owner: string | ((env: Env, tenant: Term) => Cond), sees?: string[], results?: string[], tenant?: string, name?: string, refusals?: 'same' | 'assumed'}): TwoRunLaw {
  const s = specOf(r), vw = stateNames(s), tenant = o.tenant ?? 'tenant'
  if (typeof o.owner === 'string' && !s.inputs.some(([n]) => n === o.owner)) throw new Error(`isolation: ${o.owner} isn't an input of ${s.name}`)
  const sees = o.sees ?? vw.maps, results = o.results ?? []
  unknownNames([...sees, ...results], vw, 'isolation')
  const scalarsSeen = sees.filter(n => !vw.maps.includes(n))
  if (scalarsSeen.length) throw new Error(`isolation: ${scalarsSeen.join(', ')} isn't a map (what B sees of the state is its cells; a result after B's request goes in results)`)
  // (the owner as a key: a string's id, a natural)
  const keyOf = (x: unknown): Term => (x instanceof Term ? x : (x as {id?: Term}).id ?? (() => { throw new Error('isolation: the owner is a natural or a string') })())
  const mine = (env: Env): Cond => (typeof o.owner === 'string' ? keyOf(env[o.owner]).eq(env[tenant] as Term) : o.owner(env, env[tenant] as Term))
  if ([...s.params, ...s.inputs].some(([n]) => n === tenant)) throw new Error(`isolation: ${tenant} is a name of ${s.name} already (name the tenant's param: tenant)`)
  const base = new Rule({...s, params: [...s.params, [tenant, nat as Kind<unknown>]]}) as AnyRule
  const all2 = [...s.params, ...s.inputs].map(([n]) => n)
  const p = twoRuns(base, base, {name: `${s.name}: isolation of ${typeof o.owner === 'string' ? o.owner : 'the owner'}`, shared: [...all2, tenant], stays: env => not(mine(env)), refusals: o.refusals})
  const maps = new Set(vw.maps), name = o.name ?? `what ${typeof o.owner === 'string' ? o.owner : 'a tenant'} B sees is the same whatever the others do`
  const at = (env: Env) => env[tenant] as Term
  const laws = [...(sees.length ? [viewLaw(p, `${name}: ${sees.join(', ')} at B`, sees, maps, at)] : []), ...(o.refusals === 'assumed' ? [] : [refusalLaw(p)])]
  const stepLaws = results.length ? [p.stepLaw(`${name}: ${results.join(', ')} of B's requests`, (_b: Env, after: Env) => all(...results.map(n => same(after[`a_${n}`], after[`b_${n}`]))), (env: Env) => mine(env))] : []
  return {name, rule: p, laws, stepLaws, helpers: vw.maps.filter(n => !sees.includes(n)).map(n => viewLaw(p, `${n} at B is the same in both runs`, [n], maps, at)), sides: [base, base], shared: [...all2, tenant]}
}

// A migration: `next` agrees with `old` on every history: after the same requests, every value of the state they share
// by name (or `visible`) is the same, and they refuse the same requests. The requests and params of one name are one.
export function agreement(old: AnyRule, next: AnyRule, o: {visible?: string[], name?: string, refusals?: 'same' | 'assumed'} = {}): TwoRunLaw {
  const so = specOf(old), sn = specOf(next), vo = stateNames(so), vn = stateNames(sn)
  const common = (xs: string[], ys: string[]) => xs.filter(n => ys.includes(n))
  const visible = o.visible ?? [...common(vo.scalars, vn.scalars), ...common(vo.maps, vn.maps)]
  unknownNames(visible, vo, `agreement: ${so.name}`); unknownNames(visible, vn, `agreement: ${sn.name}`)
  const p = twoRuns(old, next, {name: `${sn.name} agrees with ${so.name}`, refusals: o.refusals})
  const maps = new Set(vo.maps), name = o.name ?? `${sn.name} agrees with ${so.name} on ${visible.join(', ')}`
  const kinds = new Map([...so.params, ...so.inputs]), shared = [...sn.params, ...sn.inputs].map(([n]) => n).filter(n => kinds.has(n))
  return {name, rule: p, laws: [viewLaw(p, name, visible, maps), ...(o.refusals === 'assumed' ? [] : [refusalLaw(p)])], stepLaws: [],
    helpers: [...common(vo.scalars, vn.scalars), ...common(vo.maps, vn.maps)].filter(n => !visible.includes(n)).map(n => viewLaw(p, `${n} is the same in both`, [n], maps)), sides: [old, next], shared}
}

// --- proving -----------------------------------------------------------------------------------------------------------

// A law of one run read in the rule built: its names renamed as the run's.
export function lift(l: Law, r: AnyRule, prefix: 'a_' | 'b_', shared: string[]): Law {
  const own = ownNames(specOf(r), new Set(shared)), n = (x: string) => (own.has(x) ? prefix + x : x)
  const e = (x: E): E => {
    switch (x.op) {
      case 'var': return {op: 'var', name: n(x.name)}
      case 'const': return x
      case 'mul': return {...x, a: e(x.a)}
      case 'if': return {op: 'if', c: c(x.c), then: e(x.then), else: e(x.else)}
      case 'get': return {op: 'get', map: n(x.map), key: e(x.key)}
      default: return {...x, a: e(x.a), b: e(x.b)}
    }
  }
  const c = (x: C): C => {
    switch (x.op) {
      case 'flag': return {op: 'flag', name: n(x.name)}
      case 'not': return {op: 'not', x: c(x.x)}
      case 'and': case 'or': return {op: x.op, xs: x.xs.map(c)}
      case 'all': return {...x, c: c(x.c), ...(x.witness ? {witness: e(x.witness)} : {})}
      default: return {...x, a: e(x.a), b: e(x.b)}
    }
  }
  if (l.some?.length) throw new Error(`${l.name}: a law with "there exists" isn't lifted to two runs`)
  return {name: `${prefix.slice(0, 1)}: ${l.name}`, holds: c(l.holds), ...(l.forall ? {forall: l.forall} : {}), ...(l.keys ? {keys: l.keys} : {})}
}
// The verdict on a law about two runs, with `invariants` (laws of each run's rule, an extraction's own) beside it. The
// helpers first (Houdini: the set proven together without the search, the one a failed goal names dropped, again), so a
// law that needs "this hidden value is the same in both runs" is proven with it; then the search, as proveSteps runs it.
// A run that breaks it is two runs side by side (`run`: its params and requests in the rule built's names).
export function proveTwoRuns(l: TwoRunLaw, opts: ProveOptions & {invariants?: [Law[], Law[]] | Law[]} = {}): Verdict & {given: Law[]} {
  const inv = opts.invariants === undefined ? [[], []] : Array.isArray(opts.invariants[0]) ? opts.invariants as [Law[], Law[]] : [opts.invariants as Law[], opts.invariants as Law[]]
  const lifted = [...inv[0].map(x => lift(x, l.sides[0], 'a_', l.shared)), ...inv[1].map(x => lift(x, l.sides[1], 'b_', l.shared))]
  let helpers = [...l.helpers]
  for (let round = 0; helpers.length && round <= l.helpers.length; round++) {
    const v = proveSteps(l.rule, [...lifted, ...helpers, ...l.laws], l.stepLaws, {search: false})
    if (v.proven && v.checked) return {...v, found: {...v.found, laws: [...v.found?.laws ?? [], ...helpers.map(h => ({law: h, text: h.name}))]}, given: lifted}
    const drop = helpers.find(h => v.goal?.startsWith(h.name))
    if (!drop) break
    helpers = helpers.filter(h => h !== drop)
  }
  const {invariants: _i, ...rest} = opts
  void _i
  return {...proveSteps(l.rule, [...lifted, ...l.laws], l.stepLaws, rest), given: lifted}
}

// --- certificates ------------------------------------------------------------------------------------------------------
// A proven set of laws (and step laws) of a rule as one interchange document (docs/interchange.md), the usual trees its
// proof, checked by the kernel as it is made: `meta` is kept beside it and never read by a checker (the clauses a law
// answers, where it is stated), so what a citation says is never what is trusted. Undefined where the kernel doesn't
// prove the set as given (a proof by k-induction, say, or one the search needed more for).
export function certify(r: AnyRule, laws: Law[], stepLaws: StepLaw[] = [], meta: Json = {}): Document | undefined {
  const env = (globalThis as unknown as {process?: {env: Record<string, string | undefined>}}).process?.env ?? {}
  const was = env.GDP_CERT
  env.GDP_CERT = 'usual'
  try {
    const rr = r.withSumsOf(laws, stepLaws), m = rr.machine, given = [...rr.kindLaws().filter(k => !laws.some(l => l.name === k.name)), ...laws]
    let c: Certificate
    if (stepLaws.length) {
      const p = proveStepLaws(m, given, stepLaws)
      if (!p.proven || !p.checked || !p.proof) return undefined
      c = {kind: 'stepLaws', machine: p.machine ?? m, laws: p.laws ?? given, stepLaws: p.stepLaws ?? stepLaws, proof: p.proof}
    } else {
      const p = proveLaws(m, given)
      if (!p.proven || !p.checked || !p.proof) return undefined
      c = {kind: 'laws', machine: p.machine ?? m, laws: p.laws ?? given, proof: {instances: p.proof.instances, trees: p.proof.trees}}
    }
    const doc = toInterchange(c, meta)
    return checkCertificate(fromInterchange(JSON.parse(JSON.stringify(doc)))).every(x => x.accepted) ? doc : undefined
  } finally { if (was === undefined) delete env.GDP_CERT; else env.GDP_CERT = was }
}
