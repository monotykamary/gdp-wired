// Resource scopes whose resources are paths: pi-fabric's patterns (src/scope.ts: `<ns>:<path>`, `<path>/*` for exactly
// one more segment, `<path>/**` for one or more, `<ns>:*` for everything) and `covers(outer, inner)`, true when every
// concrete resource inner matches, outer matches too. A pattern's segments are a sequence (`carriesSeq`, interned
// names), so a prefix is a condition about every position below a length and no law here needs induction or a lemma.
// For the suite (`bun examples/scopes.ts`), core/seqs.test.ts and lean-kernel/package-check.ts.
//   - patterns: covering is transitive and reflexive, and what a covered pattern matches the covering one matches
//     (matching written apart from covers); the broken variants let `/*` cover `/**`, or skip the prefix
//   - grants: scopes as lists of grants, each a pattern with actions, a grant's segments a row of a table of sequences
//     (`carriesSeqs`); a derived scope's grants are each covered, actions included, by some parent grant, and what it
//     allows, its parent allows (the two "some grant"s as witnesses); the broken variant ignores the actions
//   - normalizing (pi-fabric's normalizeGrants: grants of one resource merged, their actions joined, sorted) changes
//     nothing a scope allows, both ways, with the normalizer's bookkeeping as data the rule checks at every key: where
//     each grant went, and where each merged action came from; the broken variant drops an action when merging
import {type Cond, type Decision, type SeqRef, type Term, all, bool, everyBelow, nat, oneOf, record, rule, when} from '../core/dsl.ts'

export const Pattern = record({ns: nat, all: bool, abs: bool, w: oneOf('none', 'one', 'any')})
type P = ReturnType<typeof Pattern.value>
// A pattern: its fields and its segments.
type Pat = {f: P, s: SeqRef}
// A concrete resource: a namespace, absolute or not, its segments.
type Res = {ns: Term, abs: Cond, s: SeqRef}
export type PatternBug = 'lets /* cover /**' | 'skips the prefix'

// How many segments past the outer pattern's the inner one may have, by the outer's wildcard.
const room = (o: Pat, len: Term, inner: P['w'] | 'none'): Cond => o.f.w.match({
  none: () => (inner === 'none' ? len.eq(o.s.len) : inner.is('none').and(len.eq(o.s.len))),
  one: () => (inner === 'none' ? len.eq(o.s.len.plus(1)) : inner.is('none').and(len.eq(o.s.len.plus(1))).or(inner.is('one').and(len.eq(o.s.len)))),
  any: () => (inner === 'none' ? len.atLeast(o.s.len.plus(1)) : inner.is('none').implies(len.atLeast(o.s.len.plus(1)))),
})
// covers(outer, inner), as src/scope.ts writes it.
export const covers = (o: Pat, i: Pat, bug?: PatternBug): Cond => {
  const prefix = bug === 'skips the prefix' ? o.s.len.atMost(i.s.len) : o.s.prefixOf(i.s)
  const wild = bug === 'lets /* cover /**' ? o.f.w.match({none: () => room(o, i.s.len, i.f.w), one: () => i.f.w.is('none').and(i.s.len.eq(o.s.len.plus(1))).or(i.f.w.is('none').not().and(i.s.len.eq(o.s.len))), any: () => room(o, i.s.len, i.f.w)}) : room(o, i.s.len, i.f.w)
  return o.f.ns.eq(i.f.ns).and(o.f.all.or(i.f.all.not().and(o.f.abs.iff(i.f.abs), prefix, wild)))
}
// What a pattern matches, written apart from covers: the namespaces agree and it is everything, or its segments start
// the resource's and the resource has the length its wildcard allows.
export const matches = (o: Pat, r: Res): Cond => o.f.ns.eq(r.ns).and(o.f.all.or(o.f.abs.iff(r.abs).and(o.s.prefixOf(r.s), room(o, r.s.len, 'none'))))

export const patterns = () => rule('resource patterns').inputs({A: Pattern, B: Pattern, C: Pattern, nsR: nat, absR: bool}).carriesSeq('SA', 'SB', 'SC', 'SR')
type PEnv = Parameters<Parameters<ReturnType<typeof patterns>['decide']>[1]>[0]
const pat = (env: PEnv, n: 'A' | 'B' | 'C'): Pat => ({f: env[n], s: env[`S${n}`]})
const res = (env: PEnv): Res => ({ns: env.nsR, abs: env.absR, s: env.SR})
export const patternLaws = (bug?: PatternBug, r = patterns()): Decision[] => [
  r.decide('covering is transitive', env => [covers(pat(env, 'A'), pat(env, 'B'), bug), covers(pat(env, 'B'), pat(env, 'C'), bug)], env => covers(pat(env, 'A'), pat(env, 'C'), bug)),
  r.decide('a pattern covers itself', () => [], env => covers(pat(env, 'A'), pat(env, 'A'), bug)),
  r.decide('what a covered pattern matches, the covering one matches', env => [covers(pat(env, 'A'), pat(env, 'B'), bug), matches(pat(env, 'B'), res(env))], env => matches(pat(env, 'A'), res(env))),
]

// Scopes as lists of grants. g is the child's grant that allows, p the parent's grant deriveScope found covering it
// (each one of its list's: an item's own laws, a yes/no being 0 or 1, hold below the list's length).
const acts = ['read', 'write', 'exec'] as const
export const Grant = record({ns: nat, all: bool, abs: bool, w: oneOf('none', 'one', 'any'), read: bool, write: bool, exec: bool})
export const grants = () => rule('scope grants').inputs({g: nat, p: nat, nsR: nat, absR: bool, act: oneOf(...acts)})
  .carriesList('Parent', Grant).carriesList('Child', Grant).carriesSeqs('ParentPaths', 'ChildPaths').carriesSeq('SR')
type GEnv = Parameters<Parameters<ReturnType<typeof grants>['decide']>[1]>[0]
type GrantValue = ReturnType<GEnv['Parent']['at']>
const has = (x: GrantValue, act: GEnv['act']): Cond => act.match({read: () => x.read, write: () => x.write, exec: () => x.exec})
export const grantLaws = (bug?: 'ignores the actions', r = grants()): Decision[] => [
  r.decide('what a derived scope allows, its parent allows', env => {
    const pg = env.Parent.at(env.p), cg = env.Child.at(env.g), parent: Pat = {f: pg, s: env.ParentPaths.row(env.p)}, child: Pat = {f: cg, s: env.ChildPaths.row(env.g)}
    const actions = bug ? [] : acts.map(a => cg[a].implies(pg[a]))
    return [all(covers(parent, child), ...actions), env.p.lt(env.Parent.len), env.g.lt(env.Child.len), has(cg, env.act), matches(child, {ns: env.nsR, abs: env.absR, s: env.SR})]
  }, env => has(env.Parent.at(env.p), env.act).and(matches({f: env.Parent.at(env.p), s: env.ParentPaths.row(env.p)}, {ns: env.nsR, abs: env.absR, s: env.SR}))),
]

// Normalizing: grants name their resource by its interned id (the normalizer merges by the resource string), the
// patterns a list keyed by resource id with their segments a table's rows (the parse is a function of the string). To:
// for each original grant, the normalized grant it went to; From: for each normalized grant and action, an original
// grant that gave it the action. rid is the resource the allowing grant names (one of the table's), g and n the grants.
const Held = record({rid: nat, read: bool, write: bool, exec: bool})
export const normalized = () => rule('normalized scope').inputs({g: nat, n: nat, rid: nat, nsR: nat, absR: bool, act: oneOf(...acts)})
  .carriesList('Res', Pattern).carriesSeqs('ResPaths').carriesList('Original', Held).carriesList('Normal', Held)
  .carriesList('To', nat).carriesList('From', record({read: nat, write: nat, exec: nat})).carriesSeq('SR')
type NEnv = Parameters<Parameters<ReturnType<typeof normalized>['decide']>[1]>[0]
const holds = (x: ReturnType<NEnv['Original']['at']>, act: NEnv['act']): Cond => act.match({read: () => x.read, write: () => x.write, exec: () => x.exec})
const matched = (env: NEnv): Cond => matches({f: env.Res.at(env.rid), s: env.ResPaths.row(env.rid)}, {ns: env.nsR, abs: env.absR, s: env.SR})
export const normalizedLaws = (bug?: 'drops an action when merging', r = normalized()): Decision[] => {
  // Each original grant's resource is its normalized grant's, and its actions are there too.
  const toOk = (env: NEnv) => everyBelow(env.Original.len, i => { const to = env.To.at(i), o = env.Original.at(i), m = env.Normal.at(to)
    return all(to.lt(env.Normal.len), m.rid.eq(o.rid), ...acts.filter(a => !(bug && a === 'exec')).map(a => o[a].implies(m[a]))) })
  // Each action of a normalized grant came from an original grant of the same resource.
  const fromOk = (env: NEnv) => everyBelow(env.Normal.len, j => all(...acts.map(a => { const src = env.From.at(j)[a], m = env.Normal.at(j), o = env.Original.at(src)
    return m[a].implies(all(src.lt(env.Original.len), o.rid.eq(m.rid), o[a])) })))
  return [
    r.decide('what a scope allows, its normalized form allows', env => { const o = env.Original.at(env.g); return [toOk(env), env.g.lt(env.Original.len), env.rid.lt(env.Res.len), holds(o, env.act), o.rid.eq(env.rid), matched(env)] },
      env => { const m = env.Normal.at(env.To.at(env.g)); return holds(m, env.act).and(m.rid.eq(env.rid), matched(env)) }),
    // One law per action: the action picks which From names the original grant.
    ...acts.map(a => r.decide(`what the normalized form allows to ${a}, the scope allows`, env => { const m = env.Normal.at(env.n); return [env.act.is(a), fromOk(env), env.n.lt(env.Normal.len), env.rid.lt(env.Res.len), m[a], m.rid.eq(env.rid), matched(env)] },
      env => { const src = env.From.at(env.n)[a], o = env.Original.at(src); return all(src.lt(env.Original.len), o[a], o.rid.eq(env.rid), matched(env)) })),
  ]
}

// pi-fabric's covers (src/scope.ts), as it is written there, on parsed resources.
export type Parsed = {ns: string, all: boolean, absolute: boolean, segments: string[], wildcard: 'none' | 'one' | 'any'}
export const piCovers = (outer: Parsed, inner: Parsed): boolean => {
  if (outer.ns !== inner.ns) return false
  if (outer.all) return true
  if (inner.all || outer.absolute !== inner.absolute) return false
  const prefix = outer.segments
  if (inner.segments.length < prefix.length || prefix.some((segment, index) => inner.segments[index] !== segment)) return false
  const extra = inner.segments.length - prefix.length
  if (outer.wildcard === 'none') return inner.wildcard === 'none' && extra === 0
  // `/*` covers exactly one more segment; `/**` covers one or more.
  if (outer.wildcard === 'one') return inner.wildcard === 'none' ? extra === 1 : inner.wildcard === 'one' && extra === 0
  return inner.wildcard === 'none' ? extra >= 1 : true
}
// The rule's covers against it on random patterns over two namespaces and three segment names: the compiled rule keeps
// covers(A, B), covers(B, C) and A matching a resource as one state value.
export function comparePatterns(trials = 20000, seed = 7): {checked: number, failure?: string} {
  const r = patterns().state({z: 0})
    .flags(env => ({ab: covers(pat(env, 'A'), pat(env, 'B')), bc: covers(pat(env, 'B'), pat(env, 'C')), mA: matches(pat(env, 'A'), res(env))}))
    .step(({ab, bc, mA}) => ({z: when(ab, 1, 0).plus(when(bc, 2, 0)).plus(when(mA, 4, 0))}))
  const gen = r.compiled(), ps = r.encodeParams({})
  let x = seed
  const draw = (k: number) => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * k) }
  const ws = ['none', 'one', 'any'] as const, name = (g: string) => 1 + 'xyz'.indexOf(g)
  const parsed = (): Parsed => { const every = draw(6) === 0; return {ns: 'ab'[draw(2)]!, all: every, absolute: draw(2) === 1, segments: every ? [] : Array.from({length: draw(4)}, () => 'xyz'[draw(3)]!), wildcard: every ? 'none' : ws[draw(3)]!} }
  const fields = (p: Parsed) => ({ns: Number(p.ns === 'b'), all: p.all, abs: p.absolute, w: p.wildcard})
  for (let t = 0; t < trials; t++) {
    const a = parsed(), b = parsed(), c = parsed(), resource: Parsed = {...parsed(), all: false, wildcard: 'none'}
    const values = {A: fields(a), B: fields(b), C: fields(c), nsR: Number(resource.ns === 'b'), absR: resource.absolute, SA: a.segments.map(name), SB: b.segments.map(name), SC: c.segments.map(name), SR: resource.segments.map(name)}
    const z = r.decode(gen.step(ps, gen.init(ps), r.encodeInput(values))).z as number
    const want = Number(piCovers(a, b)) + 2 * Number(piCovers(b, c)) + 4 * Number(piCovers(a, resource))
    if (z !== want) return {checked: t, failure: `${JSON.stringify({a, b, c, resource})}: ${z} here, ${want} in pi-fabric`}
  }
  return {checked: trials}
}

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  const prove = async (what: string, ds: Decision[], want: boolean) => {
    const {proveDecision} = await import('../core/dsl.ts')
    for (const d of ds) { const t = performance.now(), v = proveDecision(d); results.push([`${what}: ${d.name} (${Math.round(performance.now() - t)} ms)`, v.proven && v.checked, want]) }
  }
  await prove('patterns', patternLaws(), true)
  await prove('patterns, /* covering /**', patternLaws('lets /* cover /**').filter(d => d.name !== 'a pattern covers itself'), false)
  await prove('patterns, the prefix skipped', patternLaws('skips the prefix').filter(d => d.name.startsWith('what')), false)
  await prove('grants', grantLaws(), true)
  await prove('grants, the actions ignored', grantLaws('ignores the actions'), false)
  await prove('normalizing', normalizedLaws(), true)
  await prove('normalizing, an action dropped', normalizedLaws('drops an action when merging').slice(0, 1), false)
  const agreed = comparePatterns()
  results.push([`covers against pi-fabric's, ${agreed.checked} random triples${agreed.failure ? `: ${agreed.failure}` : ''}`, !agreed.failure, true])
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
