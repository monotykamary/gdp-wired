// The structure track's first case: resource patterns that are lists of path segments, `<ns>:<path>`, `<path>/*`
// (exactly one more segment), `<path>/**` (one or more), `<ns>:*` (everything), and `covers(outer, inner)`, true when
// every concrete resource inner matches outer matches too: the namespaces agree, and either outer is everything or
// outer's segments are a prefix of inner's with the wildcards' room for the extra segments. A pattern's segments are a
// carried map from positions to interned names, its length an input. The laws a scope's attenuation rests on:
// covering is transitive, and a pattern covers itself.
import {type Cond, type Verdict, bool, everyKey, nat, oneOf, proveSteps, rule, when, yes, all} from '../../core/dsl.ts'

const pattern = (p: string) => ({[`ns${p}`]: nat, [`all${p}`]: bool, [`abs${p}`]: bool, [`w${p}`]: oneOf('none', 'one', 'any'), [`len${p}`]: nat})
export type ScopeBug = 'skips the prefix' | 'lets /* cover /**'
export const scopes = () => rule('resource patterns')
  .inputs({...pattern('A'), ...pattern('B'), ...pattern('C'), nsR: nat, absR: bool, lenR: nat})
  .carries('SA', 'SB', 'SC', 'SR')
  .state({z: 0})

/* eslint-disable @typescript-eslint/no-explicit-any */
// covers(outer, inner), as pi-fabric's scope.ts writes it.
export const covers = (env: any, o: string, i: string, bug?: ScopeBug): Cond => {
  const lo = env[`len${o}`], li = env[`len${i}`], wo = env[`w${o}`], wi = env[`w${i}`], So = env[`S${o}`], Si = env[`S${i}`]
  const prefix = bug === 'skips the prefix' ? lo.atMost(li) : lo.atMost(li).and(everyKey(k => k.lt(lo).implies(So.at(k).eq(Si.at(k)))))
  const room = wo.match({
    none: () => wi.is('none').and(li.eq(lo)),
    one: () => (wi.is('none').and(li.eq(lo.plus(1)))).or(bug === 'lets /* cover /**' ? wi.is('one').or(wi.is('any')).and(li.eq(lo)) : wi.is('one').and(li.eq(lo))),
    any: () => wi.is('none').implies(li.atLeast(lo.plus(1))),
  })
  return env[`ns${o}`].eq(env[`ns${i}`]).and(env[`all${o}`].or(env[`all${i}`].not().and(env[`abs${o}`].iff(env[`abs${i}`]), prefix, room)))
}

// What a pattern matches, written apart from `covers`: a concrete resource R (its segments SR, its length lenR, no
// wildcard) is matched by a pattern when the namespaces agree and the pattern is everything, or the pattern's segments
// start R's and R has the length its wildcard allows.
export const matches = (env: any, p: string): Cond => {
  const lp = env[`len${p}`], lr = env.lenR, S = env[`S${p}`]
  return env[`ns${p}`].eq(env.nsR).and(env[`all${p}`].or(env[`abs${p}`].iff(env.absR).and(
    everyKey(k => k.lt(lp).implies(S.at(k).eq(env.SR.at(k)))),
    env[`w${p}`].match({none: () => lr.eq(lp), one: () => lr.eq(lp.plus(1)), any: () => lr.atLeast(lp.plus(1))}))))
}

// The decision form (`decide`) above doesn't read conditions about every key, so the same laws as step laws of a rule
// whose flags are the three coverings, each prefix a condition about every key of its own.
export const scopeRule = (bug?: ScopeBug) => scopes()
  .flags(env => ({ab: covers(env, 'A', 'B', bug), bc: covers(env, 'B', 'C', bug), ac: covers(env, 'A', 'C', bug), aa: covers(env, 'A', 'A', bug)}))
  .flags(env => ({mA: matches(env, 'A'), mB: matches(env, 'B')}))
  .step(({z}) => ({z}))
export const scopeSteps = (r = scopeRule()) => [
  r.stepLaw('covering is transitive', ({ac}) => ac, ({ab, bc}) => ab.and(bc)),
  r.stepLaw('a pattern covers itself', ({aa}) => aa),
  r.stepLaw('what a covered pattern matches, the covering one matches', ({mA}) => mA, ({ab, mB}) => ab.and(mB)),
]

// Scopes as lists of grants: each grant a pattern and its actions (read, write, execute as bits), a scope's grants as
// tables keyed by grant (namespace, everything, absolute, wildcard 0/1/2, length, the three actions) and its segments
// as one table keyed by grant·W + position. deriveScope accepts a child only when each of its grants is covered, actions
// included, by some grant of the parent; scopeAllows allows an action on a resource when some grant has it and matches.
// The law attenuation rests on: what a derived scope allows, its parent allows. The two "some grant"s are witnesses: g,
// the child's grant that allows, and p, the parent's grant deriveScope found covering g.
export const W = 512
const fields = ['ns', 'all', 'abs', 'w', 'len', 'read', 'write', 'exec'] as const
export const grants = (bug?: 'ignores the actions') => rule('scope grants')
  .inputs({g: nat, p: nat, nsR: nat, absR: bool, lenR: nat, act: oneOf('read', 'write', 'exec')})
  .carries(...fields.map(f => `P${f}`), ...fields.map(f => `C${f}`), 'PS', 'CS', 'SR')
  .state({z: 0})
  .flags((env: any) => {
    const P = (f: string) => env[`P${f}`].at(env.p), C = (f: string) => env[`C${f}`].at(env.g)
    const pat = (F: (f: string) => any) => ({ns: F('ns'), all: F('all').eq(1), abs: F('abs').eq(1), w: F('w'), len: F('len')})
    const pp = pat(P), cp = pat(C)
    const prefixOf = (lo: any, So: any, bo: any, Si: any, bi: any) => everyKey(k => k.lt(lo).implies(So.at(k.plus(bo)).eq(Si.at(k.plus(bi)))))
    const room = (o: any, li: any, wi: any) => o.w.eq(0).and(wi.eq(0), li.eq(o.len)).or(o.w.eq(1).and(wi.eq(0).and(li.eq(o.len.plus(1))).or(wi.eq(1).and(li.eq(o.len)))), o.w.eq(2).and(wi.eq(0).implies(li.atLeast(o.len.plus(1)))))
    const has = (F: (f: string) => any) => env.act.match({read: () => F('read').eq(1), write: () => F('write').eq(1), exec: () => F('exec').eq(1)})
    const acts = bug === 'ignores the actions' ? yes : ['read', 'write', 'exec'].map(a => C(a).eq(1).implies(P(a).eq(1))).reduce((x: any, y: any) => x.and(y))
    const covered = pp.ns.eq(cp.ns).and(pp.all.or(cp.all.not().and(pp.abs.iff(cp.abs), pp.len.atMost(cp.len), prefixOf(pp.len, env.PS, env.p.times(W), env.CS, env.g.times(W)), room(pp, cp.len, cp.w))), acts)
    const matches = (o: any, So: any, bo: any) => o.ns.eq(env.nsR).and(o.all.or(o.abs.iff(env.absR).and(everyKey(k => k.lt(o.len).implies(So.at(k.plus(bo)).eq(env.SR.at(k)))), room(o, env.lenR, env.lenR.times(0)))))
    return {covered, childAllows: has(C).and(matches(cp, env.CS, env.g.times(W))), parentAllows: has(P).and(matches(pp, env.PS, env.p.times(W)))}
  })
  .assume((env: any) => everyKey(k => ['all', 'abs', 'read', 'write', 'exec'].map(f => env[`P${f}`].at(k).atMost(1).and(env[`C${f}`].at(k).atMost(1))).reduce((x: any, y: any) => x.and(y)).and(env.Pw.at(k).atMost(2), env.Cw.at(k).atMost(2), env.Plen.at(k).atMost(W), env.Clen.at(k).atMost(W))))
  .step(({z}) => ({z}))
export const grantSteps = (r = grants()) => [r.stepLaw('what a derived scope allows, its parent allows', ({parentAllows}) => parentAllows, ({covered, childAllows}) => covered.and(childAllows))]

// pi-fabric's covers (src/scope.ts), as it is written there, on parsed resources.
type Parsed = {ns: string, all: boolean, absolute: boolean, segments: string[], wildcard: 'none' | 'one' | 'any'}
export const piCovers = (outer: Parsed, inner: Parsed): boolean => {
  if (outer.ns !== inner.ns) return false
  if (outer.all) return true
  if (inner.all || outer.absolute !== inner.absolute) return false
  const prefix = outer.segments
  if (inner.segments.length < prefix.length || prefix.some((segment, index) => inner.segments[index] !== segment)) return false
  const extra = inner.segments.length - prefix.length
  if (outer.wildcard === 'none') return inner.wildcard === 'none' && extra === 0
  if (outer.wildcard === 'one') return inner.wildcard === 'none' ? extra === 1 : inner.wildcard === 'one' && extra === 0
  return inner.wildcard === 'none' ? extra >= 1 : true
}
// The rule above against it on random patterns over two namespaces and three segment names, the coverings and
// matchings computed by the compiled rule (each flag kept as a state value).
export function compareScopes(trials = 20000, seed = 7): {checked: number, failure?: string} {
  const r = scopes().flags(env => ({ab: covers(env, 'A', 'B'), bc: covers(env, 'B', 'C'), mA: matches(env, 'A')}))
    .step(({ab, bc, mA}) => ({z: when(ab, 1, 0).plus(when(bc, 2, 0)).plus(when(mA, 4, 0))}))
  const gen = r.compiled(), ps = r.encodeParams({} as never)
  let x = seed
  const draw = (k: number) => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * k) }
  const ws = ['none', 'one', 'any'] as const
  const pat = (): Parsed => { const all = draw(6) === 0; return {ns: 'ab'[draw(2)]!, all, absolute: draw(2) === 1, segments: all ? [] : Array.from({length: draw(4)}, () => 'xyz'[draw(3)]!), wildcard: all ? 'none' : ws[draw(3)]!} }
  const enc = (p: Parsed, n: string) => ({[`ns${n}`]: p.ns === 'a' ? 0 : 1, [`all${n}`]: p.all, [`abs${n}`]: p.absolute, [`w${n}`]: p.wildcard, [`len${n}`]: p.segments.length, [`S${n}`]: new Map(p.segments.map((g, i) => [i, 1 + 'xyz'.indexOf(g)]))})
  for (let t = 0; t < trials; t++) {
    const a = pat(), b = pat(), c = pat(), res = {...pat(), wildcard: 'none' as const, all: false}
    const values = {...enc(a, 'A'), ...enc(b, 'B'), ...enc(c, 'C'), nsR: res.ns === 'a' ? 0 : 1, absR: res.absolute, lenR: res.segments.length, SR: new Map(res.segments.map((g, i) => [i, 1 + 'xyz'.indexOf(g)]))}
    const z = r.decode(gen.step(ps, gen.init(ps), r.encodeInput(values as never, {} as never))).z as number
    const want = Number(piCovers(a, b)) + 2 * Number(piCovers(b, c)) + 4 * Number(piCovers(a, res))
    if (z !== want) return {checked: t, failure: `${JSON.stringify({a, b, c, res})}: ${z} here, ${want} in pi-fabric`}
  }
  return {checked: trials}
}

// The grant tables against pi-fabric's grantCovered and scopeAllows for one pair of grants: random scopes of up to four
// grants, a random child grant g and parent grant p, a random resource and action.
export function compareGrants(trials = 5000, seed = 11): {checked: number, failure?: string} {
  const r = grants().step(({covered, childAllows, parentAllows}: any) => ({z: when(covered, 1, 0).plus(when(childAllows, 2, 0)).plus(when(parentAllows, 4, 0))}))
  const gen = r.compiled(), ps = r.encodeParams({} as never)
  let x = seed
  const draw = (k: number) => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * k) }
  const ws = ['none', 'one', 'any'] as const, acts = ['read', 'write', 'exec'] as const
  type Grant = Parsed & {actions: string[]}
  const grant = (): Grant => { const all = draw(6) === 0; return {ns: 'ab'[draw(2)]!, all, absolute: draw(2) === 1, segments: all ? [] : Array.from({length: draw(4)}, () => 'xyz'[draw(3)]!), wildcard: all ? 'none' : ws[draw(3)]!, actions: acts.filter(() => draw(2) === 1)} }
  const table = (gs: Grant[], n: string) => ({
    ...Object.fromEntries(fields.map(f => [`${n}${f}`, new Map(gs.map((q, i) => [i, f === 'ns' ? Number(q.ns === 'b') : f === 'all' ? Number(q.all) : f === 'abs' ? Number(q.absolute) : f === 'w' ? ws.indexOf(q.wildcard) : f === 'len' ? q.segments.length : Number(q.actions.includes(f))]))])),
    [`${n}S`]: new Map(gs.flatMap((q, i) => q.segments.map((g, j) => [i * W + j, 1 + 'xyz'.indexOf(g)] as [number, number]))),
  })
  for (let t = 0; t < trials; t++) {
    const P = Array.from({length: 1 + draw(4)}, grant), C = Array.from({length: 1 + draw(4)}, grant), p = draw(P.length), g = draw(C.length)
    const res: Parsed = {ns: 'ab'[draw(2)]!, all: false, absolute: draw(2) === 1, segments: Array.from({length: draw(5)}, () => 'xyz'[draw(3)]!), wildcard: 'none'}, act = acts[draw(3)]!
    const values = {...table(P, 'P'), ...table(C, 'C'), g, p, act, nsR: Number(res.ns === 'b'), absR: res.absolute, lenR: res.segments.length, SR: new Map(res.segments.map((q, i) => [i, 1 + 'xyz'.indexOf(q)]))}
    const z = r.decode(gen.step(ps, gen.init(ps), r.encodeInput(values as never, {} as never))).z as number
    const pg = P[p]!, cg = C[g]!
    const want = Number(cg.actions.every(a => pg.actions.includes(a)) && piCovers(pg, cg)) + 2 * Number(cg.actions.includes(act) && piCovers(cg, res)) + 4 * Number(pg.actions.includes(act) && piCovers(pg, res))
    if (z !== want) return {checked: t, failure: `${JSON.stringify({pg, cg, res, act})}: ${z} here, ${want} in pi-fabric`}
  }
  return {checked: trials}
}


// Normalizing a scope (pi-fabric's normalizeGrants: grants of one resource merged, their actions joined, sorted by
// resource) changes nothing it allows. A permutation is no condition about every key on its own; the normalizer's
// bookkeeping is: `To[g]`, the normalized grant original grant g went to, and `From<a>[n]`, an original grant that gave
// normalized grant n the action a. Grants name their resource by its interned id (`Orid`, `Nrid`), as the normalizer
// merges by the resource string, and the patterns are a table keyed by resource id (each one's segments from its
// offset `RB` in one segment table): the parse is a function of the string. The rule checks the bookkeeping at every
// key, and the law follows at the witnesses: what the original allows through grant g and its resource rid, the
// normalized allows through To[g] and rid; what the normalized allows through n, the original allows through From<a>[n].
const acts = ['read', 'write', 'exec'] as const
export const normalized = (bug?: 'drops an action when merging' | 'merges two resources') => rule('normalized scope')
  .inputs({g: nat, n: nat, rid: nat, nsR: nat, absR: bool, lenR: nat, act: oneOf('read', 'write', 'exec'), sizeO: nat, sizeN: nat})
  .carries('Rns', 'Rall', 'Rabs', 'Rw', 'Rlen', 'RB', 'Seg', 'SR', 'Orid', 'Nrid', ...acts.map(a => `O${a}`), ...acts.map(a => `N${a}`), 'To', ...acts.map(a => `From${a}`))
  .state({z: 0})
  .flags((env: any) => {
    const pat = (rid: any) => ({ns: env.Rns.at(rid), all: env.Rall.at(rid).eq(1), abs: env.Rabs.at(rid).eq(1), w: env.Rw.at(rid), len: env.Rlen.at(rid), base: env.RB.at(rid)})
    const room = (o: any, li: any) => o.w.eq(0).and(li.eq(o.len)).or(o.w.eq(1).and(li.eq(o.len.plus(1))), o.w.eq(2).and(li.atLeast(o.len.plus(1))))
    const matches = (rid: any) => { const o = pat(rid); return o.ns.eq(env.nsR).and(o.all.or(o.abs.iff(env.absR).and(everyKey(k => k.lt(o.len).implies(env.Seg.at(k.plus(o.base)).eq(env.SR.at(k)))), room(o, env.lenR)))) }
    const has = (side: string, i: any) => env.act.match({read: () => env[`${side}read`].at(i).eq(1), write: () => env[`${side}write`].at(i).eq(1), exec: () => env[`${side}exec`].at(i).eq(1)})
    return {
      // Each original grant's resource is its normalized grant's, and its actions are there too.
      toOk: everyKey(i => { const to = env.To.at(i); return i.lt(env.sizeO).implies(all(to.lt(env.sizeN), bug === 'merges two resources' ? yes : env.Nrid.at(to).eq(env.Orid.at(i)),
        ...acts.filter(a => !(bug === 'drops an action when merging' && a === 'exec')).map(a => env[`O${a}`].at(i).eq(1).implies(env[`N${a}`].at(to).eq(1))))) }),
      // Each action of a normalized grant came from an original grant of the same resource.
      fromOk: everyKey(j => j.lt(env.sizeN).implies(all(...acts.map(a => { const src = env[`From${a}`].at(j); return env[`N${a}`].at(j).eq(1).implies(all(src.lt(env.sizeO), env.Orid.at(src).eq(env.Nrid.at(j)), env[`O${a}`].at(src).eq(1))) })))),
      // A grant allows through the resource rid when it has the action, names rid, and rid's pattern matches.
      matched: matches(env.rid),
      originalAllows: env.g.lt(env.sizeO).and(has('O', env.g), env.Orid.at(env.g).eq(env.rid)),
      normalizedAllowsTo: has('N', env.To.at(env.g)).and(env.Nrid.at(env.To.at(env.g)).eq(env.rid)),
      normalizedAllows: env.n.lt(env.sizeN).and(has('N', env.n), env.Nrid.at(env.n).eq(env.rid)),
      originalAllowsFrom: env.act.match(Object.fromEntries(acts.map(a => [a, () => { const src = env[`From${a}`].at(env.n); return src.lt(env.sizeO).and(env[`O${a}`].at(src).eq(1), env.Orid.at(src).eq(env.rid)) }])) as never),
    }
  })
  .assume((env: any) => everyKey(k => all(env.Rall.at(k).atMost(1), env.Rabs.at(k).atMost(1), env.Rw.at(k).atMost(2), ...acts.flatMap(a => [env[`O${a}`].at(k).atMost(1), env[`N${a}`].at(k).atMost(1)]))))
  .step(({z}) => ({z}))
export const normalizedSteps = (r = normalized()) => [
  r.stepLaw('what the original allows, the normalized allows', ({normalizedAllowsTo, matched}) => normalizedAllowsTo.and(matched), ({toOk, originalAllows, matched}) => toOk.and(originalAllows, matched)),
  // One law per action: the action picks which From map names the original grant.
  ...acts.map(a => r.stepLaw(`what the normalized allows to ${a}, the original allows`, ({originalAllowsFrom, matched}) => originalAllowsFrom.and(matched), ({act, fromOk, normalizedAllows, matched}) => act.is(a).and(fromOk, normalizedAllows, matched))),
]

if (import.meta.main) {
  console.log('grants against pi-fabric:', JSON.stringify(compareGrants()))
  console.log('against pi-fabric:', JSON.stringify(compareScopes()))
  for (const bug of [undefined, 'drops an action when merging'] as const) {
    const r = normalized(bug)
    for (const s of normalizedSteps(r)) {
      const t = performance.now(), v = proveSteps(r as never, [], [s])
      console.log(`${bug ?? 'faithful'} | ${s.name}: ${v.proven && v.checked ? 'proven' : `not proven (${v.goal} ${v.stuck ?? ''})`} ${Math.round(performance.now() - t)} ms`)
    }
  }
  for (const bug of [undefined, 'ignores the actions'] as const) {
    const r = grants(bug), t = performance.now(), v = proveSteps(r as never, [], grantSteps(r))
    console.log(`${bug ?? 'faithful'} | attenuation: ${v.proven && v.checked ? 'proven' : `not proven (${v.goal} ${v.stuck ?? ''})`} ${Math.round(performance.now() - t)} ms`)
  }
  for (const bug of [undefined, 'skips the prefix', 'lets /* cover /**'] as const) {
    const r = scopeRule(bug)
    for (const s of scopeSteps(r)) {
      const t = performance.now(), v: Verdict = proveSteps(r, [], [s])
      console.log(`${bug ?? 'faithful'} | ${s.name}: ${v.proven && v.checked ? 'proven' : `not proven (${v.stuck ?? ''} ${JSON.stringify(v.witness ?? {})})`} ${Math.round(performance.now() - t)} ms`)
    }
  }
}
