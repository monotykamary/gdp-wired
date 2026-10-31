// The candidate pipeline (untrusted): the counted search, for a machine with counts (the kernel's countedObligations
// and checkCountedLaws, Lean's CountMachine.lean), and the ∃ search's cone (core/dsl.ts's someCone) are one pipeline:
//   1. the small instances (core/exists.ts's smallOf: each param 2 and 3, inputs and carried sets below 3), the one
//      filter of every candidate, witness and ghost map;
//   2. the candidates (`candidates`): one list from the machine's shapes, each true on every small state: each map's
//      cells at most what the instances reach; a guard's count comparison (`guardLaws`): a step writes P[t] where a
//      quantified flag says every member of a set the request counts satisfies R(member, t) and the assumption compares
//      that count with a bound (2·|Q| > size, |Q| ≥ n − t, …), so c_R(x) = |{k < bound: R(k, x)}| is declared and
//      P[a] ⇒ the comparison with c_R[a] proposed, and a guard comparing a state count at the written key, that
//      comparison at a; one key a row; the engine's minimal ∀ cubes of at most two literals (core/infer.ts's), their
//      guards loosened where a caller reads the key unbounded;
//   3. a goal's instances (`attempt`): the quantified flags at the law's own terms, then only what each model of the
//      goal asks (kernel/prove.ts's modelInstances, MBQI, while the attempt's time lasts, a second at least); a
//      goal the CDCL search refutes cut to the instances its core reads, its core's tree widened to it;
//   4. the cone (`cone`): each candidate kept where it is proven from the kept ones and itself (IC3's relative
//      induction), the proof the caller's (the counted goals here, the kernel's for an ∃ law's cubes), in two thirds of
//      what is left; then, for the counted search, Houdini over the rest; the kernel checks the set (checkCountedLaws).
import {type C, type E, type Law, type Machine} from './machine.ts'
import {type CountCert, type CountInst, type Goal, type Instances, type MapRead, assumed, checkCountedLaws, countedObligations, mcGoal, substC} from '../kernel/kernel.ts'
import {clock, grow, modelInstances, widen} from '../kernel/prove.ts'
import {REFUTED, type Refuted, cdclStats, growCdcl} from '../kernel/cdcl.ts'
import {inferLaws} from './infer.ts'
import {smallOf, trueSmall} from './exists.ts'
import {env} from './solver.ts'

// (GDP_COUNTS_PROF: where a counted search's time goes, by phase, on stderr at the end; `countsDump.on`, set by research's
// profiles: each step goal left unknown or with a model past GDP_COUNTS_DUMP_MIN (300) hypotheses, the first GDP_COUNTS_DUMP_N (3))
export const cprof: Record<string, number> = {}
export const countsDump: {on?: (goal: object) => void} = {}
const ptime = <T>(k: string, f: () => T): T => { const t = performance.now(); try { return f() } finally { cprof[k] = (cprof[k] ?? 0) + performance.now() - t } }
let dumped = 0

const v = (name: string): E => ({op: 'var', name}), k = (value: number): E => ({op: 'const', value})
const json = (t: unknown) => JSON.stringify(t)
const one = k(1), zero = k(0)

// Every term t with `get(map, t)` in t0.
function reads(t0: unknown, map: (m: string) => boolean, out: Map<string, [string, E]> = new Map()): Map<string, [string, E]> {
  const go = (x: unknown): void => {
    if (!x || typeof x !== 'object') return
    const o = x as Record<string, unknown>
    if (o.op === 'get' && map(o.map as string)) out.set(json([o.map, o.key]), [o.map as string, o.key as E])
    for (const y of Object.values(o)) go(y)
  }
  go(t0)
  return out
}
const mentions = (t: unknown, name: string) => json(t).includes(`"name":${json(name)}`)
const atoms = (c: C): C[] => (c.op === 'and' || c.op === 'or' ? c.xs.flatMap(atoms) : c.op === 'not' ? atoms(c.x) : [c])

// --- candidates from the guard's shape -----------------------------------------------------------------------------------
export function guardLaws(m: Machine): {counts: Machine['counts'], laws: Law[]} {
  const counts: NonNullable<Machine['counts']> = {}, laws: Law[] = []
  const flags = m.step.flags ?? {}, fsub = {vars: {}, maps: {}, flags: Object.fromEntries(Object.entries(flags).map(([f, fc]) => [f, fc.op === 'all' ? {op: '=', a: v(`?${f}`), b: one} as C : fc]))}
  const inline = (c: C): C => { let x = c; for (let i = 0; i < 4 && json(x).includes('"op":"flag"'); i++) x = substC(x, fsub); return x }
  const guards = m.assume ? atoms(m.assume).filter(a => a.op === '<' || a.op === '<=') : []
  const isCount = (mp: string) => !!m.counts?.[mp]
  const when = (name: string, h: C, cmp: C): Law => ({name, forall: 'a$c', holds: {op: 'or', xs: [{op: 'not', x: h}, cmp]}})
  // A stored set: a write at every key that copies a request's counted set (its value reads the count's body at the key)
  // keeps what the guard asked of it. Its state count, below the same bound, in place of the request's in each guard
  // comparison, is proposed under each member of the set and each scalar literal the flags read (started = 1); and that
  // comparison is a guard the quantified flags below read too (a leader whose votes cover the stored set).
  const all = {...m.counts}, more: C[] = []
  const lits = [...new Map(Object.values(flags).flatMap(f => (f.op === 'all' ? [] : atoms(f))).filter(a => a.op === '=' && a.a.op === 'var' && a.a.name in m.state && a.b.op === 'const').map(a => [json(a), a])).values()]
  for (const [mp, w] of Object.entries(m.step.maps ?? {})) {
    if (!('each' in w)) continue
    for (const [c, d] of Object.entries(m.counts ?? {})) {
      if (d.body.op !== 'if' || !json(w.value).includes(json(substC(d.body.c, {vars: {[d.key]: v(w.each)}, maps: {}, flags: {}})))) continue
      const name = `${c}$${mp}`, key = `${name}$k`, member = (x: string): C => ({op: '=', a: {op: 'get', map: mp, key: v(x)}, b: one}), mine = member('a$c')
      all[name] = counts[name] = {j: `${name}$x`, key, below: d.below, body: {op: 'if', c: member(key), then: one, else: zero}}
      for (const g of guards) if (reads(g, x => x === c).size) {
        const g2 = substC(g, {vars: {}, maps: {[c]: () => ({op: 'get', map: name, key: v('a$c')})}, flags: {}})
        more.push(g2)
        for (const [i, h] of [mine, ...lits].entries()) laws.push(when(`${name} keeps ${c}'s bound ${i}`, h, g2))
      }
    }
  }
  for (const [mp, w] of Object.entries(m.step.maps ?? {})) {
    if ('each' in w || w.key.op !== 'var' || !m.inputs.includes(w.key.name)) continue
    const t = w.key.name, written = inline({op: '<=', a: one, b: w.value} as C)
    const law = (name: string, cmp: C): Law => when(name, {op: '<=', a: one, b: {op: 'get', map: mp, key: v('a$c')}}, cmp)
    // A comparison with a state count at the written key.
    for (const g of guards) for (const [, [c, key]] of reads(g, isCount)) {
      if (json(key) !== json(v(t)) || mentions(m.counts![c]!.body, t)) continue
      if (m.inputs.some(i => i !== t && mentions(g, i))) continue
      laws.push(law(`${mp} keeps ${c}'s bound`, substC(g, {vars: {[t]: v('a$c')}, maps: {}, flags: {}})))
    }
    // A quantified flag the write reads: every member of a counted set satisfies R(member, t).
    for (const [f, q] of Object.entries(flags)) {
      if (q.op !== 'all' || q.keys?.length || !mentions(written, `?${f}`) || q.c.op !== 'or' || q.c.xs.length !== 2) continue
      const [h, r] = q.c.xs[0]!.op === 'not' ? [q.c.xs[0]!.x, q.c.xs[1]!] : [q.c.xs[1]!.op === 'not' ? q.c.xs[1]!.x : undefined, q.c.xs[0]!]
      if (!h || !r) continue
      for (const [c, d] of Object.entries(all)) {
        // the set: the count's body is the flag's hypothesis at its key
        const body = d.body.op === 'if' ? d.body.c : undefined
        if (!body || json(substC(body, {vars: {[d.key]: v(q.key)}, maps: {}, flags: {}})) !== json(h)) continue
        if (m.inputs.some(i => i !== t && mentions(r, i))) continue
        const name = `${c}$${mp}`, j = `${name}$x`, key = `${name}$k`
        counts[name] = {j, key, below: d.below, body: {op: 'if', c: substC(r, {vars: {[q.key]: v(key), [t]: v(j)}, maps: {}, flags: {}}), then: one, else: zero}}
        for (const g of [...guards, ...more]) if (reads(g, x => x === c).size)
          laws.push(law(`${mp} keeps ${c}'s bound through ${name}`, substC(g, {vars: {}, maps: {[c]: () => ({op: 'get', map: name, key: v('a$c')})}, flags: {}})))
      }
    }
  }
  return {counts, laws}
}

// --- a goal's certificate -------------------------------------------------------------------------------------------------
// The count cells the goal reads (each before the step with its post name's twin), instances over pairs of them with one
// bound (a count that doesn't drop, +1 and −1; two that meet, +1, +1 and −1), each with a fresh witness; and the laws and
// quantified flags at the witnesses (returned, for the goal's law's instances).
export function certFor(goal: {hyps: C[]}, decls: {map: string, below: E, j: string, body: E}[]): {reads: MapRead[], insts: CountInst[], wits: string[]} {
  const byMap = new Map(decls.map(d => [d.map, d])), last = goal.hyps.at(-1)
  // (the conclusion's reads first, then those at a constant or the law's own names, then the rest)
  const own = (t: E) => t.op === 'const' || (t.op === 'var' && json(last).includes(`"name":${json(t.name)}`))
  const all0 = [...reads(goal.hyps, mp => byMap.has(mp)).values()], inLast = [...reads(last, mp => byMap.has(mp)).keys()]
  const rank = ([mp, t]: [string, E]) => (inLast.includes(json([mp, t])) ? 0 : own(t) ? 1 : 2)
  const rs = all0.sort((x, y) => rank(x) - rank(y))
  // (each read after the step beside its twin before it, when the goal declares both)
  for (const [mp, t] of [...rs]) if (mp.endsWith('#') && byMap.has(mp.slice(0, -1)) && !rs.some(([m2, t2]) => m2 === mp.slice(0, -1) && json(t2) === json(t))) rs.push([mp.slice(0, -1), t])
  // (a count whose bound and body don't read its key is one number at every key: read once, at its first-ranked key)
  const once = new Set<string>(), keyless = (mp: string) => { const d = byMap.get(mp)!; return !mentions([d.below, d.body], d.j) }
  const rs1 = rs.filter(([mp]) => !keyless(mp) || (!once.has(mp) && !!once.add(mp)))
  const named: MapRead[] = rs1.map(([mp, t], i) => [`r$${i}`, mp, t])
  const bound = (r: MapRead) => json(byMap.get(r[1])!.below)
  const insts: CountInst[] = [], wits: string[] = []
  const add = (terms: [number, string][], unit: number, below: E) => { const w = `w$${insts.length}`; wits.push(w); insts.push({wit: w, below, terms, unit}) }
  // first: a count after the step at least each other one (it doesn't drop; what the step adds); then two counts before it
  // that meet, the first of the pair one the conclusion or the law's own names read; then the rest at most another
  const post = (r: MapRead) => r[1].endsWith('#'), ranked = (r: MapRead) => rank([r[1], r[2]]) <= 1
  for (const c of named) if (post(c)) for (const a of named) if (a !== c && !post(a) && bound(a) === bound(c)) add([[1, a[0]], [-1, c[0]]], 0, byMap.get(c[1])!.below)
  for (const [i, a] of named.entries()) for (const [j, c] of named.entries())
    if (i < j && (ranked(a) || ranked(c)) && bound(a) === bound(c) && !post(a) && !post(c)) add([[1, a[0]], [1, c[0]]], -1, byMap.get(a[1])!.below)
  for (const [i, a] of named.entries()) for (const [j, c] of named.entries())
    if (i < j && !(ranked(a) || ranked(c)) && bound(a) === bound(c) && !post(a) && !post(c)) add([[1, a[0]], [1, c[0]]], -1, byMap.get(a[1])!.below)
  return {reads: named, insts: insts.slice(0, 10), wits: wits.slice(0, 10)}
}

// --- the candidates --------------------------------------------------------------------------------------------------
// One list from the machine's shapes, each kept only if true on every small state: each map's cells at most what the
// small instances reach; the guards' count comparisons (guardLaws, `guarded`); one key a row; the engine's minimal ∀
// cubes of at most two literals (core/infer.ts's `cubes`, read off these small states, within a quarter of the search's
// budget `ms`, 15 s at most), its template `shapes` (the caller's laws, or an ∃ law's frame), each guard `u < param` loosened where a caller reads u with no param bound.
export function candidates(src: Parameters<typeof inferLaws>[0], m: Machine, caller: Law[], shapes: Law[], guarded: Law[], ms: number, until: number): Law[] {
  const states = ptime('small', () => smallOf(m))
  const trueAll = (l: Law) => clock() < until && trueSmall(m, [l])
  const kinds: Law[] = Object.keys(m.maps ?? {}).map(mp => {
    const most = Math.max(0, ...states.flatMap(({sts}) => sts.flatMap(st => [...(st.maps[mp]?.values() ?? [])])))
    return {name: `${mp} at most ${most}`, forall: 'a$c', holds: {op: '<=', a: {op: 'get', map: mp, key: v('a$c')}, b: k(most)}} as Law
  })
  // (a relation written at a composed key N·a + b under a quantified flag that its row a (or column b) holds no cell:
  // at most one b a row (one a a column), three keys read, which the engine's cubes of two keys can't state: one
  // decision a node where a decision needs the node undecided; a map a caller reads)
  const rowLaws: Law[] = Object.entries(m.step.maps ?? {}).flatMap(([mp, w]) => {
    const key = 'each' in w ? undefined : w.key
    if (key?.op !== 'add' || key.a.op !== 'mul' || key.a.a.op !== 'var' || key.b.op !== 'var' || !caller.some(l => reads(l.holds, x => x === mp).size)) return []
    const n = key.a.k, row = key.a.a, col0 = key.b, cellAt = (p: E, q: E): E => ({op: 'get', map: mp, key: {op: 'add', a: {op: 'mul', k: n, a: p}, b: q}})
    const empty = (col: boolean) => Object.values(m.step.flags ?? {}).some(q => q.op === 'all' && !q.keys?.length && json(q.c).includes(json(col ? cellAt(v(q.key), col0) : cellAt(row, v(q.key)))))
    return [false, true].filter(empty).map((col): Law => {
      const [a, x, y] = [v('a$c'), v('x$c'), v('y$c')], cell = (z: E): C => ({op: '<=', a: one, b: col ? cellAt(z, a) : cellAt(a, z)})
      return {name: `${mp}: one ${col ? 'first key a second' : 'second key a first'}`, forall: 'a$c', keys: ['x$c', 'y$c'],
        holds: {op: 'or', xs: [{op: 'not', x: {op: 'and', xs: [...[a, x, y].map((z): C => ({op: '<', a: z, b: k(n)})), cell(x), cell(y)]}}, {op: '=', a: x, b: y}]}}
    })
  })
  const t1 = clock(), rows = states.flatMap(({p, sts}) => sts.map(st => ({params: p, st})))
  const cubes0 = ptime('cubes', () => inferLaws(src, shapes, [], {cubes: 2, ms: Math.min(15_000, ms / 4), first: {proven: false, checked: false}, rows}).found.map(f => f.law))
  // (a cube's guard `u < param` dropped where u sits at a map's place that a caller reads with no param bound, the
  // decided value below N and not below size, if the small instances still hold it: the engine's template reads every
  // key of a composed map as one sort)
  const placesOf = (key: E): string[] | undefined => (key.op === 'var' ? [key.name] : key.op === 'add' && key.a.op === 'mul' && key.a.a.op === 'var' && key.b.op === 'var' ? [key.a.a.name, key.b.name] : undefined)
  const conjs = (c: C): C[] => (c.op === 'and' ? c.xs.flatMap(conjs) : [c])
  const guardsOf = (l: Law): C[] => (l.holds.op === 'or' ? l.holds.xs.flatMap(d => (d.op === 'not' ? conjs(d.x) : [])) : [])
  const bounded = (gs: C[], u: string) => gs.some(c => c.op === '<' && c.a.op === 'var' && c.a.name === u && c.b.op === 'var' && m.params.includes(c.b.name))
  const loose = new Set(caller.filter(l => guardsOf(l).length).flatMap(l => [...reads(l.holds, mp => mp in (m.maps ?? {})).values()].flatMap(([mp, key]) => (placesOf(key) ?? []).flatMap((u, i) => (bounded(guardsOf(l), u) ? [] : [`${mp}:${i}`])))))
  const loosened = (c: Law): Law => {
    const drop = new Set([...reads(c.holds, () => true).values()].flatMap(([mp, key]) => (placesOf(key) ?? []).filter((u, i) => loose.has(`${mp}:${i}`))))
    const keep = (x: C): boolean => !(x.op === '<' && x.a.op === 'var' && drop.has(x.a.name) && x.b.op === 'var' && m.params.includes(x.b.name))
    if (!drop.size || c.holds.op !== 'or' || !guardsOf(c).some(x => !keep(x))) return c
    // (the engine names the law's keys x, y, z in order)
    const shown = [c.forall, ...(c.keys ?? [])].flatMap((u, i) => (u && drop.has(u) ? ['xyzw'[i] ?? u] : []))
    const name = shown.reduce((t, x) => t.replace(new RegExp(`\\b${x} < (${m.params.join('|')}) ∧ `, 'g'), ''), c.name)
    const w: Law = {...c, name: name === c.name ? `${c.name} (any ${shown.join(', ')})` : name, holds: {op: 'or', xs: c.holds.xs.map(d => (d.op === 'not' ? {op: 'not', x: {op: 'and', xs: conjs(d.x).filter(keep)}} : d))}}
    return trueAll(w) ? w : c
  }
  const cubes = cubes0.map(loosened)
  if (env.GDP_COUNTS_TRACE) console.error(`counts: small ${states.map(({sts}) => sts.length).join('/')}; cubes ${cubes.length} in ${Math.round(clock() - t1)} ms: ${cubes.map(l => l.name).join('; ')}`)
  // (a candidate whose every conjunct a law before it states, its keys named apart by place, is not proposed again: a
  // cell's maximum its kind's law states, a cube a guard's)
  const said = new Set<string>(), parts = (l: Law): string[] => {
    const ks = [l.forall, ...(l.keys ?? [])].filter((x): x is string => !!x), named = substC(l.holds, {vars: Object.fromEntries(ks.map((x, i) => [x, v(`$${i}`)])), maps: {}, flags: {}})
    return (named.op === 'and' ? named.xs : [named]).map(json)
  }
  for (const l of caller) for (const q of parts(l)) said.add(q)
  const out = ptime('filter', () => [...kinds, ...guarded, ...rowLaws, ...cubes].filter(l => { const ps = parts(l); if (ps.every(q => said.has(q)) || !trueAll(l)) return false; for (const q of ps) said.add(q); return true }))
  if (env.GDP_COUNTS_TRACE) console.error(`counts: ${kinds.length + guarded.length + rowLaws.length + cubes.length - out.length} candidates said before or false on the small instances`)
  return out
}

// --- the cone ----------------------------------------------------------------------------------------------------------
// The candidates kept: each proven from the kept laws and itself (IC3's relative induction: its cone), so its proof
// stands whatever else the set holds. In tiers, each to its fixpoint before the next: the law alone, once; with the kept
// laws that read one of its maps; with every kept law (twice a law at most), the nearer tier again after each kept.
// Within two thirds of what is left (the rest the caller's: Houdini, or the whole set's proof), each goal an even share
// of that over the candidates. `attempt` is the caller's proof: the counted goals, or the kernel's for plain laws.
export type Tried<P> = {proof: P} | {stuck: string}
export function cone<P>(m: Machine, set: Law[], attempt: (law: Law, ls: Law[], ms: number) => Tried<P>, until: number): Map<string, P> {
  const kept = new Map<string, P>(), inCone = (l: Law) => kept.has(l.name), tried = new Map<string, number>(), times = new Map<string, number>(), asked = new Set<string>()
  const stopAt = until - (until - clock()) / 3, brief = (stopAt - clock()) / Math.max(1, set.length)
  // (the maps a law reads, a count's through its body)
  const mapsOf = (l: Law) => new Set([...reads(l.holds, () => true).values()].flatMap(([mp]) => [mp, ...(m.counts?.[mp] ? [...reads(m.counts[mp]!.body, () => true).values()].map(([q]) => q) : [])]))
  const near = (law: Law) => { const ms0 = mapsOf(law); return set.filter(l => l === law || (inCone(l) && [...mapsOf(l)].some(q => ms0.has(q)))) }
  const tier = (t: 0 | 1 | 2): boolean => {
    let any = false
    for (let grew = true; grew && clock() < stopAt;) {
      grew = false
      for (const law of set) {
        const id = `${t} ${law.name}`
        if (kept.has(law.name) || tried.get(id) === kept.size || (t === 0 && tried.has(id)) || (t === 2 && (times.get(law.name) ?? 0) >= 2) || clock() > stopAt) continue
        tried.set(id, kept.size)
        if (t === 2) times.set(law.name, (times.get(law.name) ?? 0) + 1)
        const ls = t === 0 ? [law] : t === 1 ? near(law) : set.filter(l => l === law || inCone(l))
        // (a tier whose goal is a nearer tier's, tried at this cone already, is skipped; and the same law over the same
        // laws, asked before in any tier: its goals are those again)
        if ((t === 1 && ls.length === 1) || (t === 2 && tried.get(`1 ${law.name}`) === kept.size && near(law).length === ls.length)) continue
        const same = `${law.name}\n${ls.map(l => l.name).join('\n')}`
        if (asked.has(same)) continue
        asked.add(same)
        const r = attempt(law, ls, brief)
        if ('proof' in r) { kept.set(law.name, r.proof); grew = any = true; if (env.GDP_COUNTS_TRACE === '3') console.error(`counts: keep ${law.name.slice(0, 50)} tier ${t}`) }
      }
      if (t === 2) break
    }
    return any
  }
  tier(0)
  do tier(1); while (tier(2) && clock() < stopAt)
  return kept
}

// --- the counted search ----------------------------------------------------------------------------------------------
export type Counted = {proven: boolean, laws: Law[], m: Machine, proof?: {instances: Record<string, Instances>, certs: Record<string, CountCert>}, why?: string}
export function searchCounted(m0: Machine, caller: Law[], ms = 60_000): Counted {
  if (!env.GDP_COUNTS_PROF) return searchCounted0(m0, caller, ms)
  cdclStats.on = true
  const t = performance.now(), out = searchCounted0(m0, caller, ms)
  console.error(`counts: prof total ${Math.round(performance.now() - t)} ms; ${Object.entries(cprof).map(([k2, x]) => `${k2} ${Math.round(x)}`).join(', ')}; cdcl runs ${cdclStats.runs} conflicts ${cdclStats.conflicts} decisions ${cdclStats.decisions} solveMs ${Math.round(cdclStats.solveMs)} rowsMs ${Math.round(cdclStats.rowsMs)} coreMs ${Math.round(cdclStats.coreMs)} unfoldMs ${Math.round(cdclStats.unfoldMs)} lpMs ${Math.round(cdclStats.lpMs)} boundMs ${Math.round(cdclStats.boundMs)} orderMs ${Math.round(cdclStats.orderMs)}`)
  return out
}
function searchCounted0(m0: Machine, caller: Law[], ms = 60_000): Counted {
  const until = clock() + ms, g = guardLaws(m0), m: Machine = {...m0, counts: {...m0.counts, ...g.counts}}
  if (!caller.every(l => clock() < until && trueSmall(m, [l]))) return {proven: false, laws: caller, m, why: clock() < until ? 'a law fails on the small instances' : 'time'}
  const t1 = clock()
  let set = [...caller, ...candidates(m0, m, caller, caller, g.laws, ms, until)]
  if (env.GDP_COUNTS_TRACE) console.error(`counts: candidates at ${Math.round(clock() - t1)} ms: ${set.map(l => l.name).join('; ')}`)
  // (the law's own names and the request's values that key a map: an action's value keys none)
  const keys0 = [...[...reads([m.step, m.assume ?? null], () => true).values()].map(([, key]) => key), ...Object.values(m.step.maps ?? {}).flatMap(w => ('each' in w ? [] : [w.key]))]
  const keyed = m.inputs.filter(i => keys0.some(key => mentions(key, i))).map(v)
  const terms = (l: Law): E[] => [...(l.forall ? [v(`${l.forall}#`)] : []), ...(l.keys ?? []).map(v), ...keyed]
  type Proof = {instances: Instances, certs: Record<string, CountCert>}
  let counted = true
  const none = {reads: [] as MapRead[], insts: [] as CountInst[]}
  // One law's goals and their certificates, the laws `ls` assumed (a subsequence of the set): pass 0 with no instances of
  // the lemma, pass 1 with the cells' (one set of witnesses a law); a tree each within `ms`. The instances: the
  // quantified flags at the law's own terms, then what the goals' models ask.
  const attempt = (law: Law, ls: Law[], pass: 0 | 1, ms: number): Tried<Proof> => {
    const ts = terms(law)
    let at: Instances = Object.fromEntries(Object.entries(m.step.flags ?? {}).flatMap(([f, q]) => (q.op === 'all' && !q.keys?.length ? [[`?${f}`, ts]] : [])))
    const obligations = (i: Instances) => ptime('encode', () => countedObligations(m, ls, {[law.name]: i}, ls.indexOf(law)))
    const build = () => obligations(at).map(({goal, decls}) => { const c = pass ? certFor(goal, decls) : none; return {goal, decls, c, gg: ptime('encode', () => mcGoal(goal.hyps, decls, c))} })
    let built = build()
    const t0 = clock(), more = () => clock() - t0 <= Math.max(ms, 1_000)
    // The step goal decided first by the CDCL search for a model (its phases the simplex's point: a model is met where the
    // tree search would split on), within 2·ms (5 s at most):
    //   - refuted: the law's instances cut to those its core reads, and the core's hypotheses grown on their own first,
    //     the tree widened to the goal;
    //   - a model: the instances it asks for (kernel/prove.ts's modelInstances, MBQI: a law or quantified flag broken at a
    //     tuple of the goal's own keys), the goals made again with them; none asked, the goal has a model and is given
    //     up at once (no tree to grow); the rounds within the attempt's time (a second at least, as the kernel's
    //     withModels gives its later rounds), past which the goal is unknown;
    //   - unknown: the goals grown as they are.
    for (;;) {
      let part: {gg: Goal, core: Goal} | undefined
      for (;;) {
        const step = built.at(-1)
        if (!step?.gg) break
        const q = ptime('decide', () => growCdcl(step.gg!, new Map(), {nodes: 0, until: Math.min(until, clock() + Math.min(2 * ms, 5_000))}, {model: true, core: true}) as Refuted)
        if (!('tree' in q) && q.why === REFUTED && q.core) {
          const gg = step.gg, last = gg.hyps.length - 1, used = new Set(q.core.map(h => json(gg.hyps[h]))), cut: Instances = {}
          for (const [name, ts2] of Object.entries(at)) {
            const l = ls.find(x => x.name === name), n = l ? 1 + (l.keys?.length ?? 0) : 0
            cut[name] = !l ? ts2 : Array.from({length: ts2.length / n}, (_, t) => ts2.slice(t * n, t * n + n)).filter(t => used.has(json(assumed([l], {[name]: t})[0]))).flat()
          }
          at = cut
          built = obligations(at).map(({goal, decls}, j) => ({goal, decls, c: built[j]!.c, gg: mcGoal(goal.hyps, decls, built[j]!.c)}))
          part = {gg: built.at(-1)!.gg!, core: {name: gg.name, hyps: (q.core.includes(last) ? q.core : [...q.core, last]).map(h => gg.hyps[h]!)}}
          break
        }
        if ('tree' in q || q.stuck !== 'sat' || !q.witness) break
        if (!more()) return {stuck: 'unknown'}
        const asked = ptime('mbqi', () => modelInstances(m, ls, at, step.gg!, q.witness!))
        if (!asked) {
          if (countsDump.on && pass && dumped < Number(env.GDP_COUNTS_DUMP_N ?? 3)) { dumped++; countsDump.on({law: law.name, goal: step.goal.name, ls: ls.map(l => l.name), stuck: 'sat', witness: q.witness, reads: step.c.reads, insts: step.c.insts, hyps: step.gg.hyps}) }
          return {stuck: 'sat'}
        }
        at = asked
        built = build()
      }
      // (whether a goal reads a count: if none does, pass 1's goals are pass 0's)
      if (!pass) counted = built.some(b => certFor(b.goal, b.decls).reads.length)
      const certs: Record<string, CountCert> = {}
      let again = false
      for (const {goal, c, gg} of built) {
        const t0 = clock(), viaPart = gg && part?.gg === gg ? ptime('part', () => {
          const o1 = grow(part!.core, new Map(), {nodes: 0, until: Math.min(until, clock() + Math.max(ms, 2_000))}), w = 'tree' in o1 ? widen(part!.core, gg, o1.tree) : undefined
          return w ? {tree: w, nodes: 0} : undefined
        }) : undefined
        const o = viaPart ?? (gg && ptime(`grow${(gg.hyps.length > 300 ? '>300' : '')}`, () => grow(gg, new Map(), {nodes: 0, until: Math.min(until, clock() + ms)})))
        if (countsDump.on && gg && o && !('tree' in o) && gg.hyps.length > Number(env.GDP_COUNTS_DUMP_MIN ?? 300) && dumped < Number(env.GDP_COUNTS_DUMP_N ?? 3)) { dumped++; countsDump.on({law: law.name, goal: goal.name, ls: ls.map(l => l.name), stuck: (o as {stuck?: string}).stuck, hyps: gg.hyps}) }
        if (env.GDP_COUNTS_TRACE === '2') console.error(`counts: ${ls.length === 1 ? 'alone' : `with ${ls.length}`} ${pass} ${goal.name}: ${o && 'tree' in o ? 'proven' : gg ? (o as {stuck?: string}).stuck : 'no read'} ${gg?.hyps.length ?? 0} hyps ${Math.round(clock() - t0)} ms`)
        // (the tree search's model of the step goal: the instances it asks for, as the CDCL search's, and the goals again)
        if (gg && o && !('tree' in o) && o.stuck === 'sat' && o.witness && gg === built.at(-1)!.gg && more()) {
          const asked = ptime('mbqi', () => modelInstances(m, ls, at, gg, o.witness!))
          if (asked) { at = asked; built = build(); again = true; break }
        }
        if (!o || !('tree' in o)) return {stuck: gg ? (o as {stuck?: string}).stuck ?? '' : ''}
        certs[goal.name] = {reads: c.reads, insts: c.insts, tree: o.tree}
      }
      if (!again) return {proof: {instances: at, certs}}
    }
  }
  const traced = (law: Law, ls: Law[], pass: 0 | 1, ms: number): Tried<Proof> => {
    const t0 = clock(), r = attempt(law, ls, pass, ms)
    if (env.GDP_COUNTS_TRACE === '3') console.error(`counts: try ${law.name.slice(0, 50)} | ls ${ls.length} pass ${pass} ms ${ms} took ${Math.round(clock() - t0)} -> ${'proof' in r ? 'kept' : r.stuck}`)
    return r
  }
  // The cone (a law about no key is assumed in every goal, so with one in the set nothing is kept); with every caller
  // kept, the kept laws are the proof; else Houdini over the whole set, the kept laws' proofs reused.
  const kept = set.every(l => l.forall) ? cone(m, set, (law, ls, ms2) => traced(law, ls, 1, ms2), until) : new Map<string, Proof>()
  if (env.GDP_COUNTS_TRACE) console.error(`counts: kept ${kept.size} of ${set.length} in ${Math.round(clock() - t1)} ms`)
  const finish = (ls: Law[], proof: {instances: Record<string, Instances>, certs: Record<string, CountCert>}): Counted =>
    (ptime('kernel', () => checkCountedLaws(m, ls, proof)) ? {proven: true, laws: ls, m, proof} : {proven: false, laws: ls, m, why: 'the kernel refused the set'})
  const keptProof = () => ({instances: Object.fromEntries([...kept].map(([n, pr]) => [n, pr.instances])), certs: Object.assign({}, ...[...kept.values()].map(pr => pr.certs))})
  if (caller.every(l => kept.has(l.name))) return finish(set.filter(l => kept.has(l.name)), keptProof())
  // (each law not kept an even share of what is left a round)
  for (let round = 0; clock() < until; round++) {
    const {instances, certs} = keptProof(), failed = new Set<string>(), share = (until - clock()) / Math.max(1, set.filter(l => !kept.has(l.name)).length)
    // (the callers last, so they meet every support kept so far)
    for (const law of [...set.filter(l => !caller.includes(l)), ...set.filter(l => caller.includes(l))]) {
      if (clock() > until) return {proven: false, laws: set, m, why: 'time'}
      if (kept.has(law.name)) continue
      let r = traced(law, set, 0, share)
      if (!('proof' in r) && counted) r = traced(law, set, 1, share)
      if (!('proof' in r)) { failed.add(law.name); continue }
      instances[law.name] = r.proof.instances
      Object.assign(certs, r.proof.certs)
    }
    if (env.GDP_COUNTS_TRACE) console.error(`counts: round ${round}: ${set.length} laws, ${kept.size} kept, failed ${[...failed].join('; ').slice(0, 600)}`)
    if (!failed.size) return finish(set, {instances, certs})
    const next = set.filter(l => !failed.has(l.name) || caller.includes(l))
    // (only callers fail: drop nothing more, give up)
    if (next.length === set.length) return {proven: false, laws: set, m, why: `not proven: ${[...failed].join(', ')}`}
    set = next
  }
  return {proven: false, laws: set, m, why: 'time'}
}
