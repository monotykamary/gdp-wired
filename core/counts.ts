// The search for a machine with counts (Machine.counts; the kernel's countedObligations and checkCountedLaws, Lean's
// CountMachine.lean): untrusted. It proposes laws that read counts of the state, filters every candidate on the small
// instances' reachable states, and keeps the largest set the kernel accepts (Houdini), each goal's certificate built
// here: the count cells the goal reads, Count.lean's instances over pairs of them, and the laws and quantified flags at
// the instances' witnesses.
//   - The guard's shape: a step writes P[t] where a quantified flag says every member of a set the request counts
//     satisfies R(member, t), and the assumption compares that count with a bound (2·|Q| > size, |Q| ≥ n − t, …). Then
//     a state count c_R(x) = |{k < bound: R(k, x)}| is declared, and P[a] ⇒ the same comparison with c_R[a] for |Q| is
//     proposed: what every majority, quorum or threshold protocol keeps of its decisions.
//   - A guard comparing a state count at the written key (2·voters[n] > size, Leader[n] := 1): P[a] ⇒ that comparison
//     at a.
//   - Each map's cells at most what the small instances reach.
//   - The supports no guard reads (one vote per node, a vote only from a node that voted, ...): core/infer.ts's engine's
//     minimal ∀ cubes of at most two literals, read off its small instance and data filter (its `cubes` option).
// Each law over keys is assumed where its reads meet the goal's cells (E-matching), and a large step goal is cut to the
// instances the CDCL search's refutation reads before its tree is grown.
import {type C, type E, type Law, type Machine, type State} from './machine.ts'
import {type CountCert, type CountDecl, type CountInst, type Instances, type MapRead, assumed, checkCountedLaws, countedObligations, mcGoal, substC} from '../kernel/kernel.ts'
import {clock, grow, modelInstances} from '../kernel/prove.ts'
import {REFUTED, type Refuted, cdclStats, growCdcl} from '../kernel/cdcl.ts'
import {inferLaws} from './infer.ts'
import {holdsAt, small} from './exists.ts'
import {env} from './solver.ts'
import {appendFileSync} from 'node:fs'

// (GDP_COUNTS_PROF: where a counted search's time goes, by phase, on stderr at the end; GDP_COUNTS_DUMP=<file>: each goal
// left unknown past 300 hypotheses written there as a JSON line, the first 3: research's profiles)
export const cprof: Record<string, number> = {}
const ptime = <T>(k: string, f: () => T): T => { const t = performance.now(); try { return f() } finally { cprof[k] = (cprof[k] ?? 0) + performance.now() - t } }
let dumped = 0

const v = (name: string): E => ({op: 'var', name}), k = (value: number): E => ({op: 'const', value})
const json = (t: unknown) => JSON.stringify(t)
const knob = {pairs: env.GDP_K_PAIRS === '1', rounds: Number(env.GDP_K_ROUNDS ?? 2), cap: Number(env.GDP_K_CAP ?? 24), ts: env.GDP_K_TS !== '0', keyed: env.GDP_K_KEYED !== '0', flagTs: env.GDP_K_FLAGTS !== '0', shrink: Number(env.GDP_K_SHRINK ?? 150), walks: Number(env.GDP_K_WALKS ?? 100_000), alone: Number(env.GDP_K_ALONE ?? 300), hops: Number(env.GDP_K_HOPS ?? 16), first: env.GDP_K_FIRST !== '0', decide: Number(env.GDP_K_DECIDE ?? 0), mbqi: Number(env.GDP_K_MBQI ?? 4), once: env.GDP_K_ONCE !== '0', reads: Number(env.GDP_K_READS ?? 6)}
const one = k(1), zero = k(0)
type Env = Record<string, number>

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
  const once = new Set<string>(), keyless = (mp: string) => { const d = byMap.get(mp)!; return knob.once && !mentions([d.below, d.body], d.j) }
  const rs1 = rs.filter(([mp]) => !keyless(mp) || (!once.has(mp) && !!once.add(mp)))
  const named: MapRead[] = rs1.slice(0, knob.reads).map(([mp, t], i) => [`r$${i}`, mp, t])
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

// --- instances by the goal's own reads (E-matching, as an SMT solver instantiates a quantifier) ------------------------
// A law over keys (and a quantified flag) is assumed at the tuples where its map reads meet the cells the goal reads: each
// read of the law, its key a pattern over the law's names, matched against a cell read in the goal (a count's body at a
// witness included), the tuples one read or two cover; the goal regrown with them, twice at most.
const ground = (t0: unknown, out: Map<string, [string, E]> = new Map()): Map<string, [string, E]> => {
  const go = (x: unknown): void => {
    if (!x || typeof x !== 'object') return
    const o = x as Record<string, unknown>
    if (o.op === 'all') return
    if (o.op === 'get') out.set(json([o.map, o.key]), [o.map as string, o.key as E])
    for (const y of Object.values(o)) go(y)
  }
  go(t0)
  return out
}
// (a name a pattern reads twice, as x·N + x, matched by a cell whose two places differ: bound to each, `alt`, so the law
// is assumed where the goal's cases make them equal)
function bindKey(p: E, g: E, names: string[], b: Record<string, E>, alt?: Record<string, E>): boolean {
  if (p.op === 'var' && names.includes(p.name)) { const x = b[p.name]; if (!x) { b[p.name] = g; return true } if (json(x) === json(g)) return true; if (!alt || alt[p.name]) return false; alt[p.name] = g; return true }
  if (p.op !== g.op) return false
  const q = g as typeof p & Record<string, unknown>
  switch (p.op) {
    case 'add': case 'sub': case 'min': case 'max': case 'prod': return bindKey(p.a, (q as typeof p).a, names, b, alt) && bindKey(p.b, (q as typeof p).b, names, b, alt)
    case 'mul': return p.k === (q as typeof p).k && bindKey(p.a, (q as typeof p).a, names, b, alt)
    case 'var': case 'const': case 'get': case 'if': return json(p) === json(g)
  }
}
export function matched(names: string[], body: C, cells: [string, E][], cap = knob.cap): E[][] {
  const pats = [...reads(body, () => true).values()].filter(([, key]) => names.some(nm => mentions(key, nm)))
  const per = pats.map(([mp, key]) => cells.filter(c => c[0] === mp).flatMap(([, g]) => { const b: Record<string, E> = {}, alt: Record<string, E> = {}; return bindKey(key, g, names, b, alt) ? [b, ...Object.entries(alt).map(([nm, t]) => ({...b, [nm]: t}))] : [] }))
  const out = new Map<string, E[]>()
  const put = (b: Record<string, E>) => { if (names.every(nm => b[nm])) { const t = names.map(nm => b[nm]!); out.set(json(t), t) } }
  for (const [i, bs] of per.entries()) for (const b of bs) {
    put(b)
    for (const c of per.slice(i + 1).flat()) { if (out.size >= cap) break; const m2 = {...b}; if (Object.entries(c).every(([nm, t]) => !m2[nm] || json(m2[nm]) === json(t))) put(Object.assign(m2, c)) }
  }
  return [...out.values()].slice(0, cap)
}

// --- Houdini ------------------------------------------------------------------------------------------------------------
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
  // The small instances: each param 2 and 3 (where the precondition allows), inputs and sets below 3.
  const insts = [2, 3].map(x => Object.fromEntries(m.params.map(p => [p, x])) as Env)
  const states = insts.map(p => {
    try { return {p, sts: ptime('small', () => small(m, p, 3, 3000, 300_000, knob.walks))} } catch { return {p, sts: [] as State[]} }
  })
  const kinds: Law[] = Object.keys(m.maps ?? {}).map(mp => {
    const most = Math.max(0, ...states.flatMap(({sts}) => sts.flatMap(st => [...(st.maps[mp]?.values() ?? [])])))
    return {name: `${mp} at most ${most}`, forall: 'a$c', holds: {op: '<=', a: {op: 'get', map: mp, key: v('a$c')}, b: k(most)}} as Law
  })
  const trueAll = (l: Law) => clock() < until && states.every(({p, sts}) => sts.every(st => holdsAt(m, l, p, st, 4)))
  if (!caller.every(trueAll)) return {proven: false, laws: caller, m, why: clock() < until ? 'a law fails on the small instances' : 'time'}
  // (the engine's minimal ∀ cubes on its own small instances and data filter, core/infer.ts's: the supports no guard reads)
  const t1 = clock(), rows = states.flatMap(({p, sts}) => sts.map(st => ({params: p, st})))
  const cubes = ptime('cubes', () => inferLaws(m0, caller, [], {cubes: 2, ms: Math.min(15_000, ms / 4), first: {proven: false, checked: false}, rows}).found.map(f => f.law))
  if (env.GDP_COUNTS_TRACE) console.error(`counts: small ${states.map(({sts}) => sts.length).join('/')}; declared ${Object.keys(g.counts ?? {}).join(', ')}`)
  if (env.GDP_COUNTS_TRACE) console.error(`counts: cubes ${cubes.length} in ${Math.round(clock() - t1)} ms: ${cubes.map(l => l.name).join('; ')}`)
  let set = [...caller, ...ptime('filter', () => [...kinds, ...g.laws, ...cubes].filter(trueAll))]
  if (env.GDP_COUNTS_TRACE) console.error(`counts: candidates at ${Math.round(clock() - t1)} ms: ${set.map(l => l.name).join('; ')}`)
  // (the law's own names and the request's values that key a map: an action's value keys none)
  const keys0 = [...[...reads([m.step, m.assume ?? null], () => true).values()].map(([, key]) => key), ...Object.values(m.step.maps ?? {}).flatMap(w => ('each' in w ? [] : [w.key]))]
  const keyed = m.inputs.filter(i => keys0.some(key => mentions(key, i)))
  const terms = (l: Law): E[] => [...(l.forall ? [v(`${l.forall}#`)] : []), ...(l.keys ?? []).map(v), ...(knob.keyed ? keyed : m.inputs).map(v)]
  type Proof = {instances: Instances, certs: Record<string, CountCert>}
  let counted = true, stuck = ''
  // One law's goals and their certificates, the laws `ls` assumed (a subsequence of the set): pass 0 with no instances of
  // the lemma, pass 1 with the cells' (one set of witnesses a law); a tree each within `ms`.
  const attempt = (law: Law, ls: Law[], pass: 0 | 1, ms: number): Proof | undefined => {
    const ts = terms(law)
    // (the laws over one key at pairs of the law's own names and the request's, every-key laws at those; the rest, and
    // the witnesses, by the goal's reads below)
    const inst: Instances = {}
    for (const l of ls) {
      if (l.keys?.length === 1 && knob.pairs) inst[l.name] = ts.flatMap(x => ts.flatMap(y => (json(x) === json(y) ? [] : [x, y])))
      else if (!l.keys?.length && l.forall && knob.ts) inst[l.name] = [...ts]
    }
    for (const [f, q] of Object.entries(m.step.flags ?? {})) if (q.op === 'all' && !q.keys?.length) inst[`?${f}`] = knob.flagTs ? ts : m.inputs.map(v)
    // (more instances where the goal's reads meet a law's: each keyed law and quantified flag, matched; at most twice)
    // (the cells the goals' conclusions read first: a law's instances at the conclusion's own keys come before the cap)
    const more = (at: Instances, hyps: C[][], concl: C[]): boolean => {
      const cells = [...ground(hyps, knob.first ? ground(concl) : new Map()).values()]
      let grew = false
      const add = (name: string, ts2: E[][]) => {
        const have = new Set<string>(), cur = at[name] ?? [], n = ts2[0]?.length ?? 1
        for (let i = 0; i + n <= cur.length; i += n) have.add(json(cur.slice(i, i + n)))
        for (const t of ts2) if (!have.has(json(t))) { have.add(json(t)); at[name] = [...(at[name] ?? []), ...t]; grew = true }
      }
      for (const l of ls) if (l.forall) add(l.name, matched([l.forall, ...(l.keys ?? [])], l.holds, cells))
      for (const [f, q] of Object.entries(m.step.flags ?? {})) if (q.op === 'all' && !q.keys?.length) add(`?${f}`, matched([q.key], q.c, cells))
      return grew
    }
    const obligations = (at: Instances) => ptime('encode', () => countedObligations(m, ls, {[law.name]: at}, ls.indexOf(law)))
    let built: {goal: {name: string, hyps: C[]}, decls: CountDecl[], c: Pick<CountCert, 'reads' | 'insts'>, gg: ReturnType<typeof mcGoal>}[] = []
    let at = inst
    for (let r = 0; r <= knob.rounds; r++) {
      built = obligations(at).map(({goal, decls}) => {
        const c = pass ? certFor(goal, decls) : {reads: [] as MapRead[], insts: [] as CountInst[]}
        return {goal, decls, c, gg: ptime('encode', () => mcGoal(goal.hyps, decls, c))}
      })
      if (r === knob.rounds || !ptime('match', () => more(at, built.map(b => b.gg?.hyps ?? b.goal.hyps), built.map(b => b.goal.hyps.at(-1)!)))) break
    }
    // The step goal decided first by the CDCL search for a model (its phases the simplex's point: a model is met where the
    // tree search would split on), within 2·ms (5 s at most):
    //   - refuted, past `shrink` hypotheses: the law's instances cut to those its core reads, the goals grown with them;
    //   - a model: the instances it asks for (kernel/prove.ts's modelInstances, MBQI: a law or quantified flag broken at a
    //     tuple of the goal's own keys), the goals made again with them, `mbqi` rounds at most; none asked, the goal has a
    //     model and is given up at once (no tree to grow);
    //   - unknown: the goals grown as they are.
    for (let round = 0; ; round++) {
      const step = built.at(-1)
      if (!step?.gg || step.gg.hyps.length < knob.decide) break
      const q = ptime('decide', () => growCdcl(step.gg!, new Map(), {nodes: 0, until: Math.min(until, clock() + Math.min(2 * ms, 5_000))}, {model: true, core: true}) as Refuted)
      if (!('tree' in q) && q.why === REFUTED && q.core) {
        if (step.gg.hyps.length <= knob.shrink) break
        const used = new Set(q.core.map(h => json(step.gg!.hyps[h]))), cut: Instances = {}
        for (const [name, ts2] of Object.entries(at)) {
          const l = ls.find(x => x.name === name), n = l ? 1 + (l.keys?.length ?? 0) : 0
          cut[name] = !l ? ts2 : Array.from({length: ts2.length / n}, (_, t) => ts2.slice(t * n, t * n + n)).filter(t => used.has(json(assumed([l], {[name]: t})[0]))).flat()
        }
        at = cut
        built = obligations(at).map(({goal, decls}, j) => ({goal, decls, c: built[j]!.c, gg: mcGoal(goal.hyps, decls, built[j]!.c)}))
        break
      }
      if ('tree' in q || q.stuck !== 'sat' || !q.witness) break
      const asked = round < knob.mbqi ? ptime('mbqi', () => modelInstances(m, ls, at, step.gg!, q.witness!)) : undefined
      if (!asked) {
        stuck = 'sat'
        if (env.GDP_COUNTS_DUMP && pass && ls.length >= Number(env.GDP_COUNTS_DUMP_LS ?? 0) && dumped < Number(env.GDP_COUNTS_DUMP_N ?? 3)) { dumped++; appendFileSync(env.GDP_COUNTS_DUMP, json({law: law.name, goal: step.goal.name, ls: ls.map(l => l.name), stuck: 'sat', witness: q.witness, reads: step.c.reads, insts: step.c.insts, hyps: step.gg.hyps}) + '\n') }
        if (env.GDP_COUNTS_TRACE === '2') console.error(`counts: ${ls.length === 1 ? 'alone' : `kept${ls.length}`} ${pass} ${step.goal.name}: sat by its model, round ${round}, ${step.gg.hyps.length} hyps`)
        return undefined
      }
      at = asked
      built = obligations(at).map(({goal, decls}) => {
        const c = pass ? certFor(goal, decls) : {reads: [] as MapRead[], insts: [] as CountInst[]}
        return {goal, decls, c, gg: mcGoal(goal.hyps, decls, c)}
      })
    }
    // (whether a goal reads a count: if none does, pass 1's goals are pass 0's)
    if (!pass) counted = built.some(b => certFor(b.goal, b.decls).reads.length)
    const certs: Record<string, CountCert> = {}
    for (const {goal, c, gg} of built) {
      const t0 = clock(), o = gg && ptime(`grow${(gg.hyps.length > 300 ? '>300' : '')}`, () => grow(gg, new Map(), {nodes: 0, until: Math.min(until, clock() + ms)}))
      if (env.GDP_COUNTS_DUMP && gg && o && !('tree' in o) && gg.hyps.length > Number(env.GDP_COUNTS_DUMP_MIN ?? 300) && ls.length >= Number(env.GDP_COUNTS_DUMP_LS ?? 0) && dumped < Number(env.GDP_COUNTS_DUMP_N ?? 3)) { dumped++; appendFileSync(env.GDP_COUNTS_DUMP, json({law: law.name, goal: goal.name, ls: ls.map(l => l.name), stuck: (o as {stuck?: string}).stuck, hyps: gg.hyps}) + '\n') }
      if (env.GDP_COUNTS_TRACE === '2') console.error(`counts: ${ls.length === 1 ? 'alone' : ls.length < set.length ? `kept${ls.length}` : 'all'} ${pass} ${goal.name}: ${o && 'tree' in o ? 'proven' : gg ? (o as {stuck?: string}).stuck : 'no read'} ${gg?.hyps.length ?? 0} hyps ${Math.round(clock() - t0)} ms`)
      if (!o || !('tree' in o)) {
        stuck = gg ? (o as {stuck?: string}).stuck ?? '' : ''
        if (env.GDP_COUNTS_TRACE && pass === 1 && ls.length === set.length) console.error(`counts: ${goal.name}: ${gg ? json(o).slice(0, 300) : 'a read of no count'} (reads ${c.reads.map(r => `${r[1]}[${json(r[2])}]`).join(' ')})`)
        return undefined
      }
      certs[goal.name] = {reads: c.reads, insts: c.insts, tree: o.tree}
    }
    return {instances: at, certs}
  }
  // The laws kept: each proven from the laws kept before it and itself (IC3's relative induction, its cone), tried again
  // as more are kept, each goal briefly; their proofs stand whatever else the set holds. Then, in turn, each law whose
  // goal ran out of time there (no model: a pigeonhole's goal over a large cone) with a full goal's time, the brief
  // round again after each kept. With every caller kept, the kept laws are the proof; else Houdini over the whole set,
  // the kept laws' proofs reused.
  // (a law about no key is assumed in every goal, so with one in the set nothing is kept)
  const kept = new Map<string, Proof>(), cone = (l: Law) => kept.has(l.name), tried = new Map<string, number>(), late = new Map<string, string>(), hard = new Map<string, number>()
  const keep = (law: Law, pr: Proof | undefined) => { if (pr) kept.set(law.name, pr); else late.set(law.name, stuck); return !!pr }
  // (the maps a law reads, a count's through its body)
  const mapsOf = (l: Law) => new Set([...reads(l.holds, () => true).values()].flatMap(([mp]) => [mp, ...(m.counts?.[mp] ? [...reads(m.counts[mp]!.body, () => true).values()].map(([q]) => q) : [])]))
  const near = (law: Law) => { const ms0 = mapsOf(law); return set.filter(l => l === law || (cone(l) && [...mapsOf(l)].some(q => ms0.has(q)))) }
  // (the kept laws by the maps they share, a hop at a time from the law's own, the fewest keys first, until `most`)
  const hops = (law: Law, most: number): Law[] => {
    const seen = new Set(mapsOf(law)), out = new Set<Law>([law])
    for (let grew = true; grew && out.size < most;) {
      grew = false
      const layer = set.filter(l => cone(l) && !out.has(l) && [...mapsOf(l)].some(q => seen.has(q))).sort((a, b) => (a.keys?.length ?? 0) - (b.keys?.length ?? 0))
      for (const l of layer) { if (out.size >= most) break; out.add(l); grew = true }
      for (const l of layer) if (out.has(l)) for (const q of mapsOf(l)) seen.add(q)
    }
    return set.filter(l => out.has(l))
  }
  // (in tiers, each to its fixpoint before the next: the law alone, once; with the kept laws that read one of its maps;
  // with every kept law, a larger goal, the nearer tier again after each kept)
  // (the whole cone's goal at most twice a law here: the hard stage below takes the rest)
  const times = new Map<string, number>()
  const tier = (t: 0 | 1 | 2): boolean => {
    let any = false
    for (let grew = true; grew && clock() < stopAt;) {
      grew = false
      for (const law of set) {
        const id = `${t} ${law.name}`
        if (kept.has(law.name) || tried.get(id) === kept.size || (t === 0 && tried.has(id)) || (t === 2 && (times.get(law.name) ?? 0) >= 2) || clock() > stopAt) continue
        tried.set(id, kept.size)
        if (t === 2) times.set(law.name, (times.get(law.name) ?? 0) + 1)
        const ls = t === 0 ? [law] : t === 1 ? near(law) : set.filter(l => l === law || cone(l))
        // (a tier whose goal is a nearer tier's, tried at this cone already, is skipped)
        if ((t === 1 && ls.length === 1) || (t === 2 && tried.get(`1 ${law.name}`) === kept.size && near(law).length === ls.length)) continue
        if (keep(law, attempt(law, ls, 1, knob.alone))) grew = any = true
      }
      if (t === 2) break
    }
    return any
  }
  // (the sweeps stop with a third of what is left after the candidates, which the hard stage keeps)
  let stopAt = until - (until - clock()) / 3
  const sweep = () => { tier(0); do tier(1); while (tier(2) && clock() < stopAt) }
  // (the callers first, then the laws that read a count, a pigeonhole's; each again once more laws are kept)
  const readsCount = (l: Law) => reads(l.holds, mp => !!m.counts?.[mp]).size > 0
  const order = [...set.filter(l => caller.includes(l)), ...set.filter(l => !caller.includes(l) && readsCount(l)), ...set.filter(l => !caller.includes(l) && !readsCount(l))]
  if (set.every(l => l.forall)) for (sweep(), stopAt = until; clock() < until;) {
    const next = order.find(l => !kept.has(l.name) && hard.get(l.name) !== kept.size && late.get(l.name) === 'unknown')
    if (!next) break
    hard.set(next.name, kept.size)
    // (the kept laws a few hops from the law's maps first, a smaller goal, then every kept law)
    const few = hops(next, knob.hops), all = set.filter(l => l === next || cone(l))
    if (keep(next, (few.length < all.length ? attempt(next, few, 1, 10_000) : undefined) ?? attempt(next, all, 1, 10_000))) sweep()
  }
  if (env.GDP_COUNTS_TRACE) console.error(`counts: kept ${kept.size} of ${set.length} in ${Math.round(clock() - t1)} ms`)
  const finish = (ls: Law[], proof: {instances: Record<string, Instances>, certs: Record<string, CountCert>}): Counted =>
    (ptime('kernel', () => checkCountedLaws(m, ls, proof)) ? {proven: true, laws: ls, m, proof} : {proven: false, laws: ls, m, why: 'the kernel refused the set'})
  const keptProof = () => ({instances: Object.fromEntries([...kept].map(([n, pr]) => [n, pr.instances])), certs: Object.assign({}, ...[...kept.values()].map(pr => pr.certs))})
  if (caller.every(cone)) return finish(set.filter(cone), keptProof())
  for (let round = 0; clock() < until; round++) {
    const {instances, certs} = keptProof(), failed = new Set<string>()
    // (the callers last, so they meet every support kept so far)
    for (const law of [...set.filter(l => !caller.includes(l)), ...set.filter(l => caller.includes(l))]) {
      if (clock() > until) return {proven: false, laws: set, m, why: 'time'}
      if (kept.has(law.name)) continue
      const pr = attempt(law, set, 0, 10_000) ?? (counted ? attempt(law, set, 1, 10_000) : undefined)
      if (!pr) { failed.add(law.name); continue }
      instances[law.name] = pr.instances
      Object.assign(certs, pr.certs)
    }
    if (env.GDP_COUNTS_TRACE) console.error(`counts: round ${round}: ${set.length} laws, ${kept.size} kept, failed ${[...failed].join('; ').slice(0, 600)}`)
    if (!failed.size) return finish(set, {instances, certs})
    if (caller.some(l => failed.has(l.name)) && set.length === caller.length) return {proven: false, laws: set, m, why: `not proven: ${[...failed].join(', ')}`}
    const next = set.filter(l => !failed.has(l.name) || caller.includes(l))
    // (only callers fail: drop nothing more, give up)
    if (next.length === set.length) return {proven: false, laws: set, m, why: `not proven: ${[...failed].join(', ')}`}
    set = next
  }
  return {proven: false, laws: set, m, why: 'time'}
}
