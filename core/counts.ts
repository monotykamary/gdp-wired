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
import {type CountCert, type CountInst, type Instances, type MapRead, assumed, checkCountedLaws, countedObligations, mcGoal, substC} from '../kernel/kernel.ts'
import {clock, grow} from '../kernel/prove.ts'
import {REFUTED, type Refuted, growCdcl} from '../kernel/cdcl.ts'
import {inferLaws} from './infer.ts'
import {holdsAt, small} from './exists.ts'
import {env} from './solver.ts'

const v = (name: string): E => ({op: 'var', name}), k = (value: number): E => ({op: 'const', value})
const json = (t: unknown) => JSON.stringify(t)
const knob = {pairs: env.GDP_K_PAIRS === '1', rounds: Number(env.GDP_K_ROUNDS ?? 2), cap: Number(env.GDP_K_CAP ?? 24), ts: env.GDP_K_TS !== '0', keyed: env.GDP_K_KEYED !== '0', flagTs: env.GDP_K_FLAGTS !== '0', shrink: Number(env.GDP_K_SHRINK ?? 150)}
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
  for (const [mp, w] of Object.entries(m.step.maps ?? {})) {
    if ('each' in w || w.key.op !== 'var' || !m.inputs.includes(w.key.name)) continue
    const t = w.key.name, written = inline({op: '<=', a: one, b: w.value} as C)
    const law = (name: string, cmp: C): Law => ({name, forall: 'a$c', holds: {op: 'or', xs: [{op: 'not', x: {op: '<=', a: one, b: {op: 'get', map: mp, key: v('a$c')}}}, cmp]}})
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
      for (const [c, d] of Object.entries(m.counts ?? {})) {
        // the set: the count's body is the flag's hypothesis at its key
        const body = d.body.op === 'if' ? d.body.c : undefined
        if (!body || json(substC(body, {vars: {[d.key]: v(q.key)}, maps: {}, flags: {}})) !== json(h)) continue
        if (m.inputs.some(i => i !== t && mentions(r, i))) continue
        const name = `${c}$${mp}`, j = `${name}$x`, key = `${name}$k`
        counts[name] = {j, key, below: d.below, body: {op: 'if', c: substC(r, {vars: {[q.key]: v(key), [t]: v(j)}, maps: {}, flags: {}}), then: one, else: zero}}
        for (const g of guards) if (reads(g, x => x === c).size)
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
export function certFor(goal: {hyps: C[]}, decls: {map: string, below: E}[]): {reads: MapRead[], insts: CountInst[], wits: string[]} {
  const byMap = new Map(decls.map(d => [d.map, d])), last = goal.hyps.at(-1)
  // (the conclusion's reads first, then those at a constant or the law's own names, then the rest)
  const own = (t: E) => t.op === 'const' || (t.op === 'var' && json(last).includes(`"name":${json(t.name)}`))
  const all0 = [...reads(goal.hyps, mp => byMap.has(mp)).values()], inLast = [...reads(last, mp => byMap.has(mp)).keys()]
  const rank = ([mp, t]: [string, E]) => (inLast.includes(json([mp, t])) ? 0 : own(t) ? 1 : 2)
  const rs = all0.sort((x, y) => rank(x) - rank(y))
  // (each read after the step beside its twin before it, when the goal declares both)
  for (const [mp, t] of [...rs]) if (mp.endsWith('#') && byMap.has(mp.slice(0, -1)) && !rs.some(([m2, t2]) => m2 === mp.slice(0, -1) && json(t2) === json(t))) rs.push([mp.slice(0, -1), t])
  const named: MapRead[] = rs.slice(0, 6).map(([mp, t], i) => [`r$${i}`, mp, t])
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
  const until = clock() + ms, g = guardLaws(m0), m: Machine = {...m0, counts: {...m0.counts, ...g.counts}}
  // The small instances: each param 2 and 3 (where the precondition allows), inputs and sets below 3.
  const insts = [2, 3].map(x => Object.fromEntries(m.params.map(p => [p, x])) as Env)
  const states = insts.map(p => {
    try { return {p, sts: small(m, p, 3)} } catch { return {p, sts: [] as State[]} }
  })
  const kinds: Law[] = Object.keys(m.maps ?? {}).map(mp => {
    const most = Math.max(0, ...states.flatMap(({sts}) => sts.flatMap(st => [...(st.maps[mp]?.values() ?? [])])))
    return {name: `${mp} at most ${most}`, forall: 'a$c', holds: {op: '<=', a: {op: 'get', map: mp, key: v('a$c')}, b: k(most)}} as Law
  })
  const trueAll = (l: Law) => clock() < until && states.every(({p, sts}) => sts.every(st => holdsAt(m, l, p, st, 4)))
  if (!caller.every(trueAll)) return {proven: false, laws: caller, m, why: clock() < until ? 'a law fails on the small instances' : 'time'}
  // (the engine's minimal ∀ cubes on its own small instances and data filter, core/infer.ts's: the supports no guard reads)
  const t1 = clock(), cubes = inferLaws(m0, caller, [], {cubes: 2, ms: Math.min(15_000, ms / 4), first: {proven: false, checked: false}}).found.map(f => f.law)
  if (env.GDP_COUNTS_TRACE) console.error(`counts: cubes ${cubes.length} in ${Math.round(clock() - t1)} ms: ${cubes.map(l => l.name).join('; ')}`)
  let set = [...caller, ...[...kinds, ...g.laws, ...cubes].filter(trueAll)]
  if (env.GDP_COUNTS_TRACE) console.error(`counts: candidates ${set.map(l => l.name).join('; ')}`)
  for (let round = 0; clock() < until; round++) {
    // (the law's own names and the request's values that key a map: an action's value keys none)
    const keys0 = [...[...reads([m.step, m.assume ?? null], () => true).values()].map(([, key]) => key), ...Object.values(m.step.maps ?? {}).flatMap(w => ('each' in w ? [] : [w.key]))]
    const keyed = m.inputs.filter(i => keys0.some(key => mentions(key, i)))
    const terms = (l: Law): E[] => [...(l.forall ? [v(`${l.forall}#`)] : []), ...(l.keys ?? []).map(v), ...(knob.keyed ? keyed : m.inputs).map(v)]
    const instances: Record<string, Instances> = {}, certs: Record<string, CountCert> = {}, failed = new Set<string>()
    for (const law of set) {
      if (clock() > until) return {proven: false, laws: set, m, why: 'time'}
      const ts = terms(law)
      // (the laws over one key at pairs of the law's own names and the request's, every-key laws at those; the rest, and
      // the witnesses, by the goal's reads below)
      const inst = (): Instances => {
        const out: Instances = {}
        for (const l of set) {
          if (l.keys?.length === 1 && knob.pairs) out[l.name] = ts.flatMap(x => ts.flatMap(y => (json(x) === json(y) ? [] : [x, y])))
          else if (!l.keys?.length && l.forall && knob.ts) out[l.name] = [...ts]
        }
        for (const [f, q] of Object.entries(m.step.flags ?? {})) if (q.op === 'all' && !q.keys?.length) out[`?${f}`] = knob.flagTs ? ts : m.inputs.map(v)
        return out
      }
      // (more instances where the goal's reads meet a law's: each keyed law and quantified flag, matched; at most twice)
      const more = (at: Instances, hyps: C[][]): boolean => {
        const cells = [...ground(hyps).values()]
        let grew = false
        const add = (name: string, ts2: E[][]) => {
          const have = new Set<string>(), cur = at[name] ?? [], n = ts2[0]?.length ?? 1
          for (let i = 0; i + n <= cur.length; i += n) have.add(json(cur.slice(i, i + n)))
          for (const t of ts2) if (!have.has(json(t))) { have.add(json(t)); at[name] = [...(at[name] ?? []), ...t]; grew = true }
        }
        for (const l of set) if (l.forall) add(l.name, matched([l.forall, ...(l.keys ?? [])], l.holds, cells))
        for (const [f, q] of Object.entries(m.step.flags ?? {})) if (q.op === 'all' && !q.keys?.length) add(`?${f}`, matched([q.key], q.c, cells))
        return grew
      }
      // The goals' certificates: first with no instances of the lemma, then with the cells' (one set of witnesses a law).
      let ok = true
      for (const pass of [0, 1]) {
        instances[law.name] = inst()
        ok = true
        let built: {goal: {name: string, hyps: C[]}, c: Pick<CountCert, 'reads' | 'insts'>, gg: ReturnType<typeof mcGoal>}[] = []
        for (let r = 0; r <= knob.rounds; r++) {
          built = countedObligations(m, set, instances, set.indexOf(law)).map(({goal, decls}) => {
            const c = pass ? certFor(goal, decls) : {reads: [] as MapRead[], insts: [] as CountInst[]}
            return {goal, c, gg: mcGoal(goal.hyps, decls, c)}
          })
          if (r === knob.rounds || !more(instances[law.name]!, built.map(b => b.gg?.hyps ?? b.goal.hyps))) break
        }
        // (a step goal past a few hundred hypotheses: the CDCL search's refutation first, its core naming the law instances
        // it read; the law's instances cut to those, and its goals grown with them, the certificate's reads kept)
        const step = built.at(-1)
        if (step?.gg && step.gg.hyps.length > knob.shrink) {
          const q = growCdcl(step.gg, new Map(), {nodes: 0, until: Math.min(until, clock() + 5_000)}, {model: true, core: true}) as Refuted
          if (!('tree' in q) && q.why === REFUTED && q.core) {
            const used = new Set(q.core.map(h => json(step.gg!.hyps[h]))), at = instances[law.name]!, cut: Instances = {}
            for (const [name, ts2] of Object.entries(at)) {
              const l = set.find(x => x.name === name), n = l ? 1 + (l.keys?.length ?? 0) : 0
              cut[name] = !l ? ts2 : Array.from({length: ts2.length / n}, (_, t) => ts2.slice(t * n, t * n + n)).filter(t => used.has(json(assumed([l], {[name]: t})[0]))).flat()
            }
            instances[law.name] = cut
            built = countedObligations(m, set, instances, set.indexOf(law)).map(({goal, decls}, j) => ({goal, c: built[j]!.c, gg: mcGoal(goal.hyps, decls, built[j]!.c)}))
          }
        }
        for (const {goal, c, gg} of built) {
          const o = gg && grow(gg, new Map(), {nodes: 0, until: Math.min(until, clock() + 10_000)})
          if (!o || !('tree' in o)) {
            ok = false
            if (env.GDP_COUNTS_TRACE && pass) console.error(`counts: ${goal.name}: ${gg ? json(o).slice(0, 300) : 'a read of no count'} (reads ${c.reads.map(r => `${r[1]}[${json(r[2])}]`).join(' ')})`)
            break
          }
          certs[goal.name] = {reads: c.reads, insts: c.insts, tree: o.tree}
        }
        if (ok) break
      }
      if (!ok) failed.add(law.name)
    }
    if (!failed.size) {
      const proof = {instances, certs}
      return checkCountedLaws(m, set, proof) ? {proven: true, laws: set, m, proof} : {proven: false, laws: set, m, why: 'the kernel refused the set'}
    }
    if (caller.some(l => failed.has(l.name)) && set.length === caller.length) return {proven: false, laws: set, m, why: `not proven: ${[...failed].join(', ')}`}
    const next = set.filter(l => !failed.has(l.name) || caller.includes(l))
    if (next.length === set.length) {
      // only callers fail: drop nothing more, give up
      return {proven: false, laws: set, m, why: `not proven: ${[...failed].join(', ')}`}
    }
    set = next
  }
  return {proven: false, laws: set, m, why: 'time'}
}
