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
import {type C, type E, type Law, type Machine, type Request, type State, carriedView, evalC, interpret} from './machine.ts'
import {type CountCert, type CountInst, type Instances, type MapRead, checkCountedLaws, countedObligations, mcGoal, postName, substC, substE} from '../kernel/kernel.ts'
import {clock, grow} from '../kernel/prove.ts'

const v = (name: string): E => ({op: 'var', name}), k = (value: number): E => ({op: 'const', value})
const json = (t: unknown) => JSON.stringify(t)
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

// --- relations over pairs: one value per first key, and one relation inside another ---------------------------------
// A map written at x·N + y (a relation, x's row) is a candidate for "at most one y in a row", and each two such maps for
// "one holds where the other does", at the same pair or the swapped one; the small instances keep the true ones.
export function pairLaws(m: Machine): Law[] {
  const widths = new Map<string, number>()
  for (const [mp, w] of Object.entries(m.step.maps ?? {})) if (!('each' in w) && w.key.op === 'add' && w.key.a.op === 'mul' && w.key.a.a.op === 'var' && w.key.b.op === 'var') widths.set(mp, w.key.a.k)
  const at = (mp: string, x: string, y: string, n: number): E => ({op: 'get', map: mp, key: {op: 'add', a: {op: 'mul', k: n, a: v(x)}, b: v(y)}})
  const has = (e: E): C => ({op: '<=', a: one, b: e}), lt = (x: string, n: number): C => ({op: '<', a: v(x), b: k(n)})
  const out: Law[] = []
  for (const [mp, n] of widths) out.push({name: `${mp}: one per row`, forall: 'p$c', keys: ['q$c', 'r$c'], holds: {op: 'or', xs: [{op: 'not', x: {op: 'and', xs: [lt('q$c', n), lt('r$c', n), has(at(mp, 'p$c', 'q$c', n)), has(at(mp, 'p$c', 'r$c', n))]}}, {op: '=', a: v('q$c'), b: v('r$c')}]}})
  for (const [a, n] of widths) for (const [b, n2] of widths) if (a !== b && n === n2) for (const swap of [false, true])
    out.push({name: `${a} inside ${b}${swap ? ', swapped' : ''}`, forall: 'p$c', keys: ['q$c'], holds: {op: 'or', xs: [{op: 'not', x: {op: 'and', xs: [lt('q$c', n), lt('p$c', n), has(at(a, 'p$c', 'q$c', n))]}}, has(swap ? at(b, 'q$c', 'p$c', n) : at(b, 'p$c', 'q$c', n))]}})
  // (and over one key: where one map's cell is set, another's is)
  const singles = Object.entries(m.step.maps ?? {}).filter(([, w]) => !('each' in w) && w.key.op === 'var').map(([mp]) => mp)
  for (const a of singles) for (const b of singles) if (a !== b)
    out.push({name: `${a} inside ${b}`, forall: 'p$c', holds: {op: 'or', xs: [{op: 'not', x: has({op: 'get', map: a, key: v('p$c')})}, has({op: 'get', map: b, key: v('p$c')})]}})
  return out
}

// --- the small instances --------------------------------------------------------------------------------------------------
// Every state reached from the start with the params at `p`, each input below `b`, each carried map a subset of 0 .. b − 1.
export function small(m: Machine, p: Env, b: number, cap = 3000): State[] {
  const run = interpret(m), start = run.init(p)
  const subsets = Array.from({length: 1 << b}, (_, s) => new Map(Array.from({length: b}, (_, i) => i).filter(i => (s >> i) & 1).map(i => [i, 1] as [number, number])))
  let reqs: Request[] = [{}]
  for (const i of m.inputs) reqs = reqs.flatMap(r => Array.from({length: b}, (_, x) => ({...r, [i]: x})))
  for (const c of m.inputMaps ?? []) reqs = reqs.flatMap(r => subsets.map(s => ({...r, [c]: s})))
  const seen = new Map<string, State>([[json(start), start]]), queue = [start]
  while (queue.length && seen.size < cap) {
    const st = queue.shift()!
    for (const r of reqs) {
      let next: State
      try { next = run.step(p, st, r) } catch { continue }
      const key = json([next.scalars, Object.entries(next.maps).map(([n, cs]) => [n, [...cs].filter(([, x]) => x).sort((a, c) => a[0] - c[0])])])
      if (!seen.has(key)) { seen.set(key, next); queue.push(next) }
    }
  }
  return [...seen.values()]
}
// A law at a state, its counts the state's, at every key below b.
function holdsAt(m: Machine, law: Law, p: Env, st: State, b: number): boolean {
  const empty: Request = Object.fromEntries((m.inputMaps ?? []).map(c => [c, new Map()]))
  const view = carriedView(m, st, empty, undefined, p), keys = [law.forall, ...(law.keys ?? [])].filter((x): x is string => !!x)
  const go = (env: Env, ks: string[]): boolean => (ks.length ? Array.from({length: b}, (_, x) => x).every(x => go({...env, [ks[0]!]: x}, ks.slice(1))) : evalC(law.holds, {...env, ...st.scalars}, view, m))
  return go({...p}, keys)
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
  const trueAll = (l: Law) => states.every(({p, sts}) => sts.every(st => holdsAt(m, l, p, st, 4)))
  if (!caller.every(trueAll)) return {proven: false, laws: caller, m, why: 'a law fails on the small instances'}
  let set = [...caller, ...[...kinds, ...pairLaws(m), ...g.laws].filter(trueAll)]
  if (process.env.GDP_COUNTS_TRACE) console.error(`counts: candidates ${set.map(l => l.name).join('; ')}`)
  for (let round = 0; clock() < until; round++) {
    const terms = (l: Law): E[] => [...(l.forall ? [v(`${l.forall}#`)] : []), ...(l.keys ?? []).map(v), ...m.inputs.map(v)]
    const instances: Record<string, Instances> = {}, certs: Record<string, CountCert> = {}, failed = new Set<string>()
    for (const law of set) {
      if (clock() > until) return {proven: false, laws: set, m, why: 'time'}
      const ts = terms(law)
      const inst = (wits: string[]): Instances => {
        const out: Instances = {}
        for (const l of set) {
          if (l.keys?.length === 1) out[l.name] = ts.flatMap(x => ts.flatMap(y => (json(x) === json(y) ? [] : [x, y])))
          else if (l.keys?.length === 2) out[l.name] = ts.flatMap(x => ts.flatMap(y => ts.flatMap(z => (json(y) === json(z) ? [] : [x, y, z]))))
          else if (l.forall) out[l.name] = [...ts, ...wits.map(v)]
        }
        for (const [f, q] of Object.entries(m.step.flags ?? {})) if (q.op === 'all' && !q.keys?.length) out[`?${f}`] = [...wits.map(v), ...m.inputs.map(v)]
        return out
      }
      // The goals' certificates: first with no instances of the lemma, then with the cells' (one set of witnesses a law).
      let ok = true
      for (const pass of [0, 1]) {
        const wits0 = pass ? Array.from({length: 10}, (_, i) => `w$${i}`) : []
        instances[law.name] = inst(wits0)
        ok = true
        for (const {goal, decls} of countedObligations(m, set, instances, set.indexOf(law))) {
          const c = pass ? certFor(goal, decls) : {reads: [] as MapRead[], insts: [] as CountInst[]}
          const gg = mcGoal(goal.hyps, decls, c)
          const o = gg && grow(gg, new Map(), {nodes: 0, until: Math.min(until, clock() + 10_000)})
          if (!o || !('tree' in o)) {
            ok = false
            if (process.env.GDP_COUNTS_TRACE && pass) console.error(`counts: ${goal.name}: ${gg ? json(o).slice(0, 300) : 'a read of no count'} (reads ${c.reads.map(r => `${r[1]}[${json(r[2])}]`).join(' ')})`)
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
