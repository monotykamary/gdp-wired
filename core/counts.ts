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
//   4. counted induction: prove the proposed set together, drop failed helpers, and carry proofs whose instantiated
//      support survives. Avoid proving the same helpers in several preliminary cone contexts; checkCountedLaws
//      checks the final set. The ∃ search still uses `cone`: relative induction from already-kept candidates.
import {type C, type E, type Law, type Machine} from './machine.ts'
import {type CountCert, type CountInst, type Goal, type Instances, type MapRead, assumed, checkCountedLaws, checkMC, countedObligations, mcGoal, scope, substC, substE} from '../kernel/kernel.ts'
import {brokenOf, clock, counted, fullRate, grow, modelInstances, wallAt, widen, usedHyps, withDeadline, withWall} from '../kernel/prove.ts'
import {REFUTED, cdclStats} from '../kernel/cdcl.ts'
import {modelSequence} from '../kernel/model-sequence.ts'
import {inferLaws} from './infer.ts'
import {carryCandidates, scanPrefixes} from './carry.ts'
import {relevantGoals, relevantLaws} from './relevance.ts'
import {countPoolKey, countSignature, grammarPool, ids, polaritySelection, readTuples, refinementSignature, reservationReadClosure, reservationState, reservePool, prepareSupport, smallSelection, sparseReadInstances, sourceContext, coarseContext, selectedCertificate, chosenView, candidateWork, stableState, UnsupportedCountProposal} from './count-support.ts'
import {fieldLaws} from './field-laws.ts'
import {countsForReads, proposeCountFacts} from './count-facts.ts'
import {proposeCountUnions} from './count-unions.ts'
import {focusedCountRecoveryEnabled,proveFocusedCounts} from './count-focus-proof.ts'
import {smallOf, trueSmall} from './exists.ts'
import {env} from './solver.ts'
import {proofOrigins, proposeLemmaCuts} from './lemma-cuts.ts'

// (GDP_COUNTS_PROF: where a counted search's time goes, by phase, on stderr at the end; `countsDump.on`, set by research's
// profiles: each step goal left unknown or with a model past GDP_COUNTS_DUMP_MIN (300) hypotheses, the first GDP_COUNTS_DUMP_N (3))
export const cprof: Record<string, number> = {}
export const countsDump: {on?: (goal: object) => void} = {}
const tally = (k: string, n = 1) => { cprof[k] = (cprof[k] ?? 0) + n }
const ptime = <T>(k: string, f: () => T): T => { const t = performance.now(); try { return f() } finally { cprof[k] = (cprof[k] ?? 0) + performance.now() - t } }
let dumped = 0
// (GDP_COUNTS_LAZY=0: every instance and pick certFor proposes in the goal at once, as before; `wide`: the narrow
// instances at once, the widened goal's further instances and picks lazily)
const lazyMode = env.GDP_COUNTS_LAZY ?? 'wide', pool = Number(env.GDP_COUNTS_POOL ?? 1000)

const v = (name: string): E => ({op: 'var', name}), k = (value: number): E => ({op: 'const', value})
const json = (t: unknown) => JSON.stringify(t)
const one = k(1), zero = k(0)

// Every term t with `get(map, t)` in t0.
function reads(t0: unknown, map: (m: string) => boolean, out: Map<string, [string, E]> = new Map(), more?: () => boolean): Map<string, [string, E]> {
  const go = (x: unknown): boolean => {
    if (more && !more()) return false
    if (!x || typeof x !== 'object') return true
    const o = x as Record<string, unknown>
    if (o.op === 'get' && map(o.map as string)) out.set(json([o.map, o.key]), [o.map as string, o.key as E])
    for (const y of Object.values(o)) if (!go(y)) return false
    return true
  }
  go(t0)
  return out
}
const mentions = (t: unknown, name: string) => json(t).includes(`"name":${json(name)}`)
// Whether some object within t0 meets p (a condition nested in a term's `if` too).
const some = (t0: unknown, p: (x: any) => boolean): boolean => !!t0 && typeof t0 === 'object' && (p(t0) || Object.values(t0).some(y => some(y, p)))
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
    // (the written key: a request's value t, or two, t and u, composed N·t + u (a relation's cell): a count of two
    // parameters, read at the law's N·a + b with b < N)
    if ('each' in w) continue
    const k0 = w.key, ps = k0.op === 'var' ? [k0.name] : k0.op === 'add' && k0.a.op === 'mul' && k0.a.k > 1 && k0.a.a.op === 'var' && k0.b.op === 'var' && k0.a.a.name !== k0.b.name ? [k0.a.a.name, k0.b.name] : []
    if (!ps.length || !ps.every(i => m.inputs.includes(i))) continue
    const t = ps[0]!, base = ps.length === 2 && k0.op === 'add' && k0.a.op === 'mul' ? k0.a.k : 0, written = inline({op: '<=', a: one, b: w.value} as C)
    const at: E = base ? {op: 'add', a: {op: 'mul', k: base, a: v('a$c')}, b: v('b$c')} : v('a$c')
    const law = (name: string, cmp: C): Law => (base
      ? {name, forall: 'a$c', keys: ['b$c'], holds: {op: 'or', xs: [{op: 'not', x: {op: 'and', xs: [{op: '<=', a: one, b: {op: 'get', map: mp, key: at}}, {op: '<', a: v('b$c'), b: k(base)}]}}, cmp]}}
      : when(name, {op: '<=', a: one, b: {op: 'get', map: mp, key: v('a$c')}}, cmp))
    // A comparison with a state count at the written key.
    if (!base) for (const g of guards) for (const [, [c, key]] of reads(g, isCount)) {
      if (json(key) !== json(v(t)) || mentions(m.counts![c]!.body, t)) continue
      if (m.inputs.some(i => i !== t && mentions(g, i))) continue
      laws.push(law(`${mp} keeps ${c}'s bound`, substC(g, {vars: {[t]: v('a$c')}, maps: {}, flags: {}})))
    }
    // What the write reads of every member of a counted set: R(member, t) by a quantified flag (∀ q. h(q) → R(q, t)),
    // or by a request's count of the members without it read 0 (|{k: h(k) ∧ ¬R(k, t)}| = 0).
    const said: {key: string, h: C, r: C}[] = []
    for (const [f, q] of Object.entries(flags)) {
      if (q.op !== 'all' || q.keys?.length || !mentions(written, `?${f}`) || q.c.op !== 'or' || q.c.xs.length !== 2) continue
      const [h, r] = q.c.xs[0]!.op === 'not' ? [q.c.xs[0]!.x, q.c.xs[1]!] : [q.c.xs[1]!.op === 'not' ? q.c.xs[1]!.x : undefined, q.c.xs[0]!]
      if (h && r) said.push({key: q.key, h, r})
    }
    for (const [c0, d0] of Object.entries(m.counts ?? {})) {
      const zero0 = some(written, x => x.op === '=' && x.a?.op === 'get' && x.a.map === c0 && x.b?.op === 'const' && x.b.value === 0)
      const b0 = d0.body.op === 'if' && d0.body.c.op === 'and' && d0.body.c.xs.length === 2 ? d0.body.c.xs : undefined
      if (!zero0 || !b0 || mentions([d0.body, d0.below], d0.j)) continue
      const [h, r] = b0[1]!.op === 'not' ? [b0[0]!, b0[1]!.x] : b0[0]!.op === 'not' ? [b0[1]!, b0[0]!.x] : []
      if (h && r) said.push({key: d0.key, h, r})
    }
    for (const {key: qk, h, r} of said) {
      for (const [c, d] of Object.entries(all)) {
        // the set: the count's body is the hypothesis at its key
        const body = d.body.op === 'if' ? d.body.c : undefined
        if (!body || json(substC(body, {vars: {[d.key]: v(qk)}, maps: {}, flags: {}})) !== json(h)) continue
        if (m.inputs.some(i => !ps.includes(i) && mentions(r, i))) continue
        const name = `${c}$${mp}`, j = `${name}$x`, key = `${name}$k`, lo = `${name}$y`
        counts[name] = {j, key, below: d.below, body: {op: 'if', c: substC(r, {vars: {[qk]: v(key), [t]: v(j), ...(base ? {[ps[1]!]: v(lo)} : {})}, maps: {}, flags: {}}), then: one, else: zero}, ...(base ? {lo, base} : {})}
        for (const g of [...guards, ...more]) if (reads(g, x => x === c).size)
          laws.push(law(`${mp} keeps ${c}'s bound through ${name}`, substC(g, {vars: {}, maps: {[c]: () => ({op: 'get', map: name, key: at})}, flags: {}})))
      }
    }
  }
  // Who did or still can write a relation: a write W[N²·n + N·t + u] := 1 by a request's node n (below the bound of the
  // set the guard counts) under a flag whose literals reading n are G(n, t, u). Its count over two parameters,
  // c(t, u) = |{k: G(k, t, u) ∨ W[N²·k + N·t + u]}|, the keys that wrote it at (t, u) or may yet; a set the guard counts
  // and every such k meet unless c is at most what the guard's comparison forbids. Proposed under each map P the flag
  // reads at N·t + u alone (a cell the writes at (t, u) need), at another (c, d): P[N·c + d] ∧ a < c (∧ b ≠ d, or a ≤ c ∧
  // b ≠ d) ⇒ ¬(the guard's comparison with c at (a, b)): no majority could write W at (a, b) once P holds further on.
  const lin = (e: E): Map<string, number> | undefined => {
    if (e.op === 'var') return new Map([[e.name, 1]])
    if (e.op === 'mul' && e.a.op === 'var') return new Map([[e.a.name, e.k]])
    if (e.op !== 'add') return undefined
    const x = lin(e.a), y = lin(e.b)
    if (!x || !y || [...x.keys()].some(q => y.has(q))) return undefined
    return new Map([...x, ...y])
  }
  const conj = (c: C): C[] => (c.op === 'and' ? c.xs.flatMap(conj) : [c])
  for (const [mp, w] of Object.entries(m.step.maps ?? {})) {
    if ('each' in w) continue
    const l = lin(w.key), es = l && [...l.entries()].sort((x, y) => y[1] - x[1])
    if (!es || es.length !== 3 || !es.every(([q]) => m.inputs.includes(q))) continue
    const [[nd, c0], [t, c1], [u, c2]] = es as [[string, number], [string, number], [string, number]]
    if (c2 !== 1 || c1 < 2 || c0 !== c1 * c1) continue
    const base = c1
    for (const [f, fc] of Object.entries(flags)) {
      if (fc.op === 'all' || !json(w.value).includes(`"op":"flag","name":${json(f)}`)) continue
      const parts = conj(inline(fc)), dep = parts.filter(x => mentions(x, nd))
      if (!dep.length || dep.some(x => m.inputs.some(i => ![nd, t, u].includes(i) && mentions(x, i)))) continue
      const ps = parts.flatMap(x => (x.op === '=' && x.a.op === 'get' && x.b.op === 'const' && x.b.value === 1 ? [x.a] : x.op === '<=' && x.a.op === 'const' && x.a.value === 1 && x.b.op === 'get' ? [x.b] : []))
        .filter(g => { const kl = lin(g.key); return !!kl && kl.size === 2 && kl.get(t) === base && kl.get(u) === 1 })
      if (!ps.length) continue
      for (const [c, d] of Object.entries(all)) {
        if (d.body.op !== 'if' || !json(m.assume).includes(json({op: '<', a: v(nd), b: d.below}))) continue
        const gs = guards.filter(g => reads(g, x => x === c).size)
        if (!gs.length || mentions(d.body, d.j)) continue
        const name = `can$${mp}$${c}`, j = `${name}$x`, key = `${name}$k`, lo = `${name}$y`, sub = {vars: {[nd]: v(key), [t]: v(j), [u]: v(lo)}, maps: {}, flags: {}}
        const body: C = {op: 'or', xs: [{op: 'and', xs: dep.map(x => substC(x, sub))}, {op: '<=', a: one, b: {op: 'get', map: mp, key: substE(w.key, sub)}}]}
        counts[name] = {j, key, lo, base, below: d.below, body: {op: 'if', c: body, then: one, else: zero}}
        const pk2 = (a: string, b: string): E => ({op: 'add', a: {op: 'mul', k: base, a: v(a)}, b: v(b)})
        for (const g of gs) for (const pg of ps) for (const [r1, r2] of [['<', true], ['<', false], ['<=', true]] as const) {
          const hyp: C = {op: 'and', xs: [{op: '<=', a: one, b: {op: 'get', map: pg.map, key: pk2('c$c', 'd$c')}}, {op: r1, a: v('a$c'), b: v('c$c')} as C,
            ...(r2 ? [{op: 'not', x: {op: '=', a: v('b$c'), b: v('d$c')}} as C] : []), {op: '<', a: v('b$c'), b: k(base)}, {op: '<', a: v('d$c'), b: k(base)}]}
          laws.push({name: `${pg.map} at (c, d) bounds ${name} at (a, b): a ${r1} c${r2 ? ', b ≠ d' : ''}`, forall: 'a$c', keys: ['b$c', 'c$c', 'd$c'],
            holds: {op: 'or', xs: [{op: 'not', x: hyp}, {op: 'not', x: substC(g, {vars: {}, maps: {[c]: () => ({op: 'get', map: name, key: pk2('a$c', 'b$c')})}, flags: {}})}]}})
        }
      }
    }
  }
  return {counts, laws}
}

// --- a goal's certificate -------------------------------------------------------------------------------------------------
// The count cells the goal reads (each before the step with its post name's twin), instances over pairs of them with one
// bound (a count that doesn't drop, +1 and −1; two that meet, +1, +1 and −1), each with a fresh witness; and the laws and
// quantified flags at the witnesses (returned, for the goal's law's instances).
export function certFor(goal: {hyps: C[]}, decls: {map: string, below: E, j: string, key: string, body: E}[], wide = false, most = wide ? 24 : 10, more?: () => boolean, structured = true): {reads: MapRead[], insts: CountInst[], wits: string[], picks: [string, E[]][], loose: boolean} {
  const tick = more ?? (() => true), byMap = new Map(decls.map(d => [d.map, d])), last = goal.hyps.at(-1), lastText = json(last)
  const own = (t: E) => t.op === 'const' || (t.op === 'var' && lastText.includes(`"name":${json(t.name)}`))
  const all0 = [...reads(goal.hyps, mp => byMap.has(mp), new Map(), more).values()], inLast = [...reads(last, mp => byMap.has(mp), new Map(), more).keys()]
  const rank = ([mp, t]: [string, E]) => (inLast.includes(json([mp, t])) ? 0 : own(t) ? 1 : 2)
  const rs = all0.sort((x, y) => rank(x) - rank(y))
  for (const [mp, t] of [...rs]) { if (!tick()) break; if (mp.endsWith('#') && byMap.has(mp.slice(0, -1)) && !rs.some(([m2, t2]) => m2 === mp.slice(0, -1) && json(t2) === json(t))) rs.push([mp.slice(0, -1), t]) }
  const once = new Set<string>(), keyless = (mp: string) => { const d = byMap.get(mp)!; return !mentions([d.below, d.body], d.j) }
  const rs1 = rs.filter(([mp]) => !keyless(mp) || (!once.has(mp) && !!once.add(mp)))
  const named: MapRead[] = rs1.map(([mp, t], i) => ['r'+'$'+i, mp, t]), bound = (r: MapRead) => json(byMap.get(r[1])!.below)
  const insts: CountInst[] = [], wits: string[] = [], cap = most, initialCap = wide ? Math.min(10, cap) : cap
  const add = (terms: [number, string][], unit: number, below: E) => { const w = 'w'+'$'+insts.length; wits.push(w); insts.push({wit: w, below, terms, unit}) }
  const post = (r: MapRead) => r[1].endsWith('#'), ranked = (r: MapRead) => rank([r[1], r[2]]) <= 1
  // Stop enumeration as soon as the requested prefix is complete. Later entries
  // were sliced away before too; the order and contents of completed prefixes stay exact.
  initial: {
    for (const c of named) if (post(c)) for (const a of named) {
      if ((!!more && insts.length >= initialCap) || !tick()) break initial
      if (a !== c && !post(a) && bound(a) === bound(c)) add([[1, a[0]], [-1, c[0]]], 0, byMap.get(c[1])!.below)
    }
    for (const [i, a] of named.entries()) for (const [j, c] of named.entries()) {
      if ((!!more && insts.length >= initialCap) || !tick()) break initial
      if (i < j && (ranked(a) || ranked(c)) && bound(a) === bound(c) && !post(a) && !post(c)) add([[1, a[0]], [1, c[0]]], -1, byMap.get(a[1])!.below)
    }
    for (const [i, a] of named.entries()) for (const [j, c] of named.entries()) {
      if ((!!more && insts.length >= initialCap) || !tick()) break initial
      if (i < j && !(ranked(a) || ranked(c)) && bound(a) === bound(c) && !post(a) && !post(c)) add([[1, a[0]], [1, c[0]]], -1, byMap.get(a[1])!.below)
    }
    for (const c of named) if (post(c) && rank([c[1], c[2]]) === 0) for (const a of named) for (const d of named) {
      if ((!!more && insts.length >= initialCap) || !tick()) break initial
      if (a !== d && !post(a) && !post(d) && keyless(a[1]) && keyless(d[1]) && bound(a) === bound(c) && bound(d) === bound(c)) add([[1, a[0]], [-1, d[0]], [-1, c[0]]], 0, byMap.get(c[1])!.below)
    }
  }
  if (wide) {
    insts.splice(10); wits.splice(10)
    pairs: for (const a of named) for (const c of named) {
      if ((!!more && insts.length >= cap) || !tick()) break pairs
      if (a !== c && bound(a) === bound(c) && !(post(c) && !post(a))) add([[1, a[0]], [-1, c[0]]], 0, byMap.get(a[1])!.below)
    }
    for (const a of named) { if ((!!more && insts.length >= cap) || !tick()) break; add([[1, a[0]]], 0, byMap.get(a[1])!.below) }
    if (cap > 24) {
      for (const a of named) { if ((!!more && insts.length >= cap) || !tick()) break; add([[1, a[0]]], -1, byMap.get(a[1])!.below) }
      const had = new Set(insts.map(i => json([i.terms, i.unit])))
      meets: for (const [i, a] of named.entries()) for (const [j, c] of named.entries()) {
        if ((!!more && insts.length >= cap) || !tick()) break meets
        if (i < j && bound(a) === bound(c) && post(a) === post(c) && !had.has(json([[[1, a[0]], [1, c[0]]], -1]))) add([[1, a[0]], [1, c[0]]], -1, byMap.get(a[1])!.below)
      }
    }
    // Structured identities supplement the legacy pool; they must not displace
    // its witness prefix at the same cap. Both generators remain available on
    // expansion; every proposal is checked as an ordinary witness certificate.
    // Do not construct a tail that the unchanged cap would immediately discard.
    const cs = structured && insts.length < cap ? countsForReads(decls, named) : undefined
    if (cs && tick()) {
      const facts = proposeCountFacts(cs, goal, {maxFacts: Math.min(cap, 256), reserved: wits})
      for (const q of facts.insts) {
        if ((!!more && insts.length >= cap) || !tick()) break
        if (q.terms.length >= 3) add(q.terms, q.unit, q.below)
      }
      const heads = named.filter(r => ranked(r)).sort((a, b) => Number(post(b)) - Number(post(a)))
      const carried = named.filter(r => !post(r) && keyless(r[1]))
      const pairs: [string, string][] = heads.flatMap(a => carried.filter(b => b !== a && bound(a) === bound(b)).map(b => [a[0], b[0]] as [string, string]))
      for (const q of proposeCountUnions(cs, pairs, Math.min(cap, 128))) { if ((!!more && insts.length >= cap) || !tick()) break; add(q.terms, q.unit, q.below) }
    }
  }
  const picks: [string, E[]][] = []
  // A counted member can be one component of a tuple/packed key, not only
  // the whole map key. These are candidate naturals, never inverse-function
  // axioms: mcGoal/checkMC still check the count body at every picked key.
  const memberKeys = (pattern: E, term: E, key: string): E[] => {
    if (pattern.op === 'var') return pattern.name === key ? [term] : []
    if (pattern.op !== term.op) return []
    const p = pattern as unknown as Record<string, E>, t = term as unknown as Record<string, E>
    return ['a', 'b', 'key', 'then', 'else'].flatMap(k => p[k] && t[k] ? memberKeys(p[k]!, t[k]!, key) : [])
  }
  if (wide) for (const r of named) {
    if (!tick()) break
    const d = byMap.get(r[1])!, at = [...reads(d.body, () => true, new Map(), more).values()].filter(([, key]) => mentions(key, d.key))
    if (!at.length) continue
    // (the key terms the goal reads those maps at, and the witnesses of the instances that name this count: a member the
    // counting lemma found is a key too; three of each first, six at most)
    const candidates = [...reads(goal.hyps, mp => at.some(([p]) => p === mp), new Map(), more).values()].flatMap(([mp, t]) => at.filter(([p]) => p === mp).flatMap(([, pattern]) => memberKeys(pattern, t, d.key)))
    const gs = [...new Map(candidates.map(t => [json(t), t] as [string, E])).values()].filter(t => !mentions(t, d.key))
    const ws = insts.slice(0, cap).filter(i => i.terms.some(([, x]) => x === r[0])).map(i => v(i.wit)), ts0 = [...gs.slice(0, 3), ...ws.slice(0, 3), ...gs.slice(3), ...ws.slice(3)]
    const ts = [...new Map(ts0.map(t => [json(t), t] as [string, E])).values()].slice(0, 6)
    for (const t of ts) picks.push([r[0], [t]])
    for (let i = 0; i < ts.length; i++) for (let j = i + 1; j < ts.length; j++) picks.push([r[0], [ts[i]!, ts[j]!]])
    if (ts.length > 2) picks.push([r[0], ts])
  }
  const loose = named.some(r => !insts.slice(0, 10).some(i => i.terms.some(([, x]) => x === r[0])))
  return {reads: named, insts: insts.slice(0, cap), wits: wits.slice(0, cap), picks, loose}
}

// --- the candidates --------------------------------------------------------------------------------------------------
// One list from the machine's shapes, each kept only if true on every small state: each map's cells at most what the
// small instances reach; the guards' count comparisons (guardLaws, `guarded`); one key a row; the engine's minimal ∀
// cubes of at most two literals (core/infer.ts's `cubes`, read off these small states, within a quarter of the search's
// budget `ms`, 15 s at most), its template `shapes` (the caller's laws, or an ∃ law's frame), each guard `u < param` loosened where a caller reads u with no param bound.
export function candidates(src: Parameters<typeof inferLaws>[0], m: Machine, caller: Law[], shapes: Law[], guarded: Law[], ms: number, until: number, support = new Set<Law>()): Law[] {
  const states = ptime('small', () => smallOf(m))
  // (a law of the state only: one the kernel's scope refuses, reading an input or a count of the request (a guard's
  // comparison with a second request count), has no value at a state, and is not proposed)
  const ofState = (l: Law) => { try { scope(m, [l]); return true } catch { return false } }
  const trueAll = (l: Law) => clock() < until && ofState(l) && trueSmall(m, [l])
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
  // (the cubes' budget counted, their wall stop the search's own: a slow machine finds the same cubes, later)
  const cubes0 = ptime('cubes', () => inferLaws(src, shapes, [], {cubes: 2, ms: Math.min(15_000, ms / 4), wall: wallAt(), first: {proven: false, checked: false}, rows}).found.map(f => f.law))
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
  const cubes = cubes0.map(loosened), fields = fieldLaws(m)
  if (env.GDP_COUNTS_TRACE) console.error(`counts: small ${states.map(({sts}) => sts.length).join('/')}; cubes ${cubes.length} in ${Math.round(clock() - t1)} ms: ${cubes.map(l => l.name).join('; ')}`)
  // (a candidate whose every conjunct a law before it states, its keys named apart by place, is not proposed again: a
  // cell's maximum its kind's law states, a cube a guard's)
  const said = new Set<string>(), parts = (l: Law): string[] => {
    const ks = [l.forall, ...(l.keys ?? [])].filter((x): x is string => !!x), named = substC(l.holds, {vars: Object.fromEntries(ks.map((x, i) => [x, v(`$${i}`)])), maps: {}, flags: {}})
    return (named.op === 'and' ? named.xs : [named]).map(json)
  }
  for (const l of caller) for (const q of parts(l)) said.add(q)
  const prefixes = scanPrefixes(m, [...caller, ...kinds, ...guarded, ...rowLaws, ...cubes])
  const admit = (l: Law) => { const ps = parts(l); if (ps.every(q => said.has(q)) || !trueAll(l)) return false; for (const q of ps) said.add(q); return true }
  const out = ptime('filter', () => [...kinds, ...guarded, ...rowLaws, ...fields, ...prefixes, ...cubes].filter(admit))
  const carried = carryCandidates(m, [...caller, ...kinds, ...guarded, ...rowLaws, ...cubes])
  out.push(...ptime('filter', () => carried.filter(admit)))
  for (const l of out) if (prefixes.includes(l) || carried.includes(l)) support.add(l)
  if (env.GDP_COUNTS_TRACE) console.error(`counts: ${kinds.length + guarded.length + rowLaws.length + fields.length + prefixes.length + carried.length + cubes.length - out.length} candidates said before or false on the small instances`)
  return out
}

// --- the cone ----------------------------------------------------------------------------------------------------------
// The candidates kept: each proven from the kept laws and itself (IC3's relative induction: its cone), so its proof
// stands whatever else the set holds. In tiers, each to its fixpoint before the next: the law alone, once; with the kept
// laws that read one of its maps; with every kept law (twice a law at most), the nearer tier again after each kept.
// Within two thirds of what is left (the rest the caller's: Houdini, or the whole set's proof), each goal an even share
// of that over the candidates. `attempt` is the caller's proof: the counted goals, or the kernel's for plain laws.
export type Tried<P> = {proof: P} | {stuck: string}
// Recovery proposals must not consume a successful ordinary attempt's allowance.
// A deferred proposal keeps the latest warmed context, but never extends its deadline.
export function withDeferredCountRecovery<P>(until: number, attempt: (defer: (recover: () => P | undefined) => void) => Tried<P>): Tried<P> {
  let recover: (() => P | undefined) | undefined
  const ordinary = attempt(next => { recover = next })
  if ('proof' in ordinary || !recover || clock() >= until) return ordinary
  const proof = recover()
  return proof === undefined ? ordinary : {proof}
}
export function cone<P>(m: Machine, set: Law[], attempt: (law: Law, ls: Law[], ms: number) => Tried<P>, until: number, houdini = false): Map<string, P> {
  const kept = new Map<string, P>(), inCone = (l: Law) => kept.has(l.name), tried = new Map<string, number>(), times = new Map<string, number>(), asked = new Set<string>(), slow = new Set<string>()
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
        if (kept.has(law.name) || tried.get(id) === kept.size || (t === 0 && tried.has(id)) || (t === 2 && ((times.get(law.name) ?? 0) >= 2 || slow.has(law.name))) || clock() > stopAt) continue
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
        // (a law out of time over every kept law: tried again over more, its goals only grow; where Houdini follows, its
        // share is larger)
        if (houdini && t === 2 && 'stuck' in r && r.stuck !== 'sat') slow.add(law.name)
        if ('proof' in r) { kept.set(law.name, r.proof); grew = any = true; if (env.GDP_COUNTS_TRACE?.includes('3')) console.error(`counts: keep ${law.name.slice(0, 50)} tier ${t}`) }
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
// Scheduling only. Candidate membership never authorizes an assumption or a result.
export const activeSupport = (set: Law[], support: Set<Law>): boolean => set.some(l => support.has(l))
// Count-specific scheduling needs count or global-state context, not merely a
// primitive pointwise implication. Otherwise preserve the ordinary family first.
export function countSupportContext(m:Machine,caller:Law[],set:Law[],support:Set<Law>):{laws:Law[],support:Set<Law>}{
  if(!activeSupport(set,support)||set.some(l=>support.has(l)&&(reads(l.holds,map=>!!m.counts?.[map]).size||!l.forall&&some(l.holds,node=>node.op==='var'&&typeof node.name==='string'&&Object.hasOwn(m.state,node.name)&&!l.some?.includes(node.name)))))return {laws:set,support}
  return {laws:set.filter(l=>caller.includes(l)||!support.has(l)),support:new Set()}
}
export function supportOrder(set: Law[], caller: Law[], support: Set<Law>, forModels = false): Law[] {
  if (forModels && !activeSupport(set, support)) return set
  if (!activeSupport(set, support)) return [...set.filter(l => !caller.includes(l)), ...set.filter(l => caller.includes(l))]
  return [...set.filter(l => support.has(l) && !caller.includes(l)), ...set.filter(l => caller.includes(l)), ...set.filter(l => !support.has(l) && !caller.includes(l))]
}
export function supportBudget(remaining: number, share: number, priority: boolean, structural = false): number {
  return Math.max(0, Math.min(remaining, structural ? 5_000 : priority ? Math.max(share, remaining / 3) : share))
}
export type Counted = {proven: boolean, laws: Law[], m: Machine, proof?: {instances: Record<string, Instances>, certs: Record<string, CountCert>}, why?: string}
// On the counted clock (kernel/prove.ts's `counted`, the cost model's work at fullRate a millisecond), as the engine's
// search is: what a budget lets it try, and so its verdict, is the same on a slow or shared machine as on a fast one; the
// wall a stop only at twice the budget. The small instances (exists.ts's smallOf) are read before the wall starts: their
// search is bounded by its own count of steps, on neither clock, and took 3.6 to 5.2 s of an 8 s budget's 16 s wall on
// a boat VM (exists.test.ts's two counts), so a shared VM crossed the wall before the search began and left every goal
// unknown (2 runs in 4 on main; 4 in 4 beside three busy loops).
// The ordinary family gets its complete existing path first. Structured
// witness families are retried only after failure, under the same absolute
// deadline and counted fuel; no generated family is removed.
function structuredFallback(until: number, attempt: (structured: boolean) => Counted): Counted {
  const ordinary = attempt(false)
  if (ordinary.proven || clock() >= until) return ordinary
  countsDump.on?.({phase: 'structured-family-expansion'})
  return attempt(true)
}
export function searchCounted(m0: Machine, caller: Law[], ms = 60_000): Counted {
  const g = guardLaws(m0), m: Machine = {...m0, counts: {...m0.counts, ...g.counts}}
  ptime('small', () => smallOf(m))
  const run = () => withWall(performance.now() + 2 * ms, () => counted(fullRate, () => searchCounted0(m0, g, m, caller, ms), true))
  if (!env.GDP_COUNTS_PROF) return run()
  cdclStats.on = true
  const t = performance.now(), out = run()
  console.error(`counts: prof total ${Math.round(performance.now() - t)} ms; ${Object.entries(cprof).map(([k2, x]) => `${k2} ${Math.round(x)}`).join(', ')}; cdcl runs ${cdclStats.runs} conflicts ${cdclStats.conflicts} decisions ${cdclStats.decisions} solveMs ${Math.round(cdclStats.solveMs)} rowsMs ${Math.round(cdclStats.rowsMs)} coreMs ${Math.round(cdclStats.coreMs)} unfoldMs ${Math.round(cdclStats.unfoldMs)} lpMs ${Math.round(cdclStats.lpMs)} boundMs ${Math.round(cdclStats.boundMs)} orderMs ${Math.round(cdclStats.orderMs)} fmCalls ${cdclStats.fmCalls} lpMisses ${cdclStats.lpMisses} lpUnknown ${cdclStats.lpUnknown} missMs ${Math.round(cdclStats.missMs)} fastMs ${Math.round(cdclStats.fastMs)} fmOpenMs ${Math.round(cdclStats.fmOpenMs)} fmLeafMs ${Math.round(cdclStats.fmLeafMs)} nodes ${cdclStats.nodes}`)
  return out
}
function searchCounted0(m0: Machine, g: ReturnType<typeof guardLaws>, m: Machine, caller: Law[], ms: number): Counted {
  const until = clock() + ms
  if (!caller.every(l => clock() < until && trueSmall(m, [l]))) return {proven: false, laws: caller, m, why: clock() < until ? 'a law fails on the small instances' : 'time'}
  const t1 = clock()
  // (GDP_COUNTS_GIVEN=1, research's: the callers alone, no candidate: whether a set written whole goes through)
  const support = new Set<Law>()
  let set = env.GDP_COUNTS_GIVEN === '1' ? [...caller] : [...caller, ...candidates(m0, m, caller, caller, g.laws, ms, until, support)]
  countsDump.on?.({phase: 'candidates', machine: m, laws: set})
  if (env.GDP_COUNTS_TRACE) console.error(`counts: candidates at ${Math.round(clock() - t1)} ms: ${set.map(l => l.name).join('; ')}`)
  const context=countSupportContext(m,caller,set,support)
  return structuredFallback(until, structured => {
    const result=admitCountedFamilyOnce(m,caller,context.laws,context.support,until,structured)
    // Preserve full-context fallback before trying extra witness families.
    return result.proven||context.laws.length===set.length||clock()>=until?result:admitCountedFamilyOnce(m,caller,set,context.support,until,structured)
  })
}

// Candidate scheduling only. Every returned family still goes through finish.
export function admitCountedFamily(m:Machine,caller:Law[],initial:Law[],support:Set<Law>,until:number):Counted {
  return structuredFallback(until, structured => admitCountedFamilyOnce(m,caller,initial,support,until,structured))
}
function admitCountedFamilyOnce(m:Machine,caller:Law[],initial:Law[],support:Set<Law>,until:number,structured:boolean):Counted {
  const previous = proofOrigins.enabled
  if (env.GDP_COUNT_LEMMA_CUTS === '1') proofOrigins.enabled = true
  try { return admitCountedFamily0(m, caller, initial, support, until, structured) }
  finally { proofOrigins.enabled = previous }
}
function admitCountedFamily0(m:Machine,caller:Law[],initial:Law[],support:Set<Law>,until:number,structured:boolean):Counted {
  if(!caller.every(l=>initial.includes(l)))return {proven:false,laws:initial,m,why:'missing caller'}
  let set=initial.slice()
  const attempts = countedAttempts(m, caller, support, until, structured), traced = attempts.traced
  const isCount = (mp: string) => !!m.counts?.[mp]
  // Prove the proposed set together. A preliminary cone reproved many helpers in
  // several smaller contexts before asking these same induction goals. Houdini
  // drops failed helpers and carries proofs whose instantiated support survives.
  // Every returned set still passes checkCountedLaws, including all caller laws.
  const finish = (ls: Law[], proof: {instances: Record<string, Instances>, certs: Record<string, CountCert>}): Counted => {
    let proposed = proof
    if (env.GDP_COUNT_LEMMA_CUTS === '1') {
      // This pass performs no search work. Reuse the enclosing wall deadline; outside one,
      // conservatively cap its wall time by the remaining counted allowance. Neither budget is extended.
      const wall = wallAt(), end = Number.isFinite(wall) ? wall : performance.now() + Math.max(0, until - clock())
      for (const {goal, decls} of countedObligations(m, ls, proof.instances)) {
        if (performance.now() >= end) break
        const cert = proof.certs[goal.name]
        if (!cert || cert.lemmas?.length) continue
        const expanded = mcGoal(goal.hyps, decls, cert)
        const shared = expanded && proposeLemmaCuts(expanded, cert.tree, {until: end})
        if (shared) proposed = {...proposed, certs: {...proposed.certs, [goal.name]: {...cert, tree: shared.tree, lemmas: shared.lemmas}}}
      }
    }
    if (proposed !== proof && ptime('kernel', () => checkCountedLaws(m, ls, proposed))) proof = proposed
    else if (!ptime('kernel', () => checkCountedLaws(m, ls, proof))) return {proven: false, laws: ls, m, why: 'the kernel refused the set'}
    // Output-only observation, after the unchanged checker accepts every obligation.
    countsDump.on?.({phase: 'closed-family', machine: m, laws: ls, proof, checked: true})
    return {proven: true, laws: ls, m, proof}
  }
  const join = (kept = new Map<string, Proof>()): Counted => {
    const keptProof = () => ({instances: Object.fromEntries([...kept].map(([n, pr]) => [n, pr.instances])), certs: Object.assign({}, ...[...kept.values()].map(pr => pr.certs))})
    if (caller.every(l => kept.has(l.name))) return finish(set.filter(l => kept.has(l.name)), keptProof())
    // (each law without a carried proof an even share of what is left a round)
    let carried = new Map<string, Proof>()
    attempts.houdini = true
    for (let round = 0; clock() < until; round++) {
      const {instances, certs} = keptProof()
      const failed = new Set<string>(), proofs = new Map<string, Proof>(), share = (until - clock()) / Math.max(1, set.filter(l => !kept.has(l.name) && !carried.has(l.name)).length)
      // Structural supports first; no-support scheduling is unchanged.
      for (const law of supportOrder(set, caller, support)) {
        if (clock() > until) return {proven: false, laws: set, m, why: 'time'}
        if (kept.has(law.name)) continue
        const was = carried.get(law.name)
        const structural = support.has(law) && !caller.includes(law)
        const boundedSupport = activeSupport(set, support)
        const allotted = supportBudget(until - clock(), share, boundedSupport && caller.includes(law), structural)
        const supportUntil = Math.min(until, clock() + (boundedSupport ? Math.min(allotted, 5_000) : allotted)), supportWall = performance.now() + 4_800
        const ask = (pass: 0 | 1): Tried<Proof> => {
          const ms = Math.min(allotted, Math.max(0, (boundedSupport ? supportUntil : until) - clock()))
          return boundedSupport ? withWall(supportWall, () => withDeadline(supportUntil, () => traced(law, set, pass, ms))) : traced(law, set, pass, ms)
        }
        const countFirst = (env.GDP_COUNTS_COUNT_FIRST === '1' || boundedSupport && env.GDP_COUNTS_COUNT_FIRST !== '0') && (reads(law.holds, isCount).size > 0 || boundedSupport && !!law.keys?.length)
        let r: Tried<Proof> = was ? {proof: was} : ask(countFirst ? 1 : 0)
        if (!('proof' in r) && (countFirst || attempts.counted)) r = ask(countFirst ? 0 : 1)
        if (!('proof' in r)) { failed.add(law.name); continue }
        proofs.set(law.name, r.proof)
        instances[law.name] = r.proof.instances
        Object.assign(certs, r.proof.certs)
      }
      if (env.GDP_COUNTS_TRACE) console.error(`counts: round ${round}: ${set.length} laws, ${kept.size} kept, ${carried.size} carried, failed ${[...failed].join('; ').slice(0, 600)}`)
      if (!failed.size) return finish(set, {instances, certs})
      const next = set.filter(l => !failed.has(l.name) || caller.includes(l))
      // (only callers fail: drop nothing more, give up)
      if (next.length === set.length) return {proven: false, laws: set, m, why: `not proven: ${[...failed].join(', ')}`}
      // (a proof that assumes no law dropped at any key is one over the rest: its goals are the same; the kernel checks all)
      const dropped = set.filter(l => !next.includes(l))
      carried = new Map([...proofs].filter(([, pr]) => dropped.every(d => d.forall && !pr.instances[d.name]?.length)))
      set = next
    }
    return {proven: false, laws: set, m, why: 'time'}
  }
  const dependencies=(owner:Law,proof:Proof,context:Law[]):Set<string>=>{
    const conservative=()=>new Set(context.filter(l=>!l.forall||proof.instances[l.name]?.length).map(l=>l.name)),used=new Set<string>()
    for(const {goal,decls}of countedObligations(m,context,{[owner.name]:proof.instances},context.indexOf(owner))){
      const cert=proof.certs[goal.name]
      if(!cert)return conservative()
      const expanded=mcGoal(goal.hyps,decls,cert),refs=expanded&&usedHyps(expanded,cert.tree)
      if(!refs)return conservative()
      for(const index of refs)if(index<goal.hyps.length)used.add(json(goal.hyps[index]))
    }
    return new Set(context.filter(l=>assumed([l],proof.instances).some(h=>used.has(json(h)))).map(l=>l.name))
  }
  const demand=():Counted=>{
    const known=new Map<string,{proof:Proof,context:Law[],deps:Set<string>}>()
    attempts.houdini=true
    while(clock()<until){
      if(!activeSupport(set,support))return join()
      const required=new Set(caller.map(l=>l.name)),available=new Set(set.map(l=>l.name))
      for(const name of required){const saved=known.get(name);if(saved)for(const dep of saved.deps)if(available.has(dep))required.add(dep)}
      const law=supportOrder(set,caller,support).find(l=>required.has(l.name)&&!known.has(l.name))
      if(!law){
        const kept=set.filter(l=>required.has(l.name)),instances:Record<string,Instances>={},certs:Record<string,CountCert>={}
        for(const l of kept){
          const saved=known.get(l.name)!
          instances[l.name]=saved.proof.instances
          const src=countedObligations(m,saved.context,{[l.name]:saved.proof.instances},saved.context.indexOf(l)),dst=countedObligations(m,kept,{[l.name]:saved.proof.instances},kept.indexOf(l))
          for(let i=0;i<dst.length;i++){
            const cert=saved.proof.certs[src[i]!.goal.name]
            if(!cert)return join()
            const a=mcGoal(src[i]!.goal.hyps,src[i]!.decls,cert),b=mcGoal(dst[i]!.goal.hyps,dst[i]!.decls,cert),tree=a&&b&&widen(a,b,cert.tree)
            if(!tree)return join()
            certs[dst[i]!.goal.name]={...cert,tree}
          }
        }
        return finish(kept,{instances,certs})
      }
      const remaining=until-clock(),share=remaining/Math.max(1,set.length-known.size),allotted=supportBudget(remaining,share,caller.includes(law),support.has(law)&&!caller.includes(law)),stop=Math.min(until,clock()+Math.min(allotted,5000)),wall=performance.now()+4800
      const countFirst=env.GDP_COUNTS_COUNT_FIRST!=='0'&&(reads(law.holds,isCount).size>0||!!law.keys?.length)
      const ask=(context:Law[]):Tried<Proof>=>withWall(wall,()=>withDeadline(stop,()=>{
        const pass:0|1=countFirst?1:0
        let result=traced(law,context,pass,Math.min(allotted,Math.max(0,stop-clock())))
        if(!('proof'in result)&&(countFirst||attempts.counted)&&clock()<stop)result=traced(law,context,pass?0:1,Math.min(allotted,Math.max(0,stop-clock())))
        return result
      }))
      let context=coarseContext(m,set,[...caller,law],support),result=ask(context)
      if(!('proof'in result)&&context.length<set.length&&clock()<stop){context=set;result=ask(context)}
      countsDump.on?.({phase:'demand-attempt',law:law.name,context:context.length,required:required.size,known:known.size,outcome:'proof'in result?'proof':result.stuck})
      if('proof'in result){known.set(law.name,{proof:result.proof,context:context.slice(),deps:dependencies(law,result.proof,context)});continue}
      if(caller.includes(law))return join()
      set=set.filter(l=>l!==law)
      for(const [name,saved]of known)if(saved.deps.has(law.name))known.delete(name)
    }
    return {proven:false,laws:set,m,why:'time'}
  }
  return activeSupport(set,support)?demand():join()
}

type Proof = {instances: Instances, certs: Record<string, CountCert>}
// The production attempt also serves the fixed-family research replay. Candidate
// generation and scheduling stay outside; inference, selection, reservation and
// all budget checks have exactly one implementation.
export function countedAttempts(m: Machine, caller: Law[], support: Set<Law>, until: number, structured = true) {
  // (the law's own names and the request's values that key a map: an action's value keys none)
  const keys0 = [...[...reads([m.step, m.assume ?? null], () => true).values()].map(([, key]) => key), ...Object.values(m.step.maps ?? {}).flatMap(w => ('each' in w ? [] : [w.key]))]
  const keyed = m.inputs.filter(i => keys0.some(key => mentions(key, i))).map(v)
  const terms = (l: Law): E[] => [...(l.forall ? [v(`${l.forall}#`)] : []), ...(l.keys ?? []).map(v), ...keyed]
  type Proof = {instances: Instances, certs: Record<string, CountCert>}
  const widened = new Set<string>()
  let counted = true, houdini = false // (houdini: the rounds over the whole set; only they widen)
  const none: ReturnType<typeof certFor> = {reads: [], insts: [], wits: [], picks: [], loose: false}
  // One law's goals and their certificates, the laws `ls` assumed (a subsequence of the set): pass 0 with no instances of
  // the lemma, pass 1 with the cells' (one set of witnesses a law); a tree each within `ms`. The instances: the
  // quantified flags at the law's own terms, then what the goals' models ask.
  // A law's last model (a counterexample to its induction, CTI) is kept: tried again over more laws (the cone's next
  // tier, Houdini's round), the model is first read against them as the attempt reads a model (modelInstances: a law
  // broken at a tuple of the goal's keys); none broken, it is still a model, and the law is refuted again without a
  // solve. (Not where a law added reads a count: its goal's count instances aren't read here.)
  const models = new Map<string, {gg: Goal, w: Record<string, number>, at: Instances, ls: Set<string>}>(), isCount = (mp: string) => !!m.counts?.[mp]
  // Cone tiers and Houdini may ask the same law again with more instances. Keep a
  // bounded set of sessions; each independently resets unless its hypotheses are
  // still present verbatim. This reuses work, never a verdict from a weaker goal.
  const decisions = new Map<string, ReturnType<typeof modelSequence>>(), focusEnabled=focusedCountRecoveryEnabled(m)
  const ordinaryAttempt = (law: Law, ls: Law[], pass: 0 | 1, ms: number, attemptEnd: number, defer: (recover: () => Proof | undefined) => void): Tried<Proof> => {
    // A cached model can return before the no-count optimization below. A helper
    // without count reads must not suppress the next law's counting-lemma pass.
    if (!pass) counted = true
    const ts = terms(law), id = `${pass} ${law.name}`, cti = models.get(id)
    const supported = ls.some(l => support.has(l)), modelLaws = supportOrder(ls, caller, support, true)
    // Finite-input recovery remains on by default, but ordinary search goes first.
    // A failed attempt may use the remainder of its original share, never a new one.
    if (!pass && focusEnabled && m.inputMaps?.length && !reads(law.holds, isCount).size) {
      defer(() => ptime('focused', () => proveFocusedCounts(m, ls, law, {}, Math.min(attemptEnd, clock() + Math.min(ms, 5000)), (g, ds) => certFor(g, ds, true, pool, undefined, structured))))
    }
    // (the model broken: the attempt starts at the instances it asks for, its last attempt's and the tuples the new laws
    // break it at, where the rounds of models would lead it again)
    let seed: Instances | undefined
    // (not where the attempt may widen: its narrow model is no model of the widened goal)
    if (cti && !(supported && pass) && !(houdini && caller.some(l => l.name === law.name) && !widened.has(law.name)) && !ls.some(l => !cti.ls.has(l.name) && reads(l.holds, isCount).size)) {
      const at0 = Object.fromEntries(Object.entries(cti.at).filter(([n]) => n.startsWith('?') || ls.some(l => l.name === n)))
      if (!(seed = ptime('mbqi', () => modelInstances(m, modelLaws, at0, cti.gg, cti.w)))) return {stuck: 'sat'}
    }
    const refuted = (gg: Goal, w: Record<string, number>): Tried<Proof> => { models.set(id, {gg, w, at, ls: new Set(ls.map(l => l.name))}); return {stuck: 'sat'} }
    // Supported obligations seed quantified flags only at demanded source terms.
    // Ordinary MBQI remains the fallback; arbitrary inputs are not initial witnesses.
    let at: Instances = seed ?? (supported ? {} : Object.fromEntries(Object.entries(m.step.flags ?? {}).flatMap(([f, q]) => (q.op === 'all' && !q.keys?.length ? [[`?${f}`, ts]] : []))))
    const obligations = (i: Instances) => ptime('encode', () => countedObligations(m, ls, {[law.name]: i}, ls.indexOf(law)))
    // (`wide`: the count instances widened once, where a model is left that the narrow ones and the laws don't refute, for
    // a caller's law or where a read is in none of them: the cone's many refuted candidates keep the narrow ones)
    // Source-only proposals share one 64-tuple/4-per-source budget for this attempt.
    // The ordinary MBQI path remains available and is unchanged without support.
    const generation = candidateWork()
    let seedCount = 0
    let sourceMaps: ReadonlySet<string> = new Set()
    if (supported) {
      const prepared = prepareSupport(m, ls, law, at, pass, generation)
      at = prepared.at; seedCount = prepared.seedCount; sourceMaps = prepared.sourceMaps
    }
    let wide = false
    const isCaller = houdini && caller.some(l => l.name === law.name)
    // (lazy (CEGAR): the goal carries the counting lemma's instances and picks some model of it broke, of all certFor
    // proposes: each model read against the rest, as a state, and those it breaks added, until a model breaks none; an
    // instance by the reads it names, a pick by its read and terms, so the choice outlives the goal's rebuilds)
    const chosen = new Set<string>()
    type Pool = {fg: Goal, keys: string[], wits: (string | undefined)[], chosen?: Set<string>, cap?: number}
    type Selection = {chosen: Set<string>, cap: number, previous: Pick<CountCert, 'reads' | 'insts' | 'picks'>, decls: Parameters<typeof certFor>[1], reserve: ReturnType<typeof reservationState>, stable: ReturnType<typeof stableState>}
    const selections = new Map<string, Selection>()
    const poolCache = new Map<string, {key: string, value: ReturnType<typeof grammarPool>}>()
    const rawBuild = () => obligations(at).map(({goal, decls}) => {
      if (pass && supported && lazyMode === 'wide') {
        if (generation.state.deadline || performance.now() >= wallAt()) throw new UnsupportedCountProposal('reservation deadline')
        let selection = selections.get(goal.name)
        const reservation = selection && reservationReadClosure(goal, decls, selection.previous, selection.decls, selection.chosen, [...m.params, ...m.inputs, ...Object.keys(m.state)])
        // Primitive PRE instances cannot introduce another count read. Reuse
        // the proposal pool while only those instances grow; retained picks
        // are still reified against this goal, and additional picks may wait
        // for failure-driven widening. This caches proposals, never a proof.
        const key = countPoolKey(goal, decls)
        const cached = poolCache.get(goal.name)
        const pool0 = cached?.key === key ? cached.value : grammarPool(goal, decls, pool, generation, structured)
        if (cached?.key !== key) poolCache.set(goal.name, {key, value: pool0})
        if (!selection) {
          const pick = readTuples(goal.hyps.at(-1), generation.tick).some(([mp]) => mp.endsWith('#') && decls.some(d => d.map === mp))
            ? polaritySelection(goal, decls, pool0, generation, sourceMaps).pick
            : smallSelection(goal, decls, pool0.full, readTuples(law.holds, generation.tick).map(([, key]) => key), none, generation)
          selection = {chosen: new Set(ids(pick)), cap: Math.min(10, pick.insts.length + 2), previous: pick, decls, reserve: reservationState(goal, [m, ls, goal], pool), stable: stableState([m, ls, goal])}
          selections.set(goal.name, selection)
        }
        const full = reservePool(goal, decls, pool0, selection.previous, selection.decls, selection.chosen, selection.reserve, pool, reservation).full
        const keys = ids(full), lazyRoom = selection.chosen.size < selection.cap
        const view = chosenView(full, selection.chosen, selection.cap)
        const c = selectedCertificate(goal, decls, view, selection.stable, lazyRoom)
        const gg = mcGoal(goal.hyps, decls, c), fg = lazyRoom ? mcGoal(goal.hyps, decls, full) : undefined
        selection.previous = full; selection.decls = decls
        return {goal, decls, c, gg, pool: fg ? {fg, keys, wits: [...full.picks.map(() => undefined), ...full.insts.map(i => i.wit)], chosen: selection.chosen, cap: selection.cap} as Pool : undefined}
      }
      const full = pass ? certFor(goal, decls, wide, wide && lazyMode !== '0' ? pool : undefined, undefined, structured) : none
      if (!pass || lazyMode === '0' || (lazyMode === 'wide' && !wide)) return {goal, decls, c: full, gg: ptime('encode', () => mcGoal(goal.hyps, decls, full)), pool: undefined as Pool | undefined}
      const rd = new Map(full.reads.map(r => [r[0], json([r[1], r[2]])]))
      const keys = [...full.picks.map(q => `p${json([rd.get(q[0]), q[1]])}`), ...full.insts.map(i => `i${json([i.terms.map(([z, x]) => [z, rd.get(x)]), i.unit, i.below])}`)]
      if (lazyMode === 'wide') for (const q of keys.slice(full.picks.length, full.picks.length + 10)) chosen.add(q)
      const c = {...full, picks: full.picks.filter((_, j) => chosen.has(keys[j]!)), insts: full.insts.filter((_, j) => chosen.has(keys[j + full.picks.length]!))}
      const fg = ptime('encode', () => mcGoal(goal.hyps, decls, full))
      return {goal, decls, c, gg: ptime('encode', () => mcGoal(goal.hyps, decls, c)), pool: fg && keys.length ? {fg, keys, wits: [...full.picks.map(() => undefined), ...full.insts.map(i => i.wit)]} : undefined}
    })
    let lastSignature = ''
    const build = () => {
      let built = rawBuild()
      if (pass && supported) while (seedCount < 64 && clock() < until) {
        const step = built.at(-1)
        if (!step?.gg) break
        const signature = refinementSignature(step.gg, step.c)
        if (signature === lastSignature) break
        lastSignature = signature
        const seeds = sparseReadInstances(m, ls.filter(l => l === law || !reads(l.holds, isCount).size), law, at, step.gg, step.c, 64 - seedCount, step.goal.hyps.at(-1), step.decls, sourceMaps, step.goal.hyps.slice(0, -1), generation)
        if (!seeds.added.length) break
        const previous = countSignature(step.c)
        at = seeds.at; seedCount += seeds.added.length
        built = rawBuild()
        if (countSignature(built.at(-1)!.c) !== previous && !seeds.summary.foundationBarrier) break
      }
      return built
    }
    // (the pool's hypotheses a model breaks, chosen; whether there were any)
    // (`strict`, where nothing else is broken or asked: the cells it leaves out at their start alone, as a model whose
    // completion meets an instance may still meet it only at a witness some law then breaks)
    const breaks = (b: ReturnType<typeof build>[number] | undefined, w: Record<string, number>, strict = false): boolean => ptime('lazy', () => {
      if (!b?.pool) return false
      // (broken where no completion of the model meets it: the cells it leaves out at their start, at 1, or one map's
      // flipped from either, and an instance's witness at each value below 16)
      const {fg, keys, wits} = b.pool, active = b.pool.chosen ?? chosen, base = fg.hyps.length - keys.length, ids = keys.flatMap((q, j) => (active.has(q) ? [] : [base + j])), judge = brokenOf(fg)
      let bad = ids.length ? judge(w, ids) : []
      const mps = [...new Set(bad.flatMap(i => [...reads(fg.hyps[i], () => true).values()].map(([mp]) => mp)))], one1 = Object.fromEntries(mps.map(mp => [mp, 1]))
      for (const d of strict ? [undefined] : [undefined, one1, ...mps.map(mp => ({[mp]: 1})), ...mps.map(mp => ({...one1, [mp]: 0}))]) for (let x = 0; x < 16 && bad.length; x++) {
        if (x && !bad.some(i => wits[i - base])) break
        const w2 = {...w}
        for (const i of bad) if (wits[i - base]) w2[wits[i - base]!] = x
        const still = new Set(judge(w2, bad, false, d))
        bad = bad.filter(i => still.has(i))
      }
      if (b.pool.cap !== undefined) { const seen = new Set<string>(); bad = bad.filter(i=>{const key=keys[i-base]!;if(seen.has(key))return false;seen.add(key);return true}).slice(0, Math.max(0, b.pool.cap - active.size)) }
      for (const i of bad) active.add(keys[i - base]!)
      tally('#lazy', bad.length)
      return bad.length > 0
    })
    let built = build()
    const observe = (b: ReturnType<typeof build>[number], phase: string, witness?: Record<string, number>) => {
      if (countsDump.on) countsDump.on({law: law.name, goal: b.goal.name, pass, phase, generation: {...generation.state}, machine: m, laws: ls, rawGoal: b.goal, decls: b.decls, instances: at, certificateRequest: b.c, hyps: b.gg?.hyps, witness, seedCount})
    }
    let decideStep = decisions.get(id)
    if (!decideStep) {
      if (decisions.size >= 64) decisions.delete(decisions.keys().next().value!)
      decisions.set(id, (decideStep = modelSequence()))
    }
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
    let preflighted = false
    for (;;) {
      let part: {gg: Goal, core: Goal} | undefined
      let direct: {gg: Goal, tree: CountCert['tree']} | undefined
      for (;;) {
        const step = built.at(-1)
        if (!step?.gg) break
        if (supported && !preflighted && !step.c.insts.length) {
          preflighted = true
          const directSmall = step.gg.hyps.length<=64, small = directSmall?step.gg:relevantGoals(step.gg)[0]??step.gg, end = Math.min(attemptEnd, clock() + (directSmall?ms:ms/6))
          // Small already-reified goals use direct tree search before model
          // construction; neither branch may outlive the original attempt. A subset model
          // says nothing about the whole goal; only a widened tree is reusable.
          const tree = ptime('preflight', () => withDeadline(end, () => {
            const quick = grow(small, new Map(), {nodes: 0, until: end})
            return 'tree' in quick ? widen(small, step.gg!, quick.tree) : undefined
          }))
          observe(step, tree ? 'preflight-proven' : 'preflight-miss')
          if (tree) { direct = {gg: step.gg, tree}; break }
        }
        observe(step, 'query')
        const q0 = clock(), q = ptime('decide', () => decideStep(step.gg!, Math.min(until, clock() + Math.min(2 * ms, 5_000))))
        observe(step, 'decision:' + ('tree' in q ? 'tree' : q.why === REFUTED ? 'refuted' : q.stuck))
        if (env.GDP_COUNTS_TRACE?.includes('2')) console.error(`counts: decide ${pass} ${step.goal.name}: ${'tree' in q ? 'proven' : q.stuck} ${step.gg.hyps.length} hyps ${Math.round(clock() - q0)} ms`)
        if ('tree' in q) { direct = {gg: step.gg, tree: q.tree}; break }
        if (q.why === REFUTED && q.core) {
          const gg = step.gg, last = gg.hyps.length - 1, used = new Set(q.core.map(h => json(gg.hyps[h]))), cut: Instances = {}
          for (const [name, ts2] of Object.entries(at)) {
            const l = ls.find(x => x.name === name), n = l ? 1 + (l.keys?.length ?? 0) : 0
            cut[name] = !l ? ts2 : Array.from({length: ts2.length / n}, (_, t) => ts2.slice(t * n, t * n + n)).filter(t => used.has(json(assumed([l], {[name]: t})[0]))).flat()
          }
          at = cut
          built = obligations(at).map(({goal, decls}, j) => ({goal, decls, c: built[j]!.c, gg: mcGoal(goal.hyps, decls, built[j]!.c), pool: built[j]!.pool}))
          part = {gg: built.at(-1)!.gg!, core: {name: gg.name, hyps: (q.core.includes(last) ? q.core : [...q.core, last]).map(h => gg.hyps[h]!)}}
          break
        }
        if (q.stuck !== 'sat' || !q.witness) break
        observe(step, 'model', q.witness)
        if (!more()) return {stuck: 'unknown'}
        const asked = ptime('mbqi', () => modelInstances(m, modelLaws, at, step.gg!, q.witness!)), lz = breaks(step, q.witness) || (!asked && breaks(step, q.witness, true))
        tally('#rounds'); tally('#hyps', step.gg.hyps.length)
        if (lz && !asked) { built = build(); continue }
        if (!asked) {
          if (countsDump.on && pass && dumped < Number(env.GDP_COUNTS_DUMP_N ?? 3)) { dumped++; countsDump.on({law: law.name, goal: step.goal.name, ls: ls.map(l => l.name), stuck: 'sat', witness: q.witness, reads: step.c.reads, insts: step.c.insts, hyps: step.gg.hyps, base: step.goal, decls: step.decls, cert: step.c, at, laws: ls, wide, pass}) }
          if (pass && !wide && houdini && 'loose' in step.c && (step.c.loose || isCaller) && more()) { wide = true; widened.add(law.name); built = build(); continue }
          return refuted(step.gg, q.witness)
        }
        at = asked
        built = build()
      }
      // A wide pool can obscure a short subset proof. Retry only ordinary
      // witness-bearing certificates with the warmed law instances; the final
      // checkCountedLaws gate is unchanged; the same bounded finite-input default applies.
      if (pass && wide && focusEnabled && clock() < attemptEnd) {
        defer(() => ptime('focused', () => proveFocusedCounts(m, ls, law, at, Math.min(attemptEnd, clock() + Math.min(ms, 5000)), (g, ds) => certFor(g, ds, true, pool, undefined, structured))))
      }
      // (whether a goal reads a count: if none does, pass 1's goals are pass 0's)
      if (!pass) counted = built.some(b => certFor(b.goal, b.decls).reads.length)
      const certs: Record<string, CountCert> = {}
      let again = false
      for (const {goal, decls, c, gg} of built) {
        const t0 = clock(), viaPart = gg && part?.gg === gg ? ptime('part', () => {
          const o1 = grow(part!.core, new Map(), {nodes: 0, until: Math.min(until, clock() + Math.max(ms, 2_000))}), w = 'tree' in o1 ? widen(part!.core, gg, o1.tree) : undefined
          return w ? {tree: w, nodes: 0} : undefined
        }) : undefined
        const o = (direct && direct.gg === gg ? {tree: direct.tree, nodes: 0} : undefined) ?? viaPart ?? (gg && ptime(`grow${(gg.hyps.length > 300 ? '>300' : '')}`, () => grow(gg, new Map(), {nodes: 0, until: Math.min(until, clock() + ms)})))
        if (gg && o && !('tree' in o)) observe(built.find(b => b.gg === gg)!, o.stuck, 'witness' in o ? o.witness : undefined)
        if (countsDump.on && gg && o && !('tree' in o) && gg.hyps.length > Number(env.GDP_COUNTS_DUMP_MIN ?? 300) && dumped < Number(env.GDP_COUNTS_DUMP_N ?? 3)) { dumped++; countsDump.on({law: law.name, goal: goal.name, ls: ls.map(l => l.name), stuck: (o as {stuck?: string}).stuck, hyps: gg.hyps, base: goal, decls, cert: c, at, laws: ls, wide, pass, ...('witness' in o ? {witness: o.witness} : {})}) }
        if (env.GDP_COUNTS_TRACE?.includes('2')) console.error(`counts: ${ls.length === 1 ? 'alone' : `with ${ls.length}`} ${pass} ${goal.name}: ${o && 'tree' in o ? 'proven' : gg ? (o as {stuck?: string}).stuck : 'no read'} ${gg?.hyps.length ?? 0} hyps (insts ${'insts' in c ? c.insts.length : 0} picks ${'picks' in c ? c.picks.length : 0}${wide ? ' wide' : ''}${built.find(b => b.gg === gg)?.pool ? ` of ${built.find(b => b.gg === gg)!.pool!.keys.length}` : ''}) ${Math.round(clock() - t0)} ms`)
        // (the tree search's model of the step goal: the instances it asks for, as the CDCL search's, and the goals again)
        if (gg && o && !('tree' in o) && o.stuck === 'sat' && o.witness && gg === built.at(-1)!.gg && more()) {
          const asked = ptime('mbqi', () => modelInstances(m, modelLaws, at, gg, o.witness!)), lz = breaks(built.at(-1), o.witness) || (!asked && breaks(built.at(-1), o.witness, true))
          if (asked || lz) { if (asked) at = asked; built = build(); again = true; break }
        }
        if (gg && o && !('tree' in o) && o.stuck === 'sat' && o.witness && gg === built.at(-1)!.gg && pass && !wide && houdini && 'loose' in c && (c.loose || isCaller) && more()) { wide = true; widened.add(law.name); built = build(); again = true; break }
        if (gg && o && !('tree' in o) && o.stuck === 'sat' && o.witness && gg === built.at(-1)!.gg) return refuted(gg, o.witness)
        if (!o || !('tree' in o)) return {stuck: gg ? (o as {stuck?: string}).stuck ?? '' : ''}
        certs[goal.name] = {reads: c.reads, insts: c.insts, tree: o.tree, ...('picks' in c && c.picks.length ? {picks: c.picks} : {})}
      }
      if (!again) return {proof: {instances: at, certs}}
    }
  }
  const attempt = (law: Law, ls: Law[], pass: 0 | 1, ms: number): Tried<Proof> => {
    const end = Math.min(until, clock() + ms)
    return withDeferredCountRecovery(end, defer => ordinaryAttempt(law, ls, pass, ms, end, defer))
  }
  const traced = (law: Law, ls: Law[], pass: 0 | 1, ms: number): Tried<Proof> => {
    const t0 = clock(), w0 = performance.now(), p0 = {...cprof}
    let r: Tried<Proof>
    try {
      const end = Math.min(until, clock() + ms)
      // Probe only strict subsets, within the existing attempt's allowance. A
      // subset model is not a verdict: failure always widens to the full set.
      // Kept certificates must be lifted to that full set's exact row layout.
      const focused = pass && ls.some(l=>support.has(l)) && (reads(law.holds,isCount).size || !caller.includes(law) && !!law.keys?.length) ? sourceContext(m,ls,law,support) : ls
      const contexts = [...(focused.length<ls.length ? [{local:focused,fraction:1,kind:'source-context'}] : []), ...(env.GDP_COUNTS_RELEVANCE==='1'?relevantLaws(m,ls,law,support).map(local=>({local,fraction:1/6,kind:'relevance'})):[])]
      for (const {local,fraction,kind} of contexts) {
        const slice = Math.max(0, Math.min(ms * fraction, end - clock()))
        if (!slice) break
        let probe: Tried<Proof>
        try { probe = withDeadline(clock() + slice, () => attempt(law, local, pass, slice)) } catch (error) {
          if (!(error instanceof UnsupportedCountProposal)) throw error
          continue
        }
        if (!('proof' in probe)) continue
        const localGoals = countedObligations(m, local, {[law.name]: probe.proof.instances}, local.indexOf(law))
        const wholeGoals = countedObligations(m, ls, {[law.name]: probe.proof.instances}, ls.indexOf(law))
        const certs: Record<string, CountCert> = {}
        let complete = true
        for (let i = 0; i < wholeGoals.length; i++) {
          const part = localGoals[i]!, whole = wholeGoals[i]!, c = probe.proof.certs[part.goal.name]
          if (!c) { complete = false; break }
          const pg = mcGoal(part.goal.hyps, part.decls, c), wg = mcGoal(whole.goal.hyps, whole.decls, c)
          const tree = pg && wg && withDeadline(end, () => widen(pg, wg, c.tree))
          if (!tree) { complete = false; break }
          const lifted = {...c, tree}
          if(!checkMC(whole.goal.hyps,whole.decls,lifted)){complete=false;break}
          certs[whole.goal.name] = lifted
        }
        if (complete) {
          r = {proof: {instances: probe.proof.instances, certs}}
          countsDump.on?.({phase: kind+'-proof', law: law.name, local: local.length, whole: ls.length})
          return r
        }
      }
      r = attempt(law, ls, pass, Math.max(0, end - clock()))
    } catch (error) {
      // Invalid or captured proposals are rejected; they cannot become assumptions.
      if (!(error instanceof UnsupportedCountProposal)) throw error
      countsDump.on?.({law: law.name, pass, phase: 'rejected proposal', error: String(error)})
      r = {stuck: 'unknown'}
    }
    if (env.GDP_COUNTS_TRACE?.includes('3')) console.error(`counts: try ${law.name.slice(0, 50)} | ls ${ls.length} pass ${pass} ms ${Math.round(ms)} took ${Math.round(clock() - t0)} wall ${Math.round(performance.now() - w0)} [${Object.entries(cprof).filter(([k2, x]) => x - (p0[k2] ?? 0) >= 1).map(([k2, x]) => `${k2} ${Math.round(x - (p0[k2] ?? 0))}`).join(' ')}] -> ${'proof' in r ? 'kept' : r.stuck}`)
    return r
  }
  return {traced, get counted() { return counted }, set houdini(value: boolean) { houdini = value }}
}
