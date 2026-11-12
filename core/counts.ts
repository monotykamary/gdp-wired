import {searchNow as countedSearchNow, traceNow as countedTraceNow} from './wall.ts'
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
import {isLocalCountExpiration} from './count-tier-budget.ts'
import {withEvaluationAdmission} from './work-observe.ts'
import {finalCountStepDeferralEnabled, closingCountCheck} from './count-final-step.ts'
import {type CountCert, type CountDecl, type CountInst, type Goal, type Instances, type MapRead, assumed, checkCountedLaws, checkMC, countedObligations, mcGoal, scope, substC, substE} from '../kernel/kernel.ts'
import {BudgetExpired,brokenOf,clock,counted,fullRate,fullWork,grow,modelInstances,wallAt,widen,withDeadline,withinDeadline,withWall} from '../kernel/prove.ts'
import {REFUTED, cdclStats} from '../kernel/cdcl.ts'
import {modelSequence} from '../kernel/model-sequence.ts'
import {inferLaws} from './infer.ts'
import {carryCandidates, scanPrefixes} from './carry.ts'
import {relevantGoals, relevantLaws} from './relevance.ts'
import {countPoolKey, countSignature, grammarPool, ids, polaritySelection, readTuples, refinementSignature, reservationReadClosure, reservationState, reservePool, prepareSupport, smallSelection, sparseReadInstances, sourceContext, coarseContext, selectedCertificate, chosenView, candidateWork, stableState, UnsupportedCountProposal} from './count-support.ts'
import {fieldLaws, selectFieldLaws} from './field-laws.ts'
import {quorumLaws} from './quorum-laws.ts'
import {countCubes, liftedOneKeyCounts} from './count-cubes.ts'
import {finiteHoudini} from './finite-houdini.ts'
import {finiteModelChecker} from './finite-model.ts'
import {countsForReads, proposeCountFacts} from './count-facts.ts'
import {completeCountLawInstances} from './count-completion.ts'
import {rangeInstances, rangeViolations} from './count-ranges.ts'
import {attemptShare, supportBudget} from './support-budget.ts'
export {attemptShare, supportBudget} from './support-budget.ts'
import {proposeCountUnions} from './count-unions.ts'
import {focusedCountRecoveryEnabled,proveFocusedCounts} from './count-focus-proof.ts'
import {preferMemberInclusions} from './count-recovery/member-inclusions.ts'
import {fixedCountFrameCase,ownCountLawInstance,proveCountFrameGoal} from './count-frames.ts'
import {independentCountInstances} from './count-focused.ts'
import {admitMemberWitnesses,instantiateMemberPremises,memberHints,memberPremiseState,type MemberHint} from './count-recovery/member-premises.ts'

import {smallOf, trueSmall} from './exists.ts'
import {WallExpired, checkWall, searchWall, withBudget} from './wall.ts'
import {env} from './solver.ts'
import {proofOrigins, proposeLemmaCuts} from './lemma-cuts.ts'
import {countedCertificateHyps,transportCountCertificate} from './count-cert-transport.ts'
import {type CountFamilyProof, type CountLawProof, type ScopedCountProof, scopeCountProof, replayScopedCountProof, isCheckedReducedScope, withCountScopeIdentityObservation, countScopeContextKey, resolveCountScopeSuppliers} from './count-proof-scope.ts'
import {assertLiftedWorkLease, prepareCountStrategyMachine, proveCountStrategies, proposeCountStrategiesForClosing, proveCountStrategyKind, proposeCountStrategyKindForClosing, selectedCountStrategies} from './count-strategies.ts'
import {type LiftedWorkBudget} from './count-lifted-budget.ts'
import {countRecipeContextDecision} from './count-recipe-context.ts'
import {CountRecipePass,runCountRecipeController,type CountControllerMember} from './count-recipe-controller.ts'
import {discoverLiftedCountGuard,discoverLiftedCountOperations} from './count-lifted-shape.ts'
import {completeWorkProfile} from './work-profile.ts'
import {workLedger} from './work-admission.ts'
import {exactRaw,workAdd,workSub,zeroWork} from './work-amount.ts'
import {workMap,workFilter,workEntries} from './work-collections.ts'
import {type CountTierBudget,countTierBudget,remainingCountTierBudget,ordinaryTierShare} from './count-tier-budget.ts'
import {countRejectionBudget,remainingRejectionAllowance} from './count-rejection-budget.ts'
import {countGenerationPhase} from './count-generation-phase.ts'
import {countReachabilityScreen,optionalReachabilityScreen,type CountReachabilityFunding} from './count-reachability.ts'
import {reconcileReachableRejections,withoutReachableRejections} from './count-reachability-reconcile.ts'
import {rejectionStage} from './rejection-discovery.ts'
import {type RejectionStage,rejectionFamily} from './rejection-stage.ts'
import {reserveCountClosing,reserveCheckedCountClosing,countOrdinaryUntil,type CountClosingBudget} from './count-closing-budget.ts'
import {rescopeCountProof} from './count-proof-rescope.ts'
import {countRescopeFunding} from './count-rescope-funding.ts'
import {countClosingNeeds} from './count-closing-needs.ts'
import {countPrerequisiteComponents,type ComponentOutcome} from './count-prerequisite-components.ts'
import {countPrerequisiteSchedule} from './count-prerequisite-plan.ts'
import {countComponentAttemptBudget} from './count-component-budget.ts'
import {prepareCountPrerequisiteMemory,type CountPrerequisiteMemory} from './count-prerequisite-memory.ts'
import {discoverRowAgreement} from './row-agreement-shape.ts'
import {countPremiseContext} from './count-premise-view.ts'
import {countPremiseSearch} from './count-premise-search.ts'

// (GDP_COUNTS_PROF: where a counted search's time goes, by phase, on stderr at the end; `countsDump.on`, set by research's
// profiles: each step goal left unknown or with a model past GDP_COUNTS_DUMP_MIN (300) hypotheses, the first GDP_COUNTS_DUMP_N (3))
export const cprof: Record<string, number> = {}
export const countsDump: {on?: (goal: object) => void} = {}
const tally = (k: string, n = 1) => { cprof[k] = (cprof[k] ?? 0) + n }
const ptime = <T>(k: string, f: () => T): T => { const t = countedTraceNow(); try { checkWall(k); const out = f(); checkWall(k); return out } finally { cprof[k] = (cprof[k] ?? 0) + countedTraceNow() - t } }
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

const quorumCandidates = new WeakSet<Law>()

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
  // Lift row-majority bodies beside the stored-set loop. Their laws are admitted
  // after the old candidate families; merely recognizing a shape trusts nothing.
  const lifted = quorumLaws(m)
  Object.assign(counts, lifted.counts)
  for (const law of lifted.laws) { laws.push(law); quorumCandidates.add(law) }
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
export function candidates(src: Parameters<typeof inferLaws>[0], m: Machine, caller: Law[], shapes: Law[], guarded: Law[], ms: number, until: number, support = new Set<Law>(), publish?: (laws:Law[])=>void): Law[] {
  const source = 'machine' in src ? src.machine : src
  const states = ptime('small', () => smallOf(m))
  // (a law of the state only: one the kernel's scope refuses, reading an input or a count of the request (a guard's
  // comparison with a second request count), has no value at a state, and is not proposed)
  const ofState = (l: Law) => { try { scope(m, [l]); return true } catch(error) { if(publish&&error instanceof BudgetExpired)throw error;return false } }
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
  const loadedFields = env.GDP_COUNT_STRATEGIES === '1'
  const cubes = cubes0.map(loosened), fields = fieldLaws(m, false, loadedFields)
  const lifted = guarded.filter(l => quorumCandidates.has(l)), ordinary = guarded.filter(l => !quorumCandidates.has(l))
  const newFields = fieldLaws(m, true, loadedFields).slice(fields.length, fields.length + Math.max(0, 32 - lifted.length))
  if (env.GDP_COUNTS_TRACE) console.error(`counts: small ${states.map(({sts}) => sts.length).join('/')}; cubes ${cubes.length} in ${Math.round(clock() - t1)} ms: ${cubes.map(l => l.name).join('; ')}`)
  // (a candidate whose every conjunct a law before it states, its keys named apart by place, is not proposed again: a
  // cell's maximum its kind's law states, a cube a guard's)
  const said = new Set<string>(), parts = (l: Law): string[] => {
    const ks = [l.forall, ...(l.keys ?? [])].filter((x): x is string => !!x), named = substC(l.holds, {vars: Object.fromEntries(ks.map((x, i) => [x, v(`$${i}`)])), maps: {}, flags: {}})
    return (named.op === 'and' ? named.xs : [named]).map(json)
  }
  for (const l of caller) for (const q of parts(l)) said.add(q)
  const prefixes = scanPrefixes(m, [...caller, ...kinds, ...guarded, ...rowLaws, ...cubes])
  const admitted:Law[]|undefined=publish?[]:undefined
  const admit = (l: Law) => { const ps = parts(l); if (ps.every(q => said.has(q)) || !trueAll(l)) return false; for (const q of ps) said.add(q); if(admitted){admitted.push(l);publish?.(admitted.slice())} return true }
  let out = ptime('filter', () => [...kinds, ...ordinary, ...rowLaws, ...fields, ...prefixes, ...cubes].filter(admit))
  const carried = carryCandidates(m, [...caller, ...kinds, ...guarded, ...rowLaws, ...cubes])
  out.push(...ptime('filter', () => carried.filter(admit)))
  // (a guarded field law is a weakening: admitted only when the stronger form it weakens was not)
  out.push(...ptime('quorumFilter', () => loadedFields ? selectFieldLaws([...lifted, ...newFields], admit) : [...lifted, ...newFields].filter(admit)))
  if (lifted.length) {
    // Counts used only by rejected liftings must not spawn another family.
    const liftedCounts = new Set([...reads([...caller, ...out], mp => !!m.counts?.[mp]).values()].map(([mp]) => mp))
    for (const name of liftedCounts) for (const [mp] of reads(m.counts![name]!.body, () => true).values()) if (m.counts?.[mp]) liftedCounts.add(mp)
    if (liftedOneKeyCounts(source, m).some(name => liftedCounts.has(name))) {
      out.push(...ptime('countCubes', () => countCubes(source, m, states, liftedCounts).filter(admit)))
      out = ptime('finiteHoudini', () => finiteHoudini(source, m, caller, out, states, {
        // Deterministic generation prefix: proposals, predecessor checks and
        // request trials share one allowance, not a machine-speed wall stop.
        ...(loadedFields ? {workLimit: 2_000} : {}),
        onFinish: row => { if (env.GDP_COUNTS_TRACE) console.error(`counts: finite result ${JSON.stringify(row)}`) },
        onDrop: d => { if (env.GDP_COUNTS_TRACE) console.error(`counts: finite drop ${d.round} ${d.law.name}`) },
        onRound: row => { if (env.GDP_COUNTS_TRACE) console.error(`counts: finite Houdini ${JSON.stringify(row)}`) },
      }))
    }
  }
  // A rejected proposal must not enlarge every later counted goal. Retain only
  // lifted counts read by an admitted law (and their transitive dependencies).
  const proposed = new Set([...reads(lifted, mp => !!m.counts?.[mp]).values()].map(([mp]) => mp))
  const used = new Set([...reads([...caller, ...out], () => true).values()].map(([mp]) => mp))
  for (const name of used) if (m.counts?.[name]) for (const [mp] of reads(m.counts[name]!.body, () => true).values()) used.add(mp)
  for (const name of proposed) if (!used.has(name)) delete m.counts![name]
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
export type Tried<P> = {proof: P} | {stuck: string, refuted?: boolean, expired?: boolean, reason?: string}
// Recovery proposals must not consume a successful ordinary attempt's allowance.
// A deferred proposal keeps the latest warmed context, but never extends its deadline.
export function withDeferredCountRecovery<P>(until: number, attempt: (defer: (recover: () => P | undefined) => void) => Tried<P>, ready: () => boolean = () => true): Tried<P> {
  let recover: (() => P | undefined) | undefined
  const ordinary = attempt(next => { recover = next })
  if ('proof' in ordinary || ordinary.refuted === true || !recover || !ready() || clock() >= until) return ordinary
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
// A selected row strategy runs before either ordinary pass, never after a
// count-first attempt has already consumed its share. Default order is unchanged.
function firstCountPass(m: Machine, law: Law, countFirst: boolean): 0 | 1 {
  return countFirst && !(env.GDP_COUNT_STRATEGIES === '1' && discoverRowAgreement(m, law)) ? 1 : 0
}
// Count-specific scheduling needs count or global-state context, not merely a
// primitive pointwise implication. Otherwise preserve the ordinary family first.
export function countSupportContext(m:Machine,caller:Law[],set:Law[],support:Set<Law>):{laws:Law[],support:Set<Law>}{
  if(!activeSupport(set,support)||set.some(l=>support.has(l)&&(reads(l.holds,map=>!!m.counts?.[map]).size||!l.forall&&some(l.holds,node=>node.op==='var'&&typeof node.name==='string'&&Object.hasOwn(m.state,node.name)&&!l.some?.includes(node.name)))))return {laws:set,support}
  return {laws:set.filter(l=>caller.includes(l)||!support.has(l)),support:new Set()}
}
export function supportOrder(set: Law[], caller: Law[], support: Set<Law>, forModels = false, m?: Machine): Law[] {
  if (forModels && !activeSupport(set, support)) return set
  const ordered = !activeSupport(set, support)
    ? [...set.filter(l => !caller.includes(l)), ...set.filter(l => caller.includes(l))]
    : [...set.filter(l => support.has(l) && !caller.includes(l)), ...set.filter(l => caller.includes(l)), ...set.filter(l => !support.has(l) && !caller.includes(l))]
  // Admission order only: keep model hypotheses, family membership, support
  // status and every per-attempt allowance unchanged.
  if (forModels || !m) return ordered
  const countReaders = new Set(ordered.filter(l => reads(l.holds, mp => !!m.counts?.[mp]).size > 0))
  if (env.GDP_COUNT_STRATEGIES === '1') {
    const rows = new Set(ordered.filter(l => !countReaders.has(l) && discoverRowAgreement(m, l)))
    if (rows.size) {
      const ordinary = ordered.filter(l => !countReaders.has(l) && !rows.has(l))
      return [...ordered.filter(l => countReaders.has(l)), ...ordered.filter(l => rows.has(l)),
        ...ordinary.filter(l => support.has(l) && !caller.includes(l)), ...ordinary.filter(l => caller.includes(l)),
        ...ordinary.filter(l => !support.has(l) && !caller.includes(l))]
    }
  }
  if (!countReaders.size) return ordered
  return [...ordered.filter(l => countReaders.has(l)),
    ...ordered.filter(l => !countReaders.has(l) && support.has(l) && !caller.includes(l)),
    ...ordered.filter(l => !countReaders.has(l) && caller.includes(l)),
    ...ordered.filter(l => !countReaders.has(l) && !support.has(l) && !caller.includes(l))]
}
export type Counted = {proven: boolean, laws: Law[], m: Machine, proof?: CountFamilyProof, why?: string}
// On the counted clock (kernel/prove.ts's `counted`, the cost model's work at fullRate a millisecond), as the engine's
// search is: counted fuel and ordering are unchanged up to the wall cutoff. The
// wall is an independent hard ceiling, including sampling and generation. A slow
// machine may stop earlier on the same counted-work prefix, never get extra time.
// The ordinary family gets its complete existing path first. Structured
// witness families are retried only after failure, under the same absolute
// deadline and counted fuel; no generated family is removed.
function structuredFallback(until: number, attempt: (structured: boolean) => Counted): Counted {
  const ordinary = attempt(false)
  if (ordinary.proven || clock() >= until) return ordinary
  checkWall('structured fallback')
  countsDump.on?.({phase: 'structured-family-expansion'})
  const structured = attempt(true)
  // A local refusal may have crossed the direct caller's inherited phase.
  // Check before withDeadline restores that phase on the return path.
  checkWall('structured fallback completion')
  return structured
}
export function searchCounted(m0: Machine, caller: Law[], ms = 60_000): Counted {
  const reject=env.GDP_COUNT_REJECTIONS==='1'&&env.GDP_COUNT_TIERS==='1'&&env.GDP_COUNT_STRATEGIES==='1'
  let m = m0,rejecting=false
  const run = () => withWall(searchWall(ms), (): Counted => {
    try {
      const start=reject?fullWork()/fullRate:0
      const g = ptime('guards', () => guardLaws(m0))
      m = {...m0, counts: {...m0.counts, ...g.counts}}
      if(reject&&g.laws.some(law=>quorumCandidates.has(law))){rejecting=true;return counted(fullRate,()=>searchCounted0(m0,g,m,caller,ms,remainingCountTierBudget(start,ms,1)),true)}
      ptime('small', () => smallOf(m, m0))
      return counted(fullRate, () => searchCounted0(m0, g, m, caller, ms), true)
    } catch (e) {
      if (!(e instanceof WallExpired)&&!(rejecting&&e instanceof BudgetExpired)) throw e
      return {proven: false, laws: caller, m, why: e.message}
    }
  })
  if (!env.GDP_COUNTS_PROF) return run()
  cdclStats.on = true
  const t = countedSearchNow(), out = run()
  console.error(`counts: prof total ${Math.round(countedSearchNow() - t)} ms; ${Object.entries(cprof).map(([k2, x]) => `${k2} ${Math.round(x)}`).join(', ')}; cdcl runs ${cdclStats.runs} conflicts ${cdclStats.conflicts} decisions ${cdclStats.decisions} solveMs ${Math.round(cdclStats.solveMs)} rowsMs ${Math.round(cdclStats.rowsMs)} coreMs ${Math.round(cdclStats.coreMs)} unfoldMs ${Math.round(cdclStats.unfoldMs)} lpMs ${Math.round(cdclStats.lpMs)} boundMs ${Math.round(cdclStats.boundMs)} orderMs ${Math.round(cdclStats.orderMs)} fmCalls ${cdclStats.fmCalls} lpMisses ${cdclStats.lpMisses} lpUnknown ${cdclStats.lpUnknown} missMs ${Math.round(cdclStats.missMs)} fastMs ${Math.round(cdclStats.fastMs)} fmOpenMs ${Math.round(cdclStats.fmOpenMs)} fmLeafMs ${Math.round(cdclStats.fmLeafMs)} nodes ${cdclStats.nodes}`)
  return out
}
function searchCounted0(m0: Machine, g: ReturnType<typeof guardLaws>, m: Machine, caller: Law[], ms: number,tiers?:CountTierBudget): Counted {
  if(tiers)return searchCountedWithRejection(m0,g,m,caller,ms,tiers)
  const tierRun: CountTierRun = {start: clock(),source:m0}, until = tierRun.start + ms
  if (!caller.every(l => clock() < until && trueSmall(m, [l]))) return {proven: false, laws: caller, m, why: clock() < until ? 'a law fails on the small instances' : 'time'}
  const t1 = clock()
  // (GDP_COUNTS_GIVEN=1, research's: the callers alone, no candidate: whether a set written whole goes through)
  const support = new Set<Law>()
  let set = env.GDP_COUNTS_GIVEN === '1' ? [...caller] : [...caller, ...candidates(m0, m, caller, caller, g.laws, ms, until, support)]
  countsDump.on?.({phase: 'candidates', machine: m, laws: set})
  if (env.GDP_COUNTS_TRACE) console.error(`counts: candidates at ${Math.round(clock() - t1)} ms: ${set.map(l => l.name).join('; ')}`)
  const context=countSupportContext(m,caller,set,support)
  return structuredFallback(until, structured => {
    const result=admitCountedFamilyOnce(m,caller,context.laws,context.support,until,structured,tierRun)
    // Preserve full-context fallback before trying extra witness families.
    return result.proven||context.laws.length===set.length||clock()>=until?result:admitCountedFamilyOnce(m,caller,set,context.support,until,structured,tierRun)
  })
}

// Production rejection is a relative size-two pass inside the existing generation
// tier. Its single ledger and absolute endpoints survive every admission fallback.
function searchCountedWithRejection(m0:Machine,g:ReturnType<typeof guardLaws>,m:Machine,caller:Law[],ms:number,tiers:CountTierBudget):Counted{
 const plan=countRejectionBudget(tiers,true)
 if(!plan)return searchCounted0(m0,g,m,caller,ms)
 const until=tiers.until,tierRun:CountTierRun={start:until-tiers.workAllowance,budget:tiers,source:m0},support=new Set<Law>(),originalCounts={...m.counts}
 let partial=[...caller]
 const generated=countGenerationPhase(plan.captureUntil,()=>{
  for(const law of g.laws){try{scope(m,[law]);partial.push(law)}catch(error){if(error instanceof BudgetExpired)throw error}}
  ptime('small',()=>smallOf(m,m0))
  if(!caller.every(law=>clock()<until&&trueSmall(m,[law])))return {valid:false as const,set:[...caller]}
  const set=env.GDP_COUNTS_GIVEN==='1'?[...caller]:[...caller,...candidates(m0,m,caller,caller,g.laws,ms,plan.captureUntil,support,laws=>{partial=[...caller,...laws]})]
  return {valid:true as const,set}
 })
 if(!generated.complete)m.counts={...originalCounts,...m.counts}
 const bundle=generated.complete?generated.value:{valid:true as const,set:partial}
 countsDump.on?.({phase:'count-generation-result',complete:generated.complete,...plan,workAllowance:tiers.workAllowance})
 if(!bundle.valid)return {proven:false,laws:caller,m,why:'a law fails on the small instances'}
 let set=bundle.set
 countsDump.on?.({phase:'candidates',machine:m,laws:set,partial:!generated.complete})
 const allowance=remainingRejectionAllowance(plan,clock())
 const rejections=rejectionStage(m0,m,caller,set,allowance)
 set=rejections.active()
 countsDump.on?.({phase:'count-rejection-result',work:rejections.screenWork,replayWork:rejections.work(),removed:rejections.evidence().map(e=>({kind:e.kind,name:e.law.name})),phases:rejections.phases,remaining:set.length,safety:rejections.safety(),replayEvidence:()=>rejections.evidence()})
 countsDump.on?.({phase:'post-rejection-candidates',machine:m,laws:set})
 const context=countSupportContext(m,caller,set,support)
 return structuredFallback(until,structured=>{
  const result=admitCountedFamilyOnce(m,caller,context.laws,support,until,structured,tierRun,rejections)
  return result.proven||context.laws.length===set.length||clock()>=until?result:admitCountedFamilyOnce(m,caller,set,support,until,structured,tierRun,rejections)
 })
}

// One reservation survives context and structured fallbacks.
type CountTierRun = {start: number, source?:Machine, budget?: CountTierBudget, prerequisites?:CountPrerequisiteMemory<ScopedCountProof>, reachability?:{key:string,screen:ReturnType<typeof countReachabilityScreen>},reachFunding?:CountReachabilityFunding,recipePass?:CountRecipePass<ScopedCountProof>,recipeStructured?:boolean}
// Candidate scheduling only. Every returned family still goes through finish.
export function admitCountedFamily(m:Machine,caller:Law[],initial:Law[],support:Set<Law>,until:number,tiers?:CountTierBudget):Counted {
  if (tiers && tiers.until !== until) throw new RangeError('mismatched tier deadline')
  const tierRun: CountTierRun = {start: tiers ? until - tiers.workAllowance : clock(), budget: tiers?.active ? tiers : undefined,source:m}
  return structuredFallback(until, structured => admitCountedFamilyOnce(m,caller,initial,support,until,structured,tierRun))
}
function admitCountedFamilyOnce(m:Machine,caller:Law[],initial:Law[],support:Set<Law>,until:number,structured:boolean,tierRun:CountTierRun,rejections?:RejectionStage):Counted {
  if(rejections)initial=rejectionFamily(rejections,initial)
  const previous = proofOrigins.enabled
  if (env.GDP_COUNT_LEMMA_CUTS === '1') proofOrigins.enabled = true
  try {
    if (env.GDP_COUNT_STRATEGIES === '1') m = prepareCountStrategyMachine(m, initial, until, event => countsDump.on?.({phase: 'count-strategy-context', ...event}))
    const selected = env.GDP_COUNT_STRATEGIES === '1' && env.GDP_COUNT_TIERS === '1' ? new Set(selectedCountStrategies(m, initial)) : new Set<Law>()
    const budget = selected.size ? (tierRun.budget = reserveCountClosing(tierRun.budget ?? countTierBudget(tierRun.start, until, selected.size), finalCountStepDeferralEnabled() && env.GDP_COUNT_CLOSING_RESERVE === '1')) : undefined
    if (budget) countsDump.on?.({phase: 'count-tier-plan', ...budget, selected: [...selected].map(law => law.name)})
    return admitCountedFamily0(m, caller, initial, support, until, structured, budget, selected, budget && 'closingMode' in budget ? budget.workAllowance : Math.max(0, until - tierRun.start),tierRun,rejections)
  }
  finally { proofOrigins.enabled = previous }
}
function admitCountedFamily0(m:Machine,caller:Law[],initial:Law[],support:Set<Law>,until:number,structured:boolean,budget:CountTierBudget|undefined,selected:Set<Law>,workAllowance:number,tierRun:CountTierRun,rejections?:RejectionStage):Counted {
  if(!caller.every(l=>initial.includes(l)))return {proven:false,laws:initial,m,why:'missing caller'}
  let closingBudget = budget && 'closingMode' in budget ? budget as CountClosingBudget : undefined
  if (closingBudget) until = countOrdinaryUntil(closingBudget)
  const prerequisiteFirst = !!closingBudget && env.GDP_COUNT_PREREQUISITES === '1'
  const proofGuided = prerequisiteFirst && env.GDP_COUNT_PROOF_GUIDED_SCHEDULING === '1'
  const beforeClosing = <T>(body:()=>T):T|undefined => {
    if (!prerequisiteFirst) return body()
    try { return withBudget(Math.max(0,until-clock())*fullRate,body) }
    catch(error) { if(!isLocalCountExpiration(error,closingBudget!.until))throw error; return undefined }
  }
  let set=rejections?rejectionFamily(rejections,initial):initial.slice()
  let reach:ReturnType<typeof countReachabilityScreen>|undefined
  if(proofGuided)reach=optionalReachabilityScreen(()=>{
    const setup=clock(),key=JSON.stringify(m)
    if(tierRun.reachability?.key!==key)tierRun.reachability={key,screen:countReachabilityScreen(tierRun.source??m,m,caller,workAllowance,undefined,tierRun.reachFunding??=new Map())}
    const screen=tierRun.reachability.screen
    set=withoutReachableRejections(set,screen.rejectedNames())
    countsDump.on?.({phase:'count-reachability-setup',units:(clock()-setup)*fullRate})
    return screen
  })
  const scopeEnabled = env.GDP_COUNT_STRATEGIES === '1'
  const attempts = countedAttempts(m, caller, support, proofGuided ? closingBudget!.until : until, structured, selected, workAllowance, budget, prerequisiteFirst ? initial : undefined), traced = attempts.traced
  const isCount = (mp: string) => !!m.counts?.[mp]
  // Prove the proposed set together. A preliminary cone reproved many helpers in
  // several smaller contexts before asking these same induction goals. Houdini
  // drops failed helpers and carries proofs whose instantiated support survives.
  // Every returned set still passes checkCountedLaws, including all caller laws.
  const finish = (ls: Law[], proof: CountFamilyProof, targetFamily=true): Counted => {
    const close = (candidate: CountFamilyProof): boolean => {
      if (!closingBudget) return closingCountCheck(() => checkCountedLaws(m, ls, candidate))
      const start = clock()
      countsDump.on?.({phase:'count-family-closing',stage:'start',at:start,end:withinDeadline(closingBudget.until),laws:ls.map(l=>l.name)})
      const checked = withDeadline(closingBudget.until, () => closingCountCheck(() => checkCountedLaws(m, ls, candidate)))
      countsDump.on?.({phase:'count-family-closing',stage:'end',checked,at:clock(),units:(clock()-start)*fullRate})
      return checked
    }
    let proposed = proof
    if (env.GDP_COUNT_LEMMA_CUTS === '1') {
      // This pass performs no search work. Reuse the enclosing wall deadline; outside one,
      // conservatively cap its wall time by the remaining counted allowance. Neither budget is extended.
      const wall = wallAt(), end = Number.isFinite(wall) ? wall : countedSearchNow() + Math.max(0, until - clock())
      for (const {goal, decls} of countedObligations(m, ls, proof.instances)) {
        if (countedSearchNow() >= end) break
        const cert = proof.certs[goal.name]
        if (!cert || cert.lemmas?.length) continue
        const expanded = mcGoal(goal.hyps, decls, cert)
        const shared = expanded && proposeLemmaCuts(expanded, cert.tree, {until: end})
        if (shared) proposed = {...proposed, certs: {...proposed.certs, [goal.name]: {...cert, tree: shared.tree, lemmas: shared.lemmas}}}
      }
    }
    if (proposed !== proof && ptime('kernel', () => close(proposed))) {
      // Sharing may retain a wider independent-cut source slice. Never attach
      // pre-sharing premise metadata to a different final certificate.
      if (!scopeEnabled) proof = proposed
      else {
      const premises = {...proof.premises}
      for (const law of ls) if ([' @start', ' @step'].some(suffix => proposed.certs[law.name + suffix] !== proof.certs[law.name + suffix])) {
        const scoped = ptime('premise-scope', () => scopeCountProof(m, law, ls, {instances: proposed.instances[law.name] ?? {}, certs: proposed.certs}, until))
        if (scoped) premises[law.name] = scoped.premises.map(p => p.name)
        else delete premises[law.name]
      }
      proof = {...proposed, premises}
      }
    } else if (!ptime('kernel', () => close(proof))) return {proven: false, laws: ls, m, why: 'the kernel refused the set'}
    // Output-only observation, after the unchanged checker accepts every obligation.
    countsDump.on?.({phase: targetFamily?'closed-family':'closed-subfamily', machine: m, laws: ls, proof, checked: true})
    if(!targetFamily)return {proven:false,laws:ls,m,why:'closed subfamily excludes caller'}
    return {proven: true, laws: ls, m, proof}
  }
  const recipeJoint=():Counted=>{
    const prepared=beforeClosing(()=>{
      const context=countScopeContextKey(m,set)
      if(tierRun.recipePass){
        workLedger.start('tableCells',Math.min(context.length,tierRun.recipePass.context.length),'count recipe inventory context')
        // Never reuse a fixed inventory for changed machine/law bytes. Keep
        // the old instances and fuel; a different context gets no new pass.
        if(!countRecipeContextDecision(tierRun.recipePass,context,tierRun.recipeStructured,structured,event=>countsDump.on?.(event)))return {kind:'context-changed' as const}
      }else{
        const plan=countPrerequisiteSchedule(m,set,selected,until)
        const members=workMap(set,(law,reference):CountControllerMember=>({name:law.name,reference,recipes:workMap(plan.recipes.get(law.name)??[],recipe=>{
          const shape=recipe.id==='lifted'?discoverLiftedCountGuard(m,law,set):undefined
          const operations=shape&&discoverLiftedCountOperations(m,shape)
          return {...recipe,...(operations?{caseKeys:workMap(operations,operation=>'op:'+operation.value,'count recipe case inventory')}:{})}
        },'count recipe inventory')}),'count member inventory')
        tierRun.recipePass=new CountRecipePass<ScopedCountProof>(members,context)
      }
      tierRun.recipeStructured=structured
      return {kind:'ready' as const,
        lawByName:new Map(workMap(set,law=>[law.name,law] as const,'count recipe law lookup')),
        active:new Set(workMap(set,law=>law.name,'count active inventory')),
        targets:workMap(caller,law=>law.name,'count recipe targets')}
    })
    if(!prepared||prepared.kind!=='ready')return {proven:false,laws:set,m,why:prepared?.kind==='context-changed'?'recipe fixed inventory context changed':'recipe planning budget'}
    const {lawByName,active,targets}=prepared
    const tick=()=>workLedger.start('ticks',1,'count recipe adapter')
    const reconcile=()=>{if(reach)for(const name of reach.rejectedNames()){tick();active.delete(name)}}
    const screen=(law:Law,ordinary:number,citing:number):boolean=>{
      if(!reach)return true
      try{
        const row=reach.screen(law,ordinary,citing,Infinity,attempts.countermodel(law))
        if(row)countsDump.on?.({phase:'count-reachability',...row})
        return !!row&&row.outcome!=='rejected'&&reach.safety()!=='broken'
      }finally{reconcile()}
    }
    if(beforeClosing(()=>{reconcile();return true})!==true)return {proven:false,laws:set,m,why:'recipe reconciliation budget'}
    attempts.houdini=true
    let transportDeclined:string|undefined
    const outcome=runCountRecipeController(tierRun.recipePass!,targets,{
      active,observe:event=>countsDump.on?.(event),
      preflight:(name,recipe)=>{
        const law=lawByName.get(name)
        // The requested legacy screen allowance is clipped by the existing
        // exact member/phase/root scopes; it never creates a new root.
        return !!law&&active.has(name)&&(recipe.kind!=='ordinary'||screen(law,workAllowance,0))
      },
      construct:(name,recipe,lease)=>{
        const law=lawByName.get(name)
        if(!law||!active.has(name)||reach?.safety()==='broken')return
        let proof:CountLawProof|undefined
        if(recipe.kind==='strategy'){
          if(recipe.caseKeys!==undefined)proof=lease&&attempts.exactStrategy(law,set,lease)
          else if(recipe.id==='row'||recipe.id==='guard')proof=attempts.strategyProposal(law,set,recipe.id)
          else countsDump.on?.({phase:'count-strategy',law:name,stage:'decline',reason:recipe.id==='lifted'?'missing-lifted-case-inventory':'unsupported-strategy-recipe',recipe:recipe.id})
        }
        else{
          let result=traced(law,set,0,Infinity,false)
          if(!('proof'in result)&&!result.refuted&&attempts.counted)result=traced(law,set,1,Infinity,false)
          if('proof'in result)proof=result.proof
          else if(result.expired)throw new BudgetExpired('ordinary recipe cutoff')
        }
        return proof
      },
      capture:(name,recipe,proof)=>{
        const law=lawByName.get(name)
        if(!law)return
        const before=workLedger.actual();let identity=zeroWork
        const captured=withCountScopeIdentityObservation(amount=>{identity=workAdd(identity,amount)},()=>{
          const scoped=rescopeCountProof(m,law,set,proof!,new Set(tierRun.recipePass!.held().keys()),Infinity,
            event=>countsDump.on?.({phase:'count-component-rescope',law:name,...event}),countRescopeFunding())
          if(!scoped)return
          const checkedReduced=isCheckedReducedScope(scoped,m,set)
          return {payload:scoped,premises:workMap(scoped.premises,p=>p.name,'count recipe scoped names'),checkedReduced}
        })
        countsDump.on?.({phase:'count-rescope-identity',law:name,rawWork:exactRaw(identity),rootEpoch:workLedger.snapshot().rootEpoch})
        if(!captured)return
        const effective=new Set<string>()
        for(const dependency of captured.premises){tick();effective.add(dependency)}
        if(!captured.checkedReduced)for(const dependency of recipe.required??[]){tick();effective.add(dependency)}
        for(const dependency of effective){tick();const premise=lawByName.get(dependency);if(premise&&!screen(premise,0,workAllowance))return}
        return {...captured,checkCost:workSub(workLedger.actual(),before)}
      },
      declinedMember:()=>transportDeclined,
      repairSuppliers:(_name,scoped)=>{
        const repaired=resolveCountScopeSuppliers(m,set,scoped,Infinity)
        return repaired&&{payload:repaired,premises:workMap(repaired.premises,p=>p.name,'count repaired supplier names')}
      },
      close:(rows,targetInFamily)=>{
        transportDeclined=undefined
        const names=new Set(workMap(rows,row=>row.id,'count closing inventory'))
        const family=workFilter(set,law=>names.has(law.name),'count closing family'),instances:Record<string,Instances>={},certs:Record<string,CountCert>={},premises:Record<string,readonly string[]>={}
        if(reach?.safety()==='broken')return {proven:false,laws:family,m,why:'reachable caller counterexample'}
        for(const row of rows){
          tick()
          // Use the graph's effective S for membership and published premises;
          // replay the untouched scoped payload against exactly that family.
          const proof=replayScopedCountProof(m,family,row.payload,Infinity,{deferToClosing:true,onTransportDecline:()=>{transportDeclined=row.id}})
          if(!proof)return {proven:false,laws:family,m,why:'recipe closing replay declined'}
          instances[row.id]=proof.instances
          for(const [name,cert]of workEntries(proof.certs,'count closing certificates'))certs[name]=cert as CountCert
          premises[row.id]=row.premises
        }
        if(reach)countsDump.on?.({phase:'count-reachability-summary',rows:reach.receipts(initial),replayEvidence:reach.evidence})
        let hasCallers=targetInFamily
        for(const law of caller){tick();if(!names.has(law.name))hasCallers=false}
        return finish(family,{instances,certs,premises},hasCallers)
      }
    })
    countsDump.on?.({phase:'count-recipe-summary',reason:outcome.reason,failure:outcome.failure,closingRoute:outcome.closingRoute,proven:outcome.result?.proven??false})
    const diagnostic='recipe pass: '+outcome.reason+(outcome.failure?'; '+outcome.failure.reason:'')
    if(!outcome.result)return {proven:false,laws:set,m,why:diagnostic}
    return outcome.result.proven?outcome.result:{...outcome.result,why:(outcome.result.why?outcome.result.why+'; ':'')+diagnostic}
  }
  const joint = (): Counted => {
    const planned=beforeClosing(()=>countPrerequisiteSchedule(m,set,selected,until))
    if(!planned)return {proven:false,laws:set,m,why:'prerequisite planning budget'}
    const ranked=[...new Set([...caller,...supportOrder(set,caller,support,false,m)])]
    const order=ranked.sort((a,b)=>planned.costs.get(a.name)!-planned.costs.get(b.name)!)
    const restored=prepareCountPrerequisiteMemory(tierRun.prerequisites,m,set),remembered=tierRun.prerequisites=restored.state
    const scopes=remembered.scopes,ends=new Map<string,number>(),attempted=new Set<string>()
    const queue=countPrerequisiteComponents(order.map(l=>l.name),planned.requirements,[...selected].map(l=>l.name),[...remembered.committed],{...planned,discoveryFirst:true,proofGuided,discoveryContexts:remembered.discoveryContexts,targets:caller.map(l=>l.name),held:new Map([...scopes].map(([name,scope])=>[name,scope.premises.map(p=>p.name)])),discovered:[...remembered.discovered],failed:[...remembered.failed]})
    const ordinaryCount=Math.max(1,set.filter(l=>!selected.has(l)).length)
    const reachSummary=()=>{if(reach)countsDump.on?.({phase:'count-reachability-summary',rows:reach.receipts(initial),replayEvidence:reach.evidence})}
    let activeAttempt:string|undefined,restarted=false
    const members=new Set(order.map(law=>law.name))
    const reconcile=()=>{
      if(!reach)return
      const delta=reconcileReachableRejections(queue,members,reach.rejectedNames(),scopes,remembered.committed,activeAttempt)
      if(!delta.rejected.length)return
      activeAttempt=undefined;restarted=true
      remembered.failed=new Set(queue.failed());remembered.discoveryContexts=queue.discoveryContexts()
      set=withoutReachableRejections(set,delta.rejected)
      countsDump.on?.({phase:'count-reachability-invalidated',...delta})
    }
    const probe=(law:Law,ordinary:number,citing:number,end:number)=>{
      if(!reach)return undefined
      const screen=reach
      reconcile();if(restarted)return undefined
      const before=clock()
      let row:ReturnType<typeof screen.screen>|undefined
      try{row=beforeClosing(()=>screen.screen(law,ordinary,citing,end,attempts.countermodel(law)))}
      finally{reconcile()}
      if(row)countsDump.on?.({phase:'count-reachability',...row,invocationUnits:(clock()-before)*fullRate})
      return row
    }
    const updateReserve=()=>{
      if(!proofGuided)return
      const costs=[...scopes.values()].flatMap(scope=>scope.checkWork===undefined?[]:[scope.checkWork])
      closingBudget=reserveCheckedCountClosing(closingBudget!,costs,clock())
      budget=tierRun.budget=closingBudget;until=closingBudget.searchUntil
      countsDump.on?.({phase:'count-closing-reserve',at:clock(),checkedPackets:costs.length,checkedWork:costs.reduce((a,b)=>a+b,0),...closingBudget})
    }
    reconcile()
    updateReserve()
    attempts.houdini=true
    countsDump.on?.({phase:'count-prerequisite-plan',premises:Object.fromEntries(planned.requirements),recipes:Object.fromEntries(planned.recipes),until,rootUntil:closingBudget!.until})
    countsDump.on?.({phase:'count-prerequisite-memory',held:[...scopes.keys()],members:[...remembered.committed],invalidated:restored.invalidated})
    const closeReady=():Counted|undefined=>{
      const available=new Set(queue.available()),needed=countClosingNeeds(caller.map(l=>l.name),scopes)
      if(![...needed].every(name=>available.has(name)&&scopes.has(name)))return undefined
      const family=set.filter(l=>needed.has(l.name)),instances:Record<string,Instances>={},certs:Record<string,CountCert>={},premises:Record<string,readonly string[]>={}
      for(const member of family){
        const proof=beforeClosing(()=>ptime('premise-replay',()=>replayScopedCountProof(m,family,scopes.get(member.name)!,until,{deferToClosing:true})))
        if(!proof)return {proven:false,laws:set,m,why:'component replay declined'}
        instances[member.name]=proof.instances;Object.assign(certs,proof.certs);premises[member.name]=proof.premises??[]
      }
      reachSummary()
      return finish(family,{instances,certs,premises})
    }
    const alreadyClosed=closeReady()
    if(alreadyClosed)return alreadyClosed
    while(clock()<until){
      restarted=false
      const decision=queue.next()
      if(!decision)break
      activeAttempt=decision.kind==='attempt'?decision.name:undefined
      if(decision.kind==='ready'){
        let blocked=false
        if(reach)for(const name of decision.members){
          const member=set.find(l=>l.name===name)!,row=probe(member,0,scopes.get(name)?.checkWork??0,until)
          if(reach.safety()==='broken')return {proven:false,laws:set,m,why:'reachable caller counterexample'}
          if(restarted){blocked=true;break}
          if(row?.outcome==='rejected')return {proven:false,laws:set,m,why:'rejected member remained ready'}
          if(!row){blocked=true;break}
        }
        if(blocked)continue
        queue.commit(decision.members)
        for(const name of decision.members){remembered.committed.add(name);if(reach)countsDump.on?.({phase:'count-required-promotion',kind:'member',law:name,reducedScopeSize:scopes.get(name)?.premises.length??0,committed:true,proposed:true,checked:false})}
        countsDump.on?.({phase:'count-component-closed',members:decision.members,proposed:true,checked:false})
        for(const name of decision.members)countsDump.on?.({phase:'count-prerequisite-complete',law:name,premises:scopes.get(name)?.premises.map(p=>p.name)??[],proposed:true,component:decision.members})
        const closed=closeReady()
        if(closed)return closed
        continue
      }
      const law=set.find(l=>l.name===decision.name)!,context=set.filter(l=>decision.context.includes(l.name))
      const discoveryOnly=decision.purpose==='discovery'
      const ordinaryMembers=decision.component.filter(name=>!selected.has(set.find(l=>l.name===name)!)).length
      const horizon=Math.min(until,discoveryOnly?until:budget!.strategyUntil!+budget!.ordinaryFloor*ordinaryMembers/ordinaryCount)
      const key=JSON.stringify([decision.purpose,decision.component,...discoveryOnly?[law.name]:[]]),available=new Set(queue.available()),failed=new Set(queue.failed())
      if(!ends.has(key)||proofGuided&&!discoveryOnly){
        const eligible=set.filter(l=>!available.has(l.name)&&!failed.has(l.name)).length
        ends.set(key,discoveryOnly?clock()+Math.max(0,horizon-clock())/Math.max(1,eligible):horizon)
      }
      const componentEnd=Math.min(horizon,ends.get(key)!)
      const unattempted=discoveryOnly?1:Math.max(1,decision.component.filter(name=>!scopes.has(name)&&(proofGuided||!attempted.has(JSON.stringify([key,name])))).length)
      const allowStrategy=!discoveryOnly&&decision.recipe.kind==='strategy',start=clock()
      const {end,allotted,reserved}=countComponentAttemptBudget(clock(),componentEnd,unattempted,1,proofGuided&&!allowStrategy)
      if(reach&&!discoveryOnly&&!allowStrategy){
        const row=probe(law,allotted,0,end)
        if(reach.safety()==='broken')return {proven:false,laws:set,m,why:'reachable caller counterexample'}
        if(restarted){updateReserve();continue}
        if(row?.outcome==='rejected')return {proven:false,laws:set,m,why:'rejected prerequisite remained active'}
        if(!row)break
      }
      attempted.add(JSON.stringify([key,law.name]))
      if(discoveryOnly)remembered.discovered.add(law.name)
      countsDump.on?.({phase:'count-component-attempt',law:law.name,component:decision.component,mode:decision.phase,recipe:decision.recipe.id,context:decision.context,end,componentEnd,allotted,reserved,discovery:decision.discovery,purpose:decision.purpose,required:queue.required(),...(proofGuided?{pass:decision.pass??0}: {})})
      countsDump.on?.({phase:'count-tier-attempt',law:law.name,tier:selected.has(law)&&allowStrategy?'strategy':'ordinary',end,allotted})
      let result:Tried<Proof>={stuck:'unknown'},expired=allotted<=0
      try{
        if(allotted>0)result=withBudget(Math.max(0,end-clock())*fullRate,()=>{
          const invoke=(pass:0|1)=>traced(law,context,pass,Math.max(0,end-clock()),allowStrategy)
          const first=invoke(proofGuided?decision.pass??0:0)
          return !proofGuided&&!discoveryOnly&&!('proof'in first)&&!first.refuted&&(!selected.has(law)||!allowStrategy)&&attempts.counted&&clock()<end?invoke(1):first
        })
      }catch(error){if(!isLocalCountExpiration(error,closingBudget!.until))throw error;expired=true}
      if(!('proof'in result)&&result.expired)expired=true
      let scope:ScopedCountProof|undefined
      if('proof'in result)try{
        scope=withBudget(Math.max(0,end-clock())*fullRate,()=>beforeClosing(()=>proofGuided
          ?ptime('premise-rescope',()=>rescopeCountProof(m,law,context,result.proof,new Set(scopes.keys()),end,event=>countsDump.on?.({phase:'count-component-rescope',law:law.name,...event}),countRescopeFunding()))
          :ptime('premise-scope',()=>scopeCountProof(m,law,context,result.proof,end))))
      }catch(error){if(!isLocalCountExpiration(error,withinDeadline(closingBudget!.until)))throw error;expired=true}
      if('proof'in result&&!scope&&!expired&&clock()>=end){
        const error=new BudgetExpired('component premise scope')
        if(!isLocalCountExpiration(error,withinDeadline(closingBudget!.until)))throw error
        expired=true
      }
      let rejectedPremise=false
      if(scope&&reach){
        const citedBy=law.name,reducedScopeSize=scope.premises.length,citingWork=clock()-start
        for(const premise of scope.premises){
          const dependency=set.find(l=>l.name===premise.name)
          if(!dependency)continue
          const row=probe(dependency,0,citingWork,until)
          countsDump.on?.({phase:'count-required-promotion-screen',law:premise.name,citedBy,reducedScopeSize,screened:!!row,outcome:row?.outcome})
          if(reach.safety()==='broken')return {proven:false,laws:set,m,why:'reachable caller counterexample'}
          if(restarted){scope=undefined;break}
          if(row?.outcome==='rejected')rejectedPremise=true
          if(!row){expired=true;scope=undefined;break}
        }
        if(rejectedPremise)scope=undefined
      }
      if(restarted){updateReserve();continue}
      let status:ComponentOutcome=rejectedPremise?{kind:'unknown',reason:'reachable-refuted premise'}:scope?{kind:'proof',citations:scope.premises.map(p=>p.name)}:expired?{kind:'unknown',reason:'budget-expired'}:'proof'in result?(proofGuided?{kind:'unknown',reason:'checked rescope declined'}:{kind:'refused',reason:'returned proof has no valid scope'}):result.refuted?{kind:'refuted'}:{kind:'unknown',reason:result.reason??result.stuck}
      if((discoveryOnly||proofGuided)&&status.kind==='refuted')status={kind:'unknown',reason:'narrow-sat'}
      const outcome=queue.finish(law.name,status)
      activeAttempt=undefined
      remembered.failed=new Set(queue.failed())
      if(proofGuided)remembered.discoveryContexts=queue.discoveryContexts()
      for(const invalidated of outcome.invalidated){scopes.delete(invalidated);remembered.committed.delete(invalidated)}
      if(outcome.held&&scope){
        scopes.set(law.name,scope)
        if(reach)for(const premise of scope.premises)countsDump.on?.({phase:'count-required-promotion',kind:'dependency',law:premise.name,citedBy:law.name,reducedScopeSize:scope.premises.length,committed:false,proposed:true,checked:false})
      }
      else if(decision.phase!=='dissolve')scopes.delete(law.name)
      updateReserve()
      countsDump.on?.({phase:'count-component-result',law:law.name,mode:decision.phase,purpose:decision.purpose,component:decision.component,at:clock(),outcome:outcome.held?'proof':status.kind,reason:'reason'in status?status.reason:undefined,units:(clock()-start)*fullRate,held:outcome.held,failed:queue.failed(),unknown:queue.unknown(),invalidated:outcome.invalidated,retries:queue.retryCount(),premises:scope?.premises.map(p=>p.name)??[]})
    }
    reachSummary()
    countsDump.on?.({phase:'count-prerequisite-incomplete',unknown:queue.unknown(),failed:queue.failed()})
    return {proven:false,laws:set,m,why:'component proposals did not close caller'}
  }
  const join = (kept = new Map<string, Proof>()): Counted => {
    const keptProof = (): CountFamilyProof => ({instances: Object.fromEntries([...kept].map(([n, pr]) => [n, pr.instances])), certs: Object.assign({}, ...[...kept.values()].map(pr => pr.certs)), ...(scopeEnabled ? {premises:Object.fromEntries([...kept].flatMap(([name,pr])=>pr.premises?[[name,pr.premises]]:[]))} : {})})
    if (caller.every(l => kept.has(l.name))) return finish(set.filter(l => kept.has(l.name)), keptProof())
    // Each untried law gets an even share of what remains now, not what
    // remained at round entry. Cheap proofs return their underspend to the pool.
    let carried = new Map<string, Proof>()
    const scopes = new Map<string, ScopedCountProof>()
    const neededForSearch = () => countClosingNeeds([...caller.map(l=>l.name),...set.filter(l=>selected.has(l)&&scopes.has(l.name)).map(l=>l.name)],scopes)
    attempts.houdini = true
    for (let round = 0; clock() < until; round++) {
      const {instances, certs, premises = {}} = keptProof()
      const failed = new Set<string>(), proofs = new Map<string, Proof>()
      const pending = new Set(set.filter(l => !selected.has(l) && !kept.has(l.name) && !carried.has(l.name)).map(l => l.name))
      // Count readers first, then explicit supports and callers; unrelated
      // scalar helpers cannot consume the whole allowance before count admission.
      const order = supportOrder(set, caller, support, false, env.GDP_COUNT_STRATEGIES === '1' ? m : undefined)
      const todo = [...order.filter(l => selected.has(l)), ...order.filter(l => !selected.has(l))]
      for (let position = 0; position < todo.length; position++) {
        if (closingBudget && !selected.has(todo[position]!)) {
          const needed = neededForSearch()
          const prerequisites = new Set([...scopes.values()].filter(s=>selected.has(set.find(l=>l.name===s.owner.name)!)).flatMap(s=>s.premises.map(p=>p.name)))
          let next = todo.findIndex((l,i)=>i>=position&&prerequisites.has(l.name)&&!proofs.has(l.name))
          if(next<0) next = todo.findIndex((l,i)=>i>=position&&needed.has(l.name))
          if (next>position) [todo[position],todo[next]]=[todo[next]!,todo[position]!]
        }
        const law = todo[position]!
        checkWall('Houdini round')
        if (clock() > until) return {proven: false, laws: set, m, why: 'time'}
        if (kept.has(law.name)) continue
        const was = carried.get(law.name)
        const required = closingBudget ? neededForSearch() : undefined
        const focused = required && new Set([...pending].filter(name=>required.has(name)))
        const share = budget && !closingBudget ? ordinaryTierShare(budget, clock(), pending) : attemptShare(until - clock(), focused?.size ? focused : pending)
        pending.delete(law.name)
        const structural = support.has(law) && !caller.includes(law)
        const strategy = selected.has(law), boundedSupport = !budget && activeSupport(set, support)
        const allotted = strategy ? Math.max(0, budget!.strategyUntil! - clock()) : budget ? share : supportBudget(until - clock(), share, boundedSupport && caller.includes(law), structural)
        const supportUntil = strategy ? budget!.strategyUntil! : Math.min(until, clock() + (boundedSupport ? Math.min(allotted, 5_000) : allotted)), supportWall = countedSearchNow() + 4_800
        let proofContext = closingBudget && !strategy && required ? set.filter(l=>required.has(l.name)||l===law) : set
        const ask = (pass: 0 | 1): Tried<Proof> => {
          const ms = Math.min(allotted, Math.max(0, (boundedSupport ? supportUntil : until) - clock()))
          if (scopeEnabled) countsDump.on?.({phase: 'houdini-attempt', law: law.name, round, pass})
          if (budget) countsDump.on?.({phase: 'count-tier-attempt', law: law.name, tier: strategy ? 'strategy' : 'ordinary', end: supportUntil, allotted})
          const run = (): Tried<Proof> => {
            const invoke = (allowance:number) => strategy ? withDeadline(supportUntil, () => traced(law, proofContext, pass, allowance)) : boundedSupport ? withWall(supportWall, () => withDeadline(supportUntil, () => traced(law, proofContext, pass, allowance))) : traced(law, proofContext, pass, allowance)
            let result=invoke(ms)
            if(closingBudget&&proofContext!==set&&!('proof' in result)&&clock()<Math.min(supportUntil,until)){
              proofContext=set
              result=invoke(Math.min(ms,Math.max(0,Math.min(supportUntil,until)-clock())))
            }
            return result
          }
          if (!closingBudget) return run()
          try { return withBudget(Math.max(0,Math.min(supportUntil,until)-clock())*fullRate,run) }
          catch(error) { if(!isLocalCountExpiration(error,closingBudget.until))throw error; return {stuck:'unknown'} }
        }
        const countFirst = !strategy && firstCountPass(m, law, (env.GDP_COUNTS_COUNT_FIRST === '1' || boundedSupport && env.GDP_COUNTS_COUNT_FIRST !== '0') && (reads(law.holds, isCount).size > 0 || boundedSupport && !!law.keys?.length)) === 1
        let r: Tried<Proof> = was ? {proof: was} : ask(countFirst ? 1 : 0)
        if (!('proof' in r) && !r.refuted && !strategy && (countFirst || attempts.counted)) r = ask(countFirst ? 0 : 1)
        if (closingBudget) countsDump.on?.({phase:'count-family-collection',law:law.name,proposed:'proof' in r,at:clock()})
        if (!('proof' in r)) { failed.add(law.name); continue }
        if (!was && scopeEnabled) {
          const scoped = ptime('premise-scope', () => scopeCountProof(m, law, proofContext, r.proof, until))
          if (scoped) { scopes.set(law.name, scoped); r.proof = {...r.proof, premises: scoped.premises.map(p => p.name)} }
          else scopes.delete(law.name)
          if(closingBudget)countsDump.on?.({phase:'count-family-scope',law:law.name,scoped:!!scoped,premises:scoped?.premises.map(p=>p.name)??[]})
        }
        proofs.set(law.name, r.proof)
        instances[law.name] = r.proof.instances
        if(r.proof.premises)premises[law.name]=r.proof.premises
        Object.assign(certs, r.proof.certs)
        if (closingBudget) {
          const needed=countClosingNeeds(caller.map(l=>l.name),scopes)
          if([...needed].every(name=>proofs.has(name)&&scopes.has(name))) {
            const family=set.filter(l=>needed.has(l.name)),instances:Record<string,Instances>={},certs:Record<string,CountCert>={},premises:Record<string,readonly string[]>={}
            let ready=true
            for(const member of family){
              const replayed=ptime('premise-replay',()=>replayScopedCountProof(m,family,scopes.get(member.name)!,until,{deferToClosing:true}))
              if(!replayed){ready=false;break}
              instances[member.name]=replayed.instances;Object.assign(certs,replayed.certs);premises[member.name]=replayed.premises??[]
            }
            if(ready)return finish(family,{instances,certs,premises})
          }
        }
      }
      if (env.GDP_COUNTS_TRACE) console.error(`counts: round ${round}: ${set.length} laws, ${kept.size} kept, ${carried.size} carried, failed ${[...failed].join('; ').slice(0, 600)}`)
      if (!failed.size) return closingBudget ? {proven:false,laws:set,m,why:'closing scope incomplete'} : finish(set, {instances, certs, ...(scopeEnabled ? {premises} : {})})
      const next = set.filter(l => !failed.has(l.name) || caller.includes(l))
      // (only callers fail: drop nothing more, give up)
      if (next.length === set.length) return {proven: false, laws: set, m, why: `not proven: ${[...failed].join(', ')}`}
      // Instantiating a law does not mean the proof used it. Replay only the
      // recorded premise scope, against the exact reduced row layout, without
      // solving again. Missing premises and failed checks reopen the attempt.
      carried = new Map()
      if (!scopeEnabled) {
        const dropped = set.filter(l => !next.includes(l))
        carried = new Map([...proofs].filter(([, pr]) => dropped.every(d => d.forall && !pr.instances[d.name]?.length)))
      } else for (const name of proofs.keys()) {
        const scoped = scopes.get(name)
        const replayed = scoped && ptime('premise-replay', () => replayScopedCountProof(m, next, scoped, until, {deferToClosing: finalCountStepDeferralEnabled()}))
        countsDump.on?.({phase: 'premise-replay', law: name, round, retained: !!replayed, premises: scoped?.premises.map(p => p.name)})
        if (replayed) carried.set(name, replayed)
        else scopes.delete(name)
      }
      set = next
    }
    return {proven: false, laws: set, m, why: 'time'}
  }
  // Flags off retain the exact pre-scoping dependency/carry algorithm.
  const dependencies=(owner:Law,proof:Proof,context:Law[]):Set<string>=>{
    const conservative=()=>new Set(context.filter(l=>!l.forall||proof.instances[l.name]?.length).map(l=>l.name)),used=new Set<string>()
    for(const {goal,decls}of countedObligations(m,context,{[owner.name]:proof.instances},context.indexOf(owner))){
      const cert=proof.certs[goal.name]
      if(!cert)return conservative()
      const expanded=mcGoal(goal.hyps,decls,cert),refs=expanded&&countedCertificateHyps(expanded,cert)
      if(!refs)return conservative()
      for(const index of refs)if(index<goal.hyps.length)used.add(json(goal.hyps[index]))
    }
    return new Set(context.filter(l=>assumed([l],proof.instances).some(h=>used.has(json(h)))).map(l=>l.name))
  }
  const legacyDemand=():Counted=>{
    const known=new Map<string,{proof:Proof,context:Law[],deps:Set<string>}>()
    attempts.houdini=true
    while(clock()<until){
      if(!activeSupport(set,support))return join()
      const required=new Set(caller.map(l=>l.name)),available=new Set(set.map(l=>l.name))
      for(const name of required){const saved=known.get(name);if(saved)for(const dep of saved.deps)if(available.has(dep))required.add(dep)}
      const law=supportOrder(set,caller,support,false,env.GDP_COUNT_STRATEGIES==='1'?m:undefined).find(l=>required.has(l.name)&&!known.has(l.name))
      if(!law){
        const kept=set.filter(l=>required.has(l.name)),instances:Record<string,Instances>={},certs:Record<string,CountCert>={}
        for(const l of kept){
          const saved=known.get(l.name)!
          instances[l.name]=saved.proof.instances
          const src=countedObligations(m,saved.context,{[l.name]:saved.proof.instances},saved.context.indexOf(l)),dst=countedObligations(m,kept,{[l.name]:saved.proof.instances},kept.indexOf(l))
          for(let i=0;i<dst.length;i++){
            const cert=saved.proof.certs[src[i]!.goal.name]
            if(!cert)return join()
            const a=mcGoal(src[i]!.goal.hyps,src[i]!.decls,cert),b=mcGoal(dst[i]!.goal.hyps,dst[i]!.decls,cert),lifted=a&&b&&transportCountCertificate(a,b,cert,wallAt())
            if(!lifted)return join()
            certs[dst[i]!.goal.name]=lifted
          }
        }
        return finish(kept,{instances,certs})
      }
      const remaining=until-clock(),share=remaining/Math.max(1,set.length-known.size),allotted=supportBudget(remaining,share,caller.includes(law),support.has(law)&&!caller.includes(law)),stop=Math.min(until,clock()+Math.min(allotted,5000)),wall=countedSearchNow()+4800
      const countFirst=env.GDP_COUNTS_COUNT_FIRST!=='0'&&(reads(law.holds,isCount).size>0||!!law.keys?.length)
      const ask=(context:Law[]):Tried<Proof>=>withWall(wall,()=>withDeadline(stop,()=>{
        const pass:0|1=countFirst?1:0
        let result=traced(law,context,pass,Math.min(allotted,Math.max(0,stop-clock())))
        if(!('proof'in result)&&!result.refuted&&(countFirst||attempts.counted)&&clock()<stop)result=traced(law,context,pass?0:1,Math.min(allotted,Math.max(0,stop-clock())))
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
  const demand=():Counted=>{
    const known=new Map<string,ScopedCountProof>()
    attempts.houdini=true
    while(clock()<until){
      if(!activeSupport(set,support))return join()
      const required=new Set(caller.map(l=>l.name)),available=new Set(set.map(l=>l.name))
      for(const name of required){const saved=known.get(name);if(saved)for(const dep of saved.premises)if(available.has(dep.name))required.add(dep.name)}
      const law=supportOrder(set,caller,support,false,env.GDP_COUNT_STRATEGIES==='1'?m:undefined).find(l=>required.has(l.name)&&!known.has(l.name))
      if(!law){
        const kept=set.filter(l=>required.has(l.name)),instances:Record<string,Instances>={},certs:Record<string,CountCert>={},premises:Record<string,readonly string[]>={}
        for(const l of kept){
          const replayed=ptime('premise-replay',()=>replayScopedCountProof(m,kept,known.get(l.name)!,until,{deferToClosing:finalCountStepDeferralEnabled()}))
          if(!replayed)return join()
          instances[l.name]=replayed.instances
          premises[l.name]=replayed.premises??[]
          Object.assign(certs,replayed.certs)
        }
        return finish(kept,{instances,certs,premises})
      }
      const remaining=until-clock(),share=remaining/Math.max(1,set.length-known.size),allotted=supportBudget(remaining,share,caller.includes(law),support.has(law)&&!caller.includes(law)),stop=Math.min(until,clock()+Math.min(allotted,5000))
      const countFirst=firstCountPass(m,law,env.GDP_COUNTS_COUNT_FIRST!=='0'&&(reads(law.holds,isCount).size>0||!!law.keys?.length))===1
      const ask=(context:Law[]):Tried<Proof>=>withDeadline(stop,()=>{
        const pass:0|1=countFirst?1:0
        let result=traced(law,context,pass,Math.min(allotted,Math.max(0,stop-clock())))
        if(!('proof'in result)&&!result.refuted&&(countFirst||attempts.counted)&&clock()<stop)result=traced(law,context,pass?0:1,Math.min(allotted,Math.max(0,stop-clock())))
        return result
      })
      let context=coarseContext(m,set,[...caller,law],support),result=ask(context)
      if(!('proof'in result)&&context.length<set.length&&clock()<stop){context=set;result=ask(context)}
      countsDump.on?.({phase:'demand-attempt',law:law.name,context:context.length,required:required.size,known:known.size,outcome:'proof'in result?'proof':result.stuck})
      if('proof'in result){
        const scoped=ptime('premise-scope',()=>scopeCountProof(m,law,context,result.proof,until))
        if(!scoped)return join()
        known.set(law.name,scoped);continue
      }
      if(caller.includes(law))return join()
      set=set.filter(l=>l!==law)
      for(const [name,saved]of known)if(saved.premises.some(p=>p.name===law.name))known.delete(name)
    }
    return {proven:false,laws:set,m,why:'time'}
  }
  return prerequisiteFirst ? proofGuided&&completeWorkProfile.enabled?recipeJoint():joint() : budget ? join() : activeSupport(set,support) ? scopeEnabled ? demand() : legacyDemand() : join()
}

type Proof = CountLawProof
// The production attempt also serves the fixed-family research replay. Candidate
// generation and scheduling stay outside; inference, selection, reservation and
// all budget checks have exactly one implementation.
export function countedAttempts(m: Machine, caller: Law[], support: Set<Law>, until: number, structured = true, focusedOrStrategies: boolean | ReadonlySet<Law> = true, budgetOrWork?: CountTierBudget | number, tierBudget?: CountTierBudget, shapeFamily?: readonly Law[]) {
  // Preserve I's boolean/tier API and B's explicit strategy-set/work API.
  const allowFocused = typeof focusedOrStrategies === 'boolean' ? focusedOrStrategies : true
  const strategyOnly = typeof focusedOrStrategies === 'boolean' ? new Set<Law>() : focusedOrStrategies
  const tiers = typeof budgetOrWork === 'number' ? tierBudget : budgetOrWork
  const workAllowance = typeof budgetOrWork === 'number' ? budgetOrWork : tiers?.workAllowance ?? Math.max(0, until - clock())
  // Capture the enclosing phase before entering any per-law or subset share.
  const enclosingEnd = withinDeadline(until)
  // (the law's own names and the request's values that key a map: an action's value keys none)
  const keys0 = [...[...reads([m.step, m.assume ?? null], () => true).values()].map(([, key]) => key), ...Object.values(m.step.maps ?? {}).flatMap(w => ('each' in w ? [] : [w.key]))]
  const keyed = m.inputs.filter(i => keys0.some(key => mentions(key, i))).map(v)
  const terms = (l: Law): E[] => [...(l.forall ? [v(`${l.forall}#`)] : []), ...(l.keys ?? []).map(v), ...keyed]
  type Proof = CountLawProof
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
  const models = new Map<string, {gg: Goal, w: Record<string, number>, at: Instances, ls: Set<string>, wits?: string[]}>(), isCount = (mp: string) => !!m.counts?.[mp]
  // Cone tiers and Houdini may ask the same law again with more instances. Keep a
  // bounded set of sessions; each independently resets unless its hypotheses are
  // still present verbatim. This reuses work, never a verdict from a weaker goal.
  const decisions = new Map<string, ReturnType<typeof modelSequence>>(), focusEnabled=allowFocused&&focusedCountRecoveryEnabled(m)
  // Opt-in until the fixed-operation census and preservation gate have been qualified.
  const frameChoice=env.GDP_COUNT_FRAMES==='1'?fixedCountFrameCase(m):undefined
  // Scheduling history only, never a cached verdict. A different family must
  // earn its own ordinary attempts before using the finite recovery search.
  const plainFailures = new WeakMap<Law, WeakSet<Law[]>>()

  let finite: ReturnType<typeof finiteModelChecker> | undefined
  const ordinaryAttempt = (law: Law, ls: Law[], pass: 0 | 1, ms: number, attemptEnd: number, defer: (recover: () => Proof | undefined) => void): Tried<Proof> => {
    // A cached model can return before the no-count optimization below. A helper
    // without count reads must not suppress the next law's counting-lemma pass.
    if (!pass) counted = true
    const ts = terms(law), id = `${pass} ${law.name}`, cti = models.get(id)
    const supported = ls.some(l => support.has(l)), modelLaws = supportOrder(ls, caller, support, true)
    let memberState: ReturnType<typeof memberPremiseState> | undefined
    const members = () => memberState ??= memberPremiseState([m,ls])
    // A source predicate may be instantiated at a count witness, but no
    // count-read key may depend on that same witness (checkMC freshness).
    const independent = (before: Instances, next: Instances | undefined, wits: string[] = []) => {
      if(!next)return undefined
      const blocked=[...memberState?.witnesses.values()??[],...cti?.wits??[]]
      return blocked.length?independentCountInstances(m,modelLaws,before,next,[...blocked,...wits]):next
    }
    // Try ordinary counted reasoning before finite recovery when the plain
    // pass needs counts. Keep the no-count fallback and the existing wide-pool
    // recovery, using only the current attempt's remaining allowance.
    if (focusEnabled && m.inputMaps?.length && !reads(law.holds, isCount).size && (!pass || plainFailures.get(law)?.has(ls))) {
      defer(() => ptime('focused', () => proveFocusedCounts(m, ls, law, {}, Math.min(attemptEnd, clock() + Math.min(ms, 5000)), (g, ds) => certFor(g, ds, true, pool, undefined, structured))))
    }
    // (the model broken: the attempt starts at the instances it asks for, its last attempt's and the tuples the new laws
    // break it at, where the rounds of models would lead it again)
    let seed: Instances | undefined
    const refuted = (gg: Goal, w: Record<string, number>, instances: Instances): Tried<Proof> => {
      const completion = (finite ??= finiteModelChecker(m))(ls, law, w, () => clock() >= attemptEnd)
      countsDump.on?.({phase: 'finite-model', law: law.name, pass, completion})
      if (env.GDP_COUNTS_DUMP_ALL_PASSES === '1') countsDump.on?.({phase: completion.genuine ? 'final-sat' : 'uncertified-model', stuck: completion.genuine || !pass ? 'sat' : 'unknown', law: law.name, pass, machine: m, laws: ls, goal: gg, witness: w, at: instances})
      models.set(id, {gg, w, at: instances, ls: new Set(ls.map(l => l.name)), wits:[...memberState?.witnesses.values()??[],...cti?.wits??[]]})
      return completion.genuine ? {stuck: 'sat', refuted: true} : {stuck: pass ? 'unknown' : 'sat'}
    }
    // (not where the attempt may widen: its narrow model is no model of the widened goal)
    if (cti && !(tiers?.active && ls.some(l => !cti.ls.has(l.name))) && !(supported && pass) && !(houdini && caller.some(l => l.name === law.name) && !widened.has(law.name)) && !ls.some(l => !cti.ls.has(l.name) && reads(l.holds, isCount).size)) {
      const at0 = Object.fromEntries(Object.entries(cti.at).filter(([n]) => n.startsWith('?') || ls.some(l => l.name === n)))
      if (!(seed = ptime('mbqi', () => independent(at0,modelInstances(m, modelLaws, at0, cti.gg, cti.w))))) return refuted(cti.gg, cti.w, cti.at)
    }
    // Supported obligations seed quantified flags only at demanded source terms.
    // Ordinary MBQI remains the fallback; arbitrary inputs are not initial witnesses.
    let at: Instances = seed ?? (supported ? {} : Object.fromEntries(Object.entries(m.step.flags ?? {}).flatMap(([f, q]) => (q.op === 'all' && !q.keys?.length ? [[`?${f}`, ts]] : []))))
    if(pass&&frameChoice&&ls.includes(law)&&reads(law.holds,isCount).size)at=ownCountLawInstance(law,at)
    const obligations = (i: Instances) => ptime('encode', () => countedObligations(m, ls, {[law.name]: i}, ls.indexOf(law)))
    // A fixed-operation frame proof needs only the ordinary own-key premise.
    // Try it before count-pool construction. INIT is still a separate obligation:
    // its zero counts need ordinary unary witnesses, absent from a narrow pool
    // containing only post-state reads. Neither its truth nor its proof is assumed.
    if (pass && frameChoice && ls.includes(law) && reads(law.holds, isCount).size) {
      const end = Math.min(attemptEnd, clock() + Math.min(ms, 500))
      try {
        const early = ptime('frames', () => withDeadline(end, (): Proof | undefined => {
          const packets = obligations(at), step = packets.at(-1)
          if (!step) return
          const more = () => clock() < end
          const request = certFor(step.goal, step.decls, false, 0, more, structured)
          const maps = new Set([...reads(law.holds, isCount).values()].map(([map]) => map))
          const cert = proveCountFrameGoal(step.goal, step.decls, request, frameChoice, maps, end, cut => countsDump.on?.({phase: 'count-cut', law: law.name, goal: step.goal.name, pass, ...cut}))
          if (!cert) return
          const emit = (p: typeof step, c: CountCert, phase: string) => countsDump.on?.({law: law.name, goal: p.goal.name, pass, phase, rawGoal: p.goal, decls: p.decls, instances: at, certificateRequest: c, hyps: mcGoal(p.goal.hyps, p.decls, c)?.hyps})
          emit(step, cert, 'frame-proven')
          const certs: Record<string, CountCert> = {[step.goal.name]: cert}
          for (const initial of packets.slice(0, -1)) {
            const request = certFor(initial.goal, initial.decls, true, 24, more, structured)
            const gg = mcGoal(initial.goal.hyps, initial.decls, request)
            const out = gg && grow(gg, new Map(), {nodes: 0, until: end})
            if (!out || !('tree' in out)) return
            const c: CountCert = {reads: request.reads, insts: request.insts, picks: request.picks, tree: out.tree}
            if (!checkMC(initial.goal.hyps, initial.decls, c)) return
            emit(initial, c, 'frame-start-proven')
            certs[initial.goal.name] = c
          }
          return {instances: at, certs}
        }))
        if (early) return {proof: early}
      } catch (error) {
        if (!(error instanceof WallExpired) || clock() >= attemptEnd) throw error
      }
    }

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
    const memberSources = new Map<string,MemberHint[]>()
    // Demand-driven ranges (Fable b89dd77a / Lane B): retain a goal's demand
    // across rebuilds, without crowding out ordinary member inclusions.
    // Every proposed range remains an ordinary kernel-checked count instance.
    const rangeWanted = new Map<string, Set<string>>()
    const withRanges = <T extends Pick<CountCert, 'reads' | 'insts' | 'picks'> & {wits?: string[]}>(goal: Goal, decls: CountDecl[], c: T, all: MapRead[]): T => {
      const wanted = rangeWanted.get(goal.name)
      if (!pass || !wanted?.size) return c
      const taken = new Set<string>([...all.map(r => r[0]), ...c.insts.map(i => i.wit), ...m.params, ...m.inputs, ...Object.keys(m.state)])
      const ranges = rangeInstances(decls, all.filter(r => wanted.has(r[0])), taken, c.insts)
      if (!ranges.length) return c
      const have = new Set(c.reads.map(r => r[0])), named = new Set(ranges.map(i => i.terms[0]![1]))
      const reads = [...c.reads, ...all.filter(r => !have.has(r[0]) && named.has(r[0]))]
      return {...c, reads, insts: [...c.insts, ...ranges], ...(c.wits ? {wits: [...c.wits, ...ranges.map(i => i.wit)]} : {})}
    }
    // (a model that puts a read's count above its bound: those reads' ranges wanted from now on; whether any is new)
    const wantRanges = (goal: Goal, decls: CountDecl[], all: MapRead[], w: Record<string, number>): boolean => {
      let set = rangeWanted.get(goal.name)
      if (!set) rangeWanted.set(goal.name, (set = new Set()))
      let grew = false
      for (const read of rangeViolations(decls, all, w)) if (!set.has(read[0])) { set.add(read[0]); grew = true }
      return grew
    }
    const rawBuild = () => obligations(at).map(({goal, decls}) => {
      if (pass && supported && lazyMode === 'wide') {
        if (generation.state.deadline || countedSearchNow() >= wallAt()) throw new UnsupportedCountProposal('reservation deadline')
        let selection = selections.get(goal.name)
        const reservation = selection && reservationReadClosure(goal, decls, selection.previous, selection.decls, selection.chosen, [...m.params, ...m.inputs, ...Object.keys(m.state)])
        // Primitive PRE instances cannot introduce another count read. Reuse
        // the proposal pool while only those instances grow; retained picks
        // are still reified against this goal, and additional picks may wait
        // for failure-driven widening. This caches proposals, never a proof.
        const key = countPoolKey(goal, decls)
        const cached = poolCache.get(goal.name)
        const pool0 = cached?.key === key ? cached.value : grammarPool(goal, decls, pool, generation, structured, m)
        if (cached?.key !== key) poolCache.set(goal.name, {key, value: pool0})
        if (!selection) {
          const ordinary = readTuples(goal.hyps.at(-1), generation.tick).some(([mp]) => mp.endsWith('#') && decls.some(d => d.map === mp))
            ? polaritySelection(goal, decls, pool0, generation, sourceMaps).pick
            : smallSelection(goal, decls, pool0.full, readTuples(law.holds, generation.tick).map(([, key]) => key), none, generation)
          const pick = preferMemberInclusions(m, decls, pool0.full, ordinary, 10, generation.tick)
          selection = {chosen: new Set(ids(pick)), cap: Math.min(10, pick.insts.length + 2), previous: pick, decls, reserve: reservationState(goal, [m, ls, goal], pool), stable: stableState([m, ls, goal])}
          selections.set(goal.name, selection)
        }
        const full = reservePool(goal, decls, pool0, selection.previous, selection.decls, selection.chosen, selection.reserve, pool, reservation).full
        const keys = ids(full), lazyRoom = selection.chosen.size < selection.cap
        const view = chosenView(full, selection.chosen, selection.cap)
        const c = withRanges(goal, decls, selectedCertificate(goal, decls, view, selection.stable, lazyRoom), full.reads)
        const gg = mcGoal(goal.hyps, decls, c), fg = lazyRoom ? mcGoal(goal.hyps, decls, full) : undefined
        selection.previous = full; selection.decls = decls
        memberSources.set(goal.name,memberHints(m,decls,c,generation.tick))
        return {goal, decls, c, gg, all: full.reads, pool: fg ? {fg, keys, wits: [...full.picks.map(() => undefined), ...full.insts.map(i => i.wit)], chosen: selection.chosen, cap: selection.cap} as Pool : undefined}
      }
      let full = pass ? certFor(goal, decls, wide, wide && lazyMode !== '0' ? pool : undefined, undefined, structured) : none
      if(pass&&m.inputMaps?.length&&lazyMode!=='0'){
        const proposed=admitMemberWitnesses(m,decls,full,members(),wide?pool:10,generation.tick)
        full=proposed.cert;memberSources.set(goal.name,proposed.hints)
      }
      if (!pass || lazyMode === '0' || (lazyMode === 'wide' && !wide)) { const c0 = withRanges(goal, decls, full, full.reads); return {goal, decls, c: c0, gg: ptime('encode', () => mcGoal(goal.hyps, decls, c0)), all: full.reads, pool: undefined as Pool | undefined} }
      const rd = new Map(full.reads.map(r => [r[0], json([r[1], r[2]])]))
      const keys = [...full.picks.map(q => `p${json([rd.get(q[0]), q[1]])}`), ...full.insts.map(i => `i${json([i.terms.map(([z, x]) => [z, rd.get(x)]), i.unit, i.below])}`)]
      if (lazyMode === 'wide') {
        const prefix = {...full, picks: [], insts: full.insts.slice(0, 10)}
        const initial = memberSources.get(goal.name)?.length ? prefix : preferMemberInclusions(m, decls, full, prefix, 10, generation.tick)
        for (const inst of initial.insts) chosen.add(keys[full.picks.length + full.insts.indexOf(inst)]!)
      }
      const c = withRanges(goal, decls, {...full, picks: full.picks.filter((_, j) => chosen.has(keys[j]!)), insts: full.insts.filter((_, j) => chosen.has(keys[j + full.picks.length]!))}, full.reads)
      const fg = ptime('encode', () => mcGoal(goal.hyps, decls, full))
      return {goal, decls, c, gg: ptime('encode', () => mcGoal(goal.hyps, decls, c)), all: full.reads, pool: fg && keys.length ? {fg, keys, wits: [...full.picks.map(() => undefined), ...full.insts.map(i => i.wit)]} : undefined}
    })
    let lastSignature = ''
    const build = () => {
      let built = rawBuild()
      if(pass)while(seedCount<64&&clock()<attemptEnd){
        const step=built.at(-1),hints=step&&memberSources.get(step.goal.name)
        if(!step||!hints?.length)break
        // Seed declaration-backed member flags first. Scalar law tuples stay
        // model-driven rather than crowding the initial goal with field bridges.
        const seeded=instantiateMemberPremises(m,[],at,step.decls,hints,members(),64-seedCount,generation.tick)
        if(!seeded.added.length)break
        at=seeded.at;seedCount+=seeded.added.length
        countsDump.on?.({phase:'member-premises',law:law.name,goal:step.goal.name,pass,added:seeded.added})
        built=rawBuild()
      }
      if (pass && supported) while (seedCount < 64 && clock() < attemptEnd) {
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
      const {fg, keys, wits} = b.pool, active = b.pool.chosen ?? chosen, base = fg.hyps.length - keys.length, ids = keys.flatMap((q, j) => (active.has(q) ? [] : [base + j])), rawJudge = brokenOf(fg), judge = (...args: Parameters<typeof rawJudge>) => withEvaluationAdmission(() => rawJudge(...args))
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
    // Complete only assumptions about count maps the requested law reads.
    // Unrelated count laws keep their ordinary demand-driven instantiation.
    const completionMaps = new Set([...reads(law.holds, isCount).values()].map(([map]) => map))
    let countCompleted = false
    const completeCounts = (): boolean => {
      if (!pass || countCompleted || !completionMaps.size) return false
      countCompleted = true
      const completion = completeCountLawInstances(modelLaws, at, ts, l => reads(l.holds, map => completionMaps.has(map)).size > 0, generation.tick)
      if (!completion.added.length) return false
      at = completion.at
      tally('#count-completion', completion.added.length)
      countsDump.on?.({law: law.name, pass, phase: 'count-completion', added: completion.added})
      return true
    }
    // A single-key clause mixing field and count reads can need count premises now.
    // Concrete goals and isolated or multi-key count targets stay sparse-first:
    // speculative self-instances can crowd out an already easy proof.
    if (pass && law.forall && !law.keys?.length && completionMaps.size &&
        reads(law.holds, map => !isCount(map)).size && [...completionMaps].every(map => !m.counts![map]!.lo) &&
        modelLaws.some(other => other.name !== law.name && reads(other.holds, map => completionMaps.has(map)).size)) completeCounts()
    // Stuck-model paths retain the same bounded completion and attempt allowance.
    let built = build()
    const observe = (b: ReturnType<typeof build>[number], phase: string, witness?: Record<string, number>) => {
      if (countsDump.on) countsDump.on({law: law.name, goal: b.goal.name, pass, phase, generation: {...generation.state}, machine: m, laws: ls, rawGoal: b.goal, decls: b.decls, instances: at, certificateRequest: b.c, hyps: b.gg?.hyps, witness, seedCount})
    }
    let decideStep = decisions.get(id)
    if (!decideStep) {
      if (decisions.size >= 64) decisions.delete(decisions.keys().next().value!)
      decisions.set(id, (decideStep = modelSequence()))
    }
    const more = () => clock() < attemptEnd
    // The step goal decided first by the CDCL search for a model (its phases the simplex's point: a model is met where the
    // tree search would split on), within the attempt's remaining allowance:
    //   - refuted: the law's instances cut to those its core reads, and the core's hypotheses grown on their own first,
    //     the tree widened to the goal;
    //   - a model: the instances it asks for (kernel/prove.ts's modelInstances, MBQI: a law or quantified flag broken at a
    //     tuple of the goal's own keys), the goals made again with them; none asked, the goal has a model and is given
    //     up at once (no tree to grow); the rounds within the attempt's time (a second at least, as the kernel's
    //     withModels gives its later rounds), past which the goal is unknown;
    //   - unknown: the goals grown as they are.
    let preflighted = false
    for (;;) {
      checkWall('counted refinement')
      if (!more()) return {stuck: 'unknown'}
      let part: {gg: Goal, core: Goal} | undefined
      let direct: {gg: Goal, tree: CountCert['tree']} | undefined
      for (;;) {
        checkWall('counted model loop')
        if (!more()) return {stuck: 'unknown'}
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
        const q0 = clock(), q = ptime('decide', () => decideStep(step.gg!, attemptEnd))
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
          // Replay changes the goal, not its proposal pool or complete read set.
          const beforeReplay = built
          built = obligations(at).map(({goal, decls}, j) => ({...built[j]!, goal, decls, gg: mcGoal(goal.hyps, decls, built[j]!.c)}))
          countsDump.on?.({phase: 'core-replay', law: law.name, pass,
            readCount: beforeReplay.at(-1)!.all.length,
            readsRetained: built.every((b, j) => b.all === beforeReplay[j]!.all),
            poolsRetained: built.every((b, j) => b.pool === beforeReplay[j]!.pool),
            certificatesRetained: built.every((b, j) => b.c === beforeReplay[j]!.c)})
          part = {gg: built.at(-1)!.gg!, core: {name: gg.name, hyps: (q.core.includes(last) ? q.core : [...q.core, last]).map(h => gg.hyps[h]!)}}
          break
        }
        if (q.stuck !== 'sat' || !q.witness) break
        observe(step, 'model', q.witness)
        if (!more()) return {stuck: 'unknown'}
        const asked = ptime('mbqi', () => independent(at,modelInstances(m, modelLaws, at, step.gg!, q.witness!),step.c.insts.map(i=>i.wit))), lz = breaks(step, q.witness) || (!asked && breaks(step, q.witness, true))
        tally('#rounds'); tally('#hyps', step.gg.hyps.length)
        // (a model with a count above its bound: that count's range instance from now on, the goal made again)
        const ranged = pass && wantRanges(step.goal, step.decls, step.all, q.witness)
        if ((lz || ranged) && !asked) { built = build(); continue }
        if (!asked) {
          if (completeCounts()) { built = build(); continue }
          if (countsDump.on && (pass || env.GDP_COUNTS_DUMP_ALL_PASSES === '1') && dumped < Number(env.GDP_COUNTS_DUMP_N ?? 3)) { dumped++; countsDump.on({law: law.name, goal: step.goal.name, ls: ls.map(l => l.name), stuck: 'sat', witness: q.witness, reads: step.c.reads, insts: step.c.insts, hyps: step.gg.hyps, base: step.goal, decls: step.decls, cert: step.c, at, laws: ls, wide, pass}) }
          if (pass && !wide && houdini && 'loose' in step.c && (step.c.loose || isCaller) && more()) { wide = true; widened.add(law.name); built = build(); continue }
          return refuted(step.gg, q.witness, at)
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
          const o1 = grow(part!.core, new Map(), {nodes: 0, until: attemptEnd}), w = 'tree' in o1 ? widen(part!.core, gg, o1.tree) : undefined
          return w ? {tree: w, nodes: 0} : undefined
        }) : undefined
        const o = (direct && direct.gg === gg ? {tree: direct.tree, nodes: 0} : undefined) ?? viaPart ?? (gg && ptime(`grow${(gg.hyps.length > 300 ? '>300' : '')}`, () => grow(gg, new Map(), {nodes: 0, until: attemptEnd})))
        if (gg && o && !('tree' in o)) observe(built.find(b => b.gg === gg)!, o.stuck, 'witness' in o ? o.witness : undefined)
        if (countsDump.on && gg && o && !('tree' in o) && gg.hyps.length > Number(env.GDP_COUNTS_DUMP_MIN ?? 300) && dumped < Number(env.GDP_COUNTS_DUMP_N ?? 3)) { dumped++; countsDump.on({law: law.name, goal: goal.name, ls: ls.map(l => l.name), stuck: (o as {stuck?: string}).stuck, hyps: gg.hyps, base: goal, decls, cert: c, at, laws: ls, wide, pass, ...('witness' in o ? {witness: o.witness} : {})}) }
        if (env.GDP_COUNTS_TRACE?.includes('2')) console.error(`counts: ${ls.length === 1 ? 'alone' : `with ${ls.length}`} ${pass} ${goal.name}: ${o && 'tree' in o ? 'proven' : gg ? (o as {stuck?: string}).stuck : 'no read'} ${gg?.hyps.length ?? 0} hyps (insts ${'insts' in c ? c.insts.length : 0} picks ${'picks' in c ? c.picks.length : 0}${wide ? ' wide' : ''}${built.find(b => b.gg === gg)?.pool ? ` of ${built.find(b => b.gg === gg)!.pool!.keys.length}` : ''}) ${Math.round(clock() - t0)} ms`)
        // (the tree search's model of the step goal: the instances it asks for, as the CDCL search's, and the goals again)
        if (gg && o && !('tree' in o) && o.stuck === 'sat' && o.witness && gg === built.at(-1)!.gg && more()) {
          const last = built.at(-1)!, asked = ptime('mbqi', () => independent(at,modelInstances(m, modelLaws, at, gg, o.witness!),c.insts.map(i=>i.wit))), lz = breaks(last, o.witness) || (!asked && breaks(last, o.witness, true))
          const ranged = pass && wantRanges(last.goal, last.decls, last.all, o.witness)
          if (asked || lz || ranged) { if (asked) at = asked; built = build(); again = true; break }
          if (completeCounts()) { built = build(); again = true; break }
        }
        if (gg && o && !('tree' in o) && o.stuck === 'sat' && o.witness && gg === built.at(-1)!.gg && pass && !wide && houdini && 'loose' in c && (c.loose || isCaller) && more()) { wide = true; widened.add(law.name); built = build(); again = true; break }
        if (gg && o && !('tree' in o) && o.stuck === 'sat' && o.witness && gg === built.at(-1)!.gg) return refuted(gg, o.witness, at)
        if (!o || !('tree' in o)) return {stuck: gg ? (o as {stuck?: string}).stuck ?? '' : ''}
        certs[goal.name] = {reads: c.reads, insts: c.insts, tree: o.tree, ...('picks' in c && c.picks.length ? {picks: c.picks} : {})}
      }
      if (!again) return {proof: {instances: at, certs}}
    }
  }
  const attempt = (law: Law, ls: Law[], pass: 0 | 1, ms: number, strategyAllowed = true): Tried<Proof> => {
    const end = Math.min(until, clock() + ms)
    const result = withDeadline(end, (): Tried<Proof> => {
      let remaining = ms
      if (strategyAllowed && !pass && env.GDP_COUNT_STRATEGIES === '1' && (!strategyOnly.size || strategyOnly.has(law))) {
        const proof = ptime('strategies', () => (tiers?.active && finalCountStepDeferralEnabled() ? proposeCountStrategiesForClosing : proveCountStrategies)(m, ls, law, end,
          (goal, decls) => certFor(goal, decls, false, 0, () => clock() < end, structured),
          event => countsDump.on?.({phase: 'count-strategy', law: law.name, pass, end, ...event}), workAllowance, shapeFamily))
        countsDump.on?.({phase: 'count-strategy-result', law: law.name, pass, end, checked: !!proof && proof.status !== 'unchecked', ...(proof?.status === 'unchecked' ? {proposed: true, status: 'unchecked'} : {})})
        if (proof) return {proof}
        if (strategyOnly.has(law)) return {stuck: 'strategy declined'}
        remaining = Math.max(0, end - clock())
        if (!remaining) return {stuck: 'unknown'}
      }
      return withDeferredCountRecovery<Proof>(end,
        defer => ordinaryAttempt(law, ls, pass, remaining, end, defer), () => !!pass || !counted)
    })
    if (!pass) {
      const failures = plainFailures.get(law) ?? new WeakSet<Law[]>()
      if (!('proof' in result) && !result.refuted) failures.add(ls)
      else failures.delete(ls)
      plainFailures.set(law, failures)
    }
    return result
  }
  const traced = (law: Law, ls: Law[], pass: 0 | 1, ms: number, strategyAllowed = true): Tried<Proof> => {
    const t0 = clock(), w0 = countedSearchNow(), p0 = {...cprof}
    let r: Tried<Proof>
    try {
      const end = Math.min(until, clock() + ms)
      if (tiers?.active) {
        r = countPremiseSearch(ls, end,
          localEnd => [false, true].flatMap(guardReads => {
            const context = countPremiseContext(m, ls, law, localEnd, guardReads)
            return context ? [context] : []
          }),
          (local, probeEnd) => attempt(law, local, pass, Math.max(0, probeEnd - clock()), strategyAllowed),
          (context, proposed, localEnd) => {
            if (!('proof' in proposed)) return
            const localGoals = countedObligations(m, context.laws, {[law.name]: proposed.proof.instances}, context.laws.indexOf(law))
            const wholeGoals = countedObligations(m, ls, {[law.name]: proposed.proof.instances}, ls.indexOf(law))
            if (localGoals.length !== wholeGoals.length) return
            const certs: Record<string, CountCert> = {}
            for (let i = 0; i < wholeGoals.length; i++) {
              const part = localGoals[i]!, whole = wholeGoals[i]!, cert = proposed.proof.certs[part.goal.name]
              if (!cert || clock() >= localEnd) return
              const from = mcGoal(part.goal.hyps, part.decls, cert), to = mcGoal(whole.goal.hyps, whole.decls, cert)
              const lifted = from && to && transportCountCertificate(from, to, cert, wallAt())
              if (!lifted || (!(finalCountStepDeferralEnabled() && proposed.proof.status === 'unchecked') && !checkMC(whole.goal.hyps, whole.decls, lifted))) return
              certs[whole.goal.name] = lifted
            }
            return {proof: {instances: proposed.proof.instances, certs, ...(proposed.proof.status === 'unchecked' ? {status: 'unchecked' as const} : {})}}
          },
          event => countsDump.on?.({...event, law: law.name, pass}),
          error => error instanceof UnsupportedCountProposal)
      } else {
      // Probe only strict subsets, within the existing attempt's allowance. A
      // subset model is not a verdict: failure always widens to the full set.
      // Kept certificates must be lifted to that full set's exact row layout.
      const focused = pass && ls.some(l=>support.has(l)) && (reads(law.holds,isCount).size || !caller.includes(law) && !!law.keys?.length) ? sourceContext(m,ls,law,support) : ls
      const contexts = [...(focused.length<ls.length ? [{local:focused,fraction:1,kind:'source-context'}] : []), ...(env.GDP_COUNTS_RELEVANCE==='1'?relevantLaws(m,ls,law,support).map(local=>({local,fraction:1/6,kind:'relevance'})):[])]
      for (const {local,fraction,kind} of contexts) {
        const slice = Math.max(0, Math.min(ms * fraction, end - clock()))
        if (!slice) break
        let probe: Tried<Proof>
        try { probe = withDeadline(clock() + slice, () => attempt(law, local, pass, slice, strategyAllowed)) } catch (error) {
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
          const lifted = pg && wg && withDeadline(end, () => transportCountCertificate(pg,wg,c,wallAt()))
          if (!lifted) { complete = false; break }
          if(!checkMC(whole.goal.hyps,whole.decls,lifted)){complete=false;break}
          certs[whole.goal.name] = lifted
        }
        if (complete) {
          r = {proof: {instances: probe.proof.instances, certs}}
          countsDump.on?.({phase: kind+'-proof', law: law.name, local: local.length, whole: ls.length})
          return r
        }
      }
      r = attempt(law, ls, pass, Math.max(0, end - clock()), strategyAllowed)
      }
    } catch (error) {
      // A local tier deadline expires this attempt, not the whole enclosing search.
      // Invalid or captured proposals are likewise never assumptions.
      if (!(error instanceof UnsupportedCountProposal) && !(error instanceof WallExpired) && !(tiers?.active&&isLocalCountExpiration(error,enclosingEnd))) throw error
      countsDump.on?.({law: law.name, pass, phase: 'rejected proposal', error: String(error)})
      r = shapeFamily ? {stuck:'unknown',expired:error instanceof BudgetExpired,reason:String(error)} : {stuck:'unknown'}
    }
    if (env.GDP_COUNTS_TRACE?.includes('3')) console.error(`counts: try ${law.name.slice(0, 50)} | ls ${ls.length} pass ${pass} ms ${Math.round(ms)} took ${Math.round(clock() - t0)} wall ${Math.round(countedSearchNow() - w0)} [${Object.entries(cprof).filter(([k2, x]) => x - (p0[k2] ?? 0) >= 1).map(([k2, x]) => `${k2} ${Math.round(x - (p0[k2] ?? 0))}`).join(' ')}] -> ${'proof' in r ? 'kept' : r.stuck}`)
    return r
  }
  // One bounded non-lifted strategy recipe, without ordinary-search fallback.
  // The explicit lifted lease dispatcher intentionally rejects row/guard kinds.
  const strategyProposal = (law:Law,ls:Law[],kind:'row'|'guard') => {
    if (env.GDP_COUNT_STRATEGIES !== '1' || strategyOnly.size && !strategyOnly.has(law)) return undefined
    const end=withinDeadline(until)
    return ptime('strategies',()=> (tiers?.active&&finalCountStepDeferralEnabled()?proposeCountStrategyKindForClosing:proveCountStrategyKind)(kind,m,ls,law,end,
      (goal,decls)=>certFor(goal,decls,false,0,()=>clock()<end,structured),
      event=>countsDump.on?.({phase:'count-strategy',law:law.name,pass:0,...event}),workAllowance,shapeFamily))
  }
  // Explicit seam for the persistent section46 controller. The legacy traced
  // path remains unchanged; no plan is inferred from ms, clock or remaining work.
  const exactStrategy = (law:Law, ls:Law[], plan:LiftedWorkBudget) => {
    assertLiftedWorkLease(plan)
    if (env.GDP_COUNT_STRATEGIES !== '1' || strategyOnly.size && !strategyOnly.has(law)) return undefined
    return ptime('strategies', () => (tiers?.active && finalCountStepDeferralEnabled() ? proposeCountStrategiesForClosing : proveCountStrategies)(m, ls, law, Infinity,
      (goal, decls) => certFor(goal, decls, false, 0, () => true, structured),
      event => countsDump.on?.({phase:'count-strategy',law:law.name,pass:0,...event}), workAllowance, shapeFamily, plan))
  }
  return {traced, exactStrategy, strategyProposal, countermodel:(law:Law)=>models.get(`1 ${law.name}`)?.w??models.get(`0 ${law.name}`)?.w, get counted() { return counted }, set houdini(value: boolean) { houdini = value }}
}
