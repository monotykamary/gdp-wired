// gdp-wired/lean end to end: rules written with the builders, exported by toLean, laid out by leanProject, and built by
// `lake build` (modal/suite.json's lean-package job). Usage: bun package-check.ts <empty folder>
import {mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {bool, count, forall, loop, maybe, min, nat, oneOf, relation, rule, yes} from '../core/dsl.ts'
import {countdown, escrowLaws, escrowRunsLean, escrowSteps, escrowWatched, meter, meterRelation, twoPhase} from '../examples/composition.ts'
import {authority, authorityLaws, authorityPairs, authoritySteps, lazyAuthority, lazyRelation, lazyWitness} from '../examples/sets.ts'
import {childUse, childUseLaws, childUseSteps, inlineAuthority, inlineLaws, inlineSteps, memberLaws, memberSteps, members, normalForm, normalFormLaws, normalFormSteps} from '../examples/quantifiers.ts'
import {larger, largerLaws, minuteLaws, minutes, pairsLean, room, roomLaws} from '../examples/functions.ts'
import {bits, bitsLaws, scope, scopeLaws, scopeSteps} from '../examples/lists.ts'
import {accountLaws, accountSteps, accounts, approveLaws, hold, holdLaws, holdSteps, jobLaws, jobSteps, jobs, seatLaws, seatSteps, seats} from '../examples/datatypes.ts'
import {invoiceLaws, invoiceSteps, invoices, metered, meteredLaws} from '../examples/invoices.ts'
import {orgChart, orgChartLaws, rollup, rollupLaws, signoffLaws, signoffs} from '../examples/folds.ts'
import {searchTree, searchTreeLaws, sheet, sheetLaws} from '../examples/trees.ts'
import {distinctNames, distinctNamesLaws, sortedList, sortedListLaws} from '../examples/pairs.ts'
import {groupLaws, groups} from '../examples/groups.ts'
import {binding, bindingLaws, checkout, checkoutLaws, order, orderLaws} from '../examples/charts.ts'
import {xorder, xorderLaws} from '../examples/xstate.ts'
import {lease, leaseLaw, pool, poolLaw} from '../examples/infer.ts'
import {wide} from '../examples/wide.ts'
import {area, areaLaws, counter, counterLaws, escalation, escalationLaws, fillMeter, fillMeterLaws, ladder, ladderLaws, ledger, ledgerLaws, pump, pumpLive, retries, retryLaws, retrySteps, tank, tankLaws} from '../examples/lemmas.ts'
import {team, teamLaws, teamSteps} from '../examples/sizes.ts'
import {allDone, batchLaws, batches, everyTaggedTicket, taggedLaws, taggedTickets, everyLoggedTicket, everyRecountedTicket, everyReview, everyTicket, loggedLaws, loggedTickets, recounted, recountedLaws, reviewLaws, reviews, ticketLaws, tickets} from '../examples/liveness.ts'
import {areaLaws as foundAreaLaws, foundArea, foundInvoices, foundOrgChart, foundRetries, orgChart as bareOrgChart, orgChartLaws as bareOrgChartLaws, retryLaws as foundRetryLaws, retrySteps as foundRetrySteps} from '../examples/discover.ts'
import {grantLaws, normalizedLaws, patternLaws} from '../examples/scopes.ts'
import {leanProject, toLean} from './emit.ts'
import {foldNodes, machineNodes, proveCyclic, recurNodes} from '../core/cyclic.ts'
import {proveLaws} from '../kernel/prove.ts'
import type {Law, Machine} from '../core/machine.ts'
import type {Cyclic} from '../kernel/cyclic.ts'
import {budget, budgetLaws, fill, fillLaws, mccarthy, mutual, tally, tallyLaws} from '../examples/cyclic.ts'
import {leanItems as cycleLeanItems} from '../examples/cycles.ts'
import {filled, growing} from '../examples/lemmas.ts'

const caps = rule('caps').params({d: nat}).inputs({acct: nat, day: nat, ok: bool}).maps({Acct: 0, Day: 0})
  .flags(({ok, acct, day, d, Acct, Day}) => ({granted: ok.and(Acct.at(acct).lt(1), Day.at(day).lt(d))}))
  .step(({acct, day, granted, Acct, Day}) => ({Acct: Acct.bump(acct, granted), Day: Day.bump(day, granted)}))
const dayCap = caps.law('day cap', ({Day, d}) => forall(k => Day.at(k).atMost(d)))
const onlyUp = caps.stepLaw('no count goes down', ({Day}, after) => forall(k => Day.at(k).atMost(after.Day.at(k))))
const twice = caps.stepsLaw('two grants on one day add two', 2, ({day, Day}, after, [, next]) => next!.day.eq(day).implies(after.Day.at(day).eq(Day.at(day).plus(2))), ({granted}) => granted)
const window = rule('window limit').params({w: nat, c: nat, now: nat}).inputs({forced: bool, t: nat}).log('forced', 't')
  .sums({ours: (r, {now, w}) => count(r.forced.not().and(r.t.atMost(now), now.lt(r.t.plus(w))))})
  .queries({seen: (r, {t, w}) => count(t.lt(r.t.plus(w)))})
  .flags(({forced, seen, c}) => ({admitted: forced.not().and(seen.plus(1).atMost(c))}))
  .keep(({forced, admitted}) => forced.or(admitted))
  .relations(({t, now, ours, seen}) => [relation(ours.atMost(seen), t.atMost(now))])
const trial = rule('trial').inputs({plan: oneOf('free', 'pro'), spent: maybe(nat), allowance: maybe(nat)})
const failsClosed = trial.decide('a missing fact means no trial', ({spent}) => spent.isNone,
  ({plan, spent, allowance}) => plan.match({free: () => spent.match({none: () => yes, some: s => allowance.match({none: () => yes, some: a => s.atLeast(a)})}), pro: () => yes}))
const pages = loop('pagination').params({total: nat}).inputs({page: nat}).state({cur: 0}).while(({cur, total}) => cur.lt(total))
  .assume(({page}) => page.atLeast(1)).body(({cur, page, total}) => ({cur: cur.plus(min(page, total.minus(cur)))})).rank(({total, cur}) => total.minus(cur))

// The budget's laws in plain Lean, from its cyclic proof: every sequence of requests, each granted when it fits, keeps
// what was spent within the cap and the grants at most what was spent (as mccarthy_91 states McCarthy's function).
const budgetRuns = (ix: (name: string) => number) => {
  const [cap, spent, n] = [ix('cap'), ix('spent'), ix('n')]
  const sim = `cycbudget_machine, sNext, sView, decideQ, decideFlags, flagSub, applyS, assoc, lookup, withInputs, withCarried, evalC, evalE`
  return `/-- The budget, plainly: from nothing spent, each request of amt i ≥ 1 granted (spent + amt i, one more grant) when it
fits the cap and refused otherwise, what was spent stays within the cap and the grants at most what was spent, after every
number of requests. -/
theorem budget_runs (cap : Nat) (hcap : 1 ≤ cap) (amt spent n : Nat → Nat) (hamt : ∀ i, 1 ≤ amt i) (h0 : spent 0 = 0) (hn0 : n 0 = 0)
    (hs : ∀ i, spent (i + 1) = if spent i + amt i ≤ cap then spent i + amt i else spent i)
    (hn : ∀ i, n (i + 1) = if spent i + amt i ≤ cap then n i + 1 else n i) (i : Nat) : spent i ≤ cap ∧ n i ≤ spent i := by
  have reach : ∀ i, ∃ ρ M, SReach cycbudget_machine ρ M ∧ ρ ${spent} = spent i ∧ ρ ${n} = n i ∧ ρ ${cap} = cap := by
    intro i
    induction i with
    | zero =>
      refine ⟨_, _, SReach.start (fun j => if j = ${cap} then cap else 0) (fun _ _ => 0) (fun p hp => by simp [cycbudget_machine] at hp)
        (by simp [cycbudget_machine, evalC, evalE, hcap]) (fun l hl => by simp [cycbudget_machine] at hl)
        (fun p hp => by simp [cycbudget_machine] at hp), ?_, ?_, ?_⟩ <;> simp [${sim}, h0, hn0]
    | succ i ih =>
      obtain ⟨ρ, M, hr, h1, h2, h3⟩ := ih
      refine ⟨_, _, SReach.step ρ M (fun _ => amt i) M hr (by simp [${sim}, hamt]), ?_, ?_, ?_⟩
      · simp [${sim}, h1, h3, hs i]
      · simp [${sim}, h1, h2, h3, hn i]
      · simp [${sim}, h3]
  obtain ⟨ρ, M, hr, h1, h2, h3⟩ := reach i
  have l0 : ρ ${spent} ≤ ρ ${cap} := cycbudget.law0 ρ M hr
  have l1 : ρ ${n} ≤ ρ ${spent} := cycbudget.law1 ρ M hr
  rw [h1, h3] at l0
  rw [h1, h2] at l1
  exact ⟨l0, l1⟩`
}

const auth = authority()
// ONLY=id,id,... exports just those items (a quicker check while working on one). The tables of nodes take Lean a few
// minutes each, so they are checked on their own (the suite's lean-nodes job), and so are the resource groups' laws, one
// per job (lean-groups-0..3, a quarter of an hour together): left out unless ONLY names them.
const only = process.env.ONLY?.split(',')
// SHARD=i/n exports every n-th item from the i-th (the suite's lean-package-0..n−1, one Lean build each).
const shard = process.env.SHARD?.split('/').map(Number)
// Built by jobs of their own (modal/suite.json: lean-big's trees and groups; lean-cyclic's cyclic proofs).
const cyclicItems = ['mccarthy', 'mutual', 'cycgrowing', 'cycfilled', 'cyccounter', 'cycrollup', 'cyccaps', 'cycfill', 'cyctally', 'cycbudget']
// The proofs core/cycles.ts finds (examples/cycles.ts's leanItems; the suite's lean-cycles jobs, the loops in a file
// of their own: Live.lean and Cyclic.lean each define lexLtC).
const foundItems = ['cycmc91', 'cycack', 'cycgcd', 'cycacc', 'cycacc2', 'cycring', 'cycthrough', 'loopphases', 'loopphases3', 'loopother', 'loopeuclid', 'rule91', 'rule91lemma', 'ruledouble', 'ruledoublelemma']
const separately = ['searchtree', 'sheet', 'groups0', 'groups1', 'groups2', 'groups3', ...cyclicItems, ...foundItems]
const file = toLean(([
  {id: 'caps', machine: caps.machine, laws: [dayCap], stepLaws: [onlyUp, twice]},
  {id: 'window', machine: window.machine, laws: [window.law('window ceiling', ({ours, c}) => ours.atMost(c))]},
  {id: 'trial', goal: failsClosed.goal},
  {id: 'pages', loop: pages.loop, rank: pages.rankTerms},
  {id: 'escrow', machine: escrowWatched(), laws: escrowLaws, stepLaws: escrowSteps, ghosts: ['released'], lean: {after: escrowRunsLean}},
  {id: 'authority', machine: auth.machine, laws: authorityLaws(auth), stepLaws: [...authoritySteps(auth), ...authorityPairs(auth)]},
  {id: 'inline', machine: inlineAuthority().machine, laws: inlineLaws(), stepLaws: inlineSteps()},
  {id: 'members', machine: members().machine, laws: memberLaws(), stepLaws: memberSteps()},
  // A flag read at a later step's witness: the first step's check where the second's would fail.
  {id: 'normalform', machine: normalForm().machine, laws: normalFormLaws(), stepLaws: normalFormSteps()},
  {id: 'childuse', machine: childUse().machine, laws: childUseLaws(), stepLaws: childUseSteps()},
  {id: 'minutes', machine: minutes().machine, laws: minuteLaws()},
  {id: 'larger', machine: larger.machine, laws: largerLaws},
  {id: 'room', machine: room().machine, laws: roomLaws(), lean: pairsLean},
  // Recurrences: defined in Lean by the recurrence, their lemmas proven there by induction.
  {id: 'backoff', machine: retries().machine, laws: retryLaws(), stepLaws: retrySteps()},
  {id: 'twos', machine: counter().machine, laws: counterLaws()},
  {id: 'filled', machine: fillMeter().machine, laws: fillMeterLaws()},
  {id: 'leftovers', machine: ledger().machine, laws: ledgerLaws()},
  {id: 'growing', machine: escalation().machine, laws: escalationLaws()},
  // Facts about several keys read at two values of the state (or the request) at once.
  {id: 'ladder', machine: ladder().machine, laws: ladderLaws()},
  {id: 'tank', machine: tank().machine, laws: tankLaws()},
  // Liveness under weak fairness, its helpful request allowed by a fact about two keys.
  // A lemma with a product, checked by Lean as the kernel's own proof.
  {id: 'area', machine: area().machine, laws: areaLaws()},
  // A request carrying a list, with folds over it; folds over trees as values.
  {id: 'invoices', machine: invoices().machine, laws: invoiceLaws(), stepLaws: invoiceSteps()},
  {id: 'rollup', fold: rollup().fold, laws: rollupLaws()},
  {id: 'orgchart', fold: orgChart().fold, laws: [...orgChart().lemmas, ...orgChartLaws()]},
  {id: 'metered', machine: metered().machine, laws: meteredLaws()},
  // Lemmas nobody stated, found (core/discover.ts): each rule made again with what was found, its laws as given.
  {id: 'foundbackoff', machine: foundRetries().rule.machine, laws: foundRetryLaws(), stepLaws: foundRetrySteps()},
  {id: 'foundarea', machine: foundArea().rule.machine, laws: foundAreaLaws()},
  {id: 'foundinvoices', machine: foundInvoices().rule.machine, laws: invoiceLaws(invoices('states no lemma')), stepLaws: invoiceSteps(invoices('states no lemma'))},
  {id: 'foundorgchart', fold: bareOrgChart().fold, laws: [...bareOrgChart().lemmas, ...foundOrgChart().lemmas, ...bareOrgChartLaws()]},
  // A decision about a carried list: the folds' equations and lemma assumed at the list's end.
  {id: 'taxwithin', goal: invoices().decide('the taxable part is within the total', () => [], ({Lines}) => Lines.fold.taxed.atMost(Lines.fold.total)).goal},
  // Cyclic proofs (Cyclic.lean's cyclic_sound): McCarthy's 91 function, with three tampered proofs computed to false and
  // the claim in plain Lean; a mutual induction; and today's rules as instances (a recurrence's lemmas and law between,
  // a machine's laws over a function's facts, a fold's laws over trees as tables). A machine's proof is carried back to
  // the machine (Bridge.lean's cyc_machine_sound): its laws over SReach, the machine Sets.lean's; for caps and budget, a
  // tampered machine's check against the proof computed to false.
  ...(!only?.some(id => cyclicItems.includes(id)) ? [] : ((): Parameters<typeof toLean>[0] => {
    const proven = (fs: Parameters<typeof proveCyclic>[0], specs: Parameters<typeof proveCyclic>[1]): Cyclic => { const r = proveCyclic(fs, specs); if (!r.proven || !r.checked) throw new Error(`cyclic: ${r.proven ? r.why : r.goal}`); return r.proof }
    const ofMachine = (id: string, machine: Machine, laws: Law[], tampered?: {what: string, machine: Machine}[], after?: (ix: (name: string) => number) => string) =>
      (r => ({id, cyclic: proven(r.facts, r.specs), bridge: {machine, laws, ...(tampered ? {tampered} : {})}, ...(after ? {after} : {})}))(machineNodes(machine, laws, proveLaws(machine, laws).proof!.instances))
    const capsLoose = rule('caps').params({d: nat}).inputs({acct: nat, day: nat, ok: bool}).maps({Acct: 0, Day: 0})
      .flags(({ok, acct, Acct}) => ({granted: ok.and(Acct.at(acct).lt(1))}))
      .step(({acct, day, granted, Acct, Day}) => ({Acct: Acct.bump(acct, granted), Day: Day.bump(day, granted)}))
    const mc = mccarthy(), p = proven(mc.facts, mc.specs)
    const use0 = (edit: (u: Cyclic['nodes'][number]['uses'][number]) => Cyclic['nodes'][number]['uses'][number]): Cyclic => ({...p, nodes: p.nodes.map(n => ({...n, uses: n.uses.map((u, j) => (j === 0 ? edit(u) : u))}))})
    const g = growing(), rc = g.recur!, fd = filled().recur!
    const c = counter(), cl = counterLaws(c), cm = c.machine, ci = proveLaws(cm, cl).proof!.instances
    const ru = rollup(), rl = rollupLaws(ru)
    return [
      {id: 'mccarthy', cyclic: p, tampered: [
        {what: 'the use at n + 11 read at n: no drop', proof: use0(u => ({...u, subst: {n: {op: 'var', name: 'n'}}}))},
        {what: 'the use at n + 11 read at n + 12', proof: use0(u => ({...u, subst: {n: {op: 'add', a: {op: 'var', name: 'n'}, b: {op: 'const', value: 12}}}}))},
        {what: 'the node unranked', proof: {...p, nodes: p.nodes.map(n => ({...n, rank: []}))}},
      ], after: (ix, mx) => `theorem mccarthy_91 (f : Nat → Nat) (hf : ∀ k, f k = if 100 < k then k - 10 else f (f (k + 11))) (n : Nat) (hn : n ≤ 101) : f n = 91 := by
  have h := mccarthy_sound (fun _ k => f k) (fun i => if i = ${ix('n')} then n else 0) (by
    intro fa hfa vals
    simp only [mccarthy_facts, List.mem_singleton] at hfa
    subst hfa
    have hk := hf (vals ${ix('k')})
    by_cases h100 : 100 < vals ${ix('k')} <;> simp [evalC, evalE, override, h100, hk]) _ mccarthy_node0_mem (by
    rw [mccarthy_node0_hyps]; simp [mccarthy_hyps0, evalC, evalE, hn])
  rw [mccarthy_node0_concl] at h
  simpa [mccarthy_concl0, evalC, evalE] using h
-- the map's number: ${mx('f')}`},
      {id: 'mutual', cyclic: proven(mutual().facts, mutual().specs)},
      ...[['cycgrowing', 'growing', rc], ['cycfilled', 'filled', fd]].map(([id, name, d]) => {
        const r = d as typeof rc, rcase = {name: name as string, args: r.args, zero: r.zero, next: r.next, lemmas: r.lemmas, between: r.between}, nodes = recurNodes({...rcase, facts: []})
        return {id: id as string, cyclic: proven(nodes.facts, nodes.specs), recur: rcase}
      }),
      ...(r => [{id: 'cyccounter', cyclic: proven(r.facts, r.specs), bridge: {machine: cm, laws: cl}}])(machineNodes(cm, cl, ci)),
      ...(r => [{id: 'cycrollup', cyclic: proven(r.facts, r.specs), fold: {fold: ru.fold, laws: rl}}])(foldNodes(ru.fold, rl)),
      ofMachine('cyccaps', caps.machine, [dayCap], [{what: 'a grant that doesn\'t check the day\'s count', machine: capsLoose.machine}]),
      ofMachine('cycfill', fill().machine, fillLaws()),
      ofMachine('cyctally', tally().machine, tallyLaws()),
      ofMachine('cycbudget', budget().machine, budgetLaws(), [{what: 'a grant that checks what was spent, not what it adds', machine: budget('grants past the cap').machine}], budgetRuns),
    ]
  })()),
  ...(!only?.some(id => foundItems.includes(id)) ? [] : cycleLeanItems()),
  // A decision that reads conditions about every key, as the step law it is proven as.
  ...(d => [{id: 'subsettrans', machine: d.steps!.rule.machine, laws: [], stepLaws: [d.steps!.law]}])(rule('sets').inputs({n: nat}).carries('A', 'B', 'C').decide('a subset of a subset is a subset', ({A, B, C}) => [A.subsetOf(B), B.subsetOf(C)], ({A, C}) => A.subsetOf(C))),
  // n times the goal, then a square: (Σv)² <= n·Σv² over running samples.
  ...(r => [{id: 'runningstats', machine: r.machine, laws: [r.law('s² within n·q', ({n, s, q}) => s.mul(s).atMost(n.mul(q)))]}])(rule('running statistics').inputs({v: nat}).state({n: 0, s: 0, q: 0}).step(({v, n, s, q}) => ({n: n.plus(1), s: s.plus(v), q: q.plus(v.mul(v))}))),
  // Path scopes (examples/scopes.ts): each decision as the step law it is proven as.
  ...[...patternLaws(), ...grantLaws(), ...normalizedLaws()].map((d, i) => ({id: `scopes${i}`, machine: d.steps!.rule.machine, laws: [], stepLaws: [d.steps!.law]})),
  {id: 'sortedlist', machine: sortedList().machine, laws: sortedListLaws()},
  {id: 'distinctnames', machine: distinctNames().machine, laws: distinctNamesLaws()},
  {id: 'wideflag', machine: wide().machine, laws: wide().kindLaws()},
  {id: 'orderchart', machine: order().rule.machine, laws: [...order().chartLaws(), ...orderLaws().laws], stepLaws: orderLaws().stepLaws},
  {id: 'checkoutchart', machine: checkout().rule.machine, laws: checkoutLaws()},
  {id: 'bindingchart', machine: binding().rule.machine, laws: [], stepLaws: bindingLaws()},
  {id: 'xstateorder', machine: xorder().rule.machine, laws: [...xorder().chartLaws(), ...xorderLaws().laws], stepLaws: xorderLaws().stepLaws},
  // Invariants core/infer.ts found (examples/infer.ts), written out as its builder calls: with the laws they prove.
  {id: 'inferpool', machine: pool().machine, laws: [poolLaw(), pool().law('inUse + released <= acquired', ({inUse, acquired, released}) => inUse.plus(released).atMost(acquired))]},
  {id: 'inferlease', machine: lease().machine, laws: [leaseLaw(), lease().law('every k: Expiry[k] <= until', ({until, Expiry}) => forall(k => Expiry.at(k).atMost(until)))]},
  {id: 'groups0', machine: groups().machine, laws: [], stepLaws: [groupLaws()[0]!]},
  {id: 'groups1', machine: groups().machine, laws: [], stepLaws: [groupLaws()[1]!]},
  {id: 'groups2', machine: groups().machine, laws: [], stepLaws: [groupLaws()[2]!]},
  {id: 'groups3', machine: groups().machine, laws: [], stepLaws: [groupLaws()[3]!]},
  {id: 'searchtree', machine: searchTree().machine, laws: [...searchTree().kindLaws(), ...searchTreeLaws()]},
  {id: 'sheet', machine: sheet().machine, laws: [...sheet().kindLaws(), ...sheetLaws()]},
  {id: 'signoffs', fold: signoffs().fold, laws: signoffLaws()},
  {id: 'pump', machine: pump().machine, laws: [], liveness: [pumpLive()]},
  // Records and variants, as the variables they are encoded in.
  {id: 'held', machine: hold().machine, laws: holdLaws(), stepLaws: holdSteps()},
  {id: 'accounts', machine: accounts().machine, laws: accountLaws(), stepLaws: accountSteps()},
  {id: 'seats', machine: seats().machine, laws: seatLaws(), stepLaws: seatSteps()},
  {id: 'jobs', machine: jobs().machine, laws: jobLaws(), stepLaws: jobSteps()},
  ...approveLaws().map((d, j) => ({id: `approve${j}`, goal: d.goal})),
  {id: 'scope', machine: scope().machine, laws: scopeLaws(), stepLaws: scopeSteps()},
  {id: 'bits', machine: bits().machine, laws: bitsLaws()},
  {id: 'team', machine: team().machine, laws: teamLaws(), stepLaws: teamSteps()},
  {id: 'tickets', machine: tickets().machine, laws: ticketLaws(), liveness: [everyTicket()]},
  {id: 'logged', machine: loggedTickets().machine, laws: loggedLaws(), liveness: [everyLoggedTicket()]},
  {id: 'tagged', machine: taggedTickets().machine, laws: taggedLaws, liveness: [everyTaggedTicket]},
  {id: 'batches', machine: batches().machine, laws: batchLaws(), liveness: [allDone()]},
  {id: 'recounted', machine: recounted().machine, laws: recountedLaws(), liveness: [everyRecountedTicket()]},
  {id: 'reviews', machine: reviews().machine, laws: reviewLaws(), liveness: [everyReview()]},
  // Refinements, with what they mean: the countdown meter refines the meter; the two-phase one refines it with stutters.
  {id: 'lazy', refinement: {impl: lazyAuthority().machine, spec: authority().machine, relation: lazyRelation, witness: lazyWitness}},
  {id: 'countdown', refinement: {impl: countdown().machine, spec: meter.machine, relation: meterRelation, witness: {amount: {op: 'min', a: {op: 'var', name: 'amount'}, b: {op: 'var', name: 'most'}}}}},
  {id: 'twophase', refinement: {impl: twoPhase().machine, spec: meter.machine, relation: [{name: 'used = used', holds: {op: '=', a: {op: 'var', name: 'a_used'}, b: {op: 'var', name: 'b_used'}}}, {name: 'pending <= most', holds: {op: '<=', a: {op: 'var', name: 'a_pending'}, b: {op: 'var', name: 'most'}}}],
    witness: {amount: {op: 'var', name: 'a_pending'}}, stutter: {op: '=', a: {op: 'var', name: 'op'}, b: {op: 'const', value: 0}}}},
] as Parameters<typeof toLean>[0]).filter(item => (only ? only.includes(item.id) : !separately.includes(item.id))).filter((_, i) => !shard || i % shard[1]! === shard[0]!), {title: 'gdp-wired/lean, end to end'})
const out = process.argv[2]
if (!out) throw new Error('usage: bun package-check.ts <empty folder>')
mkdirSync(out, {recursive: true})
for (const [name, text] of Object.entries(leanProject(file))) writeFileSync(join(out, name), text)
console.log(`${Object.keys(leanProject(file)).length} files in ${out}; ${[...file.matchAll(/^theorem /gm)].length} theorems`)
