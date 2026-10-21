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
import type {Cyclic} from '../kernel/cyclic.ts'
import {mccarthy, mutual} from '../examples/cyclic.ts'
import {growing} from '../examples/lemmas.ts'

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

const auth = authority()
// ONLY=id,id,... exports just those items (a quicker check while working on one). The tables of nodes take Lean a few
// minutes each, so they are checked on their own (the suite's lean-nodes job), and so are the resource groups' laws, one
// per job (lean-groups-0..3, a quarter of an hour together): left out unless ONLY names them.
const only = process.env.ONLY?.split(',')
// Built by jobs of their own (modal/suite.json: lean-big's trees and groups; lean-cyclic's cyclic proofs).
const cyclicItems = ['mccarthy', 'mutual', 'cycgrowing', 'cyccounter', 'cycrollup']
const separately = ['searchtree', 'sheet', 'groups0', 'groups1', 'groups2', 'groups3', ...cyclicItems]
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
  // a machine's laws over a function's facts, a fold's laws over trees as tables).
  ...(!only?.some(id => cyclicItems.includes(id)) ? [] : ((): Parameters<typeof toLean>[0] => {
    const proven = (fs: Parameters<typeof proveCyclic>[0], specs: Parameters<typeof proveCyclic>[1]): Cyclic => { const r = proveCyclic(fs, specs); if (!r.proven || !r.checked) throw new Error(`cyclic: ${r.proven ? r.why : r.goal}`); return r.proof }
    const mc = mccarthy(), p = proven(mc.facts, mc.specs)
    const use0 = (edit: (u: Cyclic['nodes'][number]['uses'][number]) => Cyclic['nodes'][number]['uses'][number]): Cyclic => ({...p, nodes: p.nodes.map(n => ({...n, uses: n.uses.map((u, j) => (j === 0 ? edit(u) : u))}))})
    const g = growing(), rc = g.recur!
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
      ...(r => [{id: 'cycgrowing', cyclic: proven(r.facts, r.specs)}])(recurNodes({name: 'growing', args: rc.args, zero: rc.zero, next: rc.next, lemmas: rc.lemmas, between: rc.between, facts: []})),
      ...(r => [{id: 'cyccounter', cyclic: proven(r.facts, r.specs)}])(machineNodes(cm, cl, ci)),
      ...(r => [{id: 'cycrollup', cyclic: proven(r.facts, r.specs)}])(foldNodes(ru.fold, rl)),
    ]
  })()),
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
] as Parameters<typeof toLean>[0]).filter(item => (only ? only.includes(item.id) : !separately.includes(item.id))), {title: 'gdp-wired/lean, end to end'})
const out = process.argv[2]
if (!out) throw new Error('usage: bun package-check.ts <empty folder>')
mkdirSync(out, {recursive: true})
for (const [name, text] of Object.entries(leanProject(file))) writeFileSync(join(out, name), text)
console.log(`${Object.keys(leanProject(file)).length} files in ${out}; ${[...file.matchAll(/^theorem /gm)].length} theorems`)
