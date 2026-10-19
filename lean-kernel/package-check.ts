// gdp-wired/lean end to end: rules written with the builders, exported by toLean, laid out by leanProject, and built by
// `lake build` (modal/suite.json's lean-package job). Usage: bun package-check.ts <empty folder>
import {mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {bool, count, forall, loop, maybe, min, nat, oneOf, relation, rule, yes} from '../core/dsl.ts'
import {countdown, escrowLaws, escrowRunsLean, escrowSteps, escrowWatched, meter, meterRelation, twoPhase} from '../examples/composition.ts'
import {authority, authorityLaws, authorityPairs, authoritySteps, lazyAuthority, lazyRelation, lazyWitness} from '../examples/sets.ts'
import {inlineAuthority, inlineLaws, inlineSteps, memberLaws, memberSteps, members} from '../examples/quantifiers.ts'
import {larger, largerLaws, minuteLaws, minutes, pairsLean, room, roomLaws} from '../examples/functions.ts'
import {bits, bitsLaws, scope, scopeLaws, scopeSteps} from '../examples/lists.ts'
import {accountLaws, accountSteps, accounts, approveLaws, hold, holdLaws, holdSteps, jobLaws, jobSteps, jobs, seatLaws, seatSteps, seats} from '../examples/datatypes.ts'
import {counter, counterLaws, escalation, escalationLaws, fillMeter, fillMeterLaws, ladder, ladderLaws, ledger, ledgerLaws, pump, pumpLive, retries, retryLaws, retrySteps, tank, tankLaws} from '../examples/lemmas.ts'
import {team, teamLaws, teamSteps} from '../examples/sizes.ts'
import {allDone, batchLaws, batches, everyTaggedTicket, taggedLaws, taggedTickets, everyLoggedTicket, everyRecountedTicket, everyReview, everyTicket, loggedLaws, loggedTickets, recounted, recountedLaws, reviewLaws, reviews, ticketLaws, tickets} from '../examples/liveness.ts'
import {leanProject, toLean} from './emit.ts'

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
// ONLY=id,id,... exports just those items (a quicker check while working on one).
const only = process.env.ONLY?.split(',')
const file = toLean(([
  {id: 'caps', machine: caps.machine, laws: [dayCap], stepLaws: [onlyUp, twice]},
  {id: 'window', machine: window.machine, laws: [window.law('window ceiling', ({ours, c}) => ours.atMost(c))]},
  {id: 'trial', goal: failsClosed.goal},
  {id: 'pages', loop: pages.loop, rank: pages.rankTerms},
  {id: 'escrow', machine: escrowWatched(), laws: escrowLaws, stepLaws: escrowSteps, ghosts: ['released'], lean: {after: escrowRunsLean}},
  {id: 'authority', machine: auth.machine, laws: authorityLaws(auth), stepLaws: [...authoritySteps(auth), ...authorityPairs(auth)]},
  {id: 'inline', machine: inlineAuthority().machine, laws: inlineLaws(), stepLaws: inlineSteps()},
  {id: 'members', machine: members().machine, laws: memberLaws(), stepLaws: memberSteps()},
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
] as Parameters<typeof toLean>[0]).filter(item => !only || only.includes(item.id)), {title: 'gdp-wired/lean, end to end'})
const out = process.argv[2]
if (!out) throw new Error('usage: bun package-check.ts <empty folder>')
mkdirSync(out, {recursive: true})
for (const [name, text] of Object.entries(leanProject(file))) writeFileSync(join(out, name), text)
console.log(`${Object.keys(leanProject(file)).length} files in ${out}; ${[...file.matchAll(/^theorem /gm)].length} theorems`)
