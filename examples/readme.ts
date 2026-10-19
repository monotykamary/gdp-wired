// The README's "Writing laws" snippets, kept here so they type-check and prove (the suite runs this file).
//   bun examples/readme.ts
import {bool, count, forall, fun, maybe, min, nat, no, oneOf, proveDecision, proveRule, proveSteps, record, recur, relation, rule, variant, when, yes} from '../core/dsl.ts'

// Maps and flags: a grant is decided once per step; each map is written once; a map law holds at every key.
const caps = rule('caps')
  .params({d: nat})
  .inputs({acct: nat, day: nat, ok: bool})
  .maps({Acct: 0, Day: 0})
  .flags(({ok, acct, day, d, Acct, Day}) => ({granted: ok.and(Acct.at(acct).lt(1), Day.at(day).lt(d))}))
  .step(({acct, day, granted, Acct, Day}) => ({Acct: Acct.bump(acct, granted), Day: Day.bump(day, granted)}))
const dayCap = caps.law('day cap', ({Day, d}) => forall(k => Day.at(k).atMost(d)))

// Step laws: about one step, for every request the rule allows; `after` reads the state and maps after it.
const onlyUp = caps.stepLaw('no count goes down', ({Day}, after) => forall(k => Day.at(k).atMost(after.Day.at(k))))
const once = caps.stepLaw('a grant adds one to its day', ({day, Day}, after) => after.Day.at(day).eq(Day.at(day).plus(1)), ({granted}) => granted)
// Laws about k steps in a row: `requests` holds each step's request, `when` narrows the j-th step's.
const twice = caps.stepsLaw('two grants on one day add two', 2, ({day, Day}, after, [, next]) => next!.day.eq(day).implies(after.Day.at(day).eq(Day.at(day).plus(2))), ({granted}) => granted)

// Histories: a log of requests, a sum over it (state), a query over it at the request's time (an input the runtime
// computes), and a relation between them proven one record at a time.
const window = rule('window limit')
  .params({w: nat, c: nat, now: nat})
  .inputs({forced: bool, t: nat})
  .log('forced', 't')
  .sums({ours: (r, {now, w}) => count(r.forced.not().and(r.t.atMost(now), now.lt(r.t.plus(w))))})
  .queries({seen: (r, {t, w}) => count(t.lt(r.t.plus(w)))})
  .flags(({forced, seen, c}) => ({admitted: forced.not().and(seen.plus(1).atMost(c))}))
  .keep(({forced, admitted}) => forced.or(admitted))
  .relations(({t, now, ours, seen}) => [relation(ours.atMost(seen), t.atMost(now))])
  .prune('t', ({w}) => w) // requests in time order: records older than the window are dropped

// Decisions over facts: optional facts and choices, every case covered.
const trial = rule('trial').inputs({plan: oneOf('free', 'pro'), spent: maybe(nat), allowance: maybe(nat)})
const failsClosed = trial.decide('a missing fact means no trial', ({spent}) => spent.isNone,
  ({plan, spent, allowance}) => plan.match({free: () => spent.match({none: () => yes, some: s => allowance.match({none: () => yes, some: a => s.atLeast(a)})}), pro: () => yes}))

// Records and variants: a payment is by card or in cash, each with fields of its own, read only in `match`.
const Pay = variant({card: {amount: nat, verified: bool}, cash: {amount: nat}})
const approve = fun('approve').inputs({pay: Pay, who: record({limit: nat, blocked: bool})})
  .returns(({pay, who}) => ({ok: who.blocked.not().and(pay.match({card: c => c.verified.and(c.amount.atMost(who.limit)), cash: c => c.amount.atMost(200)}))}))
const unverified = approve.law('an unverified card is never approved', ({pay}, out) => [pay.match({card: c => c.verified.not(), cash: () => no}), out.ok], () => no)

// A lemma you state, proven by induction: the backoff delay is defined by its recurrence, and its lemmas are facts
// every rule that reads it may use (its two equations alone don't bound it at an unknown attempt).
const delay = recur('delay', {zero: 1, next: (_, d) => min(d.times(2), 64)}, {'at least 1': (_, d) => d.atLeast(1), 'at most 64': (_, d) => d.atMost(64)})
const retry = rule('retry').inputs({failed: bool, now: nat}).state({tries: 0, next: 0, last: 0}).fns({delay})
  .assume(({now, last}) => now.atLeast(last))
  .step(({failed, now, tries, next, delay}) => ({tries: when(failed, tries.plus(1), 0), next: when(failed.and(now.atLeast(next)), now.plus(delay(tries)), next), last: now}))
const soon = retry.law('the next try is at most 64 after the last request', ({next, last}) => next.atMost(last.plus(64)))

const results = {
  'caps: day cap': proveRule(caps, [dayCap]),
  'caps: step laws': proveSteps(caps, [dayCap], [onlyUp, once, twice]),
  'window: ceiling': proveRule(window, [window.law('window ceiling', ({ours, c}) => ours.atMost(c))]),
  'trial: fails closed': proveDecision(failsClosed),
  'approve: unverified': proveDecision(unverified),
  'retry: backoff': proveRule(retry, [soon]),
}
for (const [what, v] of Object.entries(results)) console.log(`${what.padEnd(22)} proven ${v.proven}, checked ${v.checked}`)
if (!Object.values(results).every(v => v.proven && v.checked)) process.exit(1)
