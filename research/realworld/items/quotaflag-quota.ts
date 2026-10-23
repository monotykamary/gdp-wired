// Quotas and budgets, from three projects:
//
// - Kubernetes v1.37.1, the ResourceQuota admission plugin's CheckRequest (k8s.io/apiserver). Apache-2.0, (c) The
//   Kubernetes Authors.
//   https://github.com/kubernetes/kubernetes/blob/f78e722310e50bcaca9276be22276d9e91d91308/staging/src/k8s.io/apiserver/pkg/admission/plugin/resourcequota/controller.go
// - LibreChat v0.8.8, the token-credit balance with reservations (packages/data-schemas, packages/api). MIT, (c)
//   LibreChat (Danny Avila).
//   https://github.com/danny-avila/LibreChat/blob/e8f3be08623663d4ad7f7241e693c94469b63bb0/packages/data-schemas/src/methods/transaction.ts
// - LiteLLM v1.106.2, the proxy's read-time max_budget checks for keys and teams and the post-call spend counter (MIT
//   outside enterprise/; these files are outside it). MIT, (c) Berri AI.
//   https://github.com/BerriAI/litellm/blob/49943cd52ea46aacf8db2e5cb2b890d580fe9bb4/litellm/proxy/auth/auth_checks.py
import {type Cond, type Term, bool, everyKey, forall, int, nat, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, leadsTo, stepLaw} from '../lib.ts'

// --- Kubernetes ResourceQuota admission ---------------------------------------------------------------------------------

const k8sSrc = {repo: 'kubernetes/kubernetes', commit: 'f78e722310e50bcaca9276be22276d9e91d91308', licence: 'Apache-2.0', author: 'The Kubernetes Authors', language: 'Go'}
const k8sPath = 'staging/src/k8s.io/apiserver/pkg/admission/plugin/resourcequota/controller.go'

// :531 `quota.SubtractWithNonNegativeResult(inputUsage, prevUsage)` (truncated minus), else :508 inputUsage.
const delta = (byDelta: Cond, n: Term, o: Term) => when(byDelta, n.minus(o), n)

// One ResourceQuota of the namespace, its status.used per resource name (names as numbers) the state; each admission
// request carries the quota's status.hard as read from the informer cache at that request (`Hard`, with `InHard` 1 for
// the names hard lists: a limit of 0 is a limit) and the evaluator's usage of the new and the old object (`New`, `Old`).
// Quantities are naturals in the resource's smallest unit (resource.Quantity adds and compares exactly). The
// evaluator's Handles, Matches (scopes), Constraints and Usage, the other quotas of the namespace and the status write
// are inputs: their outcomes. A request rejected anywhere changes nothing (the error is returned before
// `outQuotas[index].Status.Used = newUsage` is stored, or the store fails).
export const resourceQuota = () => rule('ResourceQuota CheckRequest')
  .inputs({
    handles: bool, // :414 `if !evaluator.Handles(a) { return quotas, nil }`
    matches: bool, // :458-466 `evaluator.Matches(&resourceQuota, inputObject)`: this quota is "interesting"
    constraintsOk: bool, // :470-472 `evaluator.Constraints(restrictedResources, inputObject)`
    usageKnown: bool, // :473-475 hasUsageStats: status.used has every restricted hard resource
    isUpdate: bool, oldFound: bool, oldHasVersion: bool, oldMatches: bool, // :515-552 the update's previous object
    covered: bool, // :575-592 every limited-by-default resource and scope has a covering quota
    status: bool, // :614 `a.GetSubresource() != "status"`
    othersOk: bool, // every other interesting quota of the namespace admits the request (:603-632 returns on the first that doesn't)
    dryRun: bool, // :245-249 dry-run requests don't update the quota
    updateOk: bool, // :288-291 UpdateQuotaStatus succeeds (a conflict fails the waiter, :305-313, or re-checks it with fresh quotas)
  })
  .carries('New', 'Old', 'Hard', 'InHard')
  .maps({Used: 0})
  .flags(({handles, matches, constraintsOk, usageKnown, isUpdate, oldFound, oldHasVersion, oldMatches}) => ({
    // :470-475 and :517-519: rejections before any usage is measured.
    early: handles.and(matches, constraintsOk.not().or(usageKnown.not())).or(handles.and(isUpdate, oldFound.not())),
    // :523-547 charge the delta only when the old object has a resource version and the quota matched it too.
    byDelta: isUpdate.and(oldHasVersion, oldMatches),
  }))
  .flags(({byDelta, New, Old, InHard, Hard, Used}) => ({
    // :556-573 a request whose usage is zero everywhere changes nothing.
    zero: everyKey(k => delta(byDelta, New.at(k), Old.at(k)).eq(0)),
    // :610-628 LessThanOrEqual(Mask(Used + Mask(delta, hard), names(requested)), hard): each resource the request
    // charges (non-zero delta, listed in hard) stays within its hard limit.
    fits: everyKey(k => InHard.at(k).gt(0).and(delta(byDelta, New.at(k), Old.at(k)).gt(0)).implies(Used.at(k).plus(delta(byDelta, New.at(k), Old.at(k))).atMost(Hard.at(k)))),
  }))
  .flags(({handles, matches, early, zero, covered, status, fits, othersOk, dryRun, updateOk}) => ({
    applies: handles.and(matches, early.not(), zero.not(), covered, status.or(fits), othersOk, dryRun.not(), updateOk),
  }))
  // :611-612, :631 `newUsage := quota.Add(Used, Mask(deltaUsage, hardResources))`, stored as status.used.
  .step(({byDelta, New, Old, InHard, Used, applies}) => ({
    Used: Used.each(k => when(applies.and(InHard.at(k).gt(0)), Used.at(k).plus(delta(byDelta, New.at(k), Old.at(k))), Used.at(k))),
  }))

const rq = resourceQuota()
const k8sItem: RealItem = {
  id: 'quota/kubernetes/ResourceQuota.CheckRequest',
  domain: 'quota',
  source: {...k8sSrc, path: k8sPath, lines: '412-635', export: 'CheckRequest'},
  also: [
    {...k8sSrc, path: k8sPath, lines: '228-342', export: 'quotaEvaluator.checkQuotas'},
    {...k8sSrc, path: 'staging/src/k8s.io/apiserver/pkg/quota/v1/resources.go', lines: '50-160', export: 'LessThanOrEqual, Add, SubtractWithNonNegativeResult, Mask'},
  ],
  summary: 'Admission of a create or update against a namespace\'s ResourceQuota: the request\'s usage (the delta on an update) is added to status.used for each resource hard lists, unless that would pass a hard limit (status writes are not checked).',
  expressible: 'partial',
  gaps: [
    {gap: 'external', blocks: 'part', detail: 'the evaluator (Handles, Matches with scope selectors, Constraints, Usage of an object), the other quotas of the namespace and UpdateQuotaStatus are inputs: their outcomes'},
    {gap: 'async', blocks: 'part', detail: 'checkQuotas batches the waiters of a namespace and retries a failed status write against fresh quotas; one waiter per step here (a batch whose write succeeds is the sequence of its waiters)'},
    {gap: 'scope', blocks: 'part', detail: 'one quota; usage goes down only through the quota controller\'s recalculation (outside admission), which is not modelled'},
  ],
  laws: [
    // Stated first for every request ('every admitted request leaves the usage it charges within the hard limits', the
    // Kubernetes docs' "If creating or updating a resource violates a quota constraint, the request will fail with HTTP
    // status code 403"), this law was refuted by a status write: :614 `if a.GetSubresource() != "status"` charges a status
    // update without the check (commit 27706a0b, "Add quota support for PVC with VolumeAttributesClass": the status
    // reports what was already admitted). A law error (repro/k8s-status-quota.go): the check is for every request but
    // status writes.
    stepLaw(rq, rq.stepLaw('an admitted request leaves every resource it charges within its hard limit', ({Used, Hard}, after) => forall(k => after.Used.at(k).eq(Used.at(k)).or(after.Used.at(k).atMost(Hard.at(k)))), ({status}) => status.not()),
      'step', 'docs', 'controller.go:617-627 "exceeded quota: %s, requested: %s, used: %s, limited: %s" is returned instead of storing newUsage'),
    stepLaw(rq, rq.stepLaw('a request that would pass a hard limit changes no usage', ({Used}, after) => forall(k => after.Used.at(k).eq(Used.at(k))), ({fits, status}) => fits.not().and(status.not())),
      'step', 'docs', 'controller.go:621 `return nil, admission.NewForbidden(...)`: the request is refused and the quota keeps its usage'),
    stepLaw(rq, rq.stepLaw('a dry run changes no usage', ({Used}, after) => forall(k => after.Used.at(k).eq(Used.at(k))), ({dryRun}) => dryRun),
      'step', 'docs', 'controller.go:245 "Don\'t update quota for admissionAttributes that correspond to dry-run requests"'),
    stepLaw(rq, rq.stepLaw('admission never lowers usage', ({Used}, after) => forall(k => Used.at(k).atMost(after.Used.at(k)))),
      'step', 'docs', 'resources.go:102-103 SubtractWithNonNegativeResult "makes sure we don\'t return negative values to prevent negative resource usage"'),
    stepLaw(rq, rq.stepLaw('a resource the quota does not limit is never charged', ({Used, InHard}, after) => forall(k => InHard.at(k).eq(0).implies(after.Used.at(k).eq(Used.at(k))))),
      'step', 'docs', 'controller.go:611 `requestedUsage := quota.Mask(deltaUsage, hardResources)`'),
  ],
}

// --- LibreChat balance reservations ----------------------------------------------------------------------------------

const lcSrc = {repo: 'danny-avila/LibreChat', commit: 'e8f3be08623663d4ad7f7241e693c94469b63bb0', licence: 'MIT', author: 'LibreChat (Danny Avila)', language: 'TypeScript'}
const lcPath = 'packages/data-schemas/src/methods/transaction.ts'

// One user's Balance document. Each step is one atomic MongoDB write (a conditional updateOne, or one update of a
// bulkWrite, which applies each update on its own); a write whose filter misses changes nothing, and the code's re-reads
// and retries are further requests. The values a write's filter was built from (read earlier) are inputs. Credits are
// naturals in the code's unit (tokenCost is `amount * multiplier`, a float, held as `Math.ceil`: whole credits here).
// Time is sent in (`now`); reservation ids are numbers (randomUUID, fresh for each admission).
export const balanceReservation = () => rule('LibreChat balance reservations')
  // isAutoRefillDue's interval (getRefillEligibilityDate) in the same unit as `now`; refillAmount; autoRefillEnabled.
  // `d`: the reservation a liveness law watches (not the code's).
  .params({interval: nat, refillAmount: nat, refillOn: bool, d: nat})
  .inputs({op: oneOf('reserve', 'expire', 'release', 'renew', 'debit', 'credit', 'refill', 'settle'), id: nat, amount: nat, seen: nat, now: nat, expiresAt: nat, clears: bool})
  // :526 `held = Math.ceil(amount)`; the reservation ids of :539 are fresh UUIDs (checkBalance.ts:224 randomUUID).
  .state({credits: 0, reserved: int.from(0), hasReserved: bool.from(false), lastRefill: 0, pending: bool.from(false), recorded: bool.from(true), refills: 0, refillTx: 0})
  // the `reservations` array as two maps: the held amount (0: none) and its expiry.
  .maps({Held: 0, Exp: 0})
  .flags(({op, id, amount, seen, now, credits, reserved, hasReserved, lastRefill, pending, interval, refillAmount, refillOn, Held, Exp}) => ({
    // :529-542 `$push`/`$inc` filtered on `tokenCredits: {$gte: credits}` and `reservedCredits <= credits - amount` (or
    // no reservedCredits yet: then the read's `balance >= amount`, :521, with balance = credits). :522 `!(amount > 0)`
    // returns without a write. A fresh id holds nothing.
    reserves: op.is('reserve').and(amount.gt(0), Held.at(id).eq(0), credits.atLeast(seen),
      when(hasReserved, reserved.plus(amount).atMost(seen), amount.atMost(seen))),
    // :406-420 removeReservations: one `$pull` + `$inc: -amount` per reservation, filtered on `{id, amount}` and, for
    // expired ones (:510), `expiresAt <= now`. :584-593 releaseBalanceReservation: no expiry filter; `!(amount > 0)` returns.
    expires: op.is('expire').and(amount.gt(0), Held.at(id).eq(amount), Exp.at(id).atMost(now)),
    releases: op.is('release').and(amount.gt(0), Held.at(id).eq(amount)),
    // :570-581 renewBalanceReservation: `$set` the expiry where `reservations.id` is there.
    renews: op.is('renew').and(Held.at(id).gt(0)),
    // :362-397 applyAutoRefill, fenced on every value the decision read (so atomic with it): :516 `balance - amount <= 0`
    // and isAutoRefillDue (:295-311: enabled, refillAmount > 0, now >= lastRefill + interval), :502-504 no refill marker
    // left unsettled (the fence's `pendingRefill: null`).
    refilling: op.is('refill').and(refillOn, refillAmount.gt(0), now.atLeast(lastRefill.plus(interval)), pending.not(), reserved.plus(amount).atLeast(credits)),
    settles: op.is('settle').and(pending),
  }))
  .step(({op, id, amount, now, expiresAt, clears, credits, reserved, hasReserved, lastRefill, pending, recorded, refills, refillTx, refillAmount, Held, Exp, reserves, expires, releases, renews, refilling, settles}) => ({
    reserved: when(reserves, reserved.plus(amount), when(expires.or(releases), reserved.minus(amount), reserved)),
    hasReserved: hasReserved.or(reserves),
    Held: Held.set(id, when(reserves, amount, when(expires.or(releases), 0, Held.at(id)))),
    Exp: Exp.set(id, when(reserves.or(renews), expiresAt, Exp.at(id))),
    // :227-293 updateBalance: optimistic (`tokenCredits: currentCredits` in the filter), `Math.max(0, current + increment)`:
    // a debit is a negative increment (spendTokens), a credit a positive one. :382 the refill adds refillAmount.
    credits: when(op.is('debit'), credits.minus(amount), when(op.is('credit'), credits.plus(amount), when(refilling, credits.plus(refillAmount), credits))),
    lastRefill: when(refilling, now, lastRefill),
    // :364-367, :384 the refill's write leaves a pendingRefill marker; :322-356 settleAutoRefill saves the ledger
    // transaction under the marker's fixed _id (a duplicate key: already recorded) and then `$unset`s the marker; the
    // unset may fail (`clears`), leaving the marker to be settled again. `refills` and `refillTx`: ghost counts of the
    // refills applied and the refill transactions saved (observed effects).
    pending: refilling.or(pending.and(settles.and(clears).not())),
    recorded: refilling.not().and(settles.or(recorded)),
    refills: when(refilling, refills.plus(1), refills),
    refillTx: when(settles.and(recorded.not()), refillTx.plus(1), refillTx),
  }))

const lc = balanceReservation()
const lcItem: RealItem = {
  id: 'quota/librechat/balanceReservation',
  domain: 'quota',
  source: {...lcSrc, path: lcPath, lines: '406-593', export: 'reserveBalance, removeReservations, renewBalanceReservation, releaseBalanceReservation'},
  also: [
    {...lcSrc, path: lcPath, lines: '227-397', export: 'updateBalance, isAutoRefillDue, settleAutoRefill, applyAutoRefill'},
    {...lcSrc, path: 'packages/api/src/middleware/checkBalance.ts', lines: '46-161,205-270', export: 'checkBalance, holdReservation'},
  ],
  summary: 'A user\'s token credits with reservations: a request is admitted against the credits no in-flight request holds and holds its cost until released or expired; spending debits the credits, and a due auto-refill adds credits once, with its ledger transaction recorded once.',
  expressible: 'partial',
  gaps: [
    {gap: 'float', blocks: 'part', detail: 'tokenCost = amount * multiplier and tokenCredits are floats; whole credits here (the held amount is Math.ceil of the cost)'},
    {gap: 'external', blocks: 'part', detail: 'MongoDB: each conditional write is one atomic step and its filter\'s read values are inputs; the reads, retries and the bulkWrite of several removals are sequences of steps'},
    {gap: 'time', blocks: 'part', detail: 'getRefillEligibilityDate adds calendar months as well as fixed units; a fixed interval in now\'s unit here'},
    {gap: 'async', blocks: 'part', detail: 'holdReservation\'s renewal timer (every half TTL) and the release on a turn\'s end are requests sent when they fire'},
  ],
  laws: [
    stepLaw(lc, lc.stepLaw('an admission reserves only credits no other request holds', ({credits}, after) => after.reserved.atMost(credits), ({reserves}) => reserves),
      'step', 'docs', 'transaction.ts:467 "Admits one request against the credits that in-flight requests have not reserved"'),
    stepLaw(lc, lc.stepLaw('releasing an unknown or already released reservation changes nothing', ({reserved, Held, id}, after) => after.reserved.eq(reserved).and(after.Held.at(id).eq(Held.at(id))), ({op, Held, id}) => op.is('release').and(Held.at(id).eq(0))),
      'step', 'docs', 'transaction.ts:583 "releasing an unknown or already pruned id is a no-op"'),
    stepLaw(lc, lc.stepLaw('a renewal never revives a released reservation', ({id}, after) => after.Held.at(id).eq(0), ({op, Held, id}) => op.is('renew').and(Held.at(id).eq(0))),
      'step', 'docs', 'transaction.ts:569 "a reservation already released or pruned stays gone"'),
    stepLaw(lc, lc.stepLaw('a reservation that has not expired is never pruned', ({Held, id}, after) => after.Held.at(id).eq(Held.at(id)), ({op, Exp, id, now}) => op.is('expire').and(Exp.at(id).gt(now))),
      'step', 'docs', 'transaction.ts:402-404 "a reservation is removed only while it is still expired at that instant, so one renewed after it was read survives"'),
    invariant(lc, lc.law('the reserved total is never negative', ({reserved}) => reserved.atLeast(0)),
      'safety', 'inferred', 'reservedCredits is the total of the held reservations (transaction.ts:400-401 "Removes reservations and their credits from the running total")'),
    invariant(lc, lc.law('an applied auto-refill is recorded at most once', ({refills, refillTx}) => refillTx.atMost(refills)),
      'safety', 'docs', 'transaction.ts:319-320 "replaying a marker left by a failed or interrupted attempt records the transaction at most once"'),
    invariant(lc, lc.law('once settled, every applied auto-refill is recorded', ({pending, refills, refillTx}) => pending.not().implies(refillTx.eq(refills))),
      'safety', 'docs', 'transaction.ts:317-318 "Records the ledger transaction of an applied auto-refill, then clears its marker"'),
    leadsTo(lc, lc.leadsTo('an applied auto-refill is eventually settled', {
      from: ({pending}) => pending,
      to: ({pending}) => pending.not(),
      helpful: () => ({op: 7, clears: 1}),
    }), 'docs', 'transaction.ts:502-504 each admission settles a marker it finds; one whose unset succeeds clears it'),
    leadsTo(lc, lc.leadsTo('every held reservation is eventually freed', {
      from: ({Held, d}) => Held.at(d).gt(0),
      to: ({Held, d}) => Held.at(d).eq(0),
      helpful: ({Held, d}) => ({op: 2, id: d, amount: Held.at(d)}),
    }), 'docs', 'checkBalance.ts:47-48 "Credits held for an admitted request until its usage has been recorded"; :52 release is idempotent'),
  ],
}

// --- LiteLLM proxy max_budget checks --------------------------------------------------------------------------------

const llSrc = {repo: 'BerriAI/litellm', commit: '49943cd52ea46aacf8db2e5cb2b890d580fe9bb4', licence: 'MIT', author: 'Berri AI', language: 'Python'}

// One key on one team, both with a max_budget (`keyLimited`/`teamLimited`: max_budget is not None, :5864, :6377).
// Spend is the cross-pod counter get_current_spend reads (proxy_server.py:3003); the read-time checks admit a request
// (:5912 key `spend >= max_budget` raises, :6386 team `spend > max_budget` raises), and after the response the cost
// callback increments both counters (proxy_server.py:3253 increment_spend_counters) by the response cost. Dollars as
// naturals in a small unit (micro-dollars; the code adds floats). `maxCost` bounds one response's cost (a modelling
// param for the overshoot law). `inflight`: admitted requests not charged yet; `overlapped`: ghost, set when a request is
// admitted while another is in flight. The pre-call reservation (budget_reservation.py) is a separate mechanism, not
// modelled (a route whose cost it cannot estimate falls back to these checks, budget_reservation.py:300-305).
export const maxBudget = () => rule('LiteLLM max_budget checks')
  .params({keyLimited: bool, keyMax: nat, teamLimited: bool, teamMax: nat, maxCost: nat})
  .inputs({op: oneOf('request', 'charge'), cost: nat})
  .assume(({cost, maxCost}) => cost.atMost(maxCost))
  .state({keySpend: 0, teamSpend: 0, inflight: 0, overlapped: bool.from(false)})
  .flags(({op, keyLimited, keyMax, teamLimited, teamMax, keySpend, teamSpend, inflight}) => ({
    // auth_checks.py:5912 `math.isfinite(valid_token.max_budget) and spend >= valid_token.max_budget` raises;
    // :6386 `math.isfinite(team_object.max_budget) and spend > team_object.max_budget` raises.
    admits: op.is('request').and(keyLimited.and(keySpend.atLeast(keyMax)).not(), teamLimited.and(teamSpend.gt(teamMax)).not()),
    // proxy_server.py:3253-3301 the cost callback of an admitted request.
    charges: op.is('charge').and(inflight.gt(0)),
  }))
  .step(({cost, keySpend, teamSpend, inflight, overlapped, admits, charges}) => ({
    keySpend: when(charges, keySpend.plus(cost), keySpend),
    teamSpend: when(charges, teamSpend.plus(cost), teamSpend),
    inflight: when(admits, inflight.plus(1), when(charges, inflight.minus(1), inflight)),
    overlapped: overlapped.or(admits.and(inflight.gt(0))),
  }))

const ll = maxBudget()
const llItem: RealItem = {
  id: 'quota/litellm/maxBudgetChecks',
  domain: 'quota',
  source: {...llSrc, path: 'litellm/proxy/auth/auth_checks.py', lines: '5853-5929,6364-6411', export: 'virtual_key_max_budget_check, team_max_budget_check'},
  also: [
    {...llSrc, path: 'litellm/proxy/proxy_server.py', lines: '3003-3070,3253-3301', export: 'get_current_spend, increment_spend_counters'},
    {...llSrc, path: 'tests/e2e/quota_management/budgets/BUDGET_CODE_MATRIX.md', lines: '20-48', export: 'budget matrix (docs)'},
  ],
  summary: 'LiteLLM\'s proxy refuses a request when the key\'s spend has reached its max_budget or the team\'s has passed its own, and adds each response\'s cost to both spend counters after the call.',
  expressible: 'partial',
  gaps: [
    {gap: 'float', blocks: 'part', detail: 'spend and max_budget are floats (with math.isfinite guards); naturals in a small unit here'},
    {gap: 'external', blocks: 'part', detail: 'the spend counters live in Redis (with in-memory and DB fallbacks and a staleness re-check against the DB, proxy_server.py:3003-3070); one consistent counter per scope here'},
    {gap: 'async', blocks: 'part', detail: 'requests run concurrently: an admission and its charge are separate requests, charged in any order'},
  ],
  laws: [
    stepLaw(ll, ll.stepLaw('a key whose spend has reached its max_budget is refused', ({inflight}, after) => after.inflight.atMost(inflight), ({op, keyLimited, keySpend, keyMax}) => op.is('request').and(keyLimited, keySpend.atLeast(keyMax))),
      'access', 'docs', 'BUDGET_CODE_MATRIX.md:39 "Spend exactly at `max_budget` blocks a key"'),
    // Refuted: a team at exactly its max_budget is admitted (:6386 `spend > max_budget`; the key's check, :5912, and
    // the user, org and window checks use `>=`). The original does it (repro/litellm-team-budget.py); the repo's own
    // budget matrix lists it as an inconsistency, not an intent (BUDGET_CODE_MATRIX.md:38-39 "Comparison operators are
    // inconsistent ... Spend exactly at `max_budget` blocks a key but not a team"). A suspected real bug: law and rule kept.
    stepLaw(ll, ll.stepLaw('a team whose spend has reached its max_budget is refused', ({inflight}, after) => after.inflight.atMost(inflight), ({op, teamLimited, teamSpend, teamMax}) => op.is('request').and(teamLimited, teamSpend.atLeast(teamMax))),
      'access', 'docs', 'auth_checks.py:6371 "Check if the team is over it\'s max budget"; the key, user, org and window checks refuse at spend >= max_budget'),
    // Stated first for every run ("a key's spend passes its max_budget by at most one request's cost"), this law was
    // refuted by requests admitted while others were in flight: each reads the counter before any response's cost is
    // added (repro/litellm-team-budget.py: two requests at 0.9 of 1.0 both admitted, 1.9 after). A law error: the
    // read-time check does not bound concurrent overspend; the pre-call reservation (budget_reservation.py, "concurrent-
    // overspend protection", :163-164) is the mechanism for that. Restated for requests that do not overlap.
    invariant(ll, ll.law("while requests do not overlap, a key's spend passes its max_budget by at most one request's cost", ({keyLimited, keySpend, keyMax, maxCost, overlapped}) => keyLimited.and(overlapped.not()).implies(keySpend.atMost(keyMax.plus(maxCost)))),
      'safety', 'inferred', 'a read-time check before each call and the cost added after it: the budget is overshot by the last admitted call'),
  ],
}

export const items: RealItem[] = [k8sItem, lcItem, llItem]
