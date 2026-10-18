// Insurance and claims: payouts within coverage, deductible accounting, policy states, an annual paid-out limit read
// from the claims log, review before a large payout, and settlement in installments.
import {bool, count, forall, loop, maybe, nat, no, oneOf, relation, rule, upTo, when, yes} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// Coverage: a policy is written once with its coverage; a claim pays what's left of the coverage, at most.
const coverage = (bug?: 'pays the full claim' | 'rewrites a policy') => rule('payouts within coverage')
  .inputs({op: oneOf('write', 'claim'), policy: nat, amount: nat})
  .maps({Coverage: 0, Paid: 0})
  .flags(({op, policy, Coverage}) => ({writes: op.is('write').and(bug === 'rewrites a policy' ? yes : Coverage.at(policy).eq(0))}))
  .step(({op, policy, amount, writes, Coverage, Paid}) => {
    const left = Coverage.at(policy).minus(Paid.at(policy))
    return {
      Coverage: Coverage.set(policy, when(writes, amount, Coverage.at(policy))),
      Paid: Paid.bump(policy, op.is('claim'), bug === 'pays the full claim' ? amount : when(amount.lt(left), amount, left)),
    }
  })
const coverageLaws = (r: ReturnType<typeof coverage>) => [
  r.law('every policy: paid <= coverage', ({Paid, Coverage}) => forall(p => Paid.at(p).atMost(Coverage.at(p)))),
]

// The deductible: the holder pays each claim until `deductible` is met over the year, the insurer the rest.
const deductible = (bug?: 'applied per claim') => rule('deductible accounting')
  .params({deductible: nat})
  .inputs({claim: nat})
  .state({insurer: 0, holder: 0, claimed: 0})
  .step(({deductible, claim, insurer, holder, claimed}) => {
    const due = bug === 'applied per claim' ? deductible : deductible.minus(holder)
    const share = when(claim.lt(due), claim, due)
    return {holder: holder.plus(share), insurer: insurer.plus(claim.minus(share)), claimed: claimed.plus(claim)}
  })
const deductibleLaws = (r: ReturnType<typeof deductible>) => [
  r.law('insurer + holder = claimed', ({insurer, holder, claimed}) => insurer.plus(holder).eq(claimed)),
  r.law('the holder pays at most the deductible', ({holder, deductible}) => holder.atMost(deductible)),
]

// Policy states: active (0), lapsed (1) after a missed premium, cancelled (2). A premium reinstates a lapsed policy;
// only an active policy pays a claim; cancellation is final.
const states = (bug?: 'pays a lapsed policy' | 'reinstates a cancelled policy') => rule('policy states')
  .inputs({op: oneOf('premium', 'miss', 'claim', 'cancel'), amount: nat})
  .state({status: 0, paid: 0})
  .flags(({op, status}) => ({
    pays: op.is('claim').and(bug === 'pays a lapsed policy' ? status.lt(2) : status.eq(0)),
    reinstates: op.is('premium').and(bug === 'reinstates a cancelled policy' ? status.atLeast(1) : status.eq(1)),
  }))
  .step(({op, amount, status, paid, pays, reinstates}) => ({
    status: when(reinstates, 0, when(op.is('miss').and(status.eq(0)), 1, when(op.is('cancel'), 2, status))),
    paid: when(pays, paid.plus(amount), paid),
  }))
const statesLaws = (r: ReturnType<typeof states>) => [r.law('status <= 2', ({status}) => status.atMost(2))]
const statesSteps = (r: ReturnType<typeof states>) => [
  r.stepLaw('a lapsed or cancelled policy pays nothing', ({status, paid}, after) => status.eq(0).or(after.paid.eq(paid))),
  r.stepLaw('a cancelled policy stays cancelled', ({status}, after) => status.eq(2).implies(after.status.eq(2))),
  r.stepsLaw('a cancelled policy pays nothing over two steps', 2, ({status, paid}, after) => status.eq(2).implies(after.paid.eq(paid))),
]

// The annual limit: a claim is paid only if what was paid in the year before it (a query over the log) plus this
// claim stays within `limit`. `paidInYear` (a sum) is what was paid in the year ending at `now`.
const annual = (bug?: 'checks before the claim') => rule('annual paid-out limit')
  .params({year: nat, limit: nat, now: nat})
  .inputs({t: nat, amount: upTo(20)})
  .log('t', 'amount')
  .sums({paidInYear: (r, {now, year}) => when(r.t.atMost(now).and(now.lt(r.t.plus(year))), r.amount, 0)})
  .queries({paidBefore: (r, {t, year}) => when(t.lt(r.t.plus(year)), r.amount, 0)})
  .flags(({paidBefore, amount, limit}) => ({pays: bug === 'checks before the claim' ? paidBefore.atMost(limit) : paidBefore.plus(amount).atMost(limit)}))
  .keep(({pays}) => pays)
  .relations(({t, now, paidInYear, paidBefore}) => [relation(paidInYear.atMost(paidBefore), t.atMost(now))])
const annualLaw = (r: ReturnType<typeof annual>) => r.law('paid in the year ending at now <= limit', ({paidInYear, limit}) => paidInYear.atMost(limit))

// Review before a large payout: above the threshold a payout needs an adjuster's sign-off, and a high fraud score
// blocks it whatever else holds; a missing review is no review.
const approval = rule('payout approval')
  .params({threshold: upTo(10000)})
  .inputs({amount: upTo(50000), reviewed: maybe(bool), fraud: upTo(100)})
type Approval = Parameters<Parameters<typeof approval.decide>[2]>[0]
const approves = ({amount, reviewed, fraud, threshold}: Approval, grace = false) =>
  fraud.lt(80).and(amount.atMost(grace ? threshold.plus(500) : threshold).or(reviewed.match({none: () => no, some: ok => ok})))
const approvalDecisions = [
  approval.decide('a payout above the threshold never goes out unreviewed', ({amount, threshold, reviewed}) => [amount.gt(threshold), reviewed.isNone], env => approves(env).not()),
  approval.decide('a fraud score of 80 or more always blocks the payout', ({fraud}) => fraud.atLeast(80), env => approves(env).not()),
  approval.decide('a small, clean claim is always approved', ({amount, threshold, fraud}) => [amount.atMost(threshold), fraud.lt(80)], env => approves(env)),
]
const approvalBroken = [
  {name: 'a grace margin above the threshold', why: 'payouts up to 500 over the threshold skip the review',
    decision: approval.decide('a payout above the threshold never goes out unreviewed', ({amount, threshold, reviewed}) => [amount.gt(threshold), reviewed.isNone], env => approves(env, true).not())},
]

// Settling a claim in installments: each installment pays at least one unit and no more than what's left.
const installments = (bug?: 'an installment may be zero') => {
  const base = loop('settlement in installments')
    .params({claim: nat})
    .inputs({pay: nat})
    .state({left: ({claim}) => claim, paid: 0})
    .while(({left}) => left.gt(0))
    .body(({left, paid, pay}) => ({left: left.minus(pay), paid: paid.plus(pay)}))
    .rank(({left}) => left)
  return bug === 'an installment may be zero' ? base.assume(({pay, left}) => pay.atMost(left)) : base.assume(({pay, left}) => pay.atLeast(1).and(pay.atMost(left)))
}
const installmentLaws = (l: ReturnType<typeof installments>) => [
  l.law('paid + left = the claim', ({paid, left, claim}) => paid.plus(left).eq(claim)),
]

// Claims per policy holder in a period are counted from the log too: at most `limit` claims within any `period`.
const frequency = (bug?: 'off by one') => rule('claim frequency')
  .params({period: nat, limit: nat, now: nat})
  .inputs({t: nat})
  .log('t')
  .sums({recent: (r, {now, period}) => count(r.t.atMost(now).and(now.lt(r.t.plus(period))))})
  .queries({before: (r, {t, period}) => count(t.lt(r.t.plus(period)))})
  .flags(({before, limit}) => ({accepts: bug === 'off by one' ? before.atMost(limit) : before.plus(1).atMost(limit)}))
  .keep(({accepts}) => accepts)
  .relations(({t, now, recent, before}) => [relation(recent.atMost(before), t.atMost(now))])
const frequencyLaw = (r: ReturnType<typeof frequency>) => r.law('claims in the period ending at now <= limit', ({recent, limit}) => recent.atMost(limit))

const coverageFull = coverage('pays the full claim'), coverageRewrite = coverage('rewrites a policy')
const deductiblePer = deductible('applied per claim')
const statesLapsed = states('pays a lapsed policy'), statesRevive = states('reinstates a cancelled policy')
const annualEarly = annual('checks before the claim')
const installmentsZero = installments('an installment may be zero')
const frequencyOff = frequency('off by one')

export const domain: Domain = {
  domain: 'insurance',
  about: 'payouts within coverage, deductibles, policy states, annual limits from the log, payout review, installments, claim frequency',
  cases: [
    machineCase('payouts within coverage', 'no policy ever pays out more than its coverage', coverage(), coverageLaws(coverage()), [
      {name: 'pays the full claim', why: 'a claim is paid in full, past what is left of the coverage', rule: coverageFull, laws: coverageLaws(coverageFull)},
      {name: 'rewrites a policy', why: 'writing a policy again lowers its coverage below what it already paid', rule: coverageRewrite, laws: coverageLaws(coverageRewrite)},
    ]),
    machineCase('deductible accounting', 'the holder and the insurer split every claim, and the holder pays at most the deductible', deductible(), deductibleLaws(deductible()), [
      {name: 'applied per claim', why: 'the deductible is charged on every claim instead of once a year', rule: deductiblePer, laws: deductibleLaws(deductiblePer)},
    ]),
    machineCase('policy states', 'only an active policy pays, and cancellation is final', states(), statesLaws(states()), [
      {name: 'pays a lapsed policy', why: 'the claim checks that the policy isn\'t cancelled, not that it is active', rule: statesLapsed, laws: statesLaws(statesLapsed), steps: statesSteps(statesLapsed)},
      {name: 'reinstates a cancelled policy', why: 'a premium brings a cancelled policy back', rule: statesRevive, laws: statesLaws(statesRevive), steps: statesSteps(statesRevive)},
    ], {steps: statesSteps(states())}),
    machineCase('annual paid-out limit', 'what is paid in any year stays within the limit, read from the claims log', annual(), [annualLaw(annual())], [
      {name: 'checks before the claim', why: 'the check compares what was paid before the claim, not after it', rule: annualEarly, laws: [annualLaw(annualEarly)]},
    ]),
    machineCase('claim frequency', 'at most `limit` claims in any period, counted from the log', frequency(), [frequencyLaw(frequency())], [
      {name: 'off by one', why: 'a claim is accepted when the period already holds `limit` claims', rule: frequencyOff, laws: [frequencyLaw(frequencyOff)]},
    ]),
    decisionCase('payout approval', 'large payouts need a review, high fraud scores block, small clean claims go through', approvalDecisions, approvalBroken),
    loopCase('settlement in installments', 'every installment pays something and no more than is left, so the claim is settled', installments(), installmentLaws(installments()), [
      {name: 'an installment may be zero', why: 'a zero installment leaves the claim where it was, forever', loop: installmentsZero, laws: installmentLaws(installmentsZero)},
    ]),
  ],
}
