// Synthetic review-routing decision + escalation step, emitted to examples/review-routing.generated.ts with zero
// runtime dependencies and re-verified by the TypeScript reader (`gdp-wired emit --verify`).
//   bun examples/review-routing.ts
//   npx gdp-wired-cli emit examples/review-routing.ts#reviewRoutingBundle --out examples/review-routing.generated.ts --check --verify
import {type EmitBundle, all, bool, decimal, fun, oneOf, proveDecision, when, yes} from '../core/dsl.ts'

export const Verdict = oneOf('approve', 'reject', 'review')

export const defaultReviewParams = {
  approveAt: 0.55,
  clearRisk: 0.35,
  blockRisk: 0.75,
  rejectAt: 0.15,
  ageLimit: 0.45,
} as const

export const makeReviewRouting = (bug?: 'drop-tamper' | 'flip-clear-risk' | 'bad-escalation') =>
  fun('review routing')
    .params({
      approveAt: decimal(4),
      clearRisk: decimal(4),
      blockRisk: decimal(4),
      rejectAt: decimal(4),
      ageLimit: decimal(4),
    })
    .inputs({
      relevance: decimal(4),
      risk: decimal(4),
      ageConcern: decimal(4),
      tamperSuspected: bool,
      explicitRequest: bool,
      secondOpinion: Verdict,
    })
    .assume(({relevance, risk, ageConcern}) => all(
      relevance.atLeast(0), relevance.atMost(1),
      risk.atLeast(0), risk.atMost(1),
      ageConcern.atLeast(0), ageConcern.atMost(1),
    ))
    .returns(({relevance, risk, ageConcern, tamperSuspected, explicitRequest, secondOpinion, approveAt, clearRisk, blockRisk, rejectAt, ageLimit}) => {
      const approve = secondOpinion.of('approve')
      const reject = secondOpinion.of('reject')
      const review = secondOpinion.of('review')
      const riskClear = bug === 'flip-clear-risk' ? risk.atMost(clearRisk) : risk.lt(clearRisk)
      const step6 = when(relevance.lt(rejectAt), reject, review)
      const step5 = when(relevance.gt(approveAt).and(riskClear), approve, step6)
      const step4 = when(explicitRequest.and(riskClear), approve, step5)
      const step3 = when(risk.atLeast(blockRisk), reject, step4)
      const step2 = when(ageConcern.atLeast(ageLimit), reject, step3)
      const decision = bug === 'drop-tamper' ? step2 : when(tamperSuspected, reject, step2)
      const final = bug === 'bad-escalation'
        ? when(decision.is('review').or(decision.is('reject')), secondOpinion, decision)
        : when(decision.is('review'), secondOpinion, decision)
      return {decision, final}
    })

export const reviewRouting = makeReviewRouting()

export const makeReviewRoutingLaws = (f = reviewRouting) => [
  f.law('tamper suspected always rejects', ({tamperSuspected}) => tamperSuspected, out => out.decision.is('reject')),
  f.law('age concern at or above limit always rejects', ({ageConcern, ageLimit}) => ageConcern.atLeast(ageLimit), out => out.decision.is('reject')),
  f.law('high risk always rejects', ({risk, blockRisk}) => risk.atLeast(blockRisk), out => out.decision.is('reject')),
  f.law('approval requires clean safety checks and signal', (_, out) => out.decision.is('approve'),
    (_out, {tamperSuspected, ageConcern, ageLimit, risk, clearRisk, blockRisk, explicitRequest, relevance, approveAt}) =>
      all(tamperSuspected.not(), ageConcern.lt(ageLimit), risk.lt(clearRisk), risk.lt(blockRisk), explicitRequest.or(relevance.gt(approveAt)))),
  f.law('escalation never turns reject into approve', (_, out) => out.decision.is('reject'), out => out.final.is('approve').not()),
]

export const reviewRoutingLaws = makeReviewRoutingLaws(reviewRouting)

export const reviewRoutingBundle: EmitBundle = {
  fun: reviewRouting,
  laws: reviewRoutingLaws,
  defaultParams: defaultReviewParams,
  name: 'reviewRouting',
}

if (import.meta.main) {
  let ok = true
  for (const l of reviewRoutingLaws) {
    const v = proveDecision(l)
    console.log(`${v.proven && v.checked ? 'ok  ' : 'FAIL'} ${l.name}`)
    if (!(v.proven && v.checked)) ok = false
  }
  const sanity = reviewRouting.run(
    {relevance: 0.72, risk: 0.12, ageConcern: 0.05, tamperSuspected: false, explicitRequest: false, secondOpinion: 'review'},
    defaultReviewParams,
  )
  console.log('sample run:', sanity)
  if (!ok || sanity.decision !== 'approve' || sanity.final !== 'approve') process.exit(1)
  void yes
}
