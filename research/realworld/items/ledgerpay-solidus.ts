// Solidus v4.8.0, Spree::Payment's state machine (the state_machines gem), its capture and its refunds. BSD-3-Clause,
// (c) Solidus. https://github.com/solidusio/solidus/tree/8acbcba84621fa0d2b8c06acb6ccfdc36ada4bc9/core
//
// The six events are the gem's: each fires only from the states its `transition from:` lists; firing it from another
// state is refused (the bang form raises StateMachines::InvalidTransition): nothing changes. `capture!` and creating a
// Spree::Refund are what move money; their checks are as the code makes them. Amounts are in cents (capture! takes
// cents; `money.money.cents` of a BigDecimal amount is exact for the currency's cents).
import {type Choice, any, bool, nat, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, leadsTo, stepLaw} from '../lib.ts'

const src = {repo: 'solidusio/solidus', commit: '8acbcba84621fa0d2b8c06acb6ccfdc36ada4bc9', licence: 'BSD-3-Clause', author: 'Solidus', language: 'Ruby'}
const states = ['checkout', 'processing', 'pending', 'completed', 'failed', 'void', 'invalid'] as const
type S = (typeof states)[number]
// state_machines/payment.rb:21-49: each event and the states it fires from (`transition from: [...], to: ...`).
const events = {
  started_processing: {from: ['checkout', 'pending', 'completed', 'processing'], to: 'processing'}, // :27-29
  failure: {from: ['pending', 'processing'], to: 'failed'}, // :31-33
  pend: {from: ['checkout', 'processing'], to: 'pending'}, // :35-37
  complete: {from: ['processing', 'pending', 'checkout'], to: 'completed'}, // :39-41
  void: {from: ['pending', 'processing', 'completed', 'checkout'], to: 'void'}, // :42-44
  invalidate: {from: ['checkout'], to: 'invalid'}, // :46-48
} as const satisfies Record<string, {from: readonly S[], to: S}>
const among = (st: Choice<S>, xs: readonly S[]) => any(...xs.map(x => st.is(x)))
const fires = (e: keyof typeof events, ev: Choice<keyof typeof events | 'capture' | 'refund'>, st: Choice<S>) => ev.is(e).and(among(st, events[e].from))

export const solidusPayment = () => rule('Spree::Payment')
  // `amount0`: the payment's amount when created; `requireRefundable`: Spree::Config.require_refundable_payment_state
  // (app_configuration.rb:296-298, false until 5.0); the refundable states are the default %w[completed pending] (:288-290).
  .params({amount0: nat, requireRefundable: bool})
  // One call: an event, `capture!(amt)` (`full`: no amount given) with the gateway's answer `ok`, or a Refund created
  // with `amt`.
  .inputs({ev: oneOf(...Object.keys(events) as (keyof typeof events)[], 'capture', 'refund'), amt: nat, full: bool, ok: bool})
  // `state`, `amount`; `captured`: capture_events' sum (payment.rb:139-141); `refunded`: refunds.sum(:amount) (:93-95).
  .state({st: oneOf(...states).from('checkout'), amount: ({amount0}) => amount0, captured: 0, refunded: 0})
  .flags(({ev, amt, st, amount, refunded, requireRefundable}) => ({
    starts: fires('started_processing', ev, st), fails: fires('failure', ev, st), pends: fires('pend', ev, st),
    completes: fires('complete', ev, st), voids: fires('void', ev, st), invalidates: fires('invalidate', ev, st),
    // processing.rb:73-91 capture!: `return true if completed?`, `return false unless amount.positive?`, then
    // started_processing! (raises from failed, void or invalid).
    captures: ev.is('capture').and(st.is('completed').not(), amount.gt(0), among(st, events.started_processing.from)),
    // refund.rb:15 `numericality: {greater_than: 0}`; :89-93 `amount > payment.credit_allowed` is an error, where
    // credit_allowed is `amount - refunds.sum(:amount)` (payment.rb:93-95); :95-109 a state outside the refundable
    // ones is an error only when requireRefundable (else a deprecation warning).
    refunds: ev.is('refund').and(amt.gt(0), amt.atMost(amount.minus(refunded)), requireRefundable.not().or(among(st, ['completed', 'pending']))),
  }))
  .step(({amt, full, ok, st, amount, captured, refunded, captures, refunds, starts, fails, pends, completes, voids, invalidates}) => {
    // processing.rb:77-89: `capture_amount ||= money.money.cents`; capture_events.create!(amount); update!(amount:
    // captured_amount); `complete! if handle_response(response)`, where a failed response fires `failure` (:185-192).
    const c = when(full, amount, amt)
    return {
      st: when(captures.and(ok), 'completed', when(captures, 'failed', when(starts, 'processing', when(fails, 'failed', when(pends, 'pending',
        when(completes, 'completed', when(voids, 'void', when(invalidates, 'invalid', st)))))))),
      captured: when(captures, captured.plus(c), captured),
      amount: when(captures, captured.plus(c), amount),
      refunded: when(refunds, refunded.plus(amt), refunded),
    }
  })

const r = solidusPayment()
export const items: RealItem[] = [{
  id: 'payment/solidus/Payment',
  domain: 'payment',
  source: {...src, path: 'core/app/models/spree/core/state_machines/payment.rb', lines: '21-49', export: 'Spree::Core::StateMachines::Payment'},
  also: [
    {...src, path: 'core/app/models/spree/payment/processing.rb', lines: '73-91', export: 'Spree::Payment::Processing#capture!'},
    {...src, path: 'core/app/models/spree/refund.rb', lines: '13-109', export: 'Spree::Refund validations'},
    {...src, path: 'core/app/models/spree/payment.rb', lines: '92-146', export: 'Spree::Payment#credit_allowed, captured_amount'},
    {...src, path: 'core/lib/spree/app_configuration.rb', lines: '288-298', export: 'refundable_payment_states, require_refundable_payment_state'},
  ],
  summary: "A payment's states (checkout, processing, pending, completed, failed, void, invalid) under the gem's six events, its capture (which resets the amount to what was captured) and its refunds (up to the amount less earlier refunds).",
  expressible: 'partial',
  gaps: [
    {gap: 'other', blocks: 'part', detail: 'authorize!, purchase! and void_transaction! (each an event or two around a gateway call) are not their own requests: the rule has their events one at a time, which covers every order they fire them in, and more'},
  ],
  laws: [
    // Refuted, and kept: a suspected real bug (triage/ledgerpay.json, repro/solidus-refund-capture.rb). A refund of
    // the whole amount on a pending (authorized) payment is valid by default, and a partial capture! afterwards sets
    // the amount to what was captured (processing.rb:88), below the refunds: credit_allowed goes negative.
    invariant(r, r.law('refunds never exceed the payment amount', ({refunded, amount}) => refunded.atMost(amount)),
      'safety', 'docs', 'refund.rb:89-93 `amount > payment.credit_allowed` is :greater_than_allowed; payment.rb:92 "the amount of this payment minus refunds"'),
    stepLaw(r, r.stepLaw('a failed, void or invalid payment never changes state', ({st}, after) => after.st.eq(st), ({st}) => among(st, ['failed', 'void', 'invalid'])),
      'step', 'docs', 'state_machines/payment.rb:21-49: no event fires from failed, void or invalid'),
    stepLaw(r, r.stepLaw('when required, a refund only on a completed or pending payment', ({st, refunded}, after) => after.refunded.atMost(refunded).or(among(st, ['completed', 'pending'])), ({requireRefundable}) => requireRefundable),
      'step', 'docs', 'app_configuration.rb:296-297 "creating a refund for a payment outside Spree::Config.refundable_payment_states is a validation error"'),
    stepLaw(r, r.stepLaw('a capture never lowers what was captured', ({captured}, after) => captured.atMost(after.captured)),
      'step', 'inferred', 'capture_events are only created (processing.rb:67, :87); captured_amount is their sum'),
    leadsTo(r, r.leadsTo('a processing payment is resolved', {
      from: ({st}) => st.is('processing'),
      to: ({st}) => st.is('processing').not(),
      helpful: () => ({ev: 3}),
    }), 'inferred', 'processing is the state a payment is in during a gateway call (processing.rb:40-49, :56-65): it ends in complete!, pend! or failure'),
  ],
}]
