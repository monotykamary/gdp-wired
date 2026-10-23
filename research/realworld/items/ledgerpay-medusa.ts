// Medusa v2.22.0: an order item's fulfilment and return quantities (the order module's change actions) and a payment's
// captures and refunds (the payment module). MIT, (c) Medusa (the files read are under the MIT licence; the repo's
// Enterprise Edition materials are not among them).
// https://github.com/medusajs/medusa/tree/205aff40bacfa0049e0b9d3a7913a674738bff31/packages/modules
//
// Order item: each order change action (actions/*.ts) is registered with OrderChangeProcessing
// (calculate-order-change.ts:43-45), which runs its `validate` and then its `operation` (:195-205) on the item the
// action's `reference_id` names. A `validate` that throws aborts the change: nothing changes, which the step says as
// "every part keeps its value". The rule is one order item (actions on other items never touch it); its quantity at
// the start is the param `q0`, every detail quantity starts at 0 (the `??= 0` in each operation).
import {type Bool, type Term, bool, int, nat, oneOf, record, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, leadsTo, stepLaw} from '../lib.ts'

const src = {repo: 'medusajs/medusa', commit: '205aff40bacfa0049e0b9d3a7913a674738bff31', licence: 'MIT', author: 'Medusa', language: 'TypeScript'}
const action = (file: string, lines: string, exp: string) => ({...src, path: `packages/modules/order/src/utils/actions/${file}.ts`, lines, export: exp})

export const orderItem = () => rule('Medusa order item')
  .params({q0: nat})
  // One action: its type (ChangeActionType) and `action.details.quantity`, a number (BigNumberInput): any integer,
  // negative too (no validate bounds it below except where it says `< 1` or `<= 0`).
  .inputs({op: oneOf('fulfill', 'ship', 'deliver', 'cancelFulfillment', 'return', 'receive', 'receiveDamaged', 'cancelReturn', 'writeOff', 'reinstate', 'update', 'remove'), q: int})
  // The item's `quantity` and its `detail.*_quantity` fields.
  .ints({quantity: ({q0}) => q0, fulfilled: 0, shipped: 0, delivered: 0, requested: 0, received: 0, dismissed: 0, writtenOff: 0})
  .flags(({op, q, quantity, fulfilled, shipped, delivered, requested}) => {
    // `if (!action.details?.quantity) throw`: a zero quantity is refused.
    const given = q.eq(0).not()
    return {
      // fulfill-item.ts:24-65: quantity given, `quantity < 1` refused, `quantity > quantity - fulfilled_quantity` refused.
      fulfills: op.is('fulfill').and(given, q.lt(1).not(), q.gt(quantity.minus(fulfilled)).not()),
      // ship-item.ts:24-66: given, `MathBN.lt(quantity, 1)` refused, more than `fulfilled - shipped` refused.
      ships: op.is('ship').and(given, q.lt(1).not(), q.gt(fulfilled.minus(shipped)).not()),
      // deliver-item.ts:24-69: `newDelivered <= 0` refused; `delivered + q` above the fulfilled or the ordered quantity refused.
      delivers: op.is('deliver').and(q.atMost(0).not(), delivered.plus(q).gt(fulfilled).not(), delivered.plus(q).gt(quantity).not()),
      // cancel-item-fulfillment.ts:26-67: given, `< 1` refused, more than `fulfilled_quantity` refused.
      cancels: op.is('cancelFulfillment').and(given, q.lt(1).not(), q.gt(fulfilled).not()),
      // return-item.ts:26-62: given, more than `fulfilled - return_requested` refused.
      returns: op.is('return').and(given, q.gt(fulfilled.minus(requested)).not()),
      // receive-return-item.ts:34-67 and receive-damaged-return-item.ts:42-73: given, more than `return_requested` refused.
      receives: op.is('receive').and(given, q.gt(requested).not()),
      damaged: op.is('receiveDamaged').and(given, q.gt(requested).not()),
      // cancel-return.ts:26-60: given, more than `return_requested` refused.
      cancelsReturn: op.is('cancelReturn').and(given, q.gt(requested).not()),
      // write-off-item.ts:23-55 and reinstate-item.ts:23-55: given, more than the item's `quantity` refused.
      writesOff: op.is('writeOff').and(given, q.gt(quantity).not()),
      reinstates: op.is('reinstate').and(given, q.gt(quantity).not()),
      // item-update.ts:71-108: `quantity == null` refused (a request always carries one), lower than `fulfilled_quantity` refused.
      updates: op.is('update').and(q.lt(fulfilled).not()),
      // item-remove.ts:30-72: given, `< 1` refused, more than `quantity - fulfilled_quantity` refused.
      removes: op.is('remove').and(given, q.lt(1).not(), q.gt(quantity.minus(fulfilled)).not()),
    }
  })
  .step(({q, quantity, fulfilled, shipped, delivered, requested, received, dismissed, writtenOff,
    fulfills, ships, delivers, cancels, returns, receives, damaged, cancelsReturn, writesOff, reinstates, updates, removes}) => ({
    // item-update.ts:24-27 `existing.quantity = currentQuantity`; item-remove.ts:19-24 `quantity - action.details.quantity`.
    quantity: when(updates, q, when(removes, quantity.minus(q), quantity)),
    // fulfill-item.ts:15-20 `fulfilled_quantity + quantity`; cancel-item-fulfillment.ts:17-22 `fulfilled_quantity - quantity`.
    fulfilled: when(fulfills, fulfilled.plus(q), when(cancels, fulfilled.minus(q), fulfilled)),
    // ship-item.ts:15-20, deliver-item.ts:15-20.
    shipped: when(ships, shipped.plus(q), shipped),
    delivered: when(delivers, delivered.plus(q), delivered),
    // return-item.ts:15-19 `return_requested + quantity`; receive-return-item.ts:25-28, receive-damaged-return-item.ts:27-30
    // and cancel-return.ts:15-20 `return_requested - quantity`.
    requested: when(returns, requested.plus(q), when(receives.or(damaged, cancelsReturn), requested.minus(q), requested)),
    // receive-return-item.ts:19-24 `return_received + quantity`; receive-damaged-return-item.ts:21-26 `return_dismissed + quantity`.
    received: when(receives, received.plus(q), received),
    dismissed: when(damaged, dismissed.plus(q), dismissed),
    // write-off-item.ts:14-19 and receive-damaged-return-item.ts:31-35 `written_off + quantity`; reinstate-item.ts:14-19 `- quantity`.
    writtenOff: when(writesOff.or(damaged), writtenOff.plus(q), when(reinstates, writtenOff.minus(q), writtenOff)),
  }))

const o = orderItem()
const orderItemQuantities: RealItem = {
  id: 'payment/medusa/orderItemQuantities',
  domain: 'payment',
  source: action('fulfill-item', '9-67', 'FULFILL_ITEM'),
  also: [
    action('ship-item', '9-68', 'SHIP_ITEM'), action('deliver-item', '9-71', 'DELIVER_ITEM'),
    action('cancel-item-fulfillment', '9-70', 'CANCEL_ITEM_FULFILLMENT'), action('return-item', '9-64', 'RETURN_ITEM'),
    action('receive-return-item', '9-69', 'RECEIVE_RETURN_ITEM'), action('receive-damaged-return-item', '9-76', 'RECEIVE_DAMAGED_RETURN_ITEM'),
    action('cancel-return', '9-62', 'CANCEL_RETURN_ITEM'), action('write-off-item', '9-57', 'WRITE_OFF_ITEM'),
    action('reinstate-item', '9-57', 'REINSTATE_ITEM'), action('item-update', '11-109', 'ITEM_UPDATE'), action('item-remove', '9-74', 'ITEM_REMOVE'),
    {...src, path: 'packages/modules/order/src/utils/calculate-order-change.ts', lines: '164-210', export: 'OrderChangeProcessing.processAction_'},
  ],
  summary: "An order item's fulfilled, shipped, delivered, return-requested, received, dismissed and written-off quantities, each action validated against the others before it changes one.",
  expressible: 'partial',
  gaps: [
    {gap: 'float', blocks: 'part', detail: 'quantities are BigNumbers and may be fractional; the rule takes integers (every validate compares them the same way)'},
  ],
  laws: [
    invariant(o, o.law('never more fulfilled than ordered', ({fulfilled, quantity}) => fulfilled.atMost(quantity)),
      'safety', 'docs', 'fulfill-item.ts:63 "Cannot fulfill more items than what was ordered"; item-update.ts:105 "quantity cannot be lower than" the fulfilled'),
    // Stated first as invariants ("never more shipped than fulfilled", "never more delivered than fulfilled"), both
    // were refuted: fulfil 1, ship (or deliver) 1, cancel the fulfilment of 1 leaves shipped 1 over fulfilled 0, and the
    // original does the same (repro/conform-medusa-order.ts). A law error: CANCEL_ITEM_FULFILLMENT checks only the
    // fulfilled count, and the module leaves "not a shipped fulfilment" to the workflow that calls it
    // (core-flows cancel-order-fulfillment.ts:127 `if (fulfillment.shipped_at)` throws). Restated as what the actions
    // keep: no step but a cancelled fulfilment takes either past the fulfilled count.
    stepLaw(o, o.stepLaw('only a cancelled fulfilment takes the shipped past the fulfilled', (_, after) => after.shipped.atMost(after.fulfilled),
      ({op, shipped, fulfilled}) => op.is('cancelFulfillment').not().and(shipped.atMost(fulfilled))),
      'step', 'docs', 'ship-item.ts:64 "Cannot ship more items than what was fulfilled"'),
    stepLaw(o, o.stepLaw('only a cancelled fulfilment takes the delivered past the fulfilled', (_, after) => after.delivered.atMost(after.fulfilled),
      ({op, delivered, fulfilled}) => op.is('cancelFulfillment').not().and(delivered.atMost(fulfilled))),
      'step', 'docs', 'deliver-item.ts:60 "Cannot deliver more items than what was fulfilled"'),
    // Refuted, and kept: a suspected real bug (triage/ledgerpay.json). RETURN_ITEM checks `fulfilled - return_requested`
    // and forgets what was already received, so fulfil 1, return 1, receive 1, return 1, receive 1 receives 2 of 1; and
    // a negative quantity passes (cancel-return of -2 requests 2 back of 0 fulfilled). The original does both.
    invariant(o, o.law('never more returned than fulfilled', ({requested, received, dismissed, fulfilled}) => requested.plus(received).plus(dismissed).atMost(fulfilled)),
      'safety', 'docs', 'return-item.ts:60 "Cannot request to return more items than what was fulfilled"'),
    // Refuted, and kept: a suspected real bug. WRITE_OFF_ITEM compares one action's quantity with the item's, not the
    // total written off (two write-offs of 2 write off 4 of 2), and a negative REINSTATE_ITEM adds to it.
    invariant(o, o.law('never more written off than ordered', ({writtenOff, quantity}) => writtenOff.atMost(quantity)),
      'safety', 'docs', 'write-off-item.ts:53 "Cannot claim more items than what was ordered."'),
    stepLaw(o, o.stepLaw('a receipt never takes the requested count below zero', (_, after) => after.requested.atLeast(0), ({op, requested}) => op.is('receive').and(requested.atLeast(0))),
      'step', 'docs', 'receive-return-item.ts:65 "Cannot receive more items than what was requested to be returned"'),
    stepLaw(o, o.stepLaw('an update never sets the quantity below the fulfilled', (_, after) => after.fulfilled.atMost(after.quantity), ({updates}) => updates),
      'step', 'docs', 'item-update.ts:105 "quantity cannot be lower than" the fulfilled quantity'),
    // "Received" is "nothing left requested" (at most 0): a negative quantity (cancel-return, receive) can take the
    // requested count past 0 in one step, and the original does the same (repro/conform-medusa-order.ts).
    leadsTo(o, o.leadsTo('every requested return is received in the end', {
      from: ({requested}) => requested.gt(0),
      to: ({requested}) => requested.atMost(0),
      helpful: ({requested}) => ({op: 5, q: requested.pos, q$neg: requested.neg}),
    }), 'inferred', 'a return request is resolved by receiving it (receive-return-item.ts), when the warehouse receives what was requested'),
  ],
}

// Payment: one payment of the payment module (payment-module.ts), from its authorization on. Amounts are in the
// currency's smallest unit, where `roundToCurrencyPrecision` (:171-187) is the identity and the refund guard's
// epsilon (:1135-1149, below one unit) lets nothing over; the provider's answer to each call is an input.
const amountOf = (full: Bool, amt: Term, amount: Term) => when(full, amount, amt)
const Refund = record({status: oneOf('none', 'pending', 'succeeded', 'failed'), amount: nat, started: nat, deleted: bool})
export const payment = () => rule('Medusa payment')
  // `payment.raw_amount`, the authorized amount; `d`: the idempotency key a liveness law watches (not the code's).
  .params({amount: nat, d: nat})
  // One call: capturePayment, refundPayment or cancelPayment; `full`: `data.amount == null`; `amt`: `data.amount`;
  // `isCaptured`: the `is_captured` flag (an auto-captured session, :686-692); `key`: `data.idempotency_key` (0: none);
  // `now`: Date.now() (:1029, sent in with the request); `outcome`: the provider's answer, or `crash` when the process
  // dies between the provider call and the status update (the case :1020-1026 describes).
  .inputs({op: oneOf('capture', 'refund', 'cancel'), full: bool, amt: nat, isCaptured: bool, key: nat, now: nat, outcome: oneOf('ok', 'fail', 'crash')})
  // `captured`: the sum of the payment's captures (:839-844); `capturedAt`, `canceled`: `captured_at`, `canceled_at`;
  // `refunded`: the sum of its refunds that are not soft-deleted (:1117-1131), kept as a running total (a ghost of
  // the query the code makes, changed where a refund is created, restored or soft-deleted).
  .state({captured: 0, capturedAt: bool.from(false), canceled: bool.from(false), refunded: 0})
  // The refunds that carry an idempotency key, by key; a refund without one is only its amount in `refunded`.
  .maps({Refunds: Refund.from({status: 'none', amount: 0, started: 0, deleted: false})})
  .flags(({op, full, amt, isCaptured, key, now, outcome, amount, captured, capturedAt, canceled, refunded, Refunds}) => {
    // :805-812 (capture) and :1065-1072 (refund): no amount is the payment's whole amount; an explicit one must be > 0.
    const a = amountOf(full, amt, amount), positive = full.or(amt.gt(0))
    const m = Refunds.at(key), keyed = key.gt(0).and(m.status.is('none').not())
    // resolveRefundRequest_ (:1000-1053): a keyed match of another amount throws (:1013-1018); a pending one throws
    // unless stale (:1020-1037), `Date.now() - startedAt > PENDING_REFUND_RECOVERY_MS` (15 minutes, :94); a succeeded
    // one is a replay (:1046-1048); a failed one, or a stale pending one, is resumed.
    const sameAmount = m.amount.eq(a), stale = now.gt(m.started.plus(15 * 60 * 1000))
    const replays = op.is('refund').and(positive, keyed, sameAmount, m.status.is('succeeded'))
    const resumes = keyed.and(sameAmount, m.status.is('failed').or(m.status.is('pending').and(stale)))
    // :1117-1131: the refunds not soft-deleted, the resumed one left out, plus this one; over what is captured throws.
    const others = refunded.minus(when(resumes.and(m.deleted.not()), m.amount, 0))
    const refunds = op.is('refund').and(positive, keyed.not().or(resumes), others.plus(a).atMost(captured))
    // capturePayment_ (:784-882): a canceled payment throws (:792-797); a captured one returns without a capture
    // (:799-801); more than `authorized - captured` throws (:846-860). capturePayment (:747-762): the provider is called
    // unless `isCaptured` (:893-910), and if it throws the capture is deleted (:757-761).
    const captures = op.is('capture').and(canceled.not(), capturedAt.not(), positive, a.atMost(amount.minus(captured)), isCaptured.or(outcome.is('fail').not()))
    return {replays, resumes, refunds, captures,
      // :893-924: captured_at is set once the captures reach the authorized amount, when the provider
      // answered (or the payment was captured already); a crash before the update leaves it unset.
      completes: captures.and(captured.plus(a).atLeast(amount), isCaptured.or(outcome.is('ok'))),
      // cancelPayment (:1214-1240): the provider's cancel, then `canceled_at`; no check of what was captured.
      cancels: op.is('cancel').and(outcome.is('ok'))}
  })
  .step(({full, amt, amount, key, now, outcome, captured, capturedAt, canceled, refunded, Refunds, resumes, refunds, captures, completes, cancels}) => {
    const m = Refunds.at(key), a = amountOf(full, amt, amount)
    // :1160-1170 a resumed refund restored if soft-deleted, then pending (its `updated_at` now); :1172-1183 a new one
    // pending; then refundPayment (:960-976): a provider error marks it failed and soft-deletes it, success marks it
    // succeeded; a crash leaves it pending.
    const status = when(outcome.is('ok'), 'succeeded', when(outcome.is('fail'), 'failed', when(outcome.is('crash'), 'pending', m.status)))
    const before = when(resumes, when(m.deleted, 0, a), 0) // what of this refund `refunded` already counts
    return {
      captured: when(captures, captured.plus(a), captured),
      capturedAt: completes.or(capturedAt),
      canceled: cancels.or(canceled),
      refunded: when(refunds, when(outcome.is('fail'), refunded.minus(before), refunded.minus(before).plus(a)), refunded),
      Refunds: Refunds.set(key, when(refunds.and(key.gt(0)), {status, amount: a, started: now, deleted: outcome.is('fail')}, m)),
    }
  })

const p = payment()
const pay = (lines: string, exp: string) => ({...src, path: 'packages/modules/payment/src/services/payment-module.ts', lines, export: exp})
const captureRefund: RealItem = {
  id: 'payment/medusa/captureRefund',
  domain: 'payment',
  source: pay('715-1240', 'PaymentModuleService.capturePayment, refundPayment, cancelPayment'),
  also: [pay('94', 'PENDING_REFUND_RECOVERY_MS'), pay('171-190', 'roundToCurrencyPrecision')],
  summary: "A payment's captures (up to the authorized amount, none once canceled) and refunds (up to what is captured), with idempotency keys that replay a succeeded refund and resume a failed or stale pending one.",
  expressible: 'partial',
  gaps: [
    {gap: 'float', blocks: 'part', detail: 'amounts are BigNumbers rounded to the currency precision (Intl.NumberFormat) and compared with an epsilon; the rule takes amounts in the smallest unit, where both are exact'},
    {gap: 'async', blocks: 'part', detail: 'the capture or refund row commits before the provider call, outside the row lock; the rule makes each call one step, so a refund between a capture and its provider failure (which deletes the capture) is not a run of the rule'},
  ],
  laws: [
    invariant(p, p.law('never more captured than authorized', ({captured, amount}) => captured.atMost(amount)),
      'safety', 'docs', 'payment-module.ts:858 "You cannot capture more than the authorized amount substracted by what is already captured."'),
    invariant(p, p.law('never more refunded than captured', ({refunded, captured}) => refunded.atMost(captured)),
      'safety', 'docs', 'payment-module.ts:1148 "You cannot refund more than what is captured on the payment."'),
    stepLaw(p, p.stepLaw('a canceled payment is never captured', ({captured}, after) => after.captured.eq(captured), ({canceled}) => canceled),
      'step', 'docs', 'payment-module.ts:795 "The payment: ${payment.id} has been canceled."'),
    stepLaw(p, p.stepLaw('a replayed refund moves no funds', ({refunded}, after) => after.refunded.eq(refunded), ({replays}) => replays),
      'step', 'docs', 'payment-module.ts:1114 "A replay moves no additional funds"'),
    leadsTo(p, p.leadsTo('a pending refund with a key is resolved once retried', {
      from: ({Refunds, d}) => d.gt(0).and(Refunds.at(d).status.is('pending')),
      to: ({Refunds, d}) => Refunds.at(d).status.is('succeeded').or(Refunds.at(d).status.is('failed')),
      helpful: ({Refunds, d}) => ({op: 1, full: when(Refunds.at(d).amount.eq(0), 1, 0), amt: Refunds.at(d).amount, key: d, now: Refunds.at(d).started.plus(15 * 60 * 1000 + 1), outcome: 0}),
    }), 'docs', 'payment-module.ts:1020-1026 "past a grace period the refund is retried instead"; fair: a retry with the same key once the provider answers'),
  ],
}

export const items: RealItem[] = [orderItemQuantities, captureRefund]
