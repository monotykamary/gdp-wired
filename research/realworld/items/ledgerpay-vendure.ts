// Vendure v2.2.7, the default order process: its transitions table and the checks its onTransitionStart makes. MIT,
// (c) 2018 Michael Bromley (Vendure was MIT up to its relicensing on 2024-07-17; v2.2.7, 2024-06-27, is MIT).
// https://github.com/vendure-ecommerce/vendure/tree/26aa924228b91eb80fabbad7d41b4f906cee7713/packages/core/src
//
// OrderStateMachine.transition (service/helpers/order-state-machine/order-state-machine.ts:44-49) runs an FSM
// (common/finite-state-machine/finite-state-machine.ts) over the process's `transitions`: a target the table doesn't
// list, or an onTransitionStart that returns a message, refuses the transition (onError throws), and the order keeps
// its state. Each event of the chart is a `transition(ctx, order, <target>)` call, named by its target. What
// onTransitionStart reads from the database (the order's payments, modifications, lines, variants, stock and
// fulfillments) comes in with the request, as the predicates and sums the code computes from it.
import {all, bool, nat, yes} from '../../../core/dsl.ts'
import {chart} from '../../../core/chart.ts'
import {type RealItem, chartLaw, chartStep, leadsTo} from '../lib.ts'

const src = {repo: 'vendure-ecommerce/vendure', commit: '26aa924228b91eb80fabbad7d41b4f906cee7713', licence: 'MIT', author: 'Michael Bromley (Vendure)', language: 'TypeScript'}
const targets = ['AddingItems', 'Draft', 'ArrangingPayment', 'PaymentAuthorized', 'PaymentSettled', 'PartiallyShipped', 'Shipped',
  'PartiallyDelivered', 'Delivered', 'Modifying', 'ArrangingAdditionalPayment', 'Cancelled'] as const
type Target = (typeof targets)[number]
// default-order-process.ts:174-236, the `transitions` table: each state and the states it may move `to`.
const table: Record<'Created' | Target, Target[]> = {
  Created: ['AddingItems', 'Draft'],
  Draft: ['Cancelled', 'ArrangingPayment'],
  AddingItems: ['ArrangingPayment', 'Cancelled'],
  ArrangingPayment: ['PaymentAuthorized', 'PaymentSettled', 'AddingItems', 'Cancelled'],
  PaymentAuthorized: ['PaymentSettled', 'Cancelled', 'Modifying', 'ArrangingAdditionalPayment'],
  PaymentSettled: ['PartiallyDelivered', 'Delivered', 'PartiallyShipped', 'Shipped', 'Cancelled', 'Modifying', 'ArrangingAdditionalPayment'],
  PartiallyShipped: ['Shipped', 'PartiallyDelivered', 'Cancelled', 'Modifying'],
  Shipped: ['PartiallyDelivered', 'Delivered', 'Cancelled', 'Modifying'],
  PartiallyDelivered: ['Delivered', 'Cancelled', 'Modifying'],
  Delivered: ['Cancelled'],
  Modifying: ['PaymentAuthorized', 'PaymentSettled', 'PartiallyShipped', 'Shipped', 'PartiallyDelivered', 'ArrangingAdditionalPayment'],
  ArrangingAdditionalPayment: ['PaymentAuthorized', 'PaymentSettled', 'PartiallyShipped', 'Shipped', 'PartiallyDelivered', 'Cancelled'],
  Cancelled: [],
}

export const orderProcess = () => {
  let c = chart('Vendure order process')
    .events(...targets)
    // What onTransitionStart reads, as the request brings it: `mods`, `unsettled`: the order's modifications and how
    // many are not settled (:262-278); `total`: order.totalWithTax; `covered`, `coveredAS`, `coveredS`:
    // totalCoveredByPayments (utils/order-utils.ts:28-44) over every payment not Error, Declined or Cancelled, over the
    // Authorized and Settled ones, over the Settled ones; `authorized`: some payment is Authorized; `lines`: how many
    // lines; `variants`: every line's variant still exists (:298-316); `customer`, `shipping`, `stock` (:317-352);
    // `allCancelled`: orderLinesAreAllCancelled (:110-112); the four fulfillment predicates (:375-400).
    .inputs({mods: nat, unsettled: nat, total: nat, covered: nat, coveredAS: nat, coveredS: nat, authorized: bool, lines: nat,
      variants: bool, customer: bool, shipping: bool, stock: bool, allCancelled: bool,
      partShipped: bool, allShipped: bool, partDelivered: bool, allDelivered: bool})
    // A ghost (not the code's): whether the order was ever PaymentAuthorized or PaymentSettled, for the law about shipping.
    .context({paid: bool.from(false)})
    .states({Created: {}, Draft: {}, AddingItems: {}, ArrangingPayment: {}, PaymentAuthorized: {}, PaymentSettled: {}, PartiallyShipped: {},
      Shipped: {}, PartiallyDelivered: {}, Delivered: {}, Modifying: {}, ArrangingAdditionalPayment: {}, Cancelled: {}}, {field: 'state'})
  for (const to of targets) {
    const from = (Object.keys(table) as ('Created' | Target)[]).filter(s => table[s].includes(to))
    if (!from.length) continue
    c = c.on(to, {from, to, ...(to === 'PaymentSettled' || to === 'PaymentAuthorized' ? {set: () => ({paid: yes})} : {}), when: env => {
      const {mods, unsettled, total, covered, coveredAS, coveredS, authorized, lines, variants, customer, shipping, stock, allCancelled} = env
      const fromModifying = to === 'ArrangingAdditionalPayment' ? mods.gt(0).and(unsettled.eq(0)).not() : unsettled.eq(0)
      return all(
        // :262-278 from Modifying: to ArrangingAdditionalPayment refused when there are modifications and all are
        // settled; to anything else refused while one is not settled.
        env.in('Modifying').implies(fromModifying),
        // :279-297 from ArrangingAdditionalPayment, unless to Cancelled: refused while `totalWithTax - covered > 0`.
        to === 'Cancelled' ? yes : env.in('ArrangingAdditionalPayment').implies(total.atMost(covered)),
        // :298-316 from AddingItems, unless to Cancelled, with lines: refused if a variant no longer exists.
        to === 'Cancelled' ? yes : env.in('AddingItems').and(lines.gt(0)).implies(variants),
        // :317-352 to ArrangingPayment: refused with no lines, no customer, no shipping line, or too little stock.
        to === 'ArrangingPayment' ? lines.gt(0).and(customer, shipping, stock) : yes,
        // :353-363 to PaymentAuthorized: the Authorized and Settled payments must cover the total, and one be
        // Authorized; to PaymentSettled: the Settled ones must cover it.
        to === 'PaymentAuthorized' ? coveredAS.atLeast(total).and(authorized) : to === 'PaymentSettled' ? coveredS.atLeast(total) : yes,
        // :364-374 to Cancelled, unless from AddingItems or ArrangingPayment: every line must be cancelled. From
        // ArrangingAdditionalPayment to Cancelled, :283-285 `if (toState === 'Cancelled') { return; }` returns from
        // onTransitionStart itself, so no check after it runs. (First modelled as skipping only the deficit check:
        // repro/conform-vendure-order.ts found the run where Vendure cancels and the rule refused, a modelling error.)
        to === 'Cancelled' ? env.in('AddingItems').or(env.in('ArrangingPayment'), env.in('ArrangingAdditionalPayment'), allCancelled) : yes,
        // :375-400 to the shipping and delivery states: the fulfillment predicates.
        to === 'PartiallyShipped' ? env.partShipped : to === 'Shipped' ? env.allShipped : to === 'PartiallyDelivered' ? env.partDelivered
          : to === 'Delivered' ? env.allDelivered : yes,
      )
    }})
  }
  return c
}

const c = orderProcess()
const ev = (t: Target) => targets.indexOf(t)
export const items: RealItem[] = [{
  id: 'payment/vendure/orderProcess',
  domain: 'payment',
  source: {...src, path: 'packages/core/src/config/order/default-order-process.ts', lines: '174-400', export: 'configureDefaultOrderProcess'},
  also: [
    {...src, path: 'packages/core/src/common/finite-state-machine/finite-state-machine.ts', lines: '37-101', export: 'FSM.transitionTo, canTransitionTo'},
    {...src, path: 'packages/core/src/service/helpers/order-state-machine/order-state-machine.ts', lines: '44-104', export: 'OrderStateMachine.transition, initConfig'},
    {...src, path: 'packages/core/src/service/helpers/utils/order-utils.ts', lines: '20-112', export: 'orderTotalIsCovered, totalCoveredByPayments, orderItemsAre*, orderLinesAreAllCancelled'},
  ],
  summary: 'The default order process: thirteen states from Created to Delivered or Cancelled, each transition allowed by the table and then checked against the payments, modifications, lines and fulfillments.',
  expressible: 'partial',
  gaps: [
    {gap: 'external', blocks: 'part', detail: "the checks read the order's payments, modifications, variants, stock and fulfillments from the database; the rule takes the predicates and sums the code computes as inputs, each free of the others"},
    {gap: 'other', blocks: 'part', detail: 'only the default process: orderOptions.process may merge in other processes (mergeTransitionDefinitions), and onTransitionEnd (placing the order, allocating stock) is not modelled'},
  ],
  laws: [
    chartStep(c, c.stepLaw('a cancelled order stays cancelled', (_, after) => after.in('Cancelled'), b => b.in('Cancelled')),
      'step', 'docs', 'default-order-process.ts:233-235 `Cancelled: { to: [] }`'),
    chartStep(c, c.stepLaw('an order is settled only when settled payments cover its total', (b, after) => after.in('PaymentSettled').implies(b.coveredS.atLeast(b.total)), b => b.in('PaymentSettled').not()),
      'step', 'docs', "default-order-process.ts:360-362 'message.cannot-transition-without-settled-payments'"),
    // A suspected real bug (triage/ledgerpay.json): from ArrangingAdditionalPayment, `if (toState === 'Cancelled') {
    // return; }` (:283-285) returns from onTransitionStart before checkAllItemsBeforeCancel runs, so an order whose
    // lines are not cancelled is cancelled from there (Created, AddingItems, ArrangingPayment, PaymentAuthorized,
    // ArrangingAdditionalPayment, Cancelled); Vendure does it (repro/conform-vendure-order.ts). Kept as stated.
    chartStep(c, c.stepLaw('a placed order is cancelled only with every line cancelled', (b, after) => after.in('Cancelled').implies(b.allCancelled), b => b.in('Cancelled').not().and(b.in('AddingItems').not(), b.in('ArrangingPayment').not())),
      'step', 'docs', 'default-order-process.ts:115-121 checkAllItemsBeforeCancel "Prevents transition to the `Cancelled` state unless all OrderItems are already cancelled. @default true"'),
    // Stated first as "an order ships only once its payment has settled" (the ghost: ever PaymentSettled), and broken
    // by Created, AddingItems, ArrangingPayment, PaymentAuthorized, Modifying, Shipped, which Vendure does too
    // (repro/conform-vendure-order.ts; createFulfillment checks no payment state, ArrangingAdditionalPayment counts
    // Authorized payments as covering). A law error: an authorized payment is enough to ship; restated as that.
    chartLaw(c, c.law('an order ships only once its payment is authorized or settled', env => env.in('Shipped').or(env.in('PartiallyShipped'), env.in('PartiallyDelivered'), env.in('Delivered')).implies(env.paid)),
      'safety', 'inferred', 'default-order-process.ts:174-236: ArrangingPayment leaves forward only to PaymentAuthorized or PaymentSettled, and every shipping state lies beyond them'),
    leadsTo(c.rule, c.rule.leadsTo('a modifying order always gets out of Modifying', {
      from: env => env.state.is('Modifying'),
      to: env => env.state.is('Modifying').not(),
      helpful: () => ({event: ev('ArrangingAdditionalPayment'), mods: 0}),
    }), 'inferred', 'Modifying is where an order waits while it is modified (order-state.ts); a transition to ArrangingAdditionalPayment with no modifications is never refused'),
  ],
}]
