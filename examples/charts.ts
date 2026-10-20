// Statecharts (core/chart.ts): for the suite (`bun examples/charts.ts`), core/chart.test.ts and lean-kernel/package-check.ts.
//   - an order: new, then active (paid, then shipped, with its history kept), then refunded or delivered, both final; a
//     payment retried at most `tries` times. Every state is reached, none is stuck, no event is ambiguous, and its laws
//     prove: a refund never follows a shipment, the retries stay within the limit. The broken variants: a refund from
//     anywhere in active (refused: a shipped order is refunded), a second `ship` transition as specific as the first
//     (ambiguous), a state with no way out (stuck)
//   - a checkout in two parallel regions, payment and shipping, reacting to the same events: shipping waits for the
//     payment, so nothing ships unpaid; the broken variant ships without looking at the payment
import {nat} from '../core/dsl.ts'
import {chart} from '../core/chart.ts'

export const order = (bug?: 'refunds a shipped order' | 'ships two ways' | 'a state with no way out') => {
  let c = chart('order')
    .params({tries: nat})
    .context({retries: 0})
    .states({
      new: {},
      active: {states: {paid: {}, shipped: {}}, history: true},
      held: {},
      refunded: {final: true},
      delivered: {final: true},
    })
    .on('pay', {from: 'new', to: 'active'})
    .on('fail', {from: 'new', to: 'new', when: ({retries, tries}) => retries.lt(tries), set: ({retries}) => ({retries: retries.plus(1)})})
    .on('hold', {from: 'active', to: 'held'})
    .on('resume', {from: 'held', to: 'active'})
    .on('ship', {from: 'active.paid', to: 'active.shipped'})
    .on('refund', {from: bug === 'refunds a shipped order' ? 'active' : 'active.paid', to: 'refunded'})
    .on('deliver', {from: 'active.shipped', to: 'delivered'})
  if (bug === 'ships two ways') c = c.on('ship', {from: 'active.paid', to: 'delivered'})
  if (bug === 'a state with no way out') c = c.states({new: {}, active: {states: {paid: {}, shipped: {}}, history: true}, held: {}, lost: {}, refunded: {final: true}, delivered: {final: true}})
  return c
}
export const orderLaws = (c = order()) => ({
  laws: [c.law('the retries stay within the limit', ({retries, tries}) => retries.atMost(tries))],
  stepLaws: [
    c.stepLaw('a shipped order is never refunded', (_, after) => after.in('refunded').not(), before => before.in('active.shipped')),
    c.stepLaw('a held order resumes where it was', (before, after) => after.in('active.shipped'), before => before.in('held').and(before.event.is('resume'), before.last('active').is('active.shipped'))),
  ],
})

export const checkout = (bug?: 'ships unpaid') => chart('checkout')
  .regions({
    payment: {states: {pending: {}, paid: {final: true}}},
    shipping: {states: {waiting: {}, sent: {final: true}}},
  })
  .on('pay', {from: 'payment.pending', to: 'payment.paid'})
  .on('ship', {from: 'shipping.waiting', to: 'shipping.sent', when: env => (bug ? env.in('shipping') : env.in('payment.paid'))})
export const checkoutLaws = (c = checkout()) => [c.law('nothing ships unpaid', env => env.in('shipping.sent').implies(env.in('payment.paid')))]

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  const o = order(), ok = o.check({params: {tries: 2}}), {laws, stepLaws} = orderLaws(o), v = o.prove(laws, stepLaws)
  results.push(['order: every state reached, none stuck, none ambiguous', ok.ok, true], ['order: its laws', v.proven && v.checked, true])
  const refunds = order('refunds a shipped order'), rv = refunds.prove(orderLaws(refunds).laws, orderLaws(refunds).stepLaws)
  results.push(['order (refunds a shipped order): its laws', rv.proven && rv.checked, false])
  results.push(['order (ships two ways): unambiguous', order('ships two ways').check({params: {tries: 2}}).ambiguous.length === 0, false])
  results.push(['order (a state with no way out): none stuck', order('a state with no way out').check({params: {tries: 2}}).stuck.length === 0, false])
  const k = checkout(), kv = k.prove(checkoutLaws(k))
  results.push(['checkout: every state reached, none stuck, none ambiguous', k.check().ok, true], ['checkout: nothing ships unpaid', kv.proven && kv.checked, true])
  const b = checkout('ships unpaid'), bv = b.prove(checkoutLaws(b))
  results.push(['checkout (ships unpaid): nothing ships unpaid', bv.proven && bv.checked, false])
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
