// An XState machine as a chart (core/xstate.ts): for the suite (`bun examples/xstate.ts`), core/xstate.test.ts (which
// runs it beside XState's own actor) and lean-kernel/package-check.ts.
//   - an order, as XState config: new, then active (paid, then shipped) with a deep history node, held, refunded
//     (final); a payment retried while a guard allows it, counted by an action; a refund guarded to orders not shipped;
//     a hold resumed through the history node, or entered fresh; a root transition back to new. The guards and the
//     action are given again in gdp-wired's terms; the laws: the retries stay within the limit, a shipped order is never
//     refunded, resuming returns where the order was, entering active directly starts it over. The broken variant's
//     refund guard lets a shipped order through
import {fromXState} from '../core/xstate.ts'

// What createMachine takes (setup() gives XState its guards and actions: core/xstate.test.ts).
export const orderConfig = {
  id: 'order', initial: 'new', context: {retries: 0},
  states: {
    new: {on: {PAY: 'active', FAIL: {target: 'new', guard: 'canRetry', actions: ['count', 'notify']}}},
    active: {
      initial: 'paid',
      states: {paid: {on: {SHIP: 'shipped'}}, shipped: {on: {UP: '#order.active'}}, hist: {type: 'history', history: 'deep'}},
      on: {HOLD: 'held', TOP: 'active', REFUND: {target: 'refunded', guard: 'unshipped'}},
    },
    held: {on: {RESUME: 'active.hist', FRESH: 'active'}},
    refunded: {type: 'final'},
  },
  on: {RESET: '.new'},
} as const

export const xorder = (bug?: 'refunds a shipped order') => fromXState(orderConfig, {
  guards: {canRetry: ({retries}) => retries.lt(2), unshipped: env => (bug ? env.in('active') : env.in('active.paid'))},
  actions: {count: ({retries}) => ({retries: retries.plus(1)}), notify: null},
})
export const xorderLaws = (c = xorder()) => ({
  laws: [c.law('the retries stay within 2', ({retries}) => retries.atMost(2))],
  stepLaws: [
    c.stepLaw('a shipped order is never refunded', (_, after) => after.in('refunded').not(), before => before.in('active.shipped')),
    c.stepLaw('resuming returns to where the order was', (_, after) => after.in('active.shipped'), before => before.in('held').and(before.event.is('RESUME'), before.last('active').is('active.shipped'))),
    c.stepLaw('entering active directly starts it over', (_, after) => after.in('active.paid'), before => before.in('held').and(before.event.is('FRESH'))),
  ],
})

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  const o = xorder(), {laws, stepLaws} = xorderLaws(o), v = o.prove(laws, stepLaws)
  results.push(['order (XState): every state reached, none stuck, none ambiguous', o.check().ok, true], ['order (XState): its laws', v.proven && v.checked, true])
  const b = xorder('refunds a shipped order'), bv = b.prove(xorderLaws(b).laws, xorderLaws(b).stepLaws)
  results.push(['order (XState, refunds a shipped order): its laws', bv.proven && bv.checked, false])
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
