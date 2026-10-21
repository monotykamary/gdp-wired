// XState machines as charts (core/xstate.ts): a machine with nesting, a history node entered both through it and
// directly, a guard, an action and a root transition runs the same as XState's own actor and its laws prove; a parallel
// machine whose guard reads the other region; a guard given wrongly shows up as a run where the two part; and what has
// no chart counterpart is refused with the reason.
import {expect, test} from 'bun:test'
import {assign, createActor, createMachine, setup, stateIn} from 'xstate'
import {conforms, fromXState} from './xstate.ts'
import {nat} from './dsl.ts'
import {orderConfig, xorder, xorderLaws} from '../examples/xstate.ts'

// The example's config, with XState's own guards and actions.
const order = setup({
  guards: {canRetry: ({context}) => context.retries < 2, unshipped: stateIn({active: 'paid'})},
  actions: {count: assign({retries: ({context}) => context.retries + 1}), notify: () => {}},
}).createMachine(orderConfig as never)

test('a machine with nesting, history, a guard, actions and a root transition: the same runs as XState, its laws proven', () => {
  const c = xorder()
  expect(conforms(c, order, createActor, {runs: 300, depth: 16})).toEqual({checked: 300 * 16})
  expect(c.check()).toMatchObject({ok: true, stuck: [], ambiguous: []})
  expect(c.prove(xorderLaws(c).laws, xorderLaws(c).stepLaws)).toMatchObject({proven: true, checked: true})
})

test('a guard given wrongly: a run where XState and the chart part, and the law it breaks refused', () => {
  const wrong = xorder('refunds a shipped order')
  expect(conforms(wrong, order, createActor, {runs: 300, depth: 16}).failure).toMatch(/REFUND: XState is in \{"active":"shipped"\}, the chart in "refunded"/)
  expect(wrong.prove(xorderLaws(wrong).laws, xorderLaws(wrong).stepLaws).proven).toBe(false)
})

test('a parallel machine whose guard reads the other region', () => {
  const checkout = setup({guards: {paid: stateIn({payment: 'paid'})}, actions: {attempt: assign({attempts: ({context}) => context.attempts + 1})}}).createMachine({
    id: 'checkout', type: 'parallel', context: {attempts: 0},
    states: {
      payment: {initial: 'pending', states: {pending: {on: {PAY: 'paid', DECLINE: {target: 'pending', actions: 'attempt'}}}, paid: {type: 'final'}}},
      shipping: {initial: 'waiting', states: {waiting: {on: {SHIP: {target: 'sent', guard: 'paid'}}}, sent: {type: 'final'}}},
    },
  })
  const c = fromXState(checkout, {guards: {paid: env => env.in('payment.paid')}, actions: {attempt: ({attempts}) => ({attempts: attempts.plus(1)})}})
  expect(conforms(c, checkout, createActor, {runs: 200, depth: 10})).toEqual({checked: 2000})
  expect(c.prove([c.law('nothing ships unpaid', env => env.in('shipping.sent').implies(env.in('payment.paid')))])).toMatchObject({proven: true, checked: true})
})

test('events with a payload: a guard and an action read it', () => {
  const tally = setup({
    guards: {small: ({event}) => event.amount <= 3},
    actions: {add: assign({total: ({context, event}) => context.total + event.amount})},
  }).createMachine({id: 'tally', initial: 'open', context: {total: 0}, states: {open: {on: {ADD: {target: 'open', guard: 'small', actions: 'add'}, CLOSE: 'closed'}}, closed: {type: 'final'}}})
  const c = fromXState(tally, {inputs: {amount: nat}, guards: {small: ({amount}) => amount.atMost(3)}, actions: {add: ({total, amount}) => ({total: total.plus(amount)})}})
  expect(conforms(c, tally, createActor, {runs: 100, depth: 12, payload: (event, rand) => (event === 'ADD' ? {amount: rand(7)} : {amount: 0})})).toEqual({checked: 1200})
})

test('what a chart cannot run the same way is refused, with the reason', () => {
  const build = (config: Record<string, unknown>, opts = {}) => () => fromXState(createMachine(config as never), opts)
  expect(build({initial: 'a', states: {a: {always: 'b'}, b: {}}})).toThrow(/`always`/)
  expect(build({initial: 'a', states: {a: {after: {1000: 'b'}}, b: {}}})).toThrow(/`after`/)
  expect(build({initial: 'a', states: {a: {type: 'parallel', states: {x: {initial: 'p', states: {p: {}}}}}}})).toThrow(/parallel state below the root/)
  expect(build({initial: 'a', context: {n: 0}, states: {a: {on: {X: {actions: assign({n: ({context}: any) => context.n + 1})}}}}})).toThrow(/inline action \(xstate.assign\)/)
  expect(build({initial: 'a', states: {a: {on: {X: {target: 'a', guard: 'ok'}}}}})).toThrow(/the guard ok: give its condition/)
  expect(build({initial: 'a', states: {a: {on: {X: {target: 'a', actions: 'log'}}}}})).toThrow(/the action log: give the context it writes/)
  expect(build({initial: 'a', context: {n: 0}, states: {a: {entry: 'bump', on: {X: 'a'}}}}, {actions: {bump: ({n}: any) => ({n: n.plus(1)})}})).toThrow(/entry actions that write the context/)
  expect(build({initial: 'a', states: {a: {on: {'*': 'a'}}}})).toThrow(/wildcard/)
  expect(build({initial: 'a', context: {name: 'x'}, states: {a: {on: {X: 'a'}}}})).toThrow(/give its kind in context/)
  expect(build({type: 'parallel', context: {n: 0}, states: {r: {initial: 'a', states: {a: {on: {X: {actions: 'inc'}}}}}, s: {initial: 'b', states: {b: {on: {X: {actions: 'inc'}}}}}}}, {actions: {inc: ({n}: any) => ({n: n.plus(1)})}})).toThrow(/both write the context/)
  expect(build({initial: 'a', states: {a: {initial: 'p', states: {p: {initial: 'q', states: {q: {}}}, h: {type: 'history'}}, on: {X: 'a.h'}}}})).toThrow(/shallow history over nested states/)
  // an action that writes nothing is fine when said so
  expect(build({initial: 'a', states: {a: {entry: 'log', on: {X: 'a'}}}}, {actions: {log: null}})).not.toThrow()
})
