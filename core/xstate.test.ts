// XState machines as charts (core/xstate.ts): a machine with nesting, a history node entered both through it and
// directly, a guard, an action and a root transition runs the same as XState's own actor and its laws prove; a parallel
// machine whose guard reads the other region; a guard given wrongly shows up as a run where the two part; and what has
// no chart counterpart is refused with the reason.
import {expect, test} from 'bun:test'
import {assign, createActor, createMachine, fromPromise, setup, stateIn} from 'xstate'
import {type Guard, conforms, fromXState} from './xstate.ts'
import {type Term, nat, no} from './dsl.ts'
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
  expect(build({initial: 'a', states: {a: {always: 'b'}, b: {}}})).toThrow(/an eventless transition the machine takes at once from its initial state/)
  expect(build({initial: 'a', states: {a: {type: 'parallel', states: {x: {initial: 'p', states: {p: {}}}}}}})).toThrow(/parallel state below the root/)
  expect(build({initial: 'a', context: {n: 0}, states: {a: {on: {X: {actions: assign({n: ({context}: any) => context.n + 1})}}}}})).toThrow(/inline action \(xstate.assign\)/)
  expect(build({initial: 'a', states: {a: {on: {X: {target: 'a', guard: 'ok'}}}}})).toThrow(/the guard ok: give its condition/)
  expect(build({initial: 'a', states: {a: {on: {X: {target: 'a', actions: 'log'}}}}})).toThrow(/the action log: give the context it writes/)
  expect(build({initial: 'a', context: {n: 0}, states: {a: {entry: 'take', on: {X: 'a'}}}}, {inputs: {amount: nat}, actions: {take: ({n, amount}: any) => ({n: n.plus(amount)})}})).toThrow(/entry actions or an eventless transition at the start that read amount/)
  expect(build({initial: 'a', states: {a: {on: {'*': 'a'}}}})).toThrow(/wildcard/)
  expect(build({initial: 'a', context: {name: 'x'}, states: {a: {on: {X: 'a'}}}})).toThrow(/give its kind in context/)
  expect(build({type: 'parallel', context: {n: 0}, states: {r: {initial: 'a', states: {a: {on: {X: {actions: 'inc'}}}}}, s: {initial: 'b', states: {b: {on: {X: {actions: 'inc'}}}}}}}, {actions: {inc: ({n}: any) => ({n: n.plus(1)})}})).toThrow(/both write the context/)
  expect(build({initial: 'a', states: {a: {initial: 'p', states: {p: {initial: 'q', states: {q: {}}}, h: {type: 'history'}}, on: {X: 'a.h'}}}})).toThrow(/shallow history over nested states/)
  // an action that writes nothing is fine when said so
  expect(build({initial: 'a', states: {a: {entry: 'log', on: {X: 'a'}}}}, {actions: {log: null}})).not.toThrow()
})

// The real-world corpus found v4's `cond` dropped: a v4 config was taken with its guards gone, so laws were proven of a
// machine with fewer guards than the real one. Every key fromXState doesn't read is refused now, and `cond` is read as
// v4 reads it.
test('every key fromXState does not read is refused, by name, rather than dropped', () => {
  const build = (config: Record<string, unknown>, opts = {}) => () => fromXState(config, opts)
  const v5 = (config: Record<string, unknown>) => () => fromXState(createMachine(config as never), {guards: {ok: () => no}})
  // XState v5 doesn't read `cond` (it takes the transition unguarded), nor v4 `guard`: a v5 machine with `cond` refused
  expect(v5({initial: 'a', states: {a: {on: {X: {target: 'b', cond: 'ok'}}}, b: {}}})).toThrow(/`cond` in an XState v5 machine, which doesn't read it/)
  expect(build({initial: 'a', states: {a: {on: {X: {target: 'b', cond: 'ok', guard: 'ok'}}}, b: {}}})).toThrow(/both `guard` and v4's `cond`/)
  expect(build({initial: 'a', states: {a: {on: {X: {target: 'b', in: '#m.a'}}}, b: {}}})).toThrow(/v4's `in` guard/)
  expect(build({initial: 'a', strict: true, states: {a: {on: {X: 'b'}}, b: {}}})).toThrow(/v4's `strict`/)
  expect(build({initial: 'a', states: {a: {activities: ['beep'], on: {X: 'b'}}, b: {}}})).toThrow(/v4's `activities`/)
  expect(build({initial: 'a', states: {a: {onEntry: 'log', on: {X: 'b'}}, b: {}}})).toThrow(/v4's `onEntry`/)
  expect(build({initial: 'a', states: {a: {on: {'': 'b', X: 'b'}}, b: {}}})).toThrow(/eventless transition/)
  expect(build({initial: 'a', states: {a: {on: {'xstate.done.state.a': 'b', X: 'b'}}, b: {}}})).toThrow(/an event XState raises itself/)
  expect(build({initial: {target: 'a', actions: 'log'}, states: {a: {on: {X: 'a'}}}})).toThrow(/an initial transition given as an object/)
  expect(build({initial: 'a', states: {a: {on: {X: {target: 'a', delay: 5}}}}})).toThrow(/`delay`, a key fromXState doesn't read/)
  expect(build({initial: 'a', states: {a: {invoke: undefined, onEnter: 'x', on: {X: 'a'}}}})).toThrow(/`onEnter`, a key fromXState doesn't read/)
  expect(build({initial: 'a', states: {a: {context: {n: 0}, on: {X: 'a'}}}})).toThrow(/`context`, a key fromXState doesn't read/)
  // what changes nothing a run shows is taken: descriptions, metadata, tags, reenter and v4's internal (which change only
  // which entry and exit actions run), v4's action-order flags
  expect(build({initial: 'a', predictableActionArguments: true, description: 'd', states: {a: {tags: ['t'], meta: {}, on: {X: {target: 'a', reenter: true, description: 'x'}, Y: {target: 'a', internal: false}}}}})).not.toThrow()
})

test("v4's cond read as the guard v5 calls guard, its params the object's other keys: the same runs as XState's", () => {
  const cfg = (key: 'cond' | 'guard') => ({id: 'retry', initial: 'idle', context: {n: 0}, states: {
    idle: {on: {GO: 'busy'}},
    busy: {on: {FAIL: [{target: 'busy', [key]: key === 'cond' ? {type: 'under', max: 2} : {type: 'under', params: {max: 2}}, actions: 'count'}, {target: 'failed'}], OK: {target: 'done', [key]: 'never'}}},
    failed: {type: 'final'}, done: {type: 'final'}}})
  const bridge = {guards: {under: (({n}, p) => (n as Term).lt((p as {max: number}).max)) as Guard, never: () => no}, actions: {count: ({n}: Record<string, Term>) => ({n: n!.plus(1)})}}
  // the v4 config's chart against v5's actor of the same machine with `guard`
  const real = setup({guards: {under: ({context}, p: {max: number}) => context.n < p.max, never: () => false}, actions: {count: assign({n: ({context}) => context.n + 1})}}).createMachine(cfg('guard') as never)
  const c = fromXState(cfg('cond'), bridge)
  expect(conforms(c, real, createActor, {runs: 200, depth: 10})).toEqual({checked: 2000})
  expect(c.prove([c.law('a guard that never holds is never passed', env => env.in('done').not()), c.law('at most two retries counted', ({n}) => n.atMost(2))])).toMatchObject({proven: true, checked: true})
})

// Actors, timers and eventless transitions (the real-world corpus's machines use all three): an invoked actor's done and
// error and a timer are events from outside, taken only where they can come; eventless transitions and entry and exit
// actions that write the context are read into each transition as XState's macrostep. The actors are inert here (their
// answers are the events the run sends), as an extracted machine's are in its check.
const inert = fromPromise(() => new Promise<never>(() => {}))
const upload = setup({
  actors: {work: inert},
  guards: {full: ({context}) => context.n >= 3, under: ({context}) => context.tries < 2},
  actions: {inc: assign({n: ({context}) => context.n + 1}), reset: assign({n: 0}), tried: assign({tries: ({context}) => context.tries + 1}), clear: assign({tries: 0}), seen: assign({visits: ({context}) => context.visits + 1}), out: assign({outs: ({context}) => context.outs + 1})},
}).createMachine({
  id: 'm', initial: 'idle', context: {n: 0, tries: 0, visits: 0, outs: 0},
  on: {RESET: {target: '.idle', actions: 'reset'}},
  states: {
    idle: {on: {GO: 'busy', INC: {actions: 'inc'}}, always: {guard: 'full', target: 'full'}},
    busy: {entry: 'seen', exit: 'out', invoke: {src: 'work', onDone: {target: 'idle', actions: 'clear'}, onError: [{guard: 'under', target: 'retry', actions: 'tried'}, {target: 'failed'}]}, on: {INC: {actions: 'inc'}}},
    retry: {after: {500: {target: 'busy'}}, on: {AGAIN: {target: 'retry', reenter: true}}},
    full: {on: {DRAIN: {target: 'idle', actions: 'reset'}}},
    failed: {type: 'final'},
  },
})
const uploadBridge = {
  guards: {full: (({n}) => (n as Term).atLeast(3)) as Guard, under: (({tries}) => (tries as Term).lt(2)) as Guard},
  actions: {inc: ({n}: Record<string, Term>) => ({n: n!.plus(1)}), reset: () => ({n: 0}), tried: ({tries}: Record<string, Term>) => ({tries: tries!.plus(1)}), clear: () => ({tries: 0}), seen: ({visits}: Record<string, Term>) => ({visits: visits!.plus(1)}), out: ({outs}: Record<string, Term>) => ({outs: outs!.plus(1)})},
}

test('an invoked actor, a timer, an eventless transition and entry and exit writes: the same runs as XState, its laws proven', () => {
  const c = fromXState(upload, uploadBridge)
  expect(conforms(c, upload, createActor, {runs: 300, depth: 20})).toEqual({checked: 6000})
  expect(c.prove([c.law('at most two retries', ({tries}) => tries.atMost(2))])).toMatchObject({proven: true, checked: true})
  // the entry action given wrongly: the run where they part
  const wrong = fromXState(upload, {...uploadBridge, actions: {...uploadBridge.actions, seen: ({visits}: Record<string, Term>) => ({visits: visits!.plus(2)})}})
  expect(conforms(wrong, upload, createActor, {runs: 300, depth: 20}).failure).toMatch(/XState's visits is 1, the chart's 2/)
})

test('entry and exit of compounds, a transition to its own state and into it again, eventless transitions in a parent and in a row', () => {
  const m = setup({
    guards: {two: ({context}) => context.n === 2, big: ({context}) => context.n >= 4},
    actions: {inc: assign({n: ({context}) => context.n + 1}), ea: assign({ea: ({context}) => context.ea + 1}), xa: assign({xa: ({context}) => context.xa + 1}), ec: assign({ec: ({context}) => context.ec + 1}), xc: assign({xc: ({context}) => context.xc + 1}), back: assign({n: ({context}) => context.n - 1})},
  }).createMachine({
    id: 'm', initial: 'a', context: {n: 0, ea: 0, xa: 0, ec: 0, xc: 0},
    states: {
      a: {
        initial: 'p', entry: 'ea', exit: 'xa', always: {guard: 'big', target: 'b'},
        on: {SELF: 'a', RE: {target: 'a', reenter: true}, KID: '.q', KIDRE: {target: '.q', reenter: true}},
        states: {
          p: {entry: 'ec', exit: 'xc', on: {INC: {actions: 'inc'}, Q: 'q'}, always: {guard: 'two', target: 'q', actions: 'inc'}},
          q: {on: {INC: {actions: 'inc'}, P: 'p'}},
        },
      },
      b: {on: {BACK: {target: 'a', actions: 'back'}, INC: {actions: 'inc'}}},
    },
  })
  const n = (f: (x: Term) => unknown, k: string) => (env: Record<string, Term>) => ({[k]: f(env[k]!)})
  const c = fromXState(m, {
    guards: {two: ({n: x}) => (x as Term).eq(2), big: ({n: x}) => (x as Term).atLeast(4)},
    actions: {inc: n(x => x.plus(1), 'n'), ea: n(x => x.plus(1), 'ea'), xa: n(x => x.plus(1), 'xa'), ec: n(x => x.plus(1), 'ec'), xc: n(x => x.plus(1), 'xc'), back: n(x => x.minus(1), 'n')},
  })
  // the initial states' entry actions are the context's start
  expect(c.rule.decode(c.rule.interpreter().init({}))).toMatchObject({ea: 1, ec: 1})
  expect(conforms(c, m, createActor, {runs: 400, depth: 20})).toEqual({checked: 8000})
})

test('what an actor, a timer or an eventless transition could not run the same way is refused, with the reason', () => {
  const build = (config: Record<string, unknown>, opts = {}) => () => fromXState(setup({actors: {w: inert}}).createMachine(config as never), opts)
  // two timers fire in the order of their delays (a chart taking each as an event would take them in any order)
  expect(build({initial: 'a', states: {a: {after: {100: 'b', 200: 'c'}}, b: {}, c: {}}})).toThrow(/two timers in one state/)
  expect(build({initial: 'a', states: {a: {after: {100: 'c'}, initial: 'p', states: {p: {after: {50: 'q'}}, q: {}}}, c: {}}})).toThrow(/a timer in a.p and another in a, running at once|a timer in a and another in a.p/)
  // an answer comes once a visit: one taken without leaving, or refused by every guard, would be taken again
  expect(build({initial: 'a', context: {n: 0}, states: {a: {invoke: {src: 'w', onDone: {}}, on: {X: 'b'}}, b: {}}})).toThrow(/an actor's onDone that doesn't leave the state/)
  expect(build({initial: 'a', states: {a: {invoke: {src: 'w', onDone: {target: 'b', guard: 'ok'}}}, b: {}}}, {guards: {ok: () => no}})).toThrow(/whose last transition is guarded/)
  expect(build({initial: 'a', states: {a: {after: {100: {target: 'a'}}}}})).toThrow(/a timer that doesn't leave the state/)
  expect(build({initial: 'a', states: {a: {invoke: {src: 'w', onSnapshot: 'b'}}, b: {}}})).toThrow(/`onSnapshot`/)
  // eventless transitions that may run without end, and one the machine takes at once
  expect(build({initial: 'a', states: {a: {on: {X: 'b'}}, b: {always: 'c'}, c: {always: 'b'}}})).toThrow(/eventless transitions that may run more than 6 times in a row/)
  expect(build({initial: 'a', context: {n: 0}, states: {a: {always: {guard: 'ok', target: 'b'}}, b: {}}}, {guards: {ok: ({n}: any) => n.atMost(0)}})).toThrow(/takes at once from its initial state/)
  // an invoke in a plain config: its answers are named by the machine's XState
  expect(() => fromXState({initial: 'a', states: {a: {invoke: {src: 'w', onDone: 'b'}}, b: {}}})).toThrow(/an invoke in a plain config/)
})
