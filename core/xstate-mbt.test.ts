// Model-based testing with @xstate/graph (core/xstate.ts):
//   - Any proven rule or chart presented as XState v5 ActorLogic (toLogic) drives @xstate/graph's TestModel and
//     graph algorithms (getShortestPaths, getSimplePaths, getPathsFromEvents, getAdjacencyMap) without mutating
//     snapshots in place.
//   - Counterexample runs from proveRule() or search() turn into XState event sequences (runToEvents) for
//     getPathsFromEvents(), both against toLogic(provenRule) and against a real XState machine.
//   - Canonical serialization keeps map entries and logs distinct, is key-order independent, and refused events leave
//     the snapshot unchanged.
import {expect, test} from 'bun:test'
import {TestModel, createTestModel, getShortestPaths} from '@xstate/graph'
import {assign, createActor, setup, stateIn} from 'xstate'
import {bool, count, minimizeRun, nat, oneOf, proveRule, rule, when} from './dsl.ts'
import {search} from './machine.ts'
import {type RuleEvent, fromXState, runToEvents, serializeState, toLogic} from './xstate.ts'
import {orderConfig, xorder, xorderLaws} from '../examples/xstate.ts'
import {uncheckedWallet, wallet, walletCovered, walletHarness} from '../examples/xstate-mbt.ts'

test('wallet rule: proved from any state, TestModel shortest paths pass correct app and catch buggy app', async () => {
  const proved = proveRule(wallet, [walletCovered], {from: 'any'})
  expect(proved).toMatchObject({proven: true, checked: true})
  expect(proved.assumes).toBeUndefined()

  const logic = toLogic(wallet, {maxValue: 2})
  const model = new TestModel(logic, logic.options)
  const paths = model.getShortestPaths()
  expect(paths.length).toBeGreaterThan(10)
  // Covers multi-key reservations (two distinct keys held at once) and topUp/reserve/release/spend states.
  expect(paths.some(p => Object.keys(p.state.context.Held as Record<string, number>).length >= 2)).toBe(true)

  // Every generated shortest path passes on the correct hand-written wallet.
  for (const path of paths) {
    await model.testPath(path, walletHarness(false))
  }

  // A state-update bug on a forward transition fails directly on getShortestPaths().
  let forwardBugFailures = 0
  for (const path of paths) {
    try { await model.testPath(path, walletHarness('reserve-skips-reserved')) }
    catch { forwardBugFailures++ }
  }
  expect(forwardBugFailures).toBeGreaterThan(0)

  // Transition coverage (shortest paths extended by every outgoing transition in getAdjacencyMap, including self-loops
  // where the proven rule ignores an over-budget reserve and backwards release/spend transitions) passes on the correct
  // wallet and catches both the missing credits check on reserve and a buggy spend.
  const adj = model.getAdjacencyMap()
  const allShortest = model.getShortestPaths({allowDuplicatePaths: true})
  const transitionPaths = allShortest.flatMap(p =>
    Object.values(adj[logic.serializeState(p.state) as keyof typeof adj]?.transitions ?? {}).map(t => ({
      ...p,
      state: t.state,
      steps: [...p.steps, {event: t.event, state: t.state}],
      weight: p.weight + 1,
    })),
  )
  expect(transitionPaths.length).toBeGreaterThan(paths.length)
  for (const path of transitionPaths) {
    await model.testPath(path, walletHarness(false))
  }
  for (const bug of ['no-credits-check', 'spend-keeps-reserved'] as const) {
    let failures = 0
    for (const path of transitionPaths) {
      try { await model.testPath(path, walletHarness(bug)) }
      catch { failures++ }
    }
    expect(failures).toBeGreaterThan(0)
  }

  // Also check standalone getShortestPaths and XState's own createActor(logic).
  expect(getShortestPaths(logic, logic.options).length).toBeGreaterThan(10)
  const actor = createActor(logic).start()
  actor.send({type: 'topUp', id: 0, amount: 10})
  actor.send({type: 'reserve', id: 7, amount: 4})
  expect(actor.getSnapshot().context).toEqual({credits: 10, reserved: 4, Held: {'7': 4}})
  actor.stop()
}, 30_000)

test('wallet broken twin: proveRule & search runs -> runToEvents -> getPathsFromEvents -> testPath', async () => {
  const brokenLaw = uncheckedWallet.law('reservations never exceed the credits', ({credits, reserved}) => reserved.atMost(credits))
  const broken = proveRule(uncheckedWallet, [brokenLaw])
  expect(broken.proven).toBe(false)
  expect(broken.run).toBeDefined()

  const logic = toLogic(wallet, {maxValue: 2})
  const model = new TestModel(logic, logic.options)

  // Counterexample from proveRule (also works minimized and from search()).
  const ceEvents = runToEvents(uncheckedWallet, broken.run!)
  expect(ceEvents.length).toBeGreaterThan(0)
  expect(ceEvents.some(e => e.type === 'reserve')).toBe(true)

  const expectRejects = async (fn: () => Promise<unknown>, pattern: RegExp) => {
    let err: unknown
    try { await fn() }
    catch (e) { err = e }
    expect(err).toBeInstanceOf(Error)
    expect((err as Error).message).toMatch(pattern)
  }

  const cePaths = model.getPathsFromEvents(ceEvents)
  expect(cePaths.length).toBe(1)
  await model.testPath(cePaths[0]!, walletHarness(false))
  await expectRejects(() => model.testPath(cePaths[0]!, walletHarness(true)), /app wallet .* !== proven rule/)

  // Counterexample from search() and minimizeRun() gives a 1-step reserve on an empty wallet.
  const searchRun = search(uncheckedWallet.machine, brokenLaw)
  expect(searchRun).toBeDefined()
  const searchEvents = runToEvents(uncheckedWallet, searchRun!)
  expect(searchEvents).toEqual([{type: 'reserve', id: 0, amount: 1}])
  const minRun = minimizeRun(uncheckedWallet, brokenLaw, broken.run!)
  const minEvents = runToEvents(uncheckedWallet, minRun)
  expect(minEvents.length).toBe(1)
  expect(minEvents[0]!.type).toBe('reserve')

  const [searchPath] = model.getPathsFromEvents(searchEvents)
  await model.testPath(searchPath!, walletHarness(false))
  await expectRejects(() => model.testPath(searchPath!, walletHarness(true)), /app wallet .* !== proven rule/)
}, 30_000)

test('XState machine: fromXState -> broken variant run -> runToEvents -> getPathsFromEvents replays violation on real machine', async () => {
  const orderBody = {
    id: orderConfig.id,
    initial: orderConfig.initial,
    context: {retries: 0},
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
  const fixedMachine = setup({
    types: {context: {} as {retries: number}},
    guards: {canRetry: ({context}) => context.retries < 2, unshipped: stateIn({active: 'paid'})},
    actions: {count: assign({retries: ({context}) => context.retries + 1}), notify: () => {}},
  }).createMachine(orderBody)

  const buggyMachine = setup({
    types: {context: {} as {retries: number}},
    guards: {canRetry: ({context}) => context.retries < 2, unshipped: stateIn('active')},
    actions: {count: assign({retries: ({context}) => context.retries + 1}), notify: () => {}},
  }).createMachine(orderBody)

  // Proven on the fixed chart; refuted on the broken variant with a concrete run.
  const fixedChart = xorder()
  expect(fixedChart.prove(xorderLaws(fixedChart).laws, xorderLaws(fixedChart).stepLaws)).toMatchObject({proven: true, checked: true})

  const brokenChart = xorder('refunds a shipped order')
  const {laws, stepLaws} = xorderLaws(brokenChart)
  const verdict = brokenChart.prove(laws, stepLaws)
  expect(verdict.proven).toBe(false)
  expect(verdict.run).toBeDefined()

  const events = runToEvents(brokenChart, verdict.run!)
  expect(events.length).toBeGreaterThanOrEqual(3)
  expect(events.at(-1)).toEqual({type: 'REFUND'})

  // Feed the counterexample events directly into @xstate/graph on the real XState machines.
  const buggyModel = createTestModel(buggyMachine)
  const [buggyPath] = buggyModel.getPathsFromEvents(events as never)
  expect(buggyPath).toBeDefined()
  expect(buggyPath!.state.value).toBe('refunded')
  // The step right before REFUND was in {active: 'shipped'}, confirming the violation on XState's own machine.
  expect(buggyPath!.steps.at(-2)?.state.value).toEqual({active: 'shipped'})

  // Replay the same path on a live XState actor of the buggy machine vs fixed machine.
  const buggyActor = createActor(buggyMachine).start()
  const fixedActor = createActor(fixedMachine).start()
  for (const ev of events) {
    buggyActor.send(ev as never)
    fixedActor.send(ev as never)
  }
  expect(buggyActor.getSnapshot().value).toBe('refunded')
  expect(fixedActor.getSnapshot().value).toEqual({active: 'shipped'})
  buggyActor.stop()
  fixedActor.stop()

  // Also test an XState machine with event payloads: runToEvents preserves the machine's payload fields.
  const tallyMachine = setup({
    types: {
      context: {} as {total: number},
      events: {} as {type: 'ADD', amount: number} | {type: 'CLOSE'},
    },
    guards: {small: ({event}) => event.type === 'ADD' && event.amount <= 3},
    actions: {add: assign({total: ({context, event}) => context.total + (event.type === 'ADD' ? event.amount : 0)})},
  }).createMachine({
    id: 'tally', initial: 'open', context: {total: 0},
    states: {open: {on: {ADD: {target: 'open', guard: 'small', actions: 'add'}, CLOSE: 'closed'}}, closed: {type: 'final'}},
  })
  const tallyChart = fromXState(tallyMachine, {
    inputs: {amount: nat},
    guards: {small: ({amount}) => amount.atMost(3)},
    actions: {add: ({total, amount}) => ({total: total.plus(amount)})},
  })
  const tallyBroken = tallyChart.prove([tallyChart.law('total stays at most 2', ({total}) => total.atMost(2))])
  expect(tallyBroken.proven).toBe(false)
  expect(tallyBroken.run).toBeDefined()
  const tallyEvents = runToEvents(tallyChart, tallyBroken.run!)
  expect(tallyEvents.every(e => typeof e.type === 'string' && typeof e.amount === 'number')).toBe(true)
  const tallyActor = createActor(tallyMachine).start()
  for (const ev of tallyEvents) tallyActor.send(ev as never)
  expect((tallyActor.getSnapshot().context as {total: number}).total).toBeGreaterThan(2)
  tallyActor.stop()

  // toLogic also works directly on a Chart, exposing snapshot.value and chart stateMatcher.
  const chartLogic = toLogic(fixedChart)
  const chartModel = new TestModel(chartLogic, chartLogic.options)
  const chartPaths = chartModel.getShortestPaths({allowDuplicatePaths: true})
  expect(chartPaths.some(p => p.state.value === 'refunded')).toBe(true)
  const reachedShipped = chartPaths.find(p => JSON.stringify(p.state.value) === JSON.stringify({active: 'shipped'}))
  expect(reachedShipped).toBeDefined()
  let sawActive = false
  await chartModel.testPath(reachedShipped!, {states: {active: () => { sawActive = true }}})
  expect(sawActive).toBe(true)
}, 30_000)

test('serialization, map distinction, log distinction, refused events, and copied states (no in-place mutation)', () => {
  const logic = toLogic(wallet, {maxValue: 2})
  const s0 = logic.getInitialSnapshot()

  // Branching from one snapshot leaves earlier snapshots untouched (copied states, never in-place compiled mutation).
  const sTop = logic.transition(s0, {type: 'topUp', id: 0, amount: 3})
  const branchA = logic.transition(logic.transition(sTop, {type: 'reserve', id: 0, amount: 1}), {type: 'reserve', id: 1, amount: 2})
  const branchB = logic.transition(logic.transition(sTop, {type: 'reserve', id: 1, amount: 2}), {type: 'reserve', id: 0, amount: 1})
  const branchC = logic.transition(logic.transition(sTop, {type: 'reserve', id: 0, amount: 2}), {type: 'reserve', id: 1, amount: 1})

  // Original sTop is unmutated after branching.
  expect(sTop.context).toEqual({credits: 3, reserved: 0, Held: {}})
  expect(s0.context).toEqual({credits: 0, reserved: 0, Held: {}})

  // Key-order independent: reserving id 0 then 1 vs id 1 then 0 yields the exact same serialized state.
  expect(serializeState(branchA)).toBe(serializeState(branchB))
  expect(branchA.context).toEqual({credits: 3, reserved: 3, Held: {'0': 1, '1': 2}})

  // States differing ONLY in a map entry (identical credits=3, reserved=3) stay distinct!
  expect(branchA.context.credits).toBe(branchC.context.credits)
  expect(branchA.context.reserved).toBe(branchC.context.reserved)
  expect(serializeState(branchA)).not.toBe(serializeState(branchC))

  // Releasing back to default 0 canonicalizes back to the empty-map state.
  const r1 = logic.transition(sTop, {type: 'reserve', id: 0, amount: 1})
  const back = logic.transition(r1, {type: 'release', id: 0, amount: 0})
  expect(serializeState(back)).toBe(serializeState(sTop))

  // Persisted snapshot round-trips losslessly through JSON.stringify/JSON.parse.
  const persisted = JSON.parse(JSON.stringify(logic.getPersistedSnapshot(branchA))) as Record<string, unknown>
  const restored = logic.restoreSnapshot(persisted as {status: string})
  expect(serializeState(restored)).toBe(serializeState(branchA))
  const afterSpend = logic.transition(restored, {type: 'spend', id: 0})
  expect(afterSpend.context).toEqual({credits: 2, reserved: 2, Held: {'1': 2}})

  // Unknown event type and invalid payload leave the snapshot unchanged.
  expect(logic.transition(sTop, {type: 'UNKNOWN_EVENT'})).toBe(sTop)
  expect(logic.transition(sTop, {type: 'xstate.init'})).toBe(sTop)
  expect(logic.transition(sTop, {type: 'topUp', id: 0, amount: -5})).toBe(sTop)

  // Refused request (failing the rule's .assume()) leaves the snapshot unchanged.
  const guarded = rule('guarded')
    .params({cap: nat})
    .inputs({op: oneOf('add', 'reset'), n: nat})
    .state({total: 0})
    .assume(({op, n}) => op.is('reset').or(n.gt(0)))
    .step(({op, n, total, cap}) => ({total: when(op.is('reset'), 0, when(total.plus(n).atMost(cap), total.plus(n), total))}))
  const gLogic = toLogic(guarded, {params: {cap: 5}, maxValue: 2})
  const g0 = gLogic.getInitialSnapshot()
  const gRefused = gLogic.transition(g0, {type: 'add', n: 0})
  expect(gRefused).toBe(g0)
  expect(serializeState(gRefused)).toBe(serializeState(g0))
  const gOk = gLogic.transition(g0, {type: 'add', n: 2})
  expect(gOk.context).toEqual({total: 2})

  // Rule with a history log: states differing only in the log serialize distinctly, and traversal terminates.
  const logged = rule('logged')
    .params({w: nat, c: nat, now: nat})
    .inputs({forced: bool, t: nat})
    .log('forced', 't')
    .sums({ours: (rec, {now, w}) => count(rec.forced.not().and(rec.t.atMost(now), now.lt(rec.t.plus(w))))})
    .queries({seen: (rec, {t, w}) => count(t.lt(rec.t.plus(w)))})
    .flags(({forced, seen, c}) => ({admitted: forced.not().and(seen.plus(1).atMost(c))}))
    .keep(({forced, admitted}) => forced.or(admitted))
  const lLogic = toLogic(logged, {params: {w: 5, c: 2, now: 10}, maxValue: 1})
  const l0 = lLogic.getInitialSnapshot()
  const lA = lLogic.transition(l0, {type: 'step', forced: true, t: 0})
  const lB = lLogic.transition(l0, {type: 'step', forced: true, t: 1})
  expect(lA.context).toEqual(lB.context)
  expect(serializeState(lA)).not.toBe(serializeState(lB))
  expect(new TestModel(lLogic, lLogic.options).getShortestPaths().length).toBeGreaterThan(2)

  // Standalone serializeState handles arbitrary plain objects and Maps key-order independently.
  const m1 = new Map<string, number>([['b', 2], ['a', 1]])
  const m2 = new Map<string, number>([['a', 1], ['b', 2]])
  expect(serializeState({y: m1, x: {k2: 2, k1: 1}})).toBe(serializeState({x: {k1: 1, k2: 2}, y: m2}))
  expect(serializeState({y: m1})).not.toBe(serializeState({y: new Map([['a', 1], ['b', 3]])}))

  // Custom events override works in toLogic.
  const custom: RuleEvent[] = [{type: 'topUp', id: 0, amount: 5}]
  const cLogic = toLogic(wallet, {events: s => ((s.context.credits as number) < 5 ? custom : [])})
  expect(new TestModel(cLogic, cLogic.options).getShortestPaths({allowDuplicatePaths: true}).map(p => p.state.context.credits)).toEqual([0, 5])
})
