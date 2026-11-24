# With XState and `@xstate/graph`

Formal verification proves the logic matches its specification; model-based testing checks that the real application
actually follows it in the world. `gdp-wired/xstate` connects both sides without adding `xstate` or `@xstate/graph` to
`gdp-wired`'s runtime dependencies.

## 1. The default: write the rule or chart, prove it, and ship it

In TypeScript, write stateful logic directly with `rule()` or `chart()`, prove its laws (`proveRule`, `proveSteps`,
`chart.prove`, with `{from: 'any'}` wherever state is reloaded), keep each broken twin and assert it is refuted, and run
the proven rule itself (`rule.interpreter()` or `rule.compiled()`). That way the code making decisions cannot drift
from the model that was proven.

You do not need XState in your application to use `@xstate/graph` for model-based testing (section 3).

## 2. An existing XState machine: `fromXState`, `conforms`, and extraction

When you already ship an XState v5 (or v4) machine, `fromXState(machine, {guards, actions})` translates it into a
`chart()` whose laws the kernel proves; `conforms(chart, machine, createActor)` runs XState's own actor beside the
compiled rule on random events so any mismatch in a guard or action shows up as a concrete run (`examples/xstate.ts`):

```ts
import {createActor} from 'xstate'
import {conforms, fromXState} from 'gdp-wired/xstate'

const c = fromXState(orderMachine, {
  guards: {canRetry: ({retries}) => retries.lt(2), unshipped: env => env.in('active.paid')},
  actions: {count: ({retries}) => ({retries: retries.plus(1)}), notify: null},
})
c.check()
c.prove([c.law('the retries stay within 2', ({retries}) => retries.atMost(2))])
conforms(c, orderMachine, createActor, {runs: 300, depth: 16})
```

- **Read:** nested states, parallel roots, deep history, final states, targetless (internal) transitions, named guards
  and actions with params, `invoke` `onDone`/`onError` and single `after` timers (as external events, once per visit),
  and `always` / context-writing `entry`/`exit` folded into XState's macrostep. What a chart cannot run the same way,
  and any key `fromXState` does not read, is refused when built with the reason.
- **Extraction (only when asked):** `extractXState('./order.ts')` (`gdp-wired/extract`) reads guards and actions from
  the machine's source and runs `conforms` against the project's own `xstate`.
- **CLI law comments on XState files:** as of 0.57, `npx gdp-wired-cli check order.ts` checks `// gdp: law` comments on
  the extracted model only and reports them as `unknown` / `unchecked` (exit `2`), because XState extraction checks
  conformance via `conforms` rather than native parameter-capture source-law replay. Prefer `fromXState` + `prove` +
  `conforms`, or prove a native `chart()` / `rule()`.

## 3. Model-based testing with `@xstate/graph`

`toLogic(ruleOrChart, {params?, events?, maxValue?})` wraps any proven `rule()` or `chart()` as XState v5 `ActorLogic`
(`getInitialSnapshot`, `transition`, `getPersistedSnapshot`, `restoreSnapshot`). Each step runs the proven rule via
`rule.interpreter()` (copied states — never the in-place `rule.compiled()` state), refused requests leave the snapshot
unchanged, `serializeState` serializes scalars, maps (key-order independent, default entries normalized) and logs
canonically, and the default `events(snapshot)` enumerates each input kind (`oneOf` choices, booleans, and for naturals
`0`, `1`, values read from the state/params, and `maxValue`).

Pass the logic and `logic.options` to `@xstate/graph`'s `TestModel` (in `@xstate/graph` 3.0.4, `new TestModel(logic,
options)` accepts any `ActorLogic`, while `createTestModel(machine, options)` is for `StateMachine`s) to generate paths
from the proven rule and drive the real application (`examples/xstate-mbt.ts`):

```ts
import {TestModel} from '@xstate/graph'
import {proveRule} from 'gdp-wired'
import {runToEvents, toLogic} from 'gdp-wired/xstate'

proveRule(wallet, [walletCovered], {from: 'any'})          // proven, checked

const logic = toLogic(wallet, {maxValue: 2})
const model = new TestModel(logic, logic.options)
for (const path of model.getShortestPaths()) {
  await model.testPath(path, {
    states: {'*': snap => expectAppMatches(snap.context)}, // check UI / DB / service state
    events: {
      'xstate.init': () => resetApp(),
      topUp: ({event}) => app.topUp((event as {amount: number}).amount),
      reserve: ({event}) => app.reserve((event as {id: number, amount: number}).id, (event as {amount: number}).amount),
      release: ({event}) => app.release((event as {id: number}).id),
      spend: ({event}) => app.spend((event as {id: number}).id),
    },
  })
}
```

### Counterexamples as regression paths (`runToEvents`)

`getShortestPaths()` covers every state reachable with the enumerated events (naturals bounded by `maxValue`, or the
`events` you pass) — not every reachable state of the rule; the proof covers the rest. To also exercise
rejected/ignored self-loops within that graph (such as an over-budget `reserve` that the proven rule leaves unchanged),
extend each shortest path with its outgoing transitions from `model.getAdjacencyMap()`, or turn a broken twin's
counterexample directly into a regression path with `runToEvents`.

`runToEvents(ruleOrChart, run)` turns a refuting run from `proveRule`, `proveSteps`, `chart.prove`, `minimizeRun`, or
`search` into the XState event objects `{type, ...payload}` ready for `getPathsFromEvents`:

```ts
// From a broken rule twin -> regression path on the proven rule's model against the real app:
const broken = proveRule(uncheckedWallet, [uncheckedCovered])
const [regression] = model.getPathsFromEvents(runToEvents(uncheckedWallet, broken.run!))
await model.testPath(regression!, walletHarness)           // fails the buggy app, passes the fixed app

// From a broken XState variant -> replay directly on the real XState machine:
const v = brokenOrderChart.prove(laws, stepLaws)
const events = runToEvents(brokenOrderChart, v.run!)       // [{type: 'PAY'}, ..., {type: 'REFUND'}]
const [path] = createTestModel(buggyOrderMachine).getPathsFromEvents(events)
// path.state.value === 'refunded' after {active: 'shipped'}
```

## 4. The division of labour

- **The proof (`proveRule`, `proveSteps`, `chart.prove`) covers the logic:** every reachable (or arbitrary `{from: 'any'}`)
  state, every unbounded natural, every map key, every interleaving within the rule — with a kernel-checked certificate
  that Lean checks again.
- **Model-based testing (`toLogic`, `runToEvents`, `@xstate/graph`) covers the app around it:** the UI wiring, database
  transactions, serialization, HTTP handlers, and integration boundaries that sit outside the rule, checked along shortest
  paths and proven counterexample regressions.
