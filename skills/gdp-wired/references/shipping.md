# Prove in CI, ship plain code

Install the prover as a dev dependency. For supported decisions, annotate the plain source and run
`gdp-wired-cli check policy.ts --mode standalone`; no duplicate runtime model is needed. For unsupported source,
keep a model in tests, prove its laws, and compare the production code with it. Protocol models still describe flows,
not arbitrary application code. See `docs/ci-only.md` in the repository.

The proof is about the rule's machine. Shipping that machine is an explicit alternative, not the default deployment pattern.

## Optional runtime use

```ts
const shipped = budget.compiled()                 // generated JavaScript; maps and the log updated in place
const params = budget.encodeParams({b: 100, m: 30})
let st = shipped.init(params)
for (const c of [50, 40, 70, 20]) st = shipped.step(params, st, budget.encodeInput({c}))
budget.decode(st)                                 // {s: 110}
```

- `rule.interpreter()`: the persistent reference evaluator (states are copied; searches branch from it). Library-built
  arithmetic and source-free recurrence helpers need no opt-in. User JavaScript helper source, including callbacks
  and transitive dependencies, needs explicit `rule.interpreter({compileHelpers: true})` or `rule.compiled()`.
- `encodeParams` / `encodeInput` turn runtime values (strings, decimals, choices, sets) into the naturals the machine
  reads; `decode` reads a state back. Both runtimes refuse inputs that aren't naturals below 2^53.
- `fun(...).run(values, params)` interprets a pure function's terms without generating JavaScript.
- `fun(...).compiled()` explicitly creates a cached callable with the same arguments and result. Declared helper
  source (`.fns(...)`, including serialized callbacks) requires this opt-in; arithmetic term methods do not.
- Comparison/proof tooling and low-level machine helpers may still compile code; do not claim that every API is CSP-safe.

## Hold existing code to the rule

```ts
budget.compare({
  init: () => ({s: 0}),
  step: ({b, m}, st, {c}) => ({s: st.s < b ? st.s + Math.min(c, m) : st.s}),
}) // {checked, exhaustive: false}, or a failure with the first disagreeing input/trace
```

`compare` runs the rule and reference side by side. Finite input domains are enumerated (up to `maxCases`);
unbounded domains use drawn and edge inputs. `fun.compare` reports per-input coverage; `rule.compare` enumerates
finite parameter/request combinations in bounded sequences, not every history or reachable state. `checked` counts
input cases, not fields. Require no failure and `exhaustive: true` when you need full finite input coverage.
An exhaustive comparison remains a test, never a kernel proof.

## Test the builders against themselves

```ts
budget.crossCheck([bounded]) // {checked: 1700}
```

`crossCheck(laws, stepLaws?)` replays every law, flag and update on concrete
runs, comparing each callback's own arithmetic with what the interpreter makes
of the expression that was proven. Put it in the test suite next to the proof.
For decisions: `crossCheckDecision(decision)`.
