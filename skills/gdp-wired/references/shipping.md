# Ship the rule you proved

In TypeScript the proven rule is what runs: `npm install gdp-wired`, prove its laws in tests, and run the same rule at
runtime, so there is no hand-written copy of its decisions to drift from what was proven.

```ts
const shipped = budget.compiled()                 // generated JavaScript; maps and the log updated in place
const params = budget.encodeParams({b: 100, m: 30})
let st = shipped.init(params)
for (const c of [50, 40, 70, 20]) st = shipped.step(params, st, budget.encodeInput({c}))
budget.decode(st)                                 // {s: 110}
```

- `rule.interpreter()`: the reference evaluator (states are copied; searches branch from it). `rule.compiled()`: the
  same machine as generated JavaScript, for the hot path.
- State the app reloads (from a database, a host, a cache) didn't come from the start: prove the step laws with
  `{from: 'any'}` and require `proven && checked && !assumes`.
- `encodeParams` / `encodeInput` turn runtime values (strings, decimals, choices, sets) into the naturals the machine
  reads; `decode` reads a state back. Both runtimes refuse inputs that aren't naturals below 2^53.
- A decision: `fun(...).run(values, params)` interprets its terms; `fun(...).compiled()` is a cached callable with the
  same arguments and result.
- User JavaScript in `.fns(...)` (strings or callbacks, and what they call) runs only through `compiled()` or
  `rule.interpreter({compileHelpers: true})`; library `divBy`/`modBy`, `recur` equations and arithmetic terms need no
  opt-in. Don't claim the prover or the machine helpers are CSP-safe.

## Test the builders against themselves

```ts
budget.crossCheck([bounded]) // {checked: 1700}
```

`crossCheck(laws, stepLaws?)` replays every law, flag and update on concrete runs, comparing each callback's own
arithmetic with what the interpreter makes of the expression that was proven. Put it in the test suite next to the
proof. For decisions: `crossCheckDecision(decision)`.

## Shipping without the runtime

When gdp-wired can't be a runtime dependency, emit the proven rule as a TypeScript file, check it in, and ship that:
no import, no `new Function`, the same bytes on every run. gdp-wired stays a dev dependency.

```ts
// policy.model.ts (tests or proofs/, never imported by the app)
export const routingBundle = {fun: routing, laws: routingLaws}   // or {rule, laws, stepLaws}, {ratRule, laws}, {chart, laws}
```

```sh
npx gdp-wired-cli emit policy.model.ts#routingBundle --out src/routing.generated.ts            # write it
npx gdp-wired-cli emit policy.model.ts#routingBundle --out src/routing.generated.ts --check --verify   # in CI
```

- The file holds the decision or the step and nothing else: typed `Params`, `Input` and `State` (or `Result`), the
  rule's own names, `init(params)` and `step(params, state, input)` for a rule, one function for a `fun`. Its header
  names the model it came from, the command that regenerates it (run from the repository root), every law with its
  proof status, the gdp-wired version and the machine's digest.
- `emit` refuses (exit 2) while any law isn't proven. `--check` exits 1 with a short diff when the file differs from
  what the model emits now: a hand edit, a changed model, or a gdp-wired upgrade that changes the output.
- `--verify` runs the emitted module beside the rule's interpreter, exhaustively on small domains and on random draws
  beyond them, and exits 1 on the first input where they differ. It is the same check `compiled()` relies on; the
  emitter itself isn't trusted.
- Decimals are exact fixed-point integers. A value with more places than its `decimal(places)` throws, as
  `encodeInput` does; `decimal(places, {round: 'half-even'})` rounds it to the grid instead, the same way in
  `encodeInput` and in the emitted file, and the laws hold for the rounded values.
- To change behavior, edit the model and its laws, prove, and emit again. Don't edit the generated file.

Prefer it over `compiled()` when the code ships somewhere gdp-wired can't go (a reviewer's rule, a CSP that forbids
`new Function`, a bundle budget), or when reviewers should read the exact code that runs.

## Code that already exists

Until it is replaced by the rule, hold hand-written code to it:

```ts
budget.compare({
  init: () => ({s: 0}),
  step: ({b, m}, st, {c}) => ({s: st.s < b ? st.s + Math.min(c, m) : st.s}),
}) // {checked, exhaustive: false}, or a failure with the first disagreeing input/trace
```

`compare` runs the rule and the reference side by side: finite input domains enumerated (up to `maxCases`), unbounded
ones drawn with their edges, in bounded sequences. It is a test, never a proof; require no failure and
`exhaustive: true` when you need full finite input coverage.

## Law comments

`// gdp: law` comments checked with `npx gdp-wired-cli check` (gdp-wired then a dev dependency; the repository's
`docs/ci-only.md`) are for code in another language, or when the user asks for them. Exit 1 is a broken law, 2 one
not checked: neither is a pass.
