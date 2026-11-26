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

## Shipping without the runtime

When you want zero `gdp-wired` runtime dependency in production — strict CSP (no `new Function` / `eval`), edge
workers, tiny bundles, or plain checked-in TypeScript your team can read and review in PRs — emit standalone source
directly from the proven rule, function, rational rule, or statechart:

```ts
const {source, digest} = budget.emit({laws: [bounded]})
```

Or via the CLI, keeping `gdp-wired` as a dev dependency:

```bash
npx gdp-wired-cli emit src/rules/review-routing.ts#reviewRoutingBundle \
  --out src/rules/review-routing.generated.ts --verify
```

Check the generated `.ts` file into git and gate CI with:

```bash
npx gdp-wired-cli emit src/rules/review-routing.ts#reviewRoutingBundle \
  --out src/rules/review-routing.generated.ts --check --verify
```

- **Zero runtime dependencies**: generated files have zero imports, zero `new Function` / `eval`, and zero proof/kernel
  code. They export clean types (`Params`, `Input`, `State`, `Result`) and functions (`init`, `step`, or `<name>`), using
  the rule's own field names (never internal slots or raw choice indices). `RatRule` emits exact BigInt `[bigint, bigint]`
  rational arithmetic with zero float rounding.
- **Refuses unproven rules**: `emit` proves every law first and exits `2` (never writing) if any law fails, is not
  kernel-checked, or carries unproven assumptions under `--from any`.
- **Deterministic drift check (`--check`)**: regenerates in memory and exits `1` with a short diff if the file on disk
  differs by even one character.
- **Closed-loop verification (`--verify`)**: emitted files inside the TypeScript reader's subset carry `// gdp: law`
  comments over the emitted code; `--verify` runs the TypeScript reader directly against the generated file so an emitter
  bug or manual edit shows up as a refuted law (exit `1`), or exits `2` honestly if the rule uses constructs outside the
  reader's subset (such as exact BigInt `RatRule`, variants, or histories).
- **When to prefer `emit` over `compiled()`**: use `emit` when shipping to strict CSP / edge / browser environments,
  when you want zero production dependency on `gdp-wired`, or when reviewers want inspectable TypeScript in git. Use
  `compiled()` / `interpreter()` when rules are constructed dynamically at runtime or when keeping the single live rule
  object in-process is simpler.

## Law comments

`// gdp: law` comments checked with `npx gdp-wired-cli check` (gdp-wired then a dev dependency; the repository's
`docs/ci-only.md`) are for code in another language, or when the user asks for them. Exit 1 is a broken law, 2 one
not checked: neither is a pass.
