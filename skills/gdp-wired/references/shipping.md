# Shipping the proven rule

The proof is about the rule's machine. Ship that machine, or check the code you ship against it.

## Run it

```ts
const shipped = budget.compiled()                 // generated JavaScript; maps and the log updated in place
const params = budget.encodeParams({b: 100, m: 30})
let st = shipped.init(params)
for (const c of [50, 40, 70, 20]) st = shipped.step(params, st, budget.encodeInput({c}))
budget.decode(st)                                 // {s: 110}
```

- `rule.interpreter()`: the persistent reference evaluator (states are copied; searches branch from it).
- `encodeParams` / `encodeInput` turn runtime values (strings, decimals, choices, sets) into the naturals the machine
  reads; `decode` reads a state back. Both runtimes refuse inputs that aren't naturals below 2^53.
- `fun(...).run(values, params)` runs a pure function's compiled terms.

## Hold existing code to the rule

```ts
budget.compare({
  init: () => ({s: 0}),
  step: ({b, m}, st, {c}) => ({s: st.s < b ? st.s + Math.min(c, m) : st.s}),
}) // {checked: 2000}, or {checked, failure: '...'} with the first disagreement
```

`compare` runs the rule and your reference side by side on drawn and edge
inputs, field by field. Use it when the production code is hand-written.

## Test the builders against themselves

```ts
budget.crossCheck([bounded]) // {checked: 1700}
```

`crossCheck(laws, stepLaws?)` replays every law, flag and update on concrete
runs, comparing each callback's own arithmetic with what the interpreter makes
of the expression that was proven. Put it in the test suite next to the proof.
For decisions: `crossCheckDecision(decision)`.
