# Opt-in model-refinement policy

The default remains **4**. `profile-049.json` and its 24G work allowance are
unchanged. No unconfirmed model may authorize a candidate deletion.

```ts
proveRule(rule, laws, {search: {work: 24_000_000_000}, modelRounds: 12})
proveRule(rule, laws, {search: {work: 24_000_000_000}, modelRounds: 'progress'})
```

Direct prover callers may use `GDP_MODEL_ROUNDS=12` or
`GDP_MODEL_ROUNDS=progress`. An explicit public option takes precedence; nested
calls inherit and restore the effective policy, including on exceptions.
Non-integers, negative values, unsafe integers and malformed strings are refused.

The sealed BAPA worker deliberately still clears inherited experimental flags.
Use its explicit `--model-rounds 12` or `--model-rounds progress`, or supply
`modelRounds` to `runProofWorker`. The override is recorded in the result and
bound into the input hash; it does not change the work allowance or flag profile.

## Progress and trust

`decideLaw`, the fast set path and ordinary `withModels` read the same scoped
policy. Numeric policies retain the existing local work-share policy and the
fast path's deadline-bounded extension. `progress` removes the round-count
stop while eligible instances are added. In a bounded caller it can use the
remaining outer allowance instead of the first model's heuristic work share;
it does not create, extend or renew that allowance. Without an outer endpoint,
the ordinary loop retains its finite local work share.

No-progress, incomplete evaluation, exhausted work, and expired walls still
return UNKNOWN. SAT still requires confirmation. Positive and negative memos
are keyed by effective policy, preventing a longer/progress attempt from being
reused as a default-four attempt. The final family checker is unchanged.

## Evidence boundary

The deterministic control confirms a model after six refinements with 8 and
`progress`, while default 4 stops as UNKNOWN. The public retained-witness
regression checks the explicit option inside the real `proveRule` path.
Kernel and worker gates also cover policy restoration, memo isolation, invalid
settings, unchanged default flags/work and expired-wall behavior.

A separate one-law diagnostic uses the retained p4 25-law fixture under the
public search-policy scope and the same 24G allowance. Its recorded outcome,
not the controlled sequence, determines whether real retained:7 converges.
The budget-correct diagnostic returned `proven: true` after six model-refinement
rounds (unconfirmed rounds 0 through 5, then the successful query), beyond the
default four. The final gate asserts that outcome and trace. This is an
individual native law result, not a complete checked family or a new
all-size/source proof. Final pinned-Bun gate `20261116-003619-chqbhn` passed
scoped typecheck, 289 kernel tests, 43 policy/worker test executions, the two
public/retained-witness tests, the asserted real six-round regression, and
commitlint. Receipt: `MODEL-ROUNDS-RESULTS.json`.
