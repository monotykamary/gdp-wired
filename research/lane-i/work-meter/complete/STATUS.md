# Complete-accounting continuation — DRAFT, UNVALIDATED

This is an isolated source-assembly and remote-constructor-preparation checkpoint,
not a production integration or a claim of complete coverage.

Frozen parent input: Lane A `30f9c3ba`, plus cumulative I2 `c9eb0f9c` and the
three-file I1 kernel-meter patch. Original protocol models are unchanged.
The I2/A2 import conflict preserves both traceNow and coreMeter.

Additional draft observations:
- One raw object shared by trusted checkers and core; no weights or budget policy.
- Direct recurrence evaluator visits and manual instance binding visits.
- Every finite-prefix tick call, including a refused one.
- Actual infer candidate/row calls (holdsRow, at, dirValue, residual) and
  attempted sampling/EPR transitions. Precredited watch estimates are NOT
  copied: the evaluator/watch paths already observe the actual calls.
- Worker-generated identity wrappers around newly allocated expression,
  condition and goal objects. Child evaluation precedes charging; reused
  nodes are not traversed or charged again. Per-file AST erasure is required.

Pending batch: 20261110-121916-gkoq76, complete-ast-preparation.
No new tests have passed yet. Constructor generic typing, complete coverage,
noninterference, phase ledger and census remain pending. The original Lane A
full-suite failure is NOT erased by using its source snapshot here.

Production, legacy fullWork, all existing budgets and W remain unchanged.
No provisional coefficients are calibrated or used for promotion.
