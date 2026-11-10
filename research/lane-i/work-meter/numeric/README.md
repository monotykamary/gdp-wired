# Finite work-budget boundaries

## Reproduced on the frozen request source

Batch `20261110-215401-xhkj8q`, `runs/lane-i/resume-numeric-budget-probe`,
restored exact source `94b65671` / patch `2c98e5dc8d92` and verified all 110
source blobs unchanged after the probe. All eight fixture weights were finite
and strictly positive, and both requested allowances were finite.

- An already infinite score admitted the callback and returned successfully
  under a one-unit allowance.
- A finite score plus a finite allowance overflowed the absolute cap to
  `Infinity`; the callback returned successfully after its score also became
  infinite.
- The ordinary finite zero-allowance control correctly threw
  `BudgetExpired` at completion.

`Infinity > Infinity` is false. A nonfinite score also needs an explicit
rejection rather than relying solely on an ordered comparison.

## Isolated candidate, not production

`apply.ts` requires the exact `94b65671` work-clock and shard-list blobs before
editing. The `numeric` composition retains the verified request source and:

1. Refuses a nonfinite current score or final computed cap before invoking the
   callback.
2. Refuses nonfinite completion scores.
3. Preserves an inherited finite cap even when the unbounded requested sum
   would overflow.
4. Adds five regression tests, including state restoration and normal finite
   cutoff behavior. The two original failure cases remain as negative controls.

The selected check and all three existing mutation acceptance runs are in
progress. Tooling and commitlint passed `20261110-215908-bw8843` (1,695 files,
zero warnings/errors); this is not the candidate's runtime result.
No existing acceptance test is removed; the new
exact numeric fixture is in the ordinary selected suite and shard roster.
`probe.jobs.json` reproduces the old-source diagnosis. `validation.jobs.json`
checks the new candidate through the existing source/receipt pipeline.

This changes only untrusted budget admission/completion, not checker
acceptance, weights, W, or the integration production tree. Runtime regression
evidence is not an unbounded IEEE-754 proof or whole-path budget qualification.
