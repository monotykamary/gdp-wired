# Finite work-budget boundaries

## Reproduced on the frozen request source

Batch `20261110-215401-xhkj8q`, `runs/lane-i/resume-numeric-budget-probe`,
restored exact source `94b65671` / patch `2c98e5dc8d92` and verified all 110
source blobs unchanged. All eight fixture weights were finite and strictly
positive; both requested allowances were finite.

- An already infinite score admitted and completed the callback under a
  one-unit allowance.
- A finite score plus a finite allowance overflowed the absolute cap to
  `Infinity`; the callback completed after its score became infinite too.
- The ordinary zero-allowance control correctly threw at completion.

`Infinity > Infinity` is false. Nonfinite scores need an explicit rejection.

## Verified separately, not promoted

`apply.ts` requires the exact request-source work-clock and shard-list blobs.
Its isolated `numeric` composition:

1. Rejects a nonfinite score or final cap before invoking the callback.
2. Rejects a nonfinite completion score.
3. Preserves an inherited finite cap when an unbounded requested sum overflows.
4. Adds five regressions, including restoration and ordinary cutoff behavior.

Source `32a59b2a` is frozen on `claude/lane-i-finite-budgets`; see
`VERIFIED-SOURCE.md` for complete identities and evidence.

- **169 selected tests** and checker erasure, roster, decoder, type/lint pass.
- **267 tests per mutation mode** (zero/double/random) pass on exactly the
  same full 111-file source manifest as the selected run.
- The identical regression fixture on unchanged `94b65671` produces exactly
  **three expected failures and two passes**.
- Independent receipt/source audit and exact-parent three-file export pass.
- Audit-tool type/lint and commitlint pass: 1,698 files, no warnings/errors.

`probe.jobs.json` reproduces the original diagnosis; `validation.jobs.json`
checks the candidate. `negative.jobs.json` retains the broken-source control.
`audit.jobs.json` verifies hashes, complete source equality, fixture identity
and the exact three-file export before a source branch is frozen.

No existing acceptance test is removed. The numeric fixture belongs to the
ordinary selected suite and shard roster, not the counter-mutation acceptance
suite. No checker acceptance code, weights or integration production code is
changed. F3/F4, floating-point precision beyond these cases, calibrated weights,
W and GATE GREEN remain unqualified.
