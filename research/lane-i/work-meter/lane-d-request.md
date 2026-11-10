# Lane D — I1 raw-meter review request

**Review candidate:** `9f89363c669127568bef7f131050c522cf233be0`
(`claude/lane-i-kernel-meter-v2`). Tree:
`4e27c04f1e720ca763105e0a6ae64c1ddcdaa297`.

**Not merge approval.** The branch descends from the still-isolated generator
candidate `279c45b3`. Do not merge the whole branch into production. The
three-file kernel-only change is `kernel-meter-v2.patch`; those baseline files
are identical on `279c45b3` and `b11e1f65`.

Only `kernel/kernel.ts`, `core/check.ts`, and new `kernel/meter.ts` differ from
the generator parent. `kernel/prove.ts` / `fullWork`, counts, weights and budgets
are unchanged. No weight vector or W has been chosen. This is raw observation,
not completed I1–I3 and not a performance or 29-protocol acceptance gate.

## Independently verified initial checks

- Four-profile matrix: `20261110-103917-o1bcsv`, task
  `23b1daa8-37f8-4845-921b-2ad4e9b97239`.
- Independent audit: `20261110-104334-8uqy2w`, task
  `b5038f31-eb77-4480-84e0-fbfd6b703aef`.
- Each of plain, zero, double and deterministic-random profiles passes the same
  **262-test / 2,314,327-assertion** vector. The file-qualified vector hash is
  `ba5b6e512633ced7ab92a9668e48d4095847ef58acfec75c210d1257d12c7d5d`.
- Preload and Bun afterAll receipts prove the counter mutations were exercised
  during checking, not merely configured before a run.
- AST audit: 14 additive sites in `kernel/kernel.ts`, six in `core/check.ts`.
  Removing only the observations reproduces the baseline checker AST. Explicit
  reads, a counter-increment result used by a branch, and unrelated changes are
  refused by negative fixtures.
- The independent reader verifies source blobs and compressed-stream hashes.
  The repaired reader rejects the original missing-receipt matrix as a negative
  fixture. It does not silently discard failed results.
- Roster, decoder, type/lint and commitlint pass in the coverage matrix. A final
  tooling-only check of the latest auditor source also passes:
  `20261110-104411-6i7p2c`, task `bc1179f8-0bc1-4efc-a902-8b8a9e21cc9e`.
  The protected source blobs remained unchanged.

The profiles happened to use Ryzen 9950X, EPYC 4585PX and EPYC 9455 hosts. This
is **not** the 29-protocol, three-CPU verdict/unit determinism census.

## Required before use

1. Lane D's independent 28-certificate accept/refuse bit-vector replay, including
   meter-zero/double/random mutation during checking. The selected tests above
   do not replace that corpus.
2. Review operation coverage and wrapper/callee counting: linear coefficient
   validation, row materialization, pair-loop iterations, rational rows and
   partial failed work must reflect distinct work rather than double-charging.
3. No calibrated `fullWork` wiring before D1. I2 AST/evaluation/sampling/finite/
   instance/cube/CDCL/EPR accounting, I3 ledger and F3 detection remain unfinished.
   D2 owns weight fitting and W; F1–F7 and the full deterministic census remain.

## Preserved failed attempts

- First meter matrix `20261110-103004-kiock2`: zero worker exits, but independent
  audit `20261110-103257-i1cc7y` failed because the process-exit hook emitted no
  mutation receipts. It is not accepted mutation evidence.
- Corrected-hook matrix `20261110-103354-jyb8xc`: all four 262-test runs passed
  with exercised receipts, but plain auxiliary lint rejected an ANSI regex in
  the reader. Replaced by Node's standard utility; no checker behavior fix.
- Generator intake still lacks quiet-host qualification: three initial workers
  were rejected before generation by measured host noise. Thresholds unchanged.

All compute and receipt processing ran on boat. No subagents, no new local
whole-tree copies, and no active production kernel or model changes.
