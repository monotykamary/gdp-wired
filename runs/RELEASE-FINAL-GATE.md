# Independently verified release gate — bar pending

Code/test revision: `9877b8762d516506cda2b222282447235ae6fd5b`.
Required baseline: `b11e1f651618b3d3fcaf6cec66b4a8b0203cdcd3`.

This is the full-suite/fuzz/private-replay gate, **not yet the final GATE GREEN**. The canonical quick bar remains a separate requirement.

## Verified on submission-class Boat

- All seven canonical per-unit suite shards: **1,719 test executions passed**.
- Check/typecheck/lint and build passed; 38 export/default-runtime tests and 6 original runtime regressions passed separately. The two treadmill tests and commitlint passed.
- **24 mutants caught**: 3 optional-choice, 5 CI-audit, 3 sibling and 13 source-boundary mutants. Source restoration was checked.
- **1,664 default-config differential cases**: 128 per each of 13 families; 1,411 extracted; 14,644 candidate laws; 3,307 validated source proofs; 3,632 kernel proofs checked over 29,403 native rows. Zero source false proofs, false rejections, unsafe verdicts or worker errors. The 325 blocked model-law errors remain findings, not successful source proofs.
- **20/20 private laws proven with replay on**. Four native finite-domain comparisons covered 212 rows; each decision also received 2,400 start-state requests and 400 drawn-state requests. All 24 branch arms covered.
- **29/29 census verdicts unchanged**: 28 proven, `mldr` unknown.

## Evidence selection and retained failures

`runs/release-final-gate-9877b876` contains the original 26-job submission. Its 18 non-data jobs passed. Seven census jobs and the private replay failed because the controller supplied nonexistent input mount paths. Only these eight jobs were rerun, with identical code, commands, budgets and assertions, in `runs/release-final-data-retry-9877b876`; all eight passed. The independent verifier requires the original failures to be missing-data errors and accepts no other replacement job.

All eight original fuzz jobs passed, but their verbose per-case stdout exceeded Boat's bounded log channel. This dropped source-identity prefixes and early case records. The verifier correctly refused the incomplete evidence. `runs/release-final-fuzz-lossless-9877b876` reruns only these eight unchanged shards, transporting complete logs as hash-checked gzip receipts. The verifier checks every case, exact source identities, generator hashes and agreement with the original terminal counters. No fuzz budget, seed or expectation was changed.

The first collector refusal is retained in `runs/release-final-gate-verified-9877b876`. The successful independent collector is `runs/release-final-gate-verified-v2-9877b876`; its structured summary is copied to `runs/release-final-gate-verified.json`.

The initial last-mile typecheck failure, the subsequent passing check, and the positive inference/Solidity/mutant runs remain in `runs/release-last-mile-focus` and `runs/release-last-mile-check-v2`. The Solidity migration retains independent compiled-bytecode checks rather than relabeling model evidence as native-law validation.
