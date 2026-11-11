# Admission optimization — active validation

Production: `2eec34ce`; pilot source: `60f8aecb`; typed harness/native driver: `3d0256f0`.

No batching or credits. Every interpreted expression still calls pre-admission. The full-work sum is unrolled in exactly the former floating-point addition order; the common single-evaluation path avoids dynamic-key dispatch and redundant count validation. Weights and budget rules unchanged; flags-off keeps the old aggregation loop.

Pilot batch `20261111-041441-kni4ly`, logs `runs/lane-i/admission-pilot`:

- 26 tests / 123 assertions pass; 134 protected identities and prover body unchanged.
- Same-VM ABBA on AMD EPYC 4585PX: 1,800,000 evaluations, 36,000 uncalibrated units, one admission per node, identical raw vectors.
- Baseline 1543.82 / 1692.46 ms, mean 1618.14.
- Candidate 25.05 / 21.68 ms, mean 23.36.
- Mean 69.26x speedup: microbenchmark only, not whole-proof speedup.
- The pilot static failure was harness-only (untyped/nullable sample array); corrected by `1066f267`. Full type/lint now passes over 1,791 files with I6 present. Both failed logs are retained.

Native finite/compiled ABBA pairs on the unchanged hash-bound MLDR fixture are running: batch `20261111-041759-v2imrf`, task `c699fa43-45eb-4498-b09c-540e6fbb8358`, output `runs/lane-i/admission-native`. Raw vectors, results, profile and units compared exactly. No native speedup claim yet.

D base gate `f95b8061` does not automatically admit this patch or I6. Rolling A/B/F overlay waits for approved prerequisite closures. No main merge/push.
