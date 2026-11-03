# Owned-mutation confidence result

Base: `38a3bcc` (the merged first mutation benchmark). Complete measurement:
`runs/sec-coverage/final`, boat batch `20261103-131512-52pwab`.
Every worker used the same fingerprinted primary harness, 8,000 ms search budget,
security proposals enabled, ordinary proposals disabled, and an isolated large VM.
Source/configuration hashes, exact edits, CLI verdicts, concrete owners, runs and source-state replays
are committed in [measurement.json](measurement.json). No timing improvement is claimed.

## Table

| Code / bug family | Clean stated laws proven | Mutants generated | Refuted with concrete source replay | Clean programs refuted |
| --- | ---: | ---: | ---: | ---: |
| Permission + role authorization: remove/invert guard | 2/2 | 4 | 4/4 | 0/2 |
| Tenant store: wrong write/delete key | 4/4 | 2 | 2/2 | 0/1 |
| Tenant private reads: wrong read key | 1/1 | 1 | 1/1 | 0/1 |
| Workflow: bypass prerequisite guard | 1/1 | 2 | 2/2 | 0/1 |
| Quota: remove/invert guard, off-by-one admission | 1/1 | 3 | 3/3 | 0/1 |
| Deduplication: weakened deployment isolation | 1/1 | 1 | 1/1 | 0/1 |
| Source-level lock removal | 1/1 | 1 | 1/1 | 0/1 |
| Source-level transaction scope narrowing | 1/1 | 1 | 1/1 | 0/1 |
| Atomic compare-and-set split into read-then-write | 1/1 | 1 | 1/1 | 0/1 |
| **Total** | **13/13** | **16** | **16/16** | **0/10** |

- **Measured mutation recall: 100% (16/16)** for this exact small corpus, not a population estimate.
- **False positives: 0/10 clean programs, 0/13 accepted laws.** Every clean law was proven.
- **Extraction: 26/26 versions fully read.** No refusal or timeout was removed from the denominator.
- Seventeen distinct law witnesses cover the sixteen mutants. Every witness is source-replayed on both
  mutant and clean parent. Private-read witnesses each contain two actual histories.
- All security proposals remain review-required. Unreviewed alternatives do not count as accepted-policy
  findings or false positives.

The previous six-module result (12/12, 0/6 false positives) is retained in commit `e8299e3a`.

## New concrete checks

Private reads compare every tenant-visible observation in two real object histories. A regression includes an
intermediate leak followed by equal final results, preventing a final-state-only replay from missing the leak.
The concrete tenant identity is retained independently of the prover process's string-interning IDs.

The three new concurrency mutations change **operation bodies**, not deployment declarations. Actual Effect
operations execute with the original lock/transaction scopes. Controlled replay gates only between those scopes
and reproduces the CLI fiber schedule. The clean parent's same requests are serialized under its own boundaries,
explicitly labelled rather than pretending it can execute an illegal split schedule.

All three races were additionally reproduced **without scheduling gates**, using Effect's supported native
32-operation preemption budget: the mutated sources grant more than once, the clean sources grant once.
The supplemental probe batch is `20261103-132504-3wudpr`; the committed regression repeats this with hard child-
process deadlines. An initial exploratory budget of one operation timed out or OOMed the runtime; it is not used or
counted as a detection. No prover budget was increased, and the same native setting is used for every module.

## Fix forced by the benchmark

The CLI previously printed concurrent witnesses as repeated `claim()` calls, losing fiber IDs and operation
numbers. It now uses the pure fiber formatter with normal decoded CLI arguments. The existing public `fiberRun`
export is preserved. Effect 3/4 CLI tests require multiple fiber identities and both transaction steps.
No prover/kernel rules or defaults changed.

## Scope and validation

This remains **owned synthetic training code**, not evidence about upstream CVEs or arbitrary real applications.
Real, permissively licensed modules are the next, separate stage. The Python deployment-isolation case still uses
a model-relative cache adapter, not a live database. The README records all authentication and replay assumptions.

- Complete 10-worker matrix: zero failed jobs; 16/16 detected with source replay, 13/13 clean laws proven.
- Check, build and 20 public-export tests passed in batch `20261103-131515-m3avnu`.
- Direct saved-witness verification and commitlint passed in final gate batch `20261103-132658-4qxjcu`.
- All seven test shards passed in that gate batch, with zero failed jobs.
- Final focused checks passed: 22 tests (13 benchmark/native tests and 9 Effect transaction tests),
  check, build, and 20 public-export tests. The fresh benchmark test remeasures all 16 mutants.
- The native no-hook regression produced one grant on each clean source, two on the lock/CAS mutants,
  and four on the transaction mutant when replaying all four requests from its witness.

See [README.md](README.md) for commands, operators and trust boundaries.
