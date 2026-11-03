# Owned-mutation confidence result

Base: `46ab97b6` (the merged snapshot-root fix). Measurement:
`runs/sec-mutants/final`, boat batch `20261103-124420-x48qxl`.
Every worker used the same fingerprinted harness, Bun version, 8,000 ms per-law budget,
security proposals enabled, ordinary proposals disabled, and an isolated large VM.
Source hashes, configuration hashes, exact edits, CLI verdicts, runs and source-state replays
are committed in [measurement.json](measurement.json).

## Table

| Code / bug family | Clean stated laws proven | Mutants generated | Refuted with concrete source replay | Clean programs refuted |
| --- | ---: | ---: | ---: | ---: |
| Permission + role authorization: remove/invert guard | 2/2 | 4 | 4/4 | 0/2 |
| Tenant store: wrong write/delete key | 4/4 | 2 | 2/2 | 0/1 |
| Workflow: bypass prerequisite guard | 1/1 | 2 | 2/2 | 0/1 |
| Quota: remove/invert guard, off-by-one admission | 1/1 | 3 | 3/3 | 0/1 |
| Deduplication: check-then-act under weakened isolation | 1/1 | 1 | 1/1 | 0/1 |
| **Total** | **9/9** | **12** | **12/12** | **0/6** |

- **Measured mutation recall: 100% (12/12)** for this exact small corpus, not a population estimate.
- **False positives: 0/6 clean programs, 0/9 accepted laws.** All nine clean laws were proven, not merely unrefuted.
- **Extraction: 18/18 versions fully read and checked against source.** No refusal or timeout was removed from the denominator.
- Thirteen distinct law witnesses cover the twelve mutants (one wrong-key mutant refutes both domain laws).
  Each witness was run on the mutant and the clean source. `verify.ts` reproduces the saved receipts without
  asking the prover again, including the full state/effect observations.
- All proposals retained their `review: required` status. Broken unreviewed candidates do not count as findings
  or as false positives against an accepted policy.

## Representative concrete effects

An unauthorized request changes the counter in both authorization mutants; the clean guard returns without
changing it. A tenant-key substitution inserts or deletes a foreign row. The workflow guard mutation permits
shipment before approval. An off-by-one quota admits one request when the validated limit is zero.
The isolation mutant lets both payment calls read an absent marker before either commits, producing two real
calls to the declared effect; the atomic parent serializes the same requests and produces one.

## Scope and fixes forced by measurement

This is **owned synthetic training code**, derived from the feature's fixture patterns. It is not evidence
that arbitrary real-world applications are supported or that published CVEs are detected. No third-party
application was examined for unknown vulnerabilities.

The concurrency mutation changes the declared deployment isolation, not the method body. Its replay executes
that body with a deterministic model-relative cache adapter, not a real database. The printed witness omits
an irrelevant effect payload; generic typed argument completion is explicitly recorded and replayed. The first
probe refused this incomplete call instead of claiming a kill; the harness was fixed, not the fixture or prover.

Other benchmark safeguards include scope-checked step laws, literal-only trace parsing, complete mutation-set
validation, matching clean policies, and rejection of empty or failed replay evidence. No per-file mutation
exceptions, prover/default changes, kernel changes, or larger budgets were needed.

## Validation

- Complete final matrix: six jobs, zero failures; 18 source versions and all 12 mutants measured.
- Direct saved-witness verifier: passed on boat; no prover invocation.
- All seven test shards passed in batch `20261103-124735-88f3lq`; strict commitlint passed there too.
- That batch caught one new test-only lint error (`await` on Bun's void-typed rejection matcher).
  It was replaced with an explicitly awaited rejection result. The fresh-recall regression was also
  expanded from one module to the entire corpus.
- Final affected checks passed in batch `20261103-125616-e7apie`: **10 benchmark tests**, including a fresh
  all-mutant measurement and exact saved replay; **check**, **build**, and **20 public-export tests**.
- No `core/`, `kernel/`, package-export or build-configuration changes. No extra prover bar was run for
  this benchmark/documentation-only change.

See [README.md](README.md) for commands, operator definitions and trust boundaries.
