# Track P: counted-support experiments

Research-only scripts for the original `paxos_epr` harness. Protocol IDs and reference-family indices occur here, never in the engine or kernel.

- `capture.ts`: optional observer; saves complete candidate and attempt inputs. Combine with `research/query/dump.ts`.
- `pack.ts`: return selected unknown queries as an xz/base64 archive within boat's stdout limit. Keep `family-first.json` for initial candidates and `family.json` for the final observed context.
- `candidates.ts <reference-family.json>`: compare generated names/alpha-normalized formulas with the supplied historical family.
- `replay.ts <dump-dir> [shard] [shards]`: whole-goal versus relevance-first search; `REPLAY_MS` defaults to 1500. Checks lifted trees against the original goal.
- `production-replay.ts <fixture-dir> [indices...]`: uses the exact exported production attempt (`countedAttempts`), including selector choice, reservation and model refinement. It tries the ordinary pass order within one 1500ms allowance, checks every returned certificate, and checks the assembled fixed family when all 19 laws close. The fixture directory contains `family.json`.
- `family.ts <reference-family.json> [shard] [shards]`: historical simplified replay. Its all-input seeds, polarity-only selector and repeated selection differ from production; do not use its open-goal count as a production result.
- `profile-step.ts`: measured legacy/retained/seedless/hand C11 controls, with diagnostic search counters. `analyze-failure.ts` compares retained failure packets with checked hand requests without running a prover.

Run substantive commands through `supercomputer`, with `--vm-type large --timing` for timing claims. Pass fixtures with `--data <local-fixture-dir>:research/track-p/input`. Keep private handoff inputs out of commits; explicitly requested checked certificates and their source/diff evidence are retained under `runs/`.

The selected-count path can use actual seeded bounds to start with relevant existing instances. Closure ignores unreferenced optional reads, matches complete affine remainders rather than cancelling packed coordinates, and keeps original guarded premises. Symmetric term premises share a slot; count-pool reuse caches proposals only, keyed by exact count-read spellings, declarations and the negative conclusion. Duplicate count reads and primitive-only growth do not rebuild the pool. Reification and final original-context checking remain mandatory.

See `runs/REPORT.md` for measured successes, failures, and unpassed gates. Checked standalone C9/C11 certificates establish derivability, not production success.

Supported attempts now try one bounded goal-level relevance proof before model construction when no count witness is active. Only a tree widened to the exact whole goal is retained; subset models are ignored. This shares, rather than extends, the existing deadline.

Additional experimental production switches (off unless enabled): `GDP_COUNTS_RELEVANCE=1` probes small law contexts and lifts certificates to the full context; `GDP_COUNTS_COUNT_FIRST=1` gives count-reading laws their counted pass first, within the same per-law/outer allowance.
