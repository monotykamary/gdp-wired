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

See `runs/REPORT.md` for final acceptance and the complete failure history. Engine commit `699b5160` passes all required gates; standalone C9/C11 certificates remain separately authenticated with zero search. `run-gates.sh` reproduces the ordered gate sequence, `final-evidence-jobs.json` refreshes the 38-obligation family and certificate checks, and `bun runs/track-p-final-gates-v5/verify.ts` checks the retained acceptance record.

Structurally supported attempts use definition-local source contexts and proof-directed admission. Required helper proofs also start in a goal-local coarse context, with the current goal retained and full-context fallback. Only a tree widened and checked against the exact whole goal is retained; subset models are ignored. This shares, rather than extends, the existing deadline.

`GDP_COUNTS_RELEVANCE=1` optionally probes the older fixed-size law contexts and lifts certificates to the full context. Count-first scheduling is automatic for structural count/global support; `GDP_COUNTS_COUNT_FIRST=1` can request it elsewhere and `GDP_COUNTS_COUNT_FIRST=0` disables it for controls. These switches do not enlarge the per-law or outer allowance, and none is needed by the accepted original-harness run.
