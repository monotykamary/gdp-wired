# Track P: counted-support experiments

Research-only scripts for the original `paxos_epr` harness. Protocol IDs and reference-family indices occur here, never in the engine or kernel.

- `capture.ts`: optional observer; saves complete candidate and attempt inputs. Combine with `research/query/dump.ts`.
- `pack.ts`: return selected unknown queries as an xz/base64 archive within boat's stdout limit. Keep `family-first.json` for initial candidates and `family.json` for the final observed context.
- `candidates.ts <reference-family.json>`: compare generated names/alpha-normalized formulas with the supplied historical family.
- `replay.ts <dump-dir> [shard] [shards]`: whole-goal versus relevance-first search; `REPLAY_MS` defaults to 1500. Checks lifted trees against the original goal.
- `family.ts <reference-family.json> [shard] [shards]`: independently replay 38 reference INIT/STEP obligations with generic proposals. Reports `checkMC` for every success. Not whole-family admission; never injects historical laws into production.

Run substantive commands through `supercomputer`, with `--vm-type large --timing` for timing claims. Pass fixtures with `--data <local-fixture-dir>:research/track-p/input`; do not commit captured goals or private handoff inputs.

The selected-count path can use actual seeded bounds to start with relevant existing instances. Closure ignores unreferenced optional reads, matches complete affine remainders rather than cancelling packed coordinates, and keeps original guarded premises. Symmetric term premises share a slot; count-pool reuse caches proposals only, invalidated by actual count-dependent law/flag instances. Reification and final original-context checking remain mandatory.

See `runs/REPORT.md` for measured successes, failures, and unpassed gates. Checked standalone C9/C11 certificates establish derivability, not production success.

Experimental production switches (off unless enabled): `GDP_COUNTS_RELEVANCE=1` probes small law contexts and lifts certificates to the full context; `GDP_COUNTS_COUNT_FIRST=1` gives count-reading laws their counted pass first, within the same per-law/outer allowance.
