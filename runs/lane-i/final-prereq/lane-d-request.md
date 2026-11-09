# For Lane D — request the next final gate (not gate green)

Candidate: **bf01190119f9409077a36e11a4a5b763fb6c1cad**
Baseline: **4497c4b05c3111959a2b8d808c426a0e3cab3f01**

The coordinator's prerequisites are met. Please run your unchanged official final gate against these exact SHAs. Do not reuse b788e195 as the next baseline, increase budgets/deadlines, or transfer earlier gate outcomes.

## Qualified prerequisite

- Both isolated fixes are integrated: A `1564709f` (ordinary counted reasoning before finite-input recovery) and B `337294ea` (completion scoped to requested count maps). Later A/B qualification fixes/tests are integrated too.
- Independent strict `consensus_forall`: **10 paired repeats / all 20 sides proven, zero losses and zero audit issues**, on two exclusive Ryzen 9 9950X workers (`bx_5f32uf5a`, `bx_7m649ges`). No opt-outs, additional budget, or supplied laws. Strict source is `8d35b7f17506fcd1f8c1d9a05ec2624c924c855d`, baseline is the exact new main above. Batch `20261110-035023-3p9acg`, snapshot `329ef3cbe804`.
- Candidate `bf011901` differs from that strict source only in the research-only `trace-error.ts` formatter/test and retained reports/receipts. All production, kernel, gate, protocol, canonical-roster and dependency paths are byte-identical. The count runtime identity is independently checked as SHA-256 `2da24a9a74a03b527c1ba111cbcc510ea0bc8627e5dcb7b5dd81a2d15d136efa`.
- Current candidate mechanical qualification: **173 tests / 3,410 assertions, zero failures; full TypeScript/lint zero warnings/errors**. Batch `20261110-035600-xl5s32`, snapshot `31b4c9d28b5a`, both workers exclusive Ryzen 9 9950X. These are targeted/current-source results, not a relabeling of the older full-suite or failed checks.
- Candidate walls were lower in every measured pair. Do not hide the remaining work difference: candidate full work is **3,256,350**, baseline **2,665,853**; candidate solver work is **11,093,727**, baseline **14,498,189**.

Proof/receipt paths in the integration worktree:
- `runs/lane-i/final-prereq/strict/consensus-audit.json`
- `runs/lane-i/final-prereq/strict/paired-summary.tsv`
- `runs/lane-i/final-prereq/strict/consensus-cohort-20.log` and `consensus-cohort-21.log` (lossless raw traces)
- `runs/lane-i/final-prereq/lint-final/validation/validation-audit.json`
- `runs/lane-i/final-prereq/lint-final/validation/clean-check.log`
- `runs/lane-i/final-prereq/lint-final/validation/clean-targeted-tests.log`

The ordinary checker `kernel/kernel.ts` and `lean-kernel/` are unchanged from baseline; existing search/cache code under `kernel/` does differ and must remain in the official gate scope.

## Bar: include these seven exact identities

| Original index | View | Task |
| --- | --- | --- |
| 1 | chc | `vmt-chc-benchmarks/ctigar/seesaw.c_000.yml` |
| 2 | chc | `vmt-chc-benchmarks/lustre/DRAGON_4_000_001.yml` |
| 3 | chc | `vmt-chc-benchmarks/lustre/DRAGON_4_e2_2799_000_001.yml` |
| 6 | its-scc | `Integer_Transition_Systems/From_T2/bio.t2.ari` |
| 8 | its | `Integer_Transition_Systems/From_T2/bio.t2.ari` |
| 9 | its | `Integer_Transition_Systems/From_T2/cover.t2.ari` |
| 10 | tip | `tip2015/list_weird_concat_map_bind.smt2` |

The historical exact reruns yielded 42 children: 10 checked-IMC parent handoffs, 9 ordinary completions, 21 strict timeouts, and 2 PID-confirmed candidate TIP OOMs. Only three pairs had both processes exit zero; their answers agreed. This is **not** a complete no-loss bar. Audit the CHC winner/parent lifecycle but preserve its raw SIGKILL and independent proof acceptance requirements; a checked-looking log alone is not a gate pass. Eleven original non-CHC kill causes remain unrecoverable. Evidence: `runs/lane-i/regressions/bar-resource/resource-summary.json` and `runs/lane-i/regressions/bar-forensics/`.

Historical b788-based merge bisection still has a five-repeat coverage shortfall. Its repaired transport does not turn two-repeat checkpoints into qualified ones. The independently requested new-main strict prerequisite above is complete. Original MLDR remains unknown in the last pre-fix paired run; do not promote it to a proof.

Please return an exact-source gate verdict with CPU labels and retained incomplete/failing receipts. Lane I is requesting re-gating, not announcing gate green.
