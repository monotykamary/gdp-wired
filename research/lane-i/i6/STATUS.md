# I6 — active, not yet admitted

Current local follow-up: `17119b50` repairs the sharded_kv cap gap; all 28
originals fit within 1,024 units of 15M (maximum excess 276.18), preserving
this I6 baseline's 10 checked proofs and all flags-off receipts. D admission
is still pending. See `../cap-gap/RESULT.md` and its exact-source receipts.
The source-specific history below is unchanged.

Draft source: `3281eb7fdcda5e04aab2c67a4950ee8e36cf1ef0`, on the `00b58ee5` line after admission optimization.

Production delta: `core/meter.ts`, `core/check.ts`, `core/infer.ts`, `kernel/kernel.ts`.

- `checkSteps`: executed tree nodes, counted-check boundaries, arithmetic derivation steps and witness rows.
- `tableCells`: built linear-table coefficients, canonical-table accesses/keys, executed cell-pair tests and parsed canonical-text cells/characters. Cache hits do not charge reconstruction.
- `cubeTests`: executed sampled form/cube tests and direction/residual evaluations.

All three are opt-in under the frozen full-work profile. Writers have no clock, callback, reset, budget or proof decision. Flags-off keeps these three columns zero. An independent AST eraser checks that checking algorithms are unchanged.

Two admitted identities change: `core/check.ts` and `kernel/kernel.ts`, **PENDING-D**. Lean, the other 132 protected identities and the prover body are untouched. Vector schema/weights unchanged. This is not calibration; the previous fit cannot be advertised as complete for this source.

B9 reference: lane B's `research/track-m/probe-strategy-tail.ts`, `core/count-stage-trace.ts`, `runs/track-m/resume-20261110/strategy-tail/`. The trace files were uncommitted when inspected; no uncommitted strategy code was integrated. First star native STEP check: 12,283.76 ms at zero units. First row: 3,468.77 ms at zero units. These are reference observations, not current-source measurements.

Native gate: **121 tests / 1,356 assertions pass**, including existing cap controls. AST erasure is exact for checker, kernel and inference. **132 other protected identities and the prover body are unchanged.** Full type/lint passes across **1,791 files** on `1066f267` (production identical to `3281eb7f`). Logs are archived under `results/`; the initial harness-only nullable-array error is retained. The 28-original / flags-off census completed on `1066f267`: 10 proved/checked, 18 unknown; all 28 flags-off normalized receipts remain exact and forbidden clock reads are zero. Compared with `00b58ee5`, `simple_election` and `client_server_ae` have changed budgeted verdicts. The completed ten-run causal controls support accounting-driven local/outer stops, not a persistent proof failure: on/lifted both prove; shadow matches off in the old 23 counters and normalized results. See `CAUSAL.md`. The independent audit also reports `sharded_kv` at 15,120,328.2561 units, above the old 1,024 slack. Accordingly I6 is observation-gated, NOT accepted. Complete census and diagnostic logs are retained in `results/census` and `results/census-audit`.

The old 1,024-unit bound is not asserted for I6 until rerun. Equal-work comparisons must preserve other columns; an enforced budget may now correctly stop earlier. B's committed capture `cace38bc` now replays positively on both sources: all 16 original calls accept, all 16 empty-derivation mutants reject, and other 23 counters match. STEP checks charge 79,061,951 (Inv*) and 77,951,219 (K3) previously unobserved provisional units. See `TAIL-REPLAY.md`. The B strategy dependency closure itself is still not promoted as GREEN. Separate A/B/F approvals are not composition approval.
