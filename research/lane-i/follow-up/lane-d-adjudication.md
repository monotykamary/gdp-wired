# Lane D: adjudicate the a8bbe098 RED entries

Baseline: `8214a543bc44e88d979f9e4457d7370e7e3c122b`.
Candidate: `a8bbe0984f270070eba9bc166a89909d0c67597e`.
Neither production source nor the original IC3Syn model changed.

## Result under the agreed majority rule

There are **zero candidate-only losses** in every complete five-pair cohort.
None reaches the rule's threshold of three. Please adjudicate the three
original RED entries as not reproduced/noise for this gate decision.
This is not a causal explanation of the historical failures, a deletion
of those receipts, or a claim that the full Lane D gate is green.
No speculative generic solver patch is justified by these reruns.

| Target / primary CPU | Base | a8 | Candidate-only losses | Native timing evidence |
|---|---:|---:|---:|---|
| `two_phase_commit`, EPYC 4585PX | 5/5 proven | 5/5 proven | 0/5 | Root 9.289–11.347 s / 9.831–14.139 s |
| `two_phase_commit`, Ryzen 9 9950X | 5/5 proven | 5/5 proven | 0/5 | Root 8.524–11.690 s / 8.804–12.281 s |
| Accounts inference, `core/infer.test.ts:47`, Ryzen 9 9950X | 5/5 pass | 5/5 pass | 0/5 | Slowest native case 2.039 s / 1.954 s |
| Full `core/sums.test.ts`, Ryzen 9 9950X | 35/35 cases pass | 35/35 cases pass | 0/5 file runs | Slowest native case 1.554 s / 1.446 s |

The protocol uses its original `--ms 60000`. Inference keeps its 15-second
proof allowance; sums keeps Bun's 5-second test limit. No test, theorem,
proof allowance or timeout was widened. Odd repeats run candidate first,
even repeats baseline first; both sides use fresh processes on the same VM.

## CPU and trace custody

- Primary EPYC: `two-phase-epyc-xlarge`, actual **AMD EPYC 4585PX 16-Core
  Processor**, eight of sixteen vCPUs pinned, exclusive/no co-tenants.
- Primary other CPU: `two-phase-traced-1`, actual **AMD Ryzen 9 9950X
  16-Core Processor**, eight of eight vCPUs pinned, exclusive/no co-tenants.
- Primaries are per batch: the original untraced batch keeps
  `two-phase-other-1`; the table uses the first eligible phase-traced
  worker, `two-phase-traced-1`, for its native timing data. The decision
  audits every cohort, not just either primary.
- All seven protocol cohorts are retained: **35 pairs / 70 proven runs**,
  including the extra 9950X and 9700X cohorts. Every cohort has 0/5 losses.
- Four initial EPYC probes and one default-size probe landed on Ryzen.
  These five skips are retained and are **not** counted as protocol runs.
- `GDP_INFER_TRACE=2` supplies native inference phase deltas. For example,
  EPYC pair 1's kernel phase is 4,391 ms base / 4,581 ms candidate; the end
  phase is 1,484 / 1,621 ms. These are individual phase deltas, not a new
  additive end-to-end budget. All phases for all traced runs remain in
  the compressed native stdout/stderr records.

The independent audit checks source/revision hashes, both source receipts,
five complete alternating pairs, all ten native outputs, raw trace hashes,
unchanged command arguments, native case counts, clean source endings,
fixed CPU identity, exclusive placement, and the majority calculation.
Required EPYC and other-CPU coverage both pass.

## Receipts

- `runs/lane-i/a8-regression-reruns/`: original eight-worker batch,
  including all four CPU skips and both complete test cohorts.
- `runs/lane-i/a8-regression-phase-reruns/`: four phase-traced cohorts.
- `runs/lane-i/a8-epyc-recovery/`: actual EPYC cohort, default-size skip,
  and the retained first commitlint installation failure.
- `runs/lane-i/regression-receipt-audit/`: successful independent audit
  (`20261110-095013-rr4jr8`).
- `runs/lane-i/follow-up-finish/`: boat-rendered summary and passing
  file-fed commitlint (`20261110-095211-rt8xfl`).
- `runs/lane-i/follow-up-final-verification/`: final current-tooling
  source check and receipt revalidation — passed in
  `20261110-095250-95qs99` with no warnings/errors and no OOM delta.

The type/lint retry fixed only the new research auditor's explicit-sort
comparator, not production code. The current seven-file tooling overlay
passes the 1,646-file check; its native audit again confirms CPU coverage
and zero majority regressions. Earlier missing-CLI/Git-root and lint
failures are preserved; none is relabelled as a successful worker.

## Other outstanding work stays separate

- The existing mixed-clause policy already gives **1152.3382236** p1 units
  on both sources in all five fresh control pairs. All ten p1 certificates
  independently replayed. The candidate's three canonical Paxos runs keep
  **6,915,544 solver / 1,037,946 full work**. See `results.md` for the old
  cost control's unknown whole-Paxos runs and the P* diagnostic boundary.
- The earlier effect-pool loss also did not recur in five same-EPYC pairs.
  Its original failure remains recorded; this is not proof of its cause.
- Lane A's original-model finite-prefix census and later loaded-row
  generator remain under qualification. B/F/E helpers remain off and
  unmerged. No P* result is credited to original-model 29/29.

All newly requested receipt processing and checking runs on boat, using
existing inputs; there are zero subagents and no new local whole-tree copy.
