# Next-candidate preflight: retained outcomes

First candidate: `1fc444caa66a97b16fffb5e27c766cc988d60580`.
Required baseline: `8214a543bc44e88d979f9e4457d7370e7e3c122b`.
Batch `20261110-070951-nblx62`: 14 boat workers, 12 exit 0, 2 fail.
Controller exit 0 is not acceptance. Final gate remains RED.

- The unchanged Lane D symbolic probe passes on both roots, including its
  explicit-symbolic positive and constant-only negative controls.
- Three fresh combined-candidate p1 attempts replay independently at
  1152.3382236 units. Three whole-Paxos runs prove at exactly 6,915,544
  solver / 1,037,946 full work. This does not claim original MLDR 29/29.
- Completed evidence re-audits and commitlint pass.
- Type checking fails with TS2345 at `next-gate-stage.ts:41`: the closed-over
  stage path remains typed `string | undefined`. Lint is not reached.
  Measured peak process-tree RSS is 3,156,652 KiB; no OOM delta or PID OOM
  was observed. This is not a repeat or a diagnosis of the prior lint SIGKILL.
- Six full shards pass. Shard 2 reports 155 pass, 17 skip and one fail:
  the unchanged effect-pool CLI test gets unknown for all three laws where
  it expects proven. The file continues, but the shard stops after that
  failed core batch; later shard units are not claimed to have run.
- The targeted job reports 60 pass / 11,128 assertions in 12 files, not the
  intended 25. Thirteen paths incorrectly said `core/recovery/` instead of
  `core/count-recovery/`; Bun silently ignored them. This result is NOT
  accepted as coverage of all 21 added files. Canonical roster paths are
  correct; the defect is in this auxiliary selection.
- TIP `tip2015/relaxedprefix_correct.smt2`, three alternating same-worker
  pairs on Ryzen 9 9950X: baseline returns unknown with exit 0 in all three;
  candidate returns unknown with exit 0 twice and is outer-time-censored
  (exit 124) once. No earlier error or OOM kill reproduced, but the timeout
  remains incomplete. Candidate peak RSS is about 10 GiB versus roughly
  6.2–6.8 GiB on the baseline. All six report zero host OOM delta.

Repair `547badb3` changes qualification tooling only, not prover/runtime
sources: a narrowed stage-path binding, corrected paths, existence guards,
and unchanged same-worker isolated/full effect test comparisons. Its six-job
qualification is pending under `61bd3c87-e7a6-43da-8592-04d4186511f7`.
The original packet has not been overwritten. The first archive-audit
launcher failed before admission because its jobs path was relative to the
wrong directory (`5e6a4244-b560-4f64-b7ff-b95af4e9d436`). The identical
independent archive/hash/count audit is now pending under
`c4e99d55-ad36-4939-b25e-98feaa77f55e`, using an absolute jobs path.
