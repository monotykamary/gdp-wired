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
independent archive/hash/count audit completed under
`c4e99d55-ad36-4939-b25e-98feaa77f55e`, batch `20261110-072741-9261hm`,
using an absolute jobs path. It found zero archive-integrity issues, passed
three refusal fixtures, and retained every acceptance blocker. Raw observed
shard totals are 1,564 passes, 17 skips, one failure and 606,052 assertions;
these are not a completed/full-passing-suite claim. The failed shard stopped
before its later units. The corrected six-job qualification subsequently completed as follows.

## Corrected selection and effect pairs (547badb3)

Batch `20261110-072557-nomeq6` ran six exclusive boat jobs. All **25**
targeted files executed: **163 pass, zero fail, 11,974 assertions**.
TypeScript passed, then type-aware lint rejected `no-unsafe-finally` in the
qualification worker. Peak RSS was 3,186,816 KiB with zero OOM delta and
no PID OOM event; the historical lint SIGKILL has not reproduced here.

The unchanged isolated effect test passes on the baseline in all three
pairs and on the candidate in two. Candidate repeat 3 again returns
unknown for the three first-call laws while baseline passes. Both sides
pass all six tests / 171 assertions in the full-file pair. This is mixed
reproduction evidence, not grounds to dismiss the candidate-only loss.
No test expectation, 30-second proof budget, or native test timeout changed.

`a8bbe098` moves the clean-source refusal out of `finally` without removing
cleanup. New task `42ba776a-d33f-4210-a31d-fe52fb42476d` runs type/lint and
three source-attribution traces: original baseline, `d3adf3c9`, current
candidate, candidate with only the symbolic fix rolled back, and candidate
with row sharing disabled. The last two are explicitly experimental
controls, not gate candidates. Traces preserve the original 30-second
CLI proof budgets and capture prerequisite-lemma outcomes and root-query
work. Results and Lane D's re-gate request remain pending.
