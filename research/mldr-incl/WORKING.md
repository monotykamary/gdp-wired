# RESUMED — user instruction, 2026-11-10

**Latest completed source ac7eacfe:** type/lint and 87 tests / 295 assertions
pass. Fresh generated conditional safety checks at 3817.24253 units with
both member inclusions, 8.762 s wall; still UNKNOWN at 2700. Original MLDR
x3 remains UNKNOWN (59.001/59.358/59.001 s). Same 34-law machine and ordered
family, no hand law. Receipts `runs/mldr-incl-demand-range-v1/`; no full gate.

**Next running:** research 5c3686f0, seven ranking alternatives on the exact
prior family with initial ranges off, unchanged flags/caps/budgets. Batch
20261110-014758-a6x9cy, task 8b23c143-90b0-4846-8b18-d72b4bfc14b3,
output `runs/mldr-incl-member-rank-v1/`. No production ranking change.


**Confirmed paired result:** exact same 34-law machine/family; eager
ranges UNKNOWN at 6000.223364 in both orders, only initial ranges disabled
checks START and STEP at 3817.24253 in both orders. Actual tree uses two
member inclusions and one row inclusion. Conditional only; measured wall
13.825/23.411 s, not a wall pass, and still above the 2700-unit share.
Targeted completion off checks at 3974.8476248, no counted-work gain.
Receipts: `runs/mldr-incl-range-regression-v1/`.

**Production candidate ac7eacfe:** B/Fable demand-driven ranges integrated
without losing E member/freshness handling. Pending guarded validation,
batch `20261110-014532-stsqg4`, task
`6d94b6ed-c01f-4ca9-8617-876fed697db3`, output
`runs/mldr-incl-demand-range-v1/` (five parallel jobs, reused frozen base,
108 KiB overlay, no new archive). No full-gate or merge claim.


**8e7e8630 executed:** type/lint and 82 tests / 280 assertions pass.
Original MLDR x3 remains UNKNOWN at 59.029/59.092/59.002 s. Fresh generated
34-law conditional safety is UNKNOWN at both 2700 and 6000 units; no new
certificate. Actual historical-command failure is the 300000-byte pack
limit, not demonstrated shell quoting. Receipts are preserved in
`runs/mldr-incl-resume-preflight-fixed-v1/`; no gate-green claim.

**Current work:** 3af3d9ad research-only exact-family comparison and
same-VM eager initial-range on/off in both orders, plus corrected targeted
completion with the unchanged 48-tuple cap. Active task
`01d0b4ba-830f-4aa4-a730-c712b43219f5`, output
`runs/mldr-incl-range-regression-v1/`. It investigates why pre-range E's
conditional 3817-unit certificate is not reproduced after range integration.
No production change or new archive; all candidates must pass fresh replay.


**Latest:** `f0eb7671` preflight passed TypeScript, then failed four
no-useless-escape lint errors in the disabled research installer. Repair
`8e7e8630` changes only those escapes, preserving emitted code. No focused
tests or new proofs have passed yet. Active corrected six-job run:
`da84933a-c5b8-4201-984f-ae4940c2b139`, output
`runs/mldr-incl-resume-preflight-fixed-v1/`. It reuses the frozen base plus
two tiny hash-checked source replacements. Every proof is source-check
guarded. The older five-job batch remains untouched until terminal.


**Actual execution now available:** frozen-v3 finished; all six jobs exited
2 on TS2345 in `research/track-m/lane-f-frame-falsifier.ts:25`. No original
or conditional proof command ran. Repair `f0eb7671` is an explicit type
union only. Active focused check: task
`b1dad863-97ea-448e-a0b0-6f8396391c87`, output
`runs/mldr-incl-resume-typefix-check-v1/`. It reuses the same frozen tree
with a tiny before/after-hash-checked overlay; no new tree archive. The
remaining five jobs are queued under task
`fee9b63c-74e6-4e11-be56-51c066e54cf8`, output
`runs/mldr-incl-resume-typefix-proof-v1/`; each independently requires its
source check to pass before any proof command. See runs/REPORT.md.


**Submissions reopened.** All three old exact batch IDs now report `no such
batch`; their output directories are empty. New six-job guarded validation
is running from completed immutable-by-use source export
`/tmp/gdp-wired-incl-resume-84a7a672`, source
`84a7a6728d578e3918b969574a36a295fc2ad5a2`. The bare export first failed
before admission (missing Git index); standalone Git metadata repaired that
without changing source bytes. **Registered:** `20261110-004001-gs8s50`,
active controller `1ce194cd-f78d-4226-9f50-41ba03b3fb16`, output
`runs/mldr-incl-resume-frozen-v3/`; six jobs queued, no results yet. Do not
duplicate it. No subagents. Disk policy is recorded in runs/REPORT.md:
reuse this source, no new per-run archives, delete nothing without approval.


**Coordinator resource hold:** no new parallel local work, submissions or
retries until lifted. This lane has no subagents. Existing boat batches
are not to be killed or resubmitted. Both formerly active controllers
below failed in source upload (`blob bytes do not match their key`), not
in tests/proofs. The attempted frozen export timed out before submission;
`/tmp/gdp-wired-incl-resume-ca0ef8f9` may be partial. See the superseding
resource-hold section at the top of runs/REPORT.md and preserved receipts.


The unchanged cancelled check was submitted first, batch
`20261110-000811-qbrwk7`, and its controller timed out at 600 s with no job
log. Authenticated close also timed out: that batch's cleanup is unconfirmed.
Receipts: `runs/mldr-incl-resume/`.

Production repair `1a1c37e4` removes the duplicate range import only.
Research commit `5f8c1e59` adds corrected quoting, a lossless family/both-phase
archive with four tests, and fresh-process conditional replay. None is yet
validated remotely. Existing active tasks, **collect before duplicating**:
- `9e2450b2-a42e-4e93-bd26-ce49e427a602`, batch
  `20261110-001749-c8xynq`, output `runs/mldr-incl-resume-check-v2/`.
- `5cae319c-b8f2-47da-b841-d6c037736e43`, output
  `runs/mldr-incl-resume-validation-v1/`, six parallel source-check-guarded
  jobs including original x3 and corrected conditional replay.

The scheduler health route answers but state/close requests time out;
no shared process or VM was stopped. No new proof experiment may execute
before its own source check passes. See runs/REPORT.md for current status;
the archived pause and exact resume plan follow there.
Finished production change: 2047d2be (generic member premises, tests).
Integrated source: 36a278e9 (B 6d69e094, A fdabeba4 as 3b500f8f,
F 682c8dc6). No new merge or push during this checkpoint.

All three owned controllers were stopped by exact task ID; their exact
scheduler batches were closed separately, and each final /snapshot reported
no such batch. The final task list had no active tasks. No shared VM or
scheduler was stopped. Receipts: runs/mldr-incl-checkpoint/.

Cancelled/closed:
- f11ae145-a0d5-4bc9-8372-add45e25265d / 20261109-154101-p0ocxa /
  runs/mldr-incl-integrated-production-v1: original harness x3, fresh
  generation/conditional/replay, integrated check. Scheduler had terminal
  rows: originals exit 0 at 59.48/59.58/59.69 s; conditional exit 1; check
  exit 2. Raw logs were not collected. NO verdict may be inferred; rerun.
- 909380dd-2e23-47d5-9759-420c2527c0f2 / 20261109-154340-h0gizc /
  runs/mldr-incl-targeted-completion-v1: invalid research fixture missing
  closing brace. Scheduler rows 1/1/2. No usable proof/performance result.
- 2d21c31c-c946-4177-81ef-9f6a7e45c45f / 20261109-154505-9np97s /
  runs/mldr-incl-targeted-completion-v2: corrected research fixture.
  Scheduler rows 0/0/2, no downloaded proof output. Not a checked win.

Established BEFORE those cancelled batches: on the captured no-hand-law
34-law family and pre-range E source, conditional safety START/STEP checkMC
true at 3817.24253 units under 6000. 2700 remains UNKNOWN. Pre-merge type/lint
and 53 tests pass. Early complete-all ordering at 6000 remains UNKNOWN and
was not adopted. Old self-dependent witness packet was rejected correctly.

Open: integrated type-check failure, conditional/replay failure, original
verdicts, explicit used-premise replay, unvalidated targeted experiment.
Lane D audit blocker remains: old 84/87 vs 83/87 and 1073/18 counts are only
iteration observations. No authoritative exact-source roster/receipt gate,
29/29, GATE GREEN, full safety, main merge or push is claimed.

On resume: recover logs if possible, otherwise rerun frozen manifests on
boat. Diagnose integration check and replay failures first; do not enable
research-only targeted completion. Then fresh conditional proof + source
replay and original harness x3; final suite acceptance belongs to Lane D.
Leave pre-existing research/claude-import/ untouched.
