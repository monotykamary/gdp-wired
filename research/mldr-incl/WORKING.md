# RESUMED — user instruction, 2026-11-10

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
