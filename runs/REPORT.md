# RESUMED — lane E, 2026-11-10

## Submissions reopened — frozen-source retry

After the coordinator reopened submissions, authenticated `/snapshot` calls
reported **`no such batch` for all three old IDs** (`20261110-000811-qbrwk7`,
`20261110-001749-c8xynq`, `20261110-002140-jvt2tb`), and all three old output
directories remained empty. No registered work was duplicated.

Exported **`84a7a6728d578e3918b969574a36a295fc2ad5a2`** into the new isolated
`/tmp/gdp-wired-incl-resume-84a7a672`; archive extraction completed, required
files exist, and `core/counts.ts` matches the committed SHA-256
`dd70a44ea0c9b97361e9c48884a2817a16e218bf8bf3b0732a56e09668a5193c`.
The earlier partial export remains untouched. The new snapshot will not be
edited while its upload runs.

Submitted the six guarded jobs from that snapshot, `--class submission
--timing --vm-type large`, with `GENERATOR_REV` bound to the full source SHA.
The first frozen-source attempt (`3d4b5140`) failed **before admission**:
`supercomputer` requires a Git index and rejected the bare export. Added
standalone Git metadata to the same export (no source-byte change, same
`core/counts.ts` SHA-256), then resubmitted once. **Registered batch:**
`20261110-004001-gs8s50`, tree `dc1bbba248e9`, active task
`1ce194cd-f78d-4226-9f50-41ba03b3fb16`, output
`runs/mldr-incl-resume-frozen-v3/`. An authenticated snapshot confirms all
six named jobs registered and queued, zero placements/rows so far. No
subagents are running; the one-subagent memory cap remains in force.

### Disk

Coordinator disk rule is in force: no new whole-tree archive per run;
future archives are one per SHA in `/private/tmp/gdp-archives/<sha>.tar`,
reused via data input. Keep return data to necessary compact receipts,
hashes and compressed diagnostics. No write over 500 MB is planned.
Nothing has been deleted to free space. The coordinator's verified offload
to `gdp-wired-offload-20261110` is welcome: no KEEP-LOCAL exception is
requested for this lane. A bounded scan found no file over 20 MiB in the
checked-input/checkpoint directories or the active snapshot's core and
inclusion source paths. Historical bulk outputs may be offloaded; use each
`.offloaded.json` receipt and its exact `store serve` / `store pull --only`
instructions if those bytes are later needed. Do not interpret an offloaded
file as a missing proof or generate a replacement result.

| Path | Allocated size (`du -sk`) | Deletion assessment |
|---|---:|---|
| `/tmp/gdp-wired-incl-resume-ca0ef8f9` | 27,496 KiB (~26.9 MiB) | Candidate: interrupted, unvalidated export; no batch uses it and it holds no unique result. Coordinator decides; left intact. |
| `/tmp/gdp-wired-incl-resume-84a7a672` | 260,928 KiB (~254.8 MiB) | **Keep while the active controller uses it.** Reuse for this SHA rather than create another snapshot. Later removable only after needed provenance/results are retained. |


## Coordinator resource hold — supersedes active-task status below

The coordinator reports host memory pressure (7.5/8 GB swap) and slow
per-file `utime` under `blob-cache.lock`. No new local parallel work,
submission or retry until that restriction is lifted. This lane has no
subagents and has not killed or resubmitted a boat batch after the notice.

Both later controllers have now failed **during source upload**, before
job execution: check-v2 `9e2450b2` after 887 s and validation-v1 `5cae319c`,
both with `ValueError: blob bytes do not match their key`. Their receipts
are in `runs/mldr-incl-resume/`; neither is a compiler/prover verdict.
The mutable source changed while upload was delayed; that is consistent
with a source-hash mismatch, not evidence of a kernel or proof failure.

A committed-source export to `/tmp/gdp-wired-incl-resume-ca0ef8f9` timed out
before its submission command ran; the directory may be partial and is
not validated. **No frozen-source validation batch was launched.** Do not
use it as a completed snapshot. Existing scheduler batches are untouched;
the initial batch's cleanup remains unconfirmed. Resume new submissions
only after the coordinator lifts the resource hold, using an immutable,
verified source export. No tests or proofs have completed in this resume.

Static review under the hold: the prepared original/replay wrappers now keep
`bun run check` stdout rather than suppressing it, so any future preflight
failure will retain its actual compiler diagnostics in that job's own log.
The original proof commands and budgets are unchanged. This manifest edit
has not been submitted or executed.


The user explicitly resumed this lane. First action: resubmit the **unchanged**
`integrated-check` command from the cancelled integrated-production manifest,
on boat (`--class submission --timing --vm-type large`), source checkpoint
`b3f8377e`, batch `20261110-000811-qbrwk7`, output
`runs/mldr-incl-resume-check-v1/`. The controller **timed out after 600 s**
without a job result or downloaded log. This is an infrastructure failure,
not a type-check or proof verdict. The authenticated snapshot and close
requests also timed out; cleanup of that exact batch is **unconfirmed**.
Small controller/close receipts: `runs/mldr-incl-resume/`.

**Committed:**
- `1a1c37e4`: remove the duplicate `rangeInstances` import from
  `core/counts.ts`. No count selection, proof rule or allowance changed.
  The duplicate is visible in source; the remote compiler failure is not
  yet captured, so this is not a claim that all compiler errors are fixed.
- `5f8c1e59`: research-only resumed validation/replay. Correct shell quoting
  and replace the old out-of-range 300000-byte archive request with a
  lossless, capped archive: preserve the exact generated family and both
  phase certificates or fail, never silently drop a required file. Four
  archive regression tests were added, **not yet run successfully**.
  A separate Bun process reconstructs START and STEP and reports the used
  original premises/count instances. This remains conditional on helpers.

**Submitted, not validated:**
- `20261110-001749-c8xynq`, task `9e2450b2-a42e-4e93-bd26-ce49e427a602`,
  `runs/mldr-incl-resume-check-v2/`: unchanged check/test command on the
  import-fixed source (shipped tree `b1b6e375981a`).
- task `5cae319c-b8f2-47da-b841-d6c037736e43`,
  `runs/mldr-incl-resume-validation-v1/`, source `5f8c1e59`: six parallel
  jobs, including original harness x3 with the unchanged 60000-unit command
  and 75-s watchdog, the historical failed replay command as a distinct
  diagnostic, the corrected fresh-family replay, and focused checks.
  **Every proof job first requires `bun run check` to pass on that VM.**
  `GENERATOR_REV` is bound to the committed source at submission.

The shared scheduler's `/health` answers, but status, exact-batch snapshot,
and close calls do not complete. Many processes (including the shared
scheduler) have the blob-cache lock open; lock contention is a hypothesis,
not an established root cause. No shared scheduler or another lane's VM
was stopped. Do not start another duplicate controller or infer a verdict
from the absence of output. Collect the existing controllers first.

### For lane I / D

`1a1c37e4` is the production import repair; it may already be unnecessary on
I's conflict-resolved source. `5f8c1e59` is only diagnostic/replay plumbing,
not a prover improvement or gate. No remote check, fresh conditional win,
original MLDR proof, 29/29, or GATE GREEN has been established in this resume.
The earlier Lane D audit blocker remains in force. Pre-existing untracked
`research/claude-import/` is untouched. No main merge or push was performed.

## Archived pause / exact resume plan

The following checkpoint was paused at the user's request and is now resumed.
Branch: **`claude/mldr-incl`**. Last work/receipt SHA before this documentation
checkpoint: **`3e0d2b647608239305618f73ebc9d27890eed0ea`**. The final checkpoint
is the commit containing this RESUME section (`git rev-parse HEAD`).

## Committed state and established results

- Finished production change **`2047d2be`**: generic, declaration-backed member
  witnesses, actual quantified-flag/field-law instances, and existing freshness
  filtering for ordinary/cached MBQI. Its tests are committed with the code.
  No fixed protocol names or packing widths, trusted premises, kernel edits,
  or proof-budget increases were introduced.
- On the captured **34-law generated family, with helpers assumed first**,
  the pre-range-integration E source returned START and STEP certificates
  accepted by `checkMC` at **3817.24253 counted units** under the 6000-unit
  diagnostic limit. The 2700-unit probe remains UNKNOWN. This is conditional,
  not a complete MLDR safety proof. Recorded whole-probe wall was 9.625 s.
- Pre-integration type/lint and **53 focused tests / 195 assertions** pass.
  Earlier rejected self-dependent count-witness certificates and earlier
  type/fixture failures remain preserved. Complete-all early ordering did not
  improve the result and was **not adopted**.
- Integrated source **`36a278e9`** includes B `6d69e094`, A `fdabeba4` as
  cherry-pick `3b500f8f`, and F `682c8dc6`. Range and member proposals are both
  preserved. A's tiny proposals remain disabled, as upstream specifies.
  **This integrated source is not validated:** its final check and
  conditional/replay job have failure exit rows but no downloaded logs.
- Unfinished research is clearly isolated in **`738764ff` (`wip:`)**:
  `research/mldr-incl/targeted-completion.ts`, its disposable installer and
  job manifest, plus the integrated validation manifest. It is **not enabled
  in production** and must not be promoted from exit status alone.
- Compact receipts and small accepted/rejected proof archives are committed
  in `runs/mldr-incl-checkpoint/` by **`3e0d2b64`**. Large/raw output stays out
  of git. `receipt-manifest.json` records original file hashes; compact logs
  explicitly omit artifact bodies. Pre-existing `research/claude-import/`
  remains untracked and untouched.

## Cancelled controllers and closed boat batches

Every owned active controller was stopped by its exact task ID, then its
exact scheduler batch was closed. Final authenticated snapshots return
**`no such batch`** for all three; the final task list has **no active tasks**.
No shared scheduler or another user's VM was stopped. The scheduler jobs had
terminal rows by the time of closure, but their raw outputs had not been
collected. Those rows are diagnostic metadata, **not proof verdicts**.

| Exact task ID | Batch / output directory | Purpose and usable partial evidence |
|---|---|---|
| `f11ae145-a0d5-4bc9-8372-add45e25265d` | `20261109-154101-p0ocxa` / `runs/mldr-incl-integrated-production-v1` | Original harness x3, fresh generated-family conditional/replay, integrated checks. Scheduler rows: originals exit 0 at 59.48/59.58/59.69 s; conditional/replay exit 1; check exit 2. **No downloaded verdicts or failure logs.** Usable only as scheduling/failure observations; recover logs or rerun all five jobs. |
| `909380dd-2e23-47d5-9759-420c2527c0f2` | `20261109-154340-h0gizc` / `runs/mldr-incl-targeted-completion-v1` | Targeted ordering and frozen control. Original helper omitted its closing brace; scheduler exits 1/1/2. Invalid fixture; **no proof or timing claim**. Retain as failed evidence, do not rerun this invalid source. |
| `2d21c31c-c946-4177-81ef-9f6a7e45c45f` | `20261109-154505-9np97s` / `runs/mldr-incl-targeted-completion-v2` | Corrected targeted ordering at 2700/6000 plus frozen control/check. Scheduler exits 0/0/2, but no downloaded proof output. **No checked win established**; recover logs or rerun corrected source. |

Authoritative cancellation record: `runs/mldr-incl-checkpoint/cancellation.jsonl`.
The earlier per-batch `*-snapshot.json` / `*-close.json` files record an
unauthenticated API attempt (`token` error), **not** successful cancellation.
`cancellation.jsonl` records the subsequent authenticated successful closures.
`tasks-final.json` records the stopped controllers. No new batch was launched
after the pause request.

## Open blockers

1. The integrated type/check job exited 2; obtain its actual error before
   claiming the integrated branch checks clean. The conditional/replay job
   exited 1 and needs the same treatment.
2. Explicit fresh-process source reconstruction and used-premise analysis
   of the integrated proof are not completed. A proposed inclusion or a
   scheduler exit 0 is not evidence of that reconstruction.
3. No original-harness MLDR proof or 29/29 result has been established here.
   Original exit-zero scheduler rows cannot establish their verdicts.
4. Lane D's `final-audit-P80.md` blocker remains: earlier 84/87 vs 83/87 and
   1073/18 totals are **iteration observations only**. Exact roster, unique
   pair identity, source binding and six shard receipts were missing.
   Stronger interpretations remain withdrawn (`3f3a523c`). Only Lane D's
   authoritative final gate can establish acceptance; do not build more
   lane-local gate tooling.
5. No GATE GREEN, main merge, push, or publication is claimed. No new merge
   or push was performed during the checkpoint.

## Exact next steps, only after explicit resume

1. Read this RESUME section and `research/mldr-incl/WORKING.md`; verify the
   branch/HEAD and leave `research/claude-import/` alone.
2. Recover existing logs if still possible. Otherwise rerun the unchanged
   integrated-check command from
   `research/mldr-incl/integrated-production-v1-jobs.json` on boat. Diagnose
   its exit 2 first; run no new proof experiment until the integrated source
   type-checks. Keep failure receipts distinct from reruns.
3. Rerun that manifest's fresh-family conditional/replay job, retaining the
   actual generated family, exact instances and both phase certificates.
   `research/mldr-incl/inspect-production.ts` must reconstruct and check
   both source obligations and identify used count witnesses/premises.
4. Rerun its three **unchanged original harness** commands on exclusive large
   boat VMs: `bun research/protocols/ic3syn/run.ts --only mldr --ms 60000
   --skip broken`, with the existing 75 s outer watchdog. Inspect JSON
   verdicts and actual wall times, not only exit codes.
5. Only if useful after the failures are understood, rerun the corrected
   research-only targeted manifest on the frozen 34-law input. Preserve the
   existing 48-tuple completion allowance. Promote nothing without tests,
   independent checking and a measured improvement.
6. Continue with the coordinator/Lane I integration and Lane D's authoritative
   paired/gate workflow. Until that completes, report conditional and
   iteration results as such.

---

# Lane E — guarded inclusion integration

**Lane D evidence blocker accepted:** the prior 84/87 vs 83/87 and
1,073-pass / 18-skip numbers are iteration observations only, not independently
established exact-source suite evidence. The shard parser does not establish
roster, uniqueness, source identity or terminal completeness, and six shard
receipts are absent from the committed tree. Hashes do not repair those gaps.
The stronger completeness interpretation of those historical claims is
withdrawn. No more lane-local gate tooling will be built; acceptance goes
through Lane D’s final gate. Audit:
`gdp-wired-verifyP/research/verify-all/final-audit-P80.md`.

## Production premise derivation — `2047d2be`

The ordinary empty-support path did not use the supported grammar pool, so
its initial ten candidates contained no useful carried-set inclusion. The
new production path proposes declaration-backed member witnesses, instantiates
the actual quantified flag bodies, and requests generated primitive field
laws at the scalar guard's keys. No guard or flag body is asserted. Stable
fresh names survive rebuilding; the existing kernel checks the full result.
No protocol names, packing widths, trusted facts, or proof limits changed.

On the latest captured Lane A **34-law** family (no supplied `p1`), assuming
the generated helpers first, the conditional safety probe now returns a
certificate with **both START and STEP checked**. It takes **3817.24253 counted
units** under the unchanged 6000-unit diagnostic limit. The corresponding
2700-unit probe remains UNKNOWN. Recorded whole-probe wall time is 9.625 s;
this is not a strict-60-second original-harness result or a per-helper wall win.
The unmodified integrated baseline was UNKNOWN at 6001.055494 units.

An earlier iteration returned a tree that passed the arithmetic tree checker
but failed `checkMC`: three count-read coordinates depended on the very member
witnesses that justify them. The kernel rejected it. The repaired ordinary and
cached MBQI paths apply the existing count-instance independence filter.
The rejected packet and logs remain preserved; it is not counted as a proof.

Diagnostics:
- `runs/mldr-incl-production-premises-baseline-v1/`
- `runs/mldr-incl-production-premises-{v1,debug-v1,v2}/`
- `runs/mldr-incl-production-checked-input/`: verified archive
  `bc13d4b9c0124e23412a6093affe48bb91062102c44ae675cecd6f72910a0327`
- 53 focused tests / 195 assertions passed in v2. That batch still failed
  type-check on a missing test-declaration `j` and an experiment tuple type;
  both are fixed, with the final check rerun pending at this checkpoint.
- Early count completion is a **research-only** experiment, not production;
  its 2700-unit probe was also UNKNOWN.

Next: pull landed A/B/F, rerun checks and the real original harness x3.
Only Lane D's authoritative gate can establish suite acceptance.

Lane A `fdabeba4` is imported as its new commit only: its older changes were
already integrated with local/Fable repairs. Tiny-instance proposals remain
disabled in production, as upstream specifies. The attempted whole-branch
merge was aborted before commit to avoid overwriting those prior repairs.

Lane F `682c8dc6` is merged: independent empty-count source cores and its
initial-range integration remain intact alongside E member witnesses. Its
research-only counterexample notes are retained upstream; no stronger frame
claim is imported. See `git show 682c8dc6:runs/REPORT.md`.

The pre-merge E source passed type/lint and all 53 focused tests in
`runs/mldr-incl-production-premises-check-v3/`. Early completion at 6000
remained UNKNOWN and was **not adopted**.

## Upstream merge after the conditional checkpoint

Imported Lane B `6d69e094`, including Fable initial range instances. Both
conflicting count-selection hunks preserve the E member proposals **and** B
range instances outside the lazy selector cap. The report conflict retains
this lane history; upstream results are readable at
`git show 6d69e094:runs/REPORT.md` and are not relabeled as E validation.

## Production-premise continuation

Pulled Lane B `568fc570` into this branch, including its existing Lane A
audit/finite-generation repairs and Lane F row-policy integration. Core
conflicts merged automatically; this report preserves the Lane E history.
Upstream reports remain available with `git show 568fc570:runs/REPORT.md`.
Those upstream diagnostic claims are not transferred to this branch.
The new task is to derive and instantiate member-inclusion premises in
production, without saved proof assumptions, protocol names or packing widths.

Branch: `claude/mldr-incl`. **NOT GATE GREEN; full gate pending; no merge claim.**

The audit code repair is committed as **`3f976cba`**, with archive-preflight
ordering corrected in **`8d275256`**. On boat, `mldr-incl-audit-check-v2` passed
type/lint and **31 tests**, including the exact duplicate-protocol regression.
`mldr-incl-audit-source-smoke/results-v2` passed both a real two-revision pair
and a tampered-candidate archive rejected before either proof. The first
tamper smoke failed and is retained; neither it nor the corrected smoke is a
full merge gate. **All v1 pass flags remain withdrawn.**

Lane D rejected the v1 paired-gate analyzer: counts alone did not enforce the
exact roster, pair identity could change between sides, and the candidate SHA
was not bound. All v1 `pass:true` / component-pass claims are **withdrawn**.
Raw logs are retained only as diagnostic observations. The replacement enforces
the independent exact roster and both source archives; acceptance will use
Lane D's one-command final gate.

Production commits: **`f6ec83db`** (ordinary preference), **`7dc52140`**
(raw lazy-pool admission and shared-cap correction), and **`0ee27c7a`**
(member upper-bound selection). No kernel rule, trusted
fact, protocol-name branch, or proof-budget increase was added.

## Implementation

The generic member matcher reaches `rawBuild` through `grammarPool`. Entries
use existing semantic deduplication, fresh witnesses, the pool cap and proposal
meter. Initial preference shares the ten-slot bound with picks. A scalar
residue is never asserted: each entry is the ordinary count-witness
disjunction, and source branches and final certificates pass the unchanged
kernel. Tests cover immutable inputs, exact-witness reuse, full-cap refusal,
missing flags, a checked generic conditional proof, and rejection of its
unguarded strengthening.

## Iteration receipts — not acceptance evidence

* `runs/mldr-incl-check-v8/`: type/lint and all four focused files passed:
  **89 tests, zero failures**. This supersedes the earlier cap-expectation
  failures; their logs remain retained.
* `runs/mldr-incl-shards-v1/`: all seven full-suite shards passed on boat:
  **1,073 tests passed, 18 skipped, zero failures**, with one pinned large VM per
  shard and zero starts charged to the batch.
* `runs/mldr-incl-gates-v1/`: historical diagnostic logs report IC3Syn 84 vs
  83, DuoAI 10 vs 10, and zero broken proofs. **These are not accepted gate
  evidence** because v1 did not bind the exact roster/pair identity/both SHAs.
* `runs/mldr-incl-baseline-v1/`: three unchanged original MLDR trials remained
  UNKNOWN at strict 60 seconds (job times 59.59, 59.61, 59.57 seconds).

The repaired exact-source diagnostic for **`0ee27c7a` vs `b788e195`** has
completed IC3Syn: **84/87 candidate vs 83/87 base**, no lost proofs, no false
proofs, and no lost refutations. All 87 protocol/repeat pairs and both archive
bindings validated. The one gained case is `consensus_forall-r1`; no causal
speedup is claimed. DuoAI is now also validated: **10/10 on both sides**,
with no lost proofs or source/identity errors. Broken variants also validate:
**0/29 proven on both sides**, with no lost refutations. All **126 paired
cases** pass the repaired diagnostic audit, including both source bindings.
This is a complete local diagnostic, **not Lane D final-gate acceptance**; only
that final gate can authorize merge.

These are not the full paired merge gate.

The new-selector seven-shard processes also all exited zero in
`runs/mldr-incl-upper-shards-v1`. Its service log truncates the first shard-7
summary (164 tests), so the visible aggregate is only 909 pass / 18 skip.
The rerun retained the complete 368,228-byte stream, but its first wrapper
incorrectly rejected singular `1 file.` summaries. The repaired parser
independently verifies its hash and all five summaries: **227 pass, 0 fail**.
Combined with shards 1–6, the new-selector suite is **1,073 pass, 18 skip,
0 fail**. The failed wrapper remains preserved; no tests were regenerated
to recover it. `mldr-incl-evidence-check-v1` also passes type/lint and
**38 focused tests**, including three receipt-parser regressions.

## Conditional safety: the failure is now localized

The first 24-job matrix lost its client during scheduler recovery, but its
completed logs were recovered from the exact owned admission before closing
that admission. No other client's batch or VM was touched. The frozen
baseline safety archive has **39 files, zero omissions**, SHA-256
`b96c779fda332e17778af88d76e69a8682b98de04739c1e07e6d3d4b154c0f0c`.
It is retained as `research/mldr-incl/fixtures/safety-gp1.br`.

At the 2,700-unit share with Gp1 (generated laws plus a supplied p1 hypothesis):

| Configuration | Result | Checked proof | Counted units | Instrumented wall |
|---|---|---|---:|---:|
| Baseline | SAT / not proved | no | 1,868.570 | 1,887.404 ms |
| Lane B completion only | SAT / not proved | no | 1,868.570 | 3,335.020 ms |
| Completion + Lane E pool | SAT / not proved | no | 1,868.570 | 2,623.211 ms |

These are one-law diagnostics, not proofs of the whole family, not original
harness passes, and not a fair uninstrumented wall-time comparison.
Completion is Lane B's `60b8c37a`, applied only in isolated experimental jobs.

**Observed blockers:** before the first numeric query, the shared proposal
meter has already consumed all **65,536** steps. The selected certificate has
only five reads. In the final raw STEP goal, quantified count laws already
supply packed quorum-count reads, but the selected certificate still has five
reads. The trace does **not** expose the full proposal pool: it cannot alone
distinguish failed pool population from failure to refresh the initial
selection. Separate full-pool/selected-certificate diagnostics and controls
test those hypotheses. The stage-0 and stage-26 packets preserve the direct
observations, including phase/work counters.

The first frozen matrices are complete and independently checked for receipt,
input-hash and mode/budget identity: **108 Gp1 jobs plus 36 actual E-14 jobs**.
No job produced a checked proof. Each cell below is SAT / UNKNOWN; all proof
counts are zero.

| Input | Raw | Preferred selection | Own-key completion | Completion + flags |
|---|---:|---:|---:|---:|
| Gp1, 27 jobs/mode | 9 / 18 | 9 / 18 | 2 / 25 | 0 / 27 |
| Actual E-14, 9 jobs/mode | 4 / 5 | 5 / 4 | 0 / 9 | 0 / 9 |

Receipts: `runs/mldr-incl-step-v1/analysis.json` and
`runs/mldr-incl-e14-step-v1/analysis.json`. Preferred rebuilds a small
selection rather than preserving all raw instances, so the additional E-14
SAT result is disclosed, not hidden. These are conditional packet experiments,
not original-harness verdicts or a completed proof improvement.

The supported-path scheduling controls proved ineffective: the actual E-14
capture has an empty production support set. Completed ordinary/reserve
controls both returned UNKNOWN at 2,700.734 units; the remaining redundant
controls were stopped and their exact admissions closed. Their partial
receipts are retained under `runs/mldr-incl-recovered/`.

The upper-bound selector in **`0ee27c7a`** passed type/lint and **35 tests**
on boat (`mldr-incl-upper-bound-check-v1`). Scalar guards remain provenance,
not asserted facts. Both new replay matrices completed with exact identity and
input-hash validation: their SAT/UNKNOWN counts are **unchanged from the table
above**, and again no checked proof was produced.

The new diagnostics verify selection of the intended **S-to-full-quorum**
instance, not merely its presence in the pool:

| Input | Preferred | Keyed | Keyed + flags |
|---|---:|---:|---:|
| Gp1 | 24/27 packets | 27/27 | 27/27 |
| Actual E-14 | 6/9 packets | 9/9 | 9/9 |

Evidence: `mldr-incl-gp1-upper-v1/analysis.json` and
`mldr-incl-e14-upper-v1/analysis.json`. Thus the voter inclusion is now selected,
but selection alone did **not** remove the proof-cost or instance gap. The
first six standalone pointwise controls all returned **SAT**, including
stronger and tighter guards: **no checked pointwise proof**. Their reduced
contexts omit original scalar/key-domain premises, so this is not a
falsification of the complete safety implication. A new control adds only
scalar conjuncts extracted from the original raw goal, with a missing-guard
negative, now produces a **checked conditional proof in 39.78 counted units**
using the tighter `CT[i] < CfgT[b]` guard. The original stronger guard also
checks (39.79 units). Omitting the guard remains numerically SAT (35.64
units); this is a missing-guard control, not a certified finite counterexample
or, by itself, a satisfiability check of the guarded premises. Both certificates
are now saved and
accepted by fresh kernel processes. The hardened V2 exporter uses unique
output files; producer, verifier, frozen-input and certificate hashes all
match. See `runs/mldr-incl-pointwise-certificates-v2/index.json`. This is
**not a safety proof** and does not establish the explicit flag premises.

The follow-up independently checks **five-premise** versions of both lemmas,
down from twenty premises. Only `size <= 64`, `b < size`, the scalar guard,
and the instantiated `canVote` / `all$2` flag bodies remain. Declarations,
count reads, witness instances and the conclusion are unchanged. The full
greedy reductions cost 572.91 / 572.77 units; these are **not** single-proof
measurements or an original-harness speedup. Both missing-guard negatives
remain numerically SAT. Fresh controls also find both original guarded
numeric contexts SAT; because reduction only removes premises and keeps the
guard, the reduced contexts are satisfiable too. These are not certified
finite-state models. The initial reduction run failed before proof because
`runs/` was omitted from the source snapshot; the retry explicitly mounted
the committed inputs. Both logs are retained. Details and exact assumptions:
`research/mldr-incl/CONDITIONAL-LEMMA.md`; certificates:
`runs/mldr-incl-pointwise-minimized/`. The final follow-up check passes
type/lint, all three receipt-parser tests, and four extractor controls: the
valid frozen receipt is accepted; forged conclusions, premise order and
parent hashes are rejected even with forged success labels. The execution
plan is preserved in `mldr-incl-final-check-v1/executed-jobs.json` and as
`research/mldr-incl/conditional-final-check-jobs.json`; the older unrelated
`final-check-jobs.json` was restored unchanged. All owned batches are terminal.

The isolated original-harness A/A+E v1 probe failed all three jobs **in patch
setup**, before any protocol verdict. Lane A changed an import
(`attemptShare`), invalidating the patch context. V2 changes only that context,
passes an exact archive patch check, and completed. The pinned Lane A source
is `48533517bf7b6ef1bee47e58d2a9a517babd5488`. These composite probes are not
a full merge gate. V2 completed all three pairs: **UNKNOWN on both sides in
every pair**, at approximately 59 seconds per side. A separate instrumented
A+E capture has 34 initial-family laws and 144 retained / 405 omitted files;
all retained ordinary-attempt stages are pass 0, with no prioritized safety
stage observed. The original-harness improvement is therefore still absent.
The capture hash is
`5926107dd7548316d2c531c7822bb440bf44e17cef3d59bf5340042f92655069`.

## For Lane B / Lane D

**Lane B:** `0ee27c7a` supplies the ordinary inclusion and bounded selection;
`research/mldr-incl/CONDITIONAL-LEMMA.md` now describes its five-premise,
freshly checked conditional certificate. `all$1` and the extra actor/key/flag
bounds are unnecessary for that lemma; the `canVote` and `all$2` bodies and
two domain premises still matter. This is a smaller conditional obligation,
not a transported proof for arbitrary declarations or a claim that its
premises hold outside the appropriate branch.

**Lane D:** the full exact-roster local diagnostics for `0ee27c7a` against
`b788e195` are retained and pass, including source bindings, no lost proofs
or refutations, and no false proof. Seven shards and type/lint pass. Please
use the authoritative one-command final gate before any merge; no local
receipt here, including the conditional certificates, grants GATE GREEN.

## Real E-14 input

`runs/mldr-incl-e14-generation-v2/` completed on boat from Lane A `1681e8e5`:
**35 generated laws, zero proof queries**, generation wall 23,359.980 ms.
No hand law was added. The result includes the count-cube p1/TypeOK forms.
The exact generation archive is `research/mldr-incl/fixtures/e14-generated.br`,
SHA-256 `4b97fb96467ee51e9b80ff0a13b33f00d2731452fd93e6191f65c17c8882d64a`.
The subsequent conditional safety archive is `fixtures/e14-safety.br`, SHA-256
`b9c7abfae8b30ed2c9de6a665aeebc2956599b8ec28fa3d5a97707719e8f3134`: **31 retained
files and 22 omitted files**. Three complete retained early/middle/late packets
were sampled; omitted packets were not reconstructed.

## Infrastructure and remaining work

The earlier recovery/quarantine window invalidated incomplete client receipts;
retries and recovered raw receipts are identified separately. The two-job v3
conditional client subsequently hit its outer queue-wait timeout. Its two
completed payloads were later recovered from the exact owned admission: base
and preferred both remain SAT at 1,868.570 counted units (instrumented walls
2,012.967 and 2,505.420 ms). They are diagnostic payloads, not a successful
client/gate receipt. Actual proof limits were not extended.

The documented generic `queue add` accepted the 108-job backlog, but this
repository's custom treadmill only consumes idea-tagged entries. Its exact
owned, still-queued entry was marked withdrawn (receipt retained), and the
same jobs were submitted once through `supercomputer run --class submission`.
No scheduler resource policy, ownership guard or other submission was changed.

Section **16.6** is now the active instruction: use the actual frozen 35-law
family for conditional safety until Lane A 16.1/16.2 lets the original harness
reach safety, then replace this measurement with the real attempt.

Remaining: turn the conditional lemma into an actual safety-cost improvement
and obtain Lane D’s exact-source final gate, including its authoritative bar.
The repaired 29×3 / DuoAI / broken diagnostics, seven shards and final local
type/lint are complete; none substitutes for that final gate. The bounded premise-reduction experiment is complete and independently
checked; it is research, not a production change. Lane B can use the smaller
conditional obligation without treating its flag assumptions as facts.
Lane D still owns the authoritative final acceptance of production
`0ee27c7a`; this report does not authorize a merge. No complete MLDR proof, integrated sub-60-second result,
merge, or push is claimed.
