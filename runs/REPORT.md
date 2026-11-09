# RESUMED — 2026-11-10

User explicitly resumed lane A. Checkpoint `bef4020f` is clean; the frozen
`runs/t16-frontier-capture/0.json` digest remains
`96ba906a86c7f54db1371cea2c55c0bbcc79fd9e8ebe368b770f6495a9ee4496`.
All six cancelled probes were resubmitted **first**, unchanged, via:

```sh
supercomputer run --jobs research/track-gen/t16-domain-hybrid-jobs.json \
  --out runs/t16-domain-hybrid-resume --class submission --timing \
  --vm-type large --data runs/t16-frontier-capture:tiny-data
```

Batch `20261110-000752-9cbvob`, snapshot tree `99439867caf3`, task
`1b2d3e1d-c456-438d-aa13-75af84ec879c`. The rerun has completed; measurements
below refer to its new payloads, never to the cancelled batch. All twelve
checkpoint/shortcut logs were independently replayed. Production tiny
screening stays disabled: only three of the named seven were caught.
Bounded grouping reached four named drops, not five. The current experiment
is an opt-in operation/request-first traversal; its validation is pending.

## Current pilot: opt-in operation-first traversal (WIP; not yet validated)

After the certified four-of-seven result below, the generic next experiment
closes relevant requests per operation before assigning states. Its
partial enablement predicate now sees the full request/state assignment
order; the separate shared pre-family predicate is checked only after the
request prefix is complete. An unknown state atom stays unknown, never
false merely because its slot still contains an old value.

- `operationFirst` is opt-in; the default state-first path is unchanged.
- The research driver sets it only with `T16_OPERATION_FIRST=1` and records
  the mode in its result; the scope also records the mode.
- Added exhaustive concrete-proposal-set equality and accepted-target tests.
- Independent CTI admission, domains, native-body cap, 1900-ms outer pilot
  wall and production-disabled status are unchanged.
- Equal complete finite proposal sets would not guarantee equal prefixes:
  sequential operations may starve later operations under the wall. The
  six actual probes, not the small fixture, decide the five-of-seven bar.

The first validation batch `20261110-013903-jm3fgc` returned 41 pass /
1 fail: the new fixture inherited count binder `a` while declaring state
`a`, so the source interpreter rejected its scope before the new search
ran. Typecheck/lint were not reached. The fixture now uses binder `row`;
only this test file changed. Corrected validation task
`90db37a7-3f2d-4239-8f19-f5f52b23614b` uses a separate one-file overlay
(test SHA-256 `270c15ac8a857813e72fda8a27600974c9b493048e70012a79d54fa775be7e9d`).
The compiler/driver and the already-submitted probes are untouched; no
probes were repeated. Failure log retained as
`runs/t16-operation-check/operation-first-check.log.gz`.

Work on boat (small overlays, no new archive):

| Work | Task | Output |
| --- | --- | --- |
| Corrected tests/type/lint | `90db37a7-3f2d-4239-8f19-f5f52b23614b` | `runs/t16-operation-fixture-check/` |
| Six probes | `9f01547d-1cc2-40a0-9111-689886bb9c86` | `runs/t16-operation-probe/` |

Overlay `runs/t16-operation-overlay/` uses canonical source archive
`6288b666`, compiler SHA-256
`779cd5b0953697a33f1a3b6e016bd34958e55e0606a9b8bea9636fc4ad165da4`,
test `d8b4af69d189ced49b54ea595da6c241f5236874a574c35dd75693168bcd4d2f`,
and driver `e59a1a84281ff57a31d71062483a14b6edc7d56068ed2bbc0c902fbf25739fe1`.
These WIP files are **not** covered by the earlier 40-test receipt. No new
performance, proof or gate success is claimed; no subagents are running.

## Resumed hybrid probes: independently replayed, criterion fails

Both six-probe batches are complete, every job exited 0, and independent
replay batch `20261110-010325-urerjg` passes for **all twelve logs**. The
replayer checks the complete beginning-of-round family, all declarations,
the source interpreter's enabled step and the target post-law. Compact
records: `research/track-gen/t16-hybrid-resume-results.json`; compressed
input logs total 64 KB under `runs/t16-replay-input/`.

| Source | Original-40 active walls (ms) | Total drops | New named-seven drops |
| --- | --- | --- | --- |
| Checkpoint `bef4020f`, batch `20261110-000752-9cbvob` | 1900.324 / 1900.814 / 1900.212 | 5 / 4 / 5 | **3 / 3 / 3** |
| Unready-atom shortcut, `19ad4ab4`, batch `20261110-003852-llmvg6` | 1900.401 / 1900.409 / 1900.419 | 5 / 4 / 4 | **3 / 3 / 3** |

The three named drops are the unweakened stored guard, disabled/1 and the CV
bound. The row-0 cube and CT/CV row agreement are **not** named-seven credit.
Every survivor-34 run drops only the first two (two new named drops, three
including its independently replayed historical CV removal). All twelve
active walls are below 2 s; every search is wall-limited, not a completed
semantic search. Process durations and scheduler wait are not algorithm wall.

**Falsifier: fewer than five of the named seven. Production stays disabled.**
The shortcut has no demonstrated removal gain; the different CPU placements
are not a paired speed comparison. No strict original-harness/full gate is
scheduled for this unsuccessful screen. No safety proof or GATE GREEN.

### Bounded native grouping: independently replayed, four of seven — not sufficient

Batch `20261110-010410-4rvkxj`, snapshot `777d8975d129`, has now passed
**40 tests / 150 assertions**, full TypeScript and type-aware lint (zero
warnings/errors), and `T16-GROUP-COMMIT.txt` commitlint. The actual job exit
is 0, 32.05 s, on exclusive large Ryzen 7 9700X, 8/8 vCPUs. The new
4,096-clause cap-splitting regression passes. Log:
`runs/t16-group-check/bounded-group-check.log.gz`.

This validates the implementation, not its removal rate or active wall.
The first six probes all exited 1 before producing `HYBRID_RESULT`: the
job changed into its extracted source but had mounted `tiny-data/0.json`
only at the outer sandbox root. This is an input-path setup failure, not a
compiler/removal/wall result. All six error logs were inspected and gzip
copies retained. The completed failing batch is `20261110-010407-6qnghm`.

The corrected batch `20261110-012637-jlj653` exited 0 for all six jobs.
Independent replay `20261110-013708-5enz4s` also passed for all six logs.
Original-family active walls: **1966.647 / 1901.227 / 1900.141 ms**. Each
original run removes six laws total, but only **four of the named seven**:
CV bound, unweakened stored guard, disabled/1 and no-quorum canVote/1.
All survivor-34 runs newly remove the last three; the historical CV drop
makes four including history. Their active walls are 1900.323 / 1902.648 /
1900.260 ms. Compact evidence: `research/track-gen/t16-group-results.json`.

**The five-of-seven bar still fails.** No production promotion, final gate,
semantic-exhaustion or safety-proof claim. No compiler code, budget, domain,
or archive changed for this retry; the passing suite was not repeated.

Individual native predicate calls may be replacing arithmetic work with call
overhead. `core/finite-tiny.ts` now tries shared-DAG logical groups within the
**same 64-KiB native-body cap**, splitting oversized groups recursively and
checking cancellation between them. Atomic early guards remain. No search
domain, wall, proof fuel, law or production switch changes. A 4,096-clause
regression exercises cap-driven splitting, alongside the exhaustive small
polarity/request tests. This now has a repeatable removal improvement over
the earlier variants (four rather than three named drops), but not a pass.
Different CPU placements preclude a paired speedup claim.

- Tests/type/lint: completed; checked implementation committed as `27ff24fc`.
- First six probes: failed before the experiment; batch
  `20261110-010407-6qnghm`, output `runs/t16-group-probe/`.
- Corrected six-probe retry: task `3a9c3826-7966-4737-83cc-593822d37f22`,
  output `runs/t16-group-probe-retry/`.
- Both reuse canonical archive `6288b666` with the small immutable overlay
  `runs/t16-group-overlay/`; no new tree archive or clone. Compiler SHA-256
  `2802f3dd4e4d53cc3382457db302f2ee7c1abcef5b394529ccf367f070d2a2a2`.

For lane I/Fable: do not enable or promote the tiny backend from these
receipts. All submitted probes and their replay have completed. Disabled/0,
/2 and /3 remain. The bounded-group change is checked but does not meet the
five-of-seven bar.

Next generic hypothesis: state-first enumeration waits until a full state
before testing any operation's enablement. An opt-in operation/request-first
search can close dispatch and request coordinates, then apply the same
partial-assignment pre-family AND enablement screen during state assignment.
It must preserve the complete proposal set on small finite fixtures, retain
the independent checker, and meet the unchanged wall/five-of-seven bar.
No name matching, new assumptions, domain expansion or timing-cap tuning.

## Prior unready-atom validation — green unit/type/lint only

The unready-atom shortcut and repaired regression fixtures pass **39 tests /
145 assertions**, TypeScript, type-aware lint (zero warnings/errors), and both
archived commit-message checks. Per-job exit is **0** in batch
`20261110-005234-oyxenp` (`archive-domain-check-overlay`, 52.44 s), exclusive
large EPYC 4585PX, 8/8 vCPUs. This is **iteration validation only**, not a
final gate, performance result, or proof.

The measured source is archive `6288b666` (hash recorded below) plus exactly
the test overlay SHA
`5f4e224572a29bbd932a2fb9a170e3265aa801b760e74ea1e7234ae2ab3ff63c`.
Only that fixture differs from the archived core files; the algorithm and
independent checker are unchanged. Compact source/hardware/failure evidence:
`research/track-gen/t16-partial-validation.json`. Compressed raw receipt:
`runs/t16-partial-overlay-check/archive-domain-check-overlay.log.gz`.
Earlier failed logs are also retained and gzip copies made; originals were
not deleted.

Both six-probe batches remain registered, so neither is rerun. The latest
scheduler read showed six queued / zero running for each; its class census
had 657 gate and 399 submission items queued, with 55 gate VMs and two
submission VMs. No scheduler policy or priority was changed to bypass that
queue. The five-of-seven / <=2 s criterion remains **unmeasured** for the
shortcut. Production remains disabled. After actual probe completion, replay
the CTIs with the full beginning-of-round family and source interpreter;
only then decide the next experiment.

## First executed validation — historical fixture failure

Batch `20261110-003848-r92jez`, tree `e258b9207ea3`, completed its one job
with **exit 1** (the outer client exited 0). `domain-check` ran on exclusive
large Ryzen 9 9950X, 8/8 vCPUs, in 0.88 s: **38 pass, 1 fail, 127 assertions**.
The new predecessor-equivalence fixture inherited count binder `a` and also
introduced state scalar `a`; the interpreter correctly rejected the name
collision before the test could run. Typecheck/lint were not reached.

The fixture now uses count binder `row`, with no production-code change, and
its conditional case tests a nontrivial equality rather than a tautological
bound. The original failure is retained in
`runs/t16-partial-immutable-check/domain-check.log`. Next validation will
use one canonical archive per SHA, reused by hard-linked data mounts, not
another whole-tree clone. Payload estimate is about 142 MiB including both
vendors, below the 500-MB disclosure threshold. This is not a proof or gate.

## Archive validation: tests pass, fixture lint correction pending

Batch `20261110-005009-p6jio6` verified all three archive digests and ran on
exclusive large EPYC 4585PX, 8/8 vCPUs. Its job exited **1** after 69.46 s
(the launcher exited 0): **39 tests pass, 145 assertions**, and TypeScript
passes, but type-aware lint reports four errors at the one new request-pair
formatting line. `Request` values include maps and `undefined`; the test
must explicitly narrow both coordinates to numbers. Commitlint was not
reached. This is not a green validation or a proof.

The correction adds an explicit numeric type guard in the fixture only.
To avoid another whole-tree archive, pending validation reuses the exact
`6288b666` source archive and overlays only `core/finite-tiny.test.ts`, whose
SHA-256 is `5f4e224572a29bbd932a2fb9a170e3265aa801b760e74ea1e7234ae2ab3ff63c`.
The job verifies that hash before replacing the archived test file, and
then repeats tests, full type/lint and both commit-message checks.

Task: `3948f73d-2ef4-4d60-b940-94edeae2b5fb`; manifest:
`runs/t16-partial-overlay-check-jobs.json`; output:
`runs/t16-partial-overlay-check/`; immutable small input:
`runs/t16-fixture-overlay/core/finite-tiny.test.ts`. No proof-engine file
changed and no new tree archive was written for this iteration.

## Fixture-repair validation and offload retention

Repair commit: `6288b666e7b23cb4a10e0e9e92cde919ea135854`. One canonical
archive was created at `/private/tmp/gdp-archives/<that-sha>.tar` (121,344,000
bytes). SHA-256:
`26824362de21cb4ea3c87e78f09aa37dc49077b88ab8a6bb1421dd3eeb311979`.
Existing exact vendor archives are reused, not rebuilt. The data mount at
`/private/tmp/gdp-archives/mount/<that-sha>/` contains **hard links**, not
additional archive copies. No write over 500 MB occurred.

Validation task `617d5ea0-36b4-49a7-bc1b-3d25d275a3f4`, output
`runs/t16-partial-archive-check/`, extracts that source on boat, verifies
all three archive hashes, runs the required three test files, full type/lint,
and commitlint for both the shortcut and fixture repair. It uses the existing
immutable `current` clone only as a stable launcher envelope. No new clone
was made. The optimized probes are not duplicated: the fixture-only change
does not change their measured algorithm.

In response to the offload notice, `runs/KEEP-LOCAL.txt` now names the frozen
input. `/private/tmp/gdp-archives/KEEP-LOCAL.txt` preserves its existing
entries and adds the active source/vendor archives and their mount hard-link
paths. No source file in the active clone is over 20 MB. Previously listed
unused clones remain cleanup candidates; no file was deleted. Results are
still pending for this repair.

## Execution reopened — immutable retries

The coordinator lifted the submission hold after the blob lock freed, while
retaining the at-most-one-subagent cap (this lane has none). Before any retry,
`supercomputer scheduler status` and all four output directories were checked:
`20261110-000752-9cbvob` is still registered with six left / zero running;
the three failed later batches are absent, and their output directories are
empty. The original batch was **not** resubmitted or killed.

A new, unchanged local clone at `/tmp/gdp-lane-a-frozen.uLpIQc/current`
is pinned to `19ad4ab4e378644d325d44b9e47c29d5c9d64129`, with exact vendor
gitlinks and the frozen data copy. Two retries only are now submitted:

- Required `t16-domain-check-jobs.json`, output
  `runs/t16-partial-immutable-check/`, task
  `a459f935-d7a4-4171-99da-0782e564d87b`, batch `20261110-003848-r92jez`,
  tree `e258b9207ea3`.
- Six optimized hybrid probes, output
  `runs/t16-partial-immutable-hybrid/`, task
  `828beead-707f-4141-b7d5-2bc133919cd7`, batch `20261110-003852-llmvg6`,
  tree `8d49b8211662`.

Both use `supercomputer --repo /tmp/gdp-lane-a-frozen.uLpIQc/current`,
`--timing --vm-type large`, normal scheduler classes (gate / submission),
no forced VM count. The required check includes the complete current source,
so it supersedes a separate retry of the failed final-source check; there is
no duplicate test batch. The bounded completion observation expired with
all three clients still active, not with a test/probe failure. Their own
completion notifications remain enabled; no additional polling or duplicate
submission is needed. Do not edit the clone while it uploads or runs.
No gate or proof claim.

## Disk

Coordinator disk rules are in force. No files are being deleted. No further
whole-tree clone/archive per run will be made. Future archive-based work must
reuse `/private/tmp/gdp-archives/<sha>.tar`, creating it only if missing, and
pass it with `--data`; no tree tar goes in output/input directories. Retrieve
compact summaries/receipts/hashes; request raw logs only for a specific
question and gzip them. No write over 500 MB is planned; such a write would
be reported here first.

Measured lane-owned scratch (created before the disk notice):

| Path | Size | Suggested disposition and why |
| --- | ---: | --- |
| `/tmp/gdp-lane-a-frozen.uLpIQc/checkpoint` | 160 MB | Coordinator may delete: never submitted; exact source `bef4020f` remains in Git. The registered original batch uses the original worktree, not this clone. |
| `/tmp/gdp-lane-a-frozen.uLpIQc/wip` | 160 MB | Coordinator may delete: never submitted; superseded by the current clone and source `32772de6` remains in Git. |
| `/tmp/gdp-lane-a-frozen.uLpIQc/current` | 160 MB | **Keep until the two immutable submissions terminate**; deferred upload reads this source. Then a cleanup candidate because `19ad4ab4` remains in Git. |
| `/tmp/gdp-lane-a-frozen.uLpIQc/data` | 68 KB | Keep while the optimized probe submission can read it; frozen input is separately preserved in this worktree. |

Only the first two paths (about 320 MB total) are immediate cleanup
candidates. Nothing was deleted, and no current upload source was changed.

## Historical execution hold — coordinator memory notice

The coordinator reported laptop memory pressure and a blocked shared
`blob-cache.lock`, and directed all lanes **not to resubmit or kill submitted
boat runs until further notice**, with at most one subagent. This lane has no
subagents. No new jobs were submitted after that notice; the original
cancelled-probe rerun remains owned by its existing client.

Three later clients have terminated with a **pre-execution snapshot error**,
`ValueError: blob bytes do not match their key` from `push_tree` /
`store_blobs` / `blobcache.put`:

- `a434a908-dd22-4bb7-b955-130b396ec578` / `20261110-001417-gd15iy`:
  required domain check, exit 1 after 1,144 s, no result files.
- `1c1edd9f-b30c-458a-93e3-7d4d17d66a28` / `20261110-001508-ez9go1`:
  optimized six-probe experiment, exit 1 after 1,151 s.
- `7c638a8f-675f-42da-80ca-337c34e13594` / `20261110-001813-riu69e`:
  final-source validation, exit 1 after 965 s.

These are **not test failures or timing measurements**. The first domain
check's output directory is empty. Delayed uploads read source files after
tree hashing, so the intervening edits are a plausible cause of the hash
mismatch; memory pressure explains the delay, not a proven hash diagnosis.

Before the coordinator's hold arrived, immutable local clones were prepared
at `/tmp/gdp-lane-a-frozen.uLpIQc/{checkpoint,wip}` (no retries launched):
checkpoint `bef4020f07c42058534515b99a15214fb4ae649a`, WIP
`32772de69e7f5ef9c3b360fbed97b61a32964950`, with both vendor gitlinks checked
out exactly. `/tmp/gdp-lane-a-frozen.uLpIQc/data/0.json` matches the frozen
input SHA above. Leave these clones unchanged. After the hold is lifted,
use them to avoid edit/upload races; do not rerun any completed work or
replace the still-active original client blindly.

The earlier bounded waits have expired; the original shell client's own
completion event remains enabled. No shared process, scheduler, VM, lease,
cache, or policy was changed. No tests or gate have passed for this WIP.

## Follow-up implementation and original submissions (not validated)

`core/finite-tiny.ts` now returns unknown before evaluating an atomic
predicate's closed expression DAG when any dependency is unassigned. The
prior code evaluated guarded intermediate terms even though the atom had to
return unknown. No search domain, law, proof fuel, native-body cap, wall,
or production switch changes. Two finite equivalence regressions cover
ternary predecessor states, both predicate polarities, and conditional
request dependencies in `core/finite-tiny.test.ts`.

- Required domain validation: `20261110-001417-gd15iy`, tree `5f8486bd01ee`,
  task `a434a908-dd22-4bb7-b955-130b396ec578`, output
  `runs/t16-partial-check/`.
- New six-probe experiment: `20261110-001508-ez9go1`, tree `d0ae610ee71f`,
  task `1c1edd9f-b30c-458a-93e3-7d4d17d66a28`, output
  `runs/t16-partial-hybrid/`.
- Final-source type/lint/regression validation, including the new independent
  replay script: task `7c638a8f-675f-42da-80ca-337c34e13594`, output
  `runs/t16-partial-final-check/`, batch `20261110-001813-riu69e`, tree
  `cef78180da95`. Its immutable snapshot still contains the disallowed `perf`
  commit-message type; the working file now uses allowed `refactor`. If this
  job reaches commitlint after passing tests/type/lint, its expected header
  failure is not a code-test failure. Revalidate the corrected message before
  promoting this WIP.
- Replay-only diagnostic: `research/track-gen/t16-hybrid-replay.ts` validates
  every logged CTI against the complete beginning-of-round family,
  declarations and actual source interpreter, separately from the proposer.
  It records the exact seven-law criterion, not total drops. It is **not**
  authoritative census/admission tooling; lane D retains final admission.

At the last read-only scheduler inspection the restart still showed six
queued, zero running. No result payload was available. Shared scheduler
health reported `churn`, `starts`, and `status` breaches; no shared process,
VM, lease, or policy was changed. The running clients remain responsible for
normal scheduling/fallback. There is one bounded completion waiter for the
required restart; no alternate local execution or duplicate restart.

---

# HISTORICAL RESUME — PAUSED AT USER REQUEST

**Start nothing until the user explicitly resumes. No push or merge.**

## Branch and checkpoint

- Branch: `claude/mldr-gen`.
- Last work SHA: **`cd31a2bfaef250c2872f72ab1900846745926e06`**, `chore: wip: checkpoint finite-domain experiments`.
- This RESUME-only commit follows that SHA; the final checkpoint SHA is `HEAD` and is given in the checkpoint reply.
- Finished earlier work: `c21a6e54` (paired-side failure propagation) and `fdabeba4` (binary tiny-instance proposer/checker).
- All pending source, tests, scripts and diagnostic inputs are committed as WIP. The allowed commitlint types exclude `wip`, so the conventional subject is explicitly labelled `wip:`.
- 254 compact collected receipts (about 699 KB) are catalogued in `research/track-gen/CHECKPOINT-RECEIPTS.json`. Large logs, captures and archives stay locally under `runs/`, outside Git. Temporary trace inputs are preserved in `research/track-gen/checkpoint-trace/*.ts.txt`.

## Proven / measured, and limits

- **MLDR safety remains unproved. No GATE GREEN or independently admitted final census.** The audited repair's three strict candidate process walls were 59.08 / 59.16 / 59.10 s, all `unknown`.
- Lane D independently cleared runtime cancellation, declared-fact and import-cycle repairs (`74dd9cc5` / `52b2382f`). The other-28 proof and canonical-list comparisons below remain reported iteration observations, not authoritative admission.
- Paired-exit validation: **11 tests / 33 assertions**, full type/lint and commitlint pass. Exit 137 is simulated in that regression, not an actual timeout kill.
- Binary tiny search: original 40 -> 35 in all three runs, 1.356–1.801 s, but only three newly caught costly helpers. One post-boundary 34 -> 31 run completed; two hit their wall. Finite screening is not a proof or semantic completeness result.
- The ternary probe found additional CV-bound and CfgT-field witnesses, but original-family active walls **2.337–2.922 s violate the 2 s allowance** and are rejected. Completed binary/ternary probes collectively catch **four of the named seven**, not five; the extra CfgT field witness is not one of those seven.
- WIP: optional state-value domains/round caps and smaller checked native predicates, bounded to 64 KiB. **Production remains disabled.** Last collected validation: **37 tests / 117 assertions**, full TypeScript/type-aware lint and commitlint, `runs/t16-domain-chunk-check-v2/`, batch `20261109-154013-z431iv`. No validation jobs were started during checkpointing. New checkpoint headers were checked locally against all configured commitlint rules.

## Cancelled work — exact inventory

Only one owned background task and its corresponding boat batch were active at checkpoint. Other tasks, including worker `01a9d7c596a34bfa8aab78764f248cff`, were already terminal.

| Task / batch / output | Purpose | Cancellation and partial-result status |
| --- | --- | --- |
| Task `49ba03f8-9004-4c26-ad20-6ece1fd110ee`; batch `20261109-153518-o1nkb4`; `runs/t16-domain-hybrid/` | Six bounded two-domain probes: `original-hybrid-{1,2,3}` and `survivors-hybrid-{1,2,3}` | Stopped by exact task ID, confirmed `killed`; exact batch closed via scoped scheduler `/close` and verified absent. Initial observation had six queued/zero running; by the close snapshot all six were remotely done. Scheduler rows/hardware were saved, but no result payloads were collected. Metadata is usable only as execution history, **not** removal or active-wall evidence. **All six must be rerun** after resume. |

Receipt: `runs/checkpoint-cancellation.json`. Its 1.96–2.08 s process durations are not the missing algorithm-wall measurements. No shared scheduler/VM was stopped and no broad PID kill was used. No new batch was started. Final task/batch inventories must be empty before the checkpoint reply.

## Open audit blockers

Lane D's `final-audit-G-side-exit.md` reviewed only through `c21a6e54`:

1. Historical receipts need both actual side statuses revalidated, or reruns with the repaired bound launcher. An old scheduler success can mask a failed side; expected kills are not proofs.
2. The 29-ID/three-repeat roster and command mapping remain mutable rather than independently bound.
3. Archive IDs are caller-labelled; trusted archive/vendor/launcher digests and their binding to each receipt remain absent.
4. Conflicting/duplicate receipts, CPU claims, MLDR list equality and proof preservation are not established by formatter completeness alone.
5. A failed CPU probe inside `printf` command substitution can be masked; a nonempty CPU string is not provenance. This is distinct from repaired side-exit propagation.

No new authoritative gate tooling: the coordinator assigned admission to Lane D. Later WIP tiny-domain code is not covered by that static audit or by earlier 28-protocol measurements.

## Exact next steps — only after explicit user resume

1. Read this handoff, inspect branch/HEAD and read live `supercomputer --skill`. Do not reuse cancelled scheduler rows as CTI/timing results.
2. Rerun into a new output directory:

   ```sh
   supercomputer run --jobs research/track-gen/t16-domain-hybrid-jobs.json \
     --out runs/t16-domain-hybrid-resume --class submission --timing \
     --vm-type large --data runs/t16-frontier-capture:tiny-data
   ```

   Required local input: `runs/t16-frontier-capture/0.json`; its expected SHA-256 is in `research/track-gen/t16-tiny-results.json`. Inspect actual `HYBRID_RESULT`, independently certified CTIs, all six exits, hardware labels and active wall. Count only the named seven; not the extra field witness.
3. If fewer than five of the named seven are caught, or any active wall exceeds 2 s, keep production disabled and report the falsifier. Do not increase proof fuel or add protocol-specific constants.
4. For subsequent code edits rerun `research/track-gen/t16-domain-check-jobs.json` on boat into a new output directory. Retain the already-collected failures and avoid repeating completed work blindly.
5. Only after the fast loop meets its criterion consider integration, three original-harness pairs under the strict 60 s wrapper, and other-28 generation/proof guardrails. Route final provenance/admission to Lane D.

---

# Lane A — runtime audit resolved; paired-exit repair locally validated

Lane D independently resolves the runtime findings at `5e4f4956` / `52b2382f`.
Its `final-audit-G26.md` identifies research-evidence defects. Per the
coordinator's direction, this follow-up is limited to **propagating either
side's failure** and focused tests; no new authoritative gate tooling is
being built. The direct launcher preserves both side records and exits
nonzero if either fails. The immutable-archive wrapper copies this repaired
execution driver before delegating, without modifying the measured engine.

Focused boat validation: **11 tests / 33 assertions pass**, covering both
modes, both side orders, either side failing after output, successful pairs,
and a simulated exit-137 side (not a real timeout kill). TypeScript,
type-aware lint and commitlint also pass.
Receipts: `runs/t16-side-exit/` and `runs/t16-side-exit-lint/`.

The numerical comparisons below remain reported observations, **not
independently admitted complete-census or final-gate evidence**. Admission
claims go through Lane D's final gate. No GATE GREEN is claimed.


**Runtime fix SHAs: `74dd9cc5` plus `52b2382f`.** Lane D has independently
resolved the cancellation, facts and import-cycle findings. The separate
G26 paired-exit repair passes its focused checks; no GATE GREEN is claimed.

- **Cancellation:** the derived-count loop checks the active wall every 256
  iterations and propagates the optional per-attempt stop through the finite
  evaluator and real interpreter step. Interrupted sums are never cached.
  `52b2382f` keeps this check through a dependency-free runtime hook, avoiding
  a proof-engine initialization cycle introduced by the first repair.
- **Declared facts:** CTI certification requires every declared fact to hold,
  in addition to the current family and precondition. Unsupported facts or
  derived sum-state cannot certify a CTI. The finite sampler applies the same
  predecessor constraints and declines unsupported derived sum-state.

Clean-archive verification in `runs/t16-audit-isolated/audit-isolated.log`
binds full commit **`52b2382f916ad9558483c14e255cb90fd0184794`** and archive
SHA-256 `a8e95db82c06d9a475b094f659dffc43ed74f07de3e1a43f297fa68b3c3bb4b2`.
On an isolated AMD Ryzen 9 9950X large VM: **20 tests, 82 assertions, zero
failures; TypeScript, type-aware lint and the three archived audit commit
messages pass.** The job takes 35.12 s (671.1 s batch wall includes scheduler
wait, not proof execution).

The exact 5,000,000-count / 20 ms reproduction was repeated three times with
a wall and three times with only an attempt stop: all stop inside the loop
at **20.03–20.20 ms**. The `p=1` model under a declared `p=0` fact is rejected
as not genuine. Unsupported-fact, derived-state, transition-count and
interrupted-cache regressions also pass.

Post-repair original-harness pairs (`t16-audit-paired/`, immutable `52b2382f`
versus `b788e195`) return **unknown** in all three candidate runs, with
strict process walls **59.08 / 59.16 / 59.10 s**, all exit 0. Baseline repeat
1 is unknown at 20.66 s; repeats 2 and 3 are strict 60 s kills, not proofs.
The current-tree audit plus isolated fallback tests also pass **30 tests /
113 assertions**, full type/lint and all audit commit messages
(`t16-audit-current-check/`); this is not a committed fallback or proof claim.

The first all-protocol generation census was incorrectly serialized inside
three jobs and timed out at 330 s per job. Its replacement is one job per
protocol/repeat (87 paired jobs). The first submission failed locally on a
snapshot blob/hash mismatch before execution; a stable temporary driver
fixture now avoids concurrent source-edit races (`t16-audit-generation-v2/`).
The local formatter reports **87/87 census records**: **all other 28 canonical
candidate lists are byte-identical in all three paired repeats**, with exactly
zero generation queries. MLDR emits the same 34-law canonical list in all
repeats (baseline 27), with candidate generation walls 24.77 / 18.75 / 18.42 s.
The six learning_switch / learning_switch_i4 comparisons initially exceeded
the generation-job timeout. They completed with the unchanged full BFS in
276.5–453.8 s per pair; only job wall was enlarged, not proof budgets or the
strict 60 s wrapper. Source SHAs, canonical hashes, CPU labels and all retry
failures are recorded in `runs/t16-audit-generation-summary.json`.
This completes the generation guardrail for the **audit repair**, not for
subsequent uncommitted tiny-fallback work.

Failures remain recorded: initial repair jobs failed on the import cycle
(`t16-audit-fix-v1/`, `t16-audit-quick/`); the first corrected working-tree
run passed the focused tests but failed lint on two then-uncommitted worker
files (`t16-audit-fixed/`). The worker has addressed them, but that fallback
experiment is separate from the immutable audit receipt. No shared scheduler
or VM was restarted. The local runtime repair is validated and independently cleared by Lane D;
**the full branch still has no admitted final-gate receipt.**

The repaired immutable `52b2382f` versus `b788e195` proof comparison is
complete: **84/84 baseline and 84/84 candidate runs are proven**, with no
candidate kills, no lost proofs and no wrong verdicts
(`t16-audit-others-summary.json`). Counted work moves in 39 pairs across
13 protocols: consensus_epr, consensus_forall, consensus_wo_decide,
majorityset_leader_election, naive_consensus, paxos_epr,
quorum_leader_election, simple, simple_election, simple_regular,
toy_consensus, toy_consensus_epr, toy_consensus_forall. These are audit-repair
iteration results, not evidence for the later uncommitted fallback and
not Lane D's authoritative final gate.

## Richer-domain follow-up: useful witnesses, rejected timing

The binary baseline is preserved at `fdabeba4`. An optional explicit
`[0,1,2]` state-cell domain (Boolean request maps unchanged) passes 36 tests /
115 assertions plus full type/lint, but is **not production-enabled**.

All three original-family probes found six total drops: the binary first-pass
four plus `CV at most 2` and
`fields: St[a]=1 -> CT[a]=CT[b] -> CfgT[b]<=CfgT[a]`. They did not reach the
later canVote/1 removal. The post-boundary probes found three drops each:
stored guard, disabled/1, and the new CfgT field implication. All six searches
hit their wall. Original-family active walls were **2.337–2.922 s**, exceeding
the 2 s allowance; those timings are rejected. Post-boundary walls were
1.901–1.914 s. Raw evidence: `runs/t16-domain/`, batch
`20261109-150826-nqfxx2`. An original-family exit 0 means only its existing
five-total-drop assertion passed, not five costly helpers or a valid timing.

This adds a useful witness but does not satisfy the replacement criterion.
The temporary-copy trace completed: native execution/request-entry gaps of
55–271 ms were observed between cooperative checkpoints. The experimental
compiler now splits predicates into individually checked clauses and caps
native function bodies at 64 KiB. A round-limit option allows a two-domain
research schedule under one 1.9 s search wall; no deadline, counted proof
budget or production switch was changed. **37 tests / 117 assertions**, full
type/lint and commitlint pass (`runs/t16-domain-chunk-check-v2/`). The preceding
check's sole failure was an undefined identifier in the new round-cap fixture;
that fixture is corrected.

At checkpoint, task `49ba03f8-9004-4c26-ad20-6ece1fd110ee` was stopped and its exact boat batch `20261109-153518-o1nkb4` closed. By the cancellation snapshot all six probes were remotely done, but their result payloads were not collected. Only scheduler rows and hardware metadata were preserved in `runs/checkpoint-cancellation.json`; these are not CTI or active-wall results. The implementation is WIP `cd31a2bf`, not promoted. Rerun all six only after explicit user resume.

The named seven-law criterion still matters: the new CfgT field implication
is **not** one of those seven. The union of completed binary/ternary probes
currently covers four of the seven (unweakened overlap, disabled/1, CV bound,
canVote/1), not five. No replacement criterion or GATE GREEN is claimed.

## Experimental binary-domain fallback: prediction not met

The generic tiny-instance proposer and independent `finiteTinyHoudini`
wrapper are implemented, but **not enabled in production generation**.
The source uses structural count grids and shared transition screens; no
protocol/law names are production conditions. Every removal is independently
checked against preconditions, all facts, the complete current family and
the source interpreter's actual step. Caller laws are protected.

On the original 40-law family, all three binary-domain runs remove the same
five laws in 1.356–1.801 s. **Only three are the previously missed costly
helpers**: unweakened stored guard, disabled/1, and canVote/1. The other two
were already caught by boundary sampling. Starting after the six certified
boundary removals, one run reaches a 31-law fixed point in 1.356 s; two runs
are wall-limited. Disabled/0, /2 and /3 remain in the completed 0/1 scope.
Thus the five-costly-helper prediction is **not met**. The next bounded
experiment is a richer value domain; no missing-law or semantic-exhaustion
conclusion is drawn from this untrusted screen.

The scope is exactly 22 state bits at size 3, structurally inferred rows,
Boolean carried sets and binder values 0–2. Completed screening is not a
semantic completeness or proof claim. `research/track-gen/t16-tiny-notes.md`
and `t16-tiny-results.json` preserve exact scope, failed earlier pilots,
input/source hashes, independent witnesses, CPU labels and remaining laws.
The final worker check passes 12 tests / 40 assertions and full type/lint;
the wrapper suite passes 35 tests / 112 assertions and full type/lint.

# Lane A / T-14 iteration receipts complete; Section 16 in progress

The E-14 + per-attempt-sharing implementation (`1681e8e5`) and the test-only
packed-domain clock repair pass the lane-local iteration checks against `b788e195`:
84/84 retained IC3Syn safety proofs, 30/30 DuoAI proofs, no broken variant
proved, all seven test shards and type/lint/commitlint green. The recovered
quick bar has wrong 0 and solid losses 0 (three non-solid CHC losses remain).
The 28 other generation lists are identical x3; MLDR has 35 laws and is still
**unknown**, not 29/29. `T14-GATE.md` records all work deltas and CPU models
for every strict pair. Original logs and failed probes remain in this worktree.

Counted-work changes occurred in: `consensus_epr`, `consensus_forall`,
`consensus_wo_decide`, `distributed_lock`, `learning_switch_i4` (broken),
`majorityset_leader_election`, `mldr`, `naive_consensus`, `paxos_epr`,
`quorum_leader_election`, `ring_leader_election`, `simple`, `simple_election`,
`simple_regular`, `toy_consensus`, `toy_consensus_epr`, `toy_consensus_forall`.
No safety verdict or returned helper law was lost.

Under the revised Gate evidence rule, these lane-local receipts do **not**
authorize a merge. GATE GREEN requires Lane D's one-command final receipt
with both SHAs, exact roster, pair identity, and CPU labels bound. No such
claim is made here.

Section 16.1 first half / 16.2: concrete relative-CTI certification and a
single counted deadline per attempt are implemented. The finite checker
recomputes count cells, checks the entire predecessor family, executes the
actual request, and requires a post-state violation. Only that result skips
the other pass. An uncertified pass-1 model is `unknown`; it does not carry
the new `refuted` marker. The existing failed-proof elimination policy is
otherwise unchanged. The exact end now bounds refinement, decision, part
growth, and final growth; supportBudget remains the caller-priority owner.

Validation: `t16-check-v1` has 23 pass / 0 fail / 2,572 assertions, plus
TypeScript and type-aware lint. `t16-probe-v1` is running three strict paired
repeats against main and three against the clean T-14 parent (`8b44e4b3`).
These changes are NOT covered by the T-14 iteration results or a Lane D
merge receipt. Geometry-biased finite sampling is now under test; Lane C owns 16.4.

First-half measurement (`t16-probe-v1`, six pairs on AMD Ryzen 9 9950X):
all six candidate runs end cleanly at 59.12–59.42 seconds, all `unknown`.
All 214 completed candidate attempts are within 1.011× their declared share
(the actual maximum is 1.010216); no >1.1× attempt. **16.1's prediction is
falsified:** zero completed models certify as genuine relative CTIs; each
fails the whole-family predecessor check. The initial family remains 35,
round 0 never completes, and safety is not reached. The second-half sampler
is therefore necessary. Raw results and all classifications are retained
in `t16-probe-v1/` and `t16-probe-inspect.json`. The inspector initially
included later baseline phases on odd repeats; it was corrected to stop at
the candidate's own end marker before reporting any of these numbers.

The committed first half (`c9d7f823`) is confirmed again in `t16-confirm`:
23 tests / 2,572 assertions, type/lint checks and commitlint all pass. The
new boundary-state tests pass; their first type check found a test-record
annotation missing the `ms` field, now repaired. `t16-frontier-v1` is running
that exact repair plus three bounded-generation repeats. The new sampler
uses only law atoms (guards, one-sided cubes, and exact field bounds), and
its entire pass has a two-second local cap; timeout retains only already
certified drops and cannot extend an earlier outer deadline.

Second-half first probe (`t16-frontier-v1`): three identical 34-law outputs,
zero generation queries. The finite pass removes six laws, including the
five earlier removals and **CV at most 2**, but this is only **one of the
seven** costly survivors. The required tiny-state fallback is therefore in
progress in an isolated new module. This is not reported as success of the
five-law prediction. The first raw local cap finished at 2,000.2–2,001.7 ms;
the implementation now reserves the existing generic wall-completion
headroom (1,900 ms active allowance) and is being remeasured in
`t16-filter-v2` now confirms all six paired filter walls at 1,900.05–1,901.27 ms, zero queries, on an isolated AMD Ryzen 9 9950X. Random-only filtering removes none within that cap; boundary-first filtering removes the same six in all three repeats. Every drop is independently rechecked against the round’s full family and the interpreter’s actual step. Complete generation is still 31.56–34.45 s: sampled-state
construction costs 16.00–19.81 s and scalar cube construction
10.29–15.52 s, which is concrete input for Lane C's 16.4 work.

The older audit/replay jobs are now terminal. `t14-replay-v1` has eight root
replays: all return an abstract `sat`, none a checked proof, at their original
2,838/3,004-unit allowances. Three concrete audits (including the symbolic
identity diagnostic) establish no genuine relative CTI. These are research
root replays, not full-helper or end-to-end proofs. No owned old T-14 job
remains pending. The 28 unaffected protocols are now running x3 from an
immutable `c9d7f823` archive against immutable `b788e195`, not the changing
working tree (`t16-others-v1`). These are iteration probes, not Lane D's
final merge gate.


# Track P report

Current assignment: [Track Gen — production invariant-generation cost](#track-gen).

**Current Track Gen status:** repaired-source acceptance is complete under the
coordinator’s policy, with one explicitly OPEN negative-phase cost delta.
Historical Track P/K results below are separate evidence.

Base: `40693c7a`; branch: `claude/track-paxos`.

**Status: the original production target passes all three strict 60-second repeats; the first paired IC3Syn gate found six protocol regressions, now under fast-loop investigation.** The initial failures below are retained as history. The engine uses no injected historical law, trusted-checker change, or larger proof budget. No gate success is inferred from scheduler exit status.

## Implementation

- Integrated the supplied generic carry, scan-prefix, and counted-support generators and their tests. Prefix generation is consolidated in `core/carry.ts`.
- Added `core/relevance.ts`: bounded deterministic relevance subsets, lifting trees and count certificates back to the exact full context. Subset failure or SAT is not a whole-context result. The old fixed-size 12/24-law tiers remain opt-in; the verified definition-local source context is enabled for structurally supported count goals.
- Improved selected-count proposals: relevant keyless before/after/incoming comparisons, upper-bound nonincrease/overlap priorities, live referenced-read projection, and exact affine remainder matching. Complete original guarded laws are instantiated; no packed-coordinate equality is assumed.
- Start with preferred existing count instances when seeded bounds exist; retain the lazy pool. Deduplicate symmetric complete instantiated term premises rather than filling source slots twice. Reuse count proposal pools when only primitive PRE support grows; follow count-dependent flags transitively for invalidation. Every retained view is reified and final certificates are checked.
- Archival duplicate files in `research/claude-import/` are excluded from type/lint discovery, not from integrated engine tests.
- No trusted-checker, Lean, model, original-law, proof-budget, or external-solver change. `kernel/cdcl.ts` has optional search-phase timing counters only (disabled by default), with an on/off verdict and checked-tree regression. Structurally supported count and multi-coordinate goals now try the counted pass first; unrelated no-support scheduling is unchanged.

## Commands and observed results

Every substantive run used boat; timing runs used `--vm-type large --timing`.

### Integration and production recapture

```
supercomputer run --jobs research/track-p-jobs.json --out runs/track-p-import-check --class interactive --vm-type large
supercomputer run --jobs research/track-p/experiment-jobs.json --out runs/track-p-fast-v1 --class interactive --vm-type large --timing --data runs/track-p-data:research/track-p/input
```

Initial integration tests: 53 passed, 0 failed, 1173 assertions. Initial check failures from absent pinned submodules and imported helper typing were repaired; final check result is below.

Original harness `run.ts --ms 60000 --only paxos_epr --skip broken`, tree `f1791b206089`: **unknown**, observed 89,328ms wall, 12,997,648 work. This fails strict 60 seconds. Generated 77 candidates; Houdini ended with 29, with safety C7 open. C7 had proved under the larger context before its supports were removed. Capture: 458 model SAT, 91 model unknown, 148 grow trees, 16 grow unknown. Archive: `runs/track-p-fast-v1/dump.tar.xz`.

`runs/track-p-candidates/candidates.log`: **19/19 reference-family formulas generated** (15 exact names, 4 alpha-equivalent generated names). Historical laws are never injected into production.

### Fast-loop relevance and family baseline

Five historical unknown queries were replayed in pairs at 1500 counted ms. Goals of 174, 196, 204 and 210 hypotheses remained unknown at depth zero; a 104-hypothesis abstraction was SAT. Hypothesis relevance produced **no checked proof flips**. These SATs are not reachable counterexamples.

```
supercomputer run --jobs research/track-p/family-jobs.json --out runs/track-p-family-v1 --class submission --vm-type large --timing --data runs/track-p-data:research/track-p/input
```

Initial generic family replay checked **32/38 obligations**, in both full-hypothesis and relevance modes. The complete v5 replay (`runs/track-p-family-v5/`, tree `f11a474c1b70`) still checked 32/38 in each mode. All INITs checked. STEP indices 7, 10, 11, 17, 33, 66 remained open (10 returned SAT for an incomplete abstraction; others unknown). This is standalone generic-proposal replay, not production family admission. Tree results were checked with `checkMC` against original obligations.

### C9 and C11: independently checked

Evidence: `runs/track-p-gaps/REPORT.md`, `recheck-run/recheck.log`, retained requests/trees, and complete investigation source in `runs/track-p-gap-source/`. Fixture SHA256:

```
ee4bee5547e52dc7222e210f1a188e9adb1b81fe542eb01396cacba26e7007f1
```

- C9 STEP checks with its own PRE law (17 hypotheses, observed 163ms), and with family19 (22 hypotheses, 115ms). Two comparisons suffice: old-minus-post and incoming-minus-post, at actual selected reads. Removing a count witness rejects retained certificates.
- C11 STEP checks with family19: 37 encoded hypotheses, observed 205.63ms. Reduced alternative: **32 hypotheses, 364.05ms**, using C33[a,b,pv] and C45[wMeet,a,b], without quantified C3/C61 instances.
- Fresh replay regenerated the original goal, verified source binding, and checked certificates again. These are derivability results, not production discovery or whole-family admission.
- Existing arithmetic proves equality of the packed prefix and low digit from equal full keys and low-digit bounds. Individual node/round cancellation is false; explicit SAT counterexamples are retained. No unsound coordinate identity was added.

### Concrete search failures and final bounded changes

The emitter audits identified:

1. Four cold C33 coordinate proposals filled its four slots before needed C33[a,b,pv] arrived. Whole-premise symmetry deduplication in a standalone scheduling control emitted that tuple on the next pass.
2. Repeated pool construction consumed the shared **65536-work** generation limit before C70's next closure pass. C70 appeared with the hand-selected request.
3. A temporary two-slot reservation failed because the first sparse pass refilled the slots. A coarse all-flags cache was invalidated by primitive rowOk because an unrelated flag read counts.

The final implementation instead deduplicates symmetric term premises at both admission sites and follows only actual/transitive count-dependent flag instances for pool invalidation. The v5/v6 regression caught lower-quality cold sources backfilling freed slots, including through the generic partial-read fallback. The final selector preserves exact write-key donor priority in both paths; its regression requires both distinct roots with no symmetric or unrelated-value backfill. Budgets are unchanged.

V5 and V6 strict checks passed (0 errors/warnings); each had 53/54 targeted tests pass before the complete backfill fix. V5 generic C9 checked at 53 hypotheses (227ms full, 269ms relevance). C11 remained unknown at 99 hypotheses, zero case splits (1524ms full, 1301ms relevance). This is a proof-search timeout, not the six-round observation ceiling or a counterexample.

Final command:

```
supercomputer run --jobs research/track-p/focused-v7-jobs.json --out runs/track-p-final-validation --class interactive --vm-type large --data runs/track-p-data:research/track-p/input
```

The exclusive-timing v7 batch (`20261107-235739-41327e`) remained wholly queued behind other real work and was explicitly cancelled/closed with zero VMs or starts. Final validation uses shared large-VM slots; its timings are **not benchmark evidence**.

Final source tree `28dca86ad30b`, `runs/track-p-final-validation/`:

- `bun run check`: **passed**, zero warnings/errors (903 files).
- Targeted support/carry/prefix/relevance tests: **54 passed, 0 failed, 914 assertions**.
- Generic C9 INIT and STEP: **checked** in both modes; STEP uses 53 encoded hypotheses.
- Generic C11 INIT: **checked**. C11 STEP: **unknown**, 99 encoded hypotheses, zero case splits, round 3; this is a proof-search time exhaustion, not the six-round observation ceiling.
- The residual wall is now explicit: the generic search still fails on a 99-hypothesis C11 context while a source-bound 32-hypothesis certificate checks. The five other open family obligations in the complete v5 replay also prevent family admission. Hypothesis-pruning experiments did not turn those into checked production proofs.

No final-run timing is used as benchmark evidence because that validation shared its large VM.

## Follow-up: certificates and 89.328-second wall-time accounting

Both requested certificates are exported to `runs/track-p-certs/{c9,c11}/{goal.json,proof.json}` in the C14 pack format. Fresh boat check-only replay returned true for both, with `searchWork: 0`, no nonzero search costs, and witness-removal controls rejected. C9 has 17 encoded hypotheses; C11 has 32. Hashes and source bindings are in that directory.

The original `DUMP_MIN=0` ledger contains **713 root queries**. `research/query/dump.ts` records wall milliseconds, and the root hooks suppress nested logging; these totals are disjoint. Exact accounting source: `runs/track-p-fast-v1/timing-accounting.json` (ledger SHA256 `c2b2ba00d188f9c1698448f7b89368fbe143fe5a53859d7c06ffff86e7762c37`).

| Root outcome | Queries | Total wall ms |
|---|---:|---:|
| proved (`tree`) | 148 | 1,379 |
| unknown | 107 | 7,347 |
| SAT | 458 | 47,516 |
| all roots | 713 | 56,242 |
| outside root queries | — | 33,086 |

549 model queries consumed 54,862ms; 164 grow queries consumed 1,380ms. Thus the six open STEPs' failed proof attempts are **not the entire overshoot**: SAT/model search and time outside the root queries dominate. The 187 traced per-law attempts total 73,060ms, comprising 56,242ms in root queries and 16,818ms between/around their queries. Another 16,268ms lies outside those traced attempts.

**Generation of the 19 laws was not wall-timestamped in this capture.** The log's `candidates at 0 ms` uses the counted `clock()`, not wall time, and cannot support a zero-generation-time claim. The 16,268ms outside attempts includes generation, early small-state work and other admission/control overhead; it cannot honestly be assigned to generation alone. Generation-only replay (`runs/track-p-generation-timing/generation-only.log`, pinned large VM, zero root queries) measured **18,387.93ms** through the same admission path: model 0.29ms, caller laws 1.27ms, guard laws 3.78ms, initial small-state warmup 6,742.40ms, caller small filter 48.10ms, candidate generation plus small-state filtering 11,590.58ms. It generated 77 candidates and matched 19/19 family formulas. This is a current-source isolated measurement, not a retroactively invented timestamp for the historical 89.328-second run.

| Rank | Ledger index (zero based) | Kind / recorded name | Hyps | Outcome | Wall ms |
|---:|---:|---|---:|---|---:|
| 1 | 459 | model / counted | 122 | unknown | 2,068 |
| 2 | 362 | model / counted | 318 | SAT | 1,967 |
| 3 | 157 | model / counted | 289 | SAT | 1,728 |
| 4 | 453 | model / counted | 279 | SAT | 1,727 |
| 5 | 474 | model / counted | 223 | SAT | 1,357 |
| 6 | 329 | model / counted | 219 | SAT | 1,258 |
| 7 | 419 | model / counted | 252 | SAT | 1,244 |
| 8 | 471 | model / counted | 195 | SAT | 1,157 |
| 9 | 122 | model / counted | 152 | SAT | 1,138 |
| 10 | 340 | model / counted | 238 | SAT | 997 |

The dump records these goals as `counted`; it does not preserve their owning law name. The ledger indices above identify them exactly. No invented law attribution or retrospective generation timestamp is used.

## Six open STEPs: checked support and emitter diffs

All six now have source-bound hand certificates checked against the unchanged original fixture (SHA256 `ee4bee5547e52dc7222e210f1a188e9adb1b81fe542eb01396cacba26e7007f1`). Each fresh check regenerates the raw goal/declarations/encoded goal and calls `checkMC`; no search is used for authentication. Deletion experiments characterize these retained requests, not globally minimal proofs: an abstract SAT result after deleting a premise is **not** a reachable protocol counterexample.

**Important audit limitation discovered during comparison:** the historical `family.ts`/`audit-support.ts` loop seeded *all* input terms, called `polaritySelection` for every target, and reselected after each closure. Production filters input terms to actual map keys, uses `smallSelection` for primitive POSTs, and retains semantic selections through reservation. Thus the table below describes the recorded emitter-only audit—not an assertion that production loses its selections. In particular, C10's lost ternary is a replay artifact. `countedAttempts` now exposes the unchanged production attempt to `research/track-p/production-replay.ts`, eliminating this divergence for the next 38-obligation replay. The hand certificates and source-matcher omissions remain independently checkable evidence.

Notation: `C<i>` is the original fixture index; `a,b,c,d` are the target's original bound keys; `k(a,b)=64a+b`. Every count instance below has `below=size`; unit is zero except the C11 meet (unit -1). No guards, assumptions, or packed-coordinate equalities were added.

| STEP | Checked raw/encoded; exact retained PRE instances | Required count expressions / witnesses | Missing or late in the historical emitter audit | Extra PRE tuples (each exact tuple is listed in the linked ledger) |
|---|---|---|---|---|
| **7** | **28/39**. C7(a,b,c,d); C10(a,b),(c,d); C17(a,b),(c,d); C11(a,b,r,v),(c,d,r,v),(r,v,a,b),(r,v,c,d); C33(a,b,v),(c,d,v); C45(wNew,r,v). | wNew: `members[0]-missing[0]`; wA/wC: `members$Decision[k]-can$Vote$members[k]` at k(a,b),k(c,d); wR: `members[0]-missing[0]-can$Vote$members[k(r,v)]`. | First 11 PRE tuples in prepare; C45(wNew,r,v) never selected generically, appears in closure:0 with hand cert. All four needed count signatures exist in full pool (indices 16,25,32,77), but polarity-only selection omits them. | **64**: flags 4x10; C2:3,C4:4,C9:1,C10:1,C14:4,C17:2,C33:2,C45:4,C61:1,C74:2. [Exact diff](track-p-six/seven-seventeen/c7/diff.json). |
| **10** | **17/23**. C10(a,b). | `members$Decision[k(a,b)]-members$Decision#[k(a,b)]`; `members[0]-missing[0]-members$Decision#[k(a,b)]`. | PRE present in prepare. Both count signatures selected in closure:0; repeated exhausted selection loses the ternary in closure:1. No-flags emitter control retains both and independently checks its 54-hypothesis goal. Production already retains selections. | **62**: flags 4x8; C4:3,C7:4,C9:1,C11:4,C14:4,C17:4,C33:2,C45:4,C61:1,C70:2,C74:1. [Every phase](track-p-six/ten-sixtysix/c10-all-audit.json). |
| **11** | **27/32**. C2(64*wMeet+a); C4(4096*wMeet+64a+b); C9(0); C11(a,b,c,d),(a,b,pmaxr,pv); C14(wMeet,k(a,b)); C33(a,b,pv); C45(wMeet,a,b); C70(wMeet,pr,a); C74(wMeet); ?rowOk(k(a,b)). | wDiff: `can$Vote$members#[k]-can$Vote$members[k]`; wMeet: `members$Qs[0]+can$Vote$members[k]-size` (unit -1). | C9 and both C11 tuples prepare. C2,C4,C14,C45,C74 and rowOk at closure:0. C33(a,b,pv), C70(wMeet,pr,a) missing when shared generation reaches65536. | **51**: flags 4x10; C2:1,C3:1,C4:1,C10:3,C14:1,C17:1,C33:2,C45:1. [Exact recorded audit](track-p-six/c11/c11-current-emission.log). |
| **17** | **19/22**. C17(a,b); C3(k(a,b)); C45(wNew,r,v). | wNew: `members[0]-missing[0]`. | First two PRE tuples prepare; C45 never selected generically, appears in closure:0 with hand cert. Needed count signature exists at base/full pool index2 but polarity-only selection omits it. | **69**: flags 4x8; C2:3,C4:4,C7:4,C9:1,C10:3,C11:4,C14:4,C33:2,C45:4,C61:3,C70:2,C74:3. [Exact diff](track-p-six/seven-seventeen/c17/diff.json). |
| **33** | **21/21**. C33(a,b,c); C3(k(a,b)),C3(k(a,c)); C61(b),C61(c). | **Empty** reads/instances/picks. | No final missing PRE. C61(b),C61(c) first closure:0; other three prepare. Generic final goal also independently checks (98 raw/106 encoded), so this is avoidable context/selection cost rather than unsupported semantics. | **77**: flags 4x9; C2:3,C4:4,C7:4,C9:1,C10:3,C11:4,C14:4,C17:4,C33:3,C45:4,C61:1,C70:2,C74:4. [Normalized phase ledger](track-p-six/thirtythree/emission-diff.json). |
| **66** | **18/18**. C45(w,maxr,v); C3(64*maxr+v). | **Empty** reads/instances/picks. | Both tuples absent throughout generic all/no-flags and fixed-empty controls, even with work remaining. Actual free PRE read `Vote[4096*w+64*maxr+v]` occurs in nonquantified `step.flags.proposes`; complete matching yields C45, whose Proposal read yields C3. This is a real missing source class, not a projection or new lemma. | **60**: flags 4x6; C2:4,C4:4,C7:4,C9:1,C10:2,C11:4,C14:4,C17:3,C33:1,C45:4,C61:1,C74:4. [Every phase](track-p-six/ten-sixtysix/c66-all-audit.json). |

[**Every one of the 383 extra PRE tuples**](track-p-six/EXTRA-INSTANCES.md) is named explicitly, including each individual flag argument. Full count mappings, semantic witness normalization, and phase lists remain in the linked JSON. Certificate directories: `track-p-six/seven-seventeen/c{7,17}`, `track-p-six/ten-sixtysix/c{10,66}`, `track-p-six/thirtythree`, and the previously exported `track-p-certs/c11`.

### Shared mechanism to test

Use **live obligation/transition reads and selected count witnesses** as source anchors; instantiate whole original laws, including all guards. Complete free transition reads must participate even for scalar targets; their newly exposed primitive reads need ordinary range closure. Delay broad quantified-flag seeding and speculative discarded cold count witnesses. Primitive targets should try primitive support before optional counts, but must retain a count fallback: C7/C17 demonstrate that a primitive POST can still need transition count reasoning. First measure and replay the exact production selector/reservation path, rather than implementing fixes for research-only selection loss.

## C11 phase profiling: zero final tree depth was not zero CDCL decisions

Pinned boat large, AMD Ryzen 9 9950X, 2 of 8 vCPUs, exclusive placement with zero co-tenants. Every request retained the same 1500ms counted allowance and <=2500ms wall ceiling. These are single fast-loop diagnostics, not a 60-second benchmark. Batch queue time was 637s; actual job time was 8.8s total and is not confused with proof time. Source: `research/track-p/profile-step.ts`; complete receipts and serialized input packs: `runs/track-p-phase-profile/`.

| Mode | Final result/context | Total wall ms | Instance generation | Pool | Selection | Closure | Encoding | grow/search |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| Historical replay, exact 99-hyp failure | unknown; lost count selection after work exhaustion | 959.15 | 19.68 | 2.84 | 3.94 | 3.96 | 6.15 | **911.68** |
| Retained initial two count instances | unknown, 85 hypotheses | 936.13 | 22.44 | 2.68 | 2.00 | 2.42 | 2.07 | **903.69** |
| No blanket initial flags (still simplified replay) | abstract SAT, 52 hypotheses | 239.73 | 19.36 | 3.89 | 4.10 | 5.72 | 5.95 | 190.33 |
| Checked hand request | **tree, checkMC=true**, 32 hypotheses | 175.94 | — | — | — | — | 0.64 | **141.42** |

The 99-hypothesis run made **12,556 CDCL decisions and 216 conflicts in 3 sessions**. Their first decisions occurred 28.47ms, 10.03ms and 8.85ms after each session's search began. CDCL setup total was 0.16ms; Boolean propagation was 7.28ms; reader row construction 140.58ms; theory solve 269.57ms (including 179.65ms FM leaf work); ordering 123.45ms; bound extraction 70.55ms. These nested diagnostic timers must not be summed as disjoint phases. The final `0 case splits deep` refers to the plain proof tree's current depth, **not** the number of CDCL decisions. Thus the premise that C11 spends its allowance before the first decision is falsified. Most wall time is search over the admitted context, not instance preprocessing.

Retaining the count view removes the replay bug but does not close C11: its 85-hypothesis search still makes 5,293 decisions and 172 conflicts. The hand request makes 554 decisions, 112 conflicts, and checks. The next generic work is to supply the exact transition/selected-witness source closure with fewer irrelevant premises; merely speeding preparation or preserving a stale selector is insufficient. The exact production-attempt baseline below independently separates the real remaining gaps from replay artifacts.

The optional diagnostic counters passed their timing-on/off verdict and kernel-check regression (`cdcl-counters.log`: 1 test, 9 assertions). The trusted checker `kernel/kernel.ts` is unchanged.

## Faithful production-attempt baseline (before demand-driven changes)

The extracted `countedAttempts` closure preserves production keyed-input filtering, primitive-vs-count selector choice, reservation, MBQI and proof search. Its fixed-family baseline checked **10/12** INIT/STEP requests for the six investigated targets; this is not yet a full-38 result.

| Target | INIT | STEP | STEP wall ms |
|---|---|---|---:|
| C7 | checked | checked | 399.28 |
| C10 | checked | checked | 140.48 |
| C11 | checked | unknown | 1101.47 |
| C17 | checked | checked | 151.10 |
| C33 | checked | checked | 172.60 |
| C66 | checked | unknown | 883.05 |

Thus four historical open STEPs were artifacts of the simplified replay. C11 still has a real context/instantiation problem; C66 still lacks the free transition-read source. Baseline receipts: `runs/track-p-production-baseline/`. All returned proofs were rechecked with `checkMC`. Its initial strict check found six TypeScript diagnostics in three newly added audit-only scripts; those explicit undefined-return/binding checks have been repaired, with the next full check pending.

The next test batch uses one generic rule for both remaining gaps: no blanket initial flag terms for supported goals, no discarded cold count-witness preparation, complete free reads reachable from the target's actual updates, and whole original range laws at exact PRE reads exposed by that closure. Existing selector/reservation code and every proof budget remain unchanged.

## Demand-driven fast loop, first implementation

`runs/track-p-demand-v1/` returned **35/38 checked**, not acceptance. C66 flipped to a checked production proof (201.94ms), confirming the missing free-transition-read source. C11 remained unknown. C14 and C45 failed in this full replay after blanket flags were removed; C14's source needs its own root-key flag argument, not an arbitrary input seed. This failure is not hidden or called a final wall.

The regression suite was 43 passed / 2 failed (1127 assertions). One new test had an invalid forward flag reference in its synthetic machine; declaration order is corrected. The other correctly caught cold constant range reads consuming all four slots: kind closure is now restricted to newly matched original premises, retaining the previous cold-read guardrail. The nonisolated full check timed out at 60s without a compiler diagnostic; the next check is isolated.

Next mechanism (implemented for the second replay): derive quantified flag arguments from corresponding actual root reads, retaining the flag's original fixed globals and all guards; cache count proposals by exact count-read spellings plus declarations and the unchanged POST, rather than invalidate them merely because another PRE tuple repeats an existing count read. Reservation and final checking still run against every current goal. No selector, source cap, proof budget or trusted rule was changed. `demand-v2` reruns the full 38, regression tests and an isolated full check, and retains source-bound failure packets for the next comparison if needed.

## Demand-driven second replay and remaining validation

`runs/track-p-demand-v2/` checked **37/38**, including all six originally open STEPs. C11's production counted-pass proof checked in 183.47ms; C66 in 147.46ms. C14 also recovered. C45's combined counted-pass attempt exhausted its allowance before the two-hypothesis INIT goal; a separately checked INIT still passes. This replay had forced pass1, whereas production ordinarily tries pass0 then pass1. The next replay now uses that actual order, sharing the same 1500ms deadline—not granting a second allowance.

TypeScript passed. Lint found nine audit-only unused-variable/type-formatting issues, now fixed. The support suite's only failure was a test requiring one AST addition order for an affine remainder; it now checks the exact normalized term and separately requires the entire original flag body with the emitted term, including unchanged fixed globals. No assertion about guards or nonaliasing was removed.

A further code review found the complete two-read, current-witness join was still rejected unless its tuple happened to mention a write-key variable. The existing stale/wrong-map test only used such a write anchor. A new no-write-anchor variant passes after correcting that eligibility guard; stale, different-witness and wrong-map controls still pass (`runs/track-p-live-join/bridge-controls.log`). Its focused production C11 replay also checks (361.38ms). This is a source eligibility repair, not an added premise, coordinate equality or larger budget.

## C45 follow-up: corrected hypothesis and next mechanism

The ordinary pass order **did not** fix C45. The initial two-hypothesis INIT timeout was a symptom: the new before-decision observation shows the allowance goes into a 47-hypothesis STEP decision search. Shared-slot correctness probes return unknown; their wall times are not benchmark claims (`runs/track-p-pass-order-probe/`, `runs/track-p-relevance-probe/`).

The existing relevance path skipped the 19-law family entirely because its early return was `laws.length <= 24`, despite having a 12-law tier. Allowing that existing tier gives a 39-hypothesis query, but it also remains unknown (`runs/track-p-relevance-medium/`). Its regression test passes. This does not justify a production-success claim.

The retained C45 packet exposes a concrete source-priority defect: all four range slots for its second root map are consumed by ambient/transition terms before the actual root read gets a range. The next change ranks exact root and reachable free-transition reads ahead of ambient reads, within the unchanged four-per-law and 64-total caps. A direct whole/subset `grow` control of the saved query runs alongside that focused test. No guard or packed-coordinate equality is added.

The isolated v3 suite waited unplaced for 13 minutes; that zero-placement interactive batch was explicitly closed before resubmission as a gate. The gate batch remains pending behind shared worker work. Focused probes use shared boat slots and are labeled correctness-only.

## C45 direct-search control and bounded preflight

The range-priority regression passes, but that priority fix alone does not close C45. The same saved, unchanged production STEP query **does** close through `grow`: full 47-hypothesis goal and both relevance subsets check after lifting back to the original goal. In particular, the 22-hypothesis subset produces an original-context checked certificate. These are shared-slot correctness controls, not isolated timing claims (`runs/track-p-range-priority/c45-captured-grow.log`). The serialized control is `runs/track-p-certs/c45/{goal,proof,source}.json`.

The next generic change uses one sixth of the existing attempt allowance for one relevance-first `grow` before model construction, only on supported goals with no current count witnesses. A subset model is ignored; only a tree widened to the exact whole STEP can be reused. The producer also keeps an actual tree returned by decision search rather than growing it again. Neither path raises an allowance or changes kernel acceptance. A true-invariant/false-update regression and the full 38-obligation replay are now queued.

The isolated gate batch expired without placing any item and was explicitly closed. The new suite uses available shared boat slots for correctness only. Strict isolated 60-second runs still remain required.

## Full fixed-family closure

`runs/track-p-preflight/family38.log` and the corrected `runs/track-p-preflight-v2/family38.log` both report **38/38 checked**, with **`closedFamily: true`** from `checkCountedLaws` on the assembled 19-law certificate. This is the production attempt implementation and ordinary pass order, not the old simplified replay. These are shared-slot correctness results, not 60-second whole-harness results.

After correcting three strict typing issues and a test-only bound-name collision, **49 targeted tests pass (1191 assertions)**. The serialized C45 certificate independently authenticates with zero search, and an empty-tree corruption is rejected (`runs/track-p-preflight-v2/c45-auth.log`; goal SHA256 `d1d6bc84db235a1c968f4572df7d9abf237a9d5028ee7e3b69990403d6e635d0`, proof SHA256 `7c6d353a29a46825a6a55f38a3f0aeaccf21e18106e52c085c38ad86cdb1656c`).

The combined type/lint command hit its shared-slot wrapper's 210-second execution limit without a diagnostic. It is being rerun with an appropriate compile-only deadline; no prover allowance changed. The original-harness target and all subsequent merge gates remain pending.

## Integrated admission after fixed-family closure

The first new isolated original-harness diagnostic is **unknown at 137,507ms**, not a pass. `runs/track-p-integrated-v2/placement.json` records one large VM, all 8 vCPUs pinned, no co-tenants. This uses the repository's whole-large-VM resource shape; the earlier one-slot timing request never placed and was closed before replacement.

Production still generates **19/19** reference-family formulas among 77 candidates (`generation-comparison.json`). The retained ledger has 647 root queries: 124 proved (4,320ms), 96 unknown (13,849ms), and 427 satisfiable (51,348ms). Total query time is 69,517ms; traced admission attempts total 100,490ms. The 37,017ms outside traced attempts must not be called generation time: this capture did not wall-timestamp generation. The full top-ten table is `timing-accounting.json`.

The failing scale is now the 77-candidate admission context, not derivability of the 19-law family. Current law-level relevance ranks many same-map empirical cubes before count and transition support; for the caller safety law, the 12-law tier contains none of the other checked-family laws, and its 24-law tier contains only one. The next fast-loop experiment compares the actual full context, existing law tiers, and a generic source/transition-width core. No hand-selected family is substituted into production. Three clean target repeats and all later merge gates remain unrun.

## Wide-context controls and witness ownership

The alpha-matched generic source/transition core contains 45 of the 77 candidates and all 19 reference formulas. At the original initial 779ms share it checks 18/19 laws; C11 is the sole remaining failure (`runs/track-p-core-context-v2/`). A 1500ms diagnostic identified **`reservation different witness owner`**, rather than merely a time or work-cap exhaustion (`runs/track-p-c11-rejection/`).

The producer now preserves every live owner and alpha-renames only an independent regenerated cold binder that reused its spelling. Any use of that binder in a read, bound, or pick still rejects; duplicated owners and captured/source names still reject. The focused regression passes all eight assertions (`runs/track-p-owner-focused/owner-test.log`). C11 no longer raises that reservation error but still does not close in this wider context: its counted queries grow from 97 to 202 hypotheses. This is a repair, not a target pass.

Research-only proof-directed admission did not close: treating every emitted instance as a dependency needed 176 queries/full-context or 82/needed-first; inspecting actual tree premise use reduced this to 28 queries, but C11 still failed before its own prerequisite closure was present (`runs/track-p-demand-admission/`, `runs/track-p-demand-used/`). No experimental admission policy has been enabled in production. The next controlled mechanism is to warm the existing structural prefix/carry proofs before demanding count guards, then follow only actual proof dependencies. It retains the original allowance helpers and requires a final `checkCountedLaws` closure; it is not allowed to substitute the known 19-law list.

### Ownership repair checkpoint

The full type/lint command passed (`runs/track-p-owner-validation/check.log`, snapshot `2168180817ed`). A shared-slot regression run timed out in two existing multi-proof carry tests; the isolated rerun passes **56/56 tests, 967 assertions** (`runs/track-p-spine-v2/targeted-isolated.log`). The first shared family replay was 36/38; the isolated replay after making collision dependency scanning lazy restores **38/38 and `closedFamily: true`** (`runs/track-p-owner-isolated-family/`, snapshot `abb62a4698e6`). These fixed-family results are not integrated timing claims.

Warming every structural candidate did not solve admission: both warm variants still failed after 46/53 queries. A definition-source frontier reduced wasted calls but also remained open. The remaining controlled question is which additional candidate sources perturb an otherwise checked C11 proof; the next fast-loop comparison adds each extra source separately to the same generated 19-law control. No experimental admission scheduler is enabled in production.

## Single-source contamination and source-budget diagnosis

The next control uses the *generated* 19 formulas, not the handwritten family. All four 779ms controls checked C11. Adding each of the 26 other generic-core formulas separately produced six failures (`runs/track-p-contamination/summary.json`). Candidate order alone is not the cause: both reference-order and production-order versions of the same generated 19 checked (`runs/track-p-order-control/`). Four failing additions exhausted the ordinary pass before any counted query; two reached 68/70-hypothesis counted queries, with the expected two count instances still present. Count-first made the 19-law controls faster but did not close either the 45- or 77-law context (`runs/track-p-count-first/`).

A replay anchored at the actual negated POST, rather than the final appended count axiom, also did not prove the wide goal. Its subsets were satisfiable: the final wide source table was missing the required co-write tuple at the actual intersection witness. Thus further hypothesis ranking alone is not justified (`runs/track-p-anchored-v2/`).

Direct preparation measurement shows why a live-source phase can be starved: the 77-law context admits **64/64** sources before any count witness exists; the 45-law context admits 46. Its ordinary pass also admits 64/64. These are measured counts, not an inferred timeout (`runs/track-p-initial-source-budget/`). Reserving half of the same 64 slots until witnesses exist, prioritizing exact same-witness read/read joins, and restoring selected entries from their owned semantic identities preserves the checked family, but does **not** by itself close the 45-/77-law contexts. The first-query snapshots show both still consuming 64/64 sources before the necessary C33/co-write instances arrive (`runs/track-p-live-source-probe/`). Restricting speculative cross-map slots also regressed C7 and was reverted.

The next generic rule operates on the **source context**, not proof budgets. It expands the target's actual count definitions, keeps keyless count sources and structural support, avoids derived binary source families duplicated by a direct family of the same footprint/arity, and filters unrelated primitive state guesses and clauses wider than any concrete update key. The resulting C11 context has **26 laws**, selected without protocol names or reference-family indices. In the standalone control it checked in 328–431ms; the old 45-/77-law searches remained unknown.

Production now tries such a context first inside the existing counted-attempt allowance, then widens and calls `checkMC` on every full-context obligation before returning the proof. Failure falls back to the original context while allowance remains. Count-bearing and multi-coordinate goals with structural support try the counted pass before the ordinary pass; no-support scheduling is unchanged. With this path, C11 checks against **both 45 and 77 original laws** in 540ms and 516ms respectively; **38/38** unchanged-family obligations check; **48 tests / 933 assertions** pass (`runs/track-p-context-integration-v2/`). These are not three-repeat acceptance results. The subsequent original integrated harness returned **unknown in 77,449ms**, with 34 candidates remaining (`runs/track-p-context-integrated/`, snapshot `8739cfe06fe7`). The strict C11 law initially survived; later, at the 38-law Houdini context, both it and C45 were dropped and safety subsequently failed. The captured machine and all 77 initial laws are byte-for-byte identical to the fast-loop fixture, ruling out fixture drift. At 38 laws the initial two-thirds size gate disables the useful 26-law source context. Removing that gate alone was insufficient when a fixed half-share cut off a valid local proof. Giving the preferred context the existing remaining allowance (no deadline extension) checks C11 at the exact late 387ms budget and against all 77 laws (`runs/track-p-late-context-v3/`). The exact C45 packet also checks in direct tree search (24–39 hypotheses, 91–184ms), while the old path spent only one sixth of its allowance on a truncated preflight and then timed out in model construction. Small, already-reified goals now receive full-goal tree preflight, capped by the original attempt deadline. The late 38-law C45 request checks in 200ms and the full 77-law request in 270ms; C11 still checks across those contexts at the same captured 387ms allowance (`runs/track-p-packet-probe/`, `runs/track-p-direct-preflight/`). The frame-only context remains research-only; no special C45 rule was added. This preflight change passes `bun run check`, **38/38** family obligations, and **48 tests / 946 assertions** (`runs/track-p-direct-preflight-validation/`, snapshot `9a66101e8de3`). The type/lint check and 38/38 replay passed at checkpoint `285dfd9cca17` (`runs/track-p-context-validation-v2/`); the final count-demand refinement also passes type/lint, **38/38**, and **48 tests / 937 assertions** at snapshot `48e47f296abf` (`runs/track-p-context-validation-v3/`).

## Dependency-closed candidate admission

The first bare, no-capture run after the preflight change was killed by the strict 60-second limit (`runs/track-p-direct-bare/`). The next fast-loop control showed why merely proving more isolated obligations is insufficient: a caller certificate can use a stronger but false empirical helper, then fail when that helper is removed. After removing two such guesses, the full 75-law caller context failed while a generic 45-law context—caller laws, structural sources, count laws, and primitive relations within concrete write width—still checked.

The new admission loop first proves callers in that generic coarse context, then follows the actual hypotheses used by their certificates. It proves the transitive dependency set, invalidates certificates whose required helper is dropped, and transports all surviving proofs to one retained family before `checkCountedLaws`. Unknown or missing dependency analysis falls back conservatively. No-support search keeps the original scheduling; budgets and all final kernel checks are unchanged.

The research pilot closed 26 laws in 18,195ms. The exact production admission entry point then closed **26 checked laws** from all 77 candidates in **20,722ms**, and from the post-drop candidate set in **13,590ms** (`runs/track-p-admission-replay/`). These are query/admission replays, not complete harness timings. Validation passes `bun run check`, **56 tests / 987 assertions**, and **38/38** unchanged-family obligations (`runs/track-p-admission-validation/`, snapshot `4269e72bd2c6`). The original strict, no-write harness is being measured again before any repeat or merge-gate claim.

## Gates and disposition

The original no-write harness first returned **proven in 50,290ms** (`runs/track-p-admission-bare/`). Three subsequent clean process repeats, all at the original 60,000ms budget and under an external `timeout -s KILL 60s`, returned:

| Repeat | Harness verdict | Harness wall ms | Retained laws | Strict exit |
| --- | --- | ---: | ---: | ---: |
| 1 | proven | 46,924 | 26 | 0 |
| 2 | proven | 36,420 | 26 | 0 |
| 3 | proven | 38,898 | 26 | 0 |

Receipts and `placement.json`: `runs/track-p-strict-repeats/`, tree `00fa79612bed`, large VMs, all eight vCPUs pinned, **zero co-tenants**. No diagnostic capture or hand-written invariant was passed to the harness. Production implementation checkpoint: `38cfd68c`.

The paired IC3Syn **29 x 3**, DuoAI **ten paired**, **29 broken**, **seven test shards**, and quick-bar gates are now in progress against main `40693c7a`. They are not yet claimed as passed. Manifests are generated by `research/track-p/make-gate-jobs.ts`; paired jobs alternate candidate/base order, use the same VM for both sides, and cap each side at the unchanged 60-second limit. No main-branch merge or publish action has been taken.

### First regression-gate pass (not acceptance)

The local coordinator deadline expired at 1,000 seconds. The scheduler had durable receipts for all **87 IC3Syn pairs** and **10 DuoAI pairs**; these were recovered without rerunning the jobs, retaining exact stdout/stderr SHA256 hashes and original placements (`recovery.json` in each suite directory; `research/track-p/recover-batch.ts`). One IC3Syn pair had no usable verdict log and is incomplete.

The first paired pass is **not green**: candidate 66/87 versus baseline 79/87, with losses on `consensus_epr`, `consensus_forall`, `consensus_wo_decide`, `majorityset_leader_election`, `naive_consensus`, and `simple_election`. The three Paxos pairs are gains. All ten DuoAI pairs prove on both sides. The common symptom in the six losses is a primitive point-guard support activating the new count-specific admission path even though no structural support law reads a declared count. The next fast-loop test retains all generated candidates but enables count-specific scheduling only when the structural support actually uses a count.

Four co-tenant test shards failed, mainly at Bun's default wall timeout. An isolated same-VM main/candidate control of the search and Python-reader tests passes, as do the isolated carry tests, with no budget or assertion changes. All seven shards are being rerun on exclusive VMs. The initial broken suite had 24 returned non-proven verdicts and five outer supervisor timeouts: the runner subtracts 30 seconds from a job's configured timeout. Those five are retried with enough supervisor overhead to record the unchanged strict 60-second inner timeout. The quick bar also lost its local coordinator and is not claimed complete.

### Semantic support roles

Disabling count-specific scheduling for primitive-only support restored five of the six failed families in captured-candidate admission. For the remaining `consensus_forall` family, retaining the two added primitive guards still lost its ordinary proof; using the original 46-candidate family restored **three checked proofs**, in 23,565ms, 16,972ms and 10,553ms (`runs/track-p-primitive-isolation/`). The generic production rule now preserves the ordinary candidate family first unless an active structural support law reads a declared count. Primitive-only proposals may widen a failed ordinary search, but do not replace it. The original shared deadline remains unchanged. Names and protocol identities are not inspected.

The role change passes **57 tests / 1,005 assertions**, and the captured Paxos admission still closes 26 checked laws in **11,120ms** (`runs/track-p-support-role-validation/`). Initial full checks found only typing/lint issues in newly added research scripts; these were repaired before the next validation sequence. The prior implementation's isolated seven-shard rerun passes all seven shards (**745 tests**), and all 29 broken variants remain non-proven: **11 refuted, 16 unknown, 2 strict timeouts**. The full gate sequence will be rerun on the role-fix commit, with each gate required to pass before the next launches (`research/track-p/run-gates.sh`). The first restart stopped correctly at the tooling check: two concurrent checks hit their 210-second worker limit. The check job is now isolated with a longer tooling-only supervisor cap; all prover budgets and strict target limits remain unchanged.

The direct-count-only role test was too narrow: all three renewed strict target runs timed out. The target's essential scan/global guards support count proofs through global state and quantified definitions, without directly reading a declared count. The refined, still generic role test therefore keeps a count read **or a non-pointwise mutable-global-state condition**. Constant tautologies do not qualify. The frozen replay now goes through the production role selector, avoiding the earlier test blind spot. All six regressed families check with that selector (`runs/track-p-global-context-regressions/`), while the full 77-candidate target retains its structured support and checks a 26-law family (`runs/track-p-global-context-validation/`). Type/lint and the targeted tests pass. The complete sequential gate run will be repeated on this refinement. Its first restart passed the full check and returned target proofs at 21,212ms and 32,236ms with identical search work; one worker hit its outer 60-second cap without a verdict. The worker cap incorrectly included dependency installation as well as the inner strict harness limit. The supervisor now leaves setup overhead outside that inner limit and logs setup/harness boundaries; the actual harness is still killed at exactly 60 seconds. No assumption is made that the missing verdict was a proof.

The separated supervisor confirmed one genuine 60-second harness timeout, alongside two proofs; setup took under one second. Current generation-only controls account for **21.5–34.4 seconds**, dominated by small-state sampling (9.9–16.2s) and cube inference (10.5–16.9s), with zero root proof queries and all 19 formulas still generated. Frozen admission profiles showed repeated broad helper attempts consuming additional time. Applying the same goal-local coarse context to each required helper, always including that helper and retaining full-context fallback, closes **25 checked laws in 27 attempts** rather than 26 in 33. Three research controls took **6.4s, 7.8s and 13.2s**; the exact production replay took **10.4s**. The unchanged checker accepts the smaller family. Type/lint and 57 tests / 1,011 assertions pass (`runs/track-p-helper-context-validation/`). No budget or sampling coverage was changed.

---

# Track M — implementation log (2026-11-07)

Base: `40693c7a`, branch `claude/track-mldr`, worktree `gdp-wired-trackM`.
All substantive computation below ran on boat. No trusted-checker, Lean,
proof-budget, or safety-law change has been made. The untrusted search/proposal
code is changing. This is **not** a completed target/gate claim.

## Diagnosis

The production capture at `../gdp-wired/runs/claude-capture-v1/out/mldr-capture.log`
contains 23 laws, ending unknown on `one primary per term`. Its candidates express
kind/range and zero/nonzero cubes, but not the published relational/count family.

Published reference: Endive `8b6f2abd1988eeb308f965813635e9871f253e2d`,
`MongoLoglessDynamicRaft_IndProofs.tla`. Source receipt:
`runs/track-m/diagnosis-v2/source.log`. The archived translation and Step 0 report
were recovered on boat from `gdp-wired-paused-20261103` /
`gdp-wired-dbae-astra.tgz`, SHA256
`f9cc6b4b98e70c6c7d7f799e56086295f89e3655c2e89e8e195eda3c1f993556`.
Correct-path receipt: `runs/track-m/atomic-v1/published.log`.

| Clause | Shape required | Candidate status |
|---|---|---|
| TypeOK | role range; positive metadata; nonempty initialized rows | kinds cover role; remaining floors/cardinality not all generated |
| Safety | two primaries at equal current term have the same key | unchanged caller law |
| Inv866 | role-guarded equality of two numeric fields at one key | new generic field family |
| Inv3915 | role guard + equal first field across keys implies second-field order | new generic field family |
| Inv1758 | equal two-field metadata tuple implies equality of relation rows | new generic tuple-row family |
| Inv2973 | two active relation rows have overlapping majorities; inactive alternative determined by an ordered-field-qualified count | missing generic count/disjunction family |
| Inv3246 | every majority of an active row meets a field-order-qualified subset, equivalently a cardinality bound | missing generic count/disjunction family |

The row predicate is a three-key universal formula, not a Boolean two-literal
cube. The last two clauses need state count definitions as well as new laws.
All proposed field/row laws still pass sample filtering and ordinary checked
induction; no published law is imported into the engine.

## Port correction

`research/track-m/port-audit.ts` executes the old port's real transition function:
init; `pick S={0}`; `copy i=0`. Equal config terms/versions then coexist with rows
`{0}` and `{}`, so Inv1758 is false. Receipt:
`runs/track-m/port-audit-v1/phase-counterexample.log` (also reproduced in focused
suite). Historical factory is kept only in `research/track-m/phased-mldr.ts`.

The old port's projected BFS nevertheless has 5,362 states / 18,327 nonstutter
edges, 0 bad states, while the broken variant reaches 5 bad states:
`runs/track-m/diagnosis-v2/port.log`. Therefore projected correspondence alone did
not establish that intermediate auxiliary states satisfy source invariants.

New `research/protocols/ic3syn/mldr.ts` uses native tuple relation keys, one atomic
Init request, and one step per subsequent source action. `models.ts` uses it
through the original harness and updates only MLDR's request enumeration and
projection. Source fields reset together at Init; no source invariant is assumed.
The strict-majority broken variant remains. `runs/track-m/atomic-v2/tlc.log`
confirms TLC and the new port both have **5,362 states / 18,327 edges / depth 10**,
with no bad state. The new port has only 5,363 raw states (one dummy plus source
states); the broken variant reaches 5 bad states at depth 3.

## Tests and failures

- `runs/track-m/diagnosis-v2/fields.log`: 63 initial field templates, 5 survive
  samples (32/1,504 states); direct field equality and its two order consequences
  were checked. The printed `proven:true` there concerned **kind laws plus generated
  helpers only, not safety**. That diagnostic no longer runs a full search.
- `runs/track-m/focused-v1/tests.log`: **8 tests pass**, 0 fail, 39 expectations.
  Covers positive checked field proof, broken write rejection, scope/capture,
  deterministic generation, ambiguous-domain refusal, row candidates, atomic
  initialization, actual majority election, and the broken-majority control.
- `runs/track-m/focused-v1/check.log`: **`bun run check` passes** (0 warnings/errors).
  Vendor sources are supplied from the pinned main submodules using `--data`.
- Earlier static check failed because the initial worktree snapshot contained no
  vendor submodule sources (`diagnosis-v2/check.log`). Not an engine regression.
- First new-port correspondence attempt stopped before TLC: the runner already
  mounts `/src/gdp-wired` read-only, so creating a symlink there was wrong
  (`atomic-v1/tlc.log`). Retried without the symlink.
- `atomic-v1/check.log`: typecheck passed; type-aware lint subprocess was SIGKILLed.
  `focused-v1/check.log` subsequently passed. A latest-tree retry requests 4 CPUs /
  14 GB explicitly.
- `published-v1/given.log`: research audit failed to parse (extra parenthesis);
  no proof result. Fixed, and shell changed to `set -e` so packaging cannot mask
  this failure. The next attempt exposed missing count references in law scope;
  explicit `MapRef`s fixed that research-only construction error. Completed
  audits and their failures are below.

## Final diagnostic / named wall

The five published clauses are translated only in `research/track-m/published.ts`
for a given-family inductiveness diagnostic (`GDP_COUNTS_GIVEN=1`, ordinary
`proveRule(..., {search:false})`). Note: the existing counted branch of proveRule
still invokes counted search even with `search:false`; GIVEN disables extra
candidates, not checking. The final fixture also includes explicit TypeOK role,
relation range/domain, positive version and initialized nonempty configuration
clauses. These are research callers only, never engine facts.

`diagnostic-v3/given.log` showed all eight then-supplied clauses true on 141/1,767
sample states but no checked full family. A concrete completeness bug was isolated:
`certFor` found known count members only at whole map keys, not in tuple key
components, and proposed no singleton lower bounds. `count-witness-red` fails that
specific test. The implemented structural member-key proposal plus singleton
picks passes it through **checkMC**, while the wrong-row negative case stays
unprovable. This changes only untrusted certificate proposals.

- `witness-fix-v1`: full static check and **59 focused tests pass**. The complete
  11-clause given family still fails safety/Inv1758/Inv3915/Inv2973/Inv3246; importantly,
  **nonempty configuration after Init now proves**, unlike before the fix.
- `region-fix-v1`: integrate existing untrusted Boolean-region **three-count
  partition** certificates into the wide pool (same cap, same budget, unchanged
  checker). Static check and **60 tests / 957 expectations pass**; includes the
  new checked partition identity and frozen count/countermodel fixtures. The same
  five target obligations remain open.
- `replay-v1/nonempty.log`: old captured 51-hypothesis goal is SAT in 157 ms;
  it lacks the newly generated picks. `replay-v1/row-agreement.log`: old captured
  251-hypothesis Inv1758 goal remains unknown after its 7,500-ms counted allowance
  (1,876,416 work). These are standalone `grow` replays, not protocol reruns.
- Final production-family diagnostics: safety reaches 13 model rounds / 1,480
  accumulated hypotheses before unknown; Inv1758 reaches 802, Inv3915 1,006,
  Inv3246 599. Inv2973 still leaves a SAT augmented goal. None of those SAT
  abstraction models is claimed to be a reachable protocol counterexample.

**Named wall:** with the port corrected and the published family supplied, the
existing bounded count/quantifier-instantiation path still does not discharge
that family. The missing automatic active-row/quorum candidate families cannot
alone close production until these explicit-family obligations flip. Further
work must target those captured count/instantiation goals, not increase budgets,
weaken safety, or assert the family as facts.

Final static/test receipt: `runs/track-m/region-fix-v1/check.log`.
Final failed-family receipt: `runs/track-m/region-fix-v1/given.log`.
Correspondence receipt: `runs/track-m/atomic-v2/tlc.log`.
Each run includes its jobs, placement and summary; relevant shipped tree hashes
are `93566a56f012` (diagnostic-v3), `412bf2630610` (witness fix), and
`b5f644aaf280` (partition fix). Raw failing goal archives are embedded as xz/base64
in the given logs, unpackable with `research/track-m/unpack-goals.py`.

No `MLDR-DESIGN.md` was present in the shared handoff at the last check. Full 3x60s
production and paired IC3Syn/DuoAI/broken/shards/bar merge gates are **not passed
or claimed**; per the handoff they were not launched without a target proof.
Track M is blocked, not merge-ready. No changes were made to main or other
worktrees, and no trusted checker/Lean change, external solver or budget increase
was made.

## Fable design — Step 0 passed (P*)

Following `private/handoff/claude-tracks-20261107/MLDR-DESIGN.md`, Section 3.
The production `mldr` port now uses P*: CV starts at 0; pick writes row 0 and
sets its CV to 1; copy writes another row and sets its CV to 1; start requires
all CVs to be 1. There are no C0/Copied/picked variables. Previous native-tuple
atomic experiments remain reproducible via `research/track-m/atomic-mldr.ts`.

- `runs/track-m/pstar-port-v1/bfs.log`: original `check.ts --only mldr --edges`
  gives **5,362 states / 18,327 edges**, raw 5,391, done true, bad 0 (37,577 ms).
- `runs/track-m/pstar-port-v1/broken.log`: original `--broken` gives bad **5**.
- `runs/track-m/pstar-port-v2/capture.log`: original 60,000-ms harness capture
  completed in 42,262 ms, with 171 queries. No C0/Copied/picked candidates;
  `never 1 <= CfgT[x] and started is 0` remains. Safety is still unknown.
- `runs/track-m/pstar-port-v2/stages.log`: sampling 46/1,205 states, 7,218 ms;
  direct candidate diagnostic finished in 28,352 ms.
- Port initialization/election regressions pass, included in the 72-test
  `runs/track-m/count-proposals-v1/tests.log` run.
- The first capture was killed at its shell deadline, and the first check had
  missing vendor snapshots. The corrected capture succeeded. Latest static
  checks found only two unreachable `cur` comparisons in the new research
  hand-set probe; these were removed before starting Step 1. Static retry pending.

Step 0 changes no source action, safety law, trusted checker, or proof budget.
The hand-set proof (Step 1) is now the gate; no new production families or merge
claims follow without it. Section 1.5 remains pending as of this checkpoint.

### SHA256 receipts

```text
4046c3bb72374cb3622ca429917a7a9156c3ba04823908fe6b10277c516957d1  core/counts.ts
5ddbfd84053b0a3ced4970fc986dc364f445d946db0f75124a903a7266c0d67f  core/field-laws.ts
ac85e04a15c1e25b2c8acc2c1352f138cd3564ce2a98cc2aa63dc9a92071dc4e  research/protocols/ic3syn/mldr.ts
71acbf0f40bc86c1e37f9f28bca5ac6dc77f0245aa0faa5aa141608a9bff1b9a  runs/track-m/atomic-v2/tlc.log
edf4b396e249396d8c5d29507ec7e923aa43702efbb235b1b2a55e15681d3f80  runs/track-m/region-fix-v1/check.log
d21ef126ad3cb849b2c102ebe68c3a37b6bb53a46b89688c6f7919bc3035acff  runs/track-m/region-fix-v1/given.log
```

## Fable design — Step 1 in progress (not passed)

Step 0 is commit `938ee238`. Section 1.5 now reports zero bounded CTIs and
zero encoding mismatches for I-A/I-B, including P*. None of the stated
fallback triggers has fired. These bounded checks are not an induction proof.

The initial explicit I-A run is `runs/track-m/pstar-hand-v1/given.log`:
`GDP_COUNTS_GIVEN=1`, 900,000 ms overall. Four laws are kept: Inv866,
Config-cell kind, p1 and p2. Safety, Inv3915, Inv1758, Inv2973 and Inv* remain
unknown; **the step-1 gate is not passed**. The captured queries and input
are in `runs/track-m/pstar-goals-v1/`.

Controlled standalone replays of the five final step goals at 5,000 ms counted
all remain unknown (`runs/track-m/pstar-replay-v1/`). Their sizes are 203, 237,
304, 334 and 243 hypotheses, respectively. The overlap goal has 293,249 AST
nodes: the current lazy pool is too large to assume that adding more instances
will improve its five-second result.

A concrete missing proposal is universal flag instances at selected count
witnesses. `core/count-witness-flags.ts` proposes those instances without changing
the checker. Its isolated regression passes (one test, seven assertions,
`runs/track-m/witness-unit-v1/witness-unit.log`). But adding all relevant flags
to the captured safety and overlap goals does **not** close either in five
seconds. The safety goal grows from 203 to 505 hypotheses; overlap from 334 to
1,329. Adding the goal's own induction instance also does not close them.
Receipts: `runs/track-m/witness-flags-v1/{safety,overlap}.log`. Broad seeding has
therefore **not** been wired into production search.

Next controlled experiments are checked action-first splits and the design's
minimal four-comparison safety certificate plus structural read instantiation.
They are research probes, not new trusted rules or claimed proofs.

The minimal safety query now **checks in 500 ms counted**, with 98 hypotheses
and four CInsts plus their witness flags (`runs/track-m/minimal-safety-v1/minimal.log`).
Without witness flags it is satisfiable; broad structural read instantiation grows
it to 1,605 hypotheses and leaves it unknown. This checks a conditional induction
goal, **not** the whole hand set. A protocol-independent focused selector and
cold-start count-law bridge seeding are being tested before integration.

The focused suite in `count-proposals-v3` passed; its static job failed because
vendor snapshots were omitted from that boat upload, not because of a reported
Track M type error. The Track M `vendor/` directories turned out to be empty;
validation now uses the populated `../gdp-wired/vendor:vendor` data path. Superseded
queued snapshots were cancelled by exact task ID.

The generic single-carried-set family reproduces the safety proof in **622 ms
counted**, 103 hypotheses and five CInsts (family 0 in
`runs/track-m/focused-families-v2/families.log`). The other family is satisfiable;
Inv3915 and Inv1758 are not yet proved by this replay. A broader cold-start
selector still timed out or returned small abstraction models. In particular,
the row-agreement capture has Inv* instances at rows `a` and `j`, but **none at
request row `i`**. The next refinement supplies those request-to-goal bridges
without enumerating unrelated row tuples.

Arithmetic-only quantified variables now remain numeric constants even when a
boundary equals a row key's current model value. The new aliasing regression and
related tests pass: 14 passed, zero failed (`runs/track-m/model-alias-v2/models.log`).

`GDP_COUNTS_FOCUS=1` enables an experimental, ordinary-kernel-checked small-certificate
recovery before growing a widened goal. It is off by default. The bounded
60,000-ms hand-set diagnostic (`focused-hand-v1/given.log`) keeps Safety through
this path: 539 ms profiled in recovery, after the main attempt reached its
5,001-ms decision cap. Inv3915, Inv1758, Inv2973 and Inv* remain unknown and the
whole call ends at its 120-second wall guard. **Step 1 is still not passed.**

The populated-vendor validation (`count-proposals-v6`) passes `bun run check`
(zero warnings/errors, 918 files) and **76 tests**, zero failures. These receipts
precede the latest focused-bridge and carried-flag refinements.

Action-local replays (`count-cases-v1/cases.log`) isolate Inv3915's remaining
failure to BecomeLeader; the other seven branches produce trees within a total
3,281 ms counted. Inv1758 still fails at Copy, BecomeLeader, Reconfig and
SendConfig under this five-second combined budget. These are partial trees,
not a checked combined proof. The next replay asks action-local models for
ordinary field-law instances and rebases all branch proofs before checking the
unchanged combined obligation.

The newest snapshot passes TypeScript and four focused regressions in
`typecheck-v1` (including column preservation). Starting from only structural
bridges reduces the two field goals to **83 / 97 hypotheses** (`cold-cases-v1`).
The row-agreement BecomeLeader branch now yields a tree, but the entire law is
still incomplete. In `core-cases-v1/cold.log`, CDCL refutes Inv3915's BecomeLeader
branch in **199 ms**, returning a 22-hypothesis core; reconstruction of that core
still times out. Thus that particular branch now has enough logical instances
for the decision procedure, but has not produced a checked proof. The next
controlled comparison enables the existing `atPoint` proof-search mode, which
these counted replays did not inherit. No new trusted rule or larger budget is
used.

`pointed-cases-v1/cold.log` constructs all eight Inv3915 branch trees in
**1,486 ms counted**, and conclusion-last ordering constructs them in 2,325 ms
(`ordered-cases-v1`). Both combined certificates were **rejected**, not proofs.
The replay was rebasing conditional trees as though their source path were empty;
that call now retains the source path. The revised replay checks each branch,
the combined ground tree, and the counted certificate separately. This is a
research-harness correction, not a checker change.

The corrected run **passes**: `pointed-cases-v2/cold.log` has all eight branches,
the combined ground tree, and `checkMC` true for Inv3915, in **1,398 ms counted**.
The standalone path-rebasing regression passes as well (`path-test-v1`). This
verified recovery is now integrated behind the existing opt-in focus flag; its
real hand-set run and new positive/negative boundary tests are running. Inv1758,
Inv2973, and Inv* still block Step 1. No Step 1 commit or later-step claim yet.

The integrated `focused-hand-v2` diagnostic keeps both Safety and Inv3915. It
still returns `proven: false`; the full attempts also exceed the desired
five-second step budget, even where the focused recovery itself is below it.
`typecheck-v2` passes TypeScript and seven focused tests. This is not the final
validation snapshot.

`row-cores-v1` isolates the remaining row-agreement actions. The SendConfig
branch checks in **1,177 ms counted** (722 ms model/core query, 455 ms tree
reconstruction). Reconfig is refuted by CDCL with an 11-hypothesis core but is
not reconstructed within budget. Reordering that fixed core ten ways does not
produce a checked Reconfig proof (`row-order-v2`); the copy core checks in every
ordering. Explicit row-alias splits also do not close Reconfig (`row-alias-v1`).

The count-law probes expose further missing proposals: packed count-key
coordinates were omitting the second row from phase-law bridges; higher-arity
count laws need copied-row instances that preserve their arithmetic witnesses;
and the focused selector was dropping all three-/five-term partition and union
instances. New proposals address these structurally, without adding axioms.
Broad post-frame/structural pools still overwhelm the counted goals
(`count-frames-v1` through `v4`, `count-algebra-v1`); several runs hit the existing
10-second wall guard before spending the full five-second counted allowance.
Their missing final branch trees are not proofs or invariant counterexamples.
A grow-returned count model is now recorded in `count-models-min-v1`, but asking
more instances there still does not close the hand set. New partition regression
and type checks were run in `proposal-tests-v1`: all 14 tests passed, and two
TypeScript diagnostics in the research replay result type were fixed.
`proposal-tests-v2` then passed both TypeScript and the expanded focused tests.
The Step 1 gate remains open.

The row-agreement proof is now complete: `row-rebase-diagnostic-v1` checks all
eight branches, the combined ground tree, and `checkMC`, at **3,739 ms counted**
and 25,198 ms wall. This explicitly labeled diagnostic kept the 5,000-ms counted
limit but allowed up to 60 s wall to isolate rebasing overhead; production
budgets were not changed. Disabling redundant unit discovery only for the
point-guided reconstruction was decisive. Branch-local instance sets keep the
SendConfig core small; all used instances are merged before the final check.
`saturated-cases-v1/rows.log` also checks the full row certificate at **3,716 ms
counted**, 17,740 ms wall, using ordinary linear proof branches for added action
bounds. Neither result is a full hand-set proof or a downstream gate pass.

A separate encoding audit found the research hand-set probe still used Ov_uw.
The design prefers the equivalent Ov_h with explicit half-cardinality premises.
The probe now exposes a reusable research builder with Ov_h by default and
retains Ov_uw under `LAB_OVERLAP_FORM=uw`. `canonical-capture-v1` contains the
fresh Ov_h fixtures. `canonical-replay-v2/rows.log` checks all eight row branches
and the combined `checkMC` certificate at **3,716 ms counted**, 17,517 ms wall.
The two count laws still fail: Inv2973 closes no complete action branch and
Inv* closes five of eight in that replay. Safety and protocol transitions are
unchanged. The two encodings were also compared with actual majority-quorum
intersections for all 1,024 pairs of subsets of a five-element universe; the
machine and every other hand law agree up to hygienic bound-variable names.

`canonical-coarse-v1` and `canonical-stutter-v1` isolate the remaining gap.
Inv*'s UpdateTerms branch checks at 229 ms counted, but BecomeLeader first asks
for an Inv2973 instance at a self-pair with numerical half witnesses. A fixed
focused certificate does not initially name those new count reads. The research
replay now has opt-in identity-preserving certificate growth (`LAB_GROW_CERT`),
which appends new reads/witnesses rather than renumbering ones used by earlier
branches. `count-progress-v1/grow.log` exercises it without completing the
leader branch; no Step 1 pass is claimed.

A separate opt-in frame-lemma experiment factors each candidate count-frame
inequality into an ordinary proof-tree split, retaining its checked pointwise
alternative. The initial full-context version timed out on every attempted
frame (`count-progress-v1/frame.log`). A narrowed field context checks the
UpdateTerms overlap branch at **1,072 ms counted** (`count-progress-v2/frame.log`);
folding its exact action first lowers that to **763 ms counted**, 8,210 ms wall
(`pinned-frames-v1/stutter.log`). Every folded proof is transported back to the
original goal/path before checking. Plain action folding also checks Inv*'s
first four action branches in 107–162 counted ms each (`pinned-cases-v1/all.log`).
Neither experiment yet checks a whole count law; full replays still run out of
budget. A single shared counted deadline now bounds implicit widening searches
as well as explicit queries.

The canonical encoding, arithmetic-witness filtering, stable certificate growth,
Boolean partitions, self-intersection view matching, frame proof, and proof-path
regressions pass the focused tests and TypeScript in `proposal-tests-v5`.
`frame-tests-v1` separately checks both Boolean partition directions and the
positive/negative frame-proof cases. New post-count subset proposals and pinned
model-query experiments remain under validation. These are untrusted proposals,
not new axioms or production budget changes. **Step 1 remains the gate; no
subsequent step is passed.**

### Step 1a: integrated non-count laws recovered (2026-11-08)

`integrated-row-v3/row.log` checks both the start and step obligations for
Inv1758 through `proveFocusedCounts` and `checkMC`, at **3,717 counted ms**.
The integration discrepancies were instance ordering and point-guidance scope:
small extracted cores need point reconstruction, but the full fallback needs
ordinary reconstruction. The same compact proof is not obtained by turning
point guidance on everywhere. `core/count-cases.ts` exposes this as an untrusted
strategy option, with scope-restoration and satisfiable-goal negative tests.

The real `GDP_COUNTS_GIVEN=1 GDP_COUNTS_FOCUS=1` search initially consumed the
row's share in broad MBQI before invoking recovery (`focused-hand-v3`). Moving
the opt-in non-count recovery ahead of that broad search fixes this integration
problem. `focused-hand-v4/given.log` retains all seven non-count laws:

| Law | counted attempt ms | result |
| --- | ---: | --- |
| Config kind | 5 | kept |
| one primary per term | 532 | kept |
| Inv866 | 181 | kept |
| Inv3915 | 2,352 | kept |
| Inv1758 | 3,713 | kept |
| p1 | 861 | kept |
| p2 | 67 | kept |

The overall result is still **not proven**, naming only Inv2973 and Inv*.
Those two attempts still exceed the desired per-goal bound and remain unknown.
`proposal-tests-v7` passes TypeScript and **27 tests / 2,154 assertions**. The
production strategy remains opt-in until the full hand-set and paired gates pass.

`count-model-audit-v4` records a concrete BecomeLeader model with the candidate
row aliased to the leader row, an abstract row size of one, and several distinct
known members. Two missing proposal shapes are now explicit: a three-term
post-remainder + carried-set / stored-row cover, and C3 lower bounds from the
model's distinct known members. The former is retained by the focused selector;
the latter is exercised by `model-count-picks.ts`, prioritizing pre-state rows
and retaining symbolic member witnesses. Its test checks both a valid distinct-
member proof and rejection when the members alias. `model-picks-v1/v2` and
`field-bounds-v1/picks.log` do not yet close the branch.

A separate research-only field-ceiling cut experiment derives candidate bounds
from a strict-successor per-member guard and an ordered count predicate. Its
cuts are never trusted: every accepted cut must have an ordinary reconstructed
proof and the final tree must check against the original goal. The first two
experiments do not prove the cuts within their query windows; further narrowing
is in progress. No complete count-law proof is claimed.

Fable's now-completed Section 1.5 confirms both hand sets on the bounded checks
and P* against TLC. None of its stated design falsifiers fired, so the prescribed
fallback is not indicated. **Step 1 remains the gate.** Step 0 is committed as
`938ee238`; no Step 1 completion commit or downstream gate claim has been made.

### Step 1a checkpoint and Step 1b proposal audit (2026-11-08)

`step1a-checkpoint-v1` repeats the real given-hand-set run and retains the same
seven non-count laws, including Inv1758 at **3,713 counted ms**. Both count laws
remain unknown (16,943 and 18,477 counted attempt ms); the complete hand set is
not proven and does not satisfy the five-second target. This checkpoints the
passed **sub-step 1a**, not Step 1 or any downstream gate.

Validation: `step1a-checkpoint-v1/check.log` passes `bun run check` with zero
warnings/errors; `tests.log` passes **31 tests / 2,171 assertions**. The exact
vendor gitlinks were staged from the initialized main worktree using
`--data /Users/monotykamary/VCS/working-remote/open-source/gdp-wired/vendor:vendor`.
The initial fresh-VM check lacked these uninitialized submodule contents
(`proposal-tests-v8`); a remote Git fetch timed out (`check-v1`). With the pinned
sources staged, `check-v2` exposed two unnecessary quote escapes in the research
member picker; those are fixed, and `check-v3` plus the checkpoint check pass.
No type-check exclusions or production budgets changed.

The subsequent count audit found a concrete selection bug:
`count-inventory-v1/inventory.log` contains **90 five-term candidates, zero
selected**. Earlier partition identities occupied all 16 algebraic slots. The
selector now reserves slots for union bounds and prioritizes their matching
partitions **within the same 16-slot cap**. Its regression is included in the
passing checkpoint tests.

Research-only cut factoring verifies six directed partition cuts in **23–34
counted ms each** and the required five-term union in **50 counted ms** under the
explicit active-leader guard (`symbolic-overlap-v7/active.log`). These cuts are
individually checked against their original goal and current path. The full
count obligation still times out. The Ov_uw symbolic-witness probes remain
separate from the default Ov_h hand set; active-only probes are explicitly
labeled and are not accepted as unrestricted proofs. The incomplete probes
remain outside the Step 1a implementation checkpoint.

### Step 1b research checkpoint — bounded pool and checked proof transport

The second bounded-selection issue is now fixed: per-positive-pair primitive
covers are interleaved with relational union covers, so a preceding irrelevant
pair cannot starve the carried set's three-term self-row cover. The existing
pool cap is unchanged. `modelSequence` also accepts an immutable copied path;
tests verify that subsequent caller mutation and empty-path queries cannot
inherit the path's assumptions. These are untrusted proposal/query changes,
not changes to the trusted kernel.

`count-regression-v4` passes **201 tests across 21 files** and `bun run check`
(type checking plus type-aware lint: zero warnings/errors, 945 files). The
pinned vendor gitlinks were staged exactly as for Step 1a. The narrower
`fold-path-v1` suite passes 27 tests; `path-guard-v5`'s test job timed out before
printing a test result, so that receipt is not counted as validation.

Research helpers now construct explicit linear recipes through count-read
bindings, including their lower-coordinate domain guards. Missing bindings
and missing domain assumptions are rejected. A single checked inactive-frame
proof can be reused across all failed activation conditions. In
`shared-guard-v1`, the active leaf checks in **3,615 counted ms**, and the
complete *pinned* activation tree checks after 221 ms of shared inactive work;
its transport to the original unpinned phase still fails at the 5,000 ms cap.
This is not an unrestricted law proof.

The direct original-path experiment avoids that transport. It exposed a real
slice omission: the active assumption `S subset X` was lost together with a
count comparison inside an operation-guarded conjunction. Path-aware
conjunct extraction restores it; the two carried-subset cuts (indices 35/36)
then check. The remaining five-term cut (index 12) reaches a native refutation
with **six hypotheses**, but does not reconstruct a checked tree in the
existing **250 ms local allowance**. `union-core-v1` reproduces this failure
for all eight raw/folded, ordinary/carried-first, unit-order variants. The
exact core and path are `runs/track-m/union-core.json`; the replay command is
in `research/track-m/jobs-union-core.json` (stage its containing directory as
`replay-input`). `jobs-fold-path.json` reproduces the direct full-phase probe.
No time budget was increased and no native refutation was accepted as proof.

**Step 1 remains open.** Neither count law is accepted as proved, the hand set
is not proven, and candidate-generation/3-by-60-second/merge gates have not
been attempted as passed. This checkpoint preserves validated generic fixes
and the exact reconstruction blocker, not completion of Step 1b.

### Step 1b continuation — checked Boolean cores and row-local count proofs

The six-hypothesis union core now has an ordinary checked proof. The untrusted
`boolean-core.ts` helper proposes bounded Boolean membership cases, uses linear
recipes or bounded ordinary search at their leaves, and checks the resulting
tree. It introduces no trusted rule. A standalone source-verified replay took
132 counted ms (`boolean-core-v3`). In the original, unpinned leader phase,
closing the phase path under the remaining constant upper bounds prevents
inactive later actions from leaving spurious offset reads. The five-term cut
then checks in 144 counted ms (`saturated-guard-v1`), although the complete
activation goal in that run remains unproved at its original 5,000 ms cap.

The remaining arithmetic models identify two additional needs: equal-row
cardinality reads must agree, and a post-state bad-quorum count on an unchanged
row is bounded by that row's old-membership count. The latter CInst was already
in the proposal pool; the research proof selector had skipped cross-declaration
post/pre pairs. The selector now considers it. Equal-key read cuts are proved
from the two actual read bindings, transported without fresh whole-goal search,
and checked against the original goal. Composite count terms, including natural
subtraction, are also transported through explicit bindings; missing bindings
and missing domain premises are still rejected by regression tests.

`startup-progress-v1/new-term.log` proves the hardest explicit leader-row case
(a > i, j = i) at **2,599 counted ms**, with 47 count instances. Both equal-key
read cuts check, the residual arithmetic core has 15 hypotheses, and its
transport checks all three count-read domain guards. This is a **diagnostic
row case**, not a whole-law proof: the output labels its extra assumptions and
sets the unrestricted `checked` result to false. The earlier unchanged-target
row case (`leader-rows-v1/frame.log`) checks at 1,883 counted ms. A generic,
checked row-case combiner has unit coverage; its integration, factoring common
cuts before all row cases, is still being tested on the full original phase.

Validation: `count-regression-v5/tests.log` passes **208 tests / 4,411
assertions across 23 files**, including the new Boolean, composite-transport,
row-case, and equal-key-read tests. Its isolated large VM placement is recorded
in `placement.json`. `progress-v1/check.log` passes the full TypeScript and
lint gate, zero warnings/errors (950 files), after `prepare-vendors.sh` restores
the pinned vendor revisions. `checkpoint-check-v1/check.log` repeats the full
check at the checkpoint source and also passes with zero warnings/errors.
The initial unprepared full check failed on absent
vendor trees and found one research helper's extra `withDeadline` argument;
that argument was corrected before the passing full check.

Several diagnostic runs hit their finite job deadlines before printing a proof
result; these are not counted as proof failures or successes. The runner's
command allowance is its job timeout minus 30 seconds: the first short runtime
isolation batch accidentally supplied too small a job timeout and was rejected
before executing its probes. The corrected `runtime-isolation-v2` passes the
basic and composite proxy probes, both Boolean tests, and the field-ceiling
probe. `runtime-diagnostic-v2` independently checks all relevant imports.
An asynchronous snapshot also lost a scratch file while indexing; subsequent
runs wait for the source-manifest receipt before further edits. The runner
replaces stderr on process timeout, so progress diagnostics now use stdout;
missing stderr markers alone do not identify a startup stall. The factored
proof diagnostic retains its 5,000 ms counted and 60,000 ms internal wall
limits; its outer runner allowance includes setup and result-collection time.

**Step 1 is still open.** No count law or complete given hand set is newly
accepted. The 3-by-60-second, candidate-generation, and downstream merge gates
remain unpassed. All new proof search remains untrusted and every accepted
recipe is checked by the existing kernel; no proof budget was increased.

### Step 1b: action guards, inactive-path reuse, and witness-key congruence (2026-11-08)

The machine-shaped guard proposal now selects the requested action and its
active carried set, rather than assuming the leader action or the first input
map. Per-member equalities also propose field ceilings; these remain ordinary
checked cuts. With both carried inputs considered, the existing capped pool
already retains the required Q2/request-row union: no pool-size increase or new
union family was necessary (`action-guard-v1/inventory.log`).

The first reconfiguration failure was an inactive-frame probe consuming its
leaf allowance before trying the actual false-guard path. The shared probe now
stops after two unsuccessful cuts, and a concrete inactive-path tree is reused
only after transport and a fresh kernel check. In `reconfig-v2`, all inactive
paths check; the remaining failure is in the active count proof. The natural
row-offset key and direct member key then exposed a missing key-congruence
proposal. Boolean-core search now proposes equal keys sharing the same witness
and checks both ordering branches. Its regression proves the natural-subtraction
alias only under the row-equality path and rejects the unrestricted goal.
Row-dependent post-count cuts are deferred to the structural row cases instead
of first trying them in a context where they are false.

`row-keys-v1/leader.log` checks the primary-equal and different/equal row classes
(reporting 1,233 and 1,217 counted ms), but not different/different; the full
original branch remains **unknown**. `row-keys-v1/reconfig.log` likewise remains
unknown at the active Q2 union core. These were non-timing diagnostic placements,
not timing-gate runs. The unchanged limits are 5,000 counted ms and 60,000 ms of
internal wall time. The earlier isolated timing request for the superseded
prototype remained queued; it was gracefully cancelled through its exact client
PID after the non-timing diagnostic falsified that prototype. The scheduler
confirmed removal of that request, without cancelling other workloads.

Validation at this checkpoint: `step1-key-check-v1/tests.log` passes **214 tests /
4,422 assertions across 24 files**; `check.log` passes TypeScript and type-aware
lint with zero warnings/errors (952 files). `row-keys-v1/tests.log` separately
passes all 18 directly affected tests. Section 1.5 was reread: its completed
bounded induction and encoding checks still support I-A/P*, with no stated
fallback triggered. **Step 1 and every downstream gate remain open.**

### Step 1b: checked source facts and witness-domain cuts (2026-11-08)

The residual Q2 union core now checks in isolation at **181 counted ms**, within
its unchanged 250-ms helper bound (`boolean-replay-v6/replay.log`, guided mode).
The score, membership-first, and key-first controls still fail. The decisive
proposals are checked cuts for the source's own forced facts and for arithmetic
row-update guards implied by the row equality and witness domain. These do not
consume the eight Boolean-candidate slots. Discovery still reads the original
syntax: pinning a nonlinear fact must not hide the membership conditions inside
it. Every opposite branch and the final source tree are checked by the kernel.

Portable captures now include the semantic expressions behind process-local
term columns. The first replay without these definitions failed with an unknown
term column; that invocation is not counted as a proof result. The corrected
replay re-registers the expressions and renames the captured path consistently.
The negative regressions continue to reject a missing subset premise and an
unjustified row equality. A frame's new Boolean helper is opt-in; enabling it on
the previously working inactive-frame probe was tested, failed, and reverted.

`row-frames-v3/reconfig.log` checks the Q2/request-row five-term cut in the actual
branch at 284 counted ms, including source transport. The full reconfiguration
branch remains unknown: the current certificate has no pair equating the copied
row's post-cardinality with the parameter set's cardinality. The existing
request-frame proposal option is the next item to exercise. The leader's first
two row classes still check; its final class reaches the unchanged 60-second
wall guard, so no complete branch or law is claimed.

Validation: `step1-domain-check-v1/tests.log` passes **219 tests / 4,433 assertions
across 24 files**, and `check.log` reports zero warnings/errors (953 files).
All probes retain the 5,000-ms counted goal cap, 250-ms Boolean helper cap, and
60,000-ms diagnostic wall guard. **The complete given hand set and downstream
gates remain unpassed.**

### Step 1b: request frames, numeric aliases, and capped partition selection

The copied-row cardinality now receives both checked comparisons with the
request-set cardinality. Membership syntax is normalized before selecting these
request-frame proposals. A structural post-count range bound is retained too.
The next numeric models identified disconnected original guard count cells,
missing request partitions, and an input-keyed row view rejected as non-stored.
The numeric slice now keeps only read bindings reached from its incoming path
(including natural-subtraction columns); source transport still checks their
read domains. A binding that substitutes to zero is reconstructed from opposite
source rows with positive weights. The initial zero-weight attempt failed the
checker and its new regression, and was replaced, not accepted.

The existing sixteen algebraic slots now deduplicate equivalent proposals and
rank pointwise Boolean partition identities ahead of unrelated triples. Request
partitions and exact pre-count aliases are retained without increasing the cap.
Carried-set comparisons also recognize their declared input-keyed row views.
Every resulting count cut and complete source tree remains kernel-checked.

Pre-rebase baseline: `request-frames-v6/reconfig.log` remains unknown at **5,028
counted ms / 31,645 wall ms**. `leader.log` remains unknown at **5,009 counted ms /
35,037 wall ms**; its equal-row class checks in 417 counted ms, but the next class
hits its 1,500-ms slice. Neither full branch nor the given hand set is proved.
These are diagnostic placements, not timing-gate runs. All original time limits
remain unchanged. Earlier request-frame iterations and the minimal proxy-path
fixture are retained as diagnostics.

`step1-request-check-v2/tests.log`: **226 tests / 4,452 assertions**, all passing
across 24 files. `check.log`: TypeScript and type-aware lint pass, zero warnings
or errors on 954 files. The request-frame batch separately passes 49 focused
tests. Section 1.5 was reread and no design falsifier has appeared.

Coordinator update: checkpoint this work, then rebase onto Track P **699b5160**,
keeping both lanes' changes. After the rebase, repeat static checks, focused tests
and this step-1 replay; future merge gates also require paxos_epr 3/3 and paired
IC3Syn 29×3 against **699b5160**, not main. Those post-rebase gates are pending.

### Track P integration checkpoint (2026-11-08)

The pre-rebase checkpoint was `a8d69064`; the replayed commit is `de9dbdd9`.
`claude/track-mldr` now descends from **699b5160**. Conflicts were resolved by
retaining both lanes: Track P's support/carry/relevance modules are byte-for-byte
unchanged from the base, its supported preflight/direct proofs and goal-local
helper contexts remain, and its deadline checks also bound Track M's additional
partition/union proposals and packed-key witness scans. Both lanes' test lists
and reports are retained.

`rebase-check-v1` passes TypeScript and type-aware lint (zero warnings/errors,
1,014 files), **226 Track M tests / 4,452 assertions** and **67 Track P tests /
1,071 assertions**. `rebase-request-v1` repeats the same branch proof status and
counted work as the pre-rebase baseline: reconfiguration **5,028 counted ms**,
leader **5,009 counted ms**, neither source goal proved. Their diagnostic wall
times were 25,755 and 29,323 ms; this wall reduction is not a closed proof gap.
The leader's equal-row class still checks in 417 counted ms and the next class
still exhausts its 1,502-ms slice. No step-one completion is claimed.

The original strict Paxos harness passes **3/3** on the merged tree
(`rebase-paxos-v1/paxos-r{1,2,3}.log`): all return `search.verdict = proven` and
`STRICT_EXIT=0`. Measured harness wall times are **26.690 s, 23.451 s, 29.947 s**;
all three jobs ran alone on their VMs with no co-tenants. These results protect
Track P's target on this tree. The paired IC3Syn 29×3 comparison against 699b5160
has not yet run and remains a merge gate, along with the unfinished MLDR gates.

### Step 1b: natural-subtraction cases and the shorter partition basis

Two clamping-threshold proposals now give an ordinary checked arithmetic tree
for the overlap contradiction. The new helper is research-only and opt-in, with
at most two splits and the unchanged 400-ms arithmetic recovery allowance.
The initial tiny fixture omitted the original guard expression, leaving its
path-only term columns uninterpreted; it was corrected to include that source
guard and explicit natural-number premises. The missing-union negative still
fails, as required. No term definition or arithmetic fact was trusted.

The full inventory exposed two redundant four-term identities taking the slots
needed by `cfgSize(a) = xm(a,i) + xn(a,i)`. Shorter three-term identities now take
precedence within the same sixteen algebraic slots. An adversarial regression
checks this against longer true identities and unrelated candidate noise.

`natural-cases-v3` checks all three logical reconfiguration row classes in one
ordering, then runs out of the goal allowance while covering the opposite
ordering. Its complete source goal is still not proved. Deferring duplicate
row-tree checks to the composing field proof preserves the final kernel check
and a negative regression rejects an unchecked deferred proposal. The v4 full
results remain unknown: reconfiguration 5,106 counted ms / 45,368 wall ms;
leader 5,000 counted ms / 39,489 wall ms. Earlier v2/v3 receipts independently
check the leader's equal and different/equal row classes. These are not timing
gate successes.

`active-rows-v1` is explicitly assumption-scoped. Its last reconfiguration row
checks at 1,963 counted ms; the leader's last row is still unknown. A portable
three-hypothesis Boolean frame core was captured for the latter; the next
hypothesis is a missing witness-related source premise in the reduced core.
A bulky Boolean dump exceeded the log tail in v2, so v3/v4 disable only that dump
and retain complete bounded verdicts.

`natural-checks-v1`: **229 Track M tests / 4,464 assertions** and **67 Track P
tests / 1,071 assertions** pass. TypeScript and type-aware lint report zero
warnings/errors across 1,016 files. Step 1 and the paired 29×3 gate remain open.

### Step 1b: actor-diagonal ceilings and a checked leader-action branch

The small failed leader core omitted the active witness's can-vote premise.
Restoring only existing source hypotheses for that witness is sound, but was
not sufficient: its next model identified the witness with the actor and left
the actor's old configuration term above its current term. The certificate had
no actor/actor instance. `countLawSeeds` now optionally prioritizes request
self-tuples within the same 32-tuple cap. The corresponding count comparison
proves the actor's own ceiling, alongside the target-row ceiling. This option
is currently selected by the research replay, not enabled as production policy.

Field-domain cuts are proved from the source before conditional ceilings are
linearized. Direct bounded arithmetic proves these domains, and the eight
pre-state partition instances now check directly without a native query.
Row-dependent carried comparisons are deferred to row children; duplicate
conditional ceilings and pre-only arithmetic queries are avoided. Source
hypotheses are never fabricated. Deferred children/cuts remain proposals until
the complete guard tree passes the unchanged checker. Negative regressions
still reject missing subset/union premises and unchecked proposals.

The leader-action entry now checks, including all row orientations and inactive
guard cases. `deferred-arithmetic-v1` is an isolated, pinned-large run (placement
recorded, zero co-tenants): **3,626 counted ms / 80,200 wall ms**;
`branches[4] = true`, `guard-complete.checked = true`. The top-level `checked`
remains false because this `LAB_CASE=4` run intentionally omits all other action
entries. This is a checked encoded action branch, not an admitted Inv* law or a
full hand-set certificate, and its wall cost is still far above the desired
production cost.

The same isolated batch leaves reconfiguration open at **5,086 counted ms /
33,166 wall ms**: every row tree is proposed, but final source transport does
not complete in the allowance. `source-active-v1` tests removing the redundant
active premise and relying on the original goal/path: leader still checks,
but reconfiguration's first row then fails. That route remains diagnostic and
is not the default. Earlier large Boolean dumps exceeding the 400-KB worker
stdout cap were replaced by bounded premise-delta and tree-rejection traces.
No missing receipt or timeout is counted as a proof.

`diagonal-checks-v4` passes **236 Track M tests / 4,492 assertions**, **67 Track P
tests / 1,071 assertions**, and TypeScript/type-aware lint with zero
warnings/errors on 1,018 files. One earlier shared-VM Track P run timed out two
five-second carry tests; the unchanged command passed with an isolated CPU
reservation and in the subsequent complete v2/v3/v4 checks. No timeout or proof
budget was raised. Step 1, production generation, and the downstream gates
remain open; the next work is the remaining count proof and its source-context
cost.

### Step 1b: smaller instance contexts close both hard action entries

`LAB_THIN_FIELD_CONTEXT=1` omits initial non-count instances with additional
quantifier keys and their field bridges for a count target. It does **not**
remove any law from the hand set, add a premise, change the target, or prevent
ordinary model-guided instantiation from recovering an omitted instance. It
asks the prover to use less of the available precondition. The option is a
research proposal strategy, not yet a production default.

`thin-fields-v1` (isolated, pinned large, zero co-tenants) checks the encoded
leader entry in **2,827 counted ms / 77,262 wall ms** and the encoded
reconfiguration entry in **4,152 counted ms / 81,685 wall ms**. Both complete
source guard trees check and the selected `branches` entry is true. No whole
Inv* or hand-set certificate is claimed: each run selects one action, the
symbolic overlap instance is still supplied by the diagnostic harness, and
wall-time source checking remains too expensive.

`remaining-cases-v1` surveys the other entries with the same context and fixed
five-second allowance. Entries 2, 3, and the final unchanged-action remainder
check (1,276 / 1,851 / 316 counted ms). Setup entries 0 and 1 and the send entry
6 remain open at the allowance. Together with `thin-fields-v1`, five of eight
entries have checked encoded trees; these are separate replays, not a combined
certificate. The setup countermodel keeps both the target config term and the
actor term at zero, suggesting that the singleton empty-post-count witness
already in the certificate must be used; the current field helper filters
those singleton witnesses out.

`one-row-v1` shows that dropping the secondary-key split alone does not prove
reconfiguration. `field-frames-v1` and `folded-frames-v1` add checked-proposal
attempts for an unchanged target field, but still fail to close that broader
row branch. Those options remain diagnostic and disabled by default. Three
regressions test frame candidate selection, the valid equality case without
fixing the target key, and rejection when the supporting equality is absent.

`thin-fields-checks-v1`: **239 Track M tests plus 67 Track P tests pass**;
TypeScript/type-aware lint reports zero warnings/errors on 1,020 files. The
latest Section 1.5 confirms no design falsifier: P* and the bounded induction
checks still support I-A. Step 1 remains the gate; no later candidate family
or downstream merge gate is claimed complete.

### Step 1b: setup emptiness recovered; send copy remains open

The setup models had zero target configuration term but a positive post-state
count. The ordinary certificate already contained the required singleton
`+postCount <= 0` CInst; the field helper excluded one-term proposals.
`LAB_EMPTY_COUNTS=1` now attempts these for post-count definitions with field
comparisons. `empty-counts-v1` checks setup entries **0 and 1** in **627 / 711
counted ms**, respectively (31,584 / 35,248 wall ms). A source-level counted
regression checks the zero-threshold proof and rejects the same conclusion
without that premise. Seven of eight action entries now have checked encoded
trees in individual replays, with their recorded options; no combined Inv*
certificate is claimed.

The remaining send entry exposed three concrete proposal gaps. Its activation
contains a disjunction, so the conjunction-only guard splitter returned before
trying it. Boolean guard coverage now follows both branches and checks the
complete source tree. The row selector then chose the copied **source**, not
the destination: live Boolean-valued writes must ignore dead arms and must not
mistake membership-read keys for write-index comparisons. Finally the selected
certificate lacked `post bq[a,j]` against `pre bq[i,j]` / `pre bq[i,i]`, and
`post cfgSize[a]` against `pre cfgSize[i]`. `focusCountCert` has an opt-in,
16-cross-pair-capped same-definition copy family, with both directions as
ordinary CInsts. The equal-primary row can also split its secondary key.
These options and their default-preservation/negative tests are checked, but
are not yet a production policy.

`active-writer-v2` confirms destination selection, and `copy-frames-v1` reaches
the correct equal/equal row but cannot reconstruct the copy count comparison.
`copy-model-v1/v2` captures its precise remaining failure: the model can set the
post indicator to 1 and pre indicator to 0 while source/destination keys are
fixed. The key-order candidates, source scalar-domain recovery, and direct
copy-point retries do not yet close it. The opaque column definitions identify
the unexposed numeric/Boolean indicator conditions as the next diagnostic
surface; these are not protocol counterexamples or accepted proofs.

`copy-checkpoint-v1` passes **253 Track M tests + 67 Track P tests**, and
TypeScript/type-aware lint reports zero warnings/errors on 1,020 files.
Independent rechecks still accept leader and reconfiguration in **2,827 /
4,152 counted ms** (85,037 / 83,458 wall ms). The long wall times remain a
problem, not a passing end-to-end timing gate. No budget, trusted-kernel rule,
safety law, or invariant was weakened.

Coordinator baseline update: remaining gates compare with **main 8610af26**.
The worktree already includes 699b5160; `git diff 699b5160 8610af26 -- core kernel
scripts` is empty. The later main commit changes reports/research packaging,
not the Track P code already present here. Step 1 and all downstream gates
remain open.

### Step 1c: checked copy indicators; source-instance size is decisive

The copy point prover now enters conditional operands even when their enclosing
comparison is forced, while still pruning inactive condition arms. Arithmetic
read-key closure emits an ordinary refutation for the opposite of each proposed
key fact; nothing is assumed by the checker. After key closure, only the unused
slots in the existing eight-choice pool are refreshed. The copy selector keeps
unchanged coordinates and shares its existing 16-pair cap across result counts,
so the larger quorum family cannot starve configuration-size copies. New tests
cover both directions, packed offsets, missing version guards, and unfair pools.

`copy-frame-points-v1` and `copy-deferred-transport-v1` construct all send row
cases but reach the external 90-second command cutoff during source checking.
The latter removes redundant intermediate transport checks only for callers
that check the complete original-goal tree. Default transport checking remains
on; a regression explicitly shows that a deferred invalid proposal is rejected
by the ordinary checker. Search and wall limits were not increased.

`copy-tree-metrics-v1` quantifies the remaining cost: **4,435 nodes / 2,218
leaves**, with **466 source hypotheses**, before the final source check. It
still times out, so this is a proposed tree, not an accepted proof. An attempted
reduction to only conditional-guard cuts passed unit tests but failed the real
equal/equal copy row (`copy-relevant-pins-v1`); that change was reverted.

A diagnostic keeps only the 17 count instances used by the previous proposal,
before witness flags and the encoded goal are built. `copy-thin-instances-v1`
then checks **the complete send action entry**, including all 18 row leaves and
both activation alternatives: `branches[6] = true`, `guard-complete.checked =
true`, **2,664 counted ms / 51,578 wall ms**. Its source goal has **140
hypotheses**; the tree has 4,359 nodes / 2,180 leaves. This is not an admitted
Inv* law or a whole hand-set certificate: every other action entry is omitted
in that run. The numeric keep-list is diagnostic, not a production policy. A
structural copy-key starting subset now replaces that numeric diagnostic:
`copy-compact-v2` checks the send entry with **22 instances / 172 hypotheses**,
**3,552 counted ms / 58,805 wall ms**. Sources are inferred from same-map value
branches, excluding inputs seen only in guards. It retains pre-state partition
instances, post-empty candidates, same-key frames, and coordinate substitutions
by one source input. It is an opt-in starting subset, not a replacement for the
full fallback pool or a claim about every kind of action.

`copy-checkpoint-v2` passed **270 Track M tests + 67 Track P tests**, but its
leader repeated a whole-tree check and hit the wall cutoff. The replay now
keeps unchecked proposals distinct from acceptance and delegates to one final
source/MC check. `copy-verification-v1` checks leader, reconfiguration and the
numeric-subset send entries at **2,827 / 4,152 / 2,664 counted ms**, respectively;
wall times are **36,292 / 41,688 / 41,480 ms**. The full, unthinned send still
hits its 90-second external cutoff; that failed job is not counted as a proof.

Final source validation (`copy-final-checks-v2`, tree `676f0c11613b`): **274 Track
M tests + 67 Track P tests pass**, and `bun run check` reports **zero warnings /
errors on 1,022 files**. The structural send receipt is `copy-compact-v2`
(tree `1db03186879e`). Reproducible job manifests are
`research/track-m/jobs-copy-checks.json`, `jobs-copy-verification.json`, and
`jobs-copy-compact.json`; replay data is the unchanged
`runs/track-m/canonical-capture-v1/fixtures` snapshot.

All eight action entries have now checked in individual replays with their
recorded options. They have **not** been assembled into a complete Inv* proof,
the full nine-law given set has **not** passed, and no production 3-by-60-second
or downstream merge gate is claimed. No trusted-kernel rule, original invariant,
safety law, or proof budget was changed.

#### Combined-action check after the copy checkpoint

Checkpoint commit: `ba821e48`. `all-actions-v1` removes the isolated action
selector and enables the already checked empty-count proposals, but retains
one **5,000-ms counted goal allowance**, the **60,000-ms diagnostic wall guard**,
and the unchanged external command limit. It is **not complete**: three early
source trees are proposed, later active cases remain open, and checking the
available partial branches reaches the external **90-second cutoff** before a
final result is printed. No proposed tree from that run is counted as a newly
accepted branch. The source context still has 466 hypotheses. Reproduction:
`research/track-m/jobs-all-actions.json`, receipt/tree `5e2838a0aa6e`.

This is the remaining evidenced wall: action-specific checked proofs and the
compact copy selection have not been integrated into a complete, sufficiently
small counted induction query. The existing production focused-count recovery
(`core/count-focus-proof.ts` / `core/count-cases.ts`) still needs that integration
and a checked whole-law result; summing isolated successes is not a proof.
Step 1's all-laws-kept and per-goal timing gates remain unpassed, so no later
family-generation or downstream merge gate was attempted.

### Wall-time profile requested by the coordinator

The integration work is paused until action wall time is small. Research-only
wrappers measure exclusive wall time (subtracting nested measured phases), with
CDCL's existing native unfold timer and a preload timestamp that includes module
loading. They do not replace the checker, change arguments, or change budgets.
`wall-profile-v1` uses the exact `copy-verification-v1` leader settings on an
isolated large VM. Profiled/control runs both check action 4, consume **2,827
counted ms**, and produce the identical final tree: **1,485 nodes, 743 leaves,
depth 59**. Their replay walls are 43,203 / 41,829 ms, respectively. The profile's
end-to-end time including loading/output is **43,325 ms** (timing tree
`c694f86f1242`; placement saved with the run).

| Exclusive phase | Wall ms |
| --- | ---: |
| Fixture reading | 0.528 |
| Instance/certificate generation | 56.225 |
| Goal construction | 12.028 |
| CDCL/model/core search | 1,884.107 |
| Native CDCL DAG unfolding | 0.000 |
| Direct arithmetic search | 133.779 |
| Prover row construction outside the above calls | 702.021 |
| Boolean/tree reconstruction and proposal control | 866.346 |
| Transport/reindexing | 5,116.291 |
| Intermediate source checking | 11,656.450 |
| Final source-tree checking | 22,825.043 |
| Final checkMC | 0.000 (not called in an isolated, incomplete-law replay) |
| Profile bookkeeping | 7.229 |
| Loading/output/unattributed residual | 65.224 |

**Checking is 79.6% of wall time; checking plus transport is 91.4%.** The gap
between counted time and wall is not expensive fixture construction or native
CDCL DAG unfolding. The final checker reconstructs rows for all 743 leaves.
An isolated action is still not a complete MC certificate: its final acceptance
is the original-goal `check(goal, tree, branchRoot)`; the profile does not pretend
that `checkMC` ran.

Tree sizes at phase boundaries (totals are work processed, not distinct nodes):

| Phase | Tree calls | Total nodes / leaves processed | Largest tree nodes / leaves / depth |
| --- | ---: | ---: | ---: |
| Search-returned trees | 51 | 593 / 322 | 95 / 48 / 14 |
| Boolean reconstruction | 12 | 596 / 304 | 127 / 64 / 20 |
| Row-case reconstruction | 1 | 803 / 402 | 803 / 402 / 30 |
| Guard composition | 1 | 1,481 / 741 | 1,481 / 741 / 57 |
| Transport | 155 | 4,059 / 2,107 | 1,149 / 575 / 50 |
| Intermediate checks | 122 | 1,484 / 803 | 191 / 96 / 20 |
| Final source check | 1 | 1,485 / 743 | 1,485 / 743 / 59 |

Leaf labels are structural provenance, not different trusted rules: a *count-row
leaf* is below the failing side of a CInst inequality or a split mentioning its
arbitrary row witness; other leaves are *arithmetic/control*. Both end in ordinary
linear refutations. The classification is exhaustive and the two columns sum to
the leaf count; it is not a count of a new trusted proof rule.

#### All eight action shapes (baseline, before wall optimizations)

`action-profiles-v1` (tree `892586f686fc`) runs all eight **individually** on
isolated large VMs with their previously checked settings. Every selected source
branch checks. All rows retain the five-second counted allowance and original
wall limits. Wall below includes module loading, fixture/build work, proof work,
and final source checking. No row invokes `checkMC`, because each is an isolated
action of an incomplete whole-law replay.

| Action | Counted ms | Wall ms | CInsts | Nodes | Leaves | Depth | Count-row leaves | Arithmetic/control leaves |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0: pick initial configuration | 627 | 24,405 | 69 | 515 | 258 | 37 | 172 | 86 |
| 1: copy during setup | 711 | 28,689 | 69 | 525 | 263 | 37 | 172 | 91 |
| 2: start | 1,276 | 33,381 | 69 | 715 | 358 | 39 | 273 | 85 |
| 3: update terms | 1,851 | 35,411 | 69 | 839 | 420 | 35 | 354 | 66 |
| 4: become leader | 2,827 | 47,163 | 53 | 1,485 | 743 | 59 | 597 | 146 |
| 5: reconfigure | 4,152 | 55,417 | 69 | 1,587 | 794 | 59 | 671 | 123 |
| 6: send configuration | 2,664 | 53,931 | 17 | 4,359 | 2,180 | 53 | 2,056 | 124 |
| Remaining/no-op inputs | 316 | 1,905 | 69 | 9 | 5 | 4 | 4 | 1 |

Action 6 uses the explicitly documented 17-instance diagnostic, matching the
4,359-node reference. It is not a generated production policy; the separately
checked structural subset has 22 instances. This table is not an assertion that
all actions fit one shared protocol deadline.

Checking dominates actions 0–5 (approximately 78–85% of wall). In action 6,
source checks take **32,046 ms**, transport **11,567 ms**, and explicit prover row
construction **5,508 ms**; these three account for **91.1%** of its wall. The
remaining/no-op case is already about two seconds. The next work is therefore
smaller/less-repeated checked reconstructions and source contexts, **not** an
integration into `count-focus-proof.ts` or any larger search budget.

The profiler's own bookkeeping is 2–21 ms per action; its source-check and
transport timings are disjoint. Run manifests: `research/track-m/jobs-wall-profile.json`
and `research/track-m/jobs-action-profiles.json`. Type/lint and all 57 focused
profiling/helper tests passed in the paired leader batch.

#### First wall optimizations: exact pin reindexing and deferred cache checking

`wall-prune-v1` (tree `2a0a9d5cf8c2`) tests a proposal-only exact row reindexer:
when a forced numeric split can be removed without losing any row read by the
proof, reindex the retained child and omit the redundant split. No solver call,
new inference rule, or budget increase is involved. Failed attempts leave the
original split intact. `LAB_PRUNE_PINS=1` opts in inside the Boolean helper.
Cached row trees now honor their existing `deferToCaller` option rather than
rechecking a subtree that the caller will check again in the complete tree.
Default nondeferred behavior is unchanged; negative tests show that deferred
invalid proposals are still rejected by the mandatory final check.

| Leader variant | Counted ms | End-to-end wall ms | Nodes / leaves / depth | Intermediate / final checking ms |
| --- | ---: | ---: | ---: | ---: |
| Cache-check deferral only | 2,827 | 41,420 | 1,485 / 743 / 59 | 9,440 / 23,135 |
| Deferral plus pin pruning | 2,824 | 38,174 | 1,415 / 708 / 54 | 8,886 / 20,734 |

Both source checks pass. The pruner removes 36 local forced splits (35 leaves in
the final composed tree); 16 local splits remain necessary. The net saving is
modest, **not the few-second target**. The pruner itself takes 48 ms exclusive;
additional row materialization is visible separately. Type/lint and normal and
pruning-enabled focused tests pass. This does not authorize integration: final
checking of the still-large source context remains dominant.

#### Checked source slicing and complete-tree deferral

The fully indexed, hash-audited `wall-staged-v1` run (tree `4c5d46d9c43d`)
passes **285 Track M tests, 67 Track P tests, and type/lint**. All three leader
variants still check. The default research control here enables pin pruning,
source slicing, and explicit nested-check deferral, but not derived-lemma
pruning or action-live witness seeding.

| Leader variant | Counted ms | End-to-end wall ms | Final source hypotheses / CInsts | Nodes / leaves / depth | Intermediate / final check ms |
| --- | ---: | ---: | ---: | ---: | ---: |
| Control | 2,824 | 15,446 | 73 / 23 | 1,415 / 708 / 54 | 39 / 6,010 |
| Also prune derived lemma cuts | 2,822 | 18,634 | 65 / 20 | 1,127 / 564 / 41 | 41 / 4,903 |
| Also seed only action-live carried witnesses | 2,752 | 18,876 | 65 / 20 | 1,127 / 564 / 41 | 44 / 5,031 |

Source slicing selects existing count instances, read bindings, universal-flag
tuples and law tuples from proof support. Its rebuilt source must be a literal
subset of the original, every retained input row is reindexed exactly, and the
ordinary kernel checks the resulting tree. A failed proposal falls back to the
original checked source. It does not introduce a fact or weaken the claimed law.
The slimmer per-action certificate remains a diagnostic: a complete machine
certificate must still be assembled and checked by `checkMC`.

Derived-cut pruning saves 144 leaves but spends additional time rebuilding rows,
so it is **not enabled by default**. Action-live seeding reduces the initial
source from 286 to 230 hypotheses in this run but does not improve the final
certificate. It remains an optional candidate-only policy. Nested deferral
applies only when an enclosing caller explicitly takes responsibility for the
complete-tree check; intermediate checking falls to about 40 ms, with final
checking still mandatory. All proof and wall budgets are unchanged.

Two intermediate batches (`wall-deferred-v1`, `wall-live-v1`) failed type checking
with an obsolete helper arity in their snapshots; their timing comparisons are
superseded. `wall-lemmas-v1` audited the new count helper but still had an obsolete
natural-case signature. The fully indexed run above prints all affected helper
hashes and passes the gate; no success claim relies on those failed snapshots.

This is substantial but still **not a few-second action**, not a complete-law
proof, and not the 3×60-second protocol gate. The coordinator's next direction is
to implement Fable's Section 4 core-ranked instance selection as the default in
`core/count-cases.ts` / `core/count-focus-proof.ts`; no certificate-level trusted
lemma rule is authorized.

#### Arithmetic-core selection in the default finite-input recovery

Core implementation: **55b5846a**. `selectCountBounds` adds candidates in the
existing certificate order, asks the closing arithmetic for its core, and treats
that result only as a proposal. `proveCountCases` derives each selected witness
bound under the real case path; a failed derivation excludes that candidate and
repeats selection. An unknown arithmetic oracle falls back to the existing
recovery, not to an assumed bound. The returned certificate contains the union
of the actually used case instances. Whole tuples for discarded witnesses are
removed; newly seeded universal-flag tuples for retained witnesses survive.
`proveFocusedCounts` retains that certificate instead of regenerating the full
pool. Finite-input recovery now runs by default (`GDP_COUNTS_FOCUS=0` remains an
explicit opt-out); all proof and wall allowances and the final kernel gate are
unchanged. The tests cover failed candidates, false laws, whole-tuple removal,
new flag witnesses, default enablement, and full counted-law certificate checking.

The research loop uses the same arithmetic selector, without `LAB_NEEDED_LEMMAS`
or a protocol/instance-index list. It also remembers confirmed bounds across
reselection: re-deriving one on its own false branch was both redundant and a
source of exhausted attempts. Count-sensitive outer row guards retain their
ranked pre-state fallback; count-free row skeletons derive no unused outer
chain. An already-unknown fallback is not queried again after every rejection.
All of these are untrusted proposal/control changes.

**Final asserted matrix:** `ranked-final-v1`, tree `84b20ff97766`, isolated
`large` VMs with placement saved in the run. Each action command now ends with
`assert-action.ts`: it fails unless the selected branch's actual final source
check is true and counted time is at most 5,000 ms. Shell exit alone is no longer
mistaken for a successful proof. The following is the raw-source diagnostic,
without source slicing or nested-check deferral, so it is comparable in shape to
Section 4's measurement. Wall is the profiler's end-to-end time including loading
and final source checking, rounded to milliseconds; batch queue time is excluded.

| Action | Counted ms | Wall ms | Nodes | Leaves | Depth | Count-row leaves | Arithmetic/control leaves | Final source check ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0: pick initial configuration | 558 | 11,134 | 335 | 168 | 27 | 82 | 86 | 4,089 |
| 1: copy during setup | 616 | 11,895 | 345 | 173 | 27 | 82 | 91 | 4,954 |
| 2: start | 640 | 12,048 | 399 | 200 | 26 | 115 | 85 | 6,727 |
| 3: update terms | 1,194 | 15,774 | 551 | 276 | 24 | 210 | 66 | 8,899 |
| 4: become leader | 3,524 | 35,257 | 1,593 | 797 | 51 | 651 | 146 | 21,134 |
| 5: reconfigure | 2,997 | 51,569 | 1,327 | 664 | 59 | 541 | 123 | 26,641 |
| 6: send configuration | 2,753 | 50,900 | 3,163 | 1,582 | 44 | 1,458 | 124 | 26,335 |
| Remaining/no-op inputs | 316 | 2,957 | 9 | 5 | 4 | 4 | 1 | 249 |

All eight selected branches check. Send exactly reproduces Fable's 3,163-node,
1,582-leaf result from the structural 22-instance source, versus 4,427 / 2,214
before selection: 28.6% fewer nodes/leaves. This is not a uniform improvement:
leader grows from 1,485 / 743 to 1,593 / 797, and its counted time increases.
Cross-VM wall times are not a paired speedup claim. Final source checking still
takes 21–27 seconds on the hard actions; this is not the few-second goal and
cannot establish the whole-protocol 60-second gate. Individual action replays
do not call `checkMC` on a complete law.

Validation: **294 focused/Track M/port tests, 67 Track P tests**, all passing.
The matrix's initial type-check job correctly failed because the new standalone
assertion script lacked module scope for top-level `await`; adding `export {}`
fixed it. `ranked-postcheck-v1`, tree `2b79b1d05bcc`, passes type/lint with **zero
warnings and errors**. This utility-only repair does not change the measured
proof code. The audited hashes in the action logs are:

- `core/count-cases.ts`: `7b728b8a1314dccfeb59e2ab6865c8309522cf1d0b490e4f3bc0ff031708df64`
- `core/count-focus-proof.ts`: `854f9b4591519418ab52a03cfacf0bb8d19357f4df96aff1cb971f1929c5e1ed`
- `core/counts.ts`: `9f28e1f73f71b93d04d32e51f81338d77c8e290583ca431cedcbf4471d40e5d6`
- `research/track-m/field-bound-lemmas.ts`: `b8139b2c8f5cf339302565899da2ff8716c6e2a5c020319d85b60b1ec2e74684`

Failures are retained: `ranked-actions-v1` checks only six actions; leader and
reconfiguration remain open despite process exit 0. `ranked-retry-v1` still
repeats confirmed bounds. `ranked-retry-v2` restores leader but reconfiguration
exhausts its share repeatedly querying an unknown fallback. `ranked-retry-v3`
checks both after confirmation tracking and fallback reuse. Early retention-test
fixtures had naming/raw-expression setup errors; the final fixtures pass and
verify the returned certificates through the original kernel.

Reproduce the asserted matrix and validation:

```sh
supercomputer run --jobs research/track-m/jobs-ranked-final.json \
  --out runs/track-m/ranked-final-v2 --class gate --timing --vm-type large \
  --data runs/track-m/canonical-capture-v1/fixtures:replay-input
supercomputer run --jobs research/track-m/jobs-ranked-postcheck.json \
  --out runs/track-m/ranked-postcheck-v2 --class gate --vm-type large
```

The standalone production-law probes are separate from this matrix. Step 1,
the three 60-second production repeats, and the downstream merge gates are **not
claimed passed** by these action proofs.

#### Production-path follow-up: Step 1 is still blocked

`ranked-production-v1` (tree `ad9bd0274a28`) calls the existing
`verify-focused.ts` against the canonical captured hand-set input, with
`GDP_COUNTS_GIVEN=1`, the new default core recovery, and the original 5,000 ms
counted allowance. Unlike the action diagnostics, it asks for a complete
counted-law certificate and checks it with the original kernel. All five jobs
finish normally; **none returns a proof**. The counted figures include the
existing search-clock granularity at the stopping boundary; no allowance was
raised to accommodate the small overshoot.

| Published obligation | Counted ms | Wall ms | Complete proof / checked |
| --- | ---: | ---: | --- |
| one primary per term | 5,005 | 3,914 | no / no |
| Inv3915: primary newest | 5,008 | 4,107 | no / no |
| Inv1758: row agreement | 5,006 | 5,277 | no / no |
| Inv2973: quorum overlap | 5,001 | 4,427 | no / no |
| Inv*: quorum term backing | 5,006 | 5,574 | no / no |

The traces demonstrate that the default selector is live, not an opt-in-only
research result. Safety and newest exclude candidate 1, then candidate 2 when
their actual witness derivations fail, and later stall on the send action's
ordinary `grow`. Row agreement also excludes candidate 1 and stalls on the
reconfiguration path. The overlap oracle returns an unknown fallback on its
16-candidate pool. Quorum term backing reaches a nine-candidate selection,
excludes candidate 5 after failed derivation, and still leaves the final send
case open. These are recorded proposal/derivation gaps, not accepted arithmetic
assumptions. Logs include every selection, exclusion, fallback and final result.

**Remaining wall:** the generic selector and retained certificate do not yet
supply the research loop's successful field/guard/row witness derivations to the
ordinary production recovery. The isolated action trees still take tens of
seconds to reconstruct/check against their sources. Neither that integration
gap nor the wall cost has been solved by selecting fewer instances. No trusted
lemma-sharing rule was introduced. Consequently Step 1's all-laws-kept gate,
the 3x60-second original-harness target, and the downstream merge gates remain
unpassed; a whole-protocol rerun would not replace these failed fast-loop goals.

Reproduce this follow-up independently of the action benchmarks:

```sh
supercomputer run --jobs research/track-m/jobs-ranked-production.json \
  --out runs/track-m/ranked-production-v2 --class gate --timing --vm-type large \
  --data runs/track-m/canonical-capture-v1/fixtures:replay-input
```

#### Production witness-derivation port — `616b0c9c` (not a Step 1 pass)

Ported the research field-bound, Boolean-core, activation-guard, row-case,
frame, key-closure, natural-case, and exact source-transport helpers into
`core/count-recovery/`. `core/count-cases.ts` now invokes them by default;
these files contain no research environment switches and do not import from
`research/`. The port retains the default arithmetic-core instance selector.
Request-diagonal seeds and counted-law model refinement now run through the
existing witness-independence filter. Unchanged obligation builds are reused.

A further production-only gap was visible in the first probes: inactive
field obligations were exhausting their slices in the full counted context.
`field-only.ts` weakens premises only, retains the real source conclusion
(before appended count bindings), and discards count conjuncts only when
there is no live count in that conclusion under the actual path.
`field-case.ts` folds that context, obtains a small arithmetic core, and
transports the candidate back through the fold and the original goal. The
same attempt now runs inside activation leaves. The original final
`checkMC` remains mandatory. No law, trusted rule, or budget changed.

The source at this commit was measured by `production-derivations-final-v1`,
boat batch `20261108-113102-vu3uwa`, tree `f67ce294b6de`. Every job ran alone on
its VM (`--timing --vm-type large`): AMD Ryzen 9 9950X, 4 pinned vCPUs for the
law probes. The table is the complete-law result from `verify-focused.ts`,
not an assertion about individual action candidates. `GDP_COUNTS_GIVEN=1`
and the original 5,000 counted-ms allowance were used; `checked` is false
for every row. Small stopping-boundary overshoots are recorded, not accepted
as satisfying the allowance.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | no / no | 5,013 | 2.561 |
| Inv3915: primary newest | no / no | 5,013 | 3.927 |
| Inv1758: row agreement | no / no | 5,014 | 3.166 |
| Inv2973: quorum overlap | no / no | 5,338 | 27.623 |
| Inv*: quorum term backing | no / no | 5,164 | 31.308 |

These wall times are the probe's reported wall field, not the scheduler wait,
package installation, or total 798-second batch latency. The job-level walls
are retained in `summary.tsv`; `placement.json` records the isolation label.
The timings are not a paired speedup claim against earlier VMs.

What is still unavailable in the complete-law derivation:

- **Safety:** candidates now cover all actions except leader (including the
  send-term action's active and inactive branches). Leader needs the
  voter-to-`bq[i,b]` containment and the resulting quorum/term contradiction;
  the active field projection is satisfiable without those counted premises.
  The `CfgT` ceiling and full active conclusion do not close. A field-only law
  has no post-count key from which the existing row splitter can discover the
  leader/other-primary cases.
- **Inv3915:** the remaining active leader and reconfiguration cases need the
  same quorum-term ceiling and the functional/ordering argument under row
  equalities. Send-configuration now obtains field candidates. Again, row
  discovery was restricted to post-count coordinates.
- **Inv1758:** start and send-terms obtain field candidates; active setup,
  copy, leader, and reconfiguration remain open. The needed functional-copy
  row cases are not discoverable from a post-count read in this field-only
  conclusion. Later paths are not all visited before the shared allowance.
- **Inv2973:** 718 source hypotheses / 195 instances / 41 count reads; the
  inactive-frame path can derive fourteen individual frame candidates but
  its 19-hypothesis closing core remains open. It stalls before the active
  overlap argument. No individual-action proof of this law was established
  by the earlier eight-action matrix (that matrix was for Inv*).
- **Inv*:** 312 source hypotheses / 73 instances / 20 reads. Pick and start
  return action candidates; setup-copy, send-terms, and leader remain open
  in their smaller shared slices. The send-terms trace includes failed
  cross-row proposals `bq#[a,j] <= bq[j,i]` and `cfgSize[0] <= cfgSize#[a]`;
  these are not accepted as facts. Leader derives a `CfgT[i] <= CT[i]`
  ceiling candidate but does not finish its row/disjointness argument.
  Reconfiguration and send-configuration are not reached in this run.

Thus the shared helper implementations are no longer absent from production,
but their full source dependencies and row discovery do not yet reproduce the
standalone Inv* certificates within one law's allowance. Intermediate
`proposed: true` records are not complete certificates and are not counted as
kernel passes. The full-law gate is still false, so no original-harness or
3x60-second claim follows from this port.

Validation at `616b0c9c`: **112 production-derivation tests**, **295 existing
Track M/count/port tests**, and **67 Track P tests**, each suite passing; the
suites overlap and these numbers must not be summed as unique tests. Type/lint
reports zero warnings and errors. The first field-projection attempt exposed
a regression that retained an excluded witness; counting the certificate's
read maps as counted expressions fixed it, and the existing slim-certificate
regression passes in this final batch. Earlier failed attempts and their
logs remain under `production-derivations-*` and `production-field-retry-v1`.

Audited source hashes from every law log:

- `core/count-cases.ts`: `d02950bf1884257666a9bdfc58bcb77b1301a48c3dcca94a3be43bfa54892322`
- `core/count-focus-proof.ts`: `9601488d68a5ee3827ee16982397496b65b9a960a2899a84aa4dc8adc6da6ed6`
- `core/count-recovery/field-bound-lemmas.ts`: `68358811e57199c2749526706432dc588c9f7df8fc255c1efe274b046fb236cf`
- `core/count-recovery/guard-cases.ts`: `af7eb61331773581e9b37466632ad87fa519f78692b4884a34971feeee93cc4d`
- `core/count-recovery/field-case.ts`: `ebba85b83df5ef59432c3fd93a267fe71569c7e7c43a13b42982717b3b70d2f5`

Reproduce the five probes and all validations together:

```sh
supercomputer run --jobs research/track-m/jobs-production-derivations-final.json \
  --out runs/track-m/production-derivations-final-repro --class interactive \
  --timing --vm-type large \
  --data runs/track-m/canonical-capture-v1/fixtures:replay-input
```

The immediate follow-up adds written-field row discovery when a conclusion
has no post-count reads, using the actual source claim and the same checked
row-case transport. Its separate measurement is recorded below; the table
above is deliberately tied to the already validated commit.

#### Field-only row discovery — `37d6319f`: safety passes

`rowPairs` previously obtained its row coordinates only from a post-count
read. Field-only laws do not have one. It now also reads the keys of written
fields in the actual source conclusion, and field-only row cases run before
the dependent field/count derivations. The existing row-case transport and
final counted checker are unchanged.

`production-derivations-final-v2`, batch `20261108-114634-5455s9`, tree
`8e9e4a39ada3`, reruns all five complete laws and all regression suites with
the same inputs, 5,000-counted-ms allowance, and isolated large-VM label.
**Safety returns a complete certificate and the final source check is true.**
This is not merely an individually checked action or an unvalidated proposal.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 4,235 | 4.299 |
| Inv3915: primary newest | no / no | 5,013 | 4.336 |
| Inv1758: row agreement | no / no | 5,015 | 5.046 |
| Inv2973: quorum overlap | no / no | 5,338 | 23.147 |
| Inv*: quorum term backing | no / no | 5,164 | 21.798 |

Safety's leader retry now produces all row branches and the whole-law
certificate checks with 22 instances. For Inv3915 the `a != i, b = i` active
leader/reconfiguration row still fails: the necessary config-term ceiling
or same-term ordering contradiction has not been completed in that row.
Inv1758 now reaches the row cases, but the active pick's `a = i` and copy's
`a = i, b = i` rows remain open. This is a pointwise field/guard-instance gap,
not the absence of a row-splitting function anymore. Inv2973 and Inv* retain
the counted derivation failures described in the previous subsection;
their counted times are unchanged. Their wall differences between VMs are
not evidence of a speedup.

Validation: **113 production-derivation tests, 295 Track M/count/port tests,
67 Track P tests**, all passing; type/lint has zero warnings/errors.
`Step 1` remains **not passed (1/5 hard complete-law probes checked)**.
There has been no Track K rebase, new trusted rule, safety weakening, or
budget increase. The original whole-protocol 3x60-second and downstream
gates remain unpassed.

#### Final row-leaf field core — `00070df4`

A discovered row may already make a field-only conclusion arithmetic. The
row callback now tries `fieldCase` before invoking the full count-bound
recovery, still transporting the candidate to the same source and checking
the complete certificate. This reduces safety's counted work and gives
Inv3915 a complete reconfiguration action candidate; it does not prove the
remaining four whole laws.

Final evidence: `production-derivations-final-v4`, batch
`20261108-115756-t0k3a6`, tree `0736fb8a06c0`. The same five probes, original
5,000 counted-ms allowance and 60-second outer wall limit, canonical captured
hand set, and isolated large-VM placement were retained.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | **yes / yes** | **3,932** | **4.780** |
| Inv3915: primary newest | no / no | 5,014 | 5.214 |
| Inv1758: row agreement | no / no | 5,025 | 4.050 |
| Inv2973: quorum overlap | no / no | 5,338 | 26.627 |
| Inv*: quorum term backing | no / no | 5,164 | 29.089 |

The safety result includes both the start and step certificates, rechecked
by `verify-focused.ts` through `countedObligations` and `checkMC`. There is
no complete-law result to check for the other rows. The recorded stopping
overshoots remain failures, not an expanded allowance.

Remaining derivations, now with the shared helpers present:

- **Inv3915:** the leader action is the sole remaining action-level blocker.
  Its first `different/equal` row fails before later retries obtain further
  row candidates; the active branch still cannot complete the count-backed
  ceiling/ordering argument and combine it within the law's allowance.
  Reconfiguration and send-configuration now return action candidates.
- **Inv1758:** active pick (`equal`) and copy (`equal/equal`) remain open;
  these need the pointwise functional-copy and setup-guard consequences at
  the actual row/column tuple. Discovering row equalities alone was not
  enough. The source-context/model-instance path still needs to deliver
  those consequences at the failing tuple; this is not a missing call to
  `proveRowCases` anymore.
- **Inv2973:** still stops on the inactive frame/closing arithmetic before
  the difficult active overlap argument. The full packet has 195 instances
  and 718 hypotheses; fourteen frame candidates do not close its
  19-hypothesis arithmetic core. Its setup/row support must be narrowed and
  instantiated for that core, rather than treating additional arbitrary
  bounds as facts.
- **Inv*:** setup-copy `different/equal`, send-terms `equal/equal`, and the
  leader's remaining count/row derivation remain open in the shared budget.
  The original individually checked research action certificates used a
  whole per-action allowance; production has not yet reproduced their
  source dependencies and combined derivations within one whole-law
  allowance. Later actions are not all reached. The rejected cross-row
  `bq` and `cfgSize` candidates are still rejected.

The earlier eight-action research matrix proved Inv* entries, not an
independent whole-law proof of each of the other four laws. Thus it would
be inaccurate to describe every remaining failure as a missing already-
verified research theorem. The default helper port is in place; the residual
work is law-specific source instantiation, narrowing and composition.

Final validation: **113 production-derivation tests, 295 Track M/count/port
tests, 67 Track P tests**, all passing; type/lint zero warnings/errors.
All jobs ran on boat and completed. There are no pending validation jobs.
No trusted-kernel, Lean, invariant, safety-law, budget, or Track K change
was made. Step 1 remains **1/5 hard complete-law probes checked**, and the
3x60-second / downstream gates remain unpassed.

Discarded experiment: `production-derivations-final-v3` added ordinary
field-row guard seeds and prioritized ceilings by live row keys. It did
not prove another law and slightly increased counted work. Its runtime
tests passed, but its new test also contained an invalid `all.in` field
caught by type checking. The entire uncommitted experiment was removed;
none of it is in `00070df4`. Its failure receipts are retained, rather
than reported as a successful validation.

#### Ordered recovery: source-proof reuse closes Inv3915

The next request prioritizes Inv3915, then Inv1758, before the two expensive
counted laws. Hypothesis: the Inv3915 leader retry repeats completed guard
and row subproofs, exhausting the shared allowance before composition.
`source-memo.ts` now keeps those untrusted proposals for one invocation of
`proveCountCases`. A lookup always uses the existing `widen` to the current
source and path; a changed or stronger-looking source is not assumed valid.
The final whole-law `checkMC` remains mandatory. There is no global proof
cache, trusted rule, or budget increase.

`ordered-recovery-v1`, boat batch `20261108-120710-d0tbh9`, source tree
`253270669de1`, tests the change with the same canonical input, five-law
runner and isolated large-VM placement. Eight memo hits occur for safety
and eight for Inv3915. **Inv3915 now returns a complete checked start and
step certificate.**

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | **yes / yes** | **3,399** | **3.272** |
| Inv3915: primary newest | **yes / yes** | **4,489** | **5.050** |
| Inv1758: row agreement | no / no | 5,025 | 3.675 |
| Inv2973: quorum overlap | no / no | 5,338 | 22.595 |
| Inv*: quorum term backing | no / no | 5,164 | 19.719 |

The latter three have no memo hits in this run; their initial failed
pointwise obligations remain the next work, not solved by reuse. Their
wall differences are not a paired speedup claim. As before, stopping-clock
overshoots are failed goals, not permission to increase the allowance.

Validation: **115 production-derivation tests, 295 Track M/count/port tests,
67 Track P tests**, all pass, and type/lint reports zero warnings/errors.
The new tests cover reordered paths, changed sources, missing paths, and
expired lookup deadlines. The original checker must still reject any bad
proposal. This is **2/5** hard complete-law probes, not Step 1 completion.
No Track K rebase has occurred.

#### Ordered recovery: constant-index initialization rows

`activeWriteKey` now discovers exact scalar write destinations, including
literal keys. The pick action writes row `0`; it must not split on the
unrelated request input `i`. `activeWriteRow` remains available for existing
string-based ranking, while row-case discovery prefers the exact key.

`ordered-recovery-v2`, batch `20261108-121303-zi5udq`, tree `0930f4754ee5`:

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 3,399 | 3.188 |
| Inv3915: primary newest | yes / yes | 4,489 | 7.097 |
| Inv1758: row agreement | no / no | 5,014 | 5.427 |
| Inv2973: quorum overlap | no / no | 5,338 | 35.881 |
| Inv*: quorum term backing | no / no | 5,001 | 17.294 |

The VM placement includes both EPYC 4585PX and Ryzen 9950X hosts. These wall
times are per-proof measurements, not a paired performance comparison; the
103-second job-level safety duration included work outside its 3.188-second
proof interval. Validation: **116 production-derivation tests, 295 Track M
and 67 Track P tests**, type/lint all passing.

The separate `ordered-point-source-v1` diagnostic rebuilds the cold Inv1758
packet (166 MC hypotheses, 22 instances) and examines the active setup/copy
rows without changing production limits. Its pick-row model has
`?noneCopied = 1`, `b$ = 1`, `size = 2`, but `CV[b$] = 1`: the ordinary
universal guard instance at the law's row is absent. This is an abstraction
model, **not** an execution counterexample. The copy row is already
SMT-refuted with a two-hypothesis core (size domain and the negated equality
of copied fields), but ordinary tree growth returns unknown: its packed,
naturally-subtracted read keys need explicit congruence reconstruction.
The next change addresses those two independently identified gaps.

#### Ordered recovery: field guard instances and packed-copy cores

`ordered-recovery-v3`, batch `20261108-121944-6yv6rl`, tree `6fe438901cb5`,
adds ordinary row instances of unary field-only guards and uses the existing
Boolean/key-closure reconstruction for small refuted cores with packed read
keys. Pick/setup now returns an action candidate, and the copy's first
`equal/equal` row now proves. The new packed-copy unit test passes, but this
snapshot's type check failed because its test's inferred union of linear
objects contained optional `undefined` entries. The test array is explicitly
typed as linear maps in the next snapshot. This failed validation is retained
and is not claimed as a passed code gate.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 3,425 | 3.261 |
| Inv3915: primary newest | yes / yes | 4,537 | 3.592 |
| Inv1758: row agreement | no / no | 5,003 | 3.715 |
| Inv2973: quorum overlap | no / no | 5,338 | 24.378 |
| Inv*: quorum term backing | no / no | 5,001 | 29.501 |

`ordered-recovery-v4`, batch `20261108-122238-gomutu`, tree `b1326a638318`,
keeps completed field-only row leaves in the source memo, obeys the existing
per-case slice during first-pass fallback, and includes the actual field
conclusion's ceiling targets (rather than filtering them out in favor of
only the write actor). These are proposal/search changes; overall proof
allowances and the checker are unchanged. In particular, Inv1758 reaches
all finite action cases rather than exhausting the budget before send.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | **yes / yes** | **2,318** | **2.802** |
| Inv3915: primary newest | **yes / yes** | **3,390** | **3.136** |
| Inv1758: row agreement | no / no | 5,014 | 6.370 |
| Inv2973: quorum overlap | no / no | 5,001 | 19.381 |
| Inv*: quorum term backing | no / no | 5,101 | 18.423 |

Validation for v4 passes: **119 production-derivation tests, 296 Track M
and 67 Track P tests**, type/lint zero warnings/errors. Copy now reuses its
first two completed rows, but a remaining ordering half and later field
rows still exhaust their shares. The next attempt skips the redundant
undivided active field search when row cases are already known, and uses
newly established field ceilings to close the field conclusion directly.
The higher-cost counted laws remain unproved; no Track K rebase has occurred.

#### Ordered recovery: close field claims from their ceiling cuts

`ordered-recovery-v5`, batch `20261108-122523-o9fvbb`, tree `7eac21953d5e`,
skips an undivided active-field attempt when the row case plan is already
known, and attempts the field conclusion directly after deriving its
ceiling cuts. The cuts still have their opposite-branch proofs and the
result is transported and checked against the original source.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | **yes / yes** | **2,260** | **2.232** |
| Inv3915: primary newest | **yes / yes** | **2,579** | **2.865** |
| Inv1758: row agreement | no / no | 5,015 | 6.504 |
| Inv2973: quorum overlap | no / no | 5,001 | 23.310 |
| Inv*: quorum term backing | no / no | 5,101 | 15.875 |

Inv3915 now closes the leader action on the first pass. Inv1758 obtains
both pick and reconfiguration action candidates; copy's remaining ordering
half, leader, and send still need pointwise closure. Its successful rows
are retained, not counted as complete-law passes. The next diagnostic
compares the two copy ordering halves and the equal-row send case.

All **119 production-derivation tests, 296 Track M/count/port tests and
67 Track P tests** pass; type/lint reports zero warnings/errors. The original
whole-law allowance remains 5,000 counted ms, stopping overshoots are not
passes, and no trusted rule or Track K change has been made.

#### Ordered recovery: first sufficient ceiling, remaining shifted row

`ordered-recovery-v6`, batch `20261108-123050-5c3aeh`, tree `6332c4c5f089`,
tries the field conclusion immediately after each new ceiling and avoids
an undivided field search before a known live row update. Inv1758 now
constructs the leader and reconfiguration action candidates on the first
pass and the copy action on retry. Send's shifted copied row remains open.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | **yes / yes** | **3,112** | **3.458** |
| Inv3915: primary newest | **yes / yes** | **2,050** | **3.288** |
| Inv1758: row agreement | no / no | 5,015 | 5.134 |
| Inv2973: quorum overlap | no / no | 5,001 | 13.854 |
| Inv*: quorum term backing | no / no | 5,101 | 17.294 |

The v6 full validation has 119 production-derivation, 296 Track M and
67 Track P tests passing, with type/lint clean. A separately added regression
(`ordered-ceiling-regression-v1`, tree `ede8373f4a65`) failed its expected
single-ceiling assertion: it incorrectly passed a positive claim absent
from the source hypotheses instead of the actual negative conclusion.
The subsequent snapshot fixes this test contract rather than weakening its
assertion; the source proof and early-stop assertion are both retained.

The current-packet point diagnostics (`ordered-point-source-v2`, batch
`20261108-122809-lmkt3b`, tree `6be3c84b1962`) check pick, equal-row copy,
both copy ordering halves, and equal-row send individually. They use the
current default field-guard seeds and are not whole-law certificates.
Send's remaining different-row branch contains guarded natural subtraction
in a shifted read key. The next attempt explicitly proves both scalar
subtraction directions before doing the same packed-key reconstruction.

#### Rejected broad direction discovery

`ordered-recovery-v7`, batch `20261108-123420-gtregl`, tree `637319e886f6`,
validates both new regressions (121 production-derivation tests) and retains
the two complete laws, but broad scalar-subtraction discovery regresses
Inv1758 by splitting directions in unrelated premises. This is not retained
as the search policy: the next snapshot restricts discovery to shifted read
keys in the live field conclusion. Track M and P remain 296/67 tests passing;
type/lint is clean.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 3,112 | 3.392 |
| Inv3915: primary newest | yes / yes | 2,050 | 4.494 |
| Inv1758: row agreement | no / no | 5,014 | 10.509 |
| Inv2973: quorum overlap | no / no | 5,001 | 13.366 |
| Inv*: quorum term backing | no / no | 5,101 | 13.788 |

#### Live-key direction discovery: no whole-law gain yet

`ordered-recovery-v8`, batch `20261108-123847-gemmbg`, tree `9dbf79d9f298`,
restores the successful action candidates by restricting direction discovery
to live conclusion read keys. It does not close Inv1758: the field row's
80 ms sublimit expires while reconstructing both shifted-key directions,
then the remaining row share goes to irrelevant ceiling attempts. The
next change routes that existing row share to the shifted-key field proof;
the global 5,000 counted-ms allowance is unchanged.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 3,112 | 5.805 |
| Inv3915: primary newest | yes / yes | 2,050 | 7.036 |
| Inv1758: row agreement | no / no | 5,015 | 16.812 |
| Inv2973: quorum overlap | no / no | 5,001 | 26.521 |
| Inv*: quorum term backing | no / no | 5,101 | 29.205 |

All 121 production-derivation, 296 Track M and 67 Track P tests pass and
type/lint is clean. The wall-time variation relative to v6/v7 is retained
rather than selecting only a faster replay; counted work is almost unchanged.

#### Shifted-row allocation and the remaining traversal gap

`ordered-recovery-v9`, batch `20261108-124250-d1d3fy`, tree `6ce8d8351915`,
routes the existing row allowance to shifted-key reconstruction instead of
ending it at the local 80 ms sublimit. This alone gives no complete-law gain.
The remaining discovery gap is a forced field comparison: ordinary live
premise traversal prunes its operands, even when conditional read keys
inside those operands still need reconstruction. The next snapshot shares
the existing choice-aware traversal used by Boolean-core reconstruction
and adds an explicit forced-comparison regression assertion.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 3,112 | 8.450 |
| Inv3915: primary newest | yes / yes | 2,050 | 4.565 |
| Inv1758: row agreement | no / no | 5,014 | 13.449 |
| Inv2973: quorum overlap | no / no | 5,001 | 44.626 |
| Inv*: quorum term backing | no / no | 5,101 | 23.986 |

Validation remains 121/296/67 tests passing, type/lint clean. No completed
certificate is claimed for any of the three open laws, and the timing
overshoots are failures under the original allowance.

#### Choice-aware discovery: source-claim scope still insufficient

`ordered-recovery-v10`, batch `20261108-124602-ua2w5e`, tree `2cb219674fd9`,
passes the forced-comparison regression but still does not close the send
row. This falsifies the expectation that changing the source-claim walker
alone would suffice. The needed shifted read occurs in the expanded field
projection's support as well as its conclusion. The next attempt discovers
directions only after obtaining that projection's refuted core and returns
satisfiable projections to the count-backed derivation immediately, rather
than spending the rest of their row allowance on a futile field-only grow.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 3,112 | 7.960 |
| Inv3915: primary newest | yes / yes | 2,050 | 6.710 |
| Inv1758: row agreement | no / no | 5,014 | 12.498 |
| Inv2973: quorum overlap | no / no | 5,001 | 47.639 |
| Inv*: quorum term backing | no / no | 5,101 | 30.855 |

All 121/296/67 tests and type/lint pass. The batch's nine independent jobs
are diagnostic measurements, not a passed whole-protocol 60-second gate.

#### Latest: core-directed field reconstruction (two of five complete)

`ordered-recovery-v11`, batch `20261108-125401-9308mw`, tree `2a9c27828091`,
uses the actual refuted field core to choose natural directions. A satisfiable
field projection is handed back immediately to count-backed recovery instead
of consuming the row share in generic field growth. This is the retained
production default, with no feature flag or protocol-name dispatch.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s | First remaining derivation |
| --- | --- | ---: | ---: | --- |
| one primary per term | **yes / yes** | **2,420** | **4.467** | — |
| Inv3915: primary newest | **yes / yes** | **1,936** | **4.536** | — |
| Inv1758: row agreement | no / no | 5,015 | 9.222 | Different/equal send row; shifted-key source reconstruction after the mirrored equal/different rows |
| Inv2973: quorum overlap | no / no | 5,001 | 29.930 | Inactive-frame arithmetic closure and its source-instance composition |
| Inv*: quorum term backing | no / no | 5,101 | 27.299 | Copy, send-terms and leader witness-chain composition |

Inv1758's setup, copy (on retry), leader and reconfiguration action candidates
now compose. Send constructs the equal/equal row and both ordering halves of
the equal/different row. The first still-open row is its mirror,
`different/equal`; later rows are not thereby established. The candidate
checks recorded as `deferred:true` are **not** individually accepted complete
certificates. The whole-law result remains false, as shown above.

The isolated point diagnostic checks source proofs for setup, equal copy,
both copy ordering halves, and equal-row send. It does not supply an
independent complete Inv1758 proof. The next useful target is generic checked
transport/reuse of the mirrored send-row derivation, not a larger allowance.

Validation on the retained snapshot: **121 production-derivation tests,
296 Track M/count/port tests and 67 Track P tests pass**; type/lint reports
zero warnings/errors. Both new source-checking regressions pass. No trusted
kernel, invariant, law, outer proof allowance or Track K code changed. There
has been no Track K rebase. The all-laws-kept, whole-protocol 3×60-second and
downstream gates remain unpassed.

Reproduce the complete-law matrix and validation:

```sh
supercomputer run --jobs research/track-m/jobs-production-derivations-final.json \
  --out runs/track-m/ordered-recovery-v11-replay \
  --class interactive --timing --vm-type large \
  --data runs/track-m/canonical-capture-v1/fixtures:replay-input
```

Point diagnostics use `research/track-m/jobs-point-source.json` with the same
fixture mount. Full results, including failed intermediate attempts, remain
under `runs/track-m/ordered-recovery-v{3,4,5,6,7,8,9,10,11}/` and
`runs/track-m/ordered-point-source-v2/`.

### Coordinator follow-up: untrusted mirrored rows and isolated Track K measurement

#### First mirror replay

`mirrored-rows-v1`, batch `20261108-130753-9a971s`, tree `04fba5ea8fca`,
adds a pure untrusted column renamer and used-row matcher. A reused proof is
emitted as an ordinary complete subtree; there is no kernel rule, symmetry
axiom, protocol-name test, or opt-in flag. Renaming covers scalar variables,
packed and tuple cells, conditional columns, squares and product references.
An unmatched source row refuses the reuse.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 2,314 | 4.932 |
| Inv3915: primary newest | yes / yes | 1,936 | 5.215 |
| Inv1758: row agreement | no / no | 5,014 | 10.148 |
| Inv2973: quorum overlap | no / no | 5,001 | 28.182 |
| Inv*: quorum term backing | no / no | 5,101 | 28.881 |

The requested different/equal send row now reuses the equal/different
subtree. The next failure is a later different/different ordering half;
the next replay also attempts swapped histories within that case label.
The 125 production tests pass, but the type check rejects the initial
polynomial helper import (scalar `times` was used in place of polynomial
`times`). The next snapshot uses the existing untrusted polynomial reader
and adds a monomial regression. This validation failure is not hidden.

#### Track K: measurement only, not integrated

A throwaway branch, `research/track-m-kmeasure-0e9afc3d`, merges exactly
`0e9afc3d` into Track M's `a75ebf56`. Merge commit `07cb2af7` resolves only
report/shard-list conflicts using the Track M copies. Measurement-only
instrumentation in `babcdb7a` counts calls and successful proposals and
turns on the optional provenance hints together with
`GDP_COUNT_LEMMA_CUTS=1`. No Track K commit is an ancestor of
`claude/track-mldr`.

Each pair runs off then on in separate Bun processes on the same pinned
large VM (AMD EPYC 4585PX, four vCPUs, no co-tenants), three pairs per law.
The measured emission result is **zero proposer calls and zero proposals
in every run**: these focused probes stop before a complete certificate
reaches the `core/counts.ts` admission hook. Therefore these measurements
show **no observed saving attributable to lemma emission**. They do not
measure the potential benefit of applying cuts to partial branch checks.

| Law | Emission off wall s (three repeats) | Emission on wall s (three repeats) | Mean off / on s | Counted ms | Verdict, all runs |
| --- | --- | --- | --- | ---: | --- |
| Inv2973 | 38.123, 29.594, 48.838 | 37.632, 36.303, 39.865 | 38.852 / 37.933 | 5,001 | unproved / unchecked |
| Inv* | 33.649, 31.109, 28.961 | 32.284, 29.490, 33.927 | 31.240 / 31.900 | 5,101 | unproved / unchecked |

Evidence: `runs/track-m/kernel-pair-v1/` (batch
`20261108-130637-npc9xy`, tree `8e625d61b85e`) and
`runs/track-m/kernel-pair-supplement-v1/` (batch
`20261108-131804-kyl88l`, tree `6b65f32f796c`), with placement files.
The first Inv* log reached the 400,000-byte output cap after its second
pair. Only the missing third pair was rerun, with trace-free output; no
truncated record was treated as a complete measurement.

#### Second mirror replay

`mirrored-rows-v2`, batch `20261108-132209-f0qm6t`, tree `040f4a1e33c3`,
retains same-label histories so different/different ordering halves can also
be swapped. The originally requested different/equal send row is reused;
a later different/different half still runs out of the current share.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 2,314 | 13.322 |
| Inv3915: primary newest | yes / yes | 1,936 | 10.857 |
| Inv1758: row agreement | no / no | 5,019 | 14.234 |
| Inv2973: quorum overlap | no / no | 5,001 | 40.078 |
| Inv*: quorum term backing | no / no | 5,101 | 33.168 |

The type error is fixed; lint now identifies an unused test variable, removed
in the next snapshot. Two Track P tests reached their unchanged 5-second test
timeout on this VM (both reported their checked cyclic certificates before
termination). They remain failed validation, not accepted passes. No timeout
is increased. The next replay uses exact row remapping rather than `widen`'s
fallback search for cache hits, and prioritizes the compatible ordering half.

#### Generic mirror implementation validated

`mirrored-rows-v3`, batch `20261108-133547-s6host`, tree `0437450d1e1f`,
checks all 126 production-derivation tests, 296 Track M tests, 67 Track P
tests, and type/lint with zero warnings/errors. The prior two Track P
timeouts do not recur under the unchanged test timeout.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 3,166 | 4.176 |
| Inv3915: primary newest | yes / yes | 2,370 | 5.645 |
| Inv1758: row agreement | no / no | 5,014 | 9.589 |
| Inv2973: quorum overlap | no / no | 5,001 | 19.528 |
| Inv*: quorum term backing | no / no | 5,100 | 19.441 |

The untrusted mirror is default and protocol-independent. The requested
send different/equal derivation is now instantiated from its sibling and
emitted in full, including reindexed ordinary arithmetic leaves. A later
different/different row still exhausts the whole-law allowance; mirror reuse
alone is not a complete Inv1758 proof. Exact-only ordinary cache transport
also costs more search than the older fallback in this replay. The next
change preserves the old ordinary-cache fallback while trying compatible
mirrors first, then addresses arithmetic-core selection of source frames
for the two counted laws. Track K remains excluded from this branch.

#### Core-selected frame instances

`frame-core-v1`, batch `20261108-134922-cflntu`, tree `5703c9be2e15`, passes
127 production-derivation tests, 296 Track M tests, 67 Track P tests and
clean type/lint. The arithmetic core selects 9 of 14 overlap frames and
2 of 4 term-backing frames before constructing their witness branches.
The inactive shared-frame conclusions now construct and transport; the
remaining source gap is in active actions, not inactive-frame arithmetic.
No speculative frame inequality is accepted without its ordinary proof.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 2,314 | 3.601 |
| Inv3915: primary newest | yes / yes | 1,936 | 3.439 |
| Inv1758: row agreement | no / no | 5,014 | 6.513 |
| Inv2973: quorum overlap | no / no | 5,000 | 25.070 |
| Inv*: quorum term backing | no / no | 5,139 | 15.154 |

Inv1758 now completes the first active send guard branch, including the
mirrored rows; the alternate active guard branch reaches equal/equal with
only 41 ms remaining. It still needs generic reuse across distinct guard
paths. Overlap reaches active count/field source closure after deriving
all selected inactive frames. Term backing additionally reaches the
active different/different row and its missing witness chain. These are
partial candidates, not accepted complete-law certificates.

#### First cross-activation source reuse replay

`activation-reuse-v1`, batch `20261108-135420-89sfw6`, tree `01f1b0b782d0`,
reuses an already-built subtree across a changed path only after every used
row matches at the destination. Safety/newest counted work drops to
1,047/1,089 ms, but limiting candidates to two geometrically nearest paths
misses the completed active send sibling behind nearer inactive paths.
The next replay tests more already-proved candidates, still under the same
deadline; none becomes trusted evidence without ordinary kernel checking.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 1,047 | 2.425 |
| Inv3915: primary newest | yes / yes | 1,089 | 2.732 |
| Inv1758: row agreement | no / no | 5,014 | 5.985 |
| Inv2973: quorum overlap | no / no | 5,394 | 35.627 |
| Inv*: quorum term backing | no / no | 5,138 | 17.229 |

Tests pass; the type/lint job did **not run**, because remote dependency
installation failed with `ENOENT: failed copying files from cache to
destination for package effect`. This is recorded as failed validation;
the full unchanged validation matrix is rerun. The clean isolated Track K
measurement worktree has been removed; branch tip `5dc10469` retains the
reproducible measurement code and jobs, with no ancestry into Track M.

#### Exact source reuse validated

`activation-reuse-v2`, batch `20261108-140203-efspur`, tree `4eb1ab84701d`,
passes 129 production-derivation tests, 296 Track M tests, 67 Track P tests,
and clean type/lint. The source-cache negative tests reject missing
assumptions and changed satisfiable goals. Larger candidate coverage does
not remove the last alternate active send derivation; it needs its own
source proof rather than an unjustified symmetry shortcut.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 1,015 | 2.537 |
| Inv3915: primary newest | yes / yes | 997 | 3.876 |
| Inv1758: row agreement | no / no | 5,014 | 6.231 |
| Inv2973: quorum overlap | no / no | 5,394 | 24.984 |
| Inv*: quorum term backing | no / no | 5,135 | 30.421 |

The next experiment preproves any arithmetically impossible default input
branch, retaining its ordinary leaf in the certificate. A proven default
need not reserve an equal share of the remaining search time. This avoids
interrupting the last real action only to repeat its partial derivation in
the recovery pass; it does not change the total counted allowance.

#### Default-branch preflight: first replay

`fallback-preflight-v1`, batch `20261108-141045-ddez6k`, tree `d135fee5da7d`,
constructs the default arithmetic leaf on all five inputs. The real send
branch receives the remaining share rather than repeating its first half.
It still reaches the allowance during the alternate active equal/different
ordering half. The preflight initially retained every source instance in
its metadata, which broke the slim-certificate regression tests; this is
not accepted. The correction retains only instances actually used by the
default leaf, without changing the tests' expected slim certificates.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 984 | 3.762 |
| Inv3915: primary newest | yes / yes | 973 | 4.223 |
| Inv1758: row agreement | no / no | 5,000 | 8.014 |
| Inv2973: quorum overlap | no / no | 5,396 | 42.122 |
| Inv*: quorum term backing | no / no | 5,137 | 38.261 |

Type/lint and Track P pass. The failed slim-certificate tests remain
failures. A second generic change splits a packed field's guarded column
domain outside row reconstruction, so each copied-row half need not
rediscover the same range bound. Both branches remain ordinary checked
subtrees; a missing domain assumption cannot certify a false claim.

#### Guarded column domain: first replay

`column-domain-v1`, batch `20261108-141720-9wyxhw`, tree `e8edfff92d63`,
restores all 296 Track M regressions, including slim certificates, and
passes type/lint. The new unit fixture proved its theorem but did not
exercise row discovery: its direct-key write is now corrected to the
production `each`/conditional write form. Two unchanged Track P 5-second
timeouts recur on the slower placement and are recorded as failures.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 984 | 7.356 |
| Inv3915: primary newest | yes / yes | 973 | 2.155 |
| Inv1758: row agreement | no / no | 5,003 | 10.957 |
| Inv2973: quorum overlap | no / no | 5,396 | 20.538 |
| Inv*: quorum term backing | no / no | 5,137 | 15.168 |

A `column < size` cut alone does not simplify packed row ranges. The next
replay uses the constant stride read from affine packed field keys, when
available, for the candidate cut. Its false branch must still be derived
from the original source; the stride is not a new axiom or domain bound.

#### Rejected repeated-boundary replay

`column-domain-v2`, batch `20261108-142340-2nmdh3`, tree `bc42a3e0d3f1`,
exposed a termination bug in the new optimization: after replacing the
claim's domain with a packed stride, the same known stride could be split
again. The new regression timed out at its unchanged 1,500 ms limit. This
snapshot is **not retained**; the following replay checks the derived
boundary at the current path before recursing.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s |
| --- | --- | ---: | ---: |
| one primary per term | yes / yes | 984 | 10.381 |
| Inv3915: primary newest | yes / yes | 973 | 4.900 |
| Inv1758: row agreement | no / no | 5,000 | 26.099 |
| Inv2973: quorum overlap | no / no | 5,362 | 62.020 |
| Inv*: quorum term backing | no / no | 5,137 | 39.684 |

The overlap wall observation exceeds 60 seconds during an uninterruptible
check; it remains an unproved failed probe, never an accepted wall-budget
extension. Other tests and type/lint pass, but the domain regression alone
is sufficient to reject this experimental snapshot.

### Current status: generic mirror and source recovery, 2/5 complete laws

Final replay: `column-domain-v3`, batch `20261108-142710-td8tbx`, tree
`b60edc7334df`, on the pinned large placements recorded beside its logs.
All **130 production-derivation tests, 296 Track M tests and 67 Track P
tests pass**. Type/lint reports zero warnings and zero errors. The prior
slim-certificate and repeated-boundary failures are fixed; their tests
remain enabled, not weakened. No test timeout or proof allowance changed.

| Complete hand-set law | Proved / checked | Counted ms | In-process wall s | Remaining production derivation |
| --- | --- | ---: | ---: | --- |
| one primary per term | **yes / yes** | **984** | **4.421** | — |
| Inv3915: primary newest | **yes / yes** | **973** | **4.776** | — |
| Inv1758: row agreement | no / no | 5,000 | 9.875 | Alternate active send guard: equal/different ordering half, followed by the remaining mirror/row composition. |
| Inv2973: quorum overlap | no / no | 5,396 | 24.357 | Active-action count/field witness closure; the selected inactive frames now construct and transport. |
| Inv*: quorum term backing | no / no | 5,137 | 18.517 | Active setup/copy/send/reconfiguration witness chains, including unresolved different/different row closure. |

The specifically requested different/equal mirror is constructed generically
from the equal/different source subtree. No action name is tested by the
remapper, no trusted symmetry rule was introduced, and emitted trees contain
ordinary splits and reindexed arithmetic leaves. Generic positive/negative
mirror tests and the two complete laws pass the unchanged kernel. **The
partial Inv1758 send candidates are not represented as a checked complete
Inv1758 certificate.** Its second active guard still needs its own derivation.

The frame selector derives only inequalities named by the numeric core:
9/14 for overlap, 2/4 for term backing on the observed inactive paths. Those
constructed partial source proofs do not constitute whole-law completion.
The earlier eight-action research matrix covered Inv*, not independently
completed research proofs of every law in this table. Failure-side counted
overshoots above 5,000 ms remain failures, never accepted extensions.

Track K is measurement-only: the separate branch tip is `5dc10469`; its
clean temporary worktree has been removed. Three off/on pairs per law are
recorded above, with zero proposer calls in all runs. No Track K commit is
an ancestor of this production branch, and no merge/rebase onto it is made.
The all-laws-kept, 3×60-second and downstream gates remain **unpassed**.

Reproduce the final matrix:

```sh
supercomputer run --jobs research/track-m/jobs-production-derivations-final.json \
  --out runs/track-m/column-domain-v3-replay --class interactive --timing \
  --vm-type large --data runs/track-m/canonical-capture-v1/fixtures:replay-input
```

All jobs for the reported replays have finished. Only validated generic
source-recovery code and evidence are retained; no kernel, law, invariant,
external solver, global budget or Track K production integration changed.

## Coordinator wall-budget audit — current strategy does not fit; proof work paused

Requested wall decomposition, on unchanged production source **`af7cb91f`**.
No further row/source proof changes were made during this audit. The result
invalidates the earlier attribution of the unproved laws' long wall time to
kernel checking: their cost is overwhelmingly construction and search.

### Measurement contract and checks

Final evidence: `runs/track-m/wall-breakdown-v3/`, batch
`20261108-144544-c5oppp`, snapshot `030e2c66b138`.
All measured child processes ran on VM `bx_27ffycju`, **AMD Ryzen 9 9950X**,
with **four-CPU affinity `0-3`**, no co-tenants. The scheduler's placement
lists six CPUs for the parent job; `profile-suite.ts` explicitly restricts
every measured Bun child to four, and each child's record confirms `0-3`.
The full process wall is measured around spawning Bun, including module
startup and output, as required by `research/protocols/ic3syn/README.md`.
Dependency installation, queueing and instrumentation installation are not
part of the measured application wall.

Input SHA-256:
`4be076f22a8fec41083719358b3518a83b23add5c3dfd26017f772404e7dac24`.
The five focused probes keep their original 5,000 counted-ms allowance and
60-second wall guard. The original production replay uses `proveRule` on
`protocols.mldr.make()` and its caller safety law with the original
60,000-ms search option; `GDP_COUNTS_GIVEN` is unset for generation/admission.

The opt-in research installer changes only disposable remote copies. It
saves originals and emits before/after SHA-256 hashes for every wrapped
file. Function bodies, arguments, return values, proof data, cost counters
and deadlines are unchanged; recursive checker calls use the original
body rather than adding a timer at every tree node. Neither the production
kernel nor the production prover imports this instrumentation.

Exclusive nested timers classify:

- **Candidate generation:** count/witness/instance proposals in each focused
  probe. Production invariant discovery is measured separately, once.
- **Search:** model/CDCL and arithmetic queries, including fallback search
  invoked while transporting a tree.
- **Construction:** goal/row construction, proof transport and control work.
  DAG unfolding and its leaf reconstruction remain construction, not search.
- **Kernel:** full-tree and count-certificate checks, **plus direct arithmetic
  certificate validation** (`core/check.ts:checkRefutation`) used by widening
  and unfolding. Row creation inside a kernel call stays in the kernel bucket.
- **Idle/GC residual:** the remainder of full process wall after these exclusive
  buckets. **Bun reports no supported GC timing events on this VM.** GC/JIT
  pauses inside a measured phase stay charged to that phase; this residual
  includes startup/unclassified time and is **not a measurement of total GC**.
  We do not manufacture a separate GC estimate.

The arithmetic sum uses unrounded times; independently displayed millisecond
rounding can differ by 0.001 s. No nested time is counted twice.

### One instrumented run per complete law — seconds

| Law | Proved / checked | Candidate gen. | Search | Construction | Kernel | Idle/GC residual | **Sum wall** |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| One primary per term | yes / yes | 0.028 | 0.439 | 0.567 | 1.080 | 0.036 | **2.150** |
| Inv3915: primary newest | yes / yes | 0.031 | 0.417 | 0.636 | 1.193 | 0.036 | **2.312** |
| Inv1758: row agreement | no / no | 0.034 | 2.335 | 2.656 | 0.006 | 0.042 | **5.072** |
| Inv2973: quorum overlap | no / no | 0.219 | 4.074 | 17.190 | 0.000 | 0.094 | **21.577** |
| Inv*: quorum term backing | no / no | 0.059 | 3.460 | 12.592 | 0.002 | 0.066 | **16.179** |
| **Sum of five** | **2/5 complete** | **0.369** | **10.725** | **33.641** | **2.281** | **0.274** | **47.290** |

Counted ms, respectively: **984.464, 972.813, 5,000.273, 5,396.452,
5,137.436**. The unproved/overshooting probes remain failures.

The original uninstrumented controls on the same VM and affinity took
**2.178, 2.363, 5.170, 21.861, 16.844 s**, totalling **48.416 s**.
All five controls and instrumented runs have **identical counted work and
identical proof/check verdicts**. Their individual wall differences range
from -1.31% to -3.94%; a single pair is a perturbation check, not a claimed
statistical speedup.

The decisive construction sites are `kernel/prove.ts:rowsAt`:

| Law | Calls | Exclusive row construction/lookup wall |
| --- | ---: | ---: |
| Inv1758 | 23,554 | 1.822 s |
| Inv2973 | 9,383 | **13.817 s** |
| Inv* | 12,279 | **10.213 s** |

Those costs occur while building/transporting candidate proofs, before a
complete certificate exists. They are not final-kernel costs that the current
Track K admission hook can remove. Kernel time on both hard counting probes
combined is only **0.002182 s**.

### Production law generation and original end-to-end replay

The independent production-generation run proposes **24 candidates** for the
original one-caller MLDR problem. Its wall is **22.156 s** (22.117 s generation,
0.040 s residual); the uninstrumented generation control takes **23.467 s**.
Both report zero work in the focused probes' `fullWork/fullRate` counter:
that counter must not be used as a wall estimate for law discovery.

The **actual original generated-law pipeline**, not the supplied hand-set,
returns **unproved / unchecked**, `not proven: one primary per term`:

| Original pipeline | Generation | Search | Construction | Kernel | Residual | **Sum wall** |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Instrumented | 23.683 | 13.915 | 11.443 | 4.350 | 0.061 | **53.451 s** |
| Uninstrumented control | — | — | — | — | — | **52.152 s** |

Its counted work and verdict also match the control. This is a timed failed
production run, not evidence that the complete hand-set or generated-law gate
has passed.

### Budget conclusion and stop decision

The current serial work plan costs **22.156 + 47.290 = 69.446 s**, already
**9.446 s beyond the entire 60-second allowance**, while three hard laws remain
unproved. Using the uninstrumented controls gives **71.883 s**, not a fit either.
Even the unrealistic removal of **all 2.281 s of kernel verification** leaves
**67.165 s**. Production generation plus the two open counting-law probes alone
uses **59.912 s**, leaving **0.088 s** for the other three laws and any additional
work needed to finish the missing certificates.

This addition is an explicit **budget diagnostic for the present serial
strategy**, not a mathematical lower bound on a redesigned joint solver:
separate cold processes do not exploit possible cross-law reuse, and the real
production-generated family differs from the hand-set. The original pipeline's
independent failure above is the direct end-to-end observation.

**Per the coordinator's condition (3), further row-closing/source-chain changes
are paused rather than adding more wall.** The next viable plan must first cut
measured generation and/or row construction/transport costs (or demonstrate
cross-law reuse), and remeasure every proposed change including any extra wall.
The remaining ordering half, active source instances and all-laws certificate
are still open. No 3×60-second success is claimed. Track K remains unmerged.

### Reproduction and validation

```sh
supercomputer run --jobs research/track-m/jobs-wall-breakdown.json \
  --out runs/track-m/wall-breakdown-replay --class gate --timing \
  --vm-type large --data runs/track-m/canonical-capture-v1/fixtures:replay-input
```

The suite runs uninstrumented controls before installing measurement wrappers
in its private remote snapshot. The installer requires
`TRACK_M_DISPOSABLE_PROFILE=1` and a backup directory. Do not run it against a
production checkout. Raw results, complete wrapper manifests and the profiler
neutrality tests are in `wall-breakdown-v3/wall-breakdown.log`.

Validation: **4 cost-accounting unit tests and 49 instrumented
kernel/prover/mirror tests pass**; type/lint reports **0 warnings, 0 errors**.
The 49-test group includes the same 4 cost tests. Preliminary `wall-breakdown-v1`
used six CPUs and omitted direct leaf-check timing; `v2` fixed affinity and
added production controls but still omitted that small verifier path. They
are retained as diagnostics, not substituted for the final table.

## Row/generator optimization investigation — ordered coordinator follow-up

### Row diagnostics (unchanged baseline)

`rows-before-v1`, four-CPU child affinity `0-3`, batch
`20261108-145619-vaswmz`, snapshot `07387b52239f`:

| Law | Calls | Distinct goal identities / structural goals | Distinct ordered (goal, path) keys | Exact repeat calls / time | New paths with built prefix / time | Mean ms per call |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| One primary | 4,648 | 59 / 48 | 2,395 | 2,253 / 0.016 s | 1,011 / 0.171 s | 0.122 |
| Inv3915 | 4,217 | 78 / 59 | 2,184 | 2,033 / 0.007 s | 901 / 0.204 s | 0.149 |
| Inv1758 | 23,554 | 212 / 94 | 12,542 | 11,012 / 0.047 s | 1,335 / 0.112 s | 0.086 |
| Inv2973 | 9,383 | 191 / 155 | 5,185 | 4,198 / 0.015 s | 1,975 / 0.862 s | 1.953 |
| Inv* | 12,279 | 316 / 210 | 7,073 | 5,206 / 0.020 s | 1,880 / 1.027 s | 0.932 |

Exact repeats are already cheap. Whole-goal structural duplicates account for
669 and 610 reusable calls in the first two laws, but only **8 and 13** in the
two hard counting laws. Simply enlarging the exact-key cache cannot recover
the hard laws' dominant time. Ordering is part of the key: path atoms precede
hypothesis rows, and proof input indices depend on that order.

A second diagnostic, `rows-cold-v1`, attributes **16.217 of 22.692 s** of
Inv2973 row time and **9.266 of 11.449 s** of Inv* row time to `facts`.
Term-row construction adds 0.320 and 1.125 s respectively. Different cold
runs have substantial wall variation; these are within-run attributions,
not claims of a regression against the previous VM sample.

The optimization target is therefore **dependency-tracked fact expansion
shared across hypotheses/goals**, not merely parent-path copies. A child can
change earlier conditional facts, natural-subtraction bounds and cell equality;
blindly appending its split atom is incorrect.

### First two candidates and rejected measurement

`rows-shared-v1` tried shared whole-hypothesis facts. `rows-shared-v2` also
cached Boolean fact subtrees. Both preserve all five proof/check verdicts;
neither establishes a satisfactory wall improvement yet. The second matched
pair (seconds; old helper versus candidate):

| Law | Old wall | Candidate wall | Proved / checked on both |
| --- | ---: | ---: | --- |
| One primary | 2.248 | 2.171 | yes / yes |
| Inv3915 | 2.284 | 2.576 | yes / yes |
| Inv1758 | 5.838 | 5.117 | no / no |
| Inv2973 | 28.837 | 25.020 | no / no |
| Inv* | 17.854 | 18.659 | no / no |

The first trial had a test-only TypeScript narrowing error; the second had an
unused import. Exact-row equivalence and kernel/mirror tests passed; these
are not clean accepted validation runs. `rows-shared-v3` is **invalid**: a
concurrent edit introduced a diagnostic import after boat enumerated the
snapshot but before it read the file, omitting the newly imported module.
Do not use its failed probes as performance or proof evidence. Subsequent
launches stage all files and await the immutable `tree` receipt before edits.
A bounded, multi-page dependency-cache candidate is under test in
`rows-shared-v4`; no new complete-law certificate has been claimed.

### Generation diagnosis, before optimization

`generators-before-v1` instruments every candidate family rather than removing
any generator. Standalone generation takes **38.519 s** on this run, with
**25.354 s** inside the cube generator. Of that, initial random sampling costs
**19.756 s**: **627,047 requests**, **6,615 trials**, **64 distinct samples**.
The original production run independently spends **13.876 s** in the same
sampling stage with exactly those request/trial/sample counts. This is the
next measured target, after the row optimization is accepted.

Families proposed before filtering: 5 map bounds, 0 row laws, 63 field laws,
0 scan prefixes, 14 cubes and 0 carry laws. Standalone admission retains 24;
the original pipeline, whose caller also declares a bound, retains 23 new
candidates. The raw log records every name. No complete production proof
exists, so **final-proof generator usage is unknown**, not zero and not an
argument for dropping a family.

### Accepted row sharing: original builder over canonical immutable expressions

The larger dependency-retention trial (`rows-shared-v4`) passed tests but was
rejected for wall regressions (Inv2973 29.193 -> 47.526 s; Inv* 27.306 ->
19.857 s). Flattened fact components (`v5`) also regressed (21.219 -> 28.300 s;
15.707 -> 18.550 s); its duplicate row builder is **not retained**.

`rows-shared-v6`, snapshot `3c19b01c39f4`, instead interns immutable expression
subtrees and ordered hypothesis vectors, then calls the **unchanged original
`leafConstraintsReusing`**. This makes the existing per-expression dependency
caches useful across freshly reconstructed goals. Exact rows are bounded-LRU
cached by canonical goal and ordered path, including the actual split atom.
There is no new arithmetic implementation and no changed trusted checker.
All scopes persist across retries/laws in the same process. `GDP_ROWS_SHARED=0`
selects the original implementation solely for paired controls; sharing is on
by default.

Matched uninstrumented four-CPU child runs on the same VM, seconds:

| Law | Original | Shared expressions / rows | Proved / checked (both) |
| --- | ---: | ---: | --- |
| One primary | 3.017 | 2.205 | yes / yes |
| Inv3915 | 3.273 | 2.254 | yes / yes |
| Inv1758 | 6.963 | 5.139 | no / no |
| Inv2973 | 30.858 | 18.149 | no / no |
| Inv* | 20.485 | 15.125 | no / no |
| **Sum** | **64.597** | **42.872** | **2/5 complete** |

**All five counted-work totals are identical**, unlike the discarded fact
builders. Original runs precede candidates in this pair, so these numbers need
a reversed-order/full-suite follow-up; they are not statistical confidence
intervals. Tests: 44 row-equivalence/kernel/path/mirror tests pass, including
structural sharing and ordered-path separation; type/lint 0 warnings/errors.
Generator optimization is the next phase; no new open-law derivation was added.

### Generation work reassigned; existing prototype isolated

Before reassignment, `generation-shared-v2` measured a generic compiled
sample guard/step prototype: **27.478 -> 24.799 s** generation, cube stage
20.374 -> 17.362 s, initial sampling 14.415 -> 11.470 s. Both sides perform
**627,047 requests / 6,615 trials / 64 samples**, and **every ordered candidate
array and generator-family name array is identical** (24 final candidates).
Tests and type/lint pass. The preceding v1 had a type-only annotation error,
fixed before v2; it is not the clean validation result.

The coordinator reassigned item (2) to `claude/track-gen`. That code is isolated
on **`research/track-m-gen-handoff`**, commit **`9a9886b9`**, based on
`3394e14c`. It was removed from the Track M worktree without rewriting history.
No further generation edits are being made here; the other lane may cherry-pick
or supersede the prototype. Its job and test sources are on that branch.

`paired-rows-generation-v1` is a **pending** 29-protocol/29-broken-variant
comparison of the immutable pre-reassignment snapshot (including that
prototype) against `76edf867`. It does not validate subsequent cross-law cache\nscope changes. **It has now completed:** all 29 correct and all 29 broken\nverdicts match baseline. Correct: 27 proven, 2 strict-wall timeouts on both\nsides (Paxos/MLDR). Broken: 11 refuted, 16 unknown, 2 strict-wall timeouts\non both sides; none proven. No result was inferred from a job's exit code.\nThe mixed EPYC 4585PX/Ryzen 9950X placements are valid for verdict pairs on\nthe same VM, but are not used for cross-VM timing claims. The complete run\ntook 951 s and used three boat VMs.\n
Cross-law work now extends the existing exact-goal, mode-sensitive completed
root-tree cache over one counted-family search. It never stores unknowns or
models and does not alter checker admission. `family-sharing-v1` is a pending
legacy/row-sharing/row-plus-tree experiment. Its first driver iterates the nine
hand-family laws, including the four easier supports; the next driver explicitly
filters the five hard targets while keeping all nine as assumptions. Do not
confuse those populations or their sums.

### Reverse-order row control and cross-law outcome

`rows-reverse-v1` runs the shared implementation **before** the legacy one,
with cross-source experiments disabled. Same 9950X VM and `0-3` affinity,
unchanged verdicts and exactly identical counted work:

| Law | Legacy wall s | Shared wall s |
| --- | ---: | ---: |
| One primary | 2.275 | 2.250 |
| Inv3915 | 2.442 | 2.040 |
| Inv1758 | 5.335 | 5.130 |
| Inv2973 | 23.674 | 18.467 |
| Inv* | 18.170 | 15.107 |
| **Sum** | **51.896** | **42.994** |

The benefit survives reversing the pair. Its magnitude varies with the VM run;
we claim the matched measurements, not a single universal percentage.

Cross-law **expression/row construction** sharing is retained and on by default.
Cross-law **completed proof** caches were investigated and rejected:

- `family-sharing-v1`: the existing exact-root tree cache kept 5 proofs but had
  **zero hits** across the nine-law family. Its total rose from row-sharing-only
  73.964 s to 78.379 s. No new default tree-cache scope is retained.
- `source-sharing-v1`: a bounded cache of used-hypothesis source subtrees stored
  **56** candidates; **zero matched transport attempts/hits**. The five-law
  total rose from 75.428 to 76.067 s. Tests passed; the initial typecheck lacked
  an explicit terminal `return undefined`.
- `source-sharing-v2`: alpha-renaming-aware matching of all used assumptions
  stored **46** candidates and again produced **zero transport attempts/hits**.
  The five-law total rose from **46.510 to 47.728 s**. Type/lint and exact-row /
  kernel / source-transport tests passed, but the cache is still rejected.

Those whole-hypothesis cache contracts do not match across the observed
calls. Zero matches do **not** exclude finer-grained arithmetic-row reuse:
a large hypothesis may contain an actually shared row among unused conjuncts.
A useful cache must expose smaller shared contracts or transport the actual
used rows rather than require each enclosing hypothesis to match. Neither
benefit can be claimed from the zero-hit caches. **No rejected whole-goal or
whole-hypothesis cache remains in the production path.**
The final rejected prototype is archived as
`research/track-m/rejected-source-sharing.patch.json`; extract its `patchLines`
with `jq -r '.patchLines|join("\n")'` and apply in a disposable worktree at
`3394e14c`, not over current production files. Its archived driver
selects the five hard targets and retains all nine laws as assumptions.

The retained row optimization is validated; a profitable completed-subproof
reuse mechanism remains **open**, and no new Inv1758/Inv2973/Inv* derivation has
been added under cover of an optimization. The all-laws and strict 3×60-second
gates remain unpassed. Generation remains owned by `claude/track-gen`.

### Reviewed Track K integration

Merged the coordinator-approved local main `6a3874d3` after the row and rejected
cache experiments. `GDP_COUNT_LEMMA_CUTS=1` remains required for emission; it was
not enabled by this integration. Kept this report on the modify/delete conflict
because the coordinator explicitly requires the Track M measurement journal.
The test-registry conflict retains both tracks' regressions. No generation
source was edited.

`post-merge-v1` confirms **369 proof/kernel/source tests** and **57 selected
support/admission tests**, all passing, plus clean type/lint. Its five focused
verdicts are still 2/5; the trailing pipeline invocation used the invalid mode
`pipeline` and failed as a driver error. It is **not** counted as a successful
pipeline run. `post-pipeline-v1` reruns the actual `production` mode unchanged.

| Latest retained post-merge law | Proved / checked | Counted ms | Wall s |
| --- | --- | ---: | ---: |
| One primary | yes / yes | 984 | 2.178 |
| Inv3915 | yes / yes | 973 | 2.172 |
| Inv1758 | no / no | 5,000 | 4.776 |
| Inv2973 | no / no | 5,396 | 16.508 |
| Inv* | no / no | 5,137 | 13.626 |
| **Sum** | **2/5** | — | **39.260** |

These are per-process uninstrumented focused probes, not a generated-law
family success or a same-VM sum with an earlier generation measurement.
The row-only 29-protocol paired check after the reviewed merge is separately
running as `paired-rows-post-merge-v1`; it changes only `GDP_ROWS_SHARED` between
the sides and pins `GDP_COUNT_LEMMA_CUTS=0` on both. It does not include the
rejected proof caches, the in-flight finer-grained source-context experiment,
or the other lane's generation changes.

`source-contexts-v1` is an uncommitted experiment, not an accepted optimization.
It retains bounded, separate `(goal identity, path)` entries per machine and
tries exact used-row transport across contexts. This deliberately removes the
whole-hypothesis filter that yielded no candidates above; every result is an
ordinary full subtree. Tests include a source whose used row is nested in a
larger conjunction and a target that contains just that row, plus unrelated
scopes and a satisfiable target. Its benefit and verdicts are pending the
remote receipt. No new open-law derivation is claimed.

#### Post-merge row-only paired verdicts

`paired-rows-post-merge-v1` completed all 116 side/phase records. Both sides
prove **27/29** correct protocols and refute **11/29** broken variants; no
proved correct protocol or refuted negative control is lost. All 27 non-Paxos
protocols have matching phase statuses. **Do not call this a clean strict-wall
conservation pass:** `paxos_epr` returns unknown on the control (58.094 s correct,
55.992 s broken), but the shared-row side is killed at the unchanged outer
60-second cap in both phases. Its two timeout deltas remain failures. The
correct MLDR variant is unknown on both sides, at 51.355/50.075 s control/shared;
the broken variant is also unknown on both (small-instance failure). The
correctly invoked original production pipeline in `post-pipeline-v1` returns
**unproved/unchecked** at **47.846 s**. It is not an all-laws-kept success.

#### Source-context v1: real hits, not yet a wall win

The finer-grained transport has **33 foreign-context hits in 1,256 attempts**,
with the same 2/5 complete-law verdicts. Hits by law: 1, 7, 21, 1, 3. These are
not yet attributed as cross-*law* rather than cross-context; the next probe
records the original obligation name. Counted work drops from 984/973 to
948/835 ms for the two complete laws, but no open law completes.

| Source-context v1 | Control wall s | Shared-context wall s |
| --- | ---: | ---: |
| One primary | 2.595 | 3.040 |
| Inv3915 | 3.628 | 3.011 |
| Inv1758 | 7.976 | 7.555 |
| Inv2973 | 27.965 | 28.514 |
| Inv* | 24.002 | 25.100 |
| **Sum** | **66.168** | **67.222** |

The **+1.055 s** total cost is explicit, not a claimed speedup. All 110 targeted
source/row tests and type/lint pass. The candidate remains uncommitted. Its
next experiment shares immutable destination-row indices between transport
attempts (instead of rebuilding an index for each of the 1,256 candidates),
compares source off / source on / source+indices on the same VM, and includes
a reversed-order strict-60-second Paxos pair. No timeout has been raised.

#### Source-context v2: useful cross-law transport, reverse confirmation pending

The same-VM three-way comparison preserves all five verdicts. **Six of the
33 successful transports cross original law/@step obligation names** (0, 3,
1, 1, 1 respectively). The complete ordinary subtrees are emitted and checked;
this is not a trusted lemma or symmetry rule. Sharing the destination-row
index removes repeated full-table scans during unsuccessful candidate matches.

| Law | Source off s | Source on, local indices s | Source on, shared indices s |
| --- | ---: | ---: | ---: |
| One primary | 3.136 | 2.991 | 2.782 |
| Inv3915 | 3.455 | 3.137 | 2.897 |
| Inv1758 | 7.420 | 6.668 | 6.740 |
| Inv2973 | 28.090 | 26.995 | 18.606 |
| Inv* | 22.524 | 23.457 | 20.430 |
| **Total** | **64.626** | **63.250** | **51.456** |

The -13.170 s comparison is a measured pair, not a hardware-independent
percentage or a successful family gate. A reverse-order pair is now running.
All 110 targeted tests and type/lint pass. No additional hard law closes.

The reversed strict Paxos control again times out on the shared-row correct
run; the baseline correct run returns unknown in 57.245 s. Both broken runs
time out in this repeat. This **does not clear** the earlier strict-wall
regression. A separate cache-retention diagnostic keeps the original internal
60-second allowance but allows up to 90 seconds solely to observe and record
an overrun; anything beyond 60 seconds remains a failure, never a success or
budget extension. Its purpose is to locate the row-cache cost before changing
any retention policy.

#### Reverse source confirmation and memory hypothesis

`cache-budget-profile-v1/reverse-family.log` runs the source/index candidate
first and the control second: **40.972 versus 43.035 s** for the five laws,
with identical verdicts and the same 33/6 context/cross-law hit counts. This
confirms a gain in reverse order, but the gain is smaller than the first
51.456/64.626 s comparison; both are reported rather than selecting the best.

Its non-gate Paxos diagnostic actually finishes inside 60 s on both sides
(58.417 s off, 57.580 s on), so wall variability is real. Nevertheless it
records **869,623 retained constraints in 8,192 entries** and **1.366 GB RSS**
with sharing, versus **648 MB RSS** without it. The prior strict timeout
failures are not erased by this diagnostic. The next candidate bounds
retention by 250,000 constraints as well as 8,192 entries, independent of any
law or protocol; eviction only triggers rebuilding ordinary rows. It changes
no proof/search allowance. An isolated strict Paxos pair and a paired family
retention test results are recorded below.

#### Weighted row retention and latest validation

`weighted-row-cache-v1` preserves the 33 source-context hits, six cross-law
hits, counted work and all five verdicts. Retaining at most 250,000 constraint
rows reduces the final cached set from **777,400 to 249,995 constraints**;
five-law wall is **57.526 → 56.803 s** on that matched run. The live-heap
observation falls from 2.115 to 1.485 GB, but RSS does **not** fall (3.741 vs
3.811 GB); no RSS-saving claim is made. The weighted-LRU tests cover
replacement, recency, oversized entries, zero-weight entries and invalid
budgets. The strict Paxos repeat returns unknown on both sides in both phases
(correct: 40.025/42.249 s baseline/candidate; broken: 39.324/43.584 s). This
successful repeat does not erase the historical timeouts.

`final-sharing-v1` passes **373 proof/kernel/source/cache tests**, **57 selected
support/admission tests**, and clean type/lint. Its slower placement produces
the following actual five-law family (the machine and caches are shared):

| Law | Proved / checked | Counted ms | Wall s |
| --- | --- | ---: | ---: |
| One primary | yes / yes | 948 | 2.663 |
| Inv3915 | yes / yes | 835 | 2.593 |
| Inv1758 | no / no | 5,000 | 8.527 |
| Inv2973 | no / no | 5,396 | 32.199 |
| Inv* | no / no | 5,137 | 25.138 |
| **Family total** | **2/5** | — | **71.122** |

The actual generated-law production replay is **unproved/unchecked** and takes
**68.913 s**. Its inner wall observation overruns 60 seconds during synchronous
work; this is a failure, **not** an accepted extension. Thus the latest absolute
measurement still does not fit the whole-MLDR budget, despite the matched
relative wins above. It is not legitimate to substitute the faster 40.972 s
sample for this failed run. Production generation remains with the other lane.
The remaining Inv1758 row is still the alternate active equal/different
ordering half; no new hard-law derivation was added while chasing cache cost.

### Final paired conservation result

`paired-final-sharing-v1` (batch `20261108-170027-uoxy4x`, snapshot
`6930582a3f7b`, submission class, isolated four-CPU child affinity) completed
all **116 side/phase records**. The source/row baseline and both default-on
optimizations have **identical outcomes for all 29 correct protocols and all
29 broken variants**, including strict outer-60-second timeout status.

| Outcome | Baseline | Optimized |
| --- | ---: | ---: |
| Correct protocol: proven | 27 | 27 |
| Correct protocol: unknown | 2 | 2 |
| Correct protocol: timeout | 0 | 0 |
| Broken variant: refuted | 11 | 11 |
| Broken variant: unknown | 17 | 17 |
| Broken variant: timeout | 1 | 1 |

The matched timeout is the broken `sharded_kv_no_lost_keys` variant; it is
not an accepted proof or successful negative check. No broken variant is
proved. Paxos returns unknown on both sides in both phases in this final
run: correct 40.067/42.908 s and broken 39.282/43.227 s baseline/optimized.
Those measured overheads and the earlier two timeout regressions remain in
the journal; this run establishes conservation on this exact snapshot, not
an assertion that all placements are identical.

The original MLDR search is unknown on both sides: **47.219/45.858 s**
baseline/optimized. Its broken variant is also unknown on both sides, with
a small-instance failure. These do not replace the failed **68.913 s**
production observation above and do not establish a successful MLDR run.
The final broad preservation comparison passes, while the complete-law gate
remains **2/5** and the all-laws-kept / strict 3×60-second gates remain
**unpassed**. All jobs for these reported comparisons have finished.

The validated source-context and weighted-retention implementations are now
committed as `67110163` and `0813bfb3`. The earlier rejected whole-hypothesis
cache remains only an archived experiment. Generation source is unchanged.

## Paxos regression correction — baseline invalidation

The coordinator independently verifies **main `6a3874d3` proves `paxos_epr`
3/3** under the original strict 60-second harness. My previous paired gates
used a flag-disabled **Track M** checkout as their baseline and a four-CPU
restriction. They only established equivalence within Track M; they did **not**
establish conservation against approved main. The 27/29 claim therefore hid a
real loss relative to main's 28/29. Those historical results remain above, but
their use as a merge/no-regression gate is **withdrawn**.

New optimization work is stopped. The regression is being bisected using
source snapshots from main, the `rebase-paxos-v1` checkpoint, the Track K merge,
and the current branch. Each revision runs the unchanged original command
`run.ts --ms 60000 --only paxos_epr --skip broken`, under outer `timeout 60s`,
with an exclusive large **8-vCPU** VM, an eight-vCPU / 14 GiB request and
**no extra four-CPU affinity**. Two scheduler submissions remained unplaced
(all compatible warm VMs reported fully occupied); both were explicitly
closed and are not measurements. The runner maps the eight-vCPU request to
four scheduler slots. A temporary four-vCPU request with the same memory
also mapped to four slots; it was not a CPU-affinity experiment. The supported
`SUPERCOMPUTER_SCHEDULER=0` dedicated-VM runner is used to obtain the required
placement without changing or killing other clients’ work. The initial
`55b5846a` hypothesis was rejected by the executed replay: it still proves
Paxos. The narrowed adjacent boundary is recorded below.

All future paired gates use `research/track-m/compare-main.sh` and
`jobs-paired-main.json`: the SHA-256-checked archived baseline is fixed to
`6a3874d3`, not constructed by disabling candidate flags. CPU/memory requests
match the original target harness. No further generation or proof-optimization
change will precede the regression fix and its 3/3 confirmation.

### Executed bisection and rejected prefix-only repair

The normal scheduler became usable again. `paxos-bisect-seed-v5` and
`paxos-bisect-narrow-v1` use exclusive **large**, 8-of-8 pinned vCPUs,
`Cpus_allowed_list=0-7`, no co-tenants, and no extra `taskset`. Each historical
revision is recreated from a `git archive 6a3874d3` plus an exact binary diff
(excluding reports). Main controls run in the same job/VM before and after
historical revisions. Hardware varies between EPYC 9455 and Ryzen 9950X;
only same-job comparisons are interpreted as paired timings.

| Revision | Strict outcome | Harness wall s |
| --- | --- | ---: |
| `d1061c8d` — last recorded good checkpoint | proven / checked | 21.614 |
| `23543462` | proven / checked | 18.550 |
| `55b5846a` — finite recovery enabled | proven / checked | 20.646 |
| **`72f0fe4d` — immediate parent** | **proven / checked** | **20.292** |
| **`616b0c9c` — guarded production recovery** | **timeout / no proof** | **60 s outer cap** |
| `37d6319f` | timeout / no proof | 60 s outer cap |
| `00070df4` | unknown (`time`) | 56.054 |
| `41b97e31` | unknown (`time`) | 58.696 |
| `a374d8f2` — Track K merge | unknown (`time`) | 56.279 |

Thus the first bad adjacent commit is **`616b0c9c`**, not the later cache
changes, the Track K merge, or `55b5846a`. Its parent is `72f0fe4d`. This commit
is below `3394e14c`; the generation lane was notified via `hc send t5r`.
Three-repeat confirmation (`paxos-repair-v1/boundary-confirmation.log`)
proves the parent **3/3**, at 26.198/25.289/23.838 s, and returns unknown/time
for the child **0/3**, at 52.082/53.045/57.816 s. Its same-VM main controls
prove 3/3 at 21.467/22.707/20.881 s.

The direct main/current comparison in `seed-v5/current-v-main.log` is:

| Side | Strict proved runs | Harness wall s |
| --- | ---: | --- |
| Main `6a3874d3` | **3/3** | 22.397, 21.991, 21.420 |
| Track M `844a1baf` | **0/3** (three `unknown/time`) | 55.298, 56.101, 55.561 |

The current-side runs consume the same 15,001,410 full-work units each and
retain 74 found candidates; main closes with 1,135,224 full-work units and 25
found laws. Earlier timeouts remain failures, not budget extensions.

The exact two-file **`f51e8996`** change was applied only to a disposable
`844a1baf` snapshot. Main passed 3/3 on that same VM (18.633, 17.520, 20.379 s),
but the candidate returned **unknown/time at 45.437 s** and 15,001,829 full-work
units. Its strict job stops on this first failed repeat; it is **not** a 3/3
pass, and the patch was not merged. This preservation of the old witness prefix
alone does not repair the regression on current Track M.

### Ordinary-first repair under validation

`616b0c9c` made the previously bounded early recovery substantially stronger:
field/guard/row search now runs before the existing ordinary attempt, including
on the support goals Paxos already proves. The repair keeps those generic,
default-on derivations, but registers them as a deferred fallback. The ordinary
attempt gets its original share first; only an unsuccessful result with time
left may invoke the latest warmed recovery proposal. Both fallback sites are
clamped to the **same original attempt deadline** and the existing 5,000-ms
recovery cap. No new time slice, trusted rule, law, generator or protocol-name
exception is introduced.

`paxos-repair-v1` jointly checks: main/repair Paxos 3/3; parent/bad-commit 3×;
all kernel/production recovery and support tests; type/lint; and the two already
proved MLDR laws against `844a1baf`, including wall times. The MLDR job also
exercises `countedAttempts` separately from the direct `proveFocusedCounts`
entry: an unchanged direct helper is not treated as evidence that the changed
ordinary scheduling route closes. **Results are pending; no repair acceptance
or extra MLDR proof is claimed here.**

#### Joint repair result and remaining Paxos margin

`paxos-repair-v1`: all six scheduling regressions are included in **379 passing
kernel/recovery tests (2,308,615 assertions)**; **67 support tests (1,071
assertions)** also pass. TypeScript and type-aware lint report zero warnings or
errors across 1,100 files. The joint strict proof gate passes:

| Check / entry | Baseline | Deferred recovery | Proof status |
| --- | --- | --- | --- |
| Paxos vs main, three strict runs, harness wall s | 23.075 / 23.908 / 23.028 | 32.034 / 28.171 / 25.871 | **3/3 checked on both sides** |
| MLDR one primary, ordinary attempt, wall s | 3.350 | 3.439 | **checked on both sides** |
| MLDR Inv3915, ordinary attempt, wall s | 3.000 | 3.822 | **checked on both sides** |
| MLDR one primary, direct focused entry, wall s | 3.912 | 2.910 | **checked on both sides** |
| MLDR Inv3915, direct focused entry, wall s | 3.407 | 3.383 | **checked on both sides** |

The MLDR baseline here is the pre-fix `844a1baf` fixed-family fixture, not a
replacement for the mandatory main baseline in protocol gates. Both ordinary
routes get the same original 5,000-counted-ms allowance. Deferral adds **0.911 s**
to their two-law total in this pair (6.350 → 7.261 s); counted work increases
947.682 → 1,190.593 ms and 856.118 → 1,171.215 ms. The direct focused work stays
identical. No direct-entry wall improvement is claimed from this one ordered
pair, and no new MLDR law closes.

**Paxos speed remains open.** The repair is **25.871–32.034 s versus main's
23.028–23.908 s on the same VM**: about **+3 to +9 s**, mean **+5.355 s**. This
restores correctness but does not pass the speed question. That residual cost
consumes margin that the shared solver and MLDR still need; it is not hidden by
the recovered 3/3 verdict. The next acceptance check is the full IC3Syn **29×3**
comparison against main `6a3874d3`, with the same strict placement.

#### Reproduction and remaining gates

`research/track-m/prepare-paxos-revisions.sh` creates the fixed-main archive,
its checksum and exact source patches. For example:

```sh
bash research/track-m/prepare-paxos-revisions.sh runs/track-m/replay-paxos \
  d1061c8d 23543462 55b5846a 72f0fe4d 616b0c9c 37d6319f 00070df4 \
  41b97e31 a374d8f2 844a1baf 844a1baf-deferred=f525d951
supercomputer run --jobs research/track-m/jobs-paxos-repair.json \
  --out runs/track-m/replay-repair --class gate --vm-type large --timing \
  --data runs/track-m/replay-paxos:bisect-input \
  --data runs/track-m/canonical-capture-v1/fixtures:replay-input
supercomputer run --jobs research/track-m/jobs-paired-main-3x.json \
  --out runs/track-m/replay-main-3x --class gate --vm-type large --timing \
  --data runs/track-m/replay-paxos:baseline-input
bun research/track-m/score-main-pairs.ts runs/track-m/replay-main-3x \
  research/track-m/jobs-paired-main-3x.json runs/track-m/replay-main-3x/score.json
```

The last command is a small log scorer, not a proof run. It rejects wrong/missing
baselines, incomplete phases, non-exclusive or non-eight-vCPU placements, and
anything other than 29 protocols × 3 pairs. Outer timeouts override an emitted
positive result; an unknown broken variant is never counted as a refutation.
Five scorer regressions and the full type/lint check pass in `pair-audit-v1`.

The committed repair is **`f525d951`**. Generation integration must wait for
the generation lane's repaired-source gates. The hard MLDR gate remains
**2/5**, and no all-laws-kept/3×60-second MLDR pass is claimed.

### Main-baseline IC3Syn 29×3 result

`paired-main-repair-3x-v1` has completed **87 same-VM pairs / 174 phase
comparisons**, each on an exclusive large VM with all eight vCPUs pinned and
no co-tenants. Pair order is reversed for the second repetition. Baseline
archive identity is `6a3874d3f2c6febe40bb14775884cb327a2cce3c`, verified by the
runner's checksum before every job.

The coordinator clarified the merge gate: **no broken variant may be proved,
and every variant main refutes must still be refuted**. A broken variant that
is unknown on main and times out on the candidate is an unresolved runtime
cost, not a lost refutation. Correct protocols remain held against main run by
run under the strict 60-second cap. The scorer and its regressions implement
that distinction; timeout records are retained rather than renamed to unknown.

| Outcome across three repetitions | Main | Repair |
| --- | ---: | ---: |
| Correct protocol proved and checked | **84 / 87** | **84 / 87** |
| Correct protocol unknown | 3 / 87 | 3 / 87 |
| Broken variant refuted | **33 / 87** | **33 / 87** |
| Broken variant unknown | 51 / 87 | 49 / 87 |
| Broken variant strict timeout | 3 / 87 | 5 / 87 |
| Broken variant proved | **0** | **0** |

All 28 protocols main proves remain proved in each repetition; the three
unknown correct runs are MLDR on both sides. Every main refutation survives.
**The clarified 29×3 conservation gate passes.** This is **not** a claim of
identical timings or identical strict status on all unproved negative cases:
172/174 phase statuses match exactly. The two cost-only differences are broken
Paxos in repetitions 2 and 3: main unknown at **53.943 / 52.191 s**, candidate
killed by the unchanged **60 s** outer timeout. They remain part of the open
Paxos runtime-cost item.

The positive Paxos matrix runs all pass: main **17.402 / 21.437 / 20.913 s**,
repair **16.373 / 20.763 / 22.899 s**. These mixed later deltas do not establish
that the earlier same-VM +3–9 s cost has been solved; the unresolved negative
work still reaches the cap. The generated MLDR pipeline also remains unknown:
main **23.947 / 19.635 / 23.515 s**, repair **46.712 / 38.998 / 46.405 s**.
The next generation work must address that cost, not relabel this as a completed
MLDR proof.

Raw logs, all 87 placements and full `score.json` are in the run directory;
`score-summary.json` is committed. Generation integration remains gated on its repaired-source checks. Per the
next coordinator instruction, row/proof work resumes meanwhile on the
`f525d951` production base rather than waiting idle.

## Resumed proof work: third complete law (Inv1758)

A generic arithmetic fast path and exact-row-checked memo reuse of recursive
field subderivations close both ordering halves of the alternate active send
guard and its remaining row composition. Full ordinary trees are emitted; no
trusted rule, invariant, protocol-name branch or allowance changes.

`inv1758-field-memo-v1`: **proved/checked**, **4,221 counted ms / 14.599 s wall**,
32 recursive field memo hits. `inv1758-complete-v1` repeats this **3/3** at
**4,221 counted ms**, walls **18.953 / 16.751 / 14.952 s**. The hard-law gate is
now **3/5**, not an all-laws-kept or whole-protocol pass.

### Updated exclusive wall breakdown

`inv1758-field-memo-v1`, sequential laws on one exclusive large VM, eight
pinned vCPUs, no co-tenants. Generation here means count/witness candidates,
not production invariant discovery. Seconds:

| Law | Proved/checked | Generation | Construction | Search | Kernel | Total wall |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| One primary | yes/yes | 0.030 | 0.563 | 0.551 | 2.082 | 3.227 |
| Inv3915 | yes/yes | 0.024 | 0.758 | 0.506 | 3.680 | 4.967 |
| Inv1758 | **yes/yes** | 0.031 | 4.543 | 2.000 | **8.588** | **15.163** |
| Inv2973 | no/no | 0.400 | **20.184** | 4.667 | 0 | 25.251 |
| Inv* | no/no | 0.060 | **14.508** | 6.443 | 0.002 | 21.012 |

The sum is **69.620 s before production invariant generation**. The new
complete certificate has a real verifier cost, unlike the earlier failed
probe; no budget-fit claim is made. Kernel time includes all checks during
construction and final admission. Inclusive `rowsAt` cost in the counting
laws remains **14.571 / 10.622 s**, including **10.116 / 8.347 s** in facts.
This is the next optimization target.

### Track K: a real complete-certificate emission pair

`inv1758-complete-v1/lemma-pair.log` runs emission off, then
`GDP_COUNT_LEMMA_CUTS=1`, on the same exclusive VM with the unchanged 60-second
cap. The isolated per-law driver invokes the same `proposeLemmaCuts` entry
point as `counts.ts:finish`, with production-style provenance collection.
It does not claim admission of the other unproved laws.

| Measurement | Off | On |
| --- | ---: | ---: |
| Complete proved/checked | yes/yes | yes/yes |
| Counted ms | 4,220.867 | 4,220.867 |
| Total wall s | **10.436** | **12.499** |
| Proof construction including internal check, s | 7.606 | 8.296 |
| Emission s | 0 | **2.253** |
| Final kernel check s | **2.829** | **1.948** |
| Proposer calls / accepted cuts | 0 / 0 | **2 / 89** |

The start obligation proposes no cut; the step obligation emits 89, all
accepted without fallback. Total emitted nodes change **4,539 -> 4,426**
(main tree 2,577 plus lemma trees). Final checking saves **0.881 s**, but the
single pair's net wall **increases 2.062 s**. This is now an actual emission
measurement, unlike the earlier zero-hook probes, but not a net speedup or
reason to enable the optional flag by default.

Validation: **382 proof/kernel tests, 67 support tests**, clean type/lint.
New regressions cover fast arithmetic, satisfiable refusal and memo transport
with missing source support. The fast-path-only trial advanced the frontier
but did not complete the law; its check was polluted by a standalone `.ts`
baseline mounted at repository root. The baseline is now `.txt` data and the
clean completion suite includes the corrected check. Logs and placements are
retained in the named run directories. Inv2973 and Inv* remain open.

### Subsequent rowsAt experiments: rejected, not shipped

`row-fact-scope-v1` tried a bounded private view so the existing
`leafConstraintsReusing` fact tries could be shared between canonical goals,
without changing row arithmetic or the checker. Both paired orders preserve
all five verdicts and counted work; row-index/source tests and type/lint pass.
But wall conservation fails, so this code is **not retained**.

| Law | Pair 1 off / on s | Pair 2 off / on s |
| --- | ---: | ---: |
| One primary | 3.215 / 2.274 | 2.598 / 2.446 |
| Inv3915 | 3.114 / 2.233 | 2.893 / 2.459 |
| Inv1758 | 15.964 / 12.356 | 14.751 / 13.175 |
| Inv2973 | 22.850 / 21.302 | **22.940 / 29.150** |
| Inv* | 16.856 / 17.465 | **18.837 / 21.813** |

Shrinking the bound to 1024 hypotheses (`row-fact-scope-v2`) regresses overlap
further: **25.006 -> 40.065 s** and **18.984 -> 32.514 s** in the two orders.
The conservative capacity test counts repeated hypotheses toward its reset
threshold and causes **2,335 scope resets** during overlap. This is a diagnosed
candidate defect, not an accepted production change. Heap/RSS instrumentation
is retained; the production builder is restored to the validated implementation.
The rejected patch is `research/track-m/rejected-row-fact-scope.patch`; apply it
only to a throwaway tree before using `jobs-row-fact-scope.json` to reproduce.
The v1 bound is 4096 instead of 1024. These are cost ablations, **not** substitutes
for the main-baseline protocol gate. All raw logs and placements remain in the
run directories. Generation integration follows the coordinator's newly
reported acceptance evidence.

## Generation lane handoff evidence (merged from 256c6707)

<a id="track-gen"></a>

## Track Gen — production invariant-generation cost

Base: **`3394e14c`**, carrying Track M's engine; branch **`claude/track-gen`**.
Comparison main: **`6a3874d3`**. Engine commits: **`6a8792d3`**, **`f00e3642`**, **`cd38afa5`**, **`d9345b9c`**, **`f51e8996`**, **`ecba5321`**, **`c7a82a75`**. The last is the requested cherry-pick of Track M’s `f525d951`; the intermediate per-law experiment **`1eda0752`** is superseded.

**Status: ready for Track M integration. Repaired-source generation and conservation gates pass, including 136 primary jobs and all 87 paired negative phases. Generation falls 61.42% (44.05% including warmup), with identical candidates. One negative-phase UNKNOWN-to-timeout cost delta remains OPEN by coordinator policy. Final engine: `c7a82a75`; checked tooling: `2f0535c6`.**
No full MLDR proof, merge, or new open-law derivation is claimed.

### Generic changes and scope

1. `core/sample-step.ts` compiles hot random-walk steps using the existing
   persistent compiler and compiled request predicates. Cold/unsupported
   machines retain the interpreter. The random draws, request decisions,
   sample order and counted work are unchanged.
2. Cube-only inference now reuses reachable rows already provided by its caller.
   With statically Boolean scalar control, it skips the redundant initial
   random walk before its own small instance and data filter. Numeric scalar
   transitions, normal inference, absent rows and empty rows retain the original
   sampling path. All candidate generators are still called;
   there are no protocol-name tests, generator exclusions or increased budgets.
3. `kernel/model-values.ts` retains symbolic domains for naturals used as
   function arguments, as it already does for map keys. Arithmetic-only
   variables still receive the same ordered boundary proposals. This repairs
   a main-relative regression inherited from Track M, not a row-code change.
4. Structured count witnesses preserve the ordinary prefix. The complete
   ordinary family, including full-context fallback, is tried first. A failed
   family may then use both structured generators under the same absolute
   deadline and counted fuel. The original selectors, admission limits and
   reservation width are unchanged; no protocol name selects the path.

`kernel/prove.ts`, row construction, the trusted kernel, laws and proof budgets
are unchanged from the Track M base. No external solver is used.

### Matched generation timing

Final repaired source: `runs/track-gen-final-gates-v2/`, snapshot
**`f379ecc3d55d`**, engine **`c7a82a75`**, compared with **`3394e14c`**.
Each paired job runs alone on an eight-vCPU **large** boat VM; the official
`placement.json` records exclusivity and zero co-tenants. Every child is a
fresh process; installation is outside the measurement. These are internal
wall measurements, not full-harness or startup-inclusive proof times.

| Repeat/order | Parent generation | Candidate generation | Parent incl. warmup | Candidate incl. warmup |
| --- | ---: | ---: | ---: | ---: |
| 1, parent first | 24.800 s | 8.395 s | 32.123 s | 16.919 s |
| 2, candidate first | 20.668 s | 8.883 s | 27.824 s | 16.555 s |
| 3, parent first | 22.710 s | 9.028 s | 29.366 s | 16.499 s |
| Mean | **22.726 s** | **8.769 s** | **29.771 s** | **16.658 s** |

Production generation falls **61.42%**; including `smallOf` warmup, the
reduction is **44.05%**. All eight records (three uninstrumented pairs plus
the attribution pair) produce identical **24 candidates in identical order**,
SHA256 `5e7acd1171d499bb2e2a21c326c0ca8013d98f8ab18c2bab9401d527de63e4e8`.
Every generator retains its call count, produced count, and retained formulas.
No hand-written family replaces the generated set.

The five separately timed probes take 42.546 s on the parent and 44.057 s
on the candidate. Adding mean generation gives **65.272 → 52.825 s**;
including warmup gives **72.318 → 60.714 s**. These sums are not a single
shared-deadline run, and do **not** establish a complete MLDR proof within
60 seconds. The earlier four-CPU series (`track-gen-final-replays-v1`,
46.51% inclusive reduction) remains historical evidence, not the final number.

### Per-generator attribution and proof use

The last two same-VM runs instrument generation only, without wrapping or
editing the kernel/row code. Full formulas, names and exact milliseconds are
in `records.json` and `generation-verified.json` in the validation directory.

| Generator | Parent ms | Candidate ms | Produced / retained | Direct match among the two checked probes' used premises |
| --- | ---: | ---: | ---: | --- |
| Guard laws | 1.001 | 1.282 | 9 / 0 | None retained |
| Map bounds | 3.397 | 3.782 | 5 / 5 | None |
| Row laws | 0.105 | 0.131 | 0 / 0 | No output on this input; still called |
| Field laws | 0.854 | 0.804 | 63 / 6 | `fields: St[a]=1 -> CT[a]=CfgT[a]`, in both |
| Scan prefixes | 0.285 | 0.217 | 0 / 0 | No output on this input; still called |
| Cubes | **25,585.366** | **8,624.086** | 14 / 13 | None as a direct premise; see context distinction below |
| Carry laws | 1.728 | 2.135 | 0 / 0 | No output on this input; still called |

Cube guard-loosening is a separate **0.182 → 0.181 ms** transformation of the
same 14 cubes, not another 14 generated candidates. Small-state warmup is
**8,355.666 → 7,792.845 ms**; admission/filtering is **71.479 → 75.981 ms**.
These are not added to the inclusive generation total twice.
The earlier trace had **627,047 random requests / 6,615 trials / 64 samples**.
The shared-row trace reads **1,251 provided states, zero trials, zero requests**.
The cube engine's own small-instance/data-filter work remains enabled.

**Proof-context distinction:** the production-generated pipeline has no final
MLDR proof to attribute. The five probes instead use Track M's frozen supplied
invariant context (input SHA256
`4be076f22a8fec41083719358b3518a83b23add5c3dfd26017f772404e7dac24`).
For each successful probe, `usedHyps` traces the checked certificate back to the
actual original law instances; missing analysis is never interpreted as zero
use. Matching to generated formulas permits only bound-variable renaming,
conjunction/disjunction ordering and equality symmetry, not unproved implication.

- **One primary:** uses itself, `Inv866`, and `Inv*`.
- **Inv3915:** uses itself, one primary, `Inv866`, `Inv*`, and
  `p2: before start no terms and no primary`.
- `Inv866` matches the field candidate named above. The other supplied premises
  are not exact generated candidates. In particular, `p2` is a bundled law,
  not a claim that the certificate used three separately generated cubes.
- **Inv1758, Inv2973, Inv*** have no complete certificates: their final-proof
  generator use is **unknown**, not zero. The whole invariant family is not
  proved merely because two relative obligations check.

### Final gates

All 136 jobs in `track-gen-final-gates-v2` have complete receipts, zero job
failures, boat placement, eight-vCPU large workers, and zero co-tenants.

| Gate | Final result |
| --- | --- |
| MLDR generation | Identical 24 formulas/order/hash; all generator calls and outputs conserved |
| MLDR five probes | Identical verdicts and used law instances; two independently checked, three unknown |
| IC3Syn 29 × 3 vs main `6a3874d3` | **83/87 on both sides**, zero lost proofs |
| DuoAI ten pairs | **10/10 on both sides**, zero lost proofs |
| Broken variants | **0/29 proven**; 11 refuted, 17 unknown, one outer timeout |
| Seven isolated test shards | **867 passed, 18 skipped, zero failed** |
| Paired negative phases 29 × 3 | **33/33 main refutations retained**, zero false proofs |
| Type/lint and focused regressions | **81 tests, 75,972 assertions**, including final tooling at `2f0535c6` |

The positive Paxos r1/r2 pairs prove on both sides. In r3, both processes
hit the strict outer cap on the same worker. This is retained in the 83/87
counts, not discarded or relabelled as 3/3. The three ordinary MLDR cases
remain unknown on both sides. Track M's later independent Inv1758 completion
`95cc0925` is deliberately outside this frozen source and these receipts.

The negative-phase comparison has one **OPEN cost-only delta**: broken Paxos
r3 returns unknown on main in 52.001 s; the candidate hits the strict outer
cap. In r1/r2 both return unknown. The strict completion-only diagnostic
therefore returns `passed:false`; the full conservation gate passes under
the coordinator's explicit policy permitting UNKNOWN-to-timeout deltas while
requiring retained refutations and no false proofs. This is not called a
performance win. See `track-gen-negative-{paxos,suite}-v1/verified.json`.

The main matrix's first scheduler batch returned 23 rows before closing;
only its missing 113 jobs were retried on boat. Every final row has verified
placement; no Modal result is counted. A receipt-parser issue initially read
its own redirected log as an 88th negative pair and failed closed. The parser
now selects job logs; that failure is preserved as `checker-self-log-failure.json`.

Earlier failures are not acceptance evidence: IC3Syn v3 had three inherited
Paxos losses; sampler-only timing had two slower comparisons; the per-law
experiment failed one of three strict comparisons; and several batches had
no placements or were explicitly stopped. Their original receipts and the
causal controls below are retained. The earlier four-CPU timing and row-reuse
series are not substituted for the fresh repaired-source measurements.

### Inherited ring-leader regression and isolated repair

The first full DuoAI comparison was **9/10 candidate vs 10/10 main**.
Untouched main and parent controls on the same isolated VM establish that the
loss predates this track: main checks in **17.161 s**, while untouched parent
`3394e14c` returns unknown in **45.306 s**. Both compiled and interpreted
samplers return unknown (45.934 s and 44.937 s). Reusing legacy rows alone
also remains unknown (46.651 s); suppressing only the new model-value
proposals restores the proof (18.028 s), as does suppressing those proposals
and row sharing together (17.253 s). Thus neither sampling nor row reuse is
the cause. Full controls are in `track-gen-ring-{control,base,isolate}-v1/`.

The new value helper was converting function-argument domains into model
constants because a bare key equality suggested an arithmetic boundary.
Commit `cd38afa5` retains symbolic function-key domains while leaving actual
arithmetic-only witnesses unchanged. Frozen key/value regression tests pass;
the ordinary full ring proof checks in **18.237 s** with row sharing enabled.
Type/lint and nine focused tests (6,922 assertions) pass in
`track-gen-model-value-fix-v1/`. No production row or trusted-checker code
was edited. The superseded IC3 v2 batch was stopped and explicitly closed;
its automatically queued retry was also stopped/closed. Partial v2 results
are not final acceptance evidence.

### Inherited Paxos loss: controlled localization

Track M’s independent historical replay subsequently established **`72f0fe4d`
good (20.292 s) → `616b0c9c` first bad (strict 60-second timeout)**;
`55b5846a` also proved, while `37d6319f`, `00070df4`, and current were
unknown/timeouts. Thus `4465559f` introduced the structured insertion but
is **not** established as the regression boundary. The causal removal tests
below characterize the later interaction, not the first bad commit.

The partial IC3Syn comparison preserves all 36 completed pairs in
`track-gen-gates-v3/ic3syn/`; all three losses are Paxos. The untouched
Track M parent also hits the strict 60-second stop, so this is not attributed
to the generation optimization. Scalar-state exploration is nevertheless
now preserved for numeric controls (commit `d9345b9c`). Four independent
cube-row tests pass, including the new numeric and Boolean cases.

Controls in `track-gen-paxos-isolate-v1/` remain unknown with legacy rows
(39.499 s) or with extra arithmetic-value proposals suppressed (42.675 s).
The current path is unknown in 43.586 s. In contrast, same-VM controls in
`track-gen-paxos-cert-control-v1/` prove with only the new structured-fact
insertion removed (31.426 s), with that insertion and singleton picks removed
(28.706 s), or with the complete legacy certificate generator (27.291 s).
Removing singleton picks alone still hits 60 seconds. This establishes a
structured-witness removal control for the later interaction, not a first-bad
commit; row construction was unchanged.
The later prefix-preservation control below shows that ordering alone was
not sufficient: downstream selection also changed.

The prefix-first, capacity-aware repair is committed as `f51e8996`; its patch
is also saved in `track-gen-prefix-proposal.diff`. It retains both structured generators and
the same cap, constructs their tail only if slots remain, and has a frozen
16-entry legacy-prefix regression. The existing checked three-count and
five-count identity tests still pass; 16 focused tests / 43 assertions pass.
The five post-ordering MLDR verdicts and exact used-law instances match the
parent (`track-gen-prefix-check-v1/probes-verified.json`). Their counted work
is not identical: candidate ms are 984.669, 973.236, 5000.781, 5234.405 and
5137.436. This is recorded explicitly, not mislabelled as zero work change.
The first combined validation had a test typing error, then passed all tests
but was killed during Paxos; the next proof was never placed before its
wrapper expired. At that stage, standalone proof validation was still pending. Four large workers reported
occupied gate slots although no live batch reported a running item. Both tracks subsequently confirmed that `cpu=8` is a valid four-slot request;
the earlier request-size suspicion was incorrect. Large workers continued to
report occupied slots, so an intermediate preflight used the supported
direct-boat ownership path. The accepted final matrix instead uses the
restored standard scheduler, with explicit exclusive eight-vCPU labels.
The corrected history is in `track-gen-scheduler-blocker.md`; no shared
scheduler or other client was restarted or modified.

The labelled xlarge diagnostic established that the prefix repair alone is
insufficient: `track-gen-prefix-paxos-v7` is unknown at 41.286 s and 15,000,054
full-work units. Removing only its structured tail gives a checked proof at
23.091 s and 2,698,087 units (`track-gen-tail-control-v1`). A generic
legacy-first, failure-driven structured expansion then proves the same case at
23.539 s (`track-gen-lazy-structured-v1`), with type/lint and focused units
passing. Its integration regression requires a real structured expansion and
an ordinarily checked three-count certificate; it does not merely call a
generator directly.

The intermediate per-law repair `1eda0752` then failed the full preflight:
Paxos candidate **2/3** versus main **3/3**. Candidate times were 47.302 s,
31.888 s, and a strict 60-second kill; main times were 28.556 s, 24.102 s,
and 47.686 s. These failures are preserved in `track-gen-preflight-v1`.
Type/lint and all focused tests passed, the 24-candidate generation hash
remained exact, and all five MLDR probe verdicts and used premises matched.
Direct-boat mode did not emit a `placement.json`, so its timing measurements
are not presented as final isolated-VM benchmark evidence.

`ecba5321` replaces that per-law experiment with a complete ordinary-family
attempt before any structured-family retry. It preserves full-context fallback
and shares the original absolute deadline/fuel. The isolated xlarge control
(`track-gen-family-control-v1`) proves in **23.434 s**, with **9,626,903 total /
2,698,087 full work**, exactly the successful tail-removal control's work.
The new end-to-end regression requires structured-family fallback, a checked
three-count certificate, and rejection of an off-by-one partition; it passes
all six assertions. The earlier per-law selection changes have been removed.

The first final matrix, `track-gen-final-gates-v1`, was stopped on the request
to integrate Track M’s validated repair **before** acceptance. Fifteen completed
jobs are preserved in `track-gen-final-gates-v1-partial/partial.json`; that batch
is explicitly closed, and these partial results do not count as final gates.

**`c7a82a75`** cherry-picks Track M’s **`f525d951`**. Conflict resolution passes
the existing structured-family parameter through the deferred proof callbacks
and includes both regression files in the shards. Track M’s repair orders an
ordinary attempt before its focused recovery; the Track Gen layer defers
supplementary structured witness families until the ordinary family fails.
Neither adds an allowance or changes the trusted checker. The combined source
passes type/lint and **81 focused tests, 75,972 assertions**, on an exclusive
8-of-8-vCPU large worker (`track-gen-m-repair-check-v1`).

The final matrix is `research/track-gen/acceptance-jobs.json`, 136 jobs,
plus three strict negative-Paxos pairs and 84 other paired negative phases.
The production source is frozen at `c7a82a75`; subsequent commits only add
acceptance tooling and evidence. The final tooling recheck passes in `track-gen-final-source-check-v2`.
No owned jobs or batches remain running. No main-branch merge or publish is performed here;
Track M will integrate the gated generation commit and check its independent
later changes together.

### Reproduction and recorded acceptance

Machine-readable acceptance is in `runs/track-gen-final/acceptance.json`.
`runs/track-gen-final/SHA256SUMS` binds the runtime source, verification tools,
final receipts and preserved controls. Raw logs retain their original whitespace.

Recheck the recorded, repaired-source evidence without running a prover:

```sh
bun research/track-gen/collect-acceptance.ts runs/track-gen-final-gates-v2
bun research/track-gen/check-gates.ts runs/track-gen-final-gates-v2
bun research/track-gen/check-generation.ts runs/track-gen-final-gates-v2
bun research/track-gen/analyze-profiles.ts runs track-gen-final-gates-v2
bun research/track-gen/collect-acceptance.ts runs/track-gen-negative-suite-v1 research/track-gen/negative-suite-jobs.json
bun research/track-gen/collect-acceptance.ts runs/track-gen-negative-paxos-v1 research/track-gen/negative-paxos-jobs.json
bun research/track-gen/check-negative-suite.ts runs/track-gen-negative-suite-v1 runs/track-gen-negative-paxos-v1
```

For a fresh run, `bash research/track-gen/prepare-data.sh` rebuilds baseline
archives from immutable commits in this checkout, without touching another
worktree. Run the three corresponding jobs files with `supercomputer run`,
`--data runs/track-gen-data:replay-input --class gate --vm-type large --timing`,
then run the same receipt checks. `final-check-jobs.json` runs type/lint and
focused regressions. No proof budget or test timeout is raised.

## Track M integration of the gated generation lane

Merged `claude/track-gen` at **256c6707**, production source **c7a82a75**,
after its reported gates. Conflict resolution retains all of the following:
ordinary-first deferred recovery from `f525d951`, deferred structured families,
the optional Track K emission hook and its scoped provenance, the new complete
Inv1758 derivation, and both lanes' test registrations and report evidence.
A merge regression confirms provenance is enabled and restored through both
direct and generated admission paths. No rejected row-fact cache is included.

The generation lane's pre-integration evidence is kept above and in its
committed receipts: identical 24 generation candidates, 83/87 correct proofs
on both sides of its main-baseline matrix (Paxos r3 times out on both in that
placement), all 33 main refutations retained, no broken variant proved,
DuoAI 10/10, and seven passing shards. These are **not** claimed as a newly
rerun 87-pair gate on the combined Track M source.

### Combined-source remeasurement, one exclusive VM

`generation-integrated-v1/family-and-production.log` runs the five-law family
and original generated-law production pipeline sequentially on the same
exclusive large VM, eight pinned vCPUs, no co-tenants. Seconds, exclusive phases:

| Law | Proved/checked | Generation | Construction | Search | Kernel | Total wall |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| One primary | yes/yes | 0.041 | 0.637 | 0.523 | 1.428 | 2.630 |
| Inv3915 | yes/yes | 0.037 | 0.667 | 0.383 | 1.586 | 2.673 |
| Inv1758 | **yes/yes** | 0.030 | 4.905 | 2.192 | 6.660 | **13.787** |
| Inv2973 | no/no | 0.197 | **15.550** | 5.061 | <0.001 | 20.808 |
| Inv* | no/no | 0.060 | **14.291** | 6.391 | 0.001 | 20.743 |

Family sum **60.644 s**, before production generation. This remains a budget
failure and **3/5**, not a successful whole-protocol run. The count-law
`rowsAt` inclusive costs are still **10.955 / 11.426 s**. Hardware/run variation
and changed generation make this an updated measurement, not a claimed paired
row-construction speedup.

The actual original generated-law pipeline is still **unproved/unchecked**,
`not proven: one primary per term`, at **43.784 s** wall:

| Production phase | Wall s |
| --- | ---: |
| Generation (all measured generation work) | 14.857 |
| Search | 20.063 |
| Construction | 8.848 |
| Kernel | 0.005 |
| Residual/startup/unclassified | 0.010 |

The production phase total is not the lane's isolated generation benchmark;
its standalone 22.7 -> 8.8 s result is retained as separately scoped evidence,
not substituted for this pipeline measurement. No 60-second proof success or
all-laws-kept result is claimed.

Combined-source validation: **400 proof/generation tests**, **12 admission,
structured-fallback and deferred-recovery tests**, and both type/lint runs
pass. Remaining work is the two active-action witness chains and their
construction cost; the row-cache trials above do not close that gap.

## Track M active-source derivations after the generation merge

**Acceptance is still 3/5.** No new complete law or complete MLDR proof is
claimed. The current pre-state-ceiling/ordering patch is a candidate awaiting
the main-baseline gate below, not an accepted default optimization.

### What the source probes establish

The new `research/track-m/active-source-probe.ts` reconstructs a cold focused
packet and checks conditional active-path trees. These are deliberately not
whole-law admissions. On exclusive large VMs with all eight vCPUs pinned:

- Inv* setup and copy active branches check in both the all-carried and first
  carried-set probes. Both enumerated send guard branches also check in the
  first-carried probe. This covers only the branches actually enumerated.
- Inv* reconfiguration and the probed Inv2973 active branches remain open.
- Model-selected sibling-law instances are ordinary family instances, filtered
  by the existing count-key freshness rule. Bounded retries did **not** close
  either reconfiguration branch, so this proposer is **not connected to the
  production default**. It is exercised by research and renamed unit fixtures.

The exact retained source query corrects an earlier attribution: the first
rejected five-term bound was `|X| + |Q2| <= |X union S|`. Its source admits a
member of both Q2 and S; that inequality is not justified by adding Inv1758.
This SAT source is not a reachable protocol counterexample. The required
post-backing/Q2 union is already present in the certificate (instance 39 in
`source-certificate-v1`); it must not be confused with this rejected pre-size
union (instance 46).

### A concrete prerequisite now derives

The valid guarded ceiling `CfgT[j] <= CT[i]` under an active committed quorum
was unknown in a 321-hypothesis diagnostic source retaining instances at
removed witnesses. Keeping the same pre-state count instances while removing
those discarded-witness instances reduces the source to **136 hypotheses**.
Both isolated target variants then check: **179.676 / 135.629 ms** in
`source-ceilings-clean-v1`. The source still assumes the original family before
the step; no extra invariant or trusted arithmetic fact is introduced.

`core/count-recovery/pre-state-source.ts` implements this weakening generically:
retain pre-state count reads and their original CInst order, remove assumptions
that depend on discarded post witnesses, and preserve all remaining terms.
The candidate caller tries that source inside the existing 250-counted-ms
ceiling window and transports any proposed tree back to its full goal. The
isolated source is checked; a transported cut inside an otherwise unfinished
whole goal is still a **proposal**, not a newly admitted complete certificate.
The ordinary final check is unchanged.

The subsequent ordering trial is also structural, with no law/protocol names:
unchanged-row frames remain first; an existing five-term carried-union
candidate whose post-count touches the active written row is considered before
speculative cross-row copy/size comparisons. No candidate generator is removed
and no candidate inequality is assumed true.

### Updated scoped measurements and validation

These are separate diagnostic runs, **not paired protocol timing claims**:

| Run / scope | Checked complete law? | Wall |
| --- | --- | ---: |
| Pre-state ceiling candidate, Inv* focused INIT+STEP runner | no / no | 17.348 s |
| Written-row ordering candidate, same focused runner | no / no | 16.767 s |
| Pre-state ceiling candidate, active Inv* reconfiguration only | no (conditional branch still open) | 4.203 s |
| Written-row ordering candidate, same active branch | no (conditional branch still open) | 4.239 s |

The previous five-law wall table remains the last measured complete family
breakdown; these numbers do not replace it or establish a speedup. Inv2973 and
Inv* remain open, and the all-laws-kept / 3x60-second gates remain unpassed.

`reconfigure-support-v1` passes **369 tests / 2,308,593 assertions** and type/lint.
`pre-state-ceiling-v1` passes **118 focused tests**, including source weakening
and checked transport, and type/lint. Earlier failed checks and the overly
strong one-round fixed-point test expectation are retained in their raw logs;
the renamed proposer is bounded and may legitimately need multiple rounds.

### Required acceptance gate: completed, rejected for an MLDR cost regression

`source-ceiling-main-3x-v1` ran the frozen candidate against **main 6a3874d3**
using `research/track-m/jobs-paired-main-3x.json`: all 29 IC3Syn protocols, three
repetitions, correct and broken variants. The gate uses exclusive large VMs,
all eight vCPUs pinned, the original strict 60-second harness, and
`score-main-pairs.ts`. The candidate patch and its parent are preserved in
`runs/track-m/source-ceiling-gate-input/`. The final score is in
`runs/track-m/source-ceiling-main-3x-complete-v1/score.json`; **noRegression is
false**. All 84 main correct-protocol proofs and all 33 broken-variant
refutations survive; neither side proves a broken variant. Correct Paxos is
3/3 on both sides. There are 170/174 exact phase-status matches and three
broken-Paxos unknown/timeout cost-only differences. The fourth difference is
**correct MLDR repetition 3: main UNKNOWN at 27.595 s, candidate strict timeout**.
This is recorded as a cost regression, not a successful gate.

The original Paxos-r1 job hit its outer setup watchdog without producing any
PAIR header. Only that incomplete job was replaced, using the archived parent
plus the captured candidate patch, on an exclusive large VM with eight pinned
vCPUs and the same four strict 60-second protocol deadlines. Both original and
retry receipts are preserved. The combined directory uses symlinks to those
original logs and records the replacement and placement in `provenance.json`.

Further live-write-source ordering and natural-arithmetic/core-chain experiments
were made **after** this snapshot. This comparison does not cover those later
runtime changes. None is accepted as a default, and the complete-law verdict
remains 3/5. Their source snapshots and receipts are retained separately in
`written-row-replacement-v1`, `written-source-v1`, `natural-selection-v1`, and
`core-chain-v1`.

### Conditional written-row diagnosis (not a complete-law proof)

Pinning both quantified rows to the active write row and allowing a diagnostic
6,000-unit local window produces an **original-kernel-checked conditional Inv***
proof (`equal-row-source-v1` and `core-chain-trace-v1`). The latter is 4.633 s
wall, versus an unproved 1.707 s at the original 1,500-unit row window. These
are diagnostic runs on exclusive eight-vCPU large VMs, not a raised production
budget or a whole-law result. The trace shows that the valid post-count/carried
union is constructible (115 ms in the latter run), but selection spends most
of the window on refuted old-row size comparisons before deriving the carried
set's pre-state subset bound. Natural-case closure and deferring redundant
closure while a selected core is incomplete are being tested; the full Inv*
remains unproved (`core-chain-v1`: 14.598 s wall). No speed claim is inferred
from these separate, heterogeneous placements.

### Narrowed deadline repair and a fresh acceptance gate

The post-gate replacement-map ordering, natural-core refinement, and deferred
closure experiments were backed out of production source: none closed the full
Inv*, and a current-source original-harness MLDR pair still timed out. Their
complete patch is retained as
`source-ceiling-gate-input/post-gate-experiments.patch`.

The next candidate is the original frozen source plus **early deadline exits**
in `fieldBoundLemmas`: an expired caller must not inspect the machine, rebuild
count rows, or enter another field-source phase. No proof budget is increased.
The regression test uses a machine that throws on inspection after expiry.

Three fresh original-harness MLDR pairs (`source-budget-v1`) now have identical
UNKNOWN verdicts, with no strict timeout:

| Repetition | Main 6a3874d3 | Deadline repair |
|---|---:|---:|
| 1 | 30.502 s | 44.232 s |
| 2 | 22.566 s | 41.150 s |
| 3 | 23.142 s | 36.565 s |

These do **not** establish a successful MLDR proof, and the positive runtime
cost delta remains open. The initial full-check job lacked the ignored vendor
sources; it was not a compiler success. Validation was resubmitted through the
existing `prepare-vendors.sh` path along with all five hard-law checks.

A fresh 87-pair gate, `source-budget-main-3x-v1`, is running against approved
main on the frozen narrowed candidate in `source-budget-gate-input/`. It uses
`jobs-paired-main-3x-budget.json`; only the outer per-job setup headroom is 420 s.
Every correct/broken protocol invocation still has the original strict 60 s
watchdog and `--ms 60000`. This pending gate must not be conflated with the
rejected first gate or with later research-only probe changes.

The narrowed candidate also reproduced the timeout in that wide run: completed
`pair-mldr-r3` has main UNKNOWN at **46.616 s** and candidate strict timeout.
The narrowed repair is therefore **not accepted** despite its three earlier
matched pairs. Its completed focused validation is: one-primary checked
2.511 s; Inv3915 checked 2.296 s; Inv1758 checked 10.661 s; Inv2973 unproved
18.192 s; Inv* unproved 15.197 s (separate exclusive eight-vCPU placements).
Prepared type/lint reports zero warnings/errors, and 119 focused tests pass.

The identified gap is that the new exits check only the counted-work clock,
not the prover's independent `pastWall()` deadline. After the wall expires,
kernel search stops but the counted clock need not advance while source
construction continues. A further repair checks the existing wall predicate
at field-source entry/loops, finite-case entry/loops, and focused recovery.
Its regression test keeps counted budget available under an expired wall and
requires all three entry points to return without inspecting the machine.
`wall-budget-v1` validates this repair locally: prepared type/lint reports zero
warnings/errors, and **120 tests pass**, including the expired-wall test.
Three strict original-harness MLDR pairs remain UNKNOWN on both sides:
main/repair 43.626/48.333 s, 22.519/37.454 s, and 25.297/45.490 s.
This is not a complete MLDR proof and does not close the runtime-cost item.

The five-law result is still **3/5**. Current independent-probe wall times are
one-primary 1.841 s (checked), Inv3915 2.366 s (checked), Inv1758 11.817 s
(checked), Inv2973 14.686 s (unproved), and Inv* 12.802 s (unproved).
A final-source 87-pair gate is pending in `wall-budget-main-3x-v1`, with its
snapshot preserved in `wall-budget-gate-input/`. No runtime files are changed
while that snapshot is under test; subsequent changes are research probes only.

The counted-clock-only predecessor's wide run completed with the already
recorded MLDR regression and one incomplete `learning_switch_i4` setup. It is
rejected; that incomplete job is not counted as a successful negative check.

### Learned count-core replay: negative ablation

`checked-core-replay-v1` and `core-source-context-v1` test a research-only replay
of the count bounds reported used by the checked conditional Inv* proof. They
do not alter production candidate generation. The 13-instance replay remains
unproved at both the 1,500- and diagnostic 6,000-unit windows. Retaining all
pre-state instances (32 total) restores the checked field ceiling, but the
conditional count proof still fails at both windows. This is evidence against
promoting index-only core replay or dropping the other candidates. Reusing
complete, transported source subproofs—not just their candidate indices—remains
the appropriate next hypothesis.

### Default speculation withdrawn after a third strict-timeout failure

The wall-aware candidate's official `pair-mldr-r2` emitted UNKNOWN at
59.955 s but exited under signal 137, so it is still a strict timeout and that
candidate is **not accepted**. All three completed correct-Paxos pairs remain
proved on both sides, but that does not excuse the MLDR cost regression.

Inspection of `searchCounted` confirmed that its existing wall bound is twice
the counted budget, with small-instance construction before that wall starts.
Thus the missing `pastWall()` checks are real deadline hygiene defects, but
fixing them alone cannot guarantee the external 60-second harness cutoff.
The dominant new speculative work must instead be removed or made cheaper.

The unaccepted eager pre-state source attempt and written-row union priority
have now been withdrawn from the **default** field-bound path. Its prior narrow
source and ordering are restored. The generic deadline checks remain; the
pre-state source helper, witness proposer, tests, and rejected-trial receipts
remain available for research. This does not declare those experiments to be
accepted default optimizations. `conservative-source-v1` is rechecking the
expected 3/5 full-law result and strict MLDR pairs before any further gate.

That conservative validation completed: prepared type/lint is clean and all
120 tests pass. The five-law result remains 3/5: one-primary checked 2.050 s;
Inv3915 checked 2.314 s; Inv1758 checked 11.786 s; Inv2973 unproved 14.794 s;
Inv* unproved 15.966 s, on independent exclusive eight-vCPU large placements.
Its three strict MLDR pairs are UNKNOWN on both sides, with main/repair times
34.516/44.209 s, 22.164/37.688 s, and 25.724/43.873 s.

The preceding wall-aware speculative matrix is now fully scored:
`wall-budget-main-3x-v1/score.json` records 173/174 matching phase statuses,
84/84 conserved main proofs, 33/33 conserved refutations, zero broken proofs,
and the one MLDR-r2 strict-timeout regression. It is rejected, not silently
relabelled as a pass.

`conservative-main-3x-v1` is the **completed, passing conservation gate** for the
restored default strategy, against main 6a3874d3 with the original strict harness
and exclusive pinned large placement. Its exact patch and parent are in
`conservative-gate-input/`; `conservative-main-3x-v1/score.json` records
**noRegression: true** and no invalid pairs.

| Three repetitions, 29 protocols | Main | Conservative repair |
|---|---:|---:|
| Correct protocols proved | 84/87 | 84/87 |
| Correct protocols unknown | 3/87 | 3/87 |
| Broken variants refuted | 33/87 | 33/87 |
| Broken variants proved | 0 | 0 |

Every main proof and refutation is preserved run by run. Correct Paxos is 3/3.
There are **173/174 exact phase-status matches**. The sole mismatch is broken
Paxos repetition 2: main UNKNOWN at 52.009 s, repair strict timeout (137).
It is a cost-only difference under the established gate definition, not a
successful negative check. The broken-Paxos runtime cost item remains OPEN.

MLDR is still UNKNOWN, not proved. Its three main/repair times in this final
gate are 25.563/43.585 s, 26.009/46.327 s, and 25.468/43.918 s. The positive
runtime delta remains OPEN; the final candidate no longer has the prior
correct-MLDR strict timeout. The complete hard-law result remains **3/5**.
Inv2973, Inv*, the all-laws-kept success gate, and 3×60-second complete MLDR
proof success are not claimed.

The final working-tree prepared check (`final-source-check-v1`) also reports
zero type/lint warnings/errors and 120 passing tests. The current core/kernel
patch was compared byte-for-byte with the frozen final-gate runtime before
committing; subsequent edits were research-only probes and this report. The
validated runtime repair is committed as `fd2d1dcb`; the research helpers remain
unwired from the default proof path.

## Inv2973: captured active-action source-count gaps for Section 5

<a id="inv2973-active-source-gap-table"></a>

**Read-only diagnosis after acceptance of `fd2d1dcb`. No default-path edits or
new proof searches.** Section 5 was absent when this inventory began and landed
while the table was being finalized; it has now been read. The evidence is the canonical `Inv2973 ... @step` input and the existing
`active-source-narrow-v1/overlap-{0,1,5,6}.log`, setup/copy follow-ups in
`active-source-resume-v1`, and `source-family-v1/overlap-family-source.log`.
All eight captured conditional outcomes are unproved. This is not a claim that
every action has been freshly replayed or that every listed dependency is a
separately observed failing leaf.

### Exact packet and notation

`research/track-m/audit-inv2973-gaps.ts` checks the recorded candidate references
against two metadata-only reconstructions of those cold packets, writes
`inv2973-gap-layout-v1/audit.json`, and performs **no proving**. The two print-only
boat jobs took 1.17 / 1.47 seconds of job time; 42.9 seconds batch elapsed includes
scheduling. This is not a proof-runtime measurement.

- `F` = first-carried packet: **41 reads, 156 candidates = 149 pairs + 7 singletons**.
- `A` = all-carried packet: **41 reads, 175 candidates = 168 pairs + 7 singletons**.
- Neither packet contains **any** three-term partition or five-term union.
  This diagnoses these captured cold packets, **not** the engine's entire later
  structured-family retry. The prototype calls `certFor(..., most=1000)`;
  its legacy pair prefix fills before its structured tail, then focusing removes
  entries. Generator existence alone does not put a needed identity in this packet.
- `F84 (w$275)` means candidate index 84 in F, with source member witness
  `w$275`. A candidate `+p -q` asks for `p <= q`; its counterexample/source
  branch must prove the corresponding pointwise predicate at that witness.
- `X_z(k) = Config[64*z+k]`, `V(z)=(CfgT[z],CV[z])` lexicographically,
  `old[z]=count(X_z(k) and V(k)<=V(z))`, and
  `D(z) := 2*old[z] <= cfgSize[z]`. `#` denotes post-state. Every member below
  is in `0 <= k < size <= 64`.
- Shared read IDs: `r$0/1=cfgSize#[a/b]`, `r$2/3=old#[a/b]`,
  `r$4=xn#[a,b]`, `r$5=xm#[a,b]`, `r$6=xm#[b,a]`;
  `r$7=inX`, `r$8=inS`, `r$9=inQ2`, `r$10=xNotS`,
  `r$11=xAndS`, `r$12=sNotX`, `r$17=cfgSize[0]`,
  `r$22=cfgSize[i]`, `r$23=old[i]`. All 41 bindings are in the audit JSON.

### Gap table: needed fact versus what is actually available

Rows marked **dependency** name the valid fact a structural design must deliver;
rows marked **observed** also identify a failing source in the saved trace.
Symmetric `a/b` cases are written together, not claimed as independently checked.

| ID / goal and action condition | Precise missing delivered fact / source obligation | Count/member read | Does a captured candidate supply it? |
|---|---|---|---|
| **P — observed**, pick (`op=0`), unwritten row `z != 0` | `old#[z]=0`, hence `D#(z)`. At its source member, combine `noneCopied` with `p1(z,k)` to show `Config#[64*z+k]=0`. The changed-row case `z=0` must be split off: its old count need not be zero. | `r$2` / `r$3`; `frame$36` / `frame$38` in F. | **Present but conditional:** F146 / F148 are zero-count proposals. They fail on the unsplit active path; no theorem `old#[z]=0` for every z is missing. Setup follow-up remains unproved with A. |
| **P/C diagonal — dependency**, both law rows are the same written row (pick or copy) | `xm#[a,b]=xm#[b,a]=0`; transport the common row size/intersection and close the integer half inequalities. Do not require the common row to be empty. | `r$5/r$6`; F152 `frame$42`, F154 `frame$44`. | Zero-difference proposals **present**. F/A38 and 39 supply `xn# <= cfgSize#`; the reverse `cfgSize# <= xn#` directions are **absent**, as are partition triples. The captures do not establish a checked diagonal sub-derivation. |
| **C — observed**, copy (`op=1`), target row `i`, source row **0** | Correct transport is `cfgSize#[i]=cfgSize[0]`, not `cfgSize[i]`. For another row y, split `CV[y]=0` (p1: empty) from `CV[y]=1` (p2 plus Inv1758(y,0,k): same row as 0). These member facts must reach the actual transport witnesses. | Correct size pairs `r$0-r$17`, `r$1-r$17`: `frame$24..27`. Intersection/difference with row 0 use `r$27..29`. | Size equality **present**: F134–137 / A149–152. `xn#[a,b] <= xn[0,b]` is F/A49 (`w$196`); reverse-direction difference `xm#[b,a] <= xm[b,0]` is F/A86 (`w$278`). The exact `xm#[a,b] <= xm[0,b]` pair is **absent in both**. Recorded failed F110/F112 compare with the old destination size `r$22`, which is not the required copy fact. |
| **R1 — dependency**, reconfigure (`op=5`), before replacing row i | `inQ2 <= old[i]` from `Q2(k) => X_i(k) and V(k)=V(i)`, so majority Q2 rules out `D(i)` before the step. | `r$9-r$23`; member `w$371`, with committedQuorum and Q2-subset flags at that same member. | **Absent in F; present in A114.** A113 (`w$370`) also proposes `inQ2 <= cfgSize[i]`. Presence is not a checked source proof. |
| **R2 — dependency**, reconfigure, other row y not disabled | Derive `V(i) <= V(y)`: if `V(i)>V(y)`, Q2 and `old[y]` are disjoint majorities inside `X_i union X_y`, contradicting pre-overlap. This needs the **conditional** five-term bound `inQ2 + old[y] <= xm[i,y]+xn[i,y]+xm[y,i]` and row partitions. Instantiate pre-Inv2973 at **(i,y,hx,h_y)**, not the post-written row's half. | For y=b: `r$9+r$16-r$25-r$24-r$26`; for y=a: `r$9+r$15-r$32-r$30-r$31`. Source member must simultaneously read Q2 and the old predicate at y. | Required five-/three-term candidates **absent in F and A**, so there is no such source member in either packet. Cold `countRowBridges` preserves u/w while changing row coordinates; it does **not** supply the hx-substituted tuple. The eight recorded model-retry rounds add no Inv2973 instance. |
| **R3 — dependency**, reconfigure, establish equal metadata with surviving y | First `CfgT[y] <= CT[i]`: under the opposite inequality Q2 is a subset of `bq[i,y]`, contradicting Inv* and Q2 majority. Combine with R2 and `CfgT[i]=CT[i]`; Inv3915 then gives `CV[y]<=CV[i]`, hence `V(y)=V(i)`. Instantiate **Inv1758(y,i,k)** at each subsequent transport member to obtain `X_y(k)=X_i(k)`. | y=a: `r$9-r$38`, member `w$386`; y=b: `r$9-r$40`, member `w$388`. Then the members of the missing R4 bridges. | Q2/bq pairs **absent in F**, **present in A122/A123**. The sibling laws exist. The recorded retry adds Inv3915 and Inv1758 at `frame$36/38` and later witnesses, but still does not check the branch. Those old-count-zero witnesses are not substitutes for the missing R4 bridge witnesses. |
| **R4 — dependency**, reconfigure, `a=i`, `b=y!=i`, after R3 | Deliver `cfgSize#[i]=inS`, `xn#[i,y]=xAndS`, `xm#[i,y]=sNotX`, `xm#[y,i]=xNotS`, pointwise using `X_y=X_i` and the write `X_i#=S`. Swap the last two relations for the mirrored orientation. | Exact post/request bridges include `r$4-r$11`, `r$5-r$12`, `r$6-r$10`; each needs a fresh common member for its two predicates. | The size equality is **present**, F140/141 (`frame$30/31`) or A155/156. All three exact intersection/difference bridge pairs, **in both directions, are absent in both F and A**. Existing same-declaration copy candidates cannot be reported as these cross-declaration request bridges. |
| **R5 — dependency**, finish reconfiguration overlap arithmetic | `inX=xNotS+xAndS` and `inS=sNotX+xAndS`; with R4, infer target halves `u=hy`, `w=hx` (or reversed orientation), and transport the guard overlap formula to the post law. Natural subtraction cases must preserve these equalities. | `r$7-r$10-r$11` and `r$8-r$12-r$11`, with partition members; guard halves hx/hy and target halves u/w. | No three-term candidates in either packet. Guard half inequalities are present, but they alone do not relate the free count reads. This is not fixed merely by adding another ordering of pair candidates. |
| **S1 — dependency**, send_config (`op=6`), written row j | `old#[j]=old[i]`; for y!=j, `old#[y]<=old[y]` because only V(j) increases. Use the former for the copied row and the latter to preserve a disabled other row. | `r$2-r$23` / `r$3-r$23`, `frame$4..7`; unchanged-row witnesses `w$104` / `w$145`. | Copy-old pairs **present**: F114–117 / A129–132. Monotonicity pairs **present**: F/A20 and 30. They require the row/guard conditions, not unconditional cross-row equality. |
| **S2 — observed**, send_config, `a=j`, `b=y` (and mirror), both guard branches | At a common member, transport `xn#[j,y]=xn[i,y]`, `xm#[j,y]=xm[i,y]`, `xm#[y,j]=xm[y,i]` through the actual flattened-row copy; retain its row-domain and offset equalities. Branch 0 is equal config term / larger CV; branch 1 is larger config term. | F47 (`w$193`), F119/120 (`frame$9/10`), F84 (`w$275`), with reverse candidates F118/F133. F84 reads `Config#[64*y+k]` and `Config#[64*j+k]` against pre `Config[64*y+k]` / `Config[64*i+k]`. | **All three equalities have both directional candidates.** F84 is still proposed=false in the tails of **both** saved guard branches, and both conditional checks fail. This is a member-source/row-composition gap, not an absent count expression. |

### Rejected distractions must not become additional assumptions

F146/F148 (`old#[a/b] <= 0`) recur as early SAT sources in pick, copy,
reconfigure, and both send branches. They are legitimate speculative candidates,
not valid unconditional invariants. Likewise F64 compares `xm#[a,b]` with the
**reversed** pre difference `xm[b,a]`, and reconfiguration tails try F66/F68/F70
against unrelated pre differences. Such bounds require additional alias/row
conditions and may simply be false under the current path. A SAT source here
is neither a reachable counterexample nor evidence that the missing theorem is
one of those overstrong inequalities.

The reconfiguration retry is particularly diagnostic: eight rounds add only
Inv3915, Inv1758, and p1 instances, while the same zero-old sources and wrong
copy differences persist. The valid chain is R1–R5, not a demand to prove all
of the failed candidates.

### Coverage limits / next design tests

- **BecomeLeader (`op=4`)** has no matching current Inv2973 active-source receipt
  in this captured series. Its syntactic dependency is `inS<=old[i]` (F/A99,
  member `w$338`, canVote/subset instances), plus monotonicity of old[y] for
  y!=i. Because rows do not change, excluding pre-D(i) should allow pre-overlap
  to carry forward. This is a **coverage hole for Section 5 testing**, not a new
  measured failing source or a claim that the branch checks.
- Start (`op=2`) and UpdateTerms (`op=3`) do not change Config/CV/CfgT, the fields
  read by Inv2973's counts. They add no corresponding source-count dependency;
  no new per-action checked certificate is claimed here.
- The all-carried packet is only a diagnostic alternative. The default focused
  loop already tries all-carried then individual carried choices; this table
  does not propose disabling a generator, changing that order, or enabling a
  research fallback.

Section 5 now proposes derivability closure followed by one arithmetic query.
This inventory supplies a concrete precondition for its Inv2973 test: the named
R2/R4/R5 facts are not in these cold packets. Closure over the existing pool does
not directly add those absent candidates; it may find another proof, but their
absence must not be mistaken for a failed ordering. The first/all packet scope
here is not the separate 73-instance equal-row Inv* test in Section 5.6.

The design can be tested against the table without a full protocol run: show
which missing R2/R4/R5 candidate and which correctly scoped witness/half tuple it
constructs, then replay that captured source. Existing S2 candidates instead
need their already-named member sources discharged. **No proof budget change,
new invariant assumption, default-path edit, or improvement in the 3/5 complete
law result is claimed.**

The audit verifies all eight captured records against the reconstructed count
indices. Its isolated one-file type-aware lint check passes with zero warnings
and errors (`inv2973-gap-audit-check-v1/audit-check.log`, 1.46 seconds job time).
Together with the two metadata jobs, this work used about four seconds of boat
job time, no new proof search, and no default-path edits.

Rebuild this evidence (read-only except the output JSON):

```sh
bun research/track-m/audit-inv2973-gaps.ts
# Optional, metadata-only packet reconstruction; no prover is called:
supercomputer run --jobs research/track-m/jobs-inv2973-gap-layout.json \
  --out runs/track-m/inv2973-gap-layout-replay --class interactive \
  --data runs/track-m/canonical-capture-v1/fixtures:replay-input
```

## Section 5.6 falsification: the 1,500-unit pass line fails

**No production implementation or default-path change follows this test.**
The research prototype reads the original `active-source-probe.ts` packet
preparation verbatim, preserving the canonical input and member names. Its
Inv* packet exactly matches the requested **406 hypotheses / 73 instances**
and all thirteen signatures from `core-chain-trace-v1/checked-core.json`.
It uses the existing structural eligibility rules (57 eligible instances),
not an arithmetic ranking or a known-proof-only subset.

`research/track-m/derivability-closure.ts` implements the proposed experiment:
scalar prerequisite proofs, a source-by-source closure pass with 30-unit
limits (150 for five-term instances), independent checked conditional cuts,
and one final arithmetic query over proved facts. Prerequisites are carried
with `lemmaPath`; their independent proof trees inline only observed prior
cut dependencies, since the kernel forbids circular lemma references. A
successful final result would still have to check against the full original
goal under the explicit active/equal-row path. None did.

### Final corrected prototype: `closure-falsification-v3`

One job runs both requested cases sequentially, on an exclusive large
Ryzen 9950X worker with all eight vCPUs pinned. `placement.json` is retained.
The job itself exits successfully; the **proof tests fail**:

| Captured conditional goal | Hypotheses / instances | Eligible / closed count facts | Reference count facts reached | Counted units | Wall | Final arithmetic query |
|---|---:|---:|---:|---:|---:|---|
| Inv*, reconfig, both rows pinned to writer | 406 / 73 | 57 / 11 | 10 / 13 | 1500.132 | 11.519 s | Not reached |
| Inv2973, active reconfig, no row aliases assumed | 871 / 175 | 155 / 0 | n/a | 1500.020 | 6.451 s | Not reached |

The small counted overshoots are recorded as failures, not extra allowance.
Neither closure reaches a fixpoint before the window expires. The Inv2973
packet still has no five-term candidate, as the preceding static audit found.
No complete law or full MLDR run was performed or newly proved.

### Where the Inv* prediction fails

- Phase A proves two **guarded** ceiling cuts, spending **684.894 counted
  units** including construction, transport, and checks. The automatic
  pre-state source has **171 hypotheses / 28 instances**, not the earlier
  separately cleaned 136-hypothesis diagnostic source. The target cut is
  `if(committedQuorum && j<size, CfgT[j], 0) <= CT[i]`; its guard must still be
  related to the source's row-domain facts. The trace does not justify
  substituting the earlier 9-ms or 136-hypothesis timing for this work.
- Phase B attempts 30 of the 57 eligible candidates. Eleven close, including
  all six reference partition directions; **nineteen remain unknown**, rather
  than returning the cheap SAT counter-witnesses predicted in Section 5.
  The attempted sources consume **815.238 counted units**.
- The required union **index 39, witness `w$566`**, is actually attempted:
  `r$0 + r$4 <= r$7 + r$5 + r$6`, namely post-backing plus Q2 bounded by
  `sNotX + xNotS + xAndS`. Its **34-hypothesis source** remains unknown after
  its 150-unit decision/reconstruction window (**155.696 counted units with
  return overhead**), with the checked guarded ceilings and earlier cuts
  present. No SAT countermodel is returned for this union.
- The other missing reference entries, **69 and 70** (`frame$22/23`), are not
  reached. The final arithmetic query never runs, so it would be incorrect
  to report that query as either SAT or refuted.

This rejects the current prototype's **in-budget pass prediction**, not the
mathematical validity of the union, and not every possible implementation of
derivability closure. There is no observed missing second scalar fact to
assert: the union's result is unknown, not a model. The next local diagnosis
is the exact 34-hypothesis source and its ceiling/domain representation;
reordering guesses or increasing the accepted budget is not a result.

### Preserved prototype corrections, not hidden successes

`v1` blindly sent each source to Boolean reconstruction and proved redundant
conditional ceilings; it exhausted 1502.218 units after one count fact and
never reached the union. `v2` deduplicated weaker ceiling guards and used the
existing tiny-source model/refutation query before reconstruction. It exposed
an error in the experimental carrier: it inlined *all* prior cut proofs,
causing unnecessary repeated work, and hit its diagnostic 20-second wall stop
at 1208.849 counted units. Neither run is a valid pass.

`v3` uses the Section 5 `ObservedPath` dependency discipline, includes product
row dependencies, and restores the original source helper's 60-second wall
stop; the fixed **1,500 counted-unit** limit remains unchanged. Its result is
the table above. Exact v1/v2/v3 prototype patches and unmodified receipts are
retained, with v3's patch hash. No default prover or kernel file is changed.

Reproduce the final research test:

```sh
supercomputer run --jobs research/track-m/jobs-closure-falsification.json \
  --out runs/track-m/closure-falsification-replay --class interactive \
  --timing --vm-type large \
  --data runs/track-m/canonical-capture-v1/fixtures:replay-input \
  --data runs/track-m/core-chain-trace-v1:trace-input
```

`closure-falsification-v3/summary.json` records all three trial outcomes.
The narrow type-aware lint check passes with zero warnings and errors on both
research files (`closure-falsification-check-v1/research-check.log`).
The accepted runtime remains `fd2d1dcb`, and the complete hard-law status
remains **3/5**, with no new conservation gate claimed or needed for this
unpromoted research prototype.

## Section 6 input: exact profiles of the nineteen unknown sources

**Observation only; no default-path change.** `closure-source-profile-v1`
repeats only the original equal-row Inv* case on an exclusive pinned large
worker. Profiling records the source before the first point query, its entry
path, the reconstruction input, and opaque-column meanings. All thirty
attempted source indices, all nineteen unknown indices, their coefficient
vectors, their hypothesis counts, and the final **1500.1317484** counted-unit
result match v3. `profile-closure-sources.ts` asserts these identities rather
than associating profiles by approximate names.

### Meaning of the table

- `Hyps` is the actual source-query size; reconstruction receives the same
  number of hypotheses in **all nineteen** cases. No core was obtained.
- Every source contains **one count-instance clause**, its own member witness,
  and **six auxiliary flag-witness variables**: `w?all$1`, `w?all$2`, `w?all$3`,
  `w?allCopied`, `w?canVote`, and `w?noneCopied`. No other count-instance
  member occurs in these sources. Thus one count instance does **not** mean
  only one ground member is mentioned.
- `AST nodes / ifs` counts serialized `op` occurrences, including repeated
  expressions and inactive branches. It is not a count of unique DAG nodes
  or of branches the solver necessarily explores.
- The candidate lists its proxy-count reads. `raw` lists additional/direct
  count-map accesses remaining inside the source formula, including accesses
  in update guards; a raw read may duplicate a proxy already in the candidate.
  These are the complete count reads in the source hypotheses, not a claim
  that the inherited path contains no other proved count facts.
- Every initial point query returns **unknown, `why: "time"`**, with no core
  and no SAT model. `Boolean` is the following `booleanCore` attempt, not
  kernel checking time. Units below are measured, including boundary overrun,
  rather than rounded caps.

Count legend (`a = a$#`, `j' = j$`; the entry path pins both to writer `i`):

| IDs | Count reads |
|---|---|
| `r0`, `r1` | post `bq(a,j')`, post `cfgSize(a)` |
| `r3`, `r4` | `inS`, `inQ2` |
| `r5`, `r6`, `r7` | `xNotS`, `xAndS`, `sNotX` |
| `r8` | pre `cfgSize(a)` |
| `r11`, `r13`, `r14` | pre `bq(i,i)`, `bq(a,i)`, `bq(i,a)` |
| `r16`, `r17`, `r19` | pre `bq(i,j')`, `bq(a,j')`, `bq(a,0)` |

| Index / witness | Hyps | Count instances | AST nodes / ifs | Candidate; direct count reads | Point / Boolean units |
|---|---:|---:|---:|---|---:|
| 1 / `w$17` | 32 | 1 | 2933 / 52 | `r0 −r8 ≤ 0`; raw: r6, r5, r7 | 8.06 / 26.00 |
| 2 / `w$22` | 32 | 1 | 2981 / 52 | `r0 −r13 ≤ 0`; raw: r6, r5, r7 | 8.15 / 26.14 |
| 3 / `w$26` | 32 | 1 | 2981 / 52 | `r0 −r17 ≤ 0`; raw: r6, r5, r7 | 8.15 / 26.14 |
| 4 / `w$28` | 32 | 1 | 2981 / 52 | `r0 −r19 ≤ 0`; raw: r6, r5, r7 | 8.15 / 26.14 |
| 5 / `w$36` | 32 | 1 | 1199 / 6 | `r1 −r8 ≤ 0`; raw: r6, r5, r7 | 8.04 / 26.53 |
| 6 / `w$41` | 32 | 1 | 1247 / 6 | `r1 −r13 ≤ 0`; raw: r6, r5, r7 | 8.12 / 26.78 |
| 7 / `w$45` | 32 | 1 | 1247 / 6 | `r1 −r17 ≤ 0`; raw: r6, r5, r7 | 8.12 / 27.04 |
| 8 / `w$47` | 32 | 1 | 1247 / 6 | `r1 −r19 ≤ 0`; raw: r6, r5, r7 | 8.12 / 26.92 |
| 19 / `w$84` | 32 | 1 | 416 / 4 | `r4 −r5 ≤ 0`; raw: none | 8.06 / 26.95 |
| 20 / `w$85` | 32 | 1 | 414 / 4 | `r4 −r6 ≤ 0`; raw: none | 8.06 / 27.13 |
| 21 / `w$86` | 32 | 1 | 416 / 4 | `r4 −r7 ≤ 0`; raw: none | 8.01 / 26.95 |
| 22 / `w$90` | 32 | 1 | 452 / 4 | `r4 −r11 ≤ 0`; raw: none | 8.03 / 26.56 |
| 24 / `w$93` | 32 | 1 | 452 / 4 | `r4 −r14 ≤ 0`; raw: none | 8.04 / 27.13 |
| 25 / `w$95` | 32 | 1 | 452 / 4 | `r4 −r16 ≤ 0`; raw: none | 8.04 / 26.98 |
| 36 / `w$562` | 32 | 1 | 2963 / 54 | `r0 +r3 −r8 ≤ 0`; raw: r6, r5, r7 | 8.26 / 22.82 |
| 38 / `w$565` | 34 | 1 | 3002 / 54 | `r0 +r4 −r8 ≤ 0`; raw: r6, r5, r7 | 8.37 / 23.67 |
| 39 / `w$566` | 34 | 1 | 3108 / 58 | `r0 +r4 −r7 −r5 −r6 ≤ 0`; raw: r6, r5, r7 | 8.77 / 146.92 |
| 41 / `w$582` | 32 | 1 | 1229 / 8 | `r1 +r3 −r8 ≤ 0`; raw: r6, r5, r7 | 8.00 / 24.36 |
| 43 / `w$584` | 34 | 1 | 1268 / 8 | `r1 +r4 −r8 ≤ 0`; raw: r6, r5, r7 | 8.02 / 25.71 |

The nineteen failed source attempts consume **771.432 counted units**:
**154.557** in initial point queries and **616.875** in Boolean reconstruction
attempts. This is over half the global 1,500-unit window, before charging the
684.894-unit scalar-prerequisite phase. Neither a cheap SAT rejection nor a
refuted core was available to prune these nineteen attempts.

Post-state sources have 1,199–3,108 AST nodes and carry raw `r5/r6/r7` reads
inside their predicates. But the six simpler `r4` sources (19–25, excluding
the proved 23) also time out with only **414–452 nodes / four conditionals**.
The larger post-state syntax is observable overhead, **not a sufficient
explanation of every unknown**. All sources retain the six auxiliary
flag-witness variables, including `CV` facts for the copy flags.

### Union 39: exact witness goal and unfinished branch

`closure-source-profile-v1/union-39.json` contains the full query, source
entry path, reconstructed-input goal, decoded opaque columns, and the last
Boolean path. Its count-instance member is **`w$566`**; the numeric candidate
reads precisely `r0,r4,r5,r6,r7`. The raw update-guard reads are again
`xNotS[0]`, `xAndS[0]`, and `sNotX[0]`.

| Source component | Hypothesis indices | Size |
|---|---|---:|
| Scalar, field, flag, and domain context | 0–31 | 357 AST nodes |
| Single count-instance clause | 32 | **2,711 AST nodes**, **58 `if` nodes**, 382 field/count-map read occurrences |
| Negated numeric candidate | 33 | 40 AST nodes |
| Total | 0–33 | **34 hypotheses, one count instance, 3,108 AST nodes** |

The source already contains `a$# < size` and `j$ < size` (hypotheses 30–31).
Its inherited path contains both checked guarded ceiling columns:

```text
if(committedQuorum && i  < size, CfgT[i],  0) <= CT[i]
if(committedQuorum && j' < size, CfgT[j'], 0) <= CT[i]
```

The point query times out at **8.774 counted units** (20.897 ms wall); the
Boolean attempt consumes **146.923 units** (423.953 ms wall). Neither returns
a tree or a model; transport/admission do not perform a proof on this source.
It is inaccurate to call this a missing-domain counterexample or a proved
UNSAT source awaiting only certificate reconstruction.

A concrete feature of the **last unfinished Boolean branch** is now checked
by the static profiler against four exact saved atoms:

```text
entry path:  a$# - i <= 0  and  i - a$# <= 0
last branch: S[w$566] <= 0
             S[64*a$# - 64*i + w$566] >= 1
```

The two entry inequalities imply `a$# = i`, so the two `S` keys are equal.
Consequently this particular recorded branch is inconsistent. It is **not**
a SAT countermodel and does not identify a missing ceiling. It exposes an
unfinished packed-key/read-congruence obligation for Section 6 to inspect;
closing that branch alone would not establish the whole union or the
1,500-unit gate.

Reproduce the source capture and static table:

```sh
supercomputer run --jobs research/track-m/jobs-closure-source-profile.json \
  --out runs/track-m/closure-source-profile-replay --class interactive \
  --timing --vm-type large \
  --data runs/track-m/canonical-capture-v1/fixtures:replay-input \
  --data runs/track-m/core-chain-trace-v1:trace-input
bun research/track-m/profile-closure-sources.ts \
  runs/track-m/closure-source-profile-replay \
  runs/track-m/closure-falsification-v3/summary.json
```

The profile log retains the gzip/base64 capture of **all thirty source
queries**. `profile.json` contains the nineteen-row metadata and per-hypothesis
union statistics; `union-39.json` is the directly readable witness handoff.
Narrow type-aware lint passes on all three research files. The remote static
replay reproduces `profile.json`, `union-39.json`, and `table.md` byte for byte
(`closure-source-profile-check-v1/source-profile-check.log`).
No new proof outcome, default optimization, or conservation gate is claimed.

## Section 6 revised isolated tests: union checks, models are cheap, generators exist

Read Section 6 in the main checkout in full before testing. The three isolated
steps run on the unchanged canonical fixtures and accepted core/kernel, in
one exclusive large-VM job with all eight vCPUs pinned. **No default-path or
`certFor` change is made.** The source-query checks below are conditional
research results, not a complete-law proof or a new 1,500-unit closure gate.

| Test | Result | Counted units | Wall, excluding fixture preparation |
|---|---|---:|---:|
| T1: union 39, plain-cell guarded ceiling, model then core-only reconstruction | **Checked** conditional source proof | **38.630** | **570.758 ms** |
| T2: 19 original unknown sources, model query only, 50-unit limit each | **18 validated SAT sources; union 39 yields a refuted six-hypothesis core** | **422.973** total | **721.424 ms** total |
| T3: existing structured generators on the 41-read Inv2973 packet, bypassing the legacy proposal cap | **R2 and both R5 partitions present** | Not metered by the solver clock | **134.410 ms** |

### T1: corrected carrier and production source-query route

The source has **45 hypotheses**: the original scalar/field witness context,
the eleven previously checked v3 count facts (indices
`0,9,18,23,26,27,28,31,32,33,34`), and the union clause and its negation.
Those eleven facts are input to this *isolated* test, not newly assumed facts
in a complete-law certificate. The full 406-hypothesis/73-instance packet
is rebuilt verbatim and its instance signatures are checked against the
captured profile before constructing the production-style part.

The new ceiling cut is exactly:

```text
CfgT[j$:1] - CT[i:1] <= 0
```

There is **no opaque column in the cut**. The committed-quorum and `j$ < size`
guards are in `when`; the missing path guard is independently proved from the
source before use. A scalar-only source slice proves the ceiling independently
in **0.037 counted units**, avoiding both the 171-hypothesis count source and
the duplicate writer ceiling. The ceiling is active on the guarded query path.

The model query consumes **35.016 units**, returning `why: "refuted, not
unfolded"` with a **six-hypothesis core**. Only that core goes to `booleanCore`,
which takes **3.530 units**. The reconstructed source tree is checked, then the
ceiling and guard branches are inlined and checked again under the original
conditional root. `t1-proof.json` retains this conditional source certificate.

Thus Phase B need not be withdrawn for union 39 on the basis of v3: the revised
carrier plus production query route produces a checked proof well inside the
150-unit local window. This test changes both representation and query route;
it is not a single-variable timing ablation, and it does not by itself prove
the full law or the whole closure's budget.

### T2: exact source models and the reuse prediction

The 19 profiled unknowns were **not nineteen two-term bounds**. The actual
split is 14 two-term bounds, four three-term bounds, and the five-term union.
All nineteen are queried, but the valid union is not counted as a failed SAT
prediction. Each query receives the production-style part, the eleven checked
count facts and the plain ceiling hypothesis; there is **no Boolean fallback**.

| Source group | Indices | Result | Per-query counted units |
|---|---|---|---:|
| Two-term bounds | 1–8, 19–22, 24–25 | **14/14 SAT**, each model validated on its full source | 12.670–26.785 |
| Three-term bounds | 36, 38, 41, 43 | **4/4 SAT**, each model validated on its full source | 23.789–29.295 |
| Five-term union | 39 | Refuted core of size 6; no SAT model | 34.871 |

These are models of the isolated witness sources, **not protocol
counterexamples**. The source-model validation uses the existing `brokenOf`
evaluator, not a keyword or syntactic similarity test.

Reusing the **first** model (source 1), with each other source's count witness
renamed to its witness, satisfies both the local candidate pair and the **full
source** for **11/18** other queries: `2–8,36,38,41,43`. It does not satisfy
`19–22,24–25`, or union 39. This misses the design's **at least 15** reuse
forecast; no multi-model cache or new selection heuristic was implemented.
The cheap-model premise is confirmed, while the single-model reuse estimate
needs revision.

### T3: exact generator availability, and a second cap still matters

The existing generators are called directly, not through the legacy pair
loop: `proposeCountUnions(..., Infinity)` and `proposeCountFacts` at its largest
supported limits (128 counts, 12 atoms, 4,096 facts). The latter emits 203 facts
and does **not** hit its fact-count limit; its existing atom-limit skips are
retained in the log. The union generator emits **4,120 proposals** for the 90
existing ranked-head/carried pairs.

| Requested relation | Existing generator matches |
|---|---|
| R2: `old[b$] + inQ2 <= xn[i,b$] + xm[i,b$] + xm[b$,i]` | `proposeCountUnions`: **`union$678`** |
| R5: `inX = xNotS + xAndS` | Both directions from **both** generators |
| R5: `inS = sNotX + xAndS` | Both directions from **`proposeCountUnions`**; not the exact requested coefficient vector from `proposeCountFacts` |

The R2 vector is `+r$16 +r$9 -r$24 -r$25 -r$26`; it is found without adding a
new rule. The captured focused packet still has 175 instances and **no
five-term instance**.

**Important additional boundary:** R2 is at zero-based union position **678**.
Production requests only `min(cap,128)` union proposals. Therefore moving the
structured tail before the legacy pairs **alone is insufficient**: that
128-proposal prefix would still omit R2. A generic bounded proposal policy
must address this as well as the legacy cap; the test does not authorize a
protocol-specific index or an increased accepted search budget.

Any eventual `certFor` ordering/prefix change remains subject to the requested
**Paxos 3/3 gate against main `6a3874d3`**, on the exclusive pinned large-VM
placement, before becoming default. No such change or new Paxos gate was run
for these isolated tests.

### Evidence and scope

- `research/track-m/section6-isolated.ts`: isolated tests only.
- `research/track-m/section6-run.ts`: canonical packet-preparation wrapper.
- `runs/track-m/section6-isolated-v1/section6-isolated.log`: all raw outcomes,
  source models, and compressed checked T1 source proof.
- `runs/track-m/section6-isolated-v1/{summary.json,t1-proof.json,prototype.patch,placement.json}`:
  readable results, exact prototype, and placement.

The two research files pass type-aware lint with zero errors or warnings.
The earlier v3 **whole-closure** budget failure remains on record; it has not
yet been rerun with a revised algorithm. The production runtime and **3/5**
complete hard-law status remain unchanged.

## Default-on closure implementation — gate 1, first iteration

The first implementation adds generic bounded demand proposals in
`core/count-demand.ts`, wires conclusion-read/pre-state-twin demand into the
focused packet without changing `certFor`'s legacy ordering, and adds a
three-phase closure. The structured pool remains capped at **128**. The
proposer has eleven passing synthetic/kernel-witness tests; the first
integrated targeted suite and type-aware lint also pass.

**This iteration is not accepted: gate 1 remains 3/5.** The exclusive large VM
had eight pinned vCPUs and no co-tenants. The full-law results were:

| Law | Proved/checked | Wall | Counted units |
|---|---|---:|---:|
| One primary | yes/yes | 2.761 s | 926.633 |
| Inv3915 | yes/yes | 8.156 s | 960.226 |
| Inv1758 | yes/yes | 34.077 s | 4,342.879 |
| Inv2973 | no/no | 23.940 s | 5,234.405 |
| Inv* | no/no | 22.339 s | 5,137.342 |

Family wall: **91.275 s**. These are measured walls, not a claimed speedup over
main. Receipts and the exact staged implementation patch are in
`runs/track-m/closure-gate-family-v1/`.

The earlier exact equal-row Inv* diagnostic **does check** with this iteration:
**1,222.488 counted units**, 8.590 s for its measured proof call. It closes all
thirteen required reference facts, including union 39 and frames 69/70, plus
three extra checked facts. Two natural-subtraction case splits close the final
arithmetic query. This is a conditional source result, not a full-law proof;
see `runs/track-m/closure-default-probe-v2/`.

The first integration still ran closure inside row leaves. That does not meet
Section 5's hoisting requirement and retains repeated work. The next iteration
moves scalar and pointwise work before row decisions, uses independently
checked conditional cuts and dependency slicing, and confines row leaves to
arithmetic over active cuts. No later gate has run: generated production,
Paxos 3/3 against `6a3874d3`, and the paired 29×3 IC3Syn matrix remain blocked
by the five-law gate.

### Hoisted closure and conditional-certificate integration — still gated

The follow-up removes ordinary-tree reinlining from the internal count-case
route. Independently checked, sliced `LemmaCut`s now travel through guard,
row-cache, and finite-action transport as untrusted proposer metadata; the
final `CountCert` contains ordinary trees and the existing kernel lemma list.
No trusted checker or Lean rule changed. Direct standalone Tree APIs retain
their ordinary-tree default.

The canonical equal-row control checks with this carrier in
`closure-final-smoke-v3`: **815.910 counted units, 4.075 s wall**. It closes all
thirteen reference facts (including union 39 and frames 69/70), reaches a
fixed point, and checks the arithmetic conclusion. This is still a conditional
source proof, not a complete-law proof. The full repository type/lint gate and
its targeted suite passed in that snapshot.

The next complete-family receipt, `closure-gate-family-v2`, remains **3/5**:

| Law | Proved / checked | Wall | Counted units |
|---|---|---:|---:|
| One primary | yes / yes | 2.273 s | 926.633 |
| Inv3915 | yes / yes | 2.466 s | 856.955 |
| Inv1758 | yes / yes | 11.906 s | 4,296.456 |
| Inv2973 | no / no | 21.380 s | 5,409.351 |
| Inv* | no / no | 15.868 s | 5,137.029 |

Family wall is **53.896 s**. Type checking and lint pass, but the combined
suite catches a demand-partner regression: restricting partners to directly
referenced count IDs loses the primitive carried map and therefore R2. The
next snapshot's new flag test also exposed the distinction between raw named
flags and the compiled `?name` representation. Both are being corrected;
these failed snapshots are not acceptance evidence.

A second substantive omission was identified against Section 6.3: R2 is a
**conditional** union on a row-field version-order branch, not a theorem of
every row-alias scope. Generic scalar-scope discovery is being added from
member/anchor equalities and existing scalar law guards; every resulting
count cut must still be proved under its condition. Phase C alone branches
those conditions. The scalar proposer is not a new axiom or a protocol-specific
version test.

No later acceptance gate has run. The generated production 60-second test,
Paxos 3/3, and paired IC3Syn 29×3 remain blocked behind a clean five-law gate.

### Complete-certificate integration and written frames — acceptance pending

The candidate now carries independent conditional cuts through full-obligation
transport and dependency selection, not only through the internal row/guard
caches. `core/count-cert-transport.ts` preserves the complete certificate and
its source slices. The unchanged kernel remains the admission authority.
`core/count-write-frames.ts` discovers bounded, witness-backed proposals from
actual map-copy value arms, including the lowered Boolean write representation;
reading an input only in a non-Boolean guard does not make it a copy source.
The structured union/partition cap remains **128** and `certFor`'s legacy order
has not been changed.

Completed `closure-final-smoke-v6` checks: full TypeScript/type-aware lint and
the targeted suite pass. The canonical Inv* conditional source proof checks in
**1,082.881 counted units, 4.801 s wall**, with seventeen independent cuts and
a completed fixed point. This is not a complete-law result. The two full active
source projections still fail within their source budgets; their retained SAT
models are models of incomplete arithmetic projections, not protocol
counterexamples.

`closure-gate-family-v4` is another **failed acceptance gate: 3/5**. Each job ran
alone on a pinned eight-vCPU large VM. Its exact source snapshot is retained in
that run directory.

| Law | Proved / checked | Wall | Counted units |
|---|---|---:|---:|
| One primary | yes / yes | 2.773 s | 926.633 |
| Inv3915 | yes / yes | 3.062 s | 872.335 |
| Inv1758 | yes / yes | 14.932 s | 4,310.475 |
| Inv2973 | no / no | 38.928 s | 5,007.610 |
| Inv* | no / no | 21.323 s | 5,166.605 |

Family wall: **81.022 s**. The full integration check passes in this snapshot,
but its demand diagnostic fails: reserving requested Boolean range facts
exposed that a positive-pair allowance could be consumed by regenerating
partitions. Consequently R2 fell out of the bounded proposal pool. This is a
proposal-budget regression, not acceptance evidence. The next revision tests
pair-only requests, symbolic post-state partition discovery, and copied-size
bridges without increasing the cap.

Generated production (60 s), Paxos 3/3 against `6a3874d3`, and paired IC3Syn
29×3 have **not run** for this implementation: they remain gated on 5/5.

### Latest verified candidate — Gate 1 still 3/5

The final checkpoint in `closure-gate-family-v7` includes the corrected
conditional-scope cache: equal guard paths now use one canonical object, so
no source query is assigned the colliding `scope = -1` key. The real-packet
diagnostic explicitly checks this invariant. Unknown or untransported sources
are no longer reported as a completed fixed point.

Other verified integration details:

- Positive-pair requests do not regenerate the partition prefix; R2 and R5
  remain discoverable under the unchanged **128** structured-proposal cap.
- Symbolic post-state shapes are used only for proposing Boolean identities.
  Every witness is still proved against the original expanded declaration.
- Written-value proposals include copied row sizes and intersections of two
  overwritten rows. All directions remain untrusted, bounded proposals.
- Requested Boolean domain ceilings and field-sensitive zero candidates share
  the existing structured budget. They are not admitted from syntax alone.
- Query-first source proofs use a real model allowance, reconstruct only small
  refuted cores, and reuse a model only where it validates. Reconstruction and
  arithmetic remain within the caller's existing deadline; the full active
  probe no longer loses its unused allowance to a second hidden 1,500-unit cap.
- Declarative containment ranks cheap inclusions before expensive expanded
  post-state partitions. `certFor`'s legacy order and all trusted rules remain
  unchanged.

Full TypeScript/type-aware lint passes. The targeted suite passes **221 tests,
977 assertions, zero failures**. The canonical equal-row Inv* source checks
with **17 cuts, 920.085 counted units, 4.374 s wall**, including all thirteen
reference facts and the arithmetic conclusion. It reaches a verified fixed
point in two rounds and remains below the 1,500-unit pass line. This is a
conditional source proof, not a complete-law result.

The requested first acceptance gate still fails:

| Law | Proved / checked | Wall | Counted units |
|---|---|---:|---:|
| One primary | yes / yes | 2.716 s | 926.633 |
| Inv3915 | yes / yes | 2.885 s | 872.335 |
| Inv1758 | yes / yes | 13.413 s | 4,310.475 |
| Inv2973 | no / no | 32.069 s | 5,002.653 |
| Inv* | no / no | 35.274 s | 5,161.747 |

**Family wall: 86.359 s; complete-law result: 3/5.** The measurement commands
exit successfully because they record unsuccessful proof attempts too; their
exit status is not an acceptance verdict. All three jobs ran alone, with eight
of eight vCPUs pinned, on the same large VM (see `placement.json`).

The full active probes still stop before closure:

| Active source | Checked cuts | Counted units | Wall | Result |
|---|---:|---:|---:|---|
| Inv* | 42 | 4,725.785 | 17.536 s | First arithmetic leaf checks; the next is SAT in the incomplete projection |
| Inv2973 | 68 | 4,802.068 | 16.717 s | First arithmetic leaf checks; the next is SAT in the incomplete projection |

For Inv*, the unfinished leaf has `a = i`, `j = i` and `CfgT[j] <= CT[i]`.
For Inv2973 it has `a = i`, `b < i`. Both exhaust the source allowance before
a fixed point. The exact path, model, candidate catalog and query trace are in
`demand-and-sources.log`. These models name unresolved proof obligations; they
are **not protocol counterexamples**.

This implementation is default-on **only on the candidate branch** and is not
accepted for promotion. The generated-production 60-second test, same-VM
Paxos 3/3 against `6a3874d3`, and paired IC3Syn 29×3 have **not been run**,
because the ordered 5/5 gate has not passed. No later gate is claimed.

## Track M — diagnostic phase and cut-use census (candidate `50109a36`)

**Diagnostic only: no search strategy, default, cap, ordering, or trusted rule
changed. Gate 1 remains 3/5; no subsequent acceptance gate was run.** The hooks
are installed only in disposable snapshots. Their before/after hashes and
hash-checked restoration receipts are in the raw log.

All six processes (candidate focused control/profile, candidate native
control/profile, main native control/profile) ran sequentially in one exclusive
job on **the same VM as v7, `bx_3kjzmmhv`**, AMD Ryzen 9 9950X, eight of eight
vCPUs pinned, zero co-tenants. Main was extracted from the checksum-verified
`6a3874d3f2c6febe40bb14775884cb327a2cce3c` archive. The canonical input, law
order, shared `withTrees` scope, 5,000-unit allowance, and 60-second per-law wall
limit are unchanged. No dependency audit runs between laws; all such work is
deferred until the complete process has finished its measurements.

### Five-law focused path: exclusive wall breakdown

Seconds below; each row is additive apart from rounding. **Kernel time is
subtracted from its enclosing phase**, not counted twice. C measures numeric
leaf construction/query/reconstruction; later lifting/transport belongs to
remaining work. Exact milliseconds, inclusive A/B intervals, per-round times,
call counts, and checker sites are in `census.json` and the per-law JSON files.

| Law | Demand proposals | A: ceilings | B: closure | C: leaf queries | Kernel checks | Remaining work | Total wall | Checked |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| One primary | <0.001 | 0 | 0 | 0 | 1.177 | 0.987 | 2.164 | yes |
| Inv3915 | 0.030 | 0 | 0 | 0 | 1.575 | 0.870 | 2.475 | yes |
| Inv1758 | 0.014 | 0 | 0 | 0 | 5.704 | 5.357 | 11.075 | yes |
| Inv2973 | 0.118 | 0.906 | 2.214 | 0.194 | 0.036 | 21.625 | 25.094 | no |
| Inv* | 0.034 | 1.598 | 6.290 | 0.171 | 10.379 | 10.726 | 29.198 | no |

The five measured law walls sum to **70.006 s**. The uninstrumented same-job
control sums to **69.791 s**. These are descriptive single-run timings, not a
performance acceptance claim against the older 86.359-second v7 measurement.

“Remaining” is explicitly accounted, not hidden overhead:

| Law | Legacy `certFor` proposals | Ordinary search outside A/B/C | Construction, transport, traversal, other |
|---|---:|---:|---:|
| One primary | 0.028 | 0.520 | 0.439 |
| Inv3915 | 0.022 | 0.400 | 0.447 |
| Inv1758 | 0.024 | 1.765 | 3.568 |
| Inv2973 | 0.219 | 5.512 | 15.893 |
| Inv* | 0.242 | 2.477 | 8.007 |

This census does **not** support attributing all of Inv2973's wall to closure:
A+B+C consume 3.315 s; its largest bucket is construction/transport/other,
which is not subdivided further here. For Inv1758 there are fourteen early
closure-entry calls, but **none reaches Phase A**. Its three final `checkMC`
calls consume 5.701 s inclusive (5.704 s total checker-exclusive time). Thus
its measured cost is not ceiling generation or closure rounds.

### Cut census, by admitted-cut ID

IDs are local to a law run, `closure-N/cut-M`; conditional copies are distinct
admissions, not distinct mathematical vectors. “Offered” means actually present
in a Phase-C numeric hypothesis list. “Referenced” means cited by an independently
checked numeric proof or the leaf query's refuted core. A SAT/unknown attempt
without such a certificate has no minimal dependency set: its supplied cuts
are **offered**, not silently counted as proof-used.

| Law | Admitted (A / B) | Offered to at least one attempted leaf | Proof/core-referenced | Numeric leaves checked / attempted |
|---|---:|---:|---:|---:|
| Inv2973 | 49 (2 / 47) | 47 | 0 | 0 / 4 |
| Inv* | 97 (9 / 88) | 87 | 3 | 12 / 17 |

**Inv2973:** admitted IDs are `closure-1/cut-1..15`,
`closure-2/cut-1..20`, and `closure-4/cut-1..14`. All are offered except
`closure-1/cut-1` and `closure-2/cut-1`. No attempted leaf produces a checked
numeric proof or a refuted core citing any of them. The four leaf outcomes
are unknown, SAT, SAT, unknown. These projected SAT results are not protocol
counterexamples.

**Inv*:** admitted IDs are `closure-{1,2,3}/cut-1..23` and
`closure-{6,7}/cut-1..14`. The exact referenced set is:

- **`closure-1/cut-17`** — cited by `closure-1/leaf-1`;
- **`closure-2/cut-17`** — cited by `closure-2/leaf-1..6`;
- **`closure-3/cut-17`** — cited by `closure-3/leaf-1..5`.

Each is candidate index **45**, witness **`frame$18`**, the single-count
nonnegativity vector **`+r$0 >= 0`** (`unit: 0`), under its recorded guard.
The proof-reference and core-reference sets coincide. Of 87 offered IDs,
84 are never cited by any Phase-C proof/core. The ten never-offered IDs are
`closure-{1,2,3,6}/cut-{1,2}`, `closure-7/cut-1`, and `closure-7/cut-14`.
The other five attempted leaves are one unknown and four SAT projections.

This is an arithmetic-leaf dependency census, **not a transitive deletion
proof**: an uncited admission may have supported an earlier A/B source proof.
No cut was removed, and no claim is made that all 84 uncited admissions can be
safely skipped. Source-proof and leaf-proof notions are kept separate.

### Inv1758 against main: compare the shared native entry honestly

Main `6a3874d3` predates both `proveFocusedCounts` and `deriveCountClosure`.
Copying the candidate focused prover into it would not be a main baseline.
The additional control therefore calls the native entry available on both
revisions, `countedAttempts(...).traced(...)`, after matched one-primary and
Inv3915 native warm-ups. A/B/C and demand generation are **not applicable**
on main, rather than a zero-cost implementation of those phases.

| Inv1758 native entry | Demand / A / B / C | Legacy proposals | Ordinary search | Kernel | Other | Total wall | Checked |
|---|---|---:|---:|---:|---:|---:|---|
| Main `6a3874d3` | n/a | 0.002 | 0.190 | 0 | 0.014 | 0.206 | no |
| Candidate `50109a36` | not reached | 0.002 | 0.189 | 0 | 0.016 | 0.207 | no |

Both native attempts fail to return a proof; their uninstrumented controls
also fail (0.202 s main, 0.238 s candidate). **These are early unsuccessful
attempts, not a fast main proof of Inv1758**, and cannot be used as the denominator
of an 11.075-second successful-proof regression claim. The useful measured
localization is that the candidate focused path spends 5.704 s checking and
3.568 s in construction/transport/other, with zero A/B/C work.

### Measurement integrity and artifacts

- All **11 profiled/control pairs** agree on proved/checked outcomes.
- **10/11** also match counted work exactly. Inv* differs by **+0.400389 units**
  (5,161.936541 vs 5,161.536152, about **0.0078%**); exact instrumentation
  neutrality is therefore **not** claimed for that wall-bounded path.
- All eleven exclusive-phase sums reconcile to wall time within **0.043 ms**.
- TypeScript and type-aware lint pass with the hooks installed; the three
  meter tests pass (nine assertions). Independent fresh-process replay checks
  **12/12 numeric proofs and 12/12 exact cut-ID sets**; its receipt is in
  `validation/verify-census.log` and `proof-replay.json`.
- The first preflight caught a missing string-sort comparator; its failed
  receipt is preserved as `preflight-1.log`, not presented as a successful run.

Artifacts: **`runs/track-m/closure-phase-census-v1/`**. Start with `census.json`,
`verification.json`, the two `candidate-focused-profiled-Inv*.json` records,
and `candidate-focused-profiled-Invstar-proofs.json`. The raw job log includes
all restoration/manifests, controls, and full cut/leaf records. Reproduction
and category definitions are in **`research/track-m/PHASE-CENSUS.md`**.

## Track M — Section 7, T0: reuse anomaly explained before implementation

**T0 is explained, but its predicted refutation is not reproduced.** On the
same exclusive VM, `bx_3kjzmmhv`, a fresh query for the exact `frame$0` fact
`bq#[a$#,j$] <= bq[i,i]` returns a validated projected SAT result in **both**
the canonical equal-row source and the active equal/equal source:

| Matched fact | Packet index | Source hypotheses | Fresh query | Counted units | Query wall |
|---|---:|---:|---|---:|---:|
| Canonical `frame$0` | 47 | 41 | SAT | 25.932 | 23.029 ms |
| Active `frame$0`, scope 7 | 27 | 53 | SAT | 27.741 | 22.981 ms |

The Section 7 anomaly came from comparing **different instances at index 27**.
Canonical index 27 is the partition `r$2 <= r$5 + r$6`, witness `w$548`;
canonical index 28 is its reverse. The original v7 log proves those partitions
with two-hypothesis cores and empty guards. It does **not** prove `frame$0`:
canonical `frame$0` is index 47, and v7 reports `reused-model` for it. Active
index 27 is `frame$0`. Matching witness, terms, and read definitions resolves
the apparent contradiction without a scope-cache change.

The separate missing-binding audit is real and conservative. Requiring every
live syntactic variable of the renamed source slice to be explicitly present
rejects **112/112 active Inv* reuses and 77/77 active Inv2973 reuses** (also
131/131 canonical reuses). Common omissions include `w?all$1` and `w?all$3`.
`brokenOf` currently supplies zero for missing scalar values via its proxy;
its empty broken-hypothesis list does not establish explicit binding coverage.
This audit does not say that all rejected candidates are provable: the fresh
matched-frame SAT queries above are counterevidence to that stronger claim.
These are partial source/projection models, not protocol counterexamples.

No production code or reuse policy was changed. Observation hooks retain
references only during the original proof calls; missing-binding checks and
fresh queries run afterward. Canonical and active source sizes and the
131/112/77 reuse counts reproduce v7 exactly. TypeScript/type-aware lint
passed on the instrumented first run. The first capture queried canonical
index 27 before the identity mismatch was known; the authoritative frame
comparison is the later **`section7-t0-matched-v1`** run, not that first query.

Evidence: `runs/track-m/section7-t0-matched-v1/results.json`, its canonical and
active source snapshots, and `runs/track-m/section7-t0-v1/results.json` for the
complete missing-binding census. T1–T3 and implementation have not run at
this checkpoint. Under the coordinator's **“T0 explained”** criterion, the
next permitted step is the requested T1 wall split—not assuming a proved frame.

## Track M — Section 7, T1: pass line not met; stop before T2/T3

**T1 fails the requested ≥50% admission/transport condition. No inversion,
guard-reduction optimization, allowance increase, or other production change
was implemented. T2, T3, and a new Gate 1 run were not started.** The measurement
ran on the same exclusive eight-vCPU VM, **`bx_3kjzmmhv`**. All five law verdicts
and counted-work totals match the profiled `38c17fc4` census exactly.

### Split of the previous “remaining” column

The original remaining walls were 21.625 s for Inv2973 and 10.726 s for Inv*.
The more detailed rerun measures 22.399 s and 10.988 s respectively. Each row
below is **exclusive/additive**: a transport inside an ordinary query is
charged to transport and removed from ordinary search. Admission already
charged to A/B or kernel is not charged a second time to remaining.

| Law | Cut admission / transport in remaining | Ordinary search, excluding that transport | Legacy proposal generation | Other construction / traversal | Remaining total | Admission / transport share |
|---|---:|---:|---:|---:|---:|---:|
| Inv2973 | 8.210 s | 4.355 s | 0.291 s | 9.543 s | 22.399 s | **36.65%** |
| Inv* | 5.436 s | 1.851 s | 0.067 s | 3.633 s | 10.988 s | **49.47%** |

The fourth column of work is retained explicitly rather than relabeled as
transport to force a three-way split. This instrumentation covers cut
admission, cut inlining, exact conditional-proof transport/retargeting,
count-certificate transport, count-proxy lifting, and `widen`; it does not
further divide the remaining construction/traversal bucket.

The result also fails for Inv2973 under the broader Section 7 wall-minus-counted
interpretation: **all** observed admission/transport wall across **every**
phase, including its kernel work, is only **9.626 s**, versus **21.264 s**
wall minus counted work (**45.27%**). Charging that entire envelope to the
uncounted excess is already generous, since some of it is counted work.
For Inv*, the analogous broad envelope is 15.505 s / 25.237 s = 61.44%; this
does not rescue the failed Inv2973 condition.

The largest measured transport site for Inv2973 is `widen`: 8.164 s inclusive,
of which 6.138 s falls in construction/other and 1.641 s inside ordinary
search. Its 49 admitted cuts cost **1.031 s total** to admit, about **21.0 ms
per admission**; those costs are already in A/B and checking, not in the
remaining column. Inv* has 97 admissions costing **4.089 s**, about **42.2 ms
per admission**. The inferred 175–305 ms per admission was therefore not a
measurement of admission itself.

### Canonical equal-row source: the admission prediction is falsified

The unchanged canonical source still checks: **17 cuts**, **920.084827 counted
units**, **4.113171 s wall**. Its wall-minus-counted proxy is **3.193087 s**.

| Measured site | Calls | Inclusive wall |
|---|---:|---:|
| Whole `admitConditionalCut` | 17 | **1.201767 s** |
| Admission `inline` | 17 | 0.109305 s |
| Dependency scans | 34 | 0.120846 s |
| Trace-based guard reduction | 17 | 0.063007 s |
| Per-atom guard-removal loop | 17 | **0.722803 s** |
| Admission final check | 17 | 0.102425 s |
| `countScalarGuards` | 73 | 0.043980 s |
| `source()` | 248 | 0.033019 s |
| `finish()` | 1 | 0.335785 s |

These site times are nested/inclusive and must **not** be summed. Whole
admission is **37.64%** of the wall-minus-counted proxy, and the per-atom loop
is **22.64%**, rather than the predicted ≥70% and ≥50%. Whole admission
averages **70.7 ms per cut**. This does not establish the required payoff for
cheapening the guard loop before implementation.

### Why Inv* had 10.4 s of kernel checking

The detailed rerun measures **11.015 s**, in the same category as the prior
10.379 s. It records **2,162 calls to the ordinary kernel checker**. The
breakdown is by the immediate caller; these call groups do not overlap:

| Caller | Checks | Goal size | Checker wall |
|---|---:|---|---:|
| Conditional-proof region checking | 136 | **489–490 hypotheses**, all leaf roots | **6.808 s** |
| Rechecking independent conditional-cut proofs | 1,354 | 1–2 hypotheses | **2.447 s** |
| Conditional-cut retarget validation | 569 | 1–2 hypotheses | **1.298 s** |
| Admission/inlining validation | 103 | 1–11 hypotheses | **0.462 s** |

The costly part is repeated checking of full-goal arithmetic leaves and
repeated validation/retargeting of conditional-cut proofs, **not primarily
the admission guard-minimization loop**. `transportConditionalProof` runs
12 times and takes 7.436 s inclusive, containing 5.542 s of kernel work;
this inclusive figure overlaps the table and is not an extra charge.

### Integrity, status, and reproduction

The canonical proof remains checked and the full-family diagnostic remains
**3/5**, with walls 1.911 / 2.271 / 11.206 / 26.267 / 30.399 s. This is a
profiling replay, not a new strategy or an acceptance-gate rerun. Counted work
matches every corresponding row in the previous profiled census exactly.
TypeScript/type-aware lint and the three measurement tests (nine assertions)
pass with the instrumentation installed. A first preflight caught a TypeScript
narrowing issue in the observation wrapper; `preflight-1.log` preserves that
failed setup, not proof evidence.

The hooks and classification are research-only. Production `core/` and
`kernel/` remain unchanged; instrumentation is installed only in disposable
remote snapshots. Raw data, per-law records, canonical site breakdown, and
computed pass status are under **`runs/track-m/section7-t1-v1/`**, starting
with **`results.json`** and **`admission-wall.log`**. The checked-in installer
and static reducer reproduce the attribution.

**Stopped at T1 as requested. T2/T3, generic inversion, admission changes,
and Gate 1 remain unrun. No per-law allowance or budget increase was used.**

## Track M — Section 7 follow-up: T2/T3 measured, no implementation

Requested measurements on the same exclusive eight-vCPU VM **`bx_3kjzmmhv`**.
No production code, proposal cap, or budget changed. This is not a Gate 1 rerun.

### T2: the targeted Inv* leaf closes, with 26 cuts

The specified indices plus v7 active indices reduce Inv* from 91 to 32
instances and Inv2973 from 289 to 58. Literal filtering alone closes neither:
discarded-witness flag hypotheses remain in the source context. A separate
research-only control uses the existing witness-cleanup/reseeding helpers,
reducing source obligations from 378 to 157 and 1010 to 205 hypotheses.

| Hygienic measurement | Result | Admitted cuts | Closure counted units | Diagnostic wall |
|---|---|---:|---:|---:|
| Inv*, captured equal/equal target | **Checked; fixed point** | **26** | **596.934** | **2.990 s** |
| Inv*, full active traversal | Incomplete projected SAT | 28 | 3603.309 | 9.266 s |
| Inv2973, captured target | Fixed point; incomplete projected SAT | 52 | 1062.136 | 8.039 s |
| Inv2973, full active traversal | 13 arithmetic leaves check, next unknown | 67 | 5009.202 | 14.999 s |

The important Inv* **conditional leaf closes**, but <=22 cuts and completion
of its full active diagnostic do not hold. Fresh guard atoms and the captured
explicit scalar/row atoms define the target; opaque column IDs are not imported.
This is not a complete-law proof.

Inv2973 R1 (126) checks at **16.927–18.099 counted units**. R2 (272/275) checks
under `CfgT[y] < CfgT[i]`, or `CfgT[y] <= CfgT[i]` with `CV[y] < CV[i]`, at
**22.045–25.029 counted units**. It does not fail under every proposed guard.
These are counted costs, not wall milliseconds. Remaining SAT projections
are not protocol counterexamples.

### T3: cheap queries, but different cores

| Law | Numeric base + actual pool goods | Query wall | Pool fact in refutation core |
|---|---:|---:|---|
| Inv* | 29 + 91 | **15.664 ms** | 54, `range$1`: `r$0 <= 0` |
| Inv2973 | 38 + **289** | **26.290 ms** | 190, `range$3`: `r$2 <= 0` |

Both refute under the requested time limits, using speculative zero-count
bounds against the negated target rather than R1/R2. This establishes query
cheapness, **not** useful selection or source provability. The captured
Inv2973 packet has 289 eligible `terms.length <= 5` goods, not the design's
175; no cap was increased.

Evidence: **`runs/track-m/section7-followup-v3/README-demand.md`**,
**`demand-results.json`**, **`t2-t3.log`**, and **`t2-hygiene.log`**.
The failed T1 implementation line remains in force. No implementation or
promotion follows from these measurements.

### Follow-up (b): Inv2973 construction/traversal one level deeper

The prior residual was **9.543 s**; this new same-input replay measures
**11.024 s** in the same exclusive category. This is not a retrospective
split of the old time. Counted work matches the control exactly.

| Exclusive category, excluding admission/transport and search | Wall |
|---|---:|
| Arithmetic-row materialization in `rowsAt` | **6.004 s** |
| Remaining case/branch control | **4.633 s** |
| Focused pool construction | 0.287 s |
| Count-goal construction | 0.049 s |
| Field-case control | 0.029 s |
| Obligation construction | 0.014 s |
| Witness seeding and other bookkeeping | 0.008 s |
| **Total** | **11.024 s** |

Thus row materialization accounts for **54.46%**; the still-coarse residual
case-control category is **42.03%**. Nested inclusive site totals are not
summed. The latter category is not falsely assigned to one AST operation.

### Follow-up (c): hypotheses and repeated full-goal checks

Each checked goal contains **378 underlying obligation hypotheses + 20
count-read bindings + 91 count-instance disjunctions**. The 91 split into
**26 frame clauses and 65 other count clauses**. A separately inserted guard
makes 490 rather than 489. Of the 378 obligation hypotheses, **341 mention
count witnesses**, including **126 frame-witness hypotheses**; only 37 are
witness-free before the guard. These count clauses are not independently
proved cuts. Proved scalar cuts add **zero goal hypotheses**: they enter the
path instead (0–23 additional atoms in the audited calls).

The earlier trace had 136 checks but did not record identities. The fresh
same-input replay records **120** (114 with 490 hypotheses, six with 489),
spending **5.717 s** in their checker. For exact goal + ordered path + leaf
certificate identity: **88 distinct leaves, 32 checked twice, 32 extra
checks**. By object identity separately: 96 leaf objects, 24 used twice.
These counts describe the new replay, not an invented audit of the old 136.

All five control/profile verdicts agree. Counted work matches exactly for
four; Inv* differs by **+0.325569 units (0.0063%)**, explicitly preventing an
exact-trace-equivalence claim. TypeScript, type-aware lint and **five tests /
15 assertions** pass. Both T3 numeric cores independently check in the kernel
under their assumed goods; this does not prove the goods themselves.

Complete compressed and decoded receipts, per-call hashes, and verification
are in **`runs/track-m/section7-followup-v3/`**, especially
**`README-census.md`**, **`Invstar-leaves.json`**, **`results.json`**, and
**`validation/verify.log`**. Production sources remain unchanged. Gate 1 stays
at the previously established 3/5; no implementation or new gate was run.

## Section 8 T-A — nonempty Inv* selection, failed requested source proof

Measurement-only on **bx_3kjzmmhv**, exclusive, eight pinned vCPUs. No
production source, allowance, cap, strategy default, or trusted rule changed.

For the exact second Inv* arithmetic leaf of the hygienic traversal, the
restricted 32-element pool has **V={27,32,77,84}**. All live variables of the
goods are explicitly bound. The full 91-element pool has 44 violated goods.
Fresh source queries for the requested **84 and 77 both return projected SAT**,
not a checked fact, at **36.647560 / 16.470482 counted units**, respectively.
In the validated rerun they take **70.484 / 35.682 ms** wall.
Both models satisfy the source AST and scope under zero completion but omit
`w?all$1` and `w?all$3`; neither is eligible for explicit-binding model reuse.
No reuse occurred. These are not protocol counterexamples; 27/32 were not tried.
The design's predicted proof of 84 was not obtained.

The exact **Inv2973 fourteenth leaf checks with its existing 53 cuts** when
retried: **26.770835 counted units / 678.389 ms wall**, including the checked
conditional proof of the original goal. The old attempt had only 13.104 units
left. No additional cut was required, and there is no SAT model/V on this leaf.
It is a checked leaf, not an empty-V generator gap or a complete-law proof.

The explicit empty-V stop is not triggered, so subsequent requested tests may
continue as measurements in order. The implementation pass line is not met:
the requested Inv* source proof failed. **No implementation or gate rerun.**
TypeScript, type-aware lint, and five census tests / 15 assertions pass.
Earlier setup/static-check timeouts are retained, not counted as T-A results.

Evidence: **runs/track-m/section8-ta-v3/README.md**, **results.json**,
**Invstar-leaf.json**, and the Inv2973 receipt/leaf in **section8-ta-v2/**.

## Section 8 T-F1 — one expensive pre-check removed; prediction not met

Committed measurement-only snapshot experiment; the final harness check and
kernel stay unchanged. All five verdicts match (three checked, two unproved).
The proved laws' counted work matches exactly. Open-law work does not: the
unchanged 60-second wall now stops both, so no trace-equivalence is claimed.

Per-call measurements show **two expensive step checks plus a nearly free
initial check**, not three equal-cost checks. Deferring the pre-transport check
changes three calls to two, one final check per returned obligation.

| Law | Control kernel | Deferred kernel | Predicted ceiling |
|---|---:|---:|---:|
| one primary | 4.416 s | 2.601 s | 0.4 s |
| Inv3915 | 8.444 s | 4.292 s | 0.5 s |
| Inv1758 | 27.746 s | 15.674 s | 1.9 s |

The pass line is not met. Absolute CPU/wall costs are also substantially above
the prior census, for an unestablished reason. The per-call CPU times track
wall, and a later VM-health probe found no orphan processes or current CPU
pressure. Do not interpret this as a controlled regression measurement.
Inv1758 control checkMC calls: **13.430 s / 0.000202 s / 14.305 s**; deferred:
**0.000296 s / 15.661 s**. The one-third cost assumption is false independently
of the unexplained absolute slowdown.

Same exclusive **bx_3kjzmmhv**. TypeScript and type-aware lint pass on both
successful snapshots. Only an outer process timeout was extended after the
first collection timed out; no law budget, cap, or final-check rule changed.
Evidence: **runs/track-m/section8-f1-calls-v1/README.md**, **results.json**,
**section8-f1-v2/** and **section8-health-v1/**. No production implementation.

## Section 8 T-F2/F3 — large slice win, but 2.5 s ceiling missed

Research-only snapshot, same exclusive **bx_3kjzmmhv**; unchanged kernel and
final harness check. Inv* exclusive kernel wall falls **10.003 → 3.037 s**,
while total diagnostic wall falls **35.017 → 25.262 s**. The required
**<=2.5 s is not met**. Counted work differs by **-0.1472452 units
(-0.002853%)**, within 0.01%; the other four laws match exactly. All five
verdicts agree. No exact trace-equivalence claim is made.

Full-goal leaf checking falls from **118 calls / 6.297 s** to **122 sliced
calls / 0.005819 s**, each over only 1–3 hypotheses. Thirty-two slice-cache
hits avoid additional calls. Independent checks fall **1190 → 460**, with
1012 cache hits. The identity-keyed retarget cache has **zero hits**;
retarget rechecks instead cost **1.844 s** across 631 calls (control:
0.815 s / 515). Thus F2 is effective, but the specified F3 cache does not
provide the predicted final reduction.

Three tests, TypeScript, and type-aware lint pass. No production change.
Evidence: **runs/track-m/section8-f23-v1/README.md**, **results.json** and
its paired raw/decoded profile receipts.

## Section 8 T-8.1 — small total work, but first-leaf share exhausted

The research-only model loop runs over the **complete 91 / 289 instance pools**,
queries with proved cuts only, and re-queries after each newly proved fact.
The explicit-binding check guards source-model reuse; no instance is attempted
twice at one scope. Fresh numeric valuations explicitly complete absent pool
columns to zero and are validated against the numeric AST and scope before V
is evaluated. This is not a source-reuse default-zero shortcut.

| Full-pool diagnostic | Cuts | Counted total | Wall | Outcome |
|---|---:|---:|---:|---|
| Inv* | 5 | 440.058722 | 0.781 s | First arithmetic leaf: time |
| Inv2973 | 2 | 352.459662 | 1.329 s | First arithmetic leaf: time |

The unchanged 350-unit leaf share expires at **354.431277 / 352.109316** units
respectively, including the last atomic operation. Inv* attempts seven source
facts; Inv2973 attempts two. Both stop in their first equal/equal row scope,
**before** the later T-A leaves. Neither completes, and neither has an empty
unexcluded V, so **no generator gap is claimed**. The T-8.1 prediction fails.
No cap, leaf share, source allowance or overall allowance was raised. Legacy
fallback after loop failure is excluded from this loop-only measurement.

Both repeated full-pool runs have identical counted totals. TypeScript and
type-aware lint pass. Exact scopes, model rounds, V/exclusion sets and source
queries are in **runs/track-m/section8-loop-final-v1/**; earlier restricted
controls and setup failures are retained. Production remains unchanged.

## Section 8 T-F4 — incremental row prototype rejected; stop

On the same exclusive **bx_3kjzmmhv**, Inv2973's exclusive remaining-phase
row-materialization bucket increases **8.551 → 22.997 s**. Its inclusive
`rowsAt` wall increases **29.045 → 48.635 s**, despite fewer calls
(13364 → 12094). Total diagnostic wall is **48.186 → 60.800 s**.
The candidate reaches the unchanged 60-second wall at **4883.592478 units**;
control reaches **5002.6530104**. These are not identical traces, so no
matched-work speed ratio is claimed. **Neither <=2 s nor 50% saving holds:
drop F4.** All five verdicts agree; proved-law counted totals match exactly.

The untrusted prototype does reuse 14,033,332 hypothesis blocks across the
candidate process, but complete row assembly/bookkeeping is not thereby cheap.
The profile does not assign the residual to a specific copy operation.
The trusted kernel and final check are unchanged.

Two row-differential tests cover 20 sibling/nested paths against the unchanged
builder. After removing two unused imports from the snapshot generator,
**TypeScript and type-aware lint pass on both the plain and F4 snapshot trees**.
Final validation: **10 tests / 46 assertions**, plus the two differential tests
and 20 assertions repeated on the installed F4 snapshot.

Evidence: **runs/track-m/section8-f4-v1/README.md**, **results.json**, paired
profile receipts, and **section8-final-validation-v1/validate.log**.

### Section 8 stop decision

All requested tests were run in order. T-A did not produce the requested
Inv* source proof, T-F1 and T-F2/F3 missed their ceilings, T-8.1 did not complete
Inv*, and F4 regressed. **The implementation pass line is not met.**
No production implementation, default change, cap/allowance increase, trusted
rule change, or new Gate 1 run. Gate 1 remains at its prior **3/5** result.

## Census / T-F1 measurement integrity — same-VM ABBA controls

Historical revisions **38c17fc4 / bdb9568a**, same captured input, fresh
processes on exclusive **bx_3kjzmmhv**, eight pinned vCPUs. Production files and
installed instrumented production files are byte-identical; only diagnostic
meter/runner code differs. No F1 deferral or other optimization is applied.

| Exclusive kernel seconds | One primary | Inv3915 | Inv1758 |
|---|---:|---:|---:|
| Census A1 | 2.982 | 4.325 | 9.357 |
| T-F1 B1 | 1.455 | 1.863 | 14.471 |
| T-F1 B2 | 1.719 | 2.254 | 7.708 |
| Census A2 | 1.205 | 1.737 | 7.389 |

All **24/24** results check, counted units match exactly, and instrumented
call-site counts match exactly. The same census varies by up to **2.49x**;
T-F1's Inv1758 varies by **1.88x**. Crossovers (new meter without T-F1 extras,
old meter with them) do not show a consistent wrapper penalty. Uninstrumented
controls also retain substantial wall cost.

The native SHA-256 calibration stays at 26.1–30.7 ms, recorded CPU-quota
throttling is zero and pressure is low. Process CPU varies with runtime wall;
this is not merely descheduled time. The historical 3–5x difference is **not a
production-source regression**, but the exact runtime cause is not established
by this comparison alone; JIT/GC isolation is being measured separately.

Evidence: **runs/track-m/census-integrity-v1/README.md**, source hashes,
**comparison.json**, raw receipts, telemetry and placement. Production unchanged.

### Runtime follow-up — no unique historical cause isolated

Two further complete eight-process experiments use the same exclusive VM:
**census-runtime-v2** isolates concurrent JIT, FTL and concurrent GC;
**census-gc-v1** interleaves default/GC-off/GC-off/default on both meters.
All **72/72** law results across the three complete batches check, with exact
counted-work and instrumented-call-count agreement.

Disabling concurrent JIT leaves Inv1758 at **12.364 / 6.947 s**. Disabling FTL
leaves it at **8.679 / 10.465 s**. An initially fast GC-off pair does not survive
the interleaved discriminator: GC-off Inv1758 means are **4.4% / 13.0% slower**
than default on the T-F1 / census meters. No unique JIT/GC culprit is established.

Sampled CPU time is concentrated in the unchanged kernel's `decide`, `truthOf`
and `truth`, not the census callbacks. These explain *where* current time is
spent, not why the historical run was slow. Current guest telemetry does not
show CPU-quota throttling; it cannot rule out physical-host contention, and the
historical Bun revision / JIT / GC / host state was not recorded.

**The exact historical 3–5x cause remains unresolved.** What is established:
no production-code or snapshot-install change, no consistent T-F1 wrapper
penalty, and substantial within-revision wall variability. Do not use those
isolated historical numbers as a source-regression ratio or normalize them by
an assumed factor. Future timing claims need matched repeats and their spread.

Retention caveats are explicit: the first runtime attempt lost its complete
summary to full CPU profiles and is excluded; the GC batch retains all structured
measurements but lacks three verbose raw trial logs. Both are documented, and
the harness now places essential structured receipts last. Full evidence and
validation are under **runs/track-m/census-{integrity,runtime,gc}-***.

Final validation on the same exclusive VM passes TypeScript, type-aware lint,
**12 tests / 18 assertions**, and the independent aggregate audit of all
**72 checked results**. The audit lists the six missing raw files explicitly.
Production sources remain unchanged; Gate 1 remains **3/5**.

## Section 9 T-9A — complement generator gap; stop

All runs are on exclusive **bx_3kjzmmhv**, eight pinned vCPUs, with three fresh
A/B interleaved repeats. Counted units are primary; walls below are median/max
of three target probes, excluding separately reported packet regeneration.
All goal/certificate/path hashes match the original Section 8 T-A packet. The
full certificate, numeric goal, index mapping and 24 active cuts also match;
only a redundant `originalIndex` annotation on the saved cuts is omitted.

| Measurement | Counted units | Wall median / max |
|---|---|---:|
| Strict run A: bare leaf | 226.582788 each | 0.163 / 0.166 s |
| Strict run B: forced G, then complement | 403.136028 / 401.837966 / 401.837966 | 1.631 / 1.785 s |
| Complement diagnostic A: bare leaf | 226.582788 each | 0.171 / 0.187 s |
| Complement diagnostic B: complement alone | **227.664816 each** | **0.141 / 0.144 s** |

The strict shared-400-unit test **does not pass**. `scopesFor` does not propose
`G = CfgT[j$] <= CT[i]`; candidate 77 proposes the opposite strict order instead.
Forced-G queries find cores of **6** for 84 (**39.713046 units**) and **5** for 77
(**18.800593–18.970285 units**). 77 is admitted in all three; 84 in one of three.
The positive branch never finishes, so the complement receives no / too little
remaining budget. Unknown is not labelled SAT or a generator gap.

The separate complement-only diagnostic answers the requested decisive question.
At **`a$# = i`, `j$ < i`, `CT[i] < CfgT[j$]`**, the numeric model has
**V = {27, 32, 77, 84}**, and all four exact source queries return validated SAT
in every repeat. In particular, **27 costs 27.602556 units** and **32 costs
21.179086 units**, with no new cut admitted. This is the requested named
**generator gap**, relative to the captured 32-candidate restricted pool—not a
protocol counterexample or a claim about every possible production-pool fact.

Numeric example: `i=a$#=1`, `j$=0`, `size=2`, `CT[i]=CfgT[i]=0`, `CfgT[j$]=1`.
The source models also have `St[j$]=0`; their separate valuations are retained,
not combined into a fabricated global state.

**Stopped. T-9B, T-9C, T-9D, implementation and Gate 1 were not run.** No production,
default, trusted-rule, cap or total-allowance change. Evidence:
**runs/track-m/section9-ta-v3/** and **section9-complement-v2/generator-gap.json**.

Final validation on the same exclusive VM passes TypeScript, type-aware lint,
**9 tests / 15 assertions**, and independent fresh-process replay of all
**42 source SAT models plus 14 numeric SAT models** and their **56 full paths**.
It also verifies the full certificate, numeric goal, active cuts and original
index mapping against the original packet. See **section9-validation-v2/**.

## Default-on cost wins — F1 / F2 / F3 / T-9C

Landed as one generic engineering change: defer only the focused caller's
pre-transport counted-certificate check; slice leaf pre-checks with a full-check
fallback; cache successful independent checks; and cache fully mapped retargets
by lemma plus target-slice vector and matched content. Missing-hypothesis and
root-collection paths retain their original scope-sensitive behavior. Final
kernel admission and the existing family harness are untouched; no cap or
allowance changes, no later gates.

Six fresh **A1/B1/A2/B2/A3/B3** processes on exclusive **bx_3kjzmmhv**, eight
pinned vCPUs. A is exact **50109a36**. All **30 verdicts match**: one primary,
Inv3915 and Inv1758 check; Inv2973 and Inv* remain unproved.

| Law | A counted units, repeats 1/2/3 | B counted units, repeats 1/2/3 | A wall median/max | B wall median/max |
|---|---|---|---:|---:|
| one primary | 926.633492 each | identical | 2.405/3.306 s | 1.968/2.967 s |
| Inv3915 | 872.335254 each | identical | 3.445/5.582 s | 2.178/3.435 s |
| Inv1758 | 4310.475353 each | identical | 20.427/30.626 s | 12.497/15.252 s |
| Inv2973 | 5002.653010 / 4837.597574 / 4882.748614 | 5002.653010 each | 60.226/60.529 s | 41.628/53.274 s |
| Inv* | 5161.293823 / 5161.673620 / 5161.673620 | 3182.585646 / 5160.096021 / 5160.077578 | 51.879/58.342 s | 34.046/60.036 s |

**Wall variance remains.** B1 Inv* is wall-truncated: 3182.586 units is not a work
saving. A2/A3 Inv2973 are also wall-truncated. B1 is slower than A1 overall;
medians are not a stable speed ratio or evidence of a 60-second gate pass.
Inv2973 has no conditional-cache activity, so its wall difference cannot be
claimed as an F2/F3 saving.

Inv* retarget hits/eligible lookups: **253/322, 506/644, 499/638**. Independent
hits/lookups: **759/851, 1495/1679, 1495/1679**. The fuller repeats pre-check
**78,320** total full-goal hypotheses as slices totaling **342 / 340** hypotheses,
with **zero fallback full checks**. The retarget cache now hits, but the earlier
>=580-hit prediction is not met. Other laws have zero conditional-cache calls.

Final `bun run check` and **236 tests / 1,056 assertions** pass. An independent
receipt audit verifies all thirty verdicts and exact baseline/kernel/harness
identity. Evidence and the patch are in **runs/track-m/cost-wins-interleaved-v1/**;
final validation is **runs/track-m/cost-wins-final-validation-v1/**. Gate 1's
record remains 3/5; no later gate was run.

## Section 10 step 1 — fresh-VM calibration

Retired **bx_3kjzmmhv** by exact scheduler ID after confirming it was idle; its
lease was released. A new exclusive large VM, **bx_25xas5gt**, with eight pinned
vCPUs, ran the requested single uninstrumented census control on exact 50109a36.

| Law | Fresh counted units | Fresh wall | Original census wall | v7 family wall |
|---|---:|---:|---:|---:|
| one primary | 926.633492 | 2.029 s | 1.963 s | 2.716 s |
| Inv3915 | 872.335254 | 2.488 s | 2.323 s | 2.885 s |
| Inv1758 | 4310.475353 | 12.179 s | 11.604 s | 13.413 s |
| Inv2973 | 5002.653010 | 25.327 s | 24.619 s | 32.069 s |
| Inv* | 5161.392998 | 29.857 s | 29.282 s | 35.274 s |

Verdicts remain 3 checked / 2 unproved; checked-law counted work is identical.
This sample is close to the original census, not similarly degraded (Inv2973
+2.9%, Inv* +2.0% wall). It is one calibration, not a stability claim or a gate.
Evidence: **runs/track-m/section10-calibration-v1/**. No production change.

## Section 10 step 2 — T-10A passes, guard retained

On **bx_25xas5gt**, exclusive eight pinned vCPUs, ran A1/B1/A2/B2/A3/B3. B extends
the exact captured packet by one freshly seeded `r$4 <= r$16` instance. All three
B repeats pass: source core **5**, **13.494384 units**; numeric core **4**,
**18.638819 units**; entire checked branch **33.221761 units**, below 120.
Admission retains **CT[i] < CfgT[j$]**, op=5 and the committed-quorum flag.

A retains the old gap at **227.664816 units**, wall median/max **0.137/0.142 s**.
B wall median/max is **0.279/0.525 s**: lower counted work, not a wall speedup;
variance remains. These are different isolated diagnostics, not law timings.
Packet regeneration is separately recorded. All three source/numeric proofs,
all 75 independent-lemma checks, and all 15 control SAT models validate in fresh
processes. The structural term table is retained and exactly restored. TypeScript
and lint pass; **39 tests / 261 assertions** pass.

Evidence: **runs/track-m/section10-ta-v7/**, with all six JSON receipts retained
in one Brotli bundle. Earlier setup failures and the corrected serialization /
retention failures are documented in its README and retained logs. No production
change yet. This permits implementation; it is not a completed law or new gate.

## Section 10 step 3 — generic implementation and pre-gate validation

Default-on equality-consequent substitutions now propose ordinary carried-count
inclusions and preferred scalar scopes. The numeric loop attempts core-selected
batches, validates zero-completed source models, and retains local guarded
splits. Split children share a leaf deadline. Leaf draws reuse the exact existing
`supportBudget` formula, with the existing 1,500-unit row cap still in force.
F1/F2/F3 remain; the kernel, final certificate admission and all existing source,
core, depth and total caps are unchanged.

TypeScript/lint and **245 tests / 1,198 assertions** pass. The real fixture emits
three relevant candidates for Inv* (including r$4 <= r$16 with the predicted
guard) and four for Inv2973.

**The active T-9D probes do not meet their early-leaf pass lines.** Both start
with nine row leaves and receive the existing 1,500-unit row share. Inv* admits
16 cuts and checks one scalar subbranch, then fails to obtain a numeric model
in the other within that share. Inv2973 admits 25 cuts, then reaches the share.
This is not a source SAT/generator-gap conclusion or a complete-law proof.

Evidence: **runs/track-m/section10-generator-v2/** and
**runs/track-m/section10-implementation-v2/**; earlier failed/setup attempts are
retained. Next is the requested three interleaved five-law repeats, not a later
gate. No budget was raised to satisfy these negative probe results.

## Section 10 step 4 — three interleaved Gate 1 repeats, still 3/5

A = exact **50109a36**, B core = **192ebbe2**; A1/B1/A2/B2/A3/B3 on the same
calibrated **bx_25xas5gt**, exclusive eight pinned vCPUs. **All 30 verdicts match**:
one primary, Inv3915, Inv1758 checked; Inv2973 and Inv* unproved. No later gates.
The kernel, existing family harness (including final checkMC) and pins match.

| Law | A counted units | B counted units | A wall median/max s | B wall median/max s |
|---|---:|---:|---:|---:|
| one primary | 926.633492 | 947.543254 | 2.129 / 2.317 | 1.661 / 1.667 |
| Inv3915 | 872.335254 | 874.116294 | 2.616 / 3.804 | 1.838 / 2.007 |
| Inv1758 | 4310.475353 | 4312.612601 | 13.519 / 13.527 | 8.962 / 9.194 |
| Inv2973 | 5002.653010 | 5001.811726 | 32.391 / 35.079 | 23.263 / 24.623 |
| Inv* | 5161.293823 / 5161.293823 / 5161.982847 | 5160.104960 | 34.456 / 36.587 | 27.479 / 29.589 |

Except A Inv*, counted values are identical across repeats. The checked laws
now cost +20.909762 / +1.781040 / +2.137248 units; do not describe this as identical
work. Both open laws still reach the counted allowance. No law is wall-truncated.

The five-law family is **63.009 / 67.076 / 62.618 seconds** on B (median/max
**63.009 / 67.076**), versus A median/max **86.313 / 87.222**. This includes prior
F1/F2/F3 changes, not an isolated Section 10 speedup. **Gate 1 has not passed**:
two proofs are missing and every B family exceeds 60 s. The original generated
harness was not run. The active probes still stop within the first shared row
allowance; the passing T-10A cut has not made the whole traversal fit.

Inv* cache hits in every B: retarget **33/42**, independent **90/102**; 80 sliced
checks, 39,160 full hypotheses to 98, zero full fallbacks. Smaller traversal is
not successful proof progress. Full evidence: **runs/track-m/section10-gate-v1/**;
independent result audit: **runs/track-m/section10-final-validation-v2/**.

Final TypeScript/type-aware lint and **251 tests / 1,208 assertions** pass. The
independent audit verifies six complete fresh-process records, all 30 verdicts,
all reported work/median/max numbers, the exact baseline and fixture, and the
negative gate result. An initial audit-only implicit-any failure is retained
in final-validation-v1; v2 is corrected. No production code changed after the
measured commit **192ebbe2**.

## Section 10 follow-up — diagnostic only, important corrections

Same **192ebbe2**, canonical input and **bx_25xas5gt**, exclusive eight pinned
vCPUs. No core, kernel, harness, cap, allowance or strategy change. No later gate.

**1,500 is a ceiling, not the actual family draw.** The earlier active-op5
probes received that ceiling in isolation. In the real family Inv* op5 receives
124.647629 units, spending 126.094380; Inv2973's first op0 row receives
71.362754, spending 75.807314 before any source attempt. The last atomic query
can overrun a boundary; it does not receive another allowance.

**The current allocation also has a specification mismatch.** leaf-allowance
reuses supportBudget's `max(share,R/3)`: R/3 is a floor, not the requested
ceiling. Existing tests assert 900/9 gives 300. Total is conserved, but the
requested even-share/third-ceiling structure was not delivered. This diagnostic
reports the error without changing the strategy.

First leaves still unresolved after fallback:

- **Inv***: op0, a$#=0, j$<0. Draw 191.008012, spent 2.731550. Numeric query is
  REFUTED with empty core; the `q.core?.length` guard skips proof construction.
  No terminal model/violated set. A fresh empty-hypothesis proof and transport
  both check under the unchanged kernel in **0.0098612 units**. No fix included.
  For context only, the preceding closed row's 31 violated sources give 14
  checked refutations / 17 validated SAT, all explicitly labeled.
- **Inv2973**: op0, a$#=b$=0. The original numeric model reproduces in 6.874298
  units, violating 101 instances. Independent source probes: **8 checked
  refutations / 93 validated SAT**, all with exact units. The actual row spent
  49.854090 natural-case + 6.874298 numeric + 19.078926 batch-selection units;
  zero source attempts. These extra probes are not charged to the row.

The literal cap is in row-cases.ts:103, introduced by **616b0c9c** with no
adjacent numeric derivation. Exact paths, models, all violated-instance results
and every row ledger: **runs/track-m/section10-full-diagnostic-v5/**. Its complete
178 MB decoded trace is retained as a checksum-verified 426,662-byte archive.
The isolated cap ledgers remain in **section10-diagnostic-v2/** and must not be
confused with actual family allocation.

Proved-law deltas are fully reconciled in **section10-deep-diagnostic-v1/**.
One extra retained inclusion adds four downstream hypotheses. One primary:
+20.693282 in four existing model queries, +0.216480 grow = **+20.909762**.
Inv3915/Inv1758: extra grow node visits only, **+1.781040 / +2.137248**. Query
counts unchanged; generator calls themselves charge zero counted units.

Validation: type/lint pass; **255 tests / 1,215 assertions**; fresh validation of
**268 source SAT models / 3 terminal numeric models** and their paths. Source
refutations were checked during their probes; the model validator does not
claim to independently replay those proof trees. The empty-core proof is
independently checked. Gate 1 remains **3/5**, not rerun as a new gate.

## Section 11 — empty-core and allowance fixes

Implementation **5974b916** fixes both defects generically: empty numeric
REFUTED cores now construct and transport a proof; leafAllowance is the even
remaining share with remaining/3 as a ceiling. Split children retain one parent
deadline and unspent allowance remains unspent. Regressions fail on the old
implementation and pass on the fix. The literal 1,500 row ceiling is unchanged:
row-cases.ts:103, originating in **616b0c9c**, with no local numeric derivation;
retain it for the after-MLDR knob census. Kernel and law harness are unchanged.

A = exact **192ebbe2**, B = **5974b916**, order A1/B1/A2/B2/A3/B3 on
**bx_25xas5gt**, exclusive eight pinned vCPUs. All 30 verdicts are identical:
**3/5 checked**. Proved-law counted units are unchanged at 947.543254,
874.116294 and 4312.612601. Inv2973: A 5001.811726 each; B 5108.274084 each.
Inv*: A 5160.104960 each; B 5162.032223 / 5160.085453 / 5160.085453.

| Wall seconds, median / maximum | A | B |
|---|---:|---:|
| one primary | 2.165 / 2.791 | 1.641 / 1.863 |
| Inv3915 | 2.817 / 3.100 | 2.019 / 2.222 |
| Inv1758 | 10.756 / 14.541 | 9.796 / 15.345 |
| Inv2973 | 24.756 / 35.721 | 27.954 / 29.729 |
| Inv* | 28.417 / 33.017 | 24.863 / 24.912 |
| family | 68.881 / 89.173 | 67.214 / 72.299 |

B family walls: **72.299 / 67.214 / 61.567 seconds**, all above 60. Variance
remains material; no stable speed ratio or gate success is claimed.

Post-fix full-family diagnostic:
- **Inv*** now closes actions 0 and 1; unresolved actions are 3,4,5,6. First
  unfinished is **op3, a$#=j, j$=j, CT[j]<CT[i]**. Valid numeric model in
  3.042176 units; 31 violated instances; **4 checked source refutations / 27
  validated SAT**. Production draw 31.837620, spend 31.863512. Its sole source
  attempt, index 54, times out; the separate probe validates SAT, not a cut.
- **Inv2973** remains at **op0, a$#=b$=0**. Production draw 23.787585, spend
  25.269563 (natural 24.498107 + numeric 0.771456), zero source attempts.
  A separate numeric replay validates the 101-violation model in 6.874298 units;
  source probes give **8 checked refutations / 93 validated SAT**.

All exact paths, models, violated sets, source units and conserved row ledgers
are in **runs/track-m/section11-diagnostic-v2/**. Its Inv* total differs slightly
from the timed repeats; this is explicitly a separate diagnostic trace, not a
claim of byte-identical replay. Full timing receipts: **section11-gate-v1/**.
Final independent raw-log audit and fresh model validation: **section11-validation-v2/**.
Type/lint and **258 tests / 1,313 assertions** pass. Fresh processes validate
**120 source SAT models and 2 numeric models**, their paths and all violated
selections; the 12 refuted source receipts were kernel-checked during probing.
Earlier audit-only failures are retained; no timed repeat was rerun. All owned
temporary archives are removed. No later gates or additional strategy changes.

## Sections 12–13 — censored unlimited work, bounded op shards and entry profile

Research-only engine **5974b916**, unchanged production/kernel. The original
deadline-free Inv* run is **censored** (external watchdog exit 137 at 3,602.85 s,
still in op 3); no terminal counted total was captured. Completed op 0–2 spans
sum to 582.893924 units. Its queued unsharded Inv2973 successor was cancelled.

Eleven independent op shards used a 50,000-unit research stop and 600-second
watchdog, each alone on a large eight-pinned-vCPU VM. The scheduler used eight
VMs, reusing three, not eleven distinct simultaneous VMs. **Inv2973 op 4 closed
and checked at 20,732.071099 units / 510.549 s; ten other shards were unknown.**
No complete law closed, no new gate ran, and sums of independent shard work
are not minimum law costs.

The requested Inv* op 3 entry profile explains the apparent reversal. Normal
production reached its first numeric leaf in 701.150586 op-local units; the
deadline-free shard did not reach one in 50,032.659118. Both enumerated the same
9 activation nodes and 4 activation cases. One nested `grow` inside Phase-A
field-source preparation spent **49,100.134260 units / 41.360 s**. That attempt
normally has a 250-unit ceiling; the research override disables local deadlines
as well as the law deadline. These shards therefore cannot establish a
50,000-unit lower bound on production need.

Per-op verdicts, exact units and walls, cuts, raw SAT/refuted source attempts,
first failing guards/points/violated sets and per-instance source results are
in [the trimmed report](track-m/shard-ops-v1/README.md), its audited
[summary](track-m/shard-ops-v1/summary.json), and the requested
[entry profile](track-m/shard-ops-v1/Invstar-op3-entry-profile.json). Exact integer
auditing passed for every captured path and violated set and all eleven work
ledgers. Full dumps remain only in checksum-verified compressed receipts; no
large `columns` dump or giant per-op JSON is committed.

The first profile lost its output to an archive-directory error. Only that
profile was repeated after a tested writer fix; the shard batch was not rerun.
Future work uses bounded captured packets and prepared runtimes; interleaved
three-repeat wall runs remain gate-only checkpoints.

## Section 14 — T-11.5 with ordinary local clocks and checked root cuts

Research only, frozen engine **5974b916**. Production, kernel and the 5,000-unit
law allowance remain unchanged. Only the diagnostic total allowance is 50,000;
the original action/leaf allocation and all source/row/local ceilings remain
active. No inflight columns dump. Prepared bundles were reused. All measurements
ran exclusively on **bx_25xas5gt**, eight pinned large vCPUs. The scheduler
serialized the seeded pair despite a two-VM request.

The no-seed op-4 control is **unknown: 16,672.478177 units / 29.018535 s**,
one terminal leaf visit, 36 learned cuts. Restoring the local clocks changes
its stopping point; it is not a same-work comparison with the former
20,732-unit, nine-leaf, deadline-free closure, and is not an I/O-only speedup.

The 129 checked source attempts cover 79 distinct indices. The design's stated
categories give **45**, not 51, non-frame candidates: 11 inclusions, 20
three-term partitions, 8 five-term purported partitions, 5 ranges and 1
purported self-zero. **31 check independently at the unguarded root**, costing
**2,326.806831 units**; all 79 trials cost **3,110.262124 units / 25.052458 s**.
The other 14 non-frame queries and all 34 frame/bridge queries return SAT at
this standalone source scope. These are not whole-law counterexamples.
Retrying those 48 against the full 1,341-hypothesis law root at 1,000 units
each yields no further proof (50,066.458559 units / 139.280292 s; all unknown).
Neither failed source queries nor whole-root timeouts are imported as cuts.

With all **31** checked root cuts admitted, op 4 remains **unknown:
16,668.652598 units / 60.979686 s**, two terminal leaf visits, **17** new cuts,
32 SAT / 16 checked-refuted source attempts. Op 0 remains **unknown:
7,144.273260 units / 56.512513 s**, three terminal leaf visits, **6** new cuts,
22 SAT / 5 checked-refuted source attempts. Its matched plain control was
7,150.415742 units / 20.112066 s and 13 new cuts. These replay intervals exclude
input loading and the initial seed recheck; the seeded full job times were
64.07 / 59.66 s. Root proof work is separate and not hidden in those totals.

The seeded first failures are `op=4, started=1, a$#=i, b$<i` (121 violated
instances) and `op=0, started=0, a$#=0, b$>0` (114). Exact paths, complete models,
violated sets, per-op ledgers, every root outcome and all qualifications are in
[the report](track-m/section14-tiering-v1/README.md) and its
[summary](track-m/section14-tiering-v1/summary.json); compressed receipts and
independent validation are linked there. The final audit passes: 31 standalone
counted proofs, 31 rejected empty mutants, 48 validated source SAT points, and
four exact path/violated-set checks. Type/lint and the 1-test/7-assertion
root-admission regression pass. Initial lint/data-placement/audit failures
are retained. No complete-law proof, production improvement or gate pass is
claimed. The implemented root lift misses the work/closure prediction; the
proposed 51-template premise was not established, so this is not a clean
falsification of a correctly specified full three-tier design.

## Section 15 — T-12 stopping rule triggered

The corrected three-flag, production-budget experiment is **unknown for all
three requested ops**. Frozen `5974b916`, no root seeds, ordinary 5,000-unit
law allowance, existing local ceilings and row draws intact; all three ran
sequentially on one prepared, exclusive large VM (`bx_25xas5gt`, eight pinned
vCPUs). Production and kernel are unchanged.

| Op | Units | Replay seconds | New cuts | Checked source-query units |
|---|---:|---:|---:|---:|
| Inv2973 op 4 | 3,988.823212 | 10.320221 | 4 | 17.229798 |
| Inv2973 op 0 | 2,709.565693 | 7.589855 | 1 | 0 |
| Inv* op 3 | 2,452.353619 | 4.801551 | 0 | 0 |

**Stop:** op 4 exceeds the prescribed 2,500-unit line without closing. No
further policy optimization or production integration followed. The 600 remains
a research-only deadline cap; the successful-test requirement for deriving a
production rule was not reached.

No six-round query-loop round ran. Op 4's outside-closure units split into
**2,183.805296 field-bound preparation**, **994.374321 frame-lemma work**,
**551.246640 retry grow**, and a **0.086466 global precheck**. Inside its
closures: **259.310490** units. The preserved row draws were **116.660918**
and **22.009527**; op 0's was **23.787147**. These are operation-boundary
ceilings, with measured atomic overruns. Even dropping the final retry grow,
op 4 spends 3,437.576572 units without a proof. This is a failure of the tested
route, not a lower-bound theorem about every possible MLDR proof.

The probe lets an unfinished op use its ordinary retry pass; unlike T-11.5's
initial-pass extractor, totals include both passes. The first recorded
unfinished scopes are op 4 `a$#=b$=i` (133 violated instances), op 0
`a$#=b$=0` (101), and Inv* op 3 `a$#=j, j$=j, CT[j]<CT[i]` (31).

[Full report](track-m/t12-v1/README.md), [audited summary](track-m/t12-v1/summary.json),
and compressed receipts retain all stage counts, exact paths and numeric
models. Independent frame/ledger and exact-integer point audits pass for all
three; type/lint and **3 tests / 8 assertions** pass. The initial driver type
error and an overly broad cross-key frame-class pilot are retained and excluded
from the primary verdict. No complete-law or gate pass is claimed.

## Section 16 — receipt-only field/frame overlap audit

The requested T-12 per-lemma saving is **not recoverable**. The driver passed
`trace:()=>{}` and discarded the helper events; whole-call wrappers retained
costs but no statements, per-lemma costs, outcomes or used premises. Each of
the three requested receipts has zero retained field/frame lemma events.

A static census of 39 archives and historical logs recovered seven positive
field/domain statement forms for the two laws. The literal intersection is
**two**: `if(?canVote=1 && i<size, CfgT[i], 0)<=CT[i]`, and `i<size`.
These are historical positive-event overlaps, not checked reusable-root sets.
None of the explicitly op-tagged normalized field records has `checked:true`;
older checked records omit the op. Another 4,323 positive indexed frame records
(including duplicate copies/tails) lack statement mappings in retained context.

T-12 subtotals are 6,698.388905 units for Inv2973 ops 0/4 and 2,452.353619 for
Inv* op 3. Deleting all field/frame work for free leaves 1,388.930707 and
1,383.481384, but that is not a once-per-law estimate: it removes failed/setup
work and the first proof, and omits other ops. Actual reusable savings and
remaining costs are **unknown**, not zero.

[Report and inventory](track-m/lemma-overlap-v1/README.md),
[summary](track-m/lemma-overlap-v1/summary.json), and compressed catalogues retain
the coverage and limitations. Twenty-eight archives had matching manifests;
eleven are marked unverified. No parse failures or available-manifest
mismatches. No solver reruns or policy/production/kernel changes. Type/lint and
**3 tests / 6 assertions** pass.

## MLDR-GEN / T-13 — syntax-driven quorum lifting (2026-11-09)

Branch `claude/mldr-gen`, based on `claude/track-mldr` at `346fbcd9`.
This lane changes generation, not the protocol, kernel, proof budgets, or solver.
The parallel proof-cost lane's worktree was not modified. No merge or push.

### Implementation and falsifiable contract

- `core/quorum-laws.ts`, called beside the stored-set loop in `guardLaws`,
  recognizes a stored-row majority and an action's quantified carried-set
  predicate. It enumerates nonempty conjunction subsets, lifts through the
  action's exact written value, and proposes no-quorum laws. A row write also
  lifts the set guard and its half-witness assumptions, including disjunctive
  no-quorum weakenings. It handles both numeric if-writes and the Boolean
  disjunctive form emitted by the DSL. No protocol/map/flag names are built in.
- Packed-key row equality supplements the existing tuple-key versioned-row
  clause in `core/field-laws.ts`.
- New laws are admitted **after the existing candidate families**. All go through
  scope, the existing reachable-state filter, and ordinary counted induction.
  The grammar has at most two quorum predicates, three conjuncts each, and a
  32-law cap on its appended family. Reversed row differences reuse a count at
  swapped keys. Counts not read by admitted laws are removed.
- `smallOf(m, source)` reuses the source's sampled graph only after checking that
  the sole changes are fresh, unreferenced count declarations. Changed steps,
  replacement definitions and shadowed map reads cannot use this shortcut.
  Sample views are cached by **machine and state**, not state alone. Filtering
  retains its per-candidate early exit and no sampling bounds were changed.

The falsification contract is unchanged: any different canonical list on the
other 28 ports, or absence of a semantic match for one of the three missing
MLDR laws, fails T-13.1. A bounded induction check is not an unbounded proof.

### Completed semantic and bounded checks

`runs/t13-fast-v4/equivalence.log` compares every binding in `{0,1,2,3}` on
2,000 seeded size-3 random states (seed 13013), not just universally quantified
truth at a state. Each comparison has both true and false instances:

| Published law | Generated match | true / false instances |
|---|---|---:|
| Inv1758 | `fields: CV[a]=CV[b] and CfgT[a]=CfgT[b] -> Config rows agree` | 126874 / 1126 |
| Inv2973, half form | `inX: stored guard reconfigs/inS or disabled/0` | 510826 / 1174 |
| Inv* | `inX: no quorum canVote/3` | 29126 / 2874 |

This is an experimental semantic cross-check, not a proof certificate. The hand
laws occur only in the research comparison oracle, never as production input.

The actual grammar proposes **18** laws (15 quorum/guard laws plus 3 packed-row
field laws), of which **9** pass the small-state filter: MLDR has **34**, not 25,
laws. The design's estimates of 19/11 are not the measured result. There are nine
retained new counts, not six: three equality-body counts remain referenced by
three admitted weakened overlap laws even though their standalone no-quorum
laws fail the filter. They are not silently removed to meet an estimate.

T-13.2: `research/track-gen/t13-relative.ts`, on boat at n=3, T=2, V=2,
enumerated 4,652,219 states after sound unary/pair pruning; 1,905,566 satisfy the
hand family. Every enabled transition was checked, **including post-states
outside the T/V pre-state bounds**. The hand family has **zero CTIs**.

| Alternative added separately | Pre-states satisfying it | transitions | CTIs |
|---|---:|---:|---:|
| unconditional low-term no-quorum | 1434341 | 7773133 | 83718 |
| unconditional row quorum overlap | 1403426 | 7445710 | 2052 |

First low-term CTI: `lead(1,2)` from
`ct=[0,1,1], st=[0,0,0], cv=[0,1,2], cft=[1,0,0], cfg=[0,2,5]` raises
`ct[1]` and `cft[1]` to 2. First overlap CTI: `reconfig(2,4)` from
`ct=[0,0,0], st=[0,0,1], cv=[1,2,2], cft=[0,0,0], cfg=[2,6,6]` changes the
last row to 4 and version to 3. Full receipts: `runs/t13-relative/relative.log`;
`placement.json` labels the exclusive pinned large VM.

### Cost, gates and experiment failures

A same-VM before/after sample-reuse pair (`runs/t13-cost`) retained identical
34-law canonical lists and zero root queries. Total generation wall was
28.737 s fresh vs 22.253 s reused; sampling was 15.155 vs 13.803 s, candidate
work 13.534 vs 8.414 s. This sequential pair includes warmup/host variance: do not
attribute the entire difference to the optimization. The new-law filter itself
was **0.325 vs 0.308 s**, not the prototype's approximately 15 s: it uses the
engine's cached sample views/count cells and exits on the first false instance.
Every timing receipt has `--timing --vm-type large` and its own placement label;
large VMs have different CPU models, so cross-VM wall comparisons are not a
fixed-CPU benchmark.

`runs/t13-gates`: **28 tests / 239 assertions passed** across the new generator,
packed-field, sample-reuse tests and neighboring counted/exists/MLDR tests.
TypeScript and type-aware lint passed. `runs/t13-final-check` also passed both
the complete type/lint check and the corrected file-input commitlint check.

Failures retained, not counted as passes:

1. `runs/t13-check-v1/check.log`: one TS `unknown` map-name error, corrected by
   the explicit type narrowing. The first prototype missed the Boolean-lowered
   row write and generated only 29 laws; the added shape recognition fixes it.
2. `runs/t13-paired-v1` and `runs/t13-original-v1`: snapshot setup failed before
   any run because `cp -al` cannot hardlink the mounted node_modules across
   devices. Source-only copies plus a dependency symlink replace it; no cache
   was cleared and the failed runs do not supply paired measurements.
3. `runs/t13-gates/commitlint.log`: remote snapshots have no `.git`, so
   commitlint's `--edit` mode failed to locate the git root. The corrected job
   reads the same message file on stdin.
4. `runs/t13-paired-v2`: the uniform census tried the universal-state evaluator
   on an existential caller (`some$36`), including on the baseline. Corrected
   the research driver: existential witness proving is not a generation query.
   The following all-port pilot was explicitly stopped after its overly broad
   preflight spent minutes enumerating non-counted caller bindings. The final
   driver applies caller preflight only on counted machines, as production does;
   all proposed candidates still pass the unchanged universal-state filter.
5. `runs/t13-paired-v3/generation-pair-2.log`: the aggregate all-29 paired job
   hit its 870 s effective shell timeout on an EPYC VM. It supplied no complete
   census and is excluded. Only this middle pair was retried, baseline first,
   in `runs/t13-paired-r2-retry` (817.35 s on a Ryzen VM). The retry allowed
   1,800 s for the aggregate shell job; **no per-protocol generation or proof
   budget changed**. The other two completed pairs were not rerun.

### Final paired generation and original-harness receipts

Implementation commit: `74a8a0e9`. The changed production-file git blob hashes are:
`core/quorum-laws.ts` = `50c3076f0c8b8c331853cdbde29470c2059d6431`,
`core/counts.ts` = `c1a976aeeb0f1151d3a06137bc62283deb6e1ef0`,
`core/field-laws.ts` = `91c4c2c1dfda9baf4cd33cb77d3e2cd457727790`,
`core/exists.ts` = `78e8a95cac8c67d8eb5dae2d3b325ec83cece3a6`.

T-13.3 completed: `runs/t13-original-v2` has three **paired original-harness**
runs, with `--ms 60000 --only mldr --skip broken`, tracing/profiling only.
Every baseline and every candidate result is **unknown**, never proven.

| repeat | baseline wall / final reason | candidate wall / final reason |
|---|---|---|
| 1 | 48.749 s / `not proven: one primary per term` | 133.399 s / `not proven: every Config cell is a value of its kind, one primary per term` |
| 2 | 82.147 s / `not proven: one primary per term` | 128.164 s / `time` |
| 3 | 41.211 s / `not proven: one primary per term` | 88.610 s / `time` |

These are measured walls, **not increased requested proof budgets**. The
original engine's counted clock and existing wall ceilings are unchanged.
`runs/t13-original-summary.json` retains the final attempts and phase profiles;
the full logs and placement labels are in `runs/t13-original-v2/`.

Exactly where safety stops (repeats 2 and 3 have the same counted trace):

- The initial 34-law family gives safety a 955-unit first-pass share. Its STEP
  stays `sat` through eight rounds / 1,013 accumulated hypotheses. The retry has
  zero share left and returns `unknown`; the final reason is `time`.
- Inv* (`no quorum canVote/3`) returns `sat` in both passes (68 and 615 counted
  units), so it is not retained as an established invariant.
- Inv2973's generated half form returns `sat` on its initial pass, then
  `unknown` on retry (6,107 counted units, 485 accumulated hypotheses). That
  retry costs 19.027 s wall in repeat 2 and 13.369 s in repeat 3.
- Inv1758's generated row equality stays `unknown` (1,934 and 2,687 counted
  units). None of the three required helpers becomes an established invariant.
- Repeat 1 reaches the existing absolute wall ceiling during the broader
  fallback; the final two-law family still cannot establish either caller.
  Its early Inv2973 retry is likewise `unknown` at 6,107 counted units.

Thus the generation gap is closed; **the original MLDR safety proof is not**.
The limit observed here is helper/STEP proof cost under the unchanged scheduler,
not missing quorum candidates. No full-suite merge gate or successful MLDR
proof is claimed.

T-13.1 completed: three paired all-29 generation censuses, **zero root proof
queries**, and byte-identical canonical lists on **all other 28 protocols in
all three pairs**. MLDR has **25 → 34** laws in every pair, with the semantic
matches recorded above. Complete lists are retained in compressed form in
`runs/t13-paired-v3/generation-pair-{1,3}.log` and
`runs/t13-paired-r2-retry/generation-pair-2.log`.
`runs/t13-generation-summary.json` records their source paths, per-list SHA-256
hashes, counts and phase walls; it is a decoded receipt, not a new experiment.

Each successful pair ran sequentially on one exclusive large VM, two pinned
vCPUs, zero co-tenants, AMD Ryzen 9 9950X. Pairs 1 and 3 ran candidate first;
pair 2 ran baseline first. Placement labels remain in each run directory.
The following are per-protocol **generation seconds**, not proof times. The
large `learning_switch` walls occur on both sides and are mostly existing
sampling; the 60,000-unit candidate budget and all sampling bounds are unchanged.
These are paired observations, not a claim of statistically significant speedup.

| protocol | baseline → candidate laws | canonical comparison | baseline seconds, repeats 1/2/3 | candidate seconds, repeats 1/2/3 |
|---|---:|---|---|---|
| consensus | 3 → 3 | identical ×3 | 0.03, 0.06, 0.02 | 0.04, 0.03, 0.03 |
| tcommit | 4 → 4 | identical ×3 | 0.06, 0.13, 0.06 | 0.06, 0.06, 0.04 |
| lock_server | 5 → 5 | identical ×3 | 0.06, 0.09, 0.08 | 0.05, 0.05, 0.04 |
| quorum_leader_election | 7 → 7 | identical ×3 | 0.69, 0.80, 0.56 | 0.57, 0.57, 0.51 |
| toy_consensus_forall | 9 → 9 | identical ×3 | 0.62, 0.86, 0.62 | 0.71, 0.72, 0.60 |
| simple | 4 → 4 | identical ×3 | 0.01, 0.02, 0.01 | 0.01, 0.01, 0.01 |
| simple_regular | 4 → 4 | identical ×3 | 0.02, 0.02, 0.02 | 0.02, 0.02, 0.01 |
| lockserv_automaton | 17 → 17 | identical ×3 | 0.03, 0.07, 0.03 | 0.04, 0.04, 0.04 |
| sharded_kv | 18 → 18 | identical ×3 | 2.63, 3.08, 2.32 | 2.59, 2.76, 2.38 |
| sharded_kv_no_lost_keys | 6 → 6 | identical ×3 | 2.74, 3.96, 2.41 | 2.69, 2.44, 2.05 |
| lockserv | 17 → 17 | identical ×3 | 0.02, 0.04, 0.02 | 0.02, 0.03, 0.02 |
| twophase | 14 → 14 | identical ×3 | 0.68, 0.86, 0.67 | 0.62, 0.62, 0.47 |
| simple_decentralized_lock | 20 → 20 | identical ×3 | 0.02, 0.02, 0.02 | 0.02, 0.02, 0.02 |
| two_phase_commit | 34 → 34 | identical ×3 | 1.23, 1.29, 1.16 | 1.16, 1.16, 0.99 |
| consensus_wo_decide | 39 → 39 | identical ×3 | 5.82, 6.10, 4.82 | 5.54, 5.36, 4.68 |
| consensus_forall | 48 → 48 | identical ×3 | 10.19, 13.02, 9.81 | 9.29, 10.72, 10.75 |
| naive_consensus | 13 → 13 | identical ×3 | 1.11, 1.40, 1.09 | 1.11, 1.34, 1.22 |
| client_server_ae | 10 → 10 | identical ×3 | 1.42, 1.73, 1.33 | 1.32, 1.42, 1.48 |
| client_server_db_ae | 15 → 15 | identical ×3 | 6.41, 8.17, 6.75 | 5.92, 7.81, 6.94 |
| simple_election | 12 → 12 | identical ×3 | 1.57, 1.99, 1.34 | 1.62, 1.76, 1.49 |
| toy_consensus_epr | 8 → 8 | identical ×3 | 1.06, 1.45, 1.06 | 1.19, 1.19, 1.13 |
| toy_consensus | 5 → 5 | identical ×3 | 0.60, 0.88, 0.57 | 0.66, 0.72, 0.79 |
| firewall | 7 → 7 | identical ×3 | 0.04, 0.06, 0.03 | 0.03, 0.05, 0.04 |
| majorityset_leader_election | 17 → 17 | identical ×3 | 1.18, 1.88, 1.23 | 1.11, 1.44, 1.44 |
| consensus_epr | 29 → 29 | identical ×3 | 8.60, 12.21, 8.06 | 8.53, 10.51, 8.92 |
| learning_switch | 16 → 16 | identical ×3 | 165.76, 158.93, 139.83 | 154.44, 157.34, 148.52 |
| learning_switch_i4 | 463 → 463 | identical ×3 | 160.89, 147.49, 149.11 | 135.62, 164.16, 133.60 |
| paxos_epr | 77 → 77 | identical ×3 | 19.97, 19.70, 16.51 | 16.11, 20.50, 15.40 |
| mldr | 25 → 34 | changed | 16.93, 15.46, 15.44 | 16.06, 19.00, 15.24 |

`runs/t13-census/census.log` separately confirms the structural trigger is
**1 of 29**: MLDR proposes 15 quorum/guard laws and 3 composed-row laws; all
other ports propose zero of both. Full type/lint and file-input commitlint
checks passed again in `runs/t13-report-check` after the final research-tooling
changes. No production file changed after implementation commit `74a8a0e9`.

Reproduction commands and receipt formats: `research/track-gen/T13.md`.
All started jobs are finished or explicitly stopped. No merge or push was done;
large logs and decoded receipt archives remain outside git.

## MLDR-GEN: strict 60 s deadline follow-up (2026-11-09)

The earlier 88.610–133.399 s candidate runs above are **not strict-gate passes**.
This follow-up compares the completed generation branch at **`189eefcd`** with
the deadline fix, not the earlier 25-law `346fbcd9` baseline. Both sides generate
34 MLDR laws. No kernel/solver file, law or trusted fact changed.

### Where the wall escaped, and the generic fix

1. `searchCounted` called `guardLaws` and `smallOf` **before** starting its wall,
   then granted `2 * ms` to proof search. `proveRule` also did preparation and
   refutation preflight before reaching that scope. Thus `--ms 60000` was not a
   60 s end-to-end deadline.
2. Sampling's BFS and random walks, sample-law binding enumeration, and the
   preflight watcher's binding enumeration had no enclosing-wall checkpoints.
   The counted clock does not debit this work. Several counted phase, Houdini,
   refinement and fallback boundaries could also continue after wall expiry.
3. `proveRule` now puts preparation, preflight, generation and proof under one
   absolute wall. `searchCounted` starts its own nested scope before generation
   and no longer doubles it. Nested scopes only shorten the caller's deadline.
4. `core/wall.ts` supplies cooperative cancellation for untrusted search only.
   Sampling checks each request; binding enumeration checks at entry and every
   256 tuple prefixes, with a fresh poll for each state/law. Counted phases and
   refinement/Houdini/fallback boundaries check the wall. A local attempt's
   expired wall returns `unknown` for that attempt. A whole-run expiry returns
   an unchecked `unknown`, never a proof. Interrupted sample graphs are not
   cached as complete or replaced by an empty successful filter.
5. The first fix still returned at 60.142 s inside the engine / 60.37 s as a
   process (`runs/t13-wall-diagnose/engine-60s.log`): an in-flight synchronous
   operation plus process setup/output straddled the deadline. Work now leaves
   **`min(1000 ms, requested_ms / 20)`** of completion headroom, generically.
   For 60 s the work wall is 59 s; the external hard wrapper stays exactly 60 s.
   This is a wall-only reduction. The requested 60,000 counted units, rates,
   counters, per-law shares and search ordering are unchanged.

### Strict three-pair gate — final source

`runs/t13-wall-final-v2`: every individual process ran the **unchanged original
harness** under:

```sh
timeout -s KILL 60 bun research/protocols/ic3syn/run.ts \
  --ms 60000 --only mldr --skip broken
```

`GDP_COUNTS_TRACE=123` / `GDP_COUNTS_PROF=1` only observe. `/usr/bin/time`
measures the process including startup and output, separately from `search.ms`.
Each pair is sequential on one exclusive large AMD Ryzen 9 9950X VM, two pinned
vCPUs and zero co-tenants (`placement.json`). The middle pair is baseline first;
the other two are candidate first. Exit 137 is a **kill**, not an unknown verdict.

| repeat | parent process / exit | fixed process / exit | fixed engine wall | fixed result |
|---|---|---|---|---|
| 1 | 60.00 s / 137 (killed) | 59.36 s / 0 | 59.223 s | unknown |
| 2 | 60.00 s / 137 (killed) | 59.19 s / 0 | 59.028 s | unknown |
| 3 | 60.00 s / 137 (killed) | 59.24 s / 0 | 59.127 s | unknown |

All three fixed processes finish cleanly under 60 s and emit their JSON verdict.
The final reason is `time (rule result)`. The MLDR proof remains **unknown**;
this fixes the deadline, not the remaining proof-cost limitation.

### Counted-work preservation and generation nonregression

The trace audit strips wall/profiling fields but retains the law, pass, share,
counted work and outcome. All **37 / 39 / 41** completed parent attempts are
identical prefixes of the corresponding fixed traces. Each fixed run then logs
one additional, deadline-interrupted attempt; no completed parent attempt was
reordered or assigned different counted work. Whole-run work differs with host
throughput and the cutoff: it is not claimed equal after a wall interruption.
Tests separately verify that checkpoints/headroom do not debit `fullWork` or the
counted clock, and an expired preflight does not debit another watched tuple.

The final paired generation census covers **all 29 protocols**, in three disjoint
subsets (`generation-rest`, `generation-switch`, `generation-switch-i4`). It
makes **zero root proof queries**. Every canonical list is byte-identical to
`189eefcd`, including MLDR's **34** laws; therefore all other **28** are unchanged.
Their SHA-256 hashes also all equal the earlier full, unsharded T-13 census.
MLDR generation was 14.866 s parent / 15.471 s fixed in this pair. This is one
paired observation, not a statistically significant speed claim.

Full exit-code, timing, counted-prefix and 29-list hash receipts:
`runs/t13-wall-summary-v2.json` (decoded by
`research/track-gen/t13-wall-report.ts`). Full logs remain in
`runs/t13-wall-final-v2`, outside git.

### Tests, failures retained, and reproduction

`runs/t13-wall-checks-v2`: **40 tests / 177 assertions passed**, including six new
wall/caching/accounting tests and the neighboring search, exists, quorum and
field-law tests. Full TypeScript, type-aware lint and file-input commitlint passed.
No baseline fragments were mounted into this check job.

- `runs/t13-wall-probe`: first cooperative fix still got exit 137 under the
  strict wrapper. It is a failure, not included among the final three pairs.
- `runs/t13-wall-diagnose`: the 10/60 s diagnostic runs used wider outer wrappers
  solely to measure the residual overrun; they are not strict-gate evidence.
- `runs/t13-wall-final/checks.log`: TypeScript saw the four mounted baseline
  fragments under `baseline/core` and reported unresolved imports. This was a
  job-layout failure, not fixed by weakening checks. Checks now run separately
  without that data mount. The earlier unamortized polling experiment is also
  not substituted for the final source's timings above.

Final production git blob hashes:

- `core/counts.ts`: `4f67e82158e82979957df4925120d8c30b6d6e82`
- `core/dsl.ts`: `a714df3e14440ae640014a9005e58d73cecc01df`
- `core/exists.ts`: `f87beb2c46ace579ef0c21ec7917aa3ee25637d6`
- `core/watch.ts`: `0dde3d54af8eb67841e0e64ef4dc31afba7b9618`
- `core/wall.ts`: `3fd094c12de30c5bba73ace61c6f72388d780620`

Reproduction commands, baseline overlay and receipt semantics:
`research/track-gen/WALL.md`. All jobs are finished. No merge, push, full-suite
merge gate or successful MLDR proof is claimed.

## Lane A / E-14 — in progress (2026-11-09)

Handoff `MLDR-29.md` and design Section 14 read. Baseline for the full merge
comparison is local main `b788e195`; the E-14 generation-only control is this
branch at `cd0a1aa4`. Hypothesis: extending width-2 cubes to fresh lifted one-key
counts supplies the missing initialization law; finite relative-CTI filtering
then removes false/non-inductive candidates before allocating proof shares.
The other 28 candidate lists must remain byte-identical. Finite filtering is a
falsifier only: it never supplies a trusted invariant, drops a caller, or drops
on an unknown evaluation. All survivors still require ordinary checked proof.

Initial probe (`runs/t14-check-v1/`): 23 tests / 83 assertions passed; the
check then correctly rejected three `Rule | Machine` adapter type errors.
Both required count cubes were present. This first version incorrectly exposed
unused lifted-count vocabulary (53 helpers before filtering) and spent 35.88 s
in finite filtering, retaining 50. Corrective work restricts atoms to counts
read by admitted candidates, covers the full finite action range, and avoids
exception-driven binder dependency tests. The initial probe is not acceptance
evidence. Second probe (`runs/t14-check-v2/`) passed TypeScript, type-aware
lint and all 23 targeted tests, but generation hit its cooperative wall during
the second finite round (not an acceptance run). Its trace exposed costly
exception-driven dependency checks and insufficiently diverse neighbor states.
The next version uses explicit dependency tests, independent finite configurations
as well as neighbors, and stored-row cardinality atoms rather than filtered
quorum bodies. All 29 generation controls ×3 are submitted separately through
the warm-VM scheduler. No MLDR proof or green merge gate is claimed.

Validated E-14 implementation (`runs/t14-verify-v6/`): all 24 targeted tests
passed, with TypeScript and type-aware lint reporting zero errors/warnings.
The generation probe completed in 23.14 s on an isolated **AMD EPYC 4585PX
16-Core Processor**, large VM, four pinned vCPUs. It retained **35 total laws**,
not the design's ≈22 prediction: the finite pass removed five helpers, but
several other predicted CTIs were not sampled. The pass is a falsifier, not
an exhaustive search, and no additional laws are dropped on that basis.
The two required initialization cubes are present. The phase timings and
exact surviving list are in `generation-acceptance.log`; the CPU receipt is
`placement.json`.

Section 15.1 is now implemented: the denominator excludes laws already tried,
kept or carried, and the share is recomputed immediately before each law.
Order, `supportBudget`, counted fuel and wall deadline are unchanged.
`runs/t14-share-check/` passed **13 tests / 2,538 assertions**, including
conservation and redistribution cases (isolated AMD Ryzen 9 9950X).
The same E-14 source with the old round-fixed share is archived as a research
control; three strict pairs isolate scheduling, while three further strict
pairs compare the combined branch with main. CPU model, VM identity and
pinning for every strict pair will be read from its `placement.json` into
the final gate report. These pairs and the generation census are pending.

### First full gate: not green

`runs/t14-gate-v1/` completed all 154 jobs on boat. Both sides proved all
**28 already-solved IC3Syn protocols in all three repeats (84/84 each)**
and all **10 DuoAI protocols in all three repeats (30/30 each)**. MLDR was
unknown on both sides, all three times. No broken variant was proved:
11 were refuted, 17 returned unknown, and `sharded_kv_no_lost_keys` hit the
strict wrapper on both sides. The killed broken check is not a safety proof.

Six test shards and type/lint/commitlint passed. Shard 2 failed the existing
`packed column domains are split once before row reconstruction and checked`
assertion in `core/count-recovery/field-bound-lemmas.test.ts`: its tree was
defined and checked, but the expected route-trace event was absent. Paired
isolated reproductions on unchanged main and this branch are submitted;
this is not yet classified as a regression or a pre-existing test defect.

The coordinator reported a scheduler recovery stall from about 12:28–12:40.
No completed assertion failure is being relabelled as infrastructure. The
restart blanked 72 CPU labels in the placement receipt: 68 can be recovered
from a nonblank receipt for the same immutable VM ID, and one more from the
earlier v6 check. Three cases without an existing CPU label are being rerun.
Future paired logs print the guest CPU model themselves. The final-source
29×3 census/capture batch was held, not discarded, and remains in progress.
The full report will list every protocol whose counted totals moved; the
raw first-gate pairs and aggregation are retained. Cross-receipt recovery
now supplies CPU labels for every original pair, without inferring a model
from a VM class. No GATE GREEN claim is made while the test and bar are pending.

### T-14 generation and first strict confirmations

`runs/t14-final-v1/` completed all 94 jobs after recovery. The generation-only
census has **87 pairs, zero prover queries, and all other 28 canonical lists
byte-identical in all three repeats**. MLDR changed from 34 to 35 laws in each
repeat, with the same candidate hash
`35b0da100cc1a3b922deb1f2ceab24068ff3d1d46f968b4cafbdd15d99f1e2bc`.
Candidate generation took 25.51, 25.31 and 25.39 s.

The three original-harness candidate processes returned unknown cleanly in
59.41, 59.64 and 59.17 s; main returned unknown in 22.70, 37.57 and 19.85 s.
Repeats 1/2/3 used AMD EPYC 4585PX / AMD Ryzen 9 9950X / AMD Ryzen 9 9950X,
respectively, each pair isolated on one pinned large VM.

Section 15.1 lifted Inv*'s share from 1,714 to 3,004 and Inv2973-half's
to 2,838 in the isolated control. All 15 distinct early kept-law labels
were retained in all three share pairs, and no returned helper was lost
on any of the other 28 protocols. The top-level verdict did not improve.
Inv* returned pass-0 sat and pass-1 unknown. Inv2973-half still returned
pass-0 sat, and pass-1 sat in repeats 2/3 (repeat 1 hit the wall). Inv1758
and the count cubes were not reached before the wall; no claim that all
three helpers got the predicted allowance is made.

The first capture transported repeat 1, but duplicates of whole families
inside each witness overflowed repeats 2/3. The bounded transport now keeps
all scalar witnesses separately from replay roots and is being rerun.
The initial standalone test comparison was invalid on main, which does
not contain the branch's field-recovery test; the candidate passed it 3/3.
The route assertion has a 50 ms internal wall window and is being retested
under the deterministic counted clock, without changing production code.
The bar's failed-window runs were retained as infrastructure failures;
the old controller was stopped and a fresh paired quick bar completed: wrong 0, solid losses 0. Three non-solid CHC losses (1/4 candidate solves versus 3/4 or 4/4 baseline solves) are retained in its report, not hidden.
