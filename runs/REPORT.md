# RESUMED — lane E, 2026-11-10

## Strict-bound repair validated; not an Inv1758 speedup

Replacement batch **`20261110-031307-hyqtwf`** completed all nine jobs. Each
of its three source variants passes **89 tests / 305 assertions**, zero
warnings/errors. All **12 measured arms remain unproved** at the unchanged
2700-unit share. The plain repaired candidate has exactly the control's
**2700.233514 units / nine refinement rounds** in both orders. Early
completion is **2700.272896 / five rounds**, also unchanged from the prior
unrepaired experiment. Row-first is wall-censored, not a saving.

This confirms the call-chain caveat below. The source-bound strictness repair
is tested proposal correctness (including a checked boundary certificate and
negative controls), **not** an Inv1758 performance fix or a full-helper proof.
No production scheduling change is promoted. Exact source/test/runner hashes,
paired results, CPU labels and validation: `runs/mldr-rows-guard-v3/`.

The validated repair and complete negative evidence are committed in
**`9528c134`**. The follow-up focused-route batch `20261110-031705-ar91sv`
also completed: **25 downstream tests / 76 assertions pass**, but all eight
focused-only / one-third-share arms remain unproved. The unit-limited
one-third pair is exactly unchanged at **2700.696015 units** (900.543481
focused + 1800.152534 ordinary). The other runs are wall-censored; their
lower reached work is not a speedup. Measurements and placement:
`runs/mldr-rows-focus-guard-v1/`. The retained operation trace reaches a
scalar SAT hint on op4, then a 192-hypothesis field query remains unknown;
these are not validated counterexamples or checked operation closures.

The next disposable hypothesis is the field-only demand gate: closure
requires two live count reads in the claim, while Inv1758 claims primitive
fields. A bounded declaration-backed bridge selects existing pre-count
reads and already proposed coupled reads, without adding any premise.
Paired/test task `981ca35b-2773-4d0d-b1f7-bf306f456c61`, batch
`20261110-032020-cxko7e`, is active in `runs/mldr-rows-field-demand-v1/`.
The prototype's four paired arms remain unproved; one pair is fully
unit-limited and the other candidate arm is wall-censored. The first source
check failed because the mounted `.ts` payloads were typechecked at their
data-directory paths, not their copied module paths; tests did not run.
The packaging-only replacement (`20261110-032233-wyx97d`) passes source
check with zero warnings/errors and **31 tests / 90 assertions**, including
checked primitive-field closure and the false-union negative control. Exact
helper/test byte equality is recorded. No proof jobs were repeated. The
new gate is reached (ten field-demand events and eight internal cut events),
but no whole helper or independently replayed operation proof is claimed. Production closure source is unchanged. Lane B's old
row/eager-member/cap failures remain contrary evidence.
Original-harness and final-gate status remain unchanged and unproved.


## Inv1758: first schedules rejected; strict-bound gap isolated

Batch `20261110-024132-w69iz6` completed all ten jobs. All **16 measured
arms are unproved** (early/row-first, controls, 2700/6000, both orders).
Several lower work totals are wall-censored and are not improvements.
Both source checks passed **14 tests / 63 assertions**, zero warnings/errors.
Measurements and retained-archive hashes: `runs/mldr-rows-early-v1/`.

Proposal-only replay (`20261110-024655-340opd`) supplies the discriminant:
controls have zero matching member inclusions; the new contexts have 16,
with ten admitted. At the actual actor/other-row pair the existing proposer
requires `CT[i]+1 < CfgT[b]`. The source flag instead establishes
`CT[n] < CT[i]+1`, so **`CT[i]+1 <= CfgT[b]` suffices** for `CT[n] < CfgT[b]`.
The captured leader boundary has equality. No new law or trusted fact is needed.
Raw/projection: `runs/mldr-rows-inclusions-v1/`.

The typed proposal fix retains source strictness. Its new tests cover all
four source/target strictness combinations, a checked equality-boundary
certificate, omitted flags, and a non-strict-source counterexample. The
nine-job frozen test batch compares plain/early/row-first at **2700 only**
and runs three source/test checks. Task
`8769a096-6698-465c-b9ba-0e8edbd6be25`, output `runs/mldr-rows-guard-v1/`.
The local patch is pending validation, not a demonstrated Inv1758 improvement.
Static review then caught missing undefined guards in the new test fixture;
test-only v2 checks add them with identical production bytes. No proof jobs
are repeated. V2 task: `b8fc0df3-4514-4277-9209-e4ea8e904e9a`.
Commitlint passed in `20261110-025106-jgmtei`; it is not a source/test verdict.
`core/counts.ts`, the kernel, laws, and allowances remain unchanged.

Both timed-out clients were recovered without duplicate work. All **12 jobs
are terminal setup failures**: the submission misspelled the local input
directory (`inputs-v1`, not the existing `input-v1`), and every job stopped
at the missing `lane-e-rows/family.json` copy. **No source check, test or
proof measurement ran** in these batches. Full logs, hash/placement records
and setup-stage classification are retained in both output directories.

Replacement batch `20261110-031307-hyqtwf`, task
`624a22b5-2f78-426c-9b1f-42bdaada5efc`, submits only the nine
needed jobs, now with the corrected test fixture and mount. The new launcher
checks the actual input hash before submitting; proof workers check it again.
Test-only workers no longer depend on a family copy. The 2700-unit share,
4800 ms proof wall and 240 s job watchdog are unchanged. The longer client
wait covers scheduler queue time only. Output: `runs/mldr-rows-guard-v3/`.
All test/proof outcomes for this replacement remain pending.

Scope correction from the downstream audit: the initial member-premise path
uses guard maps/keys, not its comparison operator. The operator is consumed
by deferred derivability closure, which may not be reached before the share
is gone. Thus the strict-bound change is a correct proposal repair, but it
may not change the initial search at all. The paired jobs must decide that;
the boundary mismatch alone is not a demonstrated convergence diagnosis.

Coordinator's isolated no-share census closes Inv1758 7/7 in pass 0 and
5/7 in pass 1. This does not imply a bounded full-helper or original-order
proof; the next experiment targets convergence rather than a larger share.


## Inv1758 baseline returned; missing actor-row count context under test

All four baseline jobs completed in **20261110-023802-tbr25k**. None produced
a checked Inv1758 proof. At 2700 units: ordinary-first returns an uncertified
`SAT` after **2700.129 units / 3.381 s**; counted-first is **UNKNOWN** after
**2700.234 / 2.359 s**. At 6000 units both reach the unchanged seven-second
wall (**3574.540** ordinary-first, **3090.096** counted-first). Lower reached
work at a wall is not an improvement. Full logs, CPU labels and hashes:
`runs/mldr-rows-baseline-v1/`.

Frozen-model inspection ran on boat, batch **20261110-024021-a5u0mp**.
Counted STEP starts with 68 hypotheses, **no universal-law tuples**, six
keyless count reads, and ten count instances. By the tenth query it has 244
hypotheses but still no bounded-completion event. The last model is the
unchanged `become_leader` action: actor i equals target row a, with a higher
pre-state config term, and distinct payload cells at the symbolic column.
This is an abstract model, **not a validated reachable counterexample**.
Compact diagnosis: `runs/mldr-rows-inspect-v1/diagnosis.json`.

Testing two **disposable-only** schedules: move the existing 4-term/48-tuple
count-law completion before the first counted query; additionally prioritize
actual row/request terms ahead of the third (column) binder. Each is paired
with an unchanged control in both orders and at both budgets, plus a source
check/test worker. Task **ce05e3b2-32d6-47f4-a62d-8d9896fada63**, output
`runs/mldr-rows-early-v1/`. No successful result is claimed yet.

**For B/I:** production `core/counts.ts` is unchanged. The experimental
installer touches only disposable boat copies of its completion block.
A later production scheduling hook would overlap B's file and will be
reported before promotion. Both kernel and original family are untouched.
The four compressed captures total about 1.48 MB and remain ignored; only
small receipts/hashes and compressed logs are committed.


## NEW TARGET — Inv1758 assigned to lane E

Coordinator moved Inv1758 to E; B retains Inv* / p1 and F retains
Inv2973-half. The completed safety evidence below remains unchanged.

Initial four-job baseline is submitted as task
**8901c267-d68f-4835-8d67-213bee7ed517**, output
`runs/mldr-rows-baseline-v1/`: ordinary-first and count-first at 2700 units /
4800 ms and 6000 units / 7000 ms, exclusive pinned large VMs. It uses the
existing hash-checked 9124348d source overlays and the **exact same fresh
34-law family**, mapped without changing machine/laws to the existing
`lane-b-cost.ts` diagnostic. No results or production improvement claimed.
Family/input hashes are in `input-provenance.json` and the working plan in
`research/mldr-rows/WORKING.md`.

Initial hypothesis: Inv1758's field-only STEP may need count-law tuples at
the actor/other row before its repeated MBQI rounds; B's eager completion
for count-bearing targets does not cover this case. Read the actual captures
before choosing a generic patch. B's negative eager-member / 64-row seeding
results are respected, not rerun. No production source has changed yet.


## VERIFIED — fresh generated-family safety below its share; original remains UNKNOWN

Production source **9124348d5d313ab7e89082b0146a72d6a7c8bf66** completes
conditional safety on its **freshly generated 34-law family** at
**2052.9079764 counted units**, both with the **2700** and **6000** allowances.
The family was captured with zero proof queries and no hand law. START and
STEP certificates pass ordinary checks plus independent reconstruction/replay
at both allowances. The two captures are byte-identical, including the full
family and all three proof files; source and archive hashes are checked.
Measured walls: **2.834 / 2.839 s**, exclusive eight-vCPU **EPYC 9455 large**.
This remains conditional: the other generated laws are assumed in this
single-target diagnostic, not proved as a whole family.

The actual original harness is **UNKNOWN 3/3**, `time (rule result)`:
**59.187 / 59.003 / 59.060 s** (R1 EPYC 4585PX; R2/R3 EPYC 9455, all pinned
exclusive large). No original proof, 29/29, or GATE GREEN is claimed.

Focused validation passes **91 tests / 314 assertions**, zero source warnings
or errors. Official quick-suite unit coverage and its retained aggregate
timeout caveat are below. The eight prior commit messages and the three
subsequent report messages pass commitlint; this evidence commit's exact
message was separately linted before commit and byte-compared afterward.

Complete batch **20261110-015518-rcbski**: all five job rows now recovered;
zero running or queued. The second observer failed parsing a shell response,
not in any proof/test job. `research/mldr-incl/collect-batch.py` recovered the
existing completed rows directly into files, avoiding bounded stdout. No
job was repeated or cancelled. Source-bound summary, all five compressed
logs, raw/compressed hashes, full conditional proof captures, and reproduction
instructions: **`runs/mldr-incl-flags-first-v1/`**. The SDK archive is only
22,240 bytes; no bulky local evidence or new whole-tree archive was created.

### For lanes I / D / B

**E's fresh-family conditional result is verified and ready as evidence.**
The production change remains **9124348d**, not this report-only commit.
I verified it is already an ancestor of V12 **8769061b**. Lane I's V12
validation/census are active; use that combined candidate for the eventual
canonical D gate rather than duplicating an E-only gate. This is not a new
integration verdict: B/F changes still require that combined validation and
D's exact paired 29x3, DuoAI, broken and bar admission. B's historical
2052.91-unit expectation now has an actual fresh production-source receipt.


## Commitlint verified; three production jobs remain never-started

Batch **20261110-015805-vx6pzb** is complete: commitlint exits **0** for its
eight exact message files, including production **9124348d**, on Ryzen 9
9950X (2 vCPUs; shared placement, not a timing claim). Scope and complete
commit IDs: `runs/mldr-incl-commitlint-v1/verified-result.json`; log preserved.
Later reporting commits were not in that batch and are checked separately.

Observer 09ae80a4-de5a-4138-addd-93d17289872a ended at its 600 s observation
deadline, not a worker failure. A fresh authenticated snapshot of production
batch **20261110-015518-rcbski** confirms integrated-check, original-r2,
and fresh-conditional-and-replay are **queued with zero placements**, no
start in flight, and no result error. R1/R3 are the already-preserved UNKNOWN
rows. Snapshot: `runs/mldr-incl-flags-first-v1/pre-recovery-snapshot.json`.
I have not cancelled or resubmitted this registered work. One read-only
collector now resumes at row 2, task **aaf38a3b-7d3f-40e1-bfa5-41bd5af42f86**,
again bounded at 600 s; there is no overlapping observer.

### For lanes B / I (static review, not measured integration evidence)

Reviewed B's **44e06e5c**: early count-law completion is explicitly guarded
by a target count read; its comment preserves the field-only lazy path.
The declared MLDR safety law in `research/protocols/ic3syn/models.ts` reads
St/CT/size, not a named count. This suggests the new hook does not directly
change E's isolated safety attempt. It is not an integration proof or a
new counted-units result. No production code or shared scheduler policy
was changed, and no redundant conditional experiment was submitted.


## Official quick-suite coverage recovered; production proof row still queued

The unchanged final bundle `research/security/score.test.ts` passes:
**28 tests / 1,305 assertions**, source check clean. Tail batch
**20261110-021006-ih70jv**, EPYC 9455, eight pinned vCPUs, worker exit 0.
Together with the seven complete shards and the ten-unit completed prefix,
this recovers all **167 unique units** of the official quick-suite roster on
9124348d. The original eight-shard batch still contains its timeout; it is
not relabelled green. The prefix completion is established by the unchanged
sequential runner advancing to its final unit, not by missing test totals.

The available logs report **1,077 passing tests / 394,688 assertions**,
excluding the missing numeric summaries for that prefix. Exact roster,
runner hash, and coverage limitation:
`runs/mldr-incl-quick-tail-v1/completion.json`. Tail log, CPU placement, and
original partial receipts are preserved. This is package quick-suite
coverage, **not** the full 29x3/DuoAI/broken/bar/Lane-D merge gate.

Read-only recovery retrieved the original 9124348d R1/R3 logs without
rerunning them: both **UNKNOWN**, `why: time (rule result)`, at **59.187 /
59.060 s**, on EPYC 4585PX / EPYC 9455 respectively. Exact rows and compressed
logs: `runs/mldr-incl-flags-first-v1/recovery-first-two.json` and siblings.
R2, focused validation, fresh conditional/replay and commitlint are still
registered, queued, and not claimed as executed. The same read-only
collector task **09ae80a4-de5a-4138-addd-93d17289872a** remains active until
its bounded observation ends. No duplicate submissions or cancellations.


## Broader tests partial; registered validation preserved, not duplicated

Quick-suite batch **20261110-015717-9fubkz** completed with **seven passing
shards and one timed-out shard**. All eight source checks pass. The seven
complete shards report **1,049 passing tests / 393,383 assertions**, zero
assertion failures. This is **not a complete quick-suite result**.

Shard 1 exits 124 after 570.04 s. Its unchanged sequential runner reached
the final `research/security/score.test.ts` bundle, after its other ten
units including `examples/data.ts`; those earlier units necessarily
returned zero for execution to advance. Their test-summary stderr is
absent from the timed-out worker log, so no numeric test total is inferred
for them. The full log, exact roster, partial totals and CPU labels are in
`runs/mldr-incl-flags-quick-suite-v1/`.

Only the unfinished score bundle is being rerun, unmodified, under the same
600 s job ceiling and unchanged per-test/proof budgets. Registered batch
**20261110-021006-ih70jv**, task
`48794f3e-aaa7-4ae8-ab58-972050aa4e7e`, output
`runs/mldr-incl-quick-tail-v1/`. No passing shard or earlier unit was repeated.

### Queue recovery / for the coordinator

The production controller expired at 900 s; the commitlint controller
expired at 600 s. Authenticated snapshots confirmed both batches still
exist, open: **20261110-015518-rcbski** has original-r1/r3 finished, while
integrated-check, original-r2, and fresh-conditional-and-replay are queued;
**20261110-015805-vx6pzb** has its commitlint job queued. These are registered
work, not failed proof or lint verdicts. Neither batch was resubmitted,
cancelled, or removed. No shared scheduler/VM was touched.

Read-only collection is reattached with one long-poll per batch, ten-minute
observation ceiling, task **09ae80a4-de5a-4138-addd-93d17289872a**. It fetches
the scheduler's durable logs as rows arrive, never submits or closes work.
Observer provenance: `runs/mldr-incl-recovery.json`. Production 9124348d's
conditional verdict remains unverified until that queued row executes.
No 29/29, full-suite, commitlint-pass, or gate-green claim.


## Ranking result: conditional safety below its share; production validation running

Completed **20261110-014758-a6x9cy**, seven rows, each with a passing source
check and 6 installer/provenance tests / 21 assertions. This is a controlled
research change to the prior exact generated family, with initial ranges
disabled, not yet a production result.

| early field-law prefix | at 2700 | checked cost at 6000 |
|---|---|---|
| unchanged control | UNKNOWN | 3817.24253 |
| none | **checked, 2052.9079764** | **2052.9079764** |
| top 1 | checked, 2116.7015284 | 2116.7015284 |
| top 2 | checked, 2125.2738472 | 2125.2738472 |
| top 3 | UNKNOWN | 4851.5793732 |
| top 4 | UNKNOWN | 4877.7164352 |
| top 6 | UNKNOWN | UNKNOWN, stopped at 6000.11004 |

Rank zero keeps every flag premise and all scalar laws available to MBQI;
it only avoids proposing scalar-field tuples before a model asks. Both
allowances independently reconstruct/check START and STEP, use `member$4`,
`member$5`, and row inclusion `w$280`, and produce the same complete archive:
`5475f29a04a0818277664657ce123974a6809dc3e4af7c3ae64707b422949891`.
The measured cost reduction is 1764.3345536 units (46.2%). These are counted
work comparisons, not cross-CPU speedups. Rank-zero walls are 6.606 / 5.772 s
on its Ryzen 9950X; no unconditional safety or original-harness win follows.
All exact outcomes, CPU labels and compressed receipts:
`runs/mldr-incl-member-rank-v1/`.

### For lane B / I: production candidate 9124348d

**9124348d** applies flags-first admission to the demand-range production
candidate. It passes an empty *proposal* law list to initial member seeding;
the actual law family, model-driven field instantiation, independence
filters, kernel checker, and every budget are unchanged. The helper's
explicit field-bridge behavior and existing tests remain intact. A new
regression checks flags-only seeding and preservation of learned tuples.

Do not call it validated yet. Five guarded jobs are registered as
**20261110-015518-rcbski**, task
`f151cb88-2215-4e96-bdee-55837243e46e`, output
`runs/mldr-incl-flags-first-v1/`: source/focused tests, original MLDR x3, and
fresh generated conditional checks with separate-process replay at **both**
2700 and 6000. It reuses the frozen base and prior tiny overlays; no new
whole-tree archive, no subagents, no deletions. No 29/29 or gate-green claim.

Broader coverage is also queued: the unchanged official quick-suite roster
(`scripts/test-shards.ts`) in all eight supported shards, batch
**20261110-015717-9fubkz**, task
`7576ff0b-3b7f-4799-9603-c42008b3cf5b`, output
`runs/mldr-incl-flags-quick-suite-v1/`. Each shard checks the same hash-bound
9124348d source first; class gate, pinned large VMs. This is not a substitute
for the 29x3 baseline pair, DuoAI, broken variants, bar, or lane D gate.

For lane B: your measured eager-member p1 regression remains valid; this
proposal removes the eager scalar-field part rather than promoting that
variant. No p1/Inv1758/Inv* gain is claimed from the safety measurement.


## ac7eacfe validated: conditional safety restored; originals remain UNKNOWN

Completed **20261110-014532-stsqg4**, all five rows exit 0. The production
repair **ac7eacfe** passes type/lint and **87 tests / 295 assertions**
(80 core, 4 lossless-capture, 3 provenance tests). The subsequent research
ranking installer is a separate, still-running test and is not included.

Fresh generation makes 34 laws with zero proof queries. Its machine and
ordered law array equal the prior exact family. At 6000, conditional safety
checks at **3817.24253 units**, the same restored cost as both range-off
controls. START and STEP both pass fresh kernel replay; the used witnesses
and 18 raw-premise indices are identical. Complete archive SHA-256:
`31b639ff1186c76b2da1c3ae81cd4e81bba6902cabe9522998e7bb7c5d67e01d`.
At 2700 it remains UNKNOWN at **2701.245368 units**. The 6000 probe's wall
is **8.762 s** on a Ryzen 9950X; this is not a 7 s wall pass.

All three unchanged original `run.ts --only mldr --ms 60000 --skip broken`
commands remain **UNKNOWN**, `why: time (rule result)`, at harness times
**59.001 / 59.358 / 59.001 s**. R1/R2 use Ryzen 9950X; R3 uses EPYC 4585PX,
all alone on large VMs with eight pinned vCPUs. No cross-CPU speedup claim.
Receipts, hashes, exact rows, CPU labels and compressed logs:
`runs/mldr-incl-demand-range-v1/`. This repairs a measured conditional
regression; it is **not 29/29, not an unconditional MLDR proof, and not GATE
GREEN**. Full nonregression and lane D's final gate remain outstanding.

### Current next experiment — no production change

Research **5c3686f0** tests the falsifiable hypothesis that lower-ranked
early field-law tuples consume the missing safety share. Seven parallel
jobs compare unchanged control with top 0/1/2/3/4/6 source laws, preserving
all flag premises, admission limits, 2700/6000 allowances, and the kernel.
This isolates ranking on the prior exact family with initial ranges off;
any winner still needs a production-candidate measurement and full gates.

Registered **20261110-014758-a6x9cy**, task
`8b23c143-90b0-4846-8b18-d72b4bfc14b3`, output
`runs/mldr-incl-member-rank-v1/`. Each modified disposable checkout must
pass type/lint and installer/provenance tests before its proof queries.
One waiter, no subagents, no new whole-tree archive, no files deleted.


## Confirmed eager-range regression; demand-driven integration under validation

Completed `20261110-014116-r49824`, six rows, all exit 0. The exact fresh
34-law family equals the prior machine **and** law array (canonical object
key order; array order preserved). Family SHA-256:
`ad1f3875ea61c34145adfaec3e015311bb096c5f5d69deb98b9e7ad9c0fc0d2f`.
The new diagnostic source check and all 3 provenance tests / 8 assertions pass.

On the same VM in each order:

| order | eager initial ranges | only initial ranges disabled |
|---|---|---|
| control, off | UNKNOWN, 6000.223364 units | checked, 3817.24253 units |
| off, control | UNKNOWN, 6000.223364 units | checked, 3817.24253 units |

These are **conditional** safety results: generated helpers are assumed,
not established by these calls. Both START and STEP are reconstructed and
accepted by the unchanged kernel. Both off runs have the same complete
4-file proof archive hash
`d508fcac4940e3a73c7c775afa9a52da875887a744746a5aab3e72c61a3c46e0`.
The STEP tree actually uses `member$4` and `member$5`: the `inS[0]` count
included in `inX$canVote$1[64*i + key$4#]` and `[64*i + key$5]`, plus
`w$274`, the `inX$row[i] <= inX[0]` inclusion. Eighteen of 73 raw source
premises are used, indices
`0,1,2,3,4,5,7,8,9,22,23,29,30,44,56,60,61,72`.

Do **not** infer a wall pass from this: the off runs take 13.825 and 23.411 s
on separately labelled EPYC 4585PX / Ryzen 9950X VMs. Within each row the
arms share a VM; no cross-CPU timing improvement is claimed. The restored
3817 units also remain above the original approximately 2700-unit share.

Targeted completion is not promoted: eager 2700/6000 probes stay UNKNOWN
(2706.343646 / 6037.742162 units); disabling ranges gives a checked
3974.8476248-unit certificate, worse counted work than 3817.24253.
Its smaller 26-instance final certificate is not evidence of faster search.
Exact rows, CPU labels, compact JSON, and lossless compressed logs:
`runs/mldr-incl-range-regression-v1/`.

### For lane B / I

**ac7eacfe** ports B/Fable's validated demand-driven range selector (B's
47215336 source) while preserving E's member admissions and both
independence-filtered MBQI paths. No protocol branch, kernel edit, hand law,
budget increase, or unconditional dropping of range facts. Demand persists
per goal and is triggered only by a known 0/1 count above a valued bound.

Submission record (completed above): five source-check-guarded jobs
were registered as `20261110-014532-stsqg4`, task
`6d94b6ed-c01f-4ca9-8617-876fed697db3`, output
`runs/mldr-incl-demand-range-v1/`: type/lint and focused tests, original
MLDR x3 unchanged at 60000, and fresh generated conditional/replay.
The frozen 84a7a672 base is reused with 8e7e8630's two preflight fixes and a
108 KiB, before/after-hash-checked overlay. Script and exact commands are
in `research/mldr-incl/{apply-demand-overlay.sh,demand-range-validation-jobs.json}`.
No new whole-tree archive, no deletions, no subagents. There is no 29/29 or
GATE GREEN claim; lane D's full gate is still required before merge.


## Executed results — 8e7e8630 source, not GATE GREEN

`20261110-012704-cgh7wh` is complete. Exact source is the frozen 84a7a672
base plus the two hash-verified, research-only preflight fixes in 8e7e8630.
**Typecheck/lint pass; 82 focused tests / 280 assertions pass** (78/270 in
8 core files, 4/10 in the lossless capture tests). New 3af3d9ad regression
tooling is not covered by that claim; its check is running separately.

The three unchanged original commands all return **UNKNOWN**, `why: time
(rule result)`, with harness-reported times **59.029 / 59.092 / 59.002 s**.
All ran alone on large VMs with eight pinned vCPUs. R1/R2 used Ryzen 9 9950X;
R3 used EPYC 9455, so no cross-CPU performance comparison is claimed.

The fresh generated family has **34 laws, no hand law, zero generation
proof queries**. Conditional safety (helpers assumed) remains UNKNOWN:
- 2700 allowance: **2700.128934 units**, 6 MBQI rounds, 987 hypotheses.
- 6000 allowance: **6000.223364 units**, 9 rounds, 1994 hypotheses.
There is **no new certificate to replay**. The lossless archive correctly
contains only `family-source.json`, SHA-256
`3c43d9ef808ca58e11764d0ab41b43c4cab10194a0e7551842f66befd9558199`.

The historical cancelled-command diagnostic reached both conditional
probes, then failed at the confirmed **invalid 300000-byte pack limit**.
The earlier shell-quoting hypothesis was not demonstrated by that run.
Its hard-coded 36a278e9 label is historical, not its actual source identity;
use the verified source header/overlay and receipts instead.

Compact parsed results, exact rows/CPU labels and necessary compressed logs:
`runs/mldr-incl-resume-preflight-fixed-v1/`. No full suite/gate, original
MLDR proof, or 29/29 is claimed.

### For lane B / I: safety integration regression under investigation

The paused pre-range E source reported a checked conditional certificate
at 3817.24253 units. The present range-integrated source is UNKNOWN at 6000.
This is a **regression hypothesis**, not yet attributed: the exact fresh
and prior families must first be compared. Research commit **3af3d9ad**
adds that comparison, same-VM initial-range on/off in both orders, and the
corrected targeted-completion probes at unchanged 2700/6000 allowances.
It changes no production code. Active task:
`01d0b4ba-830f-4aa4-a730-c712b43219f5`, output
`runs/mldr-incl-range-regression-v1/`; six jobs, no new whole-tree archive.
All candidate certificates are freshly reconstructed/checked, and the
helpers remain assumed. The targeted allowance remains 48 total tuples.


## Latest completed preflight: TypeScript passes, installer lint repaired

The focused `f0eb7671` check completed: both overlay hashes verified and
`tsc -p .` passed. `oxlint` then rejected **four `no-useless-escape` errors**
in `research/mldr-incl/install-targeted-completion.ts:8`. Therefore the
focused tests still did not execute. Receipt:
`runs/mldr-incl-resume-typefix-check-v1/` (summary, CPU placement, compressed
necessary error log). This is not a proof result.

**`8e7e8630`** removes only those redundant double-quote escapes inside a
single-quoted installer string. The emitted code is unchanged; the
research-only experiment is still not enabled in production.

A new six-job guarded batch is submitted with the same frozen base and
only two small hash-checked replacement files (6.5 KB total payload, no
new tree archive): task `da84933a-c5b8-4201-984f-ae4940c2b139`, output
`runs/mldr-incl-resume-preflight-fixed-v1/`, source label
`8e7e863060d3b27582f605ce51411035997ea5dd`. Both old/new hashes are checked
before any source check. All proof commands remain behind `bun run check`.
The older five-job typefix batch has now completed unchanged: all five
exited 1 from `script "check"`, confirming no original or conditional proof
command ran. Its summary and CPU labels are retained in
`runs/mldr-incl-resume-typefix-proof-v1/`; the identical lint diagnostic is
already preserved with the focused check. No retry of that superseded
source was started. The corrected batch is registered as
`20261110-012704-cgh7wh`, tree `bff29a99a14c`, and remains in progress.


## First executed rerun: source check blocked; no proof query executed

Batch `20261110-004001-gs8s50` completed all six jobs. Each exited **2** at
`bun run check`, with the same `TS2345` at
`research/track-m/lane-f-frame-falsifier.ts:25`: `flatMap` inferred only the
`{index, condition}` branch and rejected `{index, error}`. The guard did its
job: **none of the original or conditional proof commands ran**. The
controller's exit 0 means collection completed, not that any job passed.
Receipts: `runs/mldr-incl-resume-frozen-v3/{summary.tsv,placement.json}`;
necessary error log retained compressed as `integrated-check.log.gz`.

Repair **`f0eb7671`** gives that research-only `flatMap` its explicit result
union; runtime behavior, all production code and all budgets are unchanged.
For lane F / I: this is a type-only repair to the imported falsifier, not a
frame-soundness change or a new certificate claim.

Submitted a focused rerun, task `b1dad863-97ea-448e-a0b0-6f8396391c87`, output
`runs/mldr-incl-resume-typefix-check-v1/`. It **reuses** the existing frozen
84a7a672 tree plus a 4.7 KB one-file overlay; no new whole-tree archive was
created. The overlay checks the old file SHA-256
`26316496c8359ab38d2ca9a1b43854fc3aa9566f5277489416ff439ac258a288` before
replacement and the new SHA-256
`80958a58c97c7c1316ec2654b79eaa72732949593080ba6998b9f61d4426d017`
afterwards. New proof experiments remain behind a passing source check.
To avoid serial scheduler delays, the five remaining original/replay jobs
are also queued with **their own** hash-checked overlay and `bun run check`
guard: task `fee9b63c-74e6-4e11-be56-51c066e54cf8`, output
`runs/mldr-incl-resume-typefix-proof-v1/`. They cannot execute a proof if
that source check fails. This reuses the same tree and tiny payload; no
whole-tree archive or duplicate integrated-check job was added.


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
