# ASTRA experiment results

Base: `7ba06d5f8f7009523007f4c35cf60c883ea11070` (current main at start).
Branch: `exp/egraph-astra-20261104`. Scope: `research/egraph/**` only.
No historical checkpoint, shared core, kernel, Lean source, gate or production
configuration was changed. No merge, push or publication is authorized here.

## Execution and retained failures

All worker jobs request **2 CPU / 4096 MiB / 600 seconds**. The scheduler reserves
30 seconds and records a 570-second worker limit. The first completed jobs below ran on
boat `bx_xqxvqagx`, type `large`, with reported allocation 2 vCPUs, host 8 vCPUs,
`exclusive: false`. Co-tenants were 1 for the probe and first two validations,
2 for the full split-hint validation, and 1 for the finishing run. CPU model is unreported (empty string), and
actual RAM enforcement is not supplied by the placement receipt. The 4096 MiB
number is a request, not a fabricated measurement.

| Batch | Snapshot | Result |
| --- | --- | --- |
| `20261104-083134-s90qj2` | `7d082784bac9` | Timing reservation stalled, no worker placement. Coordinator-directed SIGTERM to owned controller 94766; exit 130, PID absent, batch absent before replacement. |
| `20261104-084001-ocfip5` | `bafbaf418e05` | Untimed probe, worker exit 0, observed job duration 2.44 s. Real-list reverse/append lemma proven and checked, 3 cyclic nodes, no helper lemmas. |
| `20261104-084102-7kjc9p` | `bafbaf418e05` | Worker exit 1, 10 tests passed / 1 failed, observed 3.68 s. Both requested milestone tests passed; extra nested-congruence positive control failed. |
| `20261104-084207-ft19ss` | `bbad2bfbad71` | Worker exit 1, targeted 1 passed / 1 failed, observed 0.65 s. An intermediate equality as a proved node alone did not repair the nested-congruence control. |
| `20261104-084353-6jkaow` | `91123b5f90f5` | All 11 tests passed (43 assertions); worker exit 2 from subsequent full-project TypeScript check, observed 47.31 s. One local closure-narrowing error and missing optional vendor imports; see below. |
| `20261104-084557-ogajis` | `77d3ec59bc72` | Worker exit 0, observed 10.88 s. Targeted recursive test passed after the type fix, scoped TypeScript passed, lint reported 0 warnings / 0 errors, both measurement assertions passed. |

These are **untimed correctness receipts, not performance or speedup evidence**.
Controller exit 0 is not success: the failed worker results above came from
controllers that exited 0. Raw receipts remain in `runs/astra-egraph-*`; the
cancellation and failed control logs are also retained in `receipts/`.

### What the failed controls taught us

`kernel/kernel.ts`'s `sameKey` reads equality from the tree **path**, not arbitrary
hypothesis rows. The direct and bridge-only proposals failed with `sat` at the
untrusted search level; this is not a counterexample to the true congruence law.
The repair proposes bounded equality split hints through the existing `Tree`
language and proves **both branches**, including the branches denying each
suggested equality. A forged e-graph merge is never made into a premise.
The direct and bridge-only failures stay asserted in the final test rather than
being hidden, while the repaired path and forged-merge control are checked.

## Static-check scope

The full-project TypeScript attempt is retained as **failed**, not relabeled as
a pass. It exposed one local test error (`v.node` lost its narrowing inside a
callback), repaired by capturing a checked `const root`. Other reported errors
come from unresolved `vendor/gdp-ts` and `vendor/handwired` imports in unrelated
research modules and the resulting implicit-any diagnostics. `git submodule status`
confirmed both vendor submodules are uninitialized in this worktree. No vendor checkout
or other worktree was changed to force a pass. The experiment now has its own
`tsconfig.json`, extending the unchanged root strict settings and including all
experiment files and their transitive imports. This is a scoped check, not a
replacement for the repository gate.

## Final validation

**GO for the isolated synthetic experiment.** No gate, merge, or broader corpus claim.

- Full experiment suite: **11 passed / 0 failed / 43 assertions** in the
  split-hint validation run.
- After the type-only `const root` fix: recursive test rerun **1 passed / 0 failed /
  9 assertions**. `tsc -p research/egraph` passed with inherited strict settings.
- Type-aware scoped lint: **0 warnings / 0 errors**, 9 TypeScript files.
- `measure.ts` assertions passed; raw output: `receipts/final-measurements.log`.

| Synthetic obligation | Disabled baseline | Enabled result | Instances / uses | Matching units | Proof work units | Adapter traversal units |
| --- | --- | --- | --- | ---: | ---: | ---: |
| Vote implies proposal | unproved (`sat`) | kernel checked | 1 fact instance | 350 | 478.144 | 1 |
| Reverse/append at recursive tail | unproved (`sat`) | kernel checked | 1 match, 1 lemma use | 2763 | 212.488 | 2 |

The real-list lemma was independently proved and checked by induction first
(459373.6268 proof work units in the measurement process). No lemma was installed
as a new axiom. Units are the reported abstract matching operations and existing
prover cost model, not wall-time performance measurements.

Necessary-use controls: deleting the vote instance or recursive lemma use is
rejected at the node's goal; a nondecreasing lemma-use rank is rejected at descent.
Missing vote, wrong ballot, malformed lemma tree and forged equality merges are
refused. Repeated-variable inconsistency, uncorrelated multi-pattern matches,
negated/disjunctive equalities, unbound keys, work/node/wall caps, cyclic e-classes,
and result caps are exercised by the test suite.

Recorded certificate SHA-256 values from the measurement run:

- Vote: `a2d6249736779ae21a062b1d25984f44b1f2ae6c446a3f3747928d83c8ef60e8`
- Recursive tail: `706ee62a4005d369356eb1b66bd3d35ac1569ce5ece8708758440847d8abe1f6`

No FEEDBACK full-gate pass or permission to merge is implied.

## Commit hygiene and cleanup

The exact prepared message passed `@commitlint/cli@19.8.1` with the explicit
conventional-header rules in `receipts/commitlint-rules.txt`: **0 problems,
0 warnings**. The first invocation used `--edit` and failed because the remote
snapshot intentionally has no `.git`; it is retained in
`receipts/commitlint-setup-failure.log`. Feeding the same message file on stdin
validated it successfully; no rule was disabled to obtain the pass.

- Setup failure: batch `20261104-084647-bpkmib`, tree `8f5491355eca`, worker
  exit 1, observed 1.14 s.
- Message validation: batch `20261104-084744-neni7f`, tree `f12d4ee00c71`, worker
  exit 0, observed 1.19 s; raw log `receipts/commitlint.log`.
- Both used the same requested limits and `bx_xqxvqagx` placement as above,
  nonexclusive, 2 allocated vCPUs on an 8-vCPU host with 1 co-tenant.
- All owned controllers terminated; no shared VM or scheduler configuration was
  changed. The only cancelled job was the original unstarted timing reservation.

## Historical follow-up

The separate historical comparison is recorded in [`historical/RESULTS.md`](historical/RESULTS.md).
It does not rewrite the synthetic acceptance or receipts below: the real TIP
`prod/lemma_09` now has a cold-replayed proof, while neither real M2 Paxos
obligation flips and native/full-gate acceptance remains pending.

## Limits

**CORE follow-up clarification for `cfa11fc7`:** the cooperative prover cap can
overshoot on rejected probes. Passing the budget controls above does not
establish a hard whole-call 5-second bound or hard CPU/RAM guarantees. The
adapter deadline and prover work cap are cooperative; the matcher's explicit
fuel and node/result caps are separate. Requested CPU/RAM, configured job
timeouts, and observed placements remain exactly as recorded, but must not be
promoted to hard whole-call resource-enforcement claims. This is a docs-only
qualification of the earlier budget wording: no code, original receipt, test
count, or synthetic-only acceptance scope is changed.

This measures synthetic clause instantiation and the use of a genuine inductively
proved reverse/append lemma at a recursive list tail. It does not measure the
historical Q3 fixture, the TIP corpus, or a full reverse-of-reverse theorem.
The baselines disable the candidate instance/use; they are ablations, not a
comparison against all production proof-search strategies.

The matcher is a finite first-order congruence/multi-pattern experiment, not a
production equality-saturation engine. Split hints in the extra congruence test
are explicitly supplied; automatic explanation extraction is future work.
No bounded execution samples are promoted to unbounded proofs. No Lean replay
has been claimed: all acceptance here is by the existing TypeScript kernel.
