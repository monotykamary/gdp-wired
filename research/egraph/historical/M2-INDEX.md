# Active M2 index investigation

This is a new research-only continuation from `98c7071a9afcb47ba391a9230dc9b6129270f3ff`
on `exp/egraph-m2-index-astra-20261104`. The original branch and frozen historical
TIP, baseline, failure and replay receipts remain unchanged. No core/kernel,
solver, production configuration or public API changes are made.

## Fixed acceptance and exact inputs

Both saved complete six-law contexts retain all hypotheses. No count/model
fixture result is substituted for these obligations:

| Obligation | Hypotheses | SHA256 of exact failure goal |
|---|---:|---|
| one-value-decided @step | 202 | `58496db30029729c33954d6cc01f61673dbe5bc0c52c4f64b1b4126c0dcc20ca` |
| P3 decision has quorum @step | 76 | `a7cee3dd679c5c19df5fd6110c24a723158e8644299c98243df8c0513bd57357` |

Compressed input SHA256 values are respectively
`c5eac7b02e6ab460d9d9e3864ad7d2a667ec583f7fb6478da7abcb75a71c7bc1` and
`6aac4db7a1f149f51ce8356e9f4f475474c583e36d7d44c69a4e7ba973411bba`.

Every comparison keeps **100,000 matching units / 512 stored graph nodes /
1,000 ms cooperative matching ceiling / 32 maximum matches**. Jobs request
2 CPU / 4096 MiB / 600 s, one active per lane. Shared-runner durations are not
speedup evidence. Neither cooperative limits nor placement labels establish
hard CPU/RAM enforcement. Every runner hashes sources/inputs before and after.

Versions 1–9 are candidate/provenance experiments. **Version 10 closes P3 @step
with an unchanged-kernel, cold-replayed counted proof**; see `P3-STEP.md`. Version 19 also closes the original
safety @step with a cold-checked certificate (`SAFETY-STEP.md`). Full M2/native
acceptance remains a separate, unclaimed gate. The historical
25-second prover ceiling is unchanged. Proof-search runners from v10 onward invoke it;
index/reconstruction runners do not.

## v1 — metered hash-consing

Batch `20261104-122320-wm0o4m`, uploaded tree `582f429b322b`, worker exit 0.
**21 tests / 138 assertions passed.** Original full scanning exhausts all 100,000
units in insertion. Signature indexing reaches the separate 512-node limit at
25,629 units (safety) / 15,776 (P3), with no complete seed or rebuild.

`IndexedEGraph` replaces linear insertion scans and pairwise rebuilds with
metered signatures and fixed-point passes, plus head/class matching indexes.
The existing matcher remains unchanged. `IteEGraph` defaults to that matcher;
an optional backend factory makes the comparison explicit.

## v2 — direct structural ITE/guard nodes

Batch `20261104-122457-t86ca1`, uploaded tree `b5e03f911ec1`, **worker exit 1**.
**9 tests / 105 assertions passed**, and both scoped TypeScript checks passed.
Lint then rejected an unenumerated switch default; that failure is retained.
The exhaustive-switch correction was validated in v3.

Native ITEs retain explicit guard/then/else children; guard operators and ordered
children remain structural, not simplified. No opaque subtree hides descendants.
All stored children, traversal and fixed-point work are charged. Direct versus
encoded bindings, guard/branch distinctions, guard-binding refusal and caps are
tested. Native mode still hits 512 nodes: 16,548 units (safety), 12,803 (P3), before
any rebuild. This does not establish a faster or successful proof.

## v3 — early positive-equality scheduling

Batch `20261104-122624-t8853w`, uploaded tree `4ea5cdc329af`, worker exit 0.
**6 tests / 33 assertions**, both scoped TypeScript checks and lint passed.
Only existing top-level/conjunctive positive equalities may run early; negative,
disjunctive and ITE-guard equalities never become assumptions.

Early scheduling performs two merges and two rebuild passes, but does not improve
the node boundary: **163/202** complete hypotheses for safety and **73/76** for P3.
Deferred/early units are 16,548/16,827 and 12,803/12,955 respectively. Both remain
incomplete seeds, not proofs. The extra work is retained rather than called a gain.

## Head-directed materialization design (tested in v4)

The P2 trigger is extracted from each input's actual original `P2 vote proposed`
law, including its exact quantified keys. Scan every condition/expression of the
full context, but store only selected read subtrees and **all asserted positive-
equality endpoint subtrees**. Every stored descendant remains an ordinary node
under the same 512-node cap. Unsupported syntax anywhere and incomplete/fuel-
exhausted scans refuse matching. No hypotheses are removed from a proof goal.

This tests index materialization, not a selected easy theorem or a new model.
It may produce candidates but cannot itself establish counted-certificate/M2
acceptance. Focused differential closure, negative-premise, full-scan and stored-
child/node-cap tests accompany the exact full-input comparison.

## v4 — complete scans and candidate generation within caps

Batch `20261104-122812-4tx1bg`, uploaded tree `d0ee0d23e504`, worker exit 0.
**4 tests / 18 assertions**, both scoped TypeScript checks and lint passed.
Full materialization still exhausts 512 nodes; head-directed materialization
scans **202/202** and **76/76** original hypotheses. All positive-equality
endpoints (two each) are included. It stores 289/90 nodes and returns 32/29 P2
candidates at 17,603/7,261 matching units. Safety reaches the 32-result cap.
These are candidate results, not kernel-accepted M2 certificates.

## v5 — candidate usefulness and missing provenance

Batch `20261104-123046-1dl5oz`, uploaded tree `58b85b5c4fdf`, worker exit 0;
scoped TypeScript and lint passed. Existing kernel `assumed` supplies the exact
P2 instance rows; canonical-key construction charges all traversed children.
Total match-plus-audit work is 43,308/18,910 units.

- Safety: 22/32 candidates duplicate exact existing positive assumptions;
  the saved failing attempt has **no witness**.
- P3: 6/29 duplicate existing assumptions; the saved witness satisfies all
  original rows **and all 29 candidate rows**. No model refutation occurs.
- Neither failed attempt retains `proof.instances` or count-certificate choices.
  Empty-instance `countedObligations` reconstructs an 11-hypothesis base, not the
  202/76-hypothesis saved failure. Missing choices are not guessed or replaced
  by new assumptions. No prover ran, and no checked certificate is claimed.

The next experiment uses the actual focus law's read patterns covering all its
quantified keys. A metered novelty predicate can reject exact duplicates before
consuming the unchanged 32-result cap. Enabled/ablated variants retain identical
full inputs and 100k/512/1s limits; this is a search-policy test, not a repair of
missing counted-certificate provenance.

## v6 — novelty-aware focus-law matching

Batch `20261104-123245-xzyeeu`, uploaded tree `2056437d155e`, worker exit 0.
**6 tests / 22 assertions**, both scoped TypeScript checks and lint passed.
Both modes use the same actual focus-law read patterns and full frozen inputs.
All pattern extraction, row-key traversal and predicate work is charged.

- Safety uses both Decision-read patterns for all four original quantified keys.
  Unfiltered: 32 results, including 12 duplicates, 39,419 units. Novel-only:
  36 bindings examined, 12 duplicates rejected, **24 novel results**, 40,199
  units, 23 stored nodes. Four extra novel candidates are exposed without
  raising the output or work cap.
- P3 uses its actual Decision-read pattern. Three bindings include two exact
  duplicates. Novel-only returns one, at 13,922 units and 15 nodes. The saved
  state still satisfies it. No model refutation or M2 certificate follows.

The next reconstruction diagnostic performs metered structural unification of
only existing positive law rows, then requires canonical structural equality
with the unchanged kernel's `assumed` output. It compares the resulting counted
base with every original row; count/flag gaps are reported, not silently filled.
This is provenance recovery, not generation of new assumptions or a substitute
for complete checked count certificates.

## v7 — existing-row recovery and checkpoint validation

Batch `20261104-123522-lml150`, uploaded tree `4e44ecc280bf`, worker exit 0.
Full research suite: **36 tests / 199 assertions passed**. Both scoped TypeScript
checks, type-aware lint over 35 files, and the pinned commitlint check passed.

Recovery identifies **89** existing quantified-law rows for safety and **17**
for P3. Each is regenerated by the unchanged kernel and compared by exact
canonical structure (not merely a matching head or text formatting).
The resulting counted bases contain **100/202** and **28/76** original rows,
with **zero additional unmatched rows**. Remaining gaps are 102 and 48 rows.
This is a strict subset, not a substitute for either frozen goal.

Metadata also locates 15/6 possible count-read declarations and 54/15 witness
names. These are candidates for reconstruction, not validated count certificates.
The next step is to parse the existing count-row shapes and require a round trip
through unchanged `mcGoal` before accepting any recovered metadata. No missing
row is to be guessed or silently omitted.

## v8–v11 — full provenance and P3 proof

- **v8**, batch `20261104-123847-zwbu7y`: exact P3 count-row round trips recover
  6 reads, 15 instances and 5 picks, reaching 54/76 rows with no extras. Safety
  reaches 100k work. Three tests / seven assertions and scoped checks pass.
- **v9**, batch `20261104-124244-1cbsf8`: actual kernel-generated quantified-flag
  templates recover P3's remaining 22 rows. All 76 rows match in order at 43,215
  units; safety reaches 100k only in final duplicate comparison. Five tests /
  twelve assertions and scoped checks pass.
- **v10**, batch `20261104-124537-4hblor`: direct count-bridge selection proves
  P3 @step. Ablated is `sat`; enabled passes `checkMC`, deletion control and fresh
  process verification. All original 76 rows and 15 instances remain, plus one
  existing count-schema instance. See `P3-STEP.md` for proof pin and limits.
- **v11**, batch `20261104-124809-foecdl`: reuse already generated row keys rather
  than rebuilding/serializing the same expansions twice. Safety is reconstructed
  exactly: 202 rows in order, 84,732 units, independent cold exact-goal check.
  Its base has 133 rows; metadata has 15 reads, 46 instances and 8 picks, including
  33 recovered flag rows. Three tests / nine assertions and scoped checks pass.

## v12 — actual safety attempt, no proof

Batch `20261104-125101-mxf9wp`, worker exit 0. Both original 202-row and
226-row (+24 focus-law instances) contexts return `unknown` at zero additional
case splits, exhausting the equal 2m work guard before the 25-second ceiling.
No tree or countermodel returned. Matching used 48,402 / 50,538 units. All
original rows/count metadata remain; scoped types/lint pass. This negative
result redirects the next probe to root search guidance, not more instances.

## v13 — adapter failure before proof search

Batch `20261104-125422-z8ilsp`, worker exit 1. The new guard extractor used
`eq` instead of the engine's `=` tag; its new test likewise used `lt` instead of
`<`. No safety proof search occurred. The other 43 tests passed. V14 corrects
these owned-adapter tags and adds positive-only guard extraction tests; it is
the same fixed-context, shared-budget split experiment, not a new solver claim.

## v14 — checked partial branch, safety still open

Batch `20261104-125543-c8mztn`, worker 0. Frozen `decides` selects action **4**;
the current phased fixture's action numbering is not used. Original-order control
is unknown at root. Guided run kernel-checks `op > 4` at about 5,318 work, then
exhausts the shared 2m guard in `op < 4` (89 splits deep); `op = 4` is unvisited.
This is a conditional branch proof only, not a complete safety proof. Four
guidance tests / 13 assertions, both scoped types and full research lint pass.

V15's next discriminator is a **permutation, not hypothesis removal**. The kernel
places the negated goal last in the counted base, then `mcGoal` appends count
rows. The prover's `openAt`/`nearOf` treat the last row as the goal, so they focus
a count lemma instead. V15 moves the original negated-goal row to the end of the
search view, preserves all 226 rows, and uses existing `widen` to remap any tree
back to the exact checked order inside the same shared budget. Both sides use
the same action cuts. The v14 conditional tree is cold-retained with exact goal,
path and source/input pins separately; **not imported by v15 proof search**.

## v15 — both non-decision branches checked; actual decision still open

Batch `20261104-125842-6fhhij`. Both variants have full 226-row root SHA256
`80130482e5f449904b040c5f3e36e4bc381bb0ad0924045c976cbaaa3106e345`.
The original-order control repeats v14. Conclusion-last permutation checks
`op > 4` and `op < 4` after remapping to original order, then exhausts the same
shared work guard in `op = 4` (262 splits deep). No complete proof/countermodel.
Exact conditional bundles are in `runs/astra-safety-order-v15/conditional/`;
no cross-run proof reuse. Runtime tests pass 3/8; worker exit 1 is a subsequent
test-only non-null-indexing TypeScript error, corrected for v16 verification.

The next direct package uses only existing source schemas: two old/new count
reads, `members - missing - votes` bridge, positive-vote witnesses instantiated
through P2, disjoint votes/blocked bounds, and P1/P5 at the two old decision keys
and request key. At most eight extra law tuples keep the total with the prior
24 at the fixed 32 cap. Six extra count instances preserve all original 46.
Every inequality remains a kernel-generated count lemma, never a supplied axiom.
The focused full context, exhaustive cuts, original-order remapping and shared
2m/25-second ceilings are unchanged. V16 performs the actual package ablation.

## v16 — direct decision package, preserved but not yet proved

Batch `20261104-130215-or5nex`, worker 0. Both baseline and augmented cases
remain unknown on `op = 4`; their non-decision branches check. The augmented
context has 242 rows, 32 total new law tuples, 52 count instances and 17 reads.
Its full root SHA256 is
`6c361c5022bd5cabfecb7c76aacf992e58459c992c6873c461a001145ce9d354`.
Four tests / 24 assertions, both scoped types and full research lint pass,
including the v15 test-only indexing correction. No complete proof or model.

V17 retains an explicit source/declaration/binding map for each v16 addition,
then holds that exact 242-row root fixed. It adds no hypotheses: four exhaustive
cuts select the arithmetic arms of the existing quorum bridge and disjoint
votes/blocked count lemmas. Each complementary branch remains an obligation,
with its existing lemma used only as search focus. All branches, remapping and
assembly remain inside the same shared work/wall guards. No conditional tree
from any previous run is imported.

## v17 — four count bounds checked, complete safety still unknown

Batch `20261104-130558-9wvmg5`. Both variants retain the exact v16 242-row root.
All four arithmetic-cut complementary branches check; the guided search still
exhausts the shared work guard at the decision case. Two tests / seven assertions,
both scoped types and full research lint pass. Worker exit 1 is solely the
subsequent commitlint invocation requiring a `.git` directory absent from the
upload, not a prover/test failure. V18 fixes that validation setup separately.

V16 provenance is retained in `recovery/safety-v16-provenance.json.gz`, SHA256
`775913b6637bd2f98bcf42751bf7eb09ccb0fb708709339893a5e5d7b6bccc30`.
It records the complete 242-row root and source pins, each of eight added law
tuples with its original law and bindings, all six new count instances with
read keys and original count declarations, and preservation of prior metadata.

The next route adds no instances or cuts: restore **native root search** on the
corrected conclusion-last view. Nonempty forced-cut paths bypass the prover's
root-level slicing/CDCL stages. V18 compares the existing protocol-pattern scope
off/on on the same 242 rows; native slicing must widen back to the full view,
then remapping/checkMC/cold verification must accept the original counted order.
The shared 2m/25-second guards remain around the entire search and remapping.

## v18 — non-exported API caught before search

Batch `20261104-130919-i743gu`, worker 1: `withPatterns` is internal, not an
export, so no proof search ran. Commitlint now succeeds after initialization
of the disposable uploaded workspace. V19 uses exported `withModels` only to
enter the same pattern scope: the model callback returns undefined, exactly
one query is required, and unchanged instance identity is checked. Tests
cover unknown results and interruption without refinement or retry. The
trusted engine remains unchanged.

## v19 — original safety step proved and cold checked

Batch `20261104-131040-wllibq`, worker 0: native root search on the focused
242-row context returns the same complete certificate in both wrapper modes,
at about 510,278 work units under each case's single 2m/25-second guards.
Original-order `checkMC`, fresh-process checking, and package-removal rejection
all pass. Two wrapper tests / five assertions, both scoped types, full research
lint and commitlint pass. See `SAFETY-STEP.md` for the proof and receipt pins.

## Remaining admission and audit work

1. Independent coordinator verification of the safety certificate and its scope.
2. V20 runtime audit is complete: actual scope off/on, empty paths and zero
   initial nodes observed; native root hooks confirm both entries. Both cases
   return the identical retained certificate and pass all proof controls.
   No import-cached environment setting was toggled.
3. Full M2/native admission remains separate. No merge or push is authorized.

Further candidate volume, additional cuts and provenance recapture are no longer
needed to obtain either of these two historical step certificates.

## Final checkpoint validation

V20 audit batch `20261104-131258-4sw8jr`, worker 0: both scoped TypeScript
checks, full research type-aware lint and commitlint pass. Integration batch
`20261104-131321-cmocea`, worker 0: **53 tests / 264 assertions**, all 17
research test files. These are research checks, not the full native gate.

## Retention

Raw logs, summaries, backend/placement records, and versioned source snapshots:
`runs/astra-m2-index-v1/`, `runs/astra-m2-compact-v2/`, and
`runs/astra-m2-equality-v3/`. The next receipt belongs separately to
`runs/astra-m2-trigger-v4/`. Earlier source snapshots and failures are never
replaced. No TIP proof rerun or native/full-frontier admission is claimed.
