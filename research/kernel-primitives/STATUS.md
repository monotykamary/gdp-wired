# Kernel primitives continuation — BLOCKED / DO NOT ADMIT / NO RELEASE

Continuation of checkpoint5f9bd81dd on the SAME `feat/kernel-primitives-checkpoint`
branch, based on6119535b7. No reader changes, main push/merge, history rewrite,
or release. The stopped rule-first and checkpointed lift streams stay stopped.

## Current result (2026-11-17)

- **u64 identity repaired and kernel-accepted.** The minimal captured leaf hit
  `-65536 * 281474976710656 = -2^64` at certificate step86. The checker correctly
  rejected unsafe arithmetic. A guarded `c_n=0` theorem plus untrusted,
  independently checked local carry cuts avoids that intermediate; safe-integer
  checks in `core/check.ts` are unchanged. See `U64-REPAIR.md`.
- Final native `20261117-185742-ovwts2`:255 runtime/fuzz tests and89
  soundness/theory regressions pass;46/46 semantic mutants killed;231,552
  C/Go/Rust/Python comparisons, zero mismatches. The accepted u64 law runs
  interpreter and compileJs boundary cases; a shifted false law is not PROVEN.
- **Performance:**60 warm samples/property/phase across three independent,
  exclusive9950X VMs,2/16 pinned vCPUs,0 co-tenants. Median paired VM changes:
  spent bound -8.37%, wrapping lap -3.01%, rollback -3.67%. Spread remains large;
  no claim that every VM/sample improved. Removed irrelevant legacy scans using
  an untrusted hint and negative-only memo. Full per-VM data in `U64-REPAIR.md`.
- **Trusted kernel delta vs6119535b7:**347 lines added,5 removed (net342) in
  `kernel/kernel.ts`, `kernel/integer-primitives.ts`, `kernel/word-division.ts`.
  Prover/cut search, tests, Lean proofs and generated source strings excluded.
- Terra rounds8 and9 **APPROVE**, kernel/prover scope only. Round9 includes
  negative-only caching and shared outer proof budgets. No Lean/release approval.
- Actual `WordDivision.lean` semantics, all guarded columns, q/r/c bounds and
  `c_n=0` are universally Lean-proved at8/16/32/64. Native185805-3djdux green;
  no sorry/custom axioms/native_decide. Actual wrap and helper-digit Machine/Reach
  certificates pass a21-claim standard-axiom gate (191430-e8g52c).
- A public **restricted helper-digit** exporter supports q/r/c bounds at all
  widths and rejects auxiliary/unknown machine effects. It is NOT generic DSL
  overflow/division-machine export. The new proof modules are included in the
  generated leanLibrary; isolated installed-bundle recheck and public API tests
  have separate receipts, recorded in `/tmp/kp2-CONTINUATION-FINAL.md`.
- Scoped TypeScript/type-aware lint passed191202-opa9yp. Whole-tree boat check
  failed because the upload excludes vendor submodules; that log has no errors
  in core/kernel/lean-kernel/scripts. GitHub's normal recursive checkout must
  perform the real whole-tree check. One authorized GitHub CI round and exact
  final source SHA/URLs are recorded externally after the branch push in
  `/tmp/kp2-CONTINUATION-FINAL.md`, not inferred from native tests.

## Exact remaining release blocker

Generic `toLean` still fails closed for intrinsic `SMachine` laws. `SReach.start`
permits arbitrary initial values at undeclared reserved map indices. Its writes
and carries need not preserve them. Therefore deriving word facts for arbitrary
SReach maps is FALSE, even though the actual helper arithmetic is proved.

Needed: a concrete `WordSReach`/word-map overlay simulation and reserved-index
preservation theorem (or verified immutable-fn lowering with tuple-key
isomorphism), followed by checkInWithFacts soundness at all sStartGoal/sStepGoal/
sKGoal framed views. Discharge every generated fact; do not assume it. Full
actual signed/mode frontend-lowering equivalence is not claimed. Scalar
`Kern.Reach` fixes maps; its restricted checked exporter is sound but does not
remove this blocker. **Do not mark READY FOR RELEASE REVIEW.**

## Custody qualification

The first timing helper exited before collecting its four successful jobs.
Immutable batch fetch recovered all four exit0 rows without rerun. That old
non-strict batch182645-k3p3b2 has no local custody journal; recover-close refused.
Missing strict-close evidence is NOT reported as cleanup_complete. Later main
native admissions use strict-once/max-attempts1. See final external receipt.

---

## Archived original checkpoint (historical, not current continuation status)

# Kernel primitives — CHECKPOINT / NOT COMPLETE / DO NOT ADMIT / NO RELEASE

Base: `6119535b7` (origin/main when assigned). Worktree: `/tmp/gdp-kernel-primitives`.
Checkpoint branch: `feat/kernel-primitives-checkpoint`. Original WIP history is
preserved unchanged on `feat/kernel-primitives` at `38c28a2cf2326a703ff3fa2ef7ade02619616132`.
A fresh branch was necessary to produce a linted checkpoint without rewriting
historical WIP subjects. No reset, amend, rebase, main merge or push. No reader
changes; stopped rule-first and checkpointed symbolic-lift work remain untouched.

## Implemented, with limited admission

- Signed/unsigned 8/16/32/64-bit DSL words, explicit WRAP/SATURATE/TRAP, exact
  add/sub/mul/neg and FLOOR/TRUNCATING/EUCLIDEAN div/rem. No floating-point types.
  A 64-bit literal must be bigint or a decimal string, not a Number.
- Zero division fails the step. Signed MIN/-1 TRAP fails both division and
  remainder. Runtime failures occur before writes; kernel obligations retain a
  stuttering failure branch instead of assuming failures impossible.
- Exact BigInt concrete evaluator/receipts; compact shared unsigned-magnitude
  division helpers, guarded convolution/range facts, parser/scope checks against
  shadowing and malformed calls. Interpreter and compileJs share the helper.
- Trusted implementation delta: 332 added lines, 4 removed (net328):
  `kernel/integer-primitives.ts`151, `kernel/word-division.ts`145,
  `kernel/kernel.ts`36 additions/4 removals. `kernel/prove.ts`12 new lines are
  UNTRUSTED search ordering, not arithmetic rules. Tests/mutants/Lean are excluded.
- Root search tries existing bounded plain proof search before finite preflight
  for compact words; accepts only a tree, never a relaxed model. The kernel still
  checks it. Facts stay BEFORE the final negated conclusion. Step-law then/when
  scopes now include declared readonly functions, as ordinary laws already did.
- Public DSL verdicts now require `proven && checked`. A candidate rejected by
  the kernel becomes UNKNOWN with an explicit reason, not public PROVEN.

## Native and soundness evidence

- Boat `20261117-161459-18yel2`:57,888 generated cases PER C/Go/Rust/Python;
  231,552 comparisons, zero mismatches against the exact concrete kernel.
  Unsupported native policies use documented exact adapters, not direct language
  operators in every case. CI workflow added; GitHub CI has NOT been run.
- Boat `20261117-174016-8y20re`:46/46 discovered semantic mutants killed,
  zero survivors/equivalents; exhaustive65,536 u8 operand pairs satisfy every
  generated compact-theory clause. Invalid/out-of-domain inputs and name aliases
  are covered. Earlier regex-corrupted mutation results are INVALID, not counted.
- Final boat `20261117-175918-qbxv36`:252 fixed/runtime/fuzz tests PASS,
  286,655 assertions;88 regression/theory tests PASS,33,015 assertions. Scoped
  TypeScript and type-aware lint PASS. All five jobs closed/cleanup_complete.
  The earlier248-pass/3-timeout attempt is NOT a passing gate: three signed64
  literal tests hit Bun's default5s timeout, without a numeric mismatch. Their
  assertions are unchanged; an explicit30s per-test budget now passes.
- Independent `pi --provider openai --model gpt-6.1-terra`, with
  `env -u OPENAI_API_KEY`, reviewed kernel-only diffs. Rounds3–6 APPROVE after
  addressing accessor TOCTOU, omitted invalid-operand receipts, namespace/scope
  and fact-order issues. Round7 APPROVE on the actual final kernel/prover diff,
  explicitly NOT a completeness/Lean approval. See `INDEPENDENT-REVIEW.md`.

## Symbolic variable-divisor matrix (not sampled proofs)

20s watchdog, one job alone per VM. Different CPUs across jobs; these are not
cross-width performance comparisons. Boat `20261117-174557-bji70g`:

| unsigned width | q/r bounds | q*d+r=n word identity | r<d for d!=0 |
|---|---:|---:|---:|
|8|checked3.896s*|checked0.297s*|checked0.044s*|
|16|checked12.148s|checked0.117s|checked0.067s|
|32|checked12.335s|checked0.436s|checked0.238s|
|64|checked12.842s|UNKNOWN: kernel rejected candidate|checked0.189s|

*8-bit values are from boat `20261117-174016-8y20re` (5s budget);64-bit
values are from final boat `20261117-175918-qbxv36`. The final64-bit public
receipt has proven=false, checked=false, admitted=false, stuck=unknown,
why="kernel rejected the candidate proof". No false public PROVEN is emitted.
The64-bit identity is NOT admitted. It remains rejected with20s available, so
this is not merely a watchdog cutoff. A read-only solver helper traced it to
`checkStepLaws`/`check`; the failing goal/leaf has NOT been captured. Unsafe
certificate arithmetic or row mismatch are hypotheses, not established causes.
Do NOT assert that it is a floating-point bug. Raw normalized-limb bounds have
checked positive regressions at all four widths;8-bit additionally rejects
reusing a valid bound certificate for a false stronger bound.
The symbolic decision requirement is NOT complete; no complete signed/mode
symbolic proof matrix has been established.

## Lean evidence and remaining blockers

- Standard primitive definitions map to BitVec and Int.fdiv/tdiv/ediv families.
  A strict standard-axiom audit passed188 declarations. Actual-addCarry Nat
  reconstruction, bounded digits, modulo and direct BitVec-add wrap bridges
  compile. Universal actual-sub and actual-mul LOW-WRAP bridges also compile.
- These do NOT prove all signed overflow/division frontend lowering equivalent
  to those standard primitives. Full-machine compact-division Lean export
  explicitly REFUSES; it never silently assumes opaque function semantics.
- Complete the rejected64-bit word identity proof/check and the universal actual
  lowering/Lean-export bridge before admission. Standalone/closed equalities or
  native samples cannot substitute for those requirements.
- Primitive failures with history, counts, sums, ghosts or per-key writes are
  explicitly refused. These combinations are not implemented or claimed safe
  by an admission. No float support.

## Existing-proof timing (source replay disabled)

Final boat `20261117-175918-qbxv36`, three cached-pass medians (ms):

| existing Rust u8 Budget property | before | after | observed change |
|---|---:|---:|---:|
| spent bound |145.43|139.36|-4.2%|
| wrapping lap |70.31|95.26|+35.5%|
| failed-spend rollback |81.69|93.45|+14.4%|

These include material regressions; too few samples to characterize variance
or claim a speedup. Baseline copies ORIGINAL
`core/dsl.ts`, `core/machine.ts`, `kernel/kernel.ts`, `kernel/prove.ts` from6119535b7;
AFTER restores the final versions in the same isolated VM/process sequence.
Three cached passes + cold pass on three properties of ONE existing Rust u8
Budget fixture. This is NOT a multi-project/type benchmark, a speedup guarantee,
or source PROVEN admission: kernel proofs check, source translation stays
unchecked because native source replay is disabled for this timing driver.

## Lifecycle

All final review/boat gates and pi sol helpers have completed; active owned
controllers/helpers=0. Removed only the owned temporary inputs:
`/tmp/kp-stage2-immutable`, `/tmp/kp-baseline-runtime`, `/tmp/kp-commitlint-inputs`,
`/tmp/kp-diag-input`. The snapshot was its own initialized gate-snapshot clone,
not shared worktree metadata. Results-only logs remain under
`/tmp/kp-stage*-results/`. All final boat jobs report cleanup_complete=true.
This legitimate delivery worktree remains. No shared VM was killed or other
lane worktree removed. The actual checkpoint message passed repository
commitlint on boat (`20261117-175210-cnja28`); historical WIP subjects remain.
No release, reader adoption, GitHub writes or source-PROVEN admissions.

Next technical work: capture the rejected64-bit step proof and locate the
first failing checker goal/leaf, fix the untrusted certificate path without
weakening the checker, then finish actual lowering/standard-Lean equivalence
and full export. Rerun conformance on semantic changes. This checkpoint is
NOT completion of the assigned six requirements.
