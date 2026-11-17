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
