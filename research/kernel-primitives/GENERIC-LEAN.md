# Generic concrete-word Lean export

## Verification status

**Native acceptance complete.** Generic library theorems and actual public
`toLean` machine certificates compiled from the shipped package with standard
axioms. This is ready for release review, not authorization to release. The
feature-branch GitHub receipt is recorded externally after the final commit.

## The generic argument, proved once

1. `WordReach.lean` defines `WordInterpret` pointwise at **every key**, and starts
   `WordSReach` from the concrete helper overlay. Ordinary maps retain their
   supplied values. Initialization, carried requests, point writes and every-key
   writes cannot modify reserved map IDs. Every transition is the source
   `SMachine` transition; forgetting provenance yields the unchanged `SReach`.
2. `WordFacts.lean` constructs the exact TypeScript fact AST from a descriptor.
   `ValueMatches` checks the environment-independent native dispatch, decoding
   operands from the right-associated tuple key. `interpret_sound` derives real
   getter equalities; it does not assume any generated clause.
3. `facts_sound` proves **all** clauses for arbitrary operand terms/environment:
   q/r/c bounds, every guarded convolution column, low-word carry zero, strict
   remainder lex order, non-strict quotient lex order, and divisor-one digits.
   Numeric arithmetic comes from `WordDivision`, `WordColumns`, `WordLex` and
   `WordOne`. High columns have a zero-padded input RHS; the incorrectly
   unpadded proposed wrapper was rejected and has a checked counterexample.
4. `WordSMachine.lean` retains every existing invariant/k-step structural guard.
   Original `checkIn` checks named-hypothesis membership and the original tree
   row order. Additional hypotheses come only from proved schemas. K-step
   frame targets must also be disjoint from the reserved namespace.
5. Public `toLean` exports its actual machine and retained certificates, then
   applies `concrete_smachine_sound` / `word_skstep_sound`. Readable laws assume
   `WordSReach`; step claims use `WordSKStepHolds`, never arbitrary-map reach.

The only axioms permitted by the audit are `propext`, `Classical.choice`, and
`Quot.sound`. No custom axioms, `sorry`, `native_decide`, or compiler-trust
axioms are used. This continuation changes **no TS kernel or prover code**.

## Independent integration review

A separate read-only Sol reviewer found two completeness/routing defects:

- Word reads confined to claims escaped detection. Detection now includes all
  options; direct cyclic exports also refuse intrinsic words, and the cyclic
  selector includes liveness. No unsupported bridge can fall back silently.
- An otherwise irrelevant word update could lose its map IDs after obligation
  minimization. Source getters and the complete q/r/c helper namespace are now
  allocated independently of which updates the proof uses.

Both have dedicated source regressions, including a claim-only native read and
an unused u64 computation. The reviewer did **not** claim to compile unfinished
facts. Earlier independent Terra approvals concerned the unchanged TS kernel /
prover diff; they are not misattributed as this Lean integration's approval.

## Scope and fail-closed boundaries

The generic bridge covers ordinary `SMachine` invariant laws, arbitrary ordinary
mutable/carried maps, flags, quantified keys, and one/k-step claims. It refuses
higher temporal, ghost, refinement, loop, history and sum bridges until they have
their own concrete-world simulations. Non-machine item kinds containing native
words also refuse. This is not a blanket frontend/lowering-equivalence theorem.

Actual DSL division fixtures retain their conditional failure-rollback updates.
The exported laws concern state-transition projections, not exception observables;
no runtime-exception or liveness claim is made. The ordinary wrap fixture carries
its real DSL `div$`/`mod$` function definitions and facts rather than treating a
hand-built opaque getter as arithmetic.

## Acceptance commands

`bash research/kernel-primitives/generic-packaged-gate.sh` requires a result
folder in `SUPERCOMPUTER_OUTPUT_DIR`. It checks the **already shipped** library,
then compiles public `toLean` output in a fresh directory populated solely from
`leanProject`. It audits every requested declaration against the exact generated
source and standard axioms. It separately repeats the unchanged prior 21-claim
wrap/helper gate. No checkout oleans or sibling source snapshots participate.

The generic gate covers all 32 q/r/c digits, actual DSL wrap/division, mixed
ordinary maps/flags, carried requests, quantified invariants, guarded u8
reconstruction, all eight u64 columns, one/k-step claims and claim-only reads.
Lean negative controls exhibit a false helper fact under arbitrary maps and
reject a carried-frame rename into a reserved helper ID. The CI workflow runs
this packaged gate independently of native differential probes.

## Final acceptance receipt

- Strict-once boat `20261117-204241-rpfl85`: native exit0, cleanup complete.
  **105/105 generic declarations**, 22 actual public fixtures, **55 readable
  invariant laws**, three one/k-step claims, all 32 helper digits, arithmetic
  reconstructions and both negative controls. The declaration count also
  includes grouped invariant/fact and generic checker theorems; it is not 105
  distinct user invariants.
- The **prior21/21 claims** recompiled separately in the same job. Their proof
  source and claim roster are unchanged; only stale audit scope wording was
  clarified to refer to the separate new generic gate.
- Each target compiled solely from its `leanProject` source dependency closure.
  Generic closure: 16 modules; 59 source modules are shipped, not all rebuilt.
  Standard axioms only, no native/compiler trust. Results:
  `/tmp/kp3-packaged2-results/generic-and-prior21-packaged.files/`.
- Strict-once static `20261117-204339-pt7gfa`: **44 tests / 1,648 assertions**
  pass across seven files, including ordinary exporters and the kernel-accepted
  u64 identity. Scoped types, type-aware lint, quick-suite roster, shipped
  library freshness, and shell syntax pass. Cleanup complete.
- The first full-package attempt rejected eight readable u64 corollaries due
  to missing argument parentheses around `ρ` applications in tuple surface
  terms. Correct tuple/projection (and adjacent min/max) grouping fixes it;
  no semantic rule or checker guard was weakened.
- Library arithmetic, reserved reachability, full facts and k-step checker each
  have independent native receipts, but only the shipped-package receipt above
  establishes the integrated result. GitHub feature-branch CI and final commit
  are recorded in `/tmp/kp3-CONTINUATION-FINAL.md` after push.
