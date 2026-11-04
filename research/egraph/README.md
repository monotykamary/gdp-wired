# ASTRA: bounded e-matching experiment

Status: isolated research, not integrated into production search. Based on main
`7ba06d5f8f7009523007f4c35cf60c883ea11070`. The direct engineering restart
supersedes the historical wait instruction only for this lane. It does not pass
FEEDBACK's full gate or authorize a merge.

## Hypotheses, before measurement

1. A correlated first-order trigger finds a vote-to-proposal clause instance
   needed by a synthetic obligation. No-instance baseline must fail and the
   enabled certificate must pass `kernel/cyclic.ts` unchanged.
2. A proved reverse/append lemma can be selected by e-matching and actually used
   in a synthetic recursive obligation. Removing the use must prevent acceptance;
   storing or matching an unused lemma does not count.
3. Congruence and multi-pattern matching remain untrusted: false merges, missing
   premises, mutated instances, and malformed certificates must not confer proof.

Go for further research only if both positive milestones and all negative controls
pass within fixed limits. Otherwise no-go, retaining failures. These are not
historical Q3 or TIP corpus results, a gate pass, or evidence for a merge. No
bounded evaluation is promoted to an unbounded theorem.

## Boundary

`match.ts` maintains finite e-classes, rebuilds congruence, and matches patterns
modulo equality. Only positive top-level conjunctive equalities are merged.
Ground terms under negation/disjunction may be indexed, but their equalities
are not assumed. Matching returns concrete substitutions, never a proof.
`if`, flags and quantified conditions are deliberately unsupported.

Nested read congruence needs equalities on the kernel tree path, not only rows
in its hypotheses. The adapter can try at most four explicit equality split
hints (4096 traversal operations): both branches are proven and checked, so a
hint is never an assumption. Direct and bridge-only failures are retained.
The synthetic congruence fixture supplies its two hints explicitly; automatic
extraction of general e-graph explanations is **not** implemented.

`certify.ts` submits ordinary fact instances and node uses to the existing goal
constructors, tree search, and final cyclic checker. No kernel source, certificate
language, trusted axiom, production configuration or export changes. A task's
explicit universal facts stay explicit premises of its certificate.

Every traversal, insertion scan, root lookup, congruence comparison, matching
attempt and join consumes local fuel. Node/result counts and wall limits bound
storage and work. Fuel exhaustion throws a non-success result; it never reports
saturation as proof. Adapter proof search receives its own existing full-work
limit minus consumed matching units. Matching units are conservative abstract
operations, **not** calibrated milliseconds. Kernel checking is included in
certificate wall time; recursive lemma preparation is reported separately. Both are contained by the remote job wall limit.

**Budget interpretation (CORE review clarification).** The prover work and
deadline limits above are cooperative, not hard whole-call resource guarantees. In
particular, the prover can overshoot its cap on probes that are ultimately
rejected. The adapter's 5-second deadline does not guarantee that the entire
call, including preparation and kernel checking, completes within 5 seconds.
The matcher's explicit fuel and node/result caps are distinct from that
cooperative prover budget. Likewise, the requested CPU/RAM and configured
remote-job timeout below are execution settings, not proof of hard whole-call
CPU, RAM, or elapsed-time enforcement. Read the earlier wall-limit wording with
this qualification; neither the recorded tests nor the placement receipts
establish such guarantees.

## Execution

All substantive runs use `supercomputer`, requested 2 CPU / 4096 MiB per job,
timeout at most 600 seconds. The initial submission-class timing reservation
stalled before execution and was cancelled through its owned controller at the
coordinator's direction (see `receipts/cancelled-first.json`). Correctness runs
use untimed interactive class. Placement receipts, not requested resources,
determine hardware labels; untimed wall durations are diagnostic only, not
performance or speedup evidence. No sweeps or resource increases. The first
job probes the existing recursive lemma prover; subsequent fixed validation runs
exercise executable assertions. No historical checkpoint is required or altered.

```
supercomputer run --jobs research/egraph/first.jobs.json \
  --out runs/astra-egraph-first-untimed --class interactive
supercomputer run --jobs research/egraph/validation.jobs.json \
  --out runs/astra-egraph-validation --class interactive
```

The TypeScript check is scoped to this experiment and its transitive imports;
the full-project attempt and missing optional vendor submodules are recorded,
not treated as a gate pass. See `RESULTS.md` for measured outcomes and retained
failures.
