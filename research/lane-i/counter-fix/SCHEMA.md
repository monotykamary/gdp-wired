# raw-work-v1 (provisional, NOT calibrated W)

Append six columns to all 20 v0 names, in order: `tinyNodes`, `tinyTerms`,
`reachStates`, `reachEdges`, `reachEvals`, `reachCompiledEvals`. Values are
monotone nonnegative integers. Full-mode vectors require all 14 extra weights,
finite and strictly positive; the old eight-weight vector is explicitly refused.
The 12 historical fixed coefficients are unchanged. Provisional priors: the two
reach-eval columns 0.02; every other extra column 1. D must fit/bind successors.
Correlated columns are observable but weights need not be uniquely identifiable.

- tinyNodes: admitted state/request assignment and seed-model node entries,
  exactly the three sites that increment native TinyFiniteStatistics.nodes.
- tinyTerms: each explicit tiny compiler/walker checkpoint; each executed
  generated predicate AST node, emitted interval/term binding and block entry.
  Short-circuited nodes do NOT charge. Instrumentation is excluded from the
  existing native code-size limit, so it cannot change a screen's support.
- reachStates: initial/admitted new BFS states; sampled Houdini state visits,
  and tiny independent candidate-certification state visits. Repeated visits
  remain work and charge again. It is not a global unique-state cardinality.
- reachEdges: attempted transition invocations including refused/no-op edges.
- reachEvals: actual interpreted or closure expression/condition-node visits
  inside a synchronous reachability scope (including finite law evaluation).
- reachCompiledEvals: fastStep's existing static step/assumption/least AST-node
  charge per invocation. NOT an estimate of actual predicate visits. Derived
  count loops retain their separately observed ticks. Predicate compileC uses
  reachEvals, not this column. Scope selection is exclusive, never subtraction.

No new scope mints budget. Per-primitive admission happens before charge. Tiny
native code is closed, straight-line, callback-free except its lexical tick:
its number of tick sites bounds execution. When the entire bound fits, the
block uses a finite local tick credit; unused credit is discarded, not charged.
Otherwise each site admits separately. Refusal latches at that endpoint so
catch-all callers cannot ignore it; same-end nested scopes inherit the refusal,
a strictly smaller child cannot poison a larger parent, and root exit restores.

The historical 1024-unit slack is a v0/provisional-profile census result, NOT a
uniform bound for arbitrary fitted coefficients. New columns introduce zero
integer-model overshoot (floating arithmetic subject to checked tolerance).
Existing legacy/cooperative primitive quanta must be rechecked under D's fitted
vector; a conservative scale is 1024*max(1, max fitted v0-extra coefficient),
not automatically 1024. A final 29-case confirmation must measure actual slack
under the fitted profile before a 'within W' acceptance. No claim is made here
that the preliminary weights or the v0 slack are calibrated guarantees.

Flags off: all six columns stay zero and all old eval charges remain in evals.
The additive raw schema itself has six new zero fields; compatibility audits
compare the exact old 20-field projection and assert all new fields zero.
Provenance and independent wall telemetry are excluded exactly as in v0 audit.
Trusted checking and Lean files remain exact; only untrusted cancellation
header functions in kernel/prove.ts change.
