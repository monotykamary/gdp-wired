# I2 insertion inventory — design only

No I2 counters or new weights are active. Basis: Section 18 and the current
b11-based source, with I1 drafts isolated in their own Git trees.

## Falsifiable target

Sampling, finite evaluation, cube testing and instance/goal construction must
produce nonzero raw counts wherever they perform work. On a qualified reference
host, the eventual weighted ledger must meet Section 18's k=3 band; a silent
or out-of-band phase is a missing/duplicated operation, not grounds for a
phase-name coefficient or a larger W. Lane D chooses the weights and W.

## Source boundaries to inspect before editing

- `core/machine.ts`: `evalE` at 380 and `evalC` at 511; `compileE` at 530,
  `compileC` at 554, `compileJsMode` at 872 and the fast-step wrapper near 1058.
  Interpreter evaluation counts actual visited nodes, including failed work.
  The compiled path needs its own documented per-call static-node cost;
  wrapping both the whole expression and all child closures would double-charge.
  Generated standalone source and public call signatures must not change.
- `core/exists.ts`: `small` at 139, `smallOf` at 240, `trueSmall` at 256,
  `holdsAt` at 278. Existing state, walk and step caps remain. Identify whether
  each path uses the interpreter or a compiled closure before charging it.
- `core/finite-houdini.ts`: charge each finite-prefix tick and the binding
  visits of `finiteEvaluator`, not only accepted laws or successful evaluations.
  `core/finite-model.ts` calls that evaluator; avoid charging the same visit a
  second time at the wrapper.
- `core/count-support.ts`: `candidateWork` at 111 (65,536 local cap), then
  `grammarPool`, `smallSelection`, `polaritySelection`, instance reification.
  The local cap stays policy; each actual tick also goes to the raw shared meter.
- `core/infer.ts` and `core/count-cubes.ts`: one `cubeTests` increment per actual
  (candidate, state) test; fold private used counters without counting output
  size as a substitute for failed/partial work.
- `kernel/kernel.ts`: substitution and obligation construction for `astNodes`.
  Charge produced nodes at construction, not by repeatedly walking a returned
  subtree. Reused nodes are not newly produced nodes.
- `kernel/cdcl.ts` and `kernel/epr.ts`: preserve existing raw counters and add
  them to the eventual model only with Lane D's explicit frozen weight vector.

## I3 contract to coordinate with Lane A

Use Lane A's `traceNow` for diagnostic time; never add a wall read to a search
control decision. A phase event records raw start/end deltas and wall duration.
State whether nested phase deltas are inclusive. The root total is a single
start/end delta, not a sum that double-counts children. Trace-on/off must preserve
verdicts and raw counts. Phase-exit checks alone do not implement F3: a truly
silent blocking loop needs an observer that can report it while it is running,
with a meaningful main-thread stack. Do not claim F3 from an ordinary timer that
cannot fire during synchronous work.

## Checks before use

- Erasure/shape checks and original-model 29-family census for construction.
- Targeted interpreter/compiled-path parity checks, including failed branches.
- Preserve all existing deterministic caps, refusal behavior and goal bodies.
- Phase-ledger measurement on mldr, B's conditional strategy and E's conditional
  Inv1758 path, with their P* research boundary explicit.
- D1 approval before kernel-counter budgeting; no provisional weight or W is a
  final calibrated value. F2, F4 and F5 belong to the coordinated full pipeline.
