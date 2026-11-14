# Slice 3 consumer addendum — multiple sorts and rigid reads

This is an addendum to `BAPA-CONSUMERS.md`, not a change to the frozen slice-1/2 implementation. No shared core/kernel/emitter file is changed by this work.

## Actual multi-sort control

`research/bapa/rigid-lower.test.ts` builds one machine with Node, Quorum and Value sizes, an immutable binary `member` function, and a native tuple-keyed `Votes` map. Two independent marked guards range over **70 Nodes** and **65 Values**. Membership is nonzero only at Nodes 17 and 35, so an old breakpoint sampler cannot stand in for exact finite evaluation. Whole laws additionally range over Node and Value; the Value failure is deliberately at 42 while the caller's sampling bound is 4.

| Consumer | Required behavior and coverage |
| --- | --- |
| `scope` / finite-marker validator | Accept both distinct marked sorts in the same machine and rigid function/native tuple reads in their bodies. Tested on the actual lowered/bound machine and both whole laws. |
| Interpreter / `evalC` | Exact guard evaluation in the bound runtime; Node failure before votes, success after both members vote; independent Value guard changes. |
| `compileC` | Both marked guards evaluated independently over the same bound immutable functions. |
| `loadJs` / generated runtime | Same state results as the interpreter before and after tuple-map updates. |
| `holdsAt` | Whole Node and Value laws use their own exact domains, not the caller's bound 4; false at Node 17 and Value 42. |
| `watch.start` | Same whole-law results, including rigid function and tuple reads; no sampling downgrade. |
| `fastStep`, `domainStep`, `requestQuotient` | Preserve deliberate unsupported/refusal result for the marked multi-sort machine. |
| `bmcFits`, `finiteEvaluator` | Preserve deliberate unsupported/refusal result, not a finite-completeness claim. |
| Other restricted consumers in the original census | Unchanged; their explicit marked-quantifier refusal/structural behavior is not replaced or bypassed. No new claim that these engines support the port. |

The source instance is JSON tables validated by exact enumeration. Binding accepts only the validator-issued immutable capability, freezes/copies the interpretation, captures immutable parameters once and never accepts replacement parameters at a step. Raw generic `interpret.init` does not enforce machine preconditions, so concrete execution uses the bound runtime rather than pretending that a `pre` equality alone prevents rebinding.

## Evidence

Batch `20261114-060236-uzr4jk`, fetched to `runs/bapa-rigid-minimal-06-fetch`, passed the expanded 20-test isolated suite (76 expectations), strict TypeScript and actual generated Lean/source-wrapper checking. The later capability-lookalike rejection and relevant unchanged legacy regressions are in the final-check job; consult `BAPA-SLICE3-LOWERING-RESULTS.md` for its terminal status.

These are foundation/consumer controls, not the original naive-consensus transition comparison or its ghost-map certificate.
