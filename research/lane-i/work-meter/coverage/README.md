# Supplemental raw coverage — draft, not promoted

The retained complete artifact does not modify `core/bitsets.ts`. Its two
loops implement finite candidate-state tests using native word operations;
they currently advance no raw counter. This is a concrete I2 coverage gap.

`bitsets.source` charges `ticks` once per visited bitmap word operation,
including the first operand read of an existence scan and each additional
operand AND. It does not claim 32 expression evaluations per machine word,
and does not charge skipped words/operands. No new weight or private cap.

`bitsets-meter.test.source` checks exact counts for empty, full-materialization,
inner-short-circuit and outer-short-circuit cases, including input identity.
Existing `bitsets.test.ts` exhaustive correctness tests must run unchanged.
This draft has not been applied to production or to the original constructor
validation jobs. It must pass separately on the validated raw source first.

A bounded search for native `structuredClone` in production core/kernel found
only `core/dsl.ts`'s `compareCopy`, used by reference comparison rather than
proof search; test-only clones are not accounting gaps. Other dynamic or
JSON-based AST reification still needs its own audit; this is not a complete
coverage claim.
