# Complete accounting — changed candidate validation in flight

No production integration or complete-coverage claim.

Active batch: 20261110-123003-1cvbpa (complete-ast-progress), task
cd893c39-f0e2-4935-9ca3-5c9b57c0c9b7. See state.json and REPORT's top section.

Preserved failures: first child error was lost; the diagnostic identified a
stale import insertion coordinate for files with late imports. The next pass
failed at kernel erasure, whose huge assertion diff was truncated. The latest
program emits bounded first-difference diagnostics. No generated patch has
been accepted yet.

A separate ledger gate passed 39 selected tests, roster and decoder, but
failed type/lint because a counter expression starting with '(' was parsed
as a call on a preceding Request. Explicit separate statements fix that
syntax. The changed candidate is being revalidated, not assumed correct.

The original model, production code and budget constants are unchanged.
Coverage of optimized bitmap work and cloned/reified ASTs remains an audit
item. No weights/W, F3, census or quiet generator-intake success is claimed.
