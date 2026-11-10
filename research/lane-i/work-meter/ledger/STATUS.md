# Unified meter and phase-ledger continuation — UNVALIDATED SOURCE DRAFT

These .source files are candidate source, not active modules and not validated.
They are being prepared in parallel with complete-ast-preparation.

The historical twelve coefficients keep their exact order and values. An
explicit complete vector has eight additional operation coefficients. There
is deliberately no implicit provisional default: D2 must supply a frozen
vector for qualification. The all-ones vector exists only in unit tests.

The synchronous ledger records raw and scalar start/end deltas, parent IDs,
inclusive and exclusive counts/time, successful or exceptional exit, and
whether its units use the historical model or an explicit complete model.
Root totals are not a sum of overlapping children. Output failures cannot
change the work's return value or replace its exception.

Next: after the I2 source checkpoint, install these into core/ in a new
isolated index, delegate kernel/prove.ts fullWork without changing the
historical fast path, and wire existing ptime plus untrusted call boundaries
for checks, table building and instance construction. Validate trace-on/off
exact equality before any census. No synchronous timer is claimed as F3;
a blocking-loop-capable observer with useful stacks remains separate.
