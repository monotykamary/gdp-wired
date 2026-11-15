# Shared proof worker: independent review and disposition

Output-hook port by pi Terra `b50d3b3aafae44189bb28763be3f7c61` exactly
adapted the reviewed `49b8b591c` source hooks. No trusted kernel decision,
search strategy or model definition changed. Hooks remain default-off.

Independent pi Terra `45a96eb810d04f0694f7b1fffe415f38` found three blockers:

1. Post-return I/O failures could hide the returned native verdict. Fixed by
   retaining the native booleans separately, returning `outputError` or
   `receiptWriteError`, using a stdout fallback and nonzero status.
2. Non-counted data lacked a source-projection qualification. Fixed with an
   exact structural same-machine/law-coverage check. Different machines,
   missing laws, witness bridges and ambiguous families remain explicitly
   unqualified, never Lean or all-size evidence. Both codec read and write
   recompute the tag. A forged-qualification control is required to fail.
3. Installing `countsDump` enabled diagnostic search paths. Removed entirely;
   native capture uses only the final-result provenance observer. The actual
   consensus native counter vectors are identical with observation on/off.

Follow-up pi Terra `ead1c361b4e7412b81389224794819a6` noted that counted
coverage failures still discarded data despite the raw-retention contract.
Fixed: a complete counted family can retain null public-law indices and an
unqualified tag. Missing certificates still fail closed. Added changed-counted-
law retention control; unqualified worker exit remains 2, not success.

All fixes passed batch `20261115-170357-6t6qmn`: 24 tests, 183 assertions,
typecheck, exact work-counter parity, fresh-process capsule read, positive
native consensus closure retention, tiny-work refusal, commitlint. This is
capture infrastructure only; there is no Lean or arbitrary-size acceptance.
The source commit/tree fields in this uncommitted gate are disclosed base
references; actual candidate source-file hashes are retained independently.
