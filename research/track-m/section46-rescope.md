# Section 46.10: one reduced-context native pass

Base: `f5851b03`, after the independent 46.4 commit `71321ab5`. Lane B private worktree. No `counts.ts`, meter, kernel or conditional-transport source edits.

## Implemented contract

1. Validate offered scope metadata, then infer the candidate set from the certificate's cited rows, including independent cut source slices. This is not authority.
2. Transport the same certificate, without search, to exactly **owner + cited premises**, not unrelated held laws. Run the existing native INIT/STEP checks once. No subsequent drop loop.
3. Only a successful nondeferred native replay can mint the opaque receipt. `isCheckedReducedScope(scoped, machine, currentLaws?)` revalidates machine, owner, exact checked context, certificate/instances and source goals. The original context's live law objects are checked too; pass the current law list to detect replacement-by-name as well as in-place mutation. Forged/copied JSON flags, changed bodies, different contexts and changed certificates are not receipts.
4. A refusal may make **one** full-context fallback only when the final optional argument to `rescopeCountProof` supplies `{allowFullFallback: () => true}` for existing funded headroom. Default is DENY. The helper grants no scope/credit and catches no hard error, cancellation or exhaustion.
5. Full-only acceptance returns `status: 'unchecked'`, no checked-reduced receipt. A must retain recorded/inferred union producing-recipe known requirements. An accepted reduced replay alone may replace that union.

A owns the production policy, recipe graph, reservations and all `counts.ts` wiring. The old `held` parameter remains source-compatible but cannot enlarge the canonical context. Public event compatibility retains the `drop` type; this implementation emits no drop attempts. Check-work telemetry includes receipt work and is not a saving claim.

## Verified gate

`jobs-section46-rescope.json`, boat gate, `section46-rescope-v5`: **82 tests / 2,323 assertions pass**, zero failures. Full TypeScript check, type-aware lint, both commitlint configurations and before/after source hashes pass. Detailed logs are in `section46-rescope-gate/`.

- 10 focused tests / 51 assertions: all four Fable negatives, real native call counts, default/explicit denied fallback, hard-error propagation, zero-work admission, false INIT/STEP and changed context, and opaque receipt mutation controls.
- 14 existing scope tests / 57 assertions, including genuine full-work/forbidden-clock controls and retained independent cuts.
- 1 frozen-source byte test / 11 assertions: both members' accepted reduced closing-family payload bytes and native verdicts equal the verbatim f585 implementation. The fixture source hashes match 46.4's f585 source manifest; only import URLs are adapted at runtime, with no checkout writes.
- The changed public proof-guided case: **1 pass / 8 assertions, 7 filtered out**, with `GDP_WORK_FULL`, `GDP_COUNT_STRATEGIES`, `GDP_COUNT_TIERS`, `GDP_COUNT_PREREQUISITES`, `GDP_COUNT_CLOSING_RESERVE`, and `GDP_COUNT_FINAL_DEFER_CHECKS` all `1`. Only its old full-first event assertion was changed. This is NOT a full-public-suite green claim; older direct-counter fixtures remain A's separate migration concern.
- 11 closed-family tests / 1,830 assertions; 4 certificate-transport / 11; 6 lemma-transport / 10; 20 conditional-proof / 222; 10 conditional-cuts / 100; 5 conditional-cache / 23.

## Prior attempts, retained honestly

Archived in `section46-rescope-gate/prior-attempts/`:

- v1: an invalid assertion expected a corrupt packet to reach both native calls; the unchanged transport actually refused before STEP. Also, JSON had duplicated the owner object in the zero-budget fixture, so owner identity failed before admission. Both fixtures were corrected; no refusal was relaxed.
- v2: escaped-newline syntax error in the new test insertion.
- v3/v4: public tests launched without their prerequisite feature profile; these were not production failures or successful tests. A separately confirmed the stale direct `costs.fm++` technique is incompatible with f585 strict admission. The final gate covers only B's changed public case with the intended flags, and makes no claim about the seven filtered cases.

## Limits

These are source/unit/native control results, not complete source-conformance or execution approval. No full T301 artifact, end-to-end/W fitness, timing saving, 1G run, global proof or M1 claim. No new measurement campaign; section 44 stays parked and existing R3/C0 holds are unchanged. Receipt fingerprints add counted work and require later final-pin measurement before any performance claim. All owned gate jobs were collected.
