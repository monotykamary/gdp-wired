# Follow-up while `a8bbe098` is gated

No production file or gated revision is changed. The gate remains Lane D's
`a8bbe098` versus `8214a543`. This directory holds separate measurements and
an integration queue, not a replacement gate.

## For lane B — fresh cost comparison

**Hypothesis:** `a8bbe098` already contains the generic mixed-clause policy
qualified in `f7c5b4ba` (count-source SHA-256
`7a4c830848afa2d05393bdd00c546393092cf1f94d5ce9cdee8a2aad9189abd4`).
Its p1 cost should therefore match the validated control `97463c56` at
1152.3382236 units, rather than the fallback-first 2046.9378360. Five fresh,
alternating-order pairs test this; each certificate is independently replayed
in another native process. Three separate whole-Paxos repetitions per source
retain raw output; the current-source target is exactly 6,915,544 solver /
1,037,946 full work. A confirmed regression requires a new generic policy,
not a protocol-name special case, and must not alter the currently gated source.

**Important encoding boundary:** Lane B now identifies frozen family
`5dbdbf766e9949b051d0764920f1bcc3707690cd6852fca6d0bcf18674fbdac4`
as the historical P* encoding. It is used here only because it is the exact
validated p1 cost control requested by the coordinator. Its `originalHarness`
metadata does **not** establish original IC3Syn model identity. None of these
conditional p1 results counts toward original-model Inv* or 29/29.
Whole-Paxos uses the restored sources' ordinary canonical runner, separately.

The first low-arity prototype failed the whole-Paxos work target. The retained
repair restricts eager bounded completion to the checked mixed-clause shape
(including an ordinary-map read); aggregate-only clauses remain sparse-first.
Its prior five-pair result does not replace the new a8-specific measurements.

## Named candidate-only loss — five new pairs

`core/effect-queue.test.ts:122`, **the CLI on the pool (4.x,
examples/effect-pool.ts; 3.x in a project of its own): laws as comments; the
cancel broken with its run**. In the earlier isolated cohort, one candidate
run returned unknown for the first-call laws while its paired baseline passed.
This is preserved in `research/lane-i/regressions/next-candidate-results.md`.

The new experiment restores exact `8214a543` and `a8bbe098`, verifies equal
test hashes, and runs the unchanged case in ten fresh Bun processes on **one
exclusive VM / one recorded CPU model**, alternating which source runs first.
The original 900,000-ms test cap and proof budgets are unchanged. Outer process
receipts include wall time, resources and compressed raw stdout/stderr. A later
pass will not erase the earlier failure or prove that it was noise.

## Helper queue — no enablement

See `helper-integration.json`. Do not merge entire lane branches: they include
unrelated changes and may replace this lane's scheduling/symbolic-domain fixes.

1. **Original-model identity first.** At initial inspection, B's canonical models blob
   matches `8214a543` / `a8bbe098` (`0541fa9436e307a6fb716aa5064637b30b893b79`);
   F and E still have the earlier routing blob
   `0d5521e2e4dcbf6ac2ea7116ecee23497a0ec66b`. Existing saved P* families are
   quarantined, even after the source entry point is restored. Re-capture the
   original family; record source, machine and family hashes. No equivalence
   of P* to original C0/Copied is assumed.
2. **No conditional-to-unconditional shortcut.** One production STEP must
   cover every operation under its original guards. Reindex and compose the
   proof on that original goal, prove uncovered cases impossible, and prove
   INIT for the same conservative extension. Never import saved per-op proofs
   as axioms or reset the budget independently for each case.
3. **Keep the attempt's original shared units and wall allowance.** Include
   construction, transport and final checking. Diagnostic proofs outside a
   limit are evidence, not an admitted helper. E's low counted cost does not
   cure its measured wall-time miss.
4. **Fresh proof custody first.** Native INIT/STEP replay, expected mutation
   refusal (not crashes), and real Lean checks where the helper adds kernel
   proof forms. No wholesale kernel tip import. The rejected `fcf2d01c` is not
   an ancestor of the gated candidate; authorization of exact `8501ab8f`
   does not authorize later guarded-rule revisions.
5. **Then default-off integration tests.** Register every new core/kernel
   test, run roster completeness, source/type/lint checks and full canonical
   shards. Run original 29-model normal/broken census and same-CPU alternating
   off/on comparisons, preserving all losses, p1 cost and whole-Paxos work.
6. **Only then request a new Lane D gate against `8214a543`.** No off-by-default
   helper becomes the default before that acceptance; `a8bbe098` stays frozen.

## Execution and custody

`jobs.json` runs only on boat. Staging is file/git-only; it reuses immutable
packs by hard link and adds the 142-KB control pack. Batch
`20261110-080834-7ilqre` completed both measurement workers. The first
audit correctly rejected the collector's 400,000-byte p1 tail. The original
816,127-byte stdout and empty stderr were recovered through the Boat API,
with matching remote/local SHA-256; the recovery VM was stopped. The
complete-evidence audit passed. The original failure remains preserved.
The CPU-qualified regression audit also passed; its native measurements
and adjudication boundary are in `lane-d-adjudication.md`. Final research-
tooling validation and commitlint passed. Keep one lightweight local waiter per batch.
All receipt aggregation, parsing, audits and checks now run as boat jobs;
reuse existing immutable source archives/packs, without local tree copies.
No subagents are in use.
