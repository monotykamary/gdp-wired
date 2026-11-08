# Track K: conditional lemma cuts, Lean first

Base: `8610af26c16cf8e50b5ec0564a154c6bf358d82c`; branch `claude/track-kernel`.

## Step 1 design

A lemma carries positive linear conditions `when`, a linear `cut`, its old-language proof tree, and an optional list of hypothesis indices. The table, count reads, instances, and witness namespace are the containing certificate's: a lemma introduces none of its own. A slice is selected from the exact already-expanded goal by checked indices; absent means the whole goal. Invalid indices reject.

The checker first verifies every lemma tree with the old tree checker against that fixed slice and the path consisting of `not cut` and every `when` atom. Lemma trees cannot cite any lemma, so the certificate contains no cyclic dependency graph. This independent-leaf restriction suffices for the initial rule and its eight pointwise send lemmas.

The main tree retains its original split paths. At a leaf, only lemmas whose every `when` atom the original path decides true are available. Their cuts are added as true path atoms for the existing leaf checker. Cuts are not fed back into eligibility, and a cut is never used to validate itself or another lemma. Empty lists reduce to the original checker.

Proof plan: selected hypotheses are members of the original goal; an accepted lemma implies its cut whenever `when` holds; path decisions imply the declared conditions; extending a path with eligible cuts preserves `PathHolds`; induction over the original tree then gives refutation by the existing `checkT_sound`. Build a model with the existing well-formed table theorem. Reuse the current counted witness construction unchanged, replacing only its final application of `sound`. Carry this into `countedW_sound` and `mc_sound` (CountMachine.lean), so the actual production counted certificate, not merely a toy goal, is covered.

No TypeScript checker modification before these proofs build without sorry or new axioms. Later phases: exact TS mirror; unchanged-certificate conservation; TS/Lean mutants; exporter/conformance; then untrusted emission and a same-VM send replay comparison. The independent review remains mandatory before merge.

## Untrusted emission and replay

`core/lemma-cuts.ts` extracts repeated forced splits, selects their exact original support, and transports proofs by matching checked rows (no solver calls). Prerequisites are inlined only when their rows are actually required; lemma entries still cannot cite each other. A weighted-context estimate, not raw node count, filters unprofitable results. Every result goes through `checkGoalLemmas` before it can be proposed to production.

The production admission experiment is opt-in with `GDP_COUNT_LEMMA_CUTS=1`. It uses only the current work/wall deadline and retains the old certificate as fallback; `checkCountedLaws` still checks the entire family. Optional row tables recorded during proof transport are untrusted, keyed by the exact goal and ordered path, and never consulted by the kernel. The standalone sharing API checks its result; production proposal construction leaves authentication to the complete family checker, avoiding duplicate checks. The default path remains unchanged while end-to-end performance is measured.

Recreate a read-only Track M snapshot and apply the experiment (recording SHA256 manifests):

```sh
bun research/track-k/snapshot-replay.ts ../gdp-wired-trackM runs/track-k-send-input
bun research/track-k/prepare-sharing.ts runs/track-k-send-input
supercomputer run --jobs research/track-k/send-capture-jobs.json --out runs/new-send-capture --class interactive --vm-type large --data runs/track-k-send-input:runs/track-k-send-source
bun research/track-k/extract-send.ts runs/new-send-capture/send-baseline.log runs/new-send-pack
supercomputer run --jobs research/track-k/share-replay-jobs.json --out runs/new-share-replay --class interactive --vm-type large --data runs/new-send-pack:runs/track-k/proof
supercomputer run --jobs research/track-k/live-sharing-jobs.json --out runs/new-live-sharing --class interactive --vm-type large --data runs/track-k-send-input:runs/track-k-send-source
```

The source worktree can advance; compare `manifest.json` to the recorded one before comparing different captures. These are isolated send-branch proofs, not whole-MLDR proofs. Captured opaque columns are re-interned before a fresh-process replay. Brotli keeps the complete artifact within boat's bounded output; compacting trace output changes no goal or search budget.

