# Track K: conditional lemma cuts, Lean first

Base: `8610af26c16cf8e50b5ec0564a154c6bf358d82c`; branch `claude/track-kernel`.

## Step 1 design

A lemma carries positive linear conditions `when`, a linear `cut`, its old-language proof tree, and an optional list of hypothesis indices. The table, count reads, instances, and witness namespace are the containing certificate's: a lemma introduces none of its own. A slice is selected from the exact already-expanded goal by checked indices; absent means the whole goal. Invalid indices reject.

The checker first verifies every lemma tree with the old tree checker against that fixed slice and the path consisting of `not cut` and every `when` atom. Lemma trees cannot cite any lemma, so the certificate contains no cyclic dependency graph. This independent-leaf restriction suffices for the initial rule and its eight pointwise send lemmas.

The main tree retains its original split paths. At a leaf, only lemmas whose every `when` atom the original path decides true are available. Their cuts are added as true path atoms for the existing leaf checker. Cuts are not fed back into eligibility, and a cut is never used to validate itself or another lemma. Empty lists reduce to the original checker.

Proof plan: selected hypotheses are members of the original goal; an accepted lemma implies its cut whenever `when` holds; path decisions imply the declared conditions; extending a path with eligible cuts preserves `PathHolds`; induction over the original tree then gives refutation by the existing `checkT_sound`. Build a model with the existing well-formed table theorem. Reuse the current counted witness construction unchanged, replacing only its final application of `sound`. Carry this into `countedW_sound` and `mc_sound` (CountMachine.lean), so the actual production counted certificate, not merely a toy goal, is covered.

No TypeScript checker modification before these proofs build without sorry or new axioms. Later phases: exact TS mirror; unchanged-certificate conservation; TS/Lean mutants; exporter/conformance; then untrusted emission and a same-VM send replay comparison. The independent review remains mandatory before merge.
