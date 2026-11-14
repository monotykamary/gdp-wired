# BAPA implementation plan

2026-11-14 — lane bapa, worktree `gdp-wired-bapa`, branch `after/bapa`.

## Source and falsifiable hypothesis

Read SECTION-64 and SECTION-63, `kernel/kernel.ts` (`closing`, `assumed`, `scope`, `keyOnly`, `keyTerm`), and the existing Lean `Sets`, `QAlpha`, and count-rule entry points before writing this plan. The restriction comes from runtime enumeration of unbounded naturals, not from unrestricted first-order instantiation itself. Hypothesis: an explicitly finite domain permits arbitrary quantifier bodies without changing legacy unbounded quantification. This is invalid if the Lean semantic correspondence or any runtime still assumes breakpoint completeness for the new syntax.

## Smallest first slice (not a claim to finish all of SECTION-64)

1. One named sized sort with size an expression over immutable natural parameters, no numeric upper cap. Empty sorts are valid. Explicit opt-in syntax; legacy AST and certificates keep their existing interpretation.
2. Bounded universal/existential conditions over one key. Runtime enumerates exactly `0 <= k < size`, including arbitrary arithmetic/function/tuple reads in the body. Do not send these bodies through the legacy breakpoint enumerator. Enforce lexical scope, alpha/capture avoidance, and a bound independent of the bound key and mutable state.
3. Bound-aware instantiation and fresh counterexample/witness hypotheses in the kernel, only after Lean soundness is checked. A universal instance is conditional on `t < size`; a fresh witness contains both its bound and body, and must not escape its branch. A false universal over size zero cannot supply a witness.
4. Venn-region count identities over that same finite domain use the existing pointwise/count checker and linear arithmetic; do not add an unproved matrix rule. Keep hand counts as comparison oracles, not axioms.

Existing native tuple keys should be reused, not a new packing convention. Rigid symbols, nested/multi-sort quantifiers, general row/column update rules, Skolemisation and constant division/remainder are later slices; each must receive its own Lean correspondence before kernel acceptance. A first-slice success does not by itself remove the cap from all 29 ports or prove MLDR closing.

## Lean-first trusted obligations

Names below are proposed API names, with precise semantic statements (X : Nat -> Nat, M : Nat -> Nat -> Nat, body : C, binder k, size n evaluated outside binder):

- `boundedAll_iff`: finite runtime enumeration is true iff `forall i, i < n -> holdsC (upd X k i) M body`. Arbitrary bodies, no `keyOnly` premise.
- `boundedAny_iff`: enumeration is true iff `exists i, i < n /\ holdsC (upd X k i) M body`.
- `bounded_instance`: from bounded universal, infer `evalE X M t < n -> holdsC (upd X k (evalE X M t)) M body`; connect syntactic substitution using existing `subst_evalC`.
- `bounded_counterexample`: from failure of bounded universal obtain `exists w, w < n /\ not (holdsC (upd X k w) M body)`; prove the fresh-environment closure using non-occurrence conditions, not just a proposition-level lemma.
- `bounded_witness`: from bounded existential obtain `exists w, w < n /\ holdsC (upd X k w) M body`; same freshness discipline.
- `bounded_empty`: at n = 0, universal is true and existential false.
- Venn region identities: for predicates X,S over i < n, `card X = card (X /\ S) + card (X /\ not S)` and `card S = card (X /\ S) + card (not X /\ S)`, plus nonnegative regions and union <= n. Reuse `Count.sumBelow_*` and `counted_sound`; no new trusted arithmetic solver.

No TS acceptance path is enabled until corresponding Lean theorems compile and pass the axiom gate. No `sorry`, added axiom, unsafe cast or trust shortcut.

## Mutants and regression acceptance

- Refuse instances outside the domain (including n=0), witnesses lacking their bound, captured/non-fresh witnesses, incorrect existential polarity, and incorrect sort size/frame. Each new rule gets a false weakened Lean statement/countermodel and a rejecting TS test.
- Exercise arbitrary body reads (scaled key, repeated key, tuple coordinates, function reads), zero/one domains, and sizes >64 with exact runtime checks.
- Preserve byte-for-byte acceptance of every old certificate: no reinterpretation of legacy `all`, `Law.forall`, count cuts, proof tags, certificate bytes or exporter defaults. Run existing kernel/count/tuple/quantifier and Lean-export regressions; compare the canonical 29 verdicts with the same profile, without editing the original 4aaf claim runs.
- Re-derive the xNotS/sNotX/xAndS identities automatically in an isolated showcase. Only claim cap removal for ports actually migrated to sorts and checked.

## Work/review/receipts

- Ask Fable (`hc t2`) to review this plan before accepting the new design; lane D (`hc t7`) reviews each kernel diff before completion.
- All builds, tests, theorem compilation, mutants and profile runs through `SUPERCOMPUTER_CONTROLLER=1 supercomputer`; job outputs under `$SUPERCOMPUTER_OUTPUT_DIR`, retain batch IDs and use `supercomputer batch fetch`.
- Local work only git, edits, reads and few-second commands. Initial shell could not find `supercomputer` on PATH; the installed executable was located at `/home/user/.local/bin/supercomputer` and its skill is the next required read.
- Never push, rewrite history, edit another worktree, modify 4aaf claim runs, or kill by pattern. Stop started resources. Only append dated RESULT/BLOCKER receipts to `/home/user/VCS/working-remote/open-source/MAIN-INBOX.md`; do not message Main.
