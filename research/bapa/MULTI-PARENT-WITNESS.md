# Complete multi-parent witness source checks

This extends `proof-witness.ts`, not the kernel or any trusted Lean theorem.
`proof-emit.ts --projection witness` still consumes an immutable SHA-bound capsule
in a fresh process, never runs a search, and leaves public source laws untouched.

## Every path is an obligation

The exporter enumerates all root-to-usual-producer paths. Empty/missing/duplicate
parents, cycles, non-usual leaves, unknown contexts and ambiguous witness contexts
are refused. Traversal is bounded to 128 paths and depth 256, failing closed.
Transparent projections and exact-machine inference contexts are admitted.

A path carrying a witness uses that witness. A context-free inference path can
reuse only the unique retained witness context in the graph; the inferred source
must equal that path's producer and each stated inference law must be present.
Reuse is an untrusted proposal, not a transport axiom: every path independently
checks the original public input, complete ghost-extension machine, original
binder/body, captured substitution, full native certificate, and public membership.
Each contextual family member must occur exactly in the complete producer family;
extra producer kind laws are checked, not discarded or supplied as assumptions.

Every path emits a distinct `<id>_pathN_laws` and source theorem. The top-level
`<id>_laws` and public theorems are conjunctions of **all** path theorems, never an
arbitrarily selected branch. A reducible `claim` definition recovers the exact
proposition type from the conjunction proof. It introduces no axiom. Single-path
output retains its previous names and theorem shapes.

`sourceProjection.parentPaths` records provenance paths, witness-context paths,
per-path family/source theorem names and public entry indices. The receipt verifier
requires named axiom output for every path and for the combined theorems. Removing
either parent's source output is a failed receipt, even if the combined name remains.

## Verified controls and firewall

Native strict-once batch `20261115-232217-ye1qw6` passed both jobs:

- Typecheck and 17 unit tests (42 assertions with the emitted fixture).
- A two-parent existential control, fully built in Lean.
- An incorrect witness only on parent 1: refused by the native substitution check;
  independently, changing only parent 1's emitted witness from 0 to 1 is rejected
  by Lean because its checked source substitution equality is false.
- A corrupted second-parent native certificate is refused.
- Cyclic/missing/duplicate parents and incompatible inference context are refused.
- Both missing-parent-theorem receipt controls are refused.
- Original firewall capsule
  `2ed5690066d27705a905eca1dc338612f19c0ed09a59d9f16d79a956ef33c14e`:
  two complete 12-law parents, original public law at entry 2 in both;
  full Lean build, explicit root Lean check and `SOURCE_CHECKED` receipt.

The firewall source theorem `bapa_firewall_ex0` conjoins
`bapa_firewall_path0_ex0` and `bapa_firewall_path1_ex0`. All source/family theorem
outputs use only `propext`, `Classical.choice`, and `Quot.sound`. No search was
repeated. Evidence: `runs/bapa-p1/multiparent-02/`; replay recipe:
`research/bapa/multi-parent-witness.jobs.json` with the capsule supplied as
`p1-historical/symbolic-firewall`.

Final expanded typecheck (including verifier and receipt controls), 17 tests and
42 assertions passed in `20261115-232707-357dv0`. Local `git diff --check` is clean.
The preceding expanded-types job had passed its typecheck/tests before its final
`git diff` failed because remote snapshots have no Git repository; the clean job
omits that laptop-only check. Commitlint passed on the shared commit title.

The first implementation gate (`20261115-231732-dct0v3`) passed native controls
but Lean refused inference holes in the joined theorem headers. The explicit
reducible proposition definition fixed the output types; no checker was weakened.

## Separate decentralized-lock disposition

The finite sub-sum route is stopped. Read-only inspection found exact flat-key
`Sum` support, not an accepted exact native-tuple-map total: `Sum` binds one key,
`sumTermOk` accepts `get(map, var(key))` and rejects tuple/projection terms, while
arity checking rejects such a unary read beside the native binary relation.
`simple_decentralized_lock` goes to the packed-key translator; this change makes
no claim about that protocol.
