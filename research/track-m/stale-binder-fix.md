# Stale-binder memo fix candidate

Base: `4aaf033bdfd25a76a202643d742fa2420ca8142a`.

## Falsifiable hypothesis

The untrusted fast prover stores concrete instances, goals, proof trees and models while comparing machine/law/support inputs after textual alpha normalization. Freshly constructed rules can therefore reuse terms naming old binders. Exact structural identities must prevent that reuse without disabling valid same-binder memo hits.

## General change

`kernel/prove.ts` uses exact machine and law/support texts instead of alpha-normalized texts. Law text caching is keyed by the complete Law object rather than just its shared `holds` object, so different `forall`/`keys` metadata cannot inherit an earlier identity. `GDP_MEMO_ALPHA` no longer permits binder-changing memo reuse. No protocol-name dispatch, kernel rule change, proof-check bypass, budget rule change or benchmark edit is introduced.

Inputs retain the existing immutability expectation of the WeakMap caches. This is not an implementation of alpha-renaming cached terms.

## Regression scope

- Fable's supplied minimal reproduction, copied with its original two-level imports.
- New default-suite unit tests: fresh binders, retained same-binder hits, and two Laws sharing `holds` but differing in tuple-binding metadata.
- Each of the original 29 protocol constructors, including MLDR: first/fresh fast proofs and ordinary proofs of **kind laws only**, all independently checked. These are not the canonical safety run or a performance/unit comparison.
- Separate native processes for default and `GDP_MEMO_ALPHA=0`; no canonical calibration profile is changed.

Source candidate, not yet runtime-verified or D-accepted. Results and review requests go only to Main's append-only inbox. Preserve every historical 4aaf artifact and accepted disclosure version.
