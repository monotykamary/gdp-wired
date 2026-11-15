# Stale-binder memo rollback base (release held)

## Current release disposition (Amendment 3)

**0.49.0 must not ship this false-negative.** Main authorized the rollback only
as the base for a proper memo-reuse fix. Fable must classify every reuse point;
B implements and D reviews the name-bearing/name-free boundary. Both stale-
binder repros must prove, both expected-failure markers must be removed, and
exists-support must retain the fc98 vector before the final gate and F runs.
No F freeze, CAL-MIN-P, or capture is authorized by this base commit.

## Prior branch-b evidence (retained as rollback rationale)

The production memo-key changes from `ffe53b2fe8b5b274a5d7df7064305f47c08e4249`
and `4222e4c0f11e71ca4115d29bb3ccb01e3949d6bf`'s associated positive regression
expectation are reverted as a development base only. Legacy alpha-normalized machine/law lookup
and the shared-`holds` text cache are restored; `GDP_MEMO_ALPHA=0` again opts out.
The same-binder, independently kernel-checked regression remains mandatory.
The fresh-binder and shared-binding-metadata positive assertions remain in the
quick suite as explicit expected false-negatives, not skipped tests. The native
counted-family regression driver, minimal reproduction, and historical evidence
remain available; they are not evidence that the reverted fix is shipped.

Main's pre-registered branch rule selected this rollback using D's batches
`20261114-105253-rphfw0` and `20261114-105514-ygug11`:

- `fc98173be`: passes, 686698 solver units / 93634 EPR / 1518 solver calls /
  90 root queries / 27 memo hits / 30 misses.
- `ffe53b2fe` and every later tested pin: fails, 3750941 solver units / 129052 EPR /
  3668 solver calls / 167 root queries / 0 memo hits / 40 misses.
- Disabling alpha reuse on `fc98173be` reproduces the failed vector exactly.
  `e98a09453` with memo cap64 also has that failed vector and fails at 51.385s,
  outside the required passing <=45s margin under the original 60s caller wall.

Before authorization, D reviewed both public boundaries on `e98a09453`:
`research/verify-all/closing-snapshot-review/E98-MEMO-ROLLBACK-SAFETY.md`.
Public `proven && checked` still requires the certificate to be checked against
current machine/laws; a public reachable `.run` refutation still requires an
actual replayed run. A raw `proven:false` / `stuck:sat` / witness without `.run`
is not a certified reachable refutation. Legacy stale-binder reuse can yield a
false-negative; it does not waive either public certification boundary.

The earlier plan to defer proper reuse to 0.49.1 is superseded: a proper fix
is now mandatory for 0.49.0. A separate single-entry LRU change remains
acceptable only after its original-wall exists-support run keeps
the full `fc98173be` counter vector, including memo hits. No wall, budget,
assertion, canonical profile, or historical 4aaf vector is relaxed here.
Final release approval requires the proper fix, cleared repro markers, the
vector-preserving integration, the one final gate, and subsequent F runs.

## Historical exact-key candidate (not shipped in 0.49.0)

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
