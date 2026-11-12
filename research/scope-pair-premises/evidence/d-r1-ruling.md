# D source-only review — 0dba5e23

Decision: **SOURCE-ONLY HOLD — R1 hard-stop contract**, not runtime GO.

Exact child: `0dba5e23d6b5099fd575312b4347c7479b2da1c0`.
Parent: `9eb09b8326fc2670fad6725f774ab1b252c4d343`.
Verified packet SHA256:
`02282c092a0883a63995857e7d0eb48edf5f13a489213e7c247283cb0919ee87`.

## R1 — inherited catch defeats the stated extraction hard-stop guarantee

`core/count-scope-hyps.ts:19-20` calls `countedCertificateHyps` and immediately
returns undefined if it returns no set. With nonempty `cert.lemmas`, that helper
runs native row/dependency extraction inside an unqualified catch in
`core/count-cert-transport.ts:26-48`. Its row rebuilding can throw a genuine
`BudgetExpired`: `usedHyps` calls native `rowsAt`; FULL row construction calls
`startWork`, whose allocator throws an authenticated capacity error on refusal.
The legacy catch converts that error to undefined. The new caller then returns
an ordinary extraction decline. There is no rethrow after the swallowed error.

This is an inherited path, not a newly introduced catch, but it remains part of
the proposed new collector. Consequently README's unqualified 'A hard budget
stop propagates' and comparison protocol M3 are not supported by this code for
a stop occurring *inside* legacy extraction. A test that expires at the new
entry tick would not cover it.

Before the source contract can pass, preserve the original hard-stop exception
through this path and prepare a regression that triggers during the legacy
nonempty-lemma extraction. Keep ordinary malformed-metadata refusal distinct.
Any change to a currently protected module must be explicitly disclosed and
resealed; this review does not authorize a hidden expansion of the delta.
No native reproduction was run. This is a static control-flow finding, not a
claim that it caused T301 or R4.

## What the source review supports

- All12 packet entries and99 protected-file hashes match the exact child and
  parent; every parent kernel file is protected. Only the two declared
  production files differ. The implementation patch exactly matches the
  committed three-file implementation/test diff and reverse-checks cleanly.
  The old scope reference is byte-identical to the parent.
- For a fixed valid native path, unchanged goal/cuts and ordinary metadata,
  the pair-cell argument is coherent: initial atom/fact rows determine the
  native pair name set; keeping every fact supplier (including duplicates and
  stored zero coefficients) preserves those cells. The actual frame/mono/lin/
  lemma prefix is used; product dependencies and square offsets are followed.
- Unioning the legacy set preserves successful old extracted references. The
  unchanged formula mapping remains conservative about duplicate owners.
  Scope metadata still grants no checked verdict. Native transport/checking
  and explicit declaration refusal remain authoritative.
- This is only the identified fixed-path pair-availability argument, not a
  complete dependency or transport theorem, nor evidence of a production fix.

## Tests/specification

The five synthetic native-check tests are prepared but UNRUN. No compiler,
project imports, test runner, native replay or worker was started. The tests
currently cover the named basic pair, unread pair, duplicate, product/square
and frame cases; they do not by themselves establish all advertised mono/lin/
lemma, atom-only, zero-coefficient or hard-stop cases. Prepare focused cases
before claiming that broader coverage; execution needs separate authority.

The comparison spec correctly separates old-false/new-true improvement,
same-decline, old-true/new-false regression, resource/infrastructure incomplete,
and missing-input block. M1 should mutate a frozen successful scoped payload
and target context, not silently re-extract a different scope; conservative
suppliers need not each be logically indispensable in isolation.

Both exact real comparisons remain BLOCKED_MISSING_REPLAY_INPUT. Existing
T301 m/law ASTs and R4 public model/names are not the missing runtime instances,
certificates, source contexts and exact declining call. No synthetic
substitution, changed family, inferred exception or success claim is accepted.
B's independent fallback/diagnostic branch is not composed by this review.
Sizing/grid and R4 holds stay unchanged. No admission, test execution, capture,
search, merge or rerun authority is issued.
