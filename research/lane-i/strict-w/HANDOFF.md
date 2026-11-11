# Strict-W table admission handoff

Source baseline: d4d600d8dce6b8c49c3ce4023470c83dd1cd3226.
Final tested runtime/test tree:340557e57aa51ca91678dd46a3cbed1017c07c3f.
The commit owning this file contains the exact runtime/test bytes of that tree;
its full hash is sent to t1/D separately. No A integration, C2 promotion or push.

## Runtime delta

- core/meter.ts: unchanged increments, optional pre-charge table hook only.
- core/table-admission-hook.ts: dependency-free scoped hook holder.
- core/table-admission.ts: amortized permission, guards allotherrawcolumns,
  activeend, directtablewrites and nested/exceptional/primitive-refusal exits.
- core/count-premise-search.ts: scoped guard around local and fallback probes.
- core/table-admission.test.ts: positive/rawidentity, all25otherbucketchanges,
  exactends, largecharges, nestedbudgets, refusedprimitive and reader controls.

No protected file, prices, root budget, tier allocation or native predicate
changed. Executed raw observations remain exactly counted; no reset/refund.
Scope and caveats are in SCOPE.md; exact outcomes in RESULT.md.

## Strict gate

The actual F12 original MLDR counter delta is224999999.62510002 atW225000000,
versus225000050.62510002 before. Only51table-cell visits disappear; allother25
buckets match. Nine/F13 clean endpoints also pass. Each emits49candidates and
one uncheckedInv* proposal, publicUNKNOWN. No1024slack or rounding argument.
Supercomputer's passive GDP_CYCLIC_LOG=1 is disclosed beside9/12/13 profiles.

Finaltypes/lint/commitlint/fullcontrols pass. Native19/38+fourmutants pass;
strict28 legacy audit passes28/28exact,27proven/1unknown. This is NOT a28model
full-W campaign, calibratedW, Lean clearance or family admission.

## Repro inputs and optional old-line patch

/tmp/lane-i-strict-w-freeze/source.tar SHA256
f63d82a481e51dfb6c03c373e2fb323a1023df9be9e44ea9aac0a08613f02d9e.
Dependencies: gdp-ts.tar68994527332b5abd3bf4c523135fb00fca7846a95451abb9e706bddaa9f1b42d;
handwired.tar242f2ad56c448edd61ee8ad7f1680018fbf6378da3ffbbf21d214930327f399e.
Manifests and full bounded receipts are committed under this directory.

runtime.patch SHA256b2e5b513bfcab9ee58fd090d0be9bae898ad617d87f6baafe8727945ee44572b
is exactly those5core/testfiles fromd4 to340557e5. It applies cleanly to
historical51ee4018ba8ad802a4b2d061a51afa59bd943aff, yieldingtree
617dc4907dadddffbcdfefbb700a75726167c6fa withoutG1/C2/scheduler additions.
That old-line overlay has only a patch/application/unchanged-kernel check,
NOT a separate native/static/endpoint gate. Do not transfer the current-line
results to it without testing. Do not alter A's active57a8f1a9 diagnostic.
