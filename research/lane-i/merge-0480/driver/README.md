# Public merge-gate inputs

Build `source.tar` with `git archive 2de2ce89`; vendor archives use gitlinks
`0b6ebeee` (gdp-ts) and `d47141cc` (handwired), prefixed with their `vendor/`
paths. `../INPUT-SHA256SUMS` binds the actual archives and original drivers.
Archives and private inputs are not committed.

Stage these files under `port-input`. Copy `census-preload.source` to
`census-preload.ts` there: the `.source` extension preserves executed bytes
without adding duplicate global declarations to repository typechecking.

`verify.ts` is the original grouped driver; `verify-isolated.source` selects each
of the seven long-running files separately, with the same source, identities,
test contents and per-command deadline. The failed grouped receipt is kept.

Measurement drivers record Bun-resolved checker-file hashes before imports.
That is source-file custody, not an attestation of an arbitrary external
loader. The strict audit remains strict. Its separately named
`release-compatible` mode permits only decreasing unpriced `evals`/`astNodes`
observations while retaining every other compared field. D decides that scope.
