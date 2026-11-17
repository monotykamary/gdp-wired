# Counted-budget audit and reviewed codemod

The migration is **incremental**, not a single-release conversion of all509 sites.
See [the0.50.3 scope and public backlog policy](0503-INCREMENTAL.md). The retained
474 review blockers are backlog items; they are not collectively a release gate.

Run these **on boat** through the lane's interactive diagnostic jobs:

```sh
bun tools/counted-budget-audit/audit.ts tools/counted-budget-audit/0501-BUDGET-INVENTORY.tsv . "$SUPERCOMPUTER_OUTPUT_DIR/0503-manifest.json"
bun tools/counted-budget-audit/codemod.ts tools/counted-budget-audit/0501-BUDGET-INVENTORY.tsv . "$SUPERCOMPUTER_OUTPUT_DIR/0503-codemod-plan.json"
```

The original ledger is retained byte-for-byte: **509 candidates in 158 files**.
Each output has exactly one stable-ID record per input row, including all of
that row's original grants. Current AST options are separate evidence; a
retired millisecond literal is never treated as a work measurement.

The codemod is intentionally **dry-run only**. `reviewed-migrations.json` lists
specific IDs, observed work maxima and native batch evidence. Its output binds
the original ledger and current source files by SHA-256, verifies already-applied
reviewed grants, and produces explicit edit plans/blockers for anything else.
There is no `ms * N`, generic numeric substitution, or blanket auto-apply path.
Missing baselines and unsupported APIs remain blockers, not completed migrations.

Classification is conservative:

- `converted`: direct work option on a reviewed work-capable API; no mixed clock option.
- `already-counted`: explicit inventory clock evidence (not a conversion claim).
- `watchdog-only`: imported native child-process `timeout`, preserved unchanged.
- `needs-reviewed-support`: everything requiring further clock/API/baseline review.

In particular **an empty `budgetGrants` list is not a watchdog certificate**.
The prior classifier mislabeled positional internal `withWall` deadlines this
way. Every such call is now a blocker until reviewed, including counted-domain
walls. Nested callbacks' work grants cannot authenticate the containing call.
Moved calls require a unique named-test AST anchor; ambiguous/missing calls fail
closed. The historical `0501-manifest.json` is retained as prior evidence, not a
current result. The retained `0503-preintegration-*` files are the completed
`20261116-230145-liinau` snapshot: 509 candidates, 7 reviewed literal grants,
28 preserved native watchdogs, and 474 review blockers; its 8 audit tests and
owned lint passed. `0503-snapshot-evidence.json` states its exact freshness
limits. In particular, CLI-dependent literal grants are not dynamic proof that
the older submitted CLI honored them.

`0503-manifest.json` and `0503-codemod-plan.json` must still be regenerated from
the final integrated source, with actual CLI and new cancellation controls.
Recovery now permits Main-owned cheap diagnostics; strict release gates and
broad profiling remain held until the candidate is assembled. No local compute
fallback or unapproved helper admission is permitted. See
`FIXTURE-DISPOSITION.md` for public-positive/model-only contracts.
