# BAPA first slice: evidence and limits

This is **not completion of SECTION-64 or migration of the 29 ports**. It is one-key finite guarded quantification plus a symbolic-size Venn-region showcase. No protocol source or old claim run was changed.

## Semantics and API

```ts
import {nat, rule, sizedSort, when} from 'gdp-wired'
const r = rule('bounded-read').params({size: nat}).state({ok: 1}).maps({A: 0})
  .flags(({size, A}) => ({allZero: sizedSort('Item', size).every(k => A.at(k.times(2)).eq(0))}))
  .step(({allZero}) => ({ok: when(allZero, 1, 0)}))
```

`sizedSort(name, size).every/some/has` uses `[0, size)`, including the empty domain. Size depends only on immutable natural parameters. Runtime numbers must remain safe integers; there is no semantic domain cap of 64. Arbitrary arithmetic, tuple and function reads in a quantifier-free body are supported.

The `finite` label is an operational annotation, **not a new trusted axiom**. The literal formula remains `forall k, k < size -> body`; existential is its negated-universal dual. `finiteBound` checks that shape before the finite runtime path or scope exemption. `closing`, `assumed`, proof tags and certificates are unchanged. Nested/multi-sort quantifiers, metadata-based existential witnesses inside finite universals, finite step laws and finite bulk writes are deliberately refused.

The interpreter and closure compiler enumerate exactly with cancellation. Standalone generated finite modules require a fourth cancellation callback to `step`; `loadJs` supplies the normal runtime cancellation bridge. `fastStep`, BMC, request quotient, small-model screens, speculative domain compilation and GPU paths refuse unsupported marked inputs. Interchange 1.1 refuses to erase the marker. Full census: [BAPA-CONSUMERS.md](BAPA-CONSUMERS.md).

## Verified receipts (all work on boat, fetched by batch ID)

| Evidence | Batch | Artifacts / outcome |
| --- | --- | --- |
| Lean semantic bridge, freshness, Venn identities, empty domain; six false-theorem mutants | `20261114-051037-fctuhv` | `runs/bapa-lean-04-fetch/bapa-lean-foundation.files/`; passed. Foundation committed as `1e5ce5951`. |
| Legacy baseline | see `runs/bapa-baseline-01-fetch/` | 40 tests passed; 271655 assertions. |
| Actual marked machine exports: arithmetic, function body, empty sort | `20261114-051501-co11c6` | `runs/bapa-export-01-fetch/`; all three compile against unchanged Sets checker. |
| Finite + existing kernel/runtime/quotient/export suites | `20261114-051606-ixrvea` | `runs/bapa-final-01-fetch/`; 69 passed, 5 skipped, 0 failed (12 files). Package typecheck in this earlier batch failed on baseline's missing process declaration; fixed below. |
| Count and count-machine certificates/mutants | `20261114-051659-7n326v` | `runs/bapa-count-01-fetch/legacy-count-mutants.files/`; 94 passed, 0 failed. |
| Six automatically derived finite-region identities + three marked machines, all Lean exported | `20261114-051659-7n326v` | `runs/bapa-count-01-fetch/finite-regions-lean.files/BoundedExamples.lean` and `.log`; all passed. |
| Type-aware lint of all 16 changed source/test files | `20261114-051919-jza6se` | `runs/bapa-hygiene-01-fetch/changed-source-lint.files/lint.log`; 0 warnings, 0 errors. Initial commitlint invocation lacked the shipped Git metadata; file-backed stdin retry and lint both passed in `20261114-051944-uko8r0`, fetched under `runs/bapa-hygiene-02-fetch/`. |
| Full repository, package-build and scoped strict typecheck; latest finite tests | `20261114-051756-quo482` | `runs/bapa-typecheck-02-fetch/`; all three typechecks passed; 11 finite tests passed. |

Every exported theorem's axiom receipt lists only `propext`, `Classical.choice`, `Quot.sound`; jobs use `scripts/lean-gate/lean`. No `sorry`, new axiom or native-decide trust shortcut.

`lean-kernel/bounded-regions.ts` derives count-cut coefficients from the requested partition expressions and lets ordinary proof search build the trees. It proves X/intersection/difference and S/intersection/difference partitions, both subtraction identities, intersection bounds and the union bound for **symbolic size**, not a fixed 64-element instance. Removing all count instances invalidates each generated certificate. These are the MLDR-style xNotS/sNotX/xAndS identities, not a claim that MLDR itself has been migrated.

## Reviews, baseline dependency, remaining gate

- Fable reviewed the plan and consumer census; its compact-spelling census gap was fixed, including explicit request-quotient refusal. No further census findings as of 2026-11-14.
- D's preliminary read found no definite new kernel-soundness defect, but required generated-runtime cancellation, boundary/renaming tests and actual Lean exports; those are now implemented and verified. Final D acceptance remains pending.
- Main initialized pinned vendor dependencies and requested the approved baseline fix `be1f5049`; it was cherry-picked as `ae51c59c1`. Earlier typecheck failures are retained rather than hidden.
- Canonical 29-port profile `a5f077dc` comparison is pending the exact end-of-slice runner/receipt recipe from D (Main identified batches `20261113-235638-qnd6a8` and `20261114-002014-3vtaev`). It must include MLDR and run once on the final slice. Historical VERIFY-ALL is not silently substituted.
- No existing port has been migrated to sized sorts. No universal cap-removal, 29-verdict preservation, or full SECTION-64 completion claim is made before those gates.
