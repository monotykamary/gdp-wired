# Independent unified-lift review

Read-only reviewer `78174ca8f48a44c2b606d89ffdff57a4` inspected the production pipeline and supporting source/shape/audit code before the final release freeze. This is static review, not a native acceptance receipt.

## Findings and disposition

1. **Source fidelity: unsupported source SUM declarations in radix simulation.** The producer SUM semantics were checked, but the provided source was emitted as an `SMachine` without a corresponding source-SUM bridge. The route now explicitly refuses nonempty provided-source SUM declarations. A negative shape test records the boundary; final native/unit gates remain required. The accepted SDL fixture has no source SUM declarations.
2. **Apostrophe-bearing theorem aliases.** Source naming validation accepted apostrophes but the old quoted-name output parser could not read them. The parser now accepts embedded apostrophes while preserving multiline axiom lists, exact name matching, duplicate refusal and allowed-axiom checks. Added unit coverage and a native alias control (including wrong-proposition rejection); final verification remains required.

Validation after those repairs: immutable preflight `e61cb5c22` passed the whole-tree TypeScript/strict-lint gate (2,357 files, zero warnings/errors), 122 targeted tests, and native apostrophe-alias plus changed-proposition controls. Preflight `787c0f9f9` then passed the complete installed-Node package smoke and the portable-byte/legacy-export controls. These are pre-release gates, not the final 27-source acceptance batch.

No additional concrete blocker was found in the reviewed structural routing, terminal candidate failures, retained-family/public-law coverage, alias proposition equality, or project/hash binding. External provenance remains conditional on an independently retained capsule hash. No all-size or external-program equivalence conclusion follows from this review.

## Gate infrastructure notes

The first whole-tree diagnostic snapshot had empty submodule directories, so TypeScript could not resolve research imports from `vendor/gdp-ts` and `vendor/handwired`. This is not fixed by excluding those files or loosening TypeScript. Subsequent full gates must mount tracked-file archives of the exact gitlink revisions:

- `vendor/gdp-ts`: `0b6ebeeec827b05210f3acfa4149a70dda9a0de5`
- `vendor/handwired`: `d47141cce2caf5b86b0c2c0c372a5174f424bc15`

The archives are made from the existing retained repositories, without a network fetch, checkout mutation, local dependency caches or credentials. Supercomputer input manifests bind the shipped archive contents. The initial package smoke also needed to create its new temporary fixture parent directory; this setup error is retained in the diagnostic logs.
