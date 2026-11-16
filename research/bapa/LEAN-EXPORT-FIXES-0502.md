# Lean export fixes for 0.50.2

Development base: published `70b660443`. This is not a strict release receipt.

## Fixes

- `fd74503cd`: parse the exact native Lake `info: file.lean:line:column:` envelope when auditing axiom answers. Arbitrary diagnostic prefixes remain unrecognized. Planted axioms, `sorryAx`, duplicate required theorem answers and missing answers still refuse.
- `bf5b03725`: unfold each cyclic law's separate `C` definition as well as its `MLaw` wrapper. Covers inferred machines, histories and explicitly supplied cyclic bridges. Statements, proof certificates, kernel checks, original assertions and search budgets are unchanged. Noncyclic inline definitions keep their existing simp list.

## Exact job recovery

The commands below are unchanged from the 0.50.1 canonical suite. Development-only wrappers install pinned dependencies and retain complete native compiler output before the original commands' `tail`/`grep`; they do not alter checks or return codes.

| Original known-failure job | Passing development batch |
| --- | --- |
| lean-package-0 | `20261116-185009-x6ha8k` |
| lean-package-1 | `20261116-185009-x6ha8k` |
| lean-package-2 | `20261116-185348-0bw8br` |
| lean-package-3 | `20261116-185348-0bw8br` |
| lean-cyclic | `20261116-185348-0bw8br` |
| lean-cycles | `20261116-185348-0bw8br` |
| lean-cycles-loops | `20261116-185348-0bw8br` |
| lean-protocols-sync | `20261116-185348-0bw8br` |
| lean-jev-fabric | `20261116-185348-0bw8br` |
| lean-ksteps | `20261116-185348-0bw8br` |

Each retained `COMMAND-RESULT.json` has code 0, no signal and no error. Local evidence: `/tmp/bapa-0502-control/runs/lean-probe-{02,03}/<job>.files/`, including full compiler logs and generated sources where captured. Both batches are interactive, not strict-once and not performance comparisons.

The focused export/axiom regressions, full typecheck and focused lint passed. The suite-presence check was skipped in those remote snapshots because `supercomputer/` is normally excluded; the policy-retirement check separately supplies the exact suite manifest.

## Policy change

Retire exactly these ten jobs from `scripts/release-ci/known-failures.json` and add them to `requiredPass`, so the validator rejects attempts to reintroduce their exceptions. The list shrinks from 22 to 12. Keep baseline provenance and every remaining exact signature unchanged. The frozen 0.50.1 policy and raw release receipts are not changed.

## Remaining work (not declared out of scope)

- `lean-keyed`: an interactive replay stopped before export while searching for the NICT rank. Its original known failure was the outbox corollary's opaque definition; the replay's distinct search unknown is preserved. Resolve the deterministic-work dependency rather than hiding it with a larger wall budget or a blind retry.
- `lean-protocols-wo`: the original consensus-without-decide search returned unknown before export. This is not the Lean unfolding defect.
- Ten non-Lean jobs: independent exact-test classification is in progress. Native-source interpretation refusals, actual cyclic translation gaps and search-budget failures must remain distinct. No assertion or source-law validation is weakened.

Original failed development batches `20261116-184514-49htp7` and `20261116-185009-x6ha8k` remain preserved. No full-suite or 0.50.2 release-readiness claim follows from these targeted passes.
