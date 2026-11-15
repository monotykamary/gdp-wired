# Section 66.8 — stage-local counted deadline refusal

## Authorization and ownership

Main t6 authorizes (a) A's read-only endpoint-kind observation on the original d5c44268 pin and (b) B's general DSL soft-deadline fix. This work is (b) only. A's probe is separate and must not contain the fix. K owns ledger-semantics source review. D owns independent review and the new execution GO. Calibration remains HOLD.

Base: d5c442685f5c11394c1ac99fa0568647290b0344 (Run A accepted pin). Worktree `../gdp-wired-trackM-soft-deadlines`, branch `track-m/soft-deadline-boundaries`.

## Falsifiable hypothesis

A locally exhausted counted stage must return its ordinary failure and let the caller continue, rather than leaking BudgetExpired to workVerdict. A root/ancestor or nonowned refusal must still abort. Full accounting and every native proof check remain on; counted results are remeasured at the new pin. This fix is not evidence that the 15 cases now prove.

## Source scope

- `core/work-admission.ts`: owned-deadline boundary, authenticated refusal-time ownership, unique failed-entry identity, separate pending fatal, isolated diagnostic copies. No budget/weight/counter reset.
- `core/dsl-deadline.ts`: legacy-preserving stage adapters.
- `core/dsl.ts`: 14 original explicit deadlines plus 7 supporting implicit/local-wall sites. See STAGES.md. Two cone catches stop swallowing nonowned BudgetExpired.
- Two new test files. Existing hard-boundary tests retained.
- No kernel, Lean, protocol-specific, flag-profile, rate, or allowance-size changes.

## Written controls; no execution yet

Focused full-profile command (remote only, after exact D GO):

```sh
GDP_WORK_FULL=1 bun test core/work-admission.test.ts core/work-capacity-boundary.test.ts core/work-deadline-boundary.test.ts core/dsl-deadline.test.ts
```

Legacy adapter control in a fresh process (all GDP flags unset except explicit full=0):

```sh
GDP_WORK_FULL=0 bun test core/work-deadline-boundary.test.ts core/dsl-deadline.test.ts
```

Also type-check under the repository's existing TS configuration/dependencies. This is a candidate gate plan, not an executed or authorized admission. Dependency preparation, exact source/input hashes, runtime pin, strict once/no retry, output custody, finite process limits and cleanup must be frozen in D's execution packet before launching.

Tests cover local continuation and remaining root, no ancestor poisoning, preexisting sticky errors, all ancestor/tied endpoint kinds, descendant mirrors vs foreign limits, nested owners, entry-before-body, unique IDs, later fatal after first soft, forged/foreign/stale errors, asynchronous callbacks, diagnostic aliasing, fallback errors, legacy unchanged behavior, and unchanged native kernel rejection. They do not claim all 21 call sites are dynamically exercised.

## Post-review gate

K source acceptance, then D source acceptance/GO for an exact packet. Run focused controls, then the 15 affected originals AND full MLDR at the accepted new pin under their prescribed measured profile. Old counts and results remain immutable. New work may differ, including MLDR. No calibration, W, aggregate performance or release claim follows from source review or a focused gate.

## Routing

Results/blockers append-only to `../MAIN-INBOX.md`. No GitHub writes. Retained prior full-run evidence and the unused JSC contingency remain untouched.
