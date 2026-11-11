# Strict Q1 refusal audit (test-only follow-up)

Runtime stays `bfe647cfd3b81e10c497ca4d5911a8097a02586b`.
The historical `5e52d5ee` source and receipts are retained. D correctly noted
that its 301,348 caught throws lacked semantic classification. None of that
count is treated as independently demonstrated guard refusal without this rerun.

## Source-bound authority

The frozen reference interpreter is file SHA-256
`03d69e7e9e768a7e6735294f819da90d965f73d72c4134ab9ef74715d36f51bf`.
The adapter verifies that hash, the single exact assumption-check expression,
and line **819**, then brands only the original `new RangeError(refused(m))`
constructed at that branch. Its condition, constructor, message and result are
unchanged. The two sampler hooks and this one exception-origin hook are applied
only to disposable extracted files, never to the working interpreter.

A class name or message is not an allowlist. The oracle's private identity map
must contain the thrown object from that source branch. Every other thrown
value is an `unexpected` outcome, recorded by class/message and then raised as
a failing audit. There is no generic RangeError exception. No precondition or
other declared-failure site is authorized in this audit; those counts remain
zero unless separately justified and source-bound in a future change.

The per-model and per-parameter histogram carries exception class, exact
message, interpreter hash/line/expression, guard-expression hash and count.
The independent summary requires zero unexpected outcomes and reconciles all
histograms, samples and prior counts.

## Controls and status

The final controls pass **9 tests /43 assertions**: injected TypeError, ordinary
Error, the genuine runtime BudgetExpired class, unexpected RangeError, forged
guard-message RangeError and a non-Error throw all fail closed. A wrong
successor and missing representative fail outside the refusal catch. Only the
source-branded assumption error is accepted.

The complete rerun passes on **29 models /49 parameter runs**, including all
18 nonvacuous models:

| Outcome | Count |
| --- | ---: |
| Skipped requests independently re-executed | 2,400,700 |
| Equal normal-return successors | 2,099,352 |
| Source-branded assumption RangeErrors | 301,348 |
| Unexpected errors | 0 |

Every per-model/per-parameter counter and canonical sample digest matches the
historical run. No other exception class or semantic failure origin occurred.
The independent summary validates each histogram, origin and total.

Receipts: `results/strict-full/` (batch `20261111-070956-0th2mv`),
`results/strict-audit/`
(batch `20261111-071713-bh7es2`), and `results/strict-final-tools/`
(batch `20261111-071426-bop0ds`). The final isolated type/lint gate is clean on
**1,856 files**. Commitlint also passed.

The original input custody auditor and native receipt remain byte-identical to
D's accepted copies: SHA256 `ac40bfab39d70b22f80c2339846cd2155a7f07b83ff96f0de42033fc80827952`
and `9aa5b6be6ba6a362719b4380c7c2767a408f6589c2129e8f03c8529fa4a55275`.
The original full bundles and new strict-run/type bundles are retained under
`runs/lane-i/quotient-input-custody/bundles/`; see `INPUT-CUSTODY.md` for limits.
This is a finite semantic audit, not a new timing, W or production proof claim.

No runtime, kernel, interpreter, budget, weight, whitelist or production
integration change is authorized or made by this Q1 repair.
