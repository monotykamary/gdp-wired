# Reserved surface binders (2026-11-16)

Supersedes the admission-only fix `c9978b17b`; no kernel or Lean edit.

## Confirmed false proofs on c9978b17b

* `params({'k$1':nat})`, initial parameter `k$1=0`, law `everyKey(k => k.eq(env['k$1']))`. The original law is false at key 1. `everyKey` allocated the same spelling as the user parameter before `prenex` saw it. Lowered law was `key$1 = key$1`; verdict **proven=true, checked=true** (451ms process).
* `params({'s$1':nat})`, initial parameter `s$1=0`, law `someKey(k => k.eq(env['s$1']).and(env['s$1'].eq(2)), 2)`. Original predicate is false for every key because the free parameter is 0, not 2. Verdict **proven=true, checked=true** (131ms). Without the explicit witness the prover did not find one; that was not evidence of safety.

Both are also present in the older lowering; the universal was reproduced on `c08bb385b` (134ms). Separately, the known nested-map collapse fails the old release (149ms) and is correctly refused by `c9978b17b` (136ms).

## Fix

Surface quantifiers, each-writes, and least keys use `?kN`, `?keyN`, `?sN`; value existentials use `?someN`. Later-request marks use `?stepJ:name`, never user spellings. Rule declaration validation rejects the namespace before any callback can capture it. A lexical free-variable guard rejects reserved free variables, including escaped bound Terms and forged temporal marks before markedE runs. Valid generated after-state and current request marks are explicitly allowed only in their temporal context.

The unchanged kernel also rejects reserved **bound** names. `core/dsl-binders.ts` therefore performs a final capture-avoiding alpha encoding: collect every declared and syntax name first, assign unused `gdp$bound$N` aliases, and replace exact bound identities (not JSON substrings). A user can declare `gdp$bound$1`; the adapter simply chooses another alias. Machine and law scopes are separately encoded. Existing AST substitution and nested-universal refusals remain.

## Other leads

* Generated law-key collisions now retain the free variable and are refuted rather than captured.
* The `2:u` parameter is **refused** by the existing reserved-name policy, now enforced earlier in the DSL too. There is no confirmed temporal user-declaration soundness bug. A forged raw `?step9:u` must also be refused before renaming.
* Duplicate param/input names are correctly refused. `distinct()` alone is not the whole validation boundary; kernel `scope()` already validates spellings.

## Verification actually completed

* `core/dsl-binders.test.ts`: **15 pass / 0 fail**, 386ms. Covers both false proofs, old generated-name spellings, encoded-name collisions, input/state/map names, positive machine flags and each writes, valid k-step marking, forbidden colon names, escaped/raw reserved variables, duplicate declarations, quantified decisions, keyed leadsTo, and existential witness metadata.
* `core/prenex-admission.test.ts`: **9 pass / 0 fail**, 476ms. Two allocation-number assumptions were replaced by semantic collision/alpha assertions.
* A bounded local invocation of the existing `core/quantifiers.test.ts` passed its first four tests, then hit the external seven-second deadline. **Not a complete pass.** No full-suite, typecheck, lint, or focused boat result is claimed.
* Commitlint was attempted with `bunx --no-install`; no cached CLI exists. It remains in the HELD focused job, not reported as passing.

Raw short-test receipts: `research/binder-local-receipts.json`. `research/binder-focused.jobs.json` is source only. Admit it once and only after Main says the scheduler is fixed; use controller=1, no-build=1, strict-once/max-attempts=1, one waiter, fetch receipts, and record the immutable source commit and compiler/runtime versions. The focused job checks types/lint, all relevant core suites, example imports, and commitlint. It does not authorize a publish or broad native rerun.
