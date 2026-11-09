CI AUDIT FOLLOW-UP — GATE PENDING

Branch `claude/fix-ci-audit`, from local main `8214a543bc44e88d979f9e4457d7370e7e3c122b`.

B1 release impact first: all 64 stable published tarballs integrity-checked on Boat. The standalone calendar case is a confirmed default-replay false proof in 0.47.0 (both API and actual bundled CLI); earlier releases refuse that standalone shape or lack its frontend/law API. Class-reader range confirmation is in progress before the private advisory is finalized. The existing calendar guard applied only to standalone extraction; it now rejects optional calendar operands in both TypeScript readers. Added default-replay tests for null/undefined and both operand directions, and a class-guard mutant.

P2: both typed and lazy record argument roots now use `Exec.id`, independently of their display name. Regressions cover named/destructured arguments in both orders, all four boolean inputs, a false cross-argument law with replay disabled, and a valid identity law. A mutant restores the old shared root ID.

B2: truthiness narrowing now preserves optional payloads in falsy arms for every reader, not only standalone. Added boolean-false/numeric-zero coverage for both `if (v)` and `if (!v)`, a replay-disabled false-law check, default replay, and a mutant. This is a distinct predicate bug from strict null/undefined narrowing: truthiness conflated present falsy values with absence; release range verification is running separately.

C1: chose the requested explicit-contract option. README, the CI guide, API comments, and emitted extraction notes now restrict standalone record arguments to immutable plain-data snapshots with stable own data properties; accessors and Proxies are excluded despite matching TypeScript types. Notes are covered for scalar and record-returning functions, with an out-of-contract accessor control and a notice-removal mutant. This is documentation of the modeled boundary, not a claim to detect arbitrary runtime Proxies.

N1, private-law replay and the final small gate remain pending. No new GATE GREEN is claimed here.

The previous P1 report and receipts are preserved in commit `bca086ad` (`runs/REPORT.md` there). The coordinator's merge `8214a543` did not carry those tracked reports; this is a new follow-up report, not a relabeling of that old gate.
