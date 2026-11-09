CI AUDIT FOLLOW-UP — GATE PENDING

Branch `claude/fix-ci-audit`, from local main `8214a543bc44e88d979f9e4457d7370e7e3c122b`.

B1 release impact first: all 64 stable published tarballs integrity-checked on Boat. The standalone calendar case is a confirmed default-replay false proof in 0.47.0 (both API and actual bundled CLI); earlier releases refuse that standalone shape or lack its frontend/law API. Class-reader range confirmation is in progress before the private advisory is finalized. The existing calendar guard applied only to standalone extraction; it now rejects optional calendar operands in both TypeScript readers. Added default-replay tests for null/undefined and both operand directions, and a class-guard mutant.

P2: both typed and lazy record argument roots now use `Exec.id`, independently of their display name. Regressions cover named/destructured arguments in both orders, all four boolean inputs, a false cross-argument law with replay disabled, and a valid identity law. A mutant restores the old shared root ID.

B2, C1, N1, private-law replay and the final small gate remain pending. No new GATE GREEN is claimed here.

The previous P1 report and receipts are preserved in commit `bca086ad` (`runs/REPORT.md` there). The coordinator's merge `8214a543` did not carry those tracked reports; this is a new follow-up report, not a relabeling of that old gate.
