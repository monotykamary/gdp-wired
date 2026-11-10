LAW CROSS-CHECK — RELEASE GATE PENDING

Branch `claude/law-crosscheck`, from `5bbf4bf7`. The native-law core has passed 13 focused regressions, typecheck/lint and commitlint on Boat (`runs/law-crosscheck-focus-v4`). CLI behavior, historical controls, the restored fuzzer, and the full release gate remain pending. This is not GATE GREEN. See `runs/LAW-CROSSCHECK.md`.

---

Historical base report:

CI AUDIT FOLLOW-UP — GATE PENDING

Branch `claude/fix-ci-audit`, from local main `8214a543bc44e88d979f9e4457d7370e7e3c122b`.

B1 release impact first: **0.46.0–0.47.0 are affected with default replay ON**, confirmed against every stable published tarball and the actual bundled CLIs. A guarded law over a numeric Map.get result proves despite native undefined subtraction being NaN. The 0.45.0 parser refuses business-day law syntax. The standalone variant starts at 0.47.0; the guarded class variant establishes the earlier boundary. Four all-64 matrices retain both positive and contrary controls, with no unclassified results. The calendar guard now rejects optional operands in both readers; default-replay tests and a class-guard mutant pass. Sanitized evidence: `runs/ci-audit-b1-releases.json`; private advisory: `private/handoff/advisory-extractor-calendar-20261110.md` in the main worktree.

P2: both typed and lazy record argument roots now use `Exec.id`, independently of their display name. Regressions cover named/destructured arguments in both orders, all four boolean inputs, a false cross-argument law with replay disabled, and a valid identity law. A mutant restores the old shared root ID.

B2: truthiness narrowing now preserves optional payloads in falsy arms for every reader, not only standalone. Added boolean-false/numeric-zero coverage for both `if (v)` and `if (!v)`, a replay-disabled false-law check, default replay, and a mutant. This is a distinct predicate bug from strict null/undefined narrowing: truthiness conflates present falsy values with absence. All 64 published stable tarballs were integrity-checked: 36 lack the frontend; all 28 versions from **0.24.0 through 0.47.0** reproduce the false proof with replay disabled, and default replay rejects the demonstrated mismatch in every affected version. Version receipts: `runs/ci-audit-b2-releases.json`; private advisory: `private/handoff/advisory-extractor-falsy-map-20261110.md` in the main worktree. The earlier strict-null advisory starts at 0.26.0, so this is not the same defect.

C1: chose the requested explicit-contract option. README, the CI guide, API comments, and emitted extraction notes now restrict standalone record arguments to immutable plain-data snapshots with stable own data properties; accessors and Proxies are excluded despite matching TypeScript types. Notes are covered for scalar and record-returning functions, with an out-of-contract accessor control and a notice-removal mutant. This is documentation of the modeled boundary, not a claim to detect arbitrary runtime Proxies.

N1: every returned record field now has a canonical method-scoped `result.<field>` name, including `value` and `failed`. Standalone records do not masquerade as bare failure channels. Legacy class/Effect envelope aliases are retained and explicitly documented; tests cover correct/false laws, both reserved fields, method scope, and bare standalone failure refusal. A mutant removes the canonical names.

Private replay on exact `f338c30cd90e9bbb8d4ce32cbe8934fe45cc3715`: **all 20 laws proven, no lost laws**, with replay on. All 212 finite cases match, all 24 branch arms are covered, and each of four decisions passed 2,400 start-state requests plus 400 drawn-state checks. Sanitized evidence: `runs/ci-audit-private-replay.json`; private full receipt: `/tmp/gdp-ci-audit-replay-f338c30c/plain-laws-replay-on.log`.

Initial B1-focused run on `b6874c2c`: **33 passes / 1 fixture failure**. The explicit optional class-return fixture was refused by the existing class reader before reaching the calendar law. Commit `69401de0` replaces it with the supported `Map.get`-returning class path, without weakening the calendar refusal assertion. Original receipt: `runs/ci-audit-b1-focus/b1-regressions-mutants-check.log`.

Focused verification on exact `f338c30c` passed: all boundary tests, **all eight mutants caught by test failures**, source restored, check/typecheck/lint, and commitlint for all six commits. Receipt: `runs/ci-audit-focus-f338c30c/audit-regressions-mutants-check.log`; summary: `runs/ci-audit-focused.json`.

The final 17-job small gate is running at submission class on Boat, with exclusive placement and all seven full-suite shards in the existing per-unit mode. No assertion or timeout is changed. The B1/B2 release-range audits and private advisories are complete. No new GATE GREEN is claimed here.

The previous P1 report and receipts are preserved in commit `bca086ad` (`runs/REPORT.md` there). The coordinator's merge `8214a543` did not carry those tracked reports; this is a new follow-up report, not a relabeling of that old gate.
