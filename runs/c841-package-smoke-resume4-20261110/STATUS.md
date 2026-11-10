# c841 package smoke — FAILED; local repair not yet runtime-validated

## Original pre-hold result

- Batch `20261110-132141-23nq9m`; task `c1ceb05f-b56b-4a16-86e9-4b2df86e4ce7` is terminal.
- **Native job exit 1** (`exact-candidate-package-consumer-smoke`); the outer scheduler/client process exited 0. The outer exit is not a package-test pass.
- Exact worker checkout: `c8411149d2c6c3c060a0665a79f10523b1281cbc`, tree `7f2e3d6269431482232d84a5460a412352c6751a`.
- Node `v20.20.2`, Bun `1.4.3`; 50.47 seconds of job time, 2,898.1 seconds of batch wall time. No fallback reported.
- The worker log reached the packed-package Node runtime checks, root CLI positive/broken TypeScript checks, and TypeScript consumer declaration check before failing in the separately installed CLI's Python test. Later standalone CLI and certificate stages did not complete.

## Failure and diagnosis

The old smoke required the Python `never past the cap` law to print proven and exit 0. The actual CLI reported `unknown`, `source translation unchecked: native source replay is unavailable or disabled`, and the wrapper aborted with `gdp-wired-cli check: a proven law exits non-zero`.

That expectation conflicts with this candidate's deliberate fail-closed contract: foreign frontends without the native-law journal return unchecked source results and exit 2. This matches `core/cli.test.ts` and `docs/ci-only.md`. Do not weaken the source validator to make the stale smoke pass. This diagnosis does not establish that the remaining smoke stages pass.

## Prepared repair, not a successful rerun

Commit `5f989777` changes only `scripts/smoke.sh`:

- Retains both positive and broken TypeScript cases through the standalone CLI, with exact exit expectations 0 and 1.
- Retains both Python examples. Requires exit 2, successful extraction, exactly one named law, `unknown`/`unchecked`, the respective positive/negative mathematical model verdict, and no source proof/run/certificate. Requests certificates and verifies none were emitted.
- Uses the supported TypeScript positive case for certificate acceptance and retains the tampered-certificate refusal check.
- Makes the root CLI broken-law exit check exactly 1 rather than any nonzero status.

Local `sh -n` and syntax-only parsing of both embedded JavaScript blocks passed. **No repaired runtime test has run.** No source-proof implementation, threshold, budget, canonical roster or scheduler code changed. The canonical proof/test candidate remains c841; the prepared release tip includes this separate smoke change and needs its own packaging validation.

After the coordinator lifts the submission hold, validate the actual prepared release tip and its tarballs on Node 20 and 24. Keep this original failed receipt unchanged. No new job was submitted in response to the failure.

## Original local receipt integrity

Raw files remain local ignored evidence; only this bounded report is committed.

| File | SHA-256 |
|---|---|
| `summary.tsv` | `52019bea3a6ca18f328bd6ec23d2a40f4d4625c541a3d36f4782bddedb6d79c7` |
| `exact-candidate-package-consumer-smoke.log` | `06f9dbdc83d5de047c276e33e5b9fb4cff9b1ba54814485816aedd8fcef0be68` |
| `placement.json` | `25c0825ece9a9cc9bac2a6de0945e5704d38fab98a195beb859da96c62306879` |
| `backends.json` | `94647931e8b97e06808e1c7f6b2549d1f5606965809f450e9405a54b7a61381b` |
