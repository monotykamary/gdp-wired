# Final Section 10 validation

All work ran on **bx_25xas5gt**, exclusive eight pinned vCPUs, the same calibrated
large VM as T-10A, implementation probes and all six family runs.

- TypeScript and type-aware lint pass (0 warnings/errors).
- **251 tests / 1,208 assertions** pass across 34 files: the production recovery,
  focused and transport suites plus six independent gate-audit tests.
- The independent auditor verifies six complete processes, all 30 law verdicts,
  exact baseline commit, canonical fixture SHA-256, unchanged kernel/harness
  flags, every reported work triple and median/max, and the negative gate status.
- The candidate still checks 3/5 in every repeat; family walls are 63.009,
  67.076 and 62.618 seconds. This is **not a Gate 1 pass**.
- `audit.json` is the structured audit also present verbatim in `validate.log`.

The measured production commit is **192ebbe2**; subsequent changes are audit
code, tests and evidence only. No later gate or original generated-family
harness ran. The first final-validation attempt is retained in v1: it stopped
on audit-helper typing before running tests. The corrected v2 job exits zero.
