# Custody

This lane created no release evidence and changed no production, assertion, or budget source.

## Completed development observation

- **Native batch:** `20261116-185815-v0cjtw`
- **Local retained run:** `runs/bapa-0502-slowdown-development-3-70b660443/`
- **Result:** one job, exit 0, 431.77 s.
- **Placement:** `large`, `AMD Ryzen 9 9950X 16-Core Processor`, 6/8 vCPUs pinned, `exclusive: true`, `co_tenants: 0` (`raw/placement.json`).
- **Inputs:** exact immutable commits fetched read-only inside the VM: `70b6604435910194a91ed2749f4f03cb2e116d62`, `c149b540bc28f9ec752cf9e5f6f299d69613d885`, `96bf476ed811081ba3d3084ab11ebe19351cd27d`, and `c08bb385bbb1afc8dbf6ce1fc8aa8d838b9eb3a5`.
- **Raw compact data:** `raw/OBSERVATIONS.jsonl`, `raw/SUMMARY.json`, `raw/environment.txt`. Full stdout/stderr remain in the native run directory, not this source tree.

## Retained non-results

1. `20261116-185204-zo2u8w` — terminal code 128 before data: the source capsule has no `.git`, so the first worktree implementation failed after `bun install`. Read-only recovery: `/tmp/bapa-0502-control/recovered-slowdown-185204/`; its tiny logs are retained there. It is not timing evidence.
2. `20261116-185449-ru35rh` — terminal code 1. The first 70 sample completed, then the c149 direct observer ran a cold renamed policy call and did not match the test's original-then-renamed order. Its partial pair is excluded. Recovery: `/tmp/bapa-0502-control/recovered-slowdown-185449/`.
3. `20261116-190701-gloscs` — full capsule `tsc -p .` is blocked by missing `vendor/gdp-ts` and `vendor/handwired` in the source capsule; unrelated to this lane.
4. `20261116-190859-zgnivr` — targeted `tsc` follows `runner.ts` into existing core/Lean sources and reports pre-existing narrowing diagnostics. The successful development profile dynamically executed every added runner/instrument/shell path and all 24 named assertion tests passed. Both check failures and logs are retained under `/tmp/bapa-0502-control/recovered-slowdown-check*`.

All owned remote jobs are terminal; no process or admission remains active.
