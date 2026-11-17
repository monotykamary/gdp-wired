# Development evidence — agent consultation prototype

Research only. No surface-semantics release, native-parity acceptance, production
MCP registration, reader removal or native evidence-label change is authorized by
these tests. The accounting profile is provisional; results prove the tested
adapter behavior, not a universal compute/memory bound.

## Preserved iterations

| Run | Result | Actual scope |
|---|---|---|
| `20261116-165236-by0mkj` (`runs/agent-tools/dev-01`) | pass |7 unit tests;18 real JSON-RPC calls, two families;1.95s payload /28.2s batch |
| local `dev-02` attempt | no admission | Invalid edited job-manifest JSON; corrected with JSON serialization. |
| `20261116-165547-t3vw9y` (`runs/agent-tools/dev-02b`) | failed | Focused type check and commitlint passed;8/9 tests passed. Existing engine correctly refused overflow, but the test expected the adapter's redundant trace-check code. Removed that redundant check and classified the existing RangeError.12.1s payload /79.5s batch across two jobs. |
| `20261116-165800-wbtxvn` (`runs/agent-tools/dev-03`) | pass | Focused strict TypeScript check, commitlint,9 tests /23 assertions,23 JSON-RPC calls; genuine helper inference.13.15s payload /29.2s batch after combining jobs. |
| `20261116-165909-d2i3gb` (`runs/agent-tools/dev-04`) | pass | Exact `30ae4387b` source hashes matched; strict type check, both commitlint bodies,9 tests and23 RPC calls passed.35.85s payload /96.8s batch. |
| `20261116-170134-zxk453` (`runs/agent-tools/dev-05-fast`) | pass | Final dependency-free runtime gate:10 tests /26 assertions,23 RPC calls, exact source hashes matched.2.89s payload /64.4s batch. |
| `20261116-170134-9d4cd6` (`runs/agent-tools/dev-05-static`) | pass | Final focused strict TypeScript check and all three commitlint bodies passed; exact source hashes matched.13.48s payload /82.2s batch. |

All original receipts remain in their distinct `runs/` directories. No failed run
was overwritten. The post-commit pass verified the bounded status cache and child-input error
handling. The later small wire-encoding fix adds an explicit bigint encoding and
refuses nonfinite results; its independent fast/static gates both passed.
Both final source manifests match the TypeScript and skill bytes committed as
`a5516535e4fffe8eee8b1b99cab3feb8362edecc`. The gates captured an uncommitted worktree
based on30ae4387b; this is a verified file-hash binding, not a claim that their
whole source snapshot was already the later Git commit. Exact final artifacts
are retained in `receipts/dev-05-fast/` and `receipts/dev-05-static/`.

## Observed behavior in dev-03

- Every tool exercised through a real local stdio MCP process on request-budget
  and permit-slot families; the latter also includes a conservation-accounting
  variant. The client is deterministic scripted code, not an LLM or network call.
- Checked proofs only: both `proven` and `checked` are required. A repeated proof
  in a fresh worker returns identical result/counters/work.
- Broken variants produce one-step reachable traces with the original variable
  names. They are shortest within the explicitly bounded existing search, not
  globally minimal.
- New-vs-old checks identify the newly broken law and a real bounded behavior
  difference; both refinement invariant and admissibility proofs are queried.
- Inference discovers `held + released <= acquired` for permit accounting and
  checks it jointly with `released never exceeds acquired`; pasteable source
  includes the support set.
- Zero work, zero API admissions and mid-inference exhaustion return typed
  refusals, never proof. The sticky existing refusal boundary is retained.
- A proof completes when Date.now/performance.now throw. An overflowing runtime
  calculation receives `numeric-range-refused`, never a bogus counterexample.
- `status` refuses supplied labels and unknown revisions; checked model proofs
  do not imply native `conformance` / `harness-checked`.

### Iteration cost, not a reasoning deadline

The two-job pass approached a minute due to batch overhead; the subsequent gate
was combined onto one warm worker. Dev-03 took29.2s end-to-end,13.15s payload.
In dev-03, individual MCP calls (including fresh child startup) were about53–183ms; actual
helper inference took768ms. Dev-04 had9.1s total in its MCP conversation (the helper
call3.39s) and2.77s dependency install; the overall batch still took96.8s. Therefore
the default edit/test job is now dependency-free; full static/setup checks are a
separate explicit verification job, not part of every unit iteration. These are observed timings only. No wall time is used
as a solver budget, a refusal reason, or a truth criterion.

The final fast gate reduced payload time to2.89s, but its complete batch still
took64.4s:61.51s outside the recorded job. The static gate took13.48s payload /82.2s
batch. Admission, transport and collection were not individually timed, so the
remaining overhead cannot honestly be assigned to a single scheduler stage.
No further native admissions were made to chase this. The runtime loop is now
small and install-free; sub-minute end-to-end service is **not established**.
