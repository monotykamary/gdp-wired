# Timeout diagnosis — original pure lifecycle batch, no rerun

## Conclusion

The requested 60 seconds was lowered to a **30-second native workload limit** by
an explicit `timeout - 30` conversion in `boat.job_items`. This is the mechanism
behind the apparent mismatch, not a claim that all layers promised a 60-second
workload. The native agent's near-limit kill normalization explains the observed
worker exit 124 / 30.1 seconds and `timed out after 30 s` text.

The exact install/driver phase active at expiration is **not recoverable from the
retained log**. In particular, this diagnosis does not establish that dependency
installation, the positive proof, or an inner driver timeout caused the delay.
No separate diagnostic job is needed to distinguish the outer timeout mechanism;
none was launched. The original proof job was not rerun.

## Evidence and provenance

Original batch `20261104-111004-adr95v`; uploaded tree `4a397ad58a2a`; frozen input
manifest `96395c0cee65d3fe96a4a251c5722caa722c8811da5538beec7feef4399e16da`.
The original worker log/summary/placement, source inputs and failure receipt remain
unchanged. The rendered RESULTS.md paragraph had literal backslash-n sequences;
only those escapes were replaced by actual line breaks.

Installed tool commit: `34dd8877519ab8811935d28755e249424de319c9` (clean checkout).
Retained scheduler code snapshot: `2d5e961da4d8`. The scheduler startup log records
that code at 09:26:14, and read-only process metadata for its PID 44010 records
2026-11-04 09:26:14. The scheduler log records this batch at 11:10:17. The relevant
installed files, retained snapshot files and Git blobs were compared byte-for-byte
by SHA256. Their copies and hashes are in `runs/astra-mac-timeout-diagnosis/`.
These are **later source/provenance observations**, not a reconstructed native
submission-time manifest or a recovered worker `spec.json`.

The local per-batch scheduler queue files are no longer present. This matches
`scheduler.close` (lines 877–897), which removes `.json`, `.rows`, `.placed` and
`.logs` after delivery. No provider call or shared-state mutation was used to
recover them. The raw native spec and exact historical worker binary hash are not
independently attested by the retained original packet.

## Exact source path

Line references below are to the frozen tool source copied in the diagnosis packet.

1. `__main__.py:25–35,47–59`: reads the jobs JSON; takes the repository run prefix;
   passes the specification to `fanout.run_jobs`. Repository prefix is only
   `export GDP_CYCLIC_LOG=1;`. `supercomputer/hooks.py` defines no `job_item` hook.
2. `fanout.py:171–187`: passes the selected jobs to `boat.boat_jobs` without
   replacing their timeout. This batch used boat; no fallback was recorded.
3. `boat.py:2669–2700`: groups jobs by requested CPU/memory/timeout, then sets
   `it['limit'] = timeout - 30`. Thus **60 - 30 = 30**, before scheduler submission.
   The code inspected does not explain the policy rationale for this subtraction;
   no rationale is inferred here.
4. `boat.py:2295–2310`: sends those items in the scheduler submission payload.
   `scheduler.py:1345`: filters scheduling metadata and adds CPUs/run name;
   **`limit` is retained**, not recomputed.
5. `scheduler.py:1361`: sends the start via native `vtick` with `wait:0` and an
   RPC timeout of 60 seconds. `boat.py:1088–1156` applies transport/socket deadlines
   and optional RPC fallback; it does not convert the spec's workload limit.
   This RPC deadline is **not** the workload's runtime allowance.
6. `agent.py:1078–1092`: `vtick` passes the start spec to `start`.
   `agent.py:964–985`: writes that spec unchanged to the job's `spec.json` and starts
   its runner. These describe the pinned implementation; the original spec file
   was not recovered in this review.
7. `agent.py:1145–1146`: wraps the shell workload with
   `timeout -s KILL str(int(spec['limit']))`. It encloses the complete shell command,
   including `bun install ... && bun .../run-review.ts`.
8. `agent.py:211–227,1198–1205`: `Outcome.code` maps exit 137 or -9 at/near the
   native limit to 124. For that normalized result, the agent replaces the stderr
   file with `timed out after {spec['limit']} s`. This matches the retained result
   and also explains why absence of inner stderr is not evidence of no inner work.

## Inner budgets and remaining uncertainty

| Layer | Configured limit / meaning |
|---|---|
| Jobs JSON | 60 seconds, input to the client conversion |
| Native whole shell | 30 seconds, derived by `job_items` |
| Start RPC | 60 seconds to obtain transport response, not job runtime |
| `bun install --silent` | No separate limit; inside the same native 30 seconds |
| Pure finite probe | Driver `spawnSync` timeout 5,000 ms |
| Positive CLI source check | Driver `spawnSync` timeout 25,000 ms |
| Broken-control CLI check | Driver `spawnSync` timeout 12,000 ms |
| CLI `--ms 2000` | Proving budget, not a global whole-job deadline |
| Certificate rechecks | No separate driver timeout; still under outer native limit |

The sequential child ceilings alone total 42 seconds, before install, driver load,
source checks and final certificate processing. They therefore do not fit a worst-
case 30-second native allowance. They are ceilings, not measured phase durations.
The driver captures child output and emits its aggregate report only after those
phases, while install is silent. Thus the retained output identifies the native
cutoff but not the active inner phase. An inner timeout could have occurred first;
its absence from the final overwritten stderr cannot rule it out.

## Disposition

No installed scheduler/provider source or configuration was changed. No limit was
bumped. No diagnostic or proof job was launched during this diagnosis. No lifecycle
signal experiment or live provider control occurred.

Any authorized future diagnostic must be separately named and fit the effective
native allowance; report immediately flushed stdout phase markers before/after
install and driver phases, because normalized timeout may overwrite stderr. It
must not reconstruct or upgrade the original result. A future proof attempt needs
explicit approval and budgets that account for this conversion; changing 60 to 90
would increase the requested cap and is **not authorized** by this diagnosis.

The original result remains a failed execution with **no proof verdict**, no
retained proof certificates and no observed completed broken-control replay.
