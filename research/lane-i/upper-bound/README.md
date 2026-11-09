# Research-only upper-bound census

Source production snapshot: `15eff72f04f74351b622b02d08e47bfb9dfdb131`. The original `run.ts` is observed after finite generation, at admission, with no supplied laws. The capture must contain exactly 34 laws and exactly one match for each requested helper. Each job verifies SHA-256 of all non-test TypeScript under `core/` and `kernel/` before any disposable edits.

Roster: Inv* (`star`), Inv2973-half (`half`), Inv1758 (`rows`), generated p1 (`p1`), safety (`safety`), each over actual `op` values 0..6, counted passes 0/1, and ceilings `on`/`off`: **140 independent jobs**, one exclusive large VM each, submitted together to boat's scheduler. No new production policy or law is installed.

Each shard keeps the captured full family; adds only the labelled operation equality to the machine's original assumption; checks STEP only; disables source-subset probes; and invokes a single counted pass with `1e12` units and a 30-minute cooperative wall. This is a conditional per-operation STEP result, never a complete helper or safety proof. The external watchdog allows 10 seconds for shutdown and kills only its own process if cooperative cancellation fails. Such output is censored, not unknown/proved. The whole batch may outlast 30 minutes because scheduling is not a measurement.

`on` leaves production local query/leaf deadlines unchanged. `off` removes the local finite numeric sub-deadlines, row/guard leaf caps, source reconstruction cap, focused recovery cap, and the proportional leaf allowance in disposable copies. Logical candidate widths, search depths and supported syntax remain as shipped. Exact before/after hashes and replacements are in `upper-patches.json` in the guest and `UPPER_PATCHES` log rows. Kernel source is not changed.

Metrics: `UPPER_RESULT` contains counted units, search and end wall, peak RSS (KiB), and the last observed leaf and its excluded violated-instance indices. Progress is persisted during trace callbacks, so a forced watchdog kill retains a lower-bound work observation (`UPPER_CENSORED`), explicitly not a final count. `UPPER_RESOURCE_BEGIN` adds GNU time's process RSS and wall. `closed` requires an ordinary kernel check, plus `UPPER_VERIFY` from a fresh process; a failed/missing verifier cannot count as closed. A symbolic SAT not validated by the finite model checker is unknown, not a certified counterexample.

Smoke: two 2-second star/op0/pass1 jobs, one per ceiling mode, exercise both installers, source checks, CPU labels, wall censorship and resource recording. They are not upper-bound results.

Artifacts stay under ignored `runs/lane-i/upper-bound/`; only compact reports and research source are committed.
