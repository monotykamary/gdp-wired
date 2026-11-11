# F3 blocking-loop capability probe — not a complete sampler

A timer on a blocked synchronous main thread is insufficient. This probe uses
a worker-thread inspector session, shared progress memory and native CPU
samples. It succeeds only if the profile contains the **named main-thread
blocking function** and is delivered before that function returns.

Receipts:
- First attempt `20261110-201620-j7x0sm`: Node v20.20.2 exited 13 during
  inspector startup. Bun 1.4.3 appeared to pass with a module/worker stack;
  that was not adequate evidence of observing the blocked main thread.
- Strengthened control `20261110-201744-s9kwtn`: keepalive prevents premature
  inspector startup exit and the named-loop condition rejects wrong-thread
  traces. Node passed: 25 recent samples, `mainThreadSilentLoop` in the stack,
  received while blocked. Bun failed: zero samples, no main-thread stack.
  Both original failures are retained, not replaced by the successful case.

This probe is capability evidence only. The subsequent original-model Node
pilot (`20261110-202238-v6auwd`) did attach to the solver and observe actual
raw counters. Off/on processes returned the same raw vector and the same
`unknown` (`work budget (completion)`) verdict. Its exclusive phase totals
reconcile with every raw counter; independent audit: `20261110-203450-h8vitu`.

It reported 12 candidate quiet windows with live `canon`/`canonFlip` stacks.
The first sampler did not recheck the heartbeat after the profiler replied,
so these are candidate coverage gaps, not definitive F3 violations. The next
sampler distinguishes stable heartbeat windows from changed windows. The
canonicalization follow-up counts existing lookup, serialization and key
inspection work without changing the checker after observation erasure.

A separate bounded probe (`bun-inspector.jobs.json`) tests Bun's external
inspector against an owned synthetic main-thread loop. It binds only loopback,
requires the named loop frame before return, and resumes/closes its child.
The bounded retry and the variant with `Inspector.enable`, `Runtime.enable`
and `Inspector.initialized` completed normally, but neither delivered a
`Debugger.paused` frame before the named loop returned. Both are negative
capability results, not solver attachments or F3 results. Retain all logs,
including the initial timeout; do not mistake a live socket for a live stack.

`canonical-pilot.jobs.json` now tests the heartbeat-fenced worker on the frozen
canonical source (`f59720c766a6`), with explicit pre-run source binding and
post-run source-blob checks. Its strict audit distinguishes changed windows
from stable quiet windows. Batch `20261110-211555-pdxwgb` passed with the same
raw vector and verdict off/on, unchanged source blobs and reconciled exclusive
phases. Of 14 captures, 11 changed during capture and **three stayed stable**:
one application stack through `instance` / `dataFilter`, and two GC stacks.
Changed canonicalization windows are not stable violations.

`map-stack.ts` rebuilt the exact canonical source with the same Bun 1.4.3
bundler (`20261110-213128-eh7sxk`), without another solver run. The generated
line and named-function anchors match: both anonymous frames are the Cartesian
request-product `combos.flatMap(c => d.map(v2 => ({...c, [i]: v2})))` in
`core/infer.ts`, before the `combosMax` truncation. This is a remaining raw
accounting gap, not a reason to discard the stable capture or exempt GC.
No production source was changed by the reconstruction.

No Bun F3, host qualification, calibrated weighted-unit sampler or complete
census is established by these results. Both pilot processes used the exact
unchanged original MLDR model and the same legacy 15,000,000 work allowance.

## Timestamp-bounded attribution

The old sampler chose the last 25 CPU samples by count. A sampling pause can
put those samples outside the actual quiet interval. `profile-window.mjs`
now reconstructs sample timestamps from `startTime` and cumulative
`timeDeltas`, selecting only the interval ending at `profile.endTime` with the
observed silence duration. Invalid timestamps fail closed. A real quiet window
with no recent samples remains in the output with an empty, unattributed
stack; it is not discarded or excused.

The observer records sample age, largest gap, selected interval and sample
count. `audit-pilot.ts --require-timed-window` requires this metadata and
checks interval bounds. Function-level sampling still does not identify an
exact native instruction. All eight adversarial fixtures and the real blocking-
loop capability check pass in `20261110-222458-ek322b`; the stack is captured
before the loop releases with 40 valid in-window samples. Type/lint and
commitlint pass in `20261110-222458-r9py84` (1,703 files, no warnings/errors).
An original-model timed-selection run is now pending, reusing the recorded
same-source off baseline rather than making an overhead comparison. New pilot
inputs must include `profile-window.mjs` beside the observer.

`timed-pilot.ts` binds source `32a59b2a`, checks the archived off-run's patch
identity, and executes only the new timed observer. It requires identical
runtime, raw vector, verdict and exclusive-phase vectors. The job also requires
`--strict-window --require-timed-window`. This avoids a redundant off rerun but
is not a paired overhead measurement. Its tooling passes
`20261110-222705-ud08x7` (1,704 files, zero warnings/errors); the original-model
runtime result is now collected: `runs/lane-i/resume-timed-f3` retains exact
raw/verdict/phase equality, but strict timestamp audit **failed** on an invalid
sample delta. No timed qualification follows. A bounded diagnostic retry now
records the exact invalid sample and at most two hash-bound gzip/base64 profiles
(up to 8 MiB uncompressed each); `inspect-profile.ts` diagnoses those archives
without normalizing them or accepting invalid timestamps. The strict audit is
unchanged. The original failed receipt is retained. The first diagnostic
dispatch (`20261111-005922-mew7r5`) failed before any solver execution because
the default data alias nested every input beneath `data/`. Its missing-file
receipts remain in `runs/lane-i/resume-timed-diagnostic`; the explicit-alias
retry uses the same frozen inputs in `resume-timed-diagnostic-routed`.
For a multi-directory frozen input tree, pass each child explicitly as
`--data "$dir:$(basename "$dir")"`; `--data .../data` deliberately ships it
under `data/`, not at the runner root. These are distinct destinations.
The diagnostic observer's type/lint and commitlint pass in
`20261111-005947-ht6lpo` (1,710 files, zero warnings/errors).
