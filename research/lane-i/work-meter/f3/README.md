# F3 blocking-loop capability probe — not a complete sampler

## Native-operation follow-up (2026-11-11, in progress)

`native-spans.ts` supplies a research-only seqlock around a method invocation.
The receiver, method lookup and arguments are evaluated in their original order
before entering the span. Nested calls restore their parent; exceptions retain
identity. Idle, torn, crossed and saturated observations cannot be attributed.
Six control tests / 22 assertions passed on boat in `20261111-013845-3xkrpa`.

`native-instrument.ts` prepares exact-source replacements for the previously
observed canonicalization functions: WeakMap lookup/set, key enumeration,
sort, map, join, and JSON serialization. It is now wired into the Node sampler. The first completed run preserved the
original MLDR raw vector, verdict and exclusive phase totals, and had three
timestamp-valid stable windows, but the 10-million-span guard saturated before
attribution (zero accepted operation windows). The guard therefore failed
closed. The 100-million-span follow-up (`20261111-015254-rydo8b`) completed
without overflow: 31,172,052 spans, five timestamp-valid stable windows and
eleven changed windows, with unchanged raw counters/verdict/exclusive phase
totals. One ~304 ms stable window identifies the `canonFlip` cache insertion
`flipMemo.set` (`WeakMap.set`). Four others remain unattributed: two `certFor`,
two tree-walker `go` frames. The audit is `runs/lane-i/native-profile-100m/audit.log`.
One invalid profile was excluded, with only hash/size metadata retained
because its complete payload exceeded the diagnostic log limit. No full F3
or exact-native-instruction claim is made. A future accepted window must retain the timestamp test,
raw-heartbeat fence, stable operation sequence and source hash together. A
span can contain callbacks, reflection overhead or GC; it identifies the
invocation boundary, not an exact native instruction. This does not close F3.


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
The original-model timed-selection runs below reuse the recorded
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
`20261111-005947-ht6lpo` (1,710 files, zero warnings/errors). The independent
archive controls and full type/lint/commitlint also pass in
`20261111-005857-ih08mm` (1,708 files): one positive and six negative archive
fixtures, with timestamp normalization explicitly false. The routed run (`20261111-010216-e0ogvi`) passes all three jobs: nine
sample-window controls, real blocking-loop capability (30 recent samples,
received before release), and original `mldr` timed diagnostic. All fifteen
capture windows have valid timestamps; three stable windows remain in
`canon2`/`canonFlip` and twelve change during capture. Raw counters, verdict,
exclusive-phase counters and source identity match the archived off baseline.
No invalid profile was emitted on this run. The prior invalid-delta failure
is unreproduced, not fixed or erased. Independent audit and exact-source
mapping **pass** in `20261111-011036-rhom40`
(`runs/lane-i/resume-timed-evidence`). The original invalid-timestamp receipt
still fails the strict audit, as required by a negative control. Full type/lint
passes on 1,732 files with zero warnings/errors; commitlint also passes.

The three source-bound stacks are `kernel/kernel.ts:canon` via
`kernel/reader.ts:form/addCopy/sync`, and `canonFlip` via `dec/equal` and
`dec/truth0`. Source blobs are unchanged before and after reconstruction.
These are function-level anchors, not exact native instruction locations.
The next attribution step must distinguish key enumeration/sorting, memo lookup,
serialization and GC with bounded before/after observations, not infer one
from a function name. CPU placement labels are empty, so no hardware or
wall-time claim is made. Full F3 and calibrated W remain open.
