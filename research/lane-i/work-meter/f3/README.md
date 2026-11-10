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
from stable quiet windows. This new original-MLDR Node pair is pending; it does
not repeat or replace the old pre-canonical pair.

No Bun F3, host qualification, calibrated weighted-unit sampler or complete
census is established by these results. Both pilot processes used the exact
unchanged original MLDR model and the same legacy 15,000,000 work allowance.
