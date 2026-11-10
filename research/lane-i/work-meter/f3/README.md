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

This is capability evidence only. It does not attach to the solver, sample
actual work counters, establish F3 for Bun, or qualify a host. The next step
is a research-only Node bundle of the exact solver source with raw progress
observed from shared memory, followed by raw-count/return-value equivalence
against the same source without observation. A calibrated weighted-unit
sampler and an original-model ledger run remain required before claiming F3.
