# Fable/t2: observable original-quorum proof review

Requested by Main after the unobserved `20261114-061315-5b3n2y` worker timed out without a report. **The observed attempt is terminal and retained; Fable/t2 review is now requested.**

Code: `after/bapa` commit `3d02f585343b1fddbe7b15abe135a4a2e121ff8f`; prior strategy `ae288532a5e8a895482e5cf6ef8b284f8af342f0`; original source/Lean foundation `d30c5cf7a1d445096979907776e664f90df9cc40`. Main's new 10-second-progress and own-budget direction authorizes the observer only; no source model, helper planner, trusted kernel, Lean rule or ordinary-instance search policy changes were made.

## Questions to answer from retained evidence

1. Did time/work stay in function-fact candidate discovery, initial obligation construction, or downstream proof search/checking? Use `progress.jsonl`, root names in `goals.jsonl`, `worker-report.json` site totals and final `proof-report.json`. Per-site totals are metered start events/primitive counts, not phase wall time.
2. Does `learnedQuorum : Value -> Quorum` actually supply the needed off-diagonal witness terms to the existing helper planner, or does the latter still lack helper instances at the newly produced intersection witness? This is a hypothesis, not yet an observed diagnosis; do not infer it solely from a timeout.
3. What is the smallest general **untrusted** next change, if any, within C75.7/D conditions? Identify a falsifiable control. Do not add a port-specific seed, state helper, source assumption or trusted rule.

## How to read this attempt

- The full attempt uses the same exact script/worker path first executed end to end on the minimal source case. Gate `20261114-062847-i89sny`: 19 tests/49 assertions, strict TypeScript, type-aware lint, commitlint, actual worker smoke all pass. Minimal proof is proven/checked; no backup/observer failures.
- Separate research thread; parent writes progress at start, every 10 seconds and terminal. Own root is 1,000,000 raw-work-v1 units, cooperative wall 180 s, backup 240 s, outer job 600 s. Child alone enables the raw-work fixture for existing site counters. **This is not a calibrated/canonical measurement or a comparison to the unmetered old attempt.**
- `kernelCalls` is explicitly the five existing metered entry sites `kernel choiceFree/linear/termId/truth/facts`, not all checker calls. `kernelCheckSteps` is a different counter. The observer does not pretend either is a complete call profile.
- A budget or backup stop is unknown/non-verdict, never a source counterexample. All three source helpers remain GIVEN, not found; the intersection axiom is ASSUMED here, not proved by counting. No source proof/ghost elimination or full-port acceptance is claimed yet.

## Terminal evidence: Fable/t2, please review this result

Batch `20261114-062935-4bfabp`, native worker exit 2 after 39.59 s. The own-work budget returned an explicit `work-budget` report at `EPR traversal`; this is **not** a job timeout, successful proof or source counterexample. Parent elapsed time 38.608 s, `workerExit=0`, `supervisorBackupStop=false`, `observerFailures=0`. No normal prover verdict/certificate was returned. Source commit remains `3d02f5853`.

Evidence root: `runs/bapa-rigid-observed-01-fetch/observed-unseeded-naive.files/`:

- `progress.jsonl`: start, 10/20/30-second snapshots, and terminal.
- `proof-report.json` and `worker-report.json`: explicit budget outcome, cumulative site counts and scope statistics.
- `goals.jsonl`: the only emitted root is **`GIVEN unique vote per node @start`**, one hypothesis. There is no observed step/ghost/agreement root yet.
- `source-machine.json`: exact model/laws/strategy used, no hand-supplied instance tuple.

Terminal rows SHA256: `52603e54c50d3b1b17745b419c75c13d4f3ade6f41ec405abb3e8926b9ec65df`.

| Observation | 10 s | 20 s | 30 s | terminal |
| --- | ---: | ---: | ---: | ---: |
| Cumulative candidates | 133 | 134 | 134 | 134 |
| Total generated instances | 427 | 427 | 427 | 427 |
| Function discovery work | 294310 | 580913 | 781909 | 781909 |
| Five-site kernel-entry count | 147 | 147 | 243 | 347 |
| Solver calls / search nodes | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| Last metered site | function fact instantiation | function fact instantiation | EPR traversal | EPR traversal |

Top terminal primitive amounts: function fact instantiation **781909**, EPR traversal **165247**, expression-node visits **47985**. There are 423 Cartesian and 4 matched instances. The reported raw-work floor is the process cumulative counter (1000072), not an independently calibrated wall-time attribution or a claim that the root allowance was overspent; the root is an additional allowance over its entry baseline.

**Concrete question:** the output set is already 427 instances at 10 s and remains 427 through 20 s while discovery work grows by 286603, with only one additional candidate. Is repeated generic fact discovery before the first trivial start goal the next target, rather than the ghost-helper combination? Please identify the smallest general untrusted change and a falsifiable control. No further algorithm or budget change has been made after seeing this result.
