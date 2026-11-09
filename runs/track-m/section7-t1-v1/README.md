# Section 7, T1 — stopped at the failed pass line

The unchanged candidate implementation is 50109a36. T0 was separately
committed as 79a5c991. All T1 measurements ran on the same exclusive
8-vCPU VM as the prior census: bx_3kjzmmhv.

- `results.json`: statically reduced canonical and five-law measurements;
  `pass` is false.
- `Inv2973.json`, `Invstar.json`: complete phase, cut, detail-site, and
  checker-caller records.
- `admission-wall.log`: raw measurements and instrumented type/lint checks.
- `preflight-1.log`: failed instrumentation-only TypeScript preflight;
  not evidence for a scientific test outcome.
- `validation/`: final uninstrumented source type/lint and meter-test check.

Reproduce the measurements with `research/track-m/jobs-section7-t1.json`
and the canonical fixture mounted at `replay-input`. The two installers
only edit disposable remote snapshots. Reduce the raw log with:

    bun research/track-m/extract-section7-t1.ts LOG OUTPUT_DIR

The detail meter divides each existing census phase into disjoint buckets.
Nested site wall times, separately provided for diagnosis, are inclusive
and must not be added. An ordinary-query transport is removed from the
ordinary-search residual and charged to transport. Kernel time retains
its separate original phase even when invoked inside admission/transport.

Measured admission/transport shares of remaining wall are 36.65% for
Inv2973 and 49.47% for Inv*. Even assigning all observed admission and
transport wall across all phases, including kernel work, to the design's
wall-minus-counted excess gives only 45.27% for Inv2973. The >=50% pass
condition was not established. T2, T3, implementation, and Gate 1 were not run.
