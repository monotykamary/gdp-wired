# Census / T-F1 measurement integrity — historical controls

One job on **bx_3kjzmmhv**, exclusive, 8/8 pinned vCPUs, AMD Ryzen 9 9950X.
Image `sc-f0d8daeee6c3`; Bun 1.4.3, revision
`c6da4a4d3010e5553438c60f6bd76d981976867c`.

## Method

Fresh processes, sequentially: census A, T-F1 B, B, A; then diagnostic
crossovers and uninstrumented controls. The exact historical source archives
are `38c17fc4` and `bdb9568a`, with `runs/` omitted. Their checksums are in
`../census-integrity-input/archives.sha256`. Both use the original captured input
(SHA-256 `4be076f22a8fec41083719358b3518a83b23add5c3dfd26017f772404e7dac24`).

The historical runner visits only its first three laws, in unchanged order;
no later-law work or deferred audit precedes these intervals. T-F1 B includes
the historical progress and per-root CPU/wall instrumentation. No F1 deferral
or other proof optimization is installed. Every returned certificate is checked
by the unchanged kernel and the historical harness. All proof limits remain
5,000 counted units / 60 seconds per law. The 180-second process deadline is
only a whole three-law diagnostic ceiling.

All `core/` and `kernel/` files are byte-identical across revisions, as are
package/configuration pins. Crucially, installed instrumented production files
are also identical between A and B. Only diagnostic meter/runner code differs.
`source-manifest.json` contains the complete hashes and variant definitions.

## ABBA results

Exclusive kernel wall seconds:

| Process | One primary | Inv3915 | Inv1758 |
|---|---:|---:|---:|
| A1: census | 2.982 | 4.325 | 9.357 |
| B1: T-F1 | 1.455 | 1.863 | 14.471 |
| B2: T-F1 | 1.719 | 2.254 | 7.708 |
| A2: census | 1.205 | 1.737 | 7.389 |

The same census control varies by **2.48x / 2.49x / 1.27x**, with no
source change. T-F1's Inv1758 varies by **1.88x**. The slowdown does not track
the source revision or the added T-F1 instrumentation consistently.

The newer meter without T-F1's extra instrumentation yields
**1.709 / 1.711 / 7.509 s**; the old meter with those extras yields
**1.335 / 2.198 / 8.605 s**. Removing all census wrappers does not remove the
wall variability: old/new raw total-law walls are **3.568 / 3.684 / 23.721 s**
and **3.192 / 3.779 / 21.986 s**, respectively.

## Integrity and limits of inference

All **24/24** law results check. Counted units agree exactly across every run:
**926.633492 / 872.3352536 / 4310.4753532**. Every instrumented call-site count
agrees exactly; each proved law has three root `checkMC` calls.

The native 64-MiB SHA-256 calibration is 26.1–30.7 ms. Recorded CPU-quota
throttling stays zero, CPU pressure is low, and the VM-reported clock stays
4291.912 MHz. Total process CPU is 24.02–37.93 s for the same work; thus this
is not simply extra time descheduled. That evidence does **not** reconstruct
historical host/VM conditions or exclude all virtualization effects.

**Conclusion so far:** no production regression or consistent diagnostic
wrapper penalty explains the historical 3–5x comparison. There is substantial
within-revision runtime variability. JIT/GC isolation is a separate follow-up;
this result alone does not identify its precise runtime cause.

## Receipts

`comparison.json` is the checked compact comparison; `measurements.json` has
per-law sites, per-call timing when available, per-second VM telemetry, CPU
resources and calibrations. `a1.log` through `u2.log` are decoded raw records;
`paired-controls.log` preserves the complete packed receipts. The job's
placement and scheduler summary are adjacent.

Reproduction: generate the two `git archive --format=tar.gz` archives for their
listed revisions (all top-level entries except `runs`), then run
`research/track-m/jobs-census-integrity.json` through `supercomputer --timing`
with `integrity-input` and the canonical fixture mounted as `replay-input`.
No production source or default is changed by this experiment.
