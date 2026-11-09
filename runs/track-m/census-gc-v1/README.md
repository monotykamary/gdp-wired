# Interleaved concurrent-GC discriminator

Same exclusive **bx_3kjzmmhv**, eight pinned vCPUs. Within each historical meter,
run default / concurrent-GC-off / off / default. Every process has GC logging
on, verified by the engine option receipt. This is a diagnostic runtime setting,
not a production or proof-strategy change.

Mean exclusive kernel seconds, two fresh processes per cell:

| Meter / runtime | One primary | Inv3915 | Inv1758 |
|---|---:|---:|---:|
| T-F1, default GC | 1.663 | 2.303 | 8.434 |
| T-F1, concurrent GC off | 1.614 | 2.366 | 8.808 |
| Census + call timers, default GC | 1.412 | 1.946 | 7.925 |
| Census + call timers, concurrent GC off | 1.432 | 1.926 | 8.956 |

Turning concurrent GC off does **not** improve the heavy law: means are
**4.4% / 13.0% slower**. Thus the preceding fast GC-off pair is not sufficient
causal evidence. Do not attribute the historical 3–5x gap to concurrent GC.

All **24/24** structured law results check; counted work and all instrumented
call counts match the other complete batches exactly. The retained default-GC
stderr logs report 116–122 completed collections and 2.588–3.129 s in cumulative
`p` pause timers over each whole three-law process. These are engine-reported
values, not an exclusive kernel-phase decomposition or historical GC trace.

## Receipt retention

`measurements.json`, source hashes, runtime metadata and placement survive for
all eight trials. Verbose GC logs again exceed stdout retention: raw stdout /
stderr for c1, c2 and c3 are missing (c3's time receipt survives); this is listed
by aggregate validation. No missing log is reconstructed or treated as present.
The retained structured measurements include all verdicts, units, sites and
per-root timings. `gc-analysis.json` reports both matched means and which raw
collector logs remain. The final harness now emits essential structured
artifacts last to protect them from tail retention.

## Final interpretation

The requested old/new same-VM comparison excludes a production-code or snapshot
installation regression. It finds large within-revision performance variation,
and no consistent penalty from the added T-F1 measurement wrappers. The JIT and
interleaved GC controls do **not** identify a unique cause of the historical gap.
CPU samples locate present cost in unchanged `decide` / `truthOf` / `truth`
work. The exact historical runtime / physical-host state was not captured and
cannot be reconstructed from those old receipts; the historical Bun revision
was not recorded either. Ordinary current guest CPU-quota throttling is not
observed, but physical-host contention and microarchitectural state are not
ruled out by guest telemetry.

**Do not compare the isolated historical wall numbers as a source-regression
ratio. The precise 3–5x historical cause remains unresolved.** Report matched
repeats and their spread; do not normalize one dataset by an assumed factor.
No production change, implementation, gate rerun or budget increase.
