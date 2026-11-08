# Runtime-only JIT / GC isolation

Complete follow-up to `../census-integrity-v1/`, on the same exclusive
**bx_3kjzmmhv**, eight pinned vCPUs, Bun 1.4.3 / `c6da4a4d3`.
All trials use the T-F1 control snapshot, not the deferred-check candidate.
The engine's own `dumpOptions` receipts verify that each requested option is
recognized. No proof, kernel rule, allowance or default is changed.

## Exclusive kernel seconds

| Diagnostic setting | One primary | Inv3915 | Inv1758 |
|---|---:|---:|---:|
| CPU sampling, p1 | 2.232 | 2.391 | 16.612 |
| CPU sampling, p2 | 1.979 | 3.032 | 12.789 |
| Concurrent JIT disabled, s1 | 1.509 | 2.434 | 12.364 |
| Concurrent JIT disabled, s2 | 1.792 | 2.076 | 6.947 |
| Concurrent GC disabled, g1 | 1.365 | 1.944 | 6.616 |
| Concurrent GC disabled, g2 | 1.250 | 1.803 | 7.045 |
| FTL JIT disabled, f1 | 1.626 | 2.154 | 8.679 |
| FTL JIT disabled, f2 | 1.730 | 2.134 | 10.465 |

All **24/24** laws check, with the same counted work and instrumented call
counts as the historical controls. Disabling concurrent compilation does not
remove variability: Inv1758 still differs by 1.78x. Disabling FTL does not
isolate the cause either. The GC pair looks fast, but its fixed position could
confound an attribution; `../census-gc-v1/` tests that hypothesis by interleaving.

## CPU sample evidence

The sampled kernel intervals total 21.216 and 17.785 s. `decide` contributes
8.063 and 6.588 s of self samples (about 38% / 37%); adding `truthOf` and `truth`
accounts for about 56% / 54%. These are the unchanged kernel's repeated path
and hypothesis evaluation, not time in the census callbacks. Sampling itself
can affect performance, so these are location evidence, not control wall
comparisons. Zero separately labelled GC samples does **not** establish zero
collector cost or account for concurrent GC threads.

`p1.cpuprofile.summary.json` and `p2.cpuprofile.summary.json` retain bounded
self/inclusive/sample summaries and hashes of the source profiles. Full
profiles were omitted from stdout because the first attempt lost earlier
receipts to retention; see `../census-runtime-v1/README.md`. All timing records,
options, telemetry and source hashes survive in this repeat.

Validation in the job: TypeScript and type-aware lint pass; **12 tests,
18 assertions** pass. No production changes.
