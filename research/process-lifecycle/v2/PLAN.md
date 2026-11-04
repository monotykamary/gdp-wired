# Distinct instrumented lifecycle validation v2

Authorized by coordinator: one ordinary 2 CPU / 4096 MiB / requested 60-second job.
The known native conversion makes the whole-workload allowance 30 seconds.
No request for 90 seconds, shared configuration edit, provider control, or lifecycle
OS experiment is involved. Model, nine law annotations, broken control, and finite
probe are byte-identical to the original frozen inputs.

## Offline pinned setup

No `bun install`: the only required external runtime dependency for this Python
extraction path is TypeScript 5.9.3. The npm tarball was downloaded by bounded public
GET and its SHA512 verified against the existing `bun.lock` integrity. It ships via
`--data`, is verified before unpacking into this job's private node_modules, and is
loaded with Bun auto-install disabled. Its package must declare no runtime
dependencies. The full TypeScript archive is kept, not an unpinned cache or stub.
Bun/Python are supplied by the existing image; their availability remains a runtime
precondition, not a new image or binary attestation.

The input manifest hashes 230 source/assets/configuration files (about 7.1 MB),
including the complete tracked .ts/.py/.json files under core, kernel, interchange
and lean-kernel and all 19 original input files. This deliberately exceeds the
active source closure. The archive hash and original manifest binding are retained.

## Sequential budget

| Phase | Child ceiling |
|---|---:|
| Verify pins, unpack/load dependency | 4 s (inner tar 2 s) |
| Unchanged finite probe | 2 s |
| Unchanged broken control, CLI | 4 s |
| Unchanged nine-law model, CLI + certificate production | 13 s |
| Kernel certificate replay and source/input binding | 3 s |
| **Total child ceilings** | **26 s** |

The parent clips each child ceiling to its remaining 27-second finish target,
reserving headroom under native 30. These are timeout allocations, not proven
real-time bounds on a contended host. Prover search is 500 ms rather than the old
2000 ms; law statements, extraction/cross-check behavior and acceptance tests are
not weakened. Failure/unknown stays failure/unknown. No success timing is assumed.

## Incremental evidence

The parent uses synchronous writes to stdout for start, every phase start, every
phase result, and final/fatal records. Each child outcome includes exit/signal/error,
duration and exact compressed stdout/stderr with uncompressed SHA256. Broken/probe
run before the positive proof so a late positive failure cannot erase them.
Partial certificates are replayed even after a positive CLI failure. Individual
certificate records retain the raw document compressed and hashed, its kernel
verdict and exact source-law metadata binding. The packet can be decoded offline.

All stdout records together are bounded to 300,000 bytes, below the pinned agent's
400,000-byte tail cap. The worker may replace stderr on its native timeout, but
these receipts are on stdout. A final record is not required to retain earlier
completed phases. A fatal/cap failure never upgrades partial evidence to success.

Acceptance requires the finite probe, exactly nine positive proven laws, the one
broken law with a replayed trace, exactly nine source-bound kernel-accepted
certificates, and unchanged input hashes. This establishes only the conditional
pure serialized model claims—not implementation locking, deadlines or delivery.
