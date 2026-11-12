# Writer-only next-run packet (Main decision)

Base48f21567f94b1d7ec26098e804af329f717a67c8; branch `track-m/closing-writer` in `/home/user/VCS/working-remote/open-source/gdp-wired-trackM-closing-writer`.

NEXT FULL RUN waits only for (1) accepted K memory fix, (2) peak export, (3) this write-only snapshot exporter. Shared-closing extraction, loader, and ledger hydration are deferred and preserved separately in `gdp-wired-trackM-peak-memory`; none is part of this packet. No tests or new B admissions yet.

## Narrow source changes

- Production search/closing body is unchanged. `core/count-recipe-controller.ts` adds a pre-first-closing observer and an observational shallow pass snapshot; exceptions cannot replace the native result. No snapshot is built when the observer is absent.
- `core/counts.ts` passes the live prepared m, ordered set/caller/initial, selected and structured context, active set, closing budget, until, workAllowance, scopeEnabled, pending transport decline, reason/failure and complete pass state. Reachability must be absent for a complete export, matching the pinned profile.
- Getter-only diagnostic exports record private ledger lattice/counters/consumed/held/scopes/leases/root and scope and counter epochs, endpoint/lease/event sequences, observer state and capacity boundaries; kernel term table plus termIds in order and term memo observations; proof subtree marks; existing checked-scope binding metadata; legacy/count-clock anchors and trace depth. There is NO ledger reset, rehydration, receipt minting or term installation in this branch.
- The graph writer streams fixed-size records into <=8MiB shards, never JSON.stringify of the full proof graph. It preserves identity, cycles, ordering, own-property descriptors, absent versus undefined, null prototypes, IEEE numeric bytes, maps/sets and ordinary errors. Unrecognized data rejects the export only. Native metadata is reached via read-only getters. A final hashed CAPTURE marker is written after all graph shards are closed/fsynced; parent directories are fsynced before closing resumes.
- Capture failures are appended separately and counted; proving continues unchanged. `closingSnapshots` reports attempted/completed/failed exports without changing native verdict or diagnosticComplete. It is the external packet audit's job to require a complete snapshot for this experiment.
- Peak export: external Bash sampler every2s, exact driver PID/start ticks, RSS/VmHWM/VmSize plus atomic phase per sample. `closing-capture` and `closing` make the new boundary visible. VmHWM is explicitly a sampled lower bound, not an exact terminal peak. Worker joins sampler by stop file. A child-side identity handshake binds the driver before sampling. Normal completion never signals the driver; abnormal worker exit uses exact-owner TERM/KILL and a terminal join before scratch removal. No proof budget caps.

## Required focused verification (written, NOT run)

`writer-parity.test.ts` runs a small REAL production counted-family/row-composition proof in fresh processes with the unchanged22-flag profile. Compare writer off/on/forced filesystem failure: exact native verdict/family order, full final/private and settled ledgers, the byte-identical complete ordered WorkAdmissionEvent stream, count-event order and replay-event order. Nonempty real native term ordinals, subtree marks and checked-binding data are round-tripped without minting authority; the fixture remains natively checked in every arm. Check no meter or kernel-term change across the writer callback, positive native check, complete on-arm snapshot, and failure transparency. This is not a 95-minute MLDR search or a substitute for subsequent harness fidelity.

`graph-capsule.test.ts`: alias/cycle/descriptor/numeric/undefined/null-prototype preservation, hidden subtree metadata, bounded sharding, corruption/incomplete refusal. `memory-sampler.test.ts`: PID reuse/disappearance, phase matching, stop/join and marker failures. Test decoder is isolated in `graph-reader.test-support.ts` and is NOT imported by the write-only harness. Run compiler plus focused regressions on boat after K's sole gate, without duplicating K's admission.

## Dependency/status

K followup batch20261112-224023-0espe5 is D TERMINAL ACCEPTED for integration: source02e4a1b92ac7968264ee6734de740615a9ba2380/tree f139708adf8c1d3a00dc05ea4b92d52df086de0f. The exact cumulative48->K patch SHA65d2fb1f81c03e9e3b3937c4fb72809c3cd9d98c3be1f4ac1cf2ccbda789497d is applied, including both expiry test-clock corrections. This is CONTRACT_PASS_WITH_EXPECTED_ORIGINAL_FAILURES, not an all-controls-green claim. Old RED is retained. Writer v3 resolves R1-R4 and the three source cautions; no new tests/compiler/admission have run. Await D source re-review and separately bound B focused-gate permission, then update sealed source archive/guard/harness inputs for the later full-run review. Add `capture.ts` and `graph-writer.ts` to the verified target archive; driver's import is bound to that target, not the external harness directory.

No full-run admission, cleanup, worker evidence query or old fetch retry is authorized by this draft.
