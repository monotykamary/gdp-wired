# Minimal admitted-file clock port — staged for lane D

Base: be661632 (common kernel db5bc38..., Lean b9039b8...). Initial port:
4e13e5f9. This is a new composition, NOT covered by the previous clock receipt.

`admitted-clock.patch` contains every change under kernel/ and lean-kernel/:

- kernel/prove.ts: A's counted/work-budget header, imports of untrusted raw
  meter/profile helpers, and wall-telemetry calls routed to traceNow.
- kernel/cdcl.ts: telemetry to traceNow and its optional wall endpoint to
  searchNow. Root orientation/search choices remain exactly as admitted.
- kernel/epr.ts: optional hook telemetry to traceNow, no decision change.
- No Lean changes. No trusted kernel/kernel.ts or core/check.ts change.

The verifier checks all other admitted files plus core/check.ts byte-for-byte.
It independently erases only the clock calls/imports from CDCL/EPR and compares
against the base. From `// units: false` onward the common prover must be
byte-identical after replacing traceNow calls with performance.now. No A prover
body is restored. The changed header retains fullRate and historical weights.

Outside the admitted tree: A's raw meter/profile/step/ledger modules, the
observational machine instrumentation, scoped clock callers and public work
admission. Raw counters are diagnostic only: this port does not claim complete
coverage or calibration of every checked/native instruction. It never changes
a checking rule or considers a meter total evidence of proof.

The two exact D-tested exporter fixtures are supplied with their minimal
untrusted count-frame helper from the admitted B source, not a strategy merge.
A and F/B continue to own generation termination and lifted route registration.

Frozen validation/census source: 9a5a80e4c32def7393f5df7b5d2c24eea5e05816.
Minimal admitted-clock.patch SHA-256:
`e6cc5f9028a8d77bb3206b565555017dbc0b9282d26c7155423fa0f526474bb5`.
Native tests and machine erasure now pass; full type/lint and the gated census
are still running. No new D GREEN, main merge, push or W claim.
