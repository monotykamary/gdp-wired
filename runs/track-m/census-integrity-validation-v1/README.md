# Final measurement-integrity validation

Same exclusive `bx_3kjzmmhv`, 8/8 pinned vCPUs.

- TypeScript and type-aware lint: pass, 0 warnings / errors.
- Phase-meter and measurement-integrity unit tests: 12 pass, 18 assertions.
- Shell syntax checks: pass.
- Aggregate audit: 24 processes, **72/72 checked law results** across the three
  complete batches; identical input and Bun revision; unchanged source hashes;
  exact counted work and instrumented site counts.
- All three measurement jobs and this validation use the same exclusive VM.
- Six absent raw GC files are explicitly reported: stdout/stderr for c1, c2, c3.
  Their structured measurements survive; the incomplete first CPU-profile
  attempt is excluded altogether from the aggregate.

See `validate.log` and `placement.json`. No production change or new gate run.
