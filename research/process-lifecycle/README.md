# Conditional process-lifecycle research

This directory retains a pure serialized lifecycle model, its deliberately broken
control, the validation runners and their historical reports. It is **not** a
supervisor implementation or authorization for live process/provider operations.

## Result history

| Packet | Outcome |
|---|---|
| [Platform and first attempt](RESULTS.md) | Conditional PID-lifetime premise supported; initial validation timed out without a verdict |
| [Timeout diagnosis](TIMEOUT-DIAGNOSIS.md) | Requested 60 seconds lowered to native 30 by the pinned scheduler client |
| [Instrumented v2](v2/RESULTS.md) | Setup import failure; no model checks started |
| [Isolated v3](v3/RESULTS.md) | Nine producer-reported proofs retained; strict collector failed; `final=false` preserved |
| [Separate cold check](cold/RESULTS.md) | Nine exact saved documents / 36 per-document claim results accepted, plus actual exact four-call negative source replay |

The cold check uses the explicitly corrected [metadata contract](cold/CONTRACT.md):
full source identity first, then basename-plus-line within that exact file. It does
not change v3's verdict or regenerate any certificate. Its accepted source replay
is `step(0), step(-1), step(1), step(2)`, ending at phase 2 / inflight 1.

## Sources and boundaries

- `model.py`: nine laws over the pure owned/retiring/reaped/invalid protocol.
- `broken.py`: deliberately missing the in-flight drain guard.
- `probe.py`: finite pure-state cross-check, distinct from the exact cold replay.
- `run-review.ts`, `v2/`, `v3/`, `cold/`: preserved versions, not one interchangeable
  executable. The cold runner expects the frozen input bundle described in its
  report; neither it nor the older jobs should be launched as a new experiment
  without a separately approved scope and budget.

The proof is conditional on serialized admission/retirement/reaping, sole-parent
ownership and the documented PID-lifetime premise. It does not establish real
locking, deadline behavior, signal delivery, runtime lifecycle correctness or an
exact-running-kernel claim.

Detailed evidence, manifests, exact certificates and downloaded platform source
snapshots remain under ignored `runs/astra-*` directories referenced by the
reports. They are intentionally excluded from this source/documentation commit.
Historical `research/egraph` packets are separate and unchanged.
