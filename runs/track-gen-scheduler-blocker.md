# Track Gen: shared scheduler placement blocker

## Current interpretation (corrected)

On 2026-11-08 the four ready `sc-f0d8daeee6c3/large` workers reported
`used: 4, slots: 4` and class `gate`, while no active batch reported a
running item. Our marked proof attempts had zero placements, so they were
not proof failures.

Both tracks checked the adapter's rule:
`max(ceil(cpu/2), ceil(memory/4096), 1)`. Thus `cpu=8,memory=14336` and
`cpu=4,memory=14336` each request FOUR slots. The initial suspicion that
`cpu=8` requested eight scheduler slots was wrong. Track M explicitly closed
its unplaced batches, as did this track. Compatible large workers continued
to report occupied agent work; the cause was not established by this track.

Final validation therefore uses the supported `SUPERCOMPUTER_SCHEDULER=0`
path: direct boat ownership, two exclusive large workers, `cpu=8`, no
`taskset`, and `--teardown`. No other client's workers or the shared service
are changed. The already warm xlarge worker was used only for labelled
intermediate diagnostics.

## Earlier static suspicion — NOT established as the cause

Read-only inspection of scheduler `9e0324b3af9b` found a possible closed
legacy-batch completion issue around `close`, `_accept_finished`, and
`_finished`. This was an inspection-based suspicion only. The earlier claim
that this caused the observed holds, or required a restart, was not
established and is withdrawn. Do not restart the service based on it.

Owned superseded clients were stopped by exact task ID and their unplaced
batches explicitly closed. Close receipts are preserved in this directory.
