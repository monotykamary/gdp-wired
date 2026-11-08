# Track Gen: shared scheduler placement blocker

Observed while collecting the final Paxos/prefix gate on 2026-11-08.
The four ready `sc-f0d8daeee6c3/large` workers report `used: 4, slots: 4`
and class `gate`; the scheduler reports no running items in any active batch.
The marked proof batch `20261108-173235-q1gtnc` is queued with zero placements.
This is not evidence of a proof failure.

Read-only inspection of installed scheduler version `9e0324b3af9b`:

- `Scheduler.close` removes a legacy batch from `self.batches`, sets its items
  done/closed, and asynchronously requests `killitem`. It does not remove the
  held entries from `VMState.running`.
- `_accept_finished` dispatches a completion to `_finished_legacy` only if the
  batch still exists and is not strict. A closed legacy batch instead takes
  `_finished`.
- `_finished` finds the old held item but returns false for `b.closed` before
  its `vm.running.pop`. That leaves a timing item holding the entire VM.
- `VMState.used` reserves all slots whenever a timing item remains in that map.

This code path is consistent with the observed occupied workers and absent
running batches. Shared-service recovery or an operator-owned scheduler fix
is required; this track has not edited the harness, restarted the shared
scheduler, or stopped another client's VM. All owned superseded batch IDs
and explicit close receipts are retained in the Track Gen runs directory.
