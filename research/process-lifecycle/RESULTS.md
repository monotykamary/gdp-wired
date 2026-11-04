# Mac sole-parent lifecycle feasibility — bounded assessment

## Decision

A Mac-only identity-safe signaling protocol is feasible **conditionally** for a
surviving sole parent and its retained direct children. A Linux host/pidfd is not
logically necessary for this narrow design. This is not a supervisor implementation,
execution approval, or evidence of real signal delivery, durability or VM deletion.

The earlier SDK-only assessment left the PID-lifetime premise open. The authoritative
POSIX text and pinned XNU implementation below now support it. Neither identifies
or attests the exact running kernel on this Mac.

## Normative contract

- POSIX.1-2024, General Concepts §4.17: a process ID shall not be reused until the
  process lifetime ends: https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/V1_chap04.html#tag_04_17
- Definitions §§3.279, 3.284–3.285 include live and zombie processes, unique PID
  identity during the lifetime, and lifetime ending when the PID is returned:
  https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/V1_chap03.html#tag_03_279
- `_Exit`: absent automatic reaping, termination produces a zombie; its lifetime
  ends when the parent consumes status via wait/waitpid/waitid without WNOWAIT.
  Explicit SIGCHLD ignore or SA_NOCLDWAIT instead permits immediate lifetime end:
  https://pubs.opengroup.org/onlinepubs/9799919799/functions/_Exit.html
- `waitid(..., WNOWAIT)` leaves the process waitable; WNOHANG alone is NOT a
  non-reaping observation: https://pubs.opengroup.org/onlinepubs/9799919799/functions/waitid.html

Therefore: preventing status consumption and auto-reap preserves the PID against
reuse after ordinary child termination. It does not grant general ownership over
arbitrary PIDs or protect a parent that has itself died.

## Pinned Apple implementation corroboration

Repository `apple-oss-distributions/xnu`, tag `xnu-12377.121.6`, immutable commit
`ac9718fb1af618d5ce8678d0dc6e8a58f252216f`. Source links share this prefix:
https://github.com/apple-oss-distributions/xnu/blob/ac9718fb1af618d5ce8678d0dc6e8a58f252216f/bsd/kern/

- `kern_fork.c:950–988`: under the process-list lock, new-PID selection rejects
  an existing process-hash entry (the comment explicitly covers zombies and running
  processes), process-group ID and session ID, then inserts the child in the hash.
- `kern_exit.c:2713–2805`: ordinary exit marks SZOMB; P_NOCLDWAIT/dead-parent
  paths permit system reaping. `kern_sig.c:681–684` sets P_NOCLDWAIT for either
  SA_NOCLDWAIT or explicit SIGCHLD SIG_IGN.
- `kern_exit.c:2967–2987`: `reap_child_locked` removes the child from the process
  hash under the list lock. `:3372–3410` reaps a zombie in waitid only without WNOWAIT.
- `kern_sig.c:1393–1414`: positive-PID kill resolves/refers to the process before
  signaling; a zombie lookup may return SUCCESS WITHOUT signal delivery. Neither
  successful kill nor ESRCH is a substitute for terminal/reap evidence.

This is source corroboration for the specified release and ordinary lifecycle,
not formal verification of XNU or a claim that this Mac runs this revision.
Debugger-driven reparenting, privileged interference and unreviewed lifecycle
extensions are outside the premise.

## Required protocol / counterexamples

1. Obtain the positive PID directly from successful child creation; no name scan,
   PID-file recovery, birth-time check-then-kill or group-wide signaling.
2. One owner controls all signaling, callbacks, timers and consuming waits. No
   library auto-reaper or independent waitpid(-1) thread; no SIGCHLD auto-reaping.
3. Closing admission is irreversible. Drain/cancel already admitted signal paths
   before consuming terminal status. Reaping while an old signal path is pending
   permits PID reuse and subsequent signaling of an unrelated replacement.
4. Direct-child ownership does not cover grandchildren whose intermediate parents
   can reap them. Broker all controlled creation through the actual owner, or prove
   a separate lifetime mechanism. An opaque CLI helper tree is not covered.
5. Parent/authority loss invalidates the record permanently. No restart may signal
   stale journal PIDs. Already in-flight operations are not retroactively undone.
6. The owner/watchdog must survive work cancellation and avoid blocking worker
   I/O. Preserve the previously agreed absolute work/cleanup/termination/reap
   cutoffs; no new grace periods. Repeated cancellation cannot renew them.

Installed Apple SDK documentation additionally supports the wait/WNOWAIT and
SA_NOCLDWAIT interfaces. Its clock_gettime(3) distinguishes sleep-inclusive
CLOCK_MONOTONIC from CLOCK_UPTIME_RAW/mach_absolute_time. Bind the actual chosen
runtime clock, not its friendly name. `_exit(2)` documents possible descriptor-drain
exit delays. These APIs do not establish hard real-time scheduling or guaranteed
physical process disappearance by a deadline. Missing terminal proof stays failure.

## Pure protocol model

`model.py` contains no PID or OS APIs. Its states are owned(0), retiring(1),
reaped(2), invalid(3); operations admit/finish/retire/reap/lose-owner are serialized
transitions. Admission represents entry into the owned critical section, not an
unchecked future callback. Finish may mean completion or cancellation/drain.
Owner loss never resurrects authority, but does not magically finish in-flight work.

Nine source laws cover three state invariants and six step properties, including
no admissions after retirement/reap/owner loss and no reap before prior drain.
`broken.py` omits the drain guard; admit -> retire -> reap is a concrete violation.
`probe.py` checks all length-six traces over five actions and replays that control.
These are pure model checks, not spawned-process/signaling experiments. The model
assumes the real implementation serializes its operations as modeled. It does not
prove locking, signal-mask discipline, OS behavior, fairness or deadlines.

## Validation status

The one authorized ordinary boat job completed with a **worker timeout**, not a
proof verdict. Batch `20261104-111004-adr95v`, uploaded tree `4a397ad58a2a`, image
`sc-f0d8daeee6c3`; requested 2 CPU / 4096 MiB / 60 seconds. The retained worker
summary is exit **124**, **30.1 seconds**, and stderr says `timed out after 30 s`.
The cause of the requested/observed timeout discrepancy is not established.
The controller's exit 0 reports batch completion, not test success.

No `LIFECYCLE_REPORT`, proof certificate, completed finite-probe receipt or
replayed broken-control result reached the retained output. Therefore **none of
the nine laws or the negative control is claimed validated by this attempt**.
Potential partial remote files have not been recovered; no additional execution,
provider inspection or duplicate job was launched. A further validation attempt
requires fresh coordinator authorization. The platform-source conclusion above
is independent of this failed validation attempt.

Frozen input manifest SHA256:
`96395c0cee65d3fe96a4a251c5722caa722c8811da5538beec7feef4399e16da`.
The manifest binds the 19 listed inputs against checker base
`7af9d486f29d14b57dfac0d67766841e6c2478ef`; the tracked checker directories were
unchanged at dispatch. Documentation downloads and Apple SDK slices have a
separate `source-manifest.json`. Evidence is under `runs/astra-mac-lifecycle/`:
`input-manifest.json`, `source-manifest.json`, `failure-receipt.json`, and
`results/{pure-lifecycle-laws.log,summary.tsv,placement.json,backends.json}`.
The observed placement is a nonexclusive large VM, two allocated vCPUs on an
eight-vCPU host, with one co-tenant; no performance or native CPU1 claim follows.
The frozen historical `research/egraph` packet is unchanged.
