# NEXT (gen/protocols3)

State: research/protocols/README.md "Class B". With nothing written: lock servers and ticket_lock (ticket at the 60 s
wall limit on Modal). Written invariants 8 of 10. Quick bars level, wrong 0. +5,736 bytes against 2644102.

Open:
- ticket_lock's join spends most of its wall time on whole-set queries (1,141 forms; ~3 s each locally). A cheaper
  escalation than "the whole set" would bring it under 60 s on Modal; doubling the relative context was tried and
  changed the path (not proven).
- Gitea #0: unchanged; its model's counterexample needs a fact the views don't make.
