# NEXT (gen/protocols3)

State: research/protocols/README.md "Class B". With nothing written: lock servers and ticket_lock (ticket at the 60 s
wall limit on Modal). Written invariants 8 of 10. Quick bars level, wrong 0. +5,736 bytes against 2644102.

Open:
- ticket_lock's join spends most of its wall time on whole-set queries (1,141 forms; ~3 s each locally). A cheaper
  escalation than "the whole set" would bring it under 60 s on Modal; doubling the relative context was tried and
  changed the path (not proven).
- Gitea #0: unchanged; its model's counterexample needs a fact the views don't make.

# NEXT (gen/sums-kinds, from 2644102)

Done. Sums.lean `sum_cells` / `cellLaws` (axioms: propext, Classical.choice, Quot.sound), kernel.ts mirror, tests,
conformance, CHANGELOG. Bars: runs/bar/runs/sums-kinds-quick, sums-kinds-onecpu-lean, sums-kinds-lean (main checkout).

Open:
- decentralized lock at 10 s: the sums pass's join (core/infer.ts, joinShare of the second inferLaws' budget) stops
  after round 1; at 60 s it finishes in 5 rounds. A budget question in the search, not the kernel.
- spend: re-read with `bun gates/bar.ts spend <run dir>` once 18:00 UTC is billed.
