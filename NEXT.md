# NEXT (gen/sums-kinds, from 2644102)

Done. Sums.lean `sum_cells` / `cellLaws` (axioms: propext, Classical.choice, Quot.sound), kernel.ts mirror, tests,
conformance, CHANGELOG. Bars: runs/bar/runs/sums-kinds-quick, sums-kinds-onecpu-lean, sums-kinds-lean (main checkout).

Open:
- decentralized lock at 10 s: the sums pass's join (core/infer.ts, joinShare of the second inferLaws' budget) stops
  after round 1; at 60 s it finishes in 5 rounds. A budget question in the search, not the kernel.
- spend: re-read with `bun gates/bar.ts spend <run dir>` once 18:00 UTC is billed.
