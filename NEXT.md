# NEXT (gen/sums-kinds, from 2644102)

The trusted theorem: a sum's cover goals assume, at their key, the cells' laws (Sums.lean `cellLaws`, `sum_cells`;
kernel.ts `cellLaws` in sumMachine, sideGoals(m, laws)). Lean builds, axioms standard (propext, Classical.choice,
Quot.sound). Lean conformance --sums 16: 79 examples agree; examples/sums.ts --lean checks; decentralized lock's found
certificate re-checks in Lean (21 s).

Measured: decentralized_lock 60 s proven (Modal 14.7 s, local 6.3 s), 10 s unknown (sums pass's join out of time).
Written invariants as before (local); broken variants refused as before. Kernel tests 26/26, sums.test.ts 7/7.
Size +2,295 (kernel.ts +871, conformance.ts +1,424).

Running: quick bar chc,rw vs c4dff18 (runs/bar/runs/sums-kinds-quick in main); protocols search fan-out
(runs/sk/modal/fan). Then: onecpu,lean bar; CHANGELOG; reap; billing.
