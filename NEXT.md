# NEXT (gen/sums-kinds, from 2644102)

The trusted theorem: a sum's cover goals assume, at their key, the cells' laws (Sums.lean `cellLaws`, `sum_cells`;
kernel.ts `cellLaws` in sumMachine, sideGoals(m, laws)). Lean builds, axioms standard.

Done: Sums.lean (sum_cells, cellLaw_holds, checkSums over ps), kernel.ts mirror, emit.ts, conformance `flag` family
with three kind tampers. decentralized_lock: 60 s search proven (6.3 s wall), 10 s unknown (join out of time).

Next:
- core/sums.test.ts: DSL test (a yes/no map's sum proven; kind out of the laws refused; a nat map's goals unchanged)
- run conformance (TS and Lean --sums), examples/sums.ts --lean, kernel tests, sums.test.ts
- protocols --skip search (all), broken variants
- CHANGELOG Unreleased; size vs 2644102; bars on Modal (chc,rw quick vs c4dff18; onecpu,lean)
