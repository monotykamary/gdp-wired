# NEXT (gen/protocols2, checkpoint)

Round: prove protocols with nothing written through the key's sort (research/protocols/STRUCTURE.md).

Done (committed):
- Step 0: core/machine.ts `writeEvery` evaluates breakpoints and one key per stretch (sums.test.ts's slow test 1.9 s to
  0.95 s locally; CI's 3.45 s to 5.7 s was the runner, ~1.7x slower on every test, median over 80 tests).
  Every default-limited (5 s) test is under 1.6 s locally (`bun test --timeout 1600`, both suites).
- kernel/prove.ts `withModels`: the one retry loop for model-based instances (proveLaw, proveThinned, the join's
  stepWith); later rounds within 3x the first round's work (at least 1 s); an unsettled later round gives back the
  first answer. Cheap skip for one-key laws already at every value of their sort.
- core/infer.ts: Houdini's law watch counted as the tuples it evaluates (k^n per law about n keys). lock_server_sync
  is then proven with nothing written at a 30 s search (the join needs 3 queries after Houdini).

Probes (local):
- decentralized_lock written invariant: proven in 222 s (the 7th law's first round alone is ~200 s of work).
- ring written invariant: proven (35 s local).

Next:
- (a) views: generalize `pairing` to several key variables per sort (lock_server_async needs {node: 2, lock: 1}).
- (b) sorted tuples in prove.ts instances.
- measure: pilot on Modal at 10 s and 60 s, quick bars chc,rw and onecpu against c4dff18.
