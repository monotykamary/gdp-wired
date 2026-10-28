# NEXT (gen/protocols2)

State: research/protocols/README.md "Round 2" has every figure. With nothing written: 2 of 10 at 60 s (lock servers),
1 of 10 at 10 s. Written invariants: 7 of 10. Quick bars vs c4dff18: no solid change, wrong 0. +15,757 bytes.

Next, by what each miss needs:
- decentralized_lock: Sums.lean's cover goal with the cells' kinds (trusted, Lean first). The search already finds
  `sum$HasLock + sum$Message <= 1` and the set the join calls inductive.
- two_phase_commit: the join's "outside" stop on the caller's law (a model state breaking a set form at a key the goal
  doesn't hold): read the model on the goal's keys only, as modelInstances does.
- toy / wo_decide / distributed: kernel cost of 3-4-key goals (class D); per-row sums (S4) would say the exclusion laws
  at one key.
- sharded KV: generate sorted tuples instead of filtering (withReads runs out of memory on 5-key laws).
- Houdini: lawful() evaluates multi-key laws at every tuple of the state's keys; sorted keys would cut it (12 s wall on
  lock_server_async, nothing killed).
- Share: keySorts (rule) and keySorted/modelInstances' sorts (goal) are one idea read twice; mapKeys/mapReads walk twice.
