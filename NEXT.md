# gen/cdcl-cost: checkpoint

- ef7941c / f5db71e: chronological backtracking in kernel/cdcl.ts's clausal mode (GDP_CDCL_CB, default 0: always one
  level back past a backjump of more than 0 levels); off (-1) the search is the old one (250/250 queries identical).
- kernel/prove.ts growRoot: goals of >= 500 hypotheses asked for a model first (GDP_MODEL_FIRST), and where the model
  search refutes, the tree searched over its core and unfolded in the goal (cdcl.ts's treeOf; GDP_MODEL_CORE).
- decentralized_lock's written invariant: proven, checked, 18.4 s locally (unknown at 100 s on c4dff18).
- Quick bars (CHC dev set, base 520/516/517): cb5 515, cb0 519, f5db71e 523 (gained 5, lost 3: s_split_46, HOLA/19
  solid, both IMC answers whose lifted proof is near the limit).
- Next: full bar of f5db71e against c4dff18 (builds c4dff18's shared baseline); if CHC moves, the side-by-side batches.
