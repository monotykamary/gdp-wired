# NEXT (gen/protocols3)

Standing: 4 of 10 with nothing written at 60 s (lock servers, decentralized, ticket), 1 of 10 at 10 s; written 8 of 10.
Full bar against c4dff18 (39dfed6): wrong 0, nothing lost in every run, CHC 1,168, Lean 48/48, speed level or faster.
research/protocols/README.md, the last section, has every figure.

Open:
- decentralized at 10 s: its sums pass needs more than the 10 s budget in all (not a share problem).
- two_phase_commit, distributed_lock, the two consensus protocols, sharded KV: unmoved; class D (prover cost on
  3-5-key goals) parked.
- The model-first gate: CHC seemed to lose without model-first on goals reading functions (dillig17), data's 1-vCPU
  tests seemed slower with it; both within batch noise so far. A dedicated A/B (several runs a side) would settle it.
