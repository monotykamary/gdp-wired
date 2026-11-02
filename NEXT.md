# Lane RL: native multi-place relations (gen/laneRL) — where it stands

Scratch runs in runs/laneRL/ (gitignored; archive with `tar -C <wt> runs` before removing the worktree). Design and
measurements: research/protocols/engine/DESIGN.md, the two gen/laneRL sections.

## Done
- Trusted: `tup`/`proj` terms; kernel.ts reads tuple keys part by part (keyParts = Lean `parts`, cells `M[⟨k1|…⟩]` =
  Lean `cellT`, tuple equality as `and`, cell equality part by part); Lean twin in Kernel.lean (+~700 lines; all modules
  build; propext/Classical.choice/Quot.sound). Map names holding column characters read no column (hole found by the
  lane's review; Lean refused it). kernel/tuples.test.ts (adversarial) in the shards; mutants 170/177 killed, 7
  equivalent (MUTANTS.md).
- Lean end to end: `bun lean-kernel/export-kernel.ts --switch` (learning_switch + published invariant, 155 s on boat);
  `--tuples`.
- DSL `.sorts`, `.relations` (RelRef has/at/add/remove/each/union); runtime decides tuple quantifiers/writes per part.
- Ports: learning_switch, learning_switch_i4 native (models.ts; phased kept as `phased`); agree.ts 12,000 steps each no
  difference; check.ts 43,672 / 240 states = TLC; broken variants reach bad.
- learning_switch PROVEN WITH NOTHING WRITTEN at strict 60 s pinned (engine, core/infer.ts): gate-ic 18.7/16.4/18.0 s,
  gate-ic2 56.1/18.5/40.6 s. Hand sets (relations/hand.ts): learning_switch 3–5 s, i4 11.5 s (the written I4 set
  needed two laws to hold whenever set, not only after start).
- Gates: IC3Syn 29×3 gate-ic: 24 all three / 25 some (main 22/24), no broken proven; gate-ic2 (HEAD 033f8e2,
  noisier VMs): 22 / 25. Quick bar (laneRL-quick2, vs main 9b62ecf): wrong 0, nothing lost solid; g332 same searches,
  time +3% to +39% across runs (base varies 288–381 s; cellParts now memoized). Shards: all pass (shard2's one
  failure a 5 s timeout, passes alone: gate-shard2b).

## Open
1. DuoAI ten: paired 3 runs vs main (runs/laneRL/ten3-rl vs ../gdp-wired/runs/laneRL-ten3-main): RL lost
   consensus_wo_decide, distributed_lock, ring_leader_election (main proves them). Bisected (scratchpad worktrees,
   2 runs a commit): distributed_lock = the sorts by tuple places / one-part map values (f53f531) → gated to tuple
   rules (2d7e5d3); the other two = 033f8e2's wide-goal EPR path → gated to tuple rules (26fed6b). Confirming:
   runs/laneRL/ten3-fix (ten ×3) and gate-ic3 (IC3Syn 29 ×3 + broken).
2. learning_switch_i4 with nothing written: unknown at ~55–75 s (engine: small instance cost, cubes; DESIGN.md).
3. Broken switches end unknown (never proven), not refuted (runs don't reach the bad states in budget).
4. pi reviews (sol xhigh, terra) not run: pi's OpenAI login expired (invalid_grant). Re-login, then review
   kernel.ts's tuple lines and Kernel.lean's.
5. certCyclic (core/cyclic.ts) ignores withWall on a flip relation with a symmetric law (prover side finding).
6. Stretch not started: Ivy/mypyvy reader.
