# Lane RL: native multi-place relations (gen/laneRL) — where it stands

Goal: IC3Syn's learning_switch and learning_switch_i4 proven with nothing written, over relations keyed by tuples
(EPR, componentwise), not radix-packed keys. Scratch runs in runs/laneRL/ (gitignored; archive with tar -C <wt> runs).

## Done (committed)
- Terms: core/machine.ts E has `tup(a, b)` (Cantor pairing cpair = tri(a+b)+b, right-nested n-tuples) and
  `proj(k, a)` (cun's parts). Runtimes evaluate both exactly (cpair/cunpair; throws past 2^53).
- Kernel (kernel/kernel.ts) mirrors Lean (lean-kernel/Kernel.lean): linear(tup) none; `keyParts` = Lean `parts`
  (tup: parts' forms; proj 1: the rest when ≥ 2 left); linear(proj 0 e) head of parts, proj 1 the last of two; a read
  at a key with parts is the cell `M[⟨k1|…⟩]` (Lean `cellT`); two tuples equal ⇔ parts equal (truth/facts as `and`);
  cell equality part by part (`sameKey`, Lean `keysEq`). Names reserve ⟨ ⟩ |. `mapArities`: one key shape per map;
  each-writes on n-part maps checked part by part (`eachParts`).
- Lean: Kernel.lean +~700 lines, all modules build, axioms propext/Classical.choice/Quot.sound;
  `bun lean-kernel/export-kernel.ts --tuples` (tuple goals, tampered cellT equality refused, two relation machines
  end to end via smachine_sound). Runs: runs/laneRL/final1, lean-k5.
- Untrusted: prove.ts (tuple cell pairs part by part, instances read tuple parts), kernel/reader.ts (CDCL reading),
  cdcl.ts (pairs per part), epr.ts (tup keys as part tuples, pattern n zeros; witness names tuple cells).
- Runtime: interpreter decides quantifiers and writes at every tuple on per-part breakpoints (writeEveryTuple);
  compileJs refuses tuple keys at every key.
- DSL: `.sorts('Node')`, `.relations({T: ['Node','Node','Node']})` → RelRef: at/has/add/remove/each/union.
- Ports: research/protocols/ic3syn/models.ts learning_switch and learning_switch_i4 are native now (no phase);
  the phased ones kept as `phased`. relations/hand.ts: published invariants. learning_switch + help_3/help_4
  PROVEN in 5.5 s (main: unknown at 300 s). i4 with manual_1..4 + "nothing before start": transitive passes,
  antisymmetric runs out at 60 s (261 hyps).
- Random CTI check (relations/cti.ts, boat): learning_switch invariant inductive on 98 random good states.
- All other TS walkers handle tup/proj (602656b); tsc clean outside infer.ts/machine.ts/prove.ts (fix those).

## Next, in order
1. tsc errors left in core/infer.ts (3), core/machine.ts (1), kernel/prove.ts (3) ('a' in e patterns: use 'b' in e).
2. Engine (core/infer.ts): tuple atoms as candidates (R(t,y,t), R ⇒ S at a projection, 4-place with don't-care
   places); IC3Syn run: runs/laneRL/sw1 both unknown (join rounds 0: time spent on laws as given; Lane MC owns the
   laws-as-given budget share in proveRule — don't change it).
3. agree.ts: native vs phased ports agree on random request sequences (phase rows run to the end).
4. check.ts/TLC state counts for the native ports (43,672 and 240).
5. kernel/mutants.ts over the new kernel lines; adversarial tests (kernel/tuples.test.ts, add to test shards);
   pi reviews (sol xhigh + terra), read-only.
6. Gates: IC3Syn 29×3 strict 60 s pinned; DuoAI ten; bun bar vs main; test shards; Lean e2e of a switch proof.
