# Verified component checks

All execution was on supercomputer/boat, not local Lean or local tests.

## Passing native gate

- Immutable development-check snapshot: `d81c320ff400e709b60c833f599745326bde37db`
- Snapshot tree: `bb1d1a61266dc9f668e9977e71252cd41d0e4b10`
- Batch: `20261116-032326-q6vj2f`
- Receipts: `lean-kernel/lift-special/runs/frozen-snapshot-04/`
- `bound-inclusion-unit-native`: native exit **0**, 33.22 s.
  TypeScript check clean; 5 tests / 30 assertions passed. Entire generated
  two-entry retained family checked by Lean; quantified public source theorem
  checked after structural disjunctive weakening.
- `structural-weakening-native`: native exit **0**, 25.4 s.
  Generic arbitrary 3-to-5 nested disjunction inclusion and contravariant
  negation checked, along with the generic soundness and law lemmas.
- Canonical `lean-kernel/StructuralWeakening.lean` checked SHA-256:
  `30b34e4341ea4afefef76301d8b69d9eb2c81acd384e497346988a8526e9ff45`.
- `Bapa.StructuralWeakening.sound` and `.law`: axioms `[propext]` only.
- Generated `bapa_opaque_source_law0_holds`: axioms
  `[propext, Classical.choice, Quot.sound]` only.
- Worktree removed after completion; real index untouched. Development-check
  snapshots were unattached, not commits to the working branch.

Earlier receipts are retained honestly: unit-01 stopped on a fixture parse
error; unit-02 exposed TypeScript narrowing, a test mutation alias, Boolean
rewrite syntax and the old-library selection issue; frozen-snapshot-03 passed
all TypeScript tests but exposed the final negation rewrite mismatch. Those
were corrected before the passing gate above. No failure was relabeled LOST,
no existing historical capsule job was replayed.

## Current source fixture

The test-only constructor export (no proving/search) produced
`runs/frozen-snapshot-04/bound-inclusion-unit-native.files/current-toy-source.json`
with SHA-256
`88e5d2ddf6a0ae0d7eef276e12105f7a8402420ac3fafef9830b4ca6bd2e5303`.
It has the current `size, values` parameters and is not the old bounded capsule
source. Production code never imports the protocol registry.

The real capsule's shared shape receipt was read from the other owner's
`toy-ast.json`; no duplicate graph inspection was run.

## Passing real public CLI integration

- Immutable snapshot: `6d76723b1c9580848e0f94f09f885814ecfb4ecc`; tree
  `dc42744b89f73cf129c1b7d547e36c249a007f8d`.
- Batch `20261116-032918-j3614k`; native exit **0**, 66.48 s.
- Public `liftMain`, no research replay entry point or protocol search.
- Capsule SHA-256 `33f1a9949fb71fec0b5c1017c0607b25517a4222de10f0634bddc9bd4d8ae84b`.
- Supplied source SHA-256
  `c3db4a2c439a60a39d56521c899d85618734afea5c0ebc961ab5850ca8cb98e5`
  (the frozen fixture includes requested theorem names).
- Entire retained family: **8 entries, 16 primary obligations**.
- Syntactically derived bound: 64; structurally selected public index: 2.
- Both `lake build` and `lake env lean BapaProof.lean` exited 0.
- **19 required theorems audited**, all using only a subset of
  `[propext, Classical.choice, Quot.sound]`.
- Public family: `bapa_toy_consensus_forall_transported_laws`.
- Public source: `bapa_toy_consensus_forall_source_law0_holds`.
- Native receipt: `runs/public-toy-02/bound-inclusion-public-toy.files/project/LIFT-CHECKED.json`,
  status `SOURCE_CHECKED`. Emitted manifest remains `EMITTED_NOT_CHECKED`, as
  intended; the checked receipt is separate.
- `public-toy-01` was rejected **before admission** due to an unsupported 32GB
  resource request; no native attempt ran. The accepted run requested 8GB.
- All development-check worktrees and temporary alternate indexes cleaned.
  Canonical helper is now only `lean-kernel/StructuralWeakening.lean`; runtime
  and test harness both read the product library, not a duplicate local file.
