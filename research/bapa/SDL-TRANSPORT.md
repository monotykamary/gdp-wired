# Decentralized lock: retained tuple transport and original source bridge

## Result: SOURCE_CHECKED, every size

The complete translated family, exact global SUM semantics, and original
symbolic-source safety theorem are checked. Final receipt:
`runs/bapa-p1/sdl-final-02/sdl-source-receipt.files/SOURCE-CHECKED.json`.
Receipt SHA256:
`ab7678282f430847817cf46886044c6d796759d5475b92121779efb0b09b8201`.
Source AST SHA256:
`fe12e0ff314f4802d68cc42cb7fb94088e492780ae131398a87f625328fda1ac`.


## Scope and identities

P1 owns this family exclusively, delegated by bapa-transport. No proof search,
seeding, induction synthesis, or finite-subsum replacement is used. The generic
translator files remain untouched. Dependencies are transport commits
`3f60b1d5f`, `2ce3c8dd5`, `7b159195a`, and `4b7007aa3` (bound-erasure dependency).

The corrected retained capsule is
`e123183e89e3d5e0378d9aaf3e4d00a5f7e55b3584821faf0c6fa2d739e82958`.
Its `Proofs.lean` SHA is
`95b20356ad9606abd1e4ea2489f8473c72b50451424b3ebdd2f13443528d5e2c`.
The original source pin is `58fa3bced2bad84e9f0be84e4340c2c750f60e9d`.
Use the corrected `release049-fprime-sum-cover-v2` artifact, never the earlier
failed decentralized-lock emission.

## Translation

`SimpleDecentralizedLockTransport.lean` specializes the shared candidate phases:

- Only Message/map0 has a binary layout; HasLock/map1 remains unary.
- Message writes and SUM cover addresses use `cpair(src,dst)`, not `64*src+dst`.
- The two SUM integrands remain raw, whole-address map reads. `IsSum` is over
  **every encoded natural address**, not a selected finite set of query points.
  Pairing is the kernel's unbounded bijection. The SUM machinery's own finite
  change covers are retained and checked separately.
- The Message kind-law binder expands to two components. Opaque raw addresses
  in the SUM layer remain raw; incidental kind-law instances can decode them.
- All four original family entries, both init/step obligations for each, and
  the one HasLock SUM-cover tree are translated without a search. Every
  resulting leaf goes through the unchanged kernel.
- A concrete literal snapshot avoids expensive repeated reduction of the
  candidate transformer. Kernel-checked equality proves that its **entire
  certificate family and cover trees**, not just its claims, equal the adapter
  output. The complete literal family and `checkSums` are then checked.

`SdlExactTransport.lean` composes the complete family with the exact SUM kernel:
`exact_sums`, `own_admission`, projection through valid sum ghosts,
`message_bound`, and unbounded `mutual_exclusion` on the underlying rule.

## Original source bridge

`sdl-source-data.ts` emits the actual symbolic rule and original public law
from `research/protocols/ic3syn/models.ts`, in an explicit checked basis. It
records the model, AST, emitted Lean and basis identities. No prover is called.

`SdlSourceBridge.lean` proves an operational simulation of that exact source
into the checked target. A simple syntactic comparison is insufficient:
source Message reads use `>=1`, the retained target uses `=1`, and their
stuttering writes differ on non-Boolean maps. The simulation therefore uses
`message_bound` from the already checked complete family at each induction
step. It proves view equality, map/step equality, source admission inclusion,
and source reachability inclusion. Source initialization is also checked.

The final theorem is:

`bapa_simple_decentralized_lock_source_law`

It states the original emitted public law on every reachable source state,
with its symbolic size parameter intact. There is no `size <= 64` premise.
Only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms occur.

## Evidence and controls

- `sdl-transport-10` / `20261116-000338-uj3dkt`: successful modules establish
  complete snapshot identity, **8/8** plain obligations and the full family,
  **2 exact SUM declarations / 1 cover obligation**, exact sums, own admission,
  source-base projection and mutual exclusion. Its final source module failed
  on unfinished simplification; that module is not counted as accepted there.
- `sdl-source-01` / `20261116-000900-376tdn`: source-only repair, exit0. Reuses
  the previous successful dependency modules by source/artifact hashes and
  checks the complete original-source theorem. No family replay or search.
- Required-certificate deletion keeps all four entries but removes the public
  step proof: refused. An empty family is vacuously checked and is deliberately
  **not** used as this control.
- Deleting the required cover: refused. Reintroducing a surviving radix64
  bound row: refused.
- Final receipt/static job `20261116-001734-0zpvph`, `sdl-source-receipt`,
  exit0: TypeScript check, four custody tests and commitlint pass. The receipt
  covers all 17 required named theorems. The batch's other job had a path/setup
  error before its negative proof check; that is not counted as a control.
- Broken-source-only batch `20261116-002224-hr1xsv`, exit0: actual source variant
  `send keeps the lock` is refused at the map-step correspondence proof
  (`SdlSourceBridge.lean:28`). The positive source proof was not rerun.
  Evidence: `runs/bapa-p1/sdl-negative-03/sdl-broken-source.files/`.
- The initial final-gates attempt caught a test-name replacement typo and an
  incorrect Lean working directory. Both were repaired; no proof statement or
  checker was weakened.

`sdl-source-verify.ts` consolidates the already completed checks. It demands
all 17 named identity, family, SUM, control and source theorem outputs, checks
source/module hashes, and applies the standard axiom gate. Custody tests
remove the source theorem, remove the SUM-cover theorem, or alter the source
AST emission; all must be refused. The broken source variant keeps the lock
on send and must fail the same operational bridge.

Development failures (syntax/serialization, missing equality instances,
expensive recursive reduction killed137, and incomplete source simplification)
remain in `runs/bapa-p1/sdl-transport-*`. None is promoted to acceptance.

## Replay

Only run through supercomputer, strict-once/max-attempts1. `sdl-transport.jobs.json`
expects the corrected artifact root, including `lean/`, mounted as `sdl-retained`.
It builds the original dependencies and complete final project. The source-only
recipe `sdl-source.jobs.json` additionally expects the successful dependency
module artifact directory as `sdl-prior`; it refuses changed dependency source.
`sdl-final.jobs.json` expects `sdl-retained`, `sdl-prior`, and the completed
source-only artifacts as `sdl-checked`, and runs custody/static gates alongside
an independent Lean rejection of the broken source. All artifacts go into
`SUPERCOMPUTER_OUTPUT_DIR`.
