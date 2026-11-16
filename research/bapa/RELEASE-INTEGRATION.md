# BAPA accepted-lane integration

Integration base: `413865f38` on `bapa/finish`. Accepted patches are applied by exact commit, not by lane tip, to exclude ongoing sharded_kv, Paxos, and MLDR proof work.

## Accepted imports

| Lane | Exact source commits | Scope |
|---|---|---|
| p1 | `a22e80195`, `e96db114a`, `2f8698641`, `2dc6f4edc` | lock_server replay; complete multi-parent witness firewall bridge; SDL source transport; **structural-only** sharded bridge |
| p2 | `dd05b37c1`, `17733ca9e` | source inclusion / toy acceptance; generic finite-step simulation (not a Paxos source acceptance) |
| p3 | `1dd07c7ce`, `a50ef765d`, `2895caf6d` | per-sort typed substitution, complete init/step goal checks, client source proof |
| p4 | `db9bd046d`, `6c001414d` | source inference wrappers and checked source-alpha transport; no-lost source replay |
| transport | `d989424d5`, `3f60b1d5f`, `2ce3c8dd5`, `519a34423` | bound erasure, radix primitives, client translator, fixed radix-certificate prerequisites required by SDL and the accepted structural bridge |

These imports preserve both uniform and typed bound substitution APIs, every witness provenance parent, existing source inference checks, and the integrator's model-confirmation / configurable-rounds SHAREDs. No trusted kernel or Lean kernel file was changed by this import.

## Source-port integration

The first accepted-bridge import exposed missing historical source-port commits in `models.ts`. Integrate p1 `a3378d565`, p2 `11729529a`, and p3 `cbab14560`, preserving both README sections. From p4 `f6a5e18dc`, take only the accepted quorum/majorityset definitions and the no-lost source branch. The no-lost builder is isolated from legacy `shardedKv(false)` so the ongoing sharded_kv, Paxos, and MLDR definitions are not replaced by their lane versions. Their proof/search work remains untouched.

The earlier gate at `18171bbe3` is a baseline diagnostic, not a final single-tree release gate. Final replay/gates must use the completed source integration plus the sealed replay manifest.

## Release verification policy

The next gate must replay the 26 accepted protocol receipts on one integration source tree. Inputs must be bound by SHA-256. Existing proof terms/capsules are reused without protocol search or reseeding; no new source acceptance is inferred from a partial/structural receipt. The remaining sharded_kv, Paxos, and MLDR work stays outside the acceptance count. The exact replay inventory and outcomes will be recorded separately. Integration alone is not a successful replay or a release claim.
