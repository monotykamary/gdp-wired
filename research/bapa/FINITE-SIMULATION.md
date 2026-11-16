# Finite-step source simulation

`FiniteSimulation.lean` is the general multi-step counterpart to
`SourceInclusion.lean`. It does not modify any machine, transition, or law.

## Checked contract

`ForwardSimulation Is Rs It Rt rel` requires an initial matching reachable
producer state and a finite producer path for each admitted source edge from
related reachable states. `Steps` is inductive: reflexivity plus finitely many
actual edges. The target does not have to match at intermediate scan states.
`ForwardSimulation.reaches` proves every reachable source state has a related
reachable producer state. `transfer` transfers a separately proved property;
`projected` specializes this to equality under a projection.

`Initial`, `STransition`, and `CTransition` encode the kernel's exact constructors.
The conversions `sreach_into/out` and `creach_into/out` are checked. In particular,
every `CTransition` includes `GHolds` for the producer declarations on that
request's actual input/carried-map view. Counts are never discarded.

- `SSimulation` and `CSimulation`: concrete kernel interfaces.
- `sprojected_reach` / `cprojected_reach`: reachable matching producer exists.
- `sprojected_law` / `cprojected_law`: law transfer under a full-state projection.
- `cobservable_law`: compare observable stores, not input temporaries; allows the
  projection to forget producer scan registers and source request temporaries.
- `safter_inclusion` / `cafter_inclusion`: compose after the existing checked
  same-step bridge from `dd05b37c1`.

The relation can include a phase-boundary invariant (`busy=false`, cleared scan
registers, and public-store equality). None of this is an assumption that the
post-state is reachable: reachability is derived by applying the finite path.

## Scan scheduling lemma

`PaxosEprScanSimulation.lean` proves `complete_scan` for a parameterized scan
state carrying `busy/cnt/pr/pmaxr/pv/qs` and a public store. Given positive size
and admission of every required row, the start plus finitely many node checks
reaches an idle state whose public store is exactly the atomic commit. Interior
scan nodes preserve the old store. `complete_counted_scan` maps these edges to
actual `CSteps` when a client proves the edge-encoding obligations.

**Remaining concrete obligation:** instantiate the row/commit/store operations
and edge encoding against the hash-bound emitted atomic source and the final
translated producer. The scheduling lemma alone does not establish Paxos source
acceptance. Bound support, guard correspondence, non-Propose steps, initial
matching, and public-law projection also remain explicit.

## Negative control and evidence

`FiniteSimulationControls.unreproducible_propose_refused` proves no such forward
simulation exists for a minimal atomic Propose that commits a proposal despite
a rejected scan row. The producer can start and reject repeatedly but can never
produce the proposed public state. This is a semantic negative control of the
generic contract, not yet a mutant of the full emitted Paxos source.

Batch `20261116-002138-oioo9w` passed all seven Lean modules and commitlint.
General reachability/projection and the negative control use no axioms; the
kernel adapters use only `propext`, `Classical.choice`, `Quot.sound`.
Artifacts: `runs/bapa-p2/finite-simulation-2/p2-finite-simulation.files/`.
