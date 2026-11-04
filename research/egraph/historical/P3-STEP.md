# Historical P3 @step — checked counted proof

**P3 `decision has quorum @step` is closed under the original full six-law
inductive context.** This does not close `one-value-decided @step`, prove the
entire conjunction, rerun P3 @start, or establish native/full-frontier admission.
No production/kernel/prover source was changed.

## Exact source and context

Original P3 goal SHA256:
`a7cee3dd679c5c19df5fd6110c24a723158e8644299c98243df8c0513bd57357`.

The originally missing count/instance provenance was reconstructed from existing
rows and verified through unchanged `countedObligations` and `mcGoal`. All **76
original rows match in their original order**. The new count proposal preserves
all 76 plus all 15 original count instances and five picks.

Kernel SHA256:
`596eaaea9a44a11330178ac37b55377f5747a4ed08a8dd010c26b393c69521e2`.
Prover SHA256:
`5e4232da2abe25c1153edf790af4b339d2be8482c5630b0740315c79f60ce708`.
The whole `kernel/` tree and relevant solver/machine source are unchanged from
the canonical M2 baseline; changed frontend/count-search files are not invoked.

## Diagnosed bottleneck and one proposal

The canonical `core/counts.ts` generates the set-difference bridge after pair
instances, then the wide path truncates to ten before adding its further pool.
The recovered P3 choices lack this bridge. The research adapter selects one
instance of the **existing checked count schema**:

```
+ members - missing - postVotes, unit = 0, bound = size
terms = [[1, "r$2"], [-1, "r$0"], [-1, "r$1"]]
fresh witness = "w$bridge0"
```

It does not assert the desired arithmetic inequality as an axiom: the unchanged
kernel constructs the count lemma's disjunction including its witness/body
branch and checks the resulting proof. Enabled has **77 rows / 16 instances**,
still below the existing 24-instance wide threshold used by this proposal.

## Native comparison and controls

Batch `20261104-124537-4hblor`, uploaded tree `dd822557f7f5`, worker exit 0.
Requested 2 CPU / 4096 MiB / 600 s. Both cases retain the historical 25-second
outer prover ceiling and have an additional equal 2m work guard. These are
untimed correctness observations, not shared-runner speedup claims.

| Case | Result |
|---|---|
| Original context, bridge ablated | `sat`, no proof |
| Same context, bridge enabled | unchanged `checkMC` accepts |
| Remove bridge from successful certificate | rejected |
| Fresh Bun process reconstructs and checks certificate | accepts |

Scoped TypeScript and type-aware lint also pass. The fresh checker does not
import or invoke the prover.

## Independent coordinator acceptance

Coordinator main independently accepted this certificate in batch
`20261104-125113-fo8xbu`, worker 0, without importing or invoking the prover.
Its review checks exact ordered original rows, six-law scope, original
reads/picks/instances, the precise legal bridge, fresh witnesses, successful
`checkMC`, and bridge-removal rejection. Record in the coordinator tree:
`runs/coord-reviews/P3-BRIDGE-v10/ACCEPT.md`. This is P3-step-only acceptance,
not a full M2/native flip and not permission to merge or push.

## Retained proof

`research/egraph/historical/proofs/p3-bridge-step.json` — 12,354 bytes.
SHA256: `d72bcca7891d1273cceb9f4db1bed0dc02e9f66cb65c56e51184b676d131499b`.

Native receipt: `runs/astra-p3-bridge-v10/receipt.json`.
SHA256: `9e2ea4cf427cbbdc25f42da7210bdc8a46e2c080b56d090f6cc96ea7b620ad3f`.

The raw paired outcomes, cold-check event, proof artifact, source hashes,
summary, backend and placement are retained in `runs/astra-p3-bridge-v10/`.
All previous failures, TIP evidence and original source branches remain intact.
