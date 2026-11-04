# Published-invariant ground-model regressions

The first five fixtures are exact saved models and goals from Astra's
`gen/mldr-astra` `runs/ground-truth/snapshots`, supplied by the coordinator for
general instantiation/counting regressions. Each JSON wrapper records its source
and contains gzip/base64 JSON with machine, complete supplied law set, ground
goal, witness and count declarations. Historical fixtures also retain MC read
and instance metadata. No fixture law is a trusted axiom outside kernel checking.

Published sources used by Astra's translation:
- mypyvy `examples/pd/paxos_epr.pyv`, commit
  `12a8f5434a25587c56814d090b6ab7fa95851e71`: safety and five invariants.
- Endive `benchmarks/MongoLoglessDynamicRaft_IndProofs.tla`, commit
  `8b6f2abd1988eeb308f965813635e9871f253e2d`: TypeOK, safety and five
  strengthening clauses. The historical phased MLDR snapshots use the explicitly
  labeled `started=1` projection guard and explicit role-range TypeOK.

`kernel/published-ground.test.ts` checks:
- `paxos-P5-19`: the sampled safety model omitted the vote-to-proposal instance
  at `(1,7,0)`. The proposed ordinary instance blocks the saved model through
  the unchanged kernel.
- `mldr-M1-13`: the sampled safety model omitted term backing at `(2,0)`;
  its falsity is checked using actual source count evaluation.
- `paxos-P1-23`, `mldr-M1-16`, `mldr-M4-9`: sampled ground models have explicit
  count values inconsistent with their reconstructed sets. Existing concrete
  completion refuses them; a ground SAT result is not a protocol counterexample.

## Atomic source-action regressions

The four `atomic-*` fixtures retain unchanged failure goals and witnesses from
Astra's `runs/atomic/published-snapshots`. Their machine, complete supplied law
context and count declarations were exported from Astra's current atomic
`research/protocols/ground-truth/published.ts` constructor, without a prover or
invariant-search call. Source filenames and clause names remain in the wrapper
and payload. Unlike the historical snapshots, these use the atomic ports; no
phase guards or new strengthening was introduced here.

- `atomic-paxos-P3`: a quorum member explicitly has no vote, but missing=0.
- `atomic-mldr-M4`: an explicit Q2 member contradicts inQ2=0.
- `atomic-mldr-M3`: TypeOK at server2 excludes St[2]=2; the ordinary and
  sort-aware instance paths both block the pinned model with a checked proof.
- `atomic-mldr-safety`: the missing M4 instance is `(3,2)`, checked against the
  source's actual counts.

All four are rejected/refined by the existing Q3 code; no further production
change is required for these snapshots. These are model-level regressions, not
a claim that the full atomic published sets are proved.

These tests do **not** assert that either published conjunction is inductive
for the port's auxiliary phases. Astra separately identified valid microstep /
initialization induction counterexamples. No full target proof is claimed.

The bounded coherent-read join used by the general proposer is adapted from
Astra's earlier untrusted MBQI experiment. Constant-coordinate matching and
materialized-model keys are needed by these concrete saved models.
