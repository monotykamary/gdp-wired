# Sharded KV actual-source structural bridge (p1)

Status: **STRUCTURAL_BRIDGE_CHECKED; final custody and negative gates passed.**
This is conditional transport, **not SOURCE_CHECKED**.

Exclusive scope confirmed by transport/t11 and p4/t9. This slice owns only
`SktSource*`, `skt-source*` and this report. Transport retains all shared and
Sharded/Radix translation/certificate logic. P3 retains all MLDR parts.

## Frozen identities

- Target commit `4434fc8d0ebebe6b6f92d8844a2f22a3216450e9`.
- `Bapa.ShardedKvSnapshot.machine`, from retained `Snapshot.lean` SHA256
  `2bef0af2d1fb819fa5f1f7ac67dc4cb27e6893e49775edf318a13be1f6f96ea5`.
- Actual source: p4 `research/protocols/ic3syn/models.ts` SHA256
  `3063304ae3bf8d7c7cc9870c838f7f5da7ab916a96d3729a7ca0b8db5f5b1d76`.
  This is **not** the old bounded source that generated the retained capsule.
- Matching common frontend module SHA256
  `d84face9091688872b001f28d0ff31f1180590c57bf944efe6b32168651cd324`.

Source export stages the byte-pinned original with only its three import
locations redirected to this checkout. It retains both byte streams and binds
the frontend hash. The local/p4 DSL difference is only candidate-seed options
and their proof-entrypoint forwarding; this data-only export invokes neither.
No source rule, bound, flag or public law is changed.

## Intended proof boundary

Keep all three independent sizes (`nodes`, `keys`, `values`) and zero-size
cases. Hide only source `Owned` (map3). Table/Owner/TransferMsg remain maps0/1/2;
all other maps are preserved. Retain source request admission and disabled-step
stuttering. There is no size<=64, positivity or equal-sort premise.

Hypothesis to test: source initialization and updates imply Boolean Owner and
TransferMsg cells and zero Owner cells for nodes outside the source Node sort.
These facts equate bounded/unbounded unowned flags and >=1/=1 relation reads.
The Owned map is a discardable ghost for the noLost=false protocol. Establish
these facts directly by source reach induction, never from individually checked
retained steps or the still-false family check.

Deliver source init/step/reach simulation and original public-law projection
**conditional on target safety**. Target checkpoint has26/46 checks, family=false;
no unconditional source safety or SOURCE_CHECKED claim is permitted here.
The broken `put without ownership` variant must be separately checked before
claiming its refusal. No proof search, seeded work or accepted family replay.

## Current work

- Confirmed source and Snapshot hashes locally.
- Data-only source emission `20261116-002831-dtkdoo` passed; output
  `runs/bapa-p1/skt-data-01`. Source AST SHA256
  `cde3dda1297299928d310c5dd57ca96d97e3e90aa83489dfd42117f2241482e7`;
  Lean literal SHA256
  `150babf4d07932842597d5d17783006cac52a8e7421f81cd88ad80e211e8b754`.
- Gate `20261116-003142-e7rj52`: source literal and target identity compiled;
  the invariant draft failed on lookup/Boolean simplification, not a checked
  semantic counterexample. Its complete failing log is retained in
  `runs/bapa-p1/skt-invariant-01`.
- `20261116-003605-d3hmi8`, output `runs/bapa-p1/skt-bridge-02`, accepted the
  corrected source invariant. `SktSourceInvariant.lean` SHA256
  `277a67cbc69447e8f9716373f87e9ee510098773a67220b7a2eece2ea3f761fc`;
  olean SHA256 `6c46679ec75940508ae66018179c11383385d6bcf80512a110973886bce1f896`.
  Only `propext`, `Classical.choice`, `Quot.sound` occur in its axiom reports.
- Bridge draft `20261116-004125-4m0605` reduced the remaining failure to scalar
  step normalization. The view, all map updates, admission and initialization
  lemmas had standard axiom reports, but the incomplete module is NOT accepted.
- Final scalar correction passed in `20261116-004245-5ej8qh`, output
  `runs/bapa-p1/skt-bridge-04/skt-source-bridge.files`. All accepted
  source/target/invariant modules were reused, not recompiled. The complete
  source bridge compiled with only the three standard axioms above.
  `SktSourceBridge.lean` SHA256
  `ad5f3835514c6be06ed1b4336304aae2d87fa7ea335ae50b26fef195853a7f51`;
  olean SHA256 `cda9928019f10aa4ededecc7e3226e3c2fa1a23f39a7233b2a03e0bcdc3463c6`;
  log SHA256 `b766b59f113d2617397f01a4d1cb49b122e97943dd4b300e614ef2a3ee7b6670`.
- Final batch `20261116-004629-5sh2uf` passed both jobs. Typecheck, eight
  custody tests (10 assertions), and commitlint passed. No Lean replay in the
  receipt job. Final receipt:
  `runs/bapa-p1/skt-final-01/skt-source-receipt.files/STRUCTURAL-BRIDGE.json`,
  SHA256 `ea888011ba0d9172957c8e7f62f8ff647ab3a4716464584a294ef2d33861c3be`.
- The actual broken `put without ownership` source was refused by the same
  bridge: `SktSourceBridge.lean:51`, `skt_plain_flags`, with zero Owner cell,
  `op=4`, `started=1`, leaving `False`. Its source and invariant dependencies
  compiled first; this was not a setup failure. Negative source AST SHA256
  `81ff0821e1f4e0c29b581342fe661495293e40bd439fec4db49dfc3163d528d9`.
  Evidence: `runs/bapa-p1/skt-final-01/skt-broken-source.files/NEGATIVE-SOURCE.json`
  and `broken-source.log` (SHA256
  `ab0b536d09b838d01d983939446cf376fdfc86ea72989f21b645b170d81e326a`).
  The refused bridge source is byte-identical to the accepted positive bridge.

All launched admissions are terminal. No shared helpers were modified and no
optional preserve-mode API was adopted. Frozen dependency sources and oleans
are enumerated in the final receipt; the retained checkpoint remains4434fc8d0.

## Checked theorem interface

- `skt_source_invariant`: source reach implies both Boolean-map invariants and
  off-domain Owner zeros, with no target-family premise.
- `skt_q_eq`, `skt_view_eq`: exact bounded/unbounded quantified-flag and request
  view equality under these source-derived facts.
- `skt_maps_step`, `skt_step_eq`: projected maps and complete next-state
  equality; raw whole-map updates keep the exact unbounded tuple bijection.
- `skt_admission`: source admission implies target admission. On source-admitted
  requests, guarded updates and disabled-action stutters agree exactly. The
  unbounded target may admit additional requests; inclusion is one-way.
- `skt_init_state`, `skt_init_maps`, `skt_source_init`: initial state/map
  projection and target initial reachability.
- `skt_source_reach`: `SReach skt_source ρ M` implies
  `SReach skt_target ρ (sktProject M)`.
- `skt_target_identity`: the data target equals
  `Bapa.ShardedKvSnapshot.machine` by `rfl` (no axioms).
- `skt_source_public_law_conditional`: original source public law, assuming
  the target public law for every target-reachable state. Its premise uses
  `Bapa.ShardedKvSnapshot.entry2.law` and the exact `entry2.keys2`, not a weaker
  hand-restatement. Supply the eventual checked target safety theorem here.

This does not change the target's certified26/46 result, prove the remaining
20 steps, or increment the suite's accepted-protocol count.

## Artifact custody and reproduction

`skt-source-data.ts` emits the pinned original port, complete machine/law AST,
injective variable/map basis and literal definitions; no solver is called.
`skt-source-check.py` copies receipt-matched frozen helper/Snapshot oleans and
compiles only new source modules. `skt-source-data`, `skt-checked`, `skt-aligned`,
and `skt-retained` are explicit supercomputer data mounts; `skt-prior` optionally
supplies already accepted source modules. The source literal and immutable
Snapshot hashes gate reuse. The resulting `LEAN-RECEIPTS.json` binds every
source and olean; missing original olean hashes were bound in this receipt.

The original target inputs remain transport's accepted
`sharded-snapshot-v4/sharded-kv-concrete-alignment-check.files` and
`sharded-aligned-v1/sharded-kv-aligned-certificate-replay.files`, with the
matching original capsule's `lean/` library. No current shared helper files
are imported during checking, so transport's later optional preserve API is
not adopted accidentally.

`skt-source-verify.ts` requires all15 named theorem outputs, the byte-pinned
original source, exact AST/literal/basis, immutable target identities and every
recorded olean. Its only accepted status is `STRUCTURAL_BRIDGE_CHECKED`, with
`sourceSafetyChecked:false` and `targetSafetyRequired:true`.
`skt-source-final.py` checks the receipt without replaying Lean; separately,
it emits the real broken port (`put without ownership`), recompiles its source
definition and dependent invariant, then attempts the *same* bridge proof.
A setup error is not counted as a negative-control refusal.

Use all jobs with `--strict-once --max-attempts 1 --backend boat`; do not rerun
already accepted family or source modules simply to collect their artifacts.
