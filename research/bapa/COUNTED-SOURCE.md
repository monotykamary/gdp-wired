# Counted-family source projection

`proof-counted-source.ts` is a no-search, fresh-process source exporter. It reads
an immutable closure, replays its exact term prelude, and keeps the **whole**
retained counted family in the split proof from `proof-parts.ts` / `FamilyParts`.
It does not select only the public entry or turn inferred helpers into axioms.

The source machine and all its original count declarations come from
`bundle.original`. Derived Venn/region declarations come unchanged from the
producer. Both are rendered in the producer's numerical variable/map basis;
source-only names are appended, never inserted into the producer prefix.

## Checked correspondence

- `CountedSourceProjection.lean` constructs counted requests with `counts_exist`
  and proves agreement of the original count interpretations.
- `CountedNoninterference.lean` derives public step agreement from the finite
  `StepAvoids` syntax check, including quantified flags and per-row map updates.
- `CountedSourceBridge.lean` lifts original source reachability to the machine
  with additional carried count maps. It derives this simulation; it does not
  assume that a source run already has a producer run.
- The generated root checks `QAlpha` renames, exact whole-machine equality after
  adding only fresh carried maps, original count-declaration inclusion, the
  reverse inclusion for nonfresh counts, freshness, and exact public-law/key
  membership. It transfers the full producer theorem back to the original law.

These are candidate proofs until the emitted project passes Lean. No finite
maximum size occurs in the source theorem: it quantifies over valuations and
inductive source reachability. This does not by itself certify all 29 protocols
or any external model-to-port correspondence.

## Split-check recipe

Run in the pinned 0.49 runtime in a fresh process, with the exact manifest hash:

```sh
bun research/bapa/proof-counted-source.ts \
  --capture /data/closure --sha256 SHA256 --out /output/project \
  --weight-limit 1000000
cd /output/project
lake build > /output/lean.log 2>&1
# Print the exact public/family dependencies even if Lake reused an object.
lake env lean BapaProof.lean >> /output/lean.log 2>&1
bun /work/gdp-wired/research/bapa/proof-source-verify.ts \
  /output/project /output/lean.log /output/SOURCE-CHECKED.json
```

Use `supercomputer` for these builds. `--weight-limit` bounds the structural
frontier proxy, not RSS or proof difficulty. A context or leaf exceeding the
limit fails closed; it is not dropped or replaced. The emitted receipt says
`EMITTED_NOT_CHECKED`, `leanExecuted:false`, `allSizesProven:false`.

`proof-source-verify.ts` does not run Lean. After the build, it checks the exact
emitted file hashes, clean completion, permitted axioms, and **named** output
for every public source theorem and the whole-family theorem. Only then does
it write a separate `SOURCE-CHECKED.json`. This is evidence for that captured
source and those public laws, not an automatic 29/29 release claim.

## Limits

The current bridge admits plain source-law metadata and nonrecursive count
declarations with exact inclusion in the producer. It refuses changed source
count definitions, missing public laws, source-machine drift, unsafe alpha
capture, history/sums/functions, and witness metadata requiring another route.
No witness, capture repair, or transport/padding result is implied.

## Verified evidence

Independent semantic review found no source-semantic blocker. The generic
projection, Boolean noninterference check, two-machine step theorem and composed
source bridge were checked together in `20261115-200541-3tug2p`.

Batch **`20261115-201417-r2eube`** passed types, **6 tests / 25 assertions**, the
tiny original-plus-derived-count Lean control, commitlint, and complete
source/axiom/file-custody gates for these retained families:

| Protocol | Public entry | Source theorem |
| --- | ---: | --- |
| `simple_election` | 3 | `bapa_simple_election_source_law0_holds` |
| `toy_consensus` | 1 | `bapa_toy_consensus_source_law0_holds` |
| `quorum_leader_election` | 1 | `bapa_quorum_leader_election_source_law0_holds` |

Receipts are under
`runs/bapa-counted-source-02/counted-source-gate.files/<protocol>/SOURCE-CHECKED.json`.
Each records the exact input capsule, emitted-file hashes, Lean-log hash, full
family theorem and public theorem names. The nested emission metadata retains
its original `EMITTED_NOT_CHECKED` label; the enclosing checked receipt is
`SOURCE_CHECKED`. There was no new search. These three source proofs do not yet
establish the remaining counted protocols or a 29/29 claim.
