# C33 — original family19 STEP certificate and emission diff

## Verified certificate

`goal.json`, `proof.json`, `source.json` retain the original STEP request, checked tree, exact family indices and PRE instances. `check.json` is a **fresh zero-search** receipt: `checked=true`, `rawMatches=true`, `declsMatch=true`, `encodedMatches=true`, fixture hash matches, `searchWork=0`, and no nonzero search costs. Raw and encoded goals both have **21 hypotheses**. `final-validation.json` additionally records structural equality of the supplied family fixture and the unchanged original `runs/track-p-gap-source/fixture.json`.

Write `a = key1$enum#`, `b = key2$enum`, `c = key3$enum`. The five retained PRE tuples are:

| Index | Tuple | First emitted by generic/hand closure, both flag modes |
|---|---|---|
| 33 | `(a,b,c)` | prepare |
| 3 | `(64*a+b)` | prepare |
| 3 | `(64*a+c)` | prepare |
| 61 | `(b)` | closure:0 (late relative to preparation) |
| 61 | `(c)` | closure:0 (late relative to preparation) |

**Empty CountCert is sufficient:** `reads=[]`, `insts=[]`, `picks=[]`. Every original machine guard, non-instantiated original assumption and family19 global law remains in the request. Packed-coordinate equalities are derived only inside the checked tree, never inserted as facts.

`minimization.json` records all five single-tuple deletion tests. Each reduced request returned SAT; the full five-tuple request produced a checked tree. This is deletion-minimal for this selected request, not a claim of globally minimum cardinality or of reachability of those abstract models. The initial three-tuple attempt (without the two kind facts) failed because Proposal cells could be 2: the no-Proposal guard excludes exactly 1. Testing the next hypothesis—retain the original kind law at both relevant cells—succeeded.

## Complete emission evidence

`emission-diff.json` enumerates **every extra tuple at every phase**, plus each required tuple's first emitted round; it includes original family indices. The four `audit-*.json` files retain full instances, selected certificates and shared candidate-work traces. `audit-hashes.json` pins the support implementation and audit helper. Affine terms use `keyId`; the actual selector's fresh witnesses are matched by semantic `instId`, not spelling. The hand certificate has no fresh witnesses. Unmatched generic witnesses remain explicit extras.

No required tuple is missing at the final phase in any mode.

| Mode | prepare emitted / extras | final emitted / extras | exact final raw / encoded hyps | final count reads / insts | direct grow + checkMC | lifted minimal tree + checkMC |
|---|---:|---:|---:|---:|---|---|
| actual generic, all flags | 52 / 49 | 82 / 77 | 98 / 106 | 8 / 0 | true | true |
| actual generic, no initial flag tuples | 16 / 13 | 45 / 40 | 61 / 70 | 9 / 0 | true | true |
| closure with hand-empty cert, all flags | 52 / 49 | 64 / 59 | 80 / 80 | 0 / 0 | true | true |
| closure with hand-empty cert, no initial flag tuples | 16 / 13 | 26 / 21 | 42 / 42 | 0 / 0 | true | true |

The actual selector nevertheless selects **10 count witnesses** during closure:0 (and closure:1 without initial flags). Shared generation work later reaches 65,536; at exhaustion its final selection has zero instances. Final nonzero read bounds are still gratuitous relative to the empty checked hand certificate. The `all` mode has one pool build/one cache hit; `none` has two builds/one hit. No added budget was used.

The 77 final generic/all extras break down as follows; their exact tuples, including fresh witnesses, are all in `emission-diff.json`:

| Source | Extra tuples |
|---|---:|
| `?noProposal`, `?joined`, `?rowOk`, `?all$1` | 9 each, 36 total |
| C2 | 3 |
| C4 | 4 |
| C7 | 4 |
| C9 | 1 |
| C10 | 3 |
| C11 | 4 |
| C14 | 4 |
| C17 | 4 |
| C33 | 3 |
| C45 | 4 |
| C61 | 1 |
| C70 | 2 |
| C74 | 4 |

Initial flag tuples are at all three own coordinates and six request inputs, for all four flags. They account for 36 extras, not a missing premise. Hand-empty closure avoids 18 generic/all final extras; removing the blanket flag seeds avoids another 38 final tuples in that hand closure (36 initial plus two induced tuples).

## Shared mechanism and next production hypothesis

This obligation's missing-support hypothesis is **refuted**: preparation supplies three of five needed tuples, and first closure supplies both remaining carry-guard tuples, regardless of selector or blanket flag seeding. The observed gap is excess admission and count activation on a primitive target. A shared, protocol-independent candidate is a bounded **primitive support/proof phase before optional count grammar and blanket flag seeding**, followed by demand-driven count/flag expansion if the primitive attempt does not close. Keep original guards and assumptions; do not permanently disable count reasoning just because the target is syntactically count-free. The hand-empty/no-initial-flags experiment and all four checked exact-final goals support this staging hypothesis; no production engine change is made here.

Main's original-run profile attributes dominance to SAT plus admission (713 roots; reported tree 1.379s, unknown 7.347s, SAT 47.516s, outside queries 33.086s), not failed grows. Those are Main's supplied observations, not timing measured by this non-timing validation. This result suggests reducing admitted contexts and unnecessary count encodings rather than optimizing unknown-proof exits. `auditSupport.finalHyps` describes its last pre-closure encoding; the table above uses fresh **final** encoding in `final.ts`, avoiding that stale-count pitfall.

## Execution and receipts

All substantive inspection, searches and validations ran through supercomputer on warm boat with `--vm-type large`; no benchmark claims are made. Each proof search used at most 1500 counted ms and a 2500ms wall cap. No engine, kernel, model, NEXT.md or other agent file was edited. No commit was made.

- `inspect/{summary.tsv,inspect.log}` — original source inspection.
- `probe/{summary.tsv,probe.log}` — initial failed three-tuple hypothesis, successful five-tuple request.
- `minimize/{summary.tsv,minimize.log}` — five deletion tests and final tree export.
- `audit-run/{summary.tsv,check.log,audit.log}` — fresh zero-search authentication and actual/hand closure traces.
- `final-run/{summary.tsv,final.log}` — original fixture equality and all four exact final-goal checks.

All five launched supercomputer tasks terminated normally, with no remaining waiter or background task.
