# Section 19 — which emitted helper lemmas are actually cited?

Research implementation: `eea1d978`. **No production, kernel, generator, allowance, local ceiling or helper-selection policy changes.** The previous 28/29 result was not rerun or re-certified.

## Scope and capture

The Section 18 inventory cannot answer the complete citation question: it retains the helper-attempt proofs, but some later solver calls retain only outcomes, not their proof trees. Availability in a context is not citation. Rather than invent uses or zeros for the old **3 / 9 / 30 / 29** emissions, this run retains the subsequent consumers for the same four shards.

Exactly four new searches ran, sequentially on one exclusive large VM with eight pinned vCPUs (AMD EPYC 4585PX). All retained the production **5,000-unit allowance**, **4,800 ms cooperative law clock**, and local ceilings. Two initial preflight failures ran no searches. The audit and report jobs ran after the searches and are not charged to them.

| Law / op | Search units | Search wall ms | Emitted | Target-checked | Outcome |
|---|---:|---:|---:|---:|---|
| Inv2973 / 0 | 500.276 | 5,000.176 | 13 | 12 | unknown |
| Inv2973 / 4 | 616.684 | 5,422.418 | 13 | 12 | unknown |
| Inv* / 3 | 1,934.974 | 4,814.191 | 54 | 54 | unknown |
| Inv* / 5 | 1,541.736 | 4,913.573 | 28 | 23 | unknown |

These are new, clock-limited prefixes, **not back-filled citations for the old 71 emissions**. The tracer and runtime variation can change how far a cooperative-clock run gets. The overshoot above is reported rather than rounded into compliance. No whole-law cost, performance comparison or complete-law proof is inferred.

## Counting a citation

The disposable observer records producer IDs, emission time, copied-hypothesis provenance, consumer goals and paths, conditional-proof marks, proof trees, returned cores, and selected control/eligibility reads. Provenance is frozen before each consumer: a later emission cannot retroactively own an earlier assumption.

The offline audit rechecks returned consumer proofs with the original kernel, then walks only the live certificate cone ending at the contradiction. Dead inputs and zero-coefficient branches are not citations. A directly owned live hypothesis/path row is `checked-proof`; a returned hypothesis core is `core`, separately from proof. Origin ambiguity, formula-only matches and context reads are retained separately; they are not promoted to direct proof citations. Core requests before emission are also separate and are not later-use credit.

There are **1,398 recorded consumer calls**, **996 proof/core consumers audited**, and **920 checked returned consumer proofs**. Repeated transport/return checks do not multiply the number of cited emitted instances.

Consumer phases are classified by the inner operation: closure first, then an active later-lemma attempt, then a leaf. This corrects the initially over-broad label that called every nested operation a leaf merely because an outer guard-leaf wrapper was still active. The presentation-only correction changed no citation verdict, unit value, or proof check; the original audit archive is retained.

A checked *consumer* proves its goal from its recorded assumptions; it does not certify that every assumed helper fact was valid in another context. Seven emitted instances fail their recorded target-context check. In particular, **Inv* op 5 producer 42 is cited by a checked local consumer but fails its own recorded target check**. It is observed use, not a successfully proved helper or an accepted law. Thus 32 emissions are directly cited, of which **31 are target-checked**.

## Per-helper answer

`Proof-cited` counts distinct emitted instances cited by at least one checked subsequent consumer. `Proof-uncited units` sums the full exclusive attempt cost of the other emissions, including their setup/failed work, not just the final successful source query.

| Law / op | Helper | Emitted | Proof-cited | Proof-uncited units |
|---|---|---:|---:|---:|
| Inv2973 / 0 | field | 4 | 0 | 0.301 |
| Inv2973 / 0 | frame | 9 | 9 | 0 |
| Inv2973 / 4 | field | 4 | 1 | 119.312 |
| Inv2973 / 4 | frame | 9 | 9 | 0 |
| Inv* / 3 | field | 50 | 1 | 118.485 |
| Inv* / 3 | frame | 4 | 4 | 0 |
| Inv* / 5 | field | 26 | 6* | 239.505 |
| Inv* / 5 | frame | 2 | 2 | 0 |

\* Five of these six field emissions pass their own target-context check; producer 42 does not.

**All 24 frame emissions are directly cited**, accounting for 1,130.847 units of emitted-attempt cost. Only eight of 84 field emissions are directly cited. Overall, **76 of 108 emissions are not directly proof-cited**, costing **477.603 units**. That is not the same as being unused.

Distinct emitted instances by checked consumer phase:

| Law / op | Closure | Leaf | Later-lemma proof | Other |
|---|---:|---:|---:|---:|
| Inv2973 / 0 | 0 | 9 | 0 | 0 |
| Inv2973 / 4 | 1 | 9 | 0 | 0 |
| Inv* / 3 | 0 | 4 | 1 | 0 |
| Inv* / 5 | 2 | 2 | 4 | 0 |

Phase columns are sets and need not be disjoint in general. They happen to partition the cited instances here. A leaf citation is evidence of a checked local subproof, **not** a closed op/law.

## What did the uncited emissions cost?

Proof-uncited facts can still be requested by a core, read in a branch decision or context, or match a live row without unambiguous ownership. The conservative `noObservedUse` category excludes all these recorded uses/matches.

| Law / op | No recorded use | Their total units | Successful source units | Of these, target-checked |
|---|---:|---:|---:|---:|
| Inv2973 / 0 | 4 | 0.301 | 0.301 | 3 |
| Inv2973 / 4 | 2 | 0.115 | 0.108 | 1 |
| Inv* / 3 | 36 | 36.247 | 3.366 | 36 |
| Inv* / 5 | 3 | 38.977 | 0.723 | 0 |
| **Total** | **45** | **75.641** | **4.498** | **40** |

The 40 target-checked emissions with no recorded use account for **36.630 total units**, of which **3.749** are successful source work. The other five have failed target checks; their attempt cost is still real, but they receive no proved-instance credit.

Examples of why proof-uncited is not unused:

- Inv2973 op 4 field producer 61 costs **119.197 units** and is read in context; it is not placed in the no-recorded-use set. Its statement is `if(?canVote=1 && i<size, CfgT[i], 0) <= CT[i]`.
- Inv* op 5 field producers 46 and 102 cost **85.351** and **96.198** units. They have recorded context reads (and, for 46, formula matches); neither is claimed unused.

`No recorded use` is an observational classification for the retained channels and prefix, **not a whole-program non-use proof**. In particular, it does not certify that arbitrary preprocessing or conditional-eligibility control flow is independent of a fact. Nor does deleting a recorded cost predict the search trajectory or clock prefix after a policy change.

## Where the helper cost actually went

The independent exclusive-cost reconciliation is:

| Bucket | Units |
|---|---:|
| Emitted attempts, cited or not | 1,644.203 |
| Attempts that emitted nothing | 2,313.230 |
| Other helper work, outside those attempts | 635.786 |
| **All helper work** | **4,593.219** |

The 75.641 units associated with no-recorded-use emissions are **1.65%** of this captured helper work; the broader 477.603 proof-uncited units are **10.40%**. Neither percentage is an executed saving or a mathematical upper bound on a redesigned search.

**Conclusion:** unused completed frame lemmas are not the large lever in these prefixes: every frame emission is cited. Most field emissions lack direct proof citations, but many have other recorded uses, and their strongest no-recorded-use subset is cheap. The largest bucket is work on attempts that never emitted a lemma. This measurement does not decide which of those failed attempts a demand-driven policy could avoid. No such policy was implemented or tested.

## Evidence, validation and reproduction

- [overview.json](overview.json): compact tables and phase counts.
- [citations.csv](citations.csv): every emitted statement, checked/cited flags, separate setup/failed/source/check/transport units, and consumer IDs.
- [summary.json](summary.json): full per-emission and per-consumer audit, including possible uses and pre-emission requests.
- [validation.json](validation.json): independent arithmetic, citation-preservation and checksum checks.
- [cleanup.json](cleanup.json): completed jobs and staging disposition.
- [Raw capture](../section19-citations-v3/receipts.tar.gz), SHA-256 `2250878789dc6ac1ea443173477e6536b677c45c6992f5998c0dd2816d820594`.
- [Original consumer audit](consumer-audit.br), SHA-256 `6734c1f33ed10b5fdaca9efbb68b8b20f26d2b335c318e57f8fc701c0d26abcf`.
- [Final report archive](receipts.br), SHA-256 `559f0eeb5ad837929a816d2930a1cf591519001ec5de0e1676a87ec304df3152`.
- [Capture log](../section19-citations-v3/citations.log), [audit log](../section19-audit-v1/audit.log), [presentation/test log](../section19-report-v1/report.log). Failed preflights are retained in `section19-citations-v1` and `-v2`.

The final typecheck/lint and **9 tests / 26 assertions** pass. The tests cover live-cone pruning, frozen provenance, emission identity and nested consumer phases. Exclusive ledgers reconcile within `1e-7` units; the presentation change preserves every emitted cost and citation flag. All three archives match their manifests. No complete-law proof or gate pass is claimed.

Reproduction uses `research/track-m/jobs-section19.json` with the existing `section12-source-input:source-input` and `section13-runtime-v1/ready:runtime` data mounts on one exclusive eight-vCPU large VM. `jobs-section19-audit.json` consumes the retrieved capture as `citation-input`; `jobs-section19-report.json` consumes the audited summary as `audited-input`. The latter two jobs perform no new search. The only modified core/helper files are disposable copies; the preparation script checks that the kernel is byte-identical and confines instrumentation to its allowlist.
