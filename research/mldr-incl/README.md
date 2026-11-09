# Lane E: ordinary guarded-inclusion pool

Production code is in `core/count-recovery/member-inclusions.ts`,
`core/count-support.ts`, and `core/counts.ts`. The matcher proposes only ordinary
count-witness disjunctions. Scalar residues are provenance, not assumptions.

## Fast loop

All prover executions go through `supercomputer`, `--class submission`, with no
VM-count override. Gates use `--class gate`. Keep the warm queue supplied rather
than buying replacement starts. Never alter another worktree.

1. `capture-jobs.json` captures original production queries with `DUMP_DIR`,
   `DUMP_ALL=1`, and the existing query/count dump hooks.
2. `pack-capture.ts` exports a bounded Brotli archive. It records omissions;
   `queries.jsonl` is retained, but the raw stage archive may be partial.
3. `extract-capture.ts RUN_DIR [LOG_NAME [DEST]]` verifies SHA-256 before writing
   the captured files. It never silently accepts a truncated archive.
4. `conditional-safety.ts` uses the captured generated family plus the published
   p1 hypothesis for one safety attempt. This is a conditional diagnostic, not
   an end-to-end proof. Set `MLDR_INCL_FAMILY=generated` to use an E-14 capture
   without adding any hand law. `make-conditional.ts` makes baseline/preferred, supported/
   ordinary, 1,000/2,700/5,000-unit pairs. The 5,000-unit cases are explicitly above
   the production-share target. `proposal.diff` reverses only this lane's ordinary
   pool integration for the same-source baseline; it must match the tested tree.
5. Extract a conditional safety archive, then run `make-replays.ts DEST` to make
   frozen STEP replays. `replay.ts` compares four explicit modes: original raw
   packet, inclusion-prioritized pool, count-law instances at the goal's own keys,
   and those instances plus ordinary quantified-flag instances at witnesses.
   Key seeding is a **research control for Section 15.2**, not a production change
   from this lane. Every successful replay is checked with `checkMC` (or `check`
   for an already numeric packet).

## Frozen replay inputs

`fixtures/safety-gp1.br` is the exact 23,581-byte captured archive from the
unmodified pool baseline at the 2,700-unit conditional safety attempt. Its
SHA-256 is `b96c779fda332e17778af88d76e69a8682b98de04739c1e07e6d3d4b154c0f0c`.
It contains 39 files, with zero omissions; neither the candidate matcher nor
new key-completion code constructs these inputs. `fixtures/e14-generated.br`
is Lane A `1681e8e5`'s real generation output: 35 laws, zero proof queries,
SHA-256 `4b97fb96467ee51e9b80ff0a13b33f00d2731452fd93e6191f65c17c8882d64a`.
`replay.ts` and `conditional-safety.ts` accept `ARCHIVE.br#ENTRY.json` as well
as a plain JSON file. Every replay records the entry's SHA-256.

`fixtures/e14-safety.br` is the conditional safety capture from the actual
35-law generated family (no supplied p1), SHA-256
`b9c7abfae8b30ed2c9de6a665aeebc2956599b8ec28fa3d5a97707719e8f3134`.
It is **partial: 31 retained files, 22 omitted files**. Its origin and omissions
are recorded in `fixtures/e14-safety.meta.json`; complete retained packets, not
truncated JSON, are replayed. This is not an original-harness proof.

`make-replays.ts` deduplicates identical raw goal/instance/pool packets across
trace phases before making the matrix: nine distinct STEP packets, four modes,
and 250/1,000/2,700 units, for 108 independent jobs. The jobs are self-contained;
no large `--data` stage bundle is needed. `refinement-variant.ts` is a separate
research-only scheduling experiment: it never changes the 65,536 proposal
ceiling or the 2,700-unit safety share and is not enabled in production.

For a separate fixture and sampled early/middle/late packets, use:

```sh
bun research/mldr-incl/make-replays.ts INPUT_DIR FIXTURE.br PLAN.json 3
bun research/mldr-incl/analyze-replays.ts RESULTS_DIR FIXTURE.br PLAN.json
```

The analyzer rejects duplicate/unexpected receipts, mode/budget mismatches,
wrong input hashes and unchecked proof claims. `preferred` rebuilds a small
selection; it does not preserve every instance from the original raw packet.
Thus a raw UNKNOWN becoming a preferred SAT is possible and is reported, not
called a proof regression or suppressed.

## Conditional pointwise evidence

`pointwise.ts` isolates a proposed count inclusion on the immutable E-14
packet. The `*-domain` modes retain scalar conjuncts implied by the original
raw goal, plus the explicit member-flag premises. `tight-domain` tests the
weaker `CT[i] < CfgT[b]` assumption instead of the proposal's sufficient
`CT[i] + 1 < CfgT[b]`. This strengthens the conditional claim; it does not
alter production matching or assert a fact.

Both guarded domain-aware variants checked in about 40 counted units. The
missing-guard control stays SAT. Without the original scalar/key-domain
premises, all initial controls were SAT; those failures remain recorded.
This is **not a proof of safety**, nor evidence that the guard or member flags
hold outside the relevant branch.

`export-pointwise.sh` uses a unique empty output file and refuses to verify
unless the producer wrote a nonempty certificate. `verify-pointwise.ts`
checks the saved certificate in a fresh process without running the matcher.
The receipt must also contain a fresh producer artifact whose hash matches
that second process; a verifier exit alone is not sufficient.

`concise-shard.ts` captures the complete child stream before summarizing it.
`recover-shard.ts` verifies the retained gzip's raw hash and size and reparses
both `1 file.` and `N files.` summaries. The initial plural-only parser failure
is retained; recovering its complete log does not rerun or regenerate tests.

A successful conditional replay warrants strict original-harness confirmation;
it does not warrant a merge. The full 29x3, DuoAI, broken, bar, type/lint and test
nonregression gate is still required. See `runs/REPORT.md` for actual receipts,
including failed and interrupted runs.
