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

A successful conditional replay warrants strict original-harness confirmation;
it does not warrant a merge. The full 29x3, DuoAI, broken, bar, type/lint and test
nonregression gate is still required. See `runs/REPORT.md` for actual receipts,
including failed and interrupted runs.
