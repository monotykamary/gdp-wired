# Counted-integration boundary after D's GREEN receipts

Reconciliation is integrated; no new semantic rejection of either admitted
patch is alleged. The whole kernel/Lean trees are exactly D's admitted hashes
on both branches. No pending label remains on the current reconciliation.

- `claude/mldr-integ`: be661632.
- `claude/mldr-candidate`: 7eccce26.
- Reconciliation: 72377361. Clock-on-A: 565ecd01.

Native batch `20261111-024930-2cn0kn` verified **133 files with zero exceptions**
before every check, then all three jobs failed:

1. Candidate counted tripwire cannot load `core/meter.ts`: its re-export
   targets absent `../kernel/meter.ts`. It runs zero test assertions; this is
   an import failure, not evidence that a wall read escaped the tripwire.
2. Candidate typecheck additionally reports missing `searchNow`, `inWorkScope`,
   `withBudget`, `BudgetExpired`, `checkBudget`, `inBudget` and related exports
   from the exact common prover. A's counted core requires those interfaces.
3. Integration typecheck reports the two B research exporter fixtures absent:
   `research/track-m/mono-export-fixture.ts` and `linear-export-fixture.ts`.
   Inspection shows the former also needs B's `core/count-frames.ts`, which
   this older integration branch does not have. This is a dependency chain,
   not safely repairable by copying two files and claiming a full green build.

The separately admitted clock patch was checked against A's different prover
and checker identity. Restoring its entire prover into the common tree would
silently recreate the mixed-tree state the coordinator expressly rejected.
No such restoration, new checking-path edit or unreviewed full strategy merge
was made. The measured db14ee14 source remains available as history only.

**Requested ownership:** A/I design a common-tree-compatible counted API and
raw-meter placement; D decide/review any resulting untrusted-prover clock
changes as a new exact identity. B/I own the full dependency/strategy merge.
Do not presume either separate GREEN receipt covers this composition.

Complete failing logs: `results/validation/`. No main merge or push.
