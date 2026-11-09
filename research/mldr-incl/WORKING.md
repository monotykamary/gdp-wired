# Lane E working state

Branch `claude/mldr-incl`; source commits `f6ec83db`, `7dc52140`.
Do not merge: full acceptance is pending. Preserve the pre-existing untracked
`research/claude-import/` untouched.

## Pending owned jobs

- `e532c154-4657-45fb-9d31-ac6201128a7a`, PID 81308: corrected member tests,
  `runs/mldr-incl-members-v7/`, gate class. Snapshot includes the cap=1 fix.
- `ef7a4469-f091-423d-b967-b437ae7636a0`, PID 77785: two conditional safety
  captures, `runs/mldr-incl-conditional-v3/`, submission class, minimal 55 KiB
  `runs/mldr-incl-conditional-input` data.

The first broad conditional batches and earlier stalled check batch were stopped
by their exact owned task IDs. Do not repeat them as if they produced evidence.
`77ef6137-24ef-48c0-be44-3c678db54772` (E-14 generation) failed before execution:
boat said `recovery quarantined; ownership held`. No global recovery action was
attempted. `supercomputer controller status` said there is no controller VM.
Do not bypass quarantine, change global policy, or touch another client's leases.

## Next actions after admission recovers

1. Collect v7 and v3; inspect actual job logs/summary, not the wrapper exit code.
2. Extract the base safety archive with:
   `bun research/mldr-incl/extract-capture.ts runs/mldr-incl-conditional-v3 base-yes-2700-r1.log runs/mldr-incl-safety-input`.
3. `bun research/mldr-incl/make-replays.ts runs/mldr-incl-safety-input`, then run
   its jobs on boat with `--class submission --vm-type large --timing` and
   `--data runs/mldr-incl-safety-input:inputs`. Raw/preferred/keyed/seeded modes
   are explicit; key seeding is only a research control for Lane B's 15.2.
4. Retry the generation-only E-14 job with `runs/mldr-incl-peer-input:inputs`.
   It is an archive of `1681e8e5`, not a modified worktree. Extract its family and
   set `MLDR_INCL_FAMILY=generated` for safety attempts (no hand p1 added).
5. Rerun full type/lint and focused tests including all current research scripts.
6. Only after a checked safety improvement: strict original MLDR x3; then the
   required paired 29x3/main, DuoAI, broken, bar and test gates before GREEN.

Known validated fact: v6's generic ordinary selected witness proves a conditional
inclusion with `checkMC`, and does not prove the unguarded version. Its only
failure was a wrong cap-test expectation, corrected for v7. This does not claim
anything about MLDR's safety verdict.
