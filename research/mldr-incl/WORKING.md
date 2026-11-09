# Lane E live state — Section 16.6

Branch `claude/mldr-incl`. Do not merge or push. Keep the pre-existing
`research/claude-import/` untouched. Production commits remain `f6ec83db` and
`7dc52140`; `bdece707` adds frozen inputs and replay support only.

## Facts already verified

- Corrected type/lint and focused suite: 89 pass, 0 fail (`mldr-incl-check-v8`).
- Seven shards: 1,073 pass, 18 skip, 0 fail (`mldr-incl-shards-v1`).
- DuoAI current-main pairs: 10/10 both sides, no loss (`mldr-incl-gates-v1`).
- E-14 `1681e8e5` actual output: 35 laws, zero proof queries, no hand p1.
- Conditional Gp1 base/preferred/completion/both all remain SAT at the same
  1,868.570 counted units. No MLDR improvement claimed.
- At first query, proposal work is exhausted (65,536/65,536). Last raw STEP has
  quorum-count reads but its certificate still has five reads. Frozen fixtures
  preserve this; their SHA-256 is in README and REPORT.

## Active task handles (one controller per batch)

- E-14 eight allocation/completion controls:
  `1f41530b-2666-4626-ba48-b273486b4a44`, batch `20261109-125428-1l3tmb`,
  output `runs/mldr-incl-e14-refinement-v1`.
- 108 frozen STEP replays:
  `3877773e-ca5b-48a9-9bd8-be94c488cde0`, batch `20261109-125643-pzfo7k`,
  output `runs/mldr-incl-step-v1`.
- Current-main IC3Syn 29x3 pairs:
  `2dedf3e9-b750-4ac9-b509-7f73c3b9b29c`, `runs/mldr-incl-gates-v1/ic3syn`.
- Current-main broken 29 pairs:
  `6215becd-4858-4247-88f8-83378d40b0ee`, `runs/mldr-incl-gates-v1/broken`.
- Final check plus frozen fixture tests:
  `97077107-e69a-43c1-b485-3c892157217a`, `runs/mldr-incl-final-check-v1`.
- Scoped quick bar:
  `c7acb82a-fc6c-4364-8e7e-bcc9e5212397`,
  `runs/mldr-incl-bar/runs/lane-e`. Baseline b788e195, candidate bdece707.
- Four E-14 preference-refresh controls:
  `bb11749d-1f34-4554-9412-2cef4e80f4a9`, `runs/mldr-incl-e14-reselect-v1`.

Get completed task results, then inspect actual output files. Do not infer a
proof from exit 0. `analyze-gates.ts` enforces exact counts, strict receipts,
no positive losses, no false proofs, and records negative refutation losses.
`analyze-replays.ts` verifies each input's hash and rejects unchecked proofs.
Both the proposal ceiling and 2,700-unit diagnostic share are unchanged.

## Research, not production

The scheduling controls use isolated per-job source copies. They limit optional
pre-query refinement to leave existing fuel for later pool refresh, move Lane B
`60b8c37a` completion earlier, or reconsider preferences when count reads change.
None is enabled in production. The four refresh cases test the second possible
blocker: current `rawBuild` preferences are only chosen on the first pool, before
later count reads arrive.

## Recovery / cleanup completed

Only these exact owned abandoned batches were recovered and closed:
`20261109-121248-zmexwp`, `20261109-122218-nesnin`,
`20261109-121814-jfjufz`, `20261109-122849-euw16n`.
Receipts and preserved log archives are under `runs/mldr-incl-recovered`.
No other client, VM ownership guard, or scheduler resource policy changed.
The generic queue entry `mldr-incl-step-v1` was accepted but not consumed by
this repository's idea-only treadmill. It was marked withdrawn while idle;
its exact same jobs now have the one direct scheduler controller listed above.
Host-specific recovery helpers are retained under ignored `runs/mldr-incl-ops`.

## Next

Collect and analyze the pending work. Section 16.6 says conditional safety uses
the actual E-14 35-law family until Lane A 16.1/16.2 reaches safety in the real
harness, then measure the real attempt. Promote no scheduling experiment before
its measured effect, tests and full nonregression. Keep working; no gate-green
or sub-60-second MLDR claim is currently justified.
