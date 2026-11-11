# Main 0.48.0 merged into lane I

Exact tested source: **2de2ce89f9f93eb8feb5fbfb3a355da3adafc4ef**.
Parents: `4d5b89fe` and main `f95f306d`. The quotient is not in this pin.

## Preserved boundaries

Only `core/dsl.ts` and `core/infer.ts` conflicted. Resolution keeps main's
source finalization and internal model-only candidate proving, with counted
time at the two conflicting clock expressions. Fourteen release safety/CLI
files match main byte-for-byte. No merge delta in `kernel/`, `lean-kernel/`
or `core/check.ts`; workers verify 132 protected identities.

`private/` remains ignored with no tracked files. The source archive comes
from the merge commit, not the working directory. No private reproducers or
quotient WIP were included. Main's privacy scrub is preserved. No push,
history rewrite or release retag occurred.

## Production validation — boat

- **541 passing test executions / 16,106 assertions; 2 profile skips.**
  Native/source/CLI 95; extraction 226; counted/checker 156;
  inference/relational/Effect/calendar 55; full-profile controls 9.
- Type/lint: **1,829 files, zero errors/warnings**; complete test roster;
  merge commit passes commitlint.
- 28 counted originals: **10 proved and checked, 18 unknown**, unchanged by
  ID; no new refutations. Maximum **15,000,276.18**, `sharded_kv`
  **15,000,018.2817**. This is finite-census evidence, not a universal cap.
- 28 flags-off originals: **27 checked, 1 unknown**, unchanged by ID.
  Candidate hashes, result fields, event/query traces, charged 12-counter
  vectors and units are unchanged.
- All 56 receipts pass source ID, resolved-checker file hash, raw/phase sum,
  unit and mode checks. Strict runs have zero measured-scope forbidden clock
  reads. The hook is installed before imports but activated for measurement;
  arbitrary module initialization is not covered by that zero-read claim.
- Scoped compatibility and five corruption controls pass. **Strict raw
  flags-off identity fails**: 19 exact receipts, 9 lower unpriced observations.

## Explicit flags-off observation changes

| Original | evals delta | astNodes delta |
|---|---:|---:|
| firewall | -1,527,719 | 0 |
| learning_switch | -1,772,622 | -132 |
| learning_switch_i4 | -3,559,945 | -540 |
| lock_server | -2,546,648 | 0 |
| lockserv | -21,752,204 | 0 |
| lockserv_automaton | -21,563,028 | 0 |
| simple_decentralized_lock | -1,245,960 | 0 |
| two_phase_commit | -1,034,548 | 0 |
| twophase | -917,782 | 0 |

These reductions are consistent with main's `infer.ts` replacing repeated
internal public-prover calls with model-only calls and outer finalization.
No production code was changed to manufacture old counts or restore the old
path. The scoped audit removes only these two observation columns from raw
and phase comparison, requires every other field to match and every changed
counter to decrease. This is not renamed "bit-identical"; D must accept the
narrower release compatibility scope. `AUDIT.json` retains exact values.

## Receipts / failed attempts retained

- `20261111-052837-wtq6py` (`merge0480-gate`): 61/62 jobs passed. The combined
  seven-file inference group hit its 800-second harness timeout, with no
  failed assertion.
- `20261111-054412-3ex1y4` (`merge0480-isolated`): all seven unchanged files
  pass independently. Effective production coverage is 68 passing jobs;
  the timed-out aggregate is replaced, not relabeled.
- `20261111-054400-57bsup`: initial auditor incorrectly expected full-mode
  weights in flags-off mode; corrected to the documented legacy projection.
- `20261111-054431-t34k4i`: strict raw identity correctly fails on nine cases.
- `20261111-054501-qco6ni`: diagnostic records the counter deltas.
- `20261111-054557-4cd4sk`: scoped compatibility and five controls pass.
  Evidence tooling found a copied global preload conflict; byte-exact source
  is now staged as `.source`. A later tooling attempt timed out; the
  isolated static-check retry `20261111-055231-wh0uky` passes: **1,837
  files, zero errors/warnings**. Runtime source is unchanged.

## Scope / next

D approval and calibration remain pending; no old fit transfers. The prior
later-external-deadline limitation remains. Full A/B/F closure is not implied.
After this handoff, resume the separately gated request quotient.
