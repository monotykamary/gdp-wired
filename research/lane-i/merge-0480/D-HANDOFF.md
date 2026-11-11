# D handoff — main 0.48.0 merged into lane I

Review **2de2ce89f9f93eb8feb5fbfb3a355da3adafc4ef** on `claude/mldr-integ`.
Parents: I evidence `4d5b89fe` and release **f95f306d**. This is a full merge,
not a selective port. Local checks are complete; D approval is pending.

## Minimal resolution review

```
git show --cc 2de2ce89 -- core/dsl.ts core/infer.ts
git diff 4d5b89fe 2de2ce89 -- kernel lean-kernel core/check.ts
git merge-base --is-ancestor f95f306d 2de2ce89
```

The second diff is empty; the ancestor check succeeds. DSL keeps
`translationVerdict` with counted enclosing time. Inference keeps main's
model-only candidate proving and first-pass `refuteModelByRuns`, with counted
statistics. Fourteen release safety/CLI files are byte-identical to main
(`driver/release-safety-tree.txt`). No source/native check is disabled.
No tracked `private/` files; its ignore boundary and main's privacy scrub
remain. No private reproducer is in this source archive or handoff.

## Local gate receipts

- `20261111-052837-wtq6py`: 61/62 pass; the seven-file grouped inference job
  reached its 800-second harness timeout, without a failed assertion.
- `20261111-054412-3ex1y4`: all seven unchanged files pass individually.
  Effective source coverage: **68 passing jobs**, 541 test executions,
  16,106 assertions, 2 profile-specific skips.
- `20261111-054557-4cd4sk`: scoped compatibility plus five corrupted-receipt
  controls pass (source, checker digest, ledger, clock, off trace).
- `20261111-055231-wh0uky`: final evidence-tooling type/lint pass, 1,837 files.
  The merged source itself passed 1,829-file type/lint and full roster checks.

All 56 source-bound census receipts validate ledger sums and resolved checker
file digests. Full mode retains 10 checked / 18 unknown; off mode retains
27 checked / 1 unknown. No new refutation, candidate-hash or event/query-trace
change. Maximum 15,000,276.18; sharded_kv 15,000,018.2817. Zero measured-scope
forbidden clock reads. These are finite-census results, not a universal cap.

## Explicit decision requested: release-related off counter delta

**Strict raw flags-off identity is 19/28, not 28/28.** Nine cases have fewer
unpriced `evals`; learning_switch and learning_switch_i4 also have 132/540
fewer `astNodes`. Every other compared field, including the 12 charged
counters, units, verdicts, candidates and traces, is identical. Full values
are in `AUDIT.json` and `RESULT.md`. The strict failing audit is retained.
The separate compatibility audit allows only decreases in those two raw
observation fields; please explicitly accept or reject that scope. We did
not restore old internal public-prover calls or fake counters to match them.

## Retained limits

No W fit transfers; calibration remains pending. The earlier exported-factory
later-external-deadline limitation remains. No universal 1,024-unit result,
29/29 finish, or full A/B/F dispatcher closure is claimed. The request quotient
is separate uncommitted WIP, absent from this source. No main push or merge
back is performed.
