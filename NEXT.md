# Lane RL: native multi-place relations (`gen/laneRL`)

## Current state — merge gates accepted, 2026-11-02

Worktree: `gdp-wired-laneRL`. The lane includes main `9df63a6` (NMT wall bound). All merge acceptance checks below are complete. **No owned boat batches remain running**: `runs/laneRL/restart-batches.json` records all 61 inventoried batches complete. Both final-bar Modal fallback apps are stopped, zero tasks (`runs/bar/modal-apps-after-merged.json`).

Commit recovery: if `git rev-parse -q --verify MERGE_HEAD` succeeds, finish the accepted merge with `git commit -F runs/laneRL/merge-message.txt` after checking status; otherwise HEAD is the completed merge-fix commit. Never abort/restart the merge, amend history, or resubmit the finished gates. `brief-sol.md` is pre-existing untracked material: do not discard or commit blindly. All `runs/` artifacts are gitignored and must be preserved/archived before worktree deletion.

The merge fix contains:
- Counted decoder renamed `countKeyParts` in Lean first, then TypeScript, avoiding the tuple `keyParts` collision; bodies unchanged.
- Terra's latent-`if` tuple regression: the old `sumTermOk` survivor is **not equivalent**. Refusal covered, false equivalence claim removed.
- Map key arity follows semantic key parts, including projected tuple tails. Lean `keyArity` first, matching TS helper, projection-chain differential tests, explicit old-arity mutant.
- `research/protocols/ic3syn/jobs.ts --paired`: each candidate/base pair sequential on one isolated VM, alternating order, separate strict 60-second walls; supports `--suite duoai`.
- Conflict in `core/dsl.ts` resolved by retaining `mapArities` and main's `pastWall`; main's NMT behavior/tests retained.

## Completed evidence — do not rerun

| Evidence | Result / artifacts |
|---|---|
| Lean-first builds | All 21 library modules pass for rename and semantic arity. `merge-lean-first/` and arity build artifacts under `runs/laneRL/`. Standard axioms only. |
| Targeted TS/tests | `runs/laneRL/arity-checks2/`: tsc, tuple/count tests, NMT tests and both earlier shard7 timeout files pass. First arity-checks failed only on optional-property typing and is superseded. |
| Final paired gates | Batch `20261102-165721-m5n6vh`, jobs `runs/laneRL/final-gates-jobs.json`, out `runs/laneRL/final-gates/`, baseline archive `runs/laneRL/base-current` = `9df63a6`. All 125 launchers zero; parsed `paired-summary.json`. |
| IC3Syn 29×3, strict 60 s | Candidate **23/23/23**, main **21/21/22**. No solid losses or errors. `learning_switch` proven **14.648/16.629/17.757 s**. i4 remains unknown. |
| DuoAI 10×3 | **30/30 both sides**. No regression. |
| Seven shards | **All seven pass** in final-gates. Earlier old-main shard7 timeouts are superseded. |
| Final Lean replay | Switch + tuples pass, **184.09 s**; only `propext`, `Classical.choice`, `Quot.sound`. |
| Touched-line mutants | Final batch `20261102-165718-6ek6nw`, `final-mutants-jobs.json`, `final-mutants/`: 185 tested, initially 166 killed. Explicit old-arity mutant 1378 killed by tuples (`mut-180.log`). |
| Full survivor battery | Batch `20261102-170714-y96o9d`, `final-survivors-jobs.json`, `final-survivors/`: unmutated baseline passes; 12 further kills. Combined **178 killed + 7 documented equivalents**. 195 = cache threshold, 197 = parser guard; correctly matched in `kernel/MUTANTS.md` and `equivalents-final.txt`. |
| Diagnostic kill replays | Batch `20261102-172309-puneb9`, `replay-kills-jobs.json`, `replay-kills2/`: baseline sets/conformance pass; mutant 370 fails the doubled-key refusal assertion (sets.test.ts:65), 405 fails the sum reference assertion (conformance.test.ts:247). Real assertions, not load timeouts. |
| Own quick bar vs current main | `runs/bar/runs/laneRL-merged-main9df63a6/REPORT.md`, `--quick --base 9df63a6 --together --runs 3`. **Wrong 0, solid losses 0**, all one-CPU jobs pass, Lean recurrent samples **6/6**. g332 **332/332**, same search on all goals, summed search 358.949 vs 349.792 s (**+2.6%**). Some data-test timings are slower; do not claim uniform speed improvement. |

Bar frozen candidate: `runs/bar/trees/acbea21d1393+d1a15ca3`; base `runs/bar/trees/9df63a6b174c`. Candidate's `.git` pointer gives boat the proper upload root: preserve it if inspecting this archived snapshot. `laneRL-final` and `laneRL-final2` were invalid nested-snapshot attempts and explicitly stopped; do not resume them. `GIT_CEILING_DIRECTORIES` alone does not work (boat needs git ls-files). First diagnostic replay `20261102-172110-r1krce` never shipped its script; superseded by replay-kills2. With boat, use one `--data` directory containing multiple files, not repeated flags.

Final bar fallback apps `ap-z4XicdsPToR1wS6kHbksDn` and `ap-SvSwjhI9e2hE1icidq7lYg` are stopped. Older fallback apps are also stopped. No live PID should be killed using this historical handoff.

Useful result helpers (few-second local file processing only):
- `bun runs/laneRL/summarize.ts runs/laneRL/final-gates`
- `bun runs/laneRL/mutant-summary.ts runs/laneRL/final-survivors`
- `python3 runs/laneRL/restart-inventory.py` is a one-shot, read-only inventory; no waiting loop or submission. All recorded work is now complete.

## Exact next work: generalized i4 improvement

1. Check whether the accepted merge commit is complete as described above. No merge-gate reruns are needed without further implementation changes.
2. Read `research/protocols/engine/DESIGN.md`, especially both `gen/laneRL` sections. `learning_switch_i4` with nothing written is still **unknown**. Implement/profile a GENERAL engine improvement, not a model-name switch, hand-supplied invariant, special goal order, or increased wall limit. Current opportunities: small-instance sampling and per-row View Env work (compiled expressions already exist).
3. All nontrivial execution goes on boat. Read `supercomputer --skill` before first use in a new session. Store new experiment jobs/results under a new `runs/laneRL/` path, preserve completed outputs, one waiter per task. Update this file immediately with any newly running batch ID, jobs file, output dir and result awaited.
4. Validate new behavior with focused tests and direct probes, then strict paired gates against current main as appropriate: keep DuoAI 30/30, learning_switch proved, broken models never proved, seven shards, current-main own bar for the final new tree. Lean first for any trusted change; no axioms/sorry.
5. Record whether i4 actually improves; no performance or completion claims from launcher success alone. No push or GitHub writes without explicit permission.

## Existing native relations and remaining research

- Trusted tup/proj terms, partwise cells/equality; DSL `.sorts`/`.relations`; runtimes evaluate tuple quantifiers and writes by parts. Native `learning_switch` and `learning_switch_i4` ports agree with original simulations (12,000 steps each) and TLC state checks (43,672 / 240 states). Phased ports retained separately.
- Published hand invariants prove switch and i4; these are diagnostic only, NOT the nothing-written target. The i4 set needed two laws to hold whenever set, not just after start.
- Broken switches currently end unknown, not refuted; never proved. A generic way to reach their bad states within budget remains open.
- `certCyclic` ignoring `withWall` on a symmetric flip relation is a prior prover-side finding; don't conflate it with this merge.
- Stretch: Ivy/mypyvy reader not started.
- Terra review: `../gdp-wired-rl-review/runs/REVIEW.md`; no confirmed false acceptance in bounded review, not an equivalence proof. Both requested fixes are incorporated.

Trust/workflow references: README.md trust boundary; docs/ARCHITECTURE.md (Lean first); research/ROADMAP.md; compare/tip/README.md (strict wall/noise); kernel/MUTANTS.md. Final detailed local report: `runs/REPORT.md`.
