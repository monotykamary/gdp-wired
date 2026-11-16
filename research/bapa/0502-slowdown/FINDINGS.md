# Soundness-fix slowdown profile — development evidence only

## Method

`run-paired.sh` runs every test in a fresh process, serially on one exclusive pinned worker. Policy observations use three paired orders per control: c149 `AB/BA/AB`, c96 and c08 `BA/AB/BA`; co-write uses c149 `AB/BA/AB`. The named Bun test retains each revision's source assertion and source budget (70: 7 s policy / 65 s co-write; historical controls: 3 s / 60 s). All 24 named test observations passed.

The direct policy observer is intentionally secondary: it reproduces the test's original control before the renamed critical check and measures raw `law.ms`, check wall, write I/O, and residual wall. It fixes the observer budget at 3 s across revisions, so it is a component probe rather than a replacement for the exact-budget named test.

Ratios use three samples. `paired95LogT` in the raw summary is an exploratory two-sided t interval on log pair ratios (df=2): very wide by design and not a release threshold.

## Results

| Case / control | Metric | 70 median / control median | Median ratio | paired geometric ratio [95% log-t] |
|---|---:|---:|---:|---:|
| Policy / c149 (sound primary) | raw renamed law | 2499 / 2870 ms | 0.871 | 0.941 [0.665, 1.332] |
| Policy / c149 | named test | 12417.53 / 11725.80 ms | 1.059 | 1.056 [0.682, 1.633] |
| Policy / c149 | process wall | 12704.85 / 12056.23 ms | 1.054 | 1.053 [0.678, 1.635] |
| Policy / c96 (sound historical control) | raw renamed law | 1421 / 1361 ms | 1.044 | 0.984 [0.804, 1.206] |
| Policy / c96 | named test | 7764.27 / 6951.24 ms | 1.117 | 0.993 [0.681, 1.448] |
| Co-write / c149 (larger provenance case) | named test | 26675.31 / 24026.65 ms | 1.110 | 1.076 [0.981, 1.180] |
| Co-write / c149 | process wall | 26767.49 / 24130.83 ms | 1.109 | 1.075 [0.980, 1.180] |

The c08 control is **unsound historical diagnostic only**. Its raw-law median ratio is 1.179 and does not support any release or optimization conclusion.

### Component split, 70 vs c149 policy

- Raw proof work (`law.ms`): 2499 vs 2870 ms (0.871 median ratio).
- Direct check wall: 3881.10 vs 4075.45 ms (0.952).
- Residual check wall (`checkWall - law`, the available lowering/renaming/extraction envelope, not a precise attribution): 1033.69 vs 1205.45 ms (0.858); paired geometric ratio 0.988 with [0.681, 1.435].
- Fixture write I/O: 0.258 vs 0.290 ms (0.889); too small/noisy to attribute.

Thus this sample does **not** support a detectable policy-law proof-search cost from the final soundness fixes. The whole named policy test is noisy (candidate sample SD 1.13 s; control 1.82 s), so its 5.9% median increase is not causal evidence.

## Causal counters

A post-timing, disposable worktree-only instrumentation pass counted `encodeBinders` work for the critical policy check. Both c149 and 70 had exactly **28 calls** and **5548 collect visits**, with **0 generated identities, groups, generated parts, collision groups, fresh-name attempts, and rewrite visits**. The instrumentation is excluded from timing statistics.

This falsifies the specific hypothesis that repeated fresh-name collision scans or generated-binder provenance groups explain this Java policy case. It does not exonerate those paths globally: this fixture did not enter generated-binder handling. The co-write case has no direct provenance-group counter yet.

## Ranked follow-ups (no implementation authorized)

1. **Instrument co-write provenance candidate/group admission and witness fresh-name scans.** The only meaningful point estimate is the larger co-write case (+7.6% paired geometric, +11.0% median), but its three-pair interval includes 1.0. Measure candidate count, group size, dedup/reject count, and generated-name collision iterations before optimizing. **Semantic risk:** dropping/reordering provenance candidates can weaken refusal or change proof selection.
2. **Instrument AST traversal identities in co-write lowering.** Policy has equal binder/AST counts; provenance may have different tree shapes. Measure visits and unique-node reuse separately. **Risk:** memoization keyed by spelling rather than provenance can reintroduce capture/identity bugs.
3. **Only after counts differ, evaluate immutable structural sharing for read-only walks.** Require equality of emitted machines/laws, kernel verdicts, and negative refusals. **Risk:** aliasing or stale cache across declared/free names.
4. **Do not optimize fresh-name scans from this evidence.** The direct causal count is zero for generated collision work in the policy fixture. Any optimization is presently speculative and has the highest namespace-soundness risk.

No production optimization, assertion change, budget change, or semantic change was made.
