# 0.50.2 slowdown diagnostic

Research-only harness. It compares `70b660443` with `c149b540b` (primary sound baseline), `96bf476ed`, and `c08bb385b` on one serial, exclusive pinned worker. `c08` is explicitly an unsound historical baseline and is diagnostic-only.

`run-paired.sh` creates disposable detached worktrees, hard-links no sources and symlinks the installed dependency directory. It preserves each revision's test source, assertions, and inner algorithm budget. It runs paired AB/BA/AB (or BA/AB/BA) orders with no discarded warm-up:

* policy identity: three pairs for each historical control; records an exact renamed-law direct check (raw `law.ms`, check wall, input write I/O, and residual `checkWall - law.ms`) plus the unedited named Bun test;
* co-write provenance: three `70/c149` pairs of the unedited named test, as a representative larger quantified/provenance case;
* causal count pass: after all timings, temporary worktree-only instrumentation counts `encodeBinders` calls, AST collect/rewrite visits, generated groups/parts, and collision fresh-name loop attempts. It is excluded from timing statistics and changes no committed production source.

The runner rejects unexpected checked/verdict/translation results and retains stdout/stderr beside each JSONL observation. This harness is diagnostic evidence only; it does not change budgets, assertions, semantic behavior, or release status.
