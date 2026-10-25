# gdp-wired gates: the bar

One command measures a candidate against a base on every benchmark and writes one report. It launches the runners
the tracks ran by hand (compare/chc/modal_chc.py, compare/term/modal_term.py and modal_sv.py, compare/tip/modal_tip.py,
modal/run.py with research/frontier*/, research/realworld/ and modal/suite.json, research/query/modal_query.py), each in
its side's own tree, reads their output as their summary scripts do, reruns what differs and compares.

| File | What |
| --- | --- |
| `bar.ts` | The command: trees, launches, the shared baseline, pilots, reruns, the report, the spend |
| `bar-lib.ts` | Each benchmark's reading of a run directory (one verdict per task, as compare/*/summary.ts and research/*/score.ts count it), the comparison, the dev sets |
| `bar-dev.json` | The quick mode's dev sets (`bun gates/bar.ts devset --write`) |
| `bar-calibrate.ts` | Every past pair of runs in runs/ launched together: does the dev set's delta predict the full delta? |

```sh
bun bar                                   # this checkout against main, every benchmark, the base from the shared baseline
bun bar --quick                           # the dev sets: a few minutes, predicted full deltas
bun bar --cand gen/x --base main --only chc,its
bun bar --together                        # the base launched beside the candidate instead of the cache
bun gates/bar.ts baseline --base main     # the shared baseline alone (made on first use otherwise)
```

Groups (`--only`): `chc`; `its` (the task's statement and per component); `sv` (both); `tip` (`--rivals`: cvc5 and
Vampire too); `f1`, `f2` (the frontier corpora, broken variants counted when refused); `rw` (the real-world corpus,
law by law); `g332` (research/dag's 332 step goals: the same search, and the search time's ratio); `suite`,
`suite-usual` (one mode after the other); `onecpu` (ten 1-vCPU jobs a side of core/data.test.ts and core/infer.test.ts,
the medians and maxima of the slowest tests); `lean` (recurrent sets of the candidate's ITS run checked by Lean
4.34.0: 48, the 0.28.0 release's sample, gained ones and the s1 family first; 6 in quick mode).

**How it compares.** The candidate is a commit (a worktree under `<main>/runs/bar/trees/`), or a directory: one with
uncommitted changes is copied first, so editing it during the run changes nothing. The base comes from the shared
baseline `<main>/runs/bar/base/<sha>-<backend>-r<version>/`: N full runs (`--runs`, 3), one after the other, made once
per base commit and reused by every candidate (a lock makes two bars wait for one baseline). A task differs when the
candidate's first pass solves it and the base's majority doesn't, or the reverse, or the two decide it opposite ways.
Each differing task runs `--reruns` (3) times more on each side, together; its verdict is gained or lost when the
majorities differ, solid when every candidate run against no base run (or the reverse), a flip at the time limit when
some run answered it only in the last quarter of the limit. The noise band is the tasks whose base runs disagree or
answered late; the report counts the first-pass flips outside it. onecpu and g332 time the two sides, so their base
always runs beside the candidate. A task the backend failed (a lost VM or container, a mount error, a missing row or
job) runs once more on Modal and its row replaces the failed one; the report lists them.

**Cost hygiene.** Every launch is its runner's own command (scaledown_window=2, its own timeouts), under a wall cap,
stopped by its exact pid (SIGINT, SIGTERM, SIGKILL); any exit of the bar stops every launch and runs modal/reap.sh in
every tree it used. Each tree's first launch of a group is a pilot of one or two tasks, read before the fan-out.
`--budget` ($25 full, $6 quick) is checked between phases and every five minutes against an estimate from the task
seconds (Modal bills an hour once it is over); the report gives the bill for the bar's own apps from
`modal billing report`, and `bun gates/bar.ts spend <run dir>` reads it again later. The default backend is Modal
(`--backend boat` or `auto` are keyed apart in the cache: boat's vCPUs are faster and move answers across the limit).

## Measured

(filled in below by infra/bar's runs)
