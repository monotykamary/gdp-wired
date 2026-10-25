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

Every figure from the run directory named, under the main checkout's `runs/bar/`; Modal's bill from `modal billing
report` where the hour was over, else the bar's estimate from task seconds (which came within 0.3% of the bill on
`repro-chc7-cache`, $2.34 against $2.343, and `repro-chc7-quick`, $1.31 against $1.3159).

| Run | Wall | Modal |
| --- | --- | --- |
| The shared baseline of main e1711ca, 3 runs of every group, one after the other (`base/e1711cace848-modal-r1`) | 3,172 s | $14.73 billed |
| Full: infra/bar (main f2e468d) against it, every group, reruns, Lean 48 (`runs/full-infra-bar-vs-e1711ca`) | 1,249 s, the suites one mode after the other being the longest path | $6.26 estimated |
| Quick: the same, dev sets, Lean 6, no suites (`runs/quick-infra-bar-vs-e1711ca`) | 780 s; every group but Lean ended by 367 s | $3.09 estimated |
| The quick Lean sample drawn under 200 KB, since (`runs/quick-lean-check`) | Lean 29.4 s after ITS | |
| A track today, runs/chc7 (gen/chc7): its runs/ activity, 11:20 to 12:24 | 64 min, launched and compared by hand | $20.61 billed (48 apps) |
| A track today, runs/rw3 (gen/realworld3) | 152 min | $13.52 billed (58 apps) |

**The cache against launching together.** Main e1711ca against its own baseline (`runs/validate-e1711ca-full`): CHC
1,087 against 1,084, 1,085 and 1,086 (6 differ, 3 outside the band; after reruns 1 gained and 1 lost, neither in every
run, both answered past 45 s, 4 noise); ITS 1,151 against a mean of 1,152.33 (2 differ, both in the band, noise);
per component 2 differ, noise; SV-COMP, TIP, both frontier corpora and the real-world corpus with no task differing;
the 332 goals the same search on all 332; Lean 48 of 48; `--usual` 224 of 224 (the default suite's client hung on a
call Modal lost, 0 tasks running for 20 minutes: modal/run.py now bounds each wait). Two past merges, the candidate
against a baseline of its base made at another time:

| | Launched together (the track's runs) | Against the cached baseline (`runs/repro-*-cache`) |
| --- | --- | --- |
| gen/chc7 2601d15 against a269124, CHC | 1,084 against 1,037 (+47); 65 differ; gained 52 (42 in every run), lost 3 (2) | 1,089 against 1,042, 1,043, 1,045 (+45.67); 54 differ; gained 47 (41), lost 3 (2) |
| gen/realworld3 891a238 against 4af8556, the real-world corpus | 274 against 259 (+15); gained 15 (13 in every run), lost 0 | 274 against 258, 259, 258 (+15.67); the same 15 laws gained, all 15 in every run, lost 0 |

Of chc7's gains, 44 are gained both ways and 39 in every run both ways; every task classified differently but two
(HOLA/24.c, ctigar/gulv_simp.c) was answered past 45 s in some run (the launched-together base ran slower: 1,037 against the cached 1,042 to 1,045). The
size line matches the CHANGELOG's (+47,448 bytes, +585 lines). So the cache is the default; `--together` stays.

**The dev sets** (`bun gates/bar-calibrate.ts`, every past pair of full runs in runs/ launched together; the dev sets
drawn from e1711ca's run 1, `gates/bar-dev.json`):

| Benchmark | Dev set | Pairs | r, predicted against full | Mean error | Pairs with a full delta within ±30: r, mean error, sign right |
| --- | --- | --- | --- | --- | --- |
| CHC | 662 of 1,406 | 42 | 0.994 | 2.9 | 36: 0.964, 2.45, 32 of 34 |
| ITS | 398 of 1,239 | 54 | 0.998 | 4.1 | 46: 0.937, 2.92, 34 of 42 |
| SV-COMP | 129 of 282 | 57 | 0.988 | 2.5 | 52: 0.908, 2.19, 35 of 38 |
| TIP | 239 of 492 | 49 | 0.635 | 2.2 | 49: 0.635, 2.21, 37 of 43 |
| Frontier 1 | 48 of 134 | 47 | 0.947 | 0.0 | |
| Frontier 2 | 64 of 94 | 50 | 0.893 | 0.1 | |
| Real-world | 91 of 311 | 51 | 0.959 | 0.7 | 51: 0.959, 0.71, 26 of 26 |

CHC at 257 tasks predicted with a mean error of 7.9 (r 0.789 on the small deltas), at 450 5.05, at 662 2.45. TIP's
past deltas are within -3 to 11, mostly noise, so its subset predicts poorly; its full run costs $0.55, so
`--only tip` without `--quick` is the better inner loop for TIP work. Measured: gen/chc7 against a269124 in quick mode
(`runs/repro-chc7-quick`) predicted +41.8 (raw +35.33 on 662 tasks), the full run +45.67.
