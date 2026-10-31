# Speed: the tasks solved past 60 s, made faster (gen/laneV, after 0.41.0)

The question: which of the tasks gdp-wired solves only given more than 60 s can a general speedup bring under 60 s,
without tuning to them. Nothing trusted changed: kernel/kernel.ts, core/check.ts and lean-kernel/ are main's (d0c76bd).
Every figure below is from a run directory in the main checkout's `runs/` or this lane's scratch (named), on Modal
(2 vCPU, 4 GB a job) unless it says boat. Boat could not be used for the lane's own runs after its first hour: its API
failed (HTTP 525 on snapshots and listings, two batches lost every VM mid-run, their results with them), and the pool
had no start left (the account's reserve for other users above the day's remaining starts, `boat.py starts_left` -7).
The comparisons below are Modal against Modal, launched together.

## The tasks

The list: every task the treadmill solved past 60 s (`runs/treadmill/cache.jsonl`, configs 300:base, 300:cyclic,
300:td at b5ba56b) that no 60 s run solved: the full bar f98466545875-vs-ae369178e65d (every run of both sides) and
boat's 60 s rounds. 46 tasks: CHC-COMP 37 (ctigar 17, Lustre 15, HOLA 2, llreve 1, extra-small-lia 1), ITS 2
(juLinkedListCreateContainsAll.jar-obl-11, eric2.t2), TIP 7 (isaplanner/prop_61, prod/lemma_10, prod/prop_06,
prod/prop_19, tip2015/int_add_inv_left, int_add_inv_right, relaxedprefix_is_prefix_4). Counting the shared Modal
baseline's three runs as that bar's too leaves 41 (5 Lustre and HOLA tasks were solved there at 60 s).

## Where the time goes (the profile)

From the treadmill's 300 s runs (each stage's time from the `stages` the runner keeps), and bun's CPU profiles of the
same tasks on Modal (`compare/chc/kind.ts` or `solve.ts --kind-ms 0 --bmc-ms 0` alone, `prof-laneV/top.py`'s self and
inclusive times):

| Dominant stage | Tasks | What it is |
| --- | --- | --- |
| IMC search (second CPU) | 15: ctigar 8 (k = 15 to 29), Lustre car, DRAGON_12 ×3, FIREFLY_luke_3, MESI | core/interp.ts's queries on one clausal CDCL session: unit propagation 15–23% self, conflict analysis, the interpolant read off the DAG 18% (dillig20) |
| IMC search, an unsat run | 3: metros_4 | the start's query at depth 33–34 |
| IMC compress | 5: DRAGON_4 ×3, DRAGON_13 ×2 | `compress`: 60–120 s in the treadmill's runs for 7–15 clauses; 63% of DRAGON_4_e2_2799_e1_1303's 146 s alone |
| IMC's or a lift's kernel proof | 2: HOLA/33 (the lifted invariant's proof, 197 s), FIREFLY_6_e3 | `proveRule(.., {search: false})`: the kernel's trees for the law set's goals |
| The join (core/infer.ts) | 11: ctigar 9, HOLA/18, llreve | the join's queries (`stepWith`: 63% of up5's run), then the set's proof |
| The set's proof after the join | 1: s_multipl_17 | one step goal, 45 hypotheses, 207 s |
| ITS rank search | 2 | eric2: the relation's rank, the exact LP (`exactLp`, `floatSolve`) 48%; juLinkedList: the kernel's checks 39% (`check`, trusted), of which 23% is solve.ts checking every tree again |
| TIP lemma search | 7 | proveData's counted budget: at 60 s the lemma pass ends at 27.6k of 57k counted ms where prop_06's proof needs the pass past 35k; 52–62% of the search is the kernel's reading of a leaf's rows (`leafRows`, its pairs of cells, trusted) |

Two costs are shared across the groups:
- **The second CPU's IMC pipeline** answers 25 of the 37 CHC tasks at 300 s, and at 60 s 324 tasks of the treadmill's
  round against 257 for the join (`60-base`). There its kernel proof is the larger part: a median 10.5 s (p90 18.4) per
  IMC answer, against 1.07 s of search and 0.3 s of compress.
- **The kernel's proof of a law set already known inductive**: IMC's clauses, the join's cone, a lifted invariant. It
  is a third to a half of a join task's time after the join (up5 9 s of 56; seq3 45 of 197), and all of s_multipl_17's.

**Boat's second CPU in place.** FIREFLY_6_e3's IMC took 24.5 s alone on a whole boat VM (search 11.6, compress 6.7,
proof 6.3; the pilot, scratch `prof/pilot`), and 72 s in the treadmill's 300 s run (17.3, 23.7, 30.6), where kind.ts
runs at nice 19 beside solve.ts in a 2-vCPU slot of a VM with three other slots busy. The search, while solve.ts runs
its random and guided runs, is 1.5 times slower there; compress and the proof, while solve.ts runs the join, 3.6 and 4.9
times. One reading: solve.ts's engine threads (the collector, the compiler) take the second CPU from a process at nice
19. `solve.ts --kind-pin 1` (each process a CPU of its own) and `--kind-nice n` are there to measure it on boat; they
are off by default, and unmeasured on boat (Modal's containers name no CPUs, so the pin does nothing there). On Modal
`--kind-nice 0` lost: 5 and 3 of the 37 at 60 s against 8 and 8 at nice 19 (scratch `gate/m-cand`).

## What changed

All untrusted; every answer is still the kernel's tree or a run `checkDerivation` confirms.
- **compress asks each target once** (core/interp.ts): after a clause is added, the targets that held are not asked
  again (one more clause assumed keeps a refutation a refutation), and the pass that leaves clauses out asks a target
  again only where its last refutation named the clause left out (the assumptions MiniSat's analyzeFinal gives,
  `assumed`). The clauses are assumed before the target, so consecutive queries keep the clauses' levels on the trail.
- **The interpolant's parts kept across an IMC session's queries** (core/interp.ts's `fromDag`, `memo`): the session's
  DAG only grows, and a node's part depends only on its hypotheses' sides and its atoms' names' sides; those stay until a
  name comes to be read by both sides (counted per query), and the parts are dropped then.
- **The clausal mode's models make no path** (kernel/cdcl.ts): core/interp.ts, its only caller, reads a model's witness;
  the path was a map of every gate on the trail, made at every model (12% of MESI's IMC).
- **Assumptions by variable** (kernel/cdcl.ts): each assumption's index on its variable for the undo, and `final` walks
  variables with a stamp and a clausal clause by its codes, not names through maps.

**IMC, deterministic** (`kind.ts --bmc 0`: IMC alone, one turn, so the same invariant both sides; scratch
`gate/det-base` at d0c76bd against `gate/det-cand3` at this commit, launched apart, Modal):

| | IMC search | compress | kernel proof |
| --- | --- | --- | --- |
| 25 tasks with both phases, seconds in all | 1,266 → 961 | 720 → 311 | 293 → 282 |

By task: DRAGON_4_e3 108.7 s → 45.7 to the answer (compress 94.1 → 29.1), DRAGON_4_e2_2799 110.2 → 46.2, DRAGON_13
75.2 → 34.6, FIREFLY_6 74.5 → 38.4, MESI 145.1 → 96.6, ex2 261.2 → 124.1, dillig20 164.7 → 115.8. The k each search
answers at is the same on both sides. car_5 went 59.1 → 73.6 (its search 56 → 69 s; the two sides ran at different
times, and Modal's spread on one task is about that).

**The 46 at 60 s** (Modal, base d0c76bd and this commit launched together; scratch `gate/m-*`, `gate/m45-*`,
`gate/fin-*`): CHC solved 7 and 6 against 9 and 6 (`fin`), 5, 2, 5 against 6, 4, 6 (`m45`), 5 and 3 against 8 and 8
with compress alone (`m-*`); ITS and TIP 0 on both sides. Nearly every CHC answer on either side comes past 50 s, so
these move with Modal's spread; none is solved in every run of one side and no run of the other.

## Tried and left out

- **A root goal's refutation core first** (kernel/prove.ts, for goals of 24 or more hypotheses: the CDCL model search
  for a core, the tree grown from those hypotheses and widened to the goal): slower everywhere it ran. The join tasks'
  set proofs 9.0 → 14.9 s (up5), 19.2 → 28.7 (dillig05), 14.8 → 26.6 (nest-len), and HOLA/18 lost (`gate/join300-*`);
  IMC's proofs 9.4 → 16.2 s (DRAGON_12), 8.4 → 18.8 (dillig20) (`gate/det-cand2`).
- **The quick plain search off** (`GDP_QUICK_CAP=0`) on IMC's proofs: within the spread (`gate/var-quick`).
- **TIP's counted budget** larger at the same wall limit (`--ms 100000` to `297000` at 60 s): not run (boat lost the
  batch). The 300 s order of the same search answers prop_06, prop_19, lemma_10 and int_add_inv_right before 57 s of
  wall time on boat, so the budget's split, not the search's speed, is what keeps them past 60 s.
- **The ITS runner's second check of every tree** (compare/term/solve.ts) repeats goalsProven's check on the same goals:
  23% of juLinkedList's run. Left as it is (it is the runner's own check of the answer).

## Gates

- tsc, build and lint in the suite's form: 0, 0, 0 (scratch `gate/fin-cand/check.log`); interp, infer, the kernel
  and CDCL fuzz seeds 1 and 2 pass.
- The ten protocols at 60 s: proven, ten of ten, on both sides (`gate/fin-*`).
- The bars, on Modal against ae36917's Modal baseline (boat had no VM to give; the main checkout's
  `runs/bar/runs/laneV-*-b3187c0-modal`). The base's reruns failed to launch on Modal (its tree, from before
  supercomputer/'s rename, has no `supercomputer/.live`), so a task's rerun verdict reads the candidate's reruns against
  the baseline's three runs. The candidate also carries main's commits since ae36917 (the bar of f984665, near them,
  measured +2 on CHC).
  - Quick: CHC dev set +10.67 (predicted full +17.7), gained 6, lost 0; ITS +1.33 (gained 2, lost 1, none solid), per
    component -0.33; SV-COMP, TIP, the frontier corpora and the real-world corpus 0; wrong 0 everywhere.
  - Full, CHC, ITS and TIP: CHC 1,181 against a base mean of 1,165 (+16; sat +15.33), gained 10 (DRAGON_13 ×2,
    FIREFLY_6 ×2, FIREFLY_luke_2, FIREFLY_rt, FIREFLY_u1, MESI_i3_e1_447_e1_1292, nested8, durationThm_3), lost 2, none
    solid (NetBSD_loop_int 0 of 4 against 2 of 3, DRAGON_4_e2_2799_e3_1915 2 of 4 against 3 of 3); ITS +1.33 (per
    component -0.33, ndes lost 2 of 4 against 3 of 3); TIP 0; wrong 0.
  - `--only suite,suite-usual`: no job failed, none differs, in either mode.
- Not run: the 46 and the bars on boat (no VM to be had), and the 200-run gauntlet (core/infer.ts and kernel/epr.ts
  unchanged).
