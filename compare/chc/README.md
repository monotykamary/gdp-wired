# CHC-COMP's LIA-Lin track through gdp-wired

Every rule and law elsewhere in this repo was written here. This directory runs gdp-wired on problems it didn't write:
the 1,406 tasks of CHC-COMP 2026's LIA-Lin track (linear constrained Horn clauses over integers and booleans,
`chc-comp/chc-comp26-benchmarks` at `b4fa7a7`), beside three solvers built for them: Z3's Spacer (5.3.1), Golem (0.9.0)
and Eldarica (2.3).

| File | What |
| --- | --- |
| `chc.ts` | The CHC-COMP format read (S-expressions, predicates, clauses), and an evaluator of a clause on values that uses no gdp-wired code |
| `translate.ts` | A linear CHC system as a rule: the state is where a derivation is (start, a predicate, error) and the predicate's arguments; a request names a clause that fires where the run is (the rule's assumption) and the values it leaves free, so each update reads the clause named alone. The law: error is never reached. `checkDerivation` checks a run against the CHC itself |
| `houdini.ts` | The first Houdini (`--old-houdini`): candidate laws per predicate (bounds, differences, sums, booleans, unreachable), those a run's state breaks dropped, then rounds of `proveRule` until the rest are inductive together |
| `solve.ts` | One task: import, `proveRule` on the law, random runs of the compiled rule, runs the prover guides (each request a model of its clause's condition where the run is, the clauses that derive false tried first), then the library's invariant search (`inferLaws`, core/infer.ts) from the states the runs reached; the bounded runs on the second CPU (`kind.ts`; `--bmc-here`, this process's stage after the guided runs, 15 s, as before). Answers sat (a proof the kernel checked), unsat (a run reaching error that `checkDerivation` confirms), unknown or unsupported |
| `modal_chc.py` | The track on Modal: every task in its own container (2 vCPU, 4 GB), each tool under the same 60 s wall-clock limit, all at once (`starmap`) |
| `summary.ts` | The table below from a run's `results.jsonl`, with wrong answers counted against each task's expected verdict where some tool decided it at CHC-COMP'26 |
| `compose.ts` | The system the searches read (`prepare`): chains composed away (a predicate with no clause to itself whose incoming times outgoing clauses are no more than the two together, each pair made one clause), and with `--slice` the cone of influence as a weakening (definitions of what nothing relevant reads dropped). `expand`: a derivation of it as requests of the original rule, replayed there and checked by `checkDerivation`. `lift`: an invariant of it as laws of the original rule, an interpolant at each eliminated predicate (or its weakest precondition), which the kernel proves of the original (`liftProven`) |
| `kind.ts` | The container's second CPU, a process at the lowest priority started once the task is read, until the search's deadline: interpolation over the unrolling first (core/interp.ts's `imcSearch`, one CDCL session in the clausal mode for the whole search), whose same session asks k-induction at each depth where the rule is as written (proven by core/kind.ts at that k) and the start's query at each depth (the bounded runs'); beside it the forced run of a deterministic loop (core/bmc.ts's `boundedSearch`, `--bmc-depth 0`; with `--bmc-depth 64` the k-step goals from the start after it, on one unrolling), in slices of 2 s, 4, 8, ...; an invariant made a few clauses (`compress`) and proven by the kernel (lifted to the original where composed), a run `checkDerivation` confirms, stops solve.ts and answers. `--imc 2 --imc-first 0 --kind 1 --bmc-depth 64` is gen/chc7's turns |
| `prof/kind.ts` | Not a solver (`--tools kind`): whether the law is k-inductive, a measure of what k-induction would add |
| `prof/kind-tree.ts`, `prof/kind-lean.ts` | Not solvers: where a k-step goal's time goes (CDCL's model search, its tree, the unfolding, the check), and a task's k-induction certificate as Lean (KInd.lean's `kind_sound`) |
| `prof/gap27.py` | The gap at a release by group, family and cause, from runs of the track and Spacer's and Golem's answers |
| `prof/imc.ts`, `prof/tpa.ts` | Not the solver (`--tools imc`, `--tools tpa`): interpolation over the unrolling (core/interp.ts, its invariant made small by `compress`; `GDP_IMC_QSTATS=1` prints each query's ms, CDCL nodes and decisions) and transition power abstraction (core/tpa.ts) alone, each answer checked as solve.ts checks it |
| `prof/itpdirs.ts` | Not a solver (`--tools itpdirs`): the directions of Spacer's invariant atoms that bounded refutations' interpolants find, from `prof/gap-models.json` (Spacer's models of the gap tasks, `runs/modal/chc2/spacer-models-sat/models.jsonl` by smt2 path; not kept) |
| `prof/` | A Modal profiler for one task's `proveRule` (it and `spacer_models.py` Modal-only and historical); `spacer_models.py`, the invariants Spacer finds for given tasks (or, with `--engine golem`, Golem's derivations of false); `template.ts` (`--tools tmpl`), what `inferLaws` would search on a task (its atoms, coefficient magnitudes and shape limits); `given.ts` (`--tools given`), `proveRule` given Spacer's invariant as laws; `gap.py`, the gap to Spacer by the shape of its invariant and what gdp-wired did |

    modal run compare/chc/modal_chc.py --out runs/modal/chc/<name> [--tools gdp,z3,golem,eldarica] [--limit 60]
    bun compare/chc/summary.ts runs/modal/chc/<name>
    modal run compare/chc/prof/spacer_models.py --out <dir> --tasks-json <file> [--engine golem]
    modal run compare/chc/modal_chc.py --out <dir> --tools tmpl            # then --tools given --tasks-json <file>
    python3 compare/chc/prof/gap.py --gdp <run> --others <run> --models <dir> --template <run> [--cex <dir>] [--given <run>] --out <file.json>
    modal run compare/chc/modal_chc.py --out <dir> --tools golem-imc,golem-tpa   # Golem with one engine of its own

## Cheaper queries, on gen/chc-speed (after 0.30.1)

The runs named here are in the main checkout's `runs/bar/runs/chcspeed-*` (Modal, 60 s, 2 vCPU), against 3cdf37e's
shared baseline (1,163, 1,165 and 1,162). Nothing trusted changed.

**Where a deep query's time went** (metros_4_e1_917, IMC alone, `prof/imc.ts`, bun's CPU profile of 20 s, local):
- core/nonterm.ts's `simpC` on each interpolant took 32.6%. Its `and` copied each nested and of a binary chain anew,
  and read a part shared along the DAG once per path to it.
- The simplex took about 40%: pivots, and the tableau begun again after a deep backjump.
- Unit propagation took 22% and relevance 12%: about 2,000 assignments a node at depth 19, the unrolling propagated
  again after each backjump.

With `simpC` linear (each nested part walked once, each part kept once), the queries are the same (316 of 316, the same
node counts). Interpolation at depth 20 takes about 0.15 s a depth, where it took 1.7 s. IMC on Modal reaches the
24-step runs of metros_2_e2_704, metros_2_e3_112 and metros_3_e3_1275_e1_1350.

**Deep unsat.** Golem's k-induction finds metros_4_e1_917's 35-step run in 0.74 s, and its TPA in 0.1 s
(`runs/chc6/golem-engines`). IMC asks 10 to 15 frontier queries at each depth, so the start's query, which is the
bounded run, reaches depth 31 in 60 s (local). Asked alone on the same session, the bounded runs reach 34 in 14 s.
core/bmc.ts's unrolling in the clausal mode (a `clausal` option of `boundedSearch`, measured at 4f7d7e6) found that run
in 25 s; the kernel's reading reached depth 10 in 20 s. The dev set with the k-step goals on the second CPU
(`--bmc-depth 64`, clausal):

| run | IMC's turn | dev set (662) | full |
| --- | --- | --- | --- |
| q1-simp | (no k-step goals) | 518 against 517.33 | 1,162 (`chcspeed-final-chc`) |
| q2-bmcx2 | twice theirs | 520 | 1,161 (`chcspeed-full`) |
| q2-bmcx4 | four times | 515 | |
| q3-bmcx1 | equal | 518 (unsat +4.33, sat -3.67) | |

The share is zero-sum: at a third of the CPU, the bounded runs reach depths 25 to 32 on the metros systems (their runs
need 34 to 35), and IMC loses late sat answers. So the default stays `--bmc-depth 0`, and the clausal option, which
nothing ran at that default, was taken out again (gen/slim).

**Tried and dropped** (local, metros_4, DRAGON_12, car_5):
- the tableau begun again against the most rows read since it was begun (fewer pivots, a slower search);
- the free basic slack rows taken out before a rebuild (no rebuild avoided);
- a rebuilt tableau seeded from the last point (no fewer pivots);
- larger rebuild thresholds;
- bound propagation over every open atom in the clausal mode (depth 21 against 23 in 20 s);
- the DAG's interpolants kept from query to query (the same search, no measurable gain);
- IMC's depth growing by k/4 (worse);
- TPA's queries on the clausal DAG: stuck at level 1, because its midpoints are full points, which Golem generalizes;
- stuttered bounded runs whose depth grows by k/4.

## IMC's query made cheap: the goal read as clauses, one session for the search, on gen/chc8 (after 0.28.0)

Every run named here is in the main checkout's `runs/chc8/` and `runs/bar/runs/` (60 s, Modal, 2 vCPU), against main
b12965e's shared baseline (`runs/bar/base/b12965ecddfc-modal-r1`, three runs). Nothing trusted changed: kernel/kernel.ts,
kernel/cyclic.ts, core/check.ts and lean-kernel/ are main's. Every sat answer is the kernel's proof (on the original rule,
lifted where composed), every unsat answer a run `checkDerivation` confirms.

**Where IMC's time went** (FIREFLY_11, 132 state values and 104 request values a step; bun's CPU profile of 12 s of
gen/chc7's IMC, `runs/chc8` notes): the reader's rows (reader.ts's `sync`) 5.25 s, of which its own bookkeeping of what
each value read (`read`, `touch`, `walk`, `readAtom`, self time) 3.88 s; the decision's candidates, every hypothesis'
open atoms scanned at every node, 2.20 s; the simplex and the exact elimination 1.03 s; building the goal and reading
the interpolant off the DAG a few ms each. The eighth query: 4,025 nodes at about 1.4 ms each, 2,527 decisions for 574
conflicts. Golem's IMC answers the task at its third lookahead in 0.17 s (locally), its invariant 212 KB: the queries
are the same in kind, about a hundred times cheaper.

**The structure.** One search engine, one unrolling, one session:
- **The goal read as clauses** (reader.ts's `Clausal`, kernel/cdcl.ts's clausal mode, a model alone wanted): each
  hypothesis as clauses over atoms and gates (Tseitin's, written for the polarities a gate is read in, Plaisted and
  Greenbaum), a term's choices (if, min, max, ∸, a division or remainder by a constant) lifted out of the comparison
  that reads them, case by case (past 16 cases a fresh natural). Unit propagation over two watched literals (a blocker
  each) in place of the reader; the rows at a node the trail's atoms and their names' naturals; a decision the most
  active relevant variable (relevance top-down: a hypothesis' own clauses at once, a gate's where the gate holds the
  value that needs them), never a case's atom; up to 16 decisions at the simplex's point between two simplex checks;
  the most violated row first and the sparsest column for the first 200 pivots of a check, Bland's rule after. Where a
  goal reads what the clauses don't (a product, a map, a quantified flag), the kernel's reading as before. Its refutation
  is a DAG whose leaves are theory conflicts or a hypothesis' clauses; the interpolant is McMillan's own system over it
  (the strongest; gen/chc7's is its dual, the weakest).
- **IMC on one unrolling** (core/interp.ts's `imcSession`): each step's hypotheses written once in names that stay (the
  state before the first step the machine's own names, one renaming a step so the parts its updates share stay shared:
  kernel.ts's substC writes a DAG out as a tree), the law broken after step k behind act@k, each frontier behind a
  selector of its own, retired when the next comes (its clauses read no more). McMillan's own loop, as Golem's IMC.cc
  has it: the query starts from the latest interpolant, not from all of them (gen/chc7's R ∨ I grew every query). The
  refutation's DAG ends in the clause of the two assumptions, so the interpolant is the query's as asked. The states
  reached so far are a second session's: each frontier's negation once, the next interpolant behind a selector.
- **The same session's other queries**: the start's query at each depth is the bounded run of that depth (a model is
  a run, replayed and checked); k-induction at each depth, the law before each of the first k steps behind ind@j, its
  refutation then proven by core/kind.ts at that k (the rule as written: a composed rule's k-induction is not the
  original's). The forced run of a deterministic loop stays beside it (s_split's 10,002 steps).
- **The invariant made small** (`compress`): IMC's R, the frontiers' disjunction, is correct (each interpolant checked
  on its own by the kernel reading's model search: FIREFLY_11's 10 of 10) but the kernel's proof of its step took past 38 s.
  PDR at one frame with R as the oracle: a state the clauses and the law allow, one step from which breaks one of them,
  lies outside R; read by R's atoms, the atoms R's refutation needs (its assumptions, then each dropped while R still
  refutes the rest) are a cube; its negation, generalized by relative induction (an atom dropped where the clause
  without it holds at the start and after every step from where it and the clauses hold), a clause; every clause
  generalized again from the full frame, then each left out where the rest still holds. FIREFLY_11: 3 clauses, proven
  in 1.5 s (locally); without the relative induction 25 clauses of 11 atoms, 8.8 s; R as it is, not proven in 38 s.

**The query, before and after** (16 tasks of the gap: FIREFLY, DRAGON, ctigar, metros, car, durationThm; IMC alone,
`prof/imc.ts --tools imc` with `GDP_IMC_QSTATS=1`; `q-before` on b12965e, `q-after2` on this branch):

| | queries | median ms | p90 ms | max ms | CDCL nodes, median |
| --- | --- | --- | --- | --- | --- |
| b12965e (gen/chc7's IMC) | 346 | 1,239 | 4,663 | 24,033 | 927 |
| gen/chc8 | 1,419 | 81 | 450 | 17,623 | 42 |

The queries are not the same ones (the frontier's against R ∨ I; deeper depths reached): a median 15 times and a p90
10 times cheaper. By task, FIREFLY_11 3,346 → 317 ms (sat at k = 4), DRAGON_4 6,456 → 530 (sat), car_6_e2_893 1,995 →
44 (unsat, 13 steps), nest-if7 1,249 → 53 (sat at k = 12, Golem's lookahead 10), metros_4_e1_917 1,133 → 92 (depth 18
by 60 s; Golem reaches its lookahead 32 in about 2 s).

**IMC alone on the 239 gap tasks** (`prof/imc.ts`, 55 s, chains composed): gen/chc7 41 (`runs/chc7/i1-comp`); the
session, frontier and compression 94 (`i2-sessc`); McMillan's strong interpolants 111 (`i3-strong`, the dual 103);
the greedy pivots and the interpolants tidied 125 (`i4-g1t1`; 122, 116, 120 without either or one); the final commit
119 (`i5-final`). Golem's IMC: 193.

**Measured on the whole track** (one run each, counted as the bar counts them, against the baseline's 1,079, 1,083
and 1,085; `runs/chc8/t*`):

| run | what | solved |
| --- | --- | --- |
| t1-imc2 / t1-imc1 | gen/chc7's turns (IMC sharing k-induction's slice) / IMC its own turn | 1,132 / 1,140 |
| t2-first / -x2 | IMC's turn first / and twice as long | 1,149 / 1,150 |
| t3-nokind / -x4 | no k-induction / IMC's turn four times as long | 1,154 / 1,154 |
| t4-sesskind | k-induction on IMC's session, no turn of its own | 1,147 (1,149 with -x2) |
| t5-nokind / -sesskind / -kind | compression by relative induction: none / on the session / its own turn | 1,164 / 1,163 / 1,163 |
| t6-nobmc | no bounded runs at all | 1,150: the forced runs' s_split ×17 lost |
| t7-sess / -forced | greedy pivots, interpolants tidied; the bounded runs' k-step goals / the forced run alone | 1,159 / 1,162 |
| t8-clausal / -strong | the lift's interpolants the clausal mode's too: dual / strong | 1,158 / 1,166 (HOLA/14, 26 lost either way) |

The answers near the limit flip from run to run (of the 41 tasks t3-nokind, t3-x4, t4-sesskind and t2-first disagree
on, 29 were answered past 45 s in some run): what moved the count was what made IMC's answers earlier. The default
(solve.ts) is `--imc 1 --imc-first 1 --kind 0 --bmc-depth 0`: IMC's session first, k-induction and the start's queries on
it, the forced run beside it; the lift's interpolants stay the kernel reading's (t8: the clausal mode's lose HOLA/14
and 26, which the bar of 6776a87 confirmed, 0 of 4 against 6 of 6).

**Timeouts.** The bar of 5044f13 had 21 timeouts against the baseline's 1 to 4: solve.ts waited for the second CPU
past its own deadline, and a kernel proof there (durationThm_3: IMC's invariant at 0.8 s, its clauses at 1.0 s, the
proof still running at the cap; locally it takes 0.2 s) read past kind.ts's. solve.ts now stops waiting half a second
after its deadline (183f4e2): 2, 3 and 3 timeouts in the three runs below.

**The final commit (183f4e2), three runs of the whole track** (`runs/chc8/final-r1`..`r3`): 1,166, 1,164 and 1,166
(mean 1,165.33, spread 2), every one wrong 0 with the same 2 disputed labels; Spacer 1,163 and Golem 1,154 (our
harness, unconfirmed under CHC-COMP's own setup). Against the baseline's three runs: gained in every run 65 (ctigar 15,
FIREFLY 11, car 7, metros 7, reve 4, DRAGON 4, durationThm 4, the rest 13), lost in every run 0; lost in a majority 1,
ctigar's nest-len (unknown, unknown and a timeout against the base's 53.9 and 54.9 s and one unknown: at the limit).

**The full bar of 183f4e2** (`runs/bar/runs/183f4e2042d5-vs-b12965ecddfc-full-2026-10-251345`): CHC 1,174 against a mean
of 1,082.33 (gained 77, 59 in every run; lost 0; wrong 0), a fourth run of the commit: with it the four runs are 1,166,
1,164, 1,166 and 1,174, a mean of 1,167.5 whose margin over Spacer's 1,163 (4.5) is below their spread (10); the three
runs alone clear it (2.33 against 2). Everything else level: ITS 1,153 against 1,153 (per component 1,157 against
1,156.67), SV-COMP 246 and 216 as the base, TIP 212 against 212.67 (one differing, noise), the frontier corpora 90 and 32
against 90 and 31 (every broken variant refused), the real-world corpus 274, 29, 8 as the base, the 332 step goals the
same search on all 332, both suites 224 of 224, the 1-vCPU tests within the base's spread (no failed job), Lean 47 of
48 (slayer-3-new.t2_fixed's export fails to compile on a noncomputable definition, its theorem on the standard axioms;
the same export error is in the infra/bar runs against e1711ca, before this branch).

## Chains composed away and interpolants off CDCL's DAG, on gen/chc7 (after 0.28.0)

Every run named here is in the main checkout's `runs/chc7/` (60 s, Modal, 2 vCPU), beside main a269124 launched
together. Nothing trusted changed: kernel/kernel.ts, kernel/cyclic.ts, core/check.ts and lean-kernel/ are main's. The
branch has it on by default (`solve.ts --compose 1 --imc 2`; `--compose 0` is main's path with gen/chc6's IMC sharing k-induction's slice).

**The structure.** One CHC-to-CHC layer (compose.ts) in front of every search, and one primitive behind it:
- **The system searched** is the original with its chains composed away (large-block encoding): a predicate with no
  clause to itself whose incoming times outgoing clauses are no more than the two together is eliminated, each pair
  made one clause. Every predicate stays declared in its order, so the composed rule has the original's locations and
  slots, and a law of one reads the same names in the other. HOLA's 26-predicate chains shrink to their loops (HOLA/13:
  33 clauses to 10). 341 of the track's 1,406 tasks change; the Lustre and ctigar transition systems (one predicate)
  don't.
- **Unsat** (`expand`): each composed step's variables valued (translate.ts's `envOf`, split out of
  `checkDerivation`), each original clause it is made of given its own free variables' values, the run replayed on the
  original rule and checked by `checkDerivation` against the original CHC, as every run is.
- **Sat** (`lift`): the predicates eliminated, in reverse order. When Q was eliminated, its incoming and outgoing
  clauses joined predicates alive then, each kept or eliminated later, so each already has its condition J; their
  products were clauses of the system after Q, which J models. So no state J allows at a predecessor reaches, through
  Q, a state J doesn't allow at a successor: that two-step goal, on the rule of those clauses alone, refuted and colored
  after its first step, gives an interpolant I with every state into Q in I and every step out of I keeping J. With
  `loc = Q → I`, J models the clauses before Q went; in the end every original clause. Where no interpolant comes and
  no clause out of Q leaves a value to the request, its weakest precondition stands in. The kernel then proves the
  original rule's law with the lifted laws (proveRule, no search): the certificate is the original's.
- **One primitive:** the lifting's query is IMC's own (`cutInterpolant`: the kernel's k-step goal colored at the first
  cut), and IMC, TPA and the lifting all read their interpolants off CDCL's refutation DAG (`fromDag`), McMillan's way
  over resolution: no tree unfolded, no leaf read again. A leaf whose integer cut mixes A and B is refuted again over
  the rationals (core/solver.ts's elimination with no cut). The tree route stays as the fallback.

**What made it work:**
- **The lifted laws' repeated atoms once** (`tidy`, a comparison known by its linear form): HOLA/16's proof of the
  original from 11.4 s to 3.0 s (locally).
- **The law read per location** (each condition with its location put in and folded), with `never error` beside it.
- **A clause's unread variables dropped:** the `CHC_COMP_UNUSED` Bool of a `fail → false` query became a request value,
  and with it s_split_08's join failed.
- **Functions an invariant reads** (a remainder by 2) can't be read by the kernel's step-law goal; that predicate goes to
  its weakest precondition.
- **Certificates:** a sat answer's are the usual trees, checked by kernel.ts (`GDP_CERT=usual`, solve.ts's default
  here): the cyclic translation took its 10 s cap on the proof of HOLA/13's composed rule with IMC's invariant (10.3 s against 0.2 s, locally). On main it changes
  nothing on the dev tasks (`d1-main` 236, `d1-mainu` 236).

**The whole track** (`f1-chc-*`, wrong 0, the same 2 disputed labels on both sides):

| | sat | unsat | solved | timeouts |
| --- | --- | --- | --- | --- |
| gen/chc7 | 657 | 427 | 1,084 | 1 |
| main a269124 | 612 | 425 | 1,037 | 7 |

- **Gained 56, lost 9.** Rerun 3 times a side (`f1r1`..`f1r3`): 179 answers against 42 of 195, none wrong.
- **Gained in 3 of 3 against 0 of 3:** 42 tasks. HOLA ×26, reve 004, 004b, 010, 010b, barthe2-big2,
  array_fill1_abstracted, array_init, s_split_44, SYNAPSE_4_e8_420_e7_572, car_2_e8_491_e7_826, loop__barthe2 ×3,
  loop__fib (clausified), simple-5-hhk2008, O0_sum01. The rest gained: car_2_e7_1027_e7_359 2 of 3, nested5 2,
  array_fill2_abstracted 2, nest-len 1, against 0; car_2_e7_1027_e1_1047 and durationThm_2_e1_118 3 against 1,
  s_split_22 3 against 1, durationThm_2 ×2, reve 019b and bmc-1-test-bmc-1-unsafe 3 against 2; up5 1 against 1, reve 025d
  and rtp_3 3 against 3.
- **By:** IMC 31 (16 on composed systems, 15 on systems composition leaves as they are: the DAG's interpolants), the join on the composed
  rule 23, the bounded runs 2. By family: eldarica-misc 33, Lustre 8, llreve 4, ctigar 3, the rest 8.
- **Lost in 3 of 3:** s_split_28 and s_multipl_17 (0 of 3 against 3 of 3). Each composes only its query proxy away (`inv
  → fail → false` to `inv → false`); the join's samples and proofs change with the rule (s_multipl_17's final proof
  takes 34.5 s on the composed rule).
- **Lost at the edge:** metros_1 ×5, 14 of 15 against 15 of 15, k-induction's answers at 41 to 54 s here (27 to 31 s on
  main): IMC shares its slice (as on gen/chc6). id_build 3 against 3, gulv_simp 1 against 0.
- **Lifting:** 162 of 172 lifts proven, the lift a median 70 ms (at most 7.07 s), the original's proof 436.5 ms (at most
  30.6 s). Not proven: the original's proof undecided at the deadline 8 times, the lift out of time once, a step goal
  reading a function once.

**The dev tasks** (513: the 341 composed and the 239 gap tasks, `d1`..`d4`): 278 against 236 in `d4`. `--slice` (the
cone of influence as a weakening: what nothing relevant reads made the request's) measured 272 against 275 without it
(`d3`): kept opt-in.

**Does IMC pay now?** On the 239 gap tasks, IMC alone (`i1-*`, `prof/imc.ts`, 55 s): 41 with the chains composed and the
DAG's interpolants, 20 with the DAG's alone, against gen/chc6's 7 (`runs/chc6/imc1`) and Golem's 193. Wired in, it
answers 31 of the 56 gained. Of the 198 it leaves, 189 end at the budget: the per-query cost on the one-predicate
systems is what is left. FIREFLY_11 (55 integers, 21 booleans, 60 request values): its eighth query took 3,744 CDCL
nodes, about 1.5 ms a node, reader.ts's re-reading 42% of it (locally); Golem answers it in 0.07 s. Composition does
nothing for the 172 gap tasks it leaves as they are (the Lustre and ctigar transition systems among them).

## Interpolants and transition powers, kept on gen/chc6 (after 0.28.0)

Every run named here is in the main checkout's `runs/chc6/` (60 s, 2 vCPU; Modal unless named boat). Nothing trusted
changed, none of the existing searches changed, and nothing is merged: on the full track the best variant is level with
main. The branch has it opt-in (`solve.ts --imc 2`).

**What the leaders' techniques do on our gap** (`golem-engines`, boat: Golem 0.9.0 with one engine each, on the 239
tasks Spacer or Golem solves at 60 s and five runs of main never did; our "Golem 1,154" is its default engine, spacer):

| Golem engine | solved of 239 | sat | unsat |
| --- | --- | --- | --- |
| `imc` (McMillan's interpolation over the unrolling) | 193 | 162 | 31 |
| `split-tpa` | 109 | 77 | 32 |
| `lawi` (lazy abstraction with interpolants) | 108 | 77 | 31 |
| `tpa` | 78 | 46 | 32 |
| `kind` (k-induction with bounded runs) | 60 | 29 | 31 |

The union is 211. IMC answers 147 of its 193 in under a second, and Golem's k-induction with its bounded runs 31 of
the 32 unsat (metros and car among them).

**What was built** (core/interp.ts, core/tpa.ts; core/interp.test.ts):
- **Interpolants from the kernel's trees** (`fromTree`): any coloring of a refutation tree's hypotheses into A and B.
  At a leaf, its derivation is replayed with each row's A part beside it (an input of A's whole, a combination adding
  the parts, a cut dividing whichever part holds the variables, else no interpolant there); a split on A's atom or-s
  its sides, on B's and-s them, and a path atom over shared names is kept in the leaf's interpolant. `interpolate`
  renames B apart and ties the shared names. The tests check A ⊨ I and B ∧ I refuted by trees the kernel checks.
- **IMC** (`imc`, `imcSearch`): the kernel's own k-step goal (stepLawObligations) with R as its `when`, on the machine
  whose step stays put once the law is broken, integers relaxed (core/bmc.ts's `relax`). Refuted, the interpolant at
  the first cut joins R; one within R is a fixed point, an invariant the kernel proves with the law (proveRule).
- **TPA** (`tpa`): relations R_n ⊇ T^{≤2ⁿ}, R_0 a step or none, each R_{n+1} the interpolants of two R_n against a
  start and a target; a model's middle state recursed into at n − 1 as an exact point; Houdini over R_{n+1} read from
  the start for invariants.
- **Interpolant directions as the join's shapes** (measured, then dropped: below).

**Each alone** (`prof/imc.ts`, `prof/tpa.ts`, 55 s):
- **On the 239 gap tasks:** IMC 7 (`imc1`: car_2_e7_1027_e7_359, car_2_e8_491_e7_826, array_fill1_abstracted,
  SYNAPSE_4_e8_420_e7_572, simple-5-hhk2008, durationThm_1 and its e3_389_e6_167, at 10.2 to 57.5 s, the kernel's proof
  6.1 to 20.0 s of it). TPA 0 (`tpa1`, `tpa2-unsat`: 0 of the 32 unsat).
- **What they subsume** (`rep1`): of the 120 tasks main's k-induction answers (sat), IMC 107 (median 9.9 s), TPA 3; of
  100 drawn from the 335 main's bounded runs answer (unsat), IMC 83 (median 3.0 s), TPA 30.
- **The cost:** a proof-producing query is the kernel's tree. HOLA/13's two-step goal: CDCL 270 to 920 ms, reading the
  64 to 230 leaves 130 to 270 ms more. car_6_e2_893's TPA query of two steps: 1.1 to 1.9 s. A counter to 10 (12
  steps) takes TPA 10 s to level 3, and to 20 more than 30 s: each refinement learns a case-split interpolant.
- **What interpolants at affordable depths say** (`itpdirs1`, the 185 gap tasks with a Spacer model, 156 that ended in
  time): Spacer's 1,442 atom directions, 284 among the interpolants'; of its 127 beyond the join's templates (more
  than three values or a coefficient past 3), 20, on 16 tasks. Locally, ctigar's nest-if7 and dillig19 to depth 7
  give interpolants of the program counter's bits alone, and HOLA/13 to depth 4 of its location alone
  (`24 <= loc~1 <= 24`): eldarica-misc/LIA's 42 multi-predicate gap tasks have 27 predicates at the median, 13 on
  cycles.

**Wired in, against main** (each batch launched together; wrong 0, the same 2 disputed labels on both sides):

| run | what | this | main |
| --- | --- | --- | --- |
| `d3-*` (339 dev tasks) | interpolant directions as shapes (4 s from the guided runs); the guided runs at 4 s alone | 101; 102 | 102 |
| `f1-chc-*` (track) | the shapes | 1,039 (611 sat, 428 unsat) | 1,044 (615, 429) |
| `e1-*` (557 dev) | IMC in turns beside k-induction and the bounded runs; IMC in k-induction's place | 321; 318 | 318 |
| `f2-chc-*` (track) | IMC in turns (`--imc 1`) | 1,040 (624, 416) | 1,042 (613, 429) |
| `e2-*` (579 dev) | IMC sharing k-induction's slice (`--imc 2`); in turns | 337; 332 | 334 |
| `f3-chc-*` (track) | IMC sharing k-induction's slice (`--imc 2`) | 1,043 (614, 429) | 1,044 (616, 428) |

- **In turns** (`f2`), sat +11 and unsat −13: IMC's turns take the bounded runs' late ones (car_5 ×6, metros_2 ×2,
  FIREFLY_a3 ×2, swimmingpool_1, reve 025c, bmc-1-test, at 28 to 54 s in main).
- **In k-induction's place** (`e1-rep`), level (7 gained, 7 lost): it loses metros_1 ×6, which k-induction answers
  at 26 to 33 s, and llreve's bug15.
- **Sharing k-induction's slice** (`f3`, 7 gained, 8 lost). The 22 tasks that differ or timed out, 3 runs a side
  (`f3r1`..`f3r3`): 28 answers here against 21. car_2_e7_1027_e1_1047 3 of 3 against 0 of 3, durationThm_2 3 against
  1, its e1_118 3 against 2, dillig25 2 against 0, ctigar bound 3 against 1, ex1 3 against 2, nested5 1 against 0;
  lost, metros_1_e2_1102_e7_1163, _e7_1255_e7_12 and _e7_606 2, 2 and 1 against 3 of 3 (k-induction's half slice puts
  its answers at 46 to 54 s, from 27 to 31 s), bmc-1-test 2 against 3. HOLA/39, array_fill1_abstracted and dillig17,
  differing in the first runs, 0 of 3 on both sides.
- **The shapes**, dropped: level on the dev tasks, five fewer on the track.

**The structure.** One object serves every search here: the kernel's k-step goal and its tree. The bounded runs ask
it from the start for a model; k-induction with the law before each step; IMC with R at the start, colored at its
first cut; the sequence interpolants color the same tree at every cut; TPA asks the two-step goal over its relations.
One primitive (`fromTree`, any coloring of any kernel tree) is all four's interpolation. Measured as replacements: IMC
reproduces 107 of k-induction's 120 and 83 of 100 of the bounded runs' answers alone, but in k-induction's place on
the second CPU it is level (it misses the late metros_1), and beside the bounded runs it costs their deep turns. What
stops it is the price of a tree (the cost above), and interpolants that split by cases, so R and the relations grow a
case at a time. Two things would move it, neither measured here: an interpolant read from CDCL's resolution DAG
(kernel/cdcl.ts keeps it internally) instead of the unfolded tree, and the clauses composed along the CHC's chains
before the rule is built (HOLA's chains to its loops), which needs the sat answer read back on the original
predicates for the kernel.

## The gap at 0.27.0; a warm CDCL session and PDR, kept on gen/chc5-pdr (gen/chc5)

Every run named here is in the main checkout's `runs/chc5/` (60 s, Modal, 2 vCPU). Counts of the whole track leave out
the 2 disputed labels, which both sides answer in every batch. Nothing trusted changed.
- **Merged (gen/chc5):** `prof/gap27.py` and an equality's two halves chosen together for cell forms (core/infer.ts).
  The CHC path is main's.
- **Kept unmerged, a measured result (branch gen/chc5-pdr, e4f5e0a):** the warm session and PDR described below. On
  the whole track they cost about as many tasks as they gained, so they are not on main. The branch has them opt-in
  (`GDP_JOIN_PDR`, `kind.ts --pdr-ms`).

**The gap at 0.27.0** (`prof/gap27.py`, on `runs/query/m5/chc-mine` and its reruns, with Spacer and Golem from
`runs/modal/chc2/combined-v020`):
- **Size:** 251 tasks (217 sat, 34 unsat). 10 of them are answered in some other run of 0.27.0.
- **Sat, by group:** D 87, E 39, F 24, C 16, the rest 15, G 4, B 4, A 2. 26 tasks were answered at 0.20.0.
- **Sat, by family:** ctigar 41, HOLA 40, Lustre's DRAGON 29 and FIREFLY_luke 11, the rest at most 8 each.
- **Sat, by cause:** the join ran out of time on 166, had no target on 43, was stuck on 4, and was inductive while the
  kernel's search after it failed on 3.
- **Sat, given Spacer's invariant:** the kernel proves 140 of them and fails 50; 27 have no Spacer model.
- **Unsat:** 34 tasks. Lustre's metros 22 and car 6, then O3_id 3, swimmingpool 1, reve 1 and rust-horn 1. The bounded
  runs refuted depths 8 to 12, where Golem's derivations take 12 to 24 steps (O3_id: 103 to 1,003).

**Where the join's time goes** (`prof1`: bun CPU profiles and every root query of 8 join-time tasks):
- **The cube queries:** on car_2_e7_1027_e1_1047, 29.0 s of 47.7 s of query time went to `a cube` models. On
  durationThm_1 they took 28.6 s.
- **The walks' request queries:** 14.2 s of 46.1 s on DRAGON_4_e1_4312, 7.8 s on car_2.
- **The reader:** in the CPU profile, the reader reading the goal at each node (`sync`, `factsOf`, `truth`) led.

**The warm session** (gen/chc5-pdr: core/infer.ts, kernel/cdcl.ts, kernel/reader.ts). One `cdclSession` holds the step once. Each
law before the step, each goal after it, and each cube literal after it is a hypothesis behind a selector of its own,
written as `1 <= sel@j` (twice) or the hypothesis. A query assumes the selectors of what it reads on and the rest off.
- **The assumptions:** `run` takes a list of them, each decided at a level of its own. A refutation names the
  assumptions it rests on (`assumed`, MiniSat's analyzeFinal).
- **Levels kept:** the levels whose decisions start the next query's list stay from one query to the next.
- **Unread:** an off selector's hypothesis isn't read past its guard (reader.ts, a guard written twice first).
- **No rows:** the selectors' atoms bring no row to the simplex (`quiet`).
- **Stamps:** a trail position's stamp is its content, so decisions made again in the same order find their values
  kept.

How it measured:
- **Fewer nodes:** on car_2, 28 nodes a query against 235 (`prof2`).
- **Slower nodes:** each cost about 6 times as much at first, and the median query took about the same time after the
  fixes (`prof3`: 76.8 against 99.5 ms on car_2, 119.0 against 51.6 on nest-if3).
- **On the join, it loses tasks:** on 318 dev tasks it was level with the cold join (`a1`, `a2`: 105 and 107 against
  107 and 107). On the 12 tasks it lost in a full run (`lost2`, `d1`), it answered 5 against the cold join's 9 and 10
  and main's 8 and 9. SYNAPSE_6, which main's join proves in about 1 s, was lost every time.

So the join stays cold, and the session serves PDR alone (`GDP_JOIN_WARM=pdr`, the default; `1` for both, `0` for
neither). `GDP_CDCL_VERIFY=1` compares its rows with kernel.ts's, less the selectors' atoms. On the 332 step goals the
searches are the same as main's in all 332 (`h-g332`: 270,048 against 271,766 ms).

**PDR** (gen/chc5-pdr: core/infer.ts's `pdr`, on the join's cube machinery: `cubeOf`, `queryWith`, a `generalize` that blockCube now
shares, `down` and `apart`):
- **Frames:** F_0 is the start, a law of its own. F_i holds the lemmas blocked at level i or above.
- **Obligations:** the lowest level is blocked first. A cube is blocked relative to F_{i-1} and its own negation, then
  generalized and pushed up while it stays blocked.
- **A predecessor the runs reached:** it becomes a sample, and `apart` makes the cube leave it out.
- **Pushing:** each lemma moves up where F_i keeps it after the step. A frame left empty is the invariant, and the
  kernel then proves it.
- **Sessions:** PDR has a session of its own, and its samples are its own.

On the dev tasks (`dev5`, 318: the 217 sat-gap tasks, 100 the join solves and the losses):

| PDR run | sat | the join alone, same batch |
| --- | --- | --- |
| first, half the join's time (a2, a3, a4, a5, a6, a7, a8) | 113, 116, 110, 113 and 110, 114, 112 and 113, 116 and 115, 115, 114 and 114 | 107, 106, 109, 112, 108 to 111, 108 and 110, 106 and 107 |
| first on a cold session (a3) | 110 | 106 |
| after the join (a4) | 111 | 109 |
| between two halves of the join (a4) | 106 to 109 | 109 |
| in turns with the join (a5, a6, a7) | 112 to 115 | 108 to 112 |

- **Its own tasks:** PDR solves seven that the join never did, in 3 of 3 or 5 of 5 runs: array_fill1_abstracted,
  barthe2-big2_merged, 35.c, bind_expands_vars2, szymanski, car_2_e8_491_e7_826 and car_2_e7_1027_e1_1047 (1.1 to
  16.3 s).
- **On the whole track it loses as much:**
  - First (`f1`, beside 548c343): 1,033 against 1,042. The join's quick tasks lost their time (SYNAPSE_6, ctigar's
    up2, up3 and bound).
  - On the second CPU, 16 s after the first turns (`f3`): 1,027 and 1,030 against 1,037. The deep bounded runs lost
    their turns (car_5, DRAGON_14, metros).
  - In k-induction's 16 s turn (`f4`): 1,040 against 1,039. It loses metros_1's late k-induction answers, 6 of them.
  - After the join with 0.9 of what is left (`f5`, `r9`): the kernel's search below loses loop__fib ×2 and s_split_19,
    0 of 3 runs against 3 of 3. That search answers more than the 4 of 478 counted above: loop__fib and durationThm_2
    there at 53 to 56 s.

**Measured and left out:**
- A walk's request with inputs fixed only while that pays.
- A chosen candidate dropped after four stuck goals.
- An equality's two halves chosen together on scalar forms.

On the 9 tasks they touched (`r7`, `r8`, 3 runs each), with PDR off: all three off answered 8, 7 and 8. The request gate
alone answered 5, 6 and 6, the drop alone 3, 5 and 3, and the halves alone 6, 7 and 7.

**Kept:** an equality's two halves are chosen together for cell forms (`every k: Σ ≤ d` beside `−Σ ≤ −d`). It proves
the real-world corpus's TimelockController law 0 and blnk law 5. CHC has no cell forms.

**gen/chc5 as merged, beside main 1a66834** (`k-*`, launched together):
- **CHC-COMP:** 1,039 (612 sat, 427 unsat) against 1,040 (614, 426). None wrong, and the same 2 disputed labels on
  both.
- **The CHC path is main's:** the halves rule reads only cell forms, and CHC has none.
- **Reruns:** the 16 tasks that differ or timed out, run 3 times a side (`kr1`..`kr3`), answer 21 times on each side
  and time out 5 times on each.
- **The real-world corpus:** law by law below, in the CHANGELOG.

**gen/chc5-pdr on the track, PDR off, beside main 1a66834** (`h-chc-*`):
- **This run:** 1,039 (615 sat, 424 unsat) against 1,044 (617, 427). None wrong, and the same 2 disputed labels on both.
- **The 11 tasks that differ, run 3 times a side** (`hr1`..`hr3`): 23 answers here against 14 on main. ex1 3 against 1,
  s_split_22 2 against 0, car_2_e7_1027_e7_359 2 against 0. No task is lost every time.
- **Beside f589873** (`g-chc`): 1,042 against 1,042, and the 10 that differ answer 20 of 30 against 19.
- **Unchanged ahead:** Spacer 1,163 and Golem 1,154 lead.

**Unsat** (`bmc1`, profiles of kind.ts on 3 metros, 2 car_5 and swimmingpool_9):
- **Depths:** the bounded runs reach 9 to 12, where Golem needs 12 to 24, and each depth costs 2 to 3 times the one
  before.
- **The time:** k-induction takes 30.2 of the second CPU's 55 s, and the reader's per-node reading leads the bounded
  runs' own time.
- **Neither closes it:** neither half of the CPU, nor a constant factor, reaches 4 or more depths further. Acceleration
  in the unrolling (gen/nonterm5's accel.ts) was not tried.

**The three named losses:**
- **car_2_e7_1027_e1_1047:** PDR answers it in 2 to 3 s, every time.
- **SYNAPSE_4 and gulwani_cegar2:** they stay as they were.
- **The join's path:** it depends on more than CDCL's model order. The wall-time runs and guided stages give it other
  samples (SYNAPSE_6: 386 against 476), and the hull follows them.

## The rule's own comparisons in the join's cubes (after 0.26.0)

**Where the gap was.** At 0.26.0 the join (core/infer.ts) blocks a counterexample's cube only where no candidate
rules it out, its predecessors 3 deep, and the cube is the counterexample's control values and the samples' bounds.
Where no sample is at the control state (a location the runs never reached: on HOLA/04, the assertion's location
after its loop and the locations before it), that cube is the control values alone: its predecessors take it back
toward the samples, one location at a time, and past 3 deep the join ends (`none: reached`). Given 300 s instead of 60
(`runs/inv2/l300-base`), the join solves 21 of the 154 sat-gap tasks whose Spacer invariant the kernel proves
(`research/inv/gap.json`); of the other 133, 25 end by the join's time and the rest by its shape: `target` (no
candidate and no cube, 43), the cube window (32), an undecided query (15), no join (18).

**What changed.** Nothing trusted (`kernel/`, `core/check.ts`, `lean-kernel/` as at 0.26.0).
- **A cube's literals at a counterexample read the rule's own comparisons** (`comparisons`, each now kept with its
  bound: Σ t·v ≤ d as the rule writes it, and its negation), those true there, beside its control values and the
  samples' bounds. A cube where no sample is then reads the guards that led to its location, as a predecessor
  Spacer projects from the step would, and the refutation's core and `down` cut it from there.
- **Predecessors blocked 8 deep** (3), and **the cube first** where no sample holds the counterexample's control
  state (the samples say nothing there, so no candidate fitted to them will); elsewhere after the candidates, as
  before. The window that gave the join 0.3 of its time once a cube was in goes.
- **The join has 0.8 of the search here** (solve.ts passes `InferOptions.join`; 0.6, the default, elsewhere): after
  a join that ran out of time the search below answered 4 of the 478 sat answers of `runs/chc3/final-mine`.
- **A cube blocked twice in one chain** no longer ends the join (its law was declared twice: rust-horn's
  simple-4-06, `runs/inv2/c2-a8`).

**The track** (60 s, Modal, `runs/inv2/chc3-mine` at b9ec9f6 beside `runs/inv2/chc3-base`, main e883e53, launched
together):

| gdp-wired | sat | unsat | wrong | disputed | solved of 1,406 | out of time | median s, sat both answer |
| --- | --- | --- | --- | --- | --- | --- | --- |
| main e883e53 (`chc3-base`) | 592 | 409 | 0 | 2 | 1,001 | 4 | 18.03 |
| this (`chc3-mine`) | 613 | 410 | 0 | 2 | 1,023 | 5 | 18.17 |

The batch before it (`chc2-mine` at 54dcd4d, the same CHC path, beside `chc2-base`): 1,026 (617 sat, 409 unsat)
against 1,001 (592, 409). No answer contradicts Spacer's or Golem's (`runs/modal/chc2/combined-v020`); the two
disputed labels are answered as before.
- **Gained 27** (each solved in both batches here unless noted, and how often main solved it in its five runs,
  `f1-base`, `f2-base`, `chc-base`, `chc2-base`, `chc3-base`): s_split_17, 37 and 38 (0 of 5), HOLA/04 (0 of 5),
  reve 013, 013b (0 of 5), 014 (1 of 5) and 015 (2 of 5), llreve break_merged and break (2 and 3 of 5), ctigar
  gulwani_cegar2 and dillig37 (0 of 5) and up4 (0 of 5, 1 of 2 here), Lustre car_2 ×3, car_all ×3, SYNAPSE_4 (0 of
  5), _6counters (2 of 5), FIREFLY_4_e3_3511_e3_422, ticket3i_all_e2_1117 and ticket3i_7_e1_2192 (4 of 5),
  durationThm_2_e1_118 and _e3_329_e6_128 (2 of 5, 1 of 2 here), and peterson_vt (unsat by the second CPU's bounded
  runs at 53.8 s; 4 of 5).
- **Lost 5.** PRODUCER_CONSUMER_2 (main 5 of 5 at 17.9 to 20.1 s, here 0 of 2): its counterexamples are at control
  states no sample holds, so each is blocked first, a cube a round for 24 rounds, the last taking 21 s, and the join
  ends by its time; main tried the candidates first, blocked one cube at round 12 and was inductive at round 17.
  s_split_42 (main 4 of 5) and llreve loop__fib_000_002 (main 5 of 5, 31.6 to 42.8 s): a cube blocked 8 deep counts
  a bound up one value at a time (s_split_42's one blocking took most of the join's 35 s: `never 251 <= i0 and i2 <=
  253`, `252`, ...) where main's 3 deep failed at once and the search below found the invariant; each 1 of 2 here,
  past 45 s. ctigar up3 (main 2 of 5) and durationThm_2 (main 3 of 5): 1 of 2 here.
- **By stage:** sat by the invariant search 480 → 503, by k-induction 112 → 110; unsat by bounded runs 316 → 317.
- **By group** (groups_chc.py's tests on the 0.20.0 gap rows, `chc2` batch): C 19 → 24 of 38, D 25 → 31 of 116, G
  10 → 12, B 36 → 38, A 190 → 192, F 17 → 18, E 32 → 32; Lustre 601 → 607 of 766, ctigar 34 → 41 of 110.
- **The gap now** (tasks Spacer or Golem solve at 60 s, `combined-v020`, and this doesn't): 263 (211 sat, 52 unsat)
  in `chc2-mine`, 281 (229, 52) for main in the same batch. Of the 154 sat-gap tasks whose Spacer invariant the
  kernel proves, 18 are solved (main 4, `chc2`).

**Each change measured** (sat on the 254 tasks of `research/inv/dev.json`: the 154 above and 100 the join solves at
0.26.0; 260 with `dev2.json`'s six earlier losses; each batch launched together, runs of the same code differing by
up to 3):

| run | what | sat |
| --- | --- | --- |
| `c2-base`, `a-base`, `d1-base` | main's search | 101, 101, 101 |
| `c-atoms3` | the rule's comparisons in cubes, 3 deep | 101 |
| `c-d8` | 8 deep alone | 101 |
| `c-atoms8`, `c2-a8` | both | 107, 103 |
| `c2-a16` | 16 deep | 105 |
| `g-a8cf`, `g-a8cfw` | the cube first; and no window | 108, 111 |
| `h-cfw`, `h-d16` | the cube first, no window; 16 deep | 111, 112 |
| `i-cfw`, `i-s8`, `i-s9`, `j-s8` | the join's share 0.6, 0.8, 0.9, 0.8 | 114, 117, 115, 116 |
| `l-cub100`, `l-cand100`, `l-hyb100` (260) | the cube first always, the candidates first always, by the control state | 120, 118, 124 |

Full runs, each beside main in its batch: `f1-a8` (comparisons, 8 deep) 1,009 against 998; `f2-cfw` (cube first, no
window) 1,015 and `f2-s8` (and 0.8) 1,021 against 1,000; `chc-mine` (fd136bc, the cube first always) 1,024 against
1,003.

**Measured and left out.**
- **PDR frames over the join's cube machinery** (frames F₁..F_N of blocked cubes, obligations as the kernel's
  predecessor points, lemmas pushed, the frames' fixpoint the answer): before the join with half or 0.9 of its time,
  93 and 80 against 101 (`d1-pdr5`, `d1-pdr9`); given the join's time from the start (guided runs off, `e-*`), 75
  against the join's 104, and 71 with cubes at the rule's constants (each direction's next constant above the point),
  Houdini-seeded control cubes and the fewest literals that leave the samples out; after a join that ran out of time,
  100 and 111 against 101 and 111 (`a-pdr`, `h-pdr`). At 300 s it converged on 6 of the 154 (`l300-pdr9`: car_2 ×3,
  car_all ×2, gulwani_cegar1), each with 43 to 66 lemmas, and reached 2 to 9 frames on the others. Its queries are
  the cost: 12 to 170 ms each locally (dillig19, FIREFLY_6), and each lemma's generalization asks up to 24 more, where
  Spacer's invariants for DRAGON_4, FIREFLY_6, dillig19 and nest-if6 have 10 to 23 clauses.
- A deadline for one counterexample's cubes (a quarter of the join's time left: 116 against 119, `k-sh25`, `k-sh100`;
  `l-hyb25` 120 against 124); the depth counted only at control states the samples hold (`m-ch8`, 122 of 264, HOLA/04
  lost: its chain passes sampled locations); `down`'s 12 or 48 queries (116, 115 against 116); 96 cubes (109 against
  111); 16 tries (112).

## The second CPU, and the join's control states as cubes (after 0.25.0)

**Where the gap was.** At 0.25.0 (`runs/chcsat/m2/chc`), 312 tasks are solved at 60 s by Spacer or Golem
(`runs/modal/chc2/combined-v020`) and not by gdp-wired: 250 sat, 62 unsat (232 by both, 54 by Spacer alone, 26 by Golem
alone). None was refused: 306 ended unknown at the search's deadline, 6 out of time.
- **Sat, by group** (research/frontier2's tests, on the 0.20.0 gap rows): D 95, E 40, C 26, F 26, A 10, G 7, B 6, the rest
  15, no 0.20.0 row 25. **By family:** Lustre 101, eldarica-misc/LIA 57, ctigar 52, llreve 15, aeval 10, the rest 15.
- **Given Spacer's invariant** (`prof/given.ts` on the 226 of the 250 Spacer gave one, `runs/chc3/given1`): the kernel
  proves 152, D 76 of 95; with the usual certificate (`GDP_CERT=usual`, as `inferLaws` proves, `runs/chc3/given2-usual`)
  176, median 6.5 s on Lustre's D tasks (24.6 s with the cyclic one). So most of the sat gap is the search, not the proof.
- **Unsat, all 62 Lustre but 6:** metros 24, car 12, swimmingpool 9, DRAGON 6, FIREFLY 4, peterson 1; O3_id 3, 025c and
  025d, bmc-1-test. Golem's derivations (clause steps, as gap.py counts them): car 12 or 13, metros 9 to 24 (15 with none
  in 60 s), swimmingpool 5 to 13, DRAGON, FIREFLY and peterson 4 or 5, O3_id 103 to 1,003 (from a start the run must
  guess), 025c and 025d 8, bmc-1-test 13. The stage alone at 56 s (`runs/bmc2/only-inc3`) solved 20 of the 62: what is
  missing is time, and on metros each depth costs about four times the one before.

**What changed.** Nothing trusted (`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts`, `lean-kernel/` as at 0.25.0).
- **The second CPU shared** (`kind.ts`): k-induction ran there alone until the deadline, but answered by 30.9 s on every
  task of `m2/chc` (95% by 23.6 s), and an unsat task's step goals have models at every k. Now k-induction and the bounded runs
  take turns there, in slices of 2 s each, then 4, 8, 16, ... (neither knows whether the task is sat or unsat); the
  bounded runs are core/bmc.ts's `boundedSearch`, `findBoundedRun` made resumable (its forced run and its CDCL session
  go on where the last slice stopped; the forced run has 4.5 s in all, its share of the old 15 s stage). solve.ts's own
  15 s stage goes, so the invariant search starts after the guided runs, at about 13 s, not after that stage's 15 s.
  Each step's goal is also tidied first (`tidier`): a comparison whose sides differ by a constant folded, and a yes/no
  copied through an if (`b~1 = if y = 1 then 1 else 0`) read as the copy, so `reduce` puts it in.
- **The control states no state reached as prime cubes** (core/infer.ts's `primes`): the join's control state is the
  choice and up to 7 yes/nos (a program counter in bits); each unreached one was a form of its own reading every bit, and a
  goal's proof read some twenty of them, each then a goal of the cone (ctigar's `dillig25`: 24 forms read by a goal, the
  join out of time). Each unreached cube now drops its values while it holds at no reached control state, and cubes
  another includes go: together they say the same (the control state is one reached), and a goal reads six or fewer.
- **A blocked cube generalized** (`down`, IC3's literal dropping): the core of a cube's refutation reads most of its
  literals where the step's terms are a chain of ifs; its literals are now dropped a part at a time (halves, then
  quarters, ..., then one by one), kept out where the cube without them still leaves the start and the samples out and
  is still blocked relative to the same laws, within 24 queries. FIREFLY's cubes went from every control value (20 or so
  literals) to three or four.
- **The final proof grows each goal once** (kernel/prove.ts's `withTrees`): `inferLaws` proves each law of the set alone
  (`proveLaw`) and then the set as a whole (`proveRule`), the same goals twice; within `withTrees` a root goal's tree is
  kept by its hypotheses and given again (the kernel checks it wherever it goes). `dillig25`'s final proof 17.2 s to 10.8 s,
  locally. Off elsewhere; `GDP_TREES=0` turns it off.

**The track** (60 s, Modal, `runs/chc3/final-mine` at fba8136 beside `runs/chc3/final-base`, main f990361, launched
together):

| gdp-wired | sat | unsat | wrong | disputed | solved of 1,406 | out of time | median s, sat / unsat |
| --- | --- | --- | --- | --- | --- | --- | --- |
| main f990361 (`final-base`) | 564 | 397 | 0 | 2 | 961 | 8 | 28.905 / 13.58 |
| this (`final-mine`) | 588 | 408 | 0 | 2 | 996 | 5 | 18.075 / 2.58 |

- **Gained 41:** sat 30 (ctigar 12, Lustre 9, eldarica-misc 7, aeval 1, rust-horn 1), unsat 11 (Lustre 10: swimmingpool 5,
  FIREFLY 3, DRAGON_4, peterson_vt; reve 025d). **Lost 6**, all sat by the invariant search in main: s_split_08
  (24.84 s; its candidates differ with the runs' samples: solved in `t4-mine`, not in `y-ctl`), s_split_42 (35.98 s;
  unknown in main's `chc-base3` too), reve 014 (52.49 s), xy0 (36.30 s), durationThm_2_e1_118 (47.49 s) and
  durationThm_2_e3_329_e6_128 (50.95 s; both gained in `t2-mine`). No unsat answer lost.
- **By stage:** sat by the invariant search 431 → 478, by k-induction 133 → 110 (none of main's lost: the search answers
  first); unsat by bounded runs 253 → 315, guided runs 57 → 9 (the bounded runs, from the start, answer first), random
  runs 50 → 47, `prove` 37 → 37.
- **By group** (groups_chc.py's tests on every task with a 0.20.0 gap row, so larger totals than the corpus's): C 10 → 19 of 38, D 21 → 23 of 116, F 13 → 17, A 184 → 191, H 216 → 226 of 273, I 25 → 26;
  ctigar 20 → 31, Lustre 584 → 601.
- No answer contradicts Spacer's or Golem's (`runs/modal/chc2/combined-v020`); the two disputed labels are answered as
  before, by the derivations of 999,002 and 280,277 steps.
- **The gap now** (`runs/chc3/gap-final.json`): 282 (231 sat, 51 unsat), from 318 for main in the same batch. Sat: D 93,
  E 40, F 25, C 19; given Spacer's invariant the kernel proves 154 of the 231 (the usual certificate); the join ends by
  its time on 126 (Lustre's DRAGON: 7 to 16 rounds, a goal's proof 0.4 to 5 s on the wide step), and finds neither a
  candidate nor a cube on 64 (most often `none: reached`: a counterexample's predecessors deeper than the cubes' 3, as
  HOLA/04's; 8 deep, its cubes block `i3 <= k` one value at a time). Unsat: metros 24, car 12 (the bounded runs reach
  depth 9 to 11 of the 12 or 13), DRAGON 5, swimmingpool 4, O3_id 3, FIREFLY_a3 2, bmc-1-test 1.

**Each change measured** (sat, unsat; each batch of runs launched together):

| run | what | sat | unsat |
| --- | --- | --- | --- |
| `t1-base` | main f990361 (launched about 2.5 min after `t1-mine`) | 566 | 394 |
| `t1-mine` | the second CPU shared, goals tidied | 576 | 408 |
| `t2-mine` | and cubes generalized (`down`) | 574 | 408 |
| `t3-mine`, `t3-nodown` (one batch) | and prime control cubes; without `down` | 589, 584 | 409, 406 |
| `t4-mine` | and the final proof's trees kept | 594 | 407 |

Runs of the same code differ by a few: `t4-mine`, `x-ctl` and `y-ctl` (the same commit) 594, 593 and 592 sat, 407 each.

**Measured and left out:** the join's share of the search 0.75 (0.6; `x-share75` 596 sat beside `x-ctl` 593) and the
cubes' window 0.5 (0.3; `x-window5` 590); the guided runs 4 s (8 s; `y-g4` 597 beside `y-ctl` 592, unsat 407 each) and
random runs 3 s with them (`y-r3g4` 594, 405): within the spread. k-induction stopped past k = 8 (`t5-mine`, 594, 407,
as `t4-mine`). Cube blocking 8 or 16 deep (3): HOLA/04's cubes then count `i3 <= k` up one value at a time, locally.
Bound propagation through rows in the model-only search (a row's variable of coefficient ±1 bounded by the others'):
car_5's nodes at depth 8 864 against 868, locally. The linear forms built without `delete` (core/solver.ts) and the
search's variables without (kernel/cdcl.ts): on 40 bounded-run searches (`runs/chc3/ab-both`), 39 did the same work,
in 374.5 s against 397.9 s (median ratio 0.95 over the 36 past 0.5 s): left out. Acceleration (core/accel.ts's `stemsTo`) for O3_id's guessed
starts: core/relation.ts gives no relation for the CHC rule (its free yes/nos' cases, 14.3 s locally to refuse).

## Disjunctions in the join (after 0.24.0)

The invariant search's join (core/infer.ts) asks its goals first of kernel/cdcl.ts for a model alone, the forms a
refutation read being its core (the hypotheses its leaves read, cdcl.ts's `core` option); where no candidate rules out a
counterexample to the law, it blocks the counterexample's cube as IC3 does (the control state and the bounds that keep
the samples out, relative to the set, cut to the literals the refutation's core read, predecessors blocked first), each
cube a disjunction in the set; the control states no run reached are one law until it is first broken; solve.ts answers
as soon as the set is proven (`minimize: false`). Nothing trusted changed. The budget split is main's (runs 5 s, guided
8 s, bounded 15 s with k-induction beside).

| gdp-wired, 60 s, Modal | sat | unsat | wrong | disputed | solved of 1,406 | out of time |
| --- | --- | --- | --- | --- | --- | --- |
| main 54bbec9 (`runs/chcsat/m2/chc-main`) | 537 | 398 | 0 | 2 | 935 | 10 |
| this, merged with it (`runs/chcsat/m2/chc`), launched beside it | 569 | 397 | 0 | 2 | 966 | 7 |

- By group (research/frontier2's): A 168 → 185 of 195, B 33 → 33 of 39, C 8 → 12 of 38, D 15 → 18 of 113, E 28 → 31
  of 71, F 7 → 9 of 34, G 8 → 8 of 15, H and I 242 → 241 of 303, the rest 426 → 429 of 598. By family: Lustre 307 →
  329, ctigar 13 → 22. Sat by the invariant search 403 → 436, by k-induction 134 → 133.
- 37 sat more, 5 fewer, 1 unsat fewer (main's bounded runs at 28 s, not found here); the losses in the CHANGELOG.
- Runs of the same code vary: the merged branch at 0.24.0's other settings 567, 571 and 575 sat
  (`runs/chcsat/m1/chc-k2a`, `chc`, `chc-k2b`, the control states' law split at its second break), 566 and 570 at the
  first (`chc-k1a`, `chc-k1b`); before the merge, beside 6b2e2df, 816 solved (551 sat, 265 unsat) against 782 (517, 265)
  (`runs/chcsat/final4`).
- Measured and left out: IC3 with frames after the join (547 against 552 without, `runs/chcsat/full1`,
  `full1-noframes`), runs from the kernel's models for Lustre's few samples (no gain on 80 Lustre tasks,
  `runs/chcsat/l1*`, `l2*`, `l3*`), and the CHANGELOG's other variants.

## Bounded runs (after 0.22.0)

An unsat answer is a run that `checkDerivation` confirms against the CHC, step by step; until now the runs came from
random requests and the guided runs (each step a model of one clause), which rarely reach a failure that needs several
steps' requests chosen together. `solve.ts`'s `bmc` stage (after the guided runs, 10 s) asks for them together:
core/bmc.ts builds the kernel's own k-step goal (kernel.ts's `stepLawObligations`, `steps: k`) from the start state to
a state at error, puts its constants in (core/nonterm.ts's folding), and asks kernel/cdcl.ts for a model alone (no
refutation unfolded into a tree; each decision's phase the incremental simplex's point's), k = 1, 2, ... The model is
a run: the compiled rule takes it, and `checkDerivation` confirms it or the stage goes on. Nothing trusted changed.

**The track** (`runs/unsat/chc`, 60 s, beside `runs/unsat/chc-base`, main 5c3f947 launched at the same time, both on
Modal):

| gdp-wired | sat | unsat | wrong | solved of 1,406 | out of time |
| --- | --- | --- | --- | --- | --- |
| 5c3f947 (`chc-base`) | 528 | 144 | 0 | 672 | 3 |
| bounded runs (`chc`) | 518 | 264 | 0 | 782 | 9 |

- Unsat: 120 more, none fewer; 120 of the 264 by the `bmc` stage. Every one is a derivation `checkDerivation`
  confirmed, and none contradicts Spacer's or Golem's verdict (`runs/modal/chc2/combined-v020`).
- Sat: 4 more, 14 fewer. Four runs of main the same day gave 528, 530, 532 and 533 (`runs/unsat/base1` to `base4`):
  the 10 s the stage takes come from the invariant search, which loses the tasks it proved last.
- Lustre's 321 unsat tasks: 38 to 147. The round-2 corpus's groups (`research/frontier2`, from 0.21.0): H (unsat
  Lustre, 273) 1 to 108; I (unsat, the others, 30) 1 to 12. Of H's 273 by Golem's derivation length, solved: 2 steps 4
  of 4, 3 steps 89 of 126, 4 steps 15 of 78, 5 or more 0 of 50 (15 have no Golem derivation).
- Out of time, 9 (main 3): each in the invariant search, which starts 10 s later; main answered unknown on 7 of the 9
  and ran out of time on 2.

**The stage alone** (`--runs-ms 0 --guide-ms 0 --no-houdini`, the stage until 56 s; the 475 unsat tasks):

| the CDCL search asked for a model | unsat | Lustre (321) | the others (154) |
| --- | --- | --- | --- |
| phases as stored (`runs/unsat/bmc-only-off`) | 280 | 180 | 100 |
| each decision's phase at the simplex's point (`bmc-only-phase`, kept) | 320 | 218 | 102 |
| every open atom decided at once at the point (`bmc-only-batch`) | 271 | 169 | 102 |
| kept, runs of at most k steps (the machine stopped at error; k = 1, 2, 3, 4, 6, 8, 12, ...; `bmc-only-upto1`) | 322 | 218 | 104 |

The kept stage found 139 within 2 s, 212 within 10 s, 245 within 20 s, 284 within 56 s (`bmc-only-upto0`). Of the
ones runs or guided runs find, it misses the long loops (s_split's 102 to 1,253 steps; past depth 64, the kernel's
bound on k). The at-most-k depths gave 2 more and were left out: no fewer depths' time to save.

**Its budget**, each against main launched with it (sat, unsat):

| run | stages before the invariant search | sat | unsat | main's sat, unsat |
| --- | --- | --- | --- | --- |
| `chc-c5000` | runs 5 s, guided 8 s, bounded 5 s | 524 | 248 | 532, 144 (`base3`) |
| `chc-c8000` | runs 5, guided 8, bounded 8 | 518 | 263 | 532, 144 |
| `chc-c10000` | runs 5, guided 8, bounded 10 | 521 | 265 | 532, 144 |
| `chc-b15000` | runs 5, guided 8, bounded 15 | 508 | 292 | 528, 144 (`base2`) |
| `chc-b20000` | runs 5, guided 8, bounded 20 | 497 | 303 | 528, 144 |
| `chc-b25000` | runs 5, guided 8, bounded 25 | 471 | 307 | 528, 144 |
| `chc-d1` | runs 3, guided 3, bounded 10 | 521 | 262 | 533, 144 (`base4`) |
| `chc-d2` | runs 5, no guided runs, bounded 10 | 520 | 250 | 533, 144 |
| `chc-d3` | runs 2, guided 2, bounded 12 | 517 | 276 | 533, 144 |

Shorter random and guided runs didn't give the sat side its time back (`d1`, `d2`, `d3`: 517 to 521 sat against
main's 533) and lost unsat tasks the guided runs find (`d1`, `d3`: 3; `d2`: 15). 10 s is the default: from 15 s to 20 s
(`b15000`, `b20000`, beside the same main), 11 more unsat and 11 fewer sat. A second process for the stage on the container's other vCPU
(`runs/unsat/chc-p1`) was dropped: 539 of the 1,406 containers failed (Modal's `RemoteError`) and the first process's
stages ran past their deadlines.

**k-induction** (`prof/kind.ts`, `runs/unsat/kind1`, the 403 sat tasks main leaves unsolved, 55 s): 17 are
k-inductive (13 Lustre; k = 3: 5, 4: 9, 9, 10, 11: one each). The kernel's proofs are 1-inductive, so a k-inductive
law isn't a checked answer without a new trusted rule; not kept.

## Bounded runs, faster and longer (after 0.23.0)

The bounded runs' stage (core/bmc.ts) now asks smaller goals, keeps one search from depth to depth, runs a
deterministic loop forward, and has 15 s; kernel/reader.ts keeps the values whose reads didn't change. Every unsat
answer is still a run the compiled rule takes and `checkDerivation` confirms against the CHC, step by step.

- **Relaxed goals** (`relax`): a CHC integer is a pair of naturals normalized where it is written (n = a ∸ b,
  n$neg = b ∸ a: a case per pair and step); every read of a pair is of its difference, so the pair written as any two
  naturals of difference a − b (n + b = a + n$neg) is the same integer to every read. The relaxed goal has every model
  of the goal; the interpreter normalizes, and where it refuses the run the goal itself is asked.
- **Reduced goals** (`reduce`, `putBack`): a name another name or a constant gives put in; a definition nothing else
  reads dropped, and the model's value for it put back from its term; for the growing goal, the cone of influence of
  the laws and the assumption through the updates.
- **One search across depths** (kernel/cdcl.ts `cdclSession`): the steps written once in names that stay (n~j,
  input@j), each depth's query `act@k >= 1 or <the law broken at ~k>`, assumed by act@k <= 0 and set aside at the next
  depth, so the learned clauses, activities, phases and the simplex's tableau carry over. For machines whose goals read
  no function and no flag; the others are asked depth by depth as before.
- **Forced runs** (`forcedRun`): from the start, the one way on the rule allows (cases chosen among a finite input's
  values, every other request value 0, at most two steps that read one), by the compiled rule with its assumption as
  a value, until a law breaks, for up to 30% of the stage and a million steps: CHC-COMP's deterministic s_split loops
  (10,002 steps; past 64, the kernel's bound on k, their k-step goals fold to false).
- **reader.ts**: a value with an open read was found again at every node; now each value notes what it read, and a
  change of the trail at an atom marks its readers to be found again (all the way up). research/dag's 332 step goals:
  the same trees (outcome, leaves, splits, conflicts, decisions) by `growCdcl` and by `grow`, as at 0.23.0
  (`runs/unsat/goals332-*`), in half the search time (608.4 s to 303.9 s over the 332 by growCdcl, 638.7 s to 360.9 s
  by grow, `runs/bmc2/eq332-1`, `eq3`); 734 bounded-run goals searched alike with and without it (`runs/bmc2/eq2`).
- **The counted clock's rate** measured again: 252 units a ms at the median (`runs/bmc2/only-mine3`), was 168 at main
  (`only-base1`); bmcRate 200 to 250.

**The stage alone** (`--runs-ms 0 --guide-ms 0 --no-houdini --bmc-ms 56000`, the 475 unsat tasks):

| run | unsat | found within 10 s | Lustre (321) | the others (154) |
| --- | --- | --- | --- | --- |
| main 6b2e2df (`runs/bmc2/only-base1`) | 312 | 244 | 210 | 102 |
| relaxed and reduced goals (`only-mine1`) | 365 | 313 | 254 | 111 |
| with forced runs and reader.ts's clean values (`only-mine2`) | 391 | 352 | 255 | 136 |
| without one search across depths (`only-noinc1`, GDP_BMC_INC=0) | 397 | 358 | 260 | 137 |
| one search across depths, its cone of influence (`only-inc3`) | 407 | 365 | 268 | 139 |

**The track** (60 s, Modal, each batch launched at one time beside main 6b2e2df; sat, unsat, solved):

| batch | main | 6 s | 10 s | 15 s | 20 s |
| --- | --- | --- | --- | --- | --- |
| at 012a145, depth by depth (`chc-base2`, `chc-mine2*`) | 520, 265, 785 | 528, 351, 879 | 524, 378, 902 | 518, 392, 910 | |
| at 6b3a15b, one search (`chc-base3`, `chc-mine3*`) | 521, 264, 785 | | 522, 382, 904 | 518, 396, 914 | 516, 401, 917 |
| at f5593ac, its cone of influence (`chc-base4`, `chc-mine4*`) | 517, 266, 783 | | 525, 384, 909 | 526, 397, 923 | 519, 404, 923 |

15 s solved more than 10 s in each of the three batches (8, 10 and 14 more), and as many as 20 s or within 3; it is
the default. At 15 s (`chc-mine4-b15` beside `chc-base4`): unsat 131 more, none fewer; sat 17 more, 8 fewer (4 solved past
58 s in main; 4 where the invariant search, starting 5 s later, didn't finish, between 24.2 s and 49.0 s in main:
`s_split_42_000_000`, the 24.2 s one, is unknown in main's `chc-base3` too). No unsat answer contradicts Spacer's or Golem's verdict
(`runs/modal/chc2/combined-v020`); 20 are tasks neither answered at 60 s, all aeval-unsafe's s_split but one
(`metros_4_e2_968_e6_236`). Out of time 5 (main 8).

- **Disputed labels** (compare/chc/disputed.json; `summary.ts` lists them as `disputed`, neither right nor wrong):

  | task | label | its source | our answer | derivation |
  | --- | --- | --- | --- | --- |
  | `aeval-unsafe/s_split_50_000_001` | sat | the majority vote, LoAT's alone | unsat | 999,002 steps |
  | `aeval-unsafe/s_split_22_000_001` | sat | a placeholder (auto-added), no vote | unsat | 280,277 steps |

  Each derivation is confirmed by `checkDerivation` (each clause evaluated on the values, no gdp-wired code) and by
  research/bmc2/disputed.py, which replays the derivation file on the clauses written out by hand and checks the query
  at its end (s_split_50: D counts modulo 2,000, B grows while D < 1,000 and A while D >= 1,000, so after 499 periods
  B − A is 0 and 1,000 steps later, at C = 999,000, it is 1,000; s_split_22: the third argument grows by 3 every third
  step and reaches 280,275 with the first). Spacer, Golem and Eldarica each run out of time on both at 60 s
  (`runs/modal/chc2/combined-v020`). The derivations: `runs/bmc2/disputed/s_split_50_000_001.json.gz`,
  `s_split_22_000_001.json.gz` (each step's clause, request and the predicate's arguments after it; written by
  research/bmc2/derivation.ts, `runs/bmc2/disputed-run`).
- Merged with main at 5055882 (k-induction on the second vCPU): 540 sat, 398 unsat (2 disputed), 938 answered, main
  5055882 beside it 536, 265, 801; sat by k-induction 134 and 133 (`runs/bmc2/chc-merged1`, `chc-main5`).
- Lustre's 321 unsat tasks by Golem's derivation length (`chc-base4` → `chc-mine4-b15`): 2 steps 8/8 → 8/8, 3 steps
  111/148 → 148/148, 4 steps 18/81 → 78/81, 5 or more 9/59 → 19/59, no derivation 1/25 → 1/25; 147 → 254. Group H of
  the round-2 corpus (273): 108 → 215 (2: 4/4, 3: 126/126, 4: 75/78, 5 or more: 10/50).
- Left: the deep Lustre tasks (metros 34, car 14, swimmingpool 9: 7 to 24 steps, each depth past 8 a search of seconds
  to tens of seconds), DRAGON_14's 5 steps, the s_split loops of 10^8 steps or a start of free values (an acceleration
  of the loop's runs, gen/accel's for nontermination, would summarize them; a derivation replayed step by step stays
  bounded by the steps it replays), and O3_id's 103 to 1,003 steps from a start value the run must guess.

## There exists (after 0.20.0)

Laws may now say "there exists" (core/exists.ts): proven through a witness term of the state or a ghost the machine
carries, chosen from the kernel's counterexamples. Two uses here, each against 0.20.0's figures above.

**Spacer's existential invariants, given** (`prof/given.ts`, `--tools given`, 60 s a task as before). The 27 tasks whose
Spacer invariant keeps an existential from its projection couldn't be stated (`runs/modal/chc2/given-spacer3`: "a
quantifier", all 27). `given.ts` now states each ∃ over Int and Bool binders as gdp-wired's `exists` (a let-bound one
translated again at each use, so two uses are two existentials), and a remainder or a quotient by a constant as an
existential too (mod e k as e − k·q, q bound with 0 <= e − k·q <= k − 1: q is e's quotient, so the binder reads the same
wherever the term sits). In the 27 the bound variables are integers (23 tasks) or yes/no values (5: the 4 rust-horn tasks, with no integer
binder, and `O3_gcd01`); no bound integer sits in an equation with a coefficient past 1 (no `x = 2k`): Spacer's
projections, not parities.

| run | stated | proven | a goal undecided at its budget | the deadline while choosing a witness | out of time (killed) |
| --- | --- | --- | --- | --- | --- |
| `chc2/given-spacer3` (0.20.0) | 0 of 27 | 0 | | | |
| `exists/given5` (60 s) | 27 of 27 | 7 | 5 | 11 | 4 |
| `exists/given4-t300` (300 s, a diagnostic) | 27 of 27 | 12 | | | |

- Proven at 60 s: `simple-1-01_unsat` (2.42 s), `array_fill1_abstracted` (9.25 s), `bmc-3-test-bmc-3-safe` (11.32 s),
  `O3_gcd01` (23.84 s), `break_safe.c-1` (40.34 s), `bmc-1-test-bmc-1-safe` (52.37 s), HOLA `01` (55.75 s). At 300 s,
  besides those, `fib_merged` (70.55 s), `loop_merged` (79.88 s), `loop2_merged` (108.31 s), `bmc-5-test-bmc-diamond-2`
  (189.61 s), `loop3_merged` (190.83 s). The witnesses are terms of the state (what the invariant's own equations and
  bounds solve for: `x9 := x4 − x2`, the slots `i4 − i2`, in `fib_merged`'s projection) or, where none fits, ghosts. Runs at the limit move:
  `runs/modal/exists/given1` (an earlier choice order) proved 8 at 60 s, `fib_merged` and `loop3_merged` at 59.56 s and
  59.19 s, and not HOLA `01`.
- What stops the rest is the kernel's time, as in class A: a step goal over 20–150 laws left undecided at the per-goal
  budget, with the witness in place (HOLA `10`, `21`, `27`, `43`, `barthe_merged`, ...), or the 55 s spent before every
  law's witness is chosen (each choice a proof of that law's goals with every other law assumed, then the whole set;
  HOLA's 26–50 predicates bring up to 152 laws). `qrsolv` and `rsolv` (788 and 878 laws) run out of time.
- The remainders and quotients (17 tasks whose Spacer invariant reads `mod` or `div`, and `array_fill1_even_odd`, which
  reads both a quantifier and `mod`): stated, every one; proven, `const_mod_1`, `const_mod_2`, `const_mod_3`. The arithmetic track's `mod` and
  `div` in the kernel state the same without a binder.

**The track, `--tools gdp`** (`runs/modal/exists/chc-gdp2`, 60 s; Spacer, Golem and Eldarica from `runs/modal/chc/full1`,
together in `runs/modal/exists/chc-combined2`). The search (`inferLaws`) now also proposes congruences, ∃k. v = c·k + r
for a state value (or the sum or difference of two) whose every sample leaves one remainder by a constant of the rule's
(2, 3, 4 and the rule's own up to 64), chosen where no bound rules a counterexample out:

| gdp-wired | sat | unsat | wrong | solved of 1,406 | out of time |
| --- | --- | --- | --- | --- | --- |
| 0.20.0 (`chc2/v020-gdp`) | 224 | 144 | 0 | 368 | 5 |
| `exists/chc-gdp2` | 231 | 144 | 0 | 375 | 5 |

- 9 more, 2 fewer. More: `const_mod_1` (13.79 s), `const_mod_3` (15.53 s), `count_by_2_m_nest` (20.69 s), `dillig02_m`
  (40.57 s), `O3_EvenOdd01` (40.54 s), and four past 58 s (`reve/014`, `reve/014b`, `s_multipl_24`, `gj2007_m_3`). On 4 of the 9 (`const_mod_3`, `count_by_2_m_nest`, `dillig02_m`,
  `s_multipl_24`) the search's printed stages name an existential candidate; the solve stage doesn't print the
  invariants found, so for the other 5 the run doesn't say. Fewer: Lustre `_6counters_e8_371_e1_448` (58.16 s at 0.20.0)
  and `car_4_e7_592_e7_265` (32.28 s), each unknown at the deadline here, no existential goal among their stages.
- The 27: unknown on 26, out of time on 1 (`fib_merged`), as at 0.20.0 (unknown on 27): their invariants are
  projections, not the congruences the search proposes; what they need is the shapes of A–E (their classes outside
  the existential, in `prof/gap.py`'s table above). An earlier run of the same code but the last infer change
  (`exists/chc-gdp1`): 369 solved, none wrongly, 6 out of time.

## Division, remainders and integers (after 0.20.0)

A rule now reads `x.modBy(k)` and `x.divBy(k)` for a constant k ≥ 1, on naturals and on integers (Euclid's: 0 ≤ x mod k
< k): the rule's functions mod$k and div$k, known to the kernel by x = k·(x div k) + x mod k and x mod k < k (nothing new
is trusted; Lean proves both facts of `%` and `/` by `omega`). Two uses here:

- `translate.ts` reads a clause's `mod` and `div` by a positive constant as `Int.modBy`/`Int.divBy`, where it took a
  request value q with k·q ≤ e ≤ k·q + k − 1 before: an invariant can now read the same remainder the clause does.
- `inferLaws` proposes remainders, v mod k = r for a state value or the sum or difference of two whose runs keep one
  remainder (where only some runs do, under the guard they share: `loc is p1 → i0 mod 2 = 0`), k among the divisors the
  rule reads, then 2, 3, 4 and the rule's own constants up to 64 (six in all), a shape whose runs reached 3 values or
  more. They are chosen as the congruences are, where no bound rules a counterexample out. Where both would apply, the
  remainder is the one proposed (the congruence, ∃k. v = c·k + r, with `{remainders: false}`): it is a plain law, so the
  kernel proves it as it stands, with no witness or ghost to choose, it takes a guard (a CHC invariant is per predicate),
  and Lean states it with `%`.

**Integers: two designs measured** (`runs/modal/arith/intdesign-*`, 215 tasks: every seventh of the 1,406 and 16 of the
18 of the remainder class, 60 s each; the prototype on a branch of its own, `lang/arith-int-proto`, chosen per run by
`GDP_CHC_INT`). A CHC integer is a pair of naturals today, p − n, normalized where it is written (p ∸ n, n ∸ p).
`raw` writes the pair as computed (no truncation, so no case of the kernel's to decide which side is 0); `native` is one
variable the TypeScript kernel reads without a naturality row, with negative constants and factors (design (b): the
kernel over integers, measured before any Lean proof was written for it).

| encoding | solved of 215 | sat | unsat | wrong | out of time | the 27 sat tasks all three solve: s in all |
| --- | --- | --- | --- | --- | --- | --- |
| pairs, normalized (0.20.0's) | 46 | 28 | 18 | 0 | 0 | 613.6 |
| pairs, as computed | 46 | 28 | 18 | 0 | 2 | 581.7 |
| native integers (TypeScript kernel only) | 49 | 31 | 18 | 0 | 1 | 547.9 |

Native integers solved 4 more and 1 fewer (2 of the 4 at 51.85 s and 58.45 s), and took 10.7% less time on the 27 sat
tasks all three solve (pairs as computed: 5.2% less). The first native run, `intdesign-native`, erred on 77 tasks (the
kernel's check that a law's constants are naturals); `intdesign-native2` excepts it, and drops the cyclic encoding's
"each state value is a natural" fact for an integer, which would otherwise make the prototype unsound. The gain is that of
one column less per integer in each leaf; the cost is a trusted change to the Lean twin's semantics (every term and
valuation of Kernel.lean, Cyclic.lean, Sets.lean and the bridges is over `Nat`), and every proof checked again. Kept:
pairs, normalized, as they were (nothing trusted changes); the Lean export now states each law about an integer over
`Int` as well (`law0_int`, by `omega` from the law over the naturals).

**The track, `--tools gdp`** (`runs/modal/arith/chc-gdp`, 60 s, at this branch merged with main):

| gdp-wired | sat | unsat | wrong | solved of 1,406 | out of time |
| --- | --- | --- | --- | --- | --- |
| 0.20.0 (`chc2/v020-gdp`) | 224 | 144 | 0 | 368 | 5 |
| main, existentials (`exists/chc-gdp2`) | 231 | 144 | 0 | 375 | 5 |
| this branch (`arith/chc-gdp`) | 237 | 144 | 0 | 381 | 8 |

- Against main: 11 more (`s_split_08`, `s_split_21`, `s_split_28`, `s_mutants_22`, `loop_merged_safe`, `const_mod_2`,
  `count_by_2`, `phases_m`, `s_multipl_17` and Lustre `car_4_e7_592_e7_265`, `_6counters_e8_371_e1_448`), 5 fewer
  (`count_by_2_m_nest`, `bug15_safe`, `reve/014b`, `O3_EvenOdd01`, `gj2007_m_3`). Against 0.20.0: 14 more, 1 fewer.
  Out of time 8, 6 of them unknown on main.
- The 18 whose Spacer invariant reads a remainder (16) or a quotient (2): 7 solved (`s_split_21`, `const_mod_1`,
  `const_mod_2`, `const_mod_3`, `dillig02_m`, `phases_m`, `s_multipl_17`), 3 on main, none at 0.20.0. Not: HOLA `34`, `38`,
  `42`, `array_fill1_even_odd`, the two `digits10` (a quotient by 10), the five Lustre `DRAGON_all2` (each a remainder
  inside a disjunction over 30-odd values, beside the class-A step goal).
- Runs at the limit move. The 23 tasks where a first run of this branch and 0.20.0 differed, run again twice at 0.20.0
  and six times here as the search changed (`arith/chcdiff-*`): 0.20.0 solved 7 and 9; this branch 16 and 16 (head1-2,
  remainders chosen like any candidate), 15 and 11 (head3-4, after main's existentials merged), 19 and 18 (head5-6,
  remainders chosen only where no bound rules the counterexample out, as shipped). Five tasks 0.20.0 solves in every run
  (`reve/027`, `027b`, `yz_plus_minus_2`, `loop__upcount`, `loop__while_after_while_if`) were lost in head1-4, a
  remainder chosen first and a slow proof after it, and are solved in head5-6. The full runs: `arith/chc-gdp-premerge`
  (the first, 375, 17 out of time), `arith/chc-gdp-prewfrec` (382, before main's well-founded recursion merged; 12 out of
  time), `arith/chc-gdp` (381, above).

## 0.20.0

Spacer, Golem and Eldarica from `runs/modal/chc/full1` again: the image pins the same releases (Z3 5.3.1, Golem 0.9.0,
Eldarica 2.3) and the benchmarks at `b4fa7a7`, and their command, container (2 vCPU, 4 GB) and 60 s limit are as
they were; since that run, only the packing changed (one task per container, where full1 ran 12 a container one after
another). gdp-wired at bf42c65 (0.20.0, the cyclic certificate the default) from `runs/modal/chc2/v020-gdp`, together
in `runs/modal/chc2/combined-v020`.

| tool | sat | unsat | wrong | solved of 1,406 | out of time | median s of those solved |
| --- | --- | --- | --- | --- | --- | --- |
| Spacer (Z3 5.3.1) | 733 | 430 | 0 | 1,163 | 242 | 0.08 |
| Golem 0.9.0 | 728 | 426 | 0 | 1,154 | 252 | 0.04 |
| Eldarica 2.3 | 501 | 267 | 0 | 768 | 638 | 0.43 |
| gdp-wired 0.20.0 | 224 | 144 | 0 | 368 | 5 | 14.77 |

- Against `eng5-gdp` (366: 223 sat, 143 unsat, 315 out of time): 7 more, 5 fewer. Against `perf4-gdp` (365: 223 sat,
  142 unsat, 12 out of time): 5 more (`s_split_42`, `O3_trex03`, Lustre `MESI_i1_e3_2145_e7_1847`,
  `car_1_e7_184_e3_299`, `fast_2_e7_1871`), 2 fewer (`reve/014b`, `gj2007_m_3`). Each of the 5 tasks lost (against either run) ends unknown
  at the deadline (58.09 s to 58.37 s here); eng5 had solved them in 15.3 s to 52.22 s, perf4 the two in 58.06 s and
  58.1 s.
- Answered by: 224 sat with the invariants `inferLaws` found, 64 unsat by runs the prover guided, 43 by random runs, 37
  by `proveRule`'s refutation. Of the 1,033 unknown, every one ends after the invariant search; the 5 out of time are
  Lustre models.
- The certificate doesn't dominate: with `GDP_CERT=usual` (`runs/modal/chc2/v020-usual-gdp`), 369 solved (225 sat, 144
  unsat, none wrongly, 7 out of time); on the 223 sat tasks both runs solve, the median is 21.66 s (cyclic) and 21.71 s
  (usual), and the time after the guided runs adds to 2,752,243 ms and 2,783,451 ms; on the 144 unsat, 0.28 s and
  0.265 s. Of the three tasks that differ, each ends unknown at the deadline in the run that misses it (58.11 s to
  58.27 s), solved in the other at 58.09 s to 58.64 s.
- Nine solved by gdp-wired alone, the same nine as eng5; 906 solved by another tool and not by gdp-wired: 536 Spacer
  answers sat, 67 only Golem or Eldarica answer sat, 303 some tool answers unsat.

### What gdp-wired lacks, by Spacer's invariants

`prof/gap.py` reads Spacer's model of each of the 536 (`runs/modal/chc2/spacer-models-sat`, 60 s each; 531 came
back, 5 ran out of time), puts each predicate's interpretation in CNF over linear atoms, and checks each clause
against what `inferLaws` builds for that task (`prof/template.ts`, `runs/modal/chc2/template`: its atoms, its
coefficient magnitudes 1, 2, 3 and the first four of the machine's constants up to 1,000, and which shapes of two and
three values its limits leave). Then `prof/given.ts` states Spacer's invariant as gdp-wired laws (one per top-level
conjunct, `loc is p → conjunct`) and runs `proveRule` with them, no search (`runs/modal/chc2/given-spacer3`). A task's
class is its most demanding clause. Spacer's invariant isn't the only one, nor the simplest: a task whose Spacer
invariant is outside the templates may have another inside them.

| Spacer's invariant (sat, 536) | tasks | Lustre | given it, proven | given it, step goal undecided | can't be stated |
| --- | --- | --- | --- | --- | --- |
| within the templates: bounds of one value (204), a yes/no guard (23), two values (15), a disjunction of two as a counterexample's form (11) | 253 | 237 | 54 | 197 | 0 |
| a disjunction of three or more literals | 154 | 72 | 58 | 87 | 3 |
| more than three values in one atom | 71 | 32 | 22 | 41 | 0 |
| an existential (Spacer's projection) | 19 | 0 | 0 | 0 | 18 |
| a remainder (16) or a quotient (2) | 18 | 5 | 0 | 0 | 18 |
| a boolean structure past 4,000 CNF clauses | 13 | 0 | 0 | 6 | 6 |
| a disjunction of two outside the counterexample's forms (2), three values with a coefficient past the template (1) | 3 | 0 | 1 | 1 | 0 |
| no Spacer model in 60 s | 5 | 0 | | | |

The rest of each row: out of the 60 s given the invariant (16 in all), and 3 where the kernel refutes a conjunct of
Spacer's printed model itself (HOLA `05`, `17`, `39`; on `39` the printed model makes `CHC_COMP_FALSE` true while a
query reads it alone, so it isn't a model of the clauses).

- **The step goal over a wide transition (332 tasks, 287 of them Lustre).** Given Spacer's own invariant, the kernel
  leaves one of its conjuncts' step goals undecided at the prover's per-goal time budget (20 s, or 1 s a hypothesis
  past 20; 20,271 ms to 59,360 ms, median 38,623.5 ms). 195 of these are Lustre tasks whose invariant is within the
  templates, most often one yes/no value (`DRAGON_10`: `b19` alone, the time budget out at 37 hypotheses, 2 case
  splits deep); on 73 of the 195 the goal gdp-wired's search stopped on is one of Spacer's conjuncts. On `DRAGON_10`,
  of the 17 candidates it chose against the law's counterexamples, it dropped the other 16 one by one, and the proof
  of `b19`'s step then ran 22,166 ms into the deadline. The runs give the search little there: 39 reachable states,
  60,000 candidates alive after Houdini.
- **The search, the shape in reach (135 tasks proven given Spacer's invariant).** 54 within the templates (41 Lustre),
  81 outside them: a disjunction of three or more (58; 33 of them guards of two or more yes/no values beside at most
  one linear literal, a program counter in bits: 24 `ctigar`, 8 Lustre, 1 `conc`), more than three values (22), and one
  other.
- **Shapes outside the templates (278 tasks).** A disjunction of three or more literals (154: 73 of three or more
  linear literals, 43 of two beside yes/no values, 38 of yes/no values beside at most one linear literal of at most two
  values); more than three values in one atom (71: 39 of four values with coefficients ±1, 25 of those Lustre; of the
  39 not Lustre, 30 are the relational `reve` and `llreve` tasks, two programs side by side, x₁ + y₂ ≤ x₂ + y₁ and the
  like); the rest above. 84 tasks' invariants are nontrivial at two predicates or more; Spacer's invariants have 1–3
  clauses on 219 tasks, 4–10 on 143, 11–30 on 88, more on 81 (within the templates: one clause on 155 of 253).
- **What a gdp-wired law can't state here (45 given Spacer's invariant).** Laws state any linear sum, any coefficient,
  any disjunction (`or`, `any`) and products (`Term.mul`), so every class above is expressible but two: an existential
  (27, Spacer's projection leaving a variable; a quantifier-free equivalent exists in linear integer arithmetic, possibly
  with divisibility), and a remainder or quotient (18): the rule reads no `modBy(c)`/`divBy(c)` (translate.ts takes a
  CHC `mod` as a request value q with c·q ≤ e ≤ c·q + c − 1), and a CHC integer is a pair of naturals, so `x mod 2 = 0`
  needs a quotient in the state or the remainders of both parts.

Unsat (303 some tool answers and gdp-wired doesn't; Golem's derivations of false, `runs/modal/chc2/golem-cex-unsat`,
287 of them within 60 s), against how deep gdp-wired's runs the prover guided went (their steps a trial):

| | Lustre | other |
| --- | --- | --- |
| Golem's derivation longer than the guided runs go | 169 | 23 |
| within that depth, the values not found | 89 | 4 |
| past 2,000 steps (a guided run's cap) | 0 | 2 |
| no Golem derivation in 60 s | 15 | 1 |

- **Short derivations whose requests no run finds (Lustre, 273).** 225 of Golem's derivations are 5 steps or fewer
  (13 of 6–10, 17 of 11–20, 3 of 21–50); on the 258 with one, gdp-wired's guided runs make a median 47 steps in 18
  trials. Each step's
  request is a model of one clause's wide condition at the state, chosen without the query in view: the trials die after
  a few steps or wander (`car_4_e3_57_e5_999`: a derivation of 3 steps, 628 steps a trial). What's missing is a model of
  k steps at once with the query at the end (a bounded model check over the rule).
- **The others (30).** Mostly `hcai-bench/svcomp` (19): 15 derivations of 4 to 14 steps, and `O3_id_o20`, `o100`,
  `o200`, `o1000` of 23, 103, 203 and 1,003; the guided runs went 1.8 to 8.7 steps a trial there. `s_split_01` and
  `s_split_48` need 10,002 (a loop run to 10,000), past any run: a derivation that summarizes a loop (acceleration).
- The candidates for the next corpus, by class: `research/frontier2/candidates-chc.md`.

## Results before 0.20.0

Spacer, Golem and Eldarica from `runs/modal/chc/full1`, gdp-wired from `runs/modal/chc/eng5-gdp` (every task in its own
container), together in `runs/modal/chc/combined-eng5`. A task is solved when the answer is sat or unsat and, where
CHC-COMP'26 decided the task, the same as its verdict.

| tool | sat | unsat | wrong | solved of 1,406 | median s of those solved |
| --- | --- | --- | --- | --- | --- |
| Spacer (Z3 5.3.1) | 733 | 430 | 0 | 1,163 | 0.08 |
| Golem 0.9.0 | 728 | 426 | 0 | 1,154 | 0.04 |
| Eldarica 2.3 | 501 | 267 | 0 | 768 | 0.43 |
| gdp-wired | 223 | 143 | 0 | 366 | 14.71 |

- With the prover's deadline (every proof the search makes bounded by the stage's time, the stage ending 2 s before
  the limit): 365 solved (223 sat, 142 unsat), none wrongly, 12 out of time, against 315 out of time before
  (`runs/modal/chc/perf4-gdp`).
- Every task imports (none refused). Of gdp-wired's answers, 223 sat are the law proven with the invariants `inferLaws`
  found, checked by the kernel; 63 unsat are runs the prover guided reaching error, 43 random runs, 37 `proveRule`'s
  own refutation; every unsat run is checked against the CHC clauses by `checkDerivation`.
- Nine tasks are solved by gdp-wired and none of the others within 60 s; the others solve 908 that gdp-wired doesn't.
- The same track at 0.15.0's code (`runs/modal/chc/eng0-gdp`): 199 solved (119 sat, 80 unsat). What moved it:
  - A request names a clause that fires (the rule's assumption) instead of a step leaving the state as it was when the
    clause doesn't: each update then reads the clause named alone, where it read each clause's whole constraint. On 461
    tasks the first proof had stopped on `loc`'s kind law (stays a location), splitting every clause's constraint;
    none does now, and the tasks that ran out of time went from 339 to 95 (`eng2-gdp`: 259 solved).
  - Runs the prover guides: each request a model of its clause's condition where the run is (the prover's witness on a
    goal it doesn't refute), the clauses that derive false tried first: 63 unsat no random run had reached (on a
    hand-written task, a derivation of 702 steps).
  - In `inferLaws`, a counterexample to induction no candidate rules out makes candidates of its own, false at it and
    met by every sample under a condition it meets (a value, or a sum or difference of two, at most a threshold), the
    choice at its value as the guard; and a choice is no term among others. Of the 148 tasks that had ended so,
    Spacer (30 s, `spacer-models-cti`, `prof/spacer_models.py`) answered 80 sat, 70 of those with a disjunction in the
    invariant (24 with a coefficient of 2 or more) and 9 reading a remainder; 21 unsat; 47 ran out of time.
- Where it stops: 706 tasks end on a candidate the search chose whose own counterexample nothing rules out, 19 on the
  law's; 315 run out of the 60 s, 282 of them Lustre models. Three tasks the folder's first Houdini answered aren't
  answered (`dillig05_m`, `s_split_28`, `reve/026b`), nor three that 0.15.0's code answered (`s_split_20`,
  `s_multipl_18`, `loop__loop3`). Unsat Lustre models (274 that another tool answers) need deeper runs than these: the
  prover-guided runs take 40.5 steps a task there (the median), each request a model of a large constraint.
- What it found in the library: on the 766 Lustre tasks (one predicate over up to 80 integers and 33 booleans),
  `proveRule` spent 20–45 s proving that a yes/no state stays 0 or 1, case-splitting the whole step guard. 0.14.1's
  kernel row (an if is at most the sum of its branches; 0.14.2 keeps it to constant branches) closes that: the median
  prove stage over the track went from 20.8 s (`full2-gdp`, 1,358 tasks) to 0.35 s (`full4-gdp`, 1,392 tasks).
- Not covered: nonlinear clauses (none in this track), arrays, bit vectors and algebraic datatypes (other tracks).
