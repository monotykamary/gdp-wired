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
| `solve.ts` | One task: import, `proveRule` on the law, random runs of the compiled rule, runs the prover guides (each request a model of its clause's condition where the run is, the clauses that derive false tried first), bounded runs (core/bmc.ts: a model of the kernel's k-step goal from the start to error, 10 s), then the library's invariant search (`inferLaws`, core/infer.ts) from the states the runs reached. Answers sat (a proof the kernel checked), unsat (a run reaching error that `checkDerivation` confirms), unknown or unsupported |
| `modal_chc.py` | The track on Modal: every task in its own container (2 vCPU, 4 GB), each tool under the same 60 s wall-clock limit, all at once (`starmap`) |
| `summary.ts` | The table below from a run's `results.jsonl`, with wrong answers counted against each task's expected verdict where some tool decided it at CHC-COMP'26 |
| `prof/kind.ts` | Not a solver (`--tools kind`): whether the law is k-inductive, a measure of what k-induction would add |
| `prof/` | A Modal profiler for one task's `proveRule`; `spacer_models.py`, the invariants Spacer finds for given tasks (or, with `--engine golem`, Golem's derivations of false); `template.ts` (`--tools tmpl`), what `inferLaws` would search on a task (its atoms, coefficient magnitudes and shape limits); `given.ts` (`--tools given`), `proveRule` given Spacer's invariant as laws; `gap.py`, the gap to Spacer by the shape of its invariant and what gdp-wired did |

    modal run compare/chc/modal_chc.py --out runs/modal/chc/<name> [--tools gdp,z3,golem,eldarica] [--limit 60]
    bun compare/chc/summary.ts runs/modal/chc/<name>
    modal run compare/chc/prof/spacer_models.py --out <dir> --tasks-json <file> [--engine golem]
    modal run compare/chc/modal_chc.py --out <dir> --tools tmpl            # then --tools given --tasks-json <file>
    python3 compare/chc/prof/gap.py --gdp <run> --others <run> --models <dir> --template <run> [--cex <dir>] [--given <run>] --out <file.json>

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
