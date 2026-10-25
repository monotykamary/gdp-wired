# Termination benchmarks through gdp-wired

gdp-wired proves a loop halts with `proveLoop` and no rank stated: core/cycles.ts's `findRank` takes the rank from the
loop's runs (linear by LP, the exact LP past coefficient 4, degree 2 one product at a time, tuples in order), then from
the loop's relation (core/relation.ts: its linear paths over the integers its pairs of naturals are, each path's
generators; a rank per location, blocks in order, each nested to depth 3; where none, regions split by one or two
atoms, invariants by Houdini over the relation, a location's and each region's own), with the invariants `inferLaws`
finds, and the kernel checks the halting goals. This directory runs it on termination problems
it didn't write, beside tools built for them, every task in its own Modal container (2 vCPU, 4 GB) under the same 60 s
wall-clock limit for every tool:

- TermComp's integer transition systems: TPDB-ARI (`TermCOMP/TPDB-ARI` at `183f29d`), `Integer_Transition_Systems`,
  all 1,239 `.ari` files (From_AProVE_2014 416, From_T2 806, Britikov_26 6, Lommen_26 6, Monma_26 5). No verdicts
  come with them.
- SV-COMP's termination tasks: sv-benchmarks (`sosy-lab/benchmarking/sv-benchmarks` at `c5cc603`), the
  ControlFlow-Termination set's directories (termination-crafted, -crafted-lit, -numeric, -restricted-15, -nla): the
  282 tasks with `termination.prp`, each with its expected verdict (221 true, 61 false).

| File | What |
| --- | --- |
| `ari.ts` | The ARI format read (`(format LCTRS)`, `(theory Ints)`: locations, an entrypoint, rules with guards), and an evaluator of a rule on integer values (BigInt) that uses no gdp-wired code; `checkLasso` replays a nontermination witness on it |
| `translate.ts` | A task as a kernel `Loop`, the same statement (below); `stepOf` turns a turn of the loop back into the task's step for the witness |
| `facts.ts` | The facts at locations: each value's constant or residue (x ≡ c mod k) at each location, a location split by a residue a guard reads, the task rewritten with them (the same runs); `lift` turns a lasso of the rewritten task back into the task's steps; `deadRules`, the rules the kernel shows never fire |
| `scc.ts` | The second translation, a stronger statement counted apart: each strongly connected component of the locations, chained (the paths between cut points composed into one rule each), from any state at its cut points |
| `solve.ts` | One task, read through facts.ts (`--no-facts`: as written): lassos from the loop's runs (2 s), a recurrent set (core/nonterm.ts, 4 s), `findRank` with all but 9 s of the limit, the kernel's check again on the loop as translated (the answer printed then, and again with the certificate once made), a recurrent set again (3/5 of what is left) and lassos with the rest; `--scc` for the second translation |
| `recur-lean.ts` | The recurrent sets of a run's answers (each printed in its `recur`) as Lean theorems `NeverEnds <task>_loop` by Kern.never_ends_of; `--shard i/n` |
| `c2ari.py` | An SV-COMP C program as an ARI system (pycparser): main and the functions it calls inlined, C's integer types and conversions on the task's data model, arrays, pointers to a fixed set of objects, undefined behaviour ending the run, recursion as two translations (one per answer); the subset in its header; refusals with their reason |
| `modal_term.py` | The ITS track on Modal: gdp-wired (`gdp`, `gdp-scc`), LoAT, LoAT with `--engine abmc`, KoAT2; `koat2-proof` and `loat-proof`, the same runs with their proofs kept |
| `modal_sv.py` | The SV-COMP tasks on Modal: gdp-wired on its translation, Ultimate Automizer on the C program, LoAT and KoAT2 on gdp-wired's translation |
| `summary.ts` | The tables below from run directories (later rows replacing earlier ones) |
| `failures.ts` | The tasks another tool answered and gdp-wired didn't, by where gdp-wired stopped and what KoAT2's proof used |
| `probes.ts`, `probes.json` | Two of the failure classes on loops written by hand (`modal run modal/run.py --jobs compare/term/probes.json`) |

    modal run compare/term/modal_term.py --out runs/modal/term/<name> [--tools gdp,gdp-scc,loat,loat-abmc,koat2] [--limit 60] [--tasks-file <names>]
    modal run compare/term/modal_sv.py --out runs/modal/term/<name> [--tools gdp,gdp-scc,uautomizer,loat-abmc,koat2]
    bun compare/term/summary.ts runs/modal/term/full1 runs/modal/term/koat-fix1 runs/modal/term/gdp2
    bun compare/term/failures.ts runs/modal/term/diag-koat runs/modal/term/full1 runs/modal/term/koat-fix1 runs/modal/term/gdp2 --bench <TPDB-ARI checkout>

## The translation

The state of the loop is `pc` (the location's number) and each argument slot as a pair of naturals (s, s$n), the
integer s − s$n, at most one of them nonzero: every step writes P ∸ N and N ∸ P for a value P − N, so a comparison
a ≤ b is a⁺ + b⁻ ≤ b⁺ + a⁻ and a product is the four products of the parts. The params are the entrypoint's integers
as pairs (every integer is one, so the loop starts wherever the task does). A turn's inputs are `t`, which rule leaving
the location fires (its index among them), and the values the rule leaves free (pairs again); the assumption is that
the rule named is at the location and its guard holds. An equation that gives a free value as a term of known ones is
a definition (x' = x + 1, or solved where the variable's coefficient is ±1), so most post values are terms, not
inputs; `exists` binds inputs; div and mod by a constant take one input each, with their range in the guard. A slot
no rule changes is a param. The loop runs while the location has a rule leaving it, and a state where no rule's guard
holds has no turn, so a run of the loop is a run of the task, value for value, and back: the loop halts from every
start exactly when the task terminates. Nothing is refused: all 1,239 tasks translate, 1,027 with nondeterministic
values, 527 with `exists`, 21 with products of variables, 5 with disjunctions, 3 with div or mod.

`gdp-scc` proves a stronger statement and is counted apart: every infinite run stays in one component from some step
on, so if no run inside a component is infinite from any values, the task terminates; that last step is scc.ts's
argument, not the kernel's (the kernel checks each component's halting). A component's slots that no guard reads
(directly or through the slots and definitions a guard's slots come from) are left out. From any values, a component
can run forever where the task never reaches those values (a loop whose bound an earlier assignment fixes); there it
proves nothing.

Nonterminating means a lasso: a run of the translated loop (gdp-wired's interpreter, random turns, inputs small or
values the state holds) that comes back to a state it was in, turned back into the task's steps (the rule and the
value of each of its free variables) and replayed by ari.ts's evaluator from the start to the repeat. gdp-wired's
prover made no claim about runs that never end until NonTerm.lean's `NeverEnds`: now a nonterminating answer is also
a closed recurrent set with its turn given by terms (core/nonterm.ts's findNeverEnds: a lasso's states, or a set of
linear facts fitted to a run whose inputs are terms over the state), a start and a stem into it, its closure goal
checked by the kernel (kernel.ts's checkRecur) and printed (`recur`) for Lean (`recur-lean.ts`); a lasso among those is
replayed by ari.ts's evaluator too.

For C, `c2ari.py` reads main and the functions it calls (each call inlined, a call inside an expression evaluated
first into a fresh variable), over C's integer types with their values exactly C's on the task's data model (LP64 or
ILP32, from its .yml; char signed, two's complement): unsigned arithmetic modulo 2^n (a fresh k with r − 2^n·k in the
range), the integer promotions and the usual arithmetic conversions (-1 < 5u is false), a conversion to an unsigned
type modulo 2^n, to a narrower signed type modulo 2^n into its range (gcc's), to _Bool 0 or 1; `/` and `%` by any
divisor as C's truncation toward zero; the ternary operator and conditions as values; arrays of a fixed size (an
element per variable; past 64 elements, the ones read at a constant index); pointers to a fixed set of objects
(globals and main's outermost locals whose address is taken, cells of a malloc, calloc or alloca executed at most
once; malloc may return null; free makes the cell dead). Undefined behaviour ends the run: a signed result out of its
type's range (checked unless the task declares no-overflow true), division by zero, an access out of bounds or through
a null, freed, too small or indeterminate pointer, a function's value used after it reached its closing brace. That is
how SV-COMP's expected verdicts read it: `cohencu1-both-t` is expected to terminate though its test 6·n + 6 <= k
overflows at k = INT_MAX (wrapped, it would hold forever), and `Binomial`, `TerminatorRec02` and
`RecursiveMultiplication-1` overflow and are expected to terminate. A run that never ends is then one with no
undefined behaviour, and "terminates" means every run ends or reaches it.

Recursion has two translations, each exact for one answer and read only for it (`--for`; solve.ts `--want`, the two
side by side in the container): for "terminates", every call to a recursive function either enters the function's
own copy with the caller's frame forgotten (a call that never returns) or skips the call, its value and every global
the function may write any value of their types (a call that returns): every infinite run of the program is one of
these (its depth grows forever, or some frame is never left and every later call it makes returns), so the system has
more runs and its termination is the program's; a call that returns has a value its function's summary allows,
where the system checks the summary itself (below). For "nonterminating", calls are inlined one deep, and past that a
call either enters the function's own copy, a return out of it ending the run, or is inlined exactly one call deeper, a
deeper call cutting the run (where that system would be past 400,000 rule-slots: inlined exactly up to 4 deep, and past
that only entering): every run of the system is a run of the program, so an infinite one is the program's. Where
overflow is checked, `--unchecked` (no checks, unbounded integers) is a third translation, for "terminates" only
(every run of the program is a prefix of one of its runs), run beside the checked one. 271 of the 282 tasks translate
(28 with recursion, 38 with overflow checked, 33 with products of variables, 25 with division, 10 unsigned, 4 with
arrays, 3 with pointers); refused: strings read through pointer arithmetic or calls whose order is unspecified and can
matter 9 (`cstr*`, `strchr-2`, `LexIndexValue-Pointer-2`), an array of 1,048 read at an index that is not a constant
2, `sqrt` (no body) 2. The 192 of the 226 that translated before translate as before, character for character; the
34 others have their overflow checks now (and `aviad`'s one unreachable rule left out)
(`runs/svfront/translations-main`, `translations-mine`). `c2ari_test.py`'s 66 adversarial programs (conversions, the
data model, recursion, arrays, pointers, division, undefined behaviour where it is and isn't evaluated, and the 21 of
the independent check's 93 that found defects, branch verify/sv-front, and 6 of its re-check's 52) are never answered
against how they run; nor are the check's 145 (`runs/svfront/suite-default-3`, `verify-fix2`). The ITS translation folds constants exactly and refuses one
past 2^53, which the kernel's numbers can't hold (no ITS task has one; a C task's 64-bit range is refused the same way).

`c2ari.py` then composes straight-line code away (`chain`; `--no-chain` keeps every location): a location other than
the entry, with no rule back to itself and one rule into it or one out of it, is left out, each rule into it composed
with each rule out of it; rules into a location no rule leaves are left out (the run ends there either way, a step
earlier), and so are locations the entry doesn't reach, rules whose guard its constants make false, and the bounds of
a fresh value nothing else reads. Every cycle keeps a location, so a run of the system is infinite exactly when the
program's is. A composition is not made where it would have more disjunctions, or more fresh values a guard
constrains past their bounds, than either part (each is a choice a random run has to draw), where it reads a guard
with a product of two values, or past 3 times its parts' size; the nonterminating translation of recursion isn't
chained (its lassos are found by runs turn by turn). A division of two constants is folded (`UINT_MAX / 2`). Across
the 271 translated tasks (`--for terminates`), the median system keeps 16% of its locations and 18% of its rules.

## Results

Integer transition systems (1,239). LoAT and KoAT2 from `runs/modal/term/full1`, KoAT2's 64 tasks that errored
there again from `koat-fix1` (KoAT2's readers refused the AProVE tasks' quoted names until renamed; 6 still error),
gdp-wired from `gdp2` (commit `327d9d6`); `bun compare/term/summary.ts` over the three gives
`runs/modal/term/its-summary.txt`. No task comes with a verdict, so an answer counts as wrong where another tool's
opposite answer is certified (gdp-wired's: the kernel's proof, or a lasso the evaluator replayed); no two tools
disagreed anywhere, certified or not.

| tool | terminates | nonterminating | wrong | solved of 1,239 | median s of those solved |
| --- | --- | --- | --- | --- | --- |
| gdp-wired (the task's statement) | 59 | 318 | 0 | 377 | 0.1 |
| gdp-wired, per component (stronger statement, counted apart) | 162 | 326 | 0 | 488 | 0.15 |
| LoAT v0.9.10 (`--mode termination`) | 2 | 532 | 0 | 534 | 0.17 |
| LoAT v0.9.10 (`--mode termination --engine abmc`) | 284 | 492 | 0 | 776 | 0.2 |
| KoAT2 v2.7.0 (`analyse --termination`) | 601 | 0 | 0 | 601 | 0.4 |

SV-COMP's termination tasks (282). Ultimate Automizer from `runs/modal/term/sv2`; gdp-wired, and LoAT and KoAT2 on
gdp-wired's translation, from `sv3` (commit `da30a0a`); `runs/modal/term/sv-summary.txt`. Wrong is an answer against
the task's expected verdict.

| tool | terminates | nonterminating | wrong | solved of 282 | median s of those solved |
| --- | --- | --- | --- | --- | --- |
| gdp-wired (the task's statement) | 0 | 47 | 0 | 47 | 0.17 |
| gdp-wired, per component (stronger statement, counted apart) | 40 | 47 | 0 | 87 | 0.2 |
| Ultimate Automizer v0.3.1 (the C program) | 171 | 53 | 0 | 224 | 7.78 |
| LoAT v0.9.10 abmc (gdp-wired's translation) | 107 | 41 | 0 | 148 | 0.26 |
| KoAT2 v2.7.0 (gdp-wired's translation) | 123 | 0 | 0 | 123 | 0.5 |

- Versions: LoAT `b41690b` (Yices 2.6.5, SwInE `141d022`, Z3 4.15.4.0, printed with its proofs in `diag-loat`),
  KoAT2 v2.7.0 (Z3 4.15.2.0), Ultimate Automizer's v0.3.1 release (OpenJDK 21.0.12.1), bun 1.4.4, pycparser 3.00.
  KoAT2 reads ARI through its own `ari-to-koat` (`^` and the quoted names renamed first); on the C translations 27 of
  its runs stop on `Z.Overflow` (the int range's constants). Ultimate Automizer refuses two tasks (`knuth-both-t`, `knuth-both-nt`: an operation its non-bitprecise translation lacks).
- Either gdp-wired translation solves 498 ITS tasks; any tool, 1,159. Eight ITS tasks are solved by gdp-wired and
  none of the others: `java_PlusSwap.c.t2` terminating (rank s7 + s8 on its one component), and seven nonterminating
  by lasso (`Velroyen08-moduloUp`, `complxStruc_rec`, `db2`, `db3` and their `_fixed` twins, `bio`), five of them
  where every other tool ran out of the 60 s. None of the SV tasks.
- The two translations' lasso counts differ (318 and 326) though their lassos are the same search: the runs are
  seeded but bounded by time, and the two rank searches between them take different times.
- Monma_26's README calls `reverse_lexicographic.ari` terminating. gdp-wired's lasso, replayed by the evaluator: from
  m = 6, l1 at (m, x, y, s, t, p) = (6, 6, 0, 0, 6, 0) goes l5 (y + 1, t − 1), l1, l2, l4 (y − 1, t + 1) and is back at
  (6, 6, 0, 0, 6, 0); LoAT abmc answers nonterminating too.
- The ranks found, over the 261 proofs of termination (ITS: gdp 59, gdp-scc 162; SV: gdp-scc 40), each component's
  counted: 320 ranks, 308 of one term and 12 tuples of two in order; 9 read a product of two variables, one a
  coefficient past 4.
- Not run: the Lean twin on the ranks found (every proof here is the kernel's, checked twice: in `findRank`, and again
  in solve.ts on the obligations of the loop as translated).

### Facts at locations, call summaries checked by the system (Unreleased)

The last misses of 0.28.0 (compare/term/facts.ts, c2ari.py; nothing in core/ or kernel/ changed, nothing trusted):

- **Facts at locations** (`facts.ts`, read by solve.ts before both translations; `--no-facts` without). What every run
  from the entrypoint knows of each slot at each location: a constant or a residue (x ≡ c mod k, Granger's
  congruences, a constant one mod 0), a fixpoint of the rules from the entrypoint, where every slot is any integer.
  The task is rewritten with them: a slot's value replaced by its constant, a value of a rule's own fixed by its guard
  replaced (∃v φ(v) is φ(c) where φ says v = c; a slot's comparison the guard makes is kept), a rule the facts make
  false and a location no run reaches left out. Where a guard reads a slot modulo k through a value of its own
  (`exists q. x − 2·q = 1`, x % 2 as c2ari translates it) and the facts there don't fix the residue, the locations of
  its strongly connected component are split by it (at most 8 copies): each rule into a copy guarded by the residue it
  gives (`exists g. x' − 2·g = r`), unless its source fixes it (x + 3 from an odd x), and in a copy the guard's own
  value is gone (∃q φ(x − k·q) is φ at one t ≡ r of each interval its comparisons of t leave). Each run of the task is
  one of the rewritten task's and back (the copy named by its values), so termination and the runs that never end are
  the same; a rank and a recurrent set then read a residue as a location and a value fixed after the start as a
  constant. A lasso is lifted back to the task's own steps (`lift`) and replayed by ari.ts's evaluator on the task as
  written. Bounded by its work (3 million units: a variable read), past which the task is read as written.
- **The rules no state fires** (`deadRules`): each rule's turn refuted by the kernel and its tree checked, within
  1.5 s in all, left out.
- **Call summaries** (c2ari.py, `--for terminates`). A recursive function whose value a caller reads past returning it
  (an argument, a condition, a variable) gets a summary: for each region its own comparisons of the arguments cut, its
  value an affine function of them, fitted to the values it returns on a grid of arguments (run on its C semantics; a
  region whose values aren't affine, or that returns none, says nothing): `mc91(n) = n − 10` where n > 100, 91 where
  n <= 100. A call that returns (skipped at a boundary) has a value the summary allows. The system checks the guess
  itself: the function's copy has a turn back to its entry, the state as it is, for each path of its body from its
  arguments (its calls skipped with their summaries' values, a loop's written values any) that returns a value the
  summary doesn't allow. That turn repeats forever, so a proof that the system terminates proves no path does; then,
  by induction on the calls' depth, every call that returns returns a value its summary allows, and the system still
  has every run of the program. The checks, where the summary holds, are rules no state fires (`deadRules` leaves them
  out; left in, a rank search reads their disjunctions on every path). Only pure functions (no global, pointer or
  nondeterministic value), of at most two arguments.
- **Calls that return past a boundary** (`--for nonterminating`): calls inlined one deep, and past that a call either
  enters the function's own copy or is inlined exactly one call deeper, a deeper call cutting the run (where the
  system stays under 400,000 rule-slots; else as before). A function's variables are one per place in its code and
  depth of calls (frames at one depth are never live together; a value an earlier frame left is one an uninitialized
  variable may hold): MutualRecursion_1a's 121 variables to 19.

One batch beside main 8b710ba (this branch's 0.28.0) launched together on Modal (60 s, 2 vCPU), and one earlier at
3ab223c (`its2-*`, `sv1-*`; `runs/par/`); every task gained or lost in either, run three times more a side
(`itsre-*`, `svre-*`). Wrong stays 0: no answer contradicts another's, LoAT's, LoAT abmc's or KoAT2's (`full1`).

| | ITS terminates | nonterminating | SV-COMP terminates | nonterminating | SV solved of 282 |
| --- | --- | --- | --- | --- | --- |
| the task's statement (`gdp`), here (cc10df0, 3ab223c) | 617, 614 | 544, 543 | 191, 191 | 57, 57 | 248, 248 |
| main 8b710ba (`its3`, `its2`, `its1`) | 612, 613, 611 | 540, 542, 539 | 183, 183 | 56, 56 | 239, 239 |
| per component (`gdp-scc`), here | 616, 613 | 545, 543 | 161, 161 | 57, 57 | 218, 218 |
| main | 614, 612, 612 | 543, 542, 542 | 154, 154 | 56, 56 | 210, 210 |

ITS nonterminating 543 to 544 on the task's statement against LoAT's default engine's 532; terminates 614 to 617
against KoAT2's 601; SV-COMP 248 against Ultimate Automizer's 224: ahead in this harness, unconfirmed under the
competitions' own setups.

- **Gained, ITS**, 3 of 3 here and 0 of 3 on main unless noted (both statements where not said): Velroyen08-alternatingIncr
  (nonterminating, 3.1 s: the odd x climbing by 2, a recurrent set over its parity's copies; VeryMax's and MuVal's NO at
  TermComp 2025), slayer-4-filtered (nonterminating, 2 of 3 here on the task's statement, 3 of 3 per component;
  LoAT's NO at TermComp 2025: 1,324 values fixed and 241 rules left out), juLinkedListCreateContainsAll, and on the
  task's statement eric2, queens.t2_fixed, traverse_twice.t2_fixed, ud.t2_fixed; per component loop3 and its `_fixed`
  twin, consts5.t2_fixed, slayer-n3-filtered and its twin, whatwhat, Graph.jar-obl-17 (nonterminating, 2 of 3).
- **Lost, ITS:** per component fun2, fun2b and fun3 (0 of 3 against 3 of 3: with 8 rules left out its component chains
  into one cut point of 108 rules, where main's, past scc.ts's cap, stays 6 locations of 36), RSA.jar-obl-17 (1 of 3
  against 3 of 3 on the task's statement, 0 against 2 per component: at the limit on main, 45.8 to 55.3 s, split by a
  parity it doesn't need, 28 locations to 34). The rest at the limit on both sides (elmhes, ns, queens.t2, opt-tree, hqr.t2_fixed,
  statemate.t2_fixed).
- **Gained, SV-COMP**, 3 of 3 here, 0 of 3 on main: the eight 0.28.0 left, McCarthy91_Recursion, NestedRecursion_1b,
  1c, 1d, rec_counter3 (summaries), MutualRecursion_1a (nonterminating: g(1) returns past the boundary before g(2) is
  entered again), 4BitCounterPointer (its pointers' constants), KroeningSharyginaTsitovichWintersteiger-CAV2010-Fig1
  (x % 2 a location); and NestedRecursion_2c; per component also IntPath and TwoWay. None lost (cohencu5-both-t per
  component 3 of 3 against 2 of 3).
- **Tests:** facts.ts against random runs both ways on the 891 ITS tasks it rewrites (each run of the task replayed on
  the rewritten one, each run of the rewritten one lifted and replayed on the task: 2,210,605 and 2,094,345 steps, none
  refused; with the first version's bug, a slot's value fixed by its own guard, 151 refused in 2 tasks, the bug that
  made 28 wrong answers in the first batch, `its1-mine`). `adversarial.test.ts` reads every program through the facts
  too, and checks no terminating one is answered nonterminating (4 new: a pinned slot, parity both ways, a constant
  after the start); `c2ari_test.py` 69 programs (3 new: a summary wrong past its samples, a value written in a loop,
  mutual recursion), none answered against the program, 44 answered as they run (main: 66, none, 40) (`tests1`).
- **Lean:** 17 recurrent sets of the batch read through the facts (alternatingIncr, slayer-4-filtered, slayer-3 and
  slayer-3-new `_fixed`, hqr.t2_fixed and 12 drawn at random), each a theorem `NeverEnds` of the rewritten task's loop
  (recur-lean.ts reads the facts where the answer's import did), on `propext`, `Classical.choice`, `Quot.sound`:
  17 of 17 checked, the longest 4 min 0.8 s (slayer-4-filtered), files up to 8,564,707 bytes (`lean1`).

What is left: on the terminating side, the 14 tasks another tool proves and no batch here does (of 18 at 0.28.0;
eric2, juLinkedListCreateContainsAll and loop3's two are closed): jacobi's five and spctrm's two, Iterations and
sudoku, where the relation's rank is found and the kernel doesn't close its goal in time (a rank per location, read at
every step: by its locations and rules, a split on pc and on t first, each branch still past the prover's budget,
17 to 20 case splits deep; KoAT2 bounds each transition on its own, after cutting the ones its invariants make
unsatisfiable); LogMult (no turn sampled), armc-difficult_foo3 (no nested rank per location on 38 paths), Domino
(out of time), and Round3 and disj_nightmare (LoAT abmc's). On the nonterminating side the hqr variants (their 24-
and 25-turn cycles give no candidate set) and the parity a split can't hold: a residue of a sum (x + y even), or past
8 copies, wants division in the kernel's terms (below).

**Hand-off to gen/sums (kernel.ts, lean-kernel, conformance; not changed here):** division by a constant in a loop's
terms. A loop's E gains `{op: 'div', a, k}`, k >= 1 a constant, natural floor division: NonTerm.lean's and Live.lean's
evalE `(.div a k) = evalE a / k`; kernel.ts's natural() accepts it where a is natural, natE reads a / k (bigint), and
the prover's term column for it brings the two rows that fix it, k·q <= a and a + 1 <= k·q + k (Euclid's, as
core/machine.ts's div$k facts already give for rules); the derivation's cuts already refute 2q + 1 = 2q'. To prove
first: the rows hold of evalE (an omega lemma), and never_ends_of/loop_halts_of are unchanged (they read evalC);
conformance: a set reading x div 2 with a tampered k, a witness reading it at the wrong residue. Then a recurrent set
can say x = 2·(x div 2) + 1 and a witness give x div 2, and a rank read x mod 2 as x − 2·(x div 2), with no location
split.

### Closures by cases, deeper cycles, the time for the next candidate (Unreleased)

The large programs' runs that never end (core/nonterm.ts, core/accel.ts) and one new certificate, Lean-first:

- **A closure by cases** (kernel.ts's `checkRecurCases`, NonTerm.lean's `never_ends_of_cases`, on `propext`,
  `Classical.choice`, `Quot.sound`). A translated program's closure goal reads the whole body at every read of the
  set: pgarch's sets, 537,164 distinct terms, never closed. Each part of an accelerated set is now a case: its location
  pinned, its rows the condition; one tree refutes the set with no case holding (`cover`), and each case's goal is read
  at its pins with the constants folded (`simpC`, `simpC_evalC`), the witness and the body first (`caseNeg`,
  `caseNeg_eval`), so it holds only that location's rules: pgarch's ten cases are 86 to 216 terms and close in 0.5 s in
  all on a laptop. Used where the goal is past 20,000 distinct terms (and so past the 1.5 million cap, where it was dropped);
  otherwise the certificate is the plain one. core/conformance.ts makes the found certificates by cases (nothing
  pinned, a value pinned) and tampered twins (the pin at another value, no case, a stem ending outside the set); every
  found one is accepted and holds on the reference run, every tampered one refused, by kernel.ts and by Lean
  (lean-kernel/conformance.ts --nonterm).
- **The time for the next candidate:** a closure tried on a set a stem reaches no longer counts against the search for
  candidates (up to the extension), and the sets whose closure ran out of time are retried smallest first, each its
  share of the time by its goal's size. edn's set (17,269 terms, closed in 1.7 s on a laptop) came after a run's 64-turn cycle whose
  closure took the whole extension. The search starts once the loop's relation is built (up to 10 s later): pgarch's and
  slayer's relations take seconds.
- **Deeper cycles:** after the walks of at most 6 choices, walks of up to 16 choices, at most 5,000, in the time left
  (hqr's cycle of 25 turns makes 16).
- **Stems:** a run's stem past 64 turns is replaced by a shorter one of the accelerated runs' search where it finds one
  within 500 ms (Lean replays every stem turn over the whole loop).

Two batches beside main a6d6403 (this branch merged it), launched together on Modal (60 s, 2 vCPU): `runs/nt5/its1-*`
(this branch at cebbf7c) and `its2-*` (at b3e8519), every gained and lost task run three times more a side
(`itsre-*`, `itsre2-*`, `itsre3-mine-*`); then a third after merging main f589873, beside it (`its3-*`, at 53bf839;
its new losses three times more, `itsre4-*`).

| | ITS terminates | nonterminating | solved of 1,239 |
| --- | --- | --- | --- |
| the task's statement (`gdp`), here | 611, 613, 612 | 541, 538, 540 | 1,152, 1,151, 1,152 |
| main (a6d6403, a6d6403, f589873) | 611, 612, 611 | 531, 534, 532 | 1,142, 1,146, 1,143 |
| per component (`gdp-scc`), here | 613, 613, 611 | 542, 542, 542 | 1,155, 1,155, 1,153 |
| main | 614, 612, 613 | 532, 533, 532 | 1,146, 1,145, 1,145 |
| LoAT's default engine (`full1`) | 2 | 532 | |

Nonterminating, 538 to 541 on the task's statement and 542 per component against LoAT's default engine's 532: ahead in
all three batches, in this harness and unconfirmed under TermComp's own setup. No answer contradicts LoAT's, LoAT abmc's or
KoAT2's (`full1`), or any tool's at TermComp 2025 (its raw data, zenodo.org/records/17076326: Golem, iRankFinder, T2,
VeryMax, MuVal, LoAT, KoAT on 1,222 of these tasks).

- **Gained**, in 5 of 5 runs here and 0 of 5 on main unless noted (task's statement; per component alike): edn.t2,
  pgarch.t2 and its `_fixed` twin, slayer-3-new.t2, slayer-3.t2; hqr.t2_fixed 3 of 5 (per component 5 of 5); db3.t2_fixed
  5 of 5 against 2 of 5; s1-striped.t2_fixed 5 against 3, s1.t2_fixed 5 against 4. Per component also slayer-3.t2_fixed
  and slayer-3-new.t2_fixed (5 of 5; on the task's statement 0 and 1 of 5). At TermComp 2025, slayer-3-new.t2 is T2's and
  LoAT's NO, slayer-3.t2 T2's, slayer-3.t2_fixed LoAT's; none is LoAT's here. In the probes (`runs/nt5/p*`) the s1 family
  answers at 15 to 26 s (38 to 59 s on main), tqli's at 4 s (15 to 40 s).
- **Lost**, each at the limit on both sides: db2.t2 (a lasso of the random runs, 4 of 5 against 5 of 5), qrdcmp.t2 and
  traverse.t2_fixed (terminating, ranks at 57 to 60 s, 4 of 5 against 5 of 5). Gained the same way: traverse2.t2_fixed,
  juLinkedListCreateRemoveFirstOccurrence (5 against 3), queens.t2 (1 against 0). After the merge (`its3-*`, 4 runs a
  side with `itsre4-*`): per component RSA.jar-obl-17 lost, 1 of 4 against 4 of 4 (main answers at 58.1 to 58.2 s: its
  component 4's rank, found there in 2.3 s and here in 1.2 s on a laptop, not found in time on Modal), ndes.t2_fixed 3
  of 4 against 4 of 4; reverse.t2_fixed gained on the task's statement, 3 of 4 against 3 of 4 (ranks at 52 to 60 s).
- **Still LoAT's alone:** hqr.c.i.hqr.pl.t2.fixed.t2_fixed and its `nor.t2.rlgfixed` twin. The deeper walks try their
  24- and 25-turn cycles (hundreds of them) and none gives a candidate set; LoAT's ends in an identity loop at l45 whose
  two fresh values sum below 0.
- **Not answered by anyone here, NO at TermComp 2025:** slayer-4-filtered (LoAT), Velroyen08-alternatingIncr (VeryMax,
  MuVal: an odd x climbing by 2 forever, whose set needs x's parity, which no linear set holds).

SV-COMP in the same batches (`sv1-*`, `sv2-*`, `sv3-*`): 239 (183, 56) in each against 225, 223 and 223 on the task's
statement, per component 210, 210 and 209 against 206, 207 and 207; every answer its expected verdict. The gains are the chained C translation's above
(gen/nonterm5-sv, merged).

Lean (`runs/nt5/lean-*`), each certificate a theorem `NeverEnds <task>_loop`, on `propext`, `Classical.choice`,
`Quot.sound`: s1.t2's file 410,471,697 bytes to 1,965,614 (the closure table held every choice of the goal, 5,214
term columns averaging 78 KB; it now holds the ones Lean's linear forms look up, here one), and the four s1 tasks
checked in 68 to 89 s each where s1.t2's was killed at 3,300 s (`lean-s1a`). A sample of
  48 recurrent sets of `its2-mine` (`lean-final`: every one closed by cases, 27, every task gained, the s1 family and 20
  more drawn at random), 48 of 48 checked, the longest 487.3 s (db2.t2_fixed), the largest file 16,485,844 bytes
  (pgarch.t2_fixed, its loop alone 10.9 MB), the median 10.2 s; Test4.jar-obl-10's in 9.0 s (62 minutes in `runs/accel/its-lean1-shard5`).
  Two exports had to change on the way: a list of more than 256 entries written as appended lists made Lean's
  elaboration of a certificate run past an hour (tqli.t2_fixed, killed at 3,300 s in `lean-p5`; 90 s as one list,
  `lean-pilot2`), and pgarch's loop, 690 body terms each 228 rules deep in one list, passed Lean's recursion limit, so a
  loop's start and body past 128 variables are definitions of 128 each (`lean-pilot3`, `lean-pilot4`: 7 min 8 s).

### Straight-line C code composed (Unreleased)

SV-COMP's 282 tasks at 60 s on Modal, `gdp` and `gdp-scc`, branch gen/nonterm5-sv (`runs/nt5/sv-chain5`) beside
gen/nonterm5 at eebdf44 (`sv-base5`), launched together; wrong is an answer against the expected verdict.

| | terminates | nonterminating | wrong | solved of 282 |
| --- | --- | --- | --- | --- |
| the task's statement (`gdp`), here | 183 | 56 | 0 | 239 |
| eebdf44 | 170 | 55 | 0 | 225 |
| per component (`gdp-scc`), here | 153 | 56 | 0 | 209 |
| eebdf44 | 151 | 55 | 0 | 206 |
| Ultimate Automizer v0.3.1 (`runs/modal/term/sv2`) | 171 | 53 | 0 | 224 |

On the task's statement 239 against Ultimate Automizer's 224 in this harness, unconfirmed under SV-COMP's own setup.
Every gained task, run three times a side (`svre5-mine-1..3`, `svre5-base-1..3`), answers in 3 of 3 here; none is lost.
- **Gained, `gdp`** (here's seconds; eebdf44 answers none of them in 3 runs but Singapore-2 in 1): Piecewise 8.5 to 9.4,
  HeizmannHoenickeLeikePodelski-ATVA2013-Fig5 9.8 to 11.2, Singapore-2 11.2 to 13.6, TelAviv-Amir-Minimum 14.7 to 16.1,
  GCD3 16.0 to 21.9, aaron3-1 19.4 to 19.5, Toulouse-MultiBranchesToLoop-2 23.7 to 25.4, UrbanMine-ESOP2014-Fig3 26.7
  to 30.1, AliasDarteFeautrierGonnord-SAS2010-nestedLoop-1 28.0 to 28.8, HarrisLalNoriRajamani-SAS2010-Fig1 37.0 to
  37.4, dijkstra1-both-t 42.8 to 45.5, cohencu4-both-t 50.3 to 50.4, TwoWay 57.3 to 57.4: ranks the search finds on
  the chained loop (a location or a few, each loop's body one turn) where per-location ranks over its 20 to 60
  locations weren't found; divbin1-both-nt (nonterminating) 0.2 to 0.3: `UINT_MAX / 2` folded, where a fresh quotient
  stood that no run drew (its lasso: B odd, the loop changes nothing).
- **Gained, `gdp-scc`:** divbin1-both-nt, LeeJonesBen-Amram-POPL2001-Ex4 (3 of 3 against 0), cohencu5-both-t (3 of 3
  against 1) and cohencu4-both-t (3 of 3 against 2).
- **Earlier versions of the chaining** (`sv-chain1` to `sv-chain4` beside `sv-base1` to `sv-base4`): composing a range
  check into the nondeterministic value it checks lost Stockholm-1 and Gothenburg_v2-1 (the invariant a = b read
  only through fresh values); composing two rules that each draw a constrained value, or each with a disjunction, lost
  Binary_Search-2's lasso (its runs stopped within 3 turns), and chaining the nonterminating translation of recursion
  lost it still; composing through `z·z` lost cohencu5-both-t (3 of 3 on eebdf44, 0 of 3 then, `svre-*`).
- `c2ari_test.py`: 66 programs, none answered against the program, 40 answered as they run (39 at eebdf44;
  `runs/nt5/sv-tests5`, `sv-tests-base`); `adversarial.test.ts` passes.
- **What Ultimate Automizer answers and `gdp` doesn't**, 8, none closed: the recursive programs whose rank needs what a
  call returns (McCarthy91_Recursion, NestedRecursion_1b, 1c, 1d, rec_counter3: the terminates translation lets a call
  return any value) and MutualRecursion_1a (nonterminating: a call that returns before the one that never does, past
  the inlining depth); 4BitCounterPointer (the rank reads the cells through pointers fixed after the stem: an invariant
  on the pointers' values); KroeningSharyginaTsitovichWintersteiger-CAV2010-Fig1 (x % 2: a rank over the parity).

### Closed forms (Unreleased)

One engine for what a loop does after n turns (core/accel.ts's `closedForm`, `nfold`, `accelerate`): a linear form along
an affine update, or a run of numbers, as Σ c·C(n, k)·rⁿ over the integer roots of its shortest recurrence. The
accelerated cycles read it for inner loops (a self-loop or a cycle of two turns that is a translation with a metering
function, taken to its end as one step: MysteriousProgram's display loop, its count growing each round), the stems for
self-loops with a closed form (a translation n times, a doubling loop 2 to 16 times at once), and core/discover.ts for
its closed forms. Around it: a product of a state value and a turn's input fixed by a case (RandomHard's arg2 = arg3·x
at arg3 = 1), the stem search deepened (twice and four times its depth) for a set the first search doesn't reach (fun9's
stem of 30 turns), a choice of a turn's input from the bounds the rest of the cycle puts on it (`lookahead`), and the
random runs held to their phase (one run of agafp's 140 locations took the whole search). Each answer is the same
certificate as before (kernel.ts's `checkRecur`, NonTerm.lean's `never_ends_of`); nothing trusted changed.

Beside main at e883e53 (0.26.0), launched together on Modal (60 s, 2 vCPU), three batches (`runs/closed/its-mine-2`
to `-4` beside `its-main-2` to `-4`; `sv-mine-2` to `-4` beside `sv-main-2` to `-4`), the branch at 55af42b, 369d88f and
6a3673e:

| | ITS terminates | nonterminating | solved of 1,239 | SV terminates | nonterminating | solved of 282 |
| --- | --- | --- | --- | --- | --- | --- |
| the task's statement (`gdp`), here | 612, 613, 613 | 529, 531, 529 | 1,141, 1,144, 1,142 | 170, 169, 170 | 55, 55, 55 | 225, 224, 225 |
| e883e53 | 610, 611, 613 | 527, 528, 526 | 1,137, 1,139, 1,139 | 170, 169, 169 | 55, 55, 55 | 225, 224, 224 |
| per component (`gdp-scc`), here | 613, 612, 611 | 534, 533, 535 | 1,147, 1,145, 1,146 | 152, 151, 151 | 55, 55, 55 | 207, 206, 206 |
| e883e53 | 612, 612, 612 | 531, 529, 527 | 1,143, 1,141, 1,139 | 152, 151, 152 | 55, 55, 55 | 207, 206, 207 |
| LoAT (`full1`), the nonterminating leader | 2 | 532 | | | | |

Per component, 533 to 535 nonterminating against LoAT's default engine's 532: ahead in each batch, in this harness and
unconfirmed under TermComp's own setup. On the task's statement 529 to 531, 1 to 3 behind. No answer contradicts
another's in the 13 ITS runs read (these, `its-mine1`, `its-mine-5`, `its-varA-1`, `nt3/its-mine6`, `its-main6`, and
LoAT's, LoAT abmc's and KoAT2's `full1`, `koat-fix1`), and every SV answer is its expected verdict.

After merging main at db0369f (gen/front-go, gen/invariants2), two batches beside db0369f (`its-merged-1`, `-2` beside
`its-main2-1`, `-2`; `sv-merged-1` beside `sv-main2-1`): ITS on the task's statement 532 and 530 nonterminating (610 and
614 terminating) against 528 and 530 (612, 613); per component 532 and 533 (613, 611) against 529 and 531 (612, 612).
LoAT's 532 is tied on either statement in the first batch, led by 1 per component in the second. SV-COMP 225 (170, 55)
against 224, per component 207 against 207 (cohencu5-both-t gained, cohencu4-both-t lost: the movers above). db2.t2
is a lasso of the first 2 s that both sides miss where the import takes past 1.6 s (here at 1.67 s in `its-merged-2`).

- **Gained in every batch** on both statements: MysteriousProgram (the inner loops and the lookahead; 42.31 to 44.91 s
  on the task's statement, where the first search's 4 s don't reach it, 8.55 to 21.92 s per component), RandomHard
  (the case arg3 = 1; 4.89 to 7.37 s), fun9 (the deepened stem; 4.09 to 5.03 s, but 41.3 s in the batch before the
  deepening moved into the first search). agafp.t2 and its `_fixed` twin, by an accelerated set since the random runs
  keep to their phase: on both statements in batches 3 and 4 (5.97 to 42.55 s); main's task statement has neither in
  any batch, its per component run some (26.14 to 55.02 s).
- **Lost**, each a search at the limit on main's side too: db2.t2_fixed and db3.t2_fixed (lassos main's runs found at
  53.99 to 57.77 s; found here per component at 55.26 to 57.01 s in batches 3 and 4), the s1 family (s1.t2, s1.t2_fixed,
  s1-striped.t2 and its twin: the closure of a set of 700,000 distinct nodes, answered between 36.58 and 59.73 s on
  both sides, lost and gained on both), and terminating answers at 58.44 to 60.08 s (elmhes, qrdcmp, ludcmp, traverse,
  print, ns, RSA: the rank search to the limit on both sides). SV's moving tasks run five
  times a side (`svre-*`): cohencu5-both-t per component 3 of 5 here, 2 of 5 on main; cohencu4-both-t 2 and 3;
  Singapore-2 4 and 1; BradleyMannaSipma-CAV2005-Fig1 5 and 5.
- **Lean** (`runs/closed/lean-1`): 39 of 40 certificates checked, on `propext`, `Classical.choice`, `Quot.sound`: the
  new ones of `its-mine-4` (MysteriousProgram, RandomHard, fun9, agafp.t2 and its twin, at most 251.7 s) and 34 others
  drawn at random; s1.t2's is too big, its Lean file 410,471,697 bytes, killed at 3,300 s.
- **Tried and left out:** the inner loops among the first walks (and KnapsackDP's counted loops dropped for them): its
  inner loop isn't a translation, and no candidate came (a local replay); the second search's accelerated
  share 0.6 in place of 0.4 (`its-varA-1` beside `its-mine-5`): 529 and 530 nonterminating against 531 and 534, the s1
  family timing out.
- **Still behind LoAT** on the task's statement: hqr's three (a cycle of 25 turns, as before), pgarch's two and
  slayer-3-new (203 and 426 locations), edn (its closure, 34 million nodes written out, not done in time), and the s1
  family and the db lassos by time.

### Accelerated cycles: products, inner loops, larger goals (Unreleased)

After merging main at 056fcc3, launched together with main at that commit in one batch (`runs/nt3/its-mine6`,
`its-main6`, `sv-mine6`, `sv-main6`):

| | ITS terminates | nonterminating | solved of 1,239 | SV terminates | nonterminating | solved of 282 |
| --- | --- | --- | --- | --- | --- | --- |
| the task's statement (`gdp`), here | 610 | 529 | 1,139 | 169 | 55 | 224 |
| 056fcc3 | 611 | 516 | 1,127 | 169 | 55 | 224 |
| per component (`gdp-scc`), here | 612 | 529 | 1,141 | 151 | 55 | 206 |
| 056fcc3 | 611 | 522 | 1,133 | 151 | 55 | 206 |
| LoAT (`full1`), the nonterminating leader | 2 | 532 | | | | |

LoAT's default engine still leads on nonterminating ITS tasks, by 3 on either statement. Of the 21 tasks it answered
NO and 0.25.0's run didn't, six are answered in each of the seven batches through this track (complInterv and
factorial by products, Test4, and three tqli by closures the kernel now builds and checks in the time); s1.t2,
s1.t2_fixed, s1-striped.t2 and its `_fixed` twin in 5 or 6 of the 7 (closure and check take 35 to 58 s); KnapsackDP
(its inner loop) in 4 (the three batches between gave the sets no stem reaches less time, since put back); agafp.t2 (a
lasso) in 3. In this batch 12 are left beside LoAT, 10 of the 21 and two that 0.25.0's run had, each read against
LoAT's proof (`runs/accel/loat-proof2`):

- a product of the state and a turn's input (RandomHard: `arg2 = arg3·x`, linear only at arg3 = 1, which nothing
  suggests), a stem through a doubling loop (MysteriousProgram: LoAT's runs x := 2x six times first);
- a cycle past the walks' 6 choices (the three hqr: one of 25 turns is found with 16 choices and 5,000 cycles, in 9 s,
  and its closure, of 633,928 distinct nodes, is not in 5 s), and programs of 203 and 426 locations (pgarch.t2, its
  `_fixed` twin, slayer-3-new);
- sets closed on a cycle no stem reaches (fun9: LoAT's set is on another cycle);
- by chance and time: agafp.t2 and its `_fixed` twin (lassos the last lasso stage finds or not), edn.t2 (main's
  second search finds it at 21.69 s per component; here, in some runs, a run's cycle of 64 turns takes that search's
  time).

Seven batches, each with main launched with it: 524, 527, 525, 525, 528 and 528 nonterminating here beside f990361's
518, 520, 517, 517, 515 and 517 (`runs/nt3/its-m4` and `its-base1`, then `its-mine` to `its-mine5` and `its-base` to
`its-base5`), then 529 beside 056fcc3's 516. No answer contradicts another tool's or another run's in the 42 ITS runs,
and every SV answer is its expected verdict.

### Accelerated cycles (Unreleased)

After merging main at 54bbec9 (gen/ranks2's rank splits, gen/sv-front's C front end), launched together with main
at that commit (`runs/accel2/its-mine`, `its-base`, `sv-mine`, `sv-base`):

| | ITS terminates | nonterminating | solved of 1,239 | SV terminates | nonterminating | solved of 282 |
| --- | --- | --- | --- | --- | --- | --- |
| the task's statement (`gdp`), here | 612 | 519 | 1,131 | 170 | 55 | 225 |
| 54bbec9 | 612 | 461 | 1,073 | 170 | 55 | 225 |
| per component (`gdp-scc`), here | 612 | 521 | 1,133 | 151 | 55 | 206 |
| 54bbec9 | 611 | 463 | 1,074 | 152 | 55 | 207 |

LoAT's default engine (532) leads on nonterminating tasks: 13 more than `gdp` here, 11 more than `gdp-scc`. Gained 59
nonterminating on each statement, lost one lasso each (db3.t2_fixed, db2.t2_fixed: found by main's lasso stage at 46
to 50 s); SV-COMP's per-component loss, cohencu5-both-t, is a rank search bounded by time, proved by main in 6 of 10
runs and here in 1 of 10 (4 of 9 with the accelerated stage off: `runs/accel2/svre-*`). The relation is one: ranks2's
shortcut for the ifs a path's pins decide, always on, and 6b2e2df's relation wherever both build
(`runs/accel2/relsame2`). Lean checks 40 of the 57 new accelerated sets, drawn at random, 40 of 40
(`runs/accel2/lean-sample`). The figures below are the run before the merge, beside 6b2e2df.

Recurrent sets from the relation's cycles (core/accel.ts), between the random runs and the policies in
core/nonterm.ts's search, on Modal (2 vCPU, 4 GB a task, 60 s): this branch (`runs/accel/its-mine1`, `sv-mine1`)
against main at 6b2e2df launched at the same time (`its-base1`, `sv-base1`). No answer contradicts another: not
LoAT's, LoAT abmc's or KoAT2's (`runs/modal/term/full1`), the other run's, or SV-COMP's expected verdicts.

| | ITS terminates | nonterminating | solved of 1,239 | SV terminates | nonterminating | solved of 282 |
| --- | --- | --- | --- | --- | --- | --- |
| the task's statement (`gdp`), here | 571 | 523 | 1,094 | 135 | 47 | 182 |
| 6b2e2df | 574 | 458 | 1,032 | 135 | 47 | 182 |
| per component (`gdp-scc`), here | 582 | 525 | 1,107 | 125 | 47 | 172 |
| 6b2e2df | 580 | 463 | 1,043 | 125 | 47 | 172 |
| LoAT (`full1`), the nonterminating leader | 2 | 532 | | | | |
| LoAT abmc (`full1`) | 284 | 492 | | | | |

The leader on nonterminating ITS tasks in this harness is LoAT's default engine, 532: 9 more than `gdp` here and 7
more than `gdp-scc`; LoAT abmc's 492 is passed.

- Nonterminating, gained 65 (`gdp`) and 62 (`gdp-scc`), lost none; 64 and 62 of them are LoAT's NO too, the other a
  lasso replayed by ari.ts's evaluator (db3.t2_fixed). Of `gdp`'s 523, 192 are accelerated sets, 323 solve.ts's own
  lassos, 8 the older recurrent sets; the 63 new accelerated ones come at a median 3.5 s (p90 45.1 s).
- Terminating, `gdp`: 2 gained, 5 lost, all five at the rank search's limit; run again (`runs/accel/lost5-mine`,
  `lost5-base`), this branch proves all five and 6b2e2df three. Nothing of the rank search changed.
- SV-COMP: the same answers; its 61 nonterminating tasks are 47 answered and 14 the C translation refuses.
- Lean: all 200 recurrent sets of the run (192 accelerated) are theorems `NeverEnds <task>_loop` that Lean 4.34.0
  checks, on `propext`, `Classical.choice`, `Quot.sound` (`recur-lean.ts --shard i/32`, `runs/accel/its-lean1`; one
  shard's 7 one a job, `its-lean1-shard5`: Test4.jar-obl-10's in 62 minutes).
- The tasks LoAT or LoAT abmc answers NO and `gdp` doesn't: 77 at 0.23.0's run (`runs/ranks/r4-its-merged`), 18 here (60 of the 77 answered),
  each read against LoAT's proof (`runs/accel/loat-proof2`, `runs/modal/term/diag-loat`): a product in the loop that
  the set needs (Velroyen08-complInterv's (x + 1)², factorial's s1·s2, RandomHard's products in its guard,
  MysteriousProgram's accelerated loop of a quadratic closed form), 4; an inner loop that runs 13 times inside the
  cycle (KnapsackDP: past the 6 choices the cycles are enumerated to, and no random run gets there), 1; a closure goal
  past what the kernel is given (s1 and s1-striped, 4: 163 to 346 million nodes, the cap 5 million), 4; a goal the
  kernel didn't close in the time left (tqli_fixed and tqli's `nor.t2.rlgfixed` twin: a cycle of 16 turns, 0.7 million
  nodes; tqli.t2's like goal closed in 22 s on a laptop; `gdp-scc` answers both), 2; no candidate from the cycles
  enumerated in the time (hqr, 3: LoAT's set is on a cycle of 13 of its chained steps; pgarch, 2, and slayer-3-new, of
  203 and 426 locations, whose LoAT proofs, 0.1 MB kept of each, show the run but not the clause it ends in), 6; sets
  closed on a cycle no stem reaches (fun9: 4, each closed within 0.2 s, the accelerated runs' search exhausted; LoAT's
  set is on another cycle), 1. One of the 18 (hqr's `nor.t2.rlgfixed` twin) was answered by a lasso at
  0.23.0's run, by chance of the random runs.

### The C front end (Unreleased)

SV-COMP's 282 tasks on Modal at 60 s, `gdp` and `gdp-scc`, this branch (`runs/svfront/f2-mine`) and main at 6b2e2df
(`f2-base`) launched together; wrong is an answer against the task's expected verdict.

| | terminates | nonterminating | unsupported | wrong | solved of 282 |
| --- | --- | --- | --- | --- | --- |
| the task's statement (`gdp`), here | 158 | 55 | 11 | 0 | 213 |
| main | 134 | 47 | 56 | 0 | 181 |
| per component (`gdp-scc`), here | 144 | 55 | 11 | 0 | 199 |
| main | 125 | 47 | 56 | 0 | 172 |
| Ultimate Automizer v0.3.1 (`runs/modal/term/sv2`) | 171 | 53 | | 0 | 224 |

- Gained (`gdp`), none lost: 25 tasks refused before (17 terminating: 12 recursive, `twisted` and `java_LogBuiltIn`
  (a call's value returned), the two `SyntaxSupportPointer01`, `Arrays01`; 8 nonterminating: 4 recursive by the
  nonterminating translation, `Arrays02`, `NonTermination3-1`, `-2`, `dijkstra1-both-nt-2` (unsigned)), and 7 unknown
  before: `cohencu2`, `3`, `6`, `7`
  and `Copenhagen_disj-2` (the overflow checks bound the values), `Pure3Phase-1`, `LeikeHeizmann-TACAS2014-Ex9`.
  `Benghazi_nondet-2`'s answer comes from the unchecked translation (the checked one proved it in 1 of 4 runs). Answer
  times: median 10.3 s for the gained ones (at most 43.6 s).
- 16 answered here and not by Ultimate Automizer (`Ackermann-2`, `Fibonacci01-2`, `MutualRecursion_1b`,
  `LeeJonesBen-Amram-POPL2001-Ex5`, `Arrays01`, `dijkstra1-both-nt-2`, the four `cohencu`, ...); 27 the other way:
  18 loops of the exact translation whose rank isn't found (6 of them `gdp-scc` proves), 5 recursive programs whose
  rank needs what a call returns (`McCarthy91_Recursion`, `NestedRecursion_1b`, `1c`, `1d`, `rec_counter3`: the
  terminates translation lets a call return any value), `TwoWay` (a param fixed to 1 the rank needs),
  `4BitCounterPointer`, and 2 nonterminating (`MutualRecursion_1a`: a call that never returns is made after a call
  at the same depth that does; `divbin1-both-nt`: unsigned, its lasso's wrap values not drawn).
- After the independent check's fixes (the translations unchanged), beside main at 5055882: 213 (158, 55), main 182
  (135, 47); per component 199, main 172; none wrong (`runs/svfront/f4-mine`, `f4-base`). One run before it answered
  212 (`f3-mine`: `gcd01-2`, the same translation, unproven where four other runs proved it at 26 to 33 s).

### Ranks from the relation (Unreleased)

With the runs that never end (below), on Modal (2 vCPU, 4 GB a task, 60 s), the same day: this branch
(`runs/ranks/r4-its-merged`, `r4-sv-merged`) against main at 2477b4a (`r2-its-main`, `r2-sv-main`: runs that never
end, no ranks from the relation) and 0.22.0 (`r2-its-base`, `r2-sv-base`). No answer contradicts another: not
LoAT's or KoAT2's (`full1`, `koat-fix1`), any other run's, earlier gdp-wired runs' (`gdp2`, `runs/backends/term-gdp`),
or SV-COMP's expected verdicts.

| | ITS terminates | nonterminating | solved of 1,239 | SV terminates | nonterminating | solved of 282 |
| --- | --- | --- | --- | --- | --- | --- |
| the task's statement (`gdp`), here | 572 | 463 | 1,035 | 134 | 47 | 181 |
| 2477b4a | 56 | 452 | 508 | 0 | 47 | 47 |
| 0.22.0 | 56 | 320 | 376 | 0 | 47 | 47 |
| per component (`gdp-scc`), here | 582 | 463 | 1,045 | 125 | 47 | 172 |
| 2477b4a | 155 | 463 | 618 | 39 | 47 | 86 |
| 0.22.0 | 155 | 325 | 480 | 39 | 47 | 86 |

- Answered by 2477b4a and not here: 5 and 7 nonterminating ITS tasks (found there between 5.8 s and 55.3 s,
  5 of the 12 past 40 s, by searches bounded by time and random; here the rank search has 70% of the time); against 0.22.0, 1 and 2 lassos (the lasso stages
  are random and bounded by time).
- On the tasks both answer alike the times are 2477b4a's (ITS, the task's statement: median 0.15 s each); a
  terminating answer's rank comes at a median 9.4 s (p95 21.9 s), the first stages' 6 s included. An earlier run of this
  branch (`r3-its-merged`, `r3-sv-merged`) answered 1,031, 1,043, 182 and 172; SV's one more is a proof at 51.4 s.
- An earlier run of the ranks alone, before the runs that never end, against 0.22.0 (`runs/ranks/its-mine`,
  `its-base`, `sv-mine`, `sv-base`): ITS 897 and 906, SV 183 and 172. Of its 572 ITS proofs on the task's statement,
  522 read the location and 13 needed invariants (SV 136 and 26); certificates 260 cyclic, 268 the usual trees, 44
  not made within the limit (SV 1, 117, 18).
- The independent check of these answers (branch verify/ranks) found two translator bugs, fixed: constants folded in
  doubles (now BigInt, past 2^53 refused) and C's conversions to char, short and _Bool read as the identity (now
  refused). No benchmark translation changed (`runs/ranks/translations-its.txt`, `translations-sv-c2ari.txt`,
  `translations-sv-loops.txt`); its adversarial programs are tests (`adversarial/`, `adversarial.test.ts`,
  `c2ari_test.py`).

### Runs that never end, after 0.22.0

The ITS track again, `gdp` alone, on Modal (the boat pool had no VM to spare): 0.22.0 (`c215ded`,
`runs/nonterm/base-its`) against this branch (`runs/nonterm/after2-its`); SV-COMP the same way (`runs/nonterm/base-sv`,
`runs/nonterm/after2-sv`).

| | terminates | nonterminating | unknown | timeout |
| --- | --- | --- | --- | --- |
| ITS, 0.22.0 | 56 | 320 | 837 | 26 |
| ITS, this branch | 56 | 450 | 703 | 30 |
| SV, 0.22.0 | 0 | 47 | 179 (56 unsupported) | 0 |
| SV, this branch | 0 | 47 | 179 (56 unsupported) | 0 |

- The 450: 319 lassos of solve.ts's own stage, as before, and 131 recurrent sets (106 sets of linear facts, 19 lassos
  of a policy run, 6 of a random run). 133 tasks are answered that 0.22.0 left (131 unknown, 2 timeouts); 3 that it
  answered by a lasso are not (2.t2 and bio.t2 unknown, afagp-fail.t2_fixed a timeout: the lasso stages' runs are
  bounded by time, and here the import took 2.9 s of the first stage's 2 s). The 56 proofs of termination are the same
  tasks.
- No answer contradicts another: none of the 450 is a task LoAT, LoAT abmc or KoAT2 proves terminating
  (`runs/modal/term/full1`, `koat-fix1`), none of the 56 one they prove nonterminating, and no task changed its answer
  between the two runs. Of the 133 new ones, 105 are LoAT's NO too and 24 are lassos replayed by ari.ts's evaluator;
  db2 and db3 had a replayed lasso in an earlier run (`runs/modal/term/gdp2`, gdp-scc); Velroyen08-fib and
  NonPeriodicNonterm2, which no other tool answers, were read by hand (a Fibonacci pair past a fixed bound never meets
  it again; a counter that doubles each time it meets the other).
- Lean: every recurrent set of the run, 131, is a theorem `NeverEnds <task>_loop` that Lean 4.34.0 checks (`decide
  +kernel`, on `propext`, `Classical.choice`, `Quot.sound`; `recur-lean.ts --shard i/32`, at most 1,865.9 s a shard on
  Modal, 4 CPUs: `runs/nonterm/after2-lean`). The 127 of an earlier run of this branch checked as well
  (`runs/nonterm/bench-lean`, `bench-lean2`).
- SV-COMP: unchanged; every nonterminating task another tool answers and gdp-wired doesn't is one the C translation
  refuses.

## Where gdp-wired stops

The tasks another tool answered and gdp-wired didn't (`failures.ts`; `runs/modal/term/failures-its.txt`,
`failures-sv.txt`). The location-free translation alone misses 113 ITS tasks and 40 SV tasks that the per-component
one proves: one rank for the whole program, the location a number in it, is what fails there (KoAT2's proofs give each
location its own). Past that, each terminating task is put where gdp-scc stopped:

| class | ITS | SV |
| --- | --- | --- |
| the rank the runs gave reads a param (a start value, constant along each run) and the kernel refused it | 217 | 95 |
| no turn of the component sampled: findRank's runs draw each input alone and keep a turn only where the guard holds | 158 | 4 |
| a rank the runs gave the kernel refused, reading no param (wrong off the runs, or needing an invariant not found) | 61 | 24 |
| no rank of the searched shapes fits the sampled turns | 9 | 6 |
| out of time | 2 | 0 |
| total, terminating by another tool | 447 | 129 |

- Params: the same loop written by hand (`while i <= 100 and X >= 1: i := i + 1`, rank 101 − i) beside params nothing
  reads is proven with 0, 1 or 2 of them and refused with 3, 4, 6 or 8, the rank found reading them
  (`(101 + P1 + P2 + X − (P0 + i))` with 3; `runs/modal/term/probes1`). Both translations make every start value a
  param, and every slot no rule changes.
- No turn sampled (ITS, the 154 where KoAT2's proof was read, split by what the component's guards ask, `--bench`):
  an input an equation pins (x = 2·q) 46, a constant past the runs' 64 in a guard 6, both 3, and 99 where several
  fresh values are bounded together (each drawn alone, the guard rarely holds of all of them). On SV it includes
  `WhileFalse`: a loop that takes no turn, where with no sampled turn findRank tries no rank at all.
- Of the 431 ITS tasks KoAT2 proved and gdp-wired didn't, its proof bounds every transition by a multiphase ranking
  function of depth 1 (354) or needs none (77): no proof read needs a multiphase rank; KoAT2 ranks each location
  separately and bounds transitions one at a time (an iterative Ackermann, `AckR`: 1 + y, 1 + y, 1 + x + y on its
  three rules). gdp-scc's rank there is x + 2·y, which the kernel refused; findRank tries no tuple after a linear rank
  the kernel refuses (the same reset written by hand is proven, rank (y, x): `probes1`).
- The multiphase and piecewise ones show up on SV, proven by Ultimate Automizer: `2Nested-1` (x := x + y; y := y − 1:
  y + 1, then x), `Toulouse-BranchesToLoop-2` (a rank by the sign of x), `Piecewise` (min(p, q)).
- Nonterminating by another tool and no lasso: 214 ITS tasks (LoAT's proofs are recurrent sets; they don't say whether
  a state repeats). gdp-wired's runs there: 129 long runs where no state came back, 85 runs that stop within 5 turns on
  average. Of 16 read by hand (every fourteenth of the 214 by name; a sample), in 9 the infinite run LoAT found grows
  or shrinks a value forever, so none of its states repeats (`toy2`, `Velroyen08-ex01`, `Velroyen08-trueDiv`,
  `ex04_rec`, `eric3`, `n-37`, `p-46`, `ruslan-benchmarks_misc_n-38`, `slayer-n2-filtered`); in 2 one turn takes the
  state LoAT's proof reaches back to itself when the turn's fresh values are chosen equal to the current ones, which
  the random draws never did (`DivTernary2`, `Samefringe`); 5 weren't decided by reading (`MainCopy`, `compress`,
  `fun10b`, `hqr.c.i.hqr.pl.t2.nor.t2.rlgfixed.t2_fixed`, `tqli`). On SV, every nonterminating task another tool
  answered and gdp-wired didn't is one it refuses to translate.

Bugs and limits found in the library, recorded here and not changed (this is a measurement):

- `findRank`'s LP reads params no guard reads, and the kernel refuses what it gives (above; `probes1`).
- With no sampled turn, `findRank` tries no rank (a loop whose guard is never met is proven by any constant).
- After the kernel refuses the linear rank the runs gave, `findRank` tries invariants and degree 2, never a tuple.
- `findRank` threw `Maximum call stack size exceeded` on 4 ITS tasks (`tqli.t2`: 29 locations, 47 rules, 22 slots;
  `pgarch.t2_fixed`: 203 locations), and on 30 ITS tasks it outran its deadline (the search given 49 s and still
  running at 60 s, `gdp2`'s timeouts).
- A loop's runs draw each input on its own and keep a turn where the assumption holds: an input the guard pins, or
  several bounded together, is almost never drawn (the 158 above).
