# TIP 2015 through gdp-wired's datatype prover

The CHC track (`../chc/`) measured gdp-wired's rules on problems it didn't write. This directory does the same for
`proveData` (core/data.ts, `gdp-wired/data`): the standard benchmark for automated induction, TIP ("Tons of Inductive
Problems", `tip-org/benchmarks` at `bace5b2`, 2023-07-05), beside cvc5's and Vampire's induction on the same tasks, in
the same container, under the same wall-clock limit.

The sets: `benchmarks/isaplanner` (86), `prod` (74), `tip2015` (326) and `grammars` (6), 492 theorems (every one true);
and apart, `benchmarks/false` (68 false properties), to test refutations.

| File | What |
| --- | --- |
| `tip.ts` | TIP's format read (S-expressions, `declare-datatype(s)` with `par`, `define-fun(s)-rec`, `match`, `lambda`, `@`, `prove`), and an evaluator of a TIP program on values. It uses no gdp-wired code |
| `translate.ts` | A TIP problem as a `proveData` law: each datatype at the instances the problem uses (mutual where their fields reach each other), Peano naturals as naturals, each polymorphic function at its instances, a higher-order function specialised at the lambdas it is passed, the goal's sort variables and TIP's uninterpreted sorts as abstract sorts, an uninterpreted constant or function and a function variable of the goal as unknown functions (`fnParam` where it is one of a natural). Every refusal has a reason, and every change to the statement is recorded (below) |
| `solve.ts` | One task: translate, check the translation against TIP's evaluator on random values (the goal at 200 values, each function at 100), then `proveData` with the run's budget. Answers proven (the kernel checked the cyclic proof), refuted (a counterexample TIP's evaluator confirms breaks the goal as TIP states it), unknown, unsupported, or error. Its diagnostic flags are below |
| `modal_tip.py` | The run on Modal: every task and tool in its own container (2 vCPU, 4 GB), each tool under the same 60 s wall-clock limit, all at once. The image builds the TIP tools (`tip-org/tools` at `ca4c414`, with Stack) and makes cvc5's and Vampire's files once |
| `summary.ts` | The tables below from a run's `results.jsonl` |
| `lemmas-sample30.json` | The lemmas given by hand to a sample of failures (the classification below) |

    modal run compare/tip/modal_tip.py --out runs/modal/tip/<name> [--tools gdp,cvc5,cvc5cg,vampire] [--limit 60]
                                       [--sets isaplanner,prod,tip2015,grammars,false] [--only a|b] [--gdp-args '--inline']
    bun compare/tip/summary.ts runs/modal/tip/<name>

The tools, on TIP's own translations of the originals (`tip <f> --smtlib` for cvc5, `tip <f> --vampire` for Vampire:
monomorphised, the goal's type variables at an uninterpreted sort, lambdas axiomatised, the goal negated). In the cvc5
files a match's default case `_`, which SMT-LIB 2.6 doesn't take as a pattern, is a variable pattern instead (46 files).
The TIP files' `assert`ed facts (true lemmas given as hints, 32 of the problems gdp-wired fails) are axioms for cvc5 and
Vampire; gdp-wired isn't given them.

- cvc5 1.4.2 (`cvc5-Linux-x86_64-static`), `--quant-ind` (induction by Skolemisation with strengthening, Reynolds and
  Kuncak, VMCAI 2015), and `cvc5cg`: `--quant-ind --conjecture-gen --conjecture-gen-per-round=3 --full-saturate-quant`
  (their subgoal generation, the configuration the TIP paper ran CVC4 in, CICM 2015, without `--quant-cf`, which cvc5
  doesn't have). An unsat on the negated goal is a proof.
- Vampire 5.1.0, `--input_syntax smtlib2 --mode portfolio --schedule induction --cores 2 --time_limit 60`. A refutation
  of the negated goal is a proof.
- gdp-wired at this branch (from 0.20.0), `bun compare/tip/solve.ts <task> --ms 57000` (`proveData`'s budget is counted
  in work units, not wall time; the 60 s wall limit kills it the same as the others).

## Results

### The lemma search: calculated steps, uses ranked per case, merged schemes (gen/tip-lemmas)

`runs/tiplem/tip-8`: this branch, and `runs/tiplem/tip-base-8`: main at 6b2e2df, launched together on Modal (`--backend
modal`), the same image, sets (`false/` too), container shape and 60 s.

| theorems (492) | proven | refuted | wrong | unknown | timeout | unsupported |
| --- | --- | --- | --- | --- | --- | --- |
| `tiplem/tip-base-8` (main 6b2e2df) | 181 | 7 | 0 | 54 | 125 | 125 |
| `tiplem/tip-8` | 193 | 7 | 0 | 57 | 110 | 125 |

- `false/` (68): 23 refuted in both, none proven; the 7 theorems refuted are the same in both (the `tip2015` ones TIP
  writes false).
- Gained 14 (how each is proven): by calculated lemmas `prod/lemma_23` (5.13 s; multiplication associative, through
  the built-ins with `mul(y + n, z) = mul(y, z) + mul(n, z)` calculated from its step), `isaplanner/prop_20` (14.23 s)
  and `prod/prop_48` (15.41 s) (the length of an insertion, from the sort's step), `tip2015/nat_alt_mul_same` (9.82 s)
  and `nat_acc_alt_mul_same` (8.88 s) (alt_mul's step at a successor calculated, its commutativity conjectured),
  `tip2015/list_assoc` (58.08 s: bind over an append, calculated from the law's step, and ++ associative from that
  one's); by merged schemes `isaplanner/prop_41` (11.40 s), `prop_55` (20.62 s), `prop_57` (3.53 s), `prop_81`
  (3.63 s); by a case's arithmetic `prop_50` (53.16 s), `prop_56` (2.82 s), `prod/lemma_05` (29.16 s); by the split on
  an unknown function's guard `isaplanner/prop_14` (12.19 s, filter by p).
- Lost 2: `isaplanner/prop_51` (54.12 s on main) is proven by both sides in some runs and not others (main in 3 of
  the six pairs `tip-3` to `tip-8`, here in 2); `prod/lemma_12` is proven by main in all six (34.93 s to 59.57 s) and
  here in `tip-3` and `tip-4` only: its lemma pass now spends more of its time (the cases' wider uses make each
  attempt with a lemma slower in wall time for the same counted work), and its proof, the law at two unfoldings after
  the pass, comes past 60 s.
- Over the branch's runs, each beside main launched with it (`runs/tiplem/tip-3` to `tip-8`, each at the branch as it
  then was; `tip-6`, with a bug since fixed, left out): 195, 194, 194, 194 and 193 against 181, 183, 183, 182 and 181.
- The median time of the 179 both prove: 0.83 s here, 0.64 s on main.
- `list_assoc`, the lang/edges finding: its lemma `(a ++ b) >>= g = (a >>= g) ++ (b >>= g)` was found and not proven,
  because the use of ++'s associativity its case `a = x :: t, b = []` needs wasn't among the node's eight (ranked by the
  models of all its cases). Now a node keeps its candidates past the caps for its cases, and a case takes up to two of
  them whose sides are both terms of its own (up to the equalities the case's models take): `research/edges/lemma-case.ts`
  is proven both ways. The proof also needs the lemma itself first: lemma calculation gives it (the law's step with
  `t >>= f` and `f x` generalised), and then ++ associative (its own step's).

What the search does now, in core/data.ts:
- **Lemma calculation** (`calculated`, `reduceX`): for each variable of the law a scheme could induct on, and each of its
  datatype's constructors, the law at that constructor of fresh fields, its definitions unfolded where they are decided
  (a call whose body's first choice is decided by the arguments; an undecided choice inside a term kept as it is, its
  binders renamed by depth), the induction's hypothesis used as a rewrite (either way, also at other values of the law's
  other variables: `qrev x (a :: y)`), and what is left unequal, each subterm common to both sides a fresh variable, a
  conjecture; the base cases' too. Those random values don't refute come first, generalised steps first, then base
  cases; a generalised one's own steps are calculated again. They have their own count in a lemma pass (as many as the
  pass proves, 3 s each), and the law is tried again after the last of them.
- **Uses per case** (`caseJoins`): above.
- **Again after a lemma**: a conjecture of the pass that failed is tried once more after each lemma proven, within the
  same count.
- **Merged schemes**: each pair of recursion schemes on different variables, their uses taken two at once where they
  substitute a variable alike (n, m and xs all smaller at once for `drop n (take m xs)`); a call whose argument is a term
  gives such a half (`take n (xs ++ ys)`: n only). In the law's first attempts at one unfolding, a third of an attempt's
  time each; four at most.
- **A case's classes** (`instancesOf`'s): its conditions' equalities; linear forms through a class's constant and, in a
  model, a truncated difference whose left side is at least its right read as their difference; in the congruence
  phase, natural arguments of a function that are truncated differences equal in every model of the case, one class (an
  explanation takes such a step only where the facts give none). A case split on a guard that reads an unknown
  function at an abstract value's code (`filter p`). A lemma's constructor matched against any value of its datatype
  by its fields.

What is left: the 167 translated theorems not proven in `tip-8`, by what they need (the frontier2 classes, counted from
the run's laws), and how many another tool proves at 60 s (`runs/modal/tip/full2`):

| group | unproven here | of those, out of time | another tool proves | on main |
| --- | --- | --- | --- | --- |
| a conditional law (an implication, an iff, injectivity: nub, permutations, regular expressions, grammars) | 54 | 36 | 10 | 54 |
| sorting (a sort's count, permutation or order) | 29 | 15 | 0 | 30 |
| binary and signed integers as datatypes | 23 | 18 | 7 | 23 |
| take, drop, zip and rotate at lengths (arithmetic of positions) | 21 | 18 | 13 | 27 |
| an accumulator or a reversal (rev, qrev, flatten2, qfac, qexp) | 17 | 6 | 4 | 17 |
| arithmetic on naturals (weird_nat, powers, halves and evens) | 16 | 12 | 3 | 21 |
| a predicate over a list (escape, select, relaxed prefix) | 7 | 5 | 2 | 7 |

The group attacked is the one the other tools prove most of (on main 19 of its 27): proven here 7 of them
(`isaplanner/prop_41`, `prop_50`, `prop_55`, `prop_56`, `prop_57`, `prop_81`, `prod/lemma_05`), `prop_51` lost (above).
The conditional laws are the largest, and other tools prove 10 of their 54.

### Abstract sorts, unknown functions and constants (lang/edges)

`runs/edges/tip`: this branch, and `runs/edges/tip-base2`: main at 5c3f947, launched together on Modal (`--backend
modal`), the same image, sets (`false/` too), container shape and 60 s. The translation now reads a goal's sort
variables (`par (a) ...`) and TIP's uninterpreted sorts (`declare-sort S 0`) as abstract sorts (core/data.ts's `opaque`:
read by equality alone, so the law proven is the statement at every sort, not its instance at the naturals), an
uninterpreted constant or function (`declare-const`, `declare-fun`) as an unknown of its sort, and a function variable of
any sort but a function's or an integer's (into a list, of an abstract sort, of several arguments) as an unknown
function (core/data.ts's `unknownFn`). `--naturals` (solve.ts) takes the sort variables at the naturals as before.

| theorems (492) | proven | refuted | wrong | translated | unknown | timeout | unsupported | proven, statement unchanged |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `edges/tip-base2` (main 5c3f947) | 178 | 7 | 0 | 363 | 56 | 122 | 129 | 136 |
| `edges/tip` | 181 | 7 | 0 | 367 | 58 | 121 | 125 | 180 |

- Newly translated 4: proven 3, `isaplanner/prop_46` (0.58 s, zip of an empty list of `Any`), `tip2015/list_return_1`
  (11.33 s, `[x] >>= f = f x`: a lemma `xs ++ [] = xs` at f's value), `list_concat_map_bind` (0.64 s); out of time 1,
  `list_assoc` (`(m >>= f) >>= g = m >>= (λx. f x >>= g)`, below). Of the 129 refused before, 10 theorems were refused
  for no termination reason (the 4, and these 6): `list_weird_concat_map_bind` and `list_weird_is_normal` translate past
  their sort and function variable and are refused at `weird_concat`'s termination (its call on `cons xs xss` keeps
  the outer length: a lexicographic measure through a field that isn't of the list's group, the termination track's);
  `list_elem` and `list_nat_elem` past their constant `undefined`, at their existential (`∃ y. x = at xs y`: no witness
  among the goal's variables, the index of x is no term of the problem); `polyrec_seq_index` and `nicomachus_theorem`
  stay outside (below).
- The statement: 180 of the 181 proven are TIP's statement unchanged (main: 136 of 178), the other reading Int as a
  natural. Every one of the 120 theorems with sort variables that translate is now read at every sort (44 proven); main
  took all 116 of them at the naturals.
- Lost 1, at the limit: `isaplanner/prop_51` (57.4 s on main, out of the 60 s here; 51.9 s in the run before,
  `runs/edges/tip-base`). Gained 1 beside the new: `tip2015/list_nat_PairOdds` (33.43 s; out of time on main this run).
  A run before the last change (`runs/edges/tip-p1` against `tip-base`, launched together): 181 and 180, the same 3
  gains, `prop_51` and `prop_61` (both 51.9 s on main) out of time; there abstract values were drawn unlike the
  naturals, and `false/queue3_QueueL` went unrefuted. They are drawn as the naturals are now (core/data.ts's
  `randomValue`), and it is refuted as on main.
- `false/` (68): 23 refuted in both, each confirmed by TIP's evaluator; none proven. The 30 refutations are the same
  tasks in both runs (the 7 of `tip2015` false as TIP writes them, above).
- The median time of the 177 both prove: 0.65 s on main, 0.64 s here.
- `list_assoc` needs `(a ++ b) >>= g = (a >>= g) ++ (b >>= g)` with g unknown. The search finds it as a conjecture and
  doesn't prove it: in its induction's case `a = x :: t, b = []`, the lemma use it needs (++ associative at g's value
  at x) is ranked by the models of all the node's cases, where it holds in 15 of 24, under uses that hold in 19, and a
  case keeps four (core/data.ts's `lemmaCaps.perCase`). With g's values those of a recursive function of x the same
  proof is found; with a read of an unknown (`rep (g x)`, no decoding at all) it isn't (`research/edges/lemma-case.ts`,
  run locally). A general finding about the lemma uses, recorded here and left: ranking them within the case is a
  search change for every law, beyond this track.
- Outside, and why. `polyrec_seq_index`: `Seq a` holds a `Seq (pair a (Maybe a))`, so its instances never end, and
  `index` recurses at each of them (polymorphic recursion); a datatype language of instances fixed in advance can't
  declare it, and a sound route (one untyped datatype of every instance, its laws under a typing predicate) is not
  cheap. `nicomachus_theorem`: `cubes n = sum n · sum n` over Int, a product of two integers (the integers' encoding
  has constant multiples only; a product needs a new operation in Lean's export, trusted) and, apart from it, not a
  consequence of its definitions: `sum (x) = sum (x − 1) + x` for every x ≠ 0 leaves `sum (−1)` free (and `cubes (−1)`
  with it), so at n = −1 the goal holds only in some models; core/data.ts would refuse `sum` for its termination at a
  negative argument even with products, rightly. Read at the naturals it would be another statement. `false/
  imperative_Apa`: the same product, and `run`, whose `While` doesn't terminate.

`runs/lem/tip-final`: this branch, and `runs/lem/tip-final-base`: 0.22.0 (c215ded), launched together on Modal (boat
had no VM starts left), the same image, sets (`false/` too), container shape and 60 s.

| theorems (492) | proven | refuted | wrong | unknown | timeout | unsupported |
| --- | --- | --- | --- | --- | --- | --- |
| `lem/tip-final-base` (0.22.0) | 140 | 7 | 0 | 50 | 166 | 129 |
| `lem/tip-final` | 176 | 7 | 0 | 57 | 123 | 129 |

- 37 proven that 0.22.0 didn't, 1 lost (`tip2015/regexp_RecEps`, out of time; 27.6 s in the base run). `false/` (68):
  23 refuted in both, each confirmed by TIP's evaluator, none proven.
- By how they are proven: 30 `weird_nat` problems through bridges to sums (add3 and add3acc 9 each; mul2, mul3 and
  mul3acc 11 through copies over those bridges; op 1); 4 by the law alone at two unfoldings, tried before any
  conjecture (`isaplanner/prop_59`, `prop_63`, `prop_64`, `prop_67`); 2 by arguments equal by arithmetic
  (`isaplanner/prop_13`, `prop_42`: a definition on the naturals unfolded at n + 1); 1 with a conjectured lemma over
  three naturals, generalised apart from two, and no induction: `prod/prop_34` from `mult x y z = x·y + z` (an
  accumulator's).
- Two earlier commits of the branch, each run beside its own base the same way, proved more and cost the suite time:
  - tried the law again after each lemma without induction only, by its schemes after every third (`runs/lem/tip`
    against `tip-base`: 180 and 140, with `isaplanner/prop_60`, `prod/prop_12`, `prod/prop_23`, `list_PairOdds`,
    `tree_Flatten2`); the suite's search tree insertion took 194.8 s against 20.4 s (`runs/lem/suite-default-1`,
    `suite-base-default-1`);
  - ranked the conjectures bottom up, lower functions first (`runs/lem/tip-final-2` against `tip-final-base-2`: 176 and
    140, with `prod/prop_12` and without `prod/prop_10`); the datatype corpus's reverseReverse took 72.6 s against
    22.3 s (`runs/lem/suite-default-2`, `suite-base-default-2`).
- What each change gave, on all of TIP (each run a step of the branch, so a row is the changes up to it; the backend
  varied as boat's starts allowed, which moves the timeouts):

| run | backend | proven | what it adds |
| --- | --- | --- | --- |
| `runs/datafix/tip` (0.22.0) | Modal | 140 | |
| `runs/lem/tip-perf1` | Modal | 140 | structural term ids and shared substitution: 165 timeouts to 146, no proof more |
| `runs/lem/tip-v2` | Modal | 177 | ranks padded through the bridges, sums of naturals bridged, conjectures generalised apart, the law at two unfoldings early |
| `runs/lem/tip-v3` | Modal | 176 | decreases proven with lemmas: 20 more translated, all 20 out of time, none proven (reverted) |
| `runs/lem/tip-v4` | boat | 179 | lemma uses through other uses' conclusions; lemmas ranked bottom up (reverted) |
| `runs/lem/tip-v5` | boat | 181 | rounds of doubling time (replaced) |
| `runs/lem/tip-v6` | boat | 182 | the order: the goal's lemmas time-boxed, then the law alone with more time |
| `runs/lem/tip-v7` | Modal | 179 | the law again after a lemma without induction only (replaced) |
| `runs/lem/tip-final` | Modal | 176 | lemma attempts bounded by number; the law by its schemes after each of the goal's lemmas; the conjectures ranked as before |

- A diagnostic (`runs/lem/nolem1`, `--opts '{"lemmas":false}'`, the 216 unproven at `tip-perf1`): 39 proven with no
  conjectures at all, the deeper law alone, which the conjectures' rounds had crowded out of the 60 s.
- What still stops: the conjectures' 24 are mostly lemmas over constants where three variables or seven symbols are
  needed (`prod/prop_35`'s `qexp x y z = exp x y · z` with · associative); `isaplanner/prop_49`'s generalisation past
  six symbols a side; lemmas about a natural's own recursion (`even (n + n)`: no scheme inducts on a natural variable);
  decreases through another function (toList's `hmerge`, a merge sort's pairwise pass): proven with a size bound as a
  lemma only past the 60 s (`tip-v3`).

### Integers, division and remainders (after the well-founded recursion)

`runs/modal/arith/tip-gdp`: gdp-wired alone at the `lang/arith` branch (main's cheap wins, existentials and well-founded
recursion merged), the same image, sets, container shape and 60 s. The translation reads Int as gdp-wired's integers
(core/data.ts's `integer`, Lean's `Int`) where a problem subtracts or negates (the statement unchanged: −, unary minus,
constant multiples of any sign, `div` and `mod` by a positive constant as SMT-LIB's, Euclid's); elsewhere as a natural,
as before, now with `div` and `mod` by a positive constant (`Nat.divBy`, `modBy`) and a product of two unknowns (`mul`).
Division by a term that isn't a positive constant is refused with that reason (nonlinear: x = y·q + r), and so is a
product of two integers.

| theorems (492) | proven | refuted | wrong | translated | unknown | timeout | unsupported | error |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `wfrec/tip4` (the baseline) | 140 | 7 | 0 | 360 | 48 | 165 | 132 | 0 |
| `arith/tip-gdp` | 140 | 7 | 0 | 363 | 50 | 166 | 129 | 0 |

- The same 140 proven, the same 7 refuted (false as TIP writes them, each confirmed by TIP's evaluator, above). `false/`
  (68): 23 refuted, was 18: the five queue properties (`queue1_QueueL`, `queue1_QueueR`, `queue2_QueueL`,
  `queue2_QueueR`, `queue3_QueueL`), which subtract on Int, now translated over the integers and refuted, each
  counterexample confirmed by TIP's evaluator (`queue1_QueueL` at `(EnqR (EnqL 1 Empty) 5)`).
- The 30 theorems `full2` refused for Int arithmetic (subtraction 14, division 12, remainder 2, a product of two unknowns
  2): 3 translate and run out of time (`list_PairEvens`, `list_PairUnpair`: `mod (length xs) 2`; `bin_times`: a product
  of two naturals); 26 are refused next by their recursion (18 "termination isn't proven": `msorttd` recurses on `take k x` and `drop k x`
  with k = `div (length x) 2`, whose decrease needs a lemma about them; `nmsorttd`'s `half1`, `twoThirds`, `third` and
  McCarthy's 91 recurse on an Int, and no integer is a measure; 8 "a ring of functions that isn't structural"), and `nicomachus_theorem` multiplies two integers. Of the
  31 such `false/` properties, 5 are refuted (above), 1 unknown, 1 out of time, 24 refused by their recursion.
- Int read as a natural, a change of the statement: 15 translated theorems, was 12 (the three above); Int as the
  integers, the statement as written: 6 problems, the queues (`queue3_QueueR` unknown).
- What the integer sort proves, and doesn't, on its own (`examples/arith.ts`, research/frontier's `datatype/integers`):
  laws over integer arithmetic without recursion, a constructor's integer field, Euclid's division of a negative value;
  not a list's integer total through its negation or an append (each call's code decoded and written back, past the
  search's budget).

### Recursion that isn't structural (well-founded, after the existentials)

`runs/modal/wfrec/tip4`: gdp-wired alone at the `lang/wfrec` branch (with main's cheap wins and existentials merged),
the same image, sets, container shape and 60 s; cvc5 and Vampire from `full2` (`bun compare/tip/summary.ts
runs/modal/wfrec/tip4 runs/modal/tip/full2`). core/data.ts now takes a function whose recursion isn't structural once
its termination is proven: a measure (a parameter's size, a lexicographic tuple of them, a sum, or the LP's rank from
the function's runs) and, for each call, the kernel's proof that the measure falls under the path to the call; only then
is its equation a fact (core/data.ts, "well-founded recursion"). A law over such a function is tried by its own call
graph, ranked by the measure.

| theorems (492) | proven | refuted | wrong | translated | unknown | timeout | unsupported | error |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `cheap/tip3` (the baseline) | 137 | 0 | 0 | 296 | 27 | 132 | 196 | 0 |
| `wfrec/tip4` | 140 | 7 | 0 | 360 | 48 | 165 | 132 | 0 |

- Of the 155 theorems `full2` refused for recursion that isn't structural, 62 translate now. Proven 3:
  `tip2015/list_Interleave`, `list_nat_Interleave` (`interleave (evens xs) (odds xs) = xs`, interleave's measure
  size xs + size ys, by its own recursion) and `weird_nat_add3_spec`; 35 out of time, 19 unknown, and 5 refuted:
  `weird_nat_mul3_same`, `weird_nat_mul3acc_assoc1..3`, `weird_nat_mul3acc_spec`. Those 5 are false as TIP writes them:
  `mul3acc` adds `add3acc x y z` where `mul3` adds `add3 x2 x3 x4` (the predecessors), so mul3acc(2, 1, 1) =
  1 + add3acc(0, 0, add3acc(2, 1, 1)) = 5 while mul3(2, 1, 1) = 2; each counterexample is confirmed by TIP's evaluator,
  and none of cvc5, cvc5 with conjecture generation or Vampire proves any of them (`full2`). The 62, by the function
  `full2` refused first: `add3` 20, `add3acc` 20, `nubBy` 8, `qsort` 8, `op` 4, `interleave` 2. On those 62, within 60 s
  in `full2`: cvc5 12, cvc5 with conjecture generation 8, Vampire 15.
- wrong 0. The table lists apart a refutation whose counterexample TIP's evaluator confirms breaks the goal as written
  (solve.ts answers refuted only then): the 5 above and the existentials' 2 (`list_elem_map`, `list_nat_elem_map`,
  below); by the earlier rule (every refutation of a `tip2015` file wrong) they would count 7.
- No theorem `tip3` proved is lost; the 3 above are the gain (137 to 140). 360 translate (296 before, 2 of the 64 more
  the existential goals).
- The 93 still refused, each with its reason (`unsupported`, the measures tried): termination not proven 87 (`toList`
  16, `idiv` 12, `bmerge`, `bubsort`, `mergingbu`, `mergingbu2`, `ssort` 8 each, `nmsorttd`, `twoThirds`, `third` 4
  each, `mod2`, `subst`, `flatten1` 2 each, `flatten3` 1) and a ring of functions that isn't structural 6 (`models` 5,
  `linTerm` 1). `idiv x y = if x < y then 0 else S (idiv (x − y) y)` never ends at y = 0 (its runs show the call from
  (1, 0) to (1, 0)): TIP's `define-fun-rec` asserts an equation with no solution there, and refusing it is the point.
  The heap and bottom-up merge sorts `full2` refused at their merges (`hmerge`, `lmerge`) are refused now at the
  sort's own recursion (`toList`, `mergingbu`, `mergingbu2`), whose decrease needs a lemma about another function
  (`toList (hmerge p q)` below `toList (Node p y q)` needs the size of a merge; likewise a bubble sort's pass lowering
  the inversions, a merge sort's halves), which the obligations' search, run without conjectured lemmas, doesn't find.
- `false/` (68): 18 refuted (17 before, and `false/mergesort_merge_comm`, now translated), each confirmed by TIP's
  evaluator; none proven.

### After the cheap wins (core/transfer.ts)

`runs/modal/cheap/tip3`: gdp-wired from this branch, every task in its own container, 60 s, the same container
shape; cvc5's and Vampire's rows are `runs/modal/tip/full2`'s (unchanged tools), the two put together in
`runs/modal/cheap/tip3-with-full2` (`bun compare/tip/summary.ts runs/modal/cheap/tip3-with-full2`). proveData now
unfolds functions that aren't recursive, bridges a recursive function of naturals that computes a built-in once the
bridge law is proven (by proveData itself, first), tries the cases of a variable when no induction proves the law, and
skips a random value whose evaluation passes its bounds (`--native` and `--inline` are no-ops now; `--no-transfer` is
the law as stated).

| tool | proven | refuted | wrong | solved of 492 | median s of those solved |
| --- | --- | --- | --- | --- | --- |
| cvc5 1.4.2 `--quant-ind` | 168 | 0 | 0 | 168 | 0.03 |
| cvc5 1.4.2 `--quant-ind --conjecture-gen` | 187 | 0 | 0 | 187 | 0.04 |
| Vampire 5.1.0 (induction schedule) | 189 | 0 | 0 | 189 | 0.16 |
| gdp-wired (`proveData`) | 137 | 0 | 0 | 137 | 0.60 |

| tool | isaplanner (86) | prod (74) | tip2015 (326) | grammars (6) |
| --- | --- | --- | --- | --- |
| gdp-wired | 54 | 36 | 47 | 0 |
| gdp-wired: translated | 85 | 74 | 132 | 5 |

- 137 of the 296 translated (was 73): cvc5 142, cvc5 with conjecture generation 164, Vampire 154 on those. On the 184
  whose statement the translation leaves unchanged, 102 (was 39). Proven by gdp-wired and by none of the three: 12
  (`isaplanner/prop_47`, `prop_66`, `prop_68`, `prop_77`, `prod/lemma_12`, `lemma_16`, `prop_05`, `prop_10`,
  `prop_31`, `tip2015/nat_acc_alt_mul_comm`, `list_Select`, `list_nat_Select`).
- 78 of the 137 through the built-ins or with definitions unfolded (the law said so then proven with no induction 38,
  by recursion induction 37, one of those with a lemma found, by structural induction 3); 59 as stated.
- 65 proven that `full2` didn't: every one of the 48 the `--native` diagnostic proved, all 6 of `--inline`'s,
  `isaplanner/prop_17` (`--today`'s, by cases now), and 10 no diagnostic proved (`isaplanner/prop_77`,
  `prod/lemma_12`, `lemma_16`, `lemma_19`, `prop_24`, `prop_26`, `prop_47`, `tip2015/nat_acc_plus_same`,
  `nat_boring_ge_trans`, `nat_boring_gt_trans`; `prop_24` and `nat_acc_plus_same` are the two `--conj-size 8`
  needed 300 s for).
- 1 proven in `full2` and not now: `prod/prop_25` (31.38 s there, a timeout here). Its `+` is bridged, and the law said
  through `+` takes the time the law as stated needed (the search on it isn't reached). The 72 both prove: median
  1.115 s in `full2`, 0.985 s here.
- The four `refute` overflows (`fermat_last`, `nat_pow_times`, `nat_pow_pow`, `nat_pow_le_factorial`) are no longer
  errors (a sample past the evaluation's bounds is skipped): two unknown, two out of time, none proven. The
  `tip2015/int_*` problems no longer throw with their definitions unfolded; three are proven (`int_add_comm`,
  `int_add_ident_left`, `int_add_ident_right`). No errors in the run.
- `false/` (68): 17 refuted, the same 17 as `full2`, each confirmed by TIP's evaluator; none proven.

### The first run

`runs/modal/tip/full2`, every task and tool in its own container. A theorem is solved when proven; a proof of a
`false/` property, or a refutation of a theorem, is wrong.

| tool | proven | refuted | wrong | solved of 492 | median s of those solved |
| --- | --- | --- | --- | --- | --- |
| cvc5 1.4.2 `--quant-ind` | 168 | 0 | 0 | 168 | 0.03 |
| cvc5 1.4.2 `--quant-ind --conjecture-gen` | 187 | 0 | 0 | 187 | 0.04 |
| Vampire 5.1.0 (induction schedule) | 189 | 0 | 0 | 189 | 0.16 |
| gdp-wired (`proveData`) | 73 | 0 | 0 | 73 | 1.18 |

| tool | isaplanner (86) | prod (74) | tip2015 (326) | grammars (6) |
| --- | --- | --- | --- | --- |
| cvc5 `--quant-ind` | 65 | 31 | 71 | 1 |
| cvc5 `--quant-ind --conjecture-gen` | 73 | 42 | 71 | 1 |
| Vampire | 66 | 43 | 80 | 0 |
| gdp-wired | 25 | 22 | 26 | 0 |
| gdp-wired: translated | 85 | 74 | 132 | 5 |

On the 296 theorems gdp-wired translates: cvc5 142, cvc5 with conjecture generation 164, Vampire 154, gdp-wired 73 (183
by at least one of the three). On the 184 of those whose statement the translation leaves unchanged: 93, 113, 100 and 39.

- gdp-wired's 73: 39 with the statement unchanged, 33 at the goal's type variables taken at the naturals, 1 with Int
  read as a natural (what that means is below). 48 by recursion induction alone, 18 by recursion induction with lemmas
  it found, 5 by structural induction, 2 by structural induction with lemmas.
- Six are proven by gdp-wired and by none of the three within 60 s: `isaplanner/prop_47`, `prod/prop_05`,
  `prod/prop_10`, `prod/prop_31`, `tip2015/list_Select`, `tip2015/list_nat_Select`. The three prove 219 between them,
  36 of those among the problems gdp-wired doesn't translate.
- `false/` (68): gdp-wired refutes 17, each counterexample confirmed by TIP's evaluator, and translates 27 (10 run out
  of time); cvc5 and Vampire refute none. cvc5 proves 1 of the false properties (`regexp_deluxe_FromToConj`), with
  conjecture generation 6 (that one, `graph_bt3`, `graph_bt4`, `graph_bt5`, `graph_btp5`, `show_bin_lists_assoc`). In
  `show_bin_lists_assoc`, `shw` doesn't terminate on a negative integer, so its `define-fun-rec` has no model and
  anything follows; the others weren't looked into. cvc5 refuses four `false/hotel_key_safe*` files (a quoted symbol in
  a pattern).
- Errors: gdp-wired 4 (below, a bug); cvc5 with conjecture generation exits with no answer on 2 theorems
  (`rotate_structural_mod`, `propositional_AndCommutative`).
- An earlier run, `runs/modal/tip/full1`, had cvc5 refuse 46 files on the `_` pattern; gdp-wired's answers there are
  72 proven (one task fewer translated: Bool fields weren't read yet).

## Existential goals (after 0.20.0)

`runs/modal/tip/full2`'s translation refused 2 theorems for an existential goal, `tip2015/list_elem_map` and
`tip2015/list_nat_elem_map` (the same file twice): `∀ y f xs. elem y (map f xs) ⇒ ∃ x. f x = y ∧ elem y xs`. The
translation now reads an existential at the goal's end (`∀ v. H ⇒ ∃ x. B`, core/exists.ts's "there exists"): it proves
the goal through a witness among the goal's own variables of x's sort (H ⇒ B with it in place, a goal of its own), and
refutes it through what B says whatever x is (B's conjuncts that read no x, W: ∃ x. B implies W, so a counterexample
to H ⇒ W is one to the goal), that counterexample confirmed by TIP's evaluator on H ⇒ W. Both laws are checked against
TIP's evaluator before proving, as every translation is.

gdp-wired alone, `runs/modal/exists/tip-gdp2` (the same image, sets and 60 s, on the cheap-wins track's `proveData`;
cvc5 and Vampire from `full2`), against that track's `runs/modal/cheap/tip3`:

| theorems (492) | proven | refuted | wrong (by the table's rule) | translated | unknown | timeout | unsupported | error |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `cheap/tip3` | 137 | 0 | 0 | 296 | 27 | 132 | 196 | 0 |
| `exists/tip-gdp2` | 137 | 2 | 2 | 298 | 29 | 130 | 194 | 0 |

- The two existential goals: refuted in 0.07 s and 0.08 s, at `y = 3, xs = [5]` with `f 5 = 3` (the function variable
  drawn as a table: f(0..7) = 3, 2, 5, 4, 5, 3, 5, 2). There `elem 3 (map f [5]) = elem 3 [3]` holds and `elem 3 [5]`
  doesn't, so no x makes `f x = 3 ∧ elem 3 [5]` true: the statement as TIP writes it is false (it reads `elem y xs`
  where `elem x xs` was presumably meant), at the naturals and at any sort with two values. The table counts a
  refutation of a file under `benchmarks/tip2015` as wrong, since every such file is meant to be a theorem; these two are
  the statement's own error, checked by TIP's evaluator. cvc5 answers unknown on both (0.04 s, 0.16 s), cvc5 with
  conjecture generation and Vampire run out of the 60 s or answer unknown (`full2`).
- Otherwise the same answers as `tip3` but for 12 tasks moving between unknown and out of time, each ending at 41.58 s
  or later in both runs. `false/`: 17 refuted, as before. On 0.20.0's `proveData` (`runs/modal/exists/tip-gdp1`, against
  `full2`'s 73): 72 proven and the same 2 refuted, `prod/prop_36` (59.73 s in `full2`) out of time there.

## The translation

296 of the 492 theorems translate (`runs/modal/tip/full2`; `runs/modal/tip/tr1` is the first pass, translation only).
Every translation is checked against TIP's evaluator before proving (none disagreed). What the translation does, and what
of it changes the statement:

- **Unchanged statement** (184 of the 296): Peano naturals (a datatype `Z | S Nat`) read as gdp-wired's naturals, a
  bijection that keeps every function's own recursive definition (`plus` stays the recursive `plus`); polymorphic
  functions taken at the instances the goal calls; higher-order functions specialised at the lambdas they are passed
  (32 tasks), the variables a lambda captures as further arguments; a goal's function variable from naturals to Bool as
  x ↦ g(x) = 0 for an unknown g (4: every predicate is one of those); a datatype field of sort Bool as a datatype of two
  constructors (2); datatypes whose instances reach each other declared together.
- **Changed statement**, counted apart (112): the goal's own type variables (`(prove (par (a) ...))`) taken at the
  naturals: the law proven is the instance at the naturals, not the statement for every type (102: a 89, a and b 9, b 2,
  a with Int 2). cvc5 and Vampire prove those at an uninterpreted sort, the general statement. Int read as a natural
  (12, 2 of them with the above): only where the problem uses no subtraction, division, remainder, negative literal or
  product of two unknowns, so each operation means the same; the change is that Int's variables and fields range over
  the naturals.
- **Refused** (196), by the first construct the translator can't read:

| reason | theorems | `false/` |
| --- | --- | --- |
| recursion that isn't structural (no parameter that every recursive call passes a field of; 62 of the 155 taken since, as well-founded recursion, above) | 155 | 10 |
| Int subtraction | 14 | 23 |
| Int division | 12 | 6 |
| Int remainder | 2 | 1 |
| Int product of two unknowns | 2 | 1 |
| a function variable returning a list (`(=> a (list a))`; read since, above) | 4 | 0 |
| an uninterpreted sort (read since, above) | 2 | 0 |
| an uninterpreted constant (read since, above) | 2 | 0 |
| an existential goal (read since, above) | 2 | 0 |
| a nested datatype at ever larger instances (`polyrec_seq_index`) | 1 | 0 |

  The functions that aren't structural: `lmerge` 24, `add3` and `add3acc` 20 each (three-argument recursion), `hmerge`
  16, `nubBy`, `bmerge`, `bubble`, `qsort`, `ssort`, `idiv` 8 each, `models` 5, `twoThirds`, `third`, `op` 4 each,
  `interleave`, `mod2`, `subst`, `flatten1` 2 each, `flatten3`, `linTerm` 1 each.

## Where gdp-wired stops

Of the 296 translated theorems, 223 aren't proven (135 out of the 60 s, 84 unknown, 4 errors). Each class below is a
diagnostic run on those tasks with one thing changed, in this order, a task counted in the first that proves it; the
runs are `runs/modal/tip/diag-*`. None of them is the benchmark's result.

| class | tasks | how it was found |
| --- | --- | --- |
| proveData throws (`Maximum call stack size exceeded` in `refute`: random values through `pow` and factorial) | 4 | errors in `full2` (`fermat_last`, `nat_pow_times`, `nat_pow_pow`, `nat_pow_le_factorial`) |
| needs no induction, only cases: not tried when no scheme applies | 1 | `diag-today` (`--today`, proveData without induction): `isaplanner/prop_17` |
| a non-recursive definition between the law and the recursion (`geq x y = leq y x`) | 6 | `diag-inline` (`--inline`: functions that aren't recursive inlined) |
| more time | 6 | `diag-t300` (300 s instead of 60) |
| a lemma of 7 or 8 symbols | 4 | `diag-conj8` (`--conj-size 8`, 300 s): `prod/lemma_16`, `prod/prop_24`, `prod/prop_26`, `tip2015/nat_acc_plus_same` |
| the problem's own recursive `==`, `<=`, `+`, `-`, `min`, `max` on Peano naturals not related to the built-ins | 48 | `diag-native` (`--native`: each read as the built-in, each bridge law, the function equals the built-in, proven first by proveData; 2 bridges weren't, both through a non-recursive `geq`/`gt`) |
| the rest | 154 | a sample (below) |

The 154: a random sample of 30 was drawn from the 202 left before the `--native` run (seed 1,
`runs/modal/tip/sample30.txt`); 10 of the 30 fell in its class, and the other 20 are classified by reading each problem.
For 17 of them a lemma was written that the proof needs (`lemmas-sample30.json`) and given to proveData (`--lemma`,
proven first, without proveData's own conjectures): none was proven with it in 60 s, with or without `--native`
(`diag-lemmas`, `diag-native-lemmas`), so these classes say what a proof needs, not what would suffice for proveData.

| class (by reading) | of the 20 | tasks |
| --- | --- | --- |
| an equation about another function, beyond the conjectures | 6 | `prod/lemma_09` (++ associative, rev of a snoc), `isaplanner/prop_53` and `tip2015/sort_ISortCount` (count of an insertion), `prod/lemma_14` (length of `w ++ x :: z`), `tip2015/bin_nat_plus`, `tip2015/bin_nat_times` (toNat of the successor) |
| a conditional lemma (an implication, a predicate kept, injectivity) | 5 | `prod/prop_14`, `tip2015/sort_nat_ISortSorts` (insertion keeps a list sorted), `prod/prop_42` (elem through union), `grammars/packrat_unambigPackrat` (linA, linB injective, their images apart), `tip2015/list_nat_deleteAll_count` |
| an accumulator's generalisation | 2 | `prod/prop_35` (qexp x y z = exp x y · z, with · associative and commutative), `isaplanner/prop_49` (butlast of `xs ++ y :: ys`) |
| a theory of several lemmas | 6 | `tip2015/sort_nat_ISortPermutes`, `tip2015/list_perm_trans` (permutations via deleteBy), `tip2015/bin_nat_times_assoc`, `tip2015/bin_times_assoc` (binary multiplication), `tip2015/int_add_assoc` (signed integers as sign and magnitude), `tip2015/regexp_SeqDistrPlus` (regular expressions by derivatives) |
| induction on two lists together | 1 | `isaplanner/prop_84` (zip over `++`, with take and drop at a length) |

The problems' own asserted facts given as lemmas (`diag-asserts`, `--asserts`, 32 tasks) prove 2 (`int_add_ident_left`,
`int_add_ident_right`), both also in the `--native` class.

## What the measurement found in the library

Recorded in the first run, and fixed since (core/transfer.ts, core/data.ts; the results above):

- `refute`'s evaluator overflows the stack on values that recursive `pow` and factorial make large, and proveData throws
  instead of skipping the sample (4 tasks above).
- With `--inline`, proveData throws `undefined is not an object (evaluating 'd.name')` on the six `tip2015/int_*`
  problems it reads (`bun compare/tip/solve.ts .../int_mul_comm.smt2 --inline --ms 2000` shows it), likely a datatype
  the inlined law reads only through a constructor or a match, which `programOf` doesn't collect (it reads the sorts of
  variables, parameters and results).
- A law that needs cases and no induction gets no attempt without induction: `isaplanner/prop_17`,
  `(<= n Z) = (== n Z)`, is given up after 9 attempts in 0.58 s and proven by `--today`.
- The largest class: a problem's own recursive comparison or arithmetic. Each bridge (`leq x y ⇔ x ≤ y`,
  `== x y ⇔ x = y`, `plus x y = x + y`) is proven by proveData (146 bridges in `diag-native`, 15 to 109 ms of its
  budget each), and with them 48 problems are; without them proveData's conjectures don't make that shape.
  `isaplanner/prop_21` (`n ≤ n + m`) is given up after 57 attempts in 5.7 s with TIP's `<=` and `+`, and proven in
  0.16 s with the built-ins.

Candidates for the next frontier corpus, and the constructs the language doesn't take: `research/frontier2/candidates-tip.md`.
