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
| `translate.ts` | A TIP problem as a `proveData` law: each datatype at the instances the problem uses (mutual where their fields reach each other), Peano naturals as naturals, each polymorphic function at its instances, a higher-order function specialised at the lambdas it is passed, a function variable of the goal as `fnParam`. Every refusal has a reason, and every change to the statement is recorded (below) |
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
| recursion that isn't structural (no parameter that every recursive call passes a field of) | 155 | 10 |
| Int subtraction | 14 | 23 |
| Int division | 12 | 6 |
| Int remainder | 2 | 1 |
| Int product of two unknowns | 2 | 1 |
| a function variable returning a list (`(=> a (list a))`) | 4 | 0 |
| an uninterpreted sort | 2 | 0 |
| an uninterpreted constant | 2 | 0 |
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
