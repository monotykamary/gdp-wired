# TIP candidates for the next frontier corpus

From the TIP 2015 run (`compare/tip/`, `runs/modal/tip/full2`: 2 vCPU a container, 60 s for every tool): problems
gdp-wired's datatype language expresses (the translation reads them and agrees with TIP's evaluator on random values)
that `proveData` doesn't prove, one or two per capability found missing. "Diagnostic" is the `runs/modal/tip/diag-*` run
with one thing changed that proves it, where one does (none of those is the benchmark's answer). cvc5 is 1.4.2
`--quant-ind`, cvc5cg adds `--conjecture-gen --conjecture-gen-per-round=3 --full-saturate-quant`, Vampire is 5.1.0's
induction schedule. Peano naturals are read as naturals; "monomorphised" means the law proven is the instance at the
naturals of a statement TIP makes for every type.

| # | TIP | statement | capability needed | gdp-wired (`full2`) | diagnostic | cvc5 | cvc5cg | Vampire |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | `isaplanner/prop_21` | `n <= n + m`, both TIP's recursive `<=` and `+` | relate a recursive `<=`, `+` to the built-ins (a bridge lemma `leq x y ⇔ x ≤ y`, not a shape the conjectures make) | unknown, 5.79 s | `diag-native`: proven, 0.16 s | proven, 0.02 s | proven, 0.02 s | proven, 0.04 s |
| 2 | `isaplanner/prop_04` | `S (count n xs) = count n (n :: xs)`, count by the recursive `==` | `n == n` (TIP's `==` is equality) | unknown, 4.04 s | `diag-native` proven; `diag-lemmas` (given `n == n`) proven, 1.15 s | timeout | timeout | proven, 0.66 s |
| 3 | `tip2015/nat_le_trans` | `leq x y ⇒ leq y z ⇒ leq x z` | the bridge for `leq`, then transitivity of ≤ | unknown, 5.07 s | `diag-native`: proven | proven, 0.02 s | proven, 0.02 s | timeout |
| 4 | `tip2015/nat_boring_ge_reflexive` | `geq x x`, where `geq x y = leq y x` | unfold a non-recursive definition before choosing the induction | unknown, 0.90 s | `diag-inline`: proven | proven, 0.03 s | proven, 0.04 s | proven, 0.07 s |
| 5 | `isaplanner/prop_17` | `(n <= Z) = (n == Z)` | a proof by cases, no induction (tried when no scheme applies) | unknown, 0.68 s | `diag-today`: proven | proven, 0.02 s | proven, 0.02 s | proven, 0.04 s |
| 6 | `tip2015/list_PairOdds` | `map snd (pairs xs) = odds xs` (monomorphised; `map` specialised at the lambda) | time: the search finds it in 137.68 s | timeout | `diag-t300`: proven, 137.68 s | timeout | timeout | proven, 0.80 s |
| 7 | `prod/prop_24` | `even (x + y) = even (y + x)`, recursive `+` and `even` | a lemma of 7–8 symbols (`(n1 + n1) + n2 = n2 + (n1 + n1)` among those used) | unknown, 10.15 s | `diag-conj8` (conjectures to 8 symbols, 300 s): proven, 26.69 s | timeout | proven, 1.22 s | proven, 2.46 s |
| 8 | `tip2015/nat_acc_plus_same` | `plus x y = acc_plus x y` (accumulator: `acc_plus (S x) y = acc_plus x (S y)`) | a lemma of 7–8 symbols | unknown, 5.68 s | `diag-conj8`: proven, 23.2 s | timeout | proven, 11.3 s | proven, 0.16 s |
| 9 | `prod/lemma_09` | `rev (x ++ (y ++ [z])) = z :: rev (x ++ y)` (monomorphised) | two equations about other functions: `++` associative, `rev (l ++ [z]) = z :: rev l` | timeout | given both (`diag-lemmas`): timeout | proven, 0.03 s | proven, 0.03 s | proven, 0.03 s |
| 10 | `isaplanner/prop_53` | `count n xs = count n (sort xs)`, insertion sort by the recursive `<=`, count by `==` | the bridges, then `count n (insort x xs) = count n (x :: xs)` | unknown, 27.23 s | given the lemma, with and without `--native`: unknown | timeout | timeout | unknown, 60 s |
| 11 | `prod/prop_14` | `sorted (isort x)` | a conditional lemma: `sorted xs ⇒ sorted (insert y xs)` (and the bridge for `<=`) | unknown, 41.36 s | given the lemma, with and without `--native`: no | timeout | timeout | timeout |
| 12 | `prod/prop_42` | `elem x y ⇒ elem x (union y z)` | a conditional lemma about another argument: `elem x z ⇒ elem x (union y z)`; `x == y ⇒ x = y` | timeout | given both: no | timeout | timeout | timeout |
| 13 | `prod/prop_35` | `exp x y = qexp x y 1` (accumulator: `qexp x (S n) z = qexp x n (x · z)`) | the accumulator's generalisation `qexp x y z = exp x y · z`, with · associative and commutative | timeout | given those: unknown | timeout | timeout | timeout |
| 14 | `isaplanner/prop_49` | `butlast (xs ++ ys) = butlastConcat xs ys` (monomorphised) | a generalisation past 8 symbols: `butlast (xs ++ y :: ys) = xs ++ butlast (y :: ys)` | timeout | given it: no | proven, 0.05 s | proven, 0.09 s | proven, 0.17 s |
| 15 | `isaplanner/prop_84` | `zip xs (ys ++ zs) = zip (take (len ys) xs) ys ++ zip (drop (len ys) xs) zs` (monomorphised) | induction on `ys` with cases of `xs` at each step (two lists together) | timeout | none tried | proven, 0.02 s | proven, 0.02 s | proven, 0.22 s |
| 16 | `tip2015/bin_nat_plus` | `toNat (plus2 x y) = toNat x + toNat y`, binary numbers | `toNat (s x) = 1 + toNat x`, then `+` associative and commutative (TIP asserts the last two) | timeout | given them: timeout | timeout | timeout | unknown, 60 s |
| 17 | `tip2015/sort_nat_ISortPermutes` | `isPermutation (isort xs) xs`, `deleteBy` specialised at the equality lambda | a theory of permutations: `isPermutation ys zs ⇒ isPermutation (insert x ys) (x :: zs)`, `elem x (insert x ys)`, … | timeout | given those two: no | timeout | timeout | unknown, 60 s |
| 18 | `tip2015/nat_pow_pow` | `pow x (y · z) = pow (pow x y) z` | not to throw: `refute`'s evaluator overflows the stack on the values recursive `pow` makes | error (`Maximum call stack size exceeded`) | — | timeout | timeout | unknown, 60 s |

Rows 10–13 and 16–18 no tool here proves within 60 s; rows 1–9, 14 and 15 at least one does.

Since (`runs/modal/cheap/tip3`, proveData through the built-ins and its definitions unfolded, by cases where no
induction applies, `refute` skipping a value past its evaluation's bounds: core/transfer.ts): rows 1–5, 7 and 8 are
proven (0.26 s, 1.06 s, 0.33 s, 0.15 s, 0.22 s, 0.39 s, 0.20 s); row 18 is no longer an error (out of time); row 13
gives up (unknown, 17.98 s); the rest are still out of time at 60 s.

## What the language doesn't take

The 196 of TIP 2015's 492 theorems the translation refuses (and 41 of the 68 `false/`), each by the first construct it
can't read (`runs/modal/tip/full2`; a problem may have more than one):

| construct | theorems | `false/` | where |
| --- | --- | --- | --- |
| recursion that isn't structural (no parameter that every recursive call passes a field of) | 155 | 10 | merges of two lists (`lmerge` 24, `hmerge` 16, `bmerge` 8), three-argument recursion (`add3` 20, `add3acc` 20), sorts by size (`qsort`, `ssort`, `bubble` 8 each), `nubBy` 8, `idiv` 8, `models` 5, `twoThirds`, `third`, `op` 4 each, `interleave`, `mod2`, `subst`, `flatten1` 2 each, `flatten3`, `linTerm` 1 each; `reck` 8 in `false/` |
| Int arithmetic beyond + and constant multiples | 30 | 31 | subtraction 14 / 23, division 12 / 6, remainder 2 / 1, a product of two unknowns 2 / 1 |
| a function variable returning a datatype (`(=> a (list a))`) | 4 | 0 | `list_assoc`, `list_concat_map_bind`, `list_return_1`, `list_weird_concat_map_bind` |
| an uninterpreted sort | 2 | 0 | `isaplanner/prop_46`, `list_weird_is_normal` |
| an uninterpreted constant | 2 | 0 | `list_elem`, `list_nat_elem` |
| an existential goal | 2 | 0 | `list_elem_map`, `list_nat_elem_map` |
| a nested datatype at ever larger instances | 1 | 0 | `polyrec_seq_index` |

And what the translation reads only by changing the statement (112 of the 296 it reads): the goal's own type variables
at the naturals (102), Int read as a natural where the problem uses nothing that differs on the naturals (12, 2 of them
also monomorphised). A sort parameter of a law, read at an uninterpreted sort as cvc5 and Vampire read it, would make
those 102 the statement itself.
