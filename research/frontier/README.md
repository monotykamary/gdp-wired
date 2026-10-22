# The frontier: proofs nobody had to state

gdp-wired proves the laws you write. What it leaves to Lean or Bend today is, first, the proofs it would have to
invent: an invariant nobody wrote, a lemma about a recurrence or a fold nobody stated, products of unknowns. This
folder is the work of moving that line, measured on one corpus.

No search closes the gap in full: integer arithmetic with products is undecidable (Hilbert's tenth problem), safety of
a rule with two unbounded counters already is (Minsky machines), and whether a linear recurrence ever reaches 0 is open
from order 5 (the Skolem problem). What can move is how much of it the prover finds by itself. Every track keeps the
library's shape: an untrusted search proposes, the kernel checks, and a new kind of certificate enters the kernel only
with its soundness proven in the Lean twin.

| Track | What the search finds | What the kernel checks |
| --- | --- | --- |
| invariant | The inductive invariant a law needs: templates and runs, Houdini, generalized from the kernel's counterexamples to induction (IC3/PDR) | The law and the invariants found, as laws |
| lemma | Lemmas about a recurrence (`recur`) nobody stated: bounds, linear bounds in x, closed forms fitted exactly to its values, laws between two points | The lemmas, by the induction `recur` already proves them by |
| fold | The same for folds over lists and trees | By induction over the items or the tree, as `.carriesList` and `proveFold` already prove stated lemmas |
| nonlinear | Which products of facts and which squares refute a goal (Positivstellensatz of degree 2, as Lean's `nlinarith`) | A product row, and a square of a linear term, each proven sound in Lean |
| structure | A representation in which the law needs no induction: a list as positions and a length, so a prefix is a condition about every position below a length (the array property fragment, decidable) | The laws as they are, through `everyKey` |
| exists | A parity or a multiple nobody stated, as ∃k. v = c·k + r (`exists.ts`: a counter stepping by two, a ledger of multiples of 5) | The law with the existential as a plain law over a ghost witness (core/exists.ts) |
| cycle | A cyclic proof's shape: each node's rank (linear or of degree 2, in order, from the runs by LP, exact past small coefficients), where each back-edge returns, the companions a stuck claim needs (constants abstracted, bounds on what it reads); a loop's or a liveness's rank and the invariants it needs | The cyclic proof (`kernel/cyclic.ts`), the loop's halting goals, the liveness goals |

## The corpus

`corpus.ts` holds laws that gdp-wired proved (at eb28edc) only when the statement the proof needs is given, with that
statement taken out: research/synth's machines without their invariant, laws of the example domains proven only beside
their sibling laws (`walls.json`), examples/lemmas.ts's rules with no lemma, folds with no lemma, and true nonlinear laws
(`nonlinear.ts`). Each item has `today` (the library's prover alone) and, where its track has one, `frontier` (`inferLaws`,
`discover`). The nonlinear items need no search of their own: the kernel's squares prove them as they are.

    bun research/frontier/score.ts [--track lemma] [--limit 60] [--json runs/frontier/<name>.json]

| Track | Items | Proven at eb28edc | Proven now |
| --- | --- | --- | --- |
| invariant | 25 | 0 | 25 |
| lemma | 6 | 0 | 6 |
| fold | 3 | 0 | 3 |
| nonlinear | 8 | 0 | 8 |
| cycle | 21 | 0 | 21 |
| datatype | 23 | 0 | 23 |
| exists | 2 | 0 | 2 |
| all | 88 | 0 | 88 |

Now: the suite's `frontier-score` job, `runs/modal/ranks/suite1` (63 / 63, and the 22 broken variants of the cycle and
lemma tracks refused; the cycle track's times: `runs/modal/ranks/corpus3`); the datatype track, its own `frontier-datatype-0..5` jobs, `runs/modal/dataplus/corpus1` (18 / 18, its 12 broken
variants refused), and with the well-founded items `runs/modal/wfrec/suite2` (23 / 23, its 18 broken variants and
definitions that don't terminate refused); the exists track (added after 0.20.0), `runs/modal/exists/frontier3` (2 / 2, 581 ms and 1,011 ms,
its broken variant refused; the prover alone proves neither). The last, `(Σx)² <= n·Σx²` over running samples, is proven by the prover multiplying the goal by n
before the squares.

## Structure: path scopes, the case the docs called the wall

`scopes.ts` takes pi-fabric's resource patterns (`<ns>:<path>`, `/*`, `/**`, `<ns>:*`) and its `covers`, the check its
scope attenuation rests on, with a pattern's segments as a carried map from positions to interned names and its length
an input. Nothing is stated beyond the laws; each is proven and checked by the kernel (Modal, 2 vCPU,
`runs/modal/frontier-scopes2`):

| Law | Faithful | Broken variants |
| --- | --- | --- |
| covering is transitive | proven, 989 ms | `/*` covering `/**`: refuted |
| a pattern covers itself | proven, 86 ms | |
| what a covered pattern matches, the covering one matches (matching written apart from `covers`) | proven, 5,823 ms | the prefix skipped: refuted; `/*` covering `/**`: refuted |
| what a derived scope allows, its parent allows (scopes as lists of grants with actions, the two "some grant"s as witnesses) | proven, 1,845 ms | the actions ignored: refuted |
| what a scope allows, its normalized form allows (grants of one resource merged, actions joined, sorted) | proven, 747 ms | an action dropped when merging: refuted |
| what the normalized form allows, the scope allows (one law per action) | proven, 12,971 ms, 13,653 ms, 14,286 ms | |

The encoding agrees with pi-fabric's own `covers` on 20,000 random triples of patterns, and the grant tables with its
grant checks on 5,000 random pairs of scopes (`compareScopes`, `compareGrants`). Two things carried it:

- **A list as positions and a length.** A prefix is then a condition about every position below a length (the array
  property fragment, decidable), so prefixes of lists of paths needed no induction.
- **The bookkeeping as data.** Normalizing is a permutation, which no condition about every key states. The normalizer
  knows where each grant went (`To[g]`) and where each merged action came from (`From<a>[n]`); given those, the rule
  checks them at every key and the laws follow at the witnesses. The proven rule is the normalizer with its bookkeeping
  as output, which the code computes as it merges.

What stayed out then: reachability through a structure that changes, and recursive datatypes as values. Datatypes as
values are the datatype track's now (below); reachability through a structure that changes is still out, and why is
below too.

## Lemma and fold track: `discover`

`core/discover.ts` (`gdp-wired/discover`): `discover(rule, laws, stepLaws)` for a rule's `recur` functions and the
folds of the lists its requests carry, `discoverFold(fold, laws)` for a fold over a tree. Candidates come from the
values (each function at x from 0 to 40 and a few values of its further arguments; folds over 300 random lists; 300
random trees), every statement of a few shapes they all meet: bounds, bounds linear in x, in the further arguments, in
the other folds or the params (a product of a tree's value and a param among them), a closed form of degree 3 at most
fitted exactly (Newton's differences at x = 0..3, kept when every value meets it, tried alone first: it decides the
function, and the bounds beside it follow from it only through products), laws between two points. They are proven by the induction stated lemmas are proven by (Houdini: one not
proven is dropped, with every candidate the kernel's counterexample to induction breaks), then only what the laws need
is kept (each dropped in turn, with those that leaned on it). The rule comes back made again with them, and they come
back as source to paste. The kernel and the Lean twin are unchanged; `lean-kernel/package-check.ts` checks five of the
rules made again (`foundbackoff`, `foundarea`, `foundpyramid`, `foundinvoices`, `foundorgchart`; `foundpyramid` in the
suite's `lean-package-3`, `runs/modal/ranks/suite1`).

On Modal (the suite's `frontier-score` job, 2 vCPU, `runs/modal/lemma-suite1`), every lemma and fold item is proven,
with what the examples state found again (the backoff delay at most 64 and at least 1, x·x, the taxable part within
the total, the reports' cost at most the cap per head):

| Item | Frontier |
| --- | --- |
| lemma/retry with backoff | proven, 407 ms |
| lemma/two by two | proven, 214 ms |
| lemma/leftover ledger | proven, 425 ms |
| lemma/escalation | proven, 938 ms (the bound alone: the law is inductive over the rule with it) |
| lemma/area | proven, 342 ms |
| lemma/pyramid: 6·f(x) = 2·x·x·x + 3·x·x + x, the sum of the squares (`runs/modal/ranks/corpus3`, 1 vCPU) | proven, 60 ms (today: not proven) |
| fold/invoices | proven, 1,068 ms |
| fold/metered invoices | proven, 863 ms |
| fold/org chart | proven, 7,902 ms |

The pyramid's broken variant (a law with 2n where n is) is refused by both (the frontier, `proveSteps` with its search,
at 10,300 ms: the runs don't refute a rule that reads a function, so the search tries every candidate lemma).

Not found: a lemma of another shape (a bound by a product of two unknowns other than a tree's value and a param, a
closed form past degree 3 or with further arguments, an exponential), and anything about a quantified state invariant
(examples/trees.ts's tables of nodes: the invariant track's).

## Cycle track: `findCycles`, `findRank`, `cycleLemmas`

`core/cycles.ts` (`gdp-wired/cycles`) searches for what core/cyclic.ts's builders fix by rule shape: from claims over
functions defined by their equations, the facts are run (values, and at each claim's samples the calls its goal
makes); back-edges go to a claim at the arguments of each call the goal reads, guarded by where that claim may be used
(its hypotheses and its rank below), so the premises and the descent are the guard's; the ranks are linear over each
claim's variables, an integer LP over the runs' edges (each sampled call must drop), lexicographic by successive
elimination, with coefficients up to 4 first and past them the exact LP (below), then of degree 2 over the products of
two variables the claims read; a stuck claim gets companions, its constants abstracted (an accumulator) below it or bounds on what its
goal reads beside it (Houdini, then only those it needs). Loops take their rank from their runs, `inferLaws` finding
the invariants the kernel's halting goals need (the descent as step laws). A rule reading functions known by their
facts gets lemmas fitted to their JavaScript and proven from the facts as cyclic claims, for functions of one argument
and of two (an exact line, or bounds by 0, k, j or k + j and the tightest constant, each proven alone). A liveness with
no rank (`leadsTo` without `rank`) gets one from the rule's runs (`findLeadsTo`): a helpful request in its region must
lower it, any other step must not raise it (an edge it need not lower, dropped once a component lowers it), then the
kernel's liveness goals with the invariants inferLaws finds. Nothing new is trusted: every rank is a term the kernel's
goals read as they read a stated one, a product a monomial, and no certificate has a new shape.

- **The exact LP.** Where no solution has coefficients up to 4 (the box the search tries first, small coefficients
  first), the rows are solved exactly over the rationals (a two-phase simplex, the least sum of absolute coefficients),
  the solution scaled to whole numbers. It is found on the smaller half of the runs (each row's size its largest
  coefficient) and kept only where it holds of all of them: 11·x + 2·y, which each trade of the exchange forces, is the
  same on both halves; 32·x + y for the triangle, which the runs' size forces (x reaches 33 there, and y := x − 1), is
  not, and the rank found is (x, y).
- **Degree 2.** One product of two variables at a time (a square too), a further variable of the LP, its value the
  product's: with every product at once the runs fit a rank of many small parts (the exact LP's least solution over
  them is dense) that the kernel refuses. For a loop, the products its own terms read first (while i < N·M), before the
  invariants; the others after them, within a quarter of its time. For claims, the products they read, each component
  a natural only at the ends of the edges it compares (n·n − i is 0, truncated, past the square, where no call is
  made). The linear rank the runs give for counting up to N·M is 299 − i (the runs stop at 300 turns), which the kernel
  refuses; the degree-2 one is M·N − (i + 1).
- **Products in order.** A product rank of a nested loop is a linear one in order where one exists, which the search
  finds first: the triangle (y counts down, then x drops and y starts again from x − 1) has x·x + y and (x, y).

`today` is what the library did before with the same statement: for claims, the builders' shape (rank x for each
variable x tried, back-edges at x − 1, the search's own fact instances); for loops, kernel/run-more.ts's rank templates
(a state variable, a param minus one, a sum of two); for rules, `proveRule`'s search with `cycles: false`; for a
liveness, the loops' templates as its rank, each through `proveLiveness`. Each item has a broken variant, which must be
refused. Modal, 1 vCPU a job, `runs/modal/ranks/corpus3` (at 0.19.0, `runs/modal/cycsearch/corpus1`):

| Item | Today | Frontier | Found |
| --- | --- | --- | --- |
| McCarthy's 91: f(n) = 91 for n <= 101 | not proven | proven, 103 ms | rank 101 − n, back-edges at n + 11 and f(n + 11) |
| Ackermann: ack(m, n) > n | not proven | proven, 368 ms | rank (m, n) |
| gcd by subtraction: >= 1 and <= x, for x, y >= 1 | not proven | proven, 460 ms | rank x + y |
| an accumulator: g(x, 0) = 2x | not proven | proven, 59 ms | g(x, a) = a + 2x, below it |
| two accumulators: h(x, 0, 0) = 3x | not proven | proven, 187 ms | h(x, a, b) = a + b + 3x, below it |
| three functions in a ring: a(x) <= x | not proven | proven, 58 ms | b(y) <= y, beside it |
| one function read through another: a(x) <= 2x | not proven | proven, 426 ms | b(y) = y, below it |
| an exchange: ex(x, y) <= 5 (six tokens buy a coin, a coin sells for five) | not proven | proven, 77 ms | rank 11·x + 2·y |
| counting up to a square: up(i, n) >= n·n | not proven | proven, 252 ms | rank n·n − i |
| loop: two phases | not proven | proven, 394 ms | rank (x, y) |
| loop: three phases | not proven | proven, 2,415 ms | rank (x, y, z) |
| loop: every other turn | not proven | proven, 900 ms | rank 2·x − p, p <= 1 |
| loop: gcd by subtraction, no invariant | not proven | proven, 1,265 ms | rank a + b, 1 <= a, 1 <= b |
| loop: a triangle (y from x − 1 again as x drops) | not proven | proven, 314 ms | rank (x, y) |
| loop: an exchange | not proven | proven, 403 ms | rank 11·x + 2·y |
| loop: counting up to a product, while i < N·M | not proven | proven, 391 ms | rank M·N − (i + 1) |
| rule: ninety-one (McCarthy's function, known by its facts) | not proven | proven, 1,752 ms | f(k) = 91 for k <= 101 |
| rule: doubling (a function given by its recurrence's facts) | not proven | proven, 152 ms | twice(k) = 2·k |
| rule: capped fill (fill(k, c), two arguments, known by its equation): the level at most the steps | not proven | proven, 122 ms | fill(k, j) ≤ k |
| liveness: batches, rank left out | not proven | proven, 709 ms | rank (waiting, items) |
| liveness: a pipeline (inbox to outbox, then shipped) | not proven | proven, 347 ms | rank 2·inbox + outbox |

All 21 broken variants (a false claim, a hypothesis dropped so the equation no longer determines the function, a coin
that sells for six so the exchange trades forever, a loop that never ends, a count that stops at N, a rule reading
past the region or one step ahead, a liveness whose helpful request stalls) are refused by both. The proofs found are
checked again in Lean: the suite's `lean-cycles` (the claims and rules, the capped fill's lemma among them) and
`lean-cycles-loops` (each loop's halting and each liveness with the rank found, through Live.lean), and `foundpyramid`
in `lean-package-3` (`runs/modal/ranks/suite1`, every job passing; at 0.19.0, `runs/modal/cycsearch/lean2` and, for
Ackermann's, `runs/modal/merge/ack1`). Nothing in the kernel or the Lean twin changed.

Against 0.19.0 (38019b6) in the same wave, three runs of each earlier item's frontier on each (`runs/modal/ranks/corpus3`,
the `rep-*` jobs): every proven item within the runs' spread (medians 0.48 to 1.26 of 0.19.0's; three phases 2,189 ms
against 2,490 ms, ninety-one 1,736 ms against 1,958 ms, every other turn 968 ms against 846 ms). Two broken variants
are refused later, the degree-2 search they now try: three phases with y reset 4,929 ms against 2,809 ms, two phases
with x never dropping 555 ms against 149 ms.

Not found:
- a rank needing two products at once (x·y + y·z) or a product of degree 3; for claims, a product the claims don't
  read; for a liveness, any rank past linear (its search is the linear one, with the exact LP);
- a coefficient the runs' size forces: one that a solution on the smaller half of the runs doesn't keep (a rank whose
  coefficient grows with the values the runs reach, which no larger run would confirm, is refused on purpose);
- a back-edge at a term no goal reads after unfolding the facts twice;
- a generalization whose conclusion isn't an exact linear fit (a closed form with products: the accumulator
  g(k, c) = g(k − 1, c + k), whose g(x, 0) is x(x + 1)/2);
- for a function of two arguments, a bound past 0, k, j and k + j plus a constant; and its facts as a base case at a
  constant argument (g(0, c) = 0 beside g(k + 1, c) = ...): the read g(0, j) and the goal's g(k, j) at k = 0 are reads
  at keys (0 + j)² + j and (k + j)² + j, which the kernel's congruence, linear over the monomials k·k and k·j, doesn't
  equate (an equation over the whole domain, as Ackermann's and the capped fill's, is found).

## Datatype track: `proveData`

`core/data.ts` (`gdp-wired/data`) takes recursive datatypes as values. A user declares a datatype by its constructors
(`data('List', {nil: {}, cons: {head: nat, tail: self}})`; a field a natural, the datatype, a datatype declared before
it, or one of a group declared together: `mutual({Rose: {node: {value: nat, kids: 'Forest'}}, Forest: {nil: {}, cons:
{head: 'Rose', tail: 'Forest'}}})`), functions over it by structural recursion (`define`, checked: every call within a
ring of functions calling each other passes a field of one parameter bound by a match, or the predecessor of a natural,
`n.match({zero, succ: ({pred}) => ...})`), or by well-founded recursion (a function whose calls are on any arguments,
taken once a measure is proven to fall at each call: below), and laws about them (`law`); nothing else. Every natural is a value of each datatype (a bijection Lean's twin defines), so a value is a natural and two
values are equal when they are the same natural; a datatype is read through maps (its tag, its fields, its size), a
constructor with fields and a function of several arguments through maps read at the arguments' pairing
((a + b)² + b, as the library reads a function of several arguments). The facts: each datatype's shape (the tag one of
the constructors', under each the size and the other constructors' fields 0) and eta (a value is its constructor at its
own fields), each constructor's fields, each function's body (a match read as ifs on the tag), and that a map is a
function (equal arguments, equal cells). Nothing is new to the kernel or to `Cyclic.lean`; the prover (untrusted) leaves
two reads at pairing keys uncompared while a datatype proof grows (`pairedKeys`: their congruence is a fact, and
comparing the keys only brings products into leaves the linear rows decide).

The search, untrusted, finds the cycle:

- **Which induction.** Structural induction on each argument of a datatype (the uses at its fields, where the tag is
  the constructor's), and recursion induction from each recursive function the law calls on its variables (the uses at
  the arguments of its own recursive calls, other arguments changing with them; on a natural n at n − 1). The rank is
  (level, size of the argument, 0 or 1), a natural's size itself. On an argument of a group's datatype, mutual
  induction: the law and a companion for each other datatype its fields reach, the law lifted through each function's
  own call at such a field (`rsize(rmirror(t)) = rsize(t)` at a forest is `fsize(fmirror(ts)) = fsize(ts)`), each node
  using the one of each field's datatype at that field, its rank that datatype's size.
- **Cases.** The law's node uses one node per case (a decision tree over the guards the unfolded definitions evaluate,
  split where 240 random values disagree), each with only what its case needs: the definitions unfolded at the calls
  its conclusion makes (one or two deep, and where an argument equals a constructor's value), the instances the models
  of the case reach, and the congruences the explanations of their classes use (proof-producing congruence closure in
  each model: a value's read explained against another of its class, through no constant first).
- **Lemmas.** Where the law alone isn't proven, conjectures from the values (theory exploration): equations between
  terms of the law's functions over two variables of each sort, up to six symbols, met by 80 random values, each named
  canonically, none ground, none the law, none following by rewriting with the definitions and smaller equations; and
  that a function keeps a predicate (under a comparison of two naturals). Those a read of the law's goal matches go
  first; each is proven the same way (one unfolding, then two) at a lower level, and the law is tried again with it,
  its uses at the reads its largest side matches (argument by argument, up to the classes, and only where a random
  value makes them equal): four of a lemma as found, then the rest ranked by the models in which the lemma's read is
  the goal's, one per set of values, and each case node keeping four of a lemma among those its models meet.
- **Through the built-ins** (`core/transfer.ts`), where the law alone at one unfolding isn't proven: its calls to
  functions that aren't recursive unfolded, and a recursive function of one or two naturals that computes a built-in
  (+, ∸, min, max, ≤, <, =, ≥, >, ≠, x + 1, x ∸ 1, 2·x, x = 0) at every argument up to 6 bridged to it once its bridge
  law (the function is the built-in, everywhere) is proven by the search; a function that reaches one is copied with
  the built-in in its place, the copy's law (f = its copy) a node made from the two bodies (or the search's). The law
  said through them is proven by the search, and the law as stated by one more node using it, each bridge and copy law
  at the calls it reads and the congruences between them: all nodes of the one cyclic proof, read by Lean as any other.
  Without induction last: the law by the cases of a variable, its definitions unfolded.

`today` is what the library proves of the same law with the same facts, without the search: the kernel's prover on
the law with the definitions unfolded and no cycle, and `findCycles` with the maps' values on the codes and that a
value's fields have smaller codes (so a rank linear in the codes exists). Each broken variant must be refused. Modal,
2 vCPU a job, `runs/modal/dataplus/corpus1` (`frontier-datatype-0..5`; the lemmas found as the search reports them, the
`data` job of the same run):

| Law | Today | Frontier | Found |
| --- | --- | --- | --- |
| length(append xs ys) = length xs + length ys | not proven | proven, 576 ms | recursion of append on xs |
| append is associative | not proven | proven, 2,283 ms | recursion of append on xs |
| reverse(reverse xs) = xs | not proven | proven, 25,991 ms | recursion of reverse on xs, with reverse(append(xs, [n])) = n :: reverse(xs) |
| map fusion: map f (map g xs) = map (f ∘ g) xs, any f and g | not proven | proven, 699 ms | recursion of map g on xs |
| length(map f xs) = length xs | not proven | proven, 211 ms | recursion of map f on xs |
| mirror(mirror t) = t | not proven | proven, 1,069 ms | recursion of mirror on t |
| size(mirror t) = size t | not proven | proven, 564 ms | recursion of mirror on t |
| sum(flatten t) = the tree's sum | not proven | proven, 11,859 ms | recursion of flatten on t, with sum(cons(sum(xs), ys)) = sum(append(xs, ys)) |
| sorted xs → sorted (insert x xs) | not proven | proven, 42,660 ms | recursion of sorted on xs, two unfoldings deep |
| count y (insert x xs) = count y xs + (1 if x = y) | not proven | proven, 2,960 ms | recursion of insert on xs |
| length(insert x xs) = length xs + 1 | not proven | proven, 416 ms | recursion of insert on xs |
| bst t → bst (insert x t) | not proven | proven, 20,081 ms | recursion of bst on t, with allBelow(t, v) ∧ x < v → allBelow(insert(x, t), v) and the allAbove one |
| rose tree: sum(flatten t) = the tree's sum | not proven | proven, 15,426 ms | mutual structure of t (its forest's sum(fflat ts) = fsum ts), with the sum of an append as above |
| rose tree: size(mirror t) = size t | not proven | proven, 16,450 ms | mutual structure of t (fsize(fmirror ts) = fsize ts), with fsize(snoc(ts, r)) = fsize ts + rsize r |
| lists of lists: length(concat b) = the lengths' sum | not proven | proven, 5,628 ms | recursion of concat on b, with length(append(xs, ys)) = length xs + length ys |
| length(replicate n x) = n | not proven | proven, 139 ms | recursion of replicate on n |
| append(take n xs, drop n xs) = xs | not proven | proven, 1,146 ms | recursion of take on n |
| length(drop n xs) = length xs − n | not proven | proven, 3,639 ms | recursion of drop on n |
| length(merge xs ys) = length xs + length ys (well-founded: (size xs, size ys)) | not proven | proven, 4,362 ms | recursion of merge on xs, ys |
| length(interleave xs ys) = length xs + length ys (size xs + size ys) | not proven | proven, 1,321 ms | recursion of interleave on xs, ys |
| add3acc x y z = x + y + z (an accumulator: (x, y)) | proven, 336 ms | proven, 132 ms | recursion of add3acc on x, y |
| length(merge xs ys), the measure stated (size xs + size ys) | not proven | proven, 4,981 ms | recursion of mergeSum on xs, ys |
| quicksort [x] = [x] (its calls on filters of the tail) | proven, 3,503 ms | proven, 3,351 ms | no induction |

The 12 broken variants are refused by both, each with a value that breaks it (4 to 17 ms): an append that drops the
head, a reverse that repeats it, a mirror that adds 1 to a value, an insertion that puts the item first, a search tree
insertion that goes the wrong way, the search tree law with its hypothesis dropped (an insertion into any tree), a
rose flatten that drops the node's value, a rose mirror that drops a tree, a concatenation that drops the first list,
a replicate with one more, and a drop of one too many (in the law of take and drop and in the length after a drop).
The well-founded items' rows are `runs/modal/wfrec/suite2`'s (the others `corpus1`'s), with 6 more variants refused by
both: a merge that drops an item (108 ms) and an add3acc that forgets one (49 ms), each with a value that breaks it;
and 4 definitions that don't terminate, refused before their law is read, the reason the measures tried (7 to 168 ms): a
merge that calls itself on the same lists, an interleave that only swaps them, an add3acc that doesn't lower y, and the
merge with the measure size xs stated, which its second call doesn't lower.

**Well-founded recursion.** A function whose recursion isn't structural (one function; a ring of them must be
structural) is taken once its termination is proven: a measure, a lexicographic tuple of components each a sum of
parameters' sizes (a natural's itself, a datatype value's its size) plus a constant, the user's (`define(..., {measure:
['xs', 'ys']})`) or the first of a parameter's size, a lexicographic pair or triple, a sum of two or all, and the LP's
rank over the function's runs (core/cycles.ts's `ranksOfRuns`) that its runs don't contradict; then for each call, a law
over the path's variables (a match on a variable is the variable at the case's constructor, an if's condition a
hypothesis) that the measure at the call's arguments is below the measure at the parameters, proven by the kernel in a
program without the function (one node first, the definitions unfolded once; else proveData's induction: a quicksort's
call on a filter of the tail by the filter's own recursion). Only then is the function's equation a fact: its body reads
it only below the argument's measure, so it has exactly one solution (Data.lean's `wf_fix_unique`), and `f(x) = f(x) + 1`
(no solution) is refused. A law over it is tried by its own call graph (functional induction), each use at a recursive
call's arguments under the call's path (its ifs too), ranked (level, the measure, 0 or 1). Lean: the function with
`termination_by` the measure (`Lx`, a tuple ordered by `lexLt`) and `decreasing_by` omega over the match equations; an
obligation that reads other functions a lemma before it, by induction on the variable the kernel inducted on
(`dataqsort.qsort_dec1`). `datamerge.len_merge`, `datainterleave.len_interleave`, `dataadd3acc.add3acc_sum`,
`datamergestated.len_merge_stated`, `dataqsort.qsort_single`: standard axioms only (`lean-data-7`, `runs/modal/wfrec/suite2`).

The search tree's insertion was out before for want of a lemma's use, not of the lemma: with both lemmas given it
stayed unproven, its search over at 183,819 ms with a case node satisfiable (`runs/modal/dataplus/prof1`, `bst-given-long`).
The goal's reads matched the allAbove lemma at four places a model can make equal, each at the left subtree (through
the classes of every branch of the insertion at once), and the four kept of a lemma were those; the use at the right
subtree, which the insertion's other side needs, wasn't among them. Ranked by the models where the lemma's read is the
goal's, and kept per case among those its models meet, it is there: the law is proven in 20,081 ms above and in
19,415 ms in the same run's `data` job, every other law of examples/data.ts still proven there.

The lemmas found are the classic ones: `reverse(append(xs, [n])) = n :: reverse(xs)` for reverse of reverse, the sum
of an append for the sum of a flattened tree (stated as `sum(cons(sum(xs), ys)) = sum(append(xs, ys))`, with
`sum(append(xs, [0])) = sum(xs)` proven before it and used), and for the rose mirror the size of a forest with one tree
more at its end. Every proven law is checked in Lean (the suite's `lean-data-0..5`, `runs/modal/dataplus/corpus1`, the
standard axioms only) as a theorem about the datatype as declared: `lean-kernel/data.ts` writes the datatypes as Lean
`inductive`s (a group as one `mutual` block) and the functions by pattern matching (a ring of them in a `mutual` block),
a bijection between each datatype and the naturals (`enc`, `dec`, with `dec_enc` and `enc_dec`, from Data.lean's
`cun`/`cpair`; a group's decodings well-founded by (group size + 1)·n plus an order that puts a datatype decoding n at
fields up to n after the datatypes those fields name), the model (each map as the facts say it is), proves every fact
of the proof true of the model, and states the law about the Lean definitions:
`datarev.reverse_reverse (xs : List) : reverse (reverse xs) = xs`,
`databst.bst_insert (x : Nat) (t : Tree) : bst t = true → bst (bstInsert x t) = true`,
`datarosemirror.rsize_rmirror (t : Rose) : rsize (rmirror t) = rsize t`,
`datatakedrop.take_drop (n : Nat) (xs : List) : append (take n xs) (drop n xs) = xs`.

`core/cycles.ts`'s `findCycles` doesn't take these laws (its `today` above): it fits ranks linear in the variables
from runs over a grid of naturals, but a list's code squares with each item (codes past 2^53 after a few), so the runs
give it no edge; its back-edges go to every call the goal reads (`xs := append(xs, ys)` among them); and its goals
lean on the kernel's own congruence, which over pairing keys splits on products. The datatype search keeps its own
cycle builder for that reason; the two share the kernel, `proveCyclic` and the corpus.

Not found in general: a termination whose decrease needs a lemma the obligations' search doesn't find without
conjectures (a heap sort's `toList (hmerge p q)`, a bubble sort's passes, a merge sort's halves), nested recursion (a
call in its own argument or condition), a ring of functions that isn't structural; a lemma past six symbols or of another shape than an equation or a kept predicate; an induction
on a term no recursive call makes; a companion of a mutual induction that the functions' own calls don't lift the law
to (a law reading a rose tree other than through functions recursing on it, or a function whose call at a forest isn't
one call with its own parameters); a recursion through a ring of functions that is a recursion induction rather than a
structural one (the ring's calls give no use; mutual structural induction does); and nested datatypes in Lean's sense,
a field of a type applied to the datatype itself (`List Rose`): there is no type parameter, so a list of trees is a
forest declared with them.

### Reachability through a structure that changes

Still out, and why precisely. A datatype here is a value: no sharing, no mutation, every function a fold over it. A
rule may hold such a value in its state and replace it at each step (a sorted list a request inserts into, its laws
those above), but a linked structure a rule mutates is a heap: a map from addresses to cells whose links the step
rewrites, aliasing and cycles allowed. Reachability there is a least fixpoint over a map that changes: "y is reachable
from x" is an existential (some path), not a structural recursion (the heap has no decreasing argument; with fuel it is
recursion on a natural, which the datatype search now takes, though not over a map that changes), and the step's law needs a frame lemma about every
path not through the written cell, an induction on the path's length inside the induction over the run's steps. The
cyclic kernel can state that (a node ranked (t, n), lexicographic), but no instance builds such nodes, and the
witness a step's new path needs (the path the law claims after the write) is a term no fact names.
