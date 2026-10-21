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
| cycle | A cyclic proof's shape: each node's rank (linear, in order, from the runs by LP), where each back-edge returns, the companions a stuck claim needs (constants abstracted, bounds on what it reads); a loop's rank and the invariants it needs | The cyclic proof (`kernel/cyclic.ts`), the loop's halting goals |

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
| lemma | 5 | 0 | 5 |
| fold | 3 | 0 | 3 |
| nonlinear | 8 | 0 | 8 |
| cycle | 13 | 0 | 13 |
| datatype | 12 | 0 | 11 |
| all | 66 | 0 | 65 |

Now: the suite's `frontier-score` job, `runs/modal/cycsearch/suite1` (54 / 54, and the cycle track's 13 broken variants
refused; the cycle track's times: `runs/modal/cycsearch/corpus1`); the datatype track, its own `frontier-datatype-0..3`
jobs, `runs/modal/cycdata/suite1` (11 / 12, its 5 broken variants refused). The last, `(Σx)² <= n·Σx²` over running samples, is
proven by the prover multiplying the goal by n before the squares.

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
the other folds or the params (a product of a tree's value and a param among them), a closed form of degree 2 at most
fitted exactly, laws between two points. They are proven by the induction stated lemmas are proven by (Houdini: one not
proven is dropped, with every candidate the kernel's counterexample to induction breaks), then only what the laws need
is kept (each dropped in turn, with those that leaned on it). The rule comes back made again with them, and they come
back as source to paste. The kernel and the Lean twin are unchanged; `lean-kernel/package-check.ts` checks four of the
rules made again (`foundbackoff`, `foundarea`, `foundinvoices`, `foundorgchart`).

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
| fold/invoices | proven, 1,068 ms |
| fold/metered invoices | proven, 863 ms |
| fold/org chart | proven, 7,902 ms |

Not found: a lemma of another shape (a bound by a product of two unknowns other than a tree's value and a param, a
closed form past degree 2 or with further arguments, an exponential), and anything about a quantified state invariant
(examples/trees.ts's tables of nodes: the invariant track's).

## Cycle track: `findCycles`, `findRank`, `cycleLemmas`

`core/cycles.ts` (`gdp-wired/cycles`) searches for what core/cyclic.ts's builders fix by rule shape: from claims over
functions defined by their equations, the facts are run (values, and at each claim's samples the calls its goal
makes); back-edges go to a claim at the arguments of each call the goal reads, guarded by where that claim may be used
(its hypotheses and its rank below), so the premises and the descent are the guard's; the ranks are linear over each
claim's variables, an integer LP over the runs' edges (each sampled call must drop), lexicographic by successive
elimination; a stuck claim gets companions, its constants abstracted (an accumulator) below it or bounds on what its
goal reads beside it (Houdini, then only those it needs). Loops take their rank from their runs, `inferLaws` finding
the invariants the kernel's halting goals need (the descent as step laws). A rule reading functions known by their
facts gets lemmas fitted to their JavaScript and proven from the facts as cyclic claims. Nothing new is trusted.

`today` is what the library did before with the same statement: for claims, the builders' shape (rank x for each
variable x tried, back-edges at x − 1, the search's own fact instances); for loops, kernel/run-more.ts's rank templates
(a state variable, a param minus one, a sum of two); for rules, `proveRule`'s search with `cycles: false`. Each item
has a broken variant, which must be refused. Modal, 1 vCPU a job, `runs/modal/cycsearch/corpus1`:

| Item | Today | Frontier | Found |
| --- | --- | --- | --- |
| McCarthy's 91: f(n) = 91 for n <= 101 | not proven | proven, 107 ms | rank 101 − n, back-edges at n + 11 and f(n + 11) |
| Ackermann: ack(m, n) > n | not proven | proven, 439 ms | rank (m, n) |
| gcd by subtraction: >= 1 and <= x, for x, y >= 1 | not proven | proven, 863 ms | rank x + y |
| an accumulator: g(x, 0) = 2x | not proven | proven, 85 ms | g(x, a) = a + 2x, below it |
| two accumulators: h(x, 0, 0) = 3x | not proven | proven, 290 ms | h(x, a, b) = a + b + 3x, below it |
| three functions in a ring: a(x) <= x | not proven | proven, 88 ms | b(y) <= y, beside it |
| one function read through another: a(x) <= 2x | not proven | proven, 550 ms | b(y) = y, below it |
| loop: two phases | not proven | proven, 419 ms | rank (x, y) |
| loop: three phases | not proven | proven, 2,744 ms | rank (x, y, z) |
| loop: every other turn | not proven | proven, 885 ms | rank 2·x − p, p <= 1 |
| loop: gcd by subtraction, no invariant | not proven | proven, 1,362 ms | rank a + b, 1 <= a, 1 <= b |
| rule: ninety-one (McCarthy's function, known by its facts) | not proven | proven, 2,340 ms | f(k) = 91 for k <= 101 |
| rule: doubling (a function given by its recurrence's facts) | not proven | proven, 105 ms | twice(k) = 2·k |

All 13 broken variants (a false claim, a hypothesis dropped so the equation no longer determines the function, a loop
that never ends, a rule reading past the region) are refused by both. The proofs found are checked again in Lean
(`runs/modal/cycsearch/lean2`), Ackermann's, whose key reads a product of cells, too (`runs/modal/merge/ack1`).

Not found: a rank that isn't linear, or needs a coefficient past 4 in one component; a back-edge at a term no goal
reads after unfolding the facts twice; a generalization whose conclusion isn't an exact linear fit (a closed form with
products); bounds on a function of two arguments; a machine's liveness (`proveLeadsTo`) with no rank.

## Datatype track: `proveData`

`core/data.ts` (`gdp-wired/data`) takes recursive datatypes as values. A user declares a datatype by its constructors
(`data('List', {nil: {}, cons: {head: nat, tail: self}})`), functions over it by structural recursion (`define`,
checked: every recursive call passes a field of one parameter bound by a match), and laws about them (`law`); nothing
else. Every natural is a value of each datatype (a bijection Lean's twin defines), so a value is a natural and two
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
  the arguments of its own recursive calls, other arguments changing with them). The rank is (level, size of the
  argument, 0 or 1).
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
  value makes them equal).

`today` is what the library proves of the same law with the same facts, without the search: the kernel's prover on
the law with the definitions unfolded and no cycle, and `findCycles` with the maps' values on the codes and that a
value's fields have smaller codes (so a rank linear in the codes exists). Each broken variant must be refused. Modal,
2 vCPU a job, `runs/modal/cycdata/suite1` (`frontier-datatype-0..3`; the lemmas found as the search reports them, `runs/modal/cycdata/batch5`):

| Law | Today | Frontier | Found |
| --- | --- | --- | --- |
| length(append xs ys) = length xs + length ys | not proven | proven, 472 ms | recursion of append on xs |
| append is associative | not proven | proven, 3,003 ms | recursion of append on xs |
| reverse(reverse xs) = xs | not proven | proven, 25,699 ms | recursion of reverse on xs, with reverse(append(xs, [n])) = n :: reverse(xs) |
| map fusion: map f (map g xs) = map (f ∘ g) xs, any f and g | not proven | proven, 521 ms | recursion of map g on xs |
| length(map f xs) = length xs | not proven | proven, 251 ms | recursion of map f on xs |
| mirror(mirror t) = t | not proven | proven, 1,983 ms | recursion of mirror on t |
| size(mirror t) = size t | not proven | proven, 488 ms | recursion of mirror on t |
| sum(flatten t) = the tree's sum | not proven | proven, 9,067 ms | recursion of flatten on t, with sum(cons(sum(xs), ys)) = sum(append(xs, ys)) |
| sorted xs → sorted (insert x xs) | not proven | proven, 37,672 ms | recursion of sorted on xs, two unfoldings deep |
| count y (insert x xs) = count y xs + (1 if x = y) | not proven | proven, 3,953 ms | recursion of insert on xs |
| length(insert x xs) = length xs + 1 | not proven | proven, 391 ms | recursion of insert on xs |
| bst t → bst (insert x t) | not proven | not proven | |

The five broken variants (an append that drops the head, a reverse that repeats it, a mirror that adds 1 to a value,
an insertion that puts the item first, a search tree insertion that goes the wrong way) are refused by both, each with
a value that breaks it (4 to 9 ms).

The lemmas found are the classic ones: `reverse(append(xs, [n])) = n :: reverse(xs)` for reverse of reverse, and the
sum of an append for the sum of a flattened tree, which the search states as `sum(cons(sum(xs), ys)) =
sum(append(xs, ys))` (with `sum(append(xs, [0])) = sum(xs)`, proven before it and used). Every proven law is checked in Lean
(`runs/modal/cycdata/leandata1`, the suite's `lean-data-0..3`, the standard axioms only) as a theorem about the datatype as declared: `lean-kernel/data.ts` writes the
datatypes as Lean `inductive`s and the functions by pattern matching, a bijection between each datatype and the
naturals (`enc`, `dec`, with `dec_enc` and `enc_dec`, from Data.lean's `cun`/`cpair`), the model (each map as the
facts say it is), proves every fact of the proof true of the model, and states the law about the Lean definitions:
`datarev.reverse_reverse (xs : List) : reverse (reverse xs) = xs`,
`dataflatten.sum_flatten (t : Tree) : sum (flatten t) = tsum t`,
`datafusion.map_fusion (f g : Nat → Nat) (xs : List) : mapF f (mapG g xs) = mapFG f g xs`,
`datasorted.insert_sorted (x : Nat) (xs : List) : sorted xs = true → sorted (insert x xs) = true`.

`core/cycles.ts`'s `findCycles` doesn't take these laws (its `today` above): it fits ranks linear in the variables
from runs over a grid of naturals, but a list's code squares with each item (codes past 2^53 after a few), so the runs
give it no edge; its back-edges go to every call the goal reads (`xs := append(xs, ys)` among them); and its goals
lean on the kernel's own congruence, which over pairing keys splits on products. The datatype search keeps its own
cycle builder for that reason; the two share the kernel, `proveCyclic` and the corpus.

Not proven: the search tree's insertion keeping the order (`bst(t) → bst(insert(x, t))`). Its two lemmas
(`allBelow(t, v) ∧ x < v → allBelow(insert(x, t), v)` and the `allAbove` one) are found and proven; the law with them
is not, within its time. Not found in general: a lemma past six symbols or of another shape than an equation or a kept
predicate, an induction on a term no recursive call makes, mutual or nested datatypes (a field of another datatype, a
list of trees), and functions defined by recursion on a natural.

### Reachability through a structure that changes

Still out, and why precisely. A datatype here is a value: no sharing, no mutation, every function a fold over it. A
rule may hold such a value in its state and replace it at each step (a sorted list a request inserts into, its laws
those above), but a linked structure a rule mutates is a heap: a map from addresses to cells whose links the step
rewrites, aliasing and cycles allowed. Reachability there is a least fixpoint over a map that changes: "y is reachable
from x" is an existential (some path), not a structural recursion (the heap has no decreasing argument; with fuel it is
recursion on a natural, which the datatype search doesn't take), and the step's law needs a frame lemma about every
path not through the written cell, an induction on the path's length inside the induction over the run's steps. The
cyclic kernel can state that (a node ranked (t, n), lexicographic), but no instance builds such nodes, and the
witness a step's new path needs (the path the law claims after the write) is a term no fact names.
