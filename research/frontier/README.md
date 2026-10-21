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
| all | 54 | 0 | 54 |

Now: the suite's `frontier-score` job, `runs/modal/cycsearch/suite1` (54 / 54, and the cycle track's 13 broken variants
refused; the cycle track's times: `runs/modal/cycsearch/corpus1`). The last, `(Σx)² <= n·Σx²` over running samples, is
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

What stays out: reachability through a structure that changes, and recursive datatypes as values.

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
