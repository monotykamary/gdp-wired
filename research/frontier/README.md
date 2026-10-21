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

## The corpus

`corpus.ts` holds laws that gdp-wired proves only when the statement the proof needs is given, with that statement taken
out: research/synth's machines without their invariant, examples/lemmas.ts's rules with no lemma, examples/invoices.ts's
ledger with no fold lemma. Each item has `today` (the library now) and, once its track has one, `frontier`.

    bun research/frontier/score.ts [--track lemma] [--limit 60] [--json runs/frontier/<name>.json]

Every item is proven by today's library with the statement put back (the examples and research/synth show it), so
none of them is false; today proves none of them without it.

## Structure: path scopes, the case the docs called the wall

`scopes.ts` takes pi-fabric's resource patterns (`<ns>:<path>`, `/*`, `/**`, `<ns>:*`) and its `covers`, the check its
scope attenuation rests on, with a pattern's segments as a carried map from positions to interned names and its length
an input. Nothing is stated beyond the laws; each is proven and checked by the kernel:

| Law | Faithful | Broken variants |
| --- | --- | --- |
| covering is transitive | proven, 450 ms | `/*` covering `/**`: refuted |
| a pattern covers itself | proven, 46 ms | |
| what a covered pattern matches, the covering one matches (matching written apart from `covers`) | proven, 2,575 ms | the prefix skipped: refuted; `/*` covering `/**`: refuted |
| what a derived scope allows, its parent allows (scopes as lists of grants with actions, the two "some grant"s as witnesses) | proven, 992 ms | the actions ignored: refuted |

The encoding agrees with pi-fabric's own `covers` on 20,000 random triples of patterns, and the grant tables with its
grant checks on 5,000 random pairs of scopes (`compareScopes`, `compareGrants`). Prefixes of lists of paths needed no
induction once a list is positions and a length. What stays out: normalizing a scope (merging and sorting grants is a
permutation), reachability, recursive datatypes as values.
