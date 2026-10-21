# The Lean handoff

Every proof gdp-wired finds can be checked again by Lean, against a Lean twin of
the kernel whose soundness is proven there. And a claim gdp-wired can't decide
goes to Lean as a function with proven facts, which the rule then uses.

## Export the proofs

```ts
import {leanProject, toLean} from 'gdp-wired/lean'

const file = toLean([
  {id: 'budget', machine: budget.machine, laws: [bounded]},
  {id: 'caps', machine: caps.machine, laws: [dayCap], stepLaws: [onlyUp, once, twice]},
  {id: 'tickets', machine: tickets.machine, laws: [noneEarly], liveness: [everyTicket]},
])
const project = leanProject(file) // {'Proofs.lean', 'lakefile.lean', 'lean-toolchain', ...the twin}: write it out, `lake build`
```

Each law comes as the twin's theorem and as a plain statement over named
variables, e.g. `theorem law0 (h : SReach budget_machine ρ μ) : ρ «s» ≤ (ρ «b» + ρ «m»)`,
for a Lean development to cite. Lean 4.34.0, core only, standard axioms.

`toLean(items, {native: true})` closes each check by `native_decide` instead of `decide +kernel`: several times faster
on a large certificate (a 64-step law in about 6 s instead of 49), but each theorem then also rests on an axiom of its
own (`#print axioms` names it, `…_native.native_decide.ax_…`), which trusts Lean's compiler and runtime. Use it while
iterating; keep the default for what you publish or cite.

## State the lemma instead

When the function is a recurrence on one natural and you can say what it needs, `recur` defines it by the recurrence
and proves the lemmas by induction itself; the rule then uses them as facts:

```ts
const delay = recur('delay', {zero: 1, next: (_, d) => min(d.times(2), 64)}, {
  'at least 1': (_, d) => d.atLeast(1),
  'at most 64': (_, d) => d.atMost(64),
})
const retry = rule('retry').inputs({failed: bool, now: nat}).state({tries: 0, next: 0, last: 0}).fns({delay})
  .assume(({now, last}) => now.atLeast(last))
  .step(({failed, now, tries, next, delay}) => ({tries: when(failed, tries.plus(1), 0), next: when(failed.and(now.atLeast(next)), now.plus(delay(tries)), next), last: now}))
proveRule(retry, [retry.law('the next try is at most 64 after the last request', ({next, last}) => next.atMost(last.plus(64)))]) // proven
```

- The lemmas are proven when `recur` runs, all together (one may lean on another, as laws do); one that fails throws
  `Unproven` with the induction step it breaks at (`verdict.witness`, over x and fx). That step need not be a real
  value of f: a lemma that holds but isn't inductive by itself needs a helper lemma beside it, as a law does.
- Without the lemmas the same law isn't proven: the two equations say nothing about the delay at an unknown attempt.
- `toLean` defines `Recur.delay` by the same recurrence and checks the kernel's own proof of `Recur.delay_lemmas`: the
  machine the lemmas were proven by, with its trees, and its run reaching x and f(x) (a lemma with a product, f(x) =
  x·x, goes through as the kernel proved it); then the rule's facts from it: nothing is left as a hypothesis.
- Further arguments (`args: ['cap']`, up to four, fixed along the recursion), functions the step and the start read
  (`fns: {rem: modBy(7)}`, another recurrence), and laws between two points (a fourth argument, `(x, fx, y, fy, env) => ...`, for
  every x <= y, proven by induction on y with the lemmas):

  ```ts
  const filled = recur('filled', {args: ['cap'], zero: 0, next: (_, f, {cap}) => min(f.plus(1), cap)},
    {'within the capacity': (_, f, {cap}) => f.atMost(cap)}, {'never drains': (_, f, __, g) => f.atMost(g)})
  ```

  In Lean a function of several arguments is `Recur.<name>_rec` with its key's function `Recur.<name>` beside it (the
  builders pair the arguments as (a + b)² + b; `Recur.pair_inj` proves that injective). A fact about several keys goes to
  the twin as one (`pfacts`), given at every value of its further keys and assumed at the tuples the proof names, as a
  law about several keys is; `<id>_pfacts_hold` proves it of the definitions.
- A recursion that isn't on a natural (a tree, a list as a value), or a lemma that isn't by induction from 0 or
  between two points, is the next section.

## Hand a claim to Lean

When a law needs induction over a recursive structure, or arithmetic with
products of unknowns past products of facts and sums of squares, the kernel
won't invent the proof. Define the function in
Lean, state the facts the rule needs, and give the rule the function:

```ts
const room = rule('handshakes').inputs({}).state({people: 0, shakes: 0})
  .fns({pairs: fn(1, 'x => x * (x - 1) / 2 + 0', {lean: 'pairs', facts: f => ({
    'pairs 0 = 0': f(0).eq(0),
    'pairs (x + 1) = pairs x + x': forall(x => f(x.plus(1)).eq(f(x).plus(x))),
  })})})
  .step(({people, shakes}) => ({people: people.plus(1), shakes: shakes.plus(people)}))
// laws about `pairs(people)` are proven from the facts; toLean with
// lean: {defs: 'def pairs : Nat → Nat\n  | 0 => 0\n  | n + 1 => pairs n + n', simp: ['pairs']}
// proves the facts of the Lean definition.
```

The kernel only ever assumes the facts. A function without a `lean`
definition has its facts stated as hypotheses of the exported theorems.

## When to hand off instead of forcing it

- The claim is about every prefix, subtree or element of a recursive value you define.
- The proof needs a lemma nobody stated, or one `recur` can't take (a recursion that isn't on a natural).
- The claim multiplies unknowns beyond multiplying two known facts.
- You need to ship an arbitrary algorithm as its proved source: that is Bend.

Don't bound the structure (lists of at most 3) and call the claim proven.
