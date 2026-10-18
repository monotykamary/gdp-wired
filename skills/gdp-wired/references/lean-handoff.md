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

## Hand a claim to Lean

When a law needs induction over a recursive structure, or arithmetic with
products of unknowns, the kernel won't invent the proof. Define the function in
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
- The proof needs a lemma nobody stated.
- The claim multiplies unknowns beyond multiplying two known facts.
- You need to ship an arbitrary algorithm as its proved source: that is Bend.

Don't bound the structure (lists of at most 3) and call the claim proven.
