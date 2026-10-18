---
name: gdp-wired
description: Prove the laws of stateful rules in TypeScript with gdp-wired, an automatic prover (no proof to write, every proof checkable again in Lean). Use when adding, changing or reviewing a budget, cap, quota, rate limit, sliding window, workflow, ledger, access policy or any state machine whose invariants matter; when code imports from 'gdp-wired'; when a law comes back refuted or unproven; or when deciding whether a claim belongs to gdp-wired, Lean or Bend.
---

# gdp-wired

A rule is a state machine: params, a request's inputs, state, and one step.
A law is a claim about every run of it. `proveRule(rule, [law])` either
proves the law (a kernel checks the proof tree; nothing to write) or says
where it fails, and a search turns a false law into a real run.

```ts
import {min, nat, proveRule, rule, when} from 'gdp-wired'
import {search} from 'gdp-wired/machine'

const budget = rule('budget')
  .params({b: nat, m: nat})
  .inputs({c: nat})
  .state({s: 0})
  .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))
const bounded = budget.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))

proveRule(budget, [bounded]) // {proven: true, checked: true}

const uncapped = budget.step(({b, c, s}) => ({s: when(s.lt(b), s.plus(c), s)}))
proveRule(uncapped, [bounded]) // {proven: false, goal: 'spend stays within b + m @step', stuck: 'sat', witness: {...}}
search(uncapped.machine, bounded) // {params: {b: 1, m: 0}, trace: [{c: 2}]}
```

It decides laws about stateful rules over naturals, maps, sets and logs.
Recursion it would have to invent a lemma for belongs to Lean or Bend
([where it fits](references/where-it-fits.md)).

## Workflow

When adding or changing a rule whose invariants matter:

1. **Write the rule as the code does it.** One `rule(...)` with the same
   params, inputs, state and step as the production code. Use kinds for what
   isn't a natural (`bool`, `oneOf`, `maybe`, `int`, `decimal`, `str`), maps
   for per-key state, `.log` for histories ([writing rules](references/writing-rules.md)).
2. **State the laws a reviewer would ask about.** Invariants with `law`
   ("no day passes its cap"), one-step facts with `stepLaw` ("a balance only
   goes down"), k steps with `stepsLaw`, "eventually" with `leadsTo`,
   request-only facts with `decide`. One claim per law, named as a sentence.
3. **Prove.** `proveRule`, `proveSteps`, `proveLeadsTo`, `proveDecision`,
   `proveLoop`. Require `proven && checked`; `checked` is the kernel's verdict
   on the tree the untrusted prover grew.
4. **When it fails, read the verdict before changing anything**
   ([reading verdicts](references/reading-verdicts.md)). `stuck: 'sat'` at
   `@step` means the law isn't inductive: run `search` from the start. A real
   run is a bug in the rule (or the law); no run means the law needs a
   helper invariant, so add the missing law next to it, never weaken the one
   that matters.
5. **Never prove a different rule than the one that ships.** Ship the rule
   itself (`rule.compiled()`), or hold hand-written code to it with
   `rule.compare(reference)`; run `rule.crossCheck(laws)` in tests
   ([shipping](references/shipping.md)).
6. **Keep the broken variant.** Next to each proven rule, keep the bug it
   rules out (the uncapped budget) and assert it is refused. It is the
   cheapest regression test you will write.
7. **Hand off what it doesn't decide.** Recursive structure or products of
   unknowns: prove the function in Lean, give the rule the function with its
   facts, export with `toLean` ([Lean handoff](references/lean-handoff.md)).
   Don't approximate a recursive claim with a bounded one and call it proven.

## References

Read the one you need:

| File | Read it when |
|---|---|
| [`references/writing-rules.md`](references/writing-rules.md) | Writing a rule or a law: kinds, maps, flags, step laws, k-step laws, histories, liveness, decisions, pure functions, two-run laws, loops. |
| [`references/reading-verdicts.md`](references/reading-verdicts.md) | A verdict is not `{proven: true, checked: true}`: `stuck: 'sat'`, `stuck: 'unknown'` with `why`, a witness, a search result. |
| [`references/shipping.md`](references/shipping.md) | Running the proven rule in an app, encoding runtime values, holding existing code to the rule. |
| [`references/lean-handoff.md`](references/lean-handoff.md) | Exporting proofs to Lean, or a claim needs recursion or arithmetic the kernel doesn't decide. |
| [`references/where-it-fits.md`](references/where-it-fits.md) | Deciding whether gdp-wired, Lean or Bend should own a claim. |

## API

From `gdp-wired`:

| Export | What it is |
|---|---|
| `rule(name)` | A rule builder: `.params` `.inputs` `.state` `.maps` `.lists` `.carries` `.flags` `.step` `.pre` `.assume` `.fns` `.facts` `.log` `.sums` `.queries` `.keep` `.relations` `.prune`. |
| `nat`, `upTo(k)`, `bool`, `oneOf(...)`, `maybe(kind)`, `int`, `decimal(places)`, `str({like, maxLength})` | Kinds; state of any kind with `kind.from(init)`. |
| `r.law`, `r.stepLaw`, `r.stepsLaw`, `r.leadsTo`, `r.decide`, `r.relate` | Claims: invariant, one step, k steps (k ≤ 16), liveness, a decision about one request, a decision about two. |
| `proveRule`, `proveSteps`, `proveLeadsTo`, `proveDecision`, `proveLoop` | Verdicts: `{proven, checked, goal?, stuck?, witness?, why?}`. |
| `when`, `min`, `max`, `count`, `sum`, `all`, `any`, `not`, `forall`, `everyKey`, `someKey`, `relation` | Terms and conditions; terms have `plus` `minus` (truncated) `times(k)` `mul` `lt` `atMost` `atLeast` `gt` `eq`, conditions `and` `or` `not` `implies`. |
| `fun(name)`, `loop(name)` | Pure functions (`.returns`, `.law`, `.relate`, `.run`) and loops (`.while`, `.body`, `.rank`). |
| `fn(arity, js, {facts, lean})`, `divBy(c)`, `modBy(c)` | Functions known by their facts. |
| `r.compiled()`, `r.interpreter()`, `r.encodeParams`, `r.encodeInput`, `r.decode`, `r.crossCheck`, `r.compare` | Running and checking the rule. |

Also: `gdp-wired/machine` (`search`, `compileJs`, the interpreter), `gdp-wired/lean`
(`toLean`, `leanProject`), `gdp-wired/compose` (`product`, `interleave`,
`refinement`, `steps`, `ghost`), `gdp-wired/kernel`, `gdp-wired/prove`.
