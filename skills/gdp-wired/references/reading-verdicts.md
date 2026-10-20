# Reading verdicts

Every prove call returns `{proven, checked, goal?, stuck?, witness?, why?}`.

| Verdict | Meaning | Do |
|---|---|---|
| `proven: true, checked: true` | The kernel checked a proof of every goal. | Done. Keep the broken variant as a test. |
| `proven: true, checked: false` | The prover's tree was rejected by the kernel. | A bug in gdp-wired: report it with the rule. Never ship on this. |
| `stuck: 'sat'` at `<law> @start` | The law is false in the start state for the witness's params. | Fix the start state, the law, or add `.pre` if those params are impossible. |
| `stuck: 'sat'` at `<law> @step` | Some state where the laws hold steps to one where this law fails. The witness may be unreachable. | Run `search` (below). |
| `stuck: 'unknown'` with `why` | The prover's budget ran out. `why` says which limit and what helps. | Usually: fewer steps in a k-step law, or split a law into laws about fewer conditions. |

## A failed step: bug, or missing invariant?

```ts
import {search} from 'gdp-wired/machine'
search(uncapped.machine, bounded)          // {params: {b: 1, m: 0}, trace: [{c: 2}]}
search(uncapped.machine, bounded, 6, 4)    // deeper (requests) and wider (values) when nothing turns up
```

The bound widens naturals; a choice, a yes/no or an `upTo` of at most 15 is always tried at every value it may take.

- **A run comes back:** it is a real sequence of requests from the start that breaks the law. The rule (or the law)
  is wrong. Replay it with `rule.interpreter()` to see each state.
- **No run:** the law is probably true but not inductive: the witness is a state no run reaches. Find the fact that
  rules that state out and add it as another law in the same call (`proveRule(r, [helper, law])`); the laws are
  proven together. Example: gcd's rank only drops if `a >= 1` and `b >= 1` are laws too.

Reading a witness: names are the goal's variables. `Day[day:1]` is the map
`Day` read at key `day` before the step; `k$...` / `key$...#` are the key a
`forall` law was checked at. A witness from `@step` is a state, not a run.

## Never

- Weaken the law that matters to make it pass. Add the helper law instead.
- Loosen `.assume` to hide a bug: an assumption is a claim about every request the code will ever see.
- Treat "the search found nothing" as a proof.
