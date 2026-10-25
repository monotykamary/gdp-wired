# Reading verdicts

Every prove call returns `{proven, checked, goal?, stuck?, witness?, why?}`; `proveRule` and `proveSteps` add `found`
when they proved the laws with what they looked for themselves, and `assumes` when that proof holds only in states
reachable from the start.

| Verdict | Meaning | Do |
|---|---|---|
| `proven: true, checked: true` | The kernel checked a proof of every goal. | Done. Keep the broken variant as a test. |
| `proven: true, checked: false` | The prover's tree was rejected by the kernel. | A bug in gdp-wired: report it with the rule. Never ship on this. |
| `stuck: 'sat'` at `<law> @start` | The law is false in the start state for the witness's params. | Fix the start state, the law, or add `.pre` if those params are impossible. |
| `stuck: 'sat'` with a `witness` and no `run`, at `@step law` | A state the laws allow (maybe one no run reaches) from which one step breaks the step law, and the search (on by default) found neither a run to it nor the law that rules it out. | Fix the rule, or add the law that rules the state out (the step law then holds from the states it allows). |
| `stuck: 'sat'` with `run` | A few random runs found a real run from the start that breaks the law: `run.params` and each request in `run.trace`. | The rule (or the law) is wrong. Replay the run with `rule.interpreter()`. |
| `stuck: 'sat'` at `<law> @step` | Some state where the laws hold steps to one where this law fails. The witness may be unreachable. | Run `search` (below). |
| `proven: true, checked: true` with `found` | Proven with laws or lemmas nobody stated, which `proveRule`/`proveSteps` found when the prover alone stopped: `found.laws` (pass them with yours), `found.lemmas` (per function or list, the lemmas to state). | Paste them, so the next proof needs no search. |
| `proven: true, checked: true` with `assumes: {states: 'reachable', laws}` | Proven in every state a run from the start reaches, not in every state the laws allow. The proof needed invariants the search found (`laws`, their texts), each proven from the start, or k-induction (`laws` empty, `k` set). A step law holds from every reachable state; from a state no run reaches it may fail. | Fine when the rule only ever steps from states its own runs reached. If the code steps it from states it is handed (a host's, a stored state it doesn't check), prove with `{from: 'any'}` and require `proven && checked && !assumes`. |
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
- **No run:** the law is probably true but not inductive: the witness is a state no run reaches. The search the prove
  calls run by default looked for the fact and didn't find it (`why` says so). Find the fact that rules that state out and add it as another law in the same call (`proveRule(r, [helper, law])`); the laws are
  proven together. Example: gcd's rank only drops if `a >= 1` and `b >= 1` are laws too.

Reading a witness: names are the goal's variables. `Day[day:1]` is the map
`Day` read at key `day` before the step; `k$...` / `key$...#` are the key a
`forall` law was checked at. A witness from `@step` is a state, not a run.

## Never

- Weaken the law that matters to make it pass. Add the helper law instead.
- Loosen `.assume` to hide a bug: an assumption is a claim about every request the code will ever see.
- Treat "the search found nothing" as a proof.
- Read a verdict with `assumes` as a proof for states your runs never reached.

## From any state: `{from: 'any'}`

A law is a claim about the states a run from the start reaches, and the search proves it with whatever holds there.
Code that steps the compiled rule from a state it is handed (a host's, a stored one it doesn't check) needs more: every
step law must hold from every state the laws allow, reachable or not, and the laws must be kept by every step from such
a state.

```ts
const v = proveSteps(rule, laws, stepLaws, {from: 'any'})
if (!(v.proven && v.checked && !v.assumes)) throw new Error(`not proven from every state: ${v.goal} ${v.stuck}`)
```

With `{from: 'any'}` the search still looks for runs that break the laws and for lemmas about the rule's functions and
lists (true in every state), never for an invariant. A step law broken from a state the laws allow comes back
`stuck: 'sat'` with that state as `witness`, reachable or not. Add the law that rules it out only if the code really
never hands the rule such a state. `{search: false}` gives the same answer without the search.
