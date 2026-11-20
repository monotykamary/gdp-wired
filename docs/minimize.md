# Minimizing refuting runs

`minimizeRun(rule, law, run, opts?)` shrinks a concrete counterexample run until
no single request can be removed while still breaking `law` on the original
`rule`. It is untrusted, like every search: every candidate is replayed from the
start through the interpreter on the original rule, and the result is a
subsequence of the caller's own requests that anyone can replay directly.

## Entry points

`minimizeRun` and `minimizeRunDetailed` are exported from:

- `gdp-wired` (the root entry point)
- `gdp-wired/minimize` (the standalone subpath)
- every language frontend subpath (`gdp-wired/extract`, `gdp-wired/effect`,
  `gdp-wired/extract-py`, `gdp-wired/extract-rb`, `gdp-wired/extract-ex`,
  `gdp-wired/extract-rs`, `gdp-wired/extract-swift`, `gdp-wired/extract-go`,
  `gdp-wired/extract-c`, `gdp-wired/extract-cpp`, `gdp-wired/extract-java`,
  `gdp-wired/extract-kotlin`, `gdp-wired/extract-sol`)

```ts
import {min, minimizeRun, minimizeRunDetailed, nat, proveRule, rule, when} from 'gdp-wired'

const uncapped = rule('uncapped')
  .params({b: nat, m: nat})
  .inputs({c: nat})
  .state({s: 0})
  .step(({b, c, s}) => ({s: when(s.lt(b), s.plus(c), s)}))

const bounded = uncapped.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))
const v = proveRule(uncapped, [bounded])

if (v.run) {
  const short = minimizeRun(uncapped, bounded, v.run)
  // Or with replay statistics and minimality status:
  const detailed = minimizeRunDetailed(uncapped, bounded, v.run, {ms: 2000})
  // detailed: {run, minimal, from, to, replays, steps, ms}
}
```

## Inputs and options

- `rule`: a `Rule` builder or a plain `Machine`.
- `law`: a `Law` or `StepLaw`.
- `run`: either a `Verdict.run` (`{params, trace}`) or a plain array of requests
  (pass `{params}` in `opts` when the rule has parameters). Requests may be wire
  objects (`Verdict.run.trace`), `Map`-bearing requests, or raw rule inputs
  encoded via `rule.encodeInput`. The return value preserves the shape given and
  keeps the caller's own request objects in their original order.
- `opts.ms`: wall-time budget in milliseconds (default `2000`).
- `opts.params`: parameters for a run passed as a plain request array.
- `opts.bound`: key bound for `forall` laws (default: the smallest of `1`, `3`,
  `8`, `24` at which the given run breaks `law`).
- `opts.shortest`: whether to run a bounded breadth-first pass for a shortest
  breaking subsequence after 1-minimality is reached (default `true`, for
  invariants and single-step laws).

`minimizeRun` throws if the parameters fail the rule's precondition or if the
given run does not break `law` when replayed from the start state.

## Guarantees and scope

- **Validity.** Every adopted candidate is replayed through `interpret` on the
  original rule (`core/watch.ts`'s `watch` reader). The returned run contains
  only requests admitted by the rule, with unchanged parameters, and ends at its
  first breaking step, so it breaks `law` under both strict (stop on refused
  request) and skip-refused replay.
- **1-minimality.** After cutting at the first break and removing chunks by
  halving, single-request removals repeat to a fixpoint under the wider
  skip-refused reading, followed by pair removals and (when enabled) bounded
  shortest-subsequence search.
- **Budget exhaustion.** If `opts.ms` expires before the closing single-removal
  pass finishes, `minimizeRun` still returns a valid breaking subsequence;
  `minimizeRunDetailed` sets `minimal: false` to report that 1-minimality was
  not confirmed within the budget.
- **What is not minimized.** Parameters and individual request field values are
  kept unchanged; only requests are dropped. Multi-step (`steps > 1`) laws skip
  the shortest-subsequence search and state-equivalence early stop while still
  shrinking via chunk and single-request removals.
