---
name: gdp-wired
description: "Prove the laws of stateful rules in TypeScript with gdp-wired's native API (the proven rule runs in production), or in Python, Ruby, Elixir, Java, Kotlin, Swift, Go, Rust, C or C++ code read as it ships (`npx gdp-wired-cli check`, laws as `gdp: law` comments), with gdp-wired, an automatic prover (no proof to write, every proof checkable again in Lean). Use when adding, changing or reviewing a budget, cap, quota, rate limit, sliding window, workflow, ledger, access policy or any state machine whose invariants matter; when code imports from 'gdp-wired'; when an XState machine or an Effect service (Refs updated in Effect.gen, STM transactions) or an Effect retry Schedule holds such a rule; when a gdp-ts trusted module's check (an authorization or entitlement policy) should be proven, not just trusted; when a law comes back refuted or unproven; or when deciding whether a claim belongs to gdp-wired, Lean or Bend."
---

# gdp-wired

**In TypeScript the native API is the default, and the proven rule is what ships.** `npm install gdp-wired`;
write the rule with `rule()`, `fun()` or `chart()` and the kinds; state its laws with `.law`, `.stepLaw`,
`.stepsLaw`, `.leadsTo` and `.decide`; prove them with `proveRule`, `proveSteps` and `proveLeadsTo` (with
`{from: 'any'}` wherever state is reloaded, requiring `proven && checked && !assumes`); keep each broken variant and
assert that search refutes it; and run the proven rule itself at runtime (`rule.interpreter()` or `rule.compiled()`,
`fun.run()` or `fun.compiled()`), so no hand-written copy of its decisions can drift ([shipping](references/shipping.md)).
`// gdp: law` comments, `gdp-wired-cli check` and extraction are for code in another language, or when the user asks
for them.

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

It decides laws about stateful rules over naturals, records, variants, maps,
sets and logs, and proves the lemmas you state about a recurrence by
induction. Recursion it would have to invent a lemma for belongs to Lean or
Bend ([where it fits](references/where-it-fits.md)).

## Workflow

When adding or changing a rule whose invariants matter:

1. **Write the rule as the code does it.** One `rule(...)` with the same
   params, inputs, state and step as the production code. Use kinds for what
   isn't a natural (`bool`, `oneOf`, `maybe`, `int`, `decimal`, `str`), records
   and variants for objects and tagged unions (`record`, `variant`), maps for
   per-key state, `.log` for histories, `chart` for a workflow with many states ([writing rules](references/writing-rules.md)).
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
   that matters. `proveRule` and `proveSteps` look for it themselves (10 s by
   default; `{search: {ms}}`, or `{search: false}` for the prover alone):
   lemmas first (`discover`), then invariants (`inferLaws`), and the verdict's
   `found` holds what proved the laws, as laws to pass with them and as
   lemmas to state, each with the source to paste. An invariant found holds
   only in states reachable from the start, and the verdict says so
   (`assumes`). If the code steps the rule from states it is handed (a
   host's, a stored one), prove with `{from: 'any'}` and require
   `proven && checked && !assumes`.
5. **Ship the rule you proved.** Run it with `rule.interpreter()` or `rule.compiled()` (`fun.run()` or
   `fun.compiled()` for a decision), or emit zero-dependency standalone TypeScript (`rule.emit()` / `fun.emit()` /
   `ratRule.emit()` / `chart.emit()`, or `npx gdp-wired-cli emit <module>#<export> --out <file.ts> --check --verify`)
   when you want no production runtime dependency or strict CSP compatibility ([shipping](references/shipping.md)).
   Always run `rule.crossCheck(laws)` in tests. Code that already exists and can't be replaced yet is held to the rule
   with `rule.compare(reference)` until it is: a test, not a proof. With gdp-ts, mint its proofs from
   the proven check (`guard`, `gate` from `gdp-wired/gdp`) so every call site
   is held to it ([with gdp-ts](references/gdp-ts.md)).
6. **Keep the broken variant.** Next to each proven rule, keep the bug it
   rules out (the uncapped budget) and assert it is refused. It is the
   cheapest regression test you will write.
7. **State the lemma, find it, or hand off.** A recurrence on one natural (a
   backoff delay, a fee schedule): define it with `recur` and state the lemmas
   the rule needs; they are proven by induction and become its facts. When the
   law isn't proven and you don't know the lemma, `discover(rule, laws,
   stepLaws)` (`gdp-wired/discover`) looks for it, for a recurrence and for a
   carried list's folds (`discoverFold(fold, laws)` for a tree): paste what
   `found` gives into `recur`, `carriesList` or `.children`. Other
   recursive structure, or products of unknowns past what products of facts
   and squares refute: prove the function in Lean,
   give the rule the function with its facts, export with `toLean`
   ([Lean handoff](references/lean-handoff.md)). Don't approximate a
   recursive claim with a bounded one and call it proven.

## Code in another language (or law comments, when asked)

`npx gdp-wired-cli check <file|dir>` (gdp-wired with TypeScript beside it) reads the rule from Python, Ruby, Elixir,
Java, Kotlin, Go, Rust, Swift, C or C++ (and from TypeScript, Effect or XState when the user asks for law comments)
with nothing configured, checks it against the code, prints its names in the
code's terms and proposes laws (each proven, broken with a run, or unknown, with the comment that states it). State a
law with one comment in the code's language, over the code's names: `# gdp: law <name>: <expr>` (`//` in the
C-family, Go, Rust, JVM and TypeScript; `@GdpLaw("...")`, `@gdp_law(...)`, `#[doc = "gdp: law ..."]` too). On the
line above a method it is a law of that method's step: fields are the state after, `old(x)` before, arguments by
name, `result`, `failed`, `f(...)` an answered call; elsewhere it holds in every state. Modelling choices
(`failures = "kept"`, a store's attrs, an untyped result's type) go in `gdp.toml` under `[rules.<name>]`.
Where the code runs among others (a lock, a limiter, a consumer over Redis or a database), state its environment with
one tag over the class, `# gdp: env read committed` (or `keys expire`, `atomic`, `snapshot`, `retries`, `an object
per call`, `acquire then release`): the laws then hold of every call at once. `at most one call between acquire and
release` is a lock's law (each key's leases expiring with their keys); `at most one call between pay and pay` with
`# gdp: effect` on the charge's line says each key is charged once (refuted under retries at read committed, or once
the dedupe mark expires). Exit 1 is
a broken law, 2 one not checked: run it in CI (`uses: monotykamary/gdp-wired@main`). A refusal names the tag or
option that fixes it; read it before changing the code.

## Consult while coding (experimental local MCP)

The research-only stdio server is `bun research/agent-tools/stdio.ts` from this
repository. It has no HTTP listener/model/network calls and accepts **data**,
not code strings, source paths or shell commands. It currently supports scalar
natural Machine/Law AST; see `research/agent-tools/README.md` and the tool schemas.
Do not promote this prototype before the surface-semantics release gate passes.

| When coding | Tool | How to interpret the answer |
|---|---|---|
| Before/after changing an invariant | `prove` with rule data + named laws | Only `proven && checked` means proven; unknown/unchecked is not success. Model proof is not source/native equivalence. |
| A law fails or is unclear | `why_not` | Inspect the trace using your own variable names. It is shortest **within the reported finite domain**, never a claimed globally minimal trace. No trace found is not proof. |
| You need helper invariants or to test a stronger claim | `suggest` | Existing `inferLaws` supplies helpers; explicit `nearMisses` are caller candidates and are returned only with actual counterexamples. Paste the stated support set, not an isolated mutually inductive helper. |
| Reviewing a modification | `check_change` with two rule revisions and the same laws | Newly broken requires an old checked proof and a new reachable trace. Lost proof alone is not a bug. Existing compose refinement is directional, not automatic equivalence. |
| Before reporting a result | `status` with exact unit + returned revision digest | Reads only this process's observed proof evidence. Native conformance/harness labels remain unavailable without independently validated native receipts. Never supply a label yourself. |

Use bounded `budget.work`, `apiCalls`, `depth`, `bound` and `candidates`, not a wall
time. Increase a counted allowance or simplify the request only as the returned
typed refusal directs. The server never evaluates client code or fetches packages.
The default service starts a fresh counted worker for each computational request
to prevent warm caches from silently changing a repeated request's result.

## References

Read the one you need:

| File | Read it when |
|---|---|
| [`references/writing-rules.md`](references/writing-rules.md) | Writing a rule or a law: kinds, records and variants, maps, flags, step laws, k-step laws, histories, liveness, decisions, pure functions, two-run laws, loops. |
| [`references/reading-verdicts.md`](references/reading-verdicts.md) | A verdict is not `{proven: true, checked: true}`: `stuck: 'sat'`, `stuck: 'unknown'` with `why`, a witness, a search result. |
| [`references/shipping.md`](references/shipping.md) | Running the proven rule in an app, encoding runtime values, holding existing code to the rule. |
| [`references/gdp-ts.md`](references/gdp-ts.md) | The codebase uses gdp-ts (`@gdp-ts/core`, a `proofs/` folder), or an authorization check should be proven and demanded at every call site: `guard` and `gate`. |
| [`references/lean-handoff.md`](references/lean-handoff.md) | Exporting proofs to Lean, stating a lemma about a recurrence (`recur`), or a claim needs recursion or arithmetic the kernel doesn't decide. |
| [`references/where-it-fits.md`](references/where-it-fits.md) | Deciding whether gdp-wired, Lean or Bend should own a claim. |

## API

From `gdp-wired`:

| Export | What it is |
|---|---|
| `rule(name)` | A rule builder: `.params` `.inputs` `.state` `.maps` (of naturals, or of a kind: `kind.from(v)`) `.lists` `.items` (lists of a kind) `.carries` `.flags` `.step` `.pre` `.assume` `.fns` `.facts` `.log` `.sums` `.queries` `.keep` `.relations` `.prune`. |
| `nat`, `upTo(k)`, `bool`, `oneOf(...)`, `maybe(kind)`, `int`, `decimal(places)`, `str({like, maxLength})`, `record({...})`, `variant({...})` | Kinds; state of any kind with `kind.from(init)`; a variant's case built with `V.make({tag, ...fields})`, read with `is` and `match`; `same(a, b)` compares two values part by part. |
| `r.law`, `r.stepLaw`, `r.stepsLaw`, `r.leadsTo`, `r.decide`, `r.relate` | Claims: invariant, one step, k steps (k ≤ 64), liveness, a decision about one request, a decision about two. |
| `ratRule(name)`, `rat`, `nonneg`, `proveRatRule(rule, laws)` (`gdp-wired/rationals`) | A rule over the rationals: exact values (decimals, fractions), linear terms (`plus` `minus` `times(k)` `over(k)`, `rmin` `rmax` `rwhen`); `{proven, checked, goal?, stuck?, witness?, run?}`, refuted by an exact run from the start or proven by trees of Farkas certificates; `rule.run(params, requests)` computes exactly; `rationalsToLean` (`gdp-wired/lean`) checks the proofs in Lean. |
| `proveNeverEnds(loop, {from?, ms?})` | Some run of the loop never ends (the claim a halting proof refutes): `{proven, checked, recur, loop, by, run}`, the certificate a closed recurrent set with the turn from each state given; toLean's `{id, neverEnds: v.loop, recur: v.recur}` proves `NeverEnds` in Lean. |
| `proveRule`, `proveSteps`, `proveLeadsTo`, `proveDecision`, `proveLoop` | Verdicts: `{proven, checked, goal?, stuck?, witness?, why?, found?}`. `proveRule` and `proveSteps` take `{search}`: where the prover alone doesn't prove the laws and no run breaks them, they look for lemmas and invariants (10 s by default; `false` for the prover alone), and `found` says what proved them. `assumes` says the proof holds only in states reachable from the start; `{from: 'any'}` proves step laws from every state the laws allow. |
| `minimizeRun`, `minimizeRunDetailed` | Shrink a refuting run (`Verdict.run` or a request array with `{params}`) on the original rule until no single request can be removed (`{ms, params, bound, shortest}`); `minimizeRunDetailed` also reports `{minimal, from, to, replays, steps, ms}`. Also on `gdp-wired/minimize` and every language extractor subpath. |
| `when`, `min`, `max`, `count`, `sum`, `all`, `any`, `not`, `forall`, `everyKey`, `someKey`, `relation` | Terms and conditions; terms have `plus` `minus` (truncated) `times(k)` `mul` `lt` `atMost` `atLeast` `gt` `eq`, conditions `and` `or` `not` `implies`. |
| `chart(name)` | A statechart: `.states({...})` (nested: `{states: {...}, initial, history, final}`) or `.regions({...})` (parallel), `.params`, `.inputs` (the payload), `.context` (extended state), `.outputs` (decided each step, reset to a default), `.events` (their order), `.on(event, {from, to, when, set, fresh})` (no `to`: internal; `fresh`: ignore history); `.check()` (every state reached with its run or proven unreachable, none stuck, no event ambiguous), `.law`, `.stepLaw` (`env.in('active.paid')`, `env.last('active')`), `.prove`, `.rule`. |
| `inferLaws(rule, laws, stepLaws?)` | `gdp-wired/infer`: the invariants a law that isn't inductive needs, found from runs and the kernel's counterexamples (bounds, sums, differences, guarded by a flag or a choice, laws about every key of a map); `found[i].source` is the `r.law(...)` call; proven and checked like `proveRule`. |
| `fromXState`, `conforms`, `toLogic`, `runToEvents`, `serializeState` | `gdp-wired/xstate`: an XState v5/v4 machine as a chart (`fromXState`, checked beside XState's actor with `conforms`), or any proven rule/chart as XState v5 `ActorLogic` (`toLogic`, copied states via `interpreter()`, canonical `serializeState`, small-edge default `events`) so `@xstate/graph`'s `TestModel` drives the real app (`getShortestPaths` / `testPath`), and `runToEvents` turns prover counterexamples into `getPathsFromEvents` regression paths (proof covers the logic; MBT covers the app around it). `extractXState('./machine.ts')` (`gdp-wired/extract`) only when asked (CLI law comments on XState remain model-only `unchecked`, exit 2). |
| `extractEffect('./limiter.ts')` | `gdp-wired/effect`: an Effect service (3.x or 4.x: Refs made by its make effect, `Effect.fn` methods, typed failures, `Clock`, STM's TRef and 4.x's TxRef in transactions, retry and repeat with a schedule) read into a rule and checked by running it on the Effect the file's project has; a method of several transactions read as every fiber's steps (`fiberRun` shows a run); a `Schedule` (`{entry}`, or `fromSchedule(source)`) read into a rule of its decisions, checked by stepping Effect's own schedule (`x.replay`, `jitterRun`); `conforms(rule, service)` runs a rule by hand beside the running service; `fromSchema(schema)` is a Schema's kind. |
| `extract`, `extractPython`, `extractRuby`, `extractElixir`, `extractJava`, `extractKotlin`, `extractGo`, `extractRust`, `extractSwift`, `extractC`, `extractCpp`, `extractEffect`, `extractXState` | One way in: `(file, options?)`, the file a path or a URL (a Go package or Rust crate by its directory or any file; TypeScript, Effect, XState also `{code, file}`); the class, service or machine inferred (`entry` names one; `entry: [...]` several functions, each a request); `methods`, `failures`, `onError`, `strict`, `answers`, `skip`, `stores`, `domains`, `check` mean the same in each that has them. Each module also exports `proveRule` and `proveSteps`: `proveRule(x.rule!, [...x.invariants ?? [], law])`. |
| `extractPython(file, {entry, answers, skip, stores})` | `gdp-wired/extract-py`: a Python class or module functions read through Python's own parser into a rule and checked by running the module beside it (python3 needed only then); a failure the step's refusal or, with `failures: 'kept'`, its result; calls of other code answered by the request, skipped, or a cache stated as a store |
| `extractRust(crateDir, {entry, methods, failures})` | `gdp-wired/extract-rs`: a Rust struct and its methods read through syn into a rule and checked by building the crate beside a generated harness (cargo needed only then); integers keep their width (a panic past it is the step's failure), Option and Result, Instant and Duration, atomics as fields |
| `fun(name)`, `loop(name)` | Pure functions (`.returns`, `.law`, `.relate`, interpreted `.run`, explicit `.compiled`) and loops (`.while`, `.body`, `.rank`; with no `.rank`, `proveLoop` finds one from the loop's runs, with the invariants it needs, in `found`). |
| `findCycles(facts, claims)`, `findRank(loop, laws)`, `cycleLemmas(machine, laws)` | `gdp-wired/cycles`: cyclic proofs nobody shaped, for claims about functions defined by their equations: ranks (linear, in order) from the runs, back-edges at the calls a goal reads, companions (constants abstracted, bounds on what a goal reads); checked by `kernel/cyclic.ts`. `proveRule`'s search tries `cycleLemmas` for functions known by their facts (`{search: {cycles: false}}` leaves it out). |
| `fn(arity, js, {facts, lean})`, `divBy(c)`, `modBy(c)` | Functions known by their facts. |
| `recur(name, {args, fns, zero, next}, lemmas, between)` | A function defined by a recurrence on its first argument (up to four further arguments fixed, other functions read), its lemmas and laws between two points proven by induction when made (`Unproven` otherwise); its equations, lemmas and laws are its facts, checked again by Lean as the kernel's own proof. |
| `discover(rule, laws, stepLaws)`, `discoverFold(fold, laws)` | `gdp-wired/discover`: lemmas nobody stated, for a recurrence's function, a carried list's folds or a tree fold, found from their values (bounds, linear relations, closed forms of degree 2 at most, laws between two points), proven by the same induction, only those the laws need kept; `verdict` is of `rule` (the rule made again with them), `found` is source to paste. |
| `r.carriesSeq(...names)`, `r.carriesSeqs(...names)`, `everyBelow(n, f)` | Sequences a request carries as positions and a length (`A.prefixOf(B)`, `startsWith`, `equals`, `extends(B, k)`, `has`, `at`, `len`), tables of them (`T.row(r)`, `T.rows`); laws about prefixes of paths need no lemma; rows compared at a witness. |
| `r.carriesList(name, kind, folds, lemmas)` | A list of values a request carries (an invoice's lines): `L.every`, `L.at(i)`, `L.fold.<f>`; folds and lemmas may read the params; fold lemmas proven by induction (they read the folds, not the items); decisions assume the folds too. |
| `fold(name)`, `proveFold`, `f.run(tree)` | A fold over a tree given as a value: `.leaf`, `.node`, `.law` (`.children` for any number of children per node); laws proven by induction over the tree. |
| `r.nodes(name, kind, children, folds)` | A tree (or lists of lists) in the state: a table of nodes that only grows, `T.make(value, kids, when)`, `T.node(n).fold`; a law about a subtree is a law about one node. |
| `optional(c, value)`, `variant(cases, {tag})`, `r.kindLaws()` | A value present where c holds; a variant whose runtime case key isn't `tag`; what the kinds of the state and cells keep true (proven by `proveSteps` on its own). |
| `r.compiled()`, `r.interpreter()`, `r.encodeParams`, `r.encodeInput`, `r.foldsOf`, `r.decode`, `r.crossCheck`, `r.compare` | Running and checking the rule. |

Also: `gdp-wired/minimize` (`minimizeRun`, `minimizeRunDetailed`), `gdp-wired/gdp` (`guard`, `gate`, `Unproven`: gdp-ts proofs minted by proven checks),
`gdp-wired/machine` (`search`, `compileJs`, the interpreter), `gdp-wired/lean`
(`toLean`, `leanProject`), `gdp-wired/compose` (`product`, `interleave`,
`refinement`, `steps`, `ghost`), `gdp-wired/kernel`, `gdp-wired/prove`.
