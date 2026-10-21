# Changelog

What changed since the first public release, 0.6.0 (2026-10-18). Times are measured on Modal (2 vCPU per job unless
noted), each with the command that reproduces it.

## Unreleased

- `lean-kernel/Bridge.lean` (trusted, on top of `Sets.lean` and `Cyclic.lean`, the standard axioms only). `cyclic_sound`
  says what a proof's nodes hold of any maps that meet its facts; nothing tied `core/cyclic.ts`'s instances to the rules'
  meanings, so a cyclic proof of a machine law was a proof about its encoding. Each instance is now written in Lean as a
  function of the rule's own syntax, a check compares an exported proof against it, and a theorem carries the node to
  the rule:
  - `cyc_machine_sound` (`machineNodes`, every machine the cyclic route covers): a reachable state ends a run of T steps
    (`reach_run`), and the run as maps over time (a state variable or input x as x@[u], a map's cell k at time u as
    M@[u + k·Ω], Ω = T + 1, which decodes at every key) meets the encoding's facts: the start, each step with its flags
    inlined, each map's start and step (a write at one key read at the fact's key), the functions' facts. If the
    exported facts are among those or true of every natural, and the node's hypotheses among the precondition, t <= T
    and T < Ω with its conclusion the law at t (`cycMOk`), the law holds in every `SReach` state at every value of its
    keys.
  - `cyc_recur_sound` (`recurNodes`): a recurrence's lemmas and laws between two points hold of its values (`recF`). The
    export shows those values equal to the recurrence as Lean defines it and states each lemma plainly of the definition
    (`cycgrowing_lemma0 : 1 ≤ cycgrowing_fn x`; `cycfilled_between0`, a recurrence with a further argument).
  - `cyc_fold_sound` (`foldNodes`): a tree's table is its post-order, each node after its children; for params that meet
    the precondition a law holds of every tree whose inputs meet the assumption, as `fold_sound` says of the structural
    induction.
- The encoding is sound as it stands, and `core/cyclic.ts` is unchanged: Ω only needs to be above the run's length (the
  node's T < Ω), and a key needs no bound. What could not be checked in Lean was a cyclic machine proof whose maps are
  read at a key from the state or a request (caps, tally): the exporter refused a cell whose key reads a product of
  cells (Ω·k@[t]). It now places each table column after the columns it reads.
- End to end (`lean-cyclic`, ten items, 107 theorems, 29.85 s): the two-by-two counter (a function's facts), caps (writes
  under a flag), fill (a write at every key), tally (a map each request carries), the budget (inputs, a flag, an
  assumption, a precondition), growing, filled and the spend roll-up. The proofs of caps and of the budget, checked
  against a machine whose grant skips the day's count or checks only what was spent, compute to false. `budget_runs`
  states the budget's laws in plain Lean, as `mccarthy_91` states McCarthy's function: from nothing spent, each request
  granted when it fits the cap, what was spent stays within the cap and the grants at most what was spent, after any
  number of requests.
- `research/cyclic/bridge.ts` checks in Lean, against Bridge.lean's encoding, the facts and nodes the instances make for
  every machine law of the example domains (with their broken variants) the cyclic route covers, and the examples'
  recurrences and folds: 265 machines, 492 laws, 6 recurrences, 5 folds, 3,854 checks, none failed
  (`lean-bridge-sweep`, 8.2 s). `lean-bridge` builds Bridge.lean with no `sorry` and prints its theorems' axioms.
- Cycles nobody shaped (`gdp-wired/cycles`, untrusted; the kernel and the Lean twin unchanged): searches whose output is
  a cyclic proof `kernel/cyclic.ts` checks, with what core/cyclic.ts's builders fix (each node's rank, where each
  back-edge returns, at which terms) found. `findCycles(facts, claims)` takes claims (hypotheses and a conclusion, no
  rank, no back-edge) about functions defined by their equations (f(k) = body, or f(0) and f(k + 1); several arguments
  paired as dsl's argsKey pairs them) and runs the equations: a false claim comes back with the point the facts break
  it at. Back-edges go to a claim at the arguments of each call its goal reads (n + 11 and f(n + 11) for McCarthy's 91),
  each guarded by where it may be used (that claim's hypotheses there and its rank there below), so the premises and
  the descent are the guard's. Ranks come from the runs: each sampled call a back-edge makes must drop, and the rank,
  linear over the claim's variables, is an integer LP (solver.ts's elimination, its rows generated from the violated
  ones, coefficients first naturals and small), lexicographic by successive elimination (Bradley–Manna–Sipma), the
  uses between strongly connected components ranked by their height first. Where a claim is stuck, its constants are
  abstracted (an accumulator: g(x, 0) = 2x through g(x, a) = a + 2x, fitted exactly to the values) into a companion below
  it, or companions beside it bound what its goal reads (by analogy with the claim, then every bound fitted to the
  values), Houdini over them and only those the claims need kept. `findRank(loop, laws)` takes a loop's rank from its
  runs the same way, and where the kernel's halting goals need an invariant, `inferLaws` finds it with the loop's
  descent as its step laws; `proveLoop` with no `.rank` calls it. `proveRule`'s and `proveSteps`'s search, for a rule
  reading functions known by their facts (`fn`, not `recur`), tries `cycleLemmas` between discover and inferLaws:
  lemmas fitted to the functions' JavaScript (a constant on a region, a line, a bound), proven from the facts as cyclic
  claims, the laws proven with them as facts (`found.facts`; `{search: {cycles: false}}` leaves it out).
  - `research/frontier`'s cycle track (`research/frontier/cycles.ts`, `examples/cycles.ts`): 13 items, none proven with
    nothing stated before (today: the builders' shape, rank x and back-edges at x − 1, for claims; kernel/run-more.ts's
    rank templates for loops; `proveRule`'s search as at 0.17.0 for rules), all 13 proven now, and their 13 broken
    variants refused both ways (Modal, 1 vCPU a job, `runs/modal/cycsearch/corpus1`): McCarthy's 91 by 101 − n (107 ms),
    Ackermann's ack(m, n) > n by (m, n) (439 ms), subtractive gcd by x + y (863 ms), an accumulator (85 ms) and two (290
    ms), three functions in a ring (88 ms) and one read through another at twice its argument (550 ms), each with the
    companion found; loops of two and three phases ((x, y), 419 ms; (x, y, z), 2,744 ms), every other turn (2·x − p with
    p <= 1, 885 ms), subtractive gcd with no invariant (a + b with 1 <= a, 1 <= b, 1,362 ms); a rule reading McCarthy's
    function (f(k) = 91 for k <= 101, 2,340 ms) and one reading a function given by its recurrence's facts (105 ms).
    The proofs found are checked again in Lean (`lean-cycles`, `lean-cycles-loops`, `runs/modal/cycsearch/lean2`),
    Ackermann's too, whose back-edge at (m − 1, ack(m, n − 1)) reads a key that is a product of cells, since the export
    places each column after the columns it reads (`runs/modal/merge/ack1`).
  - Not found: a rank that isn't linear or needs a coefficient past 4 in one component, a back-edge at a term no goal
    reads (after unfolding the facts twice), a generalization whose conclusion isn't an exact linear fit, bounds on a
    function of two arguments, a machine's liveness with no rank. CHC-COMP's LIA-Lin tasks read no function and state
    no loop, so their verdicts are unchanged (the search isn't reached).
  - The suite (`modal/suite.json`, 178 jobs with `cycles`, `lean-cycles` and `lean-cycles-loops`): 365.7 s wall and
    2,624.2 s of job time, none failed; `frontier-score` 54 / 54 (`runs/modal/cycsearch/suite1`).

## 0.17.0

Cyclic proofs in the kernel and its Lean twin, and a prover about twice as fast: the suite (175 jobs) passes in
372.3 s wall and 2,378.3 s of job time at this release (`runs/modal/rel017-suite`).

- Faster proofs, and a suite at about half its time. The prover keeps a quantified flag's or an every-key law's
  instance only where the goal reads a map the way its condition reads one at its key (a tuple, where each of its keys
  is so read), the rest left out unless a goal needs them (then every instance, as before), and on a goal that outgrows
  64 cases splits first the atoms the root's rows already force (a guard `?f = 0` where `?f = 1` holds), whose forced
  side then refutes at once instead of under every other case. In the same run against 0.16.0 (`runs/modal/perf/ab4-*`,
  three containers each): pi-fabric's resource scope (`private/pifabric/bench.ts`, three proofs a container) 16.4 to
  24.6 s a proof against 36.6 to 47.5 s; `examples/scopes.ts`'s attenuation 3,886 ms against 40,665 ms, normalizing
  1,374 ms against 16,593 ms and each action back 678 to 715 ms against 9,051 to 9,597 ms; the prover bench
  (`research/perf/prover-bench.ts`, five runs) 4.7 to 7.2 s against 6.1 to 7.6 s.
- The Lean export proves each step law again from only the instances its first proof's leaves read
  (`minimal.on`, set by `toLean`): the resource groups' laws (`examples/groups.ts`) were built from 944 to 1,186
  hypotheses for trees of 29 to 52 leaves, and Lean took 268 s on one (`runs/modal/perf/suite1`), 15 to 21 s now
  (`runs/modal/perf/lean2`). The package check runs in four shards (`SHARD=i/n`, lean-package-0..3), the item jobs
  against the twin's library compiled once and cached (`scripts/lean-items.sh`; lean-package-0 still builds the Lake
  project whole), and research/hw's step checks in three (`PART=`). The suite (`modal/suite.json`, 175 jobs): 326.0 s
  wall and 2,404.6 s of job time (`runs/modal/perf/suite3`), against 621.4 s and 3,874.5 s (`runs/modal/suite-merged3`).
- A deadline the prover keeps (`withDeadline`): `inferLaws` and the search `proveRule` falls back on bound every proof
  they make by their own time, a goal past it left `unknown`. On CHC-COMP's LIA-Lin track (`compare/chc`, the search's
  deadline now 2 s before the 60 s limit, as the prover keeps it): 365 solved (223 sat, 142 unsat), none wrongly, 12
  out of time (`runs/modal/chc/perf4-gdp`), against 366, none wrongly, 315 out of time (`eng5-gdp`). `grow`'s
  `units: false` leaves a goal's own order for a caller after a model (the guided runs), and `--env` sets variables
  for each task (`GDP_UNITS=0`, `GDP_TRIGGER=0` turn the two changes above off, for comparing).
- Cyclic proofs: one rule for every induction (`kernel/cyclic.ts`, trusted; its twin `lean-kernel/Cyclic.lean`,
  `cyclic_sound`, proven with the standard axioms only). A proof is facts (conditions that hold at every value of their
  keys) and nodes, each a sequent with a rank (naturals compared in order); a node uses any node, itself included, at a
  substitution of its variables where a guard holds, once that node's hypotheses there follow and its rank there is
  below. Every goal is built from the nodes, in TypeScript and again in Lean, and refuted by the kernel's trees; soundness
  is well-founded induction on the rank. `gdp-wired/cyclic`'s `proveCyclic(facts, nodes)` grows every tree.
  - New inductions (`examples/cyclic.ts`): McCarthy's 91 function, nested recursion `recur` can't define, proven at every
    n <= 101 (566 ms, `runs/modal/suite-plain3`) and stated in plain Lean as `mccarthy_91` (every f meeting the equation gives 91); two
    functions defined by each other, their bounds proven together. Three tampered proofs (a back-edge that doesn't drop,
    one read at the wrong term, the node unranked) are refused by the kernel and computed to false by Lean.
  - Today's rules as instances, behind `modal/run.py --cyclic` (GDP_CYCLIC=1: every proof they cover made again as a
    cyclic proof, a differing verdict failing the job): a recurrence's lemmas (rank x) and laws between two points; a
    fold over trees as a table of nodes, children below their parent (rank n); a machine's laws over its run as maps
    over time (rank t, a map's cell at time u and key k at u + k·Ω, Ω above the run's length). On the whole suite
    (`runs/modal/suite-cyclic3`): 4,528 machine proofs of 252 machines, 258 recurrence proofs and 16 fold proofs
    compared; all agree but 3 (`running statistics` twice and the lists example's normalized scope, proven the usual
    way, not as cyclic proofs: the run's equations would need the goal's multiplier with them, and two keys at once go
    past the prover's budget). Left to the usual rules: histories, flags that hold at every key, and laws that read a
    map at a key read from a map (tables of nodes, `research/cyclic/probe.ts`). The cyclic route is slower (machines
    17,738 ms the usual way against 231,733 ms; recurrences 934 ms against 8,824 ms; laws between 285 ms against 16,913
    ms; folds 199 ms against 9,078 ms), so the default prover stays as it was: the suite takes 3,910.0 s of job time on
    its 168 jobs from before against 3,874.5 s at 0.16.0 (`runs/modal/suite-plain3`, `suite-merged3`), quantifiers
    150.8–164.6 s against 148.5–186.8 s over three runs each. Lean's checks of the cyclic proofs are a job of their own
    (`lean-cyclic`, 74.57 s).
  - Loops and liveness are not instances: their claims are about runs that never end, not sequents over a frame (their
    rank's drop is a cyclic descent goal, but the claim around it isn't).

## 0.16.0

`research/frontier`'s corpus: all 41 laws proven with nothing stated (the suite's `frontier-score` job,
`runs/modal/suite-merged3`); `proveRule` and `proveSteps` search for what a stuck law needs on their own.

- Sequences a request carries (`.carriesSeq('Path')`, and tables of them, `.carriesSeqs('Paths')`): positions and a
  length, `at`, `len`, `prefixOf`, `startsWith`, `equals`, `extends(B, k)`, `has`, a table's `row(r)` and `rows`, each
  comparison a condition about every position below a length, so a law about prefixes of paths needs no lemma; the
  request gives an array of naturals, a table an array of them; `everyBelow(n, k => ...)` for bookkeeping a request
  carries, row by row. `examples/scopes.ts`: pi-fabric's path scopes (`<ns>:<path>`, `/*`, `/**`, `<ns>:*`), its
  `covers` compared with the rule's on 20,000 random triples of patterns; covering transitive and reflexive and what a
  covered pattern matches the covering one matches (64 to 933 ms each), what a derived scope allows its parent allows
  (41,279 ms), normalizing changes nothing a scope allows, both ways (15,602 ms, and 8,211 to 9,145 ms per action); the
  broken variants refused (`runs/modal/seqs-scopes3`, Modal, 2 vCPU). A condition about every row of a table that
  compares the rows' sequences is refused (two keys at once): a row is compared at a witness.
- A goal multiplied by a factor first: where a leaf with products isn't refuted by products and squares, the prover
  multiplies every row by a factor the path has at least 1, with the squares (x·a − b) of the products the rows read.
  `(Σv)² <= n·Σv²` over running samples (n times the goal, then (n·v − s)²) is proven, 53 ms (the suite's `nonlinear`
  job, 1 vCPU, `runs/modal/seqs-suite1`); it was the one item of
  `research/frontier`'s nonlinear corpus not proven. The kernel and the Lean twin are unchanged (the certificate is
  products and squares); the package check exports it (`runningstats`). The prover bench (`research/perf/prover-bench.ts`,
  520 items, 1,210 goals) makes the same 14,008 solver calls with it as without, in 5.1–6.3 s over five Modal runs
  against 3.6–6.3 s without (`runs/modal/seqs-bench1`).
- `proveRule` and `proveSteps` look for what the laws need when the prover alone doesn't prove them and no run breaks
  them: first runs deeper than the first ones (600 of up to 24 requests, values up to 8, within 1.5 s; a false law comes
  back with the run that breaks it), then lemmas about the rule's recurrences and lists' folds (`discover`), then
  invariants (`inferLaws`), within 10 s (`{search: {ms}}`; `{search: false}` is the prover alone). The verdict's
  `found` holds what proved the laws, as laws to pass with them and lemmas to state, with the source to paste. A proven
  or refuted law costs what it did: pi-fabric's resource scope (`private/pifabric/bench.ts`, Modal, three containers of
  three proofs) took 35.5 to 51.1 s a proof against 41.1 to 55.9 s at 0.15.0 in the same run of both; the prover bench
  (`research/perf/prover-bench.ts`, five runs) 6.4 to 9.3 s against 5.5 to 7.4 s, 14,037 solver calls against 14,008,
  the difference eight broken variants now refuted by the deeper runs and one searched for 1 s.
- CHC-COMP's LIA-Lin track (`compare/chc`): 366 solved (223 sat, 143 unsat), none wrongly, from 199 at 0.15.0's code
  (`runs/modal/chc/eng5-gdp` against `eng0-gdp`); nine tasks solved by none of Spacer, Golem and Eldarica within 60 s.
  A request names a clause that fires (the rule's assumption), so each update reads the clause named alone and the
  first proof no longer splits every clause's constraint on `loc`'s kind law (461 tasks had stopped there); runs the
  prover guides (each request a model of its clause's condition where the run is) answer 63 unsat; and `inferLaws`
  makes candidates from a counterexample to induction no candidate rules out (false at it, met by every sample under a
  condition it meets), a choice no term among others.

## 0.15.0

The proofs nobody had to state. `research/frontier/` holds a corpus of laws gdp-wired proved only when someone
stated what the proof needs (an invariant, a lemma about a recurrence or a fold, a square), with that statement taken
out: 41 laws, none proven at eb28edc, 40 proven now (the suite's `frontier-score` job, `runs/modal/suite-merged2`).

- Invariants nobody wrote, found (`gdp-wired/infer`): `inferLaws(rule, laws, stepLaws?)` proves a law that holds but
  isn't inductive by finding the laws it needs among bounds, sums and differences of up to three values over the state
  and params, the same guarded by a flag or a choice, and laws about every key of a map; candidates broken by states
  random runs reach are dropped, and the kernel's counterexamples to induction pick which to add. What it found comes
  back as laws and as the `r.law(...)` call that states each; the verdict is the prover's on the laws with them, so the
  kernel and the Lean twin are unchanged (`examples/infer.ts`, two proofs Lean-checked in the package check). A false
  law comes back with the run that breaks it. On the corpus: research/synth's four machines (in-flight requests, the
  token bucket, the leaky bucket, the metered blocks), 951 to 1,399 ms each, and 21 laws of the example domains that
  were proven only beside their sibling laws, proven alone (606 to 3,081 ms). On CHC-COMP's LIA-Lin track
  (`compare/chc`, every task in its own container, 60 s each): 203 solved (123 sat, 80 unsat), none wrongly, from 128
  with the folder's own Houdini (`runs/modal/chc/infer5-gdp` against `full4-gdp`); four tasks solved by none of Spacer,
  Golem and Eldarica within the limit.
- A decision whose `given` or `then` reads a condition about every key (`everyKey`, `subsetOf`, `disjointFrom`) is
  proven as a step law of its rule, the kernel closing the quantifiers as it does for flags (`decision.steps`); it came
  back unproven before.
- `research/frontier/scopes.ts`: pi-fabric's path scopes (`<ns>:<path>`, `/*`, `/**`, `<ns>:*`), the case
  docs/comparison.md called induction over nested lists, proven with no lemma once a path is positions and a length:
  covering is transitive, what a covered pattern matches the covering one matches, what a derived scope allows its
  parent allows (grants with actions), and normalizing a scope changes nothing it allows, both ways (the normalizer's
  bookkeeping, where each grant went and where each merged action came from, as data the rule checks at every key).
  The encoding agrees with pi-fabric's `covers` on 20,000 random triples of patterns and its grant checks on 5,000
  random pairs of scopes; each broken variant is refuted (`runs/modal/frontier-scopes2`).

- Products of unknowns, further: a map's cell may be a factor (a per-key quota, `Used[k] <= per·Seats[k]`; a cost kept
  as `Price[k]·Qty[k]`), and a leaf may add the square of any linear form t (t·t >= 0, whatever t's sign), in the
  kernel and the Lean twin alike (`leafSq`, its soundness case proven; a monomial's factors may be cells there too).
  Where a leaf with products isn't refuted linearly, the prover tries, after the products of two facts it tried
  before: (x − y)² for each product x·y the goal reads, its factors as the path leaves them (4ab <= (a + b)² kept by a
  rule that moves one from b to a needs (a − b + 2)²), and for each monomial split into two halves (Cauchy–Schwarz's
  (ad − bc)²), alone and with the products, then each square times each factor (a³ + b³ + c³ >= 3abc). A leaf keeps only
  the squares and products its derivation reads. `research/frontier/nonlinear.ts`: 8 true laws, none proven at
  eb28edc, 7 proven now (Modal, 1 vCPU: 1 to 308 ms each); `(Σx)² <= n·Σx²` over running samples is not (its
  certificate multiplies the goal by n first). The prover bench (`research/perf/prover-bench.ts`, 520 items, 1,210
  goals) makes the same 14,008 solver calls as before, in 4.0–6.0 s over five Modal runs against 5.0–6.5 s before.
  The Lean exports gain these goals and a per-key quota machine (`quota_laws`), and a tampered Cauchy–Schwarz tree
  computes to false.
- Lemmas nobody stated, found (`gdp-wired/discover`): `discover(rule, laws, stepLaws)` looks, where the laws aren't
  proven, for lemmas about the rule's `recur` functions and the folds of the lists its requests carry, among bounds,
  linear relations, closed forms of degree 2 at most and laws between two points that their values meet; proves them by
  the same induction stated lemmas are proven by and keeps only what the laws need. `discoverFold(fold, laws)` does the
  same for a fold over a tree, the children's lemmas of `.children` among them. The rule comes back made again with
  them, what was found as source to paste, and the Lean export checks it as it checks stated lemmas
  (`examples/discover.ts`). The kernel and the Lean twin are unchanged. On `research/frontier`'s corpus every lemma and
  fold item is proven (8 items), from 214 ms to 7.9 s each on Modal (`runs/modal/lemma-suite1`).

## 0.14.2

- The kernel's if row (0.14.1) only over constant branches, in the kernel and the Lean twin alike: over a variable
  branch (a map's `if(c, Given[k], 0)` for every cell) each row was one more in every leaf, and a rule proving nine laws
  at once over one ran about 12% slower (reported by a downstream project). The yes/no it was for, `if(c, 1, 0)`, keeps
  it. On that rule (Modal, 2 vCPU, three containers each, the median per container): 41.5, 37.0 and 29.1 s, against
  42.4, 45.0 and 53.2 s on 0.14.1 and 29.8, 41.7 and 44.8 s with no such row. The CHC track's median `proveRule` time
  stays at 0.35 s (0.33 s on 0.14.1), with 128 tasks solved (48 sat, 80 unsat), none wrongly.

## 0.14.1

- The kernel bounds an if by the sum of its two branches (when neither branch reads another term), whichever way its
  condition goes, and the Lean twin has the same row with its soundness case. A yes/no written under a wide condition
  (`if(c, 1, 0)`) now keeps its kind without the prover deciding `c` atom by atom: on CHC-COMP's LIA-Lin track below,
  the median time `proveRule` takes on a task went from 20.8 s to 0.33 s (Modal, 2 vCPU). `examples/wide.ts` (an alarm
  over 12 sensor pairs) is in the suite and checked again in Lean (`wideflag`).
- On a rule with 32 variables or more, refutation also tries one step from random states the laws allow, each variable
  of a kind drawn as its kind draws, for the laws as well as the step laws: a law that isn't inductive is refused with
  its counterexample at once instead of after the prover's whole budget. It only ever refuses; smaller rules take the
  same path as before.
- `compare/chc/`: gdp-wired on the 1,406 tasks of CHC-COMP 2026's LIA-Lin track, beside Spacer, Golem and Eldarica,
  every task in its own Modal container under the same 60 s limit. gdp-wired solves 127 (47 sat with a checked proof,
  80 unsat with a run the CHC itself confirms), none wrongly; Spacer 1,163, Golem 1,154, Eldarica 768. The gap is
  invariant inference, which gdp-wired doesn't do (its prover checks the laws you write); the table and what it found
  are in [`compare/chc/README.md`](compare/chc/README.md).

## 0.14.0

- XState machines as charts (`gdp-wired/xstate`): `fromXState(machine, {guards, actions})` reads an XState v5 machine
  (or its config) and builds the chart it runs as: nesting, a parallel root, `initial`, final states, targets as
  `#id.path`, `.child` or a sibling, targetless transitions, history nodes, root transitions, named guards and actions
  with their `params` and several actions in a row. Each guard and action the machine names is given again in
  gdp-wired's terms (an action as the context it writes, `null` for one that writes none). `conforms(chart, machine,
  createActor)` sends the same random events to XState's own actor and to the compiled rule and compares every state
  value and context: on `examples/xstate.ts`'s order (nesting, a deep history node entered through it and directly, a
  guard, two actions, a root transition), 4,800 events agree, `check()` passes and its four laws prove, in 623 ms
  (Modal, 1 vCPU); its broken variant's guard is caught as the run where the two part and its law refused, in 478 ms.
  What a chart can't run the same way is refused when built, with the reason: a parallel state below the root, `always`,
  `after`, `invoke`, `onDone`, wildcard events, several targets, inline guards and actions, entry and exit actions that
  write the context, two regions writing the context on one event, a shallow history over nested states. XState is a
  dev dependency only; the module imports nothing from it. The order is checked again in Lean (`xstateorder`).
- A chart transition with `fresh: true` enters its target at the initial states all the way down, not where a compound
  keeping its history was last (XState enters a state that way unless through its history node).
- The README and the skill say what a chart does not do yet: parallel regions inside a state, entry and exit actions,
  eventless and delayed transitions.

## 0.13.3

- A choice compares with a natural term too, as its index: `a.phase.eq(when(c, 2, b.phase.index))`.

## 0.13.2

- A chart compiles to a lighter step: a transition's source states as ranges of their indices (no disjunction over every
  state, none at all for the whole region), a transition outranks only those on its own event, and transitions writing
  the same value share one `when`. `check()` stops walking once every state has a run and proves its pairs and its
  unreached states together. On a binding lifecycle of 6 states, 12 events and 19 transitions with 19 step laws and 7
  broken variants (Modal, 2 vCPU): the laws prove in 1.7 to 2.2 s (12.5 s before), `check()` takes 18 ms (7.0 s), and
  the whole run 3.9 s (33.5 s).
- A step law broken only from a state no run reaches is refused at once too: after the random runs, `proveSteps` tries
  random states the laws allow (each scalar and cell small, kept where every law and kind law holds) and returns the
  first that breaks it, with its `witness` and no `run`. The lifecycle's two variants that the runs missed are refused in
  39 ms and 1.2 s (4.3 s and 9.6 s).
- A choice compares by name, choice or index: `phase.eq('closing')`, `a.phase.eq(b.phase)`, `phase.eq(3)`, `ne` the
  same, and `phase.index` is its index as a term (the order declared).

## 0.13.1

- Charts: internal transitions (no `to`: the state stays, nothing is exited or entered, `set` runs), outputs
  (`.outputs({...})`: what each step decides, reset to its default every step, so a step where nothing fires reads the
  default), `.states(tree, {field})` to name the state variable, and `.events(...)` to fix the events' encoding, so a
  machine already shipped keeps its names (`examples/charts.ts`: a binding's lifecycle, its counts changed by internal
  transitions and its command an output; Lean checks its laws, package-check `bindingchart`). `set` takes a choice's
  name.

## 0.13.0

- Statecharts: `chart(name)` with nested states, parallel regions, a compound's history, guards, extended state and
  final states, written as a table of transitions (`.on(event, {from, to, when, set})`) and compiled to a rule, so
  everything proven about rules holds of charts (`core/chart.ts`, `examples/charts.ts`). `check()` gives every state the
  shortest run that reaches it or a proof that none does, lists states with no way out that aren't final, and proves
  each pair of transitions as specific as each other never enabled by one request (or names the request that enables
  both). Lean checks the examples' laws (package-check `orderchart`, `checkoutchart`).
- The guide gains the statechart recipe, its code in `examples/guide.ts`.

## 0.12.7

- Both runtimes refuse a request that fails the rule's `assume`: `rule.compiled()` and `rule.interpreter()` throw a
  `RangeError` instead of taking a step no proof covers. Before, an assumption was the caller's to keep: a row of the
  resource groups naming an effect past the list was taken, and read as independent. `rule.compare` skips such requests;
  `gdp-wired/gdp`'s gate already refused them.
- A condition at every two keys whose premise is x(k) = y(k1) (a value at one key equal to a value at the other) is
  decided by a join in the compiled runtime: only the pairs whose values match are read, rows plus matches instead of
  rows squared; the interpreter reads every pair, and the two are compared on drawn maps. The resource groups at 256
  effects a side with 64 names each, disjoint, decide in 62 ms, against 5.92 s reading every pair of rows and 2.46 s for
  the loop over every pair of the pair rule (`research/perf/groups-scale.ts`, Modal, 2 vCPU):

  | Effects per side × names | Loop over pairs | Rule, every pair of rows | Rule, joined on names |
  | --- | --- | --- | --- |
  | 32 × 4 | 16 ms | 5.1 ms | 2.5 ms |
  | 256 × 4 | 366 ms | 30 ms | 9.2 ms |
  | 256 × 16 | 776 ms | 352 ms | 20 ms |
  | 256 × 32 | 1.30 s | 1.24 s | 32 ms |
  | 256 × 64 | 2.46 s | 5.92 s | 62 ms |

## 0.12.6

- A false law is refused at once, with a real run: `proveRule` and `proveSteps` first take a few random runs from the
  start (150 ms at most) and watch every law and step law on them; a run that breaks one comes back as the verdict's
  `run` (the params and each request in order) with `stuck: 'sat'`. The symbolic search had to decide every case of a
  goal to reach a model, and a goal with many instances (a condition at every two keys, read at hundreds of key terms)
  ran out its budget first: a broken variant of the resource groups below took over 10 minutes and now takes
  milliseconds. Rules that read functions known by their facts are left to the prover.
- Two groups of effects decided at every pair at once (`examples/groups.ts`): each group's effects a list, each scope
  as rows (the effect's place, a name), so a row reads its effect at the place it names inside a condition at every two
  keys. Its four laws prove in about 3 s each; the compiled rule says what checking every pair with the pair rule says
  on 2,000 drawn groups; pairs on the diagonal only, a skipped last effect, the first effect only and a group against
  itself are each refused with a run. Lean checks the four laws, one suite job each (`lean-groups-0` to `-3`, 2.7 to
  6.3 minutes on 4 vCPU); the suite is 163 jobs, 575 s of wall time and 2,741 s of job time (`runs/modal/refute3`).
- `when(c, 'closed', status)`: a choice's name beside a choice of that kind is its value (no more
  `new Choice(lit(2), status.values)`), and `status.of('closed')` names one directly.
- `rule.compare` and `fun.compare` take the reference with the runtime types of the params and inputs (a natural as a
  `number`, a choice as its names, a flag as a `boolean`, a carried list as an array of its items), so a reference
  needs no casts.
- `examples/guide.ts`: the code of the guide at gdpwired.dev/guide, run by the suite.
- `search` tries every value of a small kind (a choice, a yes/no, an `upTo` of at most 15), whatever its bound: a
  choice's fifth case was out of reach at the default bound of 2. The bound still widens naturals.

## 0.12.5

- A law over several steps may read a condition an earlier step kept at a key a later step's request names, not only at
  that step's witness (`examples/quantifiers.ts`: a child derived from its parent's grants, then used, uses only the
  parent's).
- `rule.foldsOf({Lines: [...]}, params)`: a carried list's folds at its end, computed from its items without running the
  rule (a rule whose laws are all decisions needs no state to compare its folds with the code it describes).
- (0.12.4, noted) Kernels compiled into one module no longer share an identical preamble: each declares the runtime
  helpers it calls. A helper's body is the same under its name within a release, so hoisting the union by name is safe.

## 0.12.4

- A law over several steps may read a condition a step kept: an earlier step's condition at every key is assumed at a
  later step's witness, where the later check would fail (`examples/quantifiers.ts`: a scope normalized, then rechecked
  against itself, keeps it). The prover tries it when the shared instances don't prove the law; the Lean twin's check
  lets a quantified flag's keys name a later step's variables (Sets.lean, `sframe_hyps`, proven: where the flag is 1 its
  condition holds at every key).
- A decision (`decide`) about a list a request carries assumes the folds' starts, steps and lemmas, at the list's end and
  wherever it reads the list, as the rule's step does; `crossCheckDecision` reads such a list's maps as 0 past their
  cells.
- A compiled module declares only the runtime helpers it calls.

## 0.12.3

- Lean checks by `native_decide` on request: `toLean(items, {native: true})`, or `GDP_LEAN_NATIVE=1`, or the suite's
  `--native`. Compiled Lean: a 64-step law's theorem checks in 5.9 s instead of 49 s. Each such theorem also rests on an
  axiom of its own that `#print axioms` names (it trusts Lean's compiler and runtime); the default stays on Lean's
  kernel and its core axioms.

## 0.12.0 – 0.12.2: speed

The prover, its solver and the Lean checker, profiled and rebuilt where the time went. No API changes; every
certificate still checks in TypeScript and in Lean.

| | Before | After | Reproduce |
| --- | --- | --- | --- |
| A 64-step law, proven | 87 s | 5.1 s | `bun research/perf/probe-limits.ts steps` |
| A 32-step law, proven | 8.8 s | 1.1 s | the same |
| A 32-step law, built and checked by Lean | 801 s | about 50 s | `ARGS=1 KS=32 bun research/perf/probe-limits.ts lean <dir>` |
| A 64-step law, checked by Lean (its theorem) | out of reach | 47 s | `KS=64`, the same |
| A variant of 64 cases, proven | unproven in its 20 s budget | 3 s | `bun research/perf/prover-stress.ts --family cases` |
| The search tree and sheet of rows, checked by Lean (`lean-nodes`) | 424 s | 74 s | `modal/suite.json` |
| The soundness fuzz, 32 shards | 8,795 job-s | 320 job-s | `modal/suite.json` (`fuzz-*`) |
| The whole suite, 159 jobs | 11,247 job-s | 1,404 job-s | `modal/suite.json` |

- Lean: a leaf's rows come with hints saying where to find them; rows are sparse throughout the checker (their nonzero
  coefficients alone); the certificate replay keeps its rows newest first instead of rebuilding a chain of appends;
  certificates name the hypotheses they refute; terms compare by a Boolean structural equality.
- The solver: the variable to eliminate chosen from an index built once per round, and an elimination given up before
  a round that would make more than five times its row cap (one such round built 18 million rows on a fuzz goal).
- The prover: values reused through a trie of the decisions they read; the hypotheses about the conclusion's own names
  split first (the two-key example's proof went from 445 leaves to 16); before a split, the rows the plain search sets
  aside tried by their Farkas rows (a 64-case variant needs n leaves, not about 2n²); a focused solve's two hops kept to
  two.
- The runtimes: a condition at every two keys read only as map keys decides on each cell and the keys after it.
- The suite compiles the Lean library once per version of its sources, on a Modal volume.

## 0.12.0: conditions at every two keys

- `everyKey((i, j) => ...)`, a condition at every two keys or three in a step: each key read on its own, compared with
  the others plainly (`i.lt(j)`). Decided by the runtimes on a few keys per breakpoint, closed by the kernel at the pairs
  a proof names, and checked in Lean, whose quantified flags take any number of keys (`examples/pairs.ts`: a list taken
  only when it increases, names taken only when none repeats).

## 0.11.0: trees in the state, longer step laws

- Tables of nodes (`.nodes(...)`): trees and lists of lists in a rule's state, each node made from nodes already there,
  its folds kept with it (`examples/trees.ts`: a search tree, a sheet of rows of cells).
- Folds over trees with any number of children (`fold(...).children(...)`: an org chart), folds over the lines a
  request carries that read the rule's params (`examples/invoices.ts`: metered lines).
- Step laws over up to 64 steps (up from 16).
- The runtimes call a function of several arguments on its arguments (keys past 2^53 no longer overflow).

## 0.10.0 – 0.10.1: lists a request carries, folds over trees

- `.carriesList(...)`: the lines of an invoice, with folds over them and lemmas about the folds proven by induction
  (`examples/invoices.ts`).
- Folds over trees as values, their laws proven by induction over the tree (`examples/folds.ts`).
- 0.10.1: the prover splits the conclusion's atoms first, refutes by Farkas rows at its nodes, lifts refutations past a
  split they don't read, and reuses rows.

## 0.9.0: the Lean twin takes facts about several keys

- Facts about several keys, and liveness and refinement proofs that carry them, checked in Lean; Lean checks the
  kernel's own proof of a recurrence's lemmas.

## 0.8.0: records, variants and the lemmas you state

- Records and variants as kinds, in inputs, state, results, map cells and list items (`examples/datatypes.ts`).
- `recur(...)`: a function defined by a recurrence, and lemmas about it proven by induction, which every rule that reads
  it may use (`examples/lemmas.ts`).

## 0.7.0: gdp-ts proofs from proven checks

- `gdp-wired/gdp`: gdp-ts proofs minted by checks gdp-wired has proven (`examples/gdp.ts`).
- Twelve more example domains: 187 rules across 21, each proven, broken by a real run when broken, and checked by Lean.
- The skill: `npx skills add monotykamary/gdp-wired`.

## Modal

From 0.6.0 to 0.12.3, the development ran 3,890 Modal containers in 89 runs, about 56 hours of job time: the suite, the
fuzz shards, the benchmarks and every Lean check (counted from the runs' `summary.tsv`, one container per job; the GPU
searches and the film's renders ran apart from these).
