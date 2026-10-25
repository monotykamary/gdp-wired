# Changelog

What changed since the first public release, 0.6.0 (2026-10-18). Times are measured on Modal (2 vCPU per job unless
noted), each with the command that reproduces it.

## 0.28.0

Four of the five benchmarks we run now lead clearly, in our harness (60 s on Modal, 2 vCPU, the rivals as installed in
compare/), each beside main launched with it. None wrong anywhere. One trusted change, Lean-first: the closure of a
nontermination certificate by cases (NonTerm.lean's `never_ends_of_cases`, on `propext`, `Classical.choice` and
`Quot.sound`; kernel.ts's `checkRecurCases`, conformance-tested with tampered certificates in both).
- **TermComp ITS, doesn't terminate:** 541, 538 and 540 on the task's statement, 542 per component in each of three
  batches (`runs/nt5/its1-mine` to `its3-mine`), beside main's 531 to 534. LoAT's default engine 532.
- **SV-COMP termination:** 239 in each of the same three batches, beside 223 to 225. Ultimate Automizer 224.
- **TIP 2015:** 205 of 492 proven in 3 of 3 runs (207, 207, 205), beside main's 195 and Vampire's 186 in one batch
  (`runs/tip2/final4`). Twelve of Vampire's are sorts calling `idiv`, whose definitions are contradictory.
- **TermComp ITS, terminates:** 611 to 613. KoAT2 601.
- **CHC-COMP LIA-Lin:** 1,039 to 1,044, unchanged this round (`runs/chc5/`). Spacer 1,163. PDR and a warm CDCL session
  were measured and kept on the unmerged branch gen/chc5-pdr (compare/chc/README.md).
- **The real-world corpus:** 254 of 311 laws proven, 29 refuted, 28 unknown, no timeouts (`runs/chc5/k-rw-mine`),
  against 240, 18, 53 at 0.27.0; liveness 26 of 35, against 18.

Large certificates check in Lean again: s1.t2's file from 410,471,697 bytes to 1,965,614, and a sample of 48 recurrent
sets checks 48 of 48 (`runs/nt5/`). These leads are measurements in this harness, ours to confirm under each
competition's own setup. The library (`core/` and `kernel/`, tests excluded) is 2,201,135 bytes against 0.27.0's
2,139,175. The release suites (221 jobs, one after the other) on boat: by default 240.7 s wall, 3,403.3 s of job time,
none failed (`runs/release/0.28.0-default`); `--usual` 312.9 s, 3,714.0 s, none failed (`runs/release/0.28.0-usual`).

Runs that never end in large programs, and the certificates Lean can check (gen/nonterm5), with the chained C
translation (gen/nonterm5-sv). One trusted change, Lean-first: **NonTerm.lean's `never_ends_of_cases`** (on `propext`,
`Classical.choice`, `Quot.sound`; with `simpC_evalC`, `caseNeg_eval`), mirrored by kernel.ts's `checkRecurCases`
(`checkRecur` takes either certificate) and tested on found and tampered certificates by core/conformance.ts and
lean-kernel/conformance.ts. In our harness (60 s on Modal, 2 vCPU), beside main a6d6403 launched together, two batches
(`runs/nt5/its1-*`, `its2-*`, `sv1-*`, `sv2-*`), and after merging main f589873 one beside it (`its3-*`, `sv3-*`,
`tip3-*`), every gained and lost task three times more a side:
- **TermComp ITS, doesn't terminate:** 541, 538 and 540 on the task's statement against 531, 534 and 532; per component
  542 in each against 532, 533 and 532. LoAT's default engine 532: ahead in all three batches, unconfirmed under TermComp's own setup. No
  answer contradicts LoAT's, LoAT abmc's, KoAT2's, or any tool's at TermComp 2025 (its raw data, 7 tools).
- **TermComp ITS, terminates:** 611, 613 and 612 against 611, 612 and 611 (per component 613, 613, 611 against 614,
  612, 613).
- **SV-COMP termination:** 239 (183, 56) in each batch against 225, 223 and 223; per component 210, 210, 209 against
  206, 207, 207.
  Every answer its expected verdict. Ultimate Automizer 224: ahead, unconfirmed.
- **Lean:** s1.t2's file 410,471,697 bytes to 1,965,614, the four s1 tasks checked in 68 to 89 s each (s1.t2's was
  killed at 3,300 s). A sample of 48 of the batch's recurrent sets (all 27 closed by cases, every task gained, the s1
  family and 20 drawn at random) checked, 48 of 48, at most 487.3 s, files up to 16.5 MB (`lean-final`).

What carried them (core/nonterm.ts, core/accel.ts, compare/term/c2ari.py, lean-kernel/emit.ts):
- **A closure by cases:** a translated program's closure goal reads every rule's body at each read of the set
  (pgarch's, 537,164 distinct terms, never closed). Each part of an accelerated set is a case at its location; the
  cover's tree and each case's goal, read at the pins with the constants folded, hold only that location's rules
  (pgarch's ten: 86 to 216 terms). Where the goal is past 20,000 terms, and no longer dropped past 1.5 million.
- **The time for the next candidate:** a closure tried on a set a stem reaches no longer counts against the search for
  the next; the sets whose closure ran out of time are retried smallest first, each its share by its goal's size; the
  search starts once the relation is built (up to 10 s later). Walks of up to 16 choices in the time left (hqr's
  cycle of 25 turns). A run's stem past 64 turns replaced by a shorter one where the accelerated runs' search finds it.
- **The Lean export:** a closure table holds only the choices Lean's linear forms look up (`encode`'s `reach`: s1's
  5,214 term columns to 1); a loop's start and body past 128 variables as definitions of 128 (pgarch's passed Lean's
  recursion limit).
- **SV-COMP:** c2ari composes straight-line code away (a location with one rule in or out, no self-loop), with
  unreached locations, rules into dead ends and false constant guards dropped, constant divisions folded; 12 of the 20
  tasks Ultimate Automizer answered and `gdp` didn't are answered (compare/term/README.md has the 20 by why).
- **findLeadsTo** reads the rule for its invariant search (the hand-off from gen/realworld2): the real-world corpus's
  verdicts are the same law by law beside a6d6403 (252 proven, 29 refuted, 29 unknown, 1 timeout on both sides,
  `runs/nt5/rw-*`) but tigerbeetle/transfers' laws 4 and 6, unknown and timeout swapped; opossum's "an open breaker goes
  half-open" finds `st is open → 1 <= armed` itself (10.2 s against 14.3 s).

Gained and lost, with the reruns, are in compare/term/README.md. The other benchmarks, beside a6d6403: CHC-COMP 1,041
(613 sat, 428 unsat) against 1,039 (`chc1-*`), the same two disputed labels wrong on both; TIP 198 against 199
(`tip2-*`: list_assoc, lost here and gained at 0.27.0 by chance of the time); frontier round 1 90 of 92 on both sides,
all 42 broken variants refused (`f1-*`); round 2 31 of 47 against 30 (term/Piecewise), all 47 broken variants
refused, its 5 nontermination items 5 of 5 (`f2-*`). 1 vCPU, ten jobs a side interleaved (`onecpu`): none failed;
data's agrees-with-+ test median 2,474.4 ms, at most 3,838.4 (main 2,514.3, 3,189.1); infer's "a law that needs an
invariant" 2,870.2 and 3,517.2 (main 2,803.1, 3,418.3). TIP 2015 after the merge: 206 against f589873's 204 (`tip3-*`). Suites: none failed at 53bf839, the merge, by default
(221 jobs, 452.4 s wall, 5,648.4 s of job time, `suite-default3`) or with `--usual` (429.9 s, 5,093.5 s,
`suite-usual3`), nor by default at b3e8519
(463.6 s wall, 5,591.6 s of job time, `suite-default2`); with `--usual` at d6ea665, none failed (432.7 s,
4,841.3 s, `suite-usual2`).

**Size:** `core/` and `kernel/` (tests excluded) are 2,194,592 bytes against a6d6403's 2,179,154 (+15,438, +200 lines;
after merging f589873, 2,200,224 against its 2,184,786):
kernel.ts +7,994 (the trusted mirror), nonterm.ts +3,484, conformance.ts +2,608, accel.ts +1,165, cycles.ts +173,
dsl.ts +14.

The lemma search on TIP 2015 (gen/tip2, core/data.ts): the induction hypothesis at other values of the variables an
induction leaves, an implication's instances from the values where its premise holds, Peano induction on a natural
inside a decreasing argument, and eta at a value a case says is nil. Nothing trusted changed (`kernel/kernel.ts`,
`kernel/cyclic.ts`, `core/check.ts`, `lean-kernel/` as at 0.27.0): every new proof is a cyclic proof the kernel checks,
its uses' descent included. In our harness (60 s a task on Modal, 2 vCPU, the rivals as installed in compare/tip/), three
runs a side, beside main a6d6403 launched together with Vampire and cvc5 (`runs/tip2/final4`):
- **TIP 2015:** 207, 207 and 205 of 492 proven, against main's 198, 196 and 199; 205 in all three runs against 195.
  Vampire 188, 191 and 190 (186 in all three), cvc5 with conjecture generation 187 in each (187), cvc5 168. The same 7
  refuted on both sides (the `tip2015` ones TIP writes false) and 23 of `false/`, each counterexample confirmed by TIP's
  evaluator; none wrong. Vampire's 186 include the 12 sorts that call `idiv`, refused here: `idiv x 0` is
  `S (idiv x 0)`, and Vampire derives `zero = succ zero` from that file's definitions alone (`runs/tip2/probe-idiv.log`).
  - Gained, in 3 of 3 runs and again in 3 of 3 reruns, never on main: isaplanner/prop_48 (1.4 to 3.4 s), prop_58 (2.4 to
    3.9 s), prop_80 (29 to 36 s), prop_82 (7.7 to 9.9 s), prod/prop_13 and prop_16 (under 0.4 s), prop_41 (1.2 to
    2.4 s), prop_43 (3.2 to 4.5 s). cvc5 with conjecture generation proves each of them, Vampire 5: gaps closed.
  - Lost: none. list_Select and list_assoc, 2 of 3 on main, are 3 of 3 here (`re-*`: list_assoc 3 of 3 against 2).
  - At 0.27.0 (main 548c343, three runs, `runs/tip2/b0-*`): 200, 199 and 199, 199 in all three; Vampire 192, 192 and
    188 (186 in all three); 108 refused (81 termination not proven, 21 rings, 2 existential, 2 nested recursion, 1 product
    of two integers, 1 nested datatype), 81 to 91 unknown and 87 to 97 out of time.
- **The changes:**
  - The hypothesis at other values (`attempt`, `lemmaUsesFor`'s `LemmaAt`): each use of a scheme is also a lemma whose
    descended variables are fixed and the others matched to the goal's reads like a lemma's, its descent the scheme's
    own; kept where the values matched are made by a datatype's constructors and fields (one of arithmetic alone), up
    to four a node. drop n (zip xs ys) needs it at both tails, take n (xs ++ ys) at n − 1.
  - An implication's instance models (the node's and each case's) are those where its premise holds first; its cases
    still come from all of them (x ⊆ y makes intersect (tail x) y the tail).
  - Peano induction on a natural no call of the law recurs on, where a call's decreasing argument reads it inside a
    term (even (x + x), half (x + x)); after the other schemes, merged with none.
  - Eta at a value a case's conditions say is a constructor of no field ([x]'s tail is nil).
  - Measured and left out: E-matching a hypothesis up to the goal's classes (no task gained, 15 s more on list_assoc), a
    first pass of the smallest conjectures below the law in the call graph (HipSpec's order: 3 lost, none gained),
    merged schemes at two unfoldings (none gained).
- **Other benchmarks:** the frontier corpora, round 1 90 of 92 and round 2 30 of 47 on both sides, every broken variant
  refused (42 and 47), every verdict the same, the same job killed at 200 s on both; the real-world corpus 252 proven,
  29 refuted, 30 unknown on both, every verdict the same (`f1-*`, `f2-*`, `rw-*`). CHC, ITS and SV-COMP don't reach
  core/data.ts, and weren't run.
- **Suites** (221 jobs, core/hypothesis.test.ts new: the three laws above with broken variants, each failing on main):
  none failed by default (493.5 s wall, 5,743.3 s of job time) or with `--usual` (479.1 s, 5,122.5 s).
- **1 vCPU,** ten jobs a side interleaved with main: data's nearPlus at a median 2,688.89 ms (main 2,603.36), infer's
  invariant law 2,805.36 ms (2,859.95). One job a side failed, each on a container that took about twice the others'
  time (mine-data-7 126.5 s, nearPlus 5,922.22 ms; main-data-9 139.8 s, "laws with no lemma" 12,310.10 ms); the others
  took 44.7 to 68.9 s. The hypothesis matched at a function's value or another variable had made nearPlus 4,271 ms at
  the median (main 3,001.5, `runs/tip2/near`); restricted as above, 3,274 against 3,157.5 (`near3`).
- **Size:** `core/` and `kernel/` (tests excluded) 2,184,786 bytes and 30,078 lines against main a6d6403's 2,179,154
  and 30,044 (+5,632 bytes, +34 lines), all in core/data.ts.

The real-world frontier (gen/realworld2): the corpus's 53 unknown laws of 0.27.0 classified and 23 of them closed in the
shared search, the suspected upstream bugs checked again against the current code, and the extractor reading more.
Nothing trusted changed (`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts`, `lean-kernel/` as at 0.27.0): every
new proof is the kernel's, every new refutation a run the interpreter took. In our harness (60 s a law on Modal, 2 vCPU),
beside main 548c343 launched together:
- **The real-world corpus:** 252 proven, 29 refuted, 30 unknown, no timeouts (`runs/rw2/c2-mine`), against 240, 18 and
  53 (`runs/rw2/c2-main`). 23 verdicts changed, all from unknown, none lost: 12 proven (8 liveness laws, 4 laws), 11
  refuted, each a triaged suspected bug the original code shows. Liveness 26 of 35 against 18.
  research/realworld/README.md has each of the 53 with why the search stopped and what closed it.
- **Frontier corpora:** round 1, 90 of 92 on both sides, all 42 broken variants refused (`runs/rw2/f1-*`). Round 2,
  31 of 47 against 30 (term/Piecewise, proven here and not on main, as at 0.27.0's own batch: findRank, untouched), all
  47 broken variants refused, the same job killed at 200 s on both sides (`runs/rw2/f2-*`).
- **CHC-COMP, TermComp ITS, SV-COMP, TIP:** not run. None reaches the code changed: CHC calls proveRule with
  `search: false` and inferLaws directly, ITS and SV-COMP go through compare/term and core/nonterm.ts, TIP through
  core/data.ts.

**Liveness, ranks of the rule's own terms** (core/live.ts's `leadsByTerms`, called by proveLeadsTo where findLeadsTo
doesn't prove the law, in the time left). The components come from the rule, not a fit to the runs:
- a variable its kind bounds (a chart's state, a status), ranked by the steps between its values: each strongly
  connected set of values one level, above every one it goes to;
- the distance until a comparison the rule makes changes, for each comparison of its guards, its steps, the law and
  the helpful requests (the request's inputs replaced by what it sends): `retries ∸ consumed`, `Ts(d) ∸ (t0 + now)`,
  a map cell the fit never read;
- a state variable alone, and 0.

The steps come from runs from the start and from random states the laws allow where the law is pending: a helpful
request's must lower the rank, so must one that leaves a region it was in, and none may raise it. Components are chosen
in order, each the one no step raises that lowers the most left. The kernel's counterexample to a rank is stepped by the
interpreter and added, and the ranks chosen again (Governor's queued proposal: no pending state in findLeadsTo's runs).
Then inferLaws on the rank's goals, given the rule rather than its machine (it draws by the rule's kinds: opossum's
`st is open → armed`, which it misses from the machine alone). 8 liveness laws: four charts' control levels, p-retry,
Timelock, Governor, opossum.

**Laws about ids a counter hands out** (core/fresh.ts, in `searched` before inferLaws, within a tenth of the time
left): a state variable no step lowers whose value some map's cell is written at as it goes on (an id handed out), with
each map: `∀k. c <= k → M[k]` unset, and `∀k. G[k]` unset `∨ M[k] < c` for maps of one record. Those the runs keep, then
Houdini with the kernel; the laws with them, then inferLaws with them given. lucia's deleted session, oidc's rotated
token and its reuse detection.

**The search past a step-law refutation with no run** (core/dsl.ts): proveSteps went to the verdict at once when the
random states broke a step law with no run to the state, so no search ran. It goes on now, as proveRule did: the
invariant search proves flagd's weight-0 law. With `search: false`, the verdict is as before (core/dsl.test.ts).

**Further runs** (core/dsl.ts's refuteByRuns, in `searched` after the deeper runs): 600 runs at bound 1 (keys that meet,
small params), then 1,200 at bounds 1 to 4 whose requests meet their assumption's equalities (`life = lives`) and clocks
(`now >= last`: the last time or a little past it), every fourth near the kernel's counterexample (its params and
request values half the time: keycloak's now = 2^31·1000). Each is counted in runs, not time.

**Bounded runs over one-step laws** (core/dsl.ts's `stepGhosts`): core/bmc.ts reads laws alone; a one-step law over no
key, on a machine without maps or a history, becomes a ghost set once a step breaks it (`then` read through the step's
updates) and the law that it stays unset. A run breaking it is the step law's counterexample; these runs also stop at
their wall budget, the deep ones at 10 s (bottleneck's step law took 133 s on the cost model's clock alone). Vendure's
order cancelled with a live line, at 5 steps.

**A modelling error fixed:** Gitea's DeleteReview restores the deleted review's reviewer's latest official review
(review.go:1040-1044), where the rule restored the deleting doer's (`triage/invapprove.json`).

**The suspected upstream bugs, re-checked (2026-10-24):** each of the 20 against the project's current default branch
and latest release, read-only, and its repro run again on the latest release where it has one; nothing was reported
upstream. 17 are unchanged and still happen. Three changed since the pins:
- Medusa's RETURN_ITEM is partly fixed in 2.22.1 (#17431): the positive run is refused, but a negative
  CANCEL_RETURN_ITEM still passes.
- Vendure 3.8.x clamps a negative `stockAllocated` at 0 (GHSA-8ghm-q833-cmgp), but a second release still frees another
  line's allocation.
- cockatiel 4.0.0 ignores a superseded half-open test's result, but a stale failure still reopens the circuit while
  its test runs.

None is a modelling error. Each triage entry records the refs, the lines and the command (`triage/*.json`, `recheck`);
the repros take `REPRO_VERSION` or `REPRO_COMMIT`, and `repro/recheck/` runs the two Vendure harnesses on 3.8.1.

**The extractor reads further into real code,** every rule still checked against it. TypeScript: a field holding a
function (an injected clock, random or id source), each call's answer an input, one a step; mixins written in the
files read, in the class chain; an XState factory's untyped functions called only by actors, outside the machine.
Go: a `context.Context` argument passed on only to the package's own functions; another package's struct given by
pointer, read as data, its package type-checked from the repo's source (and the check's pointer-to-struct argument,
never built before, fixed). Beside main 548c343 (`runs/extract-rw2/b1-*`, boat) the extracted sources are the same (5
of 41, 8 of the corpus's 81 current TypeScript and JavaScript sources, 1 Go) and so are their rules and the 35
example-law verdicts; 15 refusals moved further into the code (research/extract/README.md). The Go batch took 367.7 s
against 61.8 s: it now reads the imported packages too.

**Suites (220 jobs, the new `live` among them),** at 3ec46bc on Modal: none failed by default (521.6 s wall, 5,363.4 s
of job time, `runs/rw2/suite2-default`); with `--usual`, none failed (444.1 s, 4,794.0 s, `runs/rw2/suite2-usual`). The data and infer tests under the 1-vCPU
limit read none of the code changed (infer's call proveRule with laws the kernel proves at once, or `search: false`).

**Size:** `core/` and `kernel/` (tests excluded) are 2,179,154 bytes against 0.27.0's 2,139,175 (+39,979): live.ts
15,266, fresh.ts 4,501, dsl.ts +6,725; the extractor +13,487 (extract-shapes.ts +5,966, extract-read.ts +3,149,
extract-go.ts +1,991, the rest +2,381; core/go/reader.go, Go, +4,138 beside it).

The CHC-COMP gap reclassified, and an equality's two halves chosen together for cell forms (gen/chc5). Nothing
trusted changed. In our harness (60 s on Modal, 2 vCPU), beside main 1a66834 launched together (`runs/chc5/k-*`):
- **The real-world corpus:** 254 proven, 29 refuted and 28 unknown, with no timeout, against 252, 29 and 30.
  - Every verdict is the same but two, both gains: TimelockController's law 0 (`∀k. Runs[k] is 1 → Ts[k] = 1`, its
    two halves; proven in 5.0 s, main unknown at 19.0 s; 3 of 3 runs, and main 0 of 3, in `hr-rw`) and blnk's law 5
    (`balance = credit − debit` at every key; 49.1 s, main unknown at 56.2 s; 3 of 3 against 0 of 3).
  - TigerBeetle's law 6 ends unknown at 116.5 s (main 124.4 s); the corpus's longest law here takes 117.5 s (main
    124.4 s).
  - Its earlier timeout at 150 s was wall time, not the rule: with the rule on, with it off, and on main, the law's
    invariant search counts the same work (66,406 counted ms), and the law ended in 75.7 to 131.2 s across five runs
    (`tb6-d2`, `tb6-diag`).
- **CHC-COMP LIA-Lin:** 1,039 (612 sat, 427 unsat) against 1,040 (614, 426), none wrong, the same 2 disputed labels.
  - The path is main's: the rule reads only cell forms, and CHC has none.
  - The 16 tasks that differ or timed out, run three times a side, answer 21 times on each side.
- **Suites (221 jobs):** none failed by default (368.5 s wall, 5,362.6 s of job time) or with `--usual` (464.2 s,
  5,204.8 s).
- **1 vCPU, ten jobs a side:** none failed. data's nearPlus took a median of 2,762.43 ms, at most 3,251.88 (main
  2,731.20, 3,290.42). infer's "a law that needs an invariant" took 2,904.40 and 3,118.45 (main 2,581.26, 3,097.75).

What changed:
- **The gap at 0.27.0** (compare/chc/prof/gap27.py): 251 tasks, 217 sat and 34 unsat.
  - On 166 of the sat tasks the join ran out of time. Of the 217, the kernel proves 140 with Spacer's invariant.
  - The unsat tasks are deep Lustre runs. The bounded runs reach depths 9 to 12, where Golem's derivations take 12 to
    24 steps.
- **The halves:** a cell form the kernel's search below the join chooses brings its mirror (`−Σ ≤ −d` beside `Σ ≤ d`,
  the same guard) where that is alive among the candidates.
- **A warm CDCL session for the join's queries, and PDR over its cubes, are kept on branch gen/chc5-pdr, unmerged.**
  compare/chc/README.md has their batches.
  - On 318 dev tasks PDR answers 110 to 116 sat against the join's 105 to 112.
  - On the whole track every placement of it cost as much as it gained: first, after the join, on the second CPU, or in
    k-induction's turn.
  - The session cut the join's nodes a query from 235 to 28, but lost tasks the cold join answers.
  - Three more rules were measured and dropped, each costing CHC tasks: a request gate on the walks, a candidate dropped
    after four stuck goals, and the halves on scalar forms.

**Size:** `core/` and `kernel/` (tests excluded) are 2,201,135 bytes and 30,285 lines, against main 1a66834's 2,200,224
and 30,278: +911 bytes and +7 lines, all in core/infer.ts.

## 0.27.0

The search's shared engines got faster and more general, and a second language front end joined the extractor. None
wrong anywhere, and nothing trusted changed since 0.26.0 (`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts` and
the Lean files as they were). In our harness (60 s on Modal, 2 vCPU, the rivals as installed in compare/), each beside
main launched with it:
- **CHC-COMP LIA-Lin:** 1,035 (610 sat, 425 unsat) beside 1,019 (`runs/query/m5/chc-mine`, `chc-main`); 1,039 beside
  1,023 in `runs/query/m4`. Spacer 1,163.
- **TermComp ITS, doesn't terminate:** 532 (`runs/query/m4/its-mine`), 530 to 535 across this round's batches, per
  component 532 to 535 (`runs/closed/`). LoAT's default engine 532: level.
- **TermComp ITS, terminates:** 610 to 614. KoAT2 601.
- **TIP 2015:** 198 beside 196 (`runs/query/m5/tip-*`), 199 beside 194 in `runs/query/m4`. Vampire 193.
- **SV-COMP termination:** 224 to 225. Ultimate Automizer 224.
- **The real-world corpus:** 240 of 311 laws proven, 18 refuted, 53 unknown, no timeouts (`runs/query/m5/rw-mine`),
  against 237, 18, 56 at 0.26.0.

These are measurements in this harness, ours to confirm under each competition's own setup. What carried them: the
kernel's CDCL keeps its rows from node to node (1.2 times the nodes a second on the step goals, 1.4 on CHC's join, 2.4
on its bounded runs, 18 on the large false goals), a cost model counts the kernel's work so k-induction, the bounded
runs and `grow`'s own budget run on the counted clock, the join's cubes read the rule's own comparisons, one
closed-form engine serves `discover`, the cycles and the stems, and the extractor reads Go beside TypeScript through
one check driver. The library (`core/` and `kernel/`, tests excluded) is 2,139,175 bytes against 0.26.0's 1,943,031,
about 140 KB of it the Go front end. The release suites (219 jobs, one after the other) on boat: by default 184.0 s
wall, 2,725.4 s of job time, none failed (`runs/release/0.27.0-default`); `--usual` 238.7 s, 3,344.5 s, none failed
(`runs/release/0.27.0-usual`).

A kernel query costs less: the CDCL search keeps its rows from one node to the next, and the reader finds again only
the values a change touches. A cost model counts what a query does, and the two budgets 0.26.0 left on wall time are
counted in it. Nothing trusted changed (`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts` and `lean-kernel/` as
in 0.26.0). Every figure below is from a batch launched together with main 3cc00e3 on Modal (60 s, 2 vCPU),
`runs/query/m4` in the main checkout, unless another run is named. These are measurements in our harness, unconfirmed
under each competition's own setup.

- **CHC-COMP LIA-Lin:** 1,039 (615 sat, 424 unsat) against main's 1,023 (615, 408). None wrong, and the same 2
  disputed labels on both. 22 gained and 6 lost; each was run again three times a side (`chcr1`..`chcr3`).
  - Gained every time, never on main: DRAGON_14 ×5, FIREFLY_a3 ×2, car_5 ×5, metros_2_e1_1116_e3_287, swimmingpool
    ×3 and ticket3i_7_e8_2126_e7_78. They are unsat answers by the bounded runs, which now go 2 to 3 depths further
    (car_5 reaches depth 12 where main stops at 10). The exception is ticket3i, which is sat.
  - Lost every time: car_2_e7_1027_e1_1047, sat on main by the join in every run. The join blocks other cubes here
    (CDCL's models differ), and its 14th round runs out of time. SYNAPSE_4 is lost in 2 of 3 runs.
  - The others answer on both sides in some runs.
  - Spacer 1,163 and Golem 1,154 lead.
- **TIP 2015:** 199 of 492 proven against 194, the same 7 refuted, none wrong. 5 gained (prop_60, prop_12, list_Select,
  list_assoc, list_nat_Select), each in 2 or 3 of 3 runs again on each side. None lost. Vampire proves 193 in this
  harness (0.25.0's batch): 199 is ahead, unconfirmed.
- **TermComp ITS:** 1,146 (614 terminating, 532 not) against 1,141 (610, 531). 6 gained, 1 lost (db3.t2_fixed). Run
  three times a side, each of the 7 answers equally often on both sides, except s1-striped.t2_fixed (2 of 3 here, 3 of
  3 on main). LoAT's default engine proves 532 nonterminating: level, not ahead.
- **SV-COMP termination:** 224 (169, 55) against 225 (170, 55). Every answer is its expected verdict. The one task
  lost, Singapore-2, answers 1 of 3 times on each side.
- **The real-world corpus** (`runs/query/m5`, after the translation's fix below, beside main 3cc00e3): 240 proven, 18
  refuted, 53 unknown and no timeout, against 237, 18 and 56. Every verdict is the same but three, each a gain:
  ledger/tigerbeetle/transfers' laws 2, 3 and 5, proven in 60.3, 79.9 and 68.5 s, unknown on main at 105.0, 107.5
  and 106.4 s. Its laws 4 and 6 end unknown in 107.2 and 115.4 s (main 106.2, 106.8).
  - Before the fix (`runs/query/m4`): laws 3 to 6 timed out at the 150 s kill, and law 2 was proven in 142.9 s.
  - Why: the faster search proves the laws' goal "every T cell is a value of its kind @step" in 10.4 s, where main
    gave up at its 20 s budget (`runs/query/tb1`). The cyclic certificate's translation of that tree, 9,523 to 21,108
    leaves, then took 92.7 s of a law's time (`runs/query/tb2p`, `tb3log`). It read both goals' leaf rows afresh with
    kernel.ts at each leaf, and the leaves whose rows weren't all there were solved again on the node's whole goal.
    usedHyps read every leaf's rows again too (22.6 s, `tb4p`). Its 60 s bound was wall time, read only where a leaf was
    grown again.
  - ledger/openzeppelin/RefundEscrow's laws 0 and 1 are proven in 9.0 s and 9.1 s (`runs/query/rw1`). These are the
    k-induction laws that ran out of memory when 0.26.0 first counted the search's budget.
- **Frontier corpora:** round 1, 90 of 92, with all 42 broken variants refused, every verdict the same as main's.
  Round 2, 31 of 47 against 30 (term/Piecewise), with all 47 broken variants refused. One job was killed at 200 s on
  both sides, as before.
- **research/dag's 332 step goals:** all 332 proven on both sides; 297 trees differ from main's, 35 are the same.
  Summed search time is 283.1 s against 353.6 s. Per goal, here/main is 0.706 at p10, 0.833 at the median and 0.976
  at p90 (`g332`, both sides in one container per goal). kernel/cdcl.test.ts passes with `GDP_CDCL_VERIFY=1`, which
  compares the kept rows with kernel.ts's at every node (`runs/query/fuzz-x5`).
- **Suites (219 jobs):** none failed by default (550.6 s wall, 5,352.3 s of job time) or with `--usual` (570.8 s,
  4,865.2 s); after the translation's fix, none either way (466.1 s, 5,635.2 s; 437.3 s, 4,890.4 s; `runs/query/m5`).
- **After the translation's fix** (`runs/query/m5`, beside main 3cc00e3): CHC-COMP 1,035 (610 sat, 425 unsat)
  against 1,019 (613, 406), none wrong. Of the 11 lost, run three times a side, four are lost in each run or all but one
  (gulwani_cegar2, SYNAPSE_4, car_2_e7_1027_e1_1047 and car_2_e8_491_e7_826: the join on another path, as above); the
  others answer as often on both sides. TermComp ITS 1,141 (611, 530) against 1,142 (611, 531). TIP 198 against 196.
- **1 vCPU,** ten jobs a side interleaved with main, none failed. In an earlier batch, main db0369f failed one: data's
  nearPlus at 5,389.34 ms (`runs/query/m3/onecpu`). In this batch:
  - data's nearPlus: median 2,403.07 ms, at most 3,108.12 (main 2,351.16, 2,768.43).
  - infer's "a law that needs an invariant": 2,239.70 ms and 2,909.15 (main 2,698.39, 3,665.57).

**Where a query's time went** (`runs/query/prof-g332`, `prof-reps`: bun CPU profiles of every root query of the 332
goals, CHC sat and unsat tasks, s1 and hqr, and the false 944-hypothesis step goals, at 0.26.0). The same few places
were hot in every case except ITS.
- At each CDCL node, every row was rebuilt from all hypotheses' facts, then deduplicated by text, then loaded into the
  simplex whole. This took 20.7 to 38.3% of the time.
- The candidate atoms were listed for every hypothesis, and bound propagation scanned all rows and all candidates.
  The lists alone took 10.7 to 27.7%.
- Simplex pivots were 0.0 to 0.5 a node; the arithmetic was cheap.
- On the false step goals, 159,895,024 candidates were scanned over 12,777 nodes (`runs/query/cal1`), and pairs of
  cells were made again with their texts at each node.
- ITS's time was mostly outside the queries (the relation's generators, runs, rank LPs). Its closures' kernel check
  took 12.4% of it.

**What changed** (kernel/cdcl.ts, kernel/reader.ts, kernel/simplex.ts, kernel/prove.ts; untrusted).
- **The rows kept** (reader.ts's `sync`): the live rows go from one node to the next. A node remakes only these:
  - the trail's rows by position;
  - each hypothesis conjunct whose read a change touched (a hypothesis' facts are kept by conjunct);
  - the rows these bring as the names they read come and go: a natural's row per name, each term column's rows, and
    each pair of cells' rows.
  There is one row per form, the first of its copies with the shortest reason. `GDP_CDCL_VERIFY=1` checks the set
  against kernel.ts's at every node.
- **The simplex given what came and went** (`assert`, `retract`, `settle`): a form that comes in and goes out
  between two runs never reaches it. A new tableau gets its rows in kernel.ts's order. Bound propagation reads a
  tableau of single-variable bounds of its own. An atom whose bounds haven't changed since it was found unforced is
  not checked again.
- **The elimination gets the rows in kernel.ts's order.** In the live rows' order, its bounded run gave up where
  kernel order refutes: s_multipl_17's `i0 mod 6 = 0 @step` took 15 s against 0.1 s.
- **The reading made cheaper, with the same search.** These steps kept all 332 trees the same, and saved 6.5% of the
  time on their own (`runs/query/ab2-g332`):
  - forms and names numbered, and stamped by node;
  - pairs of cells made once;
  - a read edge to an earlier finding dropped when a change walks past it;
  - a reason inside another not copied.
- **Candidates by variable**, each list's variables kept with the list. A decision's phase is set at the point for
  the atom decided. Pairs of cells come from the reader's live cells and are made again only when those, or the
  decisions about pairs, change.

**Query time, before and after, on the same tasks** (`runs/query/m4`; both sides log every root query; main is
3cc00e3 with research/query's logging patch).

| Tasks | Main's queries a second of CDCL nodes | Here |
| --- | --- | --- |
| The 332 step goals | 355 (median query 718.6 ms, p90 2,131.6) | 441 (604.1, 1,540.4) |
| CHC sat, 11 Lustre and ctigar tasks (the join) | 470 (12,403 queries, median 7.5 ms, p99 520.7) | 680 (13,204, 9.2, 450.9) |
| CHC unsat, metros and car (k-induction and the bounded runs) | 173 (median 1,898.5 ms) | 415 (1,333.5) |
| The false step goals (944 hypotheses, 120 s) | 15 | 268 |
| ITS (s1, hqr, pgarch, slayer-3-new, edn) | 48 | 45 |

- **The handed-off goals:**
  - The join's model-only queries, PDR's kind (gen/invariants2), at their median: dillig19 39.1 ms against 43.0,
    FIREFLY_6 98.0 against 183.7, DRAGON_4 219.9 against 352.6, nest-if6 116.0 against 133.3.
  - The small queries cost about as much as before: each starts the reader cold.
  - ITS's s1 tasks' two root queries took 13.0 to 23.9 s together, on both sides alike. The kernel's closure check
    and the goal's size bound them. CDCL nodes cost the same there, so hqr, pgarch, slayer-3-new and edn stay unknown
    on both sides.

**The cyclic certificate's translation** (core/translate.ts, core/cyclic.ts, kernel/prove.ts, kernel/cdcl.ts;
untrusted):
- **The node's rows at each leaf** come from a reader whose trail follows the translation's path (reader.ts's leaf
  rows: only what the step between two leaves' paths changed is read again). A path about a term column, a cut's,
  is still read by kernel.ts. `GDP_CDCL_VERIFY=1` compares them with kernel.ts's at every leaf; core's and research/hw's
  tests pass with it.
- **The usual leaf's rows** are kept as CDCL's unfolding made them (prove.ts's `leafRowsOf`), for the translation and
  for usedHyps.
- **The translation is on the cost model's clock** (cyclic.ts's `counting`, its bound the time it had, counted; the
  leaves' rows counted, `translateRows`), so a large tree's translation stops at its bound on any machine.
- ledger/tigerbeetle/transfers' translations took 20.2 to 25.7 s, against 40.0 to 60.6 s with the counted bound
  alone and 92.7 s on wall time (`runs/query/tbc5`, `tbc2`, `tb3log`). Laws 0 to 7 ended in 42.1 to 109.1 s
  (jobs' seconds), the longest law 6, against 140.0 and 152.1 s for laws 4 and 6 with the bound alone.

**The cost model and the counted budgets** (kernel/prove.ts's `fullWork`, `counted(…, full)`; core/bmc.ts;
core/dsl.ts).
- **The model:** each kind of the kernel's work, weighed to its time on a Modal 2-vCPU container: elimination's pairs,
  the float simplex's cells, the plain search's rows a node, the values the reader finds again, the live rows'
  copies, the read edges walked, the candidates scanned, the pivots' rows, the root's rows for units, the unfolding's
  rows, and the goal's nodes. The weights come from research/query/fit.py on 7,027 root queries of 20 ms or more
  (`runs/query/cal2`).
- **The spread:** work.n did 28 to 377 units a ms (p10 to p90); the model does 120 to 401. On queries of 10 s or more,
  the median by group is 163 to 271.
- **grow's own budget**, where its caller gives none and outside `counted`, is the model's work: 180 units a ms of the
  second a hypothesis.
- **The search proveRule falls back on:** its bounded runs and k-induction are counted on the model's clock with no
  wall stop. Their forced run is counted in steps. This needs no memory blowup (RefundEscrow above), and no
  real-world verdict changed by it. The tigerbeetle laws change by the speed.
- **The resumable bounded search** (compare/chc/kind.ts's second CPU) reads the model's clock, so a slice takes about
  the wall time it is given. On work.n's clock it stopped before its slice's end, its counted budget spent: the
  faster nodes now run that clock about four times past wall time (CHC unsat's model queries: a median 979 units a
  ms of work.n, `runs/query/cal2`). This is where the CHC unsat gains come from.
- **findBoundedRun keeps work.n's clock** unless asked (`full`). core/nonterm.ts's bounded runs from a closed set were
  set against it. On the model's clock, s1.t2 and s1.t2_fixed timed out (`runs/query/its-mine`). On work.n's clock,
  they answer (`its2-mine`).

**Size:** `core/` and `kernel/` (tests excluded) are 2,139,175 bytes and 29,549 lines, against main 3cc00e3's
2,103,360 and 28,962 (+35,815 bytes, +587 lines). By file: reader.ts +15,114, cdcl.ts +5,703, prove.ts +5,459,
simplex.ts +4,664, translate.ts +2,778, bmc.ts +766, cyclic.ts +719, solver.ts +534, dsl.ts +78; the translation's
fix is 5,213 of it. The non-incremental node is gone, and its flag with it.
research/query/ holds the profiler, the runner, the fit and the comparisons, outside the library.

One closed-form engine for what a loop does after n turns, and the nonterminating ITS tasks it reaches: TermComp's ITS
per component 533 to 535 nonterminating against LoAT's default engine's 532, ahead in each of three batches launched
with main at e883e53 (527 to 531 there), 532 and 533 after merging main at db0369f (529 and 531 there); on the task's
statement 529 to 531 against main's 526 to 528, 1 to 3 behind LoAT, 532 and 530 after the merge (528 and 530). In our
harness (60 s on Modal, 2 vCPU), unconfirmed under TermComp's own setup. Nothing trusted changed (`kernel/kernel.ts`,
`kernel/cyclic.ts`, `core/check.ts`, `lean-kernel/` as at 0.26.0): each answer is a recurrent set kernel.ts's
`checkRecur` checks, NonTerm.lean's `never_ends_of`. compare/term/README.md has the batches, every task gained and lost,
and what was left out.

- **The engine** (core/accel.ts's `closedForm`, `nfold`, `polyOf`, `closedAt`, `accelerate`): a run of linear forms (a
  form along an affine update, g(Uⁿx), or the numbers of a function's values) as Σ c·C(n, k)·rⁿ over the integer roots
  of the shortest recurrence every given term meets (exact over the rationals; a form of an affine update meets it
  everywhere once it meets it at its first terms, numbers only where every window does). Polynomial, geometric and
  triangular updates have one; Fibonacci's doesn't. `accelerate` reads a translation's n-fold turn and its metering
  function (an atom of the guard that rises by 1 a turn: the count, linear in the state; the guard's other atoms at the
  first and the last turn, so throughout).
- **Its callers.** core/discover.ts's closed forms of degree 2 and 3 come from it: the recurrence's own where its step
  is affine in f and a polynomial in x (squares, the pyramid: the engine on f and x, x·x, x·x·x), else the values', each
  checked against every sample as before (the same lemmas found: core/discover.test.ts, examples/discover.ts). The
  accelerated cycles take inner loops to their end (a self-loop or a cycle of two turns that is a translation with a
  metering function: one step of a walk, its count linear in the state, a part of the set at each of its turns); the
  stems take a self-loop with a closed form many times at once (a translation n times, as before; any other, a doubling
  loop, 2 to 16 times). The cycles' differences are its iterates differenced, as before.
- **Products with a turn's input** (RandomHard's arg2 = arg3·x, which the relation leaves out): the loop's cases with
  the state value or param fixed at 1, 0, −1 or 2, each the relation of the loop whose condition fixes it first, the set
  holding it fixed; 30% of the stage's time where there are such cases.
- **Stems by deepening**: a set the stem search, run to its end, doesn't reach is searched again at twice and four times
  the depth (with 4 and 16 times the calls), at once for the first four such sets (500 ms each) and after a set's
  closure (fun9's stem of 30 turns, past the depth of 8 and a bounded run's 24).
- **Inputs from the rest of the cycle** (`lookahead`): a turn's input chosen as a bound the cycle's later turns put on
  it, over the state at that turn (MysteriousProgram's reset of a bound to the one the next turns need). After the
  relation's cycles and those with inner loops.
- **Time**: the relation built once a loop (the cases' search had built it again: agafp's, 822 and 854 ms on a laptop);
  a random run stopped at its phase's end (one run of agafp's 140 locations took a whole search).
- **Beside main at e883e53**, three batches launched together (`runs/closed/its-mine-2` to `-4`, `its-main-2` to `-4`,
  `sv-*`): ITS on the task's statement 1,141, 1,144 and 1,142 solved (612 to 613 terminating, 529 to 531 not) against
  1,137, 1,139 and 1,139; per component 1,147, 1,145 and 1,146 against 1,143, 1,141 and 1,139. Gained in each:
  MysteriousProgram, RandomHard, fun9; agafp.t2 and its twin in the last two. Lost: lassos and closures at the limit on
  both sides (db2 and db3's `_fixed`, the s1 family, 36.58 to 59.73 s), terminating answers at 58.44 to 60.08 s. SV-COMP
  225, 224, 225 against 225, 224, 224 (per component 207, 206, 206 against 207, 206, 207), every answer its expected
  verdict; its moving tasks, five runs a side (`svre-*`), within the same counts. No answer contradicts another's in the
  13 ITS runs read.
- **After merging main at db0369f**, two batches beside it (`its-merged-1`, `-2`, `its-main2-1`, `-2`, `sv-merged-1`,
  `sv-main2-1`): ITS nonterminating 532 and 530 on the task's statement against 528 and 530, per component 532 and 533
  against 529 and 531 (LoAT 532: tied, then led by 1 per component); terminating 610 and 614 against 612 and 613, per
  component 613 and 611 against 612 and 612, each loss at 55 s or later. SV-COMP 225 against 224, per component 207 and
  207.
- **The other benchmarks**, launched with main: CHC-COMP LIA-Lin 1,004 (595 sat, 409 unsat) against 1,001 (591, 410),
  the same two disputed labels on both, none other wrong (`chc-mine-1`, `chc-main-1`; 13 tasks answered on one side,
  each at 17.31 s or later); TIP 2015 199 proven against 198 (`tip-mine-1`, `tip-main-1`: isaplanner's prop_60 at 57.37
  s here). The corpora, every item as main's: round 1 90 / 92, broken 42 / 42; round 2 30 / 47, broken 47 / 47, its
  nontermination items 5 / 5, broken 5 / 5; the real-world corpus 237 proven, 18 refuted, 56 unknown, law by law (`c1-`,
  `c2-`, `rw-mine-1`, `-main-1`). The suites (218 jobs) on Modal: by default 593.5 s wall, 5,337.0 s of job time, none
  failed (`suite-default`); `--usual` 553.5 s and 4,979.3 s, none failed (`suite-usual`). The 5 s tests on 1 vCPU, ten
  jobs a side interleaved twice (`onecpu-1`, `-2`), none failed: `data`'s nearPlus at most 3,484.95 and 3,179.47 ms here
  (medians 2,576.01, 2,602.35), 2,987.93 and 3,317.47 on main (2,536.98, 2,379.18); `infer`'s "a law that needs an
  invariant" 3,546.35 and 3,150.34 here, 3,734.60 and 3,732.28 on main.
- **Lean** (`runs/closed/lean-1`, Lean 4.34.0, `recur-lean.ts`): 39 of 40 certificates are theorems `NeverEnds
  <task>_loop` on `propext`, `Classical.choice`, `Quot.sound`: the six new ones of `its-mine-4` but s1.t2
  (MysteriousProgram 96.5 s, RandomHard 13.9 s, fun9 48.4 s, agafp.t2 183.2 s, agafp.t2_fixed 251.7 s) and 34 of the
  run's other accelerated sets drawn at random. s1.t2's is too big: its Lean file 410,471,697 bytes, killed at 3,300 s.
- **Left out:** the inner loops among the first walks, KnapsackDP's counted loops dropped for them (its inner loop is no
  translation: no candidate); the second search's accelerated share 0.6 (`its-varA-1` beside `its-mine-5`: 529 and 530
  nonterminating against 531 and 534); a rank from a closed form for the terminating side (LogMult's x := x·x below a0:
  the rank a0 − 1 − x, its guard atom's first difference x·x − x ≥ 2, has its step goal unproven by the kernel within 5
  s, products' facts and real models on; the translations' metering functions are linear ranks findRank's LP finds
  already).
- **Size**: `core/` and `kernel/` (tests excluded) 1,964,655 bytes and 26,790 lines against 0.26.0's 1,943,031 and
  26,476 (+21,624). The engine is 7,862 bytes (126 lines); discover's closed forms 3,059 bytes for its 1,637.

A second language for the extractor: Go (`core/extract-go.ts`, untrusted), on the same Model, printer and rule as the
TypeScript one. Nothing trusted changed (`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts` and the Lean files as
in 0.26.0).

- **Why Go**: of research/realworld's items, 8 have their rule in Go and 4 in Solidity (in the 41-source list, 6 and 4).
- **The reader**: core/go/reader.go (go/parser and go/types, built and run with the Go toolchain) prints a package's
  typed AST as JSON; core/extract-go.ts executes a struct's methods symbolically into core/extract-read.ts's Model.
  Integers are Go's: 8 to 32 bits wrap modulo 2^n by cases (as compare/term/c2ari.py takes C's unsigned arithmetic), 64
  bits stop at the rule's ±2^53 with a uint64 below 0 refused, division truncates toward zero; pointers alias (interior
  pointers too), struct values copy, `*big.Int` is unbounded with nil a state of its own, maps and slices (as lists),
  switch, early returns, a mutex's Lock with its deferred Unlock; an error that isn't nil and a panic are refusals, the
  state as it was (or dropped where the caller drops it: `onError: 'discard'`, cited in research/extract/go-options.json).
  Refused where they are: loops (a range over a map besides), slices under a second name, other defers, recover,
  floats, interfaces, generics, the clock, another module's code.
- **The check**: core/extract-check.ts's `drive` with Go's code side: the package built in its own module with a
  generated harness (`go build -cover`), spoken to through two named pipes (runs from the start, drawn states with the
  types' edges, the prover's witnesses), every state, result and refusal compared, the fields the rule leaves out
  asked to be unchanged; a model edited to forget the uint8 wrap is refused by it (core/extract-go.test.ts, 16 tests:
  overflow at each width, aliasing, maps, slices sharing a backing array, defer, panics, errors after a write).
- **Shared, not copied**, each step measured on its own with the extract job's rows and rules (22 and 41 sources),
  the Go corpus's rules and rows, 52 + 16 tests and both suites (`runs/front-go/step3`, `step2`, `step1`):
  - core/extract.ts's printing, build and invariants are `fromModel`, called by both front ends; the Model takes the
    laws a front end knows (`laws`: a field within its type);
  - one evaluator at concrete values, `evalTerm` with map cells and list items (−1,055 bytes);
  - one check driver, `drive`, with a pluggable code side (`CodeSide`), the TypeScript VM's and the Go harness's
    (−4,138); every TypeScript row the same, and Go's rows the same but for two counts, which now mean what the
    TypeScript check's do: `requests` the runs' steps alone (2,400 and 2,263, were 2,824 and 2,691) and `fromStates`
    the drawn states alone (400, were 424 and 428), the witnesses counted in `probes`;
  - one merge of a map's write and of a list's operations by a condition (`mergeWrites`, `mergeOps`) for both
    readers, and the Go reader's results joined as locals (−53);
  - dropped: one path-join core for both executors (`mergePaths`), +1,149 bytes over the two joins it replaced.
  `core/` and `kernel/` (tests excluded) 2,083,720 bytes and 28,697 lines against 0.26.0's 1,943,031 and 26,476, and
  2,088,966 before the sharing (extract-go.ts 108,240, extract-go-check.ts 27,966, the shared files +4,483;
  reader.go's 20,138 bytes are Go, outside the count, and outside the package: dist's 87 files don't reach it).
- **The corpus's Go code** (`runs/front-go/go2`, research/extract/results/go/): of 25 Go sources (8 items), gobreaker's
  `Counts` (an `also`) extracted whole (2,824 steps beside Go, 8 of 8 blocks) and blnk's Balance in part (5 of its 7
  methods, 2,334 steps, 34 of 34 blocks); 24 refused (an interface 7, another module's type 6, floats 3, not code 3,
  not a declaration 2, generics 1, a loop 1, the clock 1). Of the two items' 13 laws, 3 have a statement on the
  extracted rules and all 3 differ from the hand's (proven by hand, refuted on the code), each explained: the item's
  step is a whole transaction where the code's methods are its parts, and its amounts are validated by UpdateBalances,
  which is refused (floats); 10 read ghosts or the CircuitBreaker's state, which the extracted code doesn't keep.
- **Beside main e883e53, on boat** (`runs/front-go/extract-mine`, `extract-base`): the extract job the same (52 of 52
  tests; 22 and 41 sources with the same rows and rules; 36 of 36 verdicts) and the corpus's 33 laws on the extracted
  XState rules the same. The suites with the new `extract-go` job, 219 jobs: by default none failed (251.2 s wall,
  3,313.5 s of job time, `runs/front-go/suite-default`), with `--usual` none failed (236.7 s, 3,012.1 s,
  `runs/front-go/suite-usual`); after the sharing (146ca37, `runs/front-go/step1`) none failed either (250.4 s and
  3,310.6 s by default, 230.6 s and 2,865.7 s with `--usual`).

The invariant search's cubes read the rule's own comparisons (core/infer.ts, the join). CHC-COMP LIA-Lin in our
harness (60 s on Modal, 2 vCPU, the rivals as installed in compare/): 1,023 solved (613 sat, 410 unsat) beside main
e883e53's 1,001 (592, 409) launched with it (`runs/inv2/chc3-mine`, `chc3-base`), and 1,026 (617, 409) beside 1,001
(592, 409) in the batch before (`chc2`); none wrong, the same 2 disputed on both. Spacer 1,163, Golem 1,154. Nothing
trusted changed (`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts` and the Lean files as in 0.26.0).

- **The cubes.** A counterexample to a caller's law is blocked as IC3 blocks one; its cube's literals now read the
  rule's own comparisons true there (`comparisons` keeps each comparison's bound: Σ t·v ≤ d and its negation) beside
  its control values and the samples' bounds, so a cube where no sample is (a location the runs never reached, where
  the cube was the control values alone and its predecessors walked it back toward the samples) reads the guards
  that led there. Predecessors are blocked 8 deep (3). The cube comes first where no sample holds the
  counterexample's control state, else after the candidates as before; the window that gave the join 0.3 of its time
  once a cube was in goes. A cube blocked twice in one chain no longer ends the join (a law declared twice).
- **The join's share** is an option (`InferOptions.join`, 0.6 as before); compare/chc/solve.ts passes 0.8.
- **CHC-COMP, gained 27 and lost 5** (compare/chc/README.md, "after 0.26.0", has each): s_split_17, 37, 38, HOLA/04,
  reve 013, 013b, 014, 015, llreve break and break_merged, ctigar gulwani_cegar2, dillig37, up4, Lustre car_2 ×3,
  car_all ×3, SYNAPSE_4 and 7 more main solves in some of its five runs. Lost: PRODUCER_CONSUMER_2 (main 5 of 5;
  here its counterexamples, at control states no sample holds, are blocked first, a cube a round until the join's
  time ends), s_split_42 and loop__fib_000_002 (a cube blocked 8 deep counting a bound up one value at a time, where
  main's 3 deep failed at once and the search below answered; 1 of 2 here), up3 and durationThm_2 (main 2 and 3 of
  5, here 1 of 2). By group: C 19 → 24 of 38, D 25 → 31 of 116; Lustre 601 → 607, ctigar 34 → 41 (`chc2`). The gap
  to Spacer and Golem: 263 (211 sat, 52 unsat) against 281 (229, 52); of the 154 sat-gap tasks whose Spacer
  invariant the kernel proves, 18 solved against 4.
- **Measured and left out** (the README has each run): PDR frames over the join's cube machinery (frames of blocked
  cubes, obligations as the kernel's predecessor points, lemmas pushed): before the join 93 and 80 against 101 on
  the 254 tasks of `research/inv/dev.json`, from the start 75 against the join's 104, after the join 100 against 101;
  at 300 s it converged on 6 of 154 with 43 to 66 lemmas, each query 12 to 170 ms locally. Also: cubes at the rule's
  constants, Houdini-seeded control cubes, a deadline for one counterexample's cubes, the depth counted at sampled
  control states, `down`'s 12 or 48 queries, 96 cubes, 16 tries.
- **The other benchmarks**, each beside main launched with it: TermComp ITS 1,140 (613 terminating, 527 not) against
  1,139 (613, 526) (`its3`) and 1,142 against 1,140 (`its2`), every difference at 39 to 60 s (s1.t2's accelerated set:
  9 of 10 here, 10 of 10 on main, 38.5 to 67.9 s and 39.2 to 62.1 s, `s1rep`); SV-COMP 224 against 225 (`sv2`) and
  225 against 226 (`sv`), each at 45 to 59 s on main, where findRank's sampling, bounded by wall time, found no rank;
  TIP 195 against 198 (`tip`): proveData reads no invariant search, and each task lost was proven at 53.6 to 59.2 s
  on main.
- **The corpora.** Frontier round 1: 90 of 92, 42 of 42 refused, every verdict and every law found the same
  (`fr1b`). Round 2: 31 of 47 against 30, 47 of 47 refused on both (`fr2b`): chc/D/gulwani_fig1a proven (in `fr2`
  too), the rest the same. The real-world corpus: 237 proven, 18 refuted, 56 unknown on both, every verdict the same
  (`rwb`); gapless.js's law 2, at the edge of its 60 s: 8 of 8 on each side (34.3 to 55.8 s here, 31.9 to 58.3 s on
  main, `onecpu-b`).
- **Suites and 1 vCPU.** By default 218 jobs, none failed, 619.8 s wall, 5,485.7 s of job time
  (`runs/inv2/suite-default`); `--usual` none failed, 507.8 s wall, 4,865.8 s (`suite-usual`). Ten jobs a side, interleaved (`onecpu-b`): infer's "a law that
  needs an invariant" at most 3,348.30 ms (median 2,506.07) against 3,036.21 (2,704.82) on main, "what was found
  reads as the builder call" 2,357.69 against 2,033.28; data's nearPlus 2,912.31 against 3,059.37.
- **One invariant engine, measured.** What the invariant searches share, read from the code: candidates from the
  runs (inferLaws' templates; nonterm's atom pool, bounds of one value and the sums and differences of two), a
  CDCL query with its core (the join's `stepWith` and `queryWith`; kind's k-step goals; nonterm's closure goal),
  a counterexample answered by a form false there (the join's cubes, `down` and prime control cubes; the search below
  the join; nonterm's next atom), and Houdini (the join; its runs' neighbours; relation.ts's over the relation's
  generators for findRank; findCycles' over cyclic nodes; invariant.ts's over Fourier–Motzkin). Moved onto the engine:
  `run-strengthen.ts`, whose Houdini (invariant.ts, 63 lines) is retired for `inferLaws` (s + 50·p ≤ b + 149 in 790
  ms, the job 0.87 s, against the Houdini's 14.94 s on Modal in `runs/pairshang/suite-default`). findRank and
  findLeadsTo already state only their goal to `inferLaws` (the descent as step laws); a helper for the block they
  share measured +194 bytes and was dropped. PDR as a second driver over the cubes paid nothing (above). The rest
  stay: k-induction is a certificate of its own whose step goal's model is k states, not a state to block; nonterm's
  closure is a goal of its own whose counterexample one atom of a 16-line pool excludes; relation.ts's Houdini reads
  exact generators, no samples and no kernel. What they share with the join is a loop of a few lines each, as
  research/refine (branch gen/loop) measured.
- **The library** (`core/` and `kernel/`, tests excluded): 1,941,047 bytes and 26,427 lines against 0.26.0's
  1,943,031 and 26,476 (−1,984 bytes, −49 lines): infer.ts +46 and −31 lines (91,053 → 92,508 bytes) (the comparisons' bounds, the cubes' literals and
  order, the share, the duplicates), invariant.ts −63, machine.ts −1, run-strengthen.ts +5 and −5.

## 0.26.0

Five benchmarks moved or held, the library got smaller, the extractor reads real projects' code, and certificates have
an interchange format with checkers outside the library. None wrong anywhere, and nothing trusted changed since 0.25.0
(`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts` and the Lean files as they were). In our harness (60 s on
Modal, 2 vCPU, the rivals as installed in compare/), each beside main launched with it:
- **TermComp ITS:** 1,139 answered (610 terminating, 529 not) beside 1,127 (`runs/nt3/its-mine6`, `its-main6`).
  KoAT2 proves 601 terminating; LoAT's default engine 532 nonterminating, still 3 ahead.
- **CHC-COMP LIA-Lin:** 996 (588 sat, 408 unsat) beside 961 (`runs/chc3/final-mine`, `final-base`); 994 to 1,002
  in the later batches. Spacer 1,163.
- **SV-COMP termination:** 224 to 225, Ultimate Automizer 224.
- **TIP 2015:** 193 to 197 across this round's batches (`runs/consol/r5`: 194 beside 197), Vampire 193 in 0.25.0's
  batch.

These are measurements in this harness, ours to confirm under each competition's own setup (its time limit, scoring
and current entrants). The release suites (218 jobs, one after the other) on boat: by default 270.4 s wall, 3,732.6 s
of job time, none failed (`runs/release/0.26.0-default`); `--usual` 244.6 s, 3,699.0 s, none failed
(`runs/release/0.26.0-usual`). The skill's XState section now lists what `fromXState` reads (invoked actors, timers,
eventless transitions, entry and exit actions).

The library smaller by sharing what the searches had copied (refactor/shared-engines): `core/` and `kernel/` (tests
excluded) 1,926,132 bytes and 26,229 lines against main 84142cc's 1,940,485 and 26,407 (−14,353 bytes; before the
merges, 1,806,516 against 0.25.0's 1,820,259, −13,743), every result as on main within its run-to-run noise. Nothing
trusted changed (`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts`, `lean-kernel/`).

- **One copy each** (sizes are the library's, each step measured on its own): the random draws' `seeded`
  (machine.ts, for eight copies, −827); `gcd` (solver.ts) and the bigint `bgcd` (q.ts) (−684); a term walker `walk`
  (machine.ts) for data's, transfer's, cycles' and eleven inline walkers (−2,176); the linear forms' `vars`, `plus`,
  `times`, `konst`, `canon` (solver.ts) (−902), `subst` (−425), `linOfE` for accel's `linRaw` and the bmc tidier's
  `linOf` (−385); relation.ts's `tightBounds` for cycles' `tightest` (−338); a congruence closure for lemmaUsesFor and
  caseJoins (data.ts, −507); conjectures' `substX` as `substXs` (−179) and one `matchX` for conjectures and the lemma
  calculation (−744); prove.ts's `eachRead` for five map-read visitors (−1,291) and `stuckAt` (−225); the float
  simplex's ratio test and pivot (solver.ts's `ratioRow`, `pivot`) for refuteFast and floatSolve (−165); machine.ts's
  builders for eight files' own `v`, `k`, `get`, `le`, `eq` (−1,181) and its `pairE`, `argsKey` for three pairings
  (−271); the environment read once (solver.ts's `env`, 22 reads, −1,541); translate.ts on prove.ts's `parseKey` and
  reader.ts's `times` (−700); dsl.ts's `verdictOf` (−451); cyclic.ts's `and`, `implies`, `vars` and nonterm's `isT`,
  `isF` (−486); accel.ts's `turn` for three compositions of a path's turn (−527).
- **Budgets on the counted clock** (−123): exists.ts's choice of witnesses compared a deadline with wall time;
  findLeadsTo's trivial ranks took a share of a clock() deadline by wall time; inferLaws' outer deadline and the search
  proveRule falls back on read wall time. Each reads `clock()` now, which is wall time outside `counted` (the same
  results there). The wall stops left are the deliberate ones (findBoundedRun's, proveKInduction's, cdcl's, the
  forced run's share, inferLaws' stop and timed mode) and the times only reported.
- **Tried and reverted, measured beside main 207179c** (`runs/consol/r2`, `r3`): searched()'s bounded runs and
  k-induction on the counted clock alone ran ledger/openzeppelin/RefundEscrow's k-induction out of memory (the k-step
  goals' building isn't counted work); grow's default budget counted (250 units a millisecond) ran five real-world laws
  (ledger/tigerbeetle/transfers 2 to 6, unknown on main) past the corpus's 150 s, the prover's work being 46 to 788
  units a millisecond across goals.
- **Beside main 84142cc, launched together on Modal** (`runs/consol/r5`): CHC-COMP LIA-Lin 1,002 against 1,000, none
  wrong (the 2 disputed labels on both); TIP 2015 194 against 197, every task both prove with the same counted
  search (`tried`), the 4 lost and 1 gained at 41 to 60 s; TermComp ITS 1,126 against 1,130 (3 gained, 7 lost, at 45
  to 60 s, 4 of them at 60.04 s or later); SV-COMP 225 and 225. The 332 step goals: 664 of 664 the same trees
  (outcome, leaves, splits, conflicts, decisions), all proven, `GDP_CDCL_VERIFY` passing. Frontier round 1: 90 of 92,
  42 of 42 refused, every verdict the same; round 2: 29 of 47 against 30 (term/Piecewise, at the edge of findRank's
  51 s, proven in one of two runs of the same base before), 47 of 47 refused. The real-world corpus: every verdict the
  same (237 proven, 18 refuted, 56 unknown). Lean exports: 516 files the same up to their fresh names' numbering (496
  byte for byte; two runs of one base differ so too). The suites, 217 jobs: none failed by default (253.5 s wall,
  3,110.8 s of job time) or with `--usual` (276.8 s, 3,117.7 s), on boat. 1 vCPU, ten jobs a side interleaved:
  `data`'s nearPlus at most 1,850.85 ms here, 1,842.41 ms on main.
- **The searches' results the same**, beside 0.25.0 (f990361, `runs/consol`): each search's calls and results hashed
  (`[found]`, research tooling outside the library): the suite 213 of 217 jobs the same, the 4 others (exists, nonterm,
  term-c2ari, a frontier item's inferLaws) differing between two runs of 0.25.0 or between its repeats too; round 1 259
  of 260, round 2 162 of 188 (25 differing between two runs of 0.25.0), the real-world corpus 295 of 311, each
  difference in a search bounded by wall time (findNeverEnds, proveKInduction's wall stop, inferLaws' stop).
- Dropped (no smaller, or not the same): natN shared with compare/tip (+7 bytes here), infer's guard (+1), the
  tidier's folding moved into `simpC` (+298, and it changes what simpC returns), the forward differences
  (discover's closedForm fits numbers, accel's differences are symbolic), the float LP for solver.ts's users and CDCL's
  cores for bmc and cycles' Houdini (each changes a search), the prime cubes for cycles' never-forms (a location's is
  one value already), a polyhedra module (each search's rows differ in shape; their shared pieces are above).

The suite's `pairs` job no longer hangs. Its test "two groups of effects" ran about 840 s now and then, in place of 9
to 15 s (`runs/live/suite`, `runs/tiplem/suite-default-1` and `-3`, `runs/reals/suite-base-usual`). Nothing trusted
changed.

- **The cause.** core/dsl.ts's `refuteByRuns` stopped its random runs after 150 ms of wall time. A broken variant's run
  is normally found in the first or second trial, in a median 11.1 ms. Sometimes the first trial alone took longer than
  150 ms, a pause on a loaded container (`runs/pairshang/rtrace`: 159.2 ms, cut before its second trial). The false
  step law then went to the kernel. Its goal, with 944 hypotheses, has a default budget of a second per hypothesis, and
  it used all of it: `unknown` after 944,441 to 990,167 ms. The variant "within one side" left two goals, 386 and 440
  hypotheses, unknown after 389,623 and 440,073 ms; the deeper runs then refuted it, at 829,796 ms in all. These are
  the suite's 836 s (`runs/pairshang/forced`, with the stop set to 0 ms). The unchanged code, 130 runs of the job
  (`runs/pairshang/natural-base`): 7 ran 845 to 870 s, 4 of 50 at 1 vCPU, 2 of 50 at 2 vCPU and 1 of 30 beside three
  busy loops.
- **The fix.** The runs' budget is counted: the trials, the depth and the requests tried, as core/infer.ts counts its
  runs. Nothing reads the clock, so a run within the budget is found on any machine. This holds both for the runs
  before the kernel and for the deeper runs of the search after it. Their cost without the stop, across the default
  suite (`runs/pairshang/nocap-suite`): of 3,721 calls before the kernel, the median took 3.9 ms, the 99th percentile
  55.1 ms and the slowest 389.4 ms. Only 4 calls passed 150 ms (ledger 2, resource groups 2), and none of them found a
  run past it. Of the 39 deeper calls, the slowest took 1,350 ms (invoices), and none passed their old 1,500 ms.
- **With the fix**, 260 runs of the job (`runs/pairshang/natural-fix`: 100 at 1 vCPU, 100 at 2 vCPU, 60 beside three
  busy loops) had no failures. The longest job ran 46.12 s, and the test took 5,195.24 to 13,825.39 ms (median
  7,772.57).
- **Against main f990361, launched together on Modal.** CHC-COMP LIA-Lin at 60 s solved 966 (568 sat, 398 unsat)
  against 962 (565, 397), with none wrong and the same 2 disputed on both (`runs/pairshang/chc-mine`, `chc-base`).
  - Gained 9: s_split_08_000_000, reve 025c, 014, 014b and 015b, DRAGON_2_e2_3183_e2_3580, and three ticket3i tasks.
  - Lost 5: s_split_22_000_000, reve 015, ctigar pldi08 and xy0, and durationThm_2_e3_329_e6_128. These took 39.5 to
    55.7 s on main, with the same stages here, in the join's timed steps. Each was unknown in one of the earlier runs
    `runs/chcsat/m2/chc-main` and `chc`.
  - Both runs answered the tasks they share in a median 17.33 s here and 18.27 s on main.
- **The other corpora, against the same run of main.** The real-world corpus had the same outcome for every law: 237
  proven, 18 refuted, 56 unknown (`realworld-mine`, `realworld-base`). Frontier round 1 had the same verdicts: 90 of
  92, with 42 of 42 broken variants refused (`frontier-mine`, `frontier-base`). Round 2 proved 30 of 47 against 29,
  with 47 of 47 refused on both (`frontier2-mine`, `frontier2-base`). The one difference is term/Piecewise, at the
  edge of findRank's 51 s, which reads no runs of `refuteByRuns`.
- **The 5 s tests on 1 vCPU**, ten jobs each, interleaved with main (`runs/pairshang/onecpu`).
  - `data`'s nearPlus: at most 3,513.00 ms (median 2,500.82) here, against 3,098.49 ms (median 2,504.91) on main.
  - `infer`'s "a law that needs an invariant": at most 3,301.65 ms here, against 3,770.07 ms on main.
  - "what was found reads as the builder call": at most 2,529.88 ms here, against 2,847.39 ms on main.
- **The suites on Modal**, 217 jobs each. By default: 0 failed, 616.2 s wall, 5,408.9 s of job time
  (`runs/pairshang/suite-default`). With `--usual`: 0 failed, 635.8 s wall, 4,964.4 s of job time
  (`runs/pairshang/suite-usual`).

gdp-wired/extract reads the real-world corpus's own code: 5 of its 41 sources extracted (none before), each checked
against the code it was read from, and the corpus's own laws proven on them beside the items' rules by hand. Nothing
trusted changed (`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts` and the Lean files are as in 0.25.0).

- XState (`core/xstate.ts`, `core/extract-xstate.ts`): `fromXState` reads `invoke` (an actor's done and error are
  events from outside, named as XState names them and taken only in the state that invoked it; every transition they
  take must leave the state and the last be unguarded, since an answer comes once a visit), `after` (the timer firing
  an event from outside; one timer at a time, two being refused since they fire in the order of their delays) and
  `always` and context-writing entry and exit actions (read into each transition as XState's macrostep: exit actions
  innermost first, the transition's, entry actions outermost first, then the eventless transitions of the state it
  lands in, again until none is enabled; by cases only where a state needs it; the initial states' entry actions are
  the context's start, an eventless transition enabled at the start refused). `conforms` sends those events only where
  they can come, stops its actors after each run, and takes the event XState is sent, the context compared and a hook
  before each send. `extractXState` reads a machine a function makes (an argument of functions as outside answers, each
  an input read once, or effects; the argument a config takes as its context as the chart's params), `string | null`
  and optional context fields as maybes, strings, `Boolean(x)`, `event.type` as the chart's event, `emit`,
  `sendParent`, v4's `sendUpdate` and `spawnChild` as effects outside, XState v4 (`cond`, `(context, event)`, `services`,
  run on xstate 4.38.3, a dev dependency as `xstate4`), the events a machine's type declares that no state takes, and
  leaves out a context field of a type outside the subset, or one written from a payload nothing kept reads, where no
  guard and no kept write reads it. The check replaces the actors with inert ones and sends their answers itself.
- Classes and functions (`core/extract-read.ts`, `core/extract-shapes.ts`, `core/extract-check.ts`): single
  inheritance (members resolved statically: `this.m()` the nearest the object has, `super.m()` the nearest above the
  class it is written in; constructors in order at `super(...)`; mixins and other modules' classes refused); a Map given
  to a constructor (starting empty, as callers make it; one Map given to two fields refused); results kept as a value, a
  record of values, or a value and whether it is missing; the object of functions a factory returns (its state what
  they close over, the factory's arguments the params; the check reads and sets that state through two functions it
  adds to the object); arrays of numbers, booleans and string unions as lists (length, `[i]`, push, pop, `[i] = x`
  within the array, `[...xs]`, `[...xs, x]`; one write a step, none read after it); Dates as their time (`new Date()`,
  `getTime()`, `setTime()` where the Date is held, the rule refusing past the Date range; a second name for a Date
  refused); null; a string's truthiness. A division whose result may be a fraction stays refused, with why: the code's
  fraction is a binary float that rounds, which a rule over the rationals would not.
- research/realworld's 41 sources (research/extract/results/realworld.jsonl, `runs/extract2/batch3`): 5 extracted,
  upstash's Cache (2,306 requests from the start, 400 drawn states, 8 of 8 conditions reached by the prover's
  witnesses, 6 of 6 arms), gapless.js's track machine, vef-framework-react's uploader, radio-room's stream and
  open-decision's websocket (v4) (3,200, 3,200, 3,200 and 1,612 events beside XState's actor); 36 refused, each where it
  is: 20 not TypeScript or JavaScript, and of the 16 others: a function value 4 (upstash's three algorithms, the step a
  closure that sends Lua to Redis; vendure's shipping checkers), a mixin 2 (medusa's services), not a declaration of the
  code 2 (a test's name; an action type registered by a call), not a step over a state 2 (vendure's order process,
  growthbook's rollout decision), untyped 2 (librechat's mongoose, express-rate-limit's timer handle), a `Math.random`
  generator field (unleash), a setter (rate-limiter-flexible), an `Error | null` read as a condition (electric), an
  untyped services argument (amplify-ui).
- The corpus's laws on the extracted rules (research/extract/corpus-verdicts.ts, results/corpus.jsonl, 60 s of search
  a law on 2 vCPU): the four XState items' 33 laws, 28 stated on the code's rule (5 read a ghost counter the item adds).
  25 get the same verdict on both (23 proven, 1 refuted, 1 unknown); 3 differ: two liveness laws proven on the
  extracted rules and unknown on the items' (vef's "a started upload ends ...", open-decision's "an opening connection
  ends ..."), from the items' models (ghost counters and flags in the state the search ranks over); and
  open-decision's "CLOSE ends an open connection", broken on both, refuted by a run on the item's and broken from a
  lawful state without a run on the extracted one (the prover's random runs, not the rule). The upstash cache is not
  compared (the item's laws are about the token bucket and the cache together).
- The extractor's own examples (research/extract/sources.json): 12 of 22 extracted (10 before: xstate's stopwatch and
  timer, with an invoked ticker and `always`); their laws, with the two added, 35 over 12 examples, the same verdict on
  both sides (results/verdicts.jsonl).
- Tests: core/extract.test.ts 42 (31 before), core/xstate.test.ts 10 (7 before): adversarial cases for each construct:
  an override reached through the base, `super` calls that write, a constructor's `super(...)` in a branch, a field
  declared again, mixins; one Map given to two fields, a record of the object's own returned; Dates under a second name,
  shared by a spread, compared by `===`, the clock read twice; a factory closing over module state, `this` in its object,
  a value beside its functions, a const it writes; one array in two places, a write to the state given, past its end,
  two writes, a read after a write; XState factories closing over mutable state, an outside answer read twice, an
  object field read by a guard, two timers in a state, a timer in a state and one within it, an answer that doesn't
  leave its state or that every guard may refuse, eventless transitions without end, `raise`; each refused with the
  reason or extracted and run beside the code (and XState's actor).
- The real-world corpus's own verdicts (311 jobs, this branch and main at f990361 launched together on boat,
  `runs/extract2/rw-mine`, `rw-base`): 310 the same; gapless's "the fetch-and-decode child is spawned at most once"
  proven in 33.2 s here and unknown at 61.8 s on main, on the identical rule (its compiled machine hashes the same on
  both: fromXState's path for a config without actors, timers or eventless transitions is unchanged).
- The suites (217 jobs) on boat: by default 255.7 s wall, 3,460.8 s of job time, none failed
  (`runs/extract2/suite-default2`; a first run failed its `check` job on an untracked debug file of the working tree the
  image took up, not in the branch: removed and run again); `--usual` 301.6 s wall, 3,398.5 s of job time, none failed
  (`runs/extract2/suite-usual`). The extract tests on 1 vCPU: each at most 798 ms by default, 1,214 ms `--usual`; the
  new xstate tests at most 559 ms.
- Dependencies: `xstate4` (npm:xstate@4.38.3), dev only, for the check of v4 machines.

CHC-COMP LIA-Lin at 60 s on Modal: 996 solved (588 sat, 408 unsat), main (f990361, 0.25.0) launched beside it 961
(564, 397), none wrong in either, the two disputed labels answered as before (`runs/chc3/final-mine`, `final-base`);
Spacer 1,163 and Golem 1,154 in this harness. The tasks Spacer or Golem solve and gdp-wired doesn't: 318 for main in
that batch, 282 here (231 sat, 51 unsat). Nothing trusted changed (`kernel/kernel.ts`, `kernel/cyclic.ts`,
`core/check.ts` and `lean-kernel/` as at 0.25.0). compare/chc/README.md has the gap by group and family, each change's
run and what was left out.

- The container's second CPU shared (compare/chc/kind.ts): k-induction and the bounded runs in turn, in slices of 2 s,
  then 4, 8, 16, ..., each going on where it stopped (core/bmc.ts's `boundedSearch`, `findBoundedRun` made resumable:
  the forced run and the CDCL session kept between slices); solve.ts's own 15 s stage of bounded runs goes (`--bmc-here`
  keeps it), so the invariant search starts about 15 s earlier. Every unsat answer is still a run `checkDerivation`
  confirms. Each step of a bounded run's goal is tidied first (`tidier`). Median time to an answer: unsat 13.58 s to
  2.58 s, sat 28.905 s to 18.075 s.
- The join's control states no state reached as prime cubes (core/infer.ts's `primes`): each drops the values that keep
  it off every reached control state, so a goal reads few of them (ctigar's programs keep their counter in bits: 20 to 31 of them solved, with every change
  here).
- A blocked cube generalized by literal dropping (IC3's down, within 24 queries): on FIREFLY the refutation's core alone
  kept every control value, 20 or so literals, and now three or four are left.
- inferLaws' final proof grows each goal once (kernel/prove.ts's `withTrees`: a root goal's tree kept by its hypotheses
  while each law is proven alone and then the set as a whole; the kernel checks the trees as before; `GDP_TREES=0` off).
- Gained 41 (30 sat, 11 unsat), lost 6 (sat by the invariant search in main, at 24.84 to 52.49 s; compare/chc/README.md
  names them). By stage: sat by the invariant search 431 to 478, by k-induction 133 to 110 (none lost: the search
  answers first), unsat by bounded runs 253 to 315. No answer contradicts Spacer's or Golem's.
- research/dag's 332 step goals: the same trees (outcome, leaves, splits, conflicts, decisions, nodes) by growCdcl and by
  grow here and on main, all 332 proven by each (`runs/chc3/g332`; summed search time, grow 343.7 s here and 330.6 s on
  main, growCdcl 293.6 s and 301.2 s); kernel/cdcl.test.ts with GDP_CDCL_VERIFY=1 passes on both.
- The other benchmarks, each launched with main (60 s, Modal, gdp-wired alone): TermComp's ITS 1,128 (610 terminating,
  518 not), main 1,129 (612, 517), 4 gained and 5 lost, every one at the limit in the run that answered it
  (`runs/chc3/its-mine`, `its-base`); run again three times a side (`its-rm*`, `its-rb*`), each answers on both sides in
  some runs (`destroy_seg_leak.t2_fixed`: found in 4 of 8 runs here, 1 of 4 here with GDP_BMC_TIDY=0, 3 of 4 on main: the
  second recurrent-set search finds it at 9.1 to 12.2 s of its 13.3 s, or not). SV-COMP's termination tasks 224 (169, 55), main 225
  (170, 55), every answer its expected verdict; Singapore-2, mannadiv-both-t and ps3-both-t, run three times a side,
  answer 1, 2 and 1 times here and 1, 2 and 0 on main (`sv-*`). TIP 2015 197 of 492 on both, the same 7 refuted
  (`tip-mine`, `tip-base`); prop_61 gained and list_nat_Select lost, each proven 3 of 3 times here and 2 of 3 on main
  when run again (`tipr-*`); TIP's prover reads none of the code changed here. No answer contradicts another run's.
- The real-world corpus (`runs/chc3/rw`): 311 laws, every verdict as on main (237 proven, 18 refuted, 56 unknown). The
  frontier corpora, every item as on main: round 1 (`f1`) frontier 90 of 92, broken variants 42 of 42 refused; round 2
  (`f2`) frontier 30 of 47, broken 47 of 47 refused (one job killed at 200 s on both sides).
- The suites (217 jobs) on Modal: by default 546.4 s wall, 5,132.1 s of job time, none failed (`runs/chc3/suite-default2`);
  `--usual` 614.4 s and 4,913.8 s, none failed (`suite-usual`). (An earlier default run failed `check` alone: oxlint read
  a copy of main the measurements had left in the tree; without it `check` passes, `suite-default-check`.)
- The 5 s tests on 1 vCPU, ten jobs a side interleaved with main, none failed: `data`'s nearPlus median 2,472.6 ms, at most
  2,692.7 (main 2,486.2, 3,331.7); `infer`'s "a law that needs an invariant" 2,934.2 and 3,278.7 (main 2,569.9 and
  3,718.7) (`runs/chc3/vcpu1`); in a second batch (`vcpu1b`) 2,435 and 3,700 (main 2,574 and 3,027), with the trees kept
  off (GDP_TREES=0) 2,772 and 3,126, with the prime cubes and down off 2,653 and 3,197.

Runs that never end, more of them from the loop's relation (core/accel.ts, core/nonterm.ts): a cycle whose first turn
reads a product (x := x·y, y := (x + 1)²), an inner loop counted out inside a cycle, and closure goals of millions of
nodes, now built and checked in the time. Nothing trusted changed (`kernel/kernel.ts`, `kernel/cyclic.ts`,
`core/check.ts`, `lean-kernel/`): each answer is the same certificate as before, kernel.ts's `checkRecur` and
NonTerm.lean's `never_ends_of`. Measured after merging main at 056fcc3 (refactor/shared-engines, gen/chc3,
gen/extract2), at 60 s on Modal (2 vCPU), launched together with main at that commit in one batch (`runs/nt3/its-mine6`,
`its-main6`, `sv-mine6`, `sv-main6`): TermComp's ITS on the task's statement 1,139 solved (610 terminating, 529
nonterminating) against main's 1,127 (611, 516); per component 1,141 (612, 529) against 1,133 (611, 522). LoAT's default
engine proves 532 nonterminating in this harness (`runs/modal/term/full1`): 3 more than here on either statement, so no
lead. SV-COMP's termination tasks 224 (169, 55) as main, per component 206 as main. No answer contradicts another tool's
or any other run's (42 ITS runs of this track, main's and the tools'), and every SV-COMP answer is its expected verdict.

- **Products** (`piFacts`): a path that reads a product of two values of the state or params is kept in the relation (it
  was left out); a cycle may take one such turn, as its first, the product read at the cycle's start. Where the set's
  bounds decide each factor's sign, the product is ±X·Y over the relation's integers (a pair's other part 0), and its
  facts are McCormick's, (X − l)(Y − m) ≥ 0 from the set's bounds, a square's tangents (X − c)² ≥ 0: what the Houdini
  check of the set needs. Bounds x ≥ c (c up to 32) on each factor are among the atoms Houdini tries, the weakest kept
  that does (complInterv's x ≥ 4 for y := (x + 1)² > 9). In the kernel's search for the closure, a model of the CDCL
  search whose products don't multiply out goes on to the plain search, which multiplies rows (kernel/prove.ts's
  `realModels`, off unless core/nonterm.ts sets it for these closures: no other search changes). Over several turns of a
  walk or a stem, a product is a value of its own each turn (the shared `turn` names it for the turn).
- **Inner loops** (`counter`): a self-loop that counts a value by ±1 to a bound of its rows, from a value the walk has
  set (x := 0, then x := x + 1 while x < 12), is taken that many times (2 to 24) as one choice of the cycle's walk:
  KnapsackDP's cycle of 15 turns, past the 6 choices the walks go to. At most 60 such cycles, after those of up to 6
  turns.
- **Large closure goals**: the prover's open atoms read which names a goal's hypotheses read through its JSON text
  (kernel/prove.ts's `namesOf`), the goal written out: s1's first goal, 163,346,993 nodes written out and 706,964
  distinct, spent 20.8 s in it before the search began (a laptop's profile). It walks the distinct terms now
  (machine.ts's `walkOnce`, beside `walk`; the same names), as the accelerated goals' cap does, at 1.5 million distinct
  terms (it was 5 million written out). A part of the set is told apart by its location and, where the cycle comes back
  to a location, by one atom of its rows that each other part there refutes (the witness's ifs read that, not the part's
  rows); where each part has a location of its own, the set is written by slots, the parts' k-th atoms in one comparison
  of two if-chains over the locations, the same set, so the kernel's reading of the set after the turn follows one
  branch (tqli's check, 10.4 s to 4.5 s on a laptop).
- **Time**: in solve.ts's first search the accelerated cycles have 75% of what the random runs leave (40%), and a set
  that a stem reaches whose closure runs out of time is tried again after the rest, with the time up to 10 s before the
  limit (shared, the smaller goal first; in the second search 85% of what is left). Its cycle keeps it by the closed
  forms and a run gets there, so its loop very likely doesn't halt; the rank search starts later only on such a task. A
  small set that no accelerated run reaches is tried after the rest, its closure and a bounded run for its stem
  (core/bmc.ts), within the search's time (it was left).
- **Beside main at 056fcc3, one batch**: nonterminating on the task's statement gained 13 (KnapsackDP,
  Velroyen08-complInterv, -factorial, s1.t2, s1.t2_fixed, s1-striped.t2 and its `_fixed` twin, the four tqli,
  db2.t2_fixed, db3.t2), each LoAT's NO but the two db (lassos ari.ts's evaluator replays), none lost. Terminating:
  traverse_twice.t2 gained, juLinkedListCreateRemoveFirstOccurrence and s1-saved.t2_fixed lost, answered at 60.12, 60.06
  and 60.09 s on their sides (the answer printed before the limit, the certificate not made). Per component: 9
  nonterminating gained, 2 lost (db3.t2_fixed, a lasso main found at 53.46 s; edn.t2, main's second recurrent-set search
  at 21.69 s: here a run's cycle of 64 turns took that search's time in some runs), ndes.t2 (60.06 s) gained. Seven
  batches through this track, each launched with main: 524, 527, 525, 525, 528 and 528 nonterminating here beside
  f990361's 518, 520, 517, 517, 515 and 517, then 529 beside 056fcc3's 516 (`runs/nt3/its-*`).
- **Where it stops beside LoAT** (12 tasks): RandomHard (a product of the state and a turn's input, which the set makes
  linear only at arg3 = 1), MysteriousProgram (a stem through a doubling loop), fun9 (closed sets no stem reaches;
  LoAT's set is on another cycle), the three hqr (a cycle of 25 turns, past the 6 choices: with 16 choices and 5,000
  cycles it is found in 9 s, and its closure, 633,928 distinct nodes, not in 5 s), pgarch.t2 and its `_fixed` twin and
  slayer-3-new (203 and 426 locations), and by time or chance agafp.t2 and its `_fixed` twin (lassos) and edn.t2.
- **The rank search beside f990361**: its tasks at the limit move between runs. The reverse, traverse and print family
  and elmhes and ns, five runs each side (`runs/nt3/trav2-*`): 88 of 120 terminating here, 90 on main. SV-COMP's tasks
  that moved, five runs each side (`runs/nt3/svre2-*`): the same counts but for BradleyMannaSipma-Fig1 (4 of 5 here, 5
  on main), Singapore-2 (1, 2) and ps3-both-t (0, 2), each answered after 40 s where it is.
- **The other benchmarks**, beside main at 056fcc3 in one batch: CHC-COMP LIA-Lin 588 sat and 406 unsat against 590 and
  405 (two disputed labels each, as before; none wrong; 11 tasks answered on one side only, 5 here and 6 there, each
  after 24 s; `runs/nt3/chc-mine6`, `chc-main6`); TIP 2015 194 proven against 193 (`tip-mine6`, `tip-main6`). The
  corpora: round 1 90 / 92, broken 42 / 42, as main; round 2 30 / 47 against 29, broken 47 / 47 (the difference
  term/Piecewise, at findRank's limit: 3 of 8 runs prove it on each side beside f990361, `runs/nt3/pw-*`), its
  nontermination items 5 / 5, broken 5 / 5, as main; the real-world corpus 237 proven, 18 refuted, 56 unknown, every law
  as main's (`c1-`, `c2-`, `rw-mine6`, `-main6`). The 5 s tests on 1 vCPU, ten jobs each side interleaved, none failed
  (`runs/nt3/onecpu6`): data's nearPlus at most 3,462.90 ms here (median 2,778.51 ms), 2,869.95 ms on main (2,589.99
  ms); nearSucc 2,651.50 ms (2,213.97 ms) and 2,189.73 ms (2,076.57 ms); in a batch beside f990361 (`onecpu2`) nearPlus
  at most 3,304.20 ms here and 3,666.16 ms on main. The suites on Modal: by default 217 jobs, none failed, 668.8 s wall,
  5,814.5 s of job time (`runs/nt3/suite-default6`); `--usual` 217, none failed, 639.9 s and 5,703.0 s (`suite-usual6`).
- **Lean**: the new accelerated sets of a run before the merge (`runs/nt3/its-mine2`), each a theorem `NeverEnds
  <task>_loop` by `never_ends_of` that Lean 4.34.0 checks on `propext`, `Classical.choice`, `Quot.sound`: 7 of 9
  (complInterv, factorial, Test4 and the four tqli, 1.155 s to 21 m 32.322 s a job); s1.t2's and s1-striped.t2_fixed's
  stopped at 55 minutes, not checked (`runs/nt3/lean-sample`). Of a later run's 11 (`its-mine5`, KnapsackDP's among
  them), 7 jobs exited 0 within 1,518.59 s (KnapsackDP's in 18.52 s) and 4 (the three s1 and one tqli) were still
  running at two hours and stopped; their logs were lost with the batch (`lean-sample2.log`).
- Tests: core/nonterm.test.ts's accelerated cycles with a product (y := (x + 1)²) and with an inner loop, each found and
  checked, each twin proven to halt and not found.
- Cost: Modal $53.22419204 for 111 of this track's 123 apps on 2026-10-24 UTC (`modal billing report --for today`,
  before the day closes; main's runs beside included); no boat.

The interchange format, version 1.0 (spec/interchange): a rule, its laws and a certificate as JSON that another language
can read, write and check, with gdp-wired as its reference implementation. Nothing trusted changed: `kernel/kernel.ts`,
`kernel/cyclic.ts`, `core/check.ts` and the Lean files are as they were, and the checker is built from them (git blobs
348282b, 3e9a73c, 0e5a454, printed by every build, the same in every run below).

- **The format** (`interchange/schema.json`, JSON Schema 2020-12: 204 lines, 41 definitions, 176 field descriptions;
  the meaning in `docs/interchange.md`): 13 kinds, each the certificate of one trusted entry point: kernel trees
  (`goals`: splits, inputs, combinations, cuts, squares and products), `laws`, `stepLaws` (k steps, histories, sets,
  functions and facts), `kInduction`, `progress`, `liveness`, `loop` (ranks in order), `recur` (nontermination),
  `fold`, `cyclic`, `qgoals` and `qmachine` (the rational trees), and `termination` (a ring's measures with each
  call's cyclic proof). Records are lists of pairs in order, a linear form lists its constant first and its atoms in
  the kernel's order (a derivation names rows by place), and a term column is named by its term (the kernel numbers
  them per process).
- **Export and import** (`interchange/format.ts`, untrusted): `toInterchange(certificate)` and `fromInterchange(json)`,
  refusing with where whatever is outside the format.
- **The standalone checker** (`interchange/check.ts`, `cli.ts`, `wasm.ts`; `bun interchange/build.ts --wasm`):
  `gdp-wired-check`, a 119.7 KB bundle (node or bun) and a 1,440.1 KB WebAssembly module (Javy 9.1.0, WASI preview 1),
  accepted or refused per law. It reads a document, writes it back and refuses it unless the two agree, then calls the
  kernel's own entry points.
- **A second checker** in Python (`interchange/py/check.py`, 458 lines, written from the spec): the tree and
  derivation check of a `goals` document, any certificate's goals written by `gdp-wired-check --goals`.
- **docs/ARCHITECTURE.md**: the trust boundaries and why each sits where it does, how to add a front end and a
  certificate kind, how the benchmarks and corpora are measured.

Measured on this branch after merging main at e13a123 (`runs/interchange/final2-*`): every suite job
(`interchange/suite-jobs.ts`: modal/suite.json's 218 but Lean's and the type check, and the two examples no job runs:
157 jobs) with every certificate handed to a trusted entry point captured (`interchange/capture.ts`), each written,
read back in the same process, then checked in other processes by the checker, the bundled CLI, the WebAssembly module
under Wasmtime 49.0.1 and, on its goals, the Python checker, against the kernel's answer where it was made, with three
tampered twins of each accepted document; every document and twin validated against the schema (jsonschema 4.23.0).

- By default (`final2-capture-default-all`: `final2-capture-default`, its `ix-data` job, which ran past its 6,570 s
  limit on Modal, from `final2-capture-default-data`, 2,506.7 s on boat): 52,202 documents (goals 37,895, cyclic 5,990,
  qgoals 2,967, kInduction 2,043, recur 1,998, laws 968, stepLaws 133, termination 115, loop 29, fold 29, qmachine 19,
  progress 10, liveness 6), the kernel accepting 42,156 and refusing 10,046 (the fuzzers' and tamper tests' own, the
  searches' failed attempts, and the 10 progress documents: by default the laws they assume are proven by a cyclic
  certificate, captured apart, so they carry no lawsProof and the checker refuses them, as the capture records). Every
  one read back to the same objects; the checker, the CLI and the WebAssembly module agree with the kernel on all
  52,202, the Python checker on all 107,892 of their goals. 83,209 twins: the checker refuses 82,982, the CLI and the
  module agree on all, the Python checker on all 245,539 of their goals; the 227 accepted are twins the tamper left a
  proof (a raised multiplier or a moved split constant that still refutes), accepted by all four. Schema: 264,880
  valid, none invalid. Outside the format: 10 tampered trees of kernel/tamper.test.ts with a multiplier that isn't an
  integer, which the kernel refuses too. compare/term's c2ari job hands the kernel nothing from its own bun processes
  (python starts them), nor does any child a script spawns: the capture covers each job's own bun processes.
- With `--usual` (`final2-capture-usual`): 43,896 documents (goals 18,272, laws 15,950, qgoals 2,967, kInduction
  2,043, recur 1,998, stepLaws 1,523, cyclic 872, termination 115, loop 64, fold 36, liveness 26, qmachine 19,
  progress 11), the kernel accepting 33,729 and refusing 10,167; every one read back to the same objects, and all four
  agree with the kernel on every document and goal (66,398 goals). 63,656 twins: 63,600 refused, the 56 accepted by
  all four; the Python checker agrees on all 129,305 of their goals. Schema: 207,032 valid, none invalid; outside the
  format: 24, as above.
- Lean (`final2-lean`, `interchange/lean-jobs.ts`): the conformance cases written as documents, read back in another
  process, checked, and written as Lean through lean-kernel's emitters, each claim computed to the checker's answer:
  NonTerm.lean's checkRecur on 127 (28 found, 99 tampered or forged); KInd.lean's checkKInd on 112 of 24 machines'
  certificates and twins (33 accepted, 79 refused; 24 refused twins with no KInd literal not sent); Rationals.lean's
  Q.checkGoal on 1,584 (300 proven, 1,284 tampered); Kernel.lean's checkGoal on 547 goals of 40 example rules' usual
  certificates and their 117 twins (431 accepted, 116 refused; one twin's goal not writable: a cut by a divisor its
  row no longer has, which Lean's Int has no quotient for); Cyclic.lean's checkCyclic on 40 example rules' cyclic
  certificates and 116 of their 117 twins with a node changed; Data.lean's `termination_by` under the 10 rings'
  measures the documents hold. Every file elaborates: Lean computes the checker's answer on each claim. The 117th
  cyclic twin (a use made of another node) the checker refuses and Lean accepts: Lean finds a leaf's rows by value
  (the emitter claims them), kernel.ts by their place, and that twin's rows are all there, moved; `IxCyclicByValue.lean`
  computes it to true, and kernel.ts accepts it too once each input is pointed at its row (`interchange/lean.ts`'s
  `byValue`). It showed first in `runs/interchange/lean-1` as a failed `= false`.
- Suites, after the merge: by default 218 jobs, none failed (`final2-suite-default`, Modal: 652.0 s wall, 5,511.0 s of
  job time); `--usual` 218, none failed (`final2-suite-usual`, Modal: 536.8 s wall, 4,890.4 s).
- The figures before the merges (main at f990361, then 056fcc3: `runs/interchange/capture-*`, `final-*`) agree with
  these: no disagreement in any run.

## 0.25.0

Ahead of or level with the leading tools on four of the six measures we run, in our harness (60 s on Modal, 2 vCPU, the
rivals as installed in compare/), and nothing trusted changed since 0.24.0 (`kernel/kernel.ts`, `kernel/cyclic.ts`,
`core/check.ts` and the Lean files as they were). None wrong anywhere. TIP 2015 197 of 492, in one batch with Vampire
193, cvc5 with conjecture generation 187 and cvc5 168 (`runs/tiplem/final-tools`), 181 at 0.23.0. TermComp's ITS 1,131
answered (612 terminating, 519 not) beside main's 1,073 (`runs/accel2/its-mine`, `its-base`); KoAT2 proves 601
terminating and LoAT's default engine 532 nonterminating (compare/term/README.md). SV-COMP's termination tasks 225,
Ultimate Automizer 224. CHC-COMP LIA-Lin 966 (569 sat, 397 unsat) beside 935 (`runs/chcsat/`), Spacer 1,163. These
leads are ours to confirm under each competition's own setup (its time limit, scoring and current entrants); until then
they are measurements in this harness. The release suites (217 jobs, one after the other) on Modal: by default 649.4 s
wall, 5,354.0 s of job time, none failed (`runs/release/0.25.0-default`); `--usual` 669.4 s, 5,005.6 s, none failed
(`runs/release/0.25.0-usual`).

The lemma search on TIP 2015 (core/data.ts): lemmas calculated from the induction steps the definitions leave, lemma
uses ranked within each case, induction schemes merged, and a case's arithmetic read into its classes. Measured after
merging main at 54bbec9 (0.24.0), TIP 2015 at 60 s on Modal, every tool in one batch through compare/tip/modal_tip.py
(`runs/tiplem/final-tools`: this branch, cvc5, cvc5 with conjecture generation and Vampire; `runs/tiplem/final-main`:
main at 54bbec9, launched with it): this branch 197 of 492 proven, Vampire 193, cvc5 with conjecture generation 187,
main 183, cvc5 168. Wrong: none here or on main (each refutation's counterexample confirmed by TIP's evaluator; the 7
theorems refuted on both are the `tip2015` ones TIP writes false); Vampire none; cvc5 proves 1 of the 68 `false/`
properties and with conjecture generation 6, as in `runs/modal/tip/full2`. `false/`: 23 refuted here and on main,
none by Vampire or cvc5. The lead over Vampire is this harness's (60 s, our installs) and unconfirmed until TIP's own
setup runs it. Nothing trusted changed (`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts`, `lean-kernel/` are as
in 0.24.0).

- Lemma calculation (Zeno's, HipSpec's; `calculated`, `reduceX`): for each variable a scheme inducts on and each of its
  constructors, the law at that constructor of fresh fields, its definitions unfolded where they are decided, the
  hypothesis (the law at each recursive field, at any values of the law's other variables: an accumulator's) used as a
  rewrite either way, and what is left unequal, its subterms common to both sides each a fresh variable, is a
  conjecture; the base cases too. Those random values don't refute are tried first, a generalised one's own step
  calculated again (bind over an append from `list_assoc`, then ++ associative from it). They have their own count in a
  pass (most of it, 3 s each), and the law is tried again after the last of them.
- Lemma uses ranked per case: past the node's caps, its candidate uses are kept for its cases (96), and a case takes up
  to two more whose sides are both its own terms, up to the equalities its models take (`caseJoins`).
  `research/edges/lemma-case.ts` (the lang/edges finding: the use `list_assoc`'s case needs was ranked out by models of
  other cases) is proven both ways now.
- A conjecture of a pass that failed is tried once more after a lemma is proven (HipSpec's loop).
- Merged schemes (Boyer and Moore's): two recursion schemes' uses at once where they agree, `drop n (take m xs)` by n,
  m and xs together; a scheme whose argument is a term (take n (xs ++ ys)) is one half of such a pair. At one unfolding,
  in the law's first attempts only, within a third of an attempt's time.
- A case's classes: its conditions' equalities, linear forms through its constants and its models (n + m ∸ 1 and
  m ∸ 1 one form where n = 0 and m ≥ 1), and natural arguments that are truncated differences equal in every model of
  the case one class in the congruence phase (n ∸ len xs and (n ∸ 1) ∸ len (tail xs), xs a cons); a split on an unknown
  function's guard (filter by p); a lemma's constructor matched by its fields, for a lemma no read matches as it stands.
- Faster, the same verdicts: conjectures matched against the goals at once (6 s of uncounted work to under 1 s on
  `bin_plus_comm`); kernel/prove.ts's `openCells` reads each cell's key once (`prod/lemma_10`: 70 s of wall time to 23 s,
  the same answer).
- Gained 15 against main in that batch: by calculated lemmas `prod/lemma_23`, `isaplanner/prop_20`, `prod/prop_48`,
  `tip2015/nat_alt_mul_same`, `nat_acc_alt_mul_same`, `list_assoc` (46.23 s); by merged schemes `isaplanner/prop_41`,
  `prop_55`, `prop_57`, `prop_81`; by a case's arithmetic `prop_50`, `prop_56`, `prod/lemma_05`; by the split on an
  unknown guard `isaplanner/prop_14`; and `prod/lemma_12` (56.40 s), out of time on main in this run. Lost 1:
  `isaplanner/prop_61` (55.34 s on main, at the limit on both sides in earlier runs). The median time of the 182 both
  prove: 0.74 s here, 0.745 s on main. Before the merge, beside main at 6b2e2df, five runs gave 195, 194, 194, 194 and
  193 against 181, 183, 183, 182 and 181 (`runs/tiplem/tip-3` to `tip-8`).
- `prod/lemma_12`, lost before the merge: a lemma's constructor matched by its fields gave its attempts with a lemma 186
  instances in place of 146, each then out of its counted time; matched so now only for a lemma that no read matches
  as it stands (proven again, 18.3 s locally).
- What is left (the 167 translated and unproven at 6b2e2df's measurement, compare/tip/README.md): conditional laws 54,
  sorting 29, binary and signed integers 23, take, drop, zip and rotate at lengths 21 (13 proven by another tool; 27
  and 19 on main), accumulators and reversals 17, arithmetic on naturals 16, predicates over a list 7.
- Against main at 54bbec9, launched together: the datatype corpus (round 1, `runs/tiplem/g1-mine`, `g1-main`) 90 of 92,
  42 of 42 broken variants refused, every item as on main; round 2 (`g2-mine`, `g2-main`) 30 of 47, 47 of 47 refused,
  every item as on main (its TIP items 2 of 15 on both); the real-world corpus (`gr-mine`, `gr-main`): 237 of 311
  proven, every verdict as on main. `data.test.ts`'s through-the-built-ins test reads n ≤ m + n: n ≤ n + m is now
  proven by plus's own recursion.
- The 5 s tests on 1 vCPU, ten jobs each side interleaved with main at 54bbec9 (`runs/tiplem/final1cpu-mine`): `data`'s
  nearPlus at most 3,535.08 ms here (median 2,609.63 ms), 3,355.13 ms on main (2,748.105 ms). Before the merge, three
  batches against 6b2e2df: at most 3,320.17, 3,143.19 and 3,780.45 ms here, 3,873.73, 3,077.19 and 3,406.48 ms there
  (`runs/tiplem/t2-mine`, `onecpu-mine`, `onecpu2-mine`).
- The suites (217 jobs) on Modal after the merge: by default 572.0 s wall, 5,279.7 s of job time, none failed
  (`runs/tiplem/suite-default-4`); `--usual` 708.3 s and 4,816.4 s, none failed (`suite-usual-3`). The default run
  before (`suite-default-3`) failed one job, `pairs`: its test "two groups of effects" ran 837 s, past its job's limit
  (as once before the merge, `suite-default-1`, where the other jobs ran slow too); alone on 1 vCPU it passed 10 of 10
  here (at most 9,713.3 ms) and 10 of 10 on main (at most 8,438.69 ms), interleaved (`runs/tiplem/final1cpu-mine`). It
  reads no core/data.ts; kernel/prove.ts's `openCells` change gives the same cells in the same order.

Ranks split by several conditions, and a rank search fast enough for programs of a hundred locations. Measured after
merging main at 98bfabe (gen/sv-front's C front end among it), at 60 s on Modal, launched together with main at that
commit, both under this branch's harness (below): TermComp's integer transition systems on the task's statement 1,073
solved (613 terminating, 460 nonterminating), main 1,022 (567, 455); per component 1,072 (611, 461), main 1,044 (580,
464); KoAT2 601 terminating in this harness (`runs/modal/term/full1`, `koat-fix1`). SV-COMP's termination tasks 224
(169, 55), main 211 (156, 55); per component 206 (151, 55), main 199 (144, 55); Ultimate Automizer 224. Both leads (ITS
terminating over KoAT2, SV-COMP level with Ultimate Automizer) are this harness's and unconfirmed until the
competitions' own setup runs them. None wrong: every SV-COMP answer is its expected verdict (no errors), and no answer
contradicts another tool's, a lasso or any of this track's or main's runs (`runs/ranks2/m-its-mine`, `m-its-base`,
`m-sv-mine`, `m-sv-base`; `m-its-compare.txt`, `m-sv-compare.txt`). Nothing trusted changed (`kernel/`, `core/check.ts`,
`lean-kernel/`); every rank is still proven by the kernel on the task's own loop.

- Regions (core/cycles.ts's `relationRank`): a component with no rank is split by one atom, then, with invariants to
  find, two at once; the atoms are the signs of what a path adds to a value (y := y + x: x ≥ 1) and the atoms its
  paths read (q < p for min(p, q)). Each sign vector at a location is a node; the kernel's term reads the atoms.
- Disjunctive invariants: with invariants (`rankWithInvariants`), each region's own, by Houdini over every path of the
  relation split the same way (every location, so a disjunction made before the loop, x := 1 or x := −1, is kept), each
  a law pc = ℓ ∧ the signs → atom that the kernel proves inductive with the rest. Toulouse-BranchesToLoop-2 (x ≠ 0) is
  proven now, in the frontier corpus and within solve.ts's time on SV-COMP; Piecewise (min(p, q)) at the edge of
  findRank's 51 s in the corpus (proven in the run before the merge, not in the one after); their broken variants
  refused.
- A location no run reaches (KoAT2's `1 ≤ 0`): `1 ≤ 0` is a candidate at every location, kept where every path into it
  leaves from states the rest rule out; and x − y = c where a path sets x := y + c and keeps y. ex17's loop with no
  guard sits past an i < 0 that never holds: unreachable, the rest has a rank.
- The relation (core/relation.ts): a condition the path's pins decide alone (pc = 3 and t = 1) is read at them, so a
  chain of a rule per case is walked, not split per case: reverse, traverse and print (80 to 100 locations), refused
  before at the paths' budget, have their relation. `generators` refuses a row over a name it isn't given (a region's
  atom over a name the path didn't read had its coefficient dropped, a wrong split the kernel then refused).
- The rank's LP: in floating point first (`floatSolve`, Dantzig's rule, Bland's after degenerate pivots; the rows scaled
  to their largest entry, then as they are), read back as fractions, scaled to integers and kept only where every row
  holds exactly (BigInt); tiny values solved again as 0 where the tolerance hid a row of a vertex at 2^31. Infeasible
  where both passes say so; else an exact refutation (solver.ts's `refuteFast`, rational) or the exact simplex, now
  fraction-free (each row integers over one denominator; no divisor per entry). On the relation's rows the integer
  boxes are skipped (the least Σ|u| is as small a rank). A shared template reads the component's live names only; a
  component may have 16 blocks (8). Two spreads of thousands of values as arguments (a stack overflow, ex22) are loops.
- `findRank`: the relation's search has a third of the time left (a half), so the search with invariants after it has
  more.
- Harness (compare/term/modal_term.py, modal_sv.py): a row's answer is the last one printed, so a proof whose answer was
  printed before its certificate keeps it when the run stops making the certificate (cert `not made`), as solve.ts
  intends. The base runs used the same harness.
- Gained on the statement, ITS (after the merge): 46 terminating (the reverse/traverse/print family 9, juLinkedList*
  7, elmhes 2, ex17 2, fun2 2, fun2b, fun3, java_Diff, java_DivWithoutMinus, java_AProVEMathRecursive, polyrank3 to 5,
  p-43 2, slayer-n3 2, sas07, qrdcmp, RSA, BinarySearch, PartitionList, RetValRec, SortCount, florian_new_ex,
  florian_sumit, ex27, eric, s1-saved) and 10 nonterminating (by the unchanged lasso and recurrent-set stages, whose
  time moved). Lost: no terminating task; 5 nonterminating (DivTernary2, FlattenTreeListRec, agafp_fixed, db2_fixed,
  n-40_fixed), each found by main in its second recurrent-set or lasso search (22 to 58 s), searches bounded by time
  and random (their runs differ from run to run). Per component: 31 terminating and 2 nonterminating gained, 5
  nonterminating lost (each a recurrent set or lasso main found, 4 to 35 s). SV-COMP: 14 terminating gained
  (Toulouse-BranchesToLoop-2, 4NestedWith3Variables-1, Gothenburg_v2-1, MenloPark, DivMinus2, IntPath, gcd01-2,
  cohencu5, mannadiv, ps2, sqrt1, BradleyMannaSipma-CAV2005-Fig1, CookSeeZuleger-TACAS2013-Fig7b, -Fig8b); Singapore-2
  lost (42.2 s on main); per component 7 gained, none lost.
- Before the merge (against main at 6b2e2df, the same night, `runs/ranks2/h-*`): ITS 1,078 (615, 463), main 1,033
  (572, 461); per component 1,073 (612, 461), main 1,045 (583, 462); SV-COMP 189 (142, 47), main 182 (135, 47).
- An answer printed before its certificate is a kernel-checked one: compare/term/solve.ts prints `answer: terminates,
  cert: not made` only once `prove` has returned ok, which it does only when every goal of loopObligations on the loop
  as translated has a tree that kernel.ts's `check` accepts (`missing` empty); per component, only once every
  component's has. The certificate is made after, and the answer printed with it is the same answer. So the
  harness's last answer printed is never an unchecked one.
- Still missed where KoAT2 proves termination: 25 (17 by neither translation): deep nests that need more blocks than the
  time allows (jacobi, ludcmp, spctrm, sudoku), and ranks the kernel takes longer than the limit to prove (magic, ns,
  ud, opt-tree: 25 to 35 s for one goal on Modal); `bun compare/term/failures.ts` gives `runs/ranks2/h-failures.txt`.
- The frontier corpora (after the merge, beside main at 98bfabe): the second's rank, nonlinear-rank, sampling and
  nested-recursion items 12 of 15, main 11 (Toulouse-BranchesToLoop-2 gained; Piecewise proven before the merge at
  findRank's 51 s, at its edge, not in this run), every broken variant refused; round 1's cycle items 21 of 21, broken 21
  of 21, as main (`runs/ranks2/m-corp-mine-c2.md`, `-c1.md`, `m-corp-base-c2.md`, `-c1.md`). The real-world corpus,
  before the merge: the same verdicts as main, law for law (218 proven, 17 refuted, 75 unknown, 1 error;
  `h-corp-mine-rw.json`, `g-corp-base-rw.json`).
- Tests: core/cycles.test.ts's relation test adds Toulouse-BranchesToLoop-2 and its broken variant. The probes
  (`term-adversarial`, `term-c2ari`: 66 programs, none answered against the program) pass. The suites on Modal after
  the merge: by default 217 jobs, 0 failed, 540.3 s wall, 5,577.2 s of job time (`runs/ranks2/m-suite-default`);
  `--usual` 217 jobs, 0 failed, 607.6 s, 5,200.2 s (`m-suite-usual`).
- 1 vCPU after the merge, ten of each interleaved with main at 98bfabe in one batch (`runs/ranks2/m-onecpu`): data's
  nearPlus min, median and max 1,788, 2,820 and 3,341 ms against main's 1,892, 2,346 and 3,343; nearSucc 1,441, 2,074
  and 2,505 against 1,447, 1,790 and 2,414; add3acc 1,123, 1,664 and 2,096 against 1,187, 1,459 and 2,062; infer's
  four-value join 4,012, 5,885 and 7,782 against 3,944, 5,351 and 7,771; none failed.
- The search reads the shared clock (gen/termlemmas' `clock()`), its float pivots counted as work (an eighth of an
  exact pivot's), so a counted search's verdict doesn't depend on the machine's speed.
- Cost: Modal $25.08366 for this track's 58 apps before the merge and $5.95577 for its 10 after (main's base runs
  included), on 2026-10-23 UTC (`modal billing report --for today`, before the day closes); no boat.

Runs that never end, from the loop's relation: a cycle of its paths, its n-fold run read in closed form, the set it
keeps closed, and a stem into it from runs whose loops are taken n times at once (core/accel.ts). Nothing trusted
changed (`kernel/`, `core/check.ts`, `lean-kernel/`): each answer is the same certificate as before, kernel.ts's
`checkRecur` and NonTerm.lean's `never_ends_of`. Measured after merging main at 54bbec9 (gen/ranks2 among it), at 60
s on Modal, launched together with main at that commit: TermComp's ITS on the task's statement 1,131 solved (612
terminating, 519 nonterminating), main 1,073 (612, 461); per component 1,133 (612, 521), main 1,074 (611, 463).
The nonterminating leader in the same harness is LoAT's default engine, 532 (LoAT abmc 492; `runs/modal/term/full1`):
13 behind it on the task's statement, 11 per component; no lead, past LoAT abmc only, and any comparison unconfirmed
under the competition's own setup. SV-COMP's termination tasks: 225 (170, 55) as main, per component 206 (151, 55)
against 207 (152, 55). No answer contradicts another tool's, the other run's or an expected verdict
(`runs/accel2/its-mine`, `its-base`, `sv-mine`, `sv-base`).

- **Cycles** of the relation (core/relation.ts's paths, each from a location to a location): closed walks by their
  least rotation, by how many choices they make among a location's paths (at most 6; straight-line code costs none),
  each turn's inputs left open and a walk cut where its rows are refuted (core/solver.ts); a self-loop also twice over
  (x := −x); then the cycles the random runs take. A turn's inputs as terms of the state before it (a row's equation, a
  bound) or constants from a model of two rounds.
- **Closed forms:** the cycle is one affine loop (guard G, update U). An atom g ≤ 0 of G holds after every n turns where
  its forward differences along the run, Δ^{k+1}g = Δ^k g∘U − Δ^k g, are ≤ 0 at the start (g(Uⁿx) = Σ C(n, k)·Δ^k g:
  translations, triangular and geometric updates); the set is G with the differences to degree 3, Houdini dropping a
  difference U doesn't keep. On the loop: per turn of the cycle, at its location, the states from which the rest of
  it is allowed and ends in the set (the weakest precondition), the witness by location (the commonest value with no
  condition).
- **Stems:** a state a random run reached; else a run found over the relation from the start, a path at a time or a
  self-loop that is a translation taken n times at once (rows at its first and last turn), pruned where its rows are
  refuted, then run on the loop itself (a stem of 5,000 turns in the tests); else, once the set is closed, a bounded
  run (core/bmc.ts). A set no such run reaches is not tried, and a set with a stem may take most of the time left.
- **The relation:** gen/ranks2's decided-branch shortcut (an `if` a path's pins decide read at them, always on) is
  the one in core/relation.ts; this branch's own (`relationOf(..., {fast: true})`, the same rule) is gone, and both
  searches read the one relation. On all 1,239 ITS tasks it is 6b2e2df's relation wherever both build (1,168 at the
  usual cap, 55 at 100,000), 12 built only now, 4 by neither (`runs/accel2/relsame2`, as `runs/accel/relsame1` for
  the flag).
- **Beside main at 54bbec9:** nonterminating gained 59 on each statement, lost 1 (`gdp`: db3.t2_fixed, `gdp-scc`:
  db2.t2_fixed, each a lasso main's lasso stage found at 46 to 50 s; the first run below found db3.t2_fixed here and
  not at 6b2e2df); 57 and 59 of the gains are LoAT's NO, the other two lassos replayed by ari.ts's evaluator; the new
  accelerated answers at a median 3.6 s (p90 42.5 s). Terminating unchanged on the task's statement (612 both), one
  more per component. SV-COMP: `gdp` GCD3 lost and another gained, both at the limit; `gdp-scc` lost
  cohencu5-both-t, a rank search bounded by time: run again, main proved it in 6 of 10 runs, this branch in 1 of 10
  and this branch with the accelerated stage off in 4 of 9 (`runs/accel2/svre-*`), so the stage's first seconds may
  cost the rank search there (not found why). ITS misses beside LoAT: 21, the 18 below with tqli.t2, its `fixed.t2`
  twin, Test4 and agafp, and tqli_fixed answered: closures and lassos that land near the limit move between runs.
  Round 2's nontermination items: 5 / 5, broken 5 / 5, as main (`nt-mine`, `nt-base`). The suites: by default 217
  jobs, none failed, 650.9 s wall, 5,687.8 s of job time, main 622.2 s and 5,371.3 s; `--usual` 595.5 s and 5,062.4
  s, main 587.1 s and 4,968.5 s (`suite-*`), `lean-nonterm` passing in all four, `nonterm` 55.2 s against 39.5 s
  (the new test), the rest spread over unrelated jobs both ways. Lean: 40 of the 57 new accelerated sets, drawn at
  random, each a theorem `NeverEnds <task>_loop` that Lean 4.34.0 checks on `propext`, `Classical.choice`,
  `Quot.sound`, 40 of 40, at most 118 s a job (`runs/accel2/lean-sample`).
- **Before the merge, beside main at 6b2e2df** (`runs/accel/its-mine1`, `its-base1`, `sv-mine1`, `sv-base1`): ITS
  1,094 (571, 523) against 1,032 (574, 458), per component 1,107 (582, 525) against 1,043 (580, 463); SV-COMP the
  same answers, 182 (135, 47) and 172 (125, 47).
- Where it landed at 6b2e2df: of its 458 nonterminating answers, 129 are accelerated sets now (they come before the
  policies), the rest as they were. Nonterminating gained 65 (`gdp`) and 62 (`gdp-scc`), lost none; 64 and 62 are
  LoAT's NO too, the other a lasso replayed by ari.ts's evaluator. Terminating `gdp` 2 gained and 5 lost at the rank
  search's limit; run again, this branch proves all five and 6b2e2df three (`runs/accel/lost5-*`). The 77 ITS tasks
  LoAT answers NO and 0.23.0's run didn't: 60 answered; the 18 left (17 of the 77, and one a lasso found by chance
  at 0.23.0) each read against LoAT's proof in compare/term/README.md.
- Tests: core/nonterm.test.ts's three tasks no other stage finds (a sign that alternates while |x| grows, a free value
  chosen 14, a stem of 5,000 turns), each with its terminating twin proven to halt and not found. The second corpus's
  nontermination items: 5 / 5, every broken variant refused, as at 6b2e2df, each by an accelerated set now (sets of
  206 to 444 bytes against 518 to 1,510, stems of 0 to 101 turns against 1 to 3,008); both corpora's verdicts as at
  6b2e2df (round 1: 90 / 92, broken 42 / 42; round 2: 27 / 47, broken 47 / 47; `runs/accel/c1-*`, `c2-*`).
- The suites on Modal: by default 213 jobs, none failed, 692.5 s wall, 5,106.6 s of job time (`runs/accel/suite-default`);
  `--usual` 213, none failed, 505.5 s, 4,567.4 s (`suite-usual`). 6b2e2df beside them: 6 failed in its checkout (no
  vendor/handwired, which hw-check and check read), and on the 207 jobs both passed 4,793.1 s and 4,522.8 s against
  4,919.3 s and 4,361.8 s here; `nonterm` 53.6 s against 39.6 s (the new test).
- compare/term/modal_term.py's `-proof` tools keep a long proof's head and its last 100 kB (where its steps are), not
  its first 30 kB.
- Lean: every recurrent set of this branch's ITS run (`gdp`), 200 (192 accelerated), is a theorem `NeverEnds
  <task>_loop` Lean 4.34.0 checks by `never_ends_of`, on `propext`, `Classical.choice`, `Quot.sound`
  (compare/term/recur-lean.ts: 193 in 31 of 32 shards, `runs/accel/its-lean1`; the 32nd's 7 killed at 50 minutes and
  checked one a job, `its-lean1-shard5`, Test4.jar-obl-10's in 62 minutes, the rest within 2.5).
- Cost: Modal, about 153,600 s of task time for the benchmark, corpus and suite runs here and their bases, 5,968 s and
  4,106 s for the Lean checks; the day's dollars not yet in Modal's billing report.

Disjunctive invariants in the join (`core/infer.ts`): a counterexample no candidate rules out is blocked as IC3 blocks
a cube, by relative induction, its literals cut down to the core of the CDCL search's refutation (`kernel/cdcl.ts`'s
new `core` option); the join's goals asked first of that search for a model alone; the control states no run reached
one law until it is first broken. Nothing trusted changed (`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts` and
`lean-kernel/` are as in 0.24.0): every answer is still the kernel's proof of the whole set. CHC-COMP LIA-Lin at 60 s
on Modal, gdp alone, merged with main at 54bbec9 (0.24.0's bounded search on one CDCL session at 15 s, k-induction on
the second vCPU) and launched together with it: 966 solved (569 sat, 397 unsat) against 935 (537, 398), none wrong, 2
disputed in each (s_split_22 and s_split_50, as main lists them) (`runs/chcsat/m2/chc`, `chc-main`). 37 sat more, 5
fewer, 1 unsat fewer; of the sat, 436 by the invariant search against 403, 133 by k-induction against 134.

| Group (research/frontier2's) | tasks | main | here |
| --- | --- | --- | --- |
| A: Lustre, the step goal over a wide transition | 195 | 168 | 185 |
| B: Lustre, within the templates, not found | 39 | 33 | 33 |
| C: a program counter in bits beside at most one linear literal | 38 | 8 | 12 |
| D: a clause of two or more linear literals | 113 | 15 | 18 |
| E: an atom over more than three values | 71 | 28 | 31 |
| F: a remainder, a quotient, a projection's existential | 34 | 7 | 9 |
| G: not Lustre, within the templates, not found | 15 | 8 | 8 |
| H, I: unsat | 303 | 242 | 241 |
| the rest | 598 | 426 | 429 |

- `growCdcl(..., {model: true, core: true})` (on bmc2's session, `cdclSession(goal, root, {model, core})`): a
  refutation's outcome names the hypotheses its leaves read (each leaf's rows are those hypotheses' facts at its
  decisions, or rows true of any value: the trail's atoms, the naturals, the term columns' definitions); a clause never
  made into a node (a bound's, not yet materialized) leaves it unnamed. Off, the search is as it was: research/dag's
  332 step goals give the same trees (outcome, leaves, splits, conflicts, decisions) by `growCdcl` and by `grow` here
  and on main, all 664 proven, and `GDP_CDCL_VERIFY=1` passes (`runs/chcsat/m1/eq`, `eq-main`). 88 cores of step goals
  of four tasks (ctigar, HOLA, Lustre) each refuted again with their hypotheses alone.
- The join's goals (`stepWith`): first a model alone of the CDCL search at a quarter of the goal's budget, the forms a
  refutation read (its core) standing for those a tree reads (`usedHyps`); a model is the counterexample; undecided,
  the prover as before. The set's proof below is the prover's, trees and all, as before.
- Cubes (where the join stopped with no candidate that rules a counterexample to a caller's law out: `target`): the
  point's cube is its control literals (the choices and yes/nos) and, greedily, the direction (each value up and down,
  pairs of them where few, the rule's own comparisons first) that leaves out the most samples still in it, its bound as
  weak as leaves them out; it is blocked relative to the set (the set and the cube's negation assumed before the step,
  each of the cube's literals after the step a hypothesis of its own), and its literals are cut to those the
  refutation's core read, put back where a sample or the start would be in it. A model is a predecessor the set allows:
  the forms that rule it out added to what is assumed (as the join's attempts do), else its own cube blocked first (3
  deep), else the cube made smaller to leave its successor out (a reached state's successor a sample now). Each cube
  blocked is a form of the set ("never all of these"), kept or dropped by the join as any other; 48 at most, 2 s a
  query. Once one is in, the join has 0.3 of what is left of its time and the search below the rest.
- The control states no run reached (pc values in bits, their combinations) one form for all until it is first broken:
  each alone needs the others to be inductive, a goal each with the whole set (ctigar's `nest-if3`: 30 rounds of 0.5–0.7
  s, each proving one such goal, `runs/chcsat/full1-noframes`); once broken, each its own form, so that a state joined
  in changes only the proofs that read its own control state. Kept one form for good, a real-world law's search
  (xstate gapless.js, "the fetch-and-decode child is spawned at most once") went from 6 of 6 proven to 0 of 6
  (`runs/chcsat/final2/gapless-k`, before the merge); after it, split at the second break, 6 of 6 at 43–58 s (main
  41–47 s); at the first, 6 of 6 at 33–44 s (`runs/chcsat/m1/gapless-ab`). The
  first break costs group C about 4 (12 and 11 in two runs against 15, 15 and 16, the whole track 566 and 570 sat
  against 567, 571 and 575, `runs/chcsat/m1/chc-k1a`, `chc-k1b`, `chc`, `chc-k2a`, `chc-k2b`); the real-world verdicts
  come first.
- `InferOptions.minimize` (default true): false answers as soon as the set is proven, without taking out what the
  proof doesn't need; compare/chc/solve.ts passes false (on the 532 sat tasks both solve, a median 28.94 s here, 29.81 s
  on main).
- By family: Lustre 307 → 329, ctigar 13 → 22. Lost: s_split_08, s_split_22_000_000, nested-while_merged_safe,
  FIREFLY_4_e3_1713, _6counters_e8_371_e1_448 (sat), 025c-horn (unsat, by main's bounded runs at 28 s, not found here).
  s_split_08 is the samples' (run locally three times each: proven 2 of 3 here and 2 of 3 on main, the search below
  the join failing where the runs' samples leave 124 of its 164 candidates); FIREFLY_4 had fewer samples (142 against
  205); on the others the join's cubes took time the search below it used on main, or the search stopped otherwise.
- Before merging main, beside 6b2e2df: 816 (551 sat, 265 unsat) against 782 (517, 265) (`runs/chcsat/final4/chc`,
  `chc-main`; main four times that day 517, 519, 521, 523), the second frontier corpus 27 of 47 in both with every
  broken variant refused and each item's verdict the same (`final4/corpus2`, `corpus2-main`), TermComp's ITS 1,029 and
  1,041 in both, terminating 568 and 578 against 574 and 580 (the 8 terminating tasks main answered and this didn't,
  run twice more each: main 8 of 16, here 7 of 16, `final4/itsl-*`), SV-COMP 181 against 182 (`final4/its`, `sv`).
- Measured and left out (each against the same code without it, on the 169 tasks of `runs/chcsat/dev.json` or all
  1,406, before the merge): IC3 with frames after the join (F_1..F_N, lemmas pushed, obligations by level, cubes joined
  per control state; 547 against 552 on all, `runs/chcsat/full1`, `full1-noframes`); runs from the kernel's models past
  the samples' bounds (k-step goals from a sample, 4 steps at most: few models within budget on Lustre, 27 of 80 Lustre
  tasks both ways, `l1`, `l1n`); runs whose every request is a CDCL model, for Lustre's few samples (28, 29, 27 and 28
  of 80 at shares 0, 0.1, 0.25, 0.4, `l2o`, `l2`, `l3a`, `l3b`); the search below the join by CDCL models first (551
  against 554 on all, `full2`, `full2-nosearch`); the set sliced by the control states a step comes from (33 against
  47, `dev-c8`, `dev-c8ns`); every unproven goal of the cone in one query (44 and 44, `dev-c10`, `dev-c10o`); cubes'
  predecessors 8 deep (41 against 40); the join's share at 0.9 (38 against 39).
- The real-world corpus, after the merge: every law's verdict as main's, 237 proven, 56 open, 18 refuted
  (`runs/chcsat/m2/rw`, `rw-main`); gapless.js's law 56.0 s on main, 39.7 s here; run eight times more each in one
  batch, 7 of 8 here (33.6–60.0 s, one at 61.7 s unknown), 8 of 8 on main (42.6–58.6 s) (`m2/gapless`).
- The suites, launched together with main's: by default 217 jobs, none failed, 636.2 s wall and 5,349.3 s of job time,
  main 633.6 s and 5,475.5 s, none failed (`runs/chcsat/m3/suite`, `suite-main`); `--usual` none failed, 646.0 s and
  4,961.4 s, main 564.4 s and 4,946.5 s (`suite-usual`, `suite-usual-main`).
- `infer`'s and `data`'s tests on 1 vCPU, ten jobs each here and on main, interleaved in one batch, twice
  (`runs/chcsat/m2/vcpu1`, `m3/vcpu1`). `infer`'s 5 s-limited "a law that needs an invariant": min, median, max 1,989,
  2,857, 5,841 ms here and 2,132, 2,970, 3,495 on main, then 1,948, 2,946, 3,353 here and 2,049, 3,096, 5,121 on main;
  each batch failed it once past 5 s, here in the first and on main in the second, both in a job whose every test ran
  two to twenty times its usual time (here "the bounded run" 3,182 ms against a median 148). `data`'s nearPlus ("a
  function that agrees with + on small values"): 1,879, 2,636, 3,380 here, 1,861, 2,385, 2,986 on main; then 1,886,
  2,477, 3,056 here, 2,500, 2,737, 3,359 on main. No other failure.
- The budget split is main's: random runs 5 s, guided runs 8 s, bounded runs 15 s (with k-induction beside), the
  invariant search the rest.
- Sizes against 54bbec9: `core/infer.ts` +191 −22, `kernel/cdcl.ts` +35 −8, `compare/chc/solve.ts` +1 −1.
- Cost: Modal $65.99 for the 114 apps before the merge, $20.64 for the 26 after it (`modal billing report`, today's
  and yesterday's figures before the day closes). No boat.

## 0.24.0

CHC-COMP's unsat side caught up most of the way, SV-COMP is read from C as C runs, and two trusted additions came with
their Lean proofs first. At 60 s on Modal, none wrong: CHC-COMP LIA-Lin 938 solved (540 sat, 398 unsat), 801 for main
launched beside it (`runs/bmc2/chc-merged1`, `runs/bmc2/chc-main5`), 782 at 0.23.0; two tasks whose expected verdict
rests on one tool's vote (or a placeholder) are answered unsat with derivations of 999,002 and 280,277 steps, each
checked twice, and listed apart as disputed (`compare/chc/disputed.json`). SV-COMP's termination tasks 213, 182 for
main beside it (`runs/svfront/f5-mine`, `f5-base`), after three independent checks of the C front end (176 probes, none
answered against how the C runs). TIP 2015 183 of 492 (`runs/termlem/tip4`), 181 at 0.23.0. The real-world corpus:
237 of 311 laws proven with nothing stated, 218 at 0.23.0, liveness 18 of 35 (0). Trusted additions: k-induction
(`lean-kernel/KInd.lean`'s `kind_sound`, then `kernel/kernel.ts`'s `checkKInduction`, 39 lines), solving 14 of the 17
CHC tasks known to be k-inductive; and rings of mutually recursive functions (`lean-kernel/Data.lean`'s
`wf_fix_unique_ring`), each on the standard axioms. Rules can now be read from TypeScript (`gdp-wired/extract`), each
checked against the code it was read from. The release suites (217 jobs, one after the other) on Modal: by default
624.7 s wall, 5,686.2 s of job time, none failed (`runs/release/0.24.0-default`); `--usual` 576.2 s, 5,169.4 s, none
failed (`runs/release/0.24.0-usual`).

Bounded runs faster and longer: CHC-COMP LIA-Lin at 60 s on Modal, 923 answered (526 sat, 397 unsat), main (6b2e2df)
launched beside it 783 (517, 266); unsat 131 more and none fewer, sat 17 more and 8 fewer, out of time 5 against 8
(`runs/bmc2/chc-mine4-b15`, `runs/bmc2/chc-base4`). Every unsat answer is a run the compiled rule takes and
`checkDerivation` confirms against the CHC; none contradicts Spacer's or Golem's verdict, and 20 are tasks neither
answered. Two derivations refute their task's expected verdict, both checked again by a simulation of the clauses:
`s_split_50_000_001` (999,002 steps; its verdict sat is LoAT's vote alone) and `s_split_22_000_001` (280,277 steps; a
placeholder verdict, no vote): compare/chc/disputed.json records them, `summary.ts` lists them as disputed (neither
right nor wrong), and their derivations are kept (`runs/bmc2/disputed/`, checked again by research/bmc2/disputed.py). Lustre's 321 unsat tasks: 147 to 254; by Golem's
derivation length, 4 steps 18/81 to 78/81, 5 or more 9/59 to 19/59; the round-2 corpus's group H 108 to 215 of 273. Its
derivation items 3 of 3 (main 2): `s_split_01`'s 10,002 steps in 260 ms. Nothing trusted changed (`kernel/kernel.ts`,
`kernel/cyclic.ts`, `core/check.ts` and `lean-kernel/` are as at 6b2e2df).

- core/bmc.ts: each goal relaxed (an integer pair written as any two naturals of the difference, which every read of
  a pair is; the interpreter normalizes, and where it refuses the run the goal itself is asked) and reduced (copies and
  constants put in, definitions nothing reads dropped and put back into the model); the deeper goals one growing goal
  for one CDCL search (kernel/cdcl.ts's `cdclSession`: each depth's query assumed by an activation atom and set aside
  at the next, so learned clauses, activities, phases and the simplex carry over), its cone of influence; a forced run
  first (a deterministic loop run by the compiled rule, up to 30% of the stage and a million steps); the counted
  clock's rate 250 units a ms (252 measured at the median, 168 at main).
- kernel/reader.ts keeps a value with an open read while nothing it read has changed (`touch` at each change of the
  trail marks its readers): research/dag's 332 step goals give the same trees, by `growCdcl` and by `grow`, as at 0.23.0,
  in half the search time (608.4 s to 303.9 s; 638.7 s to 360.9 s); 734 bounded-run goals searched alike with and
  without it (`runs/bmc2/eq332-1`, `eq3`, `eq2`).
- compare/chc/solve.ts's `bmc` stage 15 s (was 10): beside main in three batches, 10 s against 15 s solved 902 and 910,
  904 and 914, 909 and 923; 20 s 917 and 923 (compare/chc/README.md, `runs/bmc2/chc-*`).
- The stage alone on the 475 unsat tasks (56 s): 407, main 312; within 10 s 365, main 244 (`runs/bmc2/only-inc3`,
  `only-base1`).
- The other benchmarks beside main, launched together: TIP 2015 182 proven, main 181 (`isaplanner/prop_51` more, none
  fewer; `runs/bmc2/tip-mine`, `tip-base`); SV-COMP termination 182 and 182, every answer the same (`sv-*`); TermComp
  ITS 1,029, main 1,026 (10 more, 7 fewer, each where the lasso and rank searches, random and bounded by wall time,
  finish near the limit, `its-*`); research/realworld's 311 laws: every verdict as main's (`rw-mine3`, `rw-base`).
  The second frontier corpus: frontier 28 of 47, main 27, every broken variant refused in both (`corpus2-mine2`,
  `corpus2-base1`).
- The infer and data tests on 1 vCPU, ten jobs each side interleaved (`runs/bmc2/onecpu`): none failed; data's "agrees
  with + on small values only" median 2,447 ms, max 3,341, main 2,985 and 3,665; infer's slowest median 4,895 ms, max
  5,814, main 5,302 and 6,052. search.test's "a search that finds nothing" 0.89 to 1.18 s, main 0.53 to 0.84 s (its
  counter is a deterministic loop, run forward until the forced run's share is spent), within its 8 s.
- A new test (core/search.test.ts): a deterministic loop broken after 10,000 steps, refuted by its forced run.
- After merging main at 5055882 (k-induction on the second vCPU beside every stage; the bounded runs' stage unchanged
  in the first process's time plan): CHC-COMP 938 answered (540 sat, 398 unsat, 2 of them the disputed labels above),
  main 5055882 launched beside it 801 (536, 265); unsat 133 more and none fewer, sat 10 more and 6 fewer (5 solved
  past 58 s in main, and `s_split_42_000_000`), sat by k-induction 134 against main's 133 (`runs/bmc2/chc-merged1`,
  `chc-main5`). The 332 step goals: the same trees by growCdcl and by grow (`runs/bmc2/eq4`). The suite (217 jobs): by
  default 552.7 s wall, 5,164.0 s of job time, none failed (`suite-merged-default`); `--usual` 569.4 s and 4,888.9 s,
  none failed (`suite-merged-usual`). The infer and data tests on 1 vCPU beside main's, interleaved (`onecpu2`,
  `onecpu3`): none failed; "a search that finds nothing" median 1.2 s against 0.8 s (above), the rest within the runs'
  spread (the infer join test median 6,004 and 5,511 ms in two runs, main's 5,334 and 5,944).
- The suite (213 jobs) on Modal at this branch's last commit: by default 552.0 s wall, 5,042.3 s of job time, none
  failed (`runs/bmc2/suite-default2`); `--usual` 526.0 s and 4,497.3 s, none failed (`suite-usual2`). Main's default
  run beside an earlier commit here: on the 207 jobs both passed, 4,833.9 s of job time against 4,846.9 s
  (`suite-base-default`, `suite-default`; main's other 6 failed in that checkout, which lacked the vendored sources).

Termination through lemmas: a ring of functions calling each other taken by well-founded recursion (a measure each),
and a call's decrease proven through size laws about the function of its argument, conjectured, proven by induction
and used. **Trusted change:** `lean-kernel/Data.lean`'s `wf_fix_unique_ring` (a functional over a ring's tuple of
functions that reads each only below its measure has exactly one fixpoint; `#print axioms`: propext, Classical.choice,
Quot.sound), proven before core/data.ts accepts a ring, whose acceptance mirrors its condition: each call within the
ring, under its path, lowers the callee's measure at the call's arguments below the caller's at its parameters, each
obligation proven by the kernel in a program without the ring. `kernel/` and `core/check.ts` are as before. TIP 2015 at
60 s on Modal, beside main at c1a0fb5 launched at the same time (`runs/termlem/tip2`, `tip2-base`): 177 of 492 proven in
both, the same 177, and the same 30 refuted (23 in `false/`, each confirmed by TIP's evaluator, none proven); none
wrong. Unsupported 112 against 129: 17 theorems translated now (the 8 bottom-up merge sorts `sort_*MSortBU*`, the 8
`MSortBU2`, `grammars/simp_expr_unambig4`'s ring), none proven within the 60 s, and 8 of `false/` (the regexp `reck`
rings), none refuted; none lost. An earlier step (`runs/termlem/tip1`, `tip1-base`: 179 against 177, the three more
near 60 s on both sides) took the size laws after a while of induction and lost `sort_nat_QSort*` (4) to the budget;
fixed (below).

- Rings (`core/data.ts`'s `termination`, one code path for a function and a ring): the calls within the ring with their
  paths, the runs recorded per call (caller to callee), the obligations as before but across functions, measures padded
  to one length (`lexLt`). A call to the ring nested in another's argument or condition is refused at once (nested
  recursion). `checkMeasures`: measures given to a ring checked as `termination` checks its own (for conformance).
- The calls' relation (`callRelation`): a location per function, a path per call, the caller's parameters' sizes and the
  callee's arguments' bounded by the sizes of the path's variables (`sizeBounds`, fitted to the path's values, naturals
  up to 40 so a guard is met), ranked by core/cycles.ts's relation search per location (`rankOfPaths`, its forms per
  location now returned beside its terms): `tokens`/`paren`'s size(e) + 1 and size(e), `linTerm`/`lin`'s. Then the runs'
  LP, now per node (`ranksOfCalls`; `ranksOfRuns` the ring of one), and each function's parameters' sum.
- Size laws (`sizeLaws`): for each function an obligation reads, S(g(y…)) + a ≤ S(yᵢ) [+ S(yⱼ)] + b at the bound its
  values give (an equation's upper half only), and 2·g(n) ≤ n + b for a natural of one natural; given to proveData as
  lemmas with `lemmasFirst` (no attempt of the law alone first: its lemmas proven by induction, the law tried after
  each), then proveData by induction, then unfolded, all within the function's counted 10 s as before.
- proveData: a lemma about a function used where the goal reads that function (a size law no longer at every size the
  goal reads); a goal that reads sizes gets the shapes at the sizes its shapes read, `depth` rounds (size(xs) is 1 plus
  its tail's, whose size is its own shape's: a recursion two fields deep); recursion induction through a function's
  ring (evens through odds: recursion of evens at the tail's tail).
- The wall-clock leak research/refine found: core/cycles.ts's and core/relation.ts's deadlines read kernel/prove.ts's
  `clock()` (wall time outside a counted search, as before; counted work inside one), and the exact LP's pivots and the
  generators count as work; `ranksOfRuns`' 1,000 ms inside core/data.ts's counted termination search was wall time.
- Lean export (`lean-kernel/data.ts`): a ring in one `mutual` block, each with `termination_by` its measure; a
  datatype's `size_pos` used where a decrease needs another field's size; the size laws an obligation used as theorems
  before it (functional induction, then plain), each at the obligation's variables of its sorts. Package items
  `dataring` (`tokens_positive`) and `dataruns` (`merge_runs_one`), the suite's `lean-data-9`: Lean checks both, on the
  three axioms.
- Conformance (`core/conformance.ts`'s `ringCase`): rings of two functions over naturals from six families, each with a
  JavaScript reference run with fuel: a ring taken ends on every reference run and its measures fall at every recorded
  call, a ring that runs forever (`up`, `late`, `swapKeep`) is refused, `down`, `lateDown` and `pair` are taken, and
  the measures taken, tampered (swapped between the functions, constants dropped, negated), are refused by
  checkMeasures wherever a recorded call contradicts them (the suite's eight conformance jobs, `runs/termlem/suite2-default`: 192 rings, the 108 that end all taken, the 84 that
  never end all refused, 282 of 282 tampered measures refused); `lean-kernel/conformance.ts --rings` writes the rings taken with their
  measures for Lean (`lean-rings`: 12 rings, Lean checks every call's decrease).
- Adversarial definitions (`examples/data.ts`'s `adversarial`, core/data.test.ts): twelve that don't terminate, made to
  look as if they did, each refused with the measures tried: a ring passing its argument round, one lowering and one
  raising it, a ring swapping two lists, a ring that loops past n ≥ 9 (beyond the runs' values), even/odd stepping up,
  a call on a helper no longer than its argument up to 9 items only (its size law refuted by its own induction), the
  same through a ring, 0 calling 1 calling 0, a sum of two that stays, f(n) = f(f(n)), an integer counted down, a ring
  whose stated measures don't fall. `wellFounded`: the ring and a bottom-up merge sort over `pairwise`.
- TIP's translator classifies a ring's refusal by its message (`, in its ring `), as before by its old one.
- After merging main at 7727716 (lang/edges, lang/reals, gen/unsat, gen/extract, research/realworld and the fixes):
  TIP beside 7727716 launched at the same time, 183 of 492 proven against 181, the same 30 refuted, none wrong, none
  lost (`isaplanner/prop_51` and `prop_60` the two more, at 56.4 s and 49.9 s); the same 25 translated now
  (`runs/termlem/tip4`, `tip4-base`). The suites (215 jobs) by default 571.7 s wall, 5,421.7 s of job time, none failed
  (`runs/termlem/suite4-default`); `--usual` 586.0 s and 4,932.6 s, none failed (`suite4-usual`).
- What is still refused among the 105 and the 14, and why: bubsort (8: inversions, no size measure), bmerge (8) and
  toList (16: the size laws about evens/odds and hmerge are conjectured but not proven within the budget; 60 s each
  doesn't either), ssort (8: needs a membership lemma), idiv (12: idiv(x, 0) never ends; TIP calls it at 2 and 3),
  third, twoThirds and nmsorttd-half1 on Int (12: below 0 they never end), McCarthy's 91 (2) and subst (2: nested),
  flatten1 and flatten3 (3: a weighted measure), mod2 (2), msorttd and nmsorttd (8: a chain of size laws past the
  budget); the 13 rings left are nested (stooge, nstooge, models).
- The suites on Modal (210 jobs: 3 new, `lean-data-9`, `lean-rings` and the data tests'): by default 614.5 s wall,
  5,211.1 s of job time, none failed (`runs/termlem/suite2-default`); `--usual` 480.2 s and 4,507.3 s, none failed
  (`suite2-usual`). Round 1 and round 2 of the frontier corpora, against c1a0fb5 the same day: every item's verdict the
  same, round 1 frontier 90 / 92 and broken 42 / 42 in both (the datatype track's items among them), round 2 25 / 47 and
  47 / 47 in both (`runs/termlem/c1-mine`, `c1-base`, `c2-mine`, `c2-base`).
- The `data` job's tests on 1 vCPU (ten each, this branch's and c1a0fb5's interleaved in one Modal batch,
  `runs/termlem/data-1cpu`): nearPlus min, median and max 1,744, 2,302 and 2,582 ms against main's 2,216, 3,013 and
  3,768; nearSucc 1,357, 1,753 and 1,947 against 1,652, 2,309 and 2,698; none failed. data.test.ts took 70.1 s median
  against 13.7 s: the new tests (the twelve adversarial definitions refused, each within its counted budget: 59.4 s
  and 40.0 s on 2 vCPU in `suite2-default` and `suite2-usual`; the rings; the size laws).

What the real-world corpus (research/realworld) found in gdp-wired itself, fixed. Nothing trusted changed (`kernel/kernel.ts`,
`core/check.ts` and `lean-kernel/` as they were). The corpus on Modal (311 jobs, 2 vCPU each), this branch beside main
the same day: at main 6b2e2df, proven 237 against 218, refuted 18 against 17, neither 56 against 76, liveness 18 of 35
against 0 (`runs/rwfix/score2`, `base2`); before main took gen/extract and lang/reals, at 6f03586, 237 against 218,
16 against 15, 58 against 78 (main's 77 unknown and one error) (`runs/rwfix/score`, `base`). Every one of main's
refutations is still refuted, and nothing went from refuted to proven. The 20 changed verdicts, the same in both
pairs: 18 liveness laws proven with the rank 0 found; p-retry's "an uncapped retry waits at least minTimeout" proven
(main threw), through the lemma found `f(x) >= minTimeout`; BullMQ's "an exponential retry waits at least the base
delay" refuted (main: unknown), a law error triaged as one (`triage/queuebreaker.json`: with delay 0 the code retries
at once and the rule leaves its ghost `until` as it was). With rank 0 stated, `rank0.ts` proves the same 18 on Modal
(`runs/rwfix/extra`; the README's 19 was a local run). Suites, each mode after the other, on Modal: at 6f03586's base
210 jobs, by default 485.4 s wall and 5,002.9 s of job time, `--usual` 516.8 s and 4,740.2 s, none failed
(`runs/rwfix/suite-default`, `-usual`); merged with main, 213 jobs, by default 639.6 s and 5,025.4 s, none failed
(`runs/rwfix/suite2-default`); `--usual` 729.0 s and 4,535.9 s, none failed (`runs/rwfix/suite2-usual`). The `data` job's paths (core/data.ts and what it calls) are
untouched, so its 1-vCPU timing wasn't measured again.

- `fromXState` dropped XState v4's `cond` without a word, so a v4 config was proven with fewer guards than it has. It
  now refuses every key it doesn't read, by name (a node's, the root's, a transition's), rather than dropping it: v4's
  `in`, `strict`, `activities`, `onEntry` and `onExit`, `''` (v4's eventless transition), events XState raises itself
  (`xstate.*`, `done.state.*`, `done.invoke.*`, `error.*`), an initial transition given as an object, `history` or
  `target` off a history node, `context` below the root, an unknown state type. It reads `cond` as v4 does, the guard
  v5 calls `guard` (a name, or `{type, ...params}`, the params its other keys): a v4 machine with `cond` guards and
  params runs as v4's own interpreter (xstate 4.34.0, 3,600 steps, checked by hand) and its laws prove. Each XState
  ignores the other's key and takes the transition unguarded, so `cond` in a v5 machine and `guard` in a v4 one are
  refused (the version read off the machine; a plain config is read by the key it uses). `reenter` and v4's
  `internal` are read as changing nothing a chart shows (they choose which entry and exit actions run, and those write
  no context here), which `conforms` confirms against both XStates on self, child and ancestor targets. For gen/extract:
  the API is the same (its `inline` guards and actions kept beside `cond`); a config it took before with a key it
  ignored is refused now; `extractXState` still refuses `cond` itself (its machines are v5's), its reason reworded. None of the corpus's six machines
  was scored through a dropped guard: five are charts by hand with their `cond` guards written in, and gapless.js's
  config (v5's `guard`) builds as before and conforms to XState's actor over 19,200 steps
  (`repro/conform-gapless.ts`, `runs/rwfix/extra`); `repro/xstate-refusals.ts` gives each shipped machine the same
  first refusal as before.
- A map read at a key that reads a flag (`M.at(when(big, a, b))`) threw `unknown flag` from the kernel: the prover
  (`kernel/prove.ts`'s readKeys) offered that key, flag and all, as an instance, and the kernel's goals inline flags.
  The prover now inlines the flags in the keys it offers, as the goals read them; such a rule proves (ERC20's
  allowance slot written with its `approves` flag in the key no longer throws). The kernel is unchanged: it never sees
  such a key from the prover.
- `refuteByRuns` skipped every rule that read a function other than division by a constant, so a false law over one
  came back unknown. Its runs compute each function by its JavaScript, as the rule runs it, and draw params only where
  every fact holds (one about the params alone exactly, one about every key at each key up to twice the bound, or each
  tuple up to the bound), so a recurrence's induction machines (fx a param, given as f(x)) get no run that isn't one.
  Every rule function carries its JavaScript, so a random table would be a run the rule can't take; none is drawn.
- `proveDecision(d, {ms})` honours a budget, on the prover's clock (the counted one inside a counted search); past
  it the verdict is unknown. With none, as before. The corpus passes its 60 s.
- `discover` threw on p-retry's delay, minTimeout · factor^k: its samples kept values past 2^53, and a candidate fitted
  to them held a constant no term can (`290760102328562900 is not a natural`). A run of samples stops where its values
  stop being safe integers, and a candidate with a coefficient that isn't one is dropped.
- With no rank stated, `findLeadsTo` fitted a rank to the helpful steps that stay pending, and where every helpful
  step reaches `to` at once there are none: 0 of the corpus's 35 liveness laws. It tries the trivial ranks first, where
  the runs allow them: 0 (no helpful step sampled stays pending), then each state variable alone that every such step
  lowers and no other raises (up to four); then the fit; then the invariants a rank needs, for the fitted rank or else
  rank 0.
- Tests: `core/xstate.test.ts` (the refused keys; v4's cond against v5's guard), `core/dsl.test.ts` (a flag in a map
  key; a decision past its budget unknown in 300 ms, about 11 s with none), `core/functions.test.ts` (a false law
  through a function refuted by a run; a fact over the params keeps a true law), `core/discover.test.ts` (the p-retry
  recurrence), `core/cycles.test.ts` (ranks 0 and a variable alone, and a helpful step that misses the goal refused).
  Each fails on main.

k-induction: a law that one step doesn't keep but k steps in a row do is proven, with its Lean proof first. Trusted
additions: `lean-kernel/KInd.lean`'s `kind_sound` (a checked certificate makes the law hold in every reachable state, on
`propext`, `Classical.choice` and `Quot.sound`), then kernel.ts's `checkKInduction`, its twin. CHC-COMP LIA-Lin at
60 s on Modal, main at 6b2e2df launched beside it each time, none wrong: 799 and 800 solved (534 sat in both runs,
265 and 266 unsat), main 785 and 777 (519 and 511 sat, 266 unsat) (`runs/kind/chc-mine2`, `chc-base2`, `chc-mine`,
`chc-base`). Of the 17 sat tasks the gen/unsat track found k-inductive and main leaves unsolved, 14 solved, main 0 of
17 (`kind17-mine3`, `kind17-main3`). The real-world corpus's verdicts unchanged.

- The certificate (`KInd`, `checkKInd`): a plain law L (no key), k, and the trees. The base: L's start goal, and for
  each 1 ≤ j < k the k-step goal of j steps (Sets.lean's `checkSKStep`) whose first state is the start (`startC`: each
  state variable its start term) with L there, and L before each later step; the step: the k-step goal of k steps with
  L before each, L after them refuted (primed names, Live.lean's `primeC`). Lean builds every `when` and `then` from L;
  the certificate brings only k, the trees, the instances and the names later requests are read by. The proof is a
  strong induction on the length of the run that reaches a state (`sreach_from`, `SPath`): shorter than k, a base;
  longer, the step from the state k requests back, L holding at each state after it by the induction (`sallowed_rep`,
  `kind_then`, `start_meets`). kernel.ts: `kInductionSteps` builds the same k-step laws from L, `kInductionStart` its
  start goal, `checkKInduction` checks them (the laws' proof, the start, `checkStepLaws`). Lean's checks are kernel.ts's
  plus what the twin's proof reads (the law reads no request's name, flag or later name; the start reads the params).
- Conformance (core/conformance.ts's `kindCases`): shift registers and rotations whose law is k-inductive for one least
  k (1 to 4), with a map and a second law in some, and each certificate's twins: k said to be k + 1, a base depth left
  out, the step's tree for k given for k − 1 (the law k-inductive only at k), the step's tree for k inside a
  certificate for k + 1, the law read stricter. kernel.ts accepts every certificate found and refuses every twin but
  the stricter law where it is still true (each accepted one holds on the reference's runs); Lean's `checkKInd`
  computes kernel.ts's answer on every one (lean-kernel/conformance.ts --kind, the suite's `lean-kind`: 24 machines,
  33 certificates checked true and 79 twins computed to kernel.ts's answer, by default).
- The search (core/kind.ts, untrusted): k = 2, 3, ... on the counted clock, each step goal decided by CDCL's model
  search (kernel/cdcl.ts, as core/bmc.ts asks it); refuted, the laws it assumes proven once (their usual trees, no
  cyclic certificate), the start goal and the base goals grown, the step's tree CDCL's, unfolded (prove.ts's grow keeps
  CDCL off goals over k steps; here the plain search's cases multiply with every step). `proveRule` tries it on the
  plain laws as one, the rule's kinds assumed, after the shallow bounded runs, within a twentieth of the search's budget
  (at most 500 ms), and reports `k`. Lean: the LeanItem `kInduction` and smachineToLean's `kind` write a `KInd` through
  `kind_sound`; examples/kinduction.ts (a clamped pipeline, k = 3; a token ring, k = 4; the unclamped pipeline refused
  with a run).
- compare/chc/solve.ts: compare/chc/kind.ts runs the search beside the other stages, a second process at nice 19 on
  the container's second CPU, from the import to the search's deadline, and answers sat when it proves the law. On the
  CDCL search's trees the counted clock runs about twenty times past wall time (compare/chc/prof/kind-tree.ts,
  `runs/kind/tree1`), so there the wall stop is the budget, as for every stage under the track's wall-clock limit. At
  the same priority the invariant search lost answers to it: of the 41 tasks either side answered alone in the first
  run, 30, 31 and 32 answered here, 32 and 35 at nice 19, main 9, 16 and 18 (`ch-mine-*`, `ch-nice-*`, `ch-base-*`).
- The second run (at nice 19), 21 gained and 7 lost. Gained by k-induction, 15: s_split_36 (k = 3), bug15_safe (10),
  hysteresis_2, _3 and _all (3), fast_2_e8_460 (3) and 9 metros_1 variants (4), each in all three runs of it; and by
  the invariant search, 6 (s_split_04, simple.c, xy0.c, DRAGON_9_e7_1843_e3_5316, DRAGON_all_e3_4821_e1_1318,
  durationThm_2_e1_118). Lost: break_merged_safe, 015-horn, xy10.c, durationThm_2 (the invariant search) and
  O3_id_o10 (unsat by bounded runs, found at 22.2 s in main), each answered in 1 or 2 of the 2 reruns here and in 1 or
  2 of main's 3 runs; break_safe (here 1 of 3, main 3 of 3; in the first run's set the reverse, here 3 of 3 and main 1
  of 3) and FIREFLY_4_e3_3511_e5_3248 (here 0 of 8 runs, main 2 of 6), where the search beside it slows the invariant
  search (`ch2-mine-*`, `ch2-base-*`, `ch-*`). The first run (same priority) gained 32 and lost 9, every loss the
  invariant search's.
- k-induction answered 133 tasks in the second run (k = 2: 62, 3: 39, 4: 24, 5: 4, 6: 3, 10: 1; the first run's 132
  among them), 118 of which main answered by the invariant search. Each of the 133, searched again by
  compare/chc/prof/kind-lean.ts and written as Lean, checked by Lean: `task_kind_holds` on the standard axioms
  (`kindlean1`, `kindlean2`, `kindlean3`; a metros certificate is about 1.9 MB of Lean and takes 3.5 to 6 minutes). Not solved of the 17: HOLA/04.c (k = 11: the step
  decided past 30 s), bmc-3 (k = 9: a base goal of 7 steps not grown in time) and fast_2 (k = 3: no tree in time).
- The real-world corpus (311 laws, `runs/kind/rw-mine2`, `rw-main2`): 218 proven, 17 refuted, 75 unknown, 1 error on
  both sides, law by law; none needed k-induction within its 500 ms. The second frontier corpus: 27 of 47 on both sides,
  every broken variant refused (47 of 47), the same outcome per item but two TIP items unproven on both sides (out of
  time on one side, not proven on the other) (`f2-mine`, `f2-base`). search.test.ts's tests on
  1 vCPU, ten runs each beside main's: "an invariant nobody wrote" 1,559 ms median (at most 1,839), main 1,067 (1,427),
  the k-induction it tries first; the rest within noise (`infer-mine`, `infer-base`).
- The suites (215 jobs, 2 new: `kinduction`, `lean-kind`): by default 758.7 s wall, 4,972.2 s of job time, none failed
  (`runs/kind/suite-default`); `--usual` 581.2 s and 4,626.8 s, none failed (`suite-usual`).

Rules read from the code that ships (`gdp-wired/extract`, core/extract.ts): `extract(code, {entry})` reads a reducer,
`useReducer`'s, functions over one record, a Redux Toolkit slice or a class whose methods write its fields, through the
TypeScript compiler, and returns the rule that steps the same way, as a builder value and as the source that makes it
(`toSource`); `extractXState` reads an XState machine's guards and actions, named in `setup()` or inline in the config,
for `fromXState`. The extractor is untrusted: each rule is run beside the code it was read from, and any difference
refuses it. Nothing trusted changed (`kernel/`, `core/check.ts` and `lean-kernel/` are as in 0.22.0).

- The subset: integers (a literal that isn't one refused; division only as Math.floor or Math.ceil of x / k for a
  constant k; % by a constant of a natural, since JavaScript's takes the sign of x), booleans, string-literal unions,
  strings set and compared, records and nested records (spreads, shorthand), Map and Record state keyed by numbers or
  strings (get, set, has, delete, [k], ?? or || a default), conditionals, ternaries, && || ?? (the right side's effects
  on its own path), early returns, switch on a tag (fall-through, default), Math.min, max and abs, Date.now() as an
  input read once a step, throws as the rule's assumption (or a constructor's as its precondition), helpers, methods and
  getters of the same files inlined, relative imports read. Each number is a natural where the code keeps it one (a
  subtraction printed as `minus` only where solver.ts proves it at most what it subtracts from, under the branch's
  conditions, the code's refusals and an XState transition's guard), an integer elsewhere. Refused, each where it is
  and why: loops, arrays, floats, async, try/catch, a write to the state a reducer is given (React and Redux keep the
  old state), a throw after a method wrote a field, two keys of one map written in one step, a map replaced whole, a
  reference into a map held across a set, `extends`, a module's own mutable state, closures, Math.random, Date.now()
  read twice in a step, other modules' code, v4 `cond` (which fromXState would drop), a machine made by a function.
- The check (core/extract-check.ts): the code compiled by TypeScript and run in node:vm with a counter on every branch
  arm, the rule through `rule.interpreter()` and `rule.compiled()` (compared too): runs from the start (random requests,
  near the boundaries, the time moving on or back), single steps from drawn states, and single steps from proveSteps'
  witnesses for each branch condition over the state and the request; every state variable, map cell, method result and
  refusal compared. Past 2^53 the code rounds where the rule's runtime refuses: counted apart, the run ended there. An
  XState chart is checked by `conforms` against XState's own actor. Each map's representation (a key it doesn't hold
  holds the defaults) is handed out as `invariants`, inductive, to prove laws beside.
- Widened along the way, each for a refusal of real code: `fromXState`'s `inline` (guards and actions written in the
  config, given by their place in it) and machines with no states (root transitions only); `when(c, str, 'x')`, a
  literal beside a string value, as beside a choice.
- On 22 examples from open-source code, each pinned (research/extract/sources.json: react.dev, redux's examples and
  Redux Toolkit's template, statelyai/xstate's examples, five rate limiters): 10 extracted, 12 refused with the place
  and the reason (`runs/extract/batch4`, research/extract/results/ours.jsonl). The 5 step functions: 11,955 requests
  in runs from the start, 2,000 steps from drawn states, 20 steps from the prover's witnesses (of 22 conditions asked;
  conditions over a map's cells aren't), 2,338 requests both refused, 14 steps past 2^53, 11,623 steps where the
  generated JavaScript agreed with the interpreter, 10 of their 10 branch arms reached; the 5 XState machines: 16,000
  events. Refused: a reducer that mutates its state (react.dev's own pitfall), an array (redux's todos), `invoke`,
  `onDone`, `always`, an undefined context, a fractional rate, `#private` fields, a destructured constructor argument,
  an optional field (the limiter package's request queue, in the file its bucket imports), two functions with no
  initial state (a sub-reducer, an Express middleware).
- research/realworld's 41 sources (its sources.json at 6c675e4, read as it is, the whole file): none extracted
  (research/extract/results/realworld.jsonl). 20 aren't TypeScript or JavaScript (Solidity 7, Go 6, Python 2, Ruby 2,
  Lua 1, Zig 1, CoffeeScript 1); of the 21 that are: `extends` 7, a machine made by a function 4, a function that isn't
  a step over a state 3, an export that isn't a function 2, and one each of a `Date` field, a Map as a constructor's
  argument, an array, a null context, a v4 `cond`. So no corpus law could be compared on an extracted rule.
- The laws of the 10 extracted examples, beside a rule written by hand the corpus's way (research/extract/verdicts.ts):
  27 laws, the same verdict for each, 17 proven and 10 refuted on both sides (research/extract/results/verdicts.jsonl).
  Before the representation invariants were handed out, 2 of 27 differed (`runs/extract/batch2`): step laws about the
  Redux cart's quantities, refuted of the extracted rule from a state no object of the code is in (a key it doesn't hold
  with a count), proven of the rule by hand, which has no such state.
- core/extract.test.ts, 31 tests: the shapes, and programs where a naive reading would be wrong, each refused with the
  reason or extracted and checked: aliasing (a write through a second name for a copy; objects chosen by the path), a
  write through a reference to the given state, a shallow copy's nested object, a Map's own set, two names into one map,
  a reference held across a set, overflow, floats and division, a negative dividend's %, NaN and Math.min(), short-
  circuit effects, a throw mid-update (a method's, refused; a reducer's, extracted), a getter with effects, closures and
  module state, Date.now() twice, Math.random, loose equality with a string. A check that catches the extractor itself:
  an XState guard and action read the same payload field as two inputs, and the chart and XState parted on the first
  run that sent them; fixed, and the test keeps it.
- Dependencies: `typescript` an optional peer (the extractor reads with it); `@reduxjs/toolkit` 2.13.0 dev only (the
  check runs a slice through Redux Toolkit itself). The corpus's code is fetched at its commit, not committed.
- The suite on Modal beside main at this branch's base (5c3f947; main has since moved), the suite with the new `extract`
  job: by default 474.5 s wall, 4,708.6 s of job time, none failed, the base 572.7 s and 4,727.5 s, none failed
  (`runs/extract/suite-default-2`, the base's `suite-default-2`); `--usual` 491.9 s and 4,307.2 s, the base 494.0 s and
  4,300.6 s, none failed there and one here: `lean-nonterm`, whose `conformance.ts --nonterm` (certificates from a
  300 ms search) failed the same way in the base's first default run and passed 4 of 4 times on each side when run
  alone (`runs/extract/suite-usual`, `nonterm4`). On the 206 jobs both ran: 4,699.4 s and 4,727.5 s by default,
  4,298.9 s and 4,300.6 s `--usual`. Modal's billing for the work: $0.870 here (four extraction batches $0.011, three
  suites, the lean-nonterm reruns), $0.851 for the base.

SV-COMP's C programs, faithfully and more of them (`compare/term/c2ari.py`): C's integer types and conversions on the
task's data model (unsigned arithmetic modulo 2^n, the usual arithmetic conversions, narrowing as gcc does it, _Bool
0 or 1), undefined behaviour ending the run (a signed overflow, checked unless the task's .yml declares none; division
by zero; an access out of bounds or through a bad pointer), division by any divisor, the ternary operator, calls
inside expressions, arrays of a fixed size, pointers to a fixed set of objects (&x, malloc, alloca, free), and
recursion as two translations, each exact for its one answer (for "terminates" a call either never returns, its frame
forgotten, or returns any value and writes any value to the globals it may write; for "nonterminating" calls inlined
4 deep, past that never returning); solve.ts `--want` searches for one answer. Nothing trusted changed. 271 of the
282 tasks translate (226 before); the 192 that translated before and have no overflow to check translate character
for character as before (`runs/svfront/translations-main`, `translations-mine`). At 60 s on Modal, launched together
with main at 6b2e2df: 213 solved (158 terminating, 55 not), main 181 (134, 47); per component 199 (144, 55), main 172
(125, 47); none wrong against the tasks' expected verdicts, none lost (`runs/svfront/f2-mine`, `f2-base`). Ultimate
Automizer 224 (`runs/modal/term/sv2`); 16 of the 213 it doesn't answer, 27 of its 224 not here (18 loops whose rank
isn't found, 6 recursive programs needing what a call returns, 4BitCounterPointer, and 2 nonterminating). 38
adversarial C programs (`compare/term/adversarial/*.c.txt`, `c2ari_test.py`: conversions, the data model, recursion,
arrays, pointers, division, undefined behaviour where it is and isn't evaluated) are never answered against how they
run (`runs/svfront/probes2`). Suites: by default 213 jobs, none failed, 595.3 s wall, 5,213.5 s of job time
(`runs/svfront/suite-default`); `--usual` 213 jobs, none failed, 504.5 s wall, 4,895.0 s (`suite-usual`); `term-c2ari`
now takes 2 vCPU.

An independent check of the C front end (branch verify/sv-front, research/verify-sv: 93 adversarial C programs, run
natively under gcc and clang with UBSan) found 20 answered against how C runs, from 8 defects, now fixed, each
modelled or refused: static locals in main start at 0; a pointer read knows every object the program takes the address
of or allocates (two passes, the second with the first's objects), not only those earlier in the text; an overflowing
constant on the side of && or || that isn't evaluated no longer ends the run; an array past 64 elements keeps the
elements read at plain int constant indices only (no names, suffixes or wrapping), anything else refused; an enum's
type is gcc's (unsigned int where no constant is negative, constants counted from the one before), and a task's typedef
of bool is its own; preprocessor directives other than #include of a known standard header are refused (no task has
one); C's unspecified evaluation order is refused wherever it can matter (two calls one of which writes a global or
through a pointer or ends the run, a call writing what the rest of the expression reads, an assignment's target
included); a task's own reach_error that returns is its own function. Also: with goto, the entry's 64-bit values keep
their range (a declaration jumped past), and an array whose size reads a variable is refused. All 93 programs are now
answered by no run against how C runs (`runs/svfront/verify-fix1`); 21 of them join `c2ari_test.py` (60 programs, none
answered against the program, `suite-default-2`). The 282 tasks' translations are unchanged, character for character,
for both recursion translations and --unchecked; 4 refusals' messages reworded (`translations-fix`). SV-COMP beside
main at 5055882, launched together: 213 (158, 55), main 182 (135, 47); per component 199, main 172, none wrong, none lost
(`runs/svfront/f4-mine`, `f4-base`); a run before it answered 212 (`f3-mine`: gcd01-2, translated the same, not proven
within the time where four other runs proved it at 26 to 33 s). Suites after merging main at 5055882: by default 217
jobs, none failed, 640.8 s wall, 5,350.6 s of job time (`suite-default-2`); `--usual` 217, none failed, 602.9 s wall,
4,961.4 s (`suite-usual-2`).

Its re-check (branch verify/sv-front-2: 52 more programs) found 2 more defects, fixed: the order check read `*p` as
reading only p (now a dereference reads every object the program takes the address of, and every allocated cell:
`*p + f()` and `*p += f()` with f writing the global p names are refused); and comments were stripped by regular
expressions, so a /* inside a // comment or a string literal began one (now one pass left to right, as C's lexer reads,
string and character literals kept whole). Refused as compilers read them differently: trigraphs, and a backslash with
spaces before its newline. All 145 programs: no run answers against how C runs (`runs/svfront/verify-fix2`); 6 join
`c2ari_test.py` (66, none answered against the program). The 282 tasks' translations unchanged, both recursion
translations and --unchecked (`translations-fix2`). SV-COMP beside main at 5055882: 213 (158, 55), main 182 (135, 47);
per component 200, main 172; none wrong, none lost (`f5-mine`, `f5-base`). Suites: by default 217 jobs, none failed,
533.6 s wall, 5,227.8 s of job time (`suite-default-3`); `--usual` 217, none failed, 593.2 s wall, 4,837.5 s
(`suite-usual-3`). Not done (it loses answers, it isn't unsound): a call before && or ? is sequenced first, so
`f() && g` could be allowed where f writes g; it is still refused.

## 0.23.0

Every benchmark moved, two trusted additions came with their Lean proofs first, and a real-world corpus joins the
scoreboard. At 60 s on Modal, none wrong: CHC-COMP LIA-Lin 782 solved (518 sat, 264 unsat), 510 at 0.22.0 the same week
(`runs/unsat/chc`, `runs/inv/chc-base`); TIP 2015 181 of 492 proven, 140 at 0.22.0 (`runs/edges/tip`,
`runs/lem/tip-final-base`); TermComp's ITS 1,035 answered (572 terminating, 463 not), 376 at 0.22.0
(`runs/ranks/r4-its-merged`, `runs/ranks/r2-its-base`); SV-COMP's termination tasks 181, 47 at 0.22.0
(`runs/ranks/r4-sv-merged`). An independent check of the new termination proofs found two translator bugs (constants
folded in floating point, C narrowing ignored), fixed here; no reported answer was wrong. The real-world corpus
(`research/realworld/`): 51 rules and state machines from open-source code, 311 laws, 218 proven with nothing stated, 15
refuted, each a suspected bug in the original code. Trusted additions: a run that never ends (`lean-kernel/NonTerm.lean`'s
`never_ends_of`, then `kernel/kernel.ts`'s `checkRecur`), and linear arithmetic over the rationals
(`lean-kernel/Rationals.lean`'s `checkQ_sound`, `sound`, `machine_sound`, then kernel.ts's rational check and
`core/check.ts`'s rational mode, its integral mode exactly as before), each on the standard axioms. The release suites
(212 jobs, one after the other) on Modal: by default 649.7 s wall, 4,951.6 s of job time, none failed
(`runs/release/0.23.0-default-2`); `--usual` 568.4 s, 4,595.5 s, none failed (`runs/release/0.23.0-usual-2`).

Ranks from a loop's relation, not only its runs: each path of a turn read exactly (its vertices, rays and lines), a
rank per location, blocks in order, multiphase, with invariants by Houdini, every rank still proven by the kernel.
Nothing trusted changed (`kernel/`, `core/check.ts` and `lean-kernel/` are as in 0.22.0). With the runs that never
end (below), TermComp's integer transition systems at 60 s on Modal, the same day against main at 2477b4a (runs
that never end, no ranks from the relation) and 0.22.0: on the task's statement 1,035 solved (572 terminating, 463
nonterminating), 2477b4a 508 (56, 452), 0.22.0 376 (56, 320); per component 1,045 (582, 463), 2477b4a 618 (155,
463), 0.22.0 480 (155, 325); LoAT abmc 776, KoAT2 601 (`runs/modal/term/full1`). SV-COMP's termination tasks: 181
(134, 47), 2477b4a and 0.22.0 47 (0, 47); per component 172 (125, 47), both 86 (39, 47); Ultimate Automizer 224. No
answer contradicts another tool's, a lasso, any other run's or an expected verdict (`runs/ranks/r4-its-merged`,
`r2-its-main`, `r2-its-base`, `r4-sv-merged`, `r2-sv-main`, `r2-sv-base`). Not answered here and answered by
2477b4a: 5 and 7 nonterminating ITS tasks (found there between 5.8 s and 55.3 s, 5 of the 12 past 40 s, by
searches bounded by time and random, where here the rank search has 70% of the time), and 1 and 2 lassos 0.22.0 found (the lasso stages are random and bounded
by time; 2477b4a missed 3 and 2 of 0.22.0's too). The second frontier corpus's rank, nonlinear-rank, sampling and
nested-recursion items: 11 of 15 proven, 0.22.0 0, every broken variant refused (`runs/ranks/c2-mine`, `c2-base`);
round 1's cycle items as before, 21 of 21, broken 21 of 21 (`runs/ranks/c1-mine`, `c1-base`). An independent check
(branch verify/ranks, research/verify-ranks) held every answer, and found two translator bugs that predate this
work, fixed here (below).

- Two translator fixes, each giving a wrong "terminates" on a small task: `compare/term/translate.ts` folded constants
  in doubles (3 · 3002399751580331 and 2^52 + 2^52 both 2^53), now in BigInt, a constant past 2^53 refusing the task;
  `compare/term/c2ari.py` read C's conversions as the identity (a char stored past 127, a cast to short, a _Bool set
  to 2), now refusing values narrower than int and casts that convert. No benchmark translation changed: all 1,239 ITS
  loops, all 282 SV-COMP ARI files and their 226 loops are the same before and after
  (`runs/ranks/translations-its.txt`, `translations-sv-c2ari.txt`, `translations-sv-loops.txt`). The check's
  adversarial programs are tests now (`compare/term/adversarial/`, `adversarial.test.ts`, `c2ari_test.py`; the suite's
  `term-adversarial` and `term-c2ari`): none that runs forever is answered terminating.
- The relation (`core/relation.ts`): one turn of a Loop as linear paths: `while`, the assumption and the laws in
  disjunctive form, each `if` decided by the values a path pins (pc = 3, t = 1) or split, each truncated difference
  split on its sign. Two naturals every row and value reads only as their difference, whose values after the turn are
  complementary differences (u := P ∸ N, w := N ∸ P), are one integer, u − w: no split, the rank over the integer.
  Each path's generators by double description, in integers.
- Ranks from it (`core/cycles.ts`'s `rankOfRelation`): each condition at every point of a path is rows over the rank's
  coefficients at the path's generators (Podelski–Rybalchenko with generators in place of Farkas' multipliers), solved
  by the exact LP over all the rows. Blocks in order (Bradley–Manna–Sipma), each strict on as many paths as one after
  another allows and kept by the rest, each a nested rank of depth 1 to 3 (Leike–Heizmann's; multiphase: y + 1 then x
  for x := x + y; y := y − 1), linear per location (the natural every path pins: the program counter), over the names
  live there. The location graph's components are ranked apart below their heights. A component with no rank is split
  by an atom its paths read, each side its own template (toy3's y ≥ 2). The kernel's terms: f + 1 truncated per block
  part, an if-chain over the locations.
- Invariants first (`rankWithInvariants`): per location, bounds at the paths' constants over the live names, then the
  paths' atoms too; those false at a sampled start dropped; Houdini over the relation (a path past the generators' cap
  checked atom by atom by the integer solver); the fewest the rank needs, each dropped in turn and the rest closed
  again; then laws (pc ≠ ℓ ∨ atom) the kernel proves inductive with the halting goals.
- `findRank`: the runs' rank first as before, its LP within 10% of the time and its check within 20%; then the
  relation's rank; degree 2 over the products the loop reads; the relation's rank with invariants; inferLaws as before.
  The DSL loops' ranks are the ones they were (`core/cycles.test.ts`), and a test of the relation's ranks on the corpus
  tasks with their broken variants refused.
- compare/term/solve.ts prints the answer once the kernel has checked the trees again, and again with the certificate
  once it is made (44 ITS proofs ran past the limit making a cyclic certificate, `not made`); the rank search has 70%
  of the time left after the first stages, the second recurrent-set search the rest.
- Groups (research/frontier2): ranks that read no parameter, ranks in order, ranks per location (Continue1, p-60,
  AckR, Alternate, toy3); multiphase (polyrank1, 2Nested-1); the sampling group (AProVEMath, ListReverseCyclicList,
  WhileFalse: no run needed); McCarthy91_Iteration with 4 invariants. Not proven: Piecewise (min(p, q): one atom's
  regions are not enough) and Toulouse-BranchesToLoop-2 (it needs x ≠ 0, a disjunction).
- On the tasks both answer alike, the times are 2477b4a's (ITS, the task's statement: median 0.15 s each); a
  terminating answer's rank comes at a median 9.4 s, p95 21.9 s, of which the first stages are 6 s.
- The suites (208 jobs: 2 new, `term-adversarial` 29.7 s and `term-c2ari` 1.7 s) on Modal: by default 592.7 s wall,
  4,832.1 s of job time, none failed (`runs/ranks/suite4-default`), main at c42ce7f the same day 567.2 s and 4,753.8 s
  (`suite3-main-default`; 4,800.7 s here on its 206 jobs, `cycles` the most, 71.5 s more); `--usual` 474.8 s and
  4,420.7 s, none failed (`suite4-usual`), main 513.2 s and 4,378.7 s (`suite3-main-usual`; 4,388.5 s on its 206). An
  earlier `--usual` run here failed `lean-nonterm` once (`suite3-usual`): one of core/conformance.ts's recurrent-set
  certificates, found within 300 ms of wall time and so different each run, on which kernel.ts and NonTerm.lean
  answered differently (its tree has a cut by a fractional coefficient); nothing of the nontermination check or the
  trusted base is changed here, and it passed in the two runs after (`suite4-default`, `suite4-usual`).

The language's edges: what an automatic prover can still say about values it may not look into and functions it isn't
given. TIP 2015 at 60 s on Modal: 181 of 492 proven, main (5c3f947) launched beside it 178, none wrong; 180 of the 181
with TIP's statement unchanged, against 136 of 178 (`runs/edges/tip`, `runs/edges/tip-base2`; `false/`: 23 refuted in
both, the same 30 refutations in all, each confirmed by TIP's evaluator, none proven). Nothing trusted changed
(`kernel/`, `core/check.ts`, `lean-kernel/`).

- **Abstract sorts** (`opaque('Elem')`, core/data.ts): values a law compares by equality and passes around, and nothing
  else; an ordinary datatype of one constructor of one natural, so the kernel and Lean's twin see what they see of any
  datatype, with a check at every `law` that refuses a match, a constructor, a test or a size of the sort in the law
  or any function it reaches (save the sort's own codecs, which only an unknown function's encoding reaches). Why a law
  proven so holds at every sort: a counterexample over any set S reads finitely many elements; sent injectively into
  the naturals (an injection exists because the naturals are infinite: a proof over a finite domain wouldn't carry),
  a program that reads elements only by equality, choices and moves computes the images, and an unknown function may
  take them too, so the law would fail at the naturals, where it is proven. An order, arithmetic, a constant of the
  sort or a match on its code would tell the encoding apart, and is what the check refuses. Lean's twin states the law
  about the inductive `Elem`, whose code no definition of the law reads: no arithmetic fact about the sort is in its
  statement. An abstract value is drawn at random as a natural is (the same draws), so refutations are the naturals'.
- **Unknown functions** (`unknownFn('f', [Elem], List)`): any function between sorts, from one unknown g of a natural
  read at keys of its arguments' injective codes paired (⟨x, y⟩ = (x + y)² + y, `pairing`, a function by recursion so
  the search keeps it whole); a natural, condition, integer or abstract result g at the key (of one natural argument,
  fnParam's f(x) and the predicate g(x) = 0 exactly); a datatype's value decoded at most g(⟨a, 0⟩) constructors deep,
  each node at its heap place p its constructor from g(⟨a, 3p + 1⟩), its naturals from g(⟨a, 3p + 2⟩). Every function
  is one of these (the points read are distinct for distinct arguments, places and reads, so some g reads any
  function's values), so the law about every g is the law about every function; it is all ordinary functions of the
  datatype language. An uninterpreted constant is an unknown function of no argument.
- **Closures** (`closures(name, args, ret, cases, {unknown})`): defunctionalisation as a datatype of the functions a field
  may hold, one constructor each with its captures as fields, and `apply`; with `unknown`, a constructor whose
  application is an unknown function, so a law about every closure is about every function too.
- **TIP** (compare/tip): a goal's sort variables and `declare-sort` are abstract sorts (`--naturals`, the instance at
  the naturals as before); `declare-const`/`declare-fun` unknowns (TIP's evaluator sees them in every body); a function
  variable of any sort but a function's or an integer's an unknown function. Newly translated 4, proven 3
  (`isaplanner/prop_46`, `tip2015/list_return_1`, `list_concat_map_bind`), `list_assoc` out of time; 4 more read past
  their sorts and constants to another refusal (`list_weird_*` 2 at weird_concat's termination, `list_elem`,
  `list_nat_elem` at an existential with no witness among their variables); outside, with the reason in
  compare/tip/README.md: `polyrec_seq_index` (a nested datatype: polymorphic recursion, no finite set of instances),
  `nicomachus_theorem` (a product of two integers, and over Int not a consequence of its definitions: `sum (−1)` is
  free). Lost 1 at the limit (`isaplanner/prop_51`, 57.4 s on main). Lambdas were already specialised at each closure
  (defunctionalisation resolved where applied); TIP stores no function in a field and returns none, so nothing more.
  Found and left: `list_assoc`'s lemma use is lost in a case node, ranked by all the cases' models
  (`research/edges/lemma-case.ts`, no unknown decoding needed to see it).
- Adversarial tests (core/abstract.test.ts 17, compare/tip/translate.test.ts 13, each refused or refuted, a TIP one
  confirmed by TIP's evaluator): an order of elements, a constant of the sort, its size, a function reading its code, a
  constructor test (refused); at most two elements, every element the default, two defaults one, an unknown function
  injective, an involution, constant, its lists of at most two items, `f x ++ f x = f x`, a predicate somewhere true,
  equal lengths making equal lists, two closures mixed up, every closure growing; in TIP, at most two elements at a
  sort variable, all of a declared sort equal, every element a constant, two constants equal, `undefined` every
  element, a `declare-fun` injective, `[x] >>= f = f x ++ f x`, two function variables equal, two lambdas and one lambda
  at two captures mixed up (refuted); a sort of arguments, a function variable of a function or over the integers
  (refused). And the decoding onto: a table that makes [3, 1, 4], read back.
- Lean: `research/edges/lean-edges.sh` (the suite's `lean-edges`) checks catAssoc, countCat, firstCons, bindReturn and
  mapLength of `examples/abstract.ts` again in Lean. Two shapes of the export's tactics aren't closed, neither new
  here (`PROBE=1` shows each with no abstract sort, unknown or closure): a datatype of two constructors with fields
  (`(2·x + 1) / 2 = x` left after simp: closures of two with captures) and two constructor values compared inside a
  disjunction (a membership by equality). Both are in `lean-kernel/data.ts`; the kernel's proofs stand.
- Corpora: the first's datatype track 23 of 25, its 18 broken variants refused, as main; the second's TIP items
  frontier 2 of 15, every broken variant refused, as main (`runs/edges/corpus-r1`, `-r2`, beside `corpus-base-*`). The
  suite on Modal: by default 208 jobs, 0 failed, 492.5 s wall, 4,896.1 s of job time (`runs/edges/suite-default`);
  `--usual` 208 jobs, 0 failed, 546.7 s and 4,698.7 s (`runs/edges/suite-usual`).
- The `data` job on 1 vCPU (ten each, this branch's and main's interleaved in one Modal batch, `runs/edges/data-1cpu`):
  nearPlus min, median and max 2,486, 2,957 and 3,931 ms against main's 2,247, 2,799 and 3,980; nearSucc 1,918, 2,323
  and 2,664 against 1,757, 2,187 and 2,901; none failed.
- Sizes: core/data.ts +153 (97 code, 56 comment), compare/tip/translate.ts +116 −33, tip.ts +15 −5, solve.ts +14 −11;
  new: core/abstract.test.ts 64, compare/tip/translate.test.ts 64, examples/abstract.ts 86, research/edges/ 76.
- Cost: Modal $3.76188 for this track's 12 apps today (`modal billing report --for today`, before the day closes);
  no boat.

Rules over the rationals: `ratRule` (`gdp-wired/rationals`) with params, inputs and state of kind `rat` or `nonneg`,
each value an exact rational (0.1 is 1/10, a third is 1/3; nothing scaled or encoded as naturals), terms linear (+,
−, × and ÷ by a constant, min, max, when). Linear arithmetic over ℚ is decidable: a law is proven by trees whose
leaves are Farkas certificates with strict rows, or refuted by an exact run from the start. A fee split, a rate
limiter with fractional tokens and a ledger in decimals proven, each broken twin refuted with its run; 12 laws true
over one of ℕ and ℚ and false over the other (5 true over ℚ only: halving keeps a positive amount positive, s ∸ c + c
is s, ...; 7 over ℕ only: x < y gives x + 1 ≤ y, 2s ≠ 1, a difference is never negative, ...), 12 of 12 decided both
ways (`examples/rationals.ts`, the suite's `rationals`). Nothing existing changes: every Lean export of the examples
(21 domains, key names renumbered in order), the package check's Proofs.lean (4 shards), the sets export and the
600-case conformance file are the same as 5c3f947's (`runs/reals/exports`, `runs/reals/exports2`), and again
after check.ts's integral mode was made Cert.lean's check exactly, with the conformance and tamper jobs passing
(`runs/reals/recheck`).

**The trusted base grows.** `lean-kernel/Rationals.lean` (new, on top of `Kernel.lean`, 946 lines) and its twins,
`kernel/kernel.ts`'s rational section (185 lines, 162 of code) and `core/check.ts` (23 lines in, 10 out):
- Cert's rows read at a rational point, each strict or not. `Q.checkQ` replays Cert's steps with no cut, a
  combination strict when either row is, and accepts a last row of zero coefficients with a constant > 0, or ≥ 0 and
  strict. `Q.checkQ_sound`: no rational point satisfies the rows. The naturals' and integers' check is the same
  replay with the cut, the one step whose soundness needs an integer point (Cert's `cut_sound`): check.ts's
  `checkRefutation(rows, steps, integral)` is both: `integral` false, no cut, strict rows, every coefficient a safe
  integer; by default exactly Cert.lean's check, no row strict, as before.
- Terms over ℚ (`QE`: variables, rational constants, +, − not truncated, × by a rational constant, min, max, if;
  `QC`: ≤, <, =, and, or, not). A term's linear form is a row over a positive denominator, a comparison's row a
  positive multiple of a − b; a split's no side is −l < 0; a leaf claims rows found among its own. `Q.sound`: an
  accepted goal's hypotheses hold together at no `Nat → Rat` environment. `Q.machine_sound`: the induction rule for
  step machines over ℚ, as Kernel.lean's scalar machines. All three on `propext`, `Classical.choice`, `Quot.sound`.
- kernel.ts mirrors each definition (`qlinear`, `qtruth`, `qfacts`, `qLeafRows`, `checkQTree`, `qObligations`,
  `checkQMachine`), forms in bigint. Lean's `evalE`, `evalC` and `checkGoal` compute kernel.ts's answers on 2,931
  cases (`lean-kernel/conformance.ts --rationals 150`, the suite's `lean-rationals`): 150 terms' values and truths,
  300 proven goals, 300 models, and 2,031 tampered trees, each refused by both (a multiplier negated or 0, a cut, an
  input out of range, a combination of itself) or by Lean alone (a claimed row's coefficient sign flipped, a row not
  among the leaf's, a row claimed strict that isn't). core/conformance.test.ts over its 8 seeds: 4,800 goals proven
  and checked, 4,800 models confirmed by the exact evaluator, 20,214 tampered trees refused (`runs/reals/suite-default`).

One linear-arithmetic core: `core/solver.ts`'s elimination takes `integral` false (no cut, strict rows, an exact
witness), the incremental simplex (`kernel/simplex.ts`) too (no rounding, strict bounds moved in by 1e-7), and both
are what `growQ` (`kernel/qprove.ts`, untrusted) uses: the kernel's rows at each node, the simplex's conflict refuted
exactly, else a split on an open atom, complete for linear arithmetic over ℚ. The runtimes compute over bigint
fractions (`interpretQ`, `loadQJs`); `refuteQ` decides the machine unrolled up to 3 requests over ℚ and replays the
model; `rationalsToLean` (`gdp-wired/lean`) exports through `Q.machine_sound` (the examples' 20 theorems, the suite's
`lean-rationals`). Outside: products of unknowns (refused) and transcendental functions; a rule is all rationals or
all naturals (integrality mixed with rationals is mixed-integer arithmetic, which a cut-free certificate doesn't
refute).

The suites on Modal beside 5c3f947, run side by side: by default 208 jobs, none failed, 735.5 s wall, 5,003.5 s of job
time (`runs/reals/suite-default`), 5c3f947's 206 jobs 581.8 s and 4,770.2 s, 6 of them failing for want of
vendor/handwired in its checkout, each passing once it was copied in (`suite-base-default`, `suite-base-default-6`);
over the 200 jobs both passed, 4,754.5 s against 4,745.6 s. `--usual`: 208 jobs, 532.0 s wall, 4,354.3 s, `check`
failing on a copy of the base tree left in the worktree and passing alone (`suite-usual`, `suite-usual-check`);
5c3f947's 1,134.6 s and 4,963.5 s, its `pairs` timing out once (843 s) and passing alone; over the 204 jobs both
passed, 4,180.6 s against 4,079.8 s. Fuzz shards summed 905.4 s against 803.4 s there, so the fuzz was run again
interleaved on 1 vCPU, 8 runs a seed each (`runs/reals/fuzzcmp`): seed 1 median 25.18 s against 26.26 s, seed 12345
27.74 s against 30.05 s. The `infer` and `data` tests on bun's 5 s limit, on 1 vCPU, 5 jobs each side interleaved
(`runs/reals/onecpu`): the slowest, data's "agrees with + on small values only", 3,613 ms at most against 5c3f947's
6,606 ms (one base job timed out there); infer's slowest 2,877 ms against 4,318 ms; none failed on this branch.

Derivations of false found together (core/bmc.ts, bounded runs). CHC-COMP LIA-Lin at 60 s on Modal: 264 unsat and 518
sat (782 solved), main the same day 144 and 528 (672), none wrong either way, no unsat answer but a derivation
`checkDerivation` confirmed (`runs/unsat/chc`, `runs/unsat/chc-base`; four runs of main that day gave 528 to 533 sat).
Lustre's 321 unsat tasks: 38 to 147. Nothing trusted changed. The second frontier corpus: derivation 2 of 3 (main 0),
frontier 16 of 47 (main 14), every broken variant refused in both (`runs/unsat/corpus2-final`, `corpus2-base`);
durationThm_1_e1_197 by the deeper depths after the invariant search (5.3 s), O0_terminator_01 by the shallow ones
(0.4 s). The suites pass by default and with `--usual` (`runs/unsat/suite-default3`: lean-nonterm failed once, its
generator's wall-timed search making a 127th case; 3 runs again pass, `runs/unsat/nonterm-recheck`; `suite-usual`).

- A run of k steps from the start that breaks a law, as a model of the kernel's own k-step goal (kernel.ts's
  `stepLawObligations`) with its start constants folded in (core/nonterm.ts's folding, now shared); the run then taken
  by the interpreter, and kept only where it breaks a law. compare/chc/solve.ts's `bmc` stage (10 s, after the guided
  runs) and proveRule's search (its shallow depths first, within 250 ms; the deeper ones where the invariant search
  finds nothing, within a tenth of the budget kept from it). proveRule now searches on from a wide rule's random
  counterexample to induction (a state, not a run), as from the kernel's.
- kernel/cdcl.ts asked for a model alone (`model`): a refutation isn't unfolded into a tree, and each decision's phase is
  the incremental simplex's point's (kernel/simplex.ts `holds`): 320 of the 475 unsat tasks by the stage alone, 280
  with the phases as stored (`runs/unsat/bmc-only-phase`, `bmc-only-off`). Off by default: research/dag's 332 step
  goals all proven with the same leaves, by `growCdcl` and by `grow`, as at main (`runs/unsat/goals332-*`).
- Measured and left out: runs of at most k steps (2 more, `bmc-only-upto1`); a second process for the stage (539 of
  1,406 containers failed, `chc-p1`); longer budgets (15 s: 292 unsat, 508 sat; 20 s: 303 and 497; beside main's 144
  and 528, `chc-b15000`, `chc-b20000`); k-induction (`compare/chc/prof/kind.ts`: 17 of the 403 sat tasks main leaves
  are k-inductive, which the kernel's 1-inductive proofs don't check; `runs/unsat/kind1`). compare/chc/README.md has
  each run.

Lemmas the datatype search finds and uses. TIP 2015 at 60 s on Modal: 176 of 492 proven, 0.22.0 the same day 140, none
wrong (`runs/lem/tip-final`, `runs/lem/tip-final-base`; `false/`: 23 refuted in both, each confirmed by TIP's
evaluator, none proven). Nothing trusted changed (`kernel/`, `core/check.ts` and `lean-kernel/` are as in 0.22.0). The
second frontier corpus's TIP items: frontier 2 of 15, 0.22.0 1 that day, every broken variant refused in both
(`runs/lem/corpus2-tip-final`, `corpus2-tip-final-base`). The suite on Modal beside 0.22.0's: by default 455.2 s wall,
4,501.7 s of job time, none failed, 0.22.0 506.4 s and 4,328.8 s (`runs/lem/suite-default`, `suite-base-default`);
`--usual` 537.6 s and 4,217.3 s, none failed, 0.22.0 487.3 s and 4,047.7 s (`runs/lem/suite-usual`,
`suite-base-usual`). The first frontier corpus's datatype track scores as at 0.22.0 in both modes.

- Terms by their structure (core/data.ts's `sid`): a key's pairing reads its arguments again, so a nested read's text
  grows exponentially with its depth; the search keyed terms by that text. Ids over shared objects, a substitution that
  keeps them shared, and traversals that visit an object once are linear in the objects. TIP's timeouts at 0.22.0's
  proofs: 165 to 146 (`runs/datafix/tip`, `runs/lem/tip-perf1`).
- Bridges (core/transfer.ts): a well-founded function of naturals that computes a sum Σ cᵢ·xᵢ + c₀ of up to four of them
  (add3, add3acc: x + y + z) is bridged like +, its bridge proven by its own recursion; and a node read through the
  bridges takes the program's widest measure in its rank (the kernel refuses ranks of two lengths, so a law through a
  well-founded function's proof was never read back). 30 of the 37 gains: add3 and add3acc 9 each, mul2, mul3 and
  mul3acc 11 through copies over them, op 1.
- Conjectures: told apart also on 40 values that fill their size (where three butlasts of anything are empty on the
  short ones); an equation reading a variable twice generalised apart (`(xs ++ xs) ++ ys = xs ++ (xs ++ ys)` is ++'s
  associativity over three lists; prod/prop_34 from `mult x y z = x·y + z`); a predicate kept over either variable of
  a sort (`elem x z ⇒ elem x (union y z)`).
- Lemma uses through other uses' conclusions (two lemmas chained by rewriting); arguments equal by arithmetic one
  class (`(n + 1) ∸ 1` and n: isaplanner/prop_13 and prop_42, a definition on the naturals unfolded at n + 1).
- The order of the search: the law at two unfoldings before any conjecture (isaplanner/prop_59, 63, 64, 67); the
  lemmas the goal reads within 30% of the time left, the law again after each, without induction first; the law alone
  with more time; the other lemmas; an attempt that failed within its time not repeated, and passes bounded by number.
  Diagnostic: with no conjectures at all, 39 of the 216 unproven at `tip-perf1` (`runs/lem/nolem1`).
- Tried and left out: decreases proven with lemmas (a size bound on another function, the toList and pairwise passes'
  91 refusals): 20 more TIP problems translated and all 20 out of time, none proven (`runs/lem/tip-v3`); lemmas ranked
  bottom up, and the law tried by its schemes only after every third lemma: more TIP (180, `runs/lem/tip`) and the
  suite's search tree insertion at 194.8 s against 20.4 s, the datatype corpus's reverseReverse at 72.6 s against
  22.3 s (`runs/lem/suite-default-1`, `suite-default-2`, beside their bases). compare/tip/README.md has each step's run.
- The `data` job: data.test.ts 14.55 s by default and 12.73 s `--usual` against 8.25 s and 8.07 s (two tests added, a
  linear bridge and a generalisation), the limited tests under their 5 s (nearPlus 3,121.95 ms, nearSucc 2,393.35 ms
  by default); on one machine the examples took 67.5 s and 68.5 s against 56.6 s and 63.1 s, data.test.ts 4.6 s against
  3.6 s (`runs/lem/local-data`). The time is attempts' instances, which aren't counted work: the searches stop at the
  same counted budget, and the new conjectures' attempts take more of the wall. On 1 vCPU (ten `data` jobs each, this
  branch's and main's at dd36f67 interleaved in one Modal batch, `runs/lem/data-1cpu`): nearPlus min, median and max
  1,751, 2,756 and 3,439 ms against main's 1,812, 2,508 and 2,811; nearSucc 1,512, 2,178 and 2,462 against 1,142, 1,555
  and 1,783; none failed; the job 180.8 s median against 153.5 s.
- `compare/tip/solve.ts --opts '<json>'`: proveData's options, for diagnostics.

A run that never ends, stated and proven: `proveNeverEnds(loop)` claims that some run of a loop goes on forever (the
claim a halting proof refutes), with a closed recurrent set as its certificate, checked by the kernel and again by Lean.
TermComp's ITS at 60 s on Modal, `gdp` alone: 450 nonterminating and 56 terminating, 0.22.0 the same day 320 and 56
(`runs/nonterm/after2-its`, `runs/nonterm/base-its`); no answer contradicts another tool's or the other run's. SV-COMP
unchanged (47 nonterminating, none wrong). The suites on Modal: by default 206 jobs, 0 failed, 519.9 s wall, 4,600.0 s
of job time (`runs/nonterm/suite-default`), 0.22.0's 204 jobs 490.4 s and 4,786.0 s (`runs/nonterm/base-suite-default`);
`--usual` 206 jobs, 0 failed, 504.2 s and 4,297.4 s (`runs/nonterm/suite-usual`), 0.22.0 469.5 s and 4,255.8 s
(`runs/nonterm/base-suite-usual`). boat had no starts to spare, so these ran on Modal; 0.22.0's release suites on boat
are `runs/release/0.22.0-*`.

**The trusted base grows.** `lean-kernel/NonTerm.lean` (new, on top of `Live.lean`, 275 lines) and its twin in
`kernel/kernel.ts` (`checkRecur`, `recurGoal`: 73 lines, 56 of code):
- `Kern.NeverEnds l`: for some maps and some params meeting the precondition, a run of turns from the start that goes
  on forever, the negation of `loop_halts_of`'s conclusion.
- The certificate (`Recur`): a condition over the state and params (the set), a term per input over the state and
  params (the turn taken from each of its states), the params as values and a stem of turns' inputs from the start into
  the set, each state on the way held as its values on a domain. `checkRecur` evaluates the start and the stem exactly
  and refutes the closure goal (a state of the set whose witnessed turn fails the guard or the assumption, or ends
  outside the set) with the kernel's tree. The run after the stem is the witnessed turn again and again, built by
  recursion: no choice.
- `Kern.never_ends_of`: a checked certificate gives `NeverEnds l` (`propext`, `Classical.choice`, `Quot.sound`, through
  the leaf check's `sound`). `Kern.halts_not_never_ends` (no axioms) and `Kern.never_ends_refutes_halts`: no loop both
  halts and has a run that never ends.
- kernel.ts's checker mirrors Lean's: Lean's `checkRecur` computes kernel.ts's answer on 127 certificates, found,
  tampered and forged (`lean-kernel/conformance.ts --nonterm`, the suite's `lean-nonterm`).

- **The search** (`core/nonterm.ts`, untrusted): lassos of random runs (the set the cycle's states, each turn's inputs
  given at its state); policies, runs whose inputs are terms over the state (by mode, the first allowed of a few
  assignments from pools of constants and values ± 1, grown where the run would stop); a recurrent set fitted to a
  policy's run (bounds, sums and differences of the integer values, one atom per counterexample the prover gives), its
  closure proven by `grow`, which tries kernel/cdcl.ts's CDCL first.
- **The API and the export:** `proveNeverEnds(loop, {from?, ms?})` (dsl); toLean's `{id, neverEnds, recur, tampered?}`
  as `<id>_never_ends : NeverEnds <id>_loop` by `never_ends_of`, each tampered certificate's check computed to false;
  `examples/nonterm.ts`, three loops that never end (pagination with empty pages, a retry with no cap, a ring reader)
  beside twins that halt; the package check builds all three in Lean.
- **Tests:** core/conformance.test.ts: every certificate the checker accepts holds on the reference run; the found ones
  accepted; tampered ones refused (the set not closed, not reached by its stem or start, a lasso's cycle that doesn't
  close) and no tree closes a changed set. core/nonterm.test.ts: no loop proven both to halt and to have a run that
  never ends, on 10 loops and 6 ITS tasks (3 and their terminating twins).
- **Termination benchmark** (compare/term/solve.ts: a recurrent set for 4 s after the first lassos, and with 3/5 of
  what is left after the rank search). ITS: 133 tasks answered that 0.22.0 left (131 unknown, 2 timeouts), 3 answered
  by 0.22.0's lasso not (timing of the lasso stage); the 56 terminating the same tasks. Of the 133, 105 are LoAT's NO
  too, 24 are lassos replayed by ari.ts's evaluator, 2 had a replayed lasso in an earlier run (db2, db3) and 2 no other
  tool answers (Velroyen08-fib, NonPeriodicNonterm2, read by hand). None is a task LoAT, LoAT abmc or KoAT2 proves
  terminating. Lean checks every recurrent set of the run, 131 of 131, as `NeverEnds <task>_loop` on `propext`,
  `Classical.choice`, `Quot.sound` (compare/term/recur-lean.ts, 32 shards, at most 1,865.9 s a shard on Modal, 4 CPUs:
  `runs/nonterm/after2-lean`).
- **The second frontier corpus:** nontermination was a language gap; five items now (`research/frontier2/nonterm.ts`:
  toy2, toy4, Choose, NO_10, EvenOdd, each LoAT NO with no lasso at 0.21.0), each with its terminating twin (KoAT2
  Finite, `runs/corpus2/truth-nonterm`): today (lassos only) 0 / 5, frontier 5 / 5, twins refused 5 / 5
  (`runs/corpus2/nonterm-items2`).
- Cost: boat $0.905 (the Lean rechecks $0.66 and $0.24, the corpus $0.005, a probe $0.001); Modal 206,125 s of job
  time over the benchmark runs, the suites and the truth checks, plus the Lean recheck's 12,817.7 s (and a first one stopped for the machine going offline), the day's dollars
  not yet in Modal's billing report.

Invariants from the samples' hull, made inductive (`core/infer.ts`, the join): per control state, the affine hull of
the states the runs reached and each direction's largest value there, then Houdini on the cone of the caller's laws by
relative induction, the kernel's models as counterexamples. Nothing trusted changed (`kernel/kernel.ts`,
`kernel/cyclic.ts`, `core/check.ts` and `lean-kernel/` are as in 0.22.0). CHC-COMP LIA-Lin at 60 s, gdp alone, this
branch and 0.22.0 (c215ded) one after the other on Modal: 670 solved (526 sat, 144 unsat) against 510 (366, 144), none
wrong either (`runs/inv/chc`, `runs/inv/chc-base`); 166 only this branch solved, 6 only 0.22.0 (five Lustre tasks and
llreve's break_safe.c-1, which 0.22.0 solved in 26.39 to 38.9 s and this branch leaves unknown at the limit). The
second frontier corpus, 8 of 42 against 3 of 42, every broken variant refused in both (`runs/inv/corpus2-after`,
`runs/inv/corpus2-before`, Modal).

- The join, where the old search would begin choosing candidates: the control state is the choice (loc) and, where
  the reached choices times their valuations are at most 128, the yes/nos (a program counter in bits: per pc its own
  hull, a pc no run reached a clause `never …`). Per control state: the hull's equalities (exact, over ℤ: a point
  joined in removes the dimensions it leaves; at most 4 values, coefficients up to 1,000, as laws) and each direction's
  largest value (each value up and down, pairs of them where there are at most 10 values, and the rule's own
  comparisons over the state, a request's value read as the state it makes).
- Houdini on the cone, not the whole set: the caller's laws first, then each form their trees read (`usedHyps`). Each
  goal is proven with as little of the set assumed as will do: none, then the forms that rule out the kernel's model
  (those of the cone first), two at a time, as IC3's relative induction, then the whole set. A model the whole set
  allows is a counterexample to induction: its successor, and those of short walks from it, are joined in (the hull
  grows; a bound rises to the next of the rule's constants and their sums, then to a constant, then goes). A model that
  breaks a caller's law adds a candidate of the old search's that rules it out. The cone proven, it is the answer, and
  the old search proves it as a set as before. Unproven within 60 % of the budget, the old search runs as it did,
  from the same candidates and counterexamples.
- Kernel searches counted in its work unless the search is timed, so a counted search finds the same on any machine.
  `GDP_JOIN=0` turns the join off.
- By CHC group (research/frontier2's, the tasks left at 0.21.0), 0.22.0 against this branch: A 113 → 165 of 195,
  B 7 → 30 of 39, G 1 → 9 of 15, C 0 → 10 of 38, D 1 → 9 of 113, E 3 → 28 of 71, F 1 → 7 of 34, H and I 1 and 1 as
  before; outside the groups 381 → 408 of 581. Where the join ended in a proof (502 tasks, at an earlier commit,
  `runs/inv/chc-join4`) it took a median 0.967 s, p90 6.174 s.
- The second corpus's new items: FIREFLY_1 (`1 <= b13`) and MESI_i3_e1_447_e3_1180 (`1 <= b8`, `i6 <= 0`, `0 <= i4`),
  simple.c (per pc in bits), three_dots_moving_2 (`i1 + i2 <= 2·i0 + i3` among three, from the start clause's
  comparison) and loop2 (equalities over four values); reve 015 and break_safe.c-1 as before.
- Measured and left out, each no gain on the same tasks (`runs/inv/dev80-*`, 79 tasks, Modal): candidates tried as IC3
  would before one is added, and a counterexample to a cone form ruled out before it is joined (675 against 670 on all
  1,406, `runs/inv/chc-join4`, `chc-join6`); IC3's lemma from a counterexample's cube (68, 68 and 67 of 79); a request
  the assumption refuses mended by local search, as WalkSAT does (67 against 67); the join at 0.35 of the budget
  (662 against 670, `runs/inv/chc-join5`).
- `examples/infer.ts`: three accounts and moves between them, one account within the total paid in, which needs
  `a + b + c <= total` (the old search's forms of three values don't hold it); a test in `core/infer.test.ts`.
- The suite (204 jobs) on Modal, 0.22.0 and this branch one after the other, as boat had no starts left: by default
  0.22.0 491.5 s wall and 4,796.4 s of job time, this branch 480.1 s and 4,604.1 s, none failed (`runs/inv/suite-base`,
  `runs/inv/suite`; a first run failed the new test on bun's 5 s limit for a test, now 60 s as the other searches'
  tests have, `runs/inv/suite-try1`); `--usual` 482.5 s and 4,351.6 s against 444.9 s and 4,237.4 s, none failed
  (`runs/inv/suite-base-usual`, `runs/inv/suite-usual`). The release's boat runs, for scale: 307.8 s and 3,073.9 s,
  `--usual` 264.7 s and 2,418.3 s (`runs/release/0.22.0-default`, `-usual`). The first frontier corpus 90 of 92, its 42
  broken variants refused, in all three.
- Sizes: `core/infer.ts` 681 → 987 lines (+313, −7), `core/infer.test.ts` +10 −1, `examples/infer.ts` +16 −1,
  `research/inv/one.ts` +11 (inferLaws on one CHC task as the corpus runs it).
- Cost: Modal $22.60314 for this track's 29 apps today (`modal billing report --for today`, today's figures before the
  day closes); boat $0.01892 (the runner's lines, four batches).

Infrastructure (nothing in the library changed): the boat backend paces its VM starts.

- boat is the main compute (`--backend auto`, the default) while its plan lasts; when boat can't start VMs (no plan, no starts, billing blocked) `auto` sends the batch to Modal, so Modal becomes the default without a change.

- boat's starts are spent by plan (a resume is a start; `boat limits` is read at every batch, so a new plan takes
  effect on the next one). A batch starts at most a quarter of the starts left this hour and day and at most 50
  (`GDPW_BOAT_MAX_STARTS`, `--max-vms` for a run); the last 60 starts of the rolling day and 15 of the hour are left
  to the account's other users (`GDPW_BOAT_RESERVE_DAY`, `GDPW_BOAT_RESERVE_HOUR`); a stopped VM is resumed only while
  the batch needs it; VMs other batches release join a batch with more work than slots; with no start left, `auto`
  waits within `--max-wait` for one, then goes to Modal. A released VM stays up 60 s and never longer to save starts
  (boat's terms, TOS-6). `GDPW_BOAT_POLICY=old` runs the policy before.
  - On the $500 plan, CHC (gdp, 1,406 tasks): the old policy 211 starts, 563.7 s, $0.9588 (`runs/starts/chc-old`);
    cap 50, 47 starts, 725.1 s, $0.33333 (`runs/starts/chc-c985479`); cap 30, 30 starts, 1,116.4 s, $0.32189
    (`runs/starts/chc-new`); Modal 330.1 s (`runs/modal/arith/chc-gdp`). TIP: 27 starts, 542.3 s (`runs/starts/tip-new`);
    the suite: 1 start and 4 VMs up, 429.4 s (`runs/starts/suite-new`). No verdict contradicts the old policy's
    (`research/boat-starts/measured/verdicts.txt`).
  - Today's batches replayed (`research/boat-starts/sim.py`): the old sizing would have needed 5,260 starts to keep
    them all on boat; on the $100 plan it got 830 and sent 14 batches to Modal; the new defaults take 598, sending none
    (`sim.txt`).
- Fixed: a pool VM boat can't stop and whose disk is gone (it answers no exec and stays up, billed) is deleted, where a
  batch took it as up and waited for it; a job needing a VM type none of which came goes to Modal after `--max-wait`
  instead of holding the batch; a released VM's lease is cleared only by the batch that holds it; `reap.sh` stops a
  free VM only past the idle time its batch gave it.

- The real-world corpus (`research/realworld/`): 51 items of open-source code (rate limiters, quotas, ledgers,
  escrow, payments, sessions and OAuth, RBAC and Cedar policies, real XState machines, job queues, circuit breakers,
  feature flags, inventory, approvals; MIT, Apache-2.0, BSD and ISC, each pinned to a commit) written as rules with 311
  laws a reviewer would ask about, each proven with nothing stated (60 s of search a law, 311 jobs on Modal,
  `runs/realworld/r1`, the table in `results.md`): 218 proven (70.1%; 77.3% of the 282 believed true), 15 refuted,
  78 open, none wrong; liveness 0 of 35, of which `rank0.ts` proves 19 once the constant rank 0 is stated (the rank
  search misses it). Every refutation is a suspected real bug in the original code (20 in all with the ones found
  past the prover, each with a repro under `repro/`; none reported upstream). The language gaps, ranked by items:
  async 19, float 16, ordered scans of a collection 8, nonlinear 7, statechart constructs `fromXState` refuses 6
  (every real machine as shipped; it also drops v4 `cond` without a refusal). `sources.json` lists the pinned sources
  for gen/extract.

## 0.22.0

The step goals of wide transitions proven: a CDCL search over a goal's atoms, with short reasons and an incremental
simplex, whose refutation is unfolded into the tree the kernel already checks. Nothing trusted changed
(`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts` and `lean-kernel/` are as in 0.21.0). research/dag's 332 CHC
step goals: 332 proven, 43 at 0.21.0 (`runs/step/grow7`, `runs/step/base-goals332`). CHC-COMP LIA-Lin at 60 s on
Modal: 518 solved, 0.21.0 the same day 381, none wrong (`runs/step/chc3-modal`, `runs/step/chc-base-modal`). Loops and
liveness get their cyclic certificate by translation: 4 proofs left on the usual rule in the suite, 119 at 0.21.0
(`runs/live/suite`). The second frontier corpus, 42 benchmark tasks and their broken variants, scored at 0.21.0: 3 of
42 (`runs/corpus2/baseline-0.21.0`). The release suites (204 jobs, one after the other) on boat.dev VMs, 2 vCPU and
4 GB a job: by default 307.8 s wall, 3,073.9 s of job time, none failed (`runs/release/0.22.0-default`); `--usual`
264.7 s, 2,418.3 s, none failed (`runs/release/0.22.0-usual`).

The step goals of wide transitions, which the tree search left undecided, are proven by a second search: CDCL over a
goal's atoms (`kernel/cdcl.ts`), its refutation unfolded into the kernel's own tree. Nothing trusted changed
(`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts` and `lean-kernel/` are as in 0.21.0): the certificate is the
tree kernel.ts already checks, so no DAG certificate was needed. research/dag's 332 CHC step goals (287 Lustre), each
alone with its own budget (a second a hypothesis, at least 20 s, within 55 s): 332 proven, 43 at 0.21.0 (Lustre 287
and 10); search median 1,044.5 ms (p90 3,538 ms) where 0.21.0's 43 took 12,108 ms; certificates median 83 leaves, on
the 43 both prove 97 against 394; none rejected by the kernel (`runs/step/grow7`, `runs/step/base-goals332`).
research/table's step goals (its 223 tasks run again with `--kernel`, the kept relations saved: 221 got a model and 197
of them stop on a step goal, `runs/step/table`): 194 proven and 3 satisfiable, 34 and 3 at 0.21.0; median 835.5 ms
against 13,337 ms, leaves median 54 against 432 (`runs/step/grow7t`, `runs/step/base-goals223`). Given each kept model
whole (compare/chc/prof/given.ts, 55 s): 181 of the 221 proven, 14 at 0.21.0, the rest a witness for an existential
not found (31) or the 55 s spent (9) (`runs/step/given7`, `runs/step/base-given223`). CHC-COMP LIA-Lin at 60 s on
Modal: 518 solved (374 sat, 144 unsat), 0.21.0 the same day 381 (237, 144), none wrong (`runs/step/chc3-modal`,
`runs/step/chc-base-modal`; on boat 0.21.0 solved 385, `runs/step/chc-base`, and this branch's boat run was stopped
unfinished when boat had no VM starts left). The suite (204 jobs: 4 new) on boat.dev VMs: by default 312.9 s wall, 2,887.4 s of job
time, none failed (`runs/step/suite-final`), 0.21.0's 200 jobs 328.8 s and 2,776.9 s (2,871.3 s now on those 200,
`runs/step/suite-base-boat`); `--usual` 207.3 s and 2,550.8 s, none failed (`runs/step/suite-final-usual`), 0.21.0
296.7 s and 2,377.2 s (2,531.8 s now on its 200, `runs/step/suite-base-usual`).

- Shorter cores (`kernel/reader.ts`): a refuted node's clause is the decisions the rows its derivation reads need, each
  row with its reason: a conjunction false needs one false part, a disjunction's last open part needs the others
  false, a term's value the decisions its choices took (not every decision its hypothesis' facts read, research/dag's
  cores). The same search with research/dag's cores proves 69 of the 332 (`runs/step/cdcl1full`), with the reasons 329
  (`runs/step/cdcl1`): a clause has 11.1 decisions on average where the trail has 59.5.
- Cheaper nodes (`kernel/simplex.ts`): each node's rows go to a floating-point simplex in general form whose tableau
  is kept from node to node; an infeasible row's bounds are refuted exactly (core/solver.ts), and the elimination runs
  only where no case is left open. 329 again at median 2,826 ms against 4,600 ms (`runs/step/cdcl2`); the tableau begun
  again once it fills past 8 entries a row the node reads: on `DRAGON_11` 11,681 ms and proven, where the filled tableau
  (27,464 entries in 438 rows) spent 49,366 ms of 60,140 in pivots and ran out (`runs/step/prof7`). `kernel/reader.ts`
  reads the rows again only where the trail changed what they read (a value with no open read kept while the trail
  keeps its reason): 332 of 332 by the search alone, median 1,619.5 ms (`runs/step/cdcl6`).
- The refutation is a resolution DAG of those clauses, unfolded into a tree (a resolution on an atom the path leaves
  open is a split; a leaf's derivation found again among the rows at its tree path, in kernel.ts's order, or those rows
  refuted afresh): on the 332, 50,353 leaves in all, median 83, max 3,043 (`runs/step/grow7`).
- `growRoot`: the quick search at 16 nodes, then CDCL with 3/4 of what is left, then the plain search, the cuts and
  the plain search as before. Not for a law over k steps in a row (the cuts make its tree a chain of one step's
  refutations, which the unfolded DAG repeats: examples/steps.ts's Lean text 1,306,965 bytes against 276,111 and its
  Lean check 152.24 s against 32.8 s with it, `runs/step/ksteps1`; identical without, `runs/step/ksteps2`), nor for
  products, nor inside a cyclic proof's search. The quick search's cap: 64 nodes give 170 of the 221 rules, 16 give 179
  and 4 give 181 (`runs/step/given6`, `given6q16`, `given6q4`), the suite's job time over 0.21.0's 200 jobs 2,921.0 s (an
  earlier commit of this branch), 2,866.4 s and 3,252.9 s (`runs/step/suite3`, `suite-q16`, `suite-q4`).
- Tests: `kernel/cdcl.test.ts` (four suite shards) refutes random linear goals larger than kernel.test.ts's, checks every
  tree with kernel.ts, finds no model of a refuted goal by brute force, agrees with the plain search on what is
  satisfiable, and with `GDP_CDCL_VERIFY=1` compares reader.ts's rows with kernel.ts's at every node and unfolded leaf.
  research/step: the runs (`modal_step.py`, `jobs.py`, `goal.ts`, `tally.py`, `suite-times.py`).

Claims about runs that never end get their cyclic certificate: a loop's halting and a liveness, each from the cyclic
proof of its step laws, nothing trusted changed (kernel/kernel.ts, kernel/cyclic.ts, core/check.ts, lean-kernel/ as in
0.21.0). Left on the usual rule in the whole suite (200 jobs, `runs/live/suite`, and again `runs/live/suite2`): 4
proofs, the four laws reading a map at a key read from a map; 119 at 0.21.0 (loops 79, liveness 36, those four;
`runs/release/0.21.0-default`). Then a line was printed for every claim tried, broken variants and claims refused
before their proof among them; now one for each claim proven: 36 loops and 22 liveness claims, every one with its
cyclic certificate.

- The rule was already there: Lean's `cyclic_sound`, through BridgeRules.lean's `cyc_kstep_sound`, gives a step law's
  meaning (`SKStepHolds`), and `sleads_of_holds` reads a liveness from its step laws' meaning (Live.lean's
  `leads_of_lex`: the rank can't drop forever, the region stays once it stops, its request comes), as `sleads_sound`
  reads it from their usual trees; `loop_halts_of` reads a loop's halting from either. One statement under both
  certificates, and the cyclic Lean export already took that route (lean-kernel/emit.ts's `cycMachineToLean`). What
  was missing was the TypeScript side.
- A liveness (kernel/prove.ts's `proveLiveness`): its certificate is its parts', the step laws' cyclic proof (stay,
  cover, one per helpful request, translated as any machine's) and each helpful request's allowed node; covered
  exactly where every part is (`cyclic: {kind: 'liveness', ..., route: 'its step laws'}`), else counted uncovered with
  the part's why (`uncovered` on the verdict).
- A loop (`certLoop`, core/cyclic.ts's `loopNodes`): the usual trees of its halting goals (kernel.ts's
  `loopObligations`) translated to one cyclic proof, the loop's machine's laws and its liveness's step laws, the proof
  Lean reads; the usual trees then its input and not checked again (`proveLoop`, a rank stated or found by
  `findRank`); where none is made, the usual trees, checked. core/cyclic.test.ts: gcd by subtraction's proof checked,
  and refused with its helpful turn's conclusion given a false part, its rank lowered to 0 or its use dropped.
- Time: loop certificates in the examples 31 to 271 ms against usual proofs of 4 to 30 ms. In one wave on Modal, the
  jobs that prove loops and liveness, three runs each against 0.21.0 (`runs/live/ab2`, `runs/live/ab2-base479`): 481.5 s
  of job time against 424.2 s (medians: the 21 examples jobs 50.31 s against 48.59 s, cycles 56.54 s against 50.16 s,
  liveness 7.25 s against 7.60 s, lean-cycles-loops 35.08 s against 30.59 s). The suite by default on Modal, every job there (no boat VM was ready): 678.3 s wall,
  4,100.5 s of job time, `data` failed (`runs/live/suite`); on boat 263.8 s wall, 2,965.4 s, four jobs that never ran
  (0.02 to 0.41 s, empty logs, boat's ticks failing with 502) failed (`runs/live/suite2`); run again on Modal, `check`,
  `infer` and `gdp` passed and `pairs` failed, its resource groups' test at 844,786.92 ms where it takes 9 to 15 s
  (`runs/live/suite2-again`), then passed three runs of three, as 0.21.0 did (`runs/live/pairs3`,
  `runs/live/base479`, the test 12.2 to 15.3 s and 9.9 to 10.9 s); with `--usual` on Modal, 642.5 s wall, 4,050.8 s, none failed (`runs/live/suite-usual`).
  `data`'s failure is its test of a function agreeing with + on small values only, at bun's 5 s limit with a 5 s
  search budget: of eight runs each on Modal one fails at this branch (5,506.90 ms) and two at 0.21.0 (5,026.99 and
  7,860.63 ms; `runs/live/data8`, `runs/live/base479`); nothing here touches its route.
- Lean: the 17 liveness and loop items' export is 0.21.0's byte for byte (the same SHA-256), 818,826 bytes cyclic
  (811,398 of them the items) and 281,197 usual (277,167); each checks on the standard axioms, 26 s cyclic and 13 s
  usual (`runs/live/lean-measure`, `runs/live/leandiff`; 0.21.0's in `runs/live/base479`, 23 s and 12 s).
- Termination (compare/term, 1,239 TPDB-ARI tasks at 60 s, on Modal): 58 terminate, each with its cyclic certificate
  (`cert` in the answer; 45,322 ms in all, at most 6,256 ms), the same 58 as 0.21.0 on Modal; 323 nonterminating against
  321, none contradicting (`runs/live/term-gdp`, `runs/live/term-gdp-base479`). Against 0.21.0's run on boat
  (`runs/backends/term-gdp`, 59 terminate) `iecs.t2.ari` is unknown: on Modal 0.21.0 doesn't prove it either, in
  three runs of three (its invariants not found within the rank search's time; `runs/live/term-diff-base479-1..3`).
- Still out: the search tree's and the sheet's laws reading a map at a key read from a map. Their usual proofs
  translated (research/cyclic/nested.ts, `runs/live/probe1`): the search tree's 18 nodes, a kind law ("every Tree
  node's folds are its children's") not proven in its 10 s (3,013 leaves grown), the sheet's 27 nodes likewise (1,445
  leaves); such a key is a cell, and its pair with the time (`t + k·Ω`) a product, so two of them equal only through
  products the translation doesn't find.
- Retiring the usual certificate, measured, not done: every rule but those four has a cyclic certificate, and the
  cyclic exports of the whole package (every item but the two) reach 866 of the Lean library's 1,098 declarations; the
  other 232 (2,779 of 10,493 lines; 176 and 1,892 with the two exported the usual way) are the usual twins'
  (`machine_sound`, `checkSKStep`, `sleads_sound`, Progress.lean, StepLaw.lean, Steps.lean's checkers) and a few no
  export reads (`wf_fix_unique`, `Repr` instances; research/cyclic/Retire.lean, `runs/live/lean-measure`'s `retire`).
  Before they go: the two laws above need a cyclic proof, and the jobs that read the usual twin need the cyclic one
  (export-kernel.ts `--examples`, every example rule and loop, the 21 `lean-examples-*` jobs; `--sets`; Trees.lean,
  TreesBig.lean, HistoryTrees.lean, StepLaw.lean and Steps.lean's demos; `lean-ksteps`, `lean-jev-fabric`). The
  usual trees stay either way: they are what core/translate.ts translates.

The second frontier corpus (`research/frontier2/`): 42 benchmark tasks that gdp-wired's 0.21.0 benchmark runs left
unproven and another tool solved, each standing for a group of tasks that fail for one reason, with 42 broken
variants. The interface is round 1's (`corpus.ts`, `score.ts`, `jobs.ts`), so a search track scores on it the same
way. Each item is the task itself, its file vendored at the benchmark's pinned commit and read by the translation its
benchmark run used (compare/chc, compare/tip, compare/term). Each is checked true outside the library, and each broken
variant false. The score at 0.21.0 (`runs/corpus2/baseline-0.21.0`, 168 jobs on boat VMs, 2 vCPU each, 618.3 s wall,
3,058.0 s of job time): the prover alone 0 of 42, with its search 3 of 42, the 42 broken variants refused. Nothing in
the library changed.

- 14 CHC-COMP LIA-Lin tasks, from groups of 825 tasks still unsolved at 0.21.0 (`runs/modal/infer/chc-final` against
  the 0.20.0 gap map, `groups_chc.py`):
  - a step goal over a wide Lustre transition left undecided even given the invariant (195 tasks);
  - invariants within the templates the search misses (39 Lustre, 15 others);
  - a program counter in bits (38);
  - clauses of several linear literals (113);
  - atoms over four or more values (71);
  - remainders and projections (34);
  - derivations of false no run finds (273 Lustre, 30 others).

  Each was checked by Spacer, Golem and Eldarica (`runs/corpus2/truth-chc`).
- 15 TIP 2015 problems, among them:
  - lemmas about other functions (prod/lemma_09, isaplanner/prop_53, prod/prop_14, prod/prop_42, sort_nat_ISortPermutes);
  - an accumulator's generalisation (prod/prop_35, isaplanner/prop_49, weird_nat_add3acc_spec);
  - two lists together (isaplanner/prop_84) and more time (list_PairOdds);
  - integer arithmetic through recursion (bin_nat_plus, nat_pow_pow);
  - a termination needing another function's lemma (sort_HSortCount);
  - McCarthy's nested recursion on an Int (mccarthy91_M1, M2).

  Each was checked by Vampire or cvc5 at 600 s where they prove it, and otherwise by TIP's theorem and its evaluator
  at 5,000 random values (`runs/corpus2/truth-tip-tools`, `truth-tip-eval`).
- 13 termination tasks (8 TermComp ITS, 5 SV-COMP), from `failures.ts`'s classes (447 ITS and 129 SV tasks another
  tool proves terminating and gdp-wired doesn't):
  - ranks reading no param;
  - a rank in order or per location;
  - multiphase ranks, a rank by a sign, min(p, q);
  - McCarthy's 91 as a loop;
  - loops whose turns the runs don't sample.

  Each was checked by KoAT2, LoAT or SV-COMP's verdict with Ultimate Automizer, and polyrank1's multiphase rank by z3.
  Each broken variant was checked by LoAT's NO, and five by a lasso `checkLasso` confirms.
- Proven at 0.21.0 by the search alone:
  - `reve/015` (16,748 ms) and `break_safe.c-1` (19,863 ms): the benchmark pipeline's 60 s of wall time and its
    runs' samples were the obstacle there, not the invariant's shape;
  - `list_PairOdds`, its group being more time (141,925 ms of wall time on 57 s of counted work).
- Language gaps recorded (README): nontermination (212 ITS tasks: a law is about every run, and the library has no
  claim that some run never ends); TIP's refusals (function variables returning a list 4, uninterpreted sorts 2 and
  constants 2, a product of two integers 1, a nested datatype 1, rings of functions that aren't structural 14); and
  SV-COMP's C translation refusals (56).

A law that is its own bridge (core/transfer.ts: `f(x, y) = x + y`, f a recursive function that agrees with the built-in
up to 6) is searched once, as the law, not first as its bridge and then again as itself. The suite's `data` job failed
now and then on core/data.test.ts's nearPlus law (x + y up to x = 7, then 0), which sat at bun's 5 s test limit:
7,860.63 and 5,026.99 ms in two of eight jobs (`runs/live/base479`), 5,506.90 ms in one of eight (`runs/live/data8`),
5,009.33 ms (`runs/live/data3`), 5,097.97 ms (`runs/live/suite`). Wall time didn't decide it: the search's budget is
already counted (`dataRate`), and its work was the same in containers of 1 and 2 vCPU, the bridge 114,197 units, the law
after it 35,367, its last lemma round begun at 496 of its 5,000 counted ms (`runs/datafix/trace0`). The search was done
twice. Now one search of 114,688 units, the same in each container, with the same verdict (not proven, 35 tried, stuck
at the same case): 2,100 to 3,069 ms alone where it took 3,758 to 5,280 ms (`runs/datafix/near-after`,
`runs/datafix/near-base`, three each on 1 and 2 vCPU). No limit and no budget changed.

- Ten `data` jobs on 1 vCPU: that test took 2,814.32 to 4,954.97 ms at a42dc81 (`runs/datafix/before`), now
  1,885.99 to 3,168.36 ms (`runs/datafix/after`), none failed in either.
- A false bridge that the samples miss, its bridge law not the law, keeps its test (core/data.test.ts): `nearSucc` is
  n + 1 up to n = 12, then 0, read in `nearSucc(n) >= n + 1`. The bridge `nearSucc is x + 1` is in the plan; neither it
  nor the law is proven or refuted, the law isn't proven through it, and each search ends at its counted budget of
  200 ms, which proveData's verdict now says (`stopped`). Its searches do the same work on 1 and 2 vCPU (75,370 and
  75,256 units at 250 ms, `runs/datafix/probe`). In ten `data` jobs on 1 vCPU it took 1,054.37 to 1,979.37 ms and the
  nearPlus test 1,932.74 to 2,936.32 ms, none failed (`runs/datafix/after2`); the suite with it, 204 jobs on boat VMs,
  252.2 s wall, 3,308.8 s of job time, none failed (`runs/datafix/suite2`).
- The suite (204 jobs, on Modal): by default 546.4 s wall, 4,473.3 s of job time, none failed, that test 2,983.40 ms
  (`runs/datafix/suite`); with `--usual` 427.1 s and 4,099.5 s, none failed, 3,194.31 ms (`runs/datafix/suite-usual`).
  The frontier jobs' verdicts are a42dc81's line for line (`runs/datafix/frontier-base`): the datatype track today 2
  of 25 and with its search 23 of 25, the rest 8 of 67 and 67 of 67, every broken variant refused.
- TIP (`compare/tip/modal_tip.py --tools gdp`, 492 tasks on Modal): 140 proven and 7 refuted, the same tasks as
  a42dc81's run (`runs/datafix/tip`, `runs/datafix/tip-base`). Ten tasks differ between unknown and a 60 s timeout;
  run twice more on each side (`runs/datafix/tip-flip-*`), each gave both answers within one side's runs.

## 0.21.0

Four new things a law or a rule can say, none of them trusted: recursion that isn't structural (a measure, found or
given), "there exists" (a witness term or a ghost), division and remainder by a constant with integers in the datatype
language, and a user's own recursive arithmetic read through the built-ins it computes. The trusted files
(`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts`) are as in 0.20.0; Lean gained three theorems for them (`wf_fix_unique` in Data.lean, `some_of_subst` and
`some_of_ghost` in Ghost.lean), on the standard axioms. TIP 2015: 140 of 492 proven, 73 at 0.20.0, none wrong
(`runs/modal/arith/tip-gdp`). CHC-COMP LIA-Lin at 60 s: 382 solved, 368 at 0.20.0, none wrong
(`runs/modal/infer/chc-final`). `inferLaws` finds the same laws on any machine. The release suites (200 jobs, one after
the other) ran on boat.dev VMs through the new `--backend auto`, 2 vCPU and 4 GB a job as on Modal: by default 264.4 s
wall, 2,668.1 s of job time, none failed (`runs/release/0.21.0-default`); `--usual` 268.2 s, 2,503.8 s, none failed
(`runs/release/0.21.0-usual`). The same suite on Modal at the merged commit before took 489.8 s and 4,246.7 s
(`runs/modal/backends/suite-default`).

Recursion that isn't structural, in the datatype language (`gdp-wired/data`): a function whose calls are on any
arguments is taken once its termination is proven, its equation a fact only then. TIP 2015 (`runs/modal/wfrec/tip4`,
gdp-wired at 60 s, cvc5 and Vampire from `full2`): 62 of the 155 theorems refused for recursion that isn't structural
translate now, 3 of them proven, 140 of 492 proven (the cheap wins' 137, none of those lost), wrong 0. The datatype
corpus: 23 of 23 laws proven, its 18 broken variants and definitions that don't terminate refused
(`runs/modal/wfrec/suite2`'s `frontier-datatype-0..5`). The suite (`modal/suite.json`, 198 jobs) at this branch: 513.8 s
wall, 4,426.3 s of job time, none failed (`runs/modal/wfrec/suite2`).

- Termination (core/data.ts, "well-founded recursion"): where no parameter is structural, a measure, a lexicographic
  tuple of sums of parameters' sizes (a natural's itself, a datatype value's its size) plus a constant: the user's
  (`define(name, params, ret, body, {measure: ['xs', 'ys']})`, a component of several names their sum), else the first
  of a size, a lexicographic pair or triple, a sum of two or of all, then core/cycles.ts's LP rank over the function's
  runs (`ranksOfRuns`), that its runs (each call from the parameters' sizes to the arguments') don't contradict. Each
  call's obligation, a law over the path's variables (a match on a variable is the case's constructor at new variables,
  an if's condition a hypothesis), is proven by the kernel in a program without the function: one node first, the
  definitions unfolded once and 16 models' congruences; else proveData's induction without conjectured lemmas (a
  quicksort's call on a filter of the tail by the filter's own recursion). 10 s of counted work a function. Refused,
  with the measures tried: a definition that doesn't terminate (`f(x) = f(x) + 1`, whose equation as a fact would prove
  anything), nested recursion (a call in its own argument or condition), a ring of functions that isn't structural.
- Soundness (lean-kernel/Data.lean's `wf_fix_unique`): a functional that reads its function only below the argument's
  measure (`lexLt`, the cyclic ranks' order) has exactly one fixpoint, so the taken equation has a model and only one,
  the function as written. Standard axioms only.
- Functional induction: a law over such a function is tried by its call graph, each use at a recursive call's arguments
  under the call's path (its ifs' conditions too), ranked (level, the measure, 0 or 1), every rank of the program padded
  to its widest measure (1 where every recursion is structural, so the structural proofs are as before); the functions
  unfolded where a matched parameter is a constructor's value; a size the goal reads gets its value's shape.
- A `size` term (`xs.size()`): 1 plus a value's fields' sizes of its group, read by measures and by laws.
- The Lean export (lean-kernel/data.ts): such a function with `termination_by` its measure (Data.lean's `Lx`, a tuple
  ordered by `lexLt`, where it has several components) and `decreasing_by` omega over the match equations it names
  (`match _h1 : xs with`); an obligation that reads other functions is a lemma before it, by induction on the variable
  the kernel inducted on (`dataqsort.qsort_dec1`). New items, `lean-data-7`: `datamerge.len_merge`,
  `datainterleave.len_interleave`, `dataadd3acc.add3acc_sum`, `datamergestated.len_merge_stated`,
  `dataqsort.qsort_single`, each on the standard axioms (`runs/modal/wfrec/suite2`).
- `examples/data.ts`: the merge of two sorted lists ((size xs, size ys) found; its length, 3,651 ms in the `data` job),
  lists interleaved (size xs + size ys; 928 ms), add3acc ((x, y); 34 ms), the merge with its measure stated (4,107 ms),
  a quicksort on filters of the tail (`qsort [x] = [x]`, 1,521 ms); broken: a merge that drops an item, an add3acc that
  forgets one (each refused with a value), and 4 definitions that don't terminate (a merge on the same lists, an
  interleave that only swaps, an add3acc that keeps y, a merge whose stated measure size xs its second call doesn't
  lower), refused with the reason. Each a frontier corpus item (`research/frontier/datatypes.ts`).
- TIP (`compare/tip/`): of the 155, 62 translate (`add3` 20, `add3acc` 20, `nubBy` 8, `qsort` 8, `op` 4, `interleave` 2,
  by the function `full2` named first), 3 proven (`list_Interleave`, `list_nat_Interleave`, `weird_nat_add3_spec`), 5
  refuted: `weird_nat_mul3_same` and `weird_nat_mul3acc_*`, false as TIP writes them (`mul3acc` adds `add3acc x y z`
  where `mul3` adds the predecessors' `add3`; mul3acc(2, 1, 1) = 5, mul3(2, 1, 1) = 2), each counterexample confirmed
  by TIP's evaluator. Still refused, with the reason: termination not proven 87 (a sort whose decrease needs a lemma
  about another function, `toList (hmerge p q)` and the like; `idiv`, which never ends at y = 0), a ring of functions
  that isn't structural 6. summary.ts lists a refutation TIP's evaluator confirms apart from the wrong ones, and reads
  several run directories (a gdp-wired run beside `full2`'s tools).

`proveData` takes a user's own recursive arithmetic and wrappers: TIP 2015 (492 theorems, 60 s each, 2 vCPU) 137
proven, was 73, none wrong; 17 of the 68 `false/` properties refuted as before, each confirmed by TIP's evaluator
(`runs/modal/cheap/tip3`, cvc5's and Vampire's rows from `runs/modal/tip/full2` in `runs/modal/cheap/tip3-with-full2`:
cvc5 168, with conjecture generation 187, Vampire 189). The datatype corpus unchanged: 15 of 15 laws proven and the 15
broken variants refused (`runs/modal/cheap/corpus2` against
`runs/modal/dataplus/corpus1`). The suite: 195 jobs, none failed, 574.2 s wall, 4,242.3 s of job time
(`runs/modal/cheap/suite1`).

- Through the built-ins (`core/transfer.ts`): a recursive function of one or two naturals that computes a built-in
  (+, ∸, min, max, ≤, <, =, ≥, >, ≠, x + 1, x ∸ 1, 2·x, x = 0) at every argument up to 6 is a candidate, found by its
  values, and used only once its bridge law (`plus(a, b) = a + b` at every a, b) is proven by `proveData` itself; a
  function that reaches it is copied with the built-in in its place and its copy law proven (a node made from the two
  bodies, else the search). The law said through them is proven by the search, and the law as stated by one more node
  that uses it, the bridges and copy laws at its calls, and the congruences between them: one cyclic proof the kernel
  checks, which Lean reads as any other (`lean-data-6`: `leq(n, plus(n, m))`, `geq(x, x)`, a count by the user's own
  `=`, a law by cases, each a theorem about the Lean definitions). `isaplanner/prop_21` (`n ≤ n + m`, both recursive)
  was given up after 57 attempts in 5.79 s; now 0.26 s. A candidate that agrees on small values only isn't bridged
  (its bridge isn't proven). The verdict's `through` names what a proof went through; `transfer: false` keeps the law
  as stated.
- Unfolding: a function that isn't recursive is its body wherever the law reaches it (the law, and the copies),
  before the induction is chosen (`geq x y = leq y x`); a law that would grow past eight times its size so isn't.
- Cases without induction: where nothing else proves a law, its cases on each variable, its definitions unfolded
  (`isaplanner/prop_17`, `(n ≤ 0) = (n = 0)`); a law no scheme applies to gets the attempt without induction first.
- Evaluation within bounds: a natural past 2^53 throws `EvalLimit` (a RangeError) instead of losing precision, and in
  the search so do calls nested past 1,000 or past 20,000 in one evaluation; `refute` skips such a sample instead of
  throwing (recursive powers and factorials: 4 TIP tasks no longer errors). `programOf` collects a datatype read only
  through a constructor, a match or a test (a law with its definitions unfolded).
- Of TIP's diagnostic classes, all 48 `--native` ones are proven now, all 6 `--inline` ones, the `--today` one, and 10
  no diagnostic proved; 1 proven before is lost within 60 s (`prod/prop_25`: its law through `+` takes the time the law
  as stated needed). `compare/tip`'s `--native` and `--inline` do nothing now; `--no-transfer` is the law as stated.

"There exists" in laws (`core/exists.ts`, `examples/exists.ts`): `exists(kind?, k => ..., witness?)` over naturals,
integers, yes/nos or a map's keys, anywhere in a law where it reads so, in the assumption (a value each request brings)
and in a precondition. The kernel never sees one, and nothing trusted changed in TypeScript: the law it proves is the
condition with a witness term of the state in place, or the condition over ghosts the machine gains (a value at the
start, and after each step one over the witness before, the request and the state before), each chosen from the
kernel's counterexamples. The Lean export states each law as `∃ w1 .. wn : Nat, ...`, proven by ⟨witness, proof⟩ through
two new theorems of `Ghost.lean`, `some_of_subst` and `some_of_ghost`, on the standard axioms (`runs/modal/exists/lean2`,
`lean3`: both the usual and the cyclic export check, and two tampered witnesses are refused).

- Witnesses: what the law's own atoms solve for (x = e, x <= e, x < e, an integer's two parts together), 0, the state,
  the params; for a ghost, its value before, shifted by a constant or by one to four times a value the request or the
  state carries, the request's values, the state before, and its value before while it still meets the law's conjuncts
  that read it after the step (else one of those). Each per case of the step (the conditions its updates split on: a
  CHC rule's clause, say), the counterexamples so far all met. A witness given is the only one tried: the kernel proves
  the law with it or refuses it, with its counterexample. The verdict's `witnesses` says how each reads ("w starts at 0;
  after a step w + 1 where go = up, else w").
- A false one is refused by a run where no value can be a witness, decided exactly where the bound value is one natural
  or integer read linearly, or a natural read as a map's whole key (`someHolds`); the runtimes find an assumption's
  witness the same way (`encodeInput`, `encodeParams`), and refuse a request none fits.
- `inferLaws` proposes congruences, ∃k. v = c·k + r, where the runs keep v's remainder by 2, 3, 4 or a constant of the
  rule's (`{existentials: false}` turns them off), chosen where no bound rules a counterexample out, and tried with the
  laws alone where the search ends unproven. The frontier corpus's new exists track: 2 of 2, its broken variant refused
  (`runs/modal/exists/frontier3`).
- CHC-COMP LIA-Lin, gdp-wired alone at 60 s (`runs/modal/exists/chc-gdp2`): 375 solved (231 sat, 144 unsat), none
  wrongly, 5 out of time, against 368 at 0.20.0 (9 more, 2 fewer: `compare/chc/README.md`). Given Spacer's own invariant
  (`prof/given.ts`), the 27 tasks whose invariant keeps an existential are all stated now (none was), and the kernel
  proves 7 of them at 60 s (`given5`; 12 at 300 s, `given4-t300`); the 18 with a remainder or a quotient are stated as
  existential quotients, 3 proven.
- TIP 2015 (`compare/tip/`, `runs/modal/exists/tip-gdp2`, 137 proven as the cheap-wins run): the two existential goals, refused before, are read and
  refuted, each counterexample confirmed by TIP's evaluator: `list_elem_map` and `list_nat_elem_map` say
  `∃ x. f x = y ∧ elem y xs` where `elem x xs` was presumably meant, false at `y = 3, xs = [5], f 5 = 3`.

Division and remainder by a constant, and integers in the datatype language. Nothing trusted changed: `x.modBy(k)` and
`x.divBy(k)` are the rule's functions mod$k and div$k, which the kernel knows by two facts it already decides
(x = k·(x div k) + x mod k, x mod k < k), and Lean proves both of its own `%` and `/` by `omega`. CHC-COMP LIA-Lin at 60 s
(`runs/modal/arith/chc-gdp`): 381 solved (237 sat, 144 unsat), none wrongly, 8 out of time, against 375 on main
(`exists/chc-gdp2`) and 368 at 0.20.0; of the 18 tasks whose Spacer invariant reads a remainder or a quotient, 7 (3 on
main, 0 at 0.20.0). TIP 2015 (`runs/modal/arith/tip-gdp`): 140 proven as on main (`wfrec/tip4`), none wrong, and 23 of
the 68 `false/` properties refuted, was 18 (the queues, which subtract on Int). The frontier corpus: 90 of 92 by the
searches, 42 of 42 broken variants refused (`runs/modal/arith/frontier2`), its two new integer items the walls they are.

- Rules: `modBy(k)` and `divBy(k)` on any term, k a constant ≥ 1 (a law, a step, a decision); on an integer, Euclid's
  (−7 div 2 is −4, −7 mod 2 is 1), the remainder of the natural pos + (k − 1)·neg. The rule declares div$k and mod$k for
  every divisor its terms and laws read (a law from another instance of the rule too); the runtimes compute
  `Math.floor(x / k)` and `x % k`, so a rule that divides is still refuted by runs. Division by a term isn't offered:
  x = y·q + r is a product of two unknowns (`examples/arith.ts`: a rota, quarter-hour billing, a pair dispenser, a signed
  ledger, each with a broken variant refused).
- Lean: a law reading x div k or x mod k states `x / k` and `x % k` (under `μ «mod$k» = fun x => x % k`, the hypothesis the
  facts' theorem takes too), and a law about an integer is stated again over `Int` (`law0_int`: ((ρ «x» : Int) − ρ
  «x$neg») % 3 = 0, by `omega` from the law over the naturals). `lean-package` checks the four examples.
- `inferLaws` proposes remainders, v mod k = r for a state value or the sum or difference of two whose runs keep one
  (under a guard where only some runs do), k the divisors the rule reads, 2, 3, 4 and its constants up to 64, chosen
  where no bound rules a counterexample out. Where the existentials' congruence would say the same, the remainder is the
  one proposed (a plain law: no witness to choose, a guard, `%` in Lean); `{remainders: false}` gives the congruences.
- Signed integers, two designs measured on 215 CHC tasks (`runs/modal/arith/intdesign-*`): pairs of naturals (kept),
  pairs written unnormalized (46 solved, as the pairs), and the kernel over integers prototyped in TypeScript alone on
  branch `lang/arith-int-proto` (49 solved, 10.7% less time on the sat tasks all three solve), not taken: it would change
  the Lean twin's semantics everywhere for that (`compare/chc/README.md`).
- The datatype language: `integer`, a sort beside `natural` (Lean's `Int`): +, −, negation, multiples of any sign,
  comparisons, Euclid's `modBy`/`divBy`, integer fields and parameters; a natural's `modBy`, `divBy` and `mul` (a product
  of two). An integer is its zigzag code (a bijection with the naturals, as a datatype's), its value two parts of the code
  read by one fact, so the encoding has no if; Lean's export defines `Z.enc`/`Z.dec`, proves the facts by `omega` and
  closes each law over `Int` (`lean-data` items `first_cons`, `twice_less`, `int_euclid`, `even_sum`). A law that calls
  no function is tried by its cases first. Integer arithmetic through recursion (a list's total through its negation)
  is past the search's budget (research/frontier's `datatype/integers`).
- CHC: a clause's `mod` and `div` by a positive constant are the rule's own (were request values).
- TIP: Int is the integers where a problem subtracts or negates (the statement unchanged), a natural elsewhere as before,
  now with `div`, `mod` by a positive constant and products of two unknowns.

`inferLaws`' budgets are counted in work, not wall time, so what it finds is the same on any machine. Its test of a law
that needs an invariant took 3,553 to 4,911 ms in ten `infer` jobs of 1 vCPU (`runs/modal/infer/before`), and one of
the ten failed its in-flight test (7,005 ms, 900 proofs, not proven); now 1,829 to 2,970 ms, none failed
(`runs/modal/infer/final`). The suite (`modal/suite.json`, 200 jobs) at this branch: 484.3 s wall, 4,396.3 s of job time,
none failed, that test 2,540 ms (`runs/modal/infer/suite`).

- The runs: 16,000 requests tried, and on until the samples are full (3,000), not 500 ms. Every search of the suite's
  jobs and the frontier corpus keeps 3,000 samples, as many as or more than 500 ms gave on 2 vCPU (745 to 3,000,
  `before`'s cal2 jobs). The rest (candidates, Houdini, the counterexamples' forms, the kernel's proofs) by the rows
  read, the forms evaluated, the laws watched and the kernel's work, each at about the slowest tenth of its rate on
  Modal's 1-vCPU containers (`inferRates`), so a counted budget runs out no later than a timed one would there.
- `ms` is that budget, and the search's wall time a stop only: `stats.stopped` says it was reached (by none of the
  searches of `final`'s jobs); core/infer.test.ts asserts it isn't. `runs` sets the runs' requests; `runsMs` times the runs
  alone; `timed` times everything as before, which `compare/chc/solve.ts` passes (the track's limit is wall time).
- Each row's atoms are read once, however many forms are evaluated there (Houdini, the counterexamples' choice).
- The same lines in a 1-vCPU and a 2-vCPU container (`final`'s f1 and f2 jobs, GDP_INFER_TRACE=1: each phase's
  counts and what was found) for the `infer`, `exists` and `arith` jobs; in `cycles` and the frontier items, the same
  verdicts and found laws, the counts differing where core/cycles.ts passes what is left of its own wall-clock budget
  as `ms`. The frontier corpus: 67 of 67 and 24 of 24 broken variants refused, every found law as before (`final`'s
  frontier-score). CHC-COMP LIA-Lin at 60 s (`runs/modal/infer/chc-final`): 382 solved (238 sat, 144 unsat), none
  wrongly, against 381 (`arith/chc-gdp`) and 380 for this branch's base rerun (`infer/chc-before`); the 7 tasks
  answered otherwise than in `arith/chc-gdp`, run three times more with each, are sat in 8 of 21 runs on the base and
  10 of 21 on this branch, each answer at 43 s or later (`infer/chc-rerun-old-*`, `chc-rerun-new-*`): noise at the
  limit.
  `research/perf/infer-cal.ts` runs the corpus' invariant, exists and cycle items for the calibration.

Infrastructure (nothing in the library changed): the experiment runners take `--backend auto|boat|runpod|modal`
(`modal/fanout.py`, `modal/README.md`). `auto` runs CPU work on a pool of boat.dev VMs (`modal/boat.py`) and GPU work on
a RunPod pod (`modal/runpod.py`), and moves to Modal what they can't serve, each move logged with its reason; `auto` is
the default from `python3` (`modal run` is Modal as before). The suite on boat: 200 jobs, none failed, 267.7 s wall, 3,002.5 s of job time, $0.032
(`runs/backends/suite-default`; Modal at the same commit 489.8 s, 4,246.7 s, $0.256, `runs/modal/backends/suite-default`).

- `modal/run.py`: the same jobs, flags and outputs on any backend; `summary.tsv` has a 4th column, the backend.
- The compare runners (`compare/chc`, `compare/tip`, `compare/term` ITS and SV-COMP): `python3 <runner> --backend ...`,
  their solvers and benchmarks in the pool's image (`BOAT_SETUP`), the same `results.jsonl`.
- The GPU runners (`research/hw/run_gpu.py`, `run_synth_gpu.py`, `research/modal-gpu/run_gpu.py`): a RunPod pod per
  run, Vulkan through NVIDIA's EGL ICD, checked before anything runs.
- `modal/reap.sh` also releases and stops boat VMs and deletes RunPod pods whose client is gone.

## 0.20.0

The frontier corpus proven in full: 81 of 81 items where the library alone proves none, every broken variant refused
(the search tree's insertion keeping its order, mutual and nested datatypes, recursion on a natural, ranks past linear
and past coefficient 4, liveness ranks found, closed forms of degree 3; `runs/modal/dataplus/corpus1`,
`runs/modal/ranks/corpus3`). Every rule the usual route proves now gets its cyclic certificate by translation but the
claims about runs that never end and four laws reading a map at a key read from a map: 119 proofs on the usual rule in
the whole suite, 1,122 in 0.19.0's. A step law's certificate costs 2.15x its usual proof, the cyclic Lean export a
quarter to a half of the text it was. The suite (194 jobs, one after the other): by default 461.3 s wall, 3,974.9 s of job time, none
failed (`runs/modal/kstep/final-default`); with `--usual` 384.0 s, 3,404.0 s, none failed (`runs/modal/kstep/final-usual2`).

The datatype track's corpus closed and widened: the search tree's insertion keeping its order proven, and datatypes
that nest or come in mutual groups, and functions recursing on a natural, taken by the search and by the Lean export.
The track: 18 of 18 laws proven where the library alone proves none, its 12 broken variants refused, every proven law
checked in Lean on the standard axioms (`runs/modal/dataplus/corpus1`).

- `bst(t) → bst(insert(x, t))` proven (20,081 ms in the corpus, 19,415 ms in the `data` job of the same run), within
  the budget it had. With both its lemmas given it had stayed unproven (its search over at 183,819 ms,
  `runs/modal/dataplus/prof1`): of the reads its goal matched the allAbove lemma at, the four kept were all at the left
  subtree, and the use at the right one, which the insertion's other side needs, wasn't kept. A lemma's uses are now
  four as found, then the rest ranked by the random models in which the lemma's read is the goal's, one per set of
  values (`lemmaCaps`), each case node keeping four of a lemma among those its models meet. Lean: `databst.bst_insert`.
- Fields of other datatypes (`core/data.ts`): one declared before (`data('Bag', {none: {}, more: {items: List, rest:
  self}})`), or one of a group declared together (`mutual({Rose: {node: {value: natural, kids: 'Forest'}}, Forest:
  {nil: {}, cons: {head: 'Rose', tail: 'Forest'}}})`). A datatype's size counts its group's fields; a group with no
  value is refused, and so is one whose datatypes with no constructor of no field name each other in a ring (the
  bijection with the naturals doesn't take it). Functions may call each other: the recursion is checked across the
  ring, each function's decreasing parameter chosen so every call within it passes a field.
- Mutual induction: on a variable of a group's datatype, the law and a companion per datatype its fields reach, the
  law lifted through each function's own call at such a field (`rsize(rmirror(t)) = rsize(t)` at a forest is
  `fsize(fmirror(ts)) = fsize(ts)`), each node using the others at the fields of their datatypes, each ranked by its own
  datatype's size. Lemmas are matched against the companions' goals too.
- Recursion on a natural: `n.match({zero: () => ..., succ: ({pred}) => ...})`, read as `if n = 0 then ... else ...` with
  `pred` as n − 1; recursion induction at n − 1, ranked by n.
- The Lean export (`lean-kernel/data.ts`): a group's inductives in a `mutual` block (`deriving instance DecidableEq`),
  its sizes, codes, decodings and both inverses each in one, the decodings well-founded by (group size + 1)·n plus an
  order (`weakOrder`); a ring of functions in a `mutual` block; a natural decreasing argument split as 0 or m + 1 in the
  facts' proofs; a second split round where goals remain. The existing exports read the same but for one tactic
  (`simp [tupk, tup] <;> omega` where `; omega` failed once simp had closed the goal).
- `examples/data.ts`: the sum of a flattened rose tree (15,426 ms, its forest companion and the sum of an append), the
  size of a mirrored rose tree (16,450 ms, with `fsize(snoc(ts, r)) = fsize(ts) + rsize(r)` found), the length of a
  concatenation of lists (5,628 ms), `length(replicate(n, x)) = n` (139 ms), `append(take(n, xs), drop(n, xs)) = xs`
  (1,146 ms), `length(drop(n, xs)) = length(xs) − n` (3,639 ms), each a law of the frontier corpus with a broken
  variant (a flatten that drops the node's value, a mirror that drops a tree, a concatenation that drops the first list,
  a replicate with one more, a drop of one too many), and the search tree law with its hypothesis dropped; all 12 broken
  variants refused in 4 to 17 ms. Lean: `dataroseflat.sum_rflat`, `datarosemirror.rsize_rmirror`,
  `databag.len_concat`, `datarep.len_replicate`, `datatakedrop.take_drop`, `datadroplen.len_drop`.
- The suite: `frontier-datatype-0..5` (six shards, was four), `lean-data-4` and `lean-data-5` for the new Lean items.
  In `corpus1` the shards took 69.75 to 153.14 s, `lean-data-0..5` 45.46 to 120.03 s, `data` 125.98 s.
  The whole suite (`modal/suite.json`, 193 jobs) at this branch's last commit: 452.9 s wall, 4,304.0 s of job time, none
  failed (`runs/modal/dataplus/suite2`).
- Still out (research/frontier/README.md): a lemma past six symbols or of another shape; a companion the functions' own
  calls don't lift the law to; a ring of functions as a recursion induction; nested datatypes in Lean's sense (a field
  of a type applied to the datatype, `List Rose`: there is no type parameter, a list of trees is a forest declared with
  them); reachability through a structure that changes.

The cycle track widened past linear ranks with small coefficients: ranks that need a coefficient past 4 (the exact LP),
ranks of degree 2 (products of two variables), a liveness whose rank is found rather than stated, closed forms of
degree 3, and lemmas about functions of two arguments. Nothing in the kernel or the Lean twin changed: every rank is a
term the kernel's goals read as they read a stated one (a product as a monomial), and every proof found is checked in
Lean as before. The cycle and lemma tracks: 27 of 27 items proven where the library alone proves none, the 22 broken
variants refused by both (`runs/modal/ranks/corpus3`, 1 vCPU a job).

- `core/cycles.ts`, the exact LP: where the ranks' box of coefficients up to 4 has no solution, the rows are solved
  exactly over the rationals (a two-phase simplex, the least sum of absolute coefficients), the solution scaled to whole
  numbers; found on the smaller half of the runs and kept only where it holds of all of them, so a coefficient the
  runs' size forces (32·x + y where x reaches 33) is refused. An exchange (six tokens buy a coin, a coin sells for five):
  11·x + 2·y, as a claim over its function (77 ms) and as a loop (403 ms).
- Ranks of degree 2, one product of two variables at a time: a loop's products its own terms read first, before the
  invariants, the others after them within a quarter of its time; a claim's products it reads, each component a
  natural only at the ends of the edges it compares. Counting up to a square, `up(i, n) >= n·n`: n·n − i (252 ms);
  `while i < N·M`: M·N − (i + 1) (391 ms; the linear rank the runs give, 299 − i, the kernel refuses). A triangle (y
  from x − 1 again as x drops) gets (x, y), linear in order, before any product (314 ms).
- `findLeadsTo`, and `leadsTo` without `rank`: `proveLeadsTo` finds the rank from the rule's runs (a helpful request in
  its region lowers it, any other step doesn't raise it), then the kernel's liveness goals with the invariants
  inferLaws finds. Batches with its rank left out: (waiting, items) (709 ms); a pipeline: 2·inbox + outbox (347 ms).
- `cycleLemmas` takes functions of two arguments: an exact line, or bounds by 0, k, j or k + j and the tightest
  constant, each proven alone as a cyclic claim, the proof their nodes side by side (checked again). A capped fill
  read at (n + 1, cap): `fill(k, j) ≤ k` found (122 ms). A use whose rank is its node's own, term for term, is left out
  (its guard is false).
- `core/discover.ts`: closed forms of degree 3, fitted exactly at x = 0..3 (Newton's differences), a closed form tried
  alone before the other candidates. The sum of the squares: `6·f(x) = 2·x·x·x + 3·x·x + x` (60 ms; Lean:
  `foundpyramid`).
- Each new item has a broken variant (a coin that sells for six, a false square bound, a loop whose x never drops, a
  count that stops at N, a fill read one step ahead, a helpful request that stalls, a false closed form), each refused.
  Lean: `lean-cycles` takes `cycexchange`, `cycsquare`, `rulefill`, `rulefilllemma`; `lean-cycles-loops` takes
  `looptriangle`, `loopexchange`, `loopproduct`, `livebatches`, `livepipeline`; every job passing in
  `runs/modal/ranks/suite1`.
- Against 0.19.0 in the same wave (three runs each, `runs/modal/ranks/corpus3`'s `rep-*` jobs): every earlier proven
  item within the runs' spread (medians 0.48 to 1.26 of 0.19.0's); two broken variants refused later, the degree-2
  search they now try (three phases with y reset 4,929 ms against 2,809 ms; two phases with x never dropping 555 ms
  against 149 ms).
- Still out (research/frontier/README.md): a rank of two products at once or of degree 3; a product a claim doesn't
  read; a liveness rank past linear; a coefficient the runs' size forces; a closed form with products as a
  generalization; a two-argument function's base case at a constant argument (its paired key's monomials).
- The suite (`modal/suite.json`, 193 jobs) at this branch: 392.3 s wall, 4,321.5 s of job time, none failed
  (`runs/modal/ranks/suite1`).

Every rule the usual route proves now gets its cyclic certificate by translation, the TypeScript certificate searched
nowhere by default: flags that hold at every key, k-step laws over a map and requests allowed join the laws, step laws,
recurrences and folds. Left on the usual rule, by default, in the whole suite (194 jobs, `runs/modal/cover/last-default`): 127 proofs, the
claims about runs that never end (liveness 36, loops 79, whose step laws are certified), four laws reading a map at a key
read from a map and 8 k-step laws the translation doesn't make; 0.19.0's suite (189 jobs) left 1,122
(`runs/modal/flip/default`). A
datatype search's verdict no longer depends on the container it runs in. The trusted code is unchanged (kernel/kernel.ts,
kernel/cyclic.ts, lean-kernel/*.lean).

- Flags that hold at every key, translated (core/cyclic.ts's `machineNodes`): the machine read as its sk machine (each
  flag and its witnesses inputs a request names), the usual goals' closing hypotheses (kernel.ts's `closing`) the
  closing facts (`qflagFacts`, BridgeRules.lean's `cycQFacts`) at the step's time, each time at most T decided first.
  `qflagNodes` is `machineNodes` now (kept, an alias); the Lean export translates these machines too. In
  `runs/modal/cover/last-default` none is left for the flags (0.19.0: 203 machines, 93 step laws, 16 k-step laws).
- k-step laws over a map: a later step reads the map as the usual goal's term over the cells at t − k (its laws there a
  use only where they read no map), its assumption, `when` and closing hypotheses the usual goal's renamed (hypotheses of
  the node after the steps); the step law's node reads each cell back to t − k through the maps' steps (`cellChain`),
  times one step back at a time (`tBack`, as a step's fact reads the time before it; BridgeRules.lean's `cycKOk` reads
  both forms). A map a later request carries is its cells at that request's time. Left: 8 (0.19.0: 702), each a
  premise or a node the translation doesn't prove (`steplaw-k`'s and `hw-check-steps`' random machines, the quantifier
  examples' normal form, derived child and derived authority); where a machine's step laws together aren't translated,
  each is tried alone, so one such law leaves the others theirs.
- k-step laws' certificates back within a small factor of their usual proofs, none left on the usual rule
  (`runs/modal/kstep/final-default` against `runs/modal/cover/last-default`). Without a map a time read one step back
  at a time is a term k deep, and each premise of the step law's node (a state after a step) was grown on a slice that
  followed each cell back through every step's fact before it: the budget rule's 32 steps took 39,188 ms against its
  usual proof's 1,503 ms. Such a law's times are t − n at once again (`tSub`, as in 0.19.0; `cycKOk` reads both forms):
  the budget rule's (leaves, ms, usual ms) at k = 2, 4, 8, 12, 16, 32 were (9, 37, 6), (36, 126, 65), (67, 459, 475),
  (99, 1,333, 384), (131, 3,131, 442), (259, 39,188, 1,503); now (12, 48, 6), (43, 120, 59), (82, 253, 521), (122, 419,
  386), (162, 690, 447), (322, 2,482, 1,477). The normal form's 2-step law ran its translation's minute out (60,201 and
  60,094 ms, 1,874 leaves, 332 grown again): a later step's closing hypotheses read the flag at a later request's
  witness, and the closing facts' keys were read over the first step's frame alone. Keyed over the whole frame, the
  later closing facts' cells chained back to t − k, it is translated (3,133 and 2,843 ms, usual 18,096 and 16,751), and
  derived child and derived authority with it. Over a map, the step law's node is carried on its goal sliced first (a
  step's equations for state the law doesn't read, whose choices `carry` split at every leaf, left out: the k-step fuzz's
  worst law 698 leaves before, `runs/modal/kstep/b4`), the tree widened to the whole goal; the node after the steps states only the equations
  after a step its usual tree reads (each is a premise where the step law uses it). A translation is bounded by
  `GDP_CERT_MS` or four times its usual proof's time, whichever is longer (`translateMs`), no longer a minute: the
  longest against its bound in `final-default` is scope grants' 5,982 ms of 11,964.
  The step-law certificates translated in both runs (1,068, matched by job, law and place in the log): 151,474 ms
  against 40,977 ms of usual proof (3.70x) before, 69,248 against 32,151 (2.15x) now; in `final-default` all 1,075
  translated, 78,504 ms against 67,334 (`last-default`: 1,077 of 1,087, the 10 that fell back 136,490 ms). Left on the
  usual rule: 119 proofs (127), liveness 36, loops 79, the four laws reading a map at a key read from a map.
  Job seconds, 0.19.0 (`runs/modal/flip/default`) / `last-default` / `final-default`: quantifiers 67.07 / 190.15 /
  74.61, steplaw-k 40.27 / 142.07 / 79.94, steps 5.75 / 47.35 / 7.1, seqs 31.98 / 58.97 / 46.91, cycles 40.43 / 59.4 /
  47.46, hw-check-steps 17.97 / 36.59 / 16.03, pairs 34.62 / 52.28 / 41.69 (one container to the next these vary
  widely: steplaw-k three times in one wave 63.9 to 95.7 s, `runs/modal/kstep/ab4`). `hw-check-steps`' random laws are
  translated in `final-default`; one fell back in `runs/modal/kstep/ab3` (6,106 ms, a premise not proven within its
  bound). The suite by default: 194 jobs, none failed, 461.3 s wall, 3,974.9 s of job time; with `--usual`: 194 jobs,
  none failed, 384.0 s wall, 3,404.0 s (`runs/modal/kstep/final-usual2`; in `final-usual` before it `infer` failed, a
  test past its 5 s limit at 5,137 ms with the usual trees as certificates, a route nothing here touches: five runs
  each in one wave, 4bba0d2 one past it at 5,057.91 ms, this branch none, `runs/modal/kstep/infer-usual`).
  `research/cyclic/ksteps.ts` and `kstepfuzz.ts` time the budget rule's laws and the k-step fuzz's alone.
- Requests allowed (`proveProgress`, a liveness's helpful requests): `allowTranslated`, the usual allowed goal over the
  cells at t (rank (t, 2)), then BridgeRules.lean's `cycAOk` node (rank (t, 3)) carried from it by the request's
  equations. 26 of 26 translated in `last-default` (0.19.0: 8 left, all).
- A node after a step states its hypotheses as their conjuncts: a premise that is a conjunction of disjunctions,
  refuted against itself, was split case by case through every conjunct (scope grants' decision: not made in 47,216 ms,
  `runs/modal/cover/dbg1`; made in 5,497 ms, `dbg3`).
- Where no cyclic proof is made the usual trees are the certificate, checked by kernel.ts, and the proof is counted
  uncovered with why (`cyclic: {..., uncovered: true, why}`, core/cyclic.ts's `uncovered`); it no longer leaves the proof
  unchecked. A translation that fails is searched only with `GDP_CERT_SEARCH=1` (within `GDP_CERT_MS`), and a translated
  node's goals are grown within 4 s. The cross-check (`GDP_CYCLIC=1`) searches within `GDP_CERT_MS` too, and counts a
  proof it makes no cyclic proof for there uncovered, not differing; a history's record goals are part of the cyclic
  route's verdict (a broken history, its plain machine's laws proven, read as differing: 20 jobs failed so in
  `runs/modal/cover/final-cyclic`), and a machine with flags at every key the usual route doesn't prove isn't searched
  (`pairs`' fuzz, its refused laws each searched up to 10 s, ran past its time there).
- Not covered still: laws reading a map at a key read from a map. Translated, the search tree's and the sheet's are not
  made within their budgets, about 200 s of job time between them (`runs/modal/cover/a3`), so they stay on the usual
  rule.
- The datatype search's budgets are counted in work, not wall time (kernel/prove.ts's `counted` and `clock`: the
  solver's rows read and made, each node's rows; core/data.ts's `dataRate`, 300 units a millisecond, above the 55 to 240
  the corpus's searches do on Modal, `runs/modal/cover/data4`'s data-cal), so a budget lets each do at least the work it
  did in wall time. Its verdicts are the same in a container of 2 vCPU and one of 1 (`runs/modal/cover/data4`: the same
  lines, reverse of reverse proven in each, in 29.6 s and 23.0 s), every frontier datatype shard 3 of 3. The suite's
  `data` job is split, the search tree's insertion its own job (`data-bst`).
- Simpler: `GDP_CYCLIC_STEP` and `GDP_CYCLIC_AFTER` (search-only) are gone, and the switches are listed in one place
  (core/cyclic.ts's header); one reader of `GDP_CERT` (`certMode`, which emit.ts's `cyclicCerts` is); in core/cyclic.ts
  one copy each of a law's keys and tuples, the fresh keys, the functions' facts, the step's update, the laws a node uses
  at a time, the map-cell walker and the loop that translates the usual trees (machines, recurrences, folds); the
  translate-then-search of the certificate and the cross-check shared (`cyclicOf`).
- The suite (194 jobs, one after the other, at this branch's last commit): by default 437.1 s wall and 4,156.9 s of job
  time, none failed (`runs/modal/cover/last-default`); with `--usual` 335.9 s and 3,590.2 s, none failed (`last-usual`);
  with `--cyclic` 537.9 s and 4,495.7 s, none failed, none differing (`last-cyclic`). An earlier run by default (190 jobs)
  had `infer`'s law that needs an invariant past its 5 s limit, 5,026.53 ms (`runs/modal/cover/final-default`); the same
  test ten times each in one wave: main (38019b6) 3,652.59 to 5,469.44 ms, two past the limit; this branch 3,751.85 to
  4,946.40 ms, none (`runs/modal/cover/infer10-main`, `infer10-branch`).

The cyclic certificate cheaper to check in Lean and to export: the cyclic export's text about a quarter to a half of
what it was, each item's usual proof made once and without a TypeScript certificate the export never read, and the
step laws a cyclic certificate covers no longer checked the usual way as well. Untrusted only: kernel/kernel.ts,
kernel/cyclic.ts and lean-kernel/*.lean unchanged.

- `lean-kernel/emit.ts`, a cyclic proof's text (`cycProofText`): each table once (`<id>_tabN`), each term column's term
  once (`<id>_termN`), each goal's table and tree once where two goals have the same (`<id>_goalN`), since a node's goals
  (its own, each use's premises and descent) share its hypotheses and so mostly their columns; a table only the columns
  Lean reads (`encode`'s `slim`: every row a leaf uses has a hint, and Lean computes only the hinted hypotheses' rows,
  Kernel.lean's `srcRows`, so a premise's table is a few columns, not every choice of the node's facts), a leaf's cell
  pairs only those its hints name; the data defs `noncomputable` where `decide +kernel` checks them (no code for Lean
  to compile; `def` with `native_decide`). The bytes a shard's file (`runs/modal/perf2/variant2`, `size1`): 0.81 to 0.92
  MB against 1.87 to 3.40 MB before (`authority` 197 KB against 2,278 KB, `tabs2`, `leanprof1`); the usual export's
  0.30 to 0.50 MB.
- What every law's and step law's check reads alike, proven once a machine: `<id>_factsIn` (the exported facts among the
  encoding's), and with no flag at every key `<id>_shape` and `<id>_terms` at no keys; each `cycMOk`, `cycKOk` and
  `cycAOk` theorem unfolds its check and reads those as true (`simp only`) before `decide +kernel`. Lean on shard 1 with
  only those checks kept (the rest `sorry`) takes the CPU time of none kept: 58.0 s and 57.8 s against 60.1 s
  (`runs/modal/perf2/variant3`).
- The export's usual proofs (`proveStepLawsOnce`): made once per `toLean` (an item exported the usual way after its
  cyclic certificate wasn't found reads the proof the search started from) and `quietly`, with no TypeScript certificate
  (the export makes its own from the usual trees; one made in `proveStepLaws` was never read: normal form's k-step law
  spent 60 s there before the export's own 10 s deadline). A translation's own bound is within the export's deadline
  (kernel/prove.ts's `withinDeadline`). `encode` finds each leaf's rows once (three passes read them).
  `GDP_LEAN_TIMES=1` prints each item's export time and each certificate tried.
- `kernel/prove.ts`: step laws the cyclic certificate covers aren't checked the usual way first (`checkStepLaws`, which
  read the laws' usual trees again, then the step laws'); it runs where no certificate is made, as a machine's laws'
  check does. `GDP_CYCLIC_PROF` lines are on the certificate's lines too (the made nodes' check timed apart).
- In one container, the same items exported with emit.ts at d04850c (the tables, the slim tables, the shared checks)
  and at 9431e00, each checked by Lean twice (`runs/modal/perf2/ab1`; 4 CPUs): shard 0 57.3, 54.1 s against 63.7, 60.0 s; shard 1 36.3,
  34.1 s against 80.8, 69.8 s; shard 2 42.0, 42.4 s against 70.9, 66.3 s; shard 3 71.7, 68.3 s against 80.7, 72.0 s.
  With main's tree at 9431e00 against this branch's whole tree in one container (`abtree1`, items as each tree's
  package check has them): shard 1 37.9, 36.5 s against 99.5, 97.6 s; shard 2 34.5, 39.8 s against 59.5, 57.6 s; shard 0
  71.5, 72.6 s against 93.4, 76.9 s; shard 3 81.2, 81.7 s against 74.1, 76.3 s (`scopes3` cyclic now, where 9431e00
  exported it the usual way past the deadline).
- The suites in one wave, one after the other, 9431e00 against this branch (`runs/modal/perf2/w2-base-default`,
  `w2-base-usual`, `w2-default`, `w2-usual`): by default 479.7 s wall and 4,132.9 s of job time (189 jobs) against
  438.4 s and 4,074.9 s (194 jobs; the 189 both have, 3,709.8 s), the 49 Lean jobs both have 1,334.0 s against 1,093.4
  s; with `--usual` 456.7 s and 3,562.6 s against 345.8 s and 3,617.6 s (the 189 both have, 3,205.1 s). None failed.
  Lean a package shard (`lean-items.sh`'s `lean`), by default against `--usual` in the same tree: 9431e00 103, 74, 71 s
  against 13, 20, 33 s; this branch 80, 25, 53 s against 22, 8, 17 s (shards 1 to 3; the shards' items aren't
  9431e00's: the datatype and rank tracks added some). The export: 34, 23, 41 s against 9, 10, 20 s; 33, 8, 16 s
  against 13, 6, 10 s. `lean-groups-0..3`: 39.2, 30.0, 32.0, 35.3 s against 11.0, 9.7, 19.8, 20.2 s.
- The certificates both runs made (`w2-base-default`, `w2-default`, matched by job, kind, name and occurrence): machines
  14,549, usual 41,307 ms and cyclic 58,131 ms (1.41x) against 36,608 and 53,055 ms (1.45x); recurrences 364, 1.89x
  against 1.96x; laws between 190, 2.99x against 2.77x; folds 7, 7.95x against 7.84x; step laws 427, usual 8,557 ms and
  cyclic 23,549 ms against 5,620 and 68,429 ms: a machine's step-law certificate now covers its step laws together, the
  ones 9431e00 left uncovered among them (k steps over a map, flags at every key), and where that fails each alone; two
  of normal form's (quantifiers) spend 60 s each and fall back (`fellBack` in its lines).
- Not done: a Lean shard is still 3.1x to 3.6x its usual export's (by default against `--usual` above), not 1.5x. With
  the text halved, Lean's time is the kernel's `decide +kernel` of `checkCyclic` (the premise and descent goals each
  read the node's whole hypotheses) and the elaboration of the goals' trees (trace.profiler with synchronous elaboration, `leanprof7`, `leanprof8`:
  `scopes3_check` 28.3 s, its two nodes 15.8 s and 19.7 s); a check one theorem a node, which Lean could check in
  parallel, made no difference (`ab3`, `ab4`). A step-law certificate checks the laws' nodes again (3,667 ms of 8,410 ms
  of its check in `tsprof2`); skipping them needs kernel/cyclic.ts to remember checked nodes, a trusted change left out.

## 0.19.0

The cyclic proof is the certificate by default. What the usual route proves becomes a cyclic proof from its own trees,
at about twice its cost where 0.18.0's search took three to seven times, and that proof is the certificate of every law
the instances cover (`GDP_CERT=usual`, `modal/run.py --usual`: the usual trees, as before); and Lean reads those certificates, each rule's theorem now also stated from the
cyclic proof through a bridge (BridgeRules.lean), so that the trusted base with them is the leaf check, the cyclic rule
and the bridges. The translation is untrusted only: kernel/kernel.ts and kernel/cyclic.ts are unchanged, and every fact
of a machine's is Bridge.lean's (`cycCanon`); the law at t is still the node `cycMOk` reads.

The suite at this release (189 jobs, one after the other): by default 485.5 s wall and 4,066.0 s of job time, none
failed (`runs/modal/flip/default`); with `--usual` 517.7 s and 3,653.4 s, one failed, `data`'s reverse of reverse not
found within its budget (`runs/modal/flip/usual`), which proves it, and reads no certificate, in five runs of five
(`runs/modal/flip/data5-usual`).

A user's proofs print nothing: the `cyclic: {...}` lines research/cyclic/ratios.ts reads come only with GDP_CYCLIC=1 or
GDP_CYCLIC_LOG=1 (modal/run.py sets it). scripts/smoke.sh checks the cyclic export of a machine with sets
(`cyc_qmachine_sound`) and, with `toLean`'s `cyclic: false`, the usual one.

- `core/translate.ts`: a usual goal's tree read over a cyclic node's goal. Each column of the usual goal is a linear
  form of the node's (`renamer`: a state variable s as s@[t − 1], a map's cell M[k] as M@[(t − 1) + k·Ω], a fresh key
  k# as k, a term column as its term substituted, a monomial as its factors'), each split the renamed split (one the
  node's path decides followed, not made again), each leaf's rows found again among the node's at the renamed path.
  Two cells the usual path has equal are cells over time here: their keys' difference (a − b)·Ω is split, each other
  side refuted by the product of a − b <= 0 with Ω >= 0 (`apart`). A step's write, read at a key K where the usual
  conclusion reads it at the write's key W, is decided K = W or apart first (`readsFirst`), the usual cells at W then
  read at K. A leaf whose rows still aren't there is closed on the node's goal (`close`: its rows solved, an open
  choice, two reads of a function or two cells over time split), grown by the prover only past that.
- The instances (`machineNodes`, `recurNodes`, `foldNodes`, given the usual proof; core/cyclic.ts's header has the
  shape): each law three nodes. At t (rank (t, 1)), its tree made, not searched (`carry`: the uses' and facts' guards
  decided, then each comparison of the law at t against the law it is carried from, a case where they differ refuted by
  the step's equations); after a step from t − 1 (rank (t, 0)), the usual step goal over the cells at t − 1, its
  conclusion as the step's facts have it, its tree the usual one's; at the start (rank (0, 0)), the usual start goal and
  tree. Only the facts and uses the usual tree reads are kept. A recurrence's lemmas and laws between and a fold's laws
  likewise (at the start, y = x, a leaf). Step laws are translated too (`proveStepLaws`): one step on any machine the
  instances cover, several on one with no map; each the step law's usual goal over the cells at t − k..t − 1 and the
  step law itself over the cells at t − k and t (`then`'s primed names at t), carried by the step's facts, reusing the
  laws' nodes. A proof made again (the same machine, laws and instances) is the one made and checked before.
- `GDP_CYCLIC_ROUTE` picks the cross-check's route: `translate` (the default; the search where there is no usual proof
  or the translation isn't proven), `search` (0.18.0's), `both` (each timed apart in the same process, both verdicts
  against the usual one). `GDP_CERT=cyclic`: every proof the instances cover gets the cyclic certificate (translated,
  searched where that fails) and the verdict is its kernel check's; the usual trees are its input, not checked again.
  The default stays the usual certificate. `research/cyclic/jobs.ts` makes the suite's job list under such settings;
  `research/cyclic/ratios.ts` prints the routes, the leaves grown again and the proofs no instance covers, by why.
- In the same run (`runs/modal/cyctrans/both7`, the suite with `--cyclic`, `GDP_CYCLIC_ROUTE=both`, `GDP_CYCLIC_LAX=1`,
  none differing either way), the usual route against the translation against the search, over the proofs the usual
  route proved: machines 3,780 proofs, 15,165 ms, 30,487 ms (2.01x), 48,921 ms (3.23x); the normalized scope 4 proofs,
  2,941 ms, 1,488 ms (0.51x), 31,425 ms (10.69x); recurrences 364, 1,945 ms, 3,422 ms (1.76x), 6,170 ms (3.17x); laws
  between 190, 523 ms, 1,768 ms (3.38x), 3,899 ms (7.46x); folds 7, 123 ms, 912 ms (7.41x), 1,420 ms (11.54x); step
  laws (no search to compare) 516, 12,747 ms, 33,532 ms (2.63x). Fell back to the search: none (machines, recurrences,
  folds and step laws all translated where the usual route proved them; 102 machine, 3 recurrence, 2 between and 9
  fold comparisons the usual route didn't prove are searched, and none proven). Of 20,360 machine leaves translated, 49
  were grown again by the prover; of 1,526 recurrence leaves 19; one machine's node at t was grown, not made. 2,644 of
  the 3,780 machine proofs were ones made before.
- `GDP_CERT=cyclic` on the whole suite (`runs/modal/cyctrans/cert3`, 189 jobs, none failed): 3,671.2 s of job time
  against 3,520.4 s plain in the same wave (`plain3`); its certificates: machines 4,000 at 32,172 ms against 15,646 ms
  for their usual proofs, step laws 516 at 33,111 ms against 12,686 ms, recurrences 364 at 3,334 ms against 1,952 ms,
  laws between 190 at 1,606 ms against 557 ms, folds 7 at 1,060 ms against 135 ms.
- Not covered (`both7`, comparisons printed by the cross-check, a rule proven several times counted each time):
  machines with a history (26,551), with a flag that holds at every key (419), with a law reading a map at a key read
  from a map (10); step laws on those machines (88 at every key, 13 with a history); k-step laws over a map (357 of 2
  steps, 263 of 3) or a flag at every key (14); liveness (27) and loops (67), claims about runs that never end; progress
  (8, a request allowed). A k-step law over a map would need the map's cells at each step's time, which the usual
  frames don't name.
- CHC-COMP's LIA-Lin track (the prover is unchanged): 369 solved (225 sat, 144 unsat), none wrongly, 7 out of time
  (`runs/modal/cyctrans/chc`), against 0.18.0's 367 (`runs/modal/cycspeed/chc-mine`).
- The suite (`modal/suite.json`, 189 jobs): plain 452.5 s wall, 3,520.4 s of job time, none failed (`plain3`); with
  `--cyclic` (the translation the default route, every differing verdict failing its job) 465.9 s wall, 3,650.0 s, none
  failed, none differing (`cyc3`); with `GDP_CERT=cyclic` 457.0 s, 3,671.2 s, none failed (`cert3`).

- `lean-kernel/BridgeRules.lean` (trusted, on top of Bridge.lean, Refine.lean and History.lean; the standard axioms only,
  no `sorry`): the rules beside a machine's laws carried by cyclic proofs, each to the statement its usual theorem
  makes. `cyc_kstep_sound`: a node over the run's last k steps up to t (the first state at t − k, the j-th request at
  its time, `then`'s primed names at t; times one step back at a time or t − n at once) checked by `cycKOk` gives
  `SKStepHolds`, step laws and k-step laws; the run a reachable state ends is extended by the k requests (`run_ext`).
  `cyc_allow_sound`: a helpful request allowed (`AllowHolds`) as a node at the run's last request, which no step takes.
  From those, with the claims' meaning in place of their certificates: liveness (`sleads_of_holds`) and weak fairness
  (`sleads_wf_of_holds`), a history's laws through its plain machine (`hreach_plain`, the record goals leaf goals still),
  a ghosted machine's ghost-free laws of the original (`cyc_ghost_holds`), refinements (`srefines_of_holds`). Flags
  that hold at every key: the machine read as its sk machine (`SMachine.sk`, each such flag and its witnesses inputs a
  request names), whose runs with every request decided as a goal reads it are the machine's off the witnesses
  (`sk_step`, `sk_run`), the flags' closing conditions facts of the encoding (`cycQFacts`, true on those runs through
  Sets.lean's `closing_true`); `cyc_qmachine_sound`, `cyc_qkstep_sound`, `cyc_qallow_sound`. Live.lean's `lexLtC` and
  `falseC` are `rankLtC` and `noneC` (Cyclic.lean defines the same two, and a file may now import both).
- The Lean export from cyclic certificates (`GDP_CERT=cyclic`, or `toLean`'s `cyclic`; `modal/run.py --cert`): each
  machine the cyclic route covers (its laws, step laws, k-step laws, history, ghosts, liveness, a loop's, a refinement's
  composite, a recurrence's machine) and each fold from one cyclic proof: the laws' nodes translated, step laws'
  translated where the node is the one `cycKOk` reads (else searched, core/cyclic.ts's `stepLawNodes`), each helpful
  request allowed a node (`allowNode`), flags at every key through `skMachine`. Every theorem is stated as the usual
  export states it: the machine and its claims numbered alike (`machineNames`), `<id>.lawN`, `<id>_stepN_holds`,
  `<id>_liveN_holds(_wf)`, `<id>_halts` and the definitions they name the same text; `research/cyclic/exports.ts`
  compares two exports. lean-kernel/README.md has the inventory: each rule kernel.ts trusts, its usual Lean theorem, and
  the cyclic proof and bridge that cover it.
- The package check both ways in the same run (`runs/modal/cycexport/pkg4`, 4 CPUs a job): of its 65 sharded items 63
  exported from cyclic certificates (21 machines' step laws translated), 2 the usual way (`normalform`'s two-step law
  and `childuse`'s, not found by the search); every user-facing statement the same (228 verbatim, 84 the same up to the
  laws read as a list where the usual export reads its proof's entries), none differing, none missing, the 139
  definitions they name the same; every item checks in Lean. Lean time a shard, usual against cyclic: 25 s against
  79 s, 14 s against 113 s, 19 s against 71 s, 30 s against 150 s; the export 30, 10, 10, 21 s against 210, 45, 24, 76
  s. The resource groups (`groups0..3`): 2 of 4 cyclic, Lean 8, 5, 8, 5 s against 4, 5, 4, 9 s, their export 489 to
  588 s against 11 to 18 s. The tables of nodes (`searchtree`, `sheet`) stay usual (the builder's `cyclicMachine`).
  In the same run `lean-bridge` builds Bridge.lean and BridgeRules.lean (49.19 s, every theorem on `propext`,
  `Classical.choice`, `Quot.sound`), `lean-bridge-sweep` 3,854 checks, none failed (31.82 s), `lean-cyclic` and
  `lean-cycles` Lean 24 s and 22 s.
- Not covered: liveness's argument along infinite runs (Live.lean's `leads_view`: an existential over a run's times
  under fairness, which no node's conclusion, a condition at one environment, states); progress (in reach as an allowed
  request and the step from it, but `ProgressHolds` is over the FMMachine twin and toLean doesn't export it); a history's
  pruning (the runtimes'); laws reading a map at a key read from a map (the bridge takes them, the builder leaves them).
- The export's search has a deadline (`GDP_CERT_MS`, 10,000 ms by default, kernel/prove.ts's `withDeadline`): where no
  certificate is found within it the item is exported the usual way, `past the certificate's deadline` its why. In
  `final2-cert` the resource groups (`groups0..3`) are all exported the usual way, export 48, 28, 38, 25 s and Lean 11,
  8, 11, 8 s (against 429 to 576 s of export in `final-cert`, two of four then cyclic), and `scopes3` joins `normalform`
  and `childuse` the usual way (62 of the 65 package items cyclic); `GDP_CERT_MS=600000` gives the longer search back.
- `GDP_CERT=cyclic` covers more: a machine with a history through its plain machine (`historyMachine`; its laws and step
  laws translated, the record goals checked as the leaf goals they are), and with `GDP_CERT_SEARCH=1` (off by default:
  each search costs seconds) a machine with flags that hold at every key (`qflagNodes`), the step laws and k-step laws
  no translation covers (the laws' nodes, then `searchedStepNodes`: core/cyclic.ts's `stepLawNodes` over the sk machine
  with the flags' closing facts, which the Lean export now shares) and a request allowed whose claim is that alone
  (`allowNode`, its witnesses by `withWitness`), each within `GDP_CERT_MS`; where none is found the usual certificate
  stays and the proof is counted uncovered, its why saying so. The usual route does no more than before: what no
  instance covers is read only where a cyclic mode is on.
- Not covered, `GDP_CERT=cyclic` (`runs/modal/cycexport/final2-cert`, against `final-cert` before): machines 209 (a flag
  at every key 203, a law reading a map at a key read from a map 6; before 11,149, of them 10,944 with a history), step
  laws 93 (a flag at every key; before 103, 13 of them with a history), k-step laws 718 (2 steps over a map 402, 3
  steps over a map 300, a flag at every key 16), progress 8, liveness 27 and loops 67. With `GDP_CERT_SEARCH=1` as
  well (`final2-search`): machines 6 (a law reading a map at a key read from a map), step laws 19 and k-step laws 22
  (8 at every key, 14 of 2 steps over a map: no certificate found within 10,000 ms), progress 0, liveness 27 and loops
  67 (claims about runs that never end: their step laws and allowed requests are certified, the argument along an
  infinite run is kernel.ts's `livenessParts` and the loop's measure). The 35 certificate searches that found none keep
  the usual verdict (ratios.ts lists them as differing: usual proven, cyclic not found).
- `infer` against 0.18.0 (`7ab4750`) in the same wave, 10 runs each of `infer.test.ts`'s law that needs an invariant:
  main 3,380 to 4,677 ms, mean 4,110 ms, median 4,241 ms, none past the 5 s limit
  (`runs/modal/cycexport/infer10b-main`, kept beside the branch's); this branch 3,307 to 5,231 ms, mean 4,189 ms, median
  4,185 ms, one past it (`infer10b-branch`). An earlier wave had main past it once in 5 (5,078 ms). No slowdown the runs
  show; the test runs near its limit on both.
- The suite (`modal/suite.json`, 189 jobs) at this track's last commit, one after the other: plain 452.0 s wall,
  3,572.6 s of job time, none failed (`runs/modal/cycexport/final2-plain`); with `--cert` (`GDP_CERT=cyclic`, the Lean
  package jobs exporting from cyclic certificates) 475.8 s wall, 4,140.3 s of job time, none failed (`final2-cert`;
  6,269.0 s before the deadline, `final-cert`); with `--cert` and `GDP_CERT_SEARCH=1` 537.5 s wall, 4,528.4 s, none
  failed (`final2-search`).

## 0.18.0

Cycles found, not shaped: ranks, generalized lemmas and recursive datatypes found as cyclic proofs, which Lean now
carries back to the machines, recurrences, folds and datatypes they were made from; the cyclic route faster and agreeing
with the usual one everywhere, the usual route still the default. The suite (189 jobs) passes in 500.5 s wall and
3,818.4 s of job time at this release (`runs/modal/rel018-suite`).

- Recursive datatypes as values (`gdp-wired/data`, `core/data.ts`): declare a datatype by its constructors
  (`data('List', {nil: {}, cons: {head: nat, tail: self}})`, fields naturals or the datatype), functions over it by
  structural recursion (`define`, the recursion checked), laws about them (`law`), and `proveData` proves a law by a
  cyclic proof it finds, or refutes it with a value that breaks it. The encoding keeps the trusted kernel as it was:
  every natural is a value of each datatype, a value read through maps (its tag, fields and size; a constructor and a
  function of several arguments at their pairing), the definitions, constructors, shape, eta and congruence as facts.
  The search picks the induction (structural on an argument, or a function's own recursion), splits the law into a
  node per case (a decision tree over the guards 240 random values disagree on) each with what its case needs
  (definitions unfolded, also where an argument equals a constructor's value; the congruences a proof-producing
  congruence closure explains in each model), and where the law alone isn't proven finds lemmas from the values
  (equations up to six symbols, predicates a function keeps), proves them the same way and uses them where the goal's
  reads match. `research/frontier`'s new datatype track: 11 of 12 laws proven where the library proved none (the
  prover alone on the unfolded law, and `findCycles` on the same facts with the maps' values on the codes), each in
  0.23 to 45.1 s, the 5 broken variants refused by both (`runs/modal/cycdata/suite2`): length of append and of map,
  append associative, map fusion for any f and g, mirror twice and the size of a mirror, the count and length after a
  sorted insertion, sorted insertion keeping a list sorted (two unfoldings), reverse of reverse (lemma found:
  `reverse(append(xs, [n])) = n :: reverse(xs)`), the sum of a flattened tree (lemma found: the sum of an append). Not
  proven: a search tree's insertion keeping its order (its two lemmas are found and proven, the law with them is not).
  `findCycles` doesn't take these laws: a list's code squares with each item, so its runs give it no edge.
- `lean-kernel/Data.lean` (on top of `Cyclic.lean`, nothing trusted beyond `cyclic_sound`; the standard axioms only):
  the pairing (a + b)² + b injective with a left inverse, a bijection between the naturals and pairs (`cun`, `cpair`),
  tuples. `lean-kernel/data.ts` exports each datatype proof as a theorem about the datatype as declared: the datatypes
  as Lean `inductive`s, the functions by pattern matching, a bijection between each datatype and the naturals, the
  model of every map, every fact of the proof proven true of it, and the law about the definitions
  (`datarev.reverse_reverse (xs : List) : reverse (reverse xs) = xs`). All 11 proven laws check
  (the suite's `lean-data-0..3`, 34.6 to 72.4 s a shard of up to three, `runs/modal/cycdata/suite2`). The suite
  (189 jobs) passes, 3,937.3 s of job time (`runs/modal/cycdata/suite2`).
- Reachability through a structure that changes is still out (research/frontier/README.md says why: a heap a rule
  rewrites is no value, and reachability there is an existential over paths with a frame lemma inside the induction
  over steps, which no cyclic instance builds).

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
- The encoding was sound as it stood, with no change to `core/cyclic.ts` needed: Ω only needs to be above the run's length (the
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
- The cyclic route faster, and no verdict apart from the usual route's: the three that differed (`running statistics`
  twice, the lists example's normalized scope) are proven as cyclic proofs. Untrusted only: the kernel, its Lean twin
  and Bridge.lean are unchanged, and every instance's facts are Bridge.lean's (`cycCanon`).
  - Each law of a machine is two nodes: at time t (rank (t, 1)), as before, and after a step from t − 1 (rank (t, 0)),
    the law read at the state the step gives over the run's cells at t − 1, using every law at t − 1 at the keys the
    machine's proof names. The second is the usual rule's step goal; the first carries it to the cells at t through the
    step's equations, the step's values opaque to its search (variables of their own, `widen` reading them back as the
    terms). A recurrence's lemmas and laws between (at x / after a step to x) and a fold's laws (at a node / from its
    children) likewise. Where the law after the step isn't proven, the law at t falls back to the one node whose goal is
    the whole step (a variant; the other then holds outright, its conclusion true).
  - Each goal is grown first on what it reads: a node keeps only the facts and uses its goal reaches (through the
    equations that give a cell it reads, a run's map read at any key one cell by its map and time), then is trimmed to
    those its tree reads; a weaker goal's tree is the whole goal's (`widen`, kernel/prove.ts: each row is a row of the
    whole). Where neither proves it within two seconds, the whole goal as before.
  - Two keys of a run's map (cells at u + k·Ω) are first compared as k = k', a linear atom; where the path has them
    equal the keys' difference is split and its other side refuted by (k − k')·Ω = 0, a product of the path's two atoms
    and Ω's sign row. The prover's leaf rows are kept by the path's decisions (a lift read every leaf of a subtree
    twice).
  - In the same run (`runs/modal/cycspeed/abA2`, the suite with `--cyclic` and `GDP_CYCLIC_LAX=1`, which prints a
    differing verdict instead of failing the job, this branch against main at 12ef6b1 in the same containers): machines
    4,683 proofs compared, 17,872 ms the usual way against 95,813 ms cyclic (5.36x; main 19,710 ms against 946,471 ms,
    48.02x, 12 differing, escalation and ladder past the prover's budget); without the normalized scope 15,238 ms
    against 57,645 ms (3.78x; main 44.03x), the normalized scope 2,634 ms against 38,168 ms; recurrences 1,747 ms
    against 5,489 ms (3.14x; main 8.84x); laws between 440 ms against 3,181 ms (7.23x; main 63.63x); folds 209 ms
    against 6,201 ms (29.67x; main 62.31x). The suite's job time with the cross-check: 2,569.4 s against 4,380.7 s. Not
    within twice the usual route, so the default prover stays the usual one; `research/cyclic/ratios.ts` prints these
    figures from a run.
  - CHC-COMP's LIA-Lin track (the prover's leaf rows are shared): 367 solved (224 sat, 143 unsat), none wrongly, 11 out
    of time (`runs/modal/cycspeed/chc-mine`), against main's 365 (222 sat, 143 unsat), none wrongly, 11 out of time
    (`chc-base`); one task main solved isn't (`llreve/break_merged_safe.c-1`, both at 58 s of 60), three it didn't are.
  - The suite (`modal/suite.json`, 180 jobs): 350.3 s wall and 2,443.9 s of job time, none failed
    (`runs/modal/cycspeed/final-plain`); with `--cyclic`, every differing verdict failing its job, 387.1 s wall and
    2,499.4 s, none failed, none differing (`final-cyclic`); `frontier-score` 54 / 54, `lean-bridge-sweep` 3,854 checks,
    none failed.
  - `GDP_CYCLIC_PROF=1` prints where each cyclic proof's time went, by goal kind; `GDP_CYCLIC_SLICE=0` grows every goal
    whole, `GDP_CYCLIC_STEP=0` states each law as one node (the encoding before).

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
