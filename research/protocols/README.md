# Distributed protocols: a pilot

Ten protocols from the DistAI and DuoAI benchmark suites, written by hand as gdp-wired rules (`models.ts`), each with
its safety property as a law, a broken variant, and the inductive invariant a person would write. `run.ts` proves the
safety law with nothing written (`proveRule`'s search), checks the written invariant with the search off, and refutes
the broken variant. Every figure below comes from `runs/protocols/` in the main checkout (gitignored).

    bun research/protocols/run.ts [--only id,...] [--ms 10000] [--skip given,broken]
    bun research/protocols/runs.ts    # the hand-written runs of two broken variants

## Sources and published results

The Ivy sources are DuoAI's (github.com/VeriGu/DuoAI, `protocols/<id>/<id>.ivy`), which collect DistAI's, I4's,
mypyvy's and Ivy's. The published times are DuoAI's Table 1 (Yao, Tao, Gu, Nieh, "DuoAI: Fast, Automated Inference of
Inductive Invariants for Verifying Distributed Protocols", OSDI 2022), in seconds, on a 28-core Xeon W-2175 at 4.3 GHz
with 62 GB, each tool allowed a week. The tools: DistAI (Yao et al., OSDI 2021), SWISS (Hance et al., NSDI 2021),
IC3PO (Goel and Sakallah, NFM 2021 and FMCAD 2021), FOL-IC3 (Koenig et al., PLDI 2020; the faster of its ∀-only and
default modes), UPDR (Karbyshev et al., CAV 2015), I4 (Ma et al., SOSP 2019). P-FOL-IC3 (Koenig et al., TACAS 2022)
is cited by DuoAI as concurrent work, not measured there; its own numbers are not used here.

| Protocol | Safety | DuoAI | SWISS | IC3PO | FOL-IC3 | DistAI | UPDR | I4 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| lock_server_sync | link(C1, S) ∧ link(C2, S) → C1 = C2 | 1.3 | 1.0 | 3.2 | 1.0 | 0.9 | 3.3 | 0.6 |
| lock_server_async | holds_lock(N1, L) ∧ holds_lock(N2, L) → N1 = N2 | 1.9 | 2625 | 5.6 | 4.8 | 1.1 | 4.4 | 8.7 |
| decentralized_lock | X ≠ Y → ¬(has_lock(X) ∧ has_lock(Y)) | 9.9 | 5.8 | 24.3 | 69.0 | 10.2 | 51.0 | 20.7 |
| distributed_lock | locked(E, N1) ∧ locked(E, N2) → N1 = N2 | 6.1 | timeout | 12856 | 1660 | 15.3 | 63568 | 195 |
| two_phase_commit | commit at one excludes abort anywhere, needs every yes; abort needs the flag | 1.5 | 9.1 | 4.7 | 4.8 | 2.0 | 9.4 | 10.2 |
| ticket_lock | pc3(T1) ∧ pc3(T2) → T1 = T2 | 23.9 | fail | 56.2 | 58.1 | timeout | 143 | fail |
| toy_consensus_forall | decided(V1) ∧ decided(V2) → V1 = V2 | 1.9 | 5.9 | 3.0 | 5.4 | 3.1 | 3.4 | 9.4 |
| consensus_wo_decide | leader(N1) ∧ leader(N2) → N1 = N2 | 3.9 | 26.1 | 160 | 24.8 | 8.5 | 24.8 | 27.5 |
| ring_leader_election | leader(X) ∧ leader(Y) → X = Y | 3.5 | 14.3 | memout | 10.8 | 2.9 | 103 | 5.3 |
| sharded_key_value_store | table(N1, K, V1) ∧ table(N2, K, V2) → N1 = N2 ∧ V1 = V2 | 1.9 | 7662 | 5.4 | 9.7 | 1.2 | 3.5 | error |

Left out: Paxos and its variants. They need ∃ in the invariant (DuoAI 60.4 s for Paxos, SWISS 16665 s, everyone else
fails), relations over four sorts (round, value, node, quorum), and quorums as a sort with an ∀∃ axiom; none of that
fits the encoding below without a front end.

## The encoding (what a mypyvy/Ivy front end would do)

- **Sorts and relations.** A sort is the naturals. A relation over one sort is a map of `bool` cells, a function into a
  sort a map of naturals (ticket lock's `m(t, K) := K = next` is one: `Ticket[t]`; distributed lock's `ep`). A relation
  over two sorts is one map at the key a·N + b, over three a·N² + b·N + c, with N = 64, so every sort but the first
  holds at most 64 elements (the encoding Casbin's link table uses in research/realworld/). The proofs are for any
  number of the first sort and at most 64 of the others.
- **The order of a pair.** A quantified flag (`everyKey`) reads its key only plainly (k, or k plus a term that doesn't
  read it), so a relation a flag ranges over is laid out with that sort last: toy consensus's `vote(N, V)` is
  `Vote[V·N + N]`, sharded KV's `owner(N, K)` is `Owner[K·N + N]`. A front end would pick the layout from the flags.
- **Actions.** Each action is a request (`op` and its parameters); its `require`s are one flag, and a request whose
  flag is false changes nothing (a stutter, which no safety property sees). Ivy's `require exists N. p(N)` is an input
  naming N (2PC's `go2`).
- **Init.** `after init` with free individuals (a start node, `first`, `e1`) takes them as params; one with an
  arbitrary relation (sharded KV's `owner`, Ivy assumes it functional) is a phase of `own` requests before `start`. An
  `init` request taken once, before any other action, sets what depends on the params.
- **Axioms.** A total order is ≤ on the naturals, its successor + 1 (ticket lock, distributed lock's epochs). A ring of
  `size` nodes is the positions 0..size − 1 with next(n) = n + 1 mod size (every finite ring is one). An injective
  function (`idn`) is a `fn` known only by its fact `idn(a) = idn(b) → a = b` (runs compute n XOR 5). Quorums: a quorum
  is a set the request carries, and Ivy's axiom that every two quorums meet is assumed of the request's quorum and the
  stored `voting_quorum`, at a node the request names (`w`, the axiom's witness). That allows more runs than Ivy's
  (quorums meet the stored one, not every other), so a proof here is a proof for Ivy's; the initial `voting_quorum`
  is set by an `init` request carrying any quorum.

Is the model the protocol? Up to the bound of 64 on all but the first sort, and the quorum over-approximation, yes:
every action is Ivy's with the same guards and writes, read side by side in `models.ts`. Not the protocol: the two
`@one` cuts below (one server, one lock), which rely on a symmetry argument gdp-wired does not prove.

## Results

Modal, 2 vCPU, the search at 10 s (`--ms 10000`), each configuration its own job:
(`GDP_PAIR_DISTINCT` and `GDP_JOIN_DROP` were b94e8a5's flags for the cubes; the merge branch has neither the flags nor
the cubes, so its default is mid's search plus STRUCTURE.md's model-based instances.)
- **base:** 0.30.1's search, `GDP_MULTI_MATCH=0 GDP_PAIRS=0 GDP_PAIR_DISTINCT=0 GDP_JOIN_DROP=0` (the same code paths as
  main 3cdf37e for these rules);
- **mid:** e83160e, the pair space over two plain keys and the multi-read matching (`GDP_PAIR_DISTINCT=0 GDP_JOIN_DROP=0`);
- **cand:** b94e8a5, with the cubes over two keys (below; tried, then dropped from the branch).

The search with nothing written is `runs/protocols/r2` (base, mid and cand side by side); the written invariants and
the broken variants of the 10 protocols are `runs/protocols/r1` (base against mid; the cubes change neither).

| Protocol | Search, nothing written (base / mid / cand) | Written invariant, kernel only (base / mid) | Broken variant |
| --- | --- | --- | --- |
| lock_server_sync | unknown 71.2 / 94.9 / 80.1 s | unknown 2.5 s / **proven 2.9 s** | refuted, 5 steps |
| lock_server_async | unknown 74.7 / 78.5 / 61.5 s | unknown 8.2 s / **proven 26.8 s** | refuted, 21 steps |
| decentralized_lock | unknown 9.6 / 10.6 / 10.1 s | unknown 9.2 / 8.8 s | refuted, 19 steps |
| distributed_lock | unknown 143.8 / 152.6 / 166.5 s | killed at 420 s | refuted, 23 steps |
| two_phase_commit | unknown 9.4 / 8.9 / 9.3 s | proven 5.7 s on both (local; r1's set had a typo, fixed) | refuted, 5 steps |
| ticket_lock | unknown 4.4 / 6.7 / 6.1 s | proven 0.9 s on both | refuted, 20 steps |
| toy_consensus_forall | unknown 30.0 / 33.4 / 33.0 s | killed at 420 s | refuted, 18 steps |
| consensus_wo_decide | unknown 60.1 / 69.0 / 60.0 s | killed at 420 s | **unknown** (search); a 15-step run by hand breaks it |
| ring_leader_election | unknown 13.2 / 12.3 / 12.7 s | unknown 19.7 / 14.5 s | **unknown** (search); a 6-step run by hand breaks it |
| sharded_key_value_store | killed at 240 s (cand; r1 base and mid too) | killed at 420 s | refuted, 6 steps (local, 0.9 s) |
| lock_server_sync@one (cut) | proven 1.7 / 1.5 / 1.8 s, found 1 law | | refuted, 3 steps |
| lock_server_async@one (cut) | unknown 3.7 s / **proven 4.9 s / proven 5.2 s**, found 14 laws | | refuted, 21 steps |

Lock_server_sync@one's search finds `forall(k => semaphore.plus(Link.at(k).n).atMost(1))`. Lock_server_async@one's
finds 14 laws (7 over two keys x ≠ y, 7 over one). Pasted back as printed, with the search off, they prove it again.
Three of them:

    r.law('every x, y with ¬(x = y): GrantMsg[x] + HoldsLock[y] <= 1', ({GrantMsg, HoldsLock}) => forall((x, y) => x.eq(y).not().implies(GrantMsg.at(x).n.plus(HoldsLock.at(y).n).atMost(1))))
    r.law('every x, y with ¬(x = y): GrantMsg[x] + GrantMsg[y] <= 1', ({GrantMsg}) => forall((x, y) => x.eq(y).not().implies(GrantMsg.at(x).n.plus(GrantMsg.at(y).n).atMost(1))))
    r.law('every k: serverHoldsLock + HoldsLock[k] <= 1', ({serverHoldsLock, HoldsLock}) => forall(k => serverHoldsLock.plus(HoldsLock.at(k).n).atMost(1)))

No verdict is wrong:
- nothing proven is false;
- every broken variant is refused: 8 with a run the search finds, and 2 unknown, each with a run by hand that breaks
  it (`runs.ts` replays both).

Wall time runs far past the search's 10 s. Its budget is counted (kernel/prove.ts's clock), and on these rules the
counted clock runs slow: lock_server_sync's Houdini took 8.6 s of wall time for 124 counted ms in a local trace. A
budget of 10 s here is up to 167 s on Modal.

**Against the published numbers:** DuoAI proves all ten in 1.3 to 23.9 s, and DistAI 9 of them in 0.9 to 15.3 s (it
times out on ticket lock). gdp-wired proves none of the ten protocols with nothing written, 4 of 10 from a written
invariant, and the two lock servers cut to one server. Their times are a 28-core workstation's with a week's limit;
ours are 2 vCPU on Modal with a 10 s counted search. The harnesses differ, and so do the models: ours bound every sort
but the first to 64 and over-approximate quorums.

## Why each one is missed

| Class | Protocols | What is missing | The smallest change that closes it |
| --- | --- | --- | --- |
| A. Relations over two sorts | lock_server_sync, lock_server_async, decentralized, distributed, toy and wo_decide consensus, ring, sharded KV | The search's spaces: the state, the cells at one key, and (where a key is composed, N·x + y) the cells at x, y and N·x + y. An invariant about three keys (two nodes at one lock: `holds(a, l)`, `grant(b, l)`) is in none. The cuts show the same invariants at two keys are found. | The pair space over tuples of keys a composed key names (x, y, z with cells at N·x + z, N·y + z): the rows over the triples a state holds. The same code as the pair space; the cost is the cube of the keys held. |
| B. Disjunctive ∀∀ facts | ticket_lock (tickets of two waiting threads differ), 2PC (`go_commit` all or none), Gitea's distinct reviewers | The join is convex: `Ticket[x] ≠ Ticket[y]` is not a hull or a bound, and cubes are blocked only in the state space. When a model the kernel gives breaks a form at a pair it didn't instantiate ("outside"), the join stops. | Cubes in the pair space with M[x] = M[y] as a literal: tried (below). inferLaws alone then proves ticket_lock; through proveRule the join still stops at an "outside" model, so nothing moves there. |
| C. The prover's instances for laws over several keys | lock_server_sync, lock_server_async (fixed here); decentralized (a 2-key law needed at the third skolem of a 3-key goal) | The tuples a law about several keys is assumed at. | Fixed for composed keys (below). For the third skolem: tuples placing any skolem anywhere, measured no-go (decentralized lock's written invariant went from 4 s, unknown, to over 300 s). |
| D. Cost with many laws over 3–5 keys | distributed lock, toy and wo_decide consensus, sharded KV (written invariant killed at 420 s) | Each law over k keys is assumed at many tuples; 5-key laws (sharded KV) multiply them. | Not small: per-sort instance pruning (a tuple only of keys of the law's own sorts) would need sorts on keys. |
| E. Refuting by runs | consensus_wo_decide, ring | Rules with maps are refuted by random runs only (bmc takes no maps): 15 coordinated steps, or a request naming one exact id (5, then 4), are not drawn. | Inputs drawn from the values the state holds (ids pending, nodes voted for) beside random ones. |

Counting is the idea behind A for the lock protocols: "one token among grant, hold, unlock and the server" is
Σ_n (grant + hold + unlock)(n, l) + server(l) = 1 per lock, a sum per row of a two-sort map. The kernel's sums are
over a whole map (Sums.lean), so a per-row sum is a trusted change, Lean first; it would also state TigerBeetle's
per-account sums in the real-world corpus.

## What changed in the search

- **kernel/prove.ts `matched`:** a law about several keys whose body reads a map at keys that each name only some of
  its bound names (`Link[c1·N + s]`, `Link[c2·N + s]`) is now assumed at the tuples two reads' matches bind together,
  as a fact about several keys already was (`withFacts`).
  - Untrusted: it chooses instances only.
  - It turns lock_server_sync's and lock_server_async's written invariants from unknown to proven.
  - `GDP_MULTI_MATCH=0` turns it off.
- **core/infer.ts, the pair space over two plain keys:** where no key is composed but a law is about several keys, the
  join gets a pair space over two distinct keys x ≠ y (the cells at x and at y), keeping only forms that read both.
  - It proves lock_server_async@one with nothing written.
  - A found law over two keys is now printed as its builder call, with a cell of a map of yes/nos as its 0/1 term
    (`.n`). Before, the source of a pair form was not code.
  - `GDP_PAIRS=0` turns it off.
- **core/infer.ts `preimages`:** a flag that reads a quantified flag (2PC's `go1` reads `noGo`) no longer throws
  `unknown flag` and ends the join. The quantified flag now reads as its 0/1 variable, as the kernel's goals read it.
- **core/infer.ts, cubes over two keys whose cells never agree (class B): tried and dropped.** b94e8a5 had it; the
  merge branch (gen/protocols-merge) removes its code and its flags, since it moved nothing through proveRule, here
  or with STRUCTURE.md's model-based instances (`runs/protocols/r3`, "on + cubes"). What it was, for the record:
  - **What it does:** where the join has no candidate for a counterexample, its pairs of keys x ≠ y with M[x] = M[y]
    become cubes. A cube is that equality plus the values there of the cells that take at most 3 values (a program
    counter, a yes/no), cut to as few of those as keep every sample's pair out. The kernel proves each as any form.
  - **Dropping forms:** a found form that nothing strengthens is now dropped, as Houdini drops one, where these cubes
    are searched.
  - **Printing:** a cube is printed as `forall((x, y) => x.eq(y).not().implies(all(...).not()))`.
  - **Flags (gone with it):** `GDP_PAIR_DISTINCT=0`, and `GDP_JOIN_DROP=0` for the dropping alone.
  - **inferLaws on ticket_lock alone:** proven in 3.9 s and 5.2 s locally. Mid's code and base's are unknown there
    (1.6 s and 0.6 s). It finds 10 laws, among them
    `never Pc[x] is 1 and Pc[y] is 1 and Ticket[x] <= Ticket[y] and Ticket[y] <= Ticket[x]` (two waiting threads
    hold different tickets) and `never 2 <= Pc[x] and 2 <= Pc[y]`.
  - **Through proveRule (the claim path):** no protocol moves; ticket_lock is still unknown, in 6.1 s on Modal.
    - The cause: proveRule first finds the law `∀k. Ticket[k] ≠ 0 → Ticket[k] < next` (core/fresh.ts) and hands it
      to inferLaws.
    - With that law in the set, the kernel's counterexample to the safety law is a state that breaks a set form at a
      pair of keys the kernel never instantiated ("outside").
    - The join gives up on such a state. That is the next gap: instantiate a set form at the keys of a model that
      breaks it, and ask again. STRUCTURE.md's model-based instances do that; with them the cubes still move nothing.
  - **Verdict:** a measured no-go on the claim path. No real-world law moves either (below). Dropped.

## The bar and the other benchmarks

Quick bars against 3cdf37e (dev sets, Modal, 60 s; 3cdf37e's shared baseline):

| | CHC-COMP LIA-Lin dev (662) | Real-world dev (91) |
| --- | --- | --- |
| base, three runs | 517, 518, 517 | 74, 74, 73 |
| e83160e (mid), `runs/bar/runs/e83160e71101-vs-3cdf37eddf65-quick-2026-10-280826` | 513: gained 1, lost 4, none in every run, 3 of the 4 lost answered only past 45 s | 74: nothing differs |
| b94e8a5 (cand), `runs/bar/runs/b94e8a5f20e8-vs-3cdf37eddf65-quick-2026-10-281018` | 515: gained 1 (FIREFLY_luke_2_e2_1375), lost 1 (HOLA/19.c, 2/4 against 6/6, at the limit), none in every run | 74: nothing differs |

Wrong is 0 in both bars. The real-world dev set holds the laws over two keys the round named:
- Gitea's "two counted approvals are never by the same reviewer";
- Casbin's roleManager #3;
- Keycloak's bruteForceProtector #0;
- TigerBeetle's transfers #0 to #7.

Each has the same verdict on both sides: no real-world law moves.

**nested8.c, lost 2 of 4 in the first bar,** replayed locally (M-series Mac, 60 s):
- base: sat by IMC in 4 of 5 runs (15 to 23 s);
- b94e8a5: sat in 4 of 8, including 3 of 3 with every change off and 1 of 2 with only `GDP_PAIRS=0`.

None of the changes runs on a CHC task. Instrumented, the rule has no maps, and no law has several keys. So these
flips are the IMC process's timing, not the search.

## Size, reuse, spend

- **Size (b94e8a5, with the cubes):** `core/` and `kernel/`, tests excluded, went from 2,387,735 to 2,393,564 bytes
  (+5,829). Without the cubes, and with the model-based instances, the merge branch's size is in CHANGELOG.md.
  - By diff lines: core/infer.ts +65 −14, kernel/prove.ts +14 −5, core/dsl.ts +2.
  - The new search was about 25 lines (the cubes over two keys, since dropped) and replaced nothing. The rest widens existing code:
    - the pair space's gate and places;
    - the matching;
    - the printer.
- **Reused:**
  - the join's pair space (Casbin's, for composed keys), its rows, levels and cube type (`Lit`, `cube`);
  - Houdini's dropping;
  - `withFacts`' partial-match idea for laws;
  - the kernel's quantified-flag variables (`?f`);
  - every proof is the kernel's, as before.
- **Could be shared:**
  - `matched` and `withFacts` now combine partial matches the same way, and could share one helper;
  - the state space's `blockCube` and the new pair cubes both block a cube relative to the samples, but only the
    state space's asks the kernel (IC3-style) before keeping one.
- **Spend:**
  - billed: r1 (40 jobs) $0.327, its pilot job $0.004, the first quick bar $1.067 plus $0.311 for the rw baseline runs
    it made;
  - r2 (34 jobs) $0.099 billed so far (its hour wasn't over);
  - the second bar: estimated $0.92 from task seconds, its hour not yet billed;
  - total billed $1.81, about $2.7 with the second bar's estimate.

## Round 2: the key's sort (gen/protocols2, from c4dff18)

STRUCTURE.md's plan: the key's sort, read off the rule, as the one organizing idea. Nothing trusted changed.
Figures are Modal, 2 vCPU, each configuration its own job (`runs/protocols2/p1` before the views, `p3` the branch
head 3929980; main checkout).

| Protocol | Search 10 s (c4dff18 → here) | Search 60 s (here) | Written invariant (c4dff18 → here) | Broken variant |
| --- | --- | --- | --- | --- |
| lock_server_sync | unknown → **proven 68.9 s** | **proven 70.5 s** | proven → proven 0.9 s | refuted, 5 steps |
| lock_server_async | unknown → unknown | **proven 100.8 s** (12 laws found) | proven → proven 12.2 s | refuted, 21 steps |
| decentralized_lock | unknown → unknown | unknown | killed at 420 s → **proven 3.5 s** | refuted, 19 steps |
| distributed_lock | unknown → unknown | unknown | killed → unknown 3.2 s | refuted, 23 steps |
| two_phase_commit | unknown → unknown | unknown | proven → proven 18.8 s | refuted, 5 steps |
| ticket_lock | unknown → unknown | unknown | proven → proven 0.8 s | refuted, 20 steps |
| toy_consensus_forall | unknown → unknown | unknown | killed → **proven 199.2 s** | refuted, 18 steps |
| consensus_wo_decide | unknown → unknown | unknown | killed → killed at 600 s | unknown; the hand run breaks it |
| ring_leader_election | unknown → unknown | unknown | proven 38.9 s → proven 2.1 s | unknown; the hand run breaks it |
| sharded_key_value_store | killed → killed (600 s) | killed | killed → killed (600 s) | refuted, 6 steps (locally, 3.0 s) |

With nothing written: **2 of 10 at 60 s, 1 of 10 at 10 s** (DuoAI: 10 of 10). Written invariants: 7 of 10 (5 at
c4dff18). Every broken variant is refused as before.

The c4dff18 column is `runs/protocols/r3`'s "on" (0d815ec, the same search as c4dff18's).

What changed, and what each bought:
- **Houdini's law watch counted as the tuples it evaluates** (core/infer.ts `lawful`: k^n per law about n keys).
  - Before, a law about three keys was counted as one evaluation, so Houdini ran 9 s of wall time for 114 counted
    ms. The wall-time stop then ended the search before the join started.
  - lock_server_sync's join then proves it in 3 queries, at 10 s.
- **Views by the key's sort** (core/infer.ts `keySorts`, `View`, `addView`).
  - **The pair space is one view.** A view is a few keys and the places they are read at.
  - **The pairs' places are sorted.** A row's maps go at x, a column's at y, the composed maps at the composed key,
    as a union-find over the places keys are read at says. Before, every map went at every place (ServerHoldsLock at a
    node, say).
  - **A view per caller law about several keys** that the pairs don't hold: three keys, two holders and their lock.
    Its places are the composed keys the law reads, and each map read at a plain key of a key's sort.
  - **Result:** lock_server_async's join finds the 12 laws a person writes, 3-key forms among them, at 60 s.
  - `GDP_VIEWS=0` turns the views off.
- **The prover's tuples cut by sort** (kernel/prove.ts `keySorted`).
  - **The rule:** a law's key read at a map takes only the terms its read matches against the keys the goal reads that
    map at. A function's argument is no sort.
  - **Instances:** lock_server_async's 3-key laws went from 157 tuples to 18.
  - **Written invariants:** decentralized lock's goes from 436 s to 3.5 s, ring's from 30.7 s to 2.1 s, and toy
    consensus's from killed to 199.2 s.
  - `GDP_SORTS=0` turns it off.
- **One retry loop for model-based instances** (kernel/prove.ts `withModels`; proveLaw, proveThinned and the join's
  stepWith). The later rounds together get 3 times the first round's work (at least a second's), and an unsettled
  later round gives back the first answer. One-key laws already at every value of their sort are skipped.
- **Step 0, the 5 s regression** (core/machine.ts `writeEvery`). This is the CI failure in core/sums.test.ts.
  - **The fix:** a write at every key with its key in key terms evaluates each breakpoint and one key per stretch
    between two. It used to evaluate every key below the last, up to a thousand keys a step for a token's `Bal.each`.
  - **The test:** 1.9 s to 0.95 s locally.
  - **The cause:** CI went from 3.45 s to 5.7 s because the runner was slower, about 1.7x on every test (the median
    over 80 tests above 300 ms). Locally the test took the same time at 3cdf37e and at every merge (1.9 s), and with
    `GDP_MODEL_INST=0` and `GDP_MULTI_MATCH=0`.
  - **Every default-limited test** is under 1.6 s locally (`bun test --timeout 1600`, both suites).

Why the rest are missed:
- **decentralized_lock.** The search's second pass, over the maps' sums, finds an inductive set:
  - `sum$HasLock + sum$Message <= 1`, `every k: HasLock[k] <= started`, and two more;
  - but the sum's cover goal for HasLock is false for a map of yes/nos. The model is a cell at 2: the cover goal knows
    no kinds.
  - Closing it is a trusted change, Lean first (Sums.lean's cover goal with the cells' kinds).
- **two_phase_commit.** The join stops on an "outside" model of the caller's law: the interpreter's state from the
  model breaks a set form at a key the goal doesn't hold.
- **ticket_lock.** Disjunctive facts (class B).
- **toy and wo_decide consensus, distributed lock.** Laws over 3 to 4 keys whose kernel goals cost too much (class D):
  - toy consensus's written invariant takes 199 s;
  - the views find forms, and their goals run out of budget.
- **sharded KV.** Laws over 5 keys. The instance lists run out of memory before the sort cut filters them, so the cut
  should make the tuples rather than filter them.

**Quick bars against c4dff18** (Modal; `runs/bar/runs/3929980a3167-vs-c4dff18b387a-quick-2026-10-281454`):
- **CHC-COMP dev:** 515 against 520, 516, 517. 4 gained and 3 lost, none in every run, all at the limit. CHC has no
  maps, so these are timing flips.
- **Real-world dev:** 73 against 74, 74, 74. One task differed in the first pass and was noise after 3 reruns a side
  (0 lost). Gitea's, Casbin's, Keycloak's and TigerBeetle's open laws are unchanged.
- **Wrong:** 0.
- **Casbin roleManager #3:** 2.0 s locally against 17.8 to 21.7 s.
- **The 1-vCPU group** (`runs/bar/runs/3929980a3167-vs-c4dff18b387a-full-2026-10-281504`): no job failed.
  - infer's tests are faster (the four-value join 5,001 ms median against 5,761).
  - Two of data's are slower on Modal: the ring of functions 5,459 against 4,657, and well-founded recursion 4,227
    against 3,779.
  - Locally those two take 1.81 and 1.51 s on both sides, so that is not reproduced.

**Size.**
- `core/` and `kernel/` without tests: 2,418,041 bytes against c4dff18's 2,402,284 (+15,757).
- By diff lines: core/infer.ts +213 −61, kernel/prove.ts +80 −42, core/machine.ts +10 −3.

**Reuse.**
- **Reused:**
  - the join's spaces, forms, levels and hull (a view is a space);
  - pairingOf's composition;
  - matchMany and eachRead (the sort cut);
  - keysOf (the watch's count);
  - breakKeys (the stretches).
- **Replaced:** the three model retry loops, now one.
- **New search:**
  - keySorts, about 70 lines;
  - addView and the law views, about 60;
  - keySorted, about 20;
  - withModels, about 20.
- **Could be shared:**
  - keySorts (the rule's union-find) and prove.ts's keySorted and modelInstances' sorts (the goal's matching) are two
    readings of one sort;
  - mapKeys and mapReads walk the goals twice.

**Spend.** No hour of this round's own was billed separately: the account's hours hold other tracks' bars too.
- **Pilots:** p1 5,516.6 s, p2 3,889.8 s and p3 3,845.1 s of job time, about $0.47 at 2 vCPU.
- **Quick bars:** about $1.04 each, two of them.
- **The 1-vCPU group:** $0.07.
- **Round total:** about $2.6 estimated.

## Class B: cubes in every view (gen/protocols3, from 2644102)

The base is 2644102: round 2, merged with gen/cdcl-cost, with growRoot's model-first step gated to goals that read map
cells or quantified flags. Three general changes to the join (core/infer.ts), nothing trusted:
- **Cubes blocked in every view** (`viewSpaces`, `viewCube`). This is the state space's IC3 cube blocking applied to
  each view's rows.
  - **The cube:** a counterexample's row that no sample's row is becomes a cube. Its literals are each few-valued cell
    at its value, each equality between two cells of one map that holds there (Ticket[x] = Ticket[y]: two `≤`
    literals, DuoAI's equality literals), and then the bounds that leave the samples' rows out.
  - **The check:** its negation is proven by the prover relative to the forms proven so far (then the whole set), at
    the instances the prover would read. Down then takes out the literals it doesn't need.
  - **The result:** a law at every tuple of the view's keys. It needs no protocol switch: every view takes part, and the
    equalities are those of each map's cells at two places.
- **A model's state is judged only at the cells it names.** No fresh key, and no cell the model leaves free; a map
  written at every key holds anything there. Round 3 tried this alone and it moved nothing (2PC). With the view cubes it
  is what lets the caller's counterexample reach them: ticket lock's was "outside" before.
- **A found form nothing strengthens is dropped** (as Houdini drops one). Before, the whole join stopped on it.

**ticket_lock is proven with nothing written.** The view cube found is the disjunction a hull can't say:
`every x, y with ¬(x = y): never Pc[x] is 1 and Pc[y] is 1 and Ticket[x] <= Ticket[y] and Ticket[y] <= Ticket[x]`
(two waiting threads hold different tickets). With it the join's cone is inductive: 18 laws, locally 44 s of wall time
at `--ms 60000`. On Modal (`runs/protocols3/q2`, 8219447):
- at 60 s, proven once (59.9 s) and unknown once (65.9 s), at the wall-time limit;
- at 120 s, proven twice (108.8 s, 120.6 s).

**Pilot** (b503155, before the proven-first frame; `runs/protocols3/q1`):
- **With nothing written:** lock_server_sync (10 s and 60 s), lock_server_async (60 s), and ticket_lock (60 s
  locally, half the time on Modal; 120 s on Modal). That is 3 of 10 at 60 s against round 2's 2.
- **Written invariants:** 8 of 10. Proven: sync, async, decentralized (2.6 s), 2PC, ticket, ring (2.9 s), toy
  consensus (200.8 s). distributed is unknown, and wo_decide and sharded are killed at 600 s.
- **Broken variants:** refused as before.

**What else it moves.** Nothing beyond ticket_lock:
- **The other protocols:** no other protocol's verdict changes.
- **Real world:** Gitea #0 (two counted approvals never by one reviewer) stays unknown locally (37.0 s; a model the
  search answers nothing to).
- **Quick bars** (b503155 against c4dff18, `runs/bar/runs/b503155fdfa7-vs-c4dff18b387a-quick-2026-10-281802`), wrong 0:
  - CHC dev: 520 against 520, 516, 517 (5 gained and 2 lost, all at the limit, none in every run);
  - real-world dev: 74 against 74, 74, 74, nothing differs.
- **1-vCPU group** (8219447): no job failed. The infer test moves from 5,848 ms median to 5,456, and data's two tests
  from 5,166 to 5,500 and from 4,274 to 4,471 (both within their runs' spread).

**The merged sort reading (round 3) is not brought over.** Without the four-key cutoff it was larger than round 2's two
readings: kernel/prove.ts +6.7 kB against core/infer.ts −2.6 kB.

**Size.** 2,426,345 bytes against 2644102's 2,420,609: +5,736, all in core/infer.ts (+75 −16 lines).
- `viewSpaces` and `viewCube`: about 30 lines.
- The named-cells judgement: about 15.
- Parameterizing queryWith and down by view: 6.
- The drop: 3.

**Reused:** the state space's cube machinery (`queryWith`, `down`, `formOf`, `litHolds`, `inCube`), lawInstances for a
view cube's instances, and views' rows.

**Spend:** the pilot q1 3,936.4 s and q2 355.9 s of job time (about $0.15), the quick bar about $1.00, and the 1-vCPU
group $0.05. About $1.2 estimated; the hours aren't billed separately from other tracks.

## After the sums-kinds merge: cheaper whole-set queries, slim, the full bar (gen/protocols3)

The base is 9bb4842: class B merged with gen/sums-kinds, where Sums.lean's `sum_cells` lets a cover goal assume the
proven one-key laws about the summed cells.

**Standing** (Modal; `runs/protocols3/m1` on 9bb4842, `m2` on 02cec45; the code since then changes no verdict path):

| | 9bb4842 | 02cec45 (proven-first) |
| --- | --- | --- |
| Nothing written, 10 s | lock_server_sync | lock_server_sync |
| Nothing written, 60 s | sync, async, decentralized (15.5 s) | sync, async, decentralized (15.9 s), **ticket_lock (51.8 s)** |
| Written invariants | 8 of 10 | 8 of 10 (toy 182.4 s) |
| Broken variants | refused as before | refused as before |

That is 4 of 10 with nothing written at 60 s, and 1 of 10 at 10 s. The misses are unchanged on the merged tree:
two_phase_commit, distributed_lock, both consensus protocols and sharded KV. None is moved by a general change here.

**Whole-set queries cheaper (proven-first).** In the join's relative induction, before a goal is asked against the whole
candidate set (about 1,100 laws and 3,400 hypotheses for ticket_lock, 2–5 s a query), it is asked against its context and
the forms proven so far. A proof there is a proof with the whole set; a model there is followed by the whole set, as
before.
- **ticket_lock:** its search went from 44 s to 27 s locally, and it is proven at 60 s on Modal (51.8 s), where it was at
  the wall-time limit.
- **Tried and dropped:**
  - doubling the relative context: the path changes, and ticket is not proven;
  - halving the first search where a sums pass follows: lock_server_async is lost at 60 s;
  - giving the sums pass more of the budget: decentralized is still unknown at 10 s, because its second pass needs more
    than 10 s in all.

**Slim.**
- **Env switches removed:** `GDP_VIEWS`, `GDP_SORTS`, `GDP_MODEL_INST`, `GDP_MULTI_MATCH`, `GDP_PAIRS`,
  `GDP_MODEL_FIRST` and `GDP_MODEL_CORE`. No test or bar read them.
- **One walk:** a goal's keys and its keys per map are read in one walk (`mapReads`).
- **Tried and reverted:** gating the model-first step to withModels' rounds of keyed rules (9abcd25, reverted in
  f48ba21). In its quick bar CHC dev was 514 against 520, 516, 517, with dillig17 unknown in 3 of 4 runs where 291a126
  solved it.

**The full bar** (gen/protocols3 = 39dfed6, the same code as now, against c4dff18;
`runs/bar/runs/39dfed6c3814-vs-c4dff18b387a-full-2026-10-281853`). Wrong is 0 everywhere and nothing is lost in every
run anywhere.

| Group | Candidate | c4dff18's three runs | Changes |
| --- | --- | --- | --- |
| CHC | 1,168 | 1,165, 1,161, 1,165 | 1 gained, 3 lost, none solid |
| ITS | 1,150 | 1,150–1,152 | |
| ITS per component | 1,157 | 1,153–1,156 | |
| SV | 246 | 246 | |
| SV per component | 216 | 214–216 | |
| TIP | 213 | 213 | |
| Frontier corpus, round 1 | 90 | 90 | |
| Frontier corpus, round 2 | 31 | 31–32 | one flip, noise |
| Real-world corpus | 274 | 273 | oidc refreshTokenRotation #0 gained, 4/4 against 3/6 |
| 332 step goals | 332 | 332 | |
| Suites | all pass | | |
| Lean | 48 of 48 checked | | |

**Speed** (the same run):

| Measure | Candidate | c4dff18 | 3cdf37e (its shared baseline) |
| --- | --- | --- | --- |
| Suite, job seconds | 5,634.3 | 5,643.9, 5,798.3, 5,723.0 | 5,727.4, 5,816.3, 5,579.4 |
| Suite --usual, job seconds | 5,226.6 | 5,132.5, 5,172.8, 5,268.1 | 5,283.9, 5,125.4, 5,338.6 |
| Real-world, per-law time over the 310 laws in every run (sum) | 1,616.4 s | 1,646.1, 1,701.0, 1,694.8 s | 1,708.5, 1,632.6, 1,653.7 s |
| Real-world, median law | 797 ms | 793–860 ms | 791–815 ms |
| 332 step goals, search | 297.4 s | 296.6 s | |

- **The suites:** level.
- **The real world:** fastest of the seven runs.
- **The 1-vCPU medians:** infer's are faster. data's two slowest tests read slower in this batch (5,586 against 5,075 ms
  and 4,448 against 4,100). In the next batch (`9abcd25cbfc4-…-full-2026-10-281931`), c4dff18's own medians for the same
  two tests were 5,907 and 4,583 ms, so base runs swing by up to 16% from batch to batch. Instrumented, those tests call
  none of the prover helpers this round changed (instancesFor, modelInstances, the sort cut).

**Size.**
- 2,428,682 bytes: +26,398 against c4dff18 and +8,073 against 2644102.
- Of the +8,073: class B 5,736, gen/sums-kinds about 2.3 kB, proven-first +785, and the slim −743.

## Slim (gen/slim, from 57abcb2)

What the protocols bought was measured again where later work could have taken its place (Modal; the main checkout's
`runs/slim/gen-slim`):
- **growRoot's model-first step:** with it off, every verdict is as in m2 and m3, and decentralized lock's written
  invariant is proven in 3.0 s (the sort cut made its step goal small). Taken out.
- **The model-based instances:** with them off, ring's written invariant goes from proven to unknown. Kept.
- **The final tree** (`final`): 4 of 10 with nothing written at 60 s (sync 90.0 s, async 101.1 s, decentralized
  16.6 s, ticket 57.4 s), 1 of 10 at 10 s (sync), and the same seven written invariants proven: sync, async,
  decentralized, 2PC, ticket, toy (234.3 s) and ring. Distributed is unknown, and wo_decide and sharded are killed at
  600 s. Every broken variant is refused as before. (m2 and m3 prove the same seven written invariants; the "8 of 10"
  above counts one too many.)


## Cost (gen/cost, from 4f7c7a6)

COST.md measures where class D's time goes and the first step. Three changes followed (CHANGELOG.md): the random runs
reading a law at its own keys under a counted cap, distributed_lock's written invariant completed, and decisions at the
simplex's point on the proof path. Figures are Modal, 2 vCPU, three runs a side (the gen/cost worktree's
`runs/cost/s3-off` and `s3-on`).

| | 4f7c7a6 | gen/cost |
| --- | --- | --- |
| Nothing written, 10 s | lock_server_sync (72.2 s) | lock_server_sync (6.8–7.8 s) |
| Nothing written, 60 s | sync 109.7 s, async 86.9 s, decentralized 11.8 s, ticket 48.9 s | sync 8.4–10.4 s, async 14.0–21.5 s, decentralized 8.0–11.8 s, ticket 59.3–60.0 s |
| Written invariants | 7 of 10 (toy 211.7 s) | **8 of 10**: distributed_lock's set completed (a fix to our model, 12.9–14.2 s), toy 12.3–16.0 s |
| The searches that miss | distributed 202.0 s; sharded KV killed at 540 s | distributed 25.5–30.8 s; sharded KV ends, 46.6–49.9 s |
| Broken variants | refused as before | refused by the same runs, faster (distributed 21.7 to 1.1–1.4 s) |

Still missed with nothing written: two_phase_commit, distributed_lock, toy_consensus_forall, consensus_wo_decide,
sharded_key_value_store and ring_leader_election. Their searches now end with "found nothing" well inside their budgets:
the misses are the search's own, not its cost. consensus_wo_decide's and sharded KV's written invariants are still
unknown at 150 s (COST.md: one goal each, an elimination blow-up for sharded KV).

## The key's domain (gen/gaps, from e7eab01)

Two of the six misses, two_phase_commit and ring_leader_election, have written invariants the kernel proves in seconds
(COST.md: 14.2 s and 2.6 s), and searches that end with "found nothing". This round diagnosed both against their
written invariants and closed 2PC with three general changes to the join (core/infer.ts). Nothing trusted changed, and
nothing in kernel/.

### two_phase_commit: a law about the keys below `size`

**Where the join stopped.** At 60 s, e7eab01's join ends on "target none" for the safety law. The counterexample is
size 2, go_commit at both nodes, VoteYes[1] = 0, and a commit at node 0. The written law that rules it out is
`go_commit only after every yes` (a < size, b < size, GoCommit[a] → VoteYes[b]). Its one-key form,
`∀x < size. GoCommit[x] ≤ VoteYes[x]`, is in no view:
- **The cells' space reads every key a state holds, and a fresh one.** GoCommit is written at every key (go1's
  `each`), and VoteYes only below size, so at every key past size GoCommit[k] = 1 and VoteYes[k] = 0. The hull can't
  say the law there, since it is false there.
- **The pair space over two plain keys** has the frame x ≠ y alone; the law's own guards (a < size) were dropped,
  because a view's frame took only conditions on the keys alone.
- The other eight written laws are a hull's or a cube's of one or two keys, once the domain is the frame.

**Then two costs.** With the domain views in, the join's first relative-induction goal needed 7 forms, and its six
tries (two forms each) had gathered 6 of them; the whole set (324 forms) then ran out of its query budget, and the
join stopped "stuck". And the samples hold 3 commits in 3,000 samples, so the rows the hulls read (capped at 6,000)
held none: forms like `DecideCommit[x] ≤ 0` came up, and each took a round to drop.

**The changes, all general:**
- **The key's domain frames its views** (`keySorts`' `shape`, the law views). A caller law's guards on its keys may
  read the state and params beside them (k < size, j < next, k < 64). A domain that moves (one that reads the state or
  params) gets a view of its key alone: the cells of its sort at the keys in the domain. Two plain keys get their law's
  view with the domain in its frame, where before only the pair space's x ≠ y. A view of one key, or of two keys at
  their own places, prints as a builder call with its frame (`forall(x => x.lt(size).implies(...))`).
- **The relative induction's tries scale with the set**: until the context would hold a sixteenth of it (6 at least,
  as before). A small set (CHC's) is asked as before.
- **Rows alike but for their key are kept once** before the 6,000-row cap of the join's spaces (the cells' space and
  every view). The hull and the levels read only which rows there are, so the cap now holds more of the samples. The
  candidates and Houdini read the cells' rows as before: kept once there too, the forms they made differed, and two of
  the 1-vCPU infer tests ran 10 to 20% slower in two batches (`runs/bar/runs/9151e47562cc-…-290443`, `…-290500`).
- Also fixed: a guard on a cell of yes/nos printed `VoteNo.at(k).eq(0)`, which isn't code; it is `VoteNo.at(k).not()`.

**Measured, ablated one at a time** (Modal, 60 s, `runs/gaps/modal/p2` in this worktree's runs): without the domain
views, without the scaled tries, or without the distinct rows, 2PC is unknown. A fourth change, a re-asked goal
starting from its last proof's reads (IC3's frame reuse), moved nothing and was taken out.

**What it finds** (Modal, 60 s, 14 laws, three runs, 14.9 to 17.7 s): the domain law
`every x with x < size: GoCommit[x] <= VoteYes[x]`, `GoCommit[x] = GoCommit[y]` and `GoAbort[x] = GoAbort[y]` over two
keys, and ten one-key laws (`VoteNo[k] is 0 → DecideCommit[k] <= GoCommit[k]`, `1 <= VoteNo[k] → 1 <= abortFlag`, ...).
Pasted back, 13 of the 14 print as code; the fourteenth is core/fresh.ts's `∀k. Alive[k] ≠ 1 → Alive[k] < abortFlag`,
which has no builder call (as before), and without it the pasted set is not inductive.

### ring_leader_election: not closed, and why

The written invariant is Ivy's three laws: a leader's id is the largest; a node's own id pending at it is the
largest; an id pending past a node is above that node's (`btw(a, b, c) ∧ Pending[idn(a)·N + c] → idn(b) < idn(a)`).
The search proposes none of them, for four separate reasons:
- **A function of a key is no atom.** `idn(x)` is read by every law, and no space has it: a view's atoms are map cells.
- **A composed key whose part is a function of a key is no place.** `Pending[idn(x)·N + x]` is the cell the rule's
  `become_leader` reads; keySorts splits a composed key only into two names.
- **The ring order is a disjunction over three keys.** `btw` is three orders of a, b, c (positions mod size), each a
  cube with order literals between keys, and the only law with three keys is the one the search would have to invent:
  views come from the caller's laws, and the safety law has two.
- **The runs never elect a leader** (class E): every sample has Leader at 0, so the hulls say `Leader[k] <= 0` until
  the join's counterexamples undo it one form at a time.

Each is general in kind (DistAI's templates have functions of variables and a sort's order), but in this pilot and in
the real-world corpus only ring needs a function of a key and an order between keys: the corpus's functions (Keycloak's
`sec`, the queues' backoffs) are of values. By this track's rule it is not built. What would close it: a template view
over three keys of one sort whose atoms are the rule's own reads with its inputs replaced by the view's keys
(`Pending[idn(x)·N + y]`, `idn(x)`), with order literals between the keys in its cubes.

### Results

Modal, 2 vCPU, each configuration its own job (`runs/gaps/modal/p1` base against candidate, `p3` the branch head with
three runs where a search is near its limit):

| Protocol | Search 10 s | Search 60 s (e7eab01 → here) | Written invariant | Broken variant |
| --- | --- | --- | --- | --- |
| lock_server_sync | proven (3 of 3, 67–76 s) | proven 120.9 s → proven 92–98 s (3 of 3) | proven 0.9 s | refuted, 5 steps |
| lock_server_async | unknown | proven 108.1 s → proven 94–106 s (3 of 3) | proven 13.0 s | refuted, 21 steps |
| decentralized_lock | unknown | proven 15.2 s → proven 15.4–17.7 s (3 of 3) | proven 2.8 s | refuted, 19 steps |
| distributed_lock | unknown | unknown | unknown 3.5 s (as COST.md says, the written set lacks "nothing before init") | refuted, 23 steps |
| two_phase_commit | unknown | **unknown 12.9 s → proven 14.9–17.7 s (3 of 3)** | proven 15.3 s | refuted, 5 steps |
| ticket_lock | unknown | proven 60.1 s → **proven 30.2–35.0 s** (3 of 3) | proven 0.9 s | refuted, 20 steps |
| toy_consensus_forall | unknown | unknown | proven 185.7 s | refuted, 18 steps |
| consensus_wo_decide | unknown | unknown | killed at 570 s | unknown; the hand run breaks it |
| ring_leader_election | unknown | unknown | proven 2.5 s | unknown; the hand run breaks it |
| sharded_key_value_store | killed at 570 s | killed at 570 s | killed at 570 s | (not reached in the job) |

With nothing written: **5 of 10 at 60 s** (e7eab01: 4), 1 of 10 at 10 s. The same seven written invariants are
proven, and every broken variant is refused as before. Ticket lock, at e7eab01 proven at the 60 s wall-time stop, now
takes half of it: that is the scaled tries (without them, 56.0 s). The branch head (a7072ce, the distinct rows in the
join alone) again in `p4`: 2PC proven in 3 of 3 (17.0 to 18.3 s), sync, async, decentralized and ticket (33.3 s)
proven, toy and ring unknown, 2PC unknown at 10 s.

**What else it moves.** Nothing beyond 2PC. Gitea #0 ("two counted approvals are never by the same reviewer", whose
guards are i < j and j < next, a domain that moves) gets its views and stays unknown (three runs a side: 55.2 to
60.4 s against 52.1 to 56.6 s). TigerBeetle #0 to #7 keep their verdicts: 1,608 s against 1,596 s over three runs a
side (`runs/gaps/modal/rwc`, `rwb`). Casbin and Keycloak: the same verdicts in the full bar.

### The bars

**Quick bar** (9151e47, against e7eab01's three runs; `runs/bar/runs/ded1ea841fec-vs-e7eab01247e6-quick-2026-10-290424`):
CHC dev 520 against 522, 523, 516 (2 gained, 2 lost, none in every run, all past 45 s); real-world dev 74 against 74,
nothing differs; wrong 0.

**Full bar** (9151e47 against e7eab01 launched together, one run a side and three reruns of every differing task;
`runs/bar/runs/9151e47562cc-vs-e7eab01247e6-full-2026-10-290443`, and `…-290500` for the suite --usual, which the
first bar's budget guard stopped). Wrong 0 everywhere, nothing lost in every run anywhere.

| Group | Candidate | e7eab01 | Changes |
| --- | --- | --- | --- |
| CHC | 1,171 | 1,171 | 5 gained, 4 lost, none in every run (8 of the 9 answered past 45 s) |
| ITS | 1,152 | 1,151 | 2 gained |
| ITS per component | 1,154 | 1,157 | 1 lost (1 of 4 runs against 3 of 4, at the limit), none solid |
| SV, SV per component | 246, 216 | 246, 216 | |
| TIP | 213 | 213 | |
| Frontier corpora | 90, 31 | 90, 31 | |
| Real-world corpus | 289 / 33 / 8 | 289 / 33 / 8 | nothing differs |
| 332 step goals | 332 | 332 | |
| Suites | 225 of 225, --usual 225 of 225 | the same | |
| Lean | 48 of 48 | | |

The head a7072ce differs from 9151e47 only in where rows are kept once (the join alone, as above), which brings the
candidates and Houdini back to e7eab01's; it was not put through the full bar again (the round was past its budget).

**Speed:**
- suite job seconds 5,587 against 5,727, and --usual 5,215 against 5,217;
- the 332 goals' search 296.7 s against 291.6 s (the prover's goals; no code they run changed);
- the real world's per-law time over its 330 laws 1,608 s against 1,576 s (+2.0%, one run a side; the three-run reruns
  of TigerBeetle and Gitea above, +0.8%), median 800 ms against 770;
- the 1-vCPU medians of the head (`runs/bar/runs/a7072ce52841-vs-e7eab01247e6-full-2026-10-290512`): infer's three
  slowest 5,548 against 5,548 ms, 2,944 against 2,890 and 2,084 against 2,056; data's within 2%.

The CHC, ITS and SV changes are timing flips: CHC's rules have no maps, so no view, and their join's sets are small
enough that its tries are e7eab01's (six).

**Size.** core/ and kernel/ without tests: 2,469,184 bytes against e7eab01's 2,465,302 (+3,882), all in core/infer.ts
(+67 −21 lines): the domain views about 25 lines, the frame printer 15, the distinct rows 7, the tries 2, the yes/no
guard printing 5.

**Spend** (billed, `modal billing report`, this round's 77 apps): $16.8 by 05:00 UTC, about $10 of it the full bar.

## distributed_lock and toy_consensus_forall (gen/gaps2, from b118bf5): diagnosed, not closed

On b118bf5 both written invariants are proven (13.7 s and 14.0 s) and both searches end with nothing found. This round
diagnosed each against its written invariant, built the general changes the diagnosis pointed to, and measured them.
None closes either protocol at 60 s, and two of them lose a protocol, so **no code change is kept**. The changes are in
`gaps2.patch` (`git apply research/protocols/gaps2.patch`; core/infer.ts, +50 lines; `GDP_X_TPL=0`, `GDP_X_VAC=0`,
`GDP_X_POINT=1` and `GDP_X_QMS` are its research switches). Modal, 2 vCPU; `runs/g2/modal/` in the gen/gaps2 worktree.

### toy_consensus_forall: the law is found; its goal costs too much

**Where the join stops on b118bf5.** At round 1, "stuck unknown". The safety law's step goal is asked with nothing
assumed, and the prover finds neither a proof nor a model within the join's query budget (8,000 counted ms). It
finds the model at 32,000.

**Then three search gaps, each general:**
- **A model's request lost the maps it carries.** The join read a kernel model's request as its numbers alone, so
  toy's quorum `Q` was missing, the interpreter's step threw, and every model was "outside": the join stopped there.
  Fix: the request takes each carried map's cells the model names (`requestOf`). This holds for every rule whose
  requests carry a map: toy, consensus_wo_decide, any carried set.
- **A carried map was no sort.** keySorts skipped reads of a carried map, so `VotingQuorum`, written from `Q`, was a
  sort of its own and in no view. The written law `Decided[v] ∧ VotingQuorum[n] → Vote[v·N + n]` needs it at the
  pair's column. Fix: a carried map's key has its cells' sort.
- **"One vote per node" has three keys (two values, one node), and the caller's law has two.** Views came from the
  caller's laws, so no view had that shape. Fix: the template views of a composed key (DistAI's template), two rows at
  one column (N·x + z, N·y + z) and one row at two columns, where no caller law's view has that shape. The join then
  has `every x, y, z: Vote[64·x + z] + Vote[64·y + z] <= 1`.

**What stops it now** (first reading, corrected below: the goal is cheap on the proof path, so it is the join's query that costs)**.** With the three in, at 600 s and four
times the query budget, the safety law is proven at round 5 from four forms, among them the three-key template law.
The template law's own step goal then runs out of budget twice: 3.7 s with two forms assumed, 9.0 s with the whole
set, unknown. Only 8 rounds fit in 600 counted seconds (45.6 s of wall time). Deciding at the simplex's point in the
join's goals too (`atPoint`, which gen/cost put on the proof path) changes nothing here. The written invariant's
three-key law is proven on the proof path, so this is the prover's cost on a three-key goal in the join's queries
(kernel/prove.ts and cdcl.ts), outside the search.

### toy, again: why the join can't settle a goal the proof path proves in 0.3 s

The pruning agent's lead was right. The template law with "a vote means voted" is proven with the search off in 0.73 s
here. kernel/prove.ts's `proveLaw` proves the template law's own goal, with the safety law and two unrelated forms
assumed, in 0.32 to 0.38 s (`runs/g2/one.ts`). In the join that goal comes back unknown. Logged (`GDP_X_LOG`, Modal,
`runs/g2/modal/d4`–`d12` in the gen/gaps2 worktree), the causes stack up in this order:
1. **The forms.** The relative induction takes two forms a counterexample rules out, ranked by their coefficients.
   The plain `Vote[64·x + y] <= Voted[y]` was 12th of the 13 that rule it out. Ahead of it came pieces of the same law
   under control guards (`Voted[y] is 0 and Decided[x] is 0 → VotingQuorum[y] is 0 → Vote[64·x + y] <= 0`) and a
   `never` cube, all of one or no coefficient. Ranking by every value a form reads, its guards' among them
   (`GDP_X_RANK`), puts the plain bounds first, but `Vote <= started` ties with it and is taken.
2. **An unknown answer jumps to the whole set.** With two forms the goal has a model the query doesn't find, so the
   join asks the whole set next (178 forms, 12,234 hypotheses), which settles nothing. Widening first by every form
   the last counterexample's ruling list holds (`GDP_X_WIDEN`, 13 forms, the plain law among them, 1,177 hypotheses)
   doesn't settle it either.
3. **The query itself, the real block.** Forced to the plain law alone (`GDP_X_FORCE`, 571 hypotheses), the join's
   query is unknown at 1.3M of the kernel's work, and at 5.2M with four times the budget. The same goal grown once on
   lawInstances' tuples is proven in 1.34 s locally, and proveLaw proves it in 0.32 s. What differs:
   - **The budget.** The proof path gives a goal a second of the counted clock per hypothesis, 20 s at least. The
     join gives 8 s, a quarter of it to a model-only search first.
   - **The tuples.** The proof path tries thinned instances (those the triggers read) before the full ones. Trying
     them first in the join (`GDP_X_THIN`, `triggered` exported from kernel/prove.ts) didn't settle the goal.
   - **The simplex's point.** The proof path decides there; turned on in the join too (`GDP_X_POINT`), nothing changed.
   Asking the proof path itself when the join's query has no answer (`GDP_X_PROOF`) does settle these goals. It
   returns the safety law's models, which the join's own query never finds, but at 0.5 to 10 s a call it spends the
   60 s search's whole budget by the end of round 1. At 600 s the join gets to the template law and stops on an
   "outside" model.
4. **The kept-hull variant.** The join refines the pair view's control by VotingQuorum, Voted and Decided, which
   splits "a vote means voted" into pieces, one for each control state. Keeping the unrefined hull's forms beside the
   pieces (`GDP_X_WHOLE`) brings the plain law back into the set; it's still out-ranked (1 above).

So toy at 60 s needs the join's queries to cost what the proof path's do: about a tenth of the counted work per goal,
or a per-goal budget the 60 s search can afford many of. No change in core/infer.ts alone measured here gets there. Every
switch above is in `gaps2.patch`, and nothing is in the code; none was put through a bar, since nothing moved.

### distributed_lock: two shapes the search can't state

At 300 s and four times the query budget the join ends on "target none" for the safety law. The counterexample has
transfers at epoch 2 to nodes 1 and 2, node 1 locked at epoch 2 and Ep[2] = 0. An accept at node 2 locks epoch 2
twice. The written laws that rule it out are `Locked[e·N + a] → e ≤ Ep[a]` and `Transfer[e·N + a] ∧ e > Ep[a] →
Ep[b] < e`. The rest of the written set also needs `two live transfers are one`. The search lacks two things:
- **The key as a value.** The epoch e is the composed key's row, and the laws compare it with a cell (e ≤ Ep[a]).
  A view's atoms are cells. Its keys are not values the hull or a cube reads.
- **A law over four keys** (two epochs, two nodes). The only views of four keys come from a caller's law of four.
Both are general in kind (rounds and ballots are such keys), but both are large: key atoms widen every view of an
ordered sort, and a four-key view's rows grow as the fourth power of the keys. Neither is built.

### What the built changes did (Modal, 60 s, one run each)

| Protocol | b118bf5 | all four changes | without the template views | without the bound pruning |
| --- | --- | --- | --- | --- |
| lock_server_sync | proven 7.5 s | proven 8.9 s | proven 11.6 s | proven 12.1 s |
| lock_server_async | proven 20.2 s | proven 20.9 s | proven 20.0 s | proven 24.2 s |
| decentralized_lock | proven 11.7 s | **unknown 53.0 s** | proven 11.3 s | unknown 63.9 s |
| two_phase_commit | proven 14.4 s | **unknown 13.7 s** | unknown 16.0 s | proven 15.3 s |
| ticket_lock | proven 30.6 s | proven 34.2 s | proven 32.0 s | proven 30.3 s |
| toy, distributed, wo_decide, ring, sharded | unknown | unknown | unknown | unknown |

The fourth change was bound pruning: a form the kinds already imply (a yes/no's range, `Vote + Decided <= 2`) was
dropped from the set, taking toy's set from 210 forms to 131. It costs 2PC its proof, and the template views cost
decentralized lock its proof. Neither gains anything. The two carried-map fixes alone move nothing measured, so they
are not kept either; they are what toy and consensus_wo_decide would need first once their goals are cheap.

### ring_leader_election: left

A scan of every law with several keys in the real-world corpus (research/realworld/items) and both frontier corpora
looked for a function applied to a bound key, or an order (<, ≤) between two bound keys. It finds one: Gitea's
`i < j`, which only breaks the symmetry of a pair the law states both ways (x ≠ y would do). No law there needs a
function of a key or an order between keys (queue positions and ranks are values, not keys). By the plan, ring's
three-key template with order literals is not built.

**Spend** (billed, this round's apps): about $0.4.

## Enumeration (gen/enum2, from 383928a, merged with e537601's EPR path)

enum/DESIGN.md's first step, built into core/infer.ts: where the join ends with nothing found on a keyed rule with a
caller law over several keys, the views of every sub-template of the keys' sorts, every minimal cube of at most three
literals no sample row is in, and Houdini over them (CHANGELOG.md has the stage). Nothing trusted changed.

**toy_consensus_forall is proven with nothing written.** The nine laws found are the written invariant's three
(a vote means voted, one vote per node, the voting quorum voted for the decided value) and "nothing before init" for
each map, as cubes:

    every x, y with x <= 63 ∧ y < 64: never Voted[x] is 0 and 1 <= Vote[64·y + x]
    every x, y, z with x <= 63 ∧ y < 64 ∧ z < 64 ∧ ¬(y = z): never 1 <= Vote[64·y + x] and 1 <= Vote[64·z + x]
    every x, y with x <= 63 ∧ y < 64: never 1 <= VotingQuorum[x] and 1 <= Decided[y] and Vote[64·y + x] is 0

**Pilot** (Modal, 2 vCPU, three runs, e537601 launched beside; `runs/enum2/p4-cand` and `p3-base` in this worktree):

| Protocol | 60 s, candidate | 60 s, e537601 | 120 s, candidate | 120 s, e537601 |
| --- | --- | --- | --- | --- |
| toy_consensus_forall | **proven 3/3, 42–58 s** | unknown 12–13 s | **proven 3/3, 39–47 s** | unknown 12–13 s |
| lock_server_sync, lock_server_async, decentralized_lock, two_phase_commit, ticket_lock | proven 3/3 each | proven 3/3 each | proven 3/3 each | proven 3/3 each |
| distributed_lock, consensus_wo_decide, ring_leader_election, sharded_key_value_store | unknown | unknown | unknown | unknown |

Every broken variant is refused (or left unknown) as at e537601. Times of the five proven before: decentralized 15–19 s
against 15 s, ticket 35–40 s against 28–32 s (the stage doesn't run on ticket: its join is inductive; container noise),
the rest level. The misses' searches end within their limits (one sharded KV run of 122 s at 60 s, a stalled container:
its three reruns took 41–44 s).

**What it took** (each measured on toy or decentralized lock, Modal):
- **Carried maps** (gaps2's findings): a carried map's key has its cells' sort, so `VotingQuorum` is a node; a model's
  request carries the quorum it names, so the interpreter can step a kernel model.
- **The top value as "at least":** `VotingQuorum` is no yes/no kind; a model put 2 there, where cubes read `= 1`.
- **Implied cubes out:** the cube that restates the safety law cost as much as the safety law's own goal.
- **The kernel's clock, not the join's counted one:** the proof path's work counts 25 times faster on the join's clock.
- **The caller's law first, and its failure ends the stage:** decentralized lock's stage failed at once instead of in
  25 s, so the search over the maps' sums that proves it (core/dsl.ts) keeps its time; later rounds leave it 21 s.

**Bars** against e537601, together: quick (chc, rw) and full (`runs/bar/runs/enum2-quick`, `enum2-full` in the main
checkout). Wrong 0, nothing lost in every run; CHC 1,166 against 1,166 (4 gained, 4 lost, none solid, all past 45 s: CHC
has no maps, so the stage never runs), ITS +1 and level per component, SV level, TIP level, the frontier corpora and
the real-world corpus (289 / 33 / 8) level, the 332 step goals the same search (289.8 s against 287.8 s), the suite
225 of 225 (5,598 against 5,686 job seconds). Gitea #0 and TigerBeetle #0–#7, three runs a side: every verdict the same,
times within the runs' spread. The suite --usual and the Lean sample were stopped on both sides by the bar's budget
guard ($8.5), so they are not measured. Size: +11,714 bytes.

**Sharded KV, tried on gen/enum3 and not merged.** Keys of three parts (`Table[n·N² + k·N + v]`) read in keySorts and
the template (up to five keys) give 10 cubes. lawInstances then takes 15 s and the caller's goal 17,168 hypotheses before
a search starts: the instance count for many laws over 5 keys, the kernel's.

**Spend** (billed, this round's 88 apps): $13.0 by 13:00 UTC, the full bar about $9.9 of it, past the $12 budget by $1.
