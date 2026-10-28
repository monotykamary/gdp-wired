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
