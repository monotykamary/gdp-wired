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

Modal, 2 vCPU, the search at 10 s (`--ms 10000`), each side its own job; base is 0.30.1's search
(`GDP_MULTI_MATCH=0 GDP_PAIRS=0`, the same as main 3cdf37e for these rules), cand this branch. `runs/protocols/r1`.

| Protocol | Search, nothing written | Written invariant, kernel only (base / cand) | Broken variant |
| --- | --- | --- | --- |
| lock_server_sync | unknown (60.3 s base, 78.8 s cand) | unknown 2.5 s / **proven 2.9 s** | refuted, 5 steps |
| lock_server_async | unknown (72.9 / 93.8 s) | unknown 8.2 s / **proven 26.8 s** | refuted, 21 steps |
| decentralized_lock | unknown (9.4 / 10.7 s) | unknown (9.2 / 8.8 s) | refuted, 19 steps |
| distributed_lock | unknown (169.4 / 143.9 s) | killed at 420 s | refuted, 23 steps |
| two_phase_commit | unknown (9.0 / 8.2 s) | proven 5.7 s both (local; r1's set had a typo, fixed) | refuted, 5 steps |
| ticket_lock | unknown (4.5 / 5.9 s) | proven 0.9 s both | refuted, 20 steps |
| toy_consensus_forall | unknown (33.1 / 34.5 s) | killed at 420 s | refuted, 18 steps |
| consensus_wo_decide | unknown (85.8 / 69.6 s) | killed at 420 s | **unknown** (search); a 15-step run by hand breaks it |
| ring_leader_election | unknown (13.9 / 12.8 s) | unknown (19.7 / 14.5 s) | **unknown** (search); a 6-step run by hand breaks it |
| sharded_key_value_store | killed at 240 s | killed at 420 s | refuted, 6 steps (local, 0.9 s) |

The cuts (local, an M-series Mac, the search at 10 s):

| Cut | base | cand |
| --- | --- | --- |
| lock_server_sync@one | proven 1.03 s, found `forall(k => semaphore.plus(Link.at(k)).atMost(1))` | proven 1.09 s, the same |
| lock_server_async@one | unknown, 3.8 s | **proven**, 3.8 s (6.2 s in a second run), 14 laws found |

The 14 laws lock_server_async@one's search finds, as it prints them, pasted back with the search off, prove it again
(7 over two keys x ≠ y, 7 over one). Three of them:

    r.law('every x, y with ¬(x = y): GrantMsg[x] + HoldsLock[y] <= 1', ({GrantMsg, HoldsLock}) => forall((x, y) => x.eq(y).not().implies(GrantMsg.at(x).n.plus(HoldsLock.at(y).n).atMost(1))))
    r.law('every x, y with ¬(x = y): GrantMsg[x] + GrantMsg[y] <= 1', ({GrantMsg}) => forall((x, y) => x.eq(y).not().implies(GrantMsg.at(x).n.plus(GrantMsg.at(y).n).atMost(1))))
    r.law('every k: serverHoldsLock + HoldsLock[k] <= 1', ({serverHoldsLock, HoldsLock}) => forall(k => serverHoldsLock.plus(HoldsLock.at(k).n).atMost(1)))

No verdict is wrong: nothing proven is false, and every broken variant is refused (8 with a run the search finds, 2
unknown, each with a run by hand that breaks it, replayed by `runs.ts`).

Wall time runs far past the search's 10 s: its budget is counted (kernel/prove.ts's clock), and on these rules the
counted clock runs slow (lock_server_sync's Houdini took 8.6 s of wall time for 124 counted ms locally). A budget of
10 s here is up to 170 s on Modal.

## Why each one is missed

| Class | Protocols | What is missing | The smallest change that closes it |
| --- | --- | --- | --- |
| A. Relations over two sorts | lock_server_sync, lock_server_async, decentralized, distributed, toy and wo_decide consensus, ring, sharded KV | The search's spaces: the state, the cells at one key, and (where a key is composed, N·x + y) the cells at x, y and N·x + y. An invariant about three keys (two nodes at one lock: `holds(a, l)`, `grant(b, l)`) is in none. The cuts show the same invariants at two keys are found. | The pair space over tuples of keys a composed key names (x, y, z with cells at N·x + z, N·y + z): the rows over the triples a state holds. The same code as the pair space; the cost is the cube of the keys held. |
| B. Disjunctive ∀∀ facts | ticket_lock (tickets of two waiting threads differ), 2PC (`go_commit` all or none), Gitea's distinct reviewers | The join is convex: `Ticket[x] ≠ Ticket[y]` is not a hull or a bound, and cubes are blocked only in the state space. When a model the kernel gives breaks a form at a pair it didn't instantiate ("outside"), the join stops. | Cubes in the pair space, with the comparisons of a map's cells at x and at y (M[x] < M[y], =, >) as literals: "never Pc[x] ≥ 1, Pc[y] ≥ 1, Ticket[x] = Ticket[y]". |
| C. The prover's instances for laws over several keys | lock_server_sync, lock_server_async (fixed here); decentralized (a 2-key law needed at the third skolem of a 3-key goal) | The tuples a law about several keys is assumed at. | Fixed for composed keys (below). For the third skolem: tuples placing any skolem anywhere, measured no-go (decentralized lock's written invariant went from 4 s, unknown, to over 300 s). |
| D. Cost with many laws over 3–5 keys | distributed lock, toy and wo_decide consensus, sharded KV (written invariant killed at 420 s) | Each law over k keys is assumed at many tuples; 5-key laws (sharded KV) multiply them. | Not small: per-sort instance pruning (a tuple only of keys of the law's own sorts) would need sorts on keys. |
| E. Refuting by runs | consensus_wo_decide, ring | Rules with maps are refuted by random runs only (bmc takes no maps): 15 coordinated steps, or a request naming one exact id (5, then 4), are not drawn. | Inputs drawn from the values the state holds (ids pending, nodes voted for) beside random ones. |

Counting is the idea behind A for the lock protocols: "one token among grant, hold, unlock and the server" is
Σ_n (grant + hold + unlock)(n, l) + server(l) = 1 per lock, a sum per row of a two-sort map. The kernel's sums are
over a whole map (Sums.lean), so a per-row sum is a trusted change, Lean first; it would also state TigerBeetle's
per-account sums in the real-world corpus.

## What changed in the search (this branch)

- **kernel/prove.ts `matched`:** a law about several keys whose body reads a map at keys that each name only some of
  its bound names (`Link[c1·N + s]`, `Link[c2·N + s]`) is assumed at the tuples two reads' matches bind together, as
  a fact about several keys already was (`withFacts`). Untrusted (instances only). It turns lock_server_sync's and
  lock_server_async's written invariants from unknown to proven. `GDP_MULTI_MATCH=0` turns it off.
- **core/infer.ts, the pair space over two plain keys:** where no key is composed but a law is about several keys,
  the join's pair space over two distinct keys x ≠ y (the cells at x and at y), keeping only forms that read both. It
  proves lock_server_async@one with nothing written. `GDP_PAIRS=0` turns it off. A found law over two keys is now
  printed as its builder call, and a cell of a map of yes/nos as its 0/1 term (`.n`); before, the source of a pair
  form was not code.
- **core/infer.ts `preimages`:** a flag that reads a quantified flag (2PC's `go1` reads `noGo`) no longer throws
  `unknown flag` and ends the join; the quantified flag reads as its 0/1 variable, as the kernel's goals read it.
