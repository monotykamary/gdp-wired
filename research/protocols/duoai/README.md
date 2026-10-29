# DuoAI beside gdp-wired: the ten pilot protocols, measured

The protocols track (`../README.md`) compared gdp-wired with DuoAI's published Table 1: a 28-core Xeon, a week's limit,
figures from a paper. This directory runs DuoAI itself, in gdp-wired's harness: the same Modal container shape, the
same two limits (60 s and 10 s), three runs of every protocol and limit for both tools, so the gap is measured.

    modal run research/protocols/duoai/duoai.py --out runs/duoai/main            # DuoAI, run.py's shape (cpu=2.0)
    modal run research/protocols/duoai/duoai.py --out runs/duoai/hard --hard     # DuoAI, a hard cap of 2 CPUs
    modal run modal/run.py --jobs research/protocols/duoai/gdp-jobs.json --out runs/duoai/gdp     # gdp-wired
    python3 research/protocols/duoai/table.py runs/duoai/main runs/duoai/gdp runs/duoai/hard

Every figure below comes from `runs/duoai/` in this worktree (gitignored).

## The artifact

DuoAI (Yao, Tao, Gu, Nieh, OSDI 2022) is github.com/VeriGu/DuoAI. Its artifact has no Docker image: the README is an
install script (conda; a Python 2.7 environment with `pip install ms-ivy` for `ivy_check`; Python >= 3.8 with numpy,
scipy and pandas; `make` in `src-c/`; the path of `ivy_check` written into `src-c/InvRefiner.h`). Its predecessor DistAI
(Yao et al., OSDI 2021, github.com/VeriGu/DistAI, same group) ships a Docker image on Google Drive; it was not needed.

`duoai.py` follows the README on Ubuntu 20.04 (one of the three systems the README names), every version pinned:

| What | Version |
| --- | --- |
| DuoAI | `ecd37c4` (master, 2025-04-30): the paper-era `8ce5ecc` (2022-07-30) plus a sampler fix in `src-py/translate.py` and a LICENSE |
| Base image | `ubuntu:20.04@sha256:8feb4d8ca5354def3d8fce243717141ce31e2c428701f6682bd2fafe15388214` |
| Python 2 (Ivy) | 2.7.18 (`2.7.18-1~20.04.7`), pip 20.3.4 |
| Python 3 (DuoAI) | 3.8.10 (`3.8.10-0ubuntu1~20.04.18`); numpy 1.20.2, scipy 1.6.2, pandas 1.2.4 (the README's), python-dateutil 2.8.1, pytz 2021.1, six 1.16.0 |
| Ivy | ms-ivy 1.8.23 (2022-02-11, the last Python 2 release, before DuoAI's), wheel by sha256 `95a59388…ec426d`; pyparsing 2.1.4, ply 3.11, tarjan 0.2.3.2, pydot 1.4.2 |
| Z3 | 4.7.1, the one inside the ms-ivy wheel (`ivy.z3`) |
| C++ | g++ 9.4.0, `-O2 -std=c++17` (DuoAI's Makefile) |

Modal runs Python 3.11 beside it for its own runtime; DuoAI runs on 3.8. One change to the install: ms-ivy writes its ply
parse tables into its package directory on first use (its wheel has none), so in a fresh container the first
`ivy_check` calls, which DuoAI makes four at a time, race to write them (one re-check in the first batch read a
truncated table and failed with ply's `_tabversion` error). The image writes them once at build, as the first
`ivy_check` on an installed machine does. The first batch, run before this fix and with a re-check that picked the
wrong file (DuoAI's success signal doesn't say which of its processes won; its log does), was stopped part way; it is
kept in `runs/duoai/main-v1` and `hard-v1` and not used below. Its DuoAI verdicts agree with the batch below.

## How a run is measured

- **DuoAI.** A fresh copy of the artifact, `python DuoAI.py <protocol>` in a session of its own, the whole session
  killed at the limit (wall time). Its verdict is its own: proven when a refinement process wrote its success signal,
  which it does only after `ivy_check` (Ivy, then Z3) found the candidate set inductive with the safety property in it.
  Then, outside the timed window, every invariant file its log says it wrote is checked again with `ivy_check`, and the
  safety property is looked for verbatim in the last one (its answer). A run counts as proven below only if all three
  hold. Times: the wall time from the process's start to its exit (the figure compared), DuoAI's own "DuoAI runtime"
  (from its object's creation: the same less the interpreter's start, about 0.1 s), and the split at "All simulation
  processes finished" (translation and simulation, then enumeration and refinement). There is no per-run setup to
  leave out: nothing is compiled per protocol (the C++ is built once in the image) and Ivy compiles nothing ahead.
  Simulation is part of DuoAI's inference (it is data-driven), so the inference-only time is DuoAI's own runtime.
- **gdp-wired.** `bun research/protocols/run.ts --ms <limit> --only <id> --skip given,broken` at `b118bf5` (main),
  through `modal/run.py` (`gdp-jobs.json`), the earlier pilots' commands with the CPU count and time logged. Its verdict is `proveRule`'s:
  proven only with a certificate the kernel checked. Times: the job's wall time (the bun process, from `summary.tsv`)
  and the search's own (`ms` in run.ts's line). Its `--ms` is a counted budget, not wall time: every proven run ended
  within its limit in wall time too, but the unknowns at 10 s ran up to 30 s of wall time before giving up, which
  DuoAI, killed at 10 s, could not. A run counts as proven below only if it ended within the limit.
- **The machines.** Both on Modal, 4 GB, one container per run, each batch launched at once and the three within
  minutes of each other (07:59 to 08:03 UTC). `modal/run.py`'s shape is `cpu=2.0`, which Modal treats as a reservation
  a container may burst above (DuoAI's containers' CPU affinity held 18 CPUs). DuoAI runs nine
  sampler processes and four refinement processes in parallel, gdp-wired one thread of search; so DuoAI was also run
  with a hard cap of 2 CPUs (`cpu=(2, 2)`). gdp-wired's CPU time over wall time was about 1.3 (bun's own threads), under
  the cap, so a capped run of it would not differ. Modal's sandbox reports the CPU model as "unknown".

## The ten protocols

DuoAI's `protocols/` has all ten under the names models.ts uses, and they are the sources models.ts was written from:

| gdp-wired (models.ts) | DuoAI | Ivy's safety property (`invariant [1000000]`) | gdp-wired's safety law | Differences |
| --- | --- | --- | --- | --- |
| lock_server_sync | `protocols/lock_server_sync` | `link(C1, S) & link(C2, S) -> C1 = C2` | `Link[c1·N + s] ∧ Link[c2·N + s] → c1 = c2` | keys below N = 64 |
| lock_server_async | `protocols/lock_server_async` | `holds_lock(N1, L) & holds_lock(N2, L) -> N1 = N2` | the same over `HoldsLock[a·N + l]` | keys below 64 |
| decentralized_lock | `protocols/decentralized_lock` | `X ~= Y -> ~(has_lock(X) & has_lock(Y))` | `a ≠ b ∧ HasLock[a] → ¬HasLock[b]` | keys below 64 |
| distributed_lock | `protocols/distributed_lock` | `locked(E, N1) & locked(E, N2) -> N1 = N2` | the same over `Locked[e·N + a]` | nodes below 64; epochs (Ivy's total order) are naturals |
| two_phase_commit | `protocols/two_phase_commit` | `(decide_commit(N0) -> ~decide_abort(N1)) & (decide_commit(N0) -> vote_yes(N1)) & (decide_abort(N0) -> abort_flag)` | the same three conjuncts | nodes below `size` (Ivy's node sort is uninterpreted) |
| ticket_lock | `protocols/ticket_lock` | `pc3(T1) & pc3(T2) -> T1 = T2` | `Pc[a] = 2 ∧ Pc[b] = 2 → a = b` | Ivy's three pc relations are one counter (0, 1, 2); tickets are naturals |
| toy_consensus_forall | `protocols/toy_consensus_forall` | `decided(V1) & decided(V2) -> V1 = V2` | the same over `Decided` | values below 64 |
| consensus_wo_decide | `protocols/consensus_wo_decide` | `leader(N1) & leader(N2) -> N1 = N2` | the same over `Leader` | nodes below 64 |
| ring_leader_election | `protocols/ring_leader_election` | `leader(X) & leader(Y) -> X = Y` | the same, nodes below `size` | the ring is positions mod `size`; `idn` an injective function |
| sharded_key_value_store | `protocols/sharded_key_value_store` | `table(N1, K, V1) & table(N2, K, V2) -> N1 = N2 & V1 = V2` | the same over `Table[a·N² + k·N + v]` | every sort below 64 |

Each pair states the same property. The differences are in the models, as `../README.md` ("The encoding") says: every
sort but the first is bounded by 64 in gdp-wired's (the keys of a map), the quorum axiom of the two consensus protocols
is over-approximated (a proof there is a proof for Ivy's), and Ivy's arbitrary initial relations are phases of
requests. Ivy's models are over unbounded sorts and are what DuoAI proves.

## Results

Modal, 4 GB, one container per run, three runs of every cell, 180 runs (`runs/duoai/main`, `hard`, `gdp`). A cell is the runs proven within the limit, and the range of their wall times (the process's start to its
exit) over all three runs. DuoAI's misses are timeouts (killed at the limit, wall time 10.0 s); gdp-wired's are
unknowns (its search gave up; at 10 s it may run past the limit in wall time, as its budget is counted, and a run that
did is not counted as proven). Every DuoAI proof that finished was checked again by `ivy_check` outside the timed window
and passed, with the safety property in the file verbatim; every gdp-wired proof carries a certificate its kernel
checked.

| Protocol | Paper (DuoAI, 28 cores) | DuoAI 60 s | gdp-wired 60 s | DuoAI 10 s | gdp-wired 10 s | DuoAI 60 s, hard 2 CPUs | DuoAI 10 s, hard 2 CPUs |
| --- | --- | --- | --- | --- | --- | --- | --- |
| lock_server_sync | 1.3 s | 3/3, 2.6–4.5 s | 3/3, 7.5–8.8 s | 2/3, 3.3–10.0 s | 3/3, 6.0–7.4 s | 3/3, 5.1–6.6 s | 3/3, 6.1–7.7 s |
| lock_server_async | 1.9 s | 3/3, 3.2–4.9 s | 3/3, 19.3–22.3 s | 3/3, 2.9–5.8 s | 0/3, 9.1–12.0 s | 3/3, 6.4–8.0 s | 3/3, 5.4–7.9 s |
| decentralized_lock | 9.9 s | 3/3, 11.7–14.1 s | 3/3, 13.5–15.5 s | 0/3, 10.0–10.0 s | 0/3, 5.2–6.9 s | 3/3, 15.9–18.7 s | 0/3, 10.0–10.2 s |
| distributed_lock | 6.1 s | 3/3, 8.3–10.6 s | 0/3, 23.0–24.7 s | 3/3, 7.1–8.3 s | 0/3, 9.1–11.9 s | 3/3, 14.9–21.6 s | 0/3, 10.0–10.4 s |
| two_phase_commit | 1.5 s | 3/3, 2.0–2.9 s | 3/3, 13.5–19.0 s | 3/3, 2.0–3.8 s | 0/3, 9.9–10.2 s | 3/3, 2.3–5.1 s | 3/3, 1.7–5.8 s |
| ticket_lock | 23.9 s | 3/3, 23.5–25.0 s | 3/3, 32.0–34.8 s | 0/3, 10.0 s | 0/3, 6.8–9.4 s | 3/3, 40.3–45.5 s | 0/3, 10.0–10.2 s |
| toy_consensus_forall | 1.9 s | 3/3, 2.9–3.7 s | 0/3, 16.4–17.7 s | 3/3, 3.3–4.6 s | 0/3, 12.2–12.5 s | 3/3, 6.1–7.7 s | 3/3, 4.6–8.2 s |
| consensus_wo_decide | 3.9 s | 3/3, 5.1–5.5 s | 0/3, 35.4–38.0 s | 3/3, 5.0–5.3 s | 0/3, 25.3–27.0 s | 3/3, 9.2–10.0 s | 3/3, 7.0–9.2 s |
| ring_leader_election | 3.5 s | 3/3, 4.8–6.4 s | 0/3, 7.0–9.3 s | 3/3, 4.7–7.0 s | 0/3, 6.8–7.2 s | 3/3, 10.4–12.9 s | 1/3, 10.0–10.0 s |
| sharded_key_value_store | 1.9 s | 3/3, 3.1–4.7 s | 0/3, 47.1–48.4 s | 3/3, 3.0–3.5 s | 0/3, 21.6–30.4 s | 3/3, 6.8–8.1 s | 3/3, 5.1–7.3 s |

| | DuoAI (`cpu=2.0`, as run.py) | DuoAI (hard 2 CPUs) | gdp-wired |
| --- | --- | --- | --- |
| Proven at 60 s, in every run | **10 of 10** | **10 of 10** | **5 of 10** |
| Proven at 10 s, in every run | **7 of 10** (sync 2 of 3) | **6 of 10** (ring 1 of 3) | **1 of 10** |
| Slowest proof at 60 s | 25.0 s (ticket_lock) | 45.5 s (ticket_lock) | 34.8 s (ticket_lock) |

Medians over the three runs at 60 s (wall time, seconds; DuoAI's simulation phase is part of its wall time):

| Protocol | Paper | DuoAI | of it, simulation | DuoAI, hard 2 CPUs | of it, simulation | invariants in DuoAI's answer | gdp-wired | laws gdp-wired found |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| lock_server_sync | 1.3 | 3.2 | 2.1 | 5.2 | 3.9 | 2 | 8.2 | 1 |
| lock_server_async | 1.9 | 3.4 | 2.3 | 7.1 | 5.9 | 13 | 21.2 | 12 |
| decentralized_lock | 9.9 | 14.0 | 4.0 | 16.9 | 3.9 | 17 | 14.4 | 2 |
| distributed_lock | 6.1 | 8.4 | 2.8 | 15.4 | 4.4 | 43 | unknown, 23.4 | |
| two_phase_commit | 1.5 | 2.1 | 1.4 | 5.0 | 2.9 | 20 | 15.7 | 14 |
| ticket_lock | 23.9 | 24.4 | 1.7 | 45.0 | 3.7 | 78 | 34.8 | 12 |
| toy_consensus_forall | 1.9 | 3.5 | 2.0 | 7.3 | 5.3 | 7 | unknown, 17.5 | |
| consensus_wo_decide | 3.9 | 5.3 | 2.3 | 9.8 | 5.1 | 18 | unknown, 36.6 | |
| ring_leader_election | 3.5 | 5.6 | 4.5 | 10.5 | 8.0 | 15 | unknown, 8.0 | |
| sharded_key_value_store | 1.9 | 4.3 | 3.2 | 7.2 | 5.5 | 13 | unknown, 48.1 | |

(DuoAI's own "DuoAI runtime", its inference-only time, is its wall time less about 0.1 s in every run: the interpreter's
start. Its invariant counts include the safety property.)

## The gap

- **Coverage.** At 60 s DuoAI proves all ten in every run, gdp-wired five (lock_server_sync, lock_server_async,
  decentralized_lock, two_phase_commit, ticket_lock). At 10 s DuoAI proves seven (six under the hard cap), gdp-wired
  one (lock_server_sync). The five gdp-wired misses at 60 s are the classes `../README.md` gives (Why each one is
  missed): distributed_lock, toy_consensus_forall, consensus_wo_decide, ring_leader_election (a function of a key and a
  three-key ring order) and sharded_key_value_store; each search stops on its own, unknown, well within the limit (8 to
  48 s), so a longer limit at this commit is unlikely to change them. DuoAI's misses at 10 s are its slower protocols (decentralized_lock 14 s,
  ticket_lock 24 s; under the cap also distributed_lock 15 s and ring 10.5 s).
- **Speed, where both prove** (60 s, medians): gdp-wired's time over DuoAI's is 2.5 (sync), 6.2 (async), 1.0
  (decentralized), 7.3 (2PC) and 1.4 (ticket) on run.py's shape; under the hard 2-CPU cap 1.6, 3.0, 0.9, 3.1 and 0.8.
  So against DuoAI held to 2 CPUs, gdp-wired is faster on decentralized_lock (14.4 against 16.9 s) and ticket_lock
  (34.8 against 45.0 s) and 1.6 to 3.1 times slower on the other three.
- **What a proof is.** DuoAI's answer is an Ivy file of universally quantified invariants (2 to 78 here) that Ivy found
  inductive with Z3 4.7.1, over the Ivy model's unbounded sorts. gdp-wired's is a set of laws (1 to 14 found here) over
  its own encoding of the same protocol (sorts bounded by 64, quorums over-approximated), with a certificate its kernel
  checked and a Lean twin of the kernel. The two are checked by different means, of different models of each protocol.

## Against the paper

- **Verdicts reproduce:** all ten proven, in every run, as in DuoAI's Table 1.
- **Times are slower than the paper's,** which were a 28-core Xeon W-2175: 1.0 to 2.5 times on run.py's shape
  (ticket_lock 24.4 s against 23.9), 1.7 to 4.0 times under the 2-CPU cap. Most of the difference on the fast
  protocols is the simulation phase (nine sampler processes, each a Python with numpy and pandas): 63% of the wall time
  at the median here.
- **Bursting.** On run.py's shape (`cpu=2.0`) DuoAI's containers saw 18 CPUs, and used several at once (its CPU time,
  as the sandbox accounts it, was a median 6.9 times its wall time, a lower bound since DuoAI kills some processes
  without waiting for them); under `cpu=(2, 2)` they saw 2. gdp-wired's search used 1.3 CPU-seconds a second (bun's
  own threads with one thread of search), so a cap of 2 does not bind it. The hard-capped column is the like-for-like
  one on CPUs; run.py's column is the like-for-like one on the Modal configuration.
- **One stalled run.** lock_server_sync at 10 s, run 3 (run.py's shape): translation took 1.5 s (0.15 s in the other
  runs) and the samplers produced nothing before the kill. The same protocol took 2.6 to 4.9 s in the other eight
  runs; it is counted as the timeout it was.
- **The artifact.** The commit is two post-paper commits on from the paper's (a sampler fix in `translate.py`); the
  parse-table race above is an artifact of fresh containers, not of DuoAI.

## Spend

The pilots, the first DuoAI batch (stopped once the parse-table race showed), the two DuoAI batches and the gdp-wired
batch: $0.29 in Modal's billing report at 08:07 UTC on 2026-10-29 (`gdp-wired-duoai` $0.23, the two gdp-wired
runs' apps $0.06), the last hour still open then. The budget was $8.
