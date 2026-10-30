# Reach: from the ten protocols to the domains not yet reached

The plan past the protocol frontier. The ten protocols are the test bed: the work to prove them with nothing written is
meant to leave general pieces behind, and this note says which pieces the rest of the reach needs, what the library
already has of them, and in what order to build the rest. It is a plan, not a result; each step ends in a measure.

**Where it stands (2026-10-30, main dfafb37):**
- **Protocols:** 7 of 10 proven with nothing written at 60 s, and all 10 with the written invariants. DuoAI (OSDI 2022),
  measured side by side: 10 of 10 at 60 s, 7 of 10 at 10 s (`protocols/duoai/`). Open: distributed_lock,
  ring_leader_election, consensus_wo_decide (`protocols/engine/DESIGN.md`, "Where it stands").
- **Real-world corpus:** 353 of 361 laws decided with nothing written (318 proven, 35 refuted, 8 unknown), Oct 29.
  Payments, stores, sign-in, APIs, AI spend, approvals, rollout, app workflows and test automation are reached.
- **Partway:** distributed storage, and backends in more languages (Python, Rust, Ruby, Elixir, C, C++ and Go read
  onto one IR, `core/extract-step.ts`).
- **Not yet:** consensus (with blockchains and telecom), trading, safety-critical systems, regulated workflows.

## 1. What the reach builds on

| Piece | Where | What it gives the reach |
| --- | --- | --- |
| Laws about every key, proven at a fresh key | kernel/kernel.ts (`k#`), Sets.lean | The unbounded check: every node, message, account or tenant at once |
| The protocol engine | core/infer.ts (`engine`) | Quantified invariants nobody wrote: small instances, symmetry, minimal cubes, ∀∃ by ghost witnesses, Houdini with IC3 frames |
| The EPR fast path | kernel/epr.ts, kernel/prove.ts | Decided goals over keyed maps with order, in model-sized time |
| Exact rationals | core/rationals.ts, kernel/qprove.ts | Decimals and fractions as they are (0.1 is 1/10), linear over ℚ with Farkas certificates |
| Liveness | core/live.ts, core/cycles.ts | "Leads to" with the rank found from the rule's own terms, on one machine |
| Runs that never end | core/nonterm.ts | A recurrent set as the counterexample to a liveness law |
| Two machines side by side | core/compose.ts (`product`), next/relational.ts | Laws over two runs: migration safety, tenant isolation |
| Bit-vectors | sat/ (research only) | Bit-blasted laws with LRAT checked in TypeScript; not in the library |
| Readers in seven languages | core/extract-*.ts | One step function out of one process, checked by running both |
| Time as a request's input | core/extract-py.ts and the other readers | Windows and rate limits over the request's time |

## 2. What 10/10 should leave behind

Each open protocol is open for a reason that is not about that protocol. The fix should be the general piece:

| Protocol | Why it is open | The general piece | Where else it is needed |
| --- | --- | --- | --- |
| distributed_lock | The laws the proof needs are not among the enumeration's shapes | Shape families: whatever shape the probe finds missing, as a family any rule's keys can take | Every keyed rule: ledgers per account, holds per resource |
| ring_leader_election | The own-id and leader laws lack support; 4- and 5-key cubes cost 1.5–3.7 s | Laws over an ordered sort's ids and the keys that point at them; cheaper wide cubes | Elections, leases, version vectors, ordered queues |
| consensus_wo_decide | One long join query; the quorum law scores in late | Laws about a set a request brings (a quorum) and its members; a join whose cost is bounded | Consensus, multi-party approval, k-of-n signing |

Two pieces carry over from what already works:
- **∀∃ by ghost witnesses** ("every request has a reply in flight") is the shape of the message-pool laws in section 3.
- **Symmetry** (keys interchangeable but for params that name them) is the shape of tenants, accounts and workers in an
  app.

**The measure:** 10 of 10 with nothing written at 60 s on main, with no new code special to one protocol. Each piece
should also prove a law in the real-world corpus that it did not before, or it is only a protocol trick.

## 3. Distributed systems in real apps

Solving the protocols is not solving distributed apps. The benchmarks hand the prover a model; an app is handlers,
queues, a database and retries across services. Most of an app's distributed bugs are not consensus. They are:
- handlers that are not idempotent under retries (a double charge);
- read-modify-write races in the database;
- outbox and inbox delivery;
- sagas and their compensations;
- duplicate delivery;
- replicated values that must converge when merged.

All of these are keyed state plus a pool of messages plus a fixed environment, the shape the engine already handles.
What is missing, most important first:

1. **The system's model.** The readers pull one step out of one process. What would be new: the nodes, their handlers
   and the message pool as one rule, built from the readers' steps. This is the largest gap.
2. **The environment.** What the network and the stores may do: at-least-once queues (SQS, Kafka), the database's
   isolation level (read committed, snapshot, serializable), a retrying HTTP client. A library of these models, each
   checked against the stack's documented behaviour. The trust here is in picking the model, and a proof says which
   one it assumed. Prior art: P (message-passing models of services at AWS), Jepsen and Elle (isolation anomalies
   found by testing).
3. **Liveness over keyed state.** live.ts proves "leads to" on one machine. Needed: the same over every key, under
   fairness ("every message is eventually delivered"), so "every order is eventually settled" is a law.
4. **Counting.** Quorums, "more than half", thresholds. Outside the EPR fast path. Needed for consensus (section 4), not
   for the patterns above.
5. **Clocks and leases.** Request time exists. Missing: time that differs between nodes (skew), leases that expire,
   timeouts as the environment's steps.
6. **Code against model.** IronFleet and Verdi proved the code refines the model by hand, at great cost. Here the
   readers make the model from the code, and checking by running both makes it a correspondence check, not a proof.
   That boundary should be stated in every result.

**The measure:** one open-source service with retries and a database, its pattern laws written and decided, every
refuted law with a run that reproduces it in the service.

## 4. The domains not yet reached

### Consensus, blockchains, telecom

- **Consensus** (Paxos, Raft, Byzantine-tolerant protocols): the argument is counting ("two majorities share a node",
  "more than 2f+1 signed"). Also membership that changes (reconfiguration) and liveness under partial synchrony.
  Needs: quorum and threshold counting as a decided theory (threshold automata, as in ByMC; or quorum intersection as
  a built-in law), liveness over keyed state, and the next tier of benchmarks (Paxos, Multi-Paxos, Flexible Paxos,
  Raft-like), where every tool in the field slows down or needs hints. wo's quorum law is the first step.
- **Smart contracts** are closer than they look: one-threaded state over a ledger, the reached payments shape. Needs:
  bit-precise 256-bit wraparound (sat/ into the library), re-entrancy (a call into untrusted code mid-step, as an
  environment that may call back), and a Solidity or EVM reader. A chain's consensus is the consensus row.
- **Telecom** (SIP, 3GPP state machines): timers, many message types, properties about progress, code in C or Erlang.
  Needs: clocks and liveness (section 3), and an Erlang reader beside the Elixir one on the same BEAM forms.

### Trading

Order books, matching engines, risk limits.
- **Reached already, likely:** risk and position laws ("exposure never above the cap") have the shape of budgets and
  quotas, and exact rationals cover decimal prices.
- **Missing:**
  - fixed-point rounding (a floor at a tick size) and floats where the code uses them;
  - price-time priority, a law over a sorted structure: ordered collections (heaps, ordered maps), not only keyed maps;
  - deeper C++ (templates; lock-free code, where the memory model matters).
- **Not laws:** some rules, such as best execution, are statistical. They stay out.

### Safety-critical systems

Avionics, automotive, medical. Mature tools exist (SPARK, Astrée, Frama-C, SCADE).
- **Where gdp-wired fits:** the discrete supervisory logic: modes, interlocks, alarms.
- **Where it does not:** continuous control laws (hybrid systems; KeYmaera X's domain).
- **Missing:**
  - qualification under DO-178C or ISO 26262: the kernel and the Lean re-check are a start; the readers and the
    environment model would need qualification evidence of their own;
  - floats;
  - hard real time;
  - embedded C past what the C reader's ub mode covers.

### Regulated workflows

Healthcare, insurance, banking compliance, know-your-customer checks. The code has the shape of the reached approvals
and workflows. What is missing is around it:
- **The law's source is regulation text.** Is the law faithful to the clause? Needs a trace from each law to its clause,
  perhaps an agent drafting the laws and a person signing them.
- **Deadlines** ("within 30 days"): calendar arithmetic over request time.
- **Data flow** ("this field never reaches that party"): a law over two runs. compose.ts's product and
  next/relational.ts's isolation are the start; needed in the library, on extracted code.
- **Audit:** a certificate checkable in Lean is the evidence an auditor can rerun.

## 5. The pieces across domains

| Piece | Have | Missing | Unlocks |
| --- | --- | --- | --- |
| Arithmetic | Linear ℤ and ℚ, products of degree 2 | Bit-vectors in the library, fixed-point rounding, floats, counting | Contracts, trading, consensus, safety-critical |
| Time and liveness | Request time; "leads to" on one machine; never-ends | Over every key, under fairness; clocks between nodes | Telecom, consensus, deadlines, distributed apps |
| Environment | — | Queues, isolation levels, retries, a hostile caller | Distributed apps, contracts |
| Structure | Keyed maps, lists by position, datatypes | Ordered collections, sets a request brings | Trading, consensus |
| Two runs | product, relational laws (research) | In the library, on extracted code | Regulated workflows, isolation |
| Readers | Seven languages on one IR | The system's model; Solidity or EVM; Erlang | Distributed apps, contracts, telecom |
| Trust packaging | Kernel, Lean twin | Law-to-clause traces; qualification evidence | Regulated workflows, safety-critical |

## 6. Order

Closest to what is reached first. Each step ends when its measure holds on main.

1. **Protocols to 10/10** (section 2). Measure: 10 of 10, nothing written, 60 s, no protocol-specific code.
2. **Distributed patterns in apps** (section 3, gaps 1 and 2). Measure: one service's pattern laws decided.
3. **Regulated workflows:** two-run laws in the library, deadlines, law-to-clause traces. Measure: one open-source
   workflow's privacy and deadline laws decided.
4. **Smart contracts:** sat/ into the library, re-entrancy as an environment, a reader. Measure: a public contract's
   ledger laws decided, against a known exploit's refutation.
5. **Trading:** fixed-point rounding, ordered collections. Measure: an open-source matching engine's priority law.
6. **Telecom:** liveness over keyed state, clocks. Measure: a SIP transaction state machine's progress law.
7. **Consensus:** counting. Measure: Paxos with nothing written.
8. **Safety-critical, last:** qualification is slow and mostly not technical.
