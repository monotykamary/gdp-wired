# Distributed systems in real apps: the system model and the environment

ROADMAP.md, section 3, gaps 1 and 2: the nodes, their handlers and the message pool as one rule built from per-process
steps, and a small library of environment models, each checked against the stack it describes.

**Where it stands (gen/laneB, 2026-10-31):**
- **The layer.** `core/system.ts` (new, 24 KB) has `system`, `lift`, `isolation`, `delivery`, `client`, `expiry`,
  `asRule` and nine environment models. Its tests are in `core/system.test.ts` (8 pass). No existing file changed.
- **The environment checked.** 11 of 11 claims hold on PostgreSQL 15, Redis 7 and urllib3 (`envcheck.py`).
- **An extracted rule.** The same layer runs on a rule the Python reader extracted: LiteLLM's session limiter. Its
  own step law is proven atomic and refuted under read committed.
- **Liveness over every key, clocks and leases (gen/laneT, section 6).** A leads-to about every key is the one-machine
  liveness at a fresh param; time, a clock within a skew and keys that expire at their time are environment steps;
  a fair run that never gets there refutes a leads-to. SIP's four transactions, an outbox and a lease are decided.

## 1. The system model

An app's distributed bugs live between handlers: two requests interleave at their calls to a store, a message is
delivered twice, a key vanishes. The readers give one step of one process (`core/extract-step.ts`). The system model
puts those steps together with the stores they share and the environment's own steps, as one rule. It is a general
layer over Machines, in the spirit of `core/compose.ts`, and specific to no language or reader.

```ts
system(name, {
  attempt: {rule: attemptRule, id: 't'},   // every attempt at once, its scalars per process
  expire: expiry({Tag: 0, Owner: 0}),     // an environment step
})
```

- **One part steps per request.** The input `act` names which part steps; the others keep their state. It is
  `compose.ts`'s `interleave` made n-ary.
- **Stores are shared by name.** A map named in two parts is one store (Redis's key space, a table), not two renamed
  copies. That is the difference from `interleave`, whose sides are independent machines. Two parts may write one map:
  the system's write is the active part's.
- **Processes, unbounded.** A part with an `id` is every process of it at once. `lift` turns each scalar (a request's
  locals: its pc, its token, its result) into a map keyed by the process. The request's input `id` says which process
  steps. A rule that reads an input named `id` reads its own process id: a token, an owner. Laws are then about every
  process (`∀t`), which is the keyed-map shape the kernel's `k#` and the protocol engine already take.
- **A handler of several steps.** A handler that awaits other services between its reads and writes is not atomic.
  Its rule has a pc, and each step is one call. The Python reader inlines a handler into one atomic step (each request
  one step, "as no await suspends"). For an in-process asyncio handler whose awaits never suspend, that is the right
  model. For a handler over a shared store it is not, and `isolation` (section 2) turns an atomic step into the
  several steps a transaction takes.
- **A Machine as a Rule.** `asRule` builds the same machine through the DSL builders, so `proveRule` (random runs,
  bounded runs, k-induction, the invariant search) and `proveSteps` take a system as they take any rule. Every name
  is a natural there, unless a kind is given (`act` is a choice, so the runs draw every part).
- **Each model is named.** Every combinator records the environment models it assumes. `modelsOf(rule)` lists them,
  and a verdict prints them beside the law.

Nothing here is trusted: a proof is about the rule built, and the kernel checks it as it checks any rule. What the
proof means for the code rests on two things it states: the environment models assumed, and that the rule's steps are
the code's. The second is a correspondence check by running both (ROADMAP gap 6), never a proof.

## 2. The environment models

Each model says what it assumes. Each claim is checked on the real stack by `research/distributed/envcheck.py`, run
on Modal against PostgreSQL 15, Redis 7 and urllib3 2.2 (`envcheck.json`: 11 of 11 as the models say).

| Model (`core/system.ts`) | What it assumes | The documented behaviour | Checked on the stack |
| --- | --- | --- | --- |
| `isolation(m, 'atomic')` | the handler is one step | PostgreSQL SERIALIZABLE: "the same effect as running them one at a time in some order" (docs 13.2.3); `SELECT ... FOR UPDATE`; `UPDATE ... SET x = x + k`; a Redis Lua script runs atomically | serializable refuses the write skew (one commit: "could not serialize access due to read/write dependencies"); an in-statement increment waits and re-reads (130 of +10, +20 on 100) |
| `isolation(m, 'read committed')` | each read at its own step, sees the latest commit; writes appear together at commit; nothing re-read at commit | "a SELECT query sees only data committed before the query began" (13.2.1) | two read-then-write deposits: one lost (120); a second read sees a commit made in between (150) |
| `isolation(m, 'snapshot')` | every read at the start; a commit refused (`aborted$`) when a cell it writes moved since; disjoint writes never conflict | REPEATABLE READ: "could not serialize access due to concurrent update" (13.2.2) | the second writer of a moved row is refused (110); write skew commits both (−60) |
| `delivery(m, pool, …, 'at-least-once')` | a sent message is delivered any number of times, in any order, also while an earlier delivery runs | SQS standard queues: "more than one copy of a message might be delivered"; Kafka re-reads after a rebalance before the offset commit | a Redis Streams entry read and not acknowledged is delivered again (XAUTOCLAIM) |
| `delivery(m, pool, …, 'exactly-once')` | taken once, the take committing with the handler's writes | a transactional consume (Kafka transactions; an inbox row in the handler's transaction) | — (the stack's own guarantee; not run) |
| `RETRIES` (a retrying client) | a request may be tried again at any time, while an earlier try runs or after it applied | urllib3 `Retry(read=…)` re-sends after a read timeout | one POST, applied then stalled past the timeout, applied 3 times by `Retry(total=2)` |
| `expiry(cells)` | any key may vanish at any step, whatever its TTL | Redis `EX`; `maxmemory-policy volatile-lru` "evicts … keys with an expire set" | a 1 s TTL lapses; a 30 s key is evicted at once under memory pressure |
| `STORE_FAILS` | a store call may raise, before or after it applied | redis-py's `ConnectionError`, `TimeoutError` | a SET whose reply is held past the client's timeout (a proxy delaying replies) raises and is applied |
| `WRITES_FAIL` | a create may raise before its insert or after it | Django: receivers and `on_commit` hooks raise after the INSERT; `transaction.atomic` rolls back before it | — (Django's documented behaviour; not run) |

How `isolation` works. It turns any atomic step (an extracted one, too) into a transaction of several steps. A local
`pc$` drives it:
- **Begin.** The request's inputs are kept (`in$x`).
- **Reads.** Under read committed, each store read site of the step is its own step, inner sites first (`rd$i`).
  Under snapshot, they are all read at the begin.
- **Commit.** The step is evaluated with each store read replaced by what was read, and its writes are applied.
  - A write whose `if` keeps the cell (`when(c, v, M.at(k))`) writes only where it changes it, as the code does.
  - Under snapshot, the commit is refused where a cell it writes moved since the begin. `aborted$` records it, and
    the commit changes nothing.

The read committed model is sound for what it says: a commit's writes become visible together, and a re-read inside
the write statement (`SET x = x + 1`) is not modelled there. That statement is atomic in every level (the envcheck's
130), so such a handler is declared `atomic`. Snapshot validates by value, not by version, so it allows an ABA commit
that PostgreSQL refuses. That is more runs, which is sound for a proof.

## 3. The layer on an extracted rule: LiteLLM's session limiter

`research/distributed/litellm.ts` takes `research/langs/litellm/rules/MaxIterationsHandler.ts`. The Python reader
extracted that rule from `max_iterations_limiter.py` (v1.106.6) and checked it against the code by running both. The
script runs every call of `async_pre_call_hook` at once over the shared session counter, and lifts the rule's own
step law, "every call of a limited session counts one", to the step that writes:

| Model | Verdict |
| --- | --- |
| atomic | proven (1.4 s) |
| read committed | refuted (9 steps: two calls read 0, both write 1) |

Which model is LiteLLM's? `_in_memory_increment` awaits `InMemoryCache.async_get_cache` and `async_set_cache`
(`in_memory_cache.py:179, 238`), and neither awaits anything, so asyncio runs no other call between the read and the
write. The atomic model is the code's with Redis off. The Redis path uses a Lua INCR, atomic too. The refutation says
what the same code would do over a store whose calls suspend. This was checked by reading the code, not by a run.

## 4. Measure

- **Tests.** `core/system.test.ts`, 8 tests, about 5 s:
  - `asRule` runs as the machine;
  - lifted processes keep their own scalars;
  - the models are named;
  - a charge without a dedupe under at-least-once: refuted; exactly-once: proven;
  - a dedupe in one step: proven; split by read committed: refuted; snapshot: proven, its invariant found;
  - a read-modify-write: refuted at read committed, proven at snapshot;
  - `client`, `expiry`.
- **The quick bar.** `bun gates/bar.ts --quick --cand gen/laneB --base ae36917 --only rw,f1,f2,g332,suite,onecpu` at
  8a889b1 (`bar.md` beside this file): f1, f2 and rw gained 0 and lost 0 on their dev sets (48, 64 and 91 tasks);
  g332 proved 332 of 332, with the same search on every goal; the suite passed 235 of 235; onecpu had no failures.
  core/ and kernel/ grew by 23,945 B. Wall time 532 s, estimated at $0.59.
- **Bytes.** Before ae36917, `core/` had no `system.ts`.
  - `core/system.ts`: +23,945 B (310 lines).
  - `core/system.test.ts`: +5,262 B.
  - No other file in `core/`, `kernel/` or the readers changed.

## 5. What is verified and what is not

**Verified:**
- **The proofs.** Every proof is the kernel's, on the system rule built.
- **The environment models.** Each claim of each model is on the real stack (11 checks), except exactly-once delivery
  and Django's write failures, which are stated from the documentation.

**Not verified:**
- **That a rule is the code.** A rule's steps are the code's only by a correspondence check of running both, never a
  proof.
- **Liveness.** Section 6 (gen/laneT) has it now: liveness over keyed state under stated fairness.
- **LiteLLM's model choice.** It was made by reading the cache's code, not by a run.

## 6. Liveness over every key, and time (ROADMAP gaps 3 and 5; gen/laneT)

### 6.1 A leads-to about every key

`leadsTo`'s callbacks may take a second parameter, the key (`from: ({S}, k) => S.at(k).eq(1)`). The key is then a fresh
param no step reads (`forall` on the liveness), and `proveLeadsTo` proves the rule with it (`keyed(r, l)`, the rule with
one more natural param). Nothing new is trusted, and the kernel's kind is the one it had:
- **Why it is the law at every key.** A run of the rule with the param is a run of the rule without it, the param fixed
  at some value: no step, assumption or start reads it. Live.lean's theorems hold of every run of the keyed rule, so of
  every run of the rule at every value of the key, each key's helpful requests fair on their own (fairness per key:
  "each message's delivery", not "some delivery").
- **Refused without it.** `proveLiveness` on the rule itself throws (the key is out of scope), so a keyed liveness can't
  be proven about a rule that lacks its key.
- **The search, generalized** (core/live.ts's `leadsByTerms`, core/cycles.ts's `findLeadsTo`): a control rank of the cells
  `from` and `to` read at a key of the params (a status per key, its values ranked by the steps between them, as a
  bounded scalar's were); laws about every key kept from the invariant search (they were dropped; a keyed liveness needs
  its key's); ranks of up to four components; a third of the time left for the invariants of the first rank.
- **Lean.** `research/distributed/lean.ts` exports three keyed proofs (NICT, NIST with the TU's response, the outbox's
  "published"), their ranks and laws found: Lean 4.34.0 checks them (`nict_live0_holds`, ...: `propext`,
  `Classical.choice`, `Quot.sound`), 52 s, 673 KB. Suite job `lean-keyed`.

### 6.2 A fair run that never gets there

core/live.ts's `refutedBy` checks a ring: a stem from the start (run on the interpreter, the params meeting the
precondition) to a state of R_0 where `from` holds and `to` doesn't; then sets R_0..R_{n−1}, each with a fully named
request the kernel proves allowed in every reachable state of R_j and taking it into R_{j+1} with `from` kept and `to` not
reached (kernel.ts's progress goals). Which of Live.lean's fairness hypotheses the infinite run meets, per helpful request:
- **taken** (`sleads_sound`): some R_j's request names its inputs as it does;
- **weak** (`sleads_wf_soundA`): taken, or no request with its named inputs is allowed in some R_j (a step law whose
  `then` is false);
- **strong** (`sleads_sf_soundA`): taken at some R_j inside its region (a step law: R_j's request outside the region is
  never allowed), or allowed in its region in no R_j.
"Allowed" is the machine's assumption, which the theorems' condition `a` implies where the machine is, so "no request
allowed" is "not enabled" in their sense. The law is refuted when the run meets the law's fairness (strong where it says
so, else weak). `findRing` finds a one-set ring from the runs: a state where the helpful requests taken in turn for up to
3,000 steps never reach `to` (the time passing every deadline), the set its literals of the rule's comparisons, dropped
(Houdini) until each ring request is proven to keep them. `refuteLeadsTo(r, laws, l)` runs it on the keyed rule.

terra reviewed `refutedBy` against the three theorems (read only): the classification is sufficient where `a` is the
machine's assumption or implies it (the instantiations the kernel uses); and the params were not checked against the
precondition, a false refutation (fixed: the precondition is checked).

### 6.3 Time, clocks, leases (core/system.ts)

| Combinator | Model | What it assumes | Checked |
| --- | --- | --- | --- |
| `time()` | time passes | a true time `now`, a natural that only rises, by any amount at a step of its own; nothing bounds how many steps run between two of its | the time reference: a store's clock for its TTLs, a node's monotonic clock for its timers |
| `clocked(m, at, ε)` | clock skew ≤ ε | m's request time `at` (the readers' time.time(), Instant::now()) is within ε of `now` either way; readings need not rise (more runs than a monotonic clock's); ε = 0 is the time itself (the input gone); Infinity is no bound | the deployment's bound (NTP/PTP discipline): stated, not checked |
| `expires(cells, at)` | keys expire at their time | a key vanishes only once `now` has reached its expiry, at any step after; never before (no eviction) | Redis 7.0.15, `envcheck.py` on Modal: a PX key there at 1.0 s of 1.5 s and refusing a second SET NX, gone at 1.8 s; under noeviction a write past maxmemory refused (OOM), the key with a TTL kept. 6 of 6 Redis checks, 13 of 13 in `envcheck.json` |

A timer is a handler step allowed once the clock has passed its deadline (late by any amount, never early); a timeout
is the same step. `lift` keeps `now` shared (a scalar `clocked` and `expires` mark as the system's).

### 6.4 Measures

**SIP transactions (research/distributed/sip.ts): a written model, not an extraction.** A survey (re, oSIP2, sofia-sip,
PJSIP, sipgo, rsipstack, sippy, JAIN-SIP) found no transaction layer a reader takes as it ships: every one has function
pointers or callbacks, async code or loops, strings and unions in the transaction's struct, or its state changes in
other files; the closest (re's `src/sip/ctrans.c` at e5ec9ba) needs about 100 lines copied into a clean struct, a rewrite.
So the four machines of RFC 3261 section 17 (Figures 5 to 8; 17.1.1.2, 17.1.2.2, 17.2.1, 17.2.2, 17.1.4 transport
errors) with RFC 6026's Accepted states (7.1, 7.2; Timers L and M) are written, each state, event and timer of the
figures, every transaction at once (`lift` by its id) beside `time()` and `clocked(…, 0)`. Not modelled: message contents,
the TU's other duties. The law, "every transaction eventually terminates", is about every transaction (keyed), under weak
fairness of time passing, each due timer firing and, where stated, the far end's or the TU's final response; rank and
laws found, nothing else written (Modal, 2 vCPU, 20 s each):

| Transaction | With time and timers only | With the final response assumed |
| --- | --- | --- |
| NICT (Trying, Proceeding: Timer F; Completed: K) | proven, 13.7 s, rank (fAt − now, the state's level, kAt − now) | — |
| ICT (Calling: B; Completed: D; Accepted: M) | refuted: a ring in Proceeding, the time passing, every timer never allowed there (fair weakly and strongly), 2.6 s | proven, 7.1 s, rank (bAt + 1 − now, level, mAt − now, dAt − now) |
| IST (Completed: H; Confirmed: I; Accepted: L) | refuted: a ring in Proceeding (no timer until the TU answers), 2.3 s | proven, 5.0 s, four components |
| NIST (Completed: J) | refuted: a ring in Trying (the TU never answers), 0.5 s | proven, 2.3 s |

The refutations are the RFC's own: Proceeding has no timer in the INVITE client (17.1.1.2: Timer B fires only in
Calling) and in the INVITE server, and Trying and Proceeding have none in the non-INVITE server; such a transaction ends
only when the far end or the TU sends a final response (in the RFC, Timer C at proxies, 16.6, and the UAS core's
duties bound that, outside the transaction layer).

**An outbox over every row (research/distributed/time.ts).** The app inserts a row (`client`), a relay publishes pending
rows to the broker at least once and then marks them, crashing between the two (a model, `CRASH`), the consumer takes
each message at least once (`delivery`):

| Law (every row k) | Fairness | Verdict |
| --- | --- | --- |
| eventually published (Outbox[k] = 1 leads to Q[k] = 1) | weak, the relay's poll of k | proven, 2.1 s; laws found: InFlight[k] ≤ Q[k], Q[k] ≤ 1 |
| eventually handled by the consumer | weak, the poll of k while pending and unsent, the delivery of k | proven, 3.3 s; rank 1 − Q[k] and Outbox[k] ≤ Q[k] + 1 found |
| eventually marked published | weak | refuted: the ring publish, crash (mark never allowed in the first set), fair weakly; findRing finds no one-set ring, the two-set ring is written |
| eventually marked published | strong | proven, 2.4 s; InFlight[k] ≤ 1 found; the same ring is not strongly fair |

**A lease (research/distributed/time.ts).** A process acquires as SET NX PX L does (`expires`: the key's expiry the
store's `now + L`), counts it valid until its clock's reading + L − M, and uses it only while its clock reads before
that (the write it protects at the instant of the check). The law, a step law at every use: "a process uses the lease
only while the store holds it for that process, unexpired" (so at most one holder uses an unexpired lease).

| Skew, margin | Verdict |
| --- | --- |
| clocks within E, M ≥ 2E, L ≥ M | proven with one written invariant (every process's until is 0, or until + E ≤ now, or it is the owner with until + E ≤ the expiry), 0.6 s; the search alone does not find it (6 s) |
| no bound on the skew | refuted, 3 ms: a process whose clock reads early uses its lease after it expired and another acquired it (the run replayed on the interpreter in core/system.test.ts) |
| clocks within E, M ≥ E | refuted, 38 ms: a margin of E is not enough |

A check-then-act with a pause between (Kleppmann's GC pause) is not this model: the use is atomic with its check. Split
into two steps it is refuted at any skew; fencing tokens are the remedy, not modelled here.

### 6.5 What is verified and what is not

**Verified:** every proof is the kernel's on the rule built; three keyed proofs exported and checked by Lean; every
refutation is a run (safety: the bounded run, replayed; liveness: a ring whose steps are the kernel's progress goals
and step laws, its stem replayed); the TTL model's claims run on Redis 7.

**Not verified:** that the SIP model is any stack's code (written from the RFC); the skew bound of a deployment; the
lease's invariant was written; the outbox's two-set ring was written (findRing finds one-set rings only).

**Gates.** The quick bar (`--quick --cand 1e5a35e --base ae36917`, 356 s, about $2.81): none wrong anywhere, nothing
solid lost (CHC gained 3 and lost 2, SV lost 1, each noise, none solid; ITS gained 1; frontier, real-world corpus, TIP the
same; 332 step goals the same search on all 332; the 1-vCPU tests none failed; Lean 6 of 6). The suites (`--only
suite,suite-usual` at 5679000): `--usual` none failed; by default one, the new `system` job, where laneB's dedupe test
passed bun's 5 s on one vCPU (5.09 s): its tests now get 30 s and the job 2 vCPU (2f33a01), passing on 1 and 2 vCPU (6.6
and 7.3 s); `liveness` and `lean-keyed` passed. tsc over the tree and oxlint on the changed files clean.

**Bytes.** Against cd97c61 (tests excluded): core/live.ts +10,520 (refutedBy, findRing, the key's control rank), core/
system.ts +5,783 (time, clocked, expires), core/dsl.ts +2,298 (keyed leadsTo, `keyed`, `refuteLeadsTo`, the verdict's
rank), core/cycles.ts +76. kernel/ and lean-kernel/ unchanged.

## 7. Lassos of several steps, and a clock a param apart, found (gen/laneT2)

Lane T left two things written: the outbox's two-step ring (publish, crash) and the lease's invariant. Both are now
found; nothing new is trusted (refutedBy and the kernel are as they were).

### 7.1 A lasso of k steps (core/live.ts's findRing)

findRing found one-set rings only: from a state the runs reach, the helpful requests in turn, the ring their literals.
A ring that needs a step no helpful request makes (the relay's crash between its publish and its mark) was out of reach.
Now: from each state a random stem reaches, a walk of up to 3,000 steps, each a helpful request allowed there (in turn,
as before) or, in every other walk, half of them any request, drawn as the runs draw them, each input a helpful request
names set to its value there with odds of a half (the environment acting on the same key). A state's abstraction is the
literals of the rule's comparisons true there (as before; constant ones dropped). A step back to an abstraction seen in
the last 64 steps closes a cycle, taken when
- the walk since then is fair to every helpful request as the law asks, read on the run: weakly, taken (its named
  inputs at its terms) or not allowed at one of its states; strongly, taken in its region, or allowed there at none
  (Live.lean's `sleads_wf_soundA` and `sleads_sf_soundA` hypotheses; the shortest such cycle);
- the cycle runs again from where it closed for 3,000 steps, through the same abstractions, each request allowed and
  `to` never reached (a cycle a deadline ends is none: the time step before a timer is due; without this filter ICT's
  refutation took 10.6 s, the kernel asked of each such cycle).
Its sets R_0..R_{k−1} are its states' abstractions, its requests the walk's (an input a helpful request's term where
it has that value, the key, else its value); a literal of R_{j+1} that R_j's request is not proven to keep is dropped,
round the cycle (Houdini over a chain), and refutedBy checks the ring as before: each request proven allowed in R_j and
into R_{j+1} with `from` kept and `to` not reached, the stem replayed, fairness by step laws. refutedBy's classification
was already per set; terra's review of it (section 6.2) covers rings of any length, which this lane did not re-ask.

### 7.2 A clock a param apart, where a key was written (core/infer.ts's candidates)

Why the lease's invariant was not proposed: it is `until[q] = 0 ∨ until[q] + E ≤ now ∨ (taken = 1 ∧ owner = q ∧
until[q] + E ≤ at)`. Its comparisons read a cell, a param and a scalar; the candidates over cells allowed at most one
value beside the cells (`until[k] ≤ now`, never `until[k] + E ≤ now`). And its first disjunct, a key never written, is
a guard no candidate had: a cell's guards were one value of a cell of few values, or one scalar's key (`k = owner or`).
The search found `taken is 1 → until[k] ≤ at` and `taken is 0 → until[k] ≤ now`, E left out, which do not prove it.
Two shapes added, general (nothing about leases):
- **A cell against a scalar, a param apart**: three-atom cell forms of one cell, one param and one scalar, the cell and
  the scalar of opposite signs (a time a key holds and a window against the clock: `Ts[k] + window ≤ now`).
- **Where the cell was written**: a one-cell form bounding a natural cell that starts at 0 and takes many values gets
  each of its guards (none, a value of a few-valued value, every key but a scalar's) also over the rows where its cell is
  off 0, at the samples' largest value there and the constant above it, or 0 where that is below 0 (a run seldom meets a
  bound between two times exactly). The three-atom forms get only these guards.
Found on the lease (proveSteps, nothing written): `every k: 1 ≤ until[k] → k = owner or E + until[k] ≤ now`;
`every k: 1 ≤ until[k] → taken is 0 → E + until[k] ≤ now`; `every k: 1 ≤ until[k] → taken is 1 → E + until[k] ≤ at`;
`taken ≤ 1`. (Not the written one: the three say the same split by `taken`, and the owner's case needs no owner.)

### 7.3 Measures (boat, 2 vCPU)

| Measure | Before (42f78b3) | After (7e13c05) |
| --- | --- | --- |
| outbox, eventually marked published, weak | refuteLeadsTo: none found; the two-set ring written | refuted, found: the ring crash (from InFlight[k] = 1), publish (from InFlight[k] = 0), fair weakly, 0.12–0.24 s |
| outbox, the same, strong | proven | proven (unchanged) |
| SIP refutations, ICT / IST / NIST (alone, two jobs a VM) | 1.57 / 1.48 / 0.27 s | 0.95 / 0.80 / 0.22 s, the same rings (fair weakly and strongly) |
| lease, skew ≤ E, M ≥ 2E | unknown (search 2 s); proven with the invariant written | proven, nothing written, at a search budget of 40 s (counted work; 4.0 s wall alone, 20 s on a VM running 14 jobs) |
| lease, skew unbounded | refuted, 1 ms | refuted, 1–2 ms |
| lease, margin E | refuted, 20 ms | refuted, 20–268 ms |

At the default 20 s budget the lease is still unknown through proveSteps: the search's runs, bounded runs and fresh
laws take half the counted budget before inferLaws starts, whose candidates and Houdini take 8.4 counted s of it
(24,400 forms, all but 60 alive); inferLaws given 20 s alone proves it in 12 kernel rounds (4.4 s wall). time.ts takes
`--lease-ms` (40 s); core/system.test.ts asserts the proof at 40 s.

The ten core protocols (research/protocols/run.ts, 60 s, one run each): ten of ten proven. SIP's NICT proof (wall-clock
liveness budget) missed once at 20.7 s on a VM running 14 jobs; alone it is proven in 9.3 s, 9.9 s with the old
infer.ts on the same VM.
