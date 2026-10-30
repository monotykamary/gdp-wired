# Distributed systems in real apps: the system model and the environment

ROADMAP.md, section 3, gaps 1 and 2: the nodes, their handlers and the message pool as one rule built from per-process
steps, and a small library of environment models, each checked against the stack it describes.

**Where it stands (gen/laneB, 2026-10-31):**
- **The layer.** `core/system.ts` (new, 24 KB) has `system`, `lift`, `isolation`, `delivery`, `client`, `expiry`,
  `asRule` and nine environment models. Its tests are in `core/system.test.ts` (8 pass). No existing file changed.
- **The environment checked.** 11 of 11 claims hold on PostgreSQL 15, Redis 7 and urllib3 (`envcheck.py`).
- **An extracted rule.** The same layer runs on a rule the Python reader extracted: LiteLLM's session limiter. Its
  own step law is proven atomic and refuted under read committed.

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
- **Liveness.** The roadmap's gap 3, liveness over keyed state under fairness, is not in the library. No liveness law
  is claimed here.
- **LiteLLM's model choice.** It was made by reading the cache's code, not by a run.
