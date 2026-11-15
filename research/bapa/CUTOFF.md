# BAPA cutoff feasibility — STOP before the trusted lift

Baseline: `after/bapa` at `4f505d65d`, merged with `origin/main`
`ebe1d4345` by `7aae419cc`, branch `bapa/finish`.

**No all-size lift has been established.** The requested per-obligation cutoff
classification is incomplete. This is a stop-gate report, not a claimed BAPA
completion or a claim that all-size proofs are impossible. No prover search,
canonical-29 regression, kernel change or certificate reinterpretation was run.

## Exact obstacle

A cutoff theorem applies to a **fixed logical sentence and its interpretations**.
The exported claims are about numeric machines, with `Nat → Nat` environments,
`Nat → Nat → Nat` maps, interpreted arithmetic, and literal 64 guards. They are
not already obligations over arbitrary finite relational structures. Before a
relational small-model theorem can lift them, a checked transport must connect:

1. the *negation of each complete init/step obligation*, including invariant,
   transition, quantified-flag and function premises;
2. the proposed finite many-sorted relational fragment;
3. every small relational countermodel to a numeric instance actually covered
   by the old certificate (including sorts **fixed** at 64).

No such transport or checked fragment recognizer was found. In particular,
`c <= 64` alone does not discharge item 3. Guessing that bridge would be a new,
unclear trusted step, so the user's stop rule applies before step 2.

### A concrete failure, not just missing implementation

`research/protocols/ic3syn/common.ts:9` uses `pk(c,s) = 64*c+s`.
Changing domain guards to permit 65 without replacing this key representation
is false even for lock_server:

1. connect `(client=0, server=64)`; it writes `Link[64] = 1` and disables server 64;
2. connect `(client=0, server=0)`; server 0 is still available, so it writes `Link[0] = 1`.

Now `Link[pk(0,0)] = Link[pk(1,0)] = 1`, because `pk(1,0) = pk(0,64)`.
Two clients appear linked to server 0. Both requests are admitted with two
clients and 65 servers. The original guard rejects the first request.

`cutoff-negative.test.ts` exercises the **actual canonical machine**, cloning
and enlarging only its input guards. A positive control uses the existing
native-tuple `lockServerSized` on the same requests. `CutoffObstruction.lean`
independently proves the collision and the two-connect counterexample in a
standalone model of that branch. This Lean control is **not** a proof of a full
source/port correspondence or a new cutoff rule.

This refutes direct cap erasure with the old radix. It does **not** refute a
correct cutoff theorem for genuinely relational EPR countermodels, or a future
checked translation to tuple keys.

## What the 29 / 67 actually inventory

`cutoff-inventory.json` records 29 protocol cases, all **67 named exported
family declarations**, their exact retained receipt paths and 897 indexed
init/step/cover obligations. These include discovered helper invariants, not
just the user-facing safety laws. Most cases export `_check` and `_laws`;
client_server_ae and firewall each have two retained families (four declarations),
and simple_decentralized_lock has seven declarations including sum transports.
Thus 28*2 + 2 + 2 + 5 + 2 (MLDR) = 67.

The 897 indexes are expanded from retained family metadata, **not a semantic
parse/classification of 897 proof trees**. Internal count side conditions,
quantifier branches and global guard checks have not all been expanded as
separate inventory records. `null` cutoffs and `unresolved` are intentional;
there is no checked per-family cutoff computation yet.

### Per-case feasibility table

`U` = unresolved: numeric-to-relational transport/fragment proof needed.
`B-C` = family uses cardinality/sums, outside pure relational EPR.
`B-A` = family uses cyclic predecessor/size arithmetic, outside that fragment.
A B label does not mean every individual sub-obligation needs counting or
arithmetic, nor does it mean there is no theory-specific cutoff. No case is
admitted to (a). `c` and `c <= 64` are **not established for every row**.

| Case | Retained laws per subfamily | Init/step/cover indexes | Fragment status | Old domain scope |
|---|---:|---:|---|---|
| consensus | 2 | 4 | U | Value fixed 64 |
| tcommit | 1 | 2 | U | RM size <=64 |
| lock_server | 4 | 8 | U; concrete radix obstruction | Client, Server fixed 64 |
| quorum_leader_election | 6 | 12 | B-C | Node size <=64 |
| toy_consensus_forall | 8 | 16 | B-C | Node size <=64; Value fixed 64 |
| simple | 10 | 20 | B-A | 1<=n<=64 |
| simple_regular | 17 | 34 | B-A | 1<=n<=64 |
| lockserv_automaton | 17 | 34 | U | Node fixed 64 |
| sharded_kv | 23 | 46 | U | Node, Key, Value fixed 64 |
| sharded_kv_no_lost_keys | 10 | 20 | U | Key size <=64; Node, Value fixed 64 |
| lockserv | 17 | 34 | U | Node fixed 64 |
| twophase | 12 | 24 | U | RM size <=64 |
| simple_decentralized_lock | 4 | 9 | B-C (retained sum-cover proof) | Node fixed 64 |
| two_phase_commit | 18 | 36 | U | Node size <=64 |
| consensus_wo_decide | 37 | 74 | B-C | Node size <=64 |
| consensus_forall | 45 | 90 | B-C | Node size <=64; Value fixed 64 |
| naive_consensus | 12 | 24 | B-C (canonical majority port) | Node size <=64; Value fixed 64 |
| client_server_ae | 10 + 10 | 40 | U | Node, Request, Response fixed 64 |
| client_server_db_ae | 27 | 54 | U | Node, Request, Response, DbRequestId fixed 64 |
| simple_election | 10 | 20 | B-C | Acceptor size <=64; Proposer fixed 64 |
| toy_consensus_epr | 8 | 16 | B-C despite name | Node size <=64; Value fixed 64 |
| toy_consensus | 4 | 8 | B-C | Node size <=64; Value fixed 64 |
| firewall | 6 + 6 | 24 | U | Node fixed 64 |
| majorityset_leader_election | 16 | 32 | B-C | Node size <=64 |
| consensus_epr | 28 | 56 | B-C despite name | Node size <=64; Value fixed 64 |
| learning_switch | 16 | 32 | U (already native tuples) | 1<=Node size<=64 |
| learning_switch_i4 | 22 | 44 | U (tuples and Node-valued functions) | 1<=Node size<=64; Packet size<=64 |
| paxos_epr | 25 | 50 | B-C plus round order | Node size<=64; Round, Value fixed 64; none<64 |
| mldr | 17 | 34 | B-C plus unbounded term/version arithmetic | 1<=Server size<=64; counters unbounded |

The 12 counted families (including MLDR), the retained sum family, and the two
ring programs cannot be waved into pure EPR. The other 14 cases are **unknown**,
not certified relational fragments. In particular, function graph totality can
introduce forall-exists alternation, and function restriction needs closure;
stratification and a Herbrand term bound must be checked, not assumed.

### Existing artifact provenance (not a new recheck)

- Normal 25: `~/.local/state/r4-launcher/release049-normal28-lean/results/normal28-family-*/FAMILY-CHECK.json`.
- simple/simple_regular: `release049-fprime-normal28-v1/results/fprime-lean-*.files/FAMILY-CHECK.json`.
- Corrected simple_decentralized_lock: `release049-fprime-sum-cover-v2/results/fprime-sum-cover-import-fixed.files/FAMILY-CHECK.json`.
  The earlier `fprime-lean-simple_decentralized_lock` attempt failed; it is not
  substituted for the passing sum-cover result.
- MLDR: `release049-family-assemble-v1/results/family-assemble.files/CHECK-RESULT.json`
  and `D-ACCEPTANCE.json`. Existing proof is assembled from the retained 35-way
  split with the further decomposed row 13; no MLDR job was started here.

The retained `_check` declarations are closed propositions about the checker,
not assertions quantified over domain sizes. `_laws` is quantified over numeric
reachable states of the **literal emitted machine**. For example the retained
lock-server `Proofs.lean:10-23,238-243` embeds both `64*c+s` and `<64`; its type
is not polymorphic in a finite Client/Server type. The receipts also explicitly
exclude some public-projection transports: do not silently strengthen them.

## Correct shape of a future cutoff proof

For a function-free relational **countermodel** sentence
`exists witnesses, forall variables, matrix`, restricting to its witnesses and
named constants preserves the quantifier-free matrix and its universal truth.
Use at least one element for each sort required nonempty. A many-sorted version
must specify empty-sort policy. Positive-arity functions require a proved finite
closure bound; cyclic function dependencies cannot use the naive linear bound.

This is a small-**satisfiability** statement. Applying it to the goal rather than
its negation is invalid. Neither a source filename containing `epr` nor a law
with a universal outer binder proves that the **whole negated induction
obligation** lies in that fragment. Counts, order and arithmetic need their own
semantics-preserving arguments.

A fixed-64 result additionally needs a padding/extension theorem or a new
bounded-size recheck. For instance, the sentence 'there are at least 64 elements'
is true on size 64 and false on size 63: fixed-64 validity is not in general
validity on all smaller structures. This example concerns the logical inference,
not a claimed bug in the existing certificates.

## Read-first material and independent review

Read Fable sections 63 (`49d2a2a0b`) and 64 (`876a55a10`), `BAPA-PLAN.md`,
`BAPA-OBSERVED-PLAN.md`, `BAPA-SLICE3-LOWERING-RESULTS.md`,
`BAPA-FUNCTION-INSTANTIATION.md`, slice-1 `Bounded.lean`, the slice-2
`lock-server-sized.ts`, and the retained output/receipt examples above.
Section 63 explicitly separates symbolic-bounded and fixed-64 sorts. Section 64
is a design proposal, not a cutoff proof. The original-Ivy naive-consensus
slice still lacks its full emitted-machine proof; it cannot replace the
canonical majority family in this inventory.

Independent read-only pi Terra review `e4b2e15a5c134a3690f7a7cf671317ce`
(`openai/gpt-6.1-terra`) agreed that no blanket lift is justified and identified
the same countermodel polarity, function-totality, radix and fixed-size issues.
It did **not** complete the per-obligation classification. An earlier provider
attempt failed authentication before any tool call; no review was claimed from it.

## Measured controls and stopping point

- `20261115-154205-vqmkro`: first focused batch failed in the new TS test's
  AST traversal (binary `a/b` guessed instead of actual `xs`; no Lean run).
  The positive tuple-runtime control passed. Failure retained unchanged.
- `20261115-154709-01pp36`: scoped TypeScript passed; lint rejected literal
  `64 * 0` in the negative test. Replaced it with a named `pack(c,s)` function,
  without disabling lint. No tests or Lean ran in this batch.
- Independent precommit diff review `f8cc7a06817e453eaa0b57cc7b66fbca` by
  `openai/gpt-6.1-terra`: no blocker; corrected its `pk` line citation. Review
  spot-checked one receipt, not all 29, and made no test-pass claim.
- `20261115-155132-h81tsb`: scoped types/lint, 3 tests / 78 assertions,
  and all six standalone Lean declarations passed (no axioms). Only commitlint
  failed: `--edit` requires a Git root absent from the uploaded tree. Use the
  established stdin/config commitlint recipe, not a weakened check.
- `20261115-160334-w3xyp0`: final worker exit 0, 31.23 s. Scoped
  types/lint, 3 tests / 78 assertions, six axiom-free Lean declarations and
  commitlint all passed. The collector timed out after the worker completed;
  read-only batch fetch recovered its terminal row without re-execution:
  SHA256 `53e6696f3196f7cc7fe7f0822c9df10c5e65f98feb2b1b24e71f175afc9adaba`.
  This verifies the worker result, not collector cleanup.

## Subsequent authorization

Main reports the user chose **both routes in parallel**: a separate
`bapa-transport` lane owns the transport/padding theorem; `bapa/finish` now
coordinates sized-sort re-port/search/Lean work for bapa-p1 through bapa-p4.
This does not change the feasibility findings or retrospectively finish the
missing per-obligation cutoff proof. Next shared deliverables are a native
no-nested-dispatch TLC wrapper, a no-given-helper search/closure-export runner,
and a symbolic-size Lean split-check recipe. The port lanes now retain the
existing models.ts registry; no `--models` hook is planned.

**All 29 canonical safety claims retain their previous bounded/fixed scopes.**
The separate slice-2 lock-server prototype already has symbolic tuple-domain
proofs, but does not retroactively change the canonical 67 declarations.

Next work, only after resolving this stop gate: choose an explicit countermodel
syntax and prove its transport in Lean, or authorize a direct certificate
translation/recheck route that does not pretend a cutoff has been established.
Do not run 29 searches to answer this missing semantic question. No step 2–4
implementation or final all-family Lean recheck was attempted here.
