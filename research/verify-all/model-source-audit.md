# IC3Syn model/source and supplied-knowledge audit (item 2)

Baseline: `6a3874d3f2c6febe40bb14775884cb327a2cce3c`, branch `claude/verify-all`. Scope: all 29 entries exported by `research/protocols/ic3syn/models.ts`; no production, proof, Lean, BFS or TLC jobs run by this auditor. No production files changed.

## Verdict

**The requested “exactly the protocol's own safety property” claim needs qualifications.** Each non-switch entry supplies one semantic safety goal; each switch supplies three goals for a four-clause source property, with reflexivity built into the representation. There are 33 explicit goal laws in total, not a hand-written inductive strengthening family. I found no `.facts`, `.prune`, rule `.keep`, or additional/seeded invariant family in these IC3Syn builders. The source's auxiliary invariants are not supplied to `p.laws`.

This is **not** a proof that the models equal every interpretation of their sources. All ports restrict sorts to at most 64 named elements; several replace arbitrary intersecting quorum families with majorities. MLDR uses a human-derived arithmetic characterization of quorum overlap. Setup phases and ghost summaries also require a correspondence argument. The source/model safety formulas match under the stated encodings, except that source typing and switch reflexivity are enforced structurally rather than explicitly proved as goal laws. No general refinement/equivalence certificate was produced here.

## Evidence, commands, and provenance

Read the user handoffs `VERIFY-ALL.md`, `COMMON.md`, and `AFTER-MLDR.md` in `/Users/monotykamary/VCS/working-remote/open-source/gdp-wired/private/handoff/claude-tracks-20261107/`, and `supercomputer --skill` before work. The branch and baseline were checked with `git status --short; git branch --show-current; git rev-parse HEAD`.

```
supercomputer run --jobs research/verify-all/model-source-jobs-20261109.json \
  --out runs/verify-all/model-source-20261109 --class interactive
supercomputer run --jobs research/verify-all/model-source-summary-jobs-20261109.json \
  --out runs/verify-all/model-source-summary-20261109 --class interactive
```

The first boat job fetches pinned source text, emits every numbered source line and SHA-256, statically inventories knowledge-bearing sites, and constructs `p.make()`/`p.laws()` for all entries **without invoking any prover**. `model-source-inventory-20261109.py` and `.ts` contain the exact commands/logic; `model-source-summary-20261109.ts` emits compact law/field/fact inventories and script hashes. No dependencies were installed. Receipts: first job exit 0, 1.52 s job, 21.1 s submission wall; summary job exit 0, 0.06 s job, 22.4 s submission wall. The summary confirms 29 protocols, 33 laws, all 29 with request assumptions, 20 with parameter preconditions, facts=[]/fns=[]/human=false for all, and two check-only keep predicates. First placement: `bx_25xas5gt`, large, AMD Ryzen 9 9950X, two allocated vCPUs, nonexclusive. This is an inventory, not a timing claim. Large evidence is in the two named `runs/verify-all/` directories, including `summary.tsv`, `placement.json`, and logs.

**Vendoring limitation:** there is no checked-in Endive or mypyvy source under this worktree's `vendor/` (which contains `gdp-ts` and `handwired`). The README explicitly says the sources are not copied into the repository. Rather than pretending a vendor copy was available, the boat audit retrieved the exact cited versions:

* Endive `will62794/endive@8b6f2abd1988eeb308f965813635e9871f253e2d`, `benchmarks/<file>`.
* mypyvy `wilcoxjay/mypyvy@12a8f5434a25587c56814d090b6ab7fa95851e71`, `examples/pd/paxos_epr.pyv`.

Every source citation below refers to those bytes, preserved as numbered text in `runs/verify-all/model-source-20261109/model-source-inventory.log` (abbreviated **L**). Source section headings contain URLs and hashes. Read these exact clauses, not just `p.safety` strings or README claims. All 30 source fetches succeeded (29 Endive files including the non-authoritative Paxos transcription, plus mypyvy).

Audited file SHA-256:

| File | SHA-256 |
|---|---|
| `research/protocols/ic3syn/models.ts` | `5d61b846a8331a9b7978b4809d53b88e5918135ded0fc6d527f2a6dc8fb3a601` |
| `research/protocols/ic3syn/common.ts` | `d84face9091688872b001f28d0ff31f1180590c57bf944efe6b32168651cd324` |
| `research/protocols/ic3syn/run.ts` | `a9fa1e966acf503db0804419f8af7b82cfec671f8fba528716ec5440ea70dd66` |
| imported `research/protocols/models.ts` | `ae2acd68175231e54e8590c2e35e04996282da22523d2fbac47d40e0adb078e4` |

## Per-protocol clause comparison and complete assumption classification

Notation: **M** = `research/protocols/ic3syn/models.ts`; all intervals include endpoints. `N=64` comes from `research/protocols/models.ts:20`. `lt(...)` means each argument `<64` (`common.ts:13`). “B” means a domain/typing bound: necessary for this chosen finite encoding, **not** an invariant supplied by hand, but a real restriction versus an arbitrary source sort. “Q” means a quorum guard (details below), not a trusted proof of safety. Each row lists the active builder's `.pre` and `.assume`; there are no other explicit assumptions in that builder beyond kind-generated input restrictions. Types/initialization and representation choices are discussed below.

| Protocol | Exact source safety clause(s) | `p.laws` match and encoding | Active `.pre` / `.assume`, other supplied structure |
|---|---|---|---|
| `consensus` | `Consensus.tla:37-38`: `TypeOK /\ Cardinality(chosen)<=1` | M:852-853 uses `one` at M:847: any two Chosen members equal. Matches cardinality conjunct; **TypeOK is structural, not an explicit goal**. | M:36 `v<64` (B); no `.pre`. Boolean Chosen starts empty. |
| `tcommit` | `TCommit.tla:57-63`: all RM pairs, not aborted/committed | M:858: St[a]=3 and St[b]=2 forbidden, all a,b<size. | M:45 size<=64; M:46 rm<size (B). Working/prepared/committed/aborted encoding 0/1/2/3. |
| `lock_server` | `lockserver.tla:57`: nonempty client lock intersection implies equal clients | M:863: for each server, Link(c1,s) and Link(c2,s) imply c1=c2; quantifying an intersection witness is equivalent. | M:61 c,s<64 (B). Semaphore initially true, Link false. |
| `quorum_leader_election` | `quorum_leader_election.tla:39`: isleader[i] and isleader[j] imply i=j | M:870: identical over i,j<size. | M:81 + shared M:74-77: size<=64, i,j<size, Q majority only on become_leader. Exact source majority at source:15. |
| `toy_consensus_forall` | `toy_consensus_forall.tla:44`: all vi,vj in decided equal | M:876 and `one`: Decided membership uniqueness. | M:91 + shared helper: size<=64, i<size,v<64; majority on decide (source:17). The duplicate Inv at source:59 is inside a comment, not another goal. |
| `simple` | `Simple.tla:82-83`: all pc Done implies some y=1 | M:886: exists i<n with pc!=2 OR y=1. This is the classical negation-of-forall rewrite on nonempty n. | M:104 n in [1,64]; M:105 self<n,v<=1. Source assumes N>0 at :22. B; no source `Inv` strengthening copied. |
| `simple_regular` | `SimpleRegular.tla:113-114`: same PCorrect | M:886, Done=3 instead of 2. Same existential rewrite. | Same M:104-105; source N>0 :61. Regular-register three-valued X encoding, not an auxiliary goal. |
| `lockserv_automaton` | `lockserv_automaton.tla:72`: two holds_lock nodes equal | M:892 `mutex`/`one`: HoldsLock membership uniqueness. | M:123 n<64 (B); held initially zero and messages false. |
| `sharded_kv` | `sharded_kv.tla:63-65`: table[n1][k]=v1 and table[n2][k]=v2 imply n1=n2 and v1=v2 | M:902: same five quantified arguments; table value v encoded as v+1, zero Nil. | M:147 n,v,n2,k<64 (B). M:150-164 setup owns each key at most once, matching source Init :44-50; not safety assumed on arbitrary live states. |
| `sharded_kv_no_lost_keys` | `sharded_kv_no_lost_keys.tla:65-67`: ANY transfer exists OR EVERY key has an owner | M:900-901: for every key, started implies owner exists OR some TransferMsg exists. Distribution equivalent after setup; this is **not** the stronger per-key-message property. | M:145 keys<=64; M:147 n,v,n2<64,k<keys (B). Setup requires every key owned at start, **explicit source Init assumption** :51-52, not discovered knowledge. Transfer existential unbounded over packed keys is justified only for well-formed reachable maps. |
| `lockserv` | `lockserv.tla:69`: two holds_lock nodes equal | M:910 `mutex`/`one`: matches. | M:172 n<64 (B), serverHoldsLock initially 1; no `.pre`. |
| `twophase` | `TwoPhase.tla:163-168`: no aborted RM coexists with committed RM | M:915: Rm[a]=3 and Rm[b]=2 forbidden. | M:193 size<=64, M:195 rm<size (B). No TM-prepared strengthening law supplied. |
| `simple_decentralized_lock` | `simple_decentralized_lock.tla:39`: two has_lock nodes equal | M:920 `one`: HasLock uniqueness. | M:220 src,dst<64 (B). One `init` picks sole holder (M:224-232), matching source existential initial holder :29-31. Pre-setup empty state satisfies uniqueness too. |
| `two_phase_commit` | `two_phase_commit.tla:102`: commit excludes abort; :103 commit implies all vote_yes; :104 abort implies abort_flag | M:926-927 conjoins the first two under DecideCommit(a), and third under DecideAbort(a), universally a,b<size. All three clauses retained, not merely agreement. | M:237 size<=64, M:239 n,w<size (B); w witnesses source Go2 failure/no-vote existential. abortFlag is actual updated state, not an assumed fact. |
| `consensus_wo_decide` | `consensus_wo_decide.tla:89`: two leaders equal | M:938: Leader uniqueness. | M:272-276 + shared helper: size<=64, i,j<size; majority on init and choose_voting_quorum. **Q-family restriction**, source constant Quorums :7. Chosen quorum stored by setup, not supplied invariant. |
| `consensus_forall` | `consensus_forall.tla:94-96`: any two decided (node,value) pairs have equal value | M:937: same four arguments. | Same as previous plus v<64. **Q-family restriction**, source constant Quorum :6. |
| `naive_consensus` | `naive_consensus.tla:56`: two decision values equal | M:947 `one`: Decision uniqueness. | M:311-312 + helper: size<=64,n<size,v<64; majority on collect_votes. Source constant Quorum :7. Voted ghost and Decide projection M:306-327, not extra laws. |
| `client_server_ae` | `client_server_ae.tla:54` and `ResponseMatched` :18: received(n,p) implies exists r: sent(n,r) and match(r,p) | M:960-961: same n,p forall and r exists, all <64. | Active M:333 with db=false: n,r,p<64 (B). Match chosen before start, source arbitrary initial relation :40 onward. |
| `client_server_db_ae` | `client_server_db_ae.tla:90` and `ResponseMatched` :25: identical provenance clause | M:959-960: native tuple `has` instead of packed get; same forall/exists. | **Active native builder** M:363-385, .assume M:367 n,r,p,i<64 (B), no `.pre`. Old db=true packed builder M:330 is not selected by this entry. |
| `simple_election` | `simple_election.tla:55`: two leader proposers equal | M:970 `one`: Leader uniqueness, proposer domain <64. | M:387-388 + helper: size<=64,a<size,p<64, majority on decide; source constant Quorum :7. Promised ghost updated with Promise (M:392-403), not assumed as a fact. |
| `toy_consensus_epr` | `toy_consensus_epr.tla:48`: decided values equal | M:974 `one`: Decided uniqueness. | M:405 + helper: size<=64,n<size,v<64, majority on decide; source constant Quorum :7. |
| `toy_consensus` | `toy_consensus.tla:46`: decision values equal | M:978 `one`: Decision uniqueness. | M:417 + helper: size<=64,i<size,v<64, majority on decide. Source defines majority at :15. |
| `firewall` | `firewall.tla:37-40`: sent(s,d) and internal(d) imply exists internal i with sent(i,s) | M:983-984: same forall(s,d), exists i and relation direction. | M:429 s,d<64 (B). Internal set initialized by setup, source arbitrary Boolean function at :28-31. AllowedIn is ordinary state with source updates, not a proof fact. |
| `majorityset_leader_election` | `majorityset_leader_election.tla:59`: two leader nodes equal | M:990: Leader uniqueness. | M:449 size<=64; M:453 n,m<size plus become_leader implies 2*count(Voters[n])>size. Guard counts actual state, source Majority :15; not an assumed reachable-state invariant. |
| `consensus_epr` | `consensus_epr.tla:110-112`: any values decided by any nodes equal | M:997: four quantified variables and two Decided memberships imply equal values, matching the source. | M:470-472 + helper: size<=64,i,j<size,v<64,nondet<=1; majority on become_leader. Source arbitrary Quorum; input nondet selects source send-vote alternatives. `SafetyWithTypeOK` :114-117 is not selected. |
| `learning_switch` | `learning_switch.tla:59` reflexive; :60 transitive; :61 antisymmetric; :62 successor chain | M:672-676, entry :1005: three explicit laws = clauses 2-4. Clause 1 built into `tabR` M:603 (`x=y OR T.has(t,x,y)`). **Not four explicit laws**, but matches the property on represented tables. | Active native builder M:607-620: size in [1,64] (:608), all ps,pd,sw0,sw1,nondet<size (:611). Source diagonal Init :41 onward; no later deletion. Check-only keep :1008 limits pending<5; not passed to proveRule. Source helper invariants :65-69 NOT supplied. |
| `learning_switch_i4` | `learning_switch_i4.tla:82-86`: reflexivity, transitivity, antisymmetry, successor chain | Same three M:672-676 laws; entry :1013 guards with started=1. Reflexivity structural via tabR. | Active native M:624-661: size in [1,64], packets<=64 (:625), p<packets and sw0,sw1,sw2<size (:628). Setup total src,dst and involutive no-self-link (:637-654) realizes source Init :64-73; these are source initial restrictions, not supplied inductive laws. |
| `paxos_epr` | **mypyvy `paxos_epr.pyv:81`**, `decision(R1,V1) & decision(R2,V2) -> V1=V2` | M:1022: same four quantified arguments. No proposal/vote/choosable invariant from source :84-97 passed in laws. | M:689-691: none<64,size<=64,n,w<size,r,v,maxr<64; shared helper majority on propose/decide. Replaces arbitrary intersecting quorum sort and arbitrary total order (:6-21) by majorities and natural order. Phased propose M:695-724 stores Q and scans voters; see limitations. |
| `mldr` | `MongoLoglessDynamicRaft.tla:170-178`: two primaries in the same currentTerm are the same server | M:1031: St[a]=St[b]=1 and CT[a]=CT[b] imply a=b. No other MLDR law supplied. | M:775 size in [1,64]; M:788-797 i,j<size, Boolean bounded S,Q2; pick implies S(j); become_leader majority of Config[i]; reconfig committed Q2 majority plus hx,hy exact floor-halves. Overlap arithmetic appears in **step guard** M:813-814, not as safety law. Setup picks nonempty initial config and copies it, matching source :142-149. Check-only keep :1034 bounds CT,CV<=2, not production proof. |

All source clauses are available verbatim in L. The source/law comparison does not rely on README line numbers.

## Knowledge-bearing sites and judgments

### 1. Request and parameter assumptions (all active sites covered above)

`overMajority`, M:74-77, expands into a size precondition, carried Q, exact request-member count, and a conditional assumption. `common.ts:19-22` requires Boolean Q cells, support below size, and `size < 2*members(0)`. For sources defining cardinality majorities this is a mathematical encoding of the action's parameter domain, **not a hand-added safety invariant**. The count must still have correct kernel/runtime semantics; this audit does not certify those.

For sources declaring **arbitrary** Quorum/Quorums (consensus_wo_decide, consensus_forall, naive_consensus, simple_election, toy_consensus_epr, consensus_epr, paxos_epr), it is a **restricted protocol family**, not equivalence to every allowed quorum family. Intersection is supplied by the quorum representation; it is not discovered by invariant synthesis. In particular the first two do not even constrain arbitrary families to intersect. Majorities may admit a full set omitted from a three-2-set TLC config; equality on that config is not automatic (`models.ts:940-945`). This is disclosed in the repository README, but “nothing supplied” without qualification obscures it.

Native relation sorts, Boolean/few-valued maps, enumerated `op` kinds, Nat values, Nil offset encoding, and bounds inject typing/representation knowledge. These are legitimate modeling choices, not mysterious solver facts. The finite bounds concern identities/sorts; MLDR's term/version counters themselves remain unbounded naturals in the production rule. They do mean that proving goal laws alone is not an independent proof of source TypeOK or well-formed map support. Quantifiers intentionally range over bounded domains; none establishes an unbounded-sort cutoff theorem.

### 2. `.facts`, `.pre`, `.prune`, `.keep`, seeds and unused alternatives

* `.facts`: zero IC3Syn builder calls; runtime machine inventories have no supplied fact family. No `.fns` call in these builders supplies axioms.
* `.pre`: exactly the active sites in the table (including shared helper and Paxos `none`); all finite-domain/nonempty constraints, no cross-state invariant precondition.
* `.assume`: exactly the active sites in the table; domain/typing, quorum parameter selection, and MLDR half-count witnesses. MLDR's constraints mention state because an action's chosen quorum must belong to the current configuration; they are not a universal assertion that safety is true.
* `.prune` and rule `.keep`: zero calls in IC3Syn models/common/run.
* `check.keep`: **two**, M:1008 pending<5 for learning_switch and M:1034 CT,CV<=2 for MLDR. Both reproduce source TLC StateConstraint (learning_switch:71, MLDR:202-205). `run.ts:18-20` uses only make/laws and never calls `check.keep`; these restrictions do not bound production proving.
* `p.human`: absent on these 29 entries. The imported sibling `research/protocols/models.ts` defines a `human` field and hand-written invariant families for **DuoAI**, but IC3Syn imports its constant `N` (and a type via common), not those law arrays. No IC3Syn entry calls them. Import-time sibling definitions are not proof premises.
* Unused legacy packed builders are still present: clientServer(db=true), learningSwitch and learningSwitchI4 (M:529-597), with exported `phased` at M:678. The active entries instead select clientServerDb, learningSwitchR and learningSwitchI4R. Their legacy assumptions are visible in the static inventory and **must not be double-counted as runtime premises**.
* Source invariants intentionally not copied: Simple/SimpleRegular's stronger `Inv` and explanatory proof, mypyvy Paxos's five invariants :84,87,90,93,96-97, learning_switch's commented helper laws :65-69, and consensus_epr's commented candidate family. The engine may synthesize similar predicates; that is not the same as `p.laws` supplying them.

### 3. Initialization, ghosts, and built-in safety

Setup adds constraints to the transition system and extra states. It is legitimate only if all source initial states and source steps are represented, and pre-setup states cannot execute live actions. Here the declared setup purpose is visible in the code: unique/complete owner assignment for sharded KV; one initial lock holder; arbitrary match/internal tables; total src/dst and perfect matching for I4 switch; one arbitrary nonempty initial MLDR config copied to every server. No equality-to-source theorem is checked here.

`Voted` in naive_consensus (M:306-327) and `Promised` in simple_election (M:387-403) are manually maintained summaries of a relation's nonempty row. They enable guards; they are **extra modeled state**, not supplied law premises. Their relation to source state needs an inductive correspondence argument.

Switch reflexivity is qualitatively different: `tabR(T,t,x,y)= (x=y) OR T.has(t,x,y)` (M:603) makes one source safety conjunct true by representation. This is supported by source diagonal Init and no deletion of the diagonal, but not separately proven as a goal. Report this as **source-derived representation knowledge / partial safety baked in**, rather than “all safety clauses independently proved.” Transitivity, antisymmetry, and successor-chain remain three actual goals.

### 4. MLDR arithmetic: necessary modeling derivation, not an invariant supplied to proveRule

Let X=config[i], Y=S, dx=|X\\Y|, dy=|Y\\X|, m=|X intersect Y|, hx=floor(|X|/2), hy=floor(|Y|/2). Every majority of X must consume at least max(0,hx+1-dx) common elements; likewise Y consumes max(0,hy+1-dy). Disjoint majorities exist exactly when those two minima fit into m. Therefore all majorities intersect iff their sum exceeds m. This is the arithmetic guard M:813-814, with natural truncated subtraction; M:794-797 constrain hx,hy to the exact floors. Counts M:780-787 compute cardinalities, not guessed invariants. For the nonempty configurations used by active reconfiguration this is a valid finite-set argument; no machine-checked equivalence lemma was supplied or run here.

This derivation is hand-supplied **semantic structure**. It is not the MLDR inductive invariants that a prover is supposed to discover, yet it exposes useful arithmetic unavailable in the source's raw quantification over sets. Distinguish those claims. `AFTER-MLDR.md` expressly identifies it as chosen with knowledge of the invariant.

### 5. Paxos provenance and limitations

The safety goal is **not** the Endive `paxos_epr.tla` protocol. That file has a different decision arity and known defects: `Decide(n,r,v,Q)` at :102 versus invocation `Decide(n,v,r,Q)` at :125; unchanged left_rnd at :80; and the Propose universal's vote argument at :88 reads maxr where the antecedent ranges mr. I read these source lines; no behavioral rerun is claimed. The authoritative comparison above is mypyvy :81 and transitions :38-77. The source's quorum intersection axiom :21 is realized only by majorities; source total-order axioms :15-18 by finite natural order. The model's phase checks the original propose guard over one node at a time (M:695-724); failure projects to a stutter and successful end adds Proposal. The safety law itself is not busy-guarded: Decision is unchanged during the phase.

The inline `paxosTla` M:727-765 is another **hand-written transcription by the same project**, not independent evidence of source equivalence. Agreement with it does not eliminate a shared translation mistake. No claim of verification of arbitrary quorum systems, unbounded rounds, or all source total orders follows from this bounded representation.

## Harness and overfitting conclusions

`run.ts:13` labels a result proven **only if `v.proven && v.checked`**. `run.ts:18-20` builds `r=p.make()` and `laws=p.laws(r)` and passes exactly those to `proveRule(r,laws,{search:{ms}})`. It does not select a human invariant family. The broken path constructs its own model with the named mutation and reuses p.laws. `run.ts:9-10` reads argv (ms/only/skip); there is no environment/file read in models.ts/common.ts/run.ts that selects per-protocol answers. `check` metadata, including fix scripts and keep predicates, are not read by this path.

**Limit of this audit:** this is a direct harness/model inspection, not a transitive no-environment/no-file proof about core/kernel imports. Those imports contain configurable engine code and require the separate item-5 audit. Absence of model-level knobs does not establish absence on every proof path.

`AFTER-MLDR.md` was found and read. Its overfitting section describes (1) benchmark-shaped scope gates, (2) benchmark-tuned constants and GDP_* knobs, (3) MLDR QuorumsOverlap arithmetic and “P*” ports chosen with hindsight, (4) repeated tuning on the same 29+10 protocols. It also asserts earlier TLC exactness and no hand laws; those are prior claims, **not evidence rerun by this audit**. “P*” is not an exported protocol id at this baseline; Paxos is the obvious related phased port, but the handoff does not uniquely define the alias. Do not invent a stronger identification. Source-law fidelity does not rule out overfitting in candidate grammar, search heuristics, encoding, or benchmark selection.

## Failures / not established

* No local vendored copies were available; exact pinned source retrieval succeeded instead. File hashes and full numbered content are retained in L.
* One exploratory `pi.grep` regex was rejected (`unclosed group`) before any match or modification; retried with shell ripgrep and the boat Python inventory. One report-edit tool program was rejected at TypeScript type-check before execution and retried with JSON payloads. No source fetch, runtime construction, or inventory job failed.
* No arbitrary-size correspondence/cutoff proof, refinement/bisimulation proof, source TypeOK proof, independent checking of MLDR arithmetic, transitive engine-knob audit, or production-result validation was performed in this task.
* Previous README assertions and TLC results are not substituted for new evidence. The strongest justified statement is **33 declared semantic safety goals, no hand-seeded inductive family in these model builders, with material and enumerated representation/domain assumptions**.

## Pinned source hash ledger

All are SHA-256 of fetched bytes, before adding line prefixes. Full source paths and URLs are in L.

| Source file | SHA-256 |
|---|---|
| Consensus.tla | `5e0bb2d31ac83b557e48b53b04817fc91a7a71771b09bcf6d7fea79a233723c3` |
| TCommit.tla | `da3d6a2b8c868ae278d765c6fa71b6c3d88e38dc8744bb0c10b4659fba3f1239` |
| lockserver.tla | `0bd06d96896a4d46aae2cd3e23c05cd47de0435d3b2889f943cdb1e8c9a299a4` |
| quorum_leader_election.tla | `b9ea61f40a2e610cf2b3c0b5171c75a00330fb17390c3192ca8c37f20efa5acb` |
| toy_consensus_forall.tla | `2127111f3b127ef5027922299e0cc2afa54f8d481a13573b443d126832f92bdf` |
| Simple.tla | `8bf6d786fc4cd19a1aef7de7367014332a2e453dc91f9b7df8e63377be35568f` |
| SimpleRegular.tla | `5b1ac9d0f48f2b51bfc9b39bab2c0a0d8305f0ddc1561f1d265a80a296e8dfd2` |
| lockserv_automaton.tla | `0ba2621c7a81aa1b4bccc09592bf7cd84ee16b8ab09d9c4a870ff2aea470e3f7` |
| sharded_kv.tla | `01118a65b28f1e28171e4727999aa8cdd44e542b6e556b7c2a4e05a55d0b48da` |
| sharded_kv_no_lost_keys.tla | `be7475450f677e5926f81c9d3644636630447e66c26ea77f66b449fbfc1817fa` |
| lockserv.tla | `87ea36326c8432bdb4a8b669b4294b5b717bd500f44f7faf987452795ca17a77` |
| TwoPhase.tla | `0f0ce7adf47bb427976a5ccc48b35887e10240e3a72239d50eadc26ce91010da` |
| simple_decentralized_lock.tla | `13ae038722fe4aa05b40669c7aaffa11247f12ef5a29db0f2503af7f2c0cab25` |
| two_phase_commit.tla | `a30bc5ce9c5bb357fc851762d5ce5b2e53b6a73616505819658283b2c97f37f8` |
| consensus_wo_decide.tla | `0bc5b0262bb27dd2dfe725dedc11cab9e666b0b60cd5d4184f8994b5c2e8cad5` |
| consensus_forall.tla | `52e9e1d7cfc9e7d4470bca9703dc24be3c4741a3b1950b231e8881efaf264519` |
| naive_consensus.tla | `63cdc8ecfeafd9e423cf0448afbd33ff7bb00f2e76d222ef026bd215e7f5e64f` |
| client_server_ae.tla | `6296d3bef08242be47b5d4f74a2e79790860e83cd0f366a83d82a0b7c1aaec3a` |
| client_server_db_ae.tla | `c10176c22e57b310d119a526d18e7eec474919aa5e6d0794e221f70ab8e59f68` |
| simple_election.tla | `85ea848525a9193aa6ace230a2b40a55049b2af8dcb0fd5e257229d08a3f0c15` |
| toy_consensus_epr.tla | `c40b96281fc1c188df63354f53df981e8a392daeba91cbf06481fbe4158c17e1` |
| toy_consensus.tla | `b9cbdff843ed1bcd6a6925a6b0e8562756041e777e674d24b2a611067c4c35af` |
| firewall.tla | `cfbd024e6d315b46555222615d6c790091c19a014af9c662fb835f1a6b317fd8` |
| majorityset_leader_election.tla | `2561cec2c9b826408ca4c0a3567c120426f23abcfccd8e1aa257339130d8766b` |
| consensus_epr.tla | `4daa0c7740ae6596a38fba52a66bbd1c14093af9dac9bf90776197921a2c2d90` |
| learning_switch.tla | `a05b9c942b5dddc17d1320e3c5f8c4d75be996d1da4a3f862e71207d85d3192d` |
| learning_switch_i4.tla | `fac1fd0be2f2ed7c42cb24ead57f2c00bfb67bee40f164808a1e71bafa9affca` |
| MongoLoglessDynamicRaft.tla | `c09dd60a54f2dc66c2f58087bbeb49b7686be0425f8af3eb1f10a9299ae73e8e` |
| paxos_epr.tla (not authoritative) | `f466e55f144a8660d3372f4e9d109e46c2b0e3f0e12d3f1e0294638c098312d5` |
| paxos_epr.pyv (authoritative) | `b19d164c17601768b12342573256e5b802c9b30b5b2ec62e1679ffefe49f8ebd` |
