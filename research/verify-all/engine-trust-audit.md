# Engine trust audit — VERIFY-ALL items 5 and proof-path part of 2

Baseline: `6a3874d3f2c6febe40bb14775884cb327a2cce3c`, branch `claude/verify-all`. Auditor: `engine-trust-audit` / `862592db`. All source citations below refer to this baseline, not the older `8610af26` discussed in AFTER-MLDR. Scope is static dependency, answer-encoding and acceptance-path review; **no proof, TLC, Lean, ablation or production rerun was performed by this auditor**.

## Finding

**No protocol-name dispatch or stored protocol-specific proof/law family was found on the IC3Syn production import path. This is not a clean bill of generality.** Production contains explicitly benchmark-shaped structural gates, hand-programmed *generic candidate templates*, tuned caps, and many environment-controlled strategies. Those can change which results finish inside the budget. Candidate proposals are not automatically accepted: the inspected final acceptance paths reconstruct obligations and invoke a checker. Static inspection does not prove that either obligation generation or those checkers are sound.

The narrower item-2 condition is supported: `run.ts` neither sets environment values by protocol nor reads a protocol-specific answer file. The stronger literal statement “the proof path reads no environment knob” is **false**. The census finds 86 distinct uppercase dotted environment accesses in the conservative DSL import closure (including four non-`GDP_` names), versus 110 across all scanned source. Diagnostics are included; this is an access census, not 86 independent algorithm switches. `supercomputer.toml:7` globally sets `GDP_CYCLIC_LOG=1`, not per protocol.

Important correction to the prior audit: `kernel/prove.ts:1982-1984` says `GDP_STRICT` is off by default, but executable `:1988` uses `env.GDP_STRICT !== '0'`: strict confirmation is **on by default for the non-usual decideLaw route**. `:1985-1987` documents the change. Do not repeat the stale comment as the current behavior. `strict(usual)` explicitly exempts the usual route; see `:1839-1853` and the final checked set at `:1872-1904`.

## Evidence and reproduction

Hypothesis tested: a protocol identifier, safety-law literal, environmental selector, file read, or structurally specialized candidate family could supply information or bypass the final checker. We deliberately searched broad fragments and nonproduction files too, then separated availability in the repository from reachability from `core/dsl.ts`.

Commands (launched from this worktree; scans executed on boat):

```sh
supercomputer --skill
git status --short
git branch --show-current
git rev-parse HEAD
supercomputer run --jobs research/verify-all/engine-trust-scan-862592db.jobs.json --out runs/verify-all/engine-trust-862592db-v4 --class interactive
supercomputer run --jobs research/verify-all/engine-trust-census-862592db.jobs.json --out runs/verify-all/engine-trust-census-862592db-final --class interactive
```

The compact scanner is `research/verify-all/engine-trust-scan-862592db.ts`. It recursively reads **all 303 files** under `core/` and `kernel/`, not just TypeScript or non-tests. It hashes every source file, extracts every literal `id`, `ic3syn` and `file` value from the protocols declaration (both ternary arms), adds their underscore/hyphen/dot fragments, and scans case-insensitively. Generic fragments such as `keys`, `simple`, `client`, `decide`, `switch` and `regular` intentionally generate false positives. Other passes cover law construction/name tests, environment accesses, filesystem/dynamic imports, and structural risk vocabulary. A conservative relative-import closure includes type-only imports; it is not a dynamic execution trace.

Protocol identifiers covered: consensus, tcommit, lock_server, quorum_leader_election, toy_consensus_forall, simple, simple_regular, lockserv_automaton, sharded_kv, sharded_kv_no_lost_keys, lockserv, twophase, simple_decentralized_lock, two_phase_commit, consensus_forall, consensus_wo_decide, naive_consensus, client_server_ae, client_server_db_ae, simple_election, toy_consensus_epr, toy_consensus, firewall, majorityset_leader_election, consensus_epr, learning_switch, learning_switch_i4, paxos_epr, mldr. Aliases and source filenames are in each log's `TOKENS` record.

Recovered full evidence: `runs/verify-all/engine-trust-862592db-v4/{names,knobs,io,shape,laws}.txt`; each has a manifest and complete matching file:line locations, with long source lines clipped to 600 characters. Match-line counts respectively: **5117, 488, 262, 2718, 2707**. Counts overlap and are not counts of findings. Each corresponding `.log` contains gzip/base64, with begin/end sentinels. Decode by extracting the one line between `AUDIT_GZIP_BASE64_BEGIN` and `AUDIT_GZIP_BASE64_END`, base64-decoding and gunzipping. Local decode commands only unpacked the boat evidence; they did not scan repository source or run the prover.

v4 batch: `20261109-085524-vdyd35`, tree `5c0f3b004daa`, image `sc-f0d8daeee6c3`; five jobs, all exit 0 on boat (0.11–0.15 seconds each; 30.7 seconds orchestration wall). These are scan times, not proof timings. v4 script SHA256: `dfb9cec43f1bf1aa28a781b18959a8fbfe0b488fd489e44281af8abe79890b88`. The later census only expands reporting; its separate script hash is recorded in its artifact and below.

### Failures and limitations

Initial single-output scan (`runs/verify-all/engine-trust-862592db/`) exited 0 but exceeded the 400 KB stdout retention limit: it is **incomplete evidence**. gzip alone (`-v2`) and clipping source lines (`-v3`) also exceeded the limit; both begin sentinels were missing and decode correctly failed with `missing payload`. Splitting into five independently bounded section jobs (`-v4`) recovered all sections. No incomplete artifact is used to claim absence. All these jobs completed; no process or waiter is left running. No external solver, cache clear, branch switch, commit, push, cleanup, or protected-source edit was used.

Regex/import-graph review is not a proof against obfuscation, generated code, ambient runtime mutation, a preload supplied by the invoking shell, or a bug in generic reasoning. The harness environment actually present during Main's production reruns remains Main's evidence to record. The scanner checks safety-law *names* in addition to generic `.law` construction; it does not prove semantic inequivalence of arbitrary handwritten formulas. Clause-by-clause model/source comparison belongs to the other item-2/model audit.

## Acceptance path and trust boundary

| Stage / citation | Verdict effect and trust status |
|---|---|
| `research/protocols/ic3syn/run.ts:5-12,16-23` | Imports the local DSL and models, filters IDs only to select jobs, calls `p.make()` then `p.laws(r)`, passes only `{search:{ms}}`. The broken path calls the same code on `p.make(p.bug)`. No local file read or environment assignment. `verdictOf` at `:12` emits `proven` **only** for `v.proven && v.checked`; then run-bearing results are `refuted`, otherwise `unknown`. Exceptions become `out.error`, not proven. The stdout serializer does not export the accepted certificate. |
| `core/dsl.ts:2747-2775` | Adds sums/divisor bookkeeping, first tries interpreter-backed refutation, then branches on the machine's **count declarations**, not ID. Counts call `searchCounted`; `checked:c.proven` at `:2758` is not itself a separate check — it relies on the checked finish below. Other machines call `proveLaws` with kind laws. |
| `core/dsl.ts:2628-2632;1866-1882` | Kind laws are constructed from declared kinds, added unless a supplied law has the same name; these are generated obligations, not a hidden protocol safety theorem. Name identity is infrastructure used for indexing/deduplication, and should not be confused with semantic identity. |
| `core/counts.ts:389-411,422-450` | Counted machine is extended with syntax-derived count definitions; callers plus candidates are scheduled. `:423` refuses missing caller objects. The *only successful family finish* at `:430-449` checks the whole retained set with `checkCountedLaws`, including optional checked lemma cuts, before returning proven. |
| `kernel/kernel.ts:2059-2092` | Reconstructs each retained law's start and step goals from the actual machine, PRE and assumptions. Every obligation must have a certificate with fresh witnesses and pass `checkMC`. |
| `kernel/kernel.ts:2039-2052` | Checks declaration binder separation, typed/valid reads and picks, witness capture, then rebuilds counted hypotheses and calls the goal/lemma checker. These generic count identities, not a protocol-special axiom, are trusted semantics. |
| `kernel/prove.ts:1872-1904` | Fast set prover can reuse decisions/cores, but widens each proof into its current reconstructed obligation and ends with `checked:checkLaws(m,laws,proof)`. Individual `proveLaw`/decide results during search are not the harness acceptance gate. |
| `kernel/prove.ts:2116-2172,2215-2231` | Usual prover can defer the ordinary check while translating to a cyclic certificate. A successful cyclic certificate supplies the check; translation failure falls back to `checkLaws`. `usualCheck` is mutable internal state, not a direct env “trust me” knob. Its correctness/lifetime remains part of the implementation trust base. |
| `core/cyclic.ts:1200-1210,1240-1276` | Cached cyclic certificates are keyed by machine/law/instance representation and retained only after proven-and-checked success. Certificate mode defaults to cyclic; cross-check mismatch throws unless LAX, while certificate failure falls back. LAX suppresses an auxiliary cross-check exception, not the final primary checker. |
| `core/dsl.ts:2837-2991` | Generic bounded runs, k-induction, discovered function lemmas, fresh-name laws, ghosts, inferred invariants and map sums can strengthen/search the proof. Successful branches require checked child verdicts. Ghost fallback at `:2924-2933` checks machine equality, original law binders/body and ghost conditions. This is a significant additional trusted obligation/bridge surface. |

## Every substantive production-name hit and benchmark-tuning risk

All direct protocol-specific hits found in production logic files are **comments/examples**, not string comparisons selecting a protocol. The generic code adjacent to these comments is still verdict-relevant through search success/cost. Below, **S** means may alter success/unknown/refuted classification or timing, but does not itself license a proof; **T** is trusted semantic checking; **N** is explanatory text only. No claim of portability follows from an S classification.

| Baseline file:line(s) | Hit / classification and effect |
|---|---|
| `core/counts.ts:75` | N: leader/vote explanation of copied-set bound proposal. S: the generic guard generator at `:65-182`, detailed below. |
| `core/dsl.ts:2645-2652` | N: sharded-KV cost example; S: per-trial/refutation work budgets affect whether a broken run is found. |
| `core/dsl.ts:2997` | N: firewall cost example; S: existential cone path's allocation/strategy, not a firewall branch. |
| `core/exists.ts:135` | N: leader/majority example in small-state exploration; S: sampling is only candidate screening. |
| `core/infer.ts:395,909` | N: quorum/Leader vocabulary explaining generic view and key-sort handling. S: type/view coverage affects generated templates. |
| `core/infer.ts:1257,1278` | N: quorum-shaped requests and sharded-KV sampling cost; S: model-to-request reconstruction and sample admission limit. |
| `core/infer.ts:1863-1864` | N: decentralized-lock/Leader/VoteRequestMsg timing example; S: `joinGrowEpr`/work allocation from `:124` constrains search. |
| `core/infer.ts:2444,2657` | N: leader-depth and decentralized-lock comments; S: sampled states / candidate selection, not an assumed invariant. |
| `kernel/cdcl.ts:754-758` | N: paxos-hand elimination cost; S: generic simplex-point versus elimination route. This is a historical tuning disclosure, not evidence that Paxos was independently held out. |
| `kernel/epr.ts:17,331` | N: Leader/Msg examples; generic relation/tuple encoding and wrong-sort cells, not map-name lookup logic. T/S: encoding correctness and EPR search are trust/performance surfaces. |
| `kernel/kernel.ts:1837` | N section title “quorum facts”; T: generic finite-count rules, definitions and freshness/typing checks at `:1840-2092`. |
| `kernel/prove.ts:460-474` | N mentions i4 learning-switch, consensus_wo_decide and ring_leader_election. S **confirmed benchmark-shaped gate**: `wideEprUnits=2_000_000`; `tupledScope` tests tuple-pattern shape, and selects wide/EPR routes. No protocol-name condition, but its comment explicitly explains retaining benchmark rows. |
| `kernel/prove.ts:1190,1342` | N: sharded-KV examples; S: instantiation fairness and related-tuple cap. |
| `kernel/prove.ts:1687` | N: toy-consensus model cost; S: relative model/search allocation. |
| `kernel/prove.ts:1796` | N: sharded-KV enumeration example; S: model-round widening policy. |
| `kernel/prove.ts:1912` | N: “wo” leader/quorum law example; S: using thinned/EPR decisions before ordinary search, then final widen/check. |
| `kernel/prove.ts:1982-1988` | N: decentralized-lock timing and stale “off” comment. S: strict model confirmation; **current default on**, override `GDP_STRICT=0` can restore the unconfirmed-answer route. Final proven families still require their checker. |
| `kernel/prove.ts:1993-2004` | N: distributed_lock comment at `:1998-1999`. S **confirmed benchmark-shaped gate**: sort-place refinement enabled only when some map has multi-part zero pattern. Reads structural patterns, not the identifier. |
| `kernel/prove.ts:2036-2037` | N: Votes/VoteMsg/VoteRequestMsg example; S: generic merging of same-pattern, same-sort key classes. |
| `kernel/prove.ts:2103-2110` | N: sharded-KV no-lost-keys benchmark cost; S: EPR set-first attempt requires fast shape plus multi-part zero patterns. |

All remaining fragment hits are either ordinary compiler/mathematical vocabulary (e.g. `switch`, `simplex`, `keys`, `regular`, `commit`) or outside this import closure. These are preserved, rather than hidden, in `names.txt`. They are **not per-protocol constants or identifier dispatch**.

## Handwritten laws versus handwritten generic candidate families

“Nothing written” cannot mean that the engine contains no human-written invariant templates. It does. The relevant distinction is whether a template proposes a formula derived from the caller's syntax and is checked, or supplies a protocol theorem as trusted input.

| Source | Classification / proof effect |
|---|---|
| `core/carry.ts:82-139` | S: copy retained inputs/sets into guarded candidate implications. Formula names use a structural hash and fresh binders. Not a stored Paxos law list. |
| `core/carry.ts:140-178,232-284` | S: monotone point/interval co-writes and point/point implications; retains source bounds and checks syntax. Can favor Paxos-like encodings. It proposes candidates only. |
| `core/carry.ts:179-231` | S: global range and frame candidates, with exact entry-copy, init and preservation eligibility tests. This is handwritten semantic pattern recognition, not general invariant synthesis. |
| `core/carry.ts:347-409` | S **scan-prefix family**: recognizes increment/reset/hold scan counter, active mode and negative quantified row flag; emits entry-reset plus prefix universal law, collision-checks names. Exactly the risk family mentioned by COMMON, now present generically on this baseline. Caps: 8192 work / 64 packets. |
| `core/counts.ts:65-137` | S: bound-lifting from counted-set guard to stored set or relation; adds *definitions* of counts and proposes preservation laws. Must not describe these as caller-supplied safety facts. |
| `core/counts.ts:138-182` | S **Paxos-shaped future-writer family**: recognizes three packed coordinates with coefficients `N²,N,1`, emits a count of prior/potential writers and cross-round/cross-value exclusions. It has no Paxos string, but is structurally specialized and may overfit the representation. |
| `core/counts.ts:258-319` | S: small-state maxima, guarded row uniqueness, two-literal cubes, guard loosening, scan-prefix and carry are filtered for scope and `trueSmall`, then proved. Passing small samples is **not** certification. |
| `core/count-support.ts:111-119,330-514,872-945,995-1063,1067-1190` | S: finite work/instance budgets, count read reservations, coordinate projection **as term proposals**, sparse PRE support, structural context filtering, priorities. `counts.ts:794-819` widens local successes and checks lifted obligations. Generic but elaborate, highly representation-sensitive logic; no projection is itself an equality premise. |
| `core/counts.ts:372-381,455-556` | S: support families change ordering, budgets, demand scheduling and reuse. Caps include 5000 counted / 4800 wall per structural attempt; `core/count-support.ts:1185` caps live selections at 10. Not an acceptance exemption. |
| `core/infer.ts:1-31,111-149,2674-2704` | S: handwritten grammar of linear bounds, cubes, views, joins and relational supports; controls include 24/96 initial cubes and width choices. Claimed genericity is not validated on held-out models here. |
| `core/lemma-cuts.ts:1-13; core/counts.ts:417-450` | S/T boundary: optional reusable conditional proof cuts; final full counted checker validates any changed certificate. No invariant/answer import. |
| `core/count-facts.ts:1-5,63-66`; `core/fixtures/count-facts.ts`; `kernel/fixtures/count-facts/`; `kernel/countmachine.test.ts:1,97,207-296`; `core/scan-prefix.test.ts:7` | **Outside production closure.** Generic opt-in count proposer, captured handwritten goals/certificates and Paxos-specific regression tests exist in the repository. They cannot affect this harness merely by existing. The literals `one value decided`, “decision has votes”, “choosable”, “busy rows”, Decision/Proposal examples in archived fixtures are disclosed; not loaded by DSL/run. |

The relevant MLDR risk is not a hidden `mldr` switch: `research/protocols/ic3syn/models.ts:1029-1037` selects the real safety property, and its construction's QuorumsOverlap arithmetic/representation belongs to model audit, outside `core/`/`kernel/`. No production CT/St/CfgT/Primary-name recognizer or MLDR-specific theorem was found by the structural pass. A source-exact behavior check would still not prove that its representation was chosen without knowing the invariant. Similarly the historical P* label cannot be interpreted as an independent Paxos validation from this scan.

## Benchmark-associated gates, caps and constants (current baseline)

This table separates numerical choices from protocol-name comments. All are generic eligibility/budget choices, not trusted protocol facts. A positive proof still needs the final gate; nevertheless they can decide whether the measured run returns proven before timeout. This is not an ablation or a count of independent tuning decisions.

| Exact location | Current choice | Association / verdict effect |
|---|---|---|
| `core/dsl.ts:2631-2652` | per-trial 10,000; pilot 60 trials, depth 6, bound 3 | Sharded-KV example explains law-evaluation work cap; counterexample discovery/completeness. |
| `core/exists.ts:138-143` | small-state cap 3000, work 300,000; fast step after 1000 | Leader/majority sampling context; candidate screen coverage, never proof by finite-state observation. |
| `core/infer.ts:113-124` | engine share 0.95; join query 8000; EPR 300,000; work 400,000 | Ring and decentralized-lock timing rationale; search allocation. |
| `core/infer.ts:124-125` | request 150; walk 8; pairs 10; raises 2; sparse 4; coefficient 1000; extras 24; tries 40; bits 7; keys 128 | Human-tuned generic join search breadth. |
| `core/infer.ts:1277-1280` | reject sample when law tuple cost >1,000,000 | Explicit sharded-KV five-key example; may lose helpful reachable samples. |
| `core/infer.ts:2439-2451` | split tuple-map view when >48; row budgets 8000 relational /20,000 otherwise; fallback 3000 | Leader-depth comment; affects relational proposal coverage. |
| `core/infer.ts:2688-2702` | tiny whole pool <=16; initial cube set 24 ordinary /96 relational; width 2 /3 | Learned-cube order/coverage; handwritten grammar not stored answers. |
| `kernel/prove.ts:324-326` | CDCL share 0.75; quick cap 16 (64 fallback described nearby) | Search route allocation; no protocol dispatch. |
| `kernel/prove.ts:366-375` | wide goal >=256 hypotheses, terms >=40,000, share 0.25 | Wide relational goal handling; may affect success and memory. |
| `kernel/prove.ts:460-475` | wide EPR 2,000,000; tupled zero-pattern gate | Explicit learning-switch / consensus / ring benchmark retention. |
| `kernel/prove.ts:1238-1240` | model share 3; floor 1000 | MBQI/model retry timing versus tree search. |
| `kernel/prove.ts:1342-1345` | related tuple max 512; matching work 8192 | Explicit sharded-KV 24,608-tuples example. |
| `kernel/prove.ts:1794-1799,1842` | retries up to four times model rounds while budget remains | Explicit sharded-KV sixth-round success rationale. |
| `kernel/prove.ts:1981-2000` | sorted on; strict non-usual confirmation on; sort-places on only tuple zero patterns | Decentralized/distributed-lock benchmark scope, with stale strict-default comment corrected above. |
| `kernel/prove.ts:2103-2110` | set-first on only fast/EPR shape, some multi-zero tuple pattern | Sharded no-lost-keys cost rationale; early route plus checked fallback. |
| `core/counts.ts:40,380-381,468-475,528-531,627-632` | pool 1000; structural budget cap 5000; wall 4800; initial selection <=10 | Structural-support scheduling, not a quorum size assumption. |
| `core/count-support.ts:111,1185`; `core/carry.ts:84,350` | proposal work 65,536; live selection <=10; carry/scan work 8192 | Hard truncation of generic proposal space; check still required. |


## Environmental and filesystem influence

`core/solver.ts:19` captures the live process environment object. Strategy toggles are read through `env` (and the DSL alias `knobs`); they are not frozen per proof. Therefore a caller, preload, or shared process can influence a run without editing the protocol model. Most knobs change search/sampling/budgets/cache behavior, and hence finite-budget verdicts. The final-check routes inspected above do not read a knob granting a protocol theorem or skipping the final check entirely.

Special cases worth distinguishing:

* Certificate routing: `GDP_CERT`, `GDP_CERT_SEARCH`, `GDP_CERT_MS`, `GDP_CERT_STEP_MS` select which certificate is attempted and how much time it gets; `GDP_CYCLIC`, `GDP_CYCLIC_ROUTE`, `GDP_CYCLIC_LAX` govern an additional comparison and whether mismatch raises an error.
* `GDP_STRICT` and `GDP_REAL_MODELS` affect how proposed countermodels are treated. They are not merely logging. Main should record their inherited values (or absence).
* `GDP_COUNTS_GIVEN` suppresses inferred candidates, `GDP_COUNTS_*`, `GDP_COUNT_LEMMA_CUTS` affect count search/support. None is selected by `p.id` in `run.ts`.
* `GDP_INFER_TRACE`, `GDP_COUNTS_TRACE`, `GDP_CYCLIC_LOG`, other TRACE/DEBUG/PROF knobs are observations; their runtime overhead can still matter under a wall deadline. `GDP_CDCL_VERIFY` is an additional consistency check, not just trace output.
* Public mutable observers/state exist: `countsDump.on` (`core/counts.ts:34`), `proveDump`/setter (`kernel/prove.ts:197-198`), `decideHook` (`kernel/epr.ts:94`), cached decisions, and `usualCheck`. The original harness does not install these hooks. A research preload is not equivalent to the unmodified command without separately auditing it.

The I/O pass found **zero matching lines in the conservative DSL import closure**. The 262 repository-wide hits are outside it: CLI config/source reads (`core/cli.ts:26,104-109,159-163,341,818-827`), language extractors/readers, compilation/conformance runners, and tests/fixtures. They can affect *other entrypoints*, but are not evidence that this direct `proveRule` harness reads protocol answers from disk. This absence claim is limited to the static spelling/import review described above, not arbitrary ambient JS behavior.

## Conclusion for Main

Supported: no protocol identifier/name-based proof shortcut found; no production-loaded captured law family; harness success is `proven && checked`; final counted/ordinary/cyclic acceptance is checked; no per-protocol env assignment/file read in the original run path.

Not supported: “the engine contains no hand-programmed invariant knowledge”, “there are no environment controls”, “every structural optimization is representation-independent”, or “the 29-row success rate demonstrates held-out generality”. Explicit benchmark-shaped gates and specialized generic templates remain. Independent certificate replay, actual inherited environment, model fidelity, failure replay and production counts remain Main/other auditors' work. This report must not be substituted for those results.

## Hash anchors

| File | SHA256 |
|---|---|
| `research/protocols/ic3syn/models.ts` | `5d61b846a8331a9b7978b4809d53b88e5918135ded0fc6d527f2a6dc8fb3a601` |
| `research/protocols/ic3syn/run.ts` | `a9fa1e966acf503db0804419f8af7b82cfec671f8fba528716ec5440ea70dd66` |
| `core/counts.ts` | `a010366e341b4fb162b0e22acef951980c0a8db297fe1273395d433fdaa7196e` |
| `core/infer.ts` | `611af51e3924d83b4102bc3d3ba84b4672789c3eb11e97b43b951a8ded71eaf6` |
| `core/solver.ts` | `d3fa9d9ec582b5899542ff32214ce20d9ffc8c8838d8b216063a86b8530e32fb` |
| `core/check.ts` | `9ae2d3c4323dd1e22d02219c1f33dcd92dfc6856a7500e969b43232d2fa6fd5b` |
| `kernel/prove.ts` | `c52fdeece6b9471aa1b0b957cac6aec72267543b568d764ea5438543d90205fb` |
| `kernel/kernel.ts` | `7ec8b310d23fab7eb3ba452b659e7051ceefe97aea01ffa6f16d990a7bea7f33` |
| `kernel/epr.ts` | `7c079dfd4f6ae35bd067a3e37eb13c37c148caa3d67fae71443e2a34c7dda5eb` |

The complete per-file manifest, not just these anchors, is embedded in each recovered scan section.

Final census batch `20261109-085821-8p1rcl`: boat tree `6a50173df4d0`, image `sc-f0d8daeee6c3`, exit 0, 0.10 s scan / 25.8 s batch wall. Final scanner SHA256 `f08a3a4594323adcbbf65028498b7a0889702b4d16189c822bd02ac3797caedf`. Artifact: `runs/verify-all/engine-trust-census-862592db-final/census.txt`. It includes all 14 literal safety names from `.law(...)` and the `one(...)` helper; all 12 resulting name-hit lines are outside the production closure (test cases or fixture documentation).

## Import-path and environment census appendix

Conservative import closure (36 files, includes type-only imports):

`core/{accel,bitsets,bmc,carry,chart,check,count-support,counts,cycles,cyclic,discover,dsl,exists,fresh,infer,kind,lemma-cuts,live,machine,nonterm,q,relation,relevance,sample-cache,solver,translate,watch}.ts`; `kernel/{cdcl,cyclic,epr,kernel,model-sequence,prove,reader,share,simplex}.ts`.

No filesystem/dynamic-loading I/O hit is in these files. All 262 I/O hits carry OUTSIDE-CLOSURE in the recovered I/O artifact. This closure is conservative, not proof that every imported function runs.

The following enumerates every uppercase dotted `env`/`knobs` access found, including non-GDP names and outside-path hits. D is not a guarantee of timing-neutrality; C does not mean a checker bypass; S does not mean trusted fact. Exact expressions/defaults are in the source and full knobs scan.

| Knob | Exact access locations | Verdict effect classification |
|---|---|---|
| `CYCLES_TRACE` | core/cycles.ts:773 | D — observation; possible deadline overhead |
| `DATA_ALLCONG` | core/data.ts:2668 | O — outside original import path |
| `DATA_NODE` | core/data.ts:2670 | O — outside original import path |
| `DATA_TRACE` | core/data.ts:2666 | O — outside original import path |
| `FORCE_COLOR` | core/cli.ts:31 | O — outside original import path |
| `FUZZ_SCALE` | core/compile.test.ts:9; core/conformance.test.ts:25; core/runtime.test.ts:12; kernel/cdcl.test.ts:15; kernel/count.test.ts:11; kernel/countmachine.test.ts:12; kernel/history.test.ts:10; kernel/kernel.test.ts:11; kernel/steplaw.test.ts:75 | O — outside original import path |
| `FUZZ_SEED` | core/compile.test.ts:8; core/conformance.test.ts:26; core/conformance.ts:21; core/dsl.test.ts:22; core/runtime.test.ts:11; kernel/cdcl.test.ts:18; kernel/count.test.ts:167; kernel/history.test.ts:9; kernel/kernel.test.ts:15; kernel/steplaw.test.ts:74; kernel/tamper.test.ts:24; kernel/tuples.test.ts:374 | O — outside original import path |
| `FUZZ_TRACE` | kernel/kernel.test.ts:12 | O — outside original import path |
| `GDP_BMC_INC` | core/bmc.ts:63 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_BMC_RELAX` | core/bmc.ts:63 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_BMC_TIDY` | core/bmc.ts:63 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_CDCL_BASE` | kernel/cdcl.ts:64 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_CDCL_BATCH` | kernel/cdcl.ts:548 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_CDCL_FILL` | kernel/cdcl.ts:64 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_CDCL_GREEDY` | kernel/cdcl.ts:64 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_CDCL_GROW` | kernel/cdcl.ts:64 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_CDCL_LP` | kernel/cdcl.ts:64 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_CDCL_POINT` | kernel/cdcl.ts:63 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_CDCL_SHARE` | kernel/prove.ts:326 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_CDCL_VERIFY` | core/translate.ts:116; kernel/cdcl.ts:64 | C — auxiliary consistency enforcement |
| `GDP_CERT` | core/cyclic.ts:1263; core/relational.ts:299; core/relational.ts:300; core/relational.ts:315 | C — certificate/cross-check route or budget |
| `GDP_CERT_MS` | core/cyclic.ts:1266 | C — certificate/cross-check route or budget |
| `GDP_CERT_SEARCH` | core/cyclic.ts:1265 | C — certificate/cross-check route or budget |
| `GDP_CERT_STEP_MS` | core/cyclic.ts:1225 | C — certificate/cross-check route or budget |
| `GDP_COMPILE_S` | core/extract-c.test.ts:253; core/extract-go.test.ts:524; core/extract-jvm.test.ts:390; core/extract-jvm.test.ts:391; core/extract-jvm.test.ts:396; core/extract-rs.test.ts:1106; core/extract-swift.test.ts:138 | O — outside original import path |
| `GDP_COUNTS_COUNT_FIRST` | core/counts.ts:473; core/counts.ts:529 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_COUNTS_DUMP_N` | core/counts.ts:753 | D — observation; possible deadline overhead |
| `GDP_COUNTS_GIVEN` | core/counts.ts:406 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_COUNTS_LAZY` | core/counts.ts:40 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_COUNTS_POOL` | core/counts.ts:40 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_COUNTS_PROF` | core/counts.ts:394 | D — observation; possible deadline overhead |
| `GDP_COUNTS_RELEVANCE` | core/counts.ts:794 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_COUNTS_TRACE` | core/counts.ts:304; core/counts.ts:318; core/counts.ts:355; core/counts.ts:408; core/counts.ts:481; core/counts.ts:771; core/counts.ts:831 | D — observation; possible deadline overhead |
| `GDP_COUNT_LEMMA_CUTS` | core/counts.ts:417; core/counts.ts:432 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_CYCLIC` | core/cyclic.ts:1184; core/cyclic.ts:1187 | C — certificate/cross-check route or budget |
| `GDP_CYCLIC_DEBUG` | core/cyclic.ts:199; core/cyclic.ts:245; core/cyclic.ts:271; core/cyclic.ts:301; core/translate.ts:24; core/translate.ts:381 | D — observation; possible deadline overhead |
| `GDP_CYCLIC_LAX` | core/cyclic.ts:1252 | C — certificate/cross-check route or budget |
| `GDP_CYCLIC_LOG` | core/cyclic.ts:1187 | D — observation; possible deadline overhead |
| `GDP_CYCLIC_PROF` | core/cyclic.ts:88 | D — observation; possible deadline overhead |
| `GDP_CYCLIC_ROUTE` | core/cyclic.ts:1212 | C — certificate/cross-check route or budget |
| `GDP_CYCLIC_SLICE` | core/cyclic.ts:175 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_DLTRIG` | kernel/prove.ts:1809 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_ENGINE_SHARE` | core/infer.ts:114 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_EPR` | kernel/prove.ts:332 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_EPR_INC` | kernel/epr.ts:318 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_EXISTS_LOG` | core/dsl.ts:2899; core/dsl.ts:2924; core/dsl.ts:2959; core/dsl.ts:2966; core/dsl.ts:3016; core/exists.ts:842 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_IC3_CONE` | core/infer.ts:3103 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_IMC_RELAX` | core/interp.ts:284 | O — outside original import path |
| `GDP_INFER_HALVES` | core/infer.ts:149 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_INFER_TRACE` | core/infer.ts:116; core/infer.ts:680 | D — observation; possible deadline overhead |
| `GDP_ITP_CLAUSAL` | core/interp.ts:286 | O — outside original import path |
| `GDP_ITP_DAG` | core/interp.ts:286 | O — outside original import path |
| `GDP_ITP_STRONG` | core/interp.ts:286 | O — outside original import path |
| `GDP_ITP_TIDY` | core/interp.ts:286 | O — outside original import path |
| `GDP_JOIN` | core/infer.ts:123 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_JOIN_ATOMS` | core/infer.ts:140 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_JOIN_CLOCKS` | core/infer.ts:636 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_JOIN_CORE` | core/infer.ts:132 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_JOIN_CUBES` | core/infer.ts:136 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_JOIN_DOWN` | core/infer.ts:145 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_JOIN_LEVELS` | core/infer.ts:1443 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_JOIN_NEVERS` | core/infer.ts:130 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_JOIN_PRIME` | core/infer.ts:142 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_MEMO_ALPHA` | kernel/prove.ts:1742 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_MEMO_CAP` | kernel/prove.ts:1736 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_MEMO_TRACE` | core/infer.ts:3020; kernel/prove.ts:1873 | D — observation; possible deadline overhead |
| `GDP_MODELS_TRACE` | kernel/prove.ts:1240 | D — observation; possible deadline overhead |
| `GDP_MODEL_CUTS` | kernel/prove.ts:1132 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_MODEL_FLOOR` | kernel/prove.ts:1240 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_POOL` | core/infer.ts:2583; core/infer.ts:2678 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_POOL_LEAST` | core/infer.ts:2596 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_POOL_MS` | core/infer.ts:2595 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_POOL_QUIET` | core/infer.ts:2596 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_POOL_STATES` | core/infer.ts:2596 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_POOL_STOP` | core/infer.ts:2637 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_QUICK_CAP` | kernel/prove.ts:326 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_READER_CLEAN` | kernel/reader.ts:76 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_REAL_MODELS` | kernel/prove.ts:513 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_SET_FIRST` | kernel/prove.ts:2104 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_SORTED` | kernel/prove.ts:1981 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_SORT_PLACES` | kernel/prove.ts:1993 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_STRICT` | kernel/prove.ts:1988 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_SWIFT` | core/cli.test.ts:36; core/extract-swift.test.ts:15 | O — outside original import path |
| `GDP_TD` | core/infer.ts:2931 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_TD_DECIDED` | core/infer.ts:2979 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_TD_ORDER` | core/infer.ts:2954 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_TD_Q1` | core/infer.ts:2933 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_TD_Q2` | core/infer.ts:2933 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_TREES` | kernel/prove.ts:299 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_TRIGGER` | kernel/prove.ts:1510 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_UNITS` | kernel/prove.ts:875 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_WIDE` | kernel/prove.ts:375 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_WIDE_EPR` | kernel/prove.ts:462 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_WIDE_PARTS` | kernel/prove.ts:462 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_WIDE_SHARE` | kernel/prove.ts:375 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_WIDE_TERMS` | kernel/prove.ts:375 | S — search/model/cache strategy; finite-budget verdict effect |
| `GDP_WIDE_TRACE` | kernel/prove.ts:375 | D — observation; possible deadline overhead |
| `JAVA_HOME` | core/cli.test.ts:17; core/extract-jvm.test.ts:14; core/extract-jvm.ts:66; core/rounding.test.ts:73 | O — outside original import path |
| `KOTLIN_HOME` | core/cli.test.ts:26; core/extract-jvm.test.ts:16; core/extract-jvm.ts:72 | O — outside original import path |
| `LP_TRACE` | core/cycles.ts:398 | D — observation; possible deadline overhead |
| `MUTANT_BATTERY` | kernel/mutants.ts:134 | O — outside original import path |
| `NO_COLOR` | core/cli.ts:31 | O — outside original import path |
| `PROVE_DEBUG` | core/machine.ts:962 | D — observation; possible deadline overhead |
| `PROVE_TRACE` | kernel/prove.ts:199 | D — observation; possible deadline overhead |
| `READER_FUZZ_N` | core/extract-fuzz.ts:35 | O — outside original import path |
| `READER_FUZZ_SEED` | core/extract-fuzz.ts:35 | O — outside original import path |
| `READER_FUZZ_SHOW` | core/extract-fuzz.ts:154 | O — outside original import path |
| `READER_FUZZ_SLOW_MS` | core/extract-fuzz.ts:35 | O — outside original import path |
| `TERM` | core/cli.ts:31 | O — outside original import path |
| `TZ` | core/extract-py-orm.test.ts:83; core/extract-py-orm.test.ts:85; core/extract-py-orm.test.ts:93; core/extract-py-orm.test.ts:106; core/extract-py-orm.test.ts:108; core/extract-py-orm.test.ts:116 | O — outside original import path |

## Integration note

Main reported primary 84/87 (MLDR 0/3), and broken runs: none proven, 11 refuted, 17 unknown, 1 timeout. Those numbers are **Main-owned rerun results, not independently reproduced by this static audit**. This report supplies no evidence to upgrade MLDR, an unknown broken run, or a timeout into a successful verification.
