# VERIFY-ALL — independent audit of the IC3Syn 28/29 claim

Baseline: `6a3874d3f2c6febe40bb14775884cb327a2cce3c`; audit branch: `claude/verify-all`; date: 2026-11-09. The engine, TypeScript kernel, Lean kernel, protocol models, original harnesses and configuration were not changed. Only verification scripts and reports are committed. No external solver was used.

## Bottom line

- **The production 28/29 result reproduces:** 84/87 IC3Syn searches were `proven && checked`; the same 28 protocols passed all three repeats. **MLDR was unknown in all three**, not proven. Its printed `found` family is not a partial-proof count.
- **DuoAI:** 30/30 unpaired searches passed, as did all 60 baseline/current paired searches. No human invariant families were passed.
- **Fresh TLC:** all 29 TLC explorations completed; 28 port explorations matched both state and edge counts. `learning_switch` remained incomplete after its 660-second outer deadline, so full 29/29 correspondence is **not established**.
- **Broken variants:** zero proven, **11 refuted, 17 unknown, one strict timeout**. For all eleven refuted IDs, witnesses from separately captured repeats replayed successfully against their stated laws. The primary harness logged trace lengths, not the original witness bytes. “All broken variants refuted” would be false.
- **Independent proof checking matters:** the captured Paxos counted certificate is accepted by the TypeScript checker but its emitted Lean `checkCMachine` computes to false. The other independent-check results, including explicit original-model bridges for existential and sum proofs, are below. A failing Lean file is not accepted because a later `#print axioms` line happens to appear.
- **The models are qualified encodings, not unrestricted source protocols:** bounded identity domains, majority specialization, setup/ghost state, structural switch reflexivity, and MLDR's invariant-aware overlap arithmetic must accompany the result. Counts agreeing on a small instance are not an equivalence theorem.
- No protocol-name proof dispatch or loaded protocol-specific answer family was found in the audited import closure. Nevertheless, benchmark-shaped generic templates, tuned cutoffs and environment switches exist. This audit does **not** establish benchmark-independent generality.

## Execution and evidence contract

Everything substantive (production, TLC, Lean, scans, type/lint checks and aggregation) ran on boat via `supercomputer`. Primary measurements used `--timing --vm-type large --backend boat`: one job per VM, no co-tenants. Each original invocation was additionally pinned by `taskset` to CPUs `0,1,2,3` of the VM's eight vCPUs. The pool used AMD EPYC 4585PX, EPYC 9455 and Ryzen 9 9950X hosts; thus fixed VM **class**, not one identical physical CPU model. Do not compare absolute timings as if hardware were homogeneous.

Installations and hashing were outside the strict timed command:

```sh
# IC3Syn: 29 protocols × 3 independent processes
/usr/bin/time taskset -c 0,1,2,3 timeout -s KILL 60 \
  bun research/protocols/ic3syn/run.ts --ms 60000 --only ID --skip broken
# Broken variants: 29 processes, same strict limit
/usr/bin/time taskset -c 0,1,2,3 timeout -s KILL 60 \
  bun research/protocols/ic3syn/run.ts --ms 60000 --only ID --skip search
# DuoAI, plus paired fresh-process archived-baseline/current controls
/usr/bin/time taskset -c 0,1,2,3 timeout -s KILL 60 \
  bun research/protocols/run.ts --ms 60000 --only ID --skip given,broken
```

Exact job commands are in `research/verify-all/jobs-*.json` and `run-*.sh`. Primary logs, placement, exit statuses and hashes: `runs/verify-all/production/`; paired controls: `runs/verify-all/duo-paired/`. The primary batch contains 146 invocations (87+30+29); the paired batch adds 60 invocations. Instrumented capture runs, re-exports and diagnostics are **additional**, not silently substituted into those numerators.

Every primary job printed these source identities from inside the job:

| Source | SHA-256 |
|---|---|
| `kernel/kernel.ts` | `7ec8b310d23fab7eb3ba452b659e7051ceefe97aea01ffa6f16d990a7bea7f33` |
| `kernel/prove.ts` | `c52fdeece6b9471aa1b0b957cac6aec72267543b568d764ea5438543d90205fb` |
| `core/dsl.ts` | `264a2586fda15ada2b126faeb3b0c253c48cfd6de8626dd9bef9e123c08a4919` |
| `research/protocols/ic3syn/run.ts` | `a9fa1e966acf503db0804419f8af7b82cfec671f8fba528716ec5440ea70dd66` |
| `research/protocols/ic3syn/models.ts` | `5d61b846a8331a9b7978b4809d53b88e5918135ded0fc6d527f2a6dc8fb3a601` |

The primary jobs also printed a hash of a sorted per-file core/kernel/Lean source manifest. Protected paths were checked unchanged with `git diff --quiet 6a3874d3 -- core kernel lean-kernel research/protocols supercomputer.toml`.

The original harness does not dump certificates. **Item 4 therefore uses separate observational repetitions of that same unchanged harness**, retaining its actual accepted objects; it does not claim to have recovered the exact proof bytes of the uninstrumented three runs. The preload only observes return values and the existing closed-family callback. It does not supply laws or alter results, but its overhead can affect a tight wall budget. Certificate identity, full retained packets, emitted-file hashes and Lean receipts are recorded separately.

The original jobs did not dump their complete inherited environment. Their commands set no per-protocol GDP switch; the configuration sets `GDP_CYCLIC_LOG=1` uniformly. A later representative in-job environment receipt (`runs/verify-all/check/check.log`) showed only that GDP setting in the inspected strategy prefixes. That later snapshot is **not** retroactive proof of the complete environment of each primary invocation.
## 1. Production reruns

Each cell is `verdict / strict wall s / harness ms / work / full / found-law count`. `work` and `full` are the original IC3Syn counters, not wall seconds. Full found-law text and the kernel hash are in every linked log. `F` is not a count of individually proven laws: notably an unknown counted search can print its candidate family.

| IC3Syn protocol | Repeat 1 | Repeat 2 | Repeat 3 | Broken (one run) |
|---|---|---|---|---|
| client_server_ae | [proven/11.27 s/11189 ms/1017296/595146/F4](verify-all/production/ic3syn-client_server_ae-r1.log) | [proven/12.18 s/12127 ms/1017296/595146/F4](verify-all/production/ic3syn-client_server_ae-r2.log) | [proven/10.11 s/10060 ms/1017296/595146/F4](verify-all/production/ic3syn-client_server_ae-r3.log) | [unknown/10.43 s/10400 ms/0/0/F0](verify-all/production/broken-client_server_ae.log) |
| client_server_db_ae | [proven/18.01 s/17963 ms/686698/369654/F24](verify-all/production/ic3syn-client_server_db_ae-r1.log) | [proven/15.07 s/15027 ms/686698/369654/F24](verify-all/production/ic3syn-client_server_db_ae-r2.log) | [proven/33.63 s/33561 ms/686698/369654/F24](verify-all/production/ic3syn-client_server_db_ae-r3.log) | [unknown/21.26 s/21104 ms/4426/14885/F0](verify-all/production/broken-client_server_db_ae.log) |
| consensus | [proven/0.43 s/351 ms/4685/52454/F0](verify-all/production/ic3syn-consensus-r1.log) | [proven/0.31 s/259 ms/4685/52454/F0](verify-all/production/ic3syn-consensus-r2.log) | [proven/0.32 s/270 ms/4685/52454/F0](verify-all/production/ic3syn-consensus-r3.log) | [refuted/0.03 s/3 ms/0/0/F0](verify-all/production/broken-consensus.log) |
| consensus_epr | [proven/33.58 s/33491 ms/7364433/1488593/F28](verify-all/production/ic3syn-consensus_epr-r1.log) | [proven/16.02 s/15860 ms/7364433/1488593/F28](verify-all/production/ic3syn-consensus_epr-r2.log) | [proven/13.54 s/13482 ms/7364433/1488593/F28](verify-all/production/ic3syn-consensus_epr-r3.log) | [unknown/2.85 s/2822 ms/0/0/F7](verify-all/production/broken-consensus_epr.log) |
| consensus_forall | [proven/24.57 s/24505 ms/14498189/2665853/F44](verify-all/production/ic3syn-consensus_forall-r1.log) | [proven/18.22 s/18174 ms/14498189/2665853/F44](verify-all/production/ic3syn-consensus_forall-r2.log) | [proven/21.14 s/21062 ms/14498189/2665853/F44](verify-all/production/ic3syn-consensus_forall-r3.log) | [unknown/5.06 s/5032 ms/0/0/F8](verify-all/production/broken-consensus_forall.log) |
| consensus_wo_decide | [proven/9.19 s/9148 ms/6321466/1365323/F37](verify-all/production/ic3syn-consensus_wo_decide-r1.log) | [proven/13.21 s/13148 ms/6321466/1365323/F37](verify-all/production/ic3syn-consensus_wo_decide-r2.log) | [proven/26.50 s/26411 ms/6321466/1365323/F37](verify-all/production/ic3syn-consensus_wo_decide-r3.log) | [unknown/2.85 s/2764 ms/0/0/F7](verify-all/production/broken-consensus_wo_decide.log) |
| firewall | [proven/17.79 s/17738 ms/1350274/1264172/F1](verify-all/production/ic3syn-firewall-r1.log) | [proven/19.58 s/19521 ms/1350274/1264172/F1](verify-all/production/ic3syn-firewall-r2.log) | [proven/20.60 s/20541 ms/1350274/1264172/F1](verify-all/production/ic3syn-firewall-r3.log) | [unknown/6.45 s/6419 ms/0/0/F0](verify-all/production/broken-firewall.log) |
| learning_switch | [proven/16.25 s/16198 ms/399436/685946/F13](verify-all/production/ic3syn-learning_switch-r1.log) | [proven/17.52 s/17459 ms/399436/685946/F13](verify-all/production/ic3syn-learning_switch-r2.log) | [proven/18.14 s/18069 ms/399436/685946/F13](verify-all/production/ic3syn-learning_switch-r3.log) | [unknown/12.92 s/12874 ms/215455/654844/F0](verify-all/production/broken-learning_switch.log) |
| learning_switch_i4 | [proven/19.11 s/19047 ms/314016/618517/F19](verify-all/production/ic3syn-learning_switch_i4-r1.log) | [proven/21.61 s/21530 ms/314016/618517/F19](verify-all/production/ic3syn-learning_switch_i4-r2.log) | [proven/21.01 s/20963 ms/314016/618517/F19](verify-all/production/ic3syn-learning_switch_i4-r3.log) | [unknown/48.20 s/48138 ms/407181/903294/F0](verify-all/production/broken-learning_switch_i4.log) |
| lock_server | [proven/3.80 s/3554 ms/56883/39220/F1](verify-all/production/ic3syn-lock_server-r1.log) | [proven/5.61 s/4951 ms/56883/39220/F1](verify-all/production/ic3syn-lock_server-r2.log) | [proven/6.80 s/6740 ms/56883/39220/F1](verify-all/production/ic3syn-lock_server-r3.log) | [refuted/0.03 s/4 ms/0/0/F0](verify-all/production/broken-lock_server.log) |
| lockserv | [proven/12.63 s/12552 ms/1340389/2197580/F12](verify-all/production/ic3syn-lockserv-r1.log) | [proven/4.91 s/4871 ms/1340389/2197580/F12](verify-all/production/ic3syn-lockserv-r2.log) | [proven/5.42 s/5377 ms/1340389/2197580/F12](verify-all/production/ic3syn-lockserv-r3.log) | [refuted/0.19 s/157 ms/7848/19202/F0](verify-all/production/broken-lockserv.log) |
| lockserv_automaton | [proven/5.77 s/5728 ms/1159509/2067272/F12](verify-all/production/ic3syn-lockserv_automaton-r1.log) | [proven/4.72 s/4684 ms/1159509/2067272/F12](verify-all/production/ic3syn-lockserv_automaton-r2.log) | [proven/6.07 s/6030 ms/1159509/2067272/F12](verify-all/production/ic3syn-lockserv_automaton-r3.log) | [refuted/0.17 s/141 ms/7414/18934/F0](verify-all/production/broken-lockserv_automaton.log) |
| majorityset_leader_election | [proven/4.79 s/4740 ms/2007722/594997/F16](verify-all/production/ic3syn-majorityset_leader_election-r1.log) | [proven/4.34 s/4298 ms/2007722/594997/F16](verify-all/production/ic3syn-majorityset_leader_election-r2.log) | [proven/4.68 s/4626 ms/2007722/594997/F16](verify-all/production/ic3syn-majorityset_leader_election-r3.log) | [unknown/0.71 s/678 ms/0/0/F4](verify-all/production/broken-majorityset_leader_election.log) |
| mldr | [unknown/20.47 s/20429 ms/2657026/921136/F23](verify-all/production/ic3syn-mldr-r1.log) | [unknown/20.96 s/20890 ms/2657026/921136/F23](verify-all/production/ic3syn-mldr-r2.log) | [unknown/26.62 s/26560 ms/2657026/921136/F23](verify-all/production/ic3syn-mldr-r3.log) | [unknown/9.36 s/9300 ms/0/0/F4](verify-all/production/broken-mldr.log) |
| naive_consensus | [proven/2.26 s/2225 ms/693719/221514/F12](verify-all/production/ic3syn-naive_consensus-r1.log) | [proven/2.30 s/2275 ms/693719/221514/F12](verify-all/production/ic3syn-naive_consensus-r2.log) | [proven/2.80 s/2758 ms/693719/221514/F12](verify-all/production/ic3syn-naive_consensus-r3.log) | [unknown/1.53 s/1497 ms/0/0/F5](verify-all/production/broken-naive_consensus.log) |
| paxos_epr | [proven/18.95 s/18915 ms/8719080/1135224/F25](verify-all/production/ic3syn-paxos_epr-r1.log) | [proven/21.34 s/21289 ms/8719080/1135224/F25](verify-all/production/ic3syn-paxos_epr-r2.log) | [proven/18.68 s/18644 ms/8719080/1135224/F25](verify-all/production/ic3syn-paxos_epr-r3.log) | [unknown/50.84 s/50735 ms/145967329/12999248/F33](verify-all/production/broken-paxos_epr.log) |
| quorum_leader_election | [proven/2.63 s/2542 ms/77815/68379/F6](verify-all/production/ic3syn-quorum_leader_election-r1.log) | [proven/2.49 s/2420 ms/77815/68379/F6](verify-all/production/ic3syn-quorum_leader_election-r2.log) | [proven/5.69 s/5596 ms/77815/68379/F6](verify-all/production/ic3syn-quorum_leader_election-r3.log) | [unknown/0.34 s/308 ms/0/0/F2](verify-all/production/broken-quorum_leader_election.log) |
| sharded_kv | [proven/15.52 s/15476 ms/1375415/820889/F20](verify-all/production/ic3syn-sharded_kv-r1.log) | [proven/14.84 s/14788 ms/1375415/820889/F20](verify-all/production/ic3syn-sharded_kv-r2.log) | [proven/18.75 s/18694 ms/1375415/820889/F20](verify-all/production/ic3syn-sharded_kv-r3.log) | [refuted/2.17 s/2143 ms/383184/89678/F0](verify-all/production/broken-sharded_kv.log) |
| sharded_kv_no_lost_keys | [proven/6.49 s/6422 ms/362642/207610/F6](verify-all/production/ic3syn-sharded_kv_no_lost_keys-r1.log) | [proven/8.18 s/8123 ms/362642/207610/F6](verify-all/production/ic3syn-sharded_kv_no_lost_keys-r2.log) | [proven/6.94 s/6868 ms/362642/207610/F6](verify-all/production/ic3syn-sharded_kv_no_lost_keys-r3.log) | [timeout/60.00 s/— ms/—/—/F0](verify-all/production/broken-sharded_kv_no_lost_keys.log) |
| simple | [proven/9.48 s/9447 ms/3095355/6901677/F9](verify-all/production/ic3syn-simple-r1.log) | [proven/12.23 s/12130 ms/2080981/4725694/F9](verify-all/production/ic3syn-simple-r2.log) | [proven/12.60 s/12539 ms/1761960/4013291/F9](verify-all/production/ic3syn-simple-r3.log) | [refuted/0.04 s/6 ms/0/0/F0](verify-all/production/broken-simple.log) |
| simple_decentralized_lock | [proven/2.96 s/2925 ms/241158/351675/F1](verify-all/production/ic3syn-simple_decentralized_lock-r1.log) | [proven/3.87 s/3823 ms/241158/351675/F1](verify-all/production/ic3syn-simple_decentralized_lock-r2.log) | [proven/3.78 s/3574 ms/241158/351675/F1](verify-all/production/ic3syn-simple_decentralized_lock-r3.log) | [refuted/0.16 s/93 ms/159/765/F0](verify-all/production/broken-simple_decentralized_lock.log) |
| simple_election | [proven/2.62 s/2587 ms/332692/158981/F10](verify-all/production/ic3syn-simple_election-r1.log) | [proven/2.80 s/2757 ms/332692/158981/F10](verify-all/production/ic3syn-simple_election-r2.log) | [proven/4.38 s/4309 ms/332692/158981/F10](verify-all/production/ic3syn-simple_election-r3.log) | [unknown/2.10 s/2068 ms/0/0/F5](verify-all/production/broken-simple_election.log) |
| simple_regular | [proven/11.88 s/11825 ms/3207253/7484032/F16](verify-all/production/ic3syn-simple_regular-r1.log) | [proven/11.46 s/11431 ms/3275051/7623080/F16](verify-all/production/ic3syn-simple_regular-r2.log) | [proven/12.12 s/12078 ms/3036364/7108253/F16](verify-all/production/ic3syn-simple_regular-r3.log) | [refuted/0.04 s/7 ms/0/0/F0](verify-all/production/broken-simple_regular.log) |
| tcommit | [proven/0.61 s/559 ms/11200/120024/F0](verify-all/production/ic3syn-tcommit-r1.log) | [proven/0.57 s/529 ms/11200/120024/F0](verify-all/production/ic3syn-tcommit-r2.log) | [proven/0.41 s/299 ms/11200/120024/F0](verify-all/production/ic3syn-tcommit-r3.log) | [refuted/0.04 s/12 ms/0/0/F0](verify-all/production/broken-tcommit.log) |
| toy_consensus | [proven/4.52 s/4456 ms/76032/64652/F4](verify-all/production/ic3syn-toy_consensus-r1.log) | [proven/1.93 s/1891 ms/76032/64652/F4](verify-all/production/ic3syn-toy_consensus-r2.log) | [proven/2.05 s/2009 ms/76032/64652/F4](verify-all/production/ic3syn-toy_consensus-r3.log) | [unknown/0.33 s/303 ms/0/0/F2](verify-all/production/broken-toy_consensus.log) |
| toy_consensus_epr | [proven/2.53 s/2502 ms/572283/185783/F8](verify-all/production/ic3syn-toy_consensus_epr-r1.log) | [proven/2.04 s/2006 ms/572283/185783/F8](verify-all/production/ic3syn-toy_consensus_epr-r2.log) | [proven/2.86 s/2810 ms/572283/185783/F8](verify-all/production/ic3syn-toy_consensus_epr-r3.log) | [unknown/1.35 s/1321 ms/0/0/F4](verify-all/production/broken-toy_consensus_epr.log) |
| toy_consensus_forall | [proven/2.34 s/2270 ms/115382/91451/F8](verify-all/production/ic3syn-toy_consensus_forall-r1.log) | [proven/5.21 s/5149 ms/115382/91451/F8](verify-all/production/ic3syn-toy_consensus_forall-r2.log) | [proven/3.11 s/2962 ms/115382/91451/F8](verify-all/production/ic3syn-toy_consensus_forall-r3.log) | [unknown/0.33 s/307 ms/0/0/F3](verify-all/production/broken-toy_consensus_forall.log) |
| two_phase_commit | [proven/7.40 s/7361 ms/2798392/1860768/F14](verify-all/production/ic3syn-two_phase_commit-r1.log) | [proven/7.35 s/7314 ms/2798392/1860768/F14](verify-all/production/ic3syn-two_phase_commit-r2.log) | [proven/13.34 s/13279 ms/2798392/1860768/F14](verify-all/production/ic3syn-two_phase_commit-r3.log) | [refuted/0.04 s/14 ms/0/0/F0](verify-all/production/broken-two_phase_commit.log) |
| twophase | [proven/10.61 s/10570 ms/1513912/2667344/F32](verify-all/production/ic3syn-twophase-r1.log) | [proven/11.08 s/11031 ms/1513912/2667344/F32](verify-all/production/ic3syn-twophase-r2.log) | [proven/17.71 s/17629 ms/1513912/2667344/F32](verify-all/production/ic3syn-twophase-r3.log) | [refuted/0.04 s/14 ms/0/0/F0](verify-all/production/broken-twophase.log) |

### DuoAI controls

The unpaired original harness does not emit counted work; no work counter was invented. Paired archived-baseline/current results are additional evidence, not part of the IC3Syn numerator.

| DuoAI protocol | Repeat 1 | Repeat 2 | Repeat 3 | Paired base/candidate |
|---|---|---|---|---|
| consensus_wo_decide | [proven/18.53 s/18462 ms/—/—/F15](verify-all/production/duoai-consensus_wo_decide-r1.log) | [proven/17.79 s/17718 ms/—/—/F15](verify-all/production/duoai-consensus_wo_decide-r2.log) | [proven/15.94 s/15888 ms/—/—/F15](verify-all/production/duoai-consensus_wo_decide-r3.log) | [r1 cand:proven(20169 ms, exit 0), base:proven(20768 ms, exit 0)](verify-all/duo-paired/paired-consensus_wo_decide-r1.log)<br>[r2 base:proven(19636 ms, exit 0), cand:proven(16208 ms, exit 0)](verify-all/duo-paired/paired-consensus_wo_decide-r2.log)<br>[r3 cand:proven(18253 ms, exit 0), base:proven(18423 ms, exit 0)](verify-all/duo-paired/paired-consensus_wo_decide-r3.log) |
| decentralized_lock | [proven/7.69 s/7632 ms/—/—/F2](verify-all/production/duoai-decentralized_lock-r1.log) | [proven/7.36 s/7302 ms/—/—/F2](verify-all/production/duoai-decentralized_lock-r2.log) | [proven/7.54 s/7488 ms/—/—/F2](verify-all/production/duoai-decentralized_lock-r3.log) | [r1 cand:proven(10745 ms, exit 0), base:proven(13171 ms, exit 0)](verify-all/duo-paired/paired-decentralized_lock-r1.log)<br>[r2 base:proven(5765 ms, exit 0), cand:proven(5553 ms, exit 0)](verify-all/duo-paired/paired-decentralized_lock-r2.log)<br>[r3 cand:proven(7669 ms, exit 0), base:proven(7099 ms, exit 0)](verify-all/duo-paired/paired-decentralized_lock-r3.log) |
| distributed_lock | [proven/9.21 s/9170 ms/—/—/F20](verify-all/production/duoai-distributed_lock-r1.log) | [proven/10.42 s/10375 ms/—/—/F20](verify-all/production/duoai-distributed_lock-r2.log) | [proven/9.22 s/9181 ms/—/—/F20](verify-all/production/duoai-distributed_lock-r3.log) | [r1 cand:proven(11620 ms, exit 0), base:proven(10232 ms, exit 0)](verify-all/duo-paired/paired-distributed_lock-r1.log)<br>[r2 base:proven(10457 ms, exit 0), cand:proven(10230 ms, exit 0)](verify-all/duo-paired/paired-distributed_lock-r2.log)<br>[r3 cand:proven(11073 ms, exit 0), base:proven(10700 ms, exit 0)](verify-all/duo-paired/paired-distributed_lock-r3.log) |
| lock_server_async | [proven/14.71 s/14633 ms/—/—/F11](verify-all/production/duoai-lock_server_async-r1.log) | [proven/9.11 s/9067 ms/—/—/F11](verify-all/production/duoai-lock_server_async-r2.log) | [proven/22.62 s/22552 ms/—/—/F11](verify-all/production/duoai-lock_server_async-r3.log) | [r1 cand:proven(10250 ms, exit 0), base:proven(9826 ms, exit 0)](verify-all/duo-paired/paired-lock_server_async-r1.log)<br>[r2 base:proven(14260 ms, exit 0), cand:proven(13442 ms, exit 0)](verify-all/duo-paired/paired-lock_server_async-r2.log)<br>[r3 cand:proven(9773 ms, exit 0), base:proven(9463 ms, exit 0)](verify-all/duo-paired/paired-lock_server_async-r3.log) |
| lock_server_sync | [proven/3.18 s/3156 ms/—/—/F1](verify-all/production/duoai-lock_server_sync-r1.log) | [proven/3.85 s/3814 ms/—/—/F1](verify-all/production/duoai-lock_server_sync-r2.log) | [proven/3.92 s/3883 ms/—/—/F1](verify-all/production/duoai-lock_server_sync-r3.log) | [r1 cand:proven(4558 ms, exit 0), base:proven(4688 ms, exit 0)](verify-all/duo-paired/paired-lock_server_sync-r1.log)<br>[r2 base:proven(4772 ms, exit 0), cand:proven(5288 ms, exit 0)](verify-all/duo-paired/paired-lock_server_sync-r2.log)<br>[r3 cand:proven(3508 ms, exit 0), base:proven(3750 ms, exit 0)](verify-all/duo-paired/paired-lock_server_sync-r3.log) |
| ring_leader_election | [proven/16.61 s/16564 ms/—/—/F18](verify-all/production/duoai-ring_leader_election-r1.log) | [proven/15.83 s/15792 ms/—/—/F18](verify-all/production/duoai-ring_leader_election-r2.log) | [proven/29.11 s/29057 ms/—/—/F18](verify-all/production/duoai-ring_leader_election-r3.log) | [r1 cand:proven(20363 ms, exit 0), base:proven(23613 ms, exit 0)](verify-all/duo-paired/paired-ring_leader_election-r1.log)<br>[r2 base:proven(15598 ms, exit 0), cand:proven(15469 ms, exit 0)](verify-all/duo-paired/paired-ring_leader_election-r2.log)<br>[r3 cand:proven(20116 ms, exit 0), base:proven(17267 ms, exit 0)](verify-all/duo-paired/paired-ring_leader_election-r3.log) |
| sharded_key_value_store | [proven/21.81 s/21722 ms/—/—/F16](verify-all/production/duoai-sharded_key_value_store-r1.log) | [proven/17.02 s/16945 ms/—/—/F16](verify-all/production/duoai-sharded_key_value_store-r2.log) | [proven/11.63 s/11584 ms/—/—/F16](verify-all/production/duoai-sharded_key_value_store-r3.log) | [r1 cand:proven(10295 ms, exit 0), base:proven(9151 ms, exit 0)](verify-all/duo-paired/paired-sharded_key_value_store-r1.log)<br>[r2 base:proven(11193 ms, exit 0), cand:proven(11154 ms, exit 0)](verify-all/duo-paired/paired-sharded_key_value_store-r2.log)<br>[r3 cand:proven(15915 ms, exit 0), base:proven(12381 ms, exit 0)](verify-all/duo-paired/paired-sharded_key_value_store-r3.log) |
| ticket_lock | [proven/9.59 s/9549 ms/—/—/F10](verify-all/production/duoai-ticket_lock-r1.log) | [proven/8.24 s/8120 ms/—/—/F10](verify-all/production/duoai-ticket_lock-r2.log) | [proven/8.03 s/7987 ms/—/—/F10](verify-all/production/duoai-ticket_lock-r3.log) | [r1 cand:proven(17832 ms, exit 0), base:proven(12560 ms, exit 0)](verify-all/duo-paired/paired-ticket_lock-r1.log)<br>[r2 base:proven(8622 ms, exit 0), cand:proven(8699 ms, exit 0)](verify-all/duo-paired/paired-ticket_lock-r2.log)<br>[r3 cand:proven(9569 ms, exit 0), base:proven(10101 ms, exit 0)](verify-all/duo-paired/paired-ticket_lock-r3.log) |
| toy_consensus_forall | [proven/5.09 s/5053 ms/—/—/F6](verify-all/production/duoai-toy_consensus_forall-r1.log) | [proven/3.74 s/3703 ms/—/—/F6](verify-all/production/duoai-toy_consensus_forall-r2.log) | [proven/3.87 s/3837 ms/—/—/F6](verify-all/production/duoai-toy_consensus_forall-r3.log) | [r1 cand:proven(4032 ms, exit 0), base:proven(3904 ms, exit 0)](verify-all/duo-paired/paired-toy_consensus_forall-r1.log)<br>[r2 base:proven(4535 ms, exit 0), cand:proven(4517 ms, exit 0)](verify-all/duo-paired/paired-toy_consensus_forall-r2.log)<br>[r3 cand:proven(4437 ms, exit 0), base:proven(4657 ms, exit 0)](verify-all/duo-paired/paired-toy_consensus_forall-r3.log) |
| two_phase_commit | [proven/7.45 s/7416 ms/—/—/F15](verify-all/production/duoai-two_phase_commit-r1.log) | [proven/7.05 s/7025 ms/—/—/F15](verify-all/production/duoai-two_phase_commit-r2.log) | [proven/10.53 s/10479 ms/—/—/F15](verify-all/production/duoai-two_phase_commit-r3.log) | [r1 cand:proven(7973 ms, exit 0), base:proven(9493 ms, exit 0)](verify-all/duo-paired/paired-two_phase_commit-r1.log)<br>[r2 base:proven(6664 ms, exit 0), cand:proven(7139 ms, exit 0)](verify-all/duo-paired/paired-two_phase_commit-r2.log)<br>[r3 cand:proven(7253 ms, exit 0), base:proven(7332 ms, exit 0)](verify-all/duo-paired/paired-two_phase_commit-r3.log) |


### Broken-run replay

| Protocol | Legal replay steps | Failed stated law | Captured run SHA-256 |
|---|---:|---|---|
| consensus | 2 | at most one value chosen | `1fa7047732459843a759ff42c77607a5bf576ad8d3cb2f7b629a9972fcd0a465` |
| lock_server | 6 | one client per server | `e947cec703de8c013cef0dcabe27d13f8d16a3d3c2271d32cd13776636987de1` |
| lockserv | 24 | one holder | `766e55385840c66debfe3780f6adaf3fbb348bcfd2dfe8368e9f15ac97b57c55` |
| lockserv_automaton | 22 | one holder | `9454250f1989faf73d5efff72e2006cce09701c4d5c60e7fd3766a0ce99cb4c8` |
| sharded_kv | 24 | one value per key | `68559038f3af9571c964014c7c3e887ec476dc406f654fb3e9203b6259b2f919` |
| simple | 3 | some process not done, or some y is 1 | `0fbfddcf0713a6d4253b87e51aa6abd39b9b31744106c30dff0f1a5f323e9f45` |
| simple_decentralized_lock | 11 | one node holds the lock | `ce10d211cfc2f25d7061b5dadb31f0d2195100307f4a26219842f784fff5ce11` |
| simple_regular | 4 | some process not done, or some y is 1 | `244e69a715fd68a86fd780b56cb7956fa44dc04979fbfdc0237505335462c25a` |
| tcommit | 4 | commit and abort exclude | `e7089998518d7a7683dea8df7265a86d801ea4a0c34c16855f340ce7ad862693` |
| two_phase_commit | 6 | commit and abort agree | `72e8a87b2f7101e75ab606047a6d557e66f4d83c0eab1867c0936e7efcbad6e6` |
| twophase | 6 | commit and abort exclude | `49f3750268e2b58dfbf4b205f25a26348a342cd3cfe88a8075f3abe283c052d2` |

All replayed traces met the initial precondition and every interpreter step checked the request assumption. The small-instance `p.bad` helper is diagnostic only: it misses some valid production-domain counterexamples outside its fixed 0..2 domain. Early audit-helper failures caused by treating it as authoritative were retained in `replay/` and `recheck-replay/`; the corrected `recheck-replay-final/` checks the actual stated law. No new production search was used for these rechecks. The witness packets themselves came from the separate instrumented broken-run repetitions: the primary harness printed only trace lengths. Exact replay of the original primary witness bytes is therefore not established; the retained repeats provide legal counterexamples for the same eleven refuted IDs.

## 2. Safety clauses and supplied knowledge

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


Source hash ledger, complete assumption inventory and judgments: [model-source-audit.md](../research/verify-all/model-source-audit.md). Runtime inventory: 29 models, 33 explicit safety laws, 29 request assumptions, 20 parameter preconditions, no supplied facts/functions/human invariant families, two check-only constraints. Kind laws are additional generated obligations, not handwritten protocol invariants. Switch reflexivity is structural; seven arbitrary-quorum sources are specialized to majorities; no unrestricted source equivalence/cutoff proof was established.

## 3. Fresh TLC correspondence


Baseline: `claude/verify-all`, `6a3874d3f2c6febe40bb14775884cb327a2cce3c`.
Only audit scripts/report under `research/verify-all/`; logs `runs/verify-all/tlc-*`. No source/harness changes.

## Commands

```sh
supercomputer run --jobs research/verify-all/tlc-jobs-20261109.json --out runs/verify-all/tlc-20261109-first --class submission --vm-type large --timing --backend boat
supercomputer run --jobs research/verify-all/tlc-source-jobs-20261109.json --out runs/verify-all/tlc-20261109-sources --class submission --backend boat
supercomputer run --jobs research/verify-all/tlc-retry-jobs-20261109.json --out runs/verify-all/tlc-20261109-retry --class submission --vm-type large --timing --backend boat
```

First command launches 29 jobs running `python3 research/verify-all/tlc-audit-run-20261109.py ID [MS]`: unchanged `check.ts --cfg`, pinned Endive download, harness-declared fixes in isolated copy, fresh TLC 1.8.0 with DOT, unchanged `check.ts --edges` and `--broken`. Finite child process deadlines; exclusive large placement requested; affinity recorded. Each `RESULT` records source/config/JAR/DOT hashes and counts, while `RECEIPT` records full command/exit/wall. Compressed evidence contains full logs/config and pre/post TLA. `tlc-decode-20261109.py` only decodes returned evidence locally, never runs models. Graph hashes returned, full graph remains ephemeral on boat.

Initial-wrapper failure to retain: it tried reading `PaxosEprPyv.tla` before the harness fix creates that module. Wrapper fixed to allow missing original. Initial Paxos attempt and subsequent fresh retry must be distinguished. No correspondence success until completion receipts arrive.

## Scope/limitations

Counts are not bisimulation: `check.ts:25-29` projects raw interpreter states to source states; `:34-47,57-62` collapses phase paths and counts non-self distinct edges. Phase traversal silently caps at 10,000 states (`:37`); exceptions are treated as refused transitions (`:41,56`). The elapsed budget is checked once per frontier (`:52`); `done:false` or killed jobs are incomplete. Constraint-boundary states are recorded separately (`:65`). `c.states` is only an optional historical output (`:74`), not evidence used by this audit. Equal cardinalities can hide different state/edge sets. This is a check on the specified small instances, not all parameters, and not the production proof.

Some quorum families are restricted to majorities (`README.md:122-133`); consensus-with/without-decide checks the config's three pairs, not the full majority also permitted by the port (`models.ts:940-945`). Naive consensus adds a quotient VIEW (`models.ts:950-952`). Learning-switch and MLDR have state constraints (`models.ts:1008-1010,1034-1036`).

Source inspection confirms the two documented Endive Paxos errors: `runs/verify-all/tlc-20261109-sources/endive-paxos_epr.tla:80` keeps `left_rnd` unchanged, and `:102,125` transpose the r/v arguments of Decide. There is also a separate apparent transcription error at `:88`: the quantifier ranges over `mr` but membership reads `<<n,maxr,mv>>` instead of `<<n,mr,mv>>`. This third observation is source inspection, not a measured counterexample.

The pinned mypyvy source uses an arbitrary total round order and intersecting quorum sort (`mypyvy-paxos_epr.pyv:15-21`), while the port/transcribed TLC restricts them to bounded natural order and majorities. Its five transition clauses (`:38-77`) match the intended Send1a, JoinRound (including left-round update), Propose, CastVote and Decide shapes in `models.ts:734-759`; its safety is `:81`. The source’s five additional invariant declarations (`:84-97`) are not part of the TLC Init/Next used here.

Paxos TLC source is a second hand transcription (`models.ts:725-762,1020-1028`), not the faulty committed Endive `paxos_epr.tla`. Thus finite agreement against it shares author/translation assumptions. The independent pinned mypyvy source and original Endive source were fetched by the source job for clause inspection, not generated from the port.

## Invariant-aware representations

Read-only handoff `private/handoff/claude-tracks-20261107/AFTER-MLDR.md:39-41` identifies MLDR's arithmetic QuorumsOverlap and “the P* port” as chosen knowing the invariant. MLDR implementation is identifiable (`models.ts:764-797,813-814`): dx=|X\\Y|, dy=|Y\\X|, m=|X∩Y| and half sizes yield `max(0,floor(|X|/2)+1-dx)+max(0,floor(|Y|/2)+1-dy)>m`. Source job independently exhausts nonempty subset pairs on universes 1..6: **5,214 pairs, zero mismatches** against the all-majority-pairs definition. This is finite arithmetic corroboration, not an all-size proof or removal of hindsight bias.

**P* remains unresolved.** Audit supplies no ID mapping; the Main coordinator also had no mapping. Do not guess it means Paxos. Finite TLC agreement cannot establish that any representation was chosen blindly.

Source job complete on boat, exit 0 (0.67 seconds job time); retained `runs/verify-all/tlc-20261109-sources/tlc-source-audit.log`:
- mypyvy 12a8f5434a25587c56814d090b6ab7fa95851e71 `examples/pd/paxos_epr.pyv`: SHA-256 `b19d164c17601768b12342573256e5b802c9b30b5b2ec62e1679ffefe49f8ebd`.
- Endive 8b6f2abd1988eeb308f965813635e9871f253e2d `benchmarks/paxos_epr.tla`: `f466e55f144a8660d3372f4e9d109e46c2b0e3f0e12d3f1e0294638c098312d5`.
- same Endive `MongoLoglessDynamicRaft.tla`: `c09dd60a54f2dc66c2f58087bbeb49b7686be0425f8af3eb1f10a9299ae73e8e`.

## Correspondence results — terminal, bounded

**28/29 ports have completed fresh TLC and unchanged port BFS with equal state AND non-self directed-edge counts. No completed count mismatch was found. `learning_switch` remains NOT ESTABLISHED:** TLC completed (43,672 states, 258,084 edges), but the port process emitted no result and was killed at both the initial 180-second and retry 660-second outer deadlines. This is not a measured count mismatch and must not be reported as 29/29 correspondence.

Both evidence-producing batches terminated: first batch 29/29 scheduler jobs exit 0, 510.8 seconds wall; retry 5/5 scheduler jobs exit 0, 798.8 seconds wall. The wrapper catches errors and still exits 0, so these scheduler exit counts are NOT model-check completion counts. The table below uses inner TLC/port results. All TLC checks in the final per-ID table completed successfully with exit 0 and no invariant violation; all 28 completed normal port runs have `bad=0`.

Initial incomplete attempts, retained without overwriting:
- `paxos_epr`: initial wrapper FileNotFoundError before running TLC (it tried to hash the not-yet-created `PaxosEprPyv.tla`). Fixed wrapper retry completed **7,377 states / 23,578 edges** on both sides. Initial script is preserved as `tlc-audit-run-initial-20261109.py`, retry script as `tlc-audit-run-retry-20261109.py`.
- `consensus_forall`: initial `done=false`, 111,669 states / 628,704 edges at 121,024ms, not a mismatch; retry completed **112,128 / 633,024**.
- `learning_switch`: port exit -9/no JSON at both 180s and 660s. Fresh TLC on each attempt completed 43,672 / 258,084. No dependency failure was involved; this is the named execution wall.
- Broken `consensus_epr`: first result `bad=0,done=false`; retry killed at 660s/no JSON. Broken `consensus_forall`: `bad=0,done=false` even in the 600,000ms retry. Nonvacuity from these two broken BFS runs is **not established**. Broken `consensus_wo_decide` recovered in retry (`bad=2,done=true`). Across all attempts, 27/29 broken variants reached bad states. Broken `done=true` means stopped after discovering bad states, not exhaustive completion.

Every retry re-ran fresh TLC; the longer budget did not change the source, inputs, constraints, projections, or port harness. The first 29 and retry 5 jobs were exclusive large placements, zero co-tenants, all 8/8 vCPUs pinned; per-job CPU model and VM are retained in each batch's `placement.json`. Hardware includes Ryzen 9 9950X, EPYC 4585PX, and EPYC 9455: these are not controlled cross-hardware timing comparisons.

Complete table and all 34 attempts (including failures), effective-source/config hash table: [tlc-results-20261109.md](../research/verify-all/tlc-results-20261109.md). Machine-readable full receipts, original/effective source hashes, DOT hashes, timings, command arrays and cwd: [tlc-evidence-20261109.json](verify-all/tlc-evidence-20261109.json). Full decoded logs and actual source/config text: `runs/verify-all/tlc-20261109-first-decoded/tlc-<id>/` and `runs/verify-all/tlc-20261109-retry-decoded/tlc-<id>/`. Raw returned log envelopes, `summary.tsv`, and placements remain in corresponding first/retry directories.

### All 29 final bounded rows

| ID | TLC states | TLC edges | TLC complete / exit | port states | port edges | port done / exit | port bad | broken bad / done / exit |
|---|---:|---:|---|---:|---:|---|---:|---|
| client_server_ae | 4504 | 15824 | true / 0 | 4504 | 15824 | true / 0 | 0 | 2 / true / 0 |
| client_server_db_ae | 56416 | 220128 | true / 0 | 56416 | 220128 | true / 0 | 0 | 4 / true / 0 |
| consensus | 4 | 3 | true / 0 | 4 | 3 | true / 0 | 0 | 3 / true / 0 |
| consensus_epr | 110464 | 717504 | true / 0 | 110464 | 717504 | true / 0 | 0 | — / — / -9 |
| consensus_forall | 112128 | 633024 | true / 0 | 112128 | 633024 | true / 0 | 0 | 0 / false / 0 |
| consensus_wo_decide | 102912 | 585792 | true / 0 | 102912 | 585792 | true / 0 | 0 | 2 / true / 0 |
| firewall | 68 | 102 | true / 0 | 68 | 102 | true / 0 | 0 | 1 / true / 0 |
| learning_switch | 43672 | 258084 | true / 0 | — | — | — / -9 | — | 1 / true / 0 |
| learning_switch_i4 | 240 | 300 | true / 0 | 240 | 300 | true / 0 | 0 | 1 / true / 0 |
| lock_server | 9 | 24 | true / 0 | 9 | 24 | true / 0 | 0 | 1 / true / 0 |
| lockserv | 80 | 204 | true / 0 | 80 | 204 | true / 0 | 0 | 1 / true / 0 |
| lockserv_automaton | 80 | 204 | true / 0 | 80 | 204 | true / 0 | 0 | 1 / true / 0 |
| majorityset_leader_election | 400 | 993 | true / 0 | 400 | 993 | true / 0 | 0 | 8 / true / 0 |
| mldr | 5362 | 18327 | true / 0 | 5362 | 18327 | true / 0 | 0 | 5 / true / 0 |
| naive_consensus | 55 | 106 | true / 0 | 55 | 106 | true / 0 | 0 | 9 / true / 0 |
| paxos_epr | 7377 | 23578 | true / 0 | 7377 | 23578 | true / 0 | 0 | 137 / true / 0 |
| quorum_leader_election | 94 | 201 | true / 0 | 94 | 201 | true / 0 | 0 | 25 / true / 0 |
| sharded_kv | 121 | 440 | true / 0 | 121 | 440 | true / 0 | 0 | 2 / true / 0 |
| sharded_kv_no_lost_keys | 100 | 400 | true / 0 | 100 | 400 | true / 0 | 0 | 4 / true / 0 |
| simple | 193 | 388 | true / 0 | 193 | 388 | true / 0 | 0 | 1 / true / 0 |
| simple_decentralized_lock | 12 | 18 | true / 0 | 12 | 18 | true / 0 | 0 | 2 / true / 0 |
| simple_election | 66 | 144 | true / 0 | 66 | 144 | true / 0 | 0 | 9 / true / 0 |
| simple_regular | 109 | 216 | true / 0 | 109 | 216 | true / 0 | 0 | 1 / true / 0 |
| tcommit | 34 | 93 | true / 0 | 34 | 93 | true / 0 | 0 | 5 / true / 0 |
| toy_consensus | 41 | 80 | true / 0 | 41 | 80 | true / 0 | 0 | 11 / true / 0 |
| toy_consensus_epr | 41 | 80 | true / 0 | 41 | 80 | true / 0 | 0 | 9 / true / 0 |
| toy_consensus_forall | 41 | 80 | true / 0 | 41 | 80 | true / 0 | 0 | 11 / true / 0 |
| two_phase_commit | 1064 | 2736 | true / 0 | 1064 | 2736 | true / 0 | 0 | 1 / true / 0 |
| twophase | 288 | 653 | true / 0 | 288 | 653 | true / 0 | 0 | 5 / true / 0 |


### Canceled extra recovery — NOT a check failure or mismatch

Two additional learning-switch recovery jobs were launched just before Main requested final bounded integration, then explicitly canceled at Main's direction. They are **excluded from the correspondence counts**. Batch `20261109-091520-1u673h`, job names `tlc-learning_switch-states` and `tlc-learning_switch-edges`; proposed budgets 600s states-only and 1800s edges. No results from these jobs are claimed.

Cleanup used `kill -TERM 16905` on the exact owning supercomputer coordinator, not a broad kill or another client's process. Supported handler: installed `supercomputer/boat.py:2642-2651` converts SIGTERM into KeyboardInterrupt; `:2951-2956` runs session close; `scheduler.py:1302-1329` closes only that batch and kills its owned runs. Coordinator terminated exit 130. Scheduler log confirms **both exact remote runs killed** at 09:17:12: states on `bx_2uat3ctg`, edges on `bx_395wpmqp`.

Retained cancellation receipts:
- `runs/verify-all/tlc-20261109-learning-recovery/cancellation-coordinator.log`, SHA-256 `9a73f94cb0bfb9bb4b9236df81a8e8a14bc424cf8373fecc57bafa2fe55065d6`.
- `runs/verify-all/tlc-20261109-learning-recovery/cancellation-scheduler.log`, SHA-256 `deaf1bc98008eb049e56d4a6ab65e42e7e111c25b2a6740d6d9961f9eea46c05`.

No audit task remains running. No commits, pushes, branch switches, source/harness edits, worktree recreation, ignored/untracked cleanup, cache clearing, or external solvers were used.

### Fixed source/tool hashes

All evidence-producing jobs report the same five baseline SHA-256 values:

| Path | SHA-256 |
|---|---|
| `research/protocols/ic3syn/models.ts` | `5d61b846a8331a9b7978b4809d53b88e5918135ded0fc6d527f2a6dc8fb3a601` |
| `research/protocols/ic3syn/common.ts` | `d84face9091688872b001f28d0ff31f1180590c57bf944efe6b32168651cd324` |
| `research/protocols/ic3syn/check.ts` | `bd864cae07b3f864ae3b6b34d454bba8b8699c84d5e679170c8c5b8458cf9161` |
| `research/protocols/ic3syn/tlc.py` | `a6090247849581aa479f4b1ef96d1d71d314e2c1402a5ec3c5e7de045a2f93a3` |
| `research/protocols/ic3syn/README.md` | `5c480248781ca6717958529234d17023a3f6303289f67cb51f617c5f17ae68e2` |
| downloaded TLC 1.8.0 JAR | `e1f11b75c4b5bc4478ba0ac5cb6ae28e40a01b0016bc33e0aa97da22dfdbcd7f` |
| initial audit wrapper | `5533c1142360837d8b83033a4832eec211a6b6ca031ed23a4307490c16e7555e` |
| fixed evidence-producing retry wrapper | `abb36ae0972fbb97fa62a70efe3f72960818667b9f7b6c073943935cc8ee78dc` |

### Verdict

Finite state/edge cardinality agreement is independently reproduced for **28 models**, including MLDR and the hand-transcribed Paxos TLC model. **Learning-switch correspondence remains incomplete**, and none of this is a proof of state/edge-set isomorphism, arbitrary-size translation correctness, blind representation selection, or the production proof path. MLDR hindsight is explicitly identified; P* remains an unresolved label. Those qualifications must accompany the measured count.


## 4. Accepted certificates checked independently in Lean

The exact captured proof objects are re-exported; no replacement invariant family is supplied. Ordinary certificates seed the emitter with their retained trees; sum cover trees also come from that packet. Existential substitutions are recovered structurally from the captured law, with fresh logical binders, then validated by Lean’s ghost-extension and `forall_some_of_ghostsubst` rules. Original-model projection is checked up to bound-variable alpha-renaming. All accepted Lean results require process exit 0 and only `propext`, `Classical.choice`, `Quot.sound`, never `native_decide` or `sorryAx`.

| Protocol | Captured certificate | Laws | Lean result | Original-claim connection | Packet SHA-256 | Lean-file SHA-256 |
|---|---|---:|---|---|---|---|
| client_server_ae | ordinary-trees | 10 | [PASS](verify-all/recheck-capture/recheck-client_server_ae.log) | checked existential/ghost bridge | `f0718ac3a082397ebdbab9aab1d17376229c65f5ac3a5d907731543349174476` | `b2302cf4dc4d7741600778c8ff14f5aaf7f2257f3baa9a7d382fcf4e3ff74579` |
| client_server_db_ae | ordinary-trees | 27 | [PASS](verify-all/recheck-capture/recheck-client_server_db_ae.log) | checked existential/ghost bridge | `281af1206130f84dbc9d9c1894690d53aa0b04bc51bc4e0b50d68de6fde5254d` | `dbd9dba52992a0608c7c5c0668c7ac47ba341ce21c0bac43979f38a3afabbd46` |
| consensus | ordinary-trees-with-cyclic | 2 | [PASS](verify-all/capture-all/capture-consensus.log) | same laws/model modulo bound names | `9b9ddc75902e4d9cdc66f2f063778fb12f8c96c2f674414d1a7dea6681822197` | `f281d66ae9f314e9201274e183b4a2f5fbde9d77024fb061efed09b291b96f2e` |
| consensus_epr | counted-machine | 28 | [PASS](verify-all/capture-all/capture-consensus_epr.log) | same model plus derived count views; caller law included | `c81f53591d19ff998dbe8f458d07c65f6bc05ffc36d0e3a0971de24a06bbe0d3` | `0552c33ca5fb5d1b157512e5e53435478fe70497d2655a8fc69295f822d920e4` |
| consensus_forall | counted-machine | 44 | [PASS](verify-all/capture-all/capture-consensus_forall.log) | same model plus derived count views; caller law included | `ea67fc7ff8388391325a64e6269072b08874ccea93d509390e7f074461c259f9` | `ccf620ae160c3b090447ddaf4b52b597fa31c4af5aabf09596e0c01c775d6822` |
| consensus_wo_decide | counted-machine | 37 | [PASS](verify-all/capture-all/capture-consensus_wo_decide.log) | same model plus derived count views; caller law included | `9f755c0b03c30faaeb4e2c4f82d72139a316b2bafcb074ef6024a667f42a1b37` | `ae0ee366c05239632a04eb4ca253f92d80bba8d3f30d9a8e043d4be4192e9442` |
| firewall | ordinary-trees | 6 | [PASS](verify-all/recheck-capture/recheck-firewall.log) | checked existential/ghost bridge | `289208b43bb920b6623d10b7f23bd25ece13bcea79b2120982bc243d77d37b35` | `8017ae2950ea734e48bffd31dbb2dd3976f3b771f25c31e51a2ecc8286163d44` |
| learning_switch | ordinary-trees | 16 | [PASS](verify-all/capture-all/capture-learning_switch.log) | same laws/model modulo bound names | `3fad96e4b916c6915f0d3b5498bdb513882c0dd9750efe9564b58bf06cac7483` | `985f87fef35d310552dc4fba159201b015b1f374cf0744786f51dad1a7e5cc5f` |
| learning_switch_i4 | ordinary-trees | 22 | [PASS](verify-all/capture-all/capture-learning_switch_i4.log) | same laws/model modulo bound names | `ad44f31b148aa0a703886783768e32216ea9c0b90dd7529aac2f1cc4daec9c59` | `1e096a70a955feaaf138964dca580397ac01e24fac2b3f6158e372c52a0c317d` |
| lock_server | ordinary-trees | 4 | [PASS](verify-all/capture-all/capture-lock_server.log) | same laws/model modulo bound names | `e68b6d5bdd30e3b86be00d674977afd718c7d984c93dee4aa83adf3c14202e4e` | `2fbb0c3b07fa47e11d57fd05fc69c360cf4df80a9b6025f0ba606e46599b452f` |
| lockserv | ordinary-trees | 17 | [PASS](verify-all/capture-all/capture-lockserv.log) | same laws/model modulo bound names | `6ffc9529116e8afdac5b2022f9b4cfc730c94c9a7fd65a06ea0437a4e0389e17` | `b7b355d6f1178bf68b6530c5493b5bca9cdf9c6fe56924bc3cb3f6c4442c6d86` |
| lockserv_automaton | ordinary-trees | 17 | [PASS](verify-all/capture-all/capture-lockserv_automaton.log) | same laws/model modulo bound names | `cc0bb87f7107a989efb68b6af660a8f72954d7ce7e767b55d35bd05ee6271d35` | `904b3db5f0ec1035a34f1850348c48fbce68de2ef3b71ae404343b9b30d28f0a` |
| majorityset_leader_election | counted-machine | 16 | [PASS](verify-all/capture-all/capture-majorityset_leader_election.log) | same model plus derived count views; caller law included | `3901663828912775846610d10f9853c135a25ab95f89afeb1eb86999f5cde1d8` | `869f5ccff2ecdf9eb429dd7f19cdc24c1c9462691dc4cbd8b7f778ad5ba3b2c6` |
| mldr | — | — | [no accepted certificate](verify-all/capture-all/capture-mldr.log) | not established | `5f4a05b9ce85c767a804ccff788d63e1d65e0ab120d726b511a60676075d5178` | — |
| naive_consensus | counted-machine | 12 | [PASS](verify-all/capture-all/capture-naive_consensus.log) | same model plus derived count views; caller law included | `7771870abacbf648204fe36578b0fc8e0e24c0529eb2ff3e3257104b58c27f2b` | `2cab86aad542fece7fcdc005368f1d58280310bd81da2daebd08f0072d19ac6b` |
| paxos_epr | counted-machine | 25 | [REJECTED](verify-all/capture-all/capture-paxos_epr.log) | same model plus derived count views; caller law included | `dc0e230fab5d0081a2c9d4f56b525ef314a2e78780647d3cb2fafaf3a512f386` | `e31b4c24e46e021c0b0187d1c2b71736530c16e47db15c18eb4d8cd77cfc15b1` |
| quorum_leader_election | counted-machine | 6 | [PASS](verify-all/capture-all/capture-quorum_leader_election.log) | same model plus derived count views; caller law included | `47c9462ca80094ac32bedf82eb46e3c962783305c07d47bdc2c256d65a3e57db` | `453ee5b909430b441f7ce7c0ef4bcfb02b93ed64ec06d098dd33aca3ebb8ded8` |
| sharded_kv | ordinary-trees | 23 | [PASS](verify-all/capture-all/capture-sharded_kv.log) | same laws/model modulo bound names | `74258416c940209a14f85bec2a195cecda1a0744c2b916a3295ab38787bdc892` | `cd1cd99deda38517d6b2adb9c9c7ada3c1dc9e455ca12508cb0cc0f62abef20d` |
| sharded_kv_no_lost_keys | ordinary-trees | 10 | [PASS](verify-all/recheck-final/recheck-sharded_kv_no_lost_keys.log) | checked existential/ghost bridge | `d47393774cf908be72b8cb1fe329d2ce4e68461b3e534cf21a4c7e13e19a02fa` | `ff93c0fe2e6e54182d8739e0da01f4dc5009e1d2d354b84aca76136abbb62a01` |
| simple | ordinary-trees | 10 | [PASS](verify-all/recheck-capture/recheck-simple.log) | checked existential/ghost bridge | `83784cec64acd8b107ca18f48c3d7993b1008e9d73d2e39fb7b610d6682732e0` | `fa61bf842aa778e21be7e63da5c6bea31666489657bd2d2406089eb6042b68d5` |
| simple_decentralized_lock | ordinary-trees | 4 | [PASS](verify-all/recheck-final/recheck-simple_decentralized_lock.log) | checked sum bridge | `f9b38416b0e6cc2fc51fe3d5560822528ebc28326fb2ac65a9018aef001c8e45` | `c3c42cdce60c48bf2f58283caea5523841db28d8da3e0010dc14f605d324b5ee` |
| simple_election | counted-machine | 10 | [PASS](verify-all/capture-all/capture-simple_election.log) | same model plus derived count views; caller law included | `7183bd7019cbc76e1b843d9c137f45277313f1b91eea8fd1b005100a771ee384` | `9bd870ff4b497621682b0d176719e6e7551fb1219d608a8d9ab4dd93138e91f7` |
| simple_regular | ordinary-trees | 17 | [PASS](verify-all/recheck-capture/recheck-simple_regular.log) | checked existential/ghost bridge | `7c441755a1dee88073d55e2d8ff701416508c8f132a6fcf176dd7cb7ec76bbfa` | `9393aa7b5681df0cf021c4792e2133191ef5bf78077e31a2461310d91278b059` |
| tcommit | ordinary-trees-with-cyclic | 1 | [PASS](verify-all/capture-all/capture-tcommit.log) | same laws/model modulo bound names | `03944dbe7f5de1b013c03ba5db13bbccbbb55746e397615550749b373a4c535d` | `da6b2d936d4646fb63839bd973f689961feefec15df2e97519ecc901dc47e7b1` |
| toy_consensus | counted-machine | 4 | [PASS](verify-all/capture-all/capture-toy_consensus.log) | same model plus derived count views; caller law included | `98e0fd726d198c96167162cf4c4fc1ca232276c7beec676bc99e33cfec658fc8` | `e2379369c2a6b3bd8a82c10ab6cfa1cc50424ddbd976b2ac7d5a64a504ecba05` |
| toy_consensus_epr | counted-machine | 8 | [PASS](verify-all/capture-all/capture-toy_consensus_epr.log) | same model plus derived count views; caller law included | `0e40c141413b088f90357b527c14c9fef7962de965716b0c05bf7a0dd59d781e` | `207dd48950b6aa1c280b1a2e40faccb5d3cc2f7485c50296b76b20b6930ab4fe` |
| toy_consensus_forall | counted-machine | 8 | [PASS](verify-all/capture-all/capture-toy_consensus_forall.log) | same model plus derived count views; caller law included | `07b9eefc1d67934f2264e2da3774dacc4a4b85c8fd76bf7a1874c58136084b11` | `ca5f69dc699e4cb81ce74deffb495c4c4ab05b821f44baa2aa16004115aaf330` |
| two_phase_commit | ordinary-trees | 22 | [PASS](verify-all/capture-all/capture-two_phase_commit.log) | same laws/model modulo bound names | `b17e1a47997f7de4e80b0d2c2cce353375c1279f7ff771e27eb1f3ba587c5359` | `8289ca3313d0ee7bb77fdbcbca8b56cf01947ef641d2aade2e0e5b2dfa4401ba` |
| twophase | ordinary-trees | 35 | [PASS](verify-all/capture-all/capture-twophase.log) | same laws/model modulo bound names | `48007eac85b8ea0a01d3b595f9330bddc125082d498c8ab074b54a550e8c2f79` | `76a60333bb61f6e1dcce0ed0276cb74cd91355e77bc508e5938c5c4831c38ce0` |

**Independent Lean summary: 27/28 accepted captured families passed the original-model export check.** MLDR has no accepted family. Initial failures and every retry are retained, not replaced. The ordinary/counted/ghost/sum kinds all have existing Lean machinery; a rejected supported certificate is not an “unsupported exporter” result.

# Paxos counted-certificate diagnostic (baseline 6a3874d3)

## Conclusion

**Item 4 remains failed for Paxos.** The retained accepted TypeScript family has **two independent Lean rejections**, not one. This investigation neither changes the production model/checkers nor replaces, repairs, or searches for a proof. No conclusion that Paxos safety itself is false follows from this failure.

| Zero-based law index | Captured law | Exact rejected check |
|---|---|---|
| 12 | `scan-prefix:cnt:rowOk:d93992f463f488aa` | `cEntryOk` → `key2Ok` → `skFresh s 29 = false` for further key `k$21` |
| 20 | `carry:co-write:6282256ba10ee781` | step `checkMC` → `checkCountedW` → `checkGoalLemmas` → main `checkTLemmas`/`checkT = false` |

All seven top-level machine checks printed true, all five count declaration checks printed true, all 25 entries' witness checks printed true, and all 50 start/step certificate checks except law 20 step printed true. Every entry condition except law 12 printed true. TypeScript `checkCountedLaws` and all 50 individual `checkMC` calls printed true on the exact retained packet.

### Law 12: identified side-condition mismatch

The emitted further key `29` is `k$21`, also the bound key of quantified flag `72`. `key2Ok` in `lean-kernel/Sets.lean:933` requires each further key to satisfy `skFresh`; `skFresh` at line 926 refuses a name occurring in any quantified-flag body. The diagnostic prints the actual flag body and finds this occurrence. All other `key2Ok` conjuncts are true (including key/primary-key inequality, exclusion from external variables, precondition and initial state, and compatibility with the other laws).

This is not failure of this law's start or step refutation: **both checkMC results are true**. It is a machine/law freshness admission condition absent from the TypeScript `checkCountedLaws` wrapper (`kernel/kernel.ts:2090`), whose body checks obligations via `witsOk` and `checkMC`. The existing exporter interns identical textual names into identical Lean variable indices (`lean-kernel/emit.ts:367–424`), so it preserves this collision. Determining whether a sound bound-variable renaming bridge could discharge this restriction is outside this diagnosis; no renaming or replacement certificate was attempted.

### Law 20: narrower unresolved checker/export boundary

For `carry:co-write:6282256ba10ee781 @step`, Lean accepts:

- all named hypotheses as members of its generated goal (`namedIn = true`, missing hypotheses `[]`);
- declaration key restrictions, read freshness and read/witness separation;
- conversion of reads to counts;
- counted witness freshness and count-instance resolution;
- certificate table well-formedness (`wfTab = true`).

There are **no lemma cuts** in this certificate. The remaining failure is the main encoded tree (`checkTLemmas ... [] tree = false`, hence ordinary `checkT`). This is distinct from law 12's admission failure.

The final diagnostic additionally encodes the exact TypeScript `mcGoal` for this step, using the original emitted name map, with the existing `encode` function and **the same retained tree**, not a new proof. It compares those literal hypotheses with Lean's reconstructed full counted hypotheses and checks the direct goal/tree. The terminal kernel output is `("bridge20", true, false)` and `("differing_hyps20", [])`: the full hypothesis lists are identical, and even direct encoding of that TypeScript goal with the retained tree is rejected. This excludes differing reconstructed hypotheses as the immediate cause of this obligation failure; the remaining boundary is tree encoding versus checker semantics. It does not establish which leaf/row operation is ultimately responsible. An emitter defect versus TypeScript/Lean arithmetic/tree-checker disagreement remains unresolved. Do not describe this as a proven soundness exploit or as an independently verified Paxos certificate.

## Evidence and reproduction

Read inputs: user `VERIFY-ALL.md`, `COMMON.md`, `supercomputer --skill`; existing `capture.ts`, `export-captured.ts`, `check-lean.sh`, `recheck-archives.ts`. All substantive extraction, TypeScript checks and Lean computations ran on boat. Laptop activity was reads, git/status, edits and supercomputer scheduling only.

Input: `runs/verify-all/capture-all/capture-paxos_epr.log`, `ARCHIVE_BEGIN` base64 xz tar. Exact original retained objects:

- packet SHA-256 `dc0e230fab5d0081a2c9d4f56b525ef314a2e78780647d3cb2fafaf3a512f386`
- generated Lean SHA-256 `e31b4c24e46e021c0b0187d1c2b71736530c16e47db15c18eb4d8cd77cfc15b1`

`research/verify-all/paxos-diagnostic.ts` asserts both hashes before checking anything. It copies only definitions before `theorem verified_check` into a separate `/tmp/paxos-diagnostic.lean`, adds `#reduce` diagnostics, and uses kernel reduction, not `#eval` or `native_decide`. The rejected original theorem and its consequent error-induced `sorryAx` are not imported into the diagnostic. Diagnostic elaboration failures listed below were rejected, never accepted as evidence of a theorem. No replacement safety theorem is generated.

Commands (same job file each time, progressively refined diagnostic script):

```sh
supercomputer run --jobs research/verify-all/paxos-diagnostic.jobs.json --out runs/verify-all/paxos-diagnostic --class interactive --data runs/verify-all/capture-all:evidence
supercomputer run --jobs research/verify-all/paxos-diagnostic.jobs.json --out runs/verify-all/paxos-diagnostic-deep --class interactive --data runs/verify-all/capture-all:evidence
supercomputer run --jobs research/verify-all/paxos-diagnostic.jobs.json --out runs/verify-all/paxos-diagnostic-deep2 --class interactive --data runs/verify-all/capture-all:evidence
supercomputer run --jobs research/verify-all/paxos-diagnostic.jobs.json --out runs/verify-all/paxos-diagnostic-detail --class interactive --data runs/verify-all/capture-all:evidence
supercomputer run --jobs research/verify-all/paxos-diagnostic.jobs.json --out runs/verify-all/paxos-diagnostic-final --class interactive --data runs/verify-all/capture-all:evidence
supercomputer run --jobs research/verify-all/paxos-diagnostic.jobs.json --out runs/verify-all/paxos-diagnostic-terminal --class interactive --data runs/verify-all/capture-all:evidence
```

Job command:

```sh
bun install --frozen-lockfile >/dev/null && bun research/verify-all/paxos-diagnostic.ts && bash research/verify-all/check-lean.sh /tmp/paxos-diagnostic.lean
```

Job allocation: `cpu:4`, `memory:14336`, `timeout:1800`, `vm_type:large`. These are diagnostics, not production timing claims. The scheduler's shell exit code is not the job's verdict; use each output directory's `summary.tsv` and job log.

| Output directory suffix (under runs/verify-all/) | Boat batch | Job exit | Job seconds | Outcome |
|---|---|---:|---:|---|
| paxos-diagnostic | 20261109-090337-5yqi57 | 0 | 55.73 | identifies two failures |
| paxos-diagnostic-deep | 20261109-090503-rou41h | 1 | 47.9 | diagnostic-only `Inhabited CEntry` indexing error; not trusted |
| paxos-diagnostic-deep2 | 20261109-090819-bnnp1u | 0 | 55.57 | isolates key2Ok and counted-tree checks |
| paxos-diagnostic-detail | 20261109-091017-b2pjj5 | 0 | 50.74 | isolates skFresh; count witness/table checks true, no lemma cuts, tree false |
| paxos-diagnostic-final | 20261109-091254-egelwj | 1 | 82.46 | diagnostic-only missing `BEq (List VDef)`; not trusted as final receipt |
| paxos-diagnostic-terminal | 20261109-091634-0i8y7p | 0 | 74.74 | clean comparison: identical hypotheses, direct retained tree rejected |

Each output directory contains `paxos-diagnostic.log`, `summary.tsv`, and scheduler metadata. Lean is 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. The clean detail diagnostic SHA-256 is `8935f6e79fd3eb61f65a930637ad567798e69259dfa578723544fe41a70915e5`.

### Final verified hashes and receipt

- Diagnostic TypeScript: `9634e991534fbc5c34b9dd53ebd734fbc91f9f3ffe2c1d4055960b5608f7cbe5`
- Job file: `725156dc86b0c222c989c72f3f5fd23fd0c219384faeb9de0f7572329cf66d82`
- Final generated diagnostic Lean: `afb426d11a5c457b514bf403501fca355c1b1c08d166a61afc8b33638c6eda7f`
- Final terminal log: `101cb41a6b9e191c98e245186db55a89f6a7cb2c2254d864fec1a4adf799dff3`
- `runs/verify-all/paxos-diagnostic-terminal/summary.tsv`: `paxos-diagnostic 0 74.74 boat`.
- Lean terminal: `LEAN_WALL seconds=68.00 maxrss_kb=3384456 exit=0`.

The final clean run contains no elaboration error or error-induced placeholder. Earlier failed diagnostic attempts remain disclosed above but are unnecessary to the conclusion. All six own scheduler tasks are terminal. Workspace verification: `git diff --stat` empty (tracked baseline unmodified); new files remain under allowed diagnostic names. No commit was made.

## Scope

No production rerun, external solver, core/kernel/lean-kernel/protocol source edits, branch changes, commit/push, cleanup or cache clearing. Boat compilation via existing `check-lean.sh` only. No other worktree writes. All own processes terminate via bounded jobs; no processes were killed. Main owns overall verification totals and final report.


## 5. Engine answer-encoding audit

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


Full generic-template, tuned-constant, environment and I/O inventories: [engine-trust-audit.md](../research/verify-all/engine-trust-audit.md). The scan covered all 303 core/kernel files; the conservative DSL import closure had 36 files and zero I/O/dynamic-loading scan hits. It found 86 distinct environment accesses in that closure (110 repository-wide). No per-protocol dispatch or loaded protocol-specific law family was found, but this does not establish the absence of benchmark-shaped knowledge: scan-prefix/carry/future-writer templates and benchmark-shaped gates remain live. `GDP_STRICT` is currently on by default for non-usual decisions despite a stale adjacent comment.

## Trust verdict and remaining limits

| Claim | Audit verdict |
|---|---|
| “Production proves 28/29 IC3Syn protocols” | **Reproduced for this baseline and these encoded models**: 84/87, the same 28 in every repeat. It is not 29/29, and it is not a claim about arbitrary source-domain sizes. |
| “Paxos is independently checked” | **Not established.** Its actual captured counted certificate is rejected by the current Lean export/check path. A TypeScript `checked` flag is not a substitute. See the diagnostic for the precise failing condition and what remains unresolved. |
| “MLDR is proved in production” | **False for these runs**: unknown in all three. A hand-supplied family or candidate count cannot replace that measurement. |
| “Every broken variant is rejected with a real run” | **Too strong**: zero were proven, but only eleven had a refuting trace. All eleven captured repeat-run witnesses replayed; exact primary witnesses were not retained. Seventeen primary runs remained unknown and one timed out. |
| “No knowledge is supplied by hand” | **Qualified only**: no hand-seeded inductive law family or supplied `.facts` in these models; but typing/domain/quorum restrictions, initialized summaries, switch reflexivity and invariant-aware representation choices are supplied. |
| “The ports are the unrestricted original protocols” | **Not established**: finite correspondence is evidence on the tested instances, not a cutoff, refinement or bisimulation theorem. Paxos’s TLC surrogate is another project-authored transcription. |
| “There are no answers in the engine” | **No literal protocol-name shortcut found**, but generic templates, scope gates and constants were visibly benchmark-shaped. Static searching cannot establish absence of all answer-encoding or out-of-distribution generality. |
| “These are the exact certificates from the three uninstrumented runs” | **Not established**: those commands do not export proof objects. Lean checked actual accepted objects from explicitly disclosed observational repetitions, with packet hashes, not inferred or substituted proof families. |

Final validation command (on boat): `supercomputer run --jobs research/verify-all/jobs-finalize.json --out runs/verify-all/finalize-confirm --class interactive --backend boat --data runs/verify-all:evidence`. Its check job runs `bun run check`; the report verifier checks every linked artifact, all 146 primary log hashes and in-job kernel identities, all five sections, and certificate/receipt tallies. The final report-only rebuild after EOF whitespace normalization and receipt relocation is in `runs/verify-all/report-final-provenance/`. Seven test shards and the quick bar were not rerun: no engine/model/kernel change or merge is proposed.

The trustworthy evidence is the reproducible, qualified measurement and the successfully kernel-checked individual certificates. The gaps are equally part of the result: especially the independent Paxos rejection, the unproved MLDR row, incomplete broken-variant refutation, and source-model/generalization limits. Nothing here justifies presenting the whole suite as unconditionally or independently verified.

### Verification-tool failures and cleanup

Initial capture/export failures are retained in `capture-all/`: missing scalar-ghost declarations (`simple`, `simple_regular`), missing `Sums` import (`simple_decentralized_lock`), and the substantive Paxos check failure. Audit-side adapters corrected the first three without touching core, kernel, models or harness and without replacing the captured proof. Additional original-claim ghost bridges were checked for client/server, firewall and no-lost-keys certificates. The final sum export seeds the effective plain machine and uses captured side-goal trees, preventing silent re-proving by the exporter.

The replay helper initially confused the fixed small-instance `p.bad` predicate with the actual production-domain law. Its failed receipts are retained; the corrected helper checks the actual law along the legal interpreter run. Initial TypeScript/lint failures were confined to new audit scripts (optional-path typing, scalar-read typing, lexical sort comparators); successful final validation is recorded with the other evidence. TLC wrapper/output and engine-scan truncation failures are detailed in their own reports. The first commitlint invocation (`finalize/commitlint.log`) failed because the remote source snapshot has no git root for `--edit`; the file-backed stdin retry in `finalize-confirm/` avoids that repository lookup without changing the message.

No cache was cleared, no ignored/untracked output was cleaned, no worktree was recreated, no history was rewritten, and nothing was pushed. All started verification jobs were awaited to terminal receipts. The report and scripts are the only intended committed changes; large evidence remains under ignored `runs/verify-all/`.


### Original-run evidence hashes

Full SHA-256 per log (includes stdout, wall, affinity, and in-job kernel identity):

```text
7f111761a678f8288b34a8cd792bab4268257b52ee817f0ac7bfc8d13a429f50  verify-all/production/broken-client_server_ae.log
f2c769804360698526959c0d6f03653b5902b82d1f25389c2dd0a5be631ca369  verify-all/production/broken-client_server_db_ae.log
38dfd372762af6288aa951e1cf005617d750fb408c3db1e8c34e51546d9220e7  verify-all/production/broken-consensus_epr.log
52d72831dfde20160cb6a999d482baf0c1fa8268ce413071cae746d23e644fff  verify-all/production/broken-consensus_forall.log
6788151d08a8599c3b974a1f30b26e00e4c8ee3a2e8cf3ecc615ce559e203353  verify-all/production/broken-consensus_wo_decide.log
4033c4096b5c08185b9bdf3ce8fbaa9c323720dc7ffe92956c1053f57444f14e  verify-all/production/broken-consensus.log
13ca3ab220af81bfe98330b37e734ff54471dd99301cf97a3c6b2ee6077f9793  verify-all/production/broken-firewall.log
dc6b21170793250ddf31fc0968e154d8acb3b0343340f2d7f8edda02a0900cdc  verify-all/production/broken-learning_switch_i4.log
98d00f6e443ce76cc0e19386dd9f290ba0b1e39e8f7e559750fcf2b6ba99e0eb  verify-all/production/broken-learning_switch.log
b9ad773f0ce3def2a6a6421ed9fadccba5e7d116d101f736f06bd8159f6a4c1b  verify-all/production/broken-lock_server.log
582f2c8174bc99ae916f37c113c642c409bad97d7a5cc4d8784bbf9dcae00baf  verify-all/production/broken-lockserv_automaton.log
c45c1d5477026b3b453fc26985c15567494f7a0ba5f56bd33aff20337c069ecb  verify-all/production/broken-lockserv.log
9aa0b066ae70afc2d0fff8a48feb63f92fb24ee75f3dc03d0f4b70c403d7e885  verify-all/production/broken-majorityset_leader_election.log
a99d8ed319ddd2bc6eb9a7b96e9192f5bdcdc4ecd7fa030cb269bdd9a0623953  verify-all/production/broken-mldr.log
9123337b883d582f8b9f455b94f35684aa907fe873a1c3f72432a5c37f101398  verify-all/production/broken-naive_consensus.log
ae7f5ef55a75c044c51d7083e49ac73c6ffbfbc47a52405a74d25d585835998b  verify-all/production/broken-paxos_epr.log
0b4991f45485374500ee3e97523df53c1f7b7016ee0d4a446254ba143e296e37  verify-all/production/broken-quorum_leader_election.log
96f22ccad42036af0730c37d1f4d820b8742cd84fe1c3e020e1ffe58bba99845  verify-all/production/broken-sharded_kv_no_lost_keys.log
d6a95f1a7239902101ffb937fe3e722f2251cb66df3ed8f78d60aecb8c76459a  verify-all/production/broken-sharded_kv.log
575a80de1bed6dee0ddbfaef738092ac89fdb1194ddfb5c3b254616902da54ef  verify-all/production/broken-simple_decentralized_lock.log
c4fa9a489374aa94e1010234ad147d30d27e4a37490b55c25fda1870d67fdc15  verify-all/production/broken-simple_election.log
b9675c2f9b51caa31ec074fe952676b797f05bcf95cdded1edb63b0bb50e80e1  verify-all/production/broken-simple_regular.log
68cab378880e2389737b834b9b530c7671b9aa92b34bcdcfc920fbe5b094561e  verify-all/production/broken-simple.log
2c93f6018906942c12ef60a2354af7d517b226e5c93e261d3f6686703aa3685f  verify-all/production/broken-tcommit.log
5afbd7a23e573754609be9ba7ec5e9e63d37456c6a2c18c9659ed2557ec3d7be  verify-all/production/broken-toy_consensus_epr.log
3b50d920d4bd76f49620067cad7c5c8a993b0e07711f002e67afd5e4ddddff67  verify-all/production/broken-toy_consensus_forall.log
d2ca2a3a94d83a74d1c8a35115e61e72d6435ef8b7bbd4f4838f6cfba3a1d248  verify-all/production/broken-toy_consensus.log
e85ea1d4c6f3fb09b0cde87d243751d444b26d25a4d34a5e9f7b3b69b66301f7  verify-all/production/broken-two_phase_commit.log
60c74a4ed17857bf36c442322dbbfa4735dc32acddfb8fd250af7356b6791d85  verify-all/production/broken-twophase.log
5f86ce5fc6d55bfa0fbd1d713556d8f0b6fc6e2cac017fe4d3e626c4e3b6d3ef  verify-all/production/duoai-consensus_wo_decide-r1.log
e899081582ef3e81a85f279a08a942abaf8a2d36ddd8788c92eece1c432f716f  verify-all/production/duoai-consensus_wo_decide-r2.log
28a82f5f29e45d1f89d1a2999edc6b8e9ab11498b399c747b8c42ebe0e3f7f58  verify-all/production/duoai-consensus_wo_decide-r3.log
55784fe7ba0ef39bd2b4abd6eb5a86c31aadf9f1e2d3f0724569be3fb4ac9dd0  verify-all/production/duoai-decentralized_lock-r1.log
c4dc6f4a5226ef28046213b1ab9d8a29d750b791d074a0a5ea53137a7c8f5688  verify-all/production/duoai-decentralized_lock-r2.log
bf7f9764b99f503c3369ae26daac696dc1074e74de33c0e9e41f4b72c5a816e3  verify-all/production/duoai-decentralized_lock-r3.log
75ec788e849f906bdab2dfeb41748b780b2263e7982d0f5d4a557548739cfc22  verify-all/production/duoai-distributed_lock-r1.log
411bc14ab0fa61f0612057510bbd25f2f7a7422556fd5b5b6efb60a99ca7b6ba  verify-all/production/duoai-distributed_lock-r2.log
642b0ebab684527f60bf267538f431772a053eb218268079c44c45c1879681dc  verify-all/production/duoai-distributed_lock-r3.log
e47560be9e7dda63f6ef0aa12302cf796cf3024adc2f001d262afce7eb8d8b93  verify-all/production/duoai-lock_server_async-r1.log
b88fda24771767b5b5e76d1031f2213084f6d9a1be5624f76c324b039ddbccd5  verify-all/production/duoai-lock_server_async-r2.log
2b7f72488ae7c245eddd9d7e843aff85d86e4eee5517fc02fe039c5ab79a8cdb  verify-all/production/duoai-lock_server_async-r3.log
a4df9ed4f6b6a0ed8191d3fa5ed02bf7890759300bf6998a9e74cae4afc6730f  verify-all/production/duoai-lock_server_sync-r1.log
0209f3d7a8487f34ed004184d1dbe684c9989190bcda0908bfda9dd80a64aa1f  verify-all/production/duoai-lock_server_sync-r2.log
56afd0ff17c805aa070f3465246ce47e73f74aabad6318975d147c992bc61354  verify-all/production/duoai-lock_server_sync-r3.log
c930f23ba3573dad655f13aca20432cb14a120f8483939e7dd741aeb92f9f24d  verify-all/production/duoai-ring_leader_election-r1.log
e67f1dfc4dcb94b9481f7554b514162a86804795a2b05bc5afb3ff664bc898a2  verify-all/production/duoai-ring_leader_election-r2.log
fd7b39c4e677a0d666c7b5eafc5adc362f16e88ebbb0c04aaadee6b6a9ada819  verify-all/production/duoai-ring_leader_election-r3.log
c0dfb02d8cf705881bd28d374853c11e03636f3f02f6abdce4a8797ebd6cbbd6  verify-all/production/duoai-sharded_key_value_store-r1.log
868ead9dd4ddbcd8e8679bc469f44bcaca661b52795277f5d559ea3cbc590e7b  verify-all/production/duoai-sharded_key_value_store-r2.log
63de081132345932d91bc3c75123ea3b369cfd239bd360ab8f433124e77b27c8  verify-all/production/duoai-sharded_key_value_store-r3.log
da3f83b3548fdd80f5fa39932a10d3d228ac759c5fbdd17a0346d65dd6d74732  verify-all/production/duoai-ticket_lock-r1.log
4065a8afb3ee0bb6f4946de5ced84940cfd083b7c92db7cbdee4fe5c11b3eddc  verify-all/production/duoai-ticket_lock-r2.log
e103a4225168bc1be2a41b8ee3cefe8e4b71c844bab7679a8347d1f2f7bd59fd  verify-all/production/duoai-ticket_lock-r3.log
51c73ddeaa2bfd1a1bd3b3aab62466f9d61ec605c3b11eaa59ea1b6bf74a4163  verify-all/production/duoai-toy_consensus_forall-r1.log
babf43aa4c71b452fca6dddbf7c226f97ccb8d22d86116ad957248a19406f6ea  verify-all/production/duoai-toy_consensus_forall-r2.log
9eecd6fe3dfda5986c6fc97de10d612b9e272336be160c3da29b3c03a8290b95  verify-all/production/duoai-toy_consensus_forall-r3.log
bcc055452fdfe6bd271d00ec68dbf6afabb7fa07c9f4bd2937a8ee35eb57b372  verify-all/production/duoai-two_phase_commit-r1.log
6baed2ee1daee157f1e39ee421b0cff87b230fc48e6f9a992ed5bb310f455b0e  verify-all/production/duoai-two_phase_commit-r2.log
cde2e52063281c7fc91500077d3e0d156eb160600a2bdb03e89f242e8d64924c  verify-all/production/duoai-two_phase_commit-r3.log
4396491198d6fd8d5b1f41637323d1a91e03f1e30c1a0490b554f37018fee1e5  verify-all/production/ic3syn-client_server_ae-r1.log
0797d5671960291d311ef09151b75190e9ae8d70220bd762f80f535b2d9663a3  verify-all/production/ic3syn-client_server_ae-r2.log
bc61c10f97b719ade5d983257102c3eccfe52006d76b6f9fd5d04de7715f6ee6  verify-all/production/ic3syn-client_server_ae-r3.log
3bd31fad640ec6c0a01ea7947274917e74526ff606a3647f5ad8e1068ef167f4  verify-all/production/ic3syn-client_server_db_ae-r1.log
b4698e21343441174bbb1ec68648cc91998188bea11308ed35573a104c9db077  verify-all/production/ic3syn-client_server_db_ae-r2.log
86fc29b3e613286cf78078e324da8c4ccd8f4fd2c7c40e9edc45930db19d47f0  verify-all/production/ic3syn-client_server_db_ae-r3.log
d0e402826734a3241feddf807945272d0450d551c625cd1344dd3c7221b0ec8e  verify-all/production/ic3syn-consensus_epr-r1.log
35a9bdb6c66c9e25670b4aaebcaf3937fcbbb5ef59f62124319b06ec258f43af  verify-all/production/ic3syn-consensus_epr-r2.log
8e67cf589304805ce7d121da969c04df5398d38c5b4fdf1d948bd2b9c2ed90d4  verify-all/production/ic3syn-consensus_epr-r3.log
1beb0c3854ed77470928e53a3767ac3e7cc50cfec465d90ab174040ad62df586  verify-all/production/ic3syn-consensus_forall-r1.log
d2c102c3837045ee915f312ec3ce1c9104143e4c20b7f623f2b12537618ad2bf  verify-all/production/ic3syn-consensus_forall-r2.log
876d7a093aade1a5e073f424034f3d02fc6e0e5ba864cd283ce1378edd548396  verify-all/production/ic3syn-consensus_forall-r3.log
815720cb22eb504c80a0efec193be1d46e3b6b34d7d45dd18530f7c48b2d8659  verify-all/production/ic3syn-consensus_wo_decide-r1.log
6096554efa45710438af89b2541818e228b2d156ef76208899844e52102fe7b4  verify-all/production/ic3syn-consensus_wo_decide-r2.log
5004e6cb988dbed7d85a6757c0d5d10e4275ff4c7e8971e77fe9fef98c6e1167  verify-all/production/ic3syn-consensus_wo_decide-r3.log
a04ca08f23597096b6867dc6aa9aef0b869dd0d1aa417e1f103994e7918b6bb6  verify-all/production/ic3syn-consensus-r1.log
744765bc8398a0c95cd29fdaa16393643a88bf28900d45218e0915cb658730f8  verify-all/production/ic3syn-consensus-r2.log
05ffb38eaaaea276e4f3bb86afc1e0e26b748bc272d0b4288e0bb6fe848cb129  verify-all/production/ic3syn-consensus-r3.log
0a19fa4d97d55f3524c2637f0c7137f6b5bd31ffba5b77d3ff09eaaa70aa0072  verify-all/production/ic3syn-firewall-r1.log
2db558f0b2647d678d2e2d3a7ac60110aa2190c2ab3e95062209da9e624848ec  verify-all/production/ic3syn-firewall-r2.log
ec2e5a342df2c18255ece307334723fcacb99e718c93a10642ef9a5860061c8d  verify-all/production/ic3syn-firewall-r3.log
0be9eff7da09390de90ac3a370830d56d20de2f5ca487b0794edec47f1fde24d  verify-all/production/ic3syn-learning_switch_i4-r1.log
dc7add54c8760382fa2502f7c66c271fdeb8a315b110422351f7c5b7bb16ffb9  verify-all/production/ic3syn-learning_switch_i4-r2.log
8010d7f8be42cbb5a51f90b7a2ba31c74b7e8c0bce3b945db03c5c4241239759  verify-all/production/ic3syn-learning_switch_i4-r3.log
9f00ad69a918334486963205da3cd62233150498fa40fee24f55472f220a99d3  verify-all/production/ic3syn-learning_switch-r1.log
9fba2cad294fa06ab74cc22f483166cf544c64f68e8b87cc2ae0cd94e562b00e  verify-all/production/ic3syn-learning_switch-r2.log
e40038a0748d5d5d9ad6cd8212373923f10a19241db3d8fc10f519729106b15b  verify-all/production/ic3syn-learning_switch-r3.log
a08bedfb5303586d381e512e14fdbf6482dcbf15404f4a51b48eb717cf34fb51  verify-all/production/ic3syn-lock_server-r1.log
37bb54173cdce7a964e3dae068d2f45541a2be52a17ea36967ecb74896c5ae99  verify-all/production/ic3syn-lock_server-r2.log
7d7c48991f9458325e9bbf347d096a142ab83bb14b411f726b69292ac111553a  verify-all/production/ic3syn-lock_server-r3.log
9eb989936bdc4cc846f1d5a6e80c762abe7659f88b900d81fb3f02018451bf82  verify-all/production/ic3syn-lockserv_automaton-r1.log
bd44aebcbda7b43984cc4ff9d58f24c29841915b6dbb69815eb14724e094b72d  verify-all/production/ic3syn-lockserv_automaton-r2.log
f901b5808a03cd23db2169a87b11ab995f3c36c58fcc4a05d153348780df3876  verify-all/production/ic3syn-lockserv_automaton-r3.log
df7f04770922dc146e41887b8deee45c147ad17ec458d077374846cb8dfcdf07  verify-all/production/ic3syn-lockserv-r1.log
bef344838d118ce3a7dcb2642773c249bec7a28743a378c0c267763d984874d9  verify-all/production/ic3syn-lockserv-r2.log
3684ec1a15c69e404d26caf2df11bfe0986a3f77fd176f7b0ee87c2a4b796144  verify-all/production/ic3syn-lockserv-r3.log
2b1f64b02d0e58eed51e2a5320f7ed3431746a5e31542bf7fbe6a81f28045e8e  verify-all/production/ic3syn-majorityset_leader_election-r1.log
7400b64f8890d03ddf7e15a80250320fa6b6c536ab27f570bcd2ebdc2c7ac428  verify-all/production/ic3syn-majorityset_leader_election-r2.log
ef8d856d126557de3f1e03acc93877177b46e95e01c2fbe77744a6e4cfe99470  verify-all/production/ic3syn-majorityset_leader_election-r3.log
4a3039865fa7ab5e8d413a5c43fab2a3867d48e10a40145437de53c3ec032dd1  verify-all/production/ic3syn-mldr-r1.log
3a09cf03974f156f80bb24c2adee78ee741e30e77917a03c5442fad044df6a44  verify-all/production/ic3syn-mldr-r2.log
a5b80b5d60e923fd6ba3e26abc7992fd40f0ac405c9220ac74c3644f9cc7cd6c  verify-all/production/ic3syn-mldr-r3.log
18705266244a449394fc9f89eb10a6cf52e81a156fd3736fb7865393cf231b3e  verify-all/production/ic3syn-naive_consensus-r1.log
63e225e152bed1abb6ede00adf6530ea0fceda9d36f78369027aa06082ad6360  verify-all/production/ic3syn-naive_consensus-r2.log
6200558dbd65567d95e416b287c22ea165b97a6594232d439b1da7240932003e  verify-all/production/ic3syn-naive_consensus-r3.log
f5fc55d08a520703d75b11d27e5e4da7be04ef63a4dbf64b8ec0a2813e92222f  verify-all/production/ic3syn-paxos_epr-r1.log
e28b8f42aa2112cb156efafbc49e87068b3cd26fb46b303d9f1155e18ad3e833  verify-all/production/ic3syn-paxos_epr-r2.log
5cbdd99fd841f34855b6f59c9783418503288c27efa885246ea4fcd2076dbbd4  verify-all/production/ic3syn-paxos_epr-r3.log
dd1acb3c2888f2424349a0b80fd621dfe72de9c9ee007595046057d925226165  verify-all/production/ic3syn-quorum_leader_election-r1.log
f8d1d3c29da2fc777d3296b4abae64cbce45c9329d790550106ab2ed03a3e30f  verify-all/production/ic3syn-quorum_leader_election-r2.log
9f2a2082ded77d0b82e229b43d878ab1af0706e4b6551b3a45b4fcb831e32a53  verify-all/production/ic3syn-quorum_leader_election-r3.log
839dfeb6bfe99d6ab83d33e22e4e2ad3d7e28091d4763caa2d748f495a1dc094  verify-all/production/ic3syn-sharded_kv_no_lost_keys-r1.log
51990daf61a8bddb54432a0b4dc61a661d62a147a9adccd042c902502d83732e  verify-all/production/ic3syn-sharded_kv_no_lost_keys-r2.log
48d9892c3598bcbaa46d314c3e141651515df6660b6861227ed5ef1feb0f26af  verify-all/production/ic3syn-sharded_kv_no_lost_keys-r3.log
b8be1113a4a0998689cc8f12bb8b6b6beb649ea16e8d6a7c63270d2d960deb96  verify-all/production/ic3syn-sharded_kv-r1.log
7f529771cd6dbd53c34e1b558ffd0fc19d138e3b0dd1465364a5655dbdc5a676  verify-all/production/ic3syn-sharded_kv-r2.log
8c3f72c30706de569d1495792de7ac85aa9ca6edfcbb86ba09a8d873ec3711fc  verify-all/production/ic3syn-sharded_kv-r3.log
80fe6f7039bc1841dc5137254929a328ac4c763b40bdb7a84af289fbea8b5421  verify-all/production/ic3syn-simple_decentralized_lock-r1.log
e88fd565861b64814a17ea73776cc4c74edbec5d85d1500c1a9bdc06be7e87f5  verify-all/production/ic3syn-simple_decentralized_lock-r2.log
0e732319f6743122ddf48ef78d0c5c116cfb12744a567b4a7679ea96abb7c505  verify-all/production/ic3syn-simple_decentralized_lock-r3.log
f2c7ca2d7a6dd0c8f3b1428e3ed34e7636e480eda0e377fcd5bef2d1694b184a  verify-all/production/ic3syn-simple_election-r1.log
ad7463cb9ac542c6e20d04e098f0c07c392bed72f2da74a6b5173aa04a38afa1  verify-all/production/ic3syn-simple_election-r2.log
aa80a6ebf8907d24167765604dcc07b1a4a3e9c8d0c5b05ca6a67fd4554f650e  verify-all/production/ic3syn-simple_election-r3.log
db9b58fd877e2a7d3b8370f48a073e11caf2f458e02ef6489403a64026dafdeb  verify-all/production/ic3syn-simple_regular-r1.log
58ddae2a717c901c002c4a875047f6a2cb6ae19e06ac352de51e2cc28b2c5a53  verify-all/production/ic3syn-simple_regular-r2.log
081094ba1b2282e01596a9fe7efd1b256514fa977e855ce99a6a0a535d1cdf0b  verify-all/production/ic3syn-simple_regular-r3.log
f7711aaf39f8ac5c0c50626c808b8e83bbfde96d5d05157dc2e3e67daab12939  verify-all/production/ic3syn-simple-r1.log
de133b674f653089cf098efe0659c425a5a47963c98b7e56fcecf6a7f03dd2c5  verify-all/production/ic3syn-simple-r2.log
0547bf525ffdd935da492dc2863ab19f12673ae7cc82490c3c468615e480d457  verify-all/production/ic3syn-simple-r3.log
358ca82ac8f634e8c257af873948d748ec7609162537a3a8d681977e97a9fd04  verify-all/production/ic3syn-tcommit-r1.log
70d6424b1348ad79aa84241bd331dda5a1785559bf82217d6dd46c4600094444  verify-all/production/ic3syn-tcommit-r2.log
cb912943ec9ee334634840eca1b5a6ac36edd51df8824433ce5f1f8ad86188e6  verify-all/production/ic3syn-tcommit-r3.log
b79f265aa648aea0a2b55c9ab360d952aa83b46366da2373d31e3b8dc4745b32  verify-all/production/ic3syn-toy_consensus_epr-r1.log
2ba26e2d60ae8f77838b1cec4ef1dd78e77b3987a798fdad96f6abd00c447e7f  verify-all/production/ic3syn-toy_consensus_epr-r2.log
ec05dfa043bc4150256257aebe5369fb8b03b435f6cd21584eadfd39b090dea5  verify-all/production/ic3syn-toy_consensus_epr-r3.log
4812e5ae4e7df5d5e5b18c3fde0d258b6dda61855bacf8a3860460490410ae49  verify-all/production/ic3syn-toy_consensus_forall-r1.log
e04fca3fb0b92eaa284578465d1b20a6fc299fbc7e3015e7cd740ff68c60c0d3  verify-all/production/ic3syn-toy_consensus_forall-r2.log
06f0e8377076c3a7024e22d56cf32d19c8a5afa5d8f4d4be57abb2028941c83d  verify-all/production/ic3syn-toy_consensus_forall-r3.log
22c6429bce538522f8ba94a31699e50f0037844d82563217a3eeeb6b6c86c2a5  verify-all/production/ic3syn-toy_consensus-r1.log
8503da406892d085d1055f7ad341fb62b5754a4c1283363325c5e46a0d0a6fd6  verify-all/production/ic3syn-toy_consensus-r2.log
75625ed6d74a14eda8174edc462addc9c7a3fb873129257b9e5ae2dfeb67b58f  verify-all/production/ic3syn-toy_consensus-r3.log
308a6ec59d3ab9c439c67adebb7303b80f070fdc4e00bb236430b17250216912  verify-all/production/ic3syn-two_phase_commit-r1.log
6fb21e2cda5514ffd06550508620dd342e0b1b60468598fec0e8263064a6eada  verify-all/production/ic3syn-two_phase_commit-r2.log
bcd817eeb3362016e2c16a6e60ccedf38f800b65e107cbdd81f54b281b438bcd  verify-all/production/ic3syn-two_phase_commit-r3.log
bc919438ece12e3f35f65d9f3bfdbf5c6ed05821d87f1429919236c5c1a21c25  verify-all/production/ic3syn-twophase-r1.log
fcd6a8af0c4b18a569c76049b7e546a7183f6e1f68c25402e6a236c6efde6a7f  verify-all/production/ic3syn-twophase-r2.log
53aac942d7974b933e4b8dde3406ce1d774de909487cc0db7bfd06b868c29a9d  verify-all/production/ic3syn-twophase-r3.log
```
