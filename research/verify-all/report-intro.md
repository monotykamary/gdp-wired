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
