# Section 18 — per-lemma recapture and once-per-law accounting

Research implementation: **d42c7034**. No production source, kernel, generator, allowance, local draw, or proof policy was changed. This is a measurement, not a cache implementation or a complete-law proof.

## Answer and scope

For the **captured prefixes** of Inv2973 ops 0/4 and Inv* ops 3/5, proving each unconditioned law-root fact once leaves **1,322.193** and **1,900.155** counted units respectively. The latter saves only **7.872** units from the measured trace; **4.557** of that is repeated work within an op and **3.315** is the additional benefit of sharing between ops.

This is not a whole-law total. The production **5,000-unit allowance**, local ceilings/draws and **4.8-second cooperative law clock** were retained. The clock stopped these runs before the allowance was exhausted. No unobserved work in other ops is estimated. No new policy, imported seed, T-12 flag or pooled budget was enabled. The original generated-law harness still does not generate these two published laws; these are the existing explicit-family packets, not a generator gate.

All eight control/observed searches returned **unknown**. They ran sequentially on one exclusive large VM, eight pinned vCPUs, AMD EPYC 4585PX (`bx_395wpmqp`). Controls preserve the same search policy with observation off. The observer changes wall overhead and therefore the prefixes selected by the cooperative clock; controls do **not** establish identical traces or a speedup.

## Captured work

`Checked` below means the emitted lemma's transported proof was independently checked in its target context, with conditional-proof metadata restored. `Root` means a certificate also checks at the original law root with **no chosen op or guard path**. A literal mention of a guard is not by itself a failure: e.g. a Boolean range can be valid at the root.

| Law / op | Search units | Search s | Field helper units | Frame helper units | Attempts | Emitted | Checked | Root instances |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Inv2973 / 0 | 778.620 | 6.323 | 0 | 778.533 | 9 | 3 | 3 | 0 |
| Inv2973 / 4 | 543.573 | 4.935 | 0 | 543.282 | 23 | 9 | 9 | 0 |
| Inv* / 3 | 869.274 | 4.951 | 750.837 | 118.400 | 72 | 30 | 30 | 28 |
| Inv* / 5 | 1,038.753 | 4.855 | 832.711 | 205.800 | 54 | 29 | 23 | 13 |

The zero field-helper columns for Inv2973 mean **not reached before the clock**, not that the law needs no field lemmas. These are not directly comparable to T-12's different flags and longer-clock diagnostic totals. The 4.8-second clock is cooperative: an in-progress helper can overrun it; the maximum observed search wall was 6.323 s (control: 6.666 s).

Control units / search seconds were: Inv2973 op 0 **659.517 / 6.666**, op 4 **545.998 / 5.034**; Inv* op 3 **922.144 / 4.927**, op 5 **1,081.788 / 4.963**. Input loading and post-search auditing are not included in these search intervals.

### Cost categories, without assigning the whole helper to a lemma

| Law / op | Other helper work | Per-attempt setup | Failed source calls | Successful source calls | Check | Transport |
|---|---:|---:|---:|---:|---:|---:|
| Inv2973 / 0 | 564.721 | 0.000 | 120.598 | 93.214 | 0 | 0 |
| Inv2973 / 4 | 70.447 | 0.000 | 271.375 | 201.460 | 0 | 0 |
| Inv* / 3 | 12.164 | 28.478 | 771.797 | 56.798 | 0 | 0 |
| Inv* / 5 | 288.212 | 0.443 | 565.298 | 184.559 | 0 | 0 |

The per-attempt buckets are exclusive counted work; nested frames are subtracted. `Other helper work` is explicitly **not** all labelled setup: it includes selection/preparation and any whole-goal or other work outside a named lemma attempt. Source categories describe returned instrumented calls; a composite call's internal work stays with that call. Nothing outside a named attempt is credited as reusable lemma work.

The current counter does not charge these kernel checks/transports. A zero is **not** a claim of zero CPU time. Separate post-search audit wall was 6.137 / 5.162 / 3.126 / 1.904 s for the four observed rows. It is excluded from search and reuse savings. Nested frame accounting, per-attempt totals, whole-helper totals and residual outside-helper work reconcile independently.

## Statements and dependencies

[lemmas.csv](lemmas.csv) contains **all 158 attempts**, with op, helper, stage/kind, normalized read-expanded statement, literal and proof-dependence flags, source/target checked status, root status and each cost bucket. It therefore includes every emitted lemma and preserves failures instead of dropping them.

[overview.json](overview.json) gives a small readable index and zero-free linear displays. The full audit in [receipts.br](receipts.br) additionally contains source and target premise indices/normalized statements, required path atoms, root premise slices and certificates. Original source/target trees, shared goals, full column registries, conditional-proof marks and path scopes are in the [raw capture](../section18-lemmas-v5/receipts.tar.gz).

Normalization expands allocated read names to map/key reads, preserves free keys (`a$#` is not renamed), retains pre/post map identity and resolves column terms. Comparison keys additionally collect integer-linear terms, remove zero coefficients, normalize strict integer bounds and common positive factors. Thus `i < size` and `i + 1 - size <= 0` are one statement. Original proof goals are **never** rewritten by this comparison normalization.

`literal_*` answers what a statement mentions. `proof_*` answers what its used source **and transported target** premises/path atoms mention. These are conservative syntactic footprints, not claims that every mentioned expression is semantically necessary. `op_independent_root` requires a successfully checked certificate under the unspecialized law root, not just an innocent-looking formula. The initial `root_checked`/`reusable` fields preserve the stricter guard-free, pre-state pass; the broader root field is the final sharing criterion. Root-premise footprints are retained even when they mention the transition relation or post-state.

### Checked overlap

There are **16 distinct checked statements shared by multiple op/law rows**:

* Inv2973 ops 0/4 share **three**: `cfgSize#[a$#] <= cfgSize[a$#]`, `cfgSize#[b$] <= cfgSize[b$]`, and `old#[a$#] <= old[a$#]`. None obtained an unconditioned root certificate.
* Inv* ops 3/5 share **13**: the eight partition/equality directions below; `?canVote <= 1`; `i < size`; `j$ < size`; `bq#[64*a$#+j$] <= bq[64*a$#+j$]`; and `cfgSize[a$#] <= cfgSize#[a$#]`.
* Exactly **one** statement overlaps the two laws: `cfgSize[a$#] <= cfgSize#[a$#]` (Inv2973 op 4; Inv* ops 3/5). It is a post-state frame, and no law-root certificate was obtained. **No cross-law cache saving is credited.**

### The 12 reusable law-root facts, all in Inv*

Paired inequality directions are separately checked facts. These are **law-root-scoped facts**, not universal set identities without premises.

| Statement | Root-checked instances | Ops | Total successful source units |
|---|---:|---|---:|
| `cfgSize[i] <= xAndS[0] + xNotS[0]` | 4 | 3, 5 | 0.187993 |
| `xAndS[0] + xNotS[0] <= cfgSize[i]` | 4 | 3, 5 | 0.174316 |
| `inX[0] <= xAndS[0] + xNotS[0]` | 4 | 3, 5 | 0.187993 |
| `xAndS[0] + xNotS[0] <= inX[0]` | 4 | 3, 5 | 0.174316 |
| `inS[0] <= sNotX[0] + xAndS[0]` | 4 | 3, 5 | 0.123541 |
| `sNotX[0] + xAndS[0] <= inS[0]` | 4 | 3, 5 | 0.110306 |
| `inX[0] <= cfgSize[i]` | 4 | 3, 5 | 4.292504 |
| `cfgSize[i] <= inX[0]` | 4 | 3, 5 | 4.292504 |
| `?canVote <= 1` | 2 | 3, 5 | 0.098295 |
| `?committedQuorum <= 1` | 1 | 3 | 0.044744 |
| `i < size` | 3 | 3, 5 | 0.151993 |
| `j$ < size` | 3 | 3, 5 | 0.160111 |

That is **41 instances / 12 facts**, with 11 facts shared across the two ops. The first eight are the stricter guard-free pre-state subset: 32 instances / eight facts. The two Boolean bounds mention guards; the index-bound root proofs mention transition/guard or post-state premises, but do not assume a selected op/path. Their certificates, not their literal spelling, establish reuse at this law root.

Six deferred emissions in Inv* op 5 have valid source proofs but **fail the transported target check**. They remain visible with both statuses, receive no proved-instance credit and are not proof successes. A root fact established by some other checked instance may still eliminate a matching failed query in the explicitly more optimistic estimate below. No complete proof using these deferred emissions was accepted.

## Once-per-law counterfactual

Within each law and identical normalized root context, retain the first root-checked proof of a comparison key. Subtract only subsequent successful source/check work, add the first measured root-admission cost, and retain setup, failed calls, transport, other-helper and outside-helper work.

| Covered law / ops | Observed prefix units | Facts / instances | Duplicate instances | Saved successful work | Units remaining |
|---|---:|---:|---:|---:|---:|
| Inv2973 / 0, 4 | 1,322.193011 | 0 / 0 | 0 | 0 | **1,322.193011** |
| Inv* / 3, 5 | 1,908.026739 | 12 / 41 | 29 | 7.871612 | **1,900.155126** |

For Inv*, removing repeats **within each op** first leaves **1,903.469968** units (4.556771 saved). Moving from once-per-op to once-per-law saves a further **3.314841** units. The first root-admission costs are zero under this counted-work model; the certificates were nevertheless replayed and checked.

Restricting reuse to the eight guard-free pre-state facts leaves **1,900.441084** (7.585654 saved). The final broader result is slightly better, not a different measured run.

A second, explicitly more optimistic fixed-trace calculation also removes all source/failed/check calls with a key whose unconditioned root fact has been established, while retaining the first proof and all setup/transport/other work. It leaves **1,824.481016** units for Inv* (83.545722 saved) and **1,322.193011** for Inv2973. This is a bookkeeping estimate, **not an executed cache**, a wall-speed prediction or a bound on a changed search trajectory. Failed work unrelated to a root-proved fact is never deleted.

## Provenance, validation and recovery

* Primary capture: [section18-lemmas-v5](../section18-lemmas-v5/), exclusive placement recorded there. Both 5,000-unit allowance and production local clocks/draws remained active.
* Final independent audit: [section18-audit-v5/audit.log](../section18-audit-v5/audit.log). Source, target and existing root outcomes replay; used premises are recomputed from proof leaves/products and implicit path/conditional-cut use. Additional root admission is exact certificate transport/checking, not new proof search. There are 187 explicitly recorded verification calls, including three added root certificates; no extra column identifiers were needed.
* Typecheck and lint pass. **5 tests / 16 assertions** pass, including allocation-independent reads, preserved quantified/post-state distinctions, integer-bound canonicalization and disabled-observer behavior.
* Primary V5's legacy all-in-memory archive wrapper ran out of memory **after all eight searches completed**. The same retained outputs were recovered with streaming tar/gzip and checksum-verified. No measured search was restarted to replace this failure. The nonzero batch exit remains in its log/summary; it is not silently relabelled successful.
* Earlier preflights/pilot and audit revisions are not additional trials in the results. Audit revisions improved premise extraction and comparison normalization on the same immutable capture.
* Raw capture SHA-256: `a49b9b46756a7273730630fcd172fc1422cfd035d7f700a12c93f3c213f04101`.
* Full final audit SHA-256: `1988f44e2580eac5bbc9d4c8bebcd725bf443495dbe0a3f5bd8ff7f1a10c1487`.
* [cleanup.json](cleanup.json) records cleanup outcomes. No measured/audit job remains running; scheduler-owned VMs are not stopped or resumed merely to remove files from an already-stopped staging VM.

Re-run the independent audit (no original-packet reconstruction needed):

```sh
supercomputer run --jobs research/track-m/jobs-section18-audit.json \
  --out runs/track-m/section18-audit-replay --class submission --vms 1 --max-vms 1 \
  --data runs/track-m/section18-lemmas-v5:lemma-input
```

The compact audit archive contains the full expanded inventory/premises; to inspect it locally without fetching a VM:

```sh
bun -e 'import {brotliDecompressSync} from "node:zlib"; const f=JSON.parse(brotliDecompressSync(await Bun.file("runs/track-m/lemma-recapture-v1/receipts.br").arrayBuffer()).toString()); await Bun.write("lemma-details.json",f["summary.json"]);'
```

Production and the kernel are unchanged; **28/29 was not rerun or re-certified by this research measurement**. No gate pass, complete-law proof or full-law cost estimate is claimed.
