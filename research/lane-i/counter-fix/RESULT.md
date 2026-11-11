# Integrated counter correction + hard cap — ready for D review

**Exact source:** `00b58ee54b4e5b8c4967fdbde35d1ff0f38d91e7`, on
`claude/mldr-integ`. D has pinned it for **PLUMBING ONLY**, not calibration or
source acceptance. Nothing merged to main or pushed.

## Implementation

`raw-work-v1` preserves the 20 named v0 columns and adds `tinyNodes`,
`tinyTerms`, `reachStates`, `reachEdges`, `reachEvals`, `reachCompiledEvals`.
[SCHEMA.md](SCHEMA.md) defines each primitive, the positive 14-extra-weight
vector, explicit old-vector rejection, and flags-off compatibility.

Tiny search now meters assignment branches and actual executed native
predicate/interval/term sites. Instrumentation is excluded from native
code-size limits. Reach buckets are exclusive: actual interpreted/closure
node visits differ from fastStep's static AST charge. Nothing is refunded.
New charges pre-admit; a closed tiny block may use only its finite admitted
tick bound. A refused endpoint cannot be reset by caught exceptions, nested
scopes, or block-credit reuse. Smaller child allowances do not poison parents.

**134 protected file/model identities and the prover body below its cancellation
header remain exact.** See [runtime.patch](runtime.patch) and [tests.patch](tests.patch).
All 13 original overruns, original file/line sites and units between checks
remain documented in [../hard-cap/LOOPS.md](../hard-cap/LOOPS.md).

## Exact-source validation — all on supercomputer

- **25 tests / 111 assertions passed**, including the checked pre-admission
  law and always-spend mutant, native pruning, nested refusal and restoration.
- TypeScript/type-aware lint: **1,783 files, zero errors or warnings**.
- **28 originals: 12 proved and checked, 16 unknown.** All prior 10 checked
  proofs retained; `client_server_ae` and `simple_election` newly checked.
- **Maximum: 15,000,385.9024 units** against 15M, within stated 1,024 slack.
- 28 strict runs: zero forbidden clock reads. All 26 raw keys and root/exclusive
  phase conservation audited; all 14 extra weights finite and positive.
- 28 flags-off runs: exact old 20-column/phase/event/query/result projection;
  all six new columns zero. Only provenance and independent wall telemetry
  excluded. The additive raw schema itself is not byte-identical to v0.
- Commitlint passed for source commits and the final evidence message.

## E1/E2 diagnostics — UNCALIBRATED

Fixed original 49-law fixture SHA-256:
`49a805953627fa2a5e55531f15c77147403cb86334e7054954a33a1c6cd5f190`.
Original model blob: `0541fa9436e307a6fb716aa5064637b30b893b79`.
Prior source `efd70276`; candidate `00b58ee5`. Same native drop/broken sets,
reported witness prefixes, and tiny statistics. Summed native nodes equal
raw tinyNodes. Fable's long witness logger truncates: **not full witness-byte
equality**. The boundary case is one round, not a complete fixpoint.

| Case | Prior units | Prior wall s | Candidate units | Candidate wall s | (units/250)/wall ms |
|---|---:|---:|---:|---:|---:|
| tiny-small | 66,287 | 3.309 | 179,836,710.74 | 12.165 | 59.131 |
| reach-finite | 249,229,203 | 17.020 | 5,246,726.06 | 235.197 | 0.089 |
| reach-compiled | 305,501,358 | 35.398 | 6,372,169.16 | 414.728 | 0.061 |
| tiny-boundary-round | 362,875 | 42.706 | 4,173,513,015.5 | 209.601 | 79.647 |

Small case: **1,088,594 nodes / 178,746,781 terms**, complete fixpoint.
Boundary round: **14,605,669 nodes / 4,158,893,243 terms**.
Pruned case at 15M: **14,999,999.1 units**, 30,472 nodes, 14,969,186 terms,
then `unknown: work budget (tinyTerms)` in 1.744 s.
The 28-original census does not invoke tiny search: its tiny columns are zero;
its four reach columns are all observed. Tiny coverage comes from E2, not a
false claim about the census.

Jobs were isolated `large`, no co-tenants. Native CPU identity is missing for
most rows: these are diagnostics, **not qualified calibration or precise
cross-hardware slowdown estimates**. The observed wall increase is material;
per-operation admission adds hot-path work. Neither that cost nor the severe
mismatch of provisional prices to wall time is hidden.

## Ranked remaining work

1. **D:** bind native+guest CPU model/boot identity, fit the successor vector,
   run 29 confirmations, and recheck the endpoint quantum under fitted weights.
   The old 1,024-unit provisional slack does not automatically survive fitting.
2. **I, with A for scopes:** quantify/optimize per-evaluation admission overhead
   if fit or finish-line throughput requires. Current tiny clock/wall is ~59–80,
   reach ~0.06–0.09. These priors are not calibrated W.
3. **A and F/B:** generation termination and transport/leaf proof work remain
   separate lanes. This counter correction is not an MLDR proof.

Guest qualification observed large Ryzen9 9950X, boot
`31a9a509-ebc0-4982-bda0-143ec46551b0`, and small Ryzen7 9700X, boot
`1d8479f9-f9ab-4e3a-9de3-31e40aa17826`. os.cpus/proc agree; qualification
placement CPU fields are empty. D received exact VM IDs and receipts and now
requires small+9700X for its third repeat. Guest evidence alone is not native
qualification. All evidence and rejected pilot controls are under [results/](results/).
