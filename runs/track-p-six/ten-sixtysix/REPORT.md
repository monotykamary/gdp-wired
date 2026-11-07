# Track P — original STEP evidence for C10 and C66

## Verified certificates

All original machine guards and family19 scalar assumptions remain intact. Fixture SHA256: `ee4bee5547e52dc7222e210f1a188e9adb1b81fe542eb01396cacba26e7007f1`. Family indices: `[2,3,4,7,9,10,11,13,14,17,33,45,61,64,66,70,71,73,74]`.

| Target | Raw / encoded hypotheses | Necessary instantiated PRE tuples | Necessary CountInst signatures | Fresh source-bound check |
|---|---:|---|---|---|
| C10 | 17 / 23 | C10[a$c#, b$c] | `+members$Decision[k] -members$Decision#[k]`, unit0; `+members[0] -missing[0] -members$Decision#[k]`, unit0; both below size; k=64*a$c#+b$c | checkMC=true; raw, decls, gg and fixture hash match; searchCalls=0 |
| C66 | 18 / 18 | C45[w,maxr,v]; C3[64*maxr+v] | Empty: no reads, instances or picks | checkMC=true; raw, decls, gg and fixture hash match; searchCalls=0 |

Each target has `cN/{goal,proof,source,check}.json`. Goal schema is `{scope,raw,decls,gg}`; proof is a CountCert including checked tree; source records exact Instances, target and family indices. Check receipts come from a fresh boat process, not the proof-producing process. `check-v1/recheck.log` contains both.

`hand-v2/c10.log` records successful deletion-minimization tests: deleting the sole PRE tuple or either count instance yields an abstract SAT result. `hand-v2/c66.log` removes C3[64*pmaxr+pv] successfully, while removing C45 or C3[64*maxr+v] yields abstract SAT. These SAT results characterize incomplete requests, NOT reachable protocol counterexamples. No assertion of global minimality beyond these deletion tests.

## Generic emission audit

Engine source at audit: `core/count-support.ts` SHA256 `ad4fe53e10f783a7e7b095eb3170203a5e5d83e1b239e4c39c47f2bae7850e5f`.

Full machine-readable files: `c10-all-audit.json`, `c10-none-audit.json`, `c66-all-audit.json`, `c66-none-audit.json`. Each contains actual generic prepare/pool-selection/current-selected closure and a fixed-hand-cert closure control. Every phase has EVERY extra PRE tuple, missing tuples, selected read/witness mappings and count-instance differences. Selected fresh witnesses are normalized by semantic instId. `report-v1/report.log` groups every phase's extras by original law index and expands all actual count signatures. Round labels are zero-based; `prepare` precedes closure:0.

| Target / initial flags / selector | Missing or late required PRE | Necessary count signatures | Final extra PRE / count instances | Final focused proof |
|---|---|---|---:|---|
| C10 / all / actual | C10 root present in prepare; none missing | Both selected at closure:0. Ternary LOST at closure:1 when shared work reaches65536; not an initial absence | 62 / 9 | abstract SAT,96hyps |
| C10 / none / actual | Root present in prepare | Both selected at closure:0 and retained through closure:2 | 28 / 0 | tree, checkMC=true,54hyps |
| C10 / all / hand | Root present in prepare | Both fixed and retained | 64 / 0 | tree, checkMC=true,87hyps |
| C10 / none / hand | Root present in prepare | Both fixed and retained | 28 / 0 | tree, checkMC=true,51hyps |
| C66 / all / actual | C45[w,maxr,v] and C3[64*maxr+v] never emitted, prepare through closure:1 | Empty needed; 10 extra meets at closure:0; exhausted reselection emits zero at closure:1 | 60 / 0 final (10 earlier) | abstract SAT,82hyps |
| C66 / none / actual | Both never emitted, prepare through closure:1 | 10 extra meets retained | 36 / 10 | abstract SAT,68hyps |
| C66 / all / hand-empty | Both never emitted, prepare through closure:2 | Empty fixed | 41 / 0 | abstract SAT,57hyps |
| C66 / none / hand-empty | Both never emitted, prepare through closure:2 | Empty fixed | 17 / 0 | abstract SAT,33hyps |

Shared candidate budget remains65536 throughout. C66 fixed-empty controls finish without exhaustion (61442 with all flags,46677 without), localizing the remaining blocker to source generation, not just work or selector pressure. C10 no-flags actual reaches65536 yet its final goal checks; reaching a resource cap is not itself evidence the goal cannot be proven. These emitter-only traces do not perform model-guided production refinement.

### Final extra PRE groups

Entries are `original law index: tuple count`; `flags4xN` means N for EACH of ?noProposal, ?joined, ?rowOk, ?all$1.

- C10 actual/all (62): `4:3,7:4,9:1,11:4,14:4,17:4,33:2,45:4,61:1,70:2,74:1,flags4x8`.
- C10 actual/none (28): `4:3,7:4,9:1,11:4,14:3,17:4,33:2,45:4,61:1,74:2`.
- C10 hand/all (64): actual/all with `74:3` instead of1.
- C10 hand/none (28): same counts as actual/none.
- C66 actual/all (60): `2:4,4:4,7:4,9:1,10:2,11:4,14:4,17:3,33:1,45:4,61:1,74:4,flags4x6`.
- C66 actual/none (36): same non-flag counts as actual/all.
- C66 hand/all (41): `7:4,9:1,10:3,11:4,17:3,33:1,61:1,flags4x6`.
- C66 hand/none (17): same non-flag counts as hand/all.

C10 final unwanted count signatures: five pair differences `+X -members$Decision#[k]`, unit0, for X in missing[0], members[0], members$Qs[0], can$Vote$members[64*r+v], can$Vote$members[k]; four meets `+missing[0] +Y`, unit-1, for Y in members[0], members$Qs[0], members$Decision[k], can$Vote$members[64*r+v]. All below size.

C66 unwanted meets: all ten unordered pairs among the six reads members[0], members$Qs[0], members$Decision[64*pmaxr+pv], members$Decision[64*pr+pv], can$Vote$members[64*pr+pv], can$Vote$members[64*pmaxr+pv] in the selector's first-ten ordering; exact ten pair list/read mapping is in each actual closure:0 trace and `report-v1/report.log` (not all fifteen possible pairs are selected). All have +1,+1, unit-1, below size.

## Exact C66 source and safe generic mechanism

Original free PRE read is at `m.step.flags.proposes.xs[4].xs[1].xs[2].a`: `Vote[4096*w+64*maxr+v]`. This is a nonquantified transition flag definition, in the non-none-maxr branch of proposes. Bound locals are empty; w, maxr, v are machine inputs. It is not a read bound by a count or quantifier.

A safe candidate annotation is `{kind:'transition-pre-read', path:['step','flags','proposes','xs',4,'xs',1,'xs',2,'a'], boundLocals:[], freeNames:['w','maxr','v']}`. Complete `matchRead` against C45's Vote pattern binds all three coordinates to `[w,maxr,v]`; full key reconstruction equals the actual key. Instantiating FULL C45 preserves every guard and exposes its PRE `Proposal[64*maxr+v]`. Ordinary all-read range closure then instantiates FULL C3 at that exact key. No projected-coordinate equality, new axiom or guard deletion is needed. The emitter-only next-hypothesis test is verified in `source-probe/source-probe.log`.

Current completeReadMatches accepts root-bound primitive reads and selected count-witness reads, but scalar C66 has no root binders. Fallback scoring rejects the otherwise complete transition-guard tuple: it mentions neither a target root variable nor own-write variables and is not a selected witness. Thus broad initial flags plus unrelated count-law roots cause excess work, AND transition-local complete-read closure is missing. A general repair should retain checked live count signatures across exhausted selection; prioritize complete transition and premise-read matches; delay speculative cold/count roots; avoid all-input quantified-flag seeding; and try an empty count tier for primitive obligations before escalating to relevant transition counts. Empty counts alone cannot fix C66 without the missing primitive tuple generation. C7 remains a reason not to assume all count-free targets need no count reasoning.

Main's full-run timing evidence (not measured here) says SAT/admission dominates: tree1.379s, unknown7.347s, SAT47.516s, outsidequeries33.086s. These results motivate reducing irrelevant source/admission work rather than optimizing failed-grow time alone.

## Execution and limitations

All substantive inspection, proof searches, source probes and audits ran through supercomputer on existing warm boat VMs, `--vm-type large`; no timing/benchmark claims. Proof requests each use1500 counted ms and2500 wall ms, unchanged. All submitted tasks completed, no process left to stop; no engine/kernel/model changes, no commit, no NEXT.md changes.

`hand-v2/summary.tsv`: both jobs exit0. `audit-v1/summary.tsv`: all4 jobs exit0, with proof statuses reported above rather than inferred from job exit. `check-v1/summary.tsv`: zero-search replay exit0; optional helper dependency-graph typecheck exit2 due existing imported core TypeScript errors, with no diagnostic in audit-support.ts itself (`audit-types.log`). `report-v1/summary.tsv` and `source-probe/summary.tsv`: exit0. The original hand-v1 log was truncated at the runner's400k log ceiling; compact complete artifacts and minimization receipts are retained in hand-v2, so hand-v1 is not the evidence source.
