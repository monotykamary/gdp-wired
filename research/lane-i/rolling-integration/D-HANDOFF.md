# Combined lane I handoff — final admission pending

Final static source: `b520b2855464c5bf91fea98c4dc0149d4b3deb1c`; native test/evidence source: `ab9f33a6599f88f0a17214d2b95682af5cca0c6d`. Their production subtrees are identical. Both descend from `00b58ee54b4e5b8c4967fdbde35d1ff0f38d91e7`.

## Narrow production layers

1. `2eec34ce`: admission-sum specialization; no removed admission, batching, clock/scope or price change. Native evidence source `3d0256f0`.
2. `3281eb7f`: three observation writers at actual work sites; evidence source `1066f267`. Only `core/check.ts` and `kernel/kernel.ts` differ among the protected identities, and AST erasure recovers their former algorithms. `core/infer.ts` receives only observation calls; no inference route change.
3. `320092ba`: exact A `620a3596` endpoint helper and test (D gate `12cfdab4`). This helper is not yet called by `counts.ts`: it is a dependency integration, not a claim that A's generation dispatcher is on the line.
4. `f7edaefb`: only the explicit test roster; catches five inherited omitted tests. No production algorithm change.

`production.patch` is the combined seven-file runtime diff against `00b58ee5`, excluding tests/docs/evidence. Separate I6-only minimal diff remains `../i6/counter-only.patch`. `kernel/prove.ts`, Lean subtrees and the other 132 protected files remain unchanged; the gate independently verifies identities and the old prover body.

## Evidence

- Admission: `../admission-perf/RESULT.md` — native 16.44x / 24.95x wall improvement at identical units and native results. Not a whole-engine or current-final-source fit.
- Observation: `../i6/STATUS.md` — 121 tests / 1,356 assertions and full static. 28 strict / 28 off receipts complete; zero forbidden reads and exact flags-off behavior.
- Causality: `../i6/CAUSAL.md` — ten same-source on/off/lifted/shadow controls, exact census reproduction and old-vector shadow equality. Accounting/local shares explain the two changed bounded verdicts; no persistent proof failure found. No quota/weight retuning.
- Closing checks: `../i6/TAIL-REPLAY.md` — four exact B9 packets, 16 positive checks and 16 negative controls, 23 other columns exact; newly observed 78–79M STEP units.
- Helper gate: `STATUS.md` and `results/` — 144 tests / 1,900 assertions, exact A blobs, corrected roster/static.
- Final all-tooling gate: 144 tests / 1,900 assertions plus complete roster pass on `ab9f33a6`; type/lint passes across 1,801 files on `b520b285`, batch `20261111-044310-9oek2z`; all 13 new commit messages pass commitlint. The only follow-ups are a missing-receipt guard and an explicitly unused diagnostic destructuring name. Production subtrees are unchanged. Initial failures are retained; final receipts are in `results/final/`.

## Explicit nonclaims / remaining gates

I6 is observation-gated, not accepted as a calibrated hard-cap source. `sharded_kv` exceeds the previous 1,024-unit slack at 15,120,328.2561; two 15M results change for the documented accounting reason. A full generation/strategy dependency closure and B/F GREEN payloads still need their owners' scoped gates before integration. No old `00b58ee5` fit transfers to this runtime. No final W, original-family MLDR success, main merge or push is claimed.
