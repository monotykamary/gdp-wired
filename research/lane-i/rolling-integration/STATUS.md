# Rolling integration — scoped entries only

## A: GREEN endpoint helper

Imported `core/count-tier-budget.ts` and its test **byte-for-byte from `620a3596`**, D's gate `12cfdab4`. The helper contains the exact-endpoint unknown handoff and retains proof/refutation results, the no-dispatch path, and the nonrenewable enclosing allowance.

This is the **helper dependency layer**, not a claim that the whole A generation pipeline is integrated: the current common `counts.ts` does not yet call it. The generation/strategy dispatcher dependency closure is requested from A. No A prover or kernel subtree is restored.

Own native gate: 144 tests / 1,900 assertions passed at `320092ba` (batch `20261111-043133-w0ds1q`), and type/lint passed across 1,796 files. The roster guard then exposed five inherited omitted tests; `f7edaefb` registers those without changing their contents. Roster plus type/lint rerun passes at `f7edaefb`, batch `20261111-043335-0tudck`; AST erasure and the other 132 identities/prover body remain exact. Receipts are under `results/`. This is a local helper-layer integration gate, not D approval of the full composition.

## Combined final gate

Native tests on `ab9f33a6`: **144 pass / 1,900 assertions**, complete roster. Final type/lint on `b520b285`: **1,801 files**, zero errors/warnings; all 13 new commit messages pass commitlint. Batch `20261111-044310-9oek2z`. Only research-parser narrowing and an unused-name annotation changed after the test pin; production subtrees remain byte-identical. Initial type/lint failures are retained in `results/final-initial` and `results/final-typed`; successful final receipts are in `results/final`.

The combined production patch SHA-256 is `ed571c09694e8c5acc5e43856790da3b488e8d6d3a6d0a851b27737e5bac987b`. See `D-HANDOFF.md`.

## B/F

No RED source is promoted as GREEN. D's `5b723d610` calls `8ad0072f` RED for integrated clock/reservation/default identity; `bd5af0b9a` calls the quorum follow-up mixed/leaf-cap RED; F `9a3e3792` is RED for the work-scope contract. Completed default diagnostics in `19f6c85bb` do not erase these findings. Waiting for the owners' actual GREEN closure/pins.

All entries remain descendants of `00b58ee5`; final integrated D gate and calibration are separate requirements.
