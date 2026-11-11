# Rolling integration — scoped entries only

## A: GREEN endpoint helper

Imported `core/count-tier-budget.ts` and its test **byte-for-byte from `620a3596`**, D's gate `12cfdab4`. The helper contains the exact-endpoint unknown handoff and retains proof/refutation results, the no-dispatch path, and the nonrenewable enclosing allowance.

This is the **helper dependency layer**, not a claim that the whole A generation pipeline is integrated: the current common `counts.ts` does not yet call it. The generation/strategy dispatcher dependency closure is requested from A. No A prover or kernel subtree is restored.

Own integration tests/type/roster gate pending. New I6/performance tests are explicitly scheduled alongside the helper test in the quick roster.

## B/F

No RED source is promoted as GREEN. D's `5b723d610` calls `8ad0072f` RED for integrated clock/reservation/default identity; `bd5af0b9a` calls the quorum follow-up mixed/leaf-cap RED; F `9a3e3792` is RED for the work-scope contract. Completed default diagnostics in `19f6c85bb` do not erase these findings. Waiting for the owners' actual GREEN closure/pins.

All entries remain descendants of `00b58ee5`; final integrated D gate and calibration are separate requirements.
