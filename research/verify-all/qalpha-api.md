# QAlpha semantic bridge

`lean-kernel/QAlpha.lean` imports `CountMachine` and changes no checker rules.
All names below are in `Kern.QAlpha`.

* `Rename := { flag : Nat, old : Nat, fresh : Nat }`.
* `rename s r` changes only `s.qflags`: for matching flag IDs it maps every occurrence of `old` in the binder list to `fresh` and substitutes `[(old, E.var fresh)]` in the quantifier-free body.
* `valid s r` checks each affected flag: old is bound, fresh is not bound, fresh does not occur in the body. Nonmatching flags are unchanged; a nonexistent flag is a valid no-op. Duplicate binder names are permitted and all occurrences are renamed together. No global freshness restriction is needed: other flag bodies and all scalar/witness metadata are unchanged.
* `renameAll s rs` applies renames left-to-right. `validAll s rs` checks freshness against the machine at each step, not merely the initial machine.
* `renameAll_equiv s rs hv` proves semantic `Equiv (renameAll s rs) s`. Its methods are `flags X N`, `view rho iota M kappa`, `next rho iota M kappa`, `sreach rho M`, and `creach ds rho M`.

Exporter entry point:

```lean
QAlpha.cmachine_sound original renames decls proof valid checked
```

Here `valid : QAlpha.validAll original renames = true` (normally `by decide`) and `checked : checkCMachine (QAlpha.renameAll original renames) decls proof = true`. The result has exactly the original `Kern.cmachine_sound` conclusion for `CReach original decls`, not normalized-machine reachability. `QAlpha.smachine_sound original renames proof valid checked` is the corresponding set-machine wrapper.

The transform does **not** promise that checker acceptance is preserved or that arbitrary packets become accepted. It proves semantic equivalence independently of acceptance; the exporter must still kernel-check the unmodified proof packet on the normalized machine. `wits`, flags, scalar fields, declarations and proof entries must not be rewritten by this bridge.

Test job: `research/verify-all/qalpha-check.jobs.json`. Positive/negative reduction and universal axiom tests: `research/verify-all/qalpha-tests.lean`.
