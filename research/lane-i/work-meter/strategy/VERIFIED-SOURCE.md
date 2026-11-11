# Verified strategy-meter source — not admitted

- Commit: `cd00524f01093838e9584edc4a20f71e2be10e2a`
- Branch: `claude/lane-i-strategy-meter`
- Parents: mini pin `aeef60912e189573eb24e658af7e915109a971d2` and lane B `37d006af`.
- Tree: `6d1453342ca15df8bf948465c13cbf9a1aedf8a2`
- Patch from the mini pin: SHA-256 `74f306a9e4419a400db5372f6be56178e682fc8a2e2d4f8c2f41167f2b8f9a4a`, 1,728,833 bytes.
- Full phase artifact: SHA-256 `c303d8b9ab4ccc5d6ab3023c93a7d72f8a55fdd1e1f171494bb1714b2aa25983`.

`20261111-014057-0li8e1` passed the full composed typecheck, five selected test
files, and zero-warning lint on 1,853 files including the diagnostic fixtures.
All eight independently rebuilt source-part jobs passed. The materializer
checks every part against the tested tree/hash, decodes the complete event
records, rechecks the raw/phase partitions and fresh-process off/on equality,
and writes `runs/lane-i/strategy-source-materialized/`. A temporary git index
applied that patch to the mini pin and reproduced the exact tested tree before
the source commit was created. It did not switch or alter the active worktree.
A fresh `freeze.sh` input pack independently rebuilt the same tree and patch
hash in `20261111-014427-5foy9v`.

The checked row-strategy proof has 83 phase events, 166,615 table cells,
529 checker steps and 2,798 AST constructions. Off/on raw counters and verdicts
match. The separate ordinary sat/unsat and actual EPR sat/unsat fixtures have
nine events and 38 EPR counter increments; off/on results and counters match. These
are direct fixtures, not original MLDR/29-case qualification or calibration.

## Lane D reads

The source retains `core/work-ledger.ts` blob
`ed88401af1577ac0fc4e5cbb270ec305274ee3e0`. The existing mini CHILD needs no
ledger adapter. In the diagnostic `phase-data.json`, full `WorkPhase[]` values
are at `results.find(r => r.on).events` and `paths.find(r => r.on).events`.
Do not fit from these Linux diagnostic wall times. Re-freezing the mini source
and setting `GDP_COUNT_STRATEGIES=1` in both calibration and confirmation are
explicit coordinator/lane-D choices, not changes made by this lane.

The shared composer is instrumented. Lane F's later prototype is not claimed
to be included or verified by this source. Full F3, exact native-operation
attribution, original-protocol strategy coverage, calibrated W and the 35%
strategy share remain open. Nine generated trailing-space warnings were
reported while applying the exact tested patch; the frozen tree was not
silently reformatted after validation.
