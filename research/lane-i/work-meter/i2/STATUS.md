# I2 evaluation slice — verified, isolated, not integrated

Tree: `643027db476e00ba3b9b95c79ad49a6f034012de`, on `b11e1f65`.
The four-file change is on `claude/lane-i-i2-evaluation`. Neither the pending
generator nor Lane A's broader A2 stack is included. When combining with A2,
preserve its `traceNow` import/debug call and every A1/A2 roster entry; the new
roster entry is only `core/meter.test.ts`.

This first slice adds raw `evals` for interpreter and compiled closures,
static expression-node charges per compiled step, and raw ticks for the
existing compiled derived-count callback. It does not change `fullWork`,
any clock decision, weights, W, deterministic caps or acceptance logic.

Validation `20261110-110749-tb8ue2`: all 35 selected tests passed, including
six new tests for values, short circuits, failed work, wrapper/fallback
double-counting, fixed compiled-step charges and refused compiled steps.
Existing compile fuzz, runtime/sample tests, roster and type/lint pass.
Independent source/stream audit and commitlint `20261110-111125-zilynh` pass.

The first run `20261110-110552-sehbz2` is retained: 33 passed, two invalid new
fixtures failed. One used an unsupported directly-bound key comparison;
one wrote an undeclared state variable so `fastStep` correctly declined it.
Only those fixtures were repaired; the evaluation implementation did not change.

Still missing: substitution/construction, finite binding visits, model
instances, cube tests, other private ticks, direct recurrence evaluation,
and per-binding work inside compiled dynamic loops. This is not complete
accounting, an F1/F2 result, or a fix of the zero-unit work-mode gap until all
raw terms are complete and Lane D chooses their weights. This candidate
has not passed the full protocol census or paired integration checks.
