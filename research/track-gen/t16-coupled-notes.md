# T16 coupled finite-map seed moves

## Hypothesis and fixed falsifier

A radius-one seed move cannot cross a guard requiring multiple cells to change
together. The checked seed pilot caught only 3/2/3 original named drops; two
runs reported a non-named new law, and one exceeded 2 seconds. It fails the same
five-of-seven bar. Independent replay confirmed all 22 witnesses; no rerun can
erase that result.

Try setting all modeled cells of one map to a common already-admitted value.
This is a generic finite-map move, not a protocol/name-specific rewrite. Input
and state maps remain separate. This can cross aggregate guards that cannot be
crossed by a single coordinate change. It must improve the same full-family
pilot to five named drops within 2 seconds; otherwise reject it too.

## Unchanged safety and bounds

The feature is separately opt-in (`seedUniformMaps`) under `seedTransitions`.
Group slots only by map identity and whether they are request/state slots. For
each group, use values present in every member's existing finite domain. Do not
add keys, widen values or inspect law names. Try these moves after seed bases
but before individual axes. Duplicate vectors consume no extra attempt.

All moves share the existing maximum 256 unique attempts from at most eight
seed projections. There is no separate coupled allowance, extra wall, or new
certification path. Ordinary global enumeration remains afterward. Callers,
full predecessor family, declarations and the actual source step still govern
every removal through the unchanged independent callback. Intervals stay off.

## Validation and diagnosis

Add complete binary/ternary state-map and carried-input-map comparisons against
the interpreter, cases where only a coupled seed reaches the failing aggregate,
unchanged seed objects, and caller/impossible-fact barriers. Retain all previous
71 tests and all static checks. The new overlay's validation is pending.

A separate diagnostic of the *previous* seed implementation moves only the
onTiny observation before its final completion-wall check, to expose counters
from interrupted passes. It is not a qualifying timing run and changes no
production file. Independent replay also remains separate from this experiment.
