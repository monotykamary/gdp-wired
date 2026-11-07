# Index 7: original family19 STEP

Hand certificate: 12 PRE tuples, 4 CountInst entries. No original guards or global assumptions removed. Fresh check receipt: zero-search.json.

## Required PRE tuples

### generic-all

- L7 (key$2#, key$3, key$4, key$5): **prepare**
- L10 (key$2#, key$3): **prepare**
- L10 (key$4, key$5): **prepare**
- L17 (key$2#, key$3): **prepare**
- L17 (key$4, key$5): **prepare**
- L11 (key$2#, key$3, r, v): **prepare**
- L11 (key$4, key$5, r, v): **prepare**
- L11 (r, v, key$2#, key$3): **prepare**
- L11 (r, v, key$4, key$5): **prepare**
- L33 (key$2#, key$3, v): **prepare**
- L33 (key$4, key$5, v): **prepare**
- L45 (wNew, r, v): **MISSING**

Phases: prepare: 55 emitted/1 missing/44 extra; closure:0: 75 emitted/1 missing/64 extra. Work 65536.

Missing hand count signatures: 4; extra selected count signatures: 10. Every extra PRE tuple appears in generic-all.json trace[].extras, with its exact phase and AST.

### generic-none

- L7 (key$2#, key$3, key$4, key$5): **prepare**
- L10 (key$2#, key$3): **prepare**
- L10 (key$4, key$5): **prepare**
- L17 (key$2#, key$3): **prepare**
- L17 (key$4, key$5): **prepare**
- L11 (key$2#, key$3, r, v): **prepare**
- L11 (key$4, key$5, r, v): **prepare**
- L11 (r, v, key$2#, key$3): **prepare**
- L11 (r, v, key$4, key$5): **prepare**
- L33 (key$2#, key$3, v): **prepare**
- L33 (key$4, key$5, v): **prepare**
- L45 (wNew, r, v): **MISSING**

Phases: prepare: 15 emitted/1 missing/4 extra; closure:0: 35 emitted/1 missing/24 extra; closure:1: 38 emitted/1 missing/27 extra; closure:2: 38 emitted/1 missing/27 extra. Work 65536.

Missing hand count signatures: 4; extra selected count signatures: 10. Every extra PRE tuple appears in generic-none.json trace[].extras, with its exact phase and AST.

### hand-closure-all

- L7 (key$2#, key$3, key$4, key$5): **prepare**
- L10 (key$2#, key$3): **prepare**
- L10 (key$4, key$5): **prepare**
- L17 (key$2#, key$3): **prepare**
- L17 (key$4, key$5): **prepare**
- L11 (key$2#, key$3, r, v): **prepare**
- L11 (key$4, key$5, r, v): **prepare**
- L11 (r, v, key$2#, key$3): **prepare**
- L11 (r, v, key$4, key$5): **prepare**
- L33 (key$2#, key$3, v): **prepare**
- L33 (key$4, key$5, v): **prepare**
- L45 (wNew, r, v): **closure:0**

Phases: prepare: 55 emitted/1 missing/44 extra; closure:0: 77 emitted/0 missing/65 extra; closure:1: 81 emitted/0 missing/69 extra; closure:2: 81 emitted/0 missing/69 extra. Work 65536.

Missing hand count signatures: 0; extra selected count signatures: 0. Every extra PRE tuple appears in hand-closure-all.json trace[].extras, with its exact phase and AST.

### hand-closure-none

- L7 (key$2#, key$3, key$4, key$5): **prepare**
- L10 (key$2#, key$3): **prepare**
- L10 (key$4, key$5): **prepare**
- L17 (key$2#, key$3): **prepare**
- L17 (key$4, key$5): **prepare**
- L11 (key$2#, key$3, r, v): **prepare**
- L11 (key$4, key$5, r, v): **prepare**
- L11 (r, v, key$2#, key$3): **prepare**
- L11 (r, v, key$4, key$5): **prepare**
- L33 (key$2#, key$3, v): **prepare**
- L33 (key$4, key$5, v): **prepare**
- L45 (wNew, r, v): **closure:0**

Phases: prepare: 15 emitted/1 missing/4 extra; closure:0: 33 emitted/0 missing/21 extra; closure:1: 38 emitted/0 missing/26 extra; closure:2: 39 emitted/0 missing/27 extra; closure:3: 39 emitted/0 missing/27 extra. Work 53334.

Missing hand count signatures: 0; extra selected count signatures: 0. Every extra PRE tuple appears in hand-closure-none.json trace[].extras, with its exact phase and AST.

## Count signatures

- wNew: below size, unit 0, +1 members[0] -1 missing[0]
- wA: below size, unit 0, +1 members$Decision[(64*key$2#+key$3)] -1 can$Vote$members[(64*key$2#+key$3)]
- wC: below size, unit 0, +1 members$Decision[(64*key$4+key$5)] -1 can$Vote$members[(64*key$4+key$5)]
- wR: below size, unit 0, +1 members[0] -1 missing[0] -1 can$Vote$members[(64*r+v)]

Exact signatures and the hand-support/generic-selector test are in diff.json. Empty-cert and per-count deletions are SAT only for the quantifier-free abstraction; they are not protocol counterexamples.
