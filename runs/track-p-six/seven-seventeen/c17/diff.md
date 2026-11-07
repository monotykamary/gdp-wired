# Index 17: original family19 STEP

Hand certificate: 3 PRE tuples, 1 CountInst entries. No original guards or global assumptions removed. Fresh check receipt: zero-search.json.

## Required PRE tuples

### generic-all

- L17 (key1$enum#, key2$enum): **prepare**
- L3 ((64*key1$enum#+key2$enum)): **prepare**
- L45 (wNew, r, v): **MISSING**

Phases: prepare: 44 emitted/1 missing/42 extra; closure:0: 71 emitted/1 missing/69 extra; closure:1: 71 emitted/1 missing/69 extra. Work 65536.

Missing hand count signatures: 1; extra selected count signatures: 10. Every extra PRE tuple appears in generic-all.json trace[].extras, with its exact phase and AST.

### generic-none

- L17 (key1$enum#, key2$enum): **prepare**
- L3 ((64*key1$enum#+key2$enum)): **prepare**
- L45 (wNew, r, v): **MISSING**

Phases: prepare: 12 emitted/1 missing/10 extra; closure:0: 36 emitted/1 missing/34 extra; closure:1: 38 emitted/1 missing/36 extra; closure:2: 38 emitted/1 missing/36 extra. Work 65536.

Missing hand count signatures: 1; extra selected count signatures: 10. Every extra PRE tuple appears in generic-none.json trace[].extras, with its exact phase and AST.

### hand-closure-all

- L17 (key1$enum#, key2$enum): **prepare**
- L3 ((64*key1$enum#+key2$enum)): **prepare**
- L45 (wNew, r, v): **closure:0**

Phases: prepare: 44 emitted/1 missing/42 extra; closure:0: 59 emitted/0 missing/56 extra; closure:1: 60 emitted/0 missing/57 extra; closure:2: 60 emitted/0 missing/57 extra. Work 53534.

Missing hand count signatures: 0; extra selected count signatures: 0. Every extra PRE tuple appears in hand-closure-all.json trace[].extras, with its exact phase and AST.

### hand-closure-none

- L17 (key1$enum#, key2$enum): **prepare**
- L3 ((64*key1$enum#+key2$enum)): **prepare**
- L45 (wNew, r, v): **closure:0**

Phases: prepare: 12 emitted/1 missing/10 extra; closure:0: 22 emitted/0 missing/19 extra; closure:1: 23 emitted/0 missing/20 extra; closure:2: 23 emitted/0 missing/20 extra. Work 31773.

Missing hand count signatures: 0; extra selected count signatures: 0. Every extra PRE tuple appears in hand-closure-none.json trace[].extras, with its exact phase and AST.

## Count signatures

- wNew: below size, unit 0, +1 members[0] -1 missing[0]

Exact signatures and the hand-support/generic-selector test are in diff.json. Empty-cert and per-count deletions are SAT only for the quantifier-free abstraction; they are not protocol counterexamples.
