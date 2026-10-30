# Adversarial inferred-boundary results

Law for every case: `r.law('n stays zero', ({n}) => n.eq(0))`, unless extraction refuses before a law can be constructed. Predictions precede runs. Refusals and explicit tagging requirements are acceptable even when the expected category differed.

| Case | Language | Attack | Predicted | Actual | Verdict |
|---|---|---|---|---|---|
| [p01](p01.py) | Python | listener handed self | needs a tag | refused: the rule and the code differ: run 1, request 1: tick() from {"n":0}: the code throws (raised: AttributeError: 'FakeStore' object has no attribute 'emit'), the rule takes the step | OK |
| [p02](p02.py) | Python | listener handed mutable state field | needs a tag | refused: the rule and the code differ: run 1, request 1: tick() from {"n":0,"data":{}}: the code throws (raised: AttributeError: 'FakeStore' object has no attribute 'emit'), the rule takes the step | OK |
| [p03](p03.py) | Python | alias to self passed to listener | needs a tag | refused: the rule and the code differ: run 1, request 1: tick() from {"n":0}: the code throws (raised: AttributeError: 'FakeStore' object has no attribute 'emit'), the rule takes the step | OK |
| [p04](p04.py) | Python | repository save mutates held record | needs a tag | refused: self.repo.save('one', self.row): a ref set in a store of numbers | OK |
| [p05](p05.py) | Python | store get mutable object alias | refused | refused: row.n: a field of a num | OK |
| [p06](p06.py) | Python | skipped helper mutates global used by rule | refused | refused: the rule and the code differ: run 1, request 1: tick() from {"n":0}: n is 1 in the code, 0 in the rule | OK |
| [p07](p07.py) | Python | truthiness of inferred boolean answer | refuted | refuted: reachable one-step run | OK |
| [p08](p08.py) | Python | optional None answer truthiness | refuted | refuted: reachable one-step run | OK |
| [p09](p09.py) | Python | untyped Any answer | needs a tag | refused: self.flags.value(): the truth of self.flags.value(): the value of flags.value, other code left out; self.flags.value(): value, a method of the store not stated as its get, set or delete (p09.py:10:12), whose value is read, and it declares no type: state what it returns (answers: {"value": 'int'}, or a `gdp: answer int` comment on its line) | OK |
| [p10](p10.py) | Python | async answer | refuted | refuted: reachable one-step run | OK |
| [p11](p11.py) | Python | post-construction field injection | refused | refused: self.flags: no field flags (the object's fields are those its constructor sets) | OK |
| [p12](p12.py) | Python | two dependencies with shared underlying store | refused | accepted, SAT from arbitrary state; real shared-store run disagrees | WRONG |
| [p13](p13.py) | Python | entry discovery through private helper | refuted | refuted: reachable one-step run | OK |
| [p14](p14.py) | Python | overloaded declared result | refuted | refuted: reachable one-step run | OK |
| [p15](p15.py) | Python | generic return TypeVar | needs a tag | refused: a self.source.get_value(1): the value of source.get_value, other code left out where the state holds a scalar; self.source.get_value(1): get_value, a method of the store not stated as its get, set or delete (p15.py:11:18), whose value is read, and it returns T, a type outside the files read: state what it returns (answers: {"get_value": 'int'}, or a `gdp: answer int` comment on its line) | OK |
| [p16](p16.py) | Python | exception-only use of external call | refused | refused: Meter(source): a constructor argument of rec (state it as a store, or give it a default) | OK |
| [r01](r01.rb) | Ruby | listener handed self | needs a tag | refused: tick returns @listener.emit(self): the value of listener.emit, other code left out (a result the rule keeps); @listener.emit(self): emit, a method of the store not stated as its get, set or delete (r01.rb:8:5), whose value is read, and it declares no type: state what it returns (answers: {"emit": 'int'}, or a `gdp: answer int` comment on its line) | OK |
| [r02](r02.rb) | Ruby | call truthiness in condition | needs a tag | refused: : the truth of Flags.enabled: the value of Flags.enabled, other code left out; Flags.enabled: Flags, another class's code (r02.rb:8:15), whose value is read, and it declares no type: state what it returns (answers: {"enabled": 'int'}, or a `gdp: answer int` comment on its line) | OK |
| [j01](j01/Meter.java) | Java | injected callback handed this | needs a tag | proven and checked; real callback changes n to 1 | WRONG |
| [j02](j02/Meter.java) | Java | generic return type | refuted | refused: a source.value(1): the value of source.value, other code left out where the state holds a scalar; source.value(1): value, a method of the store not stated as its get, set or delete (Meter.java:7:28), whose value is read, and it returns a typevar:T (a type of other code): state what it returns (answers: {"value": 'int'}, or a `gdp: answer int` comment on its line) | OK |
| [t01](t01.ts) | TypeScript | injected callback handed this | needs a tag | refused: the rule and the code differ: run 1, request 1: tick() from {"n":0}: the code throws (a function given to the constructor called while the object is made), the rule takes the step | OK |
| [t02](t02.ts) | TypeScript | injected boolean result truthiness | refuted | refuted: reachable two-step run | OK |
| [j03](j03/Meter.java) | Java | answered callback handed this | needs a tag | proven and checked; real callback changes n to 1 | WRONG |
| [j04](j04/Meter.java) | Java | keyed get extra argument aliases this | needs a tag | proven and checked; real get changes n to 1 | WRONG |
| [p17](p17.py) | Python | FastAPI Depends with yielding dependency | refuted | harness could not load: FastAPI not installed | UNSURE |

### Diagnoses and witnesses

**j01.** `core/extract-step.ts:1464` dispatches injected methods to `storeCall`, and `core/extract-step.ts:771` discards their evaluated arguments before `boundary` can see `this`.
`core/jvm/Harness.java:51`–`52` makes the unrecognized method a no-op, so the check and checked proof miss `j01/Repro.java`, whose real listener sets `n` to 1.

**j03.** The same argument erasure at `core/extract-step.ts:771` bypasses the state-reference refusal at `core/extract-step.ts:845`–`847`, even when the call is promoted to an answer.
The stubbed check proves `n = 0`; `j03/Repro.java` supplies a conforming listener that sets `n` to 1 and returns false.

**j04.** `core/extract-step.ts:1464` sends the call to `storeCall`; `core/extract-step.ts:779`–`781` models a get using only its key and never rejects the extra `this` argument.
The proxy's get at `core/jvm/Harness.java:44` ignores that extra argument; `j04/Repro.java` supplies a conforming get that mutates it, so the checked invariant is false.

**p12.** `core/extract-step.ts:2283` creates separate store identities from parameter names, without detecting that injected dependencies may share an object or backing data.
`core/py/harness.py:74` likewise supplies distinct `FakeStore`s: the accepted rule reads an empty `b` and leaves `n = 0`, but `repro_p12.py` passes one store twice and prints `n = 1` after one tick. The SAT result has no reachable run, so it is not claimed as a checked false proof.

The per-case JSON files preserve extraction notes, generated rule, evidence and proof result. Each successful extraction used 30 runs, depth 6 and 60 from-states; Java reports zero instrumented branch arms. SAT results marked refuted include a `run` in the corresponding JSON and may assume the inferred answer. The Python callback cases p01–p03 were refused only because the fake store lacks the method, not because the state reference was detected.

Reproduce Java witnesses with `/opt/homebrew/opt/openjdk@21/bin/javac -d j01 j01/Meter.java j01/Repro.java` followed by `/opt/homebrew/opt/openjdk@21/bin/java -cp j01 Repro` from this directory; substitute `j03` or `j04`. Run the Python witness with `python3 -B repro_p12.py`. The ordinary `java_home` lookup found no JDK, but Homebrew JDK 21 worked; Python, Ruby with Prism, Node and Bun were available. FastAPI was unavailable, and Kotlin was not tested.

### WRONG cases ranked by severity

1. **j03** — an answered callback is stubbed despite receiving mutable rule state; a checked proof is false for a conforming implementation.
2. **j01** — an unread callback given the whole rule object is silently skipped; a checked proof is false for a conforming implementation.
3. **j04** — a keyed store operation ignores an extra state reference; a checked proof is false for a conforming implementation.
4. **p12** — accepted extraction disagrees with a real shared-store injection; this particular attempted law was not proven.
