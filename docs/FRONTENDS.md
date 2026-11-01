# Plugging in a front end

A front end reads something people wrote into a rule the kernel can be asked about. It is untrusted
([ARCHITECTURE.md](ARCHITECTURE.md)): a wrong reader doesn't make the kernel unsound, it makes the kernel prove a true
fact about a different rule. So a reader in gdp-wired is never only a translator. It ships with a run of the code beside
the rule it reads, and the extraction is refused on any difference. This page covers the contract, the shared machinery
and what a new language brings, with Python as the worked example. Every name below is in the code. The design notes
behind the shared structure are in [research/langs/DESIGN.md](../research/langs/DESIGN.md).

```
 the code ──► reader (the language's parser) ──► step IR (JSON) ──► executor (TS, shared) ──► Model ──► fromModel ──► rule
              core/py/reader.py                 core/extract-step.ts  Stepper, readStep              core/extract.ts   │
                                                                                                                       ▼
 the code ◄── harness (the language's runtime) ◄── JSON lines ◄── checkStep (code side) ◄── drive (both sides, compared)
              core/py/harness.py                     core/extract-step.ts                    core/extract-check.ts
```

## The contract: what a front end returns

`Extraction` (`core/extract.ts`) holds:

- `ok`: whether the rule was read and checked against the code.
- `rule`: a builder rule whose `machine` is the kernel's plain `Machine`.
- `invariants`: inductive facts about every state the code can be in, proven with the laws.
- `source`: the rule as printed TypeScript, the thing that is proven.
- `refusals`: `{where, what}` pairs (`file:line:col`, and why).
- `evidence`: what the check ran.
- `names`: each rule variable's path in the code, with its role: state, param, input, answer, result, failed,
  method, clock or const. `core/laws.ts` reads laws through these and never guesses one.

A front end never approximates. Whatever is outside its subset becomes a `Refusal` (`core/extract-read.ts`) at the
place it occurs, and the extraction comes back with `ok: false`.

The model a reader produces is `Model` (`core/extract-read.ts`): the parameters, inputs and state (scalars, maps and
lists), the event that picks a method, and one term per state variable over them (`core/extract-ir.ts`'s `N`, `B`, `L`
and `K`: exact integers, conditions, choices and keys). It also holds the refusal condition, the initial state, the
outputs and the laws stated beside the code. Everything from the Model on is shared:

| Shared piece | Where | What it does |
| --- | --- | --- |
| sorts and printer | `core/extract-print.ts` (`sortsOf`, `pterm`) | Decides which numbers are naturals and prints the rule as builder source. |
| build | `core/extract.ts` (`fromModel`) | Builds the rule from the printed source, derives its invariants, runs the check, and refuses with `the rule and the code differ: …` when `evidence.mismatch` is set. |
| merges | `core/extract-read.ts` (`mergeWrites`, `mergeOps`) | Merges map writes and list operations made under a condition. |
| step IR and executor | `core/extract-step.ts` (`SModule`, `Stepper`, `readStep`, `extractStep`) | Executes each method symbolically: a path condition, locals, a heap of records, maps and stores, branches forked and joined, the module's own calls inlined. |
| the check | `core/extract-check.ts` (`drive`, `CodeSide`) | Runs both sides and compares them (below). |
| code side over pipes | `core/extract-step.ts` (`checkStep`, `Harness`) | Speaks to the harness: JSON lines over two named pipes, with the ops `hello`, `new`, `at`, `get`, `call` and `coverage`. |

Two routes reach the Model:

- **Through the step IR.** This is the route for Python, Ruby, Elixir, Java, Kotlin, Rust, Swift and Solidity. The
  language brings a reader that prints `SModule` JSON, a harness that answers the six ops, and a thin `extractX` that
  calls `extractStep`. Its semantics are explicit IR operations that the reader chooses, so the executor stays one.
  DESIGN.md's "Where each language's semantics live" has the table.
- **Through its own executor.** Go (`core/extract-go.ts`, with `core/go/reader.go`), C and C++ (`core/extract-c.ts`)
  and TypeScript (`core/extract-shapes.ts`) execute into the Model themselves. Each implements its own `CodeSide`:
  `core/extract-go-check.ts` builds a generated harness with `go build -cover` and calls `drive`.

## The differential check

`drive(m, r, sorts, code, opts)` in `core/extract-check.ts` holds a reader to the code it read. On the rule's side,
every request runs on the interpreter (`r.interpreter()`) and the generated JavaScript (`r.compiled()`), and the two
must agree. On the code's side, `CodeSide` runs the code as it ships. It has these members:

- `make`, `at`, `snapOf`, `call`, `args`, `setNow` and `coverage`;
- optionally `reduce`, `init`, `input`, `drawSnap`, `normalize` and `edge`.

Requests come from three sources:

- **runs from the start**: 200 runs of up to 12 requests by default, the values drawn near each comparison's
  boundaries and the clock allowed to move back;
- **drawn states**: 400 by default. A proof covers every state, not only the reached ones, so `at` sets the object to
  each drawn state;
- **the prover's witnesses**: each branch condition is put to `proveSteps` as "never holds", and the state it
  produces runs on both sides.

After each request `drive` compares:

- the refusal on each side, where a throw that changed the object is a difference of its own;
- the whole state, with `sameSnap`, every map cell and list included;
- the method's result.

The first difference sets `evidence.mismatch`, and `fromModel` refuses the extraction with it. The printed source is
still returned, so the difference can be read. Branch arms are counted on both sides. The executor records each arm's
first line, and the harness traces which lines ran. The tests require every arm reached (`coverage.hit ===
coverage.arms`). A value past the rule's exact range (±2^53) is counted as `outside` or `edge`, never compared as a
wrong number.

What the check does not show is what no run reaches. The adversarial round covers that. `research/langs/adversarial/cases.json`
holds code written to make a reader prove `n stays zero` falsely: aliasing, a listener handed `self`, truthiness of an
answer, two injected dependencies sharing a store and so on. `cases.test-lib.ts`'s `judge` requires that no case
yields a checked proof, and that each case listed in `WHY` is refused for its stated reason. Each language's test file
runs its own cases. For Python, `core/extract-py.test.ts` runs `advCases('Python')`, cases p01 to p17.

## The CLI's comment-law contract

`gdp-wired check <file|dir>` (`core/cli.ts`, published as `npx gdp-wired-cli check`) reads the rule from the code and
the laws from its comments. The contract is the same in every language:

- **Syntax** (`core/laws.ts`'s `FORMS`, read by `lawsIn`):
  - a comment, `# gdp: law <name>: <expr>`, with `//`, `--`, `%` or `/* */` in place of `#`;
  - an annotation, `@GdpLaw("<name>: <expr>")`, `@gdp.law(...)` or `@gdp_law ...`;
  - a Rust attribute, `#[doc = "gdp: law ..."]`.

  The first `:` splits the name from the expression. `gdp: cite <law>: <clause>` (`citesIn`) ties a law to the text
  it answers. A citation of a law nobody stated is reported, not dropped.
- **The expression** (the header of `core/laws.ts`, and `parse`):
  - comparisons, `+ − ×` by a constant, `//` and `%` by one, `and or not implies`;
  - `min`, `max`, `abs`, `sum(map)` and `forall k in m:`;
  - `old(x)` and `before.x`, the request's arguments by name, `result` and `failed`;
  - maps at a key as the code reads them, store keys by template, choices by value, and durations
    (`30 days`; months are refused).

  Names resolve only through `Extraction.names`. A name the code doesn't have is refused, and the refusal lists the
  names it has.
- **Kind, by what the law reads** (`buildLaw`): a law that reads only the state and sits outside any method is an
  invariant. A law that sits on a method, or reads an argument, `result`, `failed`, `old` or the clock, is a law of
  one step. Other forms:
  - two-run laws: `never reaches`, `isolated by` and `agrees with` (`buildTwoRuns`);
  - liveness: `<from> leads to <to> [by <rank>] via <request>[; …] [strongly]` (`buildLeadsTo`).
- **Placement** (`core/cli.ts`'s `scoped`): a law belongs to the nearest enclosing class and to the definition it sits
  on. In Python the class must enclose the law's indentation, and a top-level `def` is in no class. In TypeScript, a
  `const` right below the law owns it. In Go, a method belongs to its receiver's type. A law no rule takes is reported
  as `not read`, with how to name its entry.
- **Options** (`configFor`): the nearest `gdp.toml`, `pyproject.toml`'s `[tool.gdp]` table, or `package.json`'s `"gdp"`
  key. Top-level keys apply to every rule, and `[rules.<entry>]` to one. The keys are `failures`, `onError`,
  `methods`, `answers`, `skip`, `stores`, `strict`, `root`, `python`, `entry`, `clock` and `from`. Flags override the
  file.
- **Verdicts and exit** (`check`): each stated law is `proven`, `broken` (with a run, replayed on the code), `unknown`
  or `not read`. The exit code is 1 when one is broken, else 2 when one is not read (a refused rule makes every law of
  it not read), else 0. `--from any` proves the laws from every state they allow; the largest inductive subset of the
  stated laws is found by Houdini (`houdini`). `--cert <dir>` writes each proven law's certificate as an interchange
  document (`core/relational.ts`'s `certify`), checked as it is written. `gdp-wired-check` checks it again with
  nothing but the kernel (`interchange/cli.ts`; [interchange.md](interchange.md)).

## Worked example: Python

| Piece | File | Notes |
| --- | --- | --- |
| reader | `core/py/reader.py` | Runs under `python3 -I` with Python's own `ast` and prints one `SModule` (`main`). It resolves names, reads record types from the repository's annotations without running them, and decides nothing beyond the syntax: a construct with no IR node becomes `{"s": "no", "why": …}` or `{"e": "no", …}`. Examples are `a loop (while)`, `match`, `a comprehension (a loop)` and `a float that isn't whole`. |
| front end | `core/extract-py.ts` | `readPython` runs the reader. If Python is missing, it fails with a `Refusal` naming python3. `extractPython` hands `extractStep` the IR and a `Harness` (`harness.py`, with `hello: {root, path, module}`). The module is 71 lines. |
| semantics | `core/extract-step.ts` | Ints are unbounded, so a step past ±2^53 is refused by the rule's range. `//` and `%` by a constant floor (`floorDiv`); a true division is refused unless it sits under `math.floor`, `math.ceil` or `int`. `truthy` gives Python's truthiness and refuses a dict's. KeyError and None read as a number are failures. A raise or assert is the step's refusal, or its `failed` result with `failures: 'kept'`. A failure after a write is refused unless `onError: 'discard'`. One object in two places of the state is refused, and so is other code handed the state (unless a `gdp: skip` says it doesn't write). |
| harness | `core/py/harness.py` | Two named pipes, one JSON line per request (`main`). Integers travel as decimal strings. It patches the clock to the request's time, stubs the answered calls, gives stores, and reports a change to a field the rule leaves out as a difference. Arms reached are counted by `sys.settrace`. |
| boundary | `StepOptions` (`answers`, `skip`, `stores`) | Inferred from annotations where it can be, otherwise stated in `gdp.toml` or by a `# gdp: skip` on the line. It is printed in the notes and enforced by the check. |
| tests | `core/extract-py.test.ts` | A token bucket, dicts of dataclasses, failures kept, stores, folds over lists, try/except, sets and key templates. Every refusal message is pinned (`refusals`), full arm coverage is required, and the adversarial cases p01–p17 are judged. |

Two reads of `extractPython` on the same file (`core/py/examples/bucket.py`) show the contract at work. With the entry
`TokenBucket`, the rule is read and the check's runs, drawn states and witnesses all agree with the module. Every arm
is reached (the test's `ok` asserts `coverage.hit === coverage.arms` and no `mismatch`), and the laws are proven on the
extracted rule. Ask for its `drain` function instead and the extraction returns `ok: false` with
`bucket.py:<line>:<col>: a loop` (the `refusals` test). Nothing is proven about a rule the reader only half read.

## Adding a language

1. **The reader**, in the language, run by its own toolchain. It prints `SModule` and refuses with a reason whatever
   has no IR node. Choose the language's semantics as IR operations: width and overflow, division, truthiness,
   failure, and value versus reference records (DESIGN.md's table).
2. **The harness**, which answers `hello`, `new`, `at`, `get`, `call` and `coverage` over the two pipes. For a static
   language it is generated and compiled, as Swift's (`core/swift/Harness.swift`) and the JVM's
   (`core/jvm/Harness.java`) are.
3. **The front end** `core/extract-X.ts`: the reader's run, then `extractStep(mod, harness, opts)`.
4. **Registration** in the CLI (`core/cli.ts`): `Lang`, `EXT`, `COMMENT`, `LANG_NAME`, a case in `extractWith`,
   `targetsOf` if a package is a directory, and the language name for messages (`core/extract-step.ts`'s `LANG`).
5. **Packaging**: a subpath in `package.json`'s `exports`, the file in `tsconfig.build.json`, the reader and harness
   copied by `scripts/build.ts`, and an entry in `core/exports.test.ts`'s `FRONT` table, which checks all four.
6. **Tests** `core/extract-X.test.ts`, skipped where the toolchain is absent. They pin every refusal message and
   require full arm coverage. They hold the semantics adversarially (overflow at each width, aliasing, negative
   division, failure after a write), and add the language's cases to `research/langs/adversarial/cases.json`. A
   suite job (`supercomputer/suite.json`, `extract-X`) runs them.
7. **Certificates**: nothing to do. The rule goes to the provers as any other, `--cert` writes interchange documents,
   and every counterexample is replayed on the code before it is reported.

The other front ends follow the same contract. The TypeScript builder chains (`core/dsl.ts`) are checked by the type
checker and `core/builders.test.ts`. XState (`core/xstate.ts`) has `conforms`, which runs the real actor beside the
compiled rule. C and C++ go through clang's AST (`core/extract-c.ts`). The C benchmarks' reader
(`compare/term/c2ari.py`, then `compare/term/translate.ts`) replays every nontermination witness on an evaluator that
shares no code with gdp-wired (`checkLasso`).
