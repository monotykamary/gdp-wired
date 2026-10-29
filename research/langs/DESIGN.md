# One structure for every language

gdp-wired/extract read TypeScript (core/extract-read.ts) and Go (core/extract-go.ts), each with its own symbolic
executor: the TypeScript one over the compiler's AST, the Go one over the JSON core/go/reader.go prints. This is the
structure the next languages share, built first for Python: one IR, one executor, one check driver, and per language
a reader in that language plus a harness.

```
  the code ──► reader (the language's own parser) ──► step IR (JSON) ──► executor (TS, shared) ──► Model
                core/py/reader.py: ast                                core/extract-step.ts       │
                                                                                                 ▼
  the code ◄── harness (the language's own runtime) ◄── JSON lines ◄── checkStep + drive ◄── fromModel: the rule
                core/py/harness.py                                   (core/extract-check.ts)  printed and built
```

## The pieces

| Piece | Where | Shared? | What it does |
| --- | --- | --- | --- |
| reader | `core/py/reader.py` (Python's `ast`) | per language | Parses the module, resolves names (locals, the module's functions and classes, imports, builtins), reads record types from the repository's own modules (annotations only, never run), and lowers everything into the IR. It decides nothing about the subset beyond the syntax: a construct the IR has no node for becomes `{"e": "no"}` / `{"s": "no"}` with the reason. |
| step IR | `core/extract-step.ts` (`SModule`, `SX`, `SS`, `SType`) | shared | Records (fields, methods, kinds), functions (params with types and defaults, decorators, async, branch arms), statements (`set`, `if`, `ret`, `fail`, `with`, `del`, `import`, `expr`, `no`), expressions (literals, `var`, `get`, `idx`, `bin`, `cmp`, `and`/`or`, `not`, `ite`, `call`, `await`, `fstr`, `tuple`, `dict`, `ext`, `lib`, `builtin`, `no`). |
| executor | `core/extract-step.ts` (`Stepper`, `readStep`) | shared | Executes each method symbolically: a path is a condition, locals and a heap of objects (records, maps, stores); branches fork and join; calls of the module's code are inlined; the methods together become the Model (core/extract-read.ts's type, the same the TypeScript and Go front ends make). |
| printing, building | `core/extract.ts` `fromModel` | shared (already) | Sorts, the rule's source, the rule built from it, its invariants. |
| check driver | `core/extract-check.ts` `drive` | shared (already) | Runs from the start, from drawn states and from the prover's witnesses, every state, cell, result and refusal compared. |
| code side | `core/extract-step.ts` `checkStep` | shared | The JSON-lines protocol over two named pipes: `hello`, `new`, `at` (an object set to a state), `get`, `call`, `coverage`. |
| harness | `core/py/harness.py` | per language | Imports the module as it ships, makes the object, sets and reads leaves by path, stubs answered calls, gives stores, patches the clock, counts the arms reached (line events). Reflective for Python (and Ruby and Elixir later); generated and compiled for static languages (as Go's is). |
| front end | `core/extract-py.ts` (`gdp-wired/extract-py`) | per language, thin | Runs the reader, then `extractStep` with the harness command. |

## Where each language's semantics live

In the IR, as explicit operations the reader chooses, so the executor stays one:

| Semantics | In the IR | Python | Later |
| --- | --- | --- | --- |
| integer width and overflow | the reader's types (`int`, `float`); fixed widths planned as `int` with `bits`, `signed` and `ovf: wrap \| trap \| ub` | unbounded: the rule's numbers stop at ±2^53, a step past them refused (as for JavaScript and Go's 64-bit) | Go, Rust: wrap or trap by the operation; C, C++: unsigned wraps, signed overflow is UB (refused) |
| division and remainder | `bin` `//` `%` by a constant: floor (`floorDiv`); `int(x / k)` truncates; `math.floor`/`math.ceil` of `x / k` | floor | C, Go, Rust: trunc (already in `quotient`) |
| floats | `float` type read at whole values (exact below 2^53, as JavaScript's numbers are read); a non-whole literal and a true division refused | yes | the same |
| truthiness | executor's `truthy`: bool, number ≠ 0, string ≠ "", None false, an object true unless its class defines `__bool__`/`__len__`, a dict's refused | yes | Ruby: only nil and false; C: ≠ 0; the reader lowers to `cmp` where the language has no truthiness |
| a missing value | `none`, `opt` (has, value); narrowed by the path (`if x is None: return`) | `X \| None` | Rust `Option`, Go nil, Ruby nil, Elixir nil |
| failure | `fail` (a statement), and the executor's own (KeyError, None where a number is read, division by zero) | raise, assert | Go's error results, Rust's `Err`/panic, Elixir's `{:error, _}`: the reader lowers each to `fail` |
| what a failure means | `failures: 'refuse'` (the step's refusal) or `'kept'` (its result `failed`, with what the step wrote before it unless `onError: 'discard'`) | both | the same |
| maps | `idx`, `dict.get/pop`, `in`, `del`: one key written a step | `dict[K, V]` | Rust `HashMap`, Ruby `Hash`, Elixir maps |
| records | the module's classes and dataclasses, by reference (a fresh one put in a map is moved) | yes | value records (copy semantics) for Go structs, Rust, C, Elixir: one flag on the record kind |
| immutability | not needed for Python | | Elixir: a function returning the new state is a reducer step (the TypeScript front end's shape), lowered as a `ret` of a record |
| atomicity | `with` a lock; an async method is one step when every await is the module's own or answered (nothing else runs while it does) | yes | Go's mutex (already Go's), Rust's `Mutex` guard, a GenServer call (one message is one step) |

## What a caller states (the boundary)

Real code calls other code. Three statements, each printed in the extraction's notes and enforced by the check:

- `answers: {callee: type}`: the call's result is an input of the request (the check stubs the callee with it). For a
  counter read from Redis, a feature flag, a registry lookup.
- `skip: [callee]`: the call is left out: its value is kept only where nothing the rule keeps reads it, and the check runs it
  as it is (a logger, an alert task, an error's message, a context manager, a decorator taken as transparent).
- `stores: {field: {get, set, delete, value, attrs}}`: an object of other code held as a key-value store (a cache
  client): each key template (a string, or an f-string with one hole) is a map of the state; its TTL, eviction and
  replication are left out, and the check gives the code a store that keeps what is set. Two templates must name
  disjoint keys (they differ in a fixed prefix or suffix) or the extraction is refused.

## Measured: does Go's front end move onto it?

Go's executor (`GoReader`, 1,340 lines, 112 KB with `readGo`) does what the shared one does plus: pointers into the state
(`Ptr` by cases, `deref`, `writeThrough`), value structs (copies), fixed-width integers with wrap, `*big.Int` (an
unbounded number with nil), slices with append's aliasing, error results and panics, a mutex's deferred Unlock, switch
with fallthrough, multiple results. About 55% of it is Go-specific semantics that the IR would carry as operations
(widths, value records, lists, tuples, nil maps); the rest (paths, joins, map writes, lazy argument fields, the methods
assembled into the Model, about 45 KB) is what `Stepper` and `readStep` already do. Moving Go means reader.go lowering
into the IR (+8 KB of Go), the executor gaining lists, value records, widths and tuples (+20 KB, needed anyway by Rust,
C, C++ and Elixir), and extract-go.ts shrinking to its options and type table (about 10 KB): an expected **−75 KB**
net. It is not cheap (the term shapes, hence the printed rules, would differ from today's unless the executor follows
Go's join order exactly, and byte-identical output is the bar), so it is planned after the languages that need those
operations anyway, not done in phase 1.

## Size

| | Bytes | Notes |
| --- | --- | --- |
| `core/extract-step.ts` | see the report | the IR, the executor, the check's code side, once |
| `core/extract-py.ts` | ~5 KB | the front end |
| `core/py/reader.py` | ~25 KB | Python |
| `core/py/harness.py` | ~12 KB | Python |

Per language from here: its reader (15–30 KB in its own language) and its harness (8–12 KB reflective, 15–25 KB of TS
generating it for a static language), and a ~3 KB front end.

## The next languages, on this structure

Each is its reader (in the language, with its own parser), a harness, a ~3 KB front end, and the executor operations it
needs that no earlier language added. In the order planned:

| Language | Reader | Harness | Executor additions (shared from then on) | Expected bytes |
| --- | --- | --- | --- | --- |
| Rust | a small binary on `syn` (as core/go/reader.go is on go/ast), types from the crate's own items | generated: a `main` beside the crate, built by cargo, serde_json lines | fixed widths with `ovf: trap` (debug) and the `wrapping_*`/`checked_*` forms; value records (copies); `Option`/`Result` as `opt`/`fail`; `HashMap`; `Vec` as lists | reader ~25 KB Rust, harness generator ~15 KB TS, executor +15 KB |
| Ruby | Prism (`Prism.parse`, Ruby 3.3+), ~15 KB Ruby | reflective (`instance_variable_set`), ~8 KB Ruby | Ruby's truthiness (only nil and false) as a reader choice; `Hash`; `Struct`/`Data.define` as records | ~23 KB, executor +1 KB |
| Elixir | `Code.string_to_quoted`, ~18 KB Elixir | reflective over a GenServer's state or a module of functions, ~8 KB | the reducer shape (a function returning the new state, the TypeScript front end's own), `case`/`cond`/`with` lowered to `if`, `{:ok, _}`/`{:error, _}` as `fail` | ~26 KB, executor +5 KB |
| C | `clang -Xclang -ast-dump=json`, lowered by a ~18 KB reader (Python or TS: C has no parser of its own to write it in) | generated C with a line protocol of numbers, ~12 KB TS | `ovf: wrap` (unsigned) and `ub` (signed: refused), trunc division, pointers to the state's structs (refs), return codes as failures stated by the caller | ~30 KB, executor +5 KB |
| C++ | the same clang JSON, classes and methods | generated C++, ~+5 KB over C's | `std::map`/`unordered_map` | ~+12 KB over C |

Then Go moves onto the executor (above: about −75 KB), since lists, value records and widths are there by then.

## Packaging

The npm library has no hard dependency on any language: `gdp-wired/extract-py` runs `python3` (or the Python given)
only when called, and its reader and harness ship as files beside it (`dist/core/py/`). A missing Python is a refusal
saying so, not a crash. A later `gdp-wired/extract` may dispatch on the file's extension; for now each language has
its entry point, as Go's has.
