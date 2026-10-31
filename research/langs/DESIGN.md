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
| `core/extract-step.ts` | 98,952 | the IR, the executor, the check's code side, once (as large as Go's executor alone; the next languages add to it only the operations above) |
| `core/extract-py.ts` | 4,947 | the front end |
| `core/py/reader.py` | 25,911 | Python |
| `core/py/harness.py` | 12,370 | Python |

core/ and kernel/ in TypeScript (the bar's measure, tests excluded): +103,695 bytes against b118bf5; with the two Python
files, +142 KB.

Per language from here: its reader (15–30 KB in its own language) and its harness (8–12 KB reflective, 15–25 KB of TS
generating it for a static language), and a ~3 KB front end.

## Rust (built second)

`core/rs/src/main.rs` (45,627 bytes of Rust on syn) lowers a crate into the IR in A-normal form: Rust's `if` and
`match` used as values, `?`, and `return` inside expressions become statements over temporaries, closures are lifted
to functions of what they capture. `core/extract-rs.ts` (20,368) builds it once per version, and generates the
harness: a `#[cfg(test)]` module appended to the struct's own module in a copy of the crate (so private fields are read
and set as the crate's code does), `Instant::now()` rewritten to read the request's time, built by `cargo test
--no-run` with serde_json as a dev-dependency; the test binary is the harness, on the same JSON-lines protocol.

What the executor gained (+21,393 bytes, each for every language from now on): fixed-width integers on values
(`IntTy`) with `trap`, `wrap` (by cases, a sum or a difference), `sat`, `checked` overflow and trunc division; ranges
for inputs (a request outside its type refused), params (the precondition) and fields (a range law); casts (widening,
a C-like enum's discriminant, narrowing refused where it doesn't fit); Option and Result values (`some`, `ok`, `err`,
`is`, `unwrap`, `expect`, `opt_or`, `bad` for `?`), a Result returned at the top as the step's failure; value records
(`copy`); atomics' read-modify-writes on a place (`rmw`); closures with captures; struct literals (`new`); maps' Rust
methods (insert, remove, contains_key); a constructor that returns the object (`new`) or a derived Default. A latent
printer bug was fixed on the way (core/extract.ts: a condition by cases, hoisted, printed as a number).

Not yet: maps and vectors in a Rust state, `answers` and `stores` (the harness has no stubs), branch coverage (no
instrumentation: the arms are not counted), generics, trait methods on foreign types (failsafe's `Millis for
Duration`), two structs of one name in two modules (leaky-bucket-lite's).

## Moving Go onto the executor: measured (gen/go-shared)

**The baseline** is taken (research/langs/go-snapshot/): every extraction the Go tests make (38, 19 tests passing) and
every one research/extract/go-run.ts makes on the corpus's 25 Go sources (50), each one's rule source, notes and
refusals, from `GDP_GO_SNAPSHOT` in extract-go.ts (`research/langs/go-snapshot.json`, two Modal jobs, about 6 min).
`compare.ts` diffs a later run against it byte for byte (88 of 88 the same on the baseline itself).

**What GoReader is** (core/extract-go.ts, 111,679 bytes; its methods by lines): about 360 lines are what the shared
executor already does the same way (paths, join and merge, the methods assembled into the Model, inlining, lazy
argument fields: about 30 KB); the other 980 are Go's semantics (pointers into the state by cases, value structs,
*big.Int, error results, nil maps, slices with append's aliasing, a mutex's deferred Unlock, switch with fallthrough,
multiple results, 171 refusal sites of which the baseline reaches 36 distinct texts).

**A prototype** (gobreaker's Counts, the first test, lowered by hand into the IR and run through readStep) prints a rule
of the same shape as Go's, and differs where Go's semantics are better than the shared ones:
- Go wraps by the bounds of the term and the path's facts (`t2.atLeast(4294967296)`, one case; no wrap at all on a
  subtraction its `if` guards); the shared `wrap` checks both sides always. Go's should become the shared one.
- Go gives a kept result its type's range law; the shared executor gives fields only.
- the header's words and the notes' texts ("uint32: a result past its range wraps modulo 2^32, as Go's does").

**So the move is a port, not a deletion:** Go's integer and pointer semantics into the executor (on its values), a Go
lowering (the reader's JSON to the IR, in TypeScript beside reader.go, Go's refusal texts carried in the IR's `no` and
`fail` nodes), then GoReader deleted. Expected: −112 KB (GoReader) +10 KB (the front end's glue) +30 KB (the lowering)
+15 KB (pointers by cases, *big.Int as an unbounded Option, slices as lists, error results, fallthrough) ≈ **−57 KB of
TypeScript**, not the 75 KB estimated in phase 1 (which counted the lowering in Go). Python's and Rust's rules change
where the shared integer semantics become Go's (their corpus rules re-extracted; the laws re-proven).

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

## Moving Go onto the executor: done (gen/go-port)

**What moved.** GoReader is gone. core/extract-go.ts lowers the reader's JSON into the step IR (what Go's types decide:
which operation a node is, an integer's width and name, the receiver's form, a refusal that needs no execution, each
with Go's text), builds the state from the struct's zero value, binds the arguments, and assembles the Model as before;
core/extract-step.ts executes it. The executor gained, for every reader: pointers by cases (`ptr`, interior ones by a
path), places and writes through them, records by value (`struct`), error values and nil, maps with a nil state, lists
pushed, popped or set once a step, big integers, a lock's key with its deferred unlock, switch with fallthrough and
break, Go's inlining by id (results by the path that returned them), firm values (merged only with themselves), and the
module's `split: false` (a condition kept whole on the path). Shared with Python and Rust: the map writes' fold, the
range laws, the write-before-failure check, and the integer semantics below.

**Byte-identical: the acceptance test.** research/langs/go-snapshot/diff.ts reads every reading the baseline jobs
captured (research/langs/go-capture.json, `GDP_GO_CAPTURE` in extractGo and probeGoFunc: the reader's JSON, the options,
the GoRead or the refusal) and compares today's as JSON, byte for byte: 119 of 119 (38 from the tests, 50 from the
corpus, 31 probes of functions). `--extra` compares every struct of every captured package (its exported methods, then
each alone, with onError both ways) against 466c0ab's front end: 2,006 of 2,006. No Go needed; it runs in a second.
The snapshot jobs (research/langs/go-snapshot.json, compare.ts) are the end-to-end confirmation (rules, notes,
refusals, through the check).

**Go's integer semantics, shared.** Rust's `wrap` is Go's (by the term's bounds and the path's facts, by cases from
the bottom, any operation: a product wraps too); `trap`, `sat` and `checked` test only the side of the range the bounds
and facts don't exclude; a narrowing cast is refused only where it may not fit; division and remainder are Go's (one
case where the dividend's bounds say it is at least 0); an input outside its type is refused per bound (Go's two
refusals); a merged number keeps its type; a kept result gets its type's range law. Python's integers are unbounded,
so its rules don't change: LiteLLM's seven rules re-extracted at v1.106.6 are byte for byte the committed ones, every
verdict the same. Rust's StateManager is unchanged; GcraState's rule (research/langs/rust/rules/) is shorter: each input
bound its own refusal, and the sign tests and a trap on revert_at's subtraction that the path's `if` excludes are gone;
its five laws are proven as before, the check agreeing on 2,518 requests.

**Bytes (measured, not the −57 KB planned).** core/extract-go.ts 111,679 → 61,201 (−50,478); core/extract-step.ts
120,364 → 168,662 (+48,298); core/ and kernel/ in TypeScript, tests excluded: −2,180 against 9220ad0 (the snapshot and
capture hooks, about 1.4 KB, included). The plan counted +15 KB for the executor and +40 KB for the lowering and its
glue; mirrored exactly (byte-identical output being the bar), Go's semantics took +48 KB in the executor, and the
lowering with the state, the arguments and the model's assembly is 61 KB, about what GoReader's own type-directed
code and readGo were. What the two executors really shared (paths, joins, maps, the model's folds) is the 2 KB saved
plus the 30 KB GoReader no longer repeats inside the 48 KB. Slimmer from here means Python and Rust moving onto the
operations Go brought (records by value for Rust's copies, pointers by cases for Python's objects, error values for
Option and Result), each a change to their rules to re-prove, not a byte-identical port.

**Resume.** Captures: runs/langs/cap/*.jsonl (not committed; retake with research/langs/go-capture.json, the realworld
one through the olean volume's /gocap, then `modal volume get`). Validation: research/langs/go-port.json (snapshot,
Rust tests and corpus with --write, LiteLLM). Bars: `bun bar --quick --cand gen/go-port --base 9220ad0 --backend modal
--together` (no shared baseline of 9220ad0 exists), then `--only suite,suite-usual,rw,onecpu --together`.

## Ruby (gen/ruby)

`core/rb/reader.rb` (23,154 bytes of Ruby on Prism) lowers a class into the IR; `core/rb/harness.rb` (5,843) is the
reflective harness, Python's protocol; `core/extract-rb.ts` (4,559) the front end; the executor +1,038 bytes.

**Types, inferred.** Ruby states none, so the reader reads them from the code: a field's from what the class assigns
it (symbols, or literal constants of the code that are symbols: a choice; nil beside numbers: an optional number; a
local or another field: what it is assigned) and how it is used (computed with or ordered against: a number), an
argument's from what its method compares it with (`case x when :a`, `x == :b`: a choice) or computes it into, or its
default, or the field it is kept in. A type inferred wrong is a refusal at the check, never a rule that lies.

**Ruby's semantics, in the IR.** Every field is nil until set (initialize sets them nil first; a class without one
gets one); a method's last expression is its result (each branch's too); `/` and `%` are floor (`//`); only nil and
false are false (the module's `truth: 'nil-false'`, the executor's one switch for it); case/when is a chain of ifs on
`==`; `x.synchronize do ... end` is a lock (`with`); attr_reader, attr_writer and attr_accessor are methods the reader
writes; a constant of the code that is a literal is read from the file under the root that defines it, and the check
loads that file first.

**What the executor gained:** the truth switch, symbol arguments (`sym` on a choice type and on the harness's
argument), keyword arguments to a constructor given as keywords (Python's keyword-only ones had the same gap), a
literal written to a field of a choice typed as the choice (any reader's), `?` and `!` in names (`open?` is
`open_p`), `@` dropped from a field's name, and arms at line 0 (statements the reader writes) not counted.

**The corpus.** semian 0.28.4 (Shopify, MIT): `Semian::Simple::State` (closed, open, half open; 4 laws) and
`Semian::Simple::Integer` (the success counter; 3 laws); stoplight 6.0.0 (MIT): the in-memory light state
(`transition_to_color`, `clear` under a mutex, the clock an injected object stated with `clocks`; 4 laws, among them
"a recovered light is never breached", an invariant). All 11 proven; each rule checked on 2,300–2,800 requests.
research/langs/ruby/run.ts fetches the gems from rubygems.org and re-extracts (`--write`).

**Not yet:** arrays and hashes (semian's CircuitBreaker keeps its errors in a sliding window, an array), blocks other
than synchronize, `answers` and `stores` (rack-attack's throttles read a cache), records as arguments, def_delegators,
modules mixed in.

## Elixir (gen/elixir)

`core/ex/reader.exs` (32,705 bytes of Elixir on `Code.string_to_quoted`) lowers a module into the IR;
`core/ex/harness.exs` (8,346) runs it; `core/ex/json.exs` (2,356) is their JSON (an Elixir before 1.18 has none);
`core/extract-ex.ts` (3,762) the front end; the executor +374 bytes.

**The reducer shape, on the object shape.** Elixir's state is a value its functions return. The reader lowers each
handler into a method of an object whose fields are the state's: the state the handler is given is the object
(`self`), and the state it returns is written back to it field by field, the reply evaluated first. A GenServer's
`init` returning `{:ok, %{...}}` is the constructor (its argument's names the rule's params), each message of
`handle_call` (`{:reply, r, state}`) and `handle_cast` (`{:noreply, state}`) a request, its clauses on the message
and on the state one method; an Agent's public functions ending in `Agent.update` or `Agent.get` are requests over
the struct's defaults; a plain module's public functions take the state first and return it (`{:ok, s}` too,
`{:error, _}` the step's failure). A handler's tuple built by another function of the module is taken apart where it
returns. The one executor addition is `upd`, an immutable update (a copy of the record with fields set: `%{s | f: v}`,
`Map.put`, `Map.merge` with a literal).

**Patterns.** Function clauses, `case` and `cond` are chains of ifs: a clause's pattern binds its variables (a
variable, `_`, a literal, `^pin`, a map or struct by its keys, `x = pat`) and tests the rest with its guard; no clause
matching is the step's failure (Elixir's FunctionClauseError, CaseClauseError, CondClauseError), as is raise. Atoms
are choices (a handler's atom replies one choice); `div` and `rem` truncate (`trunc(a / k)` too); only nil and false
are false.

**Types.** From the module's `@type` (or `@typep`) of a map or struct with the state's fields, where it states one
(written bare, `pos_integer` parses as a variable); else from each field's default and what the module puts in it; an
argument's from the field it initializes, or from its name's use in arithmetic anywhere in the module.

**The harness.** It compiles the module from its file with its clock calls rewritten to read the request's time
(System's and `:os`'s and `:erlang`'s times, `DateTime.utc_now`, a DateTime field read and set as unix seconds),
starts it as the module does (GenServer.start with init's argument, the module's start_link for an Agent), reads and
sets the state through `:sys`, and after a failed call restores the state the call was given (a fresh process given
it, where the call crashed the old one). It reads its pipe through a `cat` port: Erlang's own reads of a pipe wait
for a full buffer.

**The corpus.** ex_break 0.0.9 (MIT, (c) 2018 Jonathan Clem): `ExBreak.Breaker`, an Agent over the breaker struct
(increment, is_tripped, reset_tripped), 4 laws proven, among them "a tripped breaker knows when it tripped", an
invariant; the check agreed on 2,715 requests. Refused, each with why: odo 0.1.0's `Odo.Bucket` (get_token divides by
a field, `div(diff, tick_duration)`, and `tick_started_at` is `:init` or a number), attempt 0.6.0's
`Attempt.Bucket.Token` (an Erlang `:queue`, a timer's message, another module's errors). hammer and ex_rated keep their
state in ETS tables (a store the front end doesn't read yet) and divide by their arguments; fuse is Erlang.

**Not yet:** ETS and `:atomics` as stores, lists and `Enum`, tuples in patterns beyond a message's, `handle_info`,
`with`, recursion, structs of other modules as arguments, a field of two types (an atom or a number).

## C and C++ (gen/c): the plan, for a fresh session

**Built (gen/c).** core/c/reader.ts (36,864 bytes of TypeScript) reads clang's JSON dump (`-Xclang -ast-dump=json
-fsyntax-only`, the project's flags or its compile_commands.json entry; the target's widths from `clang -dM -E`) and
writes the shape core/go/reader.go prints (GoPkg: a type table, typed expressions and statements), so Go's lowering in
core/extract-go.ts reads both: one lowering, C's semantics written as Go's own nodes where clang's types say so.
core/extract-c.ts (21,045) is the front end and the harness generator; `checkC` builds the harness and hands it to Go's
driver (core/extract-go-check.ts's `speak`, split out of checkGo).

- **Reading the dump.** clang writes a location's file and line only where they change, in the dump's order (an
  include chain's `includedFrom` aside): `locate` replays that order so each node knows its file. The file's own
  functions are read, and those of the project's headers (`root`, by default the file's directory: a static inline
  helper); types (typedefs, records, enums) from every file. The state is the struct named (`entry`: its typedef's name
  or its tag); a function whose first parameter points to it is a method (the receiver), a request by default where it
  is the file's and not static.
- **C as Go's nodes.** ImplicitCastExpr is the promotions and conversions (IntegralCast a conversion, a constant folded
  into the literal); a condition is a comparison with 0 or NULL, and a comparison used as a number is ?: of 1 and 0;
  stacked case labels are one case, a case that doesn't end in break or return a fallthrough; `x op= y` computed at a
  wider type is `x = (T)((C)x op y)` and ++ of a narrow type `x = (T)(x + 1)`; `x & (2^k − 1)` is x's floor remainder
  (u % 2^k for an unsigned or a non-negative sum, ((x % 2^k) + 2^k) % 2^k otherwise, two's complement); assert, abort
  and __builtin_trap are panics (glibc's assert: a discarded sizeof, __extension__, a statement expression); a struct
  initializer (a compound literal, clang's semantic form) is Go's struct literal; a pointer to an integer parameter is
  a box of one field (`*p` its field), what is left in it a result beside the returned one (a record result).
- **The executor and the lowering gained** (each for every reader, +7.5 KB shared): `ub` on an integer type (signed
  overflow refused where the bounds and the path's facts don't exclude it, "signed overflow: undefined behavior"; a
  negative value shifted left too; a conversion wraps as clang defines it), fixed-length lists (`MapDecl.len`,
  `items(kinds, lens)` in the DSL: a list of N items of 0 is length N with no cells, so a C array starts as the rule
  does; an index outside [0, N) refused; one write a step; each item's range law), stated failures (`fails:
  {take: '< 0'}`, pruned where the result's bounds and the path's facts exclude them), a panic's own text, a switch's
  join that keeps a carried case's condition (merge dropped a path whose conditions were a prefix of the other's: a
  case entered and carried into by fallthrough lost the later default; Go's switch had it too, no capture reaches it),
  and the drive skips a probe the prover can't state (a probe is only extra requests).
- **The harness** is generated C in a temporary directory: it #includes the file (main renamed), so static functions are called as they
  are, compiled with the same flags, -O0, `-fsanitize=undefined -fsanitize-trap=undefined` and
  `-fstrict-flex-arrays=3` (clang 15 and later: a fixed array last in a struct is bounds-checked), other files'
  symbols left unresolved (the rule refuses their calls). A hand-written JSON scanner, the state leaf by leaf (arrays
  whole), SIGABRT, SIGTRAP and SIGILL caught by siglongjmp (an assertion, the sanitizer's trap: the step's failure), the
  fields the rule leaves out compared by memcmp, the object restored after a failure under `onError: 'discard'`.
- **Refused, each where it is with why:** loops, goto, pointer arithmetic and indices into pointers, floats, strings,
  unions, globals and static locals, other files' and libraries' functions, function pointers, bit operations but the
  masks, division by a variable, constants past 2^53 (UINT64_MAX), the comma operator outside a statement, an
  assignment or ++ inside an expression, sizeof, bitfields.
- **Tests:** core/extract-c.test.ts (8 cases, ~15 s locally; the suite's extract-c job on Modal installs clang 19).

**The corpus** (research/langs/c/specs.ts, run.ts, rules/; research/realworld/items/c-projects.ts), each checked against
the project's own file: Ring-Buffer 8b93e1b (AndersKaloer, MIT: a 128-char ring in a fixed array, 7 functions,
dequeue and peek through out-parameters, a queue on a full buffer overwriting the oldest byte), nghttp2 1.70.0's
nghttp2_ratelim (MIT: init and drain; update refused at UINT64_MAX, and it divides by a variable), ENet 1.3.18's packet
throttle (MIT: enet_peer_throttle, ping_interval, timeout on ENetPeer, whose lists and pointers they don't touch are left
out and compared unchanged). 14 laws, all proven, the checks agreeing on 2,392–2,400 requests each. No law refuted.
Read and not taken: Tor's token_bucket and libevent's
ev_token_bucket (division by a variable; generated config headers), FreeRTOS-Plus-TCP's stream buffer (the kernel's
headers and a config), MIN's link state machine (a CRC loop, bit operations; no licence file), quicly's maxsender
(bitfields), coreMQTT's publish states (functions of no struct). No circuit or connection state machine and no
allocator's bookkeeping fit: each kept a pointer it writes through, a loop, or bit flags.

**Bars** (against 4415419, together): rw 347 / 35 / 8 against 333 / 35 / 8, nothing lost; the suite and --usual 229 of
229 each plus extract-c, job seconds level; check (lint) fixed after the bar and passing. Go 119 of 119; LiteLLM, Ruby and
Elixir rules byte-identical; build and smoke pass without clang. research/langs/c/identity.json has those jobs.

**Not yet:** bit flags (`f |= F`, `f & F` for one bit: expressible as / and % by constants), bitfields, division by a
variable (most often an overflow guard), constants past 2^53 in comparisons, coverage (clang's source-based coverage),
Go's slices' item range law (C's arrays have it; Go's output kept byte-identical).

The plan as written before it started (the session that ported Go, Ruby and Elixir ran out of room for it). Clang is local
(Apple clang 21: `clang -Xclang -ast-dump=json -fsyntax-only f.c` works; a 3-line struct and function dumps 70 KB, so
the reader must filter by the file's own `loc` and the names asked for).

**Reader** (`core/c/reader.ts`, TypeScript: C has no parser of its own to write one in): run clang's JSON dump with
the project's flags (`-I`, `-D`, `-std`; from a `compile_commands.json` where there is one), keep the translation
unit's own declarations, and lower into the IR exactly as core/extract-go.ts lowers Go: the executor already has
what C needs from Go (pointers by cases with paths, places, `writeThrough`, records by value, Go's wrap by bounds and
facts, refuseWhere). The state is a struct the functions take by pointer (`struct B *b` as the receiver), each
function named a request.

**Integers, explicit operations:** each `int` node carries its width and sign from clang's type (`unsigned`, `int`,
`uint32_t`, `size_t`: the target's sizes from `clang -dM -E`); unsigned arithmetic wraps (Go's `wrap`, at every
width); signed overflow is UB: a new mode beside `wrap`, `ub`, refused where the bounds and the path's facts don't
exclude it (the Rust `trap` logic, `past`, with the refusal "signed overflow (undefined behavior)"), never assumed;
integer promotion and the usual arithmetic conversions from clang's `ImplicitCastExpr` nodes (the dump states them);
`/` and `%` truncate (Go's `quot`/`rem`), by zero UB.

**Fixed arrays** where the index is bounded: an array field as Go's list cells (`cell` of `$item`) with a length that
is the type's; an index the path doesn't keep within `[0, n)` refused (out of bounds is UB).

**Failures:** a return code the caller states (`fails: {take: '< 0'}`, or `errno` set) is the step's refusal; assert
and abort too.

**Harness:** generated C beside the file, compiled with the same flags, reading and printing the struct's leaves as
JSON lines (core/extract-go-check.ts's generator is the model: a `main` that makes the struct, sets a state, calls a
function by name, prints the state; no JSON library: numbers and booleans only, by a hand-written scanner).

**C++** next, on the same dump: a class's members as the state, methods as requests (`this` the receiver),
`std::lock_guard<std::mutex>` as the step atomic (Go's lock, `with`), the harness generated as C++.

**Corpus candidates** (real, stateful, small): a token bucket or rate limiter in a C library, a ring buffer's head
and tail (e.g. an embedded ring buffer: `head - tail` within capacity), a connection or circuit state machine
(libuv, nginx or redis code that is a struct and functions), a small allocator's bookkeeping. Each needs its laws from
its docs or tests, and a refuted law that looks like a real bug is recorded only.

**Bars and budget:** the cheap plan (`--only suite,suite-usual,rw --together` against main), build and smoke with clang
shadowed, Go (research/langs/go-snapshot/diff.ts with the captures in ../gdp-wired-goport/runs/langs/cap/), LiteLLM
(research/langs/litellm/jobs.json on Modal), Ruby (`bun research/langs/ruby/run.ts --write`, no diff) and Elixir
(`bun research/langs/elixir/run.ts --write`, no diff) byte-identical. $10 for C and C++; stop for merge after each.

## C++ (gen/cpp)

C++ is the C reader extended (core/c/reader.ts, +12,256 bytes) and the C harness generated as C++ (core/extract-c.ts,
+3,426; `extractCpp`, `gdp-wired/extract-cpp`), on Go's lowering (+2,110: the constructor, a mutex of another language)
and driver (+853: the constructor's arguments, a natural sort kept in drawn values): +18,645 bytes in all, no new reader.

- **The dump.** A C++ file's standard headers make a dump of hundreds of MB (281 MB for <mutex> and <array>): clang
  dumps only the declarations named after the class (`-ast-dump-filter`), one after another, its locations' state
  going on from each to the next, so `locate` reads them as one translation unit (73 KB). Free functions and types the
  class doesn't nest are not in it (a call of one is other code); `-std=c++17` where the project's flags name none.
- **The class.** Its methods (in the class or out of line, by their declaration's context) are functions whose
  receiver is `this` (CXXThisExpr a pointer to the object, an implicit member access a field through it); a member
  call of the class's own method is Go's method call (`obj.m()` through obj's address); the public non-static ones are
  the requests. An overloaded or virtual method, another class's method, a static method, an operator but std::array's
  `[]` are refused where they are called.
- **The constructor** is run once, from the zeroed object: its member initializers, each field's in-class one where
  it has no other, then its body; where it leaves each leaf is the rule's start, its parameters the rule's
  (`.params`, their types' ranges the precondition). One that can fail, or writes an array, is refused; so is a class
  with two constructors.
- **What else maps onto C's and Go's:** std::array<T, N> is a fixed array (`size()` its length); a reference to an
  integer parameter is an out-parameter (C's box); std::min and std::max are Go's; `throw` is a panic (the step's
  refusal); std::lock_guard, std::scoped_lock and std::unique_lock of a member std::mutex in the method's own block are
  Go's Lock with its deferred Unlock (the step atomic); a scoped enum is its underlying integer.
- **The harness** is the C one compiled as C++ with clang++: the object made in zeroed memory by its constructor with
  the rule's parameters (`new (calloc(...)) T(args)`), private members read and set through pointers to members taken
  in an explicit instantiation (where access isn't checked: `template struct gdp_rob<gdp_tagN, &T::m>`), the state
  snapshot as bytes (a class with a mutex can't be copied), an exception caught as the step's failure, the mutexes not
  compared.
- **Fixed on the way (C's too):** a constant converted to a 64-bit type was folded in doubles (2^64 + 1 is 2^64: an
  index `a[1]` of a std::array, size_t, read as 0); now exactly. The committed C rules re-extract unchanged.
- **Refused:** class templates (and templates generally), virtual dispatch, STL containers but std::array, lambdas,
  try and catch, a reference held in a local, std::atomic and std::chrono (types outside the subset).
- **Also read:** a const reference to an integer is its value; a class named with its namespaces (`this`'s type gives
  the harness its qualified name); the standard's fixed-width names without their typedefs (a filtered dump has none)
  and an integer typedef met desugared elsewhere; `std::numeric_limits<T>::max()` and `min()` folded; an overloaded
  method picked by its arity (`functions: ['throttle/1']`: the other overloads refused where they are called); a
  scalar's braces (`T x{0}`). A signed leaf the caller states is a natural (`domains`) gets its range law from 0, and
  the drive draws it at 0 or above (Go's `domains` had the same gap in its drawn values).

**The C++ corpus** (research/langs/c/specs.ts, `cpp: true`; each project's files fetched one by one at the pin, a header
that would bring its build system stood in for by `shims`, types and macros only, named in `reads`):
libtorrent 2.1.2's `aux::bandwidth_channel` (BSD-3-Clause: the token bucket under its rate limits; throttle(int),
update_quota, use_quota, return_quota, quota_left; libtorrent/assert.hpp as assert; m_limit and the milliseconds stated
naturals, as its asserts and their meaning say) and PX4-Autopilot 1.17.0's `systemlib::Hysteresis` (BSD-3-Clause: the
debounced boolean of its checks; its constructor, the four methods; drivers/drv_hrt.h as hrt_abstime = uint64_t).
10 of 11 laws proven, each check agreeing on about 2,300 requests, 400 drawn states and 32–39 witnesses.

**Bars** (against 52152a3, together): rw 357 / 35 / 9 against 347 / 35 / 8 (the 10 proven, the cap law unknown),
nothing lost, wrong 0; the suite and --usual 230 of 230 each, job seconds level (+32 s, +7 s); lint clean. Go 119 of 119;
LiteLLM, Ruby and Elixir rules and the five C and C++ corpus rules (Linux, clang 19) byte-identical; build and smoke pass
without clang.

**Triage (recorded only, no one contacted):** "an update keeps at most 3 seconds of quota" (inferred from update_quota's
`if (m_quota_left / 3 > m_limit) m_quota_left = m_limit * 3`) is refuted: where the addition would pass INT32_MAX the
overflow guard sets the quota to INT32_MAX, past 3·m_limit. Concretely, on the real code (compiled and run): throttle
(714,396,227), update_quota(3000) fills it to 2,143,188,681 (3·m_limit), and update_quota(7) leaves 2,147,483,647, 4.3 MB
over. (The prover's own witness took the product m_limit·dt as a free value, so the corpus's scoring counts the law
unknown, not refuted; run.ts prints the witness.) The guard is intentional
(the comment: "may exceed <int>::max"), and past about 715 MB/s three seconds don't fit an int at all: an edge of the
cap, not a bug in practice.

**Not fitting, each with why** (the candidates' search): no permissively licensed circuit breaker reads (brpc's,
mod_pagespeed's, Envoy's: atomics, doubles, a clock read inside; helixscreen's ControlBreaker fits but is GPL-3.0), no ring
buffer class (Fuchsia's console Fifo: its constructor takes a zx::eventpair, its byte methods private; ot-br-posix's
queue: memcpy into a void*; tenbox's and Arduino's: GPL and LGPL); WebRTC's IntervalBudget (two constructors, a function
of another file in the same .cc).


## The boundary inferred (gen/boundary)

**The API, as shipped (additive; for a front end on gen/jvm after its rebase).**
- Options (`StepOptions`): `entry` is optional (none: the module's one class whose public methods write its state, and
  those methods); `strict?: boolean` restores the boundary only as stated. `answers`, `skip` and `stores` are unchanged
  and win over anything inferred.
- What a reader may add to the IR, each optional: `ret: SType` on an `ext` node (the callee's declared result), `rets`
  on a record (its methods' results, another module's class's too), `kinds: ['protocol']` (an interface, a protocol, a
  trait), `inject: true` on a parameter or a record's field (Spring's `@Autowired`/`@Inject`, FastAPI's `Depends`), `ext:
  <name>` on a `no` node for a call of other code it doesn't lower (with its `args` and `recv` lowered, or the `names`
  its arguments mention), `names` on any `no` node, `stubs: false` on the module (its check can't stub a call), and
  decorators or annotations named `gdp.skip` / `GdpSkip` / `gdp_skip` (and `answer`, `strict`).
- Exported from core/extract-step.ts: `Inferred`, `entryNames`, `assumed(x, request)` (what a refutation assumes of the
  inferred answers: "assumes `get_current_spend` may return -1 (inferred: any float)"), `new Stepper(mod, opts, inf)` and
  `stepper.promote(refusal)` for a front end with its own driver (Go's `readGo` loops on them).
- The harness protocol gained `patch.store` (an injected dependency's method stubbed on the object the check gives),
  `how` on an answer (`inferred`, `tagged`), and `inject` in `hello` (fields set to a store after the constructor).
- In the code: `# gdp: skip`, `# gdp: answer [type]`, `# gdp: strict` (or `//`, `--`, `%`) on a call's line state that
  call; on a function's line or the line above it, every call of it.

**What is inferred.** The executor already kept a value of other code "only where nothing reads it". Reading is now
the boundary's test, over runs of one reading (`readStep`, Go's `readGo`): each call of code the subset doesn't read is
left out (an opaque value that remembers its call); a run refused where such a value is read adds the call as an
answer, and the next run starts again. A refusal it can't use is the reading's, with the statement that accepts it.
- *Skip*: a call whose value nothing the rule keeps reads (a logger, an alert, an error's message, an object of another
  module made and passed on, a context manager's call, a decorator of other code taken as transparent). The check runs
  it as it is: one that raises, writes the state or changes the step's result is a disagreement, and the rule refused.
- *Answer*: a call whose value is read becomes an input over its declared result type: the reader takes it from the
  annotation (Python reads the repository's modules for it, through re-exports: `get_current_spend -> float`), a
  method's from its class (`rets`). This over-approximates the callee, so a proof holds of the code; a refutation may
  be the callee's impossibility, so `assumed` names what it assumes. Where no type is declared (untyped Python, Ruby) or
  the type isn't one an answer takes (a record, a list), it is not guessed: the refusal says where the value is read
  and prints the option or the comment that states it. Where the check can't stub a call (Rust, Ruby, Elixir, Go and
  C: `stubs: false`), an answer is refused the same way; their skips are inferred.
- *Own code the subset can't read*: a function of the module whose body is refused (a loop, try/except, a dict read
  the subset doesn't take) is taken as other code where it is called: the innermost one around the refusal, never an
  entry or the constructor, and only where it writes none of the rule's state. That is decided from the IR alone
  (`writesState`): a write through a parameter holding the state (or a local aliasing it), a method called on one, other
  code given one, or a node the subset doesn't read that mentions one (readers say which names a `no` node mentions);
  the module's functions it calls are read the same way. An answered function is stubbed by the check, so this test,
  not the check, is what makes it sound; a skipped one runs as it is.
- *Injected dependencies*: a constructor argument marked so, or one of another module's class, a protocol, or no type,
  that the class keeps in a field and calls methods on, is held as a store: a method named as a key's get, set or delete
  (`get`, `find`, `findById`, `put`, `save`, `delete`, `remove`, with `async_` and `_cache` forms) given a key that is a
  string or a format reads and writes a map of the state, one per key template (as a stated store's); its other methods
  are answers (their class's declared results) or skips. Of a dependency the class reads by a key, another method may
  change what it holds, so it is refused unless stated. An attribute of it the rule reads (`dual_cache.redis_cache`) is
  a modelling choice no type decides: refused with the `attrs` that state it. Effect services (core/effect.ts) were
  already read so.
- *Still refused*: other code given a reference to the rule's state (the object, its nested objects, maps, lists, a
  store), which may change it, unless the caller states it (`skip`, or `# gdp: skip` on the line); and everything the
  subset refused before that isn't a call.
- *Entries*: with no `entry`, the module's one class whose public methods write its state (by `writesState`), and those
  methods (the others only read it); several or none are refused, naming them. Python's reader, asked for no names,
  lists the module's classes; the other readers still need the entry.

Every inferred statement is a note (`left out (inferred: nothing the rule keeps reads its value)`, `answered by the
request (inferred: its value is read; assumes X may return any float)`, `an injected dependency (inferred: ...)`,
`the module's own code, outside the subset (...), and writing none of the rule's state: taken as other code`), and the
check runs both the code and the rule as for a stated one: a skip by running the call, an answer by stubbing it.

**Measured: every extraction that stated a boundary, stated nothing.** Two in the tests (core/extract-py.test.ts) and
LiteLLM's seven (research/langs/litellm, `run.ts --bare`: no answers, skip or stores, but each item's `needs`), checked
on Modal against LiteLLM v1.106.6 installed. No other language's tests, examples or corpus state a boundary (Rust, Ruby
and Elixir refused `answers` and `stores`; Ruby's stoplight states `clocks`, which is not one), and research/realworld
scores the committed LiteLLM rules.

| Extraction | Language | Stated before | With nothing stated | Rule | Verdicts |
| --- | --- | --- | --- | --- | --- |
| SessionLimit (tests) | Python | `stores: {cache: {get, set, value: 'int'}}` | the same (cache an injected store) | byte for byte | its 2 laws proven, as before |
| gate (tests) | Python | `answers: {spend_of: 'float'}, skip: ['log']` | needs a tag: `spend_of` is a stand-in that raises, read as it is unless `# gdp: answer` on its def | with the tag, byte for byte (but its header's file name) | (no laws) |
| virtual_key_max_budget_check | Python | answers 2, skip 4 | the same | byte for byte | 3 proven |
| team_max_budget_check | Python | answers 1, skip 4 | the same | byte for byte | 2 proven, 1 refuted |
| _project_max_budget_check | Python | answers 1, skip 4 | the same | byte for byte | 3 proven |
| check_end_user_budget | Python | answers 2, skip 4 | the same | byte for byte | 2 proven, 1 refuted |
| MaxIterationsHandler | Python | answers 2, skip 6, a store | needs a tag: Redis off (`attrs: {'dual_cache.redis_cache': null}`); the rest inferred | byte for byte | 4 proven |
| MaxBudgetPerSessionHandler | Python | answers 2, skip 6, a store | needs a tag: Redis off, as above | byte for byte | 2 proven |
| should_cooldown_based_on_allowed_fails_policy | Python | answers 2 | needs a tag: `Router.get_allowed_fails_from_policy` declares no result (`answers: {get_allowed_fails_from_policy: 'int | None'}`); `_increment_allowed_fails` (own code, a try) inferred | byte for byte | 3 proven |

So 5 of 9 the same with nothing stated, 4 need one statement each (one a stand-in, two a modelling choice, one an
untyped result): 45 stated names down to 4. Every rule is byte for byte the stated one's, and every verdict is:
LiteLLM's 21 laws 19 proven and 2 refuted, as at the pin; the stated runs reprinted the committed rules unchanged. The
two refutations (a team, and an end user, whose spend equals the max_budget are admitted) now read `assumes
\`get_current_spend\` may return -1 (inferred: any float)` (the end user's -2, with max_budget the same): they are the
code's `>` against `>=`, not the boundary's, since a spend equal to the budget is one the counter returns.

**The other languages, on the same executor.** Rust's reader already wrote other code as `ext`: its skips are inferred.
Ruby's and Elixir's readers mark another class's or module's call (`ext`, the names it mentions; Elixir's are values it
can't change). Go's lowering marks another package's function and method and a call of a function value, its object
and arguments lowered, and `readGo` loops on `promote`: of the 119 captured readings, 115 are byte for byte the same and
the 4 that differ were refusals, 3 still refused (with the call that made the value read and why it can't be answered)
and one now read (`context.WithTimeout`'s context and cancel, read by nothing the rule keeps). C and C++ stay as they
were: their harness links only the file's own code, so a call of another file can't run as it is.

**Bytes.** core/ and kernel/ in TypeScript, tests excluded, against 5ac6467: +31,432 (core/extract-step.ts +29,324, the
inference itself: the boundary's decision, the state-reference and write tests, the tags, promotion, injected stores,
the entry; core/extract-go.ts +1,407, its marks and loop; the front ends +701, most of it extract-py.ts's header). The
readers in their own languages: +1,989 Python, +536 Ruby, +164 Elixir; the Python harness +371. The kernel is unchanged.

**Validation.** On Modal: LiteLLM stated and bare (one job, 365 s: the stated run reprints the committed rules, the
bare run prints them byte for byte, every verdict the same); the Go, Rust and C tests (19, 3 and 10 pass); the Rust, C
and C++, Ruby and Elixir corpus rules re-extracted byte for byte. Locally: the Python, Ruby and Elixir tests, Go's 119
captured readings (research/langs/go-snapshot/diff.ts: 115 the same, the 4 above).

**Bar** (quick, `--only rw,f1,f2,g332,suite,onecpu`, against the cached baseline of 5d4da3f, the nearest base with one:
5ac6467 has none, and making it costs more than this task's budget; main's changes since were barred clean against it):
f1 34 / 35 and f2 24 / 33 proven, rw 74 / 14 / 3, g332 332 of 332 with the same search, each 0 differing; the suite 230
of 230 (the base's 227 jobs, 3 added since); onecpu no failure; $0.58 estimated.

## Java and Kotlin (gen/jvm)

One JVM structure for both languages: a reader per language on its own parser, one shared layer both lower through,
one reflective harness, one front end (core/extract-jvm.ts: `extractJava`, `extractKotlin`, `gdp-wired/extract-java`
and `gdp-wired/extract-kotlin`).

| Piece | Where | Bytes | What |
| --- | --- | --- | --- |
| the JVM layer | `core/jvm/Jvm.java` | 27,820 | JSON; one canonical name per JVM type (Kotlin's `Int` is Java's `int`, its `Int?` an `Integer` that may be null); each type's SType; the library's calls lowered alike from either reader (maps, Optional, the atomics, Math, TimeUnit, the clock, the checks that throw); the boundary's metadata (annotations, DI, `// gdp:` tags) |
| Java reader | `core/jvm/JavaReader.java` | 59,123 | javac's tree API (`com.sun.source`, `JavacTask.analyze()` against `-sourcepath` and the classpath): every expression's type is javac's, attributed even where other parts of the file don't compile |
| Kotlin reader | `core/jvm/KtReader.java` | 72,145 | the Kotlin compiler's PSI (`KtPsiFactory` over a `KotlinCoreEnvironment`, from the kotlinc installed): syntax, the types from the code's declarations, a local's from its initializer, an expression's from its parts; other files of the package indexed for their classes and enums |
| harness | `core/jvm/Harness.java`, `core/jvm/Rt.java` | 24,645 + 538 | reflective, for both: loads the class (compiled from the file, or the project's own jar), makes it, sets and reads leaves through fields, atomics, Optional, maps (the map the object has), stores; stubs answered calls |
| front end | `core/extract-jvm.ts` | 15,917 | builds the tools once per version (javac into the tmpdir), runs the reader, compiles the code for the check (javac, or kotlinc's K2JVMCompiler) with the clock's and the answered calls' sites rewritten to `gdp.Rt` |

**Why the Kotlin reader is Java on the compiler's PSI.** The PSI is Kotlin's own parser (the one kotlinc and the IDE
use); kotlin-compiler.jar is in every kotlinc distribution's `lib/`. Written in Java, the reader shares Jvm.java with the
Java reader (one lowering of the library, one type model) and needs no Kotlin build step: javac compiles it once against
the jar (0.3 s to parse a file). Kotlin's analysis API (K2's resolved types) would give every expression's type, but it
is unstable across releases and heavy; the PSI is stable (one API change between 2.1 and 2.4, an extension storage, met
reflectively) and Kotlin states the types that matter (a property's, a parameter's, a function's result). Where a type
can't be read off the code, the value is opaque and refused where a step reads it, never guessed.

**What a user installs.** A JDK 17 or later (`javac` on the PATH or `$JAVA_HOME`; jobs here use Temurin 21) for both;
for Kotlin also kotlinc (Homebrew's `kotlin`, SDKMAN's, or the GitHub release zip: `$KOTLIN_HOME`, or `kotlinc` on the
PATH; 2.4.21 here). Nothing at all for the rule printed. Without them the front ends refuse ("a JDK 17 or later is
needed", "kotlinc ... is needed to extract Kotlin"), never throw; scripts/smoke.sh checks it.
research/langs/jvm/jvm-setup.sh installs both in a Modal container.

**The subset, as the shared IR's operations.**
- classes with fields as the state (a static nested one too; their superclasses of the code's own sources merged in);
  the one constructor (or `ctor: n`, its arity) as `__init__`: `super(...)` inlined, then the fields' defaults and
  initializers in order, then its body; Kotlin's primary constructor's `val`/`var` parameters, its property initializers
  and `init` blocks in order. Its arguments are the rule's params. Methods are requests; a Kotlin computed property is
  one too (`unacknowledged`, the harness calling `getUnacknowledged`); an `internal` one is found by its mangled name.
- `int`, `long`, `short`, `byte`, `char` (Kotlin's `Int`, `Long`, ...) as fixed widths with Java's wraparound: binary
  promotion as `as` on each operand, a compound assignment's implicit narrowing a `conv`; `Math.addExact`,
  `subtractExact`, `multiplyExact`, `incrementExact`, `toIntExact` trap (an ArithmeticException: the step's failure);
  `/` and `%` truncate by a constant; `Math.min`/`max`/`abs` (abs of MIN_VALUE is MIN_VALUE), `floorDiv`, `floorMod`,
  `clamp`, Kotlin's `coerceAtLeast`/`AtMost`/`In`, `minOf`/`maxOf`; floats at whole values, a float argument within
  ±2^24 (its exact integers: the harness refuses to give one past them, as the rule does), a float cast to an int
  saturating as Java's does.
- booleans, strings set and compared, enums (Java's, Kotlin's, TimeUnit) as choices; TimeUnit's `toMillis` and the rest
  as the unit's factor, truncated.
- records: Java records, Kotlin data classes, plain classes whose one constructor sets their fields from its arguments
  in order, Lombok's `@Value`/`@Data`/`@Getter` (getters read as the fields); a data class's `copy(f = v)` is an update.
- `Map`, `HashMap`, `ConcurrentHashMap`, Kotlin's `mutableMapOf`/`HashMap()` as maps: `get`, `getOrDefault`,
  `containsKey`, `put` (a statement: one key written; a value: Rust's insert, the old value), `remove`, Kotlin's `m[k]`,
  `m[k] = v`, `k in m`, `getValue`.
- `Optional` (`empty`, `of`, `ofNullable`, `isPresent`, `isEmpty`, `get`/`orElseThrow`, `orElse`) and Kotlin's nullable
  types (`?:` with a value, a `return` or a `throw`, `!!`, `?.` and `?.let { }`, `== null` and its smart cast,
  `checkNotNull`, `requireNotNull`) as options; a Java reference field may be null where the class says so (`@Nullable`,
  null assigned to it, or no initializer the constructors all set).
- exceptions as failures: `throw`, Guava's `checkArgument`/`checkState`, `Objects.requireNonNull`, Kotlin's `check`,
  `require`, `error`, `TODO`; `assert` is off, as the JVM runs by default.
- `synchronized` (a method or a block), `@Synchronized`, a `ReentrantLock`'s `lock(); try { ... } finally { unlock(); }`,
  `synchronized(x) { }` and `withLock { }` make the step atomic.
- the atomics (`AtomicInteger`, `AtomicLong`, `AtomicBoolean`, `AtomicReference`, kotlinx's `atomic()`) as the fields
  they hold: `get`/`set`, `getAndSet`, the increments and adds, `compareAndSet`; a `while (true)` / `for (;;)` /
  `do ... while (true)` compare-and-set loop is read as its first pass (a block `break` leaves; a pass that would go
  around again is refused where it is reached), which is the claim for calls that don't interleave.
- `switch` (a statement, arrows or colons) and `when` as chains of ifs on `==` inside a block a `break` leaves, each
  case's arm its statements and those it falls through into; `is` decided where the type is the class read or a parent;
  `in a..b`; if and when used as a value pushed into their branches where they return.
- Kotlin's scope functions (`let`, `also`, `takeIf`, `takeUnless`) inlined, their statements before the expression.
- an immutable class's method that returns its next value (a data class's `copy`, `this`: Arrow's
  `trackFailure(): OpeningStrategy`) is a step to it: each return writes the fields, the harness keeps the object
  returned.
- `System.currentTimeMillis()`, `nanoTime()`, a `Clock`'s `millis()` as the request's time (the check's copy calls
  `gdp.Rt.now()`).
- Refused, each where it is with why: other loops, `continue`, try/catch (but a lock's finally), lambdas other than the
  scope functions', arrays and other collections, `instanceof`, static fields that aren't constants, inner classes,
  generic classes and methods, a switch or when expression as a value inside an expression, Kotlin's `run`/`apply`.

**The executor gained** (each shared): a start's quotient of the params (`threshold = maxTokens / 2`) is a param of its
own, which the precondition fixes (k·q ≤ a < k·q + k) and the check computes from the others (the kernel's starts read
the params alone: gRPC's Throttle couldn't be read without it); what the constructor refuses (a narrowing cast's value
that doesn't fit) is the precondition's, not a step's refusal; an answered call whose callee declares a fixed-width
result (`ity` on the call) is an input within it, where it is read; Java and Kotlin named in the notes. The printer: a
signed field the printer reads as a natural keeps only its range's top (a range law of `maxFailures: Int` that `init`
keeps at 0 or above didn't build); a recursion guard in `nonneg` (a wrapped sum in a refusal's atom asked for its own
facts forever); `int.from(({n}) => n.times(2))` typechecks (dsl.ts's `from` took a callback of `never`). The shared changes are
3,194 bytes; with the front end, core/ in TypeScript (tests excluded) is +19,111 bytes against d2e157a (extract-jvm.ts
15,917; extract-step.ts +2,066; extract.ts +370; extract-check.ts +309; dsl.ts +234; extract-print.ts +215).

**The boundary (adopted after gen/boundary landed).** The readers emit what the inference reads: other code's types as
records (`own: false`; an interface `kinds: ['protocol']`; its methods' declared results `rets`, from javac's elements
or the Kotlin file's interfaces or reflection), `ret` on an `ext` node (a static call's declared result), a method of
an object of other code called on it (`self.f.m(...)`, so a constructor-injected interface is read as a store),
`inject` on a field or a parameter annotated `@Autowired`, `@Inject` or `@Resource` (an injected field's default null
isn't the constructor's), `@GdpSkip`/`@GdpAnswer("int")`/`@GdpStrict` as a method's decorators, and `// gdp:` comments
(the executor's own). With no entry the readers list the file's classes and the executor takes the one whose public
methods write its state. The harness stubs answered calls: an injected dependency of an interface type is a
`java.lang.reflect.Proxy` keeping what its get/set/delete store and answering its other methods from the request (a
stored value outside its getter's type refused, as a drawn state the code can't hold), a field the framework injects is
set to one after the constructor, and any other answered call's site is rewritten to `gdp.Rt.answer(key, type)` in the
check's copy (so `stubs` is false only for `prebuilt`). Field injection's first test is here (core/extract-jvm.test.ts:
Spring's `@Autowired` on a field, Java and Kotlin `lateinit`), with a constructor-injected interface whose call is an
inferred answer and the entry inferred.

**The corpus** (research/langs/jvm/specs.ts, run.ts, rules/; research/realworld/items/jvm-projects.ts), each checked
against the project's own code:

| Item | Language | Code | Checked against | Requests (start / drawn / witness) | Laws |
| --- | --- | --- | --- | --- | --- |
| grpc-java 1.85.1 `RetriableStream.Throttle` (Apache-2.0) | Java | the retry throttle's token count: compare-and-set loops on an AtomicInteger, Math.max/min, a float constructor | grpc-core-1.85.1.jar (`prebuilt`) | 1,164 / 400 / 14 | 4 proven, 1 refuted |
| resilience4j 2.4.0 `PartialAggregation` (Apache-2.0) | Java | a sliding window's bucket: a switch on Metrics.Outcome that falls through, int counts, `TimeUnit.toMillis`, its superclass AbstractAggregation | the package compiled by javac | 2,092 / 400 / 30 | 5 proven, 1 refuted |
| OkHttp 5.5.1 `WindowCounter` (Apache-2.0) | Kotlin | HTTP/2 flow control: `@Synchronized`, `check`, Long counts, a computed property, `failures: 'kept'` | the file compiled by kotlinc | 1,916 / 400 / 10 | 4 proven, 1 refuted |
| Arrow 2.3.0.1 `CircuitBreaker.OpeningStrategy.Count` (Apache-2.0) | Kotlin | an immutable data class's steps (`copy`), `init { takeIf ... let ... requireNotNull }`, `when (this) { is Count -> }`, internal methods | arrow-resilience-jvm-2.3.0.1.jar (`prebuilt`) | 996 / 400 / 6 | 4 proven |

20 laws: 17 proven, 3 refuted. The three (research/realworld/triage/jvm.json, recorded only, no one contacted):
- **gRPC, suspected bug (a configuration's edge).** "The token_count will always be between 0 and maxTokens" is refuted:
  ServiceConfigUtil checks only maxTokens > 0, and at 2,147,484 tokens or more maxTokens (1000 times them, cast to int)
  saturates at MAX_VALUE; one qualified failure then one success overflow `currentCount + tokenRatio`, and the count goes
  negative (then the next failure's `- 1000` wraps it back to MAX_VALUE). On the release's jar:
  research/realworld/repro/grpc-throttle-overflow.sh prints `after a success: -2147482649`. Within ServiceConfig-sized
  bounds the invariant is proven.
- **OkHttp, suspected bug (minor).** "no more is acknowledged than consumed" is refuted: `update` adds both arguments
  before its last `check(this.acknowledged <= this.total)`, so an update acknowledging more than was consumed throws and
  leaves the counter holding it (repro: `total=0, acknowledged=3, unacknowledged=-3`). Its two argument checks come
  before the writes; the last doesn't.
- **resilience4j, a law stated without the wraparound.** "slow failed calls never outnumber slow calls" breaks only
  past 2^31 slow calls in one epoch second's bucket; kept as a false law the prover must not prove.

Read and not taken: Ktor's DefaultRateLimiter (a suspend `tryConsume` reading its clock lambda several times a step,
atomicfu, a sealed State result, a Duration), Arrow's CircuitBreaker itself (an Atomic of a sealed state with
CompletableDeferreds), resilience4j's AtomicRateLimiter and Eureka's RateLimiter (each divides by a field), Bucket4j's
state (long arrays), Failsafe's CountingCircuitStats (a BitSet), Guava's SmoothRateLimiter (doubles divided).

**Tests:** core/extract-jvm.test.ts, 13 cases (8 Java, 5 Kotlin), each compiling and running the code it reads; skipped
where no JDK or kotlinc is installed; the suite's `extract-jvm` job installs both.

**Not yet:** branch coverage (the arms aren't counted: no instrumentation), `stores` stated by the caller (inferred
ones work), loops beyond a CAS's first pass, a Kotlin expression's type the code doesn't state through a call of other
code that isn't on the reader's classpath, sealed classes as choices, Duration, suspend functions that suspend, top-level
functions as entries.

**Validation** (on Modal, research/langs/jvm/jobs.json, 8 jobs, 368 s wall): the JVM tests 13 of 13 on Linux (Temurin
21, Kotlin 2.4.21); the four corpus rules re-extracted byte for byte; build and smoke without a JDK (the front ends
refuse); the C and C++, Rust, Ruby and Elixir corpus rules and LiteLLM's seven (v1.106.6 installed) re-extracted byte
for byte, so the shared changes leave every other language's rules as they were.

**Bar** (quick, `--only rw,f1,f2,g332,suite,onecpu`, against the cached baseline of 5d4da3f, the one cached: d2e157a
has none): f1 34 / 35 and f2 24 / 33 proven, rw 74 / 14 / 3, g332 332 of 332 with the same search, each 0 differing;
the suite 231 of 231 (extract-jvm 13 pass among them, tsc and lint clean); onecpu no failure; $0.57 estimated
(runs/bar/runs/9868500d5293-vs-5d4da3f49013-quick-2026-10-300347).

## The boundary inferred in every language (gen/boundary2)

**The stub protocol, one for every check.** An answered call (stated, tagged or inferred) is a stub point named by the
callee's qualified name (`Answer.key`: `litellm.proxy.proxy_server.get_current_spend`, `unicode/utf8.RuneCountInString`,
`std::process::id`, `quota_bonus`), and each request carries `answers: {<name>: {in: v} | {none: true}}`. A harness
reads its stub point's value from there, by the name, whatever stubs it: Python `stub(key)`, Ruby `answer(key)`, Elixir
`GdpAnswer.a(key)`, Rust `crate::__gdp_answer(key)`, Go `gdpAnswer[T](key, callee, args...)`, C and C++
`gdp_answer(key)`, the JVM's `gdp.Rt.answer(key, T)` (gen/jvm), TypeScript's module stub's export. A later opt-in macro
can target the same points. What reaches the point is the language's own mechanism, the slimmer of two:

| Language | How an answered call reaches its stub point | Stores (injected dependencies) |
| --- | --- | --- |
| Python | reflection: the callee's attribute set (`patch` by module and path, or on the object) | yes: a store object the check gives |
| Ruby | reflection: a module prepended to the callee's class, as the clock's is | yes: the same, in Ruby |
| Elixir | the module's AST rewritten as the harness compiles it: `Mod.f(...)` becomes the stub (another module can't be swapped where it is the standard library's) | no (state is a value) |
| TypeScript | the sandbox's module for the import: a Proxy whose exports answer, or do nothing | no |
| Rust | the crate's copy, each answered call's text (the reader's position to its end) replaced by the stub | no |
| Go | an overlay (`go build -overlay`) of the package's file with each answered call replaced; the callee and its arguments still evaluated, so its imports stay used | no |
| C, C++ | the copy of the file the harness includes, each answered call replaced (`-iquote` the original directory) | no |
| Java, Kotlin | the compiled copy (gen/jvm) | yes: a proxy of the interface |

The rewriting is shared (core/extract-step.ts `stubbed`: the answers' sites, by `line:col` from the reader's position
to the end it gives, or by offsets); each reader gained a call's end (Rust's syn spans, Go's `ast.Node.End`, clang's last
token). The user's code is never touched: the copies live in the check's temporary directory. A Go copy is built without
`-cover` (cover reads the files as they are), so its arms are not counted; a C file's call of another file left out
still links against a stub that reports itself (the file is linked alone), so such a skip is a refusal of the check.

**What every reader gained.** The entry inferred (no names: Ruby's reader lists the file's classes, Rust's the crate's
structs, Elixir's the file's one module or its GenServer or Agent, Go's `readGo` the package's structs, C's front end
the dump's structs; C++'s dump needs the class named); `gdp:` comments read in the file a position names (resolved
against the module's root and path); a call of other code marked (`ext`, its `patch` by name, its result's type where the
language states one: Go's and C's types make their answers inferred; Ruby, Elixir and Rust state none, so theirs are
tagged, `# gdp: answer int`, `// gdp: answer u32`). An answer of a fixed width is typed (`u32`, `int64`): the request is
within it, and the check treats a drawn value outside it as outside what it compares. Rust, Ruby and Elixir now take
`answers` and (Ruby) `stores` as options too.

**TypeScript: the same behaviour, not the shared executor.** Its executor (core/extract-read.ts) already had the boundary
for a class's injected functions (`fnFields`: a call's answer an input over the checker's type, a call returning nothing
left out, a compound result refused). A call of another module's function from a class now goes through it
(`import:<module>:<name>`), and the check gives the sandbox that module as a Proxy whose exports answer by that name.
That is about 2.5 KB; moving TypeScript onto the shared executor would mean a second reader for TypeScript's AST into the
step IR (its own executor is 98 KB), for the same behaviour. `strict: true` refuses as before.

**FastAPI's Depends** is exercised by a real dependency (core/extract-py.test.ts: a rate limiter whose cache is
`Depends(get_cache)`, held as a store; the suite's extract-py job installs fastapi). Spring's field `@Autowired` is
gen/jvm's.

**Measured.** The nine extractions of the first round, rerun with nothing stated on the round's code: the same as before
(5 the same, 4 needing one statement, every rule byte for byte, LiteLLM's 19 proven and 2 refuted). Real code that calls
other code, per language:

| Language | Extraction | With nothing stated |
| --- | --- | --- |
| Python | LiteLLM's 7 (v1.106.6) | 4 the same, 3 need one statement (above) |
| Ruby | stoplight 6.0.0's `Memory::Storage::State`, its injected clock | needs a tag: the clock is inferred an injected dependency, but Ruby states no type for `current_time`, so `clocks: ['clock']` stays |
| Java, Kotlin | gen/jvm's corpus (gRPC's Throttle, resilience4j, OkHttp, Arrow) | gen/jvm's |
| Rust, Elixir, Go, C, C++, TypeScript | no real code of the corpora calls other code (each corpus was chosen among what the subset read); each language's tests extract code that does (a call left out, one answered, the entry) | not measured on real code |

The corpora (Rust, C and C++, Ruby, Elixir, Java and Kotlin) re-extract byte for byte; Go's 119 captured readings: 115
the same, the 4 that differ as in the first round (the captured JSON predates a call's end, so nothing there can be
answered); read by today's reader, `strings.ToUpper`'s is answered over its `string` (core/extract-go.test.ts).

**Bytes.** core/ and kernel/ in TypeScript, tests excluded, against 38b998a (gen/jvm on this branch's base): +14,280. The
harnesses' stub points and the copies they build are most of it: Go's lowering, driver and harness +4,678, C's front end
and reader +2,630, the TypeScript front end and its check +2,226, Rust's +1,304. core/extract-step.ts +3,738 (the shared
rewrite `stubbed`, a file's text by a position's name, typed answers, the `no` node's stated answers and skips); one IR
visitor for its scans and its callFree and foreign took about 1 KB back. Against 5ac6467, core/extract-step.ts is
+35,128 in all (the first round's +29,324, gen/jvm's +2,066, this round's). The readers and harnesses in their own
languages: Ruby +2,844, Elixir +1,225, Rust +568, Go +201. The kernel is unchanged.

**Validation** (Modal): every front end's tests (TypeScript 50, Python 10 with fastapi, Rust 4, Ruby 4, Elixir 4, C and
C++ 11, Go 20, Java and Kotlin 13); the Rust, C and C++, Ruby, Elixir, Java and Kotlin corpus rules re-extracted byte
for byte; LiteLLM stated (the committed rules reprinted) and bare (7 of 7 byte for byte, the same verdicts); the build
and smoke without the languages. Locally: Go's captured readings (above).

**Bar** (quick, `--only rw,f1,f2,g332,suite,onecpu`, against the cached baseline of 5d4da3f again: neither 5ac6467 nor
38b998a has one, and making one costs more than the round's budget): f1 34 / 35, f2 25 / 33 (one task solved by the
candidate alone in the first pass, noise after three reruns a side: gained 0, lost 0), rw 74 / 14 / 3, g332 332 of 332,
each 0 differing; the suite 231 of 231 (the base's 227 jobs, 4 added since); onecpu no failure; $0.59 estimated.

## The boundary's state references, closed (gen/boundary3)

An adversarial round against c57c8ee (research/langs/adversarial/: RESULTS.md, the 25 cases and their repros) found
three checked proofs that are false and one accepted mismatch, all through injected dependencies:
- j03 and j01: an injected listener handed `this` (answered, or left out). A dependency's call went to `storeCall`,
  which dropped its arguments before the state-reference test `boundary` makes for other code.
- j04: a store's `get` given `this` beside its key. The op was modeled by its key alone, and the JVM's proxy ignored
  the rest.
- p12: two injected dependencies modeled as two stores, where a real run passing one object twice disagrees.
- p01–p03 (Python listeners handed `self`) and t01 (TypeScript) were refused only because the check's fake lacked the
  method, not by the test.

**The fix, the same in every language:**
- **A dependency's every call inspects all its evaluated arguments.** A key's op (a store's get, set or delete) takes
  its key, and a set its value; any other argument, and any argument of a dependency's other method (answered or left
  out), that is or holds a reference to the rule's state is refused. The reference may be `self`/`this`, a nested
  object, a map, a list, a store whose keys the rule holds, or an alias of one. The refusal names the tag that accepts
  it, `gdp: skip` on its line. Other code's calls already did this (`boundary`).
- **No harness does nothing silently.** A dependency's method the rule leaves out is declared in its store
  (`StoreDecl.skip`, noted as "assumes it returns and changes nothing the rule keeps"), and the check's fake does
  nothing only for those. Any other method fails there (Python and Ruby: no such method; the JVM's proxy: an
  `UnsupportedOperationException` naming it).
- **Two injected dependencies are taken as two objects.** The notes say "assumes its injected dependencies a, b are
  distinct objects". The narrowest refusal that covers a run passing one object twice: two dependencies of one declared
  type (or both of none), the rule holding keys of either, are refused unless the caller states both stores. Of two
  types, or of services whose calls are only answers, nothing the rule keeps depends on their identity.
- **TypeScript's functions from outside** (a class's injected function, another module's) given the object's state, or
  a part of it, are refused.

**Validation.** The 25 cases are tests in their front ends' files (core/extract-py.test.ts, extract-rb, extract,
extract-jvm; research/langs/adversarial/cases.test-lib.ts):
- the four WRONG cases are refused for their reason: j01, j03 and j04 by the state reference, p12 by the two
  dependencies of one type;
- p01–p03, r01 and t01 are refused by the state reference;
- every other case is refused or its false law is not proven, as before;
- no case yields a checked proof of `n stays zero`.

On Modal:
- every front end's tests pass: TypeScript 52, Python 27 (with fastapi: p17 runs, and is refused or unproven), Rust 4,
  Ruby 6, Elixir 4, C and C++ 11, Go 20, Java and Kotlin 17;
- the Rust, C and C++, Ruby, Elixir, Java and Kotlin corpus rules re-extract byte for byte;
- LiteLLM stated reprints the committed rules; bare, 7 of 7 are byte for byte, 19 proven and 2 refuted both ways, the
  refutations assuming `get_current_spend` may return -1 and -2;
- the first round's two test extractions are unchanged, and the build and smoke pass;
- the CLI (core/cli.test.ts) reports the j01, j03 and j04 shapes refused, their stated law not read (exit 2), never
  proven.

On the branch rebased onto 2fdc902 (gen/cli), LiteLLM and the JVM corpus again: the same (stated and bare, 7 of 7
byte for byte, 19 and 2; the JVM rules identical).

**Bar** (quick, `--only rw,f1,f2,g332,suite,onecpu`, against the cached baseline of 5d4da3f, the nearest with one): f1
34 / 35, f2 24 / 33, rw 74 / 14 / 3, g332 332 of 332, each 0 differing; the suite 232 of 232 (the base's 227 jobs, 5
added since); onecpu no failure; $0.55 estimated. (A first bar, before the rebase, lost the suite's `check`: the
adversarial runner's absolute imports, now relative.)

**Bytes.** core/ and kernel/ in TypeScript, tests excluded, against 2fdc902 (gen/cli merged, this branch's base): +3,210 (core/extract-step.ts +2,722,
core/extract-read.ts +488); the harnesses +280 (Python), +191 (Ruby), +239 (the JVM's). The kernel is unchanged.

## Swift (gen/swift)

`core/swift/Sources/gdp-swiftreader/main.swift` (a reader on swift-syntax's parser and SwiftOperators' folding) lowers a
package's target into the IR; `core/extract-swift.ts` (`gdp-wired/extract-swift`) builds it, generates the harness and
runs `extractStep`. Types are the declarations' own (a property's annotation or literal initializer, a parameter's, a
result's, a protocol's requirements), parsed from their text; where none is declared the value is opaque and refused
where read, never guessed. `swiftc -dump-ast` was not needed: the subset reads only declared types.

**The reader, built for the user.** Every Swift 5.9+ toolchain ships SwiftSyntax for macros in `lib/swift/host`
(checked: Xcode's 6.4 on macOS, swift:6.3.3 on Linux), so the front end compiles main.swift against those modules
(`swiftc -O -I host -L host -lSwiftSyntax -lSwiftParser -lSwiftOperators`, about 20 s once), cached in the temporary
directory by a hash of the source and `swift --version`. Where a toolchain lacks them, `core/swift/Package.swift` (swift-syntax
pinned at 603.0.2) is built by SwiftPM instead (minutes, once). Prebuilding per platform would mean a binary per
OS/arch per toolchain line (the host modules' ABI is the compiler's), so it is left out.

**The harness.** The package is copied to a stable directory per package (files rewritten only where they differ, so
`swift build` is incremental); the entry type's file gets an extension (make, call, and per-field accessors, so private
members are reached as the code's own extensions reach them) and a JSON/stub/store runtime in pure Swift (no Foundation:
importing it could change the file's name lookup); `let` properties the harness sets become `var` and an actor becomes
a `final class` in the copy only; answered calls are rewritten with the shared `stubbed` to `(__gdpAnswer("<key>") as T)`;
an injected protocol gets a generated conforming fake (get, set, delete over what it keeps, answered methods from the
request, left-out ones doing nothing, any other one a crash the check reports). An executable target appended to
Package.swift drives it; each `new`, `at` and `call` first runs in a forked child, so a trap (Swift has no recovery from
overflow, precondition, fatalError or a nil force-unwrap) is the step's failure and the parent keeps the state as it was.

**Executor additions (shared).** A failure node may say `crash: true`: the process ends, so nothing sees what the step
wrote before it (no write-before-failure refusal; with failures kept and carried, a crash after a write is refused).
A bin node may carry its own `trap` text. A method's result that is None now holds its sort's zero in the rule (it
held the other branch's value; no committed rule of any language has an Optional result, so none changes).

**Boundary mechanism.** As the table in gen/boundary2: Swift stubs by rewriting the compiled copy (as Rust, Go, C); stores:
yes, a generated conforming class per injected protocol. Init parameters typed by a protocol are the injected
dependencies; the state-reference refusal applies unchanged (it is the executor's).

**The subset.** A class, struct or actor (an actor's method is one step: Swift runs it without interleaving up to a
suspension point, and an `await` is refused); stored properties as the state (a `var` of an Optional type with no
initial value starts nil, as Swift's does); the init's parameters (one init, or `ctor`: its arity or its parameters as
written, `'(initialValue: Int)'`; a struct's memberwise one where it has none) as params, with the properties' initial
values run first; methods (mutating ones too) as requests, private and static ones inlined only; computed properties and
the package's free functions inlined. Int and every fixed width with Swift's default trap on `+ - *`, `&+ &- &*`
wrapping, `/ %` truncating by a constant, `Int32(x)` trapping where x doesn't fit, `(truncatingIfNeeded:)` wrapping,
`(clamping:)` saturating, `(exactly:)` an Optional, the `ReportingOverflow` forms a pair, `<< >> &<< &>>` by a constant;
Bool, String (interpolation as a store's key template); enums without associated values as choices (an Int raw value
their discriminant, `.rawValue` a cast); Optional (`if let`, `guard let`, `??`, `!`, `== nil`, `case .some`/`.none`/`x?`);
Dictionary as maps (`[k]`, `[k, default:]`, `[k] = nil`, `updateValue`, `removeValue`); `throw`, `precondition`,
`assert` (on: the check builds in debug) and `fatalError` as failures; `switch` (enum cases, literals, ranges, `where`,
`break`) and if/guard condition lists as ifs; a struct made by its memberwise init as a record, copied where read.
Refused, each where it is: loops, closures, generics, `await`, `do`/`catch`, `try?`, optional chaining, arrays, floats,
enums with associated values, `inout`, a subclass of the code's own class, `defer`.

**Real code** (research/langs/swift/: specs.ts, run.ts, rules/, results.json; research/realworld/items/swift-projects.ts),
each checked against its package built by `swift build`:

| Item | Code | Requests (start / drawn / witness) | Laws |
| --- | --- | --- | --- |
| swift-nio-http2 1.46.0 `InboundWindowManager` (Apache-2.0) | HTTP/2 inbound flow control: the WINDOW_UPDATE to send; Int32 that traps, Int32(x), an Optional | 1,050 / 400 / 31 | 5 proven, 1 refuted |
| swift-nio-http2 1.46.0 `HTTP2FlowControlWindow` (Apache-2.0) | a stream's window: updates, settings deltas, consumption; throws kept as failures; `ctor: '(initialValue: Int)'` | 1,481 / 400 / 14 | 6 proven, 1 refuted |
| swift-nio 2.104.0 `NIOAsyncSequenceProducerBackPressureStrategies.HighLowWatermark` (Apache-2.0) | back-pressure hysteresis between two watermarks | 1,294 / 400 / 2 | 6 proven |

19 laws, 17 proven, 2 refuted, no suspected bug (nothing triaged): "the buffered bytes are never negative" needs a
negative size given to bufferedFrameReceived (an internal method, frame sizes never negative); "a settings change never
fails but past the maximum" needs a window already below -1 lowered by -(2^31 - 1) (its `+=` traps), unreachable when
the deltas are differences of HTTP/2 settings (0 ... 2^31 - 1). InboundWindowManager's `closed` is written only by other
code, so a law about a closed window is vacuous in the rule (left out).

**Adversarial** (research/langs/adversarial/s01–s04, tests in core/extract-swift.test.ts): a listener protocol given
`self` (left out), an answered callback given `self`, a keyed `get` given `self` beside its key: refused by the state
reference; two injected dependencies of one protocol: refused. None proven.

**Sizes.** core/ and kernel/ in TypeScript, tests excluded, against fc5611b: +35,834 (core/extract-swift.ts 34,656, its
harness's fixed Swift moved to core/swift/Harness.swift and Main.swift, 45,708 before; core/cli.ts +604;
core/extract-step.ts +574). In Swift: the reader 89,624, the harness's fixed part 11,982. The kernel is unchanged.

**What a user installs.** A Swift 5.9 or later toolchain (`swift` on the PATH, or `swift:` / `$GDP_SWIFT`); nothing
else (the reader builds against the toolchain's own SwiftSyntax). Without one the front end refuses, never throws.

**Validation** (Modal, swift:6.3.3 image; research/langs/swift/modal_swift.py): core/extract-swift.test.ts 8 of 8
(Budget, Limiter, Tally, Loop, s01–s04); the three real types extracted and their laws as above; the realworld items'
19 laws re-proven from the committed rules (17 proven); the CLI on a `.swift` file (its `// gdp: law` proven, exit 0) and
on a Package.swift directory (Budget, Limiter, Tally read, Loop refused); exports.test.ts; tsc and lint clean for the
changed files. On the suite's own image (modal/run.py): the new `extract-swift` job (research/langs/swift/swift-setup.sh
installs swift.org's 6.3.3 for Debian 12 in 46 s; 111 s in all) and scripts/smoke.sh without Swift (the front end
refuses). Not verified: other platforms than Linux x86-64 for the harness (macOS's fork path is the same code, untested
here), Swift 5.9 and 5.10 toolchains (6.3.3 only), branch coverage (not counted).

**Bar** (quick, `--only rw,f1,f2,g332,suite,onecpu`, b05f651 on fc5611b against the cached baseline of 5d4da3f): f1, f2,
rw 74 / 14 / 3 and g332 332 of 332 (the same search) each 0 differing (gained 0, lost 0, wrong 0); the suite 233 of 233
(the base's 227 jobs, 6 added since, extract-swift among them); onecpu no failure; $0.56 estimated
(runs/bar/runs/b05f65166824-vs-5d4da3f49013-quick-2026-10-301006). The quick rw dev set holds no Swift item, so the
realworld Swift items were proven on their own (above).

**Next (not built): string-keyed maps.** A Swift map keyed by `String` (a `[String: Int]` field, a store keyed by a
string's template) extracts and checks, but its laws can't name a key: the rule's maps are keyed by naturals, so a law
reading `m.at(user)` with a string `user` fails to build (core/dsl.ts's `at` takes a number), and a signed `Int` key is
refused ("a map key that may be negative"). The Limiter test keys by `UInt` for that reason. The fix belongs to the
shared maps (keys of a string sort, as the rule's strings are interned), not to the Swift front end.


## One way in (gen/oneway)

Every entry point a user calls to read code, audited at 07b2518 before any change: its signature, and the lines a user
writes from "I have a file" to a proven law (the import statements, the call, the proof; the law itself inline).

| Front end | Export | Signature at 07b2518 | Source | Runtime module | `entry` | Result | CLI | Lines |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| TypeScript | `gdp-wired/extract` | `extract(code, {file, entry, ...})` | code string (the caller reads the file; `file` names it) | `typescript` resolved beside gdp-wired | required | `x.rule`, `x.invariants`, `x.names` | yes | 5 |
| Effect | `gdp-wired/effect` | `extractEffect(code, {file, entry, effect})` | code string | `effect` passed by hand (`import * as effect`) | required (`make` by convention) | `x.rule` | wired (`from 'effect'`), untested | 6 |
| XState | `gdp-wired/extract` | `extractXState(code, {file, entry, xstate})` | code string | `xstate` passed by hand | required | `x.chart` (no `rule`, `invariants`, `names`) | no (an XState file goes to `extract` and is refused) | 5 |
| Python | `gdp-wired/extract-py` | `extractPython(file, opts)` | path | `python3` (or `python`) | inferred | `x.rule` | yes | 4 |
| Ruby | `gdp-wired/extract-rb` | `extractRuby(file, opts)` | path | `ruby` | inferred | `x.rule` | yes | 4 |
| Elixir | `gdp-wired/extract-ex` | `extractElixir(file, opts)` | path | `elixir` | inferred (one module; a list refused) | `x.rule` | yes | 4 |
| Java, Kotlin | `gdp-wired/extract-java`, `-kotlin` | `extractJava(file, opts)`, `extractKotlin(file, opts)` | path | a JDK, kotlinc | inferred | `x.rule` | yes | 4 |
| Go | `gdp-wired/extract-go` | `extractGo(dir, opts)` | a package directory only (a `.go` file is read alone and its check built in the wrong place) | `go` | inferred | `x.rule`, `x.leaves` | yes (a file mapped to its directory) | 4 |
| Rust | `gdp-wired/extract-rs` | `extractRust(dir, opts)` | a crate directory only | `cargo` | inferred | `x.rule` | yes (a file mapped to its crate) | 4 |
| Swift | `gdp-wired/extract-swift` | `extractSwift(at, opts)` | a file or a package directory | `swift` | inferred | `x.rule` | yes | 4 |
| C | `gdp-wired/extract-c` | `extractC(file, opts, cpp?)` | path | `clang` | inferred | `x.rule`, `x.leaves` | yes | 4 |
| C++ | `gdp-wired/extract-cpp` | `extractCpp(file, opts)` | path | `clang++` | required (the dump reads only the class named) | `x.rule` | yes (each class tried) | 4 |
| XState, by hand | `gdp-wired/xstate` | `fromXState(machine, bridge)`, `conforms(chart, machine, createActor)` | the machine object, imported | `createActor` passed by hand | n/a | a chart | no | n/a |
| Effect, by hand | `gdp-wired/effect` | `conforms(rule, {effect, make, request, ...}, {draw})` | a running service | `effect` passed by hand | n/a | `{checked, failure}` | no | n/a |
| Laws in text | `gdp-wired/laws` | `lawsIn(text, where)`, `buildLaw(x, law)` | text | none | n/a | a law | (the CLI's) | n/a |
| The CLI | `gdp-wired/cli` | `check(targets, opts)`, `gdp-wired check <file|dir>` | paths | resolved from the target | inferred (TS: each exported class or function tried) | rules and verdicts | itself | 2 (a comment, a command) |

The 4 of the step languages: `import {extractPython}`, `import {proveRule} from 'gdp-wired'`, the call (with `{}`: the
options are a required argument even when empty), the proof. TypeScript adds `import {readFileSync}` and repeats the
path as `file`; Effect adds `import * as effect`; XState adds `import * as xstate`.

**Inconsistencies.**

1. *Code, path or directory.* TypeScript, Effect and XState take the code as a string (the caller reads the file and
   names it again in `file`; a type that should resolve from the project's node_modules, Effect 3.x's say, needs `file`
   to be the real path). Every other front end takes a path. Go and Rust take only a directory, though the CLI maps a
   file to its package or crate; Swift takes either. No front end takes a `URL` (`new URL('./x.ts', import.meta.url)`).
2. *A runtime module passed in by hand.* `effect` (Effect) and `xstate` (XState): required, though the module the code
   runs on is the one beside the file (the CLI already resolves `effect` from the file). `typescript` is resolved
   beside gdp-wired; the toolchains (python, ruby, go, ...) are found on the PATH with an option to name another.
   `conforms` (both) and `fromXState` take a running object: there is no file to resolve from.
3. *A required `entry` the inference could find.* TypeScript, Effect and XState require it; the step languages, Go and
   C infer it (the one class or struct whose methods write its state), and the CLI tries every exported class and
   function of a TypeScript file. C++ requires it (clang's dump is filtered by the name). Elixir takes one module.
4. *One meaning, several names.* The requests read: `methods` (TypeScript classes, the step languages, Go), `functions`
   (C: the struct's functions; TypeScript: several functions over one record, the entry first), `entry: [...]`
   (Python's module functions). Failures: `failures: 'refuse' | 'kept'` in the step languages; Go and C have only
   `onError` and `fails` (a result that is a failure); TypeScript and Effect neither (a throw is the refusal). The
   boundary (`answers`, `skip`, `stores`) is in the step languages only; `strict` everywhere but XState. `stores` is
   refused in Rust, Elixir, Java, Kotlin and Swift. `check` has four shapes (CheckOptions, StepOptions', GoCheckOptions,
   XState's). The options argument is required everywhere but Swift's readers.
5. *How the result is read.* Every result has `ok`, `refusals` ({where, what}) and `notes`; the rule is `x.rule` with
   `x.invariants` beside it (`proveRule(x.rule, [...x.invariants, law])`), except XState's, which is `x.chart` (proven
   by `x.chart.prove([x.chart.law(...)])`) with no names, so no law stated in its code can be read. The evidence has
   two shapes (requests, states, probes; or runs and events).
6. *What the CLI doesn't cover.* XState files (read by `extract`, refused). Effect files were wired but never tested.

## One way in: the shape after it

Every front end is `(file, options?) => {ok, rule, invariants, names, refusals, notes, ...}`:

- **The source** is a path or a `URL` (`new URL('./x.ts', import.meta.url)`), read by the front end; Go and Rust take
  the package's or crate's directory or any file in it, Swift a file or a package. TypeScript, Effect and XState also
  take `{code, file}` for code in memory, and their code-first call as it was (a string is code where it holds a line
  break or doesn't end in a script's extension). core/extract-read.ts's `sourceOf`, `pathOf`.
- **Runtime modules from the file's project**: `effect` and `xstate` are what the file imports, resolved from its own
  node_modules (`beside`: a require from the file's place), so the check runs the version the code is written for
  (Effect 3 where the project has 3); `{effect}`, `{xstate}` still win. The CLI imports them the same way.
- **The entry inferred** where the reading can decide it: TypeScript tries each exported class and function and takes
  the one that reads as a rule (several: refused with their names); Effect takes the file's one make effect (each
  declaration tried, exported ones first; `make` and a `Layer.effect(Tag, make)` are one); XState the file's one
  machine (a createMachine, or a function returning one); C++ tries each class the file declares. A note says what
  was inferred; an explicit `entry` wins.
- **One name per meaning**: the requests read are `methods` everywhere (C's `functions` is a deprecated alias), several
  functions as requests are `entry: [...]` (TypeScript's `functions` is a deprecated alias, as Python's form was
  already); `failures`, `onError`, `strict`, `answers`, `skip`, `stores`, `domains`, `check` were already one name each
  where a front end has them. The options argument is optional everywhere.
- **One result**: `extractXState`'s has `rule` (the chart's), `invariants` (the chart's own laws) and `names` (`value`,
  `value.<region>`, the context's fields, `event`, `event.<field>`, the answers of a factory's functions), so it is
  proven, and its `// gdp: law` comments read, like any front end's. Each front end's module exports `proveRule` and
  `proveSteps`: one import.
- **The CLI** reads XState files (a `.ts` importing xstate and calling createMachine) and Effect files with the
  packages of the file's project, and runs TypeScript with the file's real path (its imports' types resolve as the
  project's do). Its test has an Effect case and an XState case, each a law proven and one broken with its run.

Nothing was removed or renamed: every signature and option at 07b2518 still type-checks and runs (each one-way-in test
compares the call as it was with the new one on the same file, source and machine equal).

| Front end | Lines before | Lines after | After |
| --- | --- | --- | --- |
| TypeScript | 5 | 3 | `import {extract, proveRule} from 'gdp-wired/extract'`; `const x = extract('./bucket.ts')`; `proveRule(x.rule!, [law])` |
| Effect | 6 | 3 | `import {extractEffect, proveRule} from 'gdp-wired/effect'`; `const x = extractEffect('./limiter.ts')`; `proveRule(...)` |
| XState | 5 | 3 | `import {extractXState, proveRule} from 'gdp-wired/extract'`; `extractXState('./machine.ts')`; `proveRule(...)` |
| Python, Ruby, Elixir, Java, Kotlin, Swift, C | 4 | 3 | `import {extractPython, proveRule} from 'gdp-wired/extract-py'`; `extractPython('limiter.py')`; `proveRule(...)` |
| Go | 4 (a directory only) | 3 (a file of the package too) | `extractGo('internal/limiter/limiter.go')` |
| Rust | 4 (a crate directory only) | 3 (a file of the crate too) | `extractRust('src/lib.rs')` |
| C++ | 4, `entry` required | 3 | `extractCpp('lim.cpp')` |
| The CLI | 2; XState not read, Effect untested | 2, every front end | a `gdp: law` comment, `npx gdp-wired check <file>` |

The film's Effect harness, before and after:

```ts
// before: 4 lines to the extraction, and proveRule from another import
import * as effect from 'effect'
import {readFileSync} from 'node:fs'
import {extractEffect} from 'gdp-wired/effect'
const x = extractEffect(readFileSync('limiter.ts', 'utf8'), {file: 'limiter.ts', entry: 'make', effect})
// after
import {extractEffect, proveRule} from 'gdp-wired/effect'
const x = extractEffect('./limiter.ts')
proveRule(x.rule!, [x.rule!.law('never below zero', ({tokens}) => tokens.atLeast(0))])
// or: `// gdp: law never below zero: tokens >= 0` above make, and `npx gdp-wired check limiter.ts`
```

What stays as it was, and why: `fromXState(machine, bridge)`, `conforms(chart, machine, createActor)` and Effect's
`conforms(rule, {effect, ...})` take a running object, so there is no file to resolve from; the toolchains (python,
ruby, go, ...) are found on the PATH with an option naming another, as before; `failures: 'kept'` is still the step
languages' only (Go and C keep `fails` and `onError`; TypeScript's throws are refusals), `answers`, `skip` and `stores`
too: a capability each front end lacks, not a name that differs.

**Sizes.** core/ in TypeScript, tests excluded, against 07b2518: +14,405 bytes (core/extract-xstate.ts +4,207: the
wrapper, the machine inferred, the names; core/effect.ts +2,577: the service inferred; core/extract.ts +2,212;
core/extract-read.ts +1,881: `sourceOf`, `pathOf`, `beside`; core/extract-c.ts +1,240: C++'s entry; the rest a few
hundred each, much of it the usage lines). Tests +9,834. kernel/, core/laws.ts and core/infer.ts are unchanged.

**Validation** (Modal, modal/run.py's image): core/extract.test.ts, effect.test.ts (Effect 4.x and 3.x), xstate.test.ts,
exports.test.ts and cli.test.ts (the TypeScript, Effect and XState cases and their one-way-in cases), 101 of 101 run;
each language's own test file with its toolchain (research/langs/*-setup.sh, research/extract/go-setup.sh) and its two
cli.test.ts cases (the CLI's laws, and one way in): Python 29, Ruby 8, Elixir 6, C and C++ 15, Java and Kotlin 21, Swift
10, Go 22, Rust 6, none skipped; chart.test.ts and examples/effect.ts, xstate.ts, charts.ts; tsc and oxlint clean;
scripts/smoke.sh under Node 22.12 (its consumer type-check caught the global `URL` in the declarations, which a
project without DOM or Node types lacks: a URL is now taken by its shape). First pass: the Rust one-way-in case failed
on the call as it was (with `entry` named, the Rust front end reads every pub fn of the impl, `new` too, and the
harness calls `new` as a method: an existing behavior, not this change's), so the case names its methods.

**Bar** (quick, `--only rw,f1,f2,g332,suite,onecpu`, 70ca4e6 against the cached baseline of 5d4da3f): f1 34 proven of
48 (base 34), f2 24 of 64 (base mean 24.33), rw 73 / 14 / 4 (base 74 / 14 / 3: one first-pass flip, noise after 3
reruns a side: gained 0, lost 0, wrong 0), g332 332 of 332 the same search; the suite 233 of 233; onecpu no failure;
$0.59 estimated (runs/bar/runs/70ca4e617289-vs-5d4da3f49013-quick-2026-10-301223).

## Loops and exceptions, read generally (gen/laneL)

Lane D unrolled loops pass by pass (+69 KB, 0 of 44 real extractions gained, lists capped at 3 items: shelved). This
lane reads the same two refusals with no pass unrolled and no cap, each one mechanism in the shared executor
(core/extract-step.ts) that every reader lowers its forms onto.

**A try: a raise routed to the handler that catches it, on the path where it is raised.** `{s: 'try', body, handlers:
[{names, mro, open?, any?, raise, as?, body}], els, fin}`. A raise has a kind: its class and bases, qualified (Python's
from the classes of the repository and builtins' `__mro__`, Ruby's from the file's classes and `ancestors`); `open`
where some base can't be known (an imported class's), `null` for a panic or a trap, which nothing catches. It goes to
the innermost try's first handler naming one of its classes (or any, a bare `except:`); a handler that may or may not
catch it (open bases, or a failure no reader names) is refused. Raised are: the code's `raise` (inside a try its
arguments are evaluated first, so a failure there is what is raised), a bare re-raise (what its handler caught, refused
where outer handlers would tell its kinds apart), and the executor's own failures (KeyError, TypeError of None,
AttributeError, ZeroDivisionError), whose bases each reader gives (`kinds`). A raise caught is a path to its handler,
and every later condition in the try is outside it: `cond(p)` is conjoined with the negations of the conditions the
enclosing tries' raises were caught under, every way out of the body (returns, breaks, the live end) is assumed past
them, and the paths raised to one handler are joined keeping that one of them was taken (`joinSome`). `else` runs on the
body's live end, outside the try; `finally` on the live end and each return, refused where it returns, raises or
breaks, or where a failure, a break or a raise an outer handler catches goes out through it. A raise through a context
manager of other code taken as transparent (which may suppress it) to a handler around it is refused.

**Other code inside a try may raise.** A call of other code (answered, left out, or stated skip) or a store's get, set
or delete inside a try is a step that returns or raises what one handler of the tries around it catches: the innermost
first, up to the first handler that catches the class other code raises (Python's `Exception`, Ruby's
`StandardError`). An input of the request says which (`<callee>_raises`: a boolean for one outcome, a choice of the
handlers' classes for several; one a method), and the check's stub raises that class there (the handler's own class,
made without its arguments); a call left out runs as it is unless the input says it raises. So a law is proven for
every outcome; what is assumed, as outside a try, is that other code raises nothing a handler there doesn't catch (the
notes say it, and a refutation that needs a raise says `assumes \`callee\` may raise`). Python and Ruby read it (their
harnesses raise); the JVM, Swift and C++ readers still refuse a try (their stubs are rewritten call sites, which can't
raise yet). Rust, Go and C have none.

**A loop over a list the request carries: a fold, exact for every length.** `{s: 'for', to, over, body}`, `continue`,
`break`; Python's `for` and `any`/`all`/`sum` of a generator (the same loop with an accumulator); `x in xs` is `any(item == x for item in xs)`, `len(xs)` the length, the truth of
`xs` an item. A list is one representation, Lane O's map by place:
a list of the state (an ordered collection: each item at a place that only grows) or a list the request carries
(Python's `list[T]`/`Sequence[T]` argument, T a scalar or a record of scalars and strings, where the harness makes
one: `lists`), a map by place 0 to its length `<list>_len` with every place held, printed as a carried list
(`carriesList`). An item is its place's cell either way (`{t: 'cell', map, key}`, its fields read as any map's
record's), and a loop runs over either: the passes a carried list's length, or one past a list of the state's last
place (its least key's, read in the state before the step) with a place that holds no item a pass that changes
nothing. The body runs once, at a pass `i$`: the item
there (its fields cells at `i$`), and each local the body sets that is set before it a running value, a cell of the
loop's own carried list `<list>$<k>` (one longer). What the pass makes of them is the fold's step: each running value
at `i$ + 1`, and whether the pass ended the loop (`__done`: a return, a break, a failure or a refusal), what it returned
(`__returned`, `__ret`), whether it failed or refused. The rule assumes every request carries the running values its
items make: `.assume(... <run>.at(0) = start, <run>.every((_x, i$) => i$ < len implies <run>.at(i$ + 1) = step))`; after the loop each
running value is its cell at the length, a return the cell `__ret` where `__returned`, a failure the step's where
`__failed`. The step reads anything the body reads (the state before the step, the request, the params, other folds'
ends), since an assumption may: every request of the code has exactly one sequence of running values meeting it, so the
assumption excludes none. The check draws lists of 0 to 12 items and computes the running values the same way
(extract-check.ts `carry`; a list of the state's from the rule's own places), so a step that misreads the body is a request the rule refuses and the code doesn't.
Refused, each where it is: a pass that writes the state, reads an answer (it would be one a pass), calls other code
inside a try around the loop, raises out of the loop to a try around it, or holds a loop itself; a loop over anything
but a list the request carries (a map or a list of the state, a literal, a range), and a loop's `else`.

What a fold leaves the prover: the equations are its only facts about the passes, so a law about the end of a list
of any length that needs induction over the passes (a running sum stays at least 0, a flag once set stays set) is
unknown; laws about the first pass, about an empty list, or that need no fact about the fold beyond its value, are
proven, and a law the fold breaks is refuted with a list. Probes (the prover's witnesses run on the code) are skipped
where a rule carries folds: each one is slow under the quantified equations, and its lists empty.

**Measured on real code** (Modal, 2 vCPU a job; the corpora sweep, research/langs/sweep.ts through each language's
`run.ts --sweep`, base cd97c61 against 1396388, the same jobs; logs in the worktree's runs/laneL/). 508 methods and
functions of the cited files (Python 276, Rust 112, Ruby 39, C 30, Swift 28, C++ 10, Java 9, Kotlin 4), extracted
119 → 122, all three gains Python's; no rule extracted on both sides differs (by hash), none lost; the laws `check`
proposes: proven 234 → 240, unknown 15 → 11, refuted 0 → 0 (every change a unit whose rule is the same on both sides
and that this lane's code doesn't reach: C, C++, Java, Ruby, Swift, each flipping between runs under the 2 s a law;
two sweeps of the candidate disagree on the same ones). Refused for a loop or a try: 55 → 39 by the sweep's own
pattern (it also counts refusals that only mention an exception); by hand, of the 21 Python functions with a try,
the 10 Python loops, Rust's 4 `while let` and C's 4 loops:
- **gained** (3): `_cache_registry_answer` and `delete_cache_key_object` (a cache write or delete inside
  `try/except Exception`: the call may raise, the handler logs), `_can_object_call_search_tool` (an empty list's
  truth). Their rules propose no laws (no state but a store's cell).
- **read past the try or loop, stopped further** (most): a function that returns other code's object
  (`get_user_object`, `get_org_object`, `model_validate`, `LitellmUserRoles(...)`, 9); other code called on a value the
  check can't stub inside a try (a callable argument `fetch_ids()`, `load_team_object()`, an untyped `kwargs.get`, 3);
  a TypedDict's `get` on a list's item (3); a list of no item type (`list`, 3); a loop over a dict, a tuple literal, a
  list literal, a `zip`, or other code's value (5); `in` against another module's enum value; a call answered twice in
  one step inside a try; `can_grants_view_search_tool`, where the check ran the module's own function left out with
  an inert argument and it raised what the handler doesn't catch: the rule and the code differ, so it is refused (the
  assumption that other code raises only what a handler catches is checked where the check runs the call).
- **Rust's `while let`** (governor's FixedWindow, 4): `while let Some(b) = buckets.first() { if b.0 < cutoff {
  buckets.remove(0) } else { break } }` drops the expired prefix of a list of the state; no fold over a collection
  (its passes are what they remove). Refused now with that reason; reading it needs a list of the state with a prefix
  dropped (a window), not a fold.
- C's 4 (ENet's linked lists, the ring buffer's copies) and Go's 5 (`range` over another package's `[]string`, not
  in the sweep) are unchanged: Go's reader and harness make no list argument yet, and C's are pointer walks.

**Soundness checks.** Every extraction above is checked against the code by the readers' own correspondence runs
(the check draws lists of 0 to 12 items and the raise inputs, the harness stubs raise). Mutation: with the returns of
a try's body not assumed past its raises, the check finds the difference (a request where a raise and a return both
hold). terra's review of the try machinery (read-only, two narrow prompts) found two real cases, both fixed and in
the tests: a raise caught by an outer handler skipped an inner `finally` (now refused), and a raise's argument that
fails first (now evaluated, its failure raised); its review of the folds found a nested loop sharing the pass name
(already refused) and nothing else. Tests (core/extract-py.test.ts, core/extract-rb.test.ts): a call that may raise
with two handlers' outcomes, a KeyError and a raise by a class with bases, else/finally/re-raise, a store that may
fail inside a try, Ruby's begin/rescue/else/ensure and a method's own rescue, a fold with continue, a raise in a pass
and an early return, strings, any/sum of a generator, a loop that reads no item, `len`; laws proven and refuted on
each. What is not verified: laws about a fold's end beyond the first pass need induction over the passes, which the
equations don't give (unknown, not wrong); the JVM, Swift and C++ readers' try, and Go's and Rust's list arguments,
are not built.

**Gates** (1396388): quick bar against the cached ae36917 baseline: wrong 0 in every group, lost (solid) 0, rw
74 / 14 / 3 as the base, f1 34, f2 24, g332 332 of 332, onecpu no failure; suites 239 of 239 by default and with
--usual (the base 235: the extra jobs are other merges'); typecheck (`tsc -p .`, no error in core/ or kernel/) and
lint clean. core/: +47 KB without tests (core/extract-step.ts +31 KB), kernel/ untouched; Lane D's unrolling was
+69 KB.
