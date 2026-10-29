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
