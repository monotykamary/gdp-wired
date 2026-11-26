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

Java and Swift classes with multiple constructors are checked by the CLI as separate initializer scopes.
Every scope retains the class's laws and must pass its own original-code replay; a successful overload does not
hide a refused or broken one. JSON and text output identify the `ctor` signature. Ambiguous constructor scopes
are not silently selected as a cross-rule dependency. A single `extractJava` / `extractSwift` call still refuses
an unspecified constructor and returns typed `initializers` alternatives. Explicit `ctor` configuration keeps
precedence: Java accepts an arity or erased parameter signature such as `"(int,java.lang.String)"`; Swift accepts
an arity or its parameter clause such as `"(seed: Int)"`. Swift resolves same-label delegation
only for exact declared scalar arguments or explicit integer conversions; context-dependent literal
overloads and failable initializers remain refused. Kotlin continues to use an arity.

Go reads direct `time.Now().UnixMilli()` and `time.Now().Unix()` projections, including qualified import
aliases, as a millisecond request-time input. The check substitutes only `time.Now` with that input;
Go still executes the original `UnixMilli`/`Unix` projection and surrounding method. Negative epoch times
use floor division for seconds, not Go integer division's truncation. Multiple reads assume the step
runs within one millisecond clock tick; time may move backwards between requests. This does not add
monotonic-clock semantics, stored/local `time.Time` values, finer projections such as `UnixNano`, or clock
reads nested inside answered calls (overlapping source substitutions are refused). Inputs retain the
Go reader's exact JavaScript-integer range restriction.

Rust reads dynamic `Ordering` values for `load`/`store` on direct standard atomic state fields.
The five standard variants remain choice inputs: invalid load orders (`Release`, `AcqRel`) and invalid
store orders (`Acquire`, `AcqRel`) cause a failure before the atomic operation, after argument evaluation.
Each argument is materialized immediately after its own prelude, before the next argument is evaluated;
an earlier argument failure therefore prevents later argument effects.
With `failures: 'kept'`, earlier state changes survive that failure. Standard/core-qualified types and direct
imports are recognized conservatively; aliases, wildcard imports and broader dynamic RMW operations
remain outside this increment. Native replay executes Rust's actual atomic methods. As for existing
atomic support, each request is one non-interleaving call; this is not a concurrent memory-model proof.

Rust reads two-argument integer-primitive associated extrema such as `usize::min(a, b)` and
`i32::max(a, b)` through the same comparison semantics as its existing min/max support. Native replay
still checks the original calls, including fixed-width integer boundaries. This shortcut is limited to
syntactically unshadowed primitive names: visible same-named types/modules, aliases, wildcard imports,
a disabled implicit prelude, generic path arguments and explicit trait-qualified calls do not authorize
it. This is not general alias, trait or import resolution.

Unqualified Rust calls resolved to a fixed source function materialize each argument after its own
prelude and before the next argument. This preserves cross-argument reads and early failures.
Local callable values, indirect calls and methods outside the direct-field cases below retain their existing
lowering; this does not claim general call or receiver evaluation-order coverage.

Direct primitive-integer state-field `min`/`max` receivers are captured before their arguments.
Direct helper fields with a unique borrowed, nongeneric inherent method in the same source file/module
also capture the receiver identity, then materialize each argument after its own prelude. A `min`/`max`
receiver consisting of a direct primitive field plus a type-compatible integer literal (with optional
parentheses) is also captured first, so checked overflow precedes argument effects. An unlabeled receiver
block ending in a direct primitive state field captures that field after its existing supported prelude;
early returns or panics in the prelude prevent later argument effects. Other computed or
side-effectful receivers, indirect callees, trait methods and generic dispatch do not enter this shortcut;
existing native mismatch and unsupported-source refusals remain outside this bounded increment.
Literal suffix/type compatibility is not a value-range guarantee: native Rust, the literal parser and
safe-number/model limits still apply.

A separate closed callee-block path supports exactly one same-typed primitive state-field assignment
(field plus a compatible integer literal, checked `+` or `wrapping_add`), followed by a bare function
item. It requires one actual loaded declaration globally, matching known caller file/module, an ordinary
safe synchronous nongeneric integer signature and exact arity. Its assignment precedes immediate
left-to-right argument captures. Shadows and ambiguous identities refuse rather than select a map entry.
This deliberately conservative path declines crate-wide imports, macros, non-doc attributes, unresolved
module metadata, local item declarations and unsupported visibility/signatures. Only verified inherent
caller identity enters it; it adds no general alias/callee resolution or shared-executor behavior.
Other callee shapes keep their prior lowering and refusals, not a blanket language ban.

Rust native replay places its harness inside a uniquely identified loaded inline module, using the
parser's UTF-8 byte position from the rewritten copy (after clock and answered-call substitutions).
File modules retain append-at-file-scope placement. Private state stays in its declaring scope; fixed
free-function calls are qualified against generated-local shadowing. Mixed-file/module function batches
and unknown/ambiguous placement refuse rather than guess. Source errors after insertion remain source
errors, while generated harness errors remain harness failures. This does not expand reader admission,
generic dispatch or module loading; inline BOM/shebang placement is conservatively refused.

A selected-scope type/module binding named `__gdp_harness` can use a deterministic fresh module name
when the parsed inventory is closed. Raw identifiers are normalized, and the first unused numeric
suffix avoids identifiers across the loaded source. Declaration, bridge targets and test selector all
use that same name. Field/value names and names in unrelated scopes do not themselves trigger renaming.
Relevant import/glob uncertainty, macros, attributes or unexpanded modules prevent a fresh-name claim;
this is conservative and does not expand aliases or macros. Ordinary noncollision paths are retained.
Root bridge repair is a separate bounded step. Value-namespace bindings that collide with `__gdp_now`
or `__gdp_answer` can receive fresh names under the same closed-inventory requirement. Functions,
constants, statics and tuple/unit constructors occupy this namespace; type-only bindings, fields and
other module scopes do not. Relevant imports/globs or foreign declarations that leave freshness
uncertain refuse; no import or macro-expanded namespace resolution is claimed.
The bridge names are chosen once at the crate root **before** rewriting clock/answered calls and are
used unchanged in those substitutions and declarations. The helper module and its byte position are
still queried **after** rewriting. Original calls to same-spelled user functions are not renamed.
This does not broaden D3 callee admission, general name resolution, or source/harness error claims.

The current Rust record/method tables use short names. A reached record with multiple source declarations,
or a called method with multiple source candidates (including trait/inherent collisions), is refused rather
than selected by declaration order. This is a reader-identity limit even where Rust itself resolves the call.
Unrelated collisions do not reject an otherwise supported entry; this adds no module/trait resolution support.

Rust lifetime parameters alone do not make a struct declaration or method/free-function signature
value-generic. Type and const parameters on those declarations and signatures remain flagged as generic
and refused, including when mixed with lifetimes. This does not generalize to parameters on `impl` blocks
or trait specialization: the existing method index does not retain impl-level generics or trait/self-type
arguments, and this change does not address that limitation.

Lifetime-bearing methods use the same original-code replay as other Rust methods. The existing type reader
erases references recursively; unsupported borrowed fields, argument types and ownership operations rely
on downstream lowering and harness compilation/checks, not a blanket reader-level reference guard.
This change neither specializes arbitrary generic code nor establishes support for lifetime-only borrowed
records; the positive replay test uses scalar state and lifetime-bearing methods.

Solidity deployment contexts, constructor-only subclasses and library callers are described in
[Solidity harnesses](SOLIDITY.md); the original source stays unchanged and the chosen context is reported.

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
    (`30 days`; months are refused), business days between two times over the calendar in gdp.toml
    (`now - t <= 10 business days`, core/calendar.ts).

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
  `methods`, `answers`, `skip`, `stores`, `strict`, `root`, `python`, `entry`, `clock`, `from`, `env`, `effects`,
  `stubs` and `types` (the type of an argument or field the code doesn't declare). Flags override the file.
- **The environment** (`env` in `gdp.toml`, `--env`, or `# gdp: env <words>` over the class; core/system.ts's
  `envOf` and `inEnv`): the rule becomes every call of it at once, and its laws are lifted to that system. The words:
  an isolation level (`atomic`, `serializable`, `read committed`, `snapshot`, `repeatable read`), `keys expire` (any
  store key may vanish), `retries`, `an object per call` (each call its own object: the fields its methods write), and
  a call's flow, `acquire then release` (its methods in order, each a step or a transaction; a call ends where a method
  fails or returns false). A law of one step holds at each call's commit, the store as the commit finds it. `at most
  one call between a and b` is the flow's mutual exclusion per key: a call holds from a's success to b, and a key that
  expires ends its holders' leases; `between a and a` is a's work done at most once per key (the flow is inferred from
  the law). A step does its work where it makes its effect: a call of other code tagged `# gdp: effect` on its line
  (or listed in `effects`), stubbed by the check, each step saying whether it made it (`<name>.called`). The verdict
  names the environment models the system assumes; a broken law's run is the calls' steps (begins, reads, commits,
  expiries), shortened, and found by a breadth-first search of calls contending with one request where the prover's
  runs don't.
- **Stores** (`stores`): a store may be an injected dependency, a field the constructor makes (a client from a URL), or
  a module's object (Django's `cache`); its operations are get, set (with `nx`), delete, `add` (set where absent: SET
  NX, memcached's add, `put_if_empty`) and `incr`, each by a key template (an f-string or a `%` format); a template's
  values are numbers or strings.
- **Verdicts and exit** (`check`): each stated law is `proven`, `broken` (with a run, replayed on the code), `unknown`
  or `not read`. The exit code is 1 when one is broken, else 2 when one is not read (a refused rule makes every law of
  it not read), else 0. `--from any` proves the laws from every state they allow; the largest inductive subset of the
  stated laws is found by Houdini (`houdini`). `--cert <dir>` writes each proven law's certificate as an interchange
  document (`core/relational.ts`'s `certify`), checked as it is written. `gdp-wired-check` checks it again with
  nothing but the kernel (`interchange/cli.ts`; [interchange.md](interchange.md)).

## ORM-backed handlers

[ORM-backed handlers](ORM.md) documents the explicit Django, SQLAlchemy, Prisma and TypeORM subset,
its persistence boundary, configuration, and refusals. Their tables use the shared map state and `gdp: env`
isolation model; the check executes the original handlers with in-memory persistence substitutes.

## Python inheritance and presence checks

Ordinary Python classes with a statically known C3 MRO select fields, methods and class
constants by their declaring owner, including cooperative `super()` on the receiver's MRO.
Module-qualified method IDs distinguish same-named classes in different modules. Class
collections may be carried opaquely, not read, copied into state or treated as constants.
Calls with no variadic arguments bind `*args` and `**kwargs` to their actual empty values;
nonempty variadic calls remain refused.

`hasattr(instance, 'literal')` checks modeled fields and known class bindings without
reading their values. Properties, unknown descriptors, implicit object attributes and
dynamic names are refused rather than speculatively evaluated. Final class-body bindings
matter: assignments replace earlier methods, annotations without values do not, and a
later unannotated definition clears the earlier return type. Constructor-inferred fields
come from the final initializer. Entry and nested construction share the same check for
nonmethod or decorated initializers. Ordinary unknown-MRO construction and custom
allocation/attribute hooks are refused. Existing dataclass/ORM generation stays a separate
reader boundary; this is not a claim of universal Python constructor safety.

## Opt-in standalone TypeScript scalar functions

The existing `gdp-wired/extract` API accepts `mode: 'standalone'` with exactly one
named `entry`. The CLI has `--entry decide --mode standalone`; `[rules.decide]`
in `gdp.toml` can set `mode = "standalone"`. Without this explicit mode the existing
reducer, class and factory routes are unchanged.

```ts
const x = extract('./decision.ts', {entry: 'decide', mode: 'standalone'})
```

Each invocation has independent scalar arguments, not a first argument reused as
state. Numeric and boolean arguments, and `boolean | undefined`, are supported.
The numeric or boolean result is kept separately with a missing flag: fall-through
and `return undefined` reset the result to absent, while present `false` stays
present. `names` exposes the arguments and the result's `none` flag to comment laws;
`result is undefined` is an absence test, not equality with the placeholder value.
In standalone comment laws, direct optional comparisons retain presence: an absent
value equals neither `true` nor `false` nor a number, and optional boolean
truthiness requires presence. Two absent optional values compare equal. Arithmetic
on an optional value is refused rather than using its hidden placeholder. These
semantics are opt-in with this frontend; other frontend law routes are unchanged.

This is a **safe-integer subset**, not a model of all JavaScript numbers. Numeric
literal unions retain their exact finite input set (at most 64 safe integers),
recorded in `model.standaloneDomains` and the extraction notes. Other values are
outside the claim; the rule rejects them and the differential checker does not
execute out-of-domain probes. Fractional literals/domains, NaN, infinities and
unsafe integers are not silently rounded. A supplied `domains` restriction remains
explicit; a natural restriction contradicting negative union members is refused.

The reader resolves the reachable bindings by TypeScript symbol, not spelling.
Module constants may contain inert primitives/arrays and references to earlier
inert constants. Direct, same-file pure helpers are inlined. Type-only imports are
erased, with supplied relative `files` used for their types. Value imports,
re-exports, executable initializers, mutable module bindings, indirect calls,
recursion, closures, objects, mutation, loops, async and exceptions in the reachable
routine are refused before conformance. Uncalled function bodies may coexist in
the file but are not claimed as supported. `model.standaloneBindings` lists the
reachable function/constant bindings; coverage counts the entry and reached helpers.

The check still compiles and executes the original module, not a hand-written
replacement. Its VM is a differential-test harness, **not an OS security sandbox**.
Untrusted source requires separately verified process/filesystem/network containment.
Passing owned examples does not establish third-party source support; a real-source
assessment needs exact revision/closure, ordinary domains, nonzero original-code
conformance and stated laws, with the sampled-vs-equivalence distinction preserved.

## Opt-in C safety (Stage 1)

C memory and undefined-behavior safety checking is strictly opt-in via `--safety` on the CLI,
`extractC(file, { ..., safety: true })`, or a `gdp: safety` directive in a C comment
(`// gdp: safety`, `/* gdp: safety */`, multiline `/* gdp:\n safety */`, backslash-continued `//`,
case/punctuation variants such as `// GDP: safety`, `// gdp: safety.`, `// TODO(gdp: safety)`,
inline comments, or comments with trailing notes, ignoring string/char literals and C23 digit
separators like `1'000`). Without opt-in, default C extraction and law checking are unchanged. A
`gdp.toml` setting `safety = false` (top-level or under `[rules.<entry>]`) cannot silently override
an in-source `gdp: safety` directive and is refused with exit code `2`; lookalike comments
(including Unicode NBSP, fullwidth colons, `// gdp safety`, `// gdp: safe`, or
`// gdp: safety = false`) emit a visible warning in both text and JSON output and exit `2` rather
than silently doing nothing.

In safety mode, every Clang invocation (analysis, `-E -v` search-dir probe, and native replay
harness) runs in a scrubbed environment with compiler include/option override variables unset
(`CPATH`, `C_INCLUDE_PATH`, `CPLUS_INCLUDE_PATH`, `OBJC_INCLUDE_PATH`, `CCC_OVERRIDE_OPTIONS`,
`CLANG_CONFIG_*`, etc.). System headers are classified strictly by resolved path under Clang's
built-in or `-isystem` search directories (read from `clang -E -v`, never from linemarker
flag `3`), and an AST node is considered system only if BOTH its spelling and expansion locations
are system files; any user-defined or `-D` macro expanded inside a system header,
`#pragma`/`_Pragma` `GCC`/`clang` `system_header`, and `#line`/linemarker directives in user files
are refused in all spellings (including digraphs `%:`, trigraphs `??=`, and macro-generated
`_Pragma`). Every function with a body in any non-system file of the translation unit (including
project headers under `root` and non-system headers outside `root`) must be covered as a selected
method or an inlined file-local `static` helper; any uncovered function body (including
narrowed-out functions, non-first-parameter functions, by-value receivers, free functions, unused
`static` helpers, `inline`/`__`-named non-system header bodies, or `void*`/pointer callbacks) is
refused as `unchecked`, named explicitly in the verdict, and exits `2`. Symbol aliases/exports
(`__attribute__((alias(...)))`, `#pragma weak`, `_Pragma("weak ...")`, weak aliases, file-scope
`__asm__`, attributed/constructor/destructor or post-definition function declarations), non-system
globals with pointers/function pointers (including struct/array fields) or function-referencing
initializers, and any user-code preprocessing divergence across build-mode configurations (`NDEBUG`
undefined/`0`/`1`, `-O0`/`-O2`/`-Os` for `__OPTIMIZE__`/`__OPTIMIZE_SIZE__`,
`-fsanitize=address,undefined` / `__SANITIZE_*`, and `DEBUG` undefined/`0`/`1`/`2` — checked by
comparing the preprocessed user-code token stream, immune to digraphs and macro pasting) are also
refused. Every verdict lists the exact `coveredFunctions` (and any inlined `coveredHelpers`)
together with the active `macroConfig` (`target` triple, compiler version and verified absolute
`compilerPath`, `libc` version, SHA-256 digest and path list of every included user file
`userFilesSha256`/`userFiles` and every included system header `systemHeadersSha256`/`systemHeaders`,
effective `std` and `__STDC_VERSION__`, scrubbed allowlisted
environment status, `-I` flags, `-D` flags, and whether `NDEBUG`, `__OPTIMIZE__`, and `DEBUG` were
defined or undefined). CLI exit codes are `0` (`proven`: every site proved clear and re-verified by
`verifyCSafetyProof` via `checkLaws` or `checkKInduction`), `1` (`broken`: counterexample trace
replayed natively under Clang ASan/UBSan with site-matched diagnostics `matchedSite`), and `2`
(`unproven` or `unchecked`: neither proven nor reproduced at the target site, the input leaves the
covered subset, a custom/wrapper compiler or forbidden preprocessor directive/macro is used,
uncovered TU functions exist, or an unhonoured `gdp: safety` lookalike directive was found).

Every `CSafetyResult` carries the four stated assumptions and checked-scope premises verbatim in
`result.assumptions` (`core/c/safety.ts`):

1. **ABI, types & compiler/macro configuration (assumption)**: Clang is resolved from a fixed safe
   `PATH` (`/usr/bin:/bin:/usr/local/bin:/opt/swift/usr/bin:/opt/homebrew/bin:/Library/Developer/CommandLineTools/usr/bin`)
   to a verified native executable (custom `clang` options, scripts, wrapper binaries whose `-dM`/`-E -v`
   differ from direct `-cc1`, external `.cfg` files, and compiler flags outside `-I`/`-D`/`-U`/`-std=`/`-O*`/`-W*`
   are refused) running in a closed-world allowlisted environment (`PATH`, `LC_ALL=C`, `TMPDIR` only),
   with 8-bit `char`, 16-bit `short`, 32-bit `int`, and two's-complement signed integers under the
   reported target triple, compiler & absolute path, `libc` version (e.g. `glibc 2.39`), SHA-256 digest
   and path list of every included user file (`userFilesSha256`/`userFiles`) and every included system
   header (`systemHeadersSha256`/`systemHeaders`), C standard (`__STDC_VERSION__`/`std`), `-I`/`-D`
   flags, and macro configuration (`macroConfig`; only covered scalar types up to 32 bits, constant
   lookup tables, and fixed arrays of known extent are modeled). Same-UID concurrent processes on
   the analysis host are trusted (outside the threat model, as a same-UID attacker could equally
   modify `gdp-wired` or Clang directly).
2. **Ownership, zeroed start & aliasing (assumption)**: Selected methods execute sequentially on
   one live, zero-initialized receiver (or single-declaration file-local `static` globals from
   their C initialization) with non-aliasing receiver and scalar out-parameters, no concurrency,
   and no external mutation from other translation units.
3. **Checked TU closure & failure paths (checked)**: System headers are classified strictly by
   resolved path under Clang's built-in search directories (never linemarker flag `3`; **caveat**:
   system headers under Clang's default search list — including `/usr/local/include` on Linux and
   Homebrew directories such as `/opt/homebrew/include` on macOS — are trusted as system headers,
   with every included system header's resolved path and snapshot SHA-256 pinned in `macroConfig`),
   and an AST node is system only if both its spelling and expansion locations are system files.
   The complete include closure (both user files and system headers) is discovered by Clang
   (`-E -H`) on the original tree, resolved component-wise (without collapsing `..` before
   symlinks), verified via `O_NONBLOCK`/`O_NOFOLLOW` `fstat` as regular files (refusing
   case-insensitive `/proc`, `/dev`, `/sys`, non-regular files/FIFOs, `-I` directories overlapping
   system directories, user-visible includes resolving into system directories, absolute includes,
   and user includes outside the root/`-I` boundary), snapshotted once into a private temp tree
   locked read-only (`0500` dirs, `0400` files) with `-nostdinc` and mapped `-I`/`-isystem` search
   dirs, cross-checked via Clang `-H` on every snapshot pass (preprocessor, AST, expanded tokens,
   alt-path/cwd/mtime/`SOURCE_DATE_EPOCH` differentials, and build-mode alternates, which snapshot
   any extra variant system headers under `-nostdinc` and never fall back to live system dirs) for
   exact include-list and order equality, walked at the end to refuse any modified, removed, or
   added files/directories in the snapshot, digested from those snapshot bytes for both user files
   and system headers, and re-hashed on disk at the end to refuse concurrent writers (modified or
   added files in the snapshot plus modified original user/system files; same-UID concurrent
   processes remain outside the threat model). Any user-defined or `-D` macro expanded inside a system header is
   refused. User files are audited from Clang's own raw/expanded token streams and preprocessor
   (`-Xclang -dump-raw-tokens` verified byte-contiguously from byte 0/BOM to EOF with raw NUL bytes
   refused, `-Xclang -dump-tokens`, and `-E -H -dD`): all 9 trigraph
   sequences (`??=` `??/` `??'` `??(` `??)` `??!` `??<` `??>` `??-`) and non-C23 digit-quote
   sequences are refused outright; only literal `#include`, `#define`, `#undef`,
   `#if`/`#elif`/`#ifdef`/`#ifndef`/`#elifdef`/`#elifndef`/`#else`/`#endif`, `#pragma once`, and
   `#error`/`#warning` are allowed; every `#if`/`#ifdef`/`#ifndef`/`#elif`/`defined()` may
   reference only macros defined earlier in user files or listed in `-D` flags (any predefined or
   undefined-elsewhere macro, `__has_*` query, `_Pragma`, non-`once` `#pragma`, token pasting `##`,
   `<scratch space>` expansion, invocation-dependent macro
   `__FILE__`/`__BASE_FILE__`/`__FILE_NAME__`/`__TIMESTAMP__`/`__DATE__`/`__TIME__`/`__COUNTER__`/
   `__LINE__`/`__INCLUDE_LEVEL__`, `SourceLocExpr`/`PredefinedExpr`, or any `__builtin_*`
   identifier is refused with its name and line), backed by differential checks comparing both preprocessed tokens
   and folded AST facts (array sizes, constants, types) across alternate path/filename length, file
   mtime, `SOURCE_DATE_EPOCH` days, distinct empty working directories with `stdin=/dev/null`, and
   `NDEBUG`/`-O0`/`-O2`/`-Os`/`-fsanitize=address,undefined`/`DEBUG`.
   Every function with a body in any non-system file of the translation unit must be covered as a
   selected method or an inlined file-local `static` helper, or is refused as `unchecked` and
   named. Symbol aliases/weak/file-scope `__asm__`/attributed or post-definition function
   declarations, non-system globals with pointers/fn-ptrs (including struct/array fields) or
   function-referencing initializers, bodyless prototypes taking the entry type or pointers, and
   configured failure returns (`fails`) after state writes are also refused.
4. **First-fault & replay scope**: Only the first tracked array/table-bounds, signed-overflow, or
   division/remainder fault is checked. Broken obligations require site-matched ASan/UBSan replay
   (`matchedSite`); unproven sites are never claimed proven or broken. Abstract stutter on fault
   is a monitor convention, not native rollback.

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
