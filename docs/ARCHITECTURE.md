# Architecture

gdp-wired is a search that proposes and a kernel that checks. A front end turns something people wrote (a builder
chain, an XState machine, a reducer, a Go struct's methods, a C program, a CHC system, a TIP problem) into a rule: a step machine, a loop, a
fold or a datatype law. The search looks for a certificate that the rule's laws hold: trees of linear splits with a
derivation at each leaf, ranks, recurrent sets, cyclic proofs. The kernel rebuilds the goals from the rule and checks
the certificate. The Lean twin defines the same checks and proves each sound, and re-checks the exported certificate in
Lean's own kernel. The runtimes run the rule the proof is about. The interchange format
([docs/interchange.md](interchange.md)) is the same certificate as JSON, so another language can check it too.

```
 front ends ──rule──▶ search ──certificate──▶ kernel (TypeScript) ──accepted──▶ verdict
 (untrusted)          (untrusted)              trusted: kernel.ts,      │
     │                                         cyclic.ts, check.ts      ├──▶ Lean twin (lean-kernel/*.lean):
     ▼                                                                  │    the same checks, proven sound,
 runtimes (interpreter, generated JS, watcher, GPU searches)            │    re-run by Lean's kernel
                                                                        └──▶ interchange (JSON) ──▶ gdp-wired-check,
                                                                             its WebAssembly module, other checkers
```

## The trust boundaries

| Part | Files | Trusted? | If it is wrong | What keeps it honest |
| --- | --- | --- | --- | --- |
| The kernel | `kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts` | yes | a false law accepted | its Lean twin, proven first; conformance against Lean; tamper tests |
| The kernel's arithmetic | `core/solver.ts`'s `add`, `sub`, `scale`, `k`, `v` | yes, in practice | the same | five short functions over linear forms; Lean computes the same rows independently, and a difference refuses an export |
| The Lean twin | `lean-kernel/*.lean` | yes (its axioms: propext, Classical.choice, Quot.sound) | a soundness proof of the wrong claim | `#print axioms`; each theorem's statement read against the claim it stands for |
| The Lean emitters | `lean-kernel/emit.ts`, `qlean.ts`, `lean-terms.ts` | no | Lean refuses the export | Lean checks every claim it writes |
| The search | `kernel/prove.ts`, `cdcl.ts`, `simplex.ts`, `reader.ts`, `qprove.ts`; `core/discover.ts`, `infer.ts`, `cycles.ts`, `cyclic.ts`, `data.ts`, `nonterm.ts`, `accel.ts`, `relation.ts`, `kind.ts`, `bmc.ts` | no | a law left unproven, or slow | the kernel checks what it returns |
| The front ends | `core/dsl.ts`, `core/xstate.ts`, `core/chart.ts`, `core/extract*.ts` (with `core/go/reader.go`); `compare/chc/translate.ts`, `compare/tip/translate.ts`, `compare/term/translate.ts`, `compare/term/c2ari.py` | no | a proof about another rule than the one meant | differential runs of the rule against the source's own semantics; refusals with reasons |
| The runtimes | `core/machine.ts` (`interpret`, `compileJs`), `core/watch.ts`, the GPU searches (`research/gpu/`, `research/hw/`) | no | the shipped code does something the proof isn't about | differential runs against `evalE`/`evalC` (`core/conformance.ts`), and Lean's `evalE`/`evalC` agreeing with them (`Conformance.lean`) |
| The interchange reader | `interchange/format.ts`, `interchange/check.ts` | no | a document checked as another | the checker writes what it read back and refuses the document unless it is the same |

Why each boundary sits where it does:

- **The kernel is the smallest code that turns a rule into goals and decides a tree.** Every induction rule (laws,
  step laws, k steps, k-induction, progress, liveness, loops, folds, histories, sets) is a few moves of one algebra of
  runs, so the trusted code is the algebra and the tree check, not one checker per feature. It is written to be read
  against its Lean twin definition by definition, and it changes only once the Lean soundness proof is written, on
  the standard axioms. `core/check.ts` is the derivation check alone (inputs, combinations, cuts), the one piece every
  kind ends in.
- **The Lean twin is the referee.** The TypeScript is what runs, Lean is where the soundness argument lives: each check
  is defined in Lean (`checkGoal`, `checkMachine`, `checkKInd`, `checkRecur`, `checkCyclic`, `Q.checkGoal`) and proven
  sound (`sound`, `machine_sound`, `kind_sound`, `never_ends_of`, `cyclic_sound`, `leads_sound`, `loop_halts_of`,
  `fold_sound`). An export hands Lean the rule and the trees; Lean builds the goals from the rule itself and checks the
  trees with `decide +kernel`. A bug in the TypeScript kernel would show as a certificate Lean refuses.
- **The search is untrusted because it is the large, fast-moving part.** It may be incomplete, nondeterministic in
  wall time (counted searches read `clock()`, never wall time), or wrong about a model: nothing it returns is believed
  until the kernel checks it. New search lines go there, never into the kernel.
- **The front ends are untrusted, and their failure mode is a different statement, not an unsound proof.** A wrong
  translation makes the kernel prove a true fact about the wrong rule. So each front end runs the rule beside the
  source and compares every state, with an evaluator that shares no code with gdp-wired where the source has one.
- **The runtimes are untrusted for the same reason.** The proof is about `evalE`/`evalC`'s semantics; the interpreter,
  the generated JavaScript, the watcher and the GPU kernels are checked against that semantics by differential tests,
  and Lean's own evaluator is checked against the same reference.
- **The interchange reader is untrusted but guarded.** `gdp-wired-check` is the kernel's entry points bundled as they
  are; the reader in front of them must say faithfully what a document holds, so the checker writes the certificate it
  read back to JSON and refuses the document unless the two agree. A reader bug would then need an equal and opposite
  writer bug to go unseen.

## How to add a front end

A front end produces a `Machine` (or a `Loop`, a `Fold`, a `QMachine`, a datatype law) and nothing else; the kernel,
the search and the runtimes don't change. The five that exist are the templates:

- **The TypeScript builder** (`core/dsl.ts`): typed chains (`rule(...).params().inputs().state().step()`) whose terms
  are kernel `E`s; names are checked by the kernel's own `scope` before any goal, and kinds (`nat`, `upTo`, `oneOf`,
  `maybe`, records, variants, lists) compile to state variables with the laws that keep their encoding (`kindLaws`).
  Its check is the type checker plus `builders.test.ts` and `values.test.ts`: every kind's encoding run against its
  values.
- **XState** (`core/xstate.ts`, `core/extract-xstate.ts`): `fromXState` reads a v5 machine's config into a chart
  (`core/chart.ts`), each named guard and action given again as a condition or a write; `conforms` runs the real XState
  actor and the compiled rule on the same random events and compares every state and context.
- **The extractor, TypeScript** (`core/extract*.ts`): reads a reducer or a class through the TypeScript compiler,
  executes one step symbolically into terms, refuses what is outside its subset where it is; `extract-check.ts` runs
  the code as it ships (in a VM, with branch counters) beside the rule's interpreter and its generated JavaScript, from
  the start, from drawn states and from the prover's own counterexamples, and refuses the extraction on any difference.
- **The extractor, Go** (`core/extract-go.ts`, `core/go/reader.go`, `core/extract-go-check.ts`): a struct and its
  methods read through go/parser and go/types, executed symbolically into the same Model; the check builds the
  package in its own module with a generated harness and compares every state the same way. It is the worked example
  below.
- **The C front end** (`compare/term/c2ari.py`, then `compare/term/translate.ts`): SV-COMP C through pycparser to an
  integer transition system (ARI), then to a kernel `Loop` with the same runs; `ari.ts`'s evaluator shares no code with
  gdp-wired and replays every nontermination witness (`checkLasso`); `c2ari_test.py` and `adversarial.test.ts` hold the
  translation to the C semantics (integer types, conversions, undefined behaviour ending the run).

The template, from them:

1. Read the source into the kernel's language, and refuse with a reason whatever is outside the subset; never
   approximate.
2. Keep an evaluator of the source that shares no code with gdp-wired (or the source's own runtime: XState's actor,
   the shipped code in a VM or built by its own toolchain, ari.ts, TIP's evaluator, chc.ts).
3. Run both on the same inputs, every state compared: random runs from the start, values at the boundaries, steps from
   drawn states (a proof is about every state, not only those reached), and steps from the prover's counterexamples.
   Count the source's branches reached; refuse the translation on any difference.
4. Hand the rule to the provers as any other; replay every counterexample and every witness on the source's
   evaluator before reporting it.
5. Write the certificates as interchange documents (`toInterchange`), so they can be checked without gdp-wired.

### A second language for the extractor: Go

The extractor's intermediate is its Model (`core/extract-read.ts`): the state's variables, maps and lists, the
inputs and the event that picks a method, one term per state variable over them (`core/extract-ir.ts`), the
refusals, and how a request is made of the code. Everything from the Model on is shared: the sorts and the printer
(`core/extract-print.ts`), the rule built from the printed source and its invariants (`core/extract.ts`'s
`fromModel`, which both front ends call), and the rule's side of the check (`ruleSnap`, `ruleState`, `sameSnap`,
`draw`, `constantsOf`, `conditionsOf`, `condAt` in `core/extract-check.ts`). A language brings two pieces:

- **A reader**: its own parser and type checker, run by its own toolchain, printing the AST with each expression's
  type and folded constant as JSON (`core/go/reader.go`, 755 lines of Go, deciding nothing); then a symbolic
  executor of that JSON into the Model, with the language's semantics exactly (`core/extract-go.ts`). Go's are:
  - integers wrap at their width: at 8 to 32 bits the term is taken modulo 2^n by cases, as c2ari.py takes C's
    unsigned arithmetic (`x + 1` past 2^32 − 1 is 0), conversions and products by a floor division; at 64 bits the
    rule's numbers stop at ±2^53 (its runtime refuses past them), and a uint64 below 0 is refused;
  - division truncates toward zero;
  - pointers alias (a heap of objects, interior pointers `&x.f`, a pointer chosen by a condition written by cases);
  - struct values copy; a `*big.Int` is an unbounded integer with nil a state of its own;
  - an error that isn't nil and a panic are refusals, with the state as it was there (or, where the caller drops
    what a failed call wrote, `onError: 'discard'`, cited per source in `research/extract/go-options.json`).
  The executor refuses where Go leaves the subset, with the place: loops, a range over a map (its order is random),
  a slice under a second name (two slices may share a backing array), defer but a mutex's Unlock, floats, interfaces,
  generics, another module's code.
- **A runner**: the code run in its own runtime beside the rule. `core/extract-go-check.ts` writes a harness into the
  package (set the object from a JSON state, call a method with JSON arguments, recover a panic, print the state, and
  ask that the fields the rule leaves out are unchanged), builds it with `go build -cover` in the package's module
  (its go.mod and dependencies), and sends it every request at once: the runs from the start are drawn on the rule's
  side (the code must follow the same states, or the first difference refuses), the drawn states and the prover's
  witnesses are single steps. Go's coverage counts the blocks reached.

`core/extract-go.test.ts` holds the semantics adversarially: overflow at each width (and a model edited to forget
the wrap, which the check refuses), aliasing through pointers and interior pointers, maps (a nil map's write, a range
over one refused), slices sharing a backing array, defer and a lock taken twice, panics and errors after a write,
truncated division, narrowing conversions, embedded methods and value receivers; each extracted is also proven of
the rule (`proveSteps`) on the exact Go value.

**Solidity next.** The same two pieces: solc's `--ast-compact-json` with its types as the reader's input; the
executor's semantics are uint256 and int256 reverting on overflow in Solidity ≥ 0.8 (a refusal, as Go's uint64 below
0 is here, except that the rule's numbers stop at 2^53 long before 2^256, so the claim stops there too), `unchecked`
blocks wrapping (modulo 2^256: past the rule's range, refused), `require` and `revert` as the rule's refusals with the
state rolled back (the EVM's own `onError: 'discard'`), `mapping` as maps (every key present at zero, so no `has`),
`msg.sender` and `block.timestamp` as inputs, and inherited contracts linearized in C3 order. The runner is a local
EVM (anvil, or py-evm) with a generated test contract or a script that sets storage, calls, and reads it back.

## How to add a certificate kind

A new kind of certificate is a new trusted rule, so the order is fixed:

1. **Lean first.** In `lean-kernel/<Kind>.lean`: the certificate's data, the check as a `Bool` function, and its
   soundness theorem stating exactly the claim the kind will make, on the standard axioms (`#print axioms`). If the
   proof is out of reach, the kind waits.
2. **The TypeScript twin.** In `kernel/kernel.ts` (or `kernel/cyclic.ts`): the same definitions, name for name, built the
   same way (Lean's goal builders and kernel.ts's must make the same hypotheses in the same order, since a derivation
   names rows by their place). Refuse anything outside the language before a goal is made. The search that finds the
   certificate goes in the untrusted part.
3. **Conformance.** In `core/conformance.ts`: a generator of cases with the certificate found and tampered twins (each
   named by what was changed), with kernel.ts's answer; in `lean-kernel/conformance.ts`, a flag that writes each case as
   `example : check… = b := by decide +kernel` for Lean to compute; a suite job running both. Tamper tests in
   `kernel/tamper.test.ts`; a fuzz against a brute-force reference where one exists.
4. **The interchange.** A `$def` and a kind in `interchange/schema.json`, its reader and writer in
   `interchange/format.ts`, its check in `interchange/check.ts` (the kernel's entry point), its capture in
   `interchange/capture.ts`, its Lean emission in `interchange/lean.ts`, and the format's minor version raised.
5. **The CHANGELOG** names the trusted change and its Lean theorems.

## How the benchmarks and corpora are measured

- **The benchmarks** (`compare/chc`, `compare/tip`, `compare/term`): problems gdp-wired didn't write, read by a
  translator with its own evaluator. Every task runs in its own container (Modal or a boat VM, 2 vCPU, 4 GB) under one
  wall-clock limit for every tool (60 s), the rivals as installed in `compare/*`. Each answer is checked as the harness
  checks it: a proof is one the kernel accepted; an unsat or a counterexample is a run confirmed by the problem's own
  evaluator (`checkDerivation`, TIP's evaluator, `checkLasso`); a verdict is compared with the expected one where the
  benchmark has it (SV-COMP's, CHC-COMP's decided tasks), and every wrong answer is counted. A change is measured
  against a run of main launched at the same time on the same backend, task by task: every task gained and every task
  lost, with its reason.
- **The corpora**: `research/frontier/` and `research/frontier2/` (laws that need a statement nobody wrote, from the
  benchmarks' unsolved groups), each item with broken variants that must be refused; `research/realworld/` (rules
  written from open-source code, the laws a reviewer would ask, its verdicts kept). A change keeps each unchanged or
  better, every broken variant refused.
- **The suites** (`modal/suite.json`, 217 jobs): by default, then with `--usual` (the usual trees as every certificate,
  rather than the cyclic proofs), one at a time; the 5 s-limited tests on 1 vCPU, measured against main interleaved
  where a change touches their paths.
- **The interchange**: `interchange/suite-jobs.ts` runs the suites again with every certificate captured
  (`interchange/capture.ts`), each written as a document, read back in the same process (the identity), then checked in
  other processes by the bundled checker, its WebAssembly module and the second checker, against the kernel's answer
  where it was made, with three tampered twins of each; `interchange/lean-jobs.ts` sends the conformance cases to Lean
  through the same documents.
- **Figures** are never rounded, extrapolated or invented: each traces to a run directory. A lead counts only once
  confirmed under the competition's own setup (its time limit, scoring and current entrants).
