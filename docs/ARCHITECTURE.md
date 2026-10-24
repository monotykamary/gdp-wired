# Architecture

gdp-wired is a search that proposes and a kernel that checks. A front end turns something people wrote (a builder
chain, an XState machine, a reducer, a C program, a CHC system, a TIP problem) into a rule: a step machine, a loop, a
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
| The front ends | `core/dsl.ts`, `core/xstate.ts`, `core/chart.ts`, `core/extract*.ts`; `compare/chc/translate.ts`, `compare/tip/translate.ts`, `compare/term/translate.ts`, `compare/term/c2ari.py` | no | a proof about another rule than the one meant | differential runs of the rule against the source's own semantics; refusals with reasons |
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
the search and the runtimes don't change. The four that exist are the templates:

- **The TypeScript builder** (`core/dsl.ts`): typed chains (`rule(...).params().inputs().state().step()`) whose terms
  are kernel `E`s; names are checked by the kernel's own `scope` before any goal, and kinds (`nat`, `upTo`, `oneOf`,
  `maybe`, records, variants, lists) compile to state variables with the laws that keep their encoding (`kindLaws`).
  Its check is the type checker plus `builders.test.ts` and `values.test.ts`: every kind's encoding run against its
  values.
- **XState** (`core/xstate.ts`, `core/extract-xstate.ts`): `fromXState` reads a v5 machine's config into a chart
  (`core/chart.ts`), each named guard and action given again as a condition or a write; `conforms` runs the real XState
  actor and the compiled rule on the same random events and compares every state and context.
- **The extractor** (`core/extract*.ts`): reads a reducer or a class through the TypeScript compiler, executes one step
  symbolically into terms, refuses what is outside its subset where it is; `extract-check.ts` runs the code as it
  ships (in a VM, with branch counters) beside the rule's interpreter and its generated JavaScript, from the start,
  from drawn states and from the prover's own counterexamples, and refuses the extraction on any difference.
- **The C front end** (`compare/term/c2ari.py`, then `compare/term/translate.ts`): SV-COMP C through pycparser to an
  integer transition system (ARI), then to a kernel `Loop` with the same runs; `ari.ts`'s evaluator shares no code with
  gdp-wired and replays every nontermination witness (`checkLasso`); `c2ari_test.py` and `adversarial.test.ts` hold the
  translation to the C semantics (integer types, conversions, undefined behaviour ending the run).

The template, from them:

1. Read the source into the kernel's language, and refuse with a reason whatever is outside the subset; never
   approximate.
2. Keep an evaluator of the source that shares no code with gdp-wired (or the source's own runtime: XState's actor,
   the shipped code in a VM, ari.ts, TIP's evaluator, chc.ts).
3. Run both on the same inputs, every state compared: random runs from the start, values at the boundaries, steps from
   drawn states (a proof is about every state, not only those reached), and steps from the prover's counterexamples.
   Count the source's branches reached; refuse the translation on any difference.
4. Hand the rule to the provers as any other; replay every counterexample and every witness on the source's
   evaluator before reporting it.
5. Write the certificates as interchange documents (`toInterchange`), so they can be checked without gdp-wired.

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
