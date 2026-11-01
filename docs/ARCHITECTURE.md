# Architecture

gdp-wired is built as a search that proposes and a kernel that checks. A front end reads something people wrote into
a rule: a step machine, a loop, a fold or a datatype law. The search looks for a certificate that the rule's laws
hold. The kernel builds the goals from the rule itself and checks the certificate against them. The Lean twin defines
the same checks, proves each one sound, and checks the exported certificates again in Lean's own kernel. The runtimes
run the rule the proof is about. The interchange format ([interchange.md](interchange.md)) writes the certificate as
JSON, so a checker in another language can check it with no gdp-wired at all.

```
 front ends ──rule──▶ search ──certificate──▶ kernel (TypeScript) ──accepted──▶ verdict
 (untrusted)          (untrusted)             trusted: kernel.ts,       │
     │                                        cyclic.ts, check.ts       ├──▶ Lean twin (lean-kernel/*.lean): the same
     ▼                                                                  │    checks, proven sound, re-run by Lean
 runtimes (interpreter, generated JS, watcher, GPU searches)            └──▶ interchange (JSON) ──▶ gdp-wired-check
 held to evalE/evalC                                                         (bundle, executable, WebAssembly), check.py
```

## The trust boundaries

Each boundary has a trusted side, an untrusted side, and the way a bug on the untrusted side can show. Each has its own
guard in the code, and a regime that keeps testing that guard.

| Boundary | A bug on the untrusted side would | Guard in the code | Regime: the suite jobs and the treadmill |
| --- | --- | --- | --- |
| **Search vs kernel.** The search (`kernel/prove.ts`, `cdcl.ts`, `reader.ts`, `simplex.ts`, `qprove.ts`; `core/discover.ts`, `infer.ts`, `cyclic.ts`, `data.ts`, `nonterm.ts`, `accel.ts`, `relation.ts`, `bmc.ts`) is untrusted. The kernel (`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts`, and `core/solver.ts`'s `add`, `sub`, `scale`, `k`, `v`) is trusted. | leave a law unproven, or run slowly. It can't make the kernel accept a false law. | The kernel builds every goal from the rule (`obligations`, `stepLawObligations`, `loopObligations`, …) and only reads the certificate's trees. It refuses anything outside its language before a goal is made (`scope`, the reserved names). | The brute-force soundness fuzz `kernel/kernel.test.ts`: a refutation the kernel accepts must have no model over a finite domain, else `UNSOUND`. It runs as `fuzz-12345` and `fuzz-1` to `fuzz-31`. `kernel/cdcl.test.ts` with `GDP_CDCL_VERIFY=1` compares the CDCL reader's rows with kernel.ts's at every node (`cdcl-fuzz-1` to `cdcl-fuzz-4`). `tamper.test.ts` and `refusals.test.ts` (`tamper-refusals`). The mutants of kernel.ts and check.ts (`kernel/mutants.ts`, [MUTANTS.md](../kernel/MUTANTS.md)): 959 mutants, 876 killed, and every survivor listed with the reason it is equivalent. The treadmill's `sound` chain (`supercomputer/treadmill.py`) runs fresh seeds every day and reruns the mutants whenever the trusted files change. It files a failure as soundness, coverage or infrastructure (`fuzz_class`), and only soundness alerts. |
| **TypeScript kernel vs Lean twin.** Lean (`lean-kernel/*.lean`) is the referee, on the axioms `propext`, `Classical.choice` and `Quot.sound`. | accept a certificate that Lean refuses. | Each check is defined in Lean and proven sound: `sound`, `machine_sound`, `kind_sound`, `never_ends_of`, `cyclic_sound`, `leads_sound`, `loop_halts_of`, `fold_sound`. kernel.ts changes only after its Lean proof exists. | `core/conformance.ts` generates cases, each with tampered twins, and records kernel.ts's answer. `lean-kernel/conformance.ts` writes each case as `example : check… = b := by decide +kernel` (`lean-rationals`, `lean-nonterm`, `lean-kind`, `lean-sums`, `lean-rings`). Every example rule's certificate is exported and checked by Lean, and its tampered twins must compute to false (`lean-examples-*`, `lean-sets`, `lean-exists`). Through the interchange, `interchange/lean-jobs.ts` sends the conformance cases and a sample of the suites' own certificates with their twins. |
| **The exporters.** The Lean emitters (`lean-kernel/emit.ts`, `qlean.ts`, `lean-terms.ts`) and the interchange writer and reader (`interchange/format.ts`) are untrusted. | make Lean refuse a true claim, or state a different claim. | Lean gets the rule and the trees, builds the goals from the rule itself, and decides them with `decide +kernel`. The interchange checker writes the certificate it read back as JSON and refuses the document unless the two are the same (`checkDocument`'s `sameJson`). | The tampered exports must compute to false: `emit.ts`'s `encode(…, tamper)`, `qlean.ts`'s `LeafTamper`, `export-kernel.ts` and `exists-tamper.ts`. The `lean-package-*` jobs build the exported Lake project end to end. `interchange/suite-jobs.ts` captures every certificate a suite run hands the kernel, reads each one back in the same process (checking the identity), and then checks it again in other processes. Every document and twin is validated against `schema.json`. |
| **Runtimes vs the meaning.** The meaning is `core/machine.ts`'s `evalE` and `evalC`. The runtimes are untrusted: `interpret`, `compileJs` and `loadJs`, the watcher (`core/watch.ts`), the u32 GPU twin, and the loop programs in `research/hw`. | ship code that does something other than what the proof is about. | Each runtime is compared with the reference evaluator, and Lean's own `evalE` and `evalC` are compared with it too. | `conformance-1` to `conformance-8` run random terms over every E and C operation through the interpreter, the generated JS, the kernel and the u32 twin, against `evalE`/`evalC`. Every operation must be seen, or the job fails to compile or fails coverage. `compile-*` (`compileJs` vs `interpret`), `runtime-*` and `history-*` (each law the kernel accepts holds on every interpreter run). `check-cpu` and `hw-check-*` (the GPU and loop runners vs interpreter replay and `watch.ts`). `lean-conformance` (Lean's evaluator agrees, `by decide`). |
| **Front ends vs the source.** The readers (`core/extract*.ts`, `core/xstate.ts`, `core/effect.ts`, `compare/*/translate.ts`) are untrusted. | prove a true fact about a different rule. | `drive` (`core/extract-check.ts`) runs the code as it ships beside the rule's interpreter and its generated JS: from the start, from drawn states and from the prover's witnesses. Every state, result and refusal is compared, and any difference refuses the extraction. XState and Effect have `conforms`. Every counterexample is replayed on the code. See [FRONTENDS.md](FRONTENDS.md). | `extract-py`, `-rb`, `-ex`, `-rs`, `-jvm`, `-swift`, `-go`, `-c` and `extract` pin every refusal and require full arm coverage. The adversarial cases (`research/langs/adversarial/cases.json`) must never yield a checked false proof. The treadmill's `xfuzz` reruns each language's tests with `XFUZZ_SEED` fresh. |
| **The standalone checker vs the document.** `gdp-wired-check` (`interchange/cli.ts`, `check.ts`) is the kernel's entry points as they are, with an untrusted reader in front. | check a different certificate from the one the document holds. | The read-back guard (above). `interchange/build.ts` builds the checker from the trusted files at their committed git blobs, prints each blob, and lists the bundle's inputs. Those are the three trusted files, `core/solver.ts` (tree-shaken to its five functions) and the interchange reader. There is no search in the bundle. | `interchange/verify.ts` checks every captured document and its three tampered twins with every build: in process, the bundle, the compiled executable, the npm bin, the WebAssembly module, and `interchange/py/check.py` (a second checker written from the spec) on the goals. The `interchange` suite job checks the round trip and the refusals. |

Why each boundary sits where it does:

- **The kernel is the smallest code that turns a rule into goals and decides a tree.** Every induction rule (laws,
  step laws, k steps, k-induction, progress, liveness, loops, folds, histories, sets) is a few moves of one algebra of
  runs. So the trusted code is that algebra and the tree check, not one checker per feature. It is written to be read
  against its Lean twin, definition by definition. `core/check.ts` is the derivation check alone (inputs, combinations,
  cuts): the one piece every kind ends in.
- **The search is untrusted because it is the large, fast-moving part.** It may be incomplete, nondeterministic in
  wall time (counted searches read `clock()`, never wall time), or wrong about a model. Nothing it returns is believed
  until the kernel checks it, and new search lines go there, never into the kernel.
- **Lean is the referee and the TypeScript is what runs.** The soundness argument lives in Lean, where each check has
  a proof. A bug in the TypeScript kernel shows as a certificate Lean refuses. The conformance cases look for one
  where no real proof would reach.
- **The exporters are untrusted because their failure is loud.** A wrong emitter makes Lean refuse. A wrong
  interchange reader would need an equal and opposite writer bug to slip past the read-back guard.
- **Front ends and runtimes are untrusted because they fail by changing the statement, not the proof.** A wrong
  translation or a wrong runtime makes the proof true of something else. So each is held to a semantics that shares
  no code with it: the source's own runtime, or `evalE`/`evalC`.

Where a guard is weaker than the table might suggest:

- `kernel/mutants.ts` mutates `kernel/kernel.ts` and `core/check.ts` only. `kernel/cyclic.ts` is held by Lean
  checking its certificates again (`lean-cyclic`, `lean-bridge`, and the cyclic twins in `ix-lean-*`) and by the tamper
  tests, not by mutants.
- `#print axioms` is printed for every exported theorem (`emit.ts`). The Lean jobs fail on `sorry`; the axiom lists
  are read, not compared by a gate.
- No job feeds random or malformed source text to the readers' parsers. The readers decide nothing past the syntax,
  and the executor refuses what has no IR node.

## How to add a front end

See [FRONTENDS.md](FRONTENDS.md). It covers the extractor's contract, the differential check, the CLI's comment-law
contract, and Python as the worked example.

## How to add a certificate kind

A new kind of certificate is a new trusted rule, so the order is fixed:

1. **Lean first.** In `lean-kernel/<Kind>.lean`, write the certificate's data, the check as a `Bool` function, and its
   soundness theorem. The theorem states exactly the claim the kind will make, on the standard axioms. If the proof
   is out of reach, the kind waits.
2. **The TypeScript twin.** In `kernel/kernel.ts` (or `kernel/cyclic.ts`), write the same definitions, name for name,
   built the same way. Lean's goal builders and kernel.ts's must make the same hypotheses in the same order, since a
   derivation names rows by their place. Refuse anything outside the language before a goal is made. The search that
   finds the certificate goes in the untrusted part.
3. **Conformance.** In `core/conformance.ts`, write a generator of cases: the certificate found, its tampered twins
   (each named by what was changed), and kernel.ts's answer. In `lean-kernel/conformance.ts`, add a flag that writes
   each case as `example : check… = b := by decide +kernel`, and a suite job that runs both. Add tamper tests in
   `kernel/tamper.test.ts`, refusals in `kernel/refusals.test.ts` (one per guard, so a mutant of it dies), and a fuzz
   against a brute-force reference where one exists.
4. **The interchange.** Add a `$def` and a kind to `interchange/schema.json`, its reader and writer to
   `interchange/format.ts`, its check to `interchange/check.ts` (the kernel's entry point, and `decidedBy`), its
   capture to `interchange/capture.ts`, and its Lean emission to `interchange/lean.ts`. Raise the format's minor
   version.
5. **The CHANGELOG** names the trusted change and its Lean theorems.

## How the benchmarks and corpora are measured

- **The benchmarks** (`compare/chc`, `compare/tip`, `compare/term`) are problems gdp-wired didn't write, read by a
  translator with its own evaluator.
  - Every task runs in its own container (a boat VM or Modal, 2 vCPU, 4 GB) under one wall-clock limit for every
    tool (60 s), with the rivals as installed in `compare/*`.
  - Each answer is checked as the harness checks it. A proof counts only if the kernel accepted it. An unsat or a
    counterexample counts only if the problem's own evaluator confirms the run (`checkDerivation`, TIP's evaluator,
    `checkLasso`).
  - A change is measured against main, launched at the same time on the same backend, task by task.
- **The corpora**: `research/frontier/` and `research/frontier2/` hold laws that need a statement nobody wrote, each
  item with broken variants that must be refused. `research/realworld/` holds rules written from open-source code. A
  change keeps each verdict unchanged or better, and every broken variant refused (`gates/bar.ts`).
- **The suites** (`supercomputer/suite.json`, 243 jobs) run by default and then with `--usual` (the usual trees as
  every certificate, rather than cyclic proofs), one mode after the other.
- **The interchange** has three runs:
  - `interchange/suite-jobs.ts` reruns the suites with every certificate captured and checked by every build of the
    checker, with three tampered twins of each;
  - `suite-jobs.ts --corpus` does the same for the conformance documents `interchange/lean.ts write` makes;
  - `interchange/lean-jobs.ts` sends both to Lean.

  `interchange/aggregate.ts` sums the logs.
- **Figures** are never rounded, extrapolated or invented: each traces to a run directory. A lead counts only once it
  is confirmed under the competition's own setup (its time limit, scoring and current entrants).
