# Changelog

What changed since the first public release, 0.6.0 (2026-10-18). Times are measured on Modal (2 vCPU per job unless
noted), each with the command that reproduces it.

## Unreleased

- A law over several steps may read a condition an earlier step kept at a key a later step's request names, not only at
  that step's witness (`examples/quantifiers.ts`: a child derived from its parent's grants, then used, uses only the
  parent's).
- `rule.foldsOf({Lines: [...]}, params)`: a carried list's folds at its end, computed from its items without running the
  rule (a rule whose laws are all decisions needs no state to compare its folds with the code it describes).
- (0.12.4, noted) Kernels compiled into one module no longer share an identical preamble: each declares the runtime
  helpers it calls. A helper's body is the same under its name within a release, so hoisting the union by name is safe.

## 0.12.4

- A law over several steps may read a condition a step kept: an earlier step's condition at every key is assumed at a
  later step's witness, where the later check would fail (`examples/quantifiers.ts`: a scope normalized, then rechecked
  against itself, keeps it). The prover tries it when the shared instances don't prove the law; the Lean twin's check
  lets a quantified flag's keys name a later step's variables (Sets.lean, `sframe_hyps`, proven: where the flag is 1 its
  condition holds at every key).
- A decision (`decide`) about a list a request carries assumes the folds' starts, steps and lemmas, at the list's end and
  wherever it reads the list, as the rule's step does; `crossCheckDecision` reads such a list's maps as 0 past their
  cells.
- A compiled module declares only the runtime helpers it calls.

## 0.12.3

- Lean checks by `native_decide` on request: `toLean(items, {native: true})`, or `GDP_LEAN_NATIVE=1`, or the suite's
  `--native`. Compiled Lean: a 64-step law's theorem checks in 5.9 s instead of 49 s. Each such theorem also rests on an
  axiom of its own that `#print axioms` names (it trusts Lean's compiler and runtime); the default stays on Lean's
  kernel and its core axioms.

## 0.12.0 – 0.12.2: speed

The prover, its solver and the Lean checker, profiled and rebuilt where the time went. No API changes; every
certificate still checks in TypeScript and in Lean.

| | Before | After | Reproduce |
| --- | --- | --- | --- |
| A 64-step law, proven | 87 s | 5.1 s | `bun research/perf/probe-limits.ts steps` |
| A 32-step law, proven | 8.8 s | 1.1 s | the same |
| A 32-step law, built and checked by Lean | 801 s | about 50 s | `ARGS=1 KS=32 bun research/perf/probe-limits.ts lean <dir>` |
| A 64-step law, checked by Lean (its theorem) | out of reach | 47 s | `KS=64`, the same |
| A variant of 64 cases, proven | unproven in its 20 s budget | 3 s | `bun research/perf/prover-stress.ts --family cases` |
| The search tree and sheet of rows, checked by Lean (`lean-nodes`) | 424 s | 74 s | `modal/suite.json` |
| The soundness fuzz, 32 shards | 8,795 job-s | 320 job-s | `modal/suite.json` (`fuzz-*`) |
| The whole suite, 159 jobs | 11,247 job-s | 1,404 job-s | `modal/suite.json` |

- Lean: a leaf's rows come with hints saying where to find them; rows are sparse throughout the checker (their nonzero
  coefficients alone); the certificate replay keeps its rows newest first instead of rebuilding a chain of appends;
  certificates name the hypotheses they refute; terms compare by a Boolean structural equality.
- The solver: the variable to eliminate chosen from an index built once per round, and an elimination given up before
  a round that would make more than five times its row cap (one such round built 18 million rows on a fuzz goal).
- The prover: values reused through a trie of the decisions they read; the hypotheses about the conclusion's own names
  split first (the two-key example's proof went from 445 leaves to 16); before a split, the rows the plain search sets
  aside tried by their Farkas rows (a 64-case variant needs n leaves, not about 2n²); a focused solve's two hops kept to
  two.
- The runtimes: a condition at every two keys read only as map keys decides on each cell and the keys after it.
- The suite compiles the Lean library once per version of its sources, on a Modal volume.

## 0.12.0: conditions at every two keys

- `everyKey((i, j) => ...)`, a condition at every two keys or three in a step: each key read on its own, compared with
  the others plainly (`i.lt(j)`). Decided by the runtimes on a few keys per breakpoint, closed by the kernel at the pairs
  a proof names, and checked in Lean, whose quantified flags take any number of keys (`examples/pairs.ts`: a list taken
  only when it increases, names taken only when none repeats).

## 0.11.0: trees in the state, longer step laws

- Tables of nodes (`.nodes(...)`): trees and lists of lists in a rule's state, each node made from nodes already there,
  its folds kept with it (`examples/trees.ts`: a search tree, a sheet of rows of cells).
- Folds over trees with any number of children (`fold(...).children(...)`: an org chart), folds over the lines a
  request carries that read the rule's params (`examples/invoices.ts`: metered lines).
- Step laws over up to 64 steps (up from 16).
- The runtimes call a function of several arguments on its arguments (keys past 2^53 no longer overflow).

## 0.10.0 – 0.10.1: lists a request carries, folds over trees

- `.carriesList(...)`: the lines of an invoice, with folds over them and lemmas about the folds proven by induction
  (`examples/invoices.ts`).
- Folds over trees as values, their laws proven by induction over the tree (`examples/folds.ts`).
- 0.10.1: the prover splits the conclusion's atoms first, refutes by Farkas rows at its nodes, lifts refutations past a
  split they don't read, and reuses rows.

## 0.9.0: the Lean twin takes facts about several keys

- Facts about several keys, and liveness and refinement proofs that carry them, checked in Lean; Lean checks the
  kernel's own proof of a recurrence's lemmas.

## 0.8.0: records, variants and the lemmas you state

- Records and variants as kinds, in inputs, state, results, map cells and list items (`examples/datatypes.ts`).
- `recur(...)`: a function defined by a recurrence, and lemmas about it proven by induction, which every rule that reads
  it may use (`examples/lemmas.ts`).

## 0.7.0: gdp-ts proofs from proven checks

- `gdp-wired/gdp`: gdp-ts proofs minted by checks gdp-wired has proven (`examples/gdp.ts`).
- Twelve more example domains: 187 rules across 21, each proven, broken by a real run when broken, and checked by Lean.
- The skill: `npx skills add monotykamary/gdp-wired`.

## Modal

From 0.6.0 to 0.12.3, the development ran 3,890 Modal containers in 89 runs, about 56 hours of job time: the suite, the
fuzz shards, the benchmarks and every Lean check (counted from the runs' `summary.tsv`, one container per job; the GPU
searches and the film's renders ran apart from these).
