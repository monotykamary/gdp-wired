# gdp-wired core

Laws about stateful rules, proven inside the library, with a Lean-checked trusted core.

| File | What it is |
| --- | --- |
| `solver.ts` | Integer linear arithmetic: Fourier–Motzkin with cuts. Refutations are derivations; satisfiable cases carry a witness; otherwise `unknown`, never a wrong answer |
| `check.ts` | The TypeScript checker for derivations and witnesses |
| `machine.ts` | Step machines (state, maps, params, inputs, one step, and optionally a history of kept requests with sums, queries and relations): the interpreter (persistent, for searches) and generated JS (maps and the log updated in place, what an app ships), both refusing undeclared names (the kernel's scope check), params and inputs that aren't naturals below 2^53, and values past 2^53 − 1; induction into solver cases; real counterexample search |
| `gdp.ts` | The gdp-ts adapter (`gdp-wired/gdp`): a guard (a function's condition) or a gate (a rule's flag, the rule run compiled) mints gdp-ts proofs only where the condition holds, its laws proven when it is made; `gdp.test.ts`, and `gdp.types.ts` (type-checked only) |
| `invariant.ts` | Houdini: candidate invariants from the machine's own variables and constants, kept while inductive together, then minimized |
| `nonterm.ts` | Untrusted: the search behind `proveNeverEnds`, a run of a loop that never ends. Lassos of random runs (the set the cycle's states); policies, runs whose inputs are terms over the state (in each mode, the first allowed of a few assignments drawn from pools: 0, ±1, constants, each value ± 1), grown where the run would stop; a recurrent set fitted to a policy's run (bounds, sums and differences of the integer values, an atom per counterexample the prover gives), its closure proven by `grow` (CDCL first). The certificate is kernel.ts's `Recur`, checked by `checkRecur` |
| `rationals.ts` | Untrusted: rules over the rationals (`gdp-wired/rationals`). `ratRule` (`.params` `.inputs` `.state` `.step` `.pre` `.assume`, kinds `rat` and `nonneg`), terms (`plus` `minus` `times(k)` `over(k)`, `rmin` `rmax` `rwhen`; a product of unknowns refused), compiled to kernel.ts's `QMachine`; exact runtimes over bigint fractions (`interpretQ`, `compileQJs`/`loadQJs`, `rule.run`); `refuteQ` (the machine unrolled up to 3 requests, each goal decided over ℚ by `growQ`, a model replayed by the interpreter) and `proveQMachine` (start and step goals by `growQ`, the trees checked by `checkQMachine`); `proveRatRule`. `q.ts`: the exact rationals |
| `models.ts` | the budget rule (bounded loss), the caps rule (per-key caps), requests in flight, and a sliding-window limit with a history |
| `run-proofs.ts`, `run-strengthen.ts` | The runs below |
| `compile.test.ts`, `runtime.test.ts` | Generated JS against the interpreter (random machines, forks); the scope, natural and overflow guards; histories compiled against interpreted, and pruning that changes nothing where the kernel proves it may drop records (and is caught when it isn't proven); the window limit |
| `export-lean.ts` → `../research/lean/Obligations.lean` | Every refutation as Lean data, each a theorem by `Cert.sound` |
| `compile-lean.ts` → `../research/lean/Verdict.lean` | The machines as Lean definitions, their laws proven by `omega` |
| `../research/lean/Cert.lean` | The checker and `Cert.sound` (no sorry), and `Cert.run_preserves` (the induction rule, no axioms) |

```sh
bun test solver.test.ts       # 3,000 random integer systems against brute force
bun test compile.test.ts runtime.test.ts
bun run-proofs.ts             # bounded_loss, 4 caps PROVEN; broken variants REFUTED with traces; in-flight NOT INDUCTIVE
bun run-strengthen.ts         # finds s + 50p <= b + 150, then proves the in-flight law
TC=~/.elan/toolchains/leanprover--lean4---v4.34.0
(cd ../research/lean && $TC/bin/lean -o Cert.olean Cert.lean)
bun export-lean.ts > ../research/lean/Obligations.lean && (cd ../research/lean && LEAN_PATH=$PWD:$TC/lib/lean $TC/bin/lean Obligations.lean)  # 2,716 theorems, ~95 s
bun compile-lean.ts > ../research/lean/Verdict.lean && (cd ../research/lean && LEAN_PATH=$PWD:$TC/lib/lean $TC/bin/lean Verdict.lean)        # 6 laws by omega, <1 s
```
