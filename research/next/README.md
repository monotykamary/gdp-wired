# gdp-wired next: synthesis, relational laws, ReBAC

| File | What |
| --- | --- |
| `synth.ts`, `run-synth.ts` | Guards from laws: the unsafe region by Fourier–Motzkin projection, its complement the weakest guard, every claim checked by the solver |
| `relational.ts`, `run-relational.ts` | Two machines side by side (`product`), migration safety (`agree`) and tenant isolation, proven by the core prover. The library's form, on rules read from code: `gdp-wired/relational` (core/relational.ts, research/regulated/DESIGN.md) |
| `rebac/model.ts` | A Zanzibar-style org and its Datalog rules; derived object tables; group closure |
| `rebac/datalog.ts` | A generic semi-naive Datalog engine over the rules as written (the reference) |
| `rebac/fast.ts`, `rebac/check-small.ts` | The fast JS audit, checked against Datalog on small orgs |
| `rebac/page.ts`, `rebac/run.ts` | The audit as a u32 WebGPU kernel against the fast JS path, in headless Chrome |

```sh
bun run-synth.ts
bun run-relational.ts
(cd rebac && bun check-small.ts && bun run.ts --profile <new folder> --out <file.json>)
```

The core changed for these: `core/machine.ts` proves laws that read several map cells (focus cells, and the every-key
laws at each key a step reads), drops impossible branches as cases are built, and `core/solver.ts` substitutes
equalities before eliminating. The earlier runs give the same verdicts with fewer cases (admit: 56 per cap law).
