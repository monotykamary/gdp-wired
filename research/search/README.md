# gdp-wired search: counterexamples on the GPU

| File | What |
| --- | --- |
| `compile.ts` | A machine and a law compiled to straight-line u32 code: WGSL for the GPU (what the forked Handwired's word ops would emit) and JS for the CPU. One candidate per index (params, then each step's request); a thread takes 256 candidates and reports the least failing (depth, offset). `fitsU32` bounds every value over the space first and refuses a space where one could pass 2^32 − 1, so u32 never wraps and hides a counterexample (hw/compile.ts checks the same) |
| `fits.test.ts` | Spaces `fitsU32` accepts, replayed by the interpreter: no value reaches 2^32 |
| `models.ts` | The searches: admit with Day unguarded, in-flight (cap 2) against a bound one too tight (fails only after 6 requests) and the exact one, and a product law with the cap forgotten |
| `check-cpu.ts` | The JS twin against the interpreter on 20,000 random candidates per search |
| `page.ts`, `run.ts` | The GPU run in headless Chrome. Every reported counterexample is replayed by the interpreter, so the GPU is untrusted |
| `cpu.ts` | The same enumeration on one CPU thread, and the interpreter's default search (depth 3) |

```sh
bun check-cpu.ts && bun cpu.ts && bun run.ts --profile <new folder> --out <file.json>
```
