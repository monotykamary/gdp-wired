# Mutation testing of the trusted base

`kernel/mutants.ts` changes `kernel/kernel.ts` and `core/check.ts` one operator, constant or quantifier at a time and runs
a test battery on each mutant (refusals, tamper, builders, conformance, the finance examples, runtimes, histories, the
kernel fuzz). Fanned out on Modal (`bun mutants.ts run <from> <to>` per batch):

| Run | Mutants | Killed | Surviving |
| --- | --- | --- | --- |
| first battery | 239 | 168 (70%) | 71 |
| with `refusals.test.ts` and the extended tamper test | 241 | 207 (86%) | 34 |
| plus the tests written for those survivors | 241 | 222 (92%) | 19 |
| the run algebra, k-step laws, and `compose.test.ts` in the battery (one test added: 16 steps accepted) | 261 | 239 (92%) | 22 |

The 22 that survive change nothing the kernel's soundness or answers rest on (line numbers as of the run algebra):

| Mutant (line, change) | Why it is equivalent |
| --- | --- |
| kernel.ts:124 `.some` → `.every` | the lists filtered there (a comparison's alternatives) have one atom each |
| kernel.ts:138 `slice(i + 1)` → `slice(i)` | adds the equality of a cell with itself |
| kernel.ts:156 `i > start` → `>=` | a parsed key gains an empty part with coefficient 0 |
| kernel.ts:188 `k >= 0` → `k > 0` | refuses `× 0` too: stricter, never accepts more |
| kernel.ts:208, 248, 261 `!(` → `(` | TypeScript non-null assertions, nothing at run time |
| kernel.ts:219, 221 (×3) | `mentions` and `aboutParams` re-check what the scope check already refuses (names a law, precondition or rank may read) |
| kernel.ts:339 `k >= 0` → `k > 0` | stricter, as above |
| kernel.ts:359, 371 | text in an error message and a goal's label |
| kernel.ts:425 `.some` → `.every` | a rank reading an input is refused by the scope check of the rank anyway |
| kernel.ts:504 inner `.every` → `.some` | `stepLawObligations` makes one goal per step law |
| check.ts:17 (×4) `> 0` → `>= 0` | a zero multiplier: 0·row is a valid (useless) combination, still sound |
| check.ts:23 `of < i` → `<=` | the row must exist (`row !== undefined`), which already excludes `of = i` |
| check.ts:23 (×2) `g > 0` → `g >= 0` | g = 0 makes every variable coefficient fail the divisibility test (NaN); a row with no variable is already a contradiction or rejected |

`kernel/refusals.test.ts` and `kernel/tamper.test.ts` hold the tests the run asked for (and `kernel/steplaw.test.ts` the step-law ones: the 8 mutants of `stepLawObligations` and `checkStepLaws`, 7 caught); the run's logs are in
`runs/modal/mutants-all2/`, `runs/modal/mutants-surv/` and, for the run algebra, `runs/modal/relations-mut/` (local).
