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
| sets (carried maps, quantified flags, writes at every key) and `sets.test.ts` in the battery (two tests added: a history refuses each kind of set; every step law needs its own trees) | 274 | 252 (92%) | 22 |
| functions and facts, two keys, keys in key terms, liveness, and `functions`, `quantifiers`, `keyterms`, `liveness`, `lists` tests in the battery (four tests added: a key in arithmetic on a comparison's right side, a fact with a negative constant, a second key equal to the first or alone, in laws and step laws) | 317 | 293 (92%) | 24 |

The 24 that survive change nothing the kernel's soundness or answers rest on (line numbers as of liveness):

| Mutant (line, change) | Why it is equivalent |
| --- | --- |
| kernel.ts:126 `.some` → `.every` | the lists filtered there (a comparison's alternatives) have one atom each |
| kernel.ts:140 `slice(i + 1)` → `slice(i)` | adds the equality of a cell with itself |
| kernel.ts:158 `i > start` → `>=` | a parsed key gains an empty part with coefficient 0 |
| kernel.ts:190, 460 `k >= 0` → `k > 0` | refuses `× 0` too: stricter, never accepts more |
| kernel.ts:210, 254, 269 `!(` → `(` | TypeScript non-null assertions, nothing at run time |
| kernel.ts:222, 224 (×3) | `mentions` and `aboutParams` re-check what the scope check already refuses (names a law, precondition or rank may read) |
| kernel.ts:308 `keys[i + 1]` → `keys[i]` | the guard before a pair's substitution: both are present for every pair the prover writes |
| kernel.ts:438 `&&` → `\|\|` | `plainKey`: a key that is any variable, not only the bound key, answers true, as walking it would |
| kernel.ts:481, 493 | text in an error message and a goal's label |
| kernel.ts:550 `.some` → `.every` | a rank reading an input is refused by the scope check of the rank anyway |
| kernel.ts:658 inner `.every` → `.some` | each step law has one goal |
| check.ts:17 (×4) `> 0` → `>= 0` | a zero multiplier: 0·row is a valid (useless) combination, still sound |
| check.ts:23 `of < i` → `<=` | the row must exist (`row !== undefined`), which already excludes `of = i` |
| check.ts:23 (×2) `g > 0` → `g >= 0` | g = 0 makes every variable coefficient fail the divisibility test (NaN); a row with no variable is already a contradiction or rejected |

`kernel/refusals.test.ts` and `kernel/tamper.test.ts` hold the tests the run asked for (and `kernel/steplaw.test.ts` the step-law ones: the 8 mutants of `stepLawObligations` and `checkStepLaws`, 7 caught); the run's logs are in
`runs/modal/mutants-all2/`, `runs/modal/mutants-surv/`, for the run algebra `runs/modal/relations-mut/` for sets `runs/modal/mut-sets/`, and for functions, two keys, key terms and liveness `runs/modal/mut-all/` (local).
