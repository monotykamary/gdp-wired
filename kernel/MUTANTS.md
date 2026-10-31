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
| counts and ghost maps (gen/laneK: `checkCounted`, `ghostedOk`, `checkGhostedLaws`, kernel.ts's lines 1582–1703), `count.test.ts` first in the battery (`MUTANT_BATTERY=counts`: that test alone) | 40 | 40 (100%) | 0 |

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

The counts and ghost maps' 40 are each killed by `kernel/count.test.ts`, whose tests give every guard a certificate only it
refuses (the tree the rest of the check accepts, grown for the goal the guard's absence would check) and a soundness fuzz
(every counted goal accepted has no model where each count is its sum). The first run left one (`ms.every` → `.some` in
`ghostedOk`: the test's clashing ghost map was also read by the original, so the check of what it reads refused it too);
the test now names a map the original declares and never reads. Their builders' mutations past these operators (the
parts, the nesting) are caught by Lean: each export states `countHyps … = some` kernel.ts's hypotheses.

`kernel/refusals.test.ts` and `kernel/tamper.test.ts` hold the tests the run asked for (and `kernel/steplaw.test.ts` the step-law ones: the 8 mutants of `stepLawObligations` and `checkStepLaws`, 7 caught); the run's logs are in
`runs/modal/mutants-all2/`, `runs/modal/mutants-surv/`, for the run algebra `runs/modal/relations-mut/` for sets `runs/modal/mut-sets/`, and for functions, two keys, key terms and liveness `runs/modal/mut-all/` (local).

```equivalent
kernel/kernel.ts | choiceFree | "if (out !== undefined) return out" | " !== " -> " === " | a memo's guard: choiceFree then answers no for every term, so each term is read through the per-path memo, which reads it alike (a choice-free term reads no decision)
kernel/kernel.ts | choiceFree | "case 'var': case 'const': out = true" | "true" -> "false" | as above: no term counts as choice-free, every one is read through the per-path memo, alike
kernel/kernel.ts | termId | "x < y ? -1" | " < " -> " <= " | the sort compares an object's keys, never two equal ones
kernel/kernel.ts | termId | "x > y ? 1" | " > " -> " >= " | the same sort: no two keys are equal
kernel/kernel.ts | comparison | "if (!free && reuse)" | " && " -> " || " | every comparison with a choice is read through reusing, in the kernel's check too: a value found there is used only when every decision it read is the path's (as with let reuse = true)
kernel/kernel.ts | facts | "!atoms.some(lin => decide(lin, path) === false)" | ".some(" -> ".every(" | comparisonOf's alternatives (unless) have one atom each, where some and every agree
kernel/kernel.ts | remember | "(seen.size ?? 0) + 1) > reuseKeep" | " > " -> " >= " | the reuse trie starts afresh one value sooner: what is kept, not what is answered (reusing checks every decision a kept value read)
kernel/kernel.ts | remember | "(seen.size ?? 0) + 1)" | " + 1" -> "" | the reuse trie never starts afresh: memory, not answers
kernel/kernel.ts | remember | "reads[j]?.[0] !== d[0]" | " !== " -> " === " | where the trie branches: a value filed under the wrong branch is found by no path, or found and checked against its decisions (reusing's every)
kernel/kernel.ts | remember | "reads[j]![1] !== d[1]" | " !== " -> " === " | as above: the trie's shape, never an answer reusing hasn't checked
kernel/kernel.ts | remember | "if (i < 0 ||" | " < " -> " <= " | a value that parts from the trie at its first decision is not kept: fewer hits
kernel/kernel.ts | remember | "reads[i]?.[0] !== node.reads[i]![0]" | " !== " -> " === " | the trie's shape again: reusing checks every decision of the value it finds
kernel/kernel.ts | remember | "i < 0 || reads[i]" | " || " -> " && " | i < 0 never happens (a value whose decisions extend a kept one's is a hit, not remembered); otherwise the trie's shape, checked as above
kernel/kernel.ts | reusing | "reuse = true" | "true" -> "false" | inside reusing the parts are read afresh on a copy of the path, with every decision recorded: slower, alike
kernel/kernel.ts | reuse | "let reuse = false" | "false" -> "true" | the kernel's check reads through reusing too: a value found is used only when every decision it read is the path's
kernel/kernel.ts | keyOf | "if (i > start)" | " > " -> " >= " | an empty part reads as the key '' with coefficient 0, which the difference of two keys drops
kernel/kernel.ts | substE | "s.maps[e.map]!(key)" | "!(" -> "(" | a TypeScript non-null assertion, nothing at run time
kernel/kernel.ts | step | "at.maps[map]!(key)" | "!(" -> "(" | a TypeScript non-null assertion, nothing at run time
kernel/kernel.ts | across | "r.at.maps[map]!(key)" | "!(" -> "(" | a TypeScript non-null assertion, nothing at run time
kernel/kernel.ts | witnessesOf | "`w${i + 1}?${f}`" | " + 1" -> "" | the witnesses are w?f, w1?f, w2?f: still apart, and fresh (? is reserved in every declared name)
```
