# Mutation testing of the trusted base

`kernel/mutants.ts` changes `kernel/kernel.ts` and `core/check.ts` one operator, constant or quantifier at a time and runs
a test battery on each mutant (refusals, tamper, builders, conformance, the finance examples, runtimes, histories, the
kernel fuzz). Fanned out on boat or Modal (`bun mutants.ts ids <a,b,...>` per job, as the treadmill runs them):

| Run | Mutants | Killed | Surviving |
| --- | --- | --- | --- |
| first battery | 239 | 168 (70%) | 71 |
| with `refusals.test.ts` and the extended tamper test | 241 | 207 (86%) | 34 |
| plus the tests written for those survivors | 241 | 222 (92%) | 19 |
| the run algebra, k-step laws, and `compose.test.ts` in the battery (one test added: 16 steps accepted) | 261 | 239 (92%) | 22 |
| sets (carried maps, quantified flags, writes at every key) and `sets.test.ts` in the battery (two tests added: a history refuses each kind of set; every step law needs its own trees) | 274 | 252 (92%) | 22 |
| functions and facts, two keys, keys in key terms, liveness, and `functions`, `quantifiers`, `keyterms`, `liveness`, `lists` tests in the battery (four tests added: a key in arithmetic on a comparison's right side, a fact with a negative constant, a second key equal to the first or alone, in laws and step laws) | 317 | 293 (92%) | 24 |
| counts and ghost maps (gen/laneK: `checkCounted`, `ghostedOk`, `checkGhostedLaws`, kernel.ts's lines 1582–1703), `count.test.ts` first in the battery (`MUTANT_BATTERY=counts`: that test alone) | 40 | 40 (100%) | 0 |
| every operator of kernel.ts and check.ts (gen/laneM, 2026-10-31: the treadmill had run 280 of 959; the rest reaches loops, recurrent sets by cases, rationals, sums, k-induction, liveness, counts in a machine) | 959 | 758 (79%) | 201 |
| plus `sums`, `rationals`, `pairs`, `nonterm` in the battery and the tests written for the 201 (refusals.test.ts, count.test.ts, countmachine.test.ts) | 959 | 872 (91%) | 87, each listed equivalent below |

The survivors that change nothing the kernel's soundness or answers rest on are in the `equivalent` block at the end,
each anchored by the top-level declaration it sits in and a snippet of its line (not a line number, which edits move):
`bun mutants.ts equivalent` lists the mutants each entry matches and the entries that match none, a run's row for a
listed mutant carries its `equivalent` reason, and the treadmill's digest counts listed survivors apart, listing only the
others. An entry belongs there only with its reason: a survivor that can change a verdict is a test to write instead.

The 2026-10-31 run's survivors that could change a verdict each have a test in `refusals.test.ts` (a certificate or
machine only the mutant answers otherwise), several of them a false certificate the mutant accepts: a term column with
no bounds read as `col <= 0` (termRows), a split on a fractional atom made integral by a product (times), a negated
equation's fact taken where the path decides it the other way (qfacts), a split the path decides already or a split
with no safe row accepted (checkQTree), 0 times a strict row kept strict and a combination at index -1 (checkRefutation
over the rationals), a witness checked past a rounded product (checkWitness), a stem step at `1 < 1` (natC), a start
below 0, a witness naming the state and a precondition failing at the start (stemOk), a case's fold reading `1 < 1`,
`1 = 2`, `2·1`, `1 ∸ 1` or `min(p, 0)` wrongly, dropping a conjunct or a pin (caseGoals, pinC), a sum's term reading
another key, a variable or a flag (sumTermOk), a k-step law's assumptions at a state after a step (stepZone), a progress
law's precondition about the state (preOf). The run found no unsound acceptance on main beyond the reserved-names fix of
0.41.1; the others are guards no test had reached (tests in the same place: liveness levels and ranks, k-induction's
law and k, rational machines' laws and precondition, a sum's names and cover keys, two keys compared plainly, ghost
variables, a count's witness fresh for every instance).

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
kernel/kernel.ts | apart | "& (other(u.a) || other(u.b))) " | " || " -> " && " | apart: the check of the other key, or keyOnly, refuses every comparison this one would (a key term on one side that reads the other key is the other key's key term, or reads it outside one)
kernel/kernel.ts | apart | " j, i <= j, i " | " <= " -> " < " | text in an error message
kernel/kernel.ts | apart | "nly (i < j, i <" | " < " -> " <= " | text in an error message
kernel/kernel.ts | plainKey | "'var' && u.key" | " && " -> " || " | plainKey (the runtimes' and the prover's helper): a variable key answers what walking it would
kernel/kernel.ts | historyMachine | "ous a <= b und" | " <= " -> " < " | text in an error message
kernel/kernel.ts | historyMachine | "n ${i + 1} @re" | " + 1" -> "" | a goal's or step law's label: each tree is looked up by the label the same kernel makes, and the labels stay apart
kernel/kernel.ts | sumCondOk | "c.op === 'flag' || c.op === 'all' " | " || " -> " && " | a flag or quantifier in a sum's condition throws either way (sumTermOk of a missing side)
kernel/kernel.ts | sumCondOk | "l' ? false : c" | "false" -> "true" | a sum term reading a flag is refused anyway: its start value (natE) reads no flag
kernel/kernel.ts | sumMachine | "ag}`) || names" | " || " -> " && " | ?cells$S and w?cells$S are names of the machine only if the flag cells$S is, which the loop just before refuses
kernel/kernel.ts | sumMachine | "(map) || (m.fn" | " || " -> " && " | a map both carried and a function is refused by scope's distinct names (obligations scopes the plain machine)
kernel/kernel.ts | sumMachine | "[map] || !(map" | " || " -> " && " | an undeclared map has no start value: natE of it throws
kernel/kernel.ts | sumMachine | " key) || reads" | " || " -> " && " | a cover key is a machine term: it reads the sum's key or x$S only if the machine names them, which the loop before refuses
kernel/kernel.ts | sumRuntime | "ms!).some(s =>" | ".some(" -> ".every(" | sumRuntime: the runtime evaluates the sums' bound flags too, which nothing reads
kernel/kernel.ts | loopObligations | "anks.some(r =>" | ".some(" -> ".every(" | the ranks are scoped first (inScope of params and state): a rank reading an input is refused there
kernel/kernel.ts | loopObligations | "ural) || !natu" | " || " -> " && " | obligations of the loop machine check every term natural too
kernel/kernel.ts | loopObligations | "arts.every(nat" | ".every(" -> ".some(" | obligations of the loop machine check every term natural too
kernel/kernel.ts | natE | "turn d > 0n ? " | " > " -> " >= " | natE: equal values give the same result either way
kernel/kernel.ts | natE | "turn a < b ? a" | " < " -> " <= " | natE: equal values give the same result either way
kernel/kernel.ts | natE | "turn a > b ? a" | " > " -> " >= " | natE: equal values give the same result either way
kernel/kernel.ts | isTC | "value <= c.b.v" | " <= " -> " < " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | isTC | "=== '<=' && c.a.op === 'const' && c.b.op ===" | " === " -> " !== " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | isTC | "nst' && c.b.op === 'const' && c.a" | " === " -> " !== " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | isFC | "value <= c.a.v" | " <= " -> " < " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | isFC | "<' && c.a.op === 'const' && " | " === " -> " !== " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | isFC | "&& c.b.op === 'const' ?" | " === " -> " !== " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | isFC | "=== '<=' && c.a.op === 'const' && c.b.op ===" | " === " -> " !== " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | isFC | "nst' && c.b.op === 'const' && c.b" | " === " -> " !== " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | foldMul | " a : a.op === 'const' ?" | " === " -> " !== " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | foldTerm | " return a.op === 'const' && a" | " === " -> " !== " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | foldTerm | "b : b.op === 'const'" | " === " -> " !== " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | foldTerm | "const' && b.op === 'const' ? kF(a" | " === " -> " !== " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | foldTerm | " ? a : a.op === 'const' && b.op === 'const' ? kF(a" | " && " -> " || " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | foldTerm | "n b.op === 'cons" | " === " -> " !== " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | foldTerm | "const' && b.op === 'const' ? kF(M" | " === " -> " !== " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | foldTerm | " ? a : a.op === 'const' && b.op === 'const' ? kF(M" | " && " -> " || " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | foldCond | " b.op !== 'con" | " !== " -> " === " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | foldCond | "t = c.op === 'and' ?" | " === " -> " !== " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | foldCond | " (ys.some(stop" | ".some(" -> ".every(" | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
kernel/kernel.ts | substituter | "c.op === 'flag' || c.op === 'all')" | " || " -> " && " | stemOk's inScope (no flags declared) refuses a flag in a loop first
kernel/kernel.ts | lexLt | " => (after.length && before.length ? o" | " && " -> " || " | lexLt: the ranks after and before have the same length
kernel/kernel.ts | eqs | " => (after.length && before.length ? a" | " && " -> " || " | eqs: the ranks after and before have the same length
kernel/kernel.ts | livenessParts | "k ${i + 1}`, {" | " + 1" -> "" | text in an error message
kernel/kernel.ts | livenessParts | "n ${i + 1}`, h" | " + 1" -> "" | text in an error message
kernel/kernel.ts | livenessParts | "     helps: helpful.map((h, i) => ({name: `${l.name}: helpful request ${i + 1}`, when: and2(pending, and2(h.when, named(Object.entries(h.request))))," | " + 1" -> "" | a goal's or step law's label: each tree is looked up by the label the same kernel makes, and the labels stay apart
kernel/kernel.ts | livenessParts | "    helps: helpful.map((h, i) => ({name: `${l.name}: helpful request ${i + 1}`, when: and2(pending, and2(h.when, named(Object.entries(h.request)))), " | " + 1" -> "" | a goal's or step law's label: each tree is looked up by the label the same kernel makes, and the labels stay apart
kernel/kernel.ts | stepLawObligations | "e.map(n => stateName(n, i + 1))).flat()" | " + 1" -> "" | ~ is reserved in every declared name, so the names s~j are checked against none
kernel/kernel.ts | stepLawObligations | "rom({length: k - 1}, (_, i) => s" | " - 1" -> "" | ~ is reserved in every declared name, so the names s~j are checked against none
kernel/kernel.ts | checkStepLaws | " sl).every(g =" | ".every(" -> ".some(" | each step law has one goal
kernel/kernel.ts | stepZone | "Array.from({length: k - 1}, (_, i) => Object.v" | " - 1" -> "" | the zone gains the names of a step past the last, which no term reads
kernel/kernel.ts | stepZone | "Array.from({length: k - 1}, (_, i) => Object.k" | " - 1" -> "" | the zone gains s~k, a state after the last step, which no term reads
kernel/kernel.ts | kInductionSteps | "e ${i + 1}`, w" | " + 1" -> "" | a goal's or step law's label: each tree is looked up by the label the same kernel makes, and the labels stay apart
kernel/kernel.ts | bgcd | " a = a < 0n ? " | " < " -> " <= " | bgcd: -0n is 0n
kernel/kernel.ts | bgcd | " b = b < 0n ? " | " < " -> " <= " | bgcd: -0n is 0n
kernel/kernel.ts | qLin | " + 1n || c > 2" | " || " -> " && " | qLin: a row past a safe integer is refused by checkRefutation's exact() as an input, and its text matches no split (linRow takes safe integers only)
kernel/kernel.ts | qLin | " + 1n || r.c >" | " || " -> " && " | qLin: a row past a safe integer is refused by checkRefutation's exact() as an input, and its text matches no split (linRow takes safe integers only)
kernel/kernel.ts | linRow | "!Object.values(lin).every(c => Number.isSafe" | ".every(" -> ".some(" | linRow: a split with a coefficient not a safe integer gives no row qLin keeps (or BigInt throws), so checkQTree refuses it
kernel/kernel.ts | linRow | "= '1' && c !==" | " && " -> " || " | linRow: a '1' entry is overwritten by the constant in qLin, and a zero coefficient adds x:0 to a key no hypothesis decides (weaker, never wrong)
kernel/kernel.ts | checkQTree | "(!row || !lin " | " || " -> " && " | linRow takes safe integers only, which qLin keeps: lin is defined whenever row is
kernel/kernel.ts | checkMC | "!(ds.every(d =" | ".every(" -> ".some(" | every counted machine's declarations pass countsScope first, which refuses j = key
kernel/kernel.ts | checkMC | " r[0] && !read" | " && " -> " || " | a read named as a witness becomes a count with that variable (witFreshW); a key term reading one reaches the count's bound or body (witFreshW) unless the declaration ignores j, where the read is the same at every key
kernel/kernel.ts | checkMC | ".insts.every(i => i" | ".every(" -> ".some(" | a read named as a witness becomes a count with that variable (witFreshW); a key term reading one reaches the count's bound or body (witFreshW) unless the declaration ignores j, where the read is the same at every key
kernel/kernel.ts | countedObligations | "  if (!ok || !(m.facts ?? []).every(l => naturalC(l.holds)) || laws.some(l => mentions(l.holds, m.inputs))) throw new Error('a negative constant or factor, or a law about a request, is outside the kernel')" | ".some(" -> ".every(" | countedObligations scopes the laws first: a law reading an input is refused there
core/check.ts | checkRefutation | "& s.of < i && " | " < " -> " <= " | the row must exist (row !== undefined), which already excludes of = i
core/check.ts | checkRefutation | "&& s.g > 0 && " | " > " -> " >= " | g = 0 passes only a row with no variable, whose ceiling is ±Infinity or NaN: positive only where the row was already a contradiction
core/check.ts | checkRefutation | "& s.g > 0 && v" | " > 0" -> " >= 0" | g = 0 passes only a row with no variable, whose ceiling is ±Infinity or NaN: positive only where the row was already a contradiction
kernel/kernel.ts | foldTerm | "=== 0 ? a : a.op === 'const' && b.op ===" | " === " -> " !== " | a fold not taken (caseGoals): the term or condition keeps its value, which the kernel's linear forms read alike; that the folds are Lean's own is the Lean conformance's (--nonterm), outside this battery
```
