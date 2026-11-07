# Track P — indices 7 and 17

Only `research/track-p/seven-seventeen` and this evidence directory were written by this worker. No engine/model/kernel changes, commits, or NEXT.md edits.

## Verified original-source certificates

| index | original raw hypotheses | encoded hypotheses | retained PRE tuples | CountInst entries | fresh zero-search |
|---|---:|---:|---:|---:|---|
| 7 | 28 | 39 | 12 | 4 | checked; fixture/raw/decls/gg exact |
| 17 | 19 | 22 | 3 | 1 | checked; fixture/raw/decls/gg exact |

Each `c*/` has `goal.json` (`scope`, `raw`, `decls`, `gg`), `proof.json` (CountCert), `source.json` (full family19 and Instances), and `zero-search.json`. Both use the unchanged original fixture SHA256 `ee4bee5547e52dc7222e210f1a188e9adb1b81fe542eb01396cacba26e7007f1`. Every retained PRE tuple resisted single deletion in the bounded search; the C7 request removed two unnecessary C33 tuples. Every selected count instance also resisted single deletion. These are inclusion-minimized bounded results, not a claim of globally minimal certificates.

C17 requires the original Proposal kind law at its target packed key: without it the abstraction permits a Proposal value 2 that normalizes to 0 at the machine's write, despite the old nonzero invariant. Adding the unmodified original law closes the checked proof. C7 needs no instantiated kind law. Neither request closes with an empty count certificate; deletion/empty SAT results are only countermodels of quantifier-free proof requests, never protocol counterexamples.

## Exact emission comparisons

`c*/diff.md` lists every needed tuple and its first phase. `c*/diff.json` includes required CountInst signatures, selector records, pool membership, all extra count instances, and EVERY extra PRE tuple at EVERY captured phase (`modes.*.normalizedTrace`). Fresh witnesses are normalized using semantic `instId`; non-hand witnesses use a SHA256-derived label with the full signature in `witnessDefinitions`. Raw emissions remain in `generic-{all,none}.json` and `hand-closure-{all,none}.json`.

Generic defaults find all needed non-witness tuples at prepare. For both indices the only missing tuple is L45(wNew,r,v), never emitted with the generic selected certificate but emitted at closure:0 when supplied the hand certificate. Disabling broad initial flag instances alone does not fix the missing count signatures.

With all flags, C7 ends at 75 tuples / 64 extras (40 broad flags), C17 at 71 tuples / 69 extras (32 broad flags); both reach the 65536 generation-work cap. These are work counts, NOT wall-time claims. With no initial flags, final extra tuples are 27 and 36 respectively. With hand certificates and no initial flags the missing required tuple appears at closure:0, but 27 / 20 extra tuples remain.

## Shared generic mechanism

Even with the exact hand-minimal PRE support, the full grammar pool contains all necessary signatures and the ordinary selector omits all of them. C7 full-pool indices: wNew16, wA25, wC32, wR77 (the last is a definition-linked PRE triple, not in base). C17 wNew is base/full index2. This localizes the blocker to selection guided only by explicit POST count directions/ordinary fallback, not an absent count grammar or an inability of closure to emit L45. Primitive target formulas can still depend on the count predicates of active transition guards.

Recommended generic direction: keep the empty-count tier for genuinely count-free proofs, escalate from active transition count definitions rather than an undirected ten-witness selection, and feed selected witnesses to source closure before speculative saturation. Limit initial quantified-flag seeds and unnecessary root count-law expansion. No budgets need increasing and no protocol indices/names belong in the engine. Main's supplied timing evidence says SAT plus admission dominates, not failed grows; these observations support reducing irrelevant hypotheses and selections, not spending more search time.

Audit helper caveat: `auditSupport.finalHyps` is computed before the last closure update and may not describe `finalInstances`; do not label that field the final re-encoded goal size. The checked hand raw/encoded sizes above are independently determined. No timing benchmark was claimed; all substantive runs used warm boat `--vm-type large`, existing 1500-counted/2500-wall per-goal caps, and all started tasks finished.

## Reproduction and logs

Source programs: `inspect.ts`, `hand.ts`, `audit.ts`, `count-tests.ts`, `analyze.ts` and their jobs files under the exclusive source directory. Boat receipts and logs: `inspect/`, `compact/`, `hand1/`, `hand2/`, `audit/`, `count-tests/`, `analyze/`, `analyze2/`. The last analysis includes the semantic normalization and full pool localization. Input used `--data runs/track-p-data:research/track-p/input`. No external solver or trusted hand fact was used.
