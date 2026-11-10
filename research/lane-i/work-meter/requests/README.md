# Request-product accounting experiment

The fenced Node run on canonical source `41d39043` retained a stable application
stack in the Cartesian request-product expression in `core/infer.ts`. Its
same-source reconstruction is recorded in `20261110-213128-eh7sxk`.

`accounting.ts` stages one discarded additive observation at that existing
allocation expression: the number of copied fields plus the new assignment.
It preserves enumeration order, overwrite semantics, map-value identity,
full materialization before truncation, and the RNG call sequence. It does
not introduce a cap, change a deadline or exempt the retained GC samples.
`Object.keys` adds observation overhead; no overhead or calibration claim is
made before measurement.

The exact-counter fixture compiles the actual private production expression
from the staged source and its adjacent truncation statement, not a parallel
instrumented helper. Its baseline is the unmodified expression captured by
the staging step. These are local expression controls; the existing inference,
checker-erasure and zero/double/random acceptance suites remain necessary.

`validation.jobs.json` stages `METER_COMPOSITION=requests`, runs the six
expression controls with the existing selected source checks, and separately
runs zero/double/random acceptance controls. It must receive the full
validation tools, generator `.ts`/`.source` files and `baseline.pack`, plus
`recovery-input/driver/resource-run.ts`; the minimal F4 census inputs omit
these deliberately. Copy the 26 KB `baseline.pack` if a hard link would cross
filesystems. The immutable packs themselves can remain shared hard links.

The first real run (`20261110-213747-rlztdu`) passed 158 inherited tests but
failed to parse the adjacent statement's TypeScript non-null assertion in
`new Function`. The transpiler repair passed all 164 tests, erasure, roster and decoder in
`20261110-214235-w4lkow`, but lint correctly rejected the `Function` constructor.
The final fixture loads the compiled snippet as an isolated ESM module instead;
no lint rule is disabled. The selected-source retry in
`20261110-214513-kscywo` passes 164 tests, erasure, roster, decoder and type/lint.
Production bytes were unchanged by these fixture repairs.
All three mutation runs passed 267 tests each; their complete source and
transport receipts were independently audited in `20261110-214151-wkgi21`.
Two retained pre-dispatch attempts ran no solver: v1 wrongly assumed the
minimal census had `prepare.ts`; v2 tried a cross-filesystem hard link for
`baseline.pack`.

`verify.ts` permits only the unused exact fixture to differ between the new
selected-source check and those mutation runs. Every other source blob must
match. `export.ts` reverses just the intended three-file delta and requires
the exact canonical parent tree before exporting a compact patch. Source
export stays separate from validation output: mixing full export chunks
with checks clipped the first run's source prefix, and that incomplete
receipt is not accepted.

The source and compact three-file delta pass independent audit
`20261110-214802-hwwfgg` and are frozen as `94b65671` on
`claude/lane-i-complete-requests`; see `VERIFIED-SOURCE.md`. The integration
production tree is untouched. New-source F3, full F4, production weights and
W remain unqualified; the old `41d39043` CPU census is not a new-source census.
