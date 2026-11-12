# N5 dependency and unexpected gate failures — source-only repair

## Historical result remains NOT_GREEN

The one completed gate on `a8115f32` remains unchanged in
`runs/track-m/B-a811-software-gate-v1/RESULT.md`. N3 and N5 were raw FAIL;
all nine new G controls passed individually. Four type errors, one lint error
and five commitlint harness blocks were retained. This repair has not been
compiled or executed, and grants no gate, retry, qualification or activation.

## N5 delta for D's review

C's `d20ee40a` explains the old fixture: target `v0 = 0` stepped to constant
zero and was independent of the member `v1 = 0`. Its genuinely checked reduced
scope could omit that member under 46.6. The final member-premises assertion
therefore received undefined despite the earlier replacement checks passing.

The repaired fixture changes exactly that dependency: target STEP is now
`v0 := v1`, while the member invariant remains `v1 = 0`. The target proof must
actually cite the member. The old cut-bearing member proof still cites
`missing`, that route still becomes unavailable, and the replacement must be
used in the closing family.

Assertions are retained and strengthened, not waived:

- native public result is proven, and `missing` is outside the final family;
- `replaceable` is explicitly inside the final family;
- replay of the old cut-bearing scope over the final family is refused;
- two member proposals and their old/new premise distinctions remain;
- the target's final premise entry contains `replaceable`;
- the final member premise entry equals the replacement proposal's entry;
- the original final assertion still rejects `missing` there.

N3's body, root, assertions and raw expected-flat failure are untouched.

## Other requested repairs in the same child

- Narrow live `available` after an explicit null guard before the owner test's
  equality assertion; keep the finite-cap and native-use assertions.
- Use a throwing never-returning request stub for the foreign-owner negative,
  preserving its request counter and zero-call assertion.
- Convert controller-member fixture rows to graph rows with explicit
  `terminal:false` at both graph calls. Runtime false semantics are unchanged.
- Remove the unused `workAdd` import.
- Preserve a reusable source gate at `software-gate.sh`. Its commitlint phase
  follows A's stdin pattern using the exact sealed message files, not `--edit`,
  so an archive need not contain a Git root. Message SHAs come from the sealed
  `messages/index.txt`, allowing the final pin to include this child. All phase
  outcomes remain retained and nonzero statuses remain failures.

The old a811 input bundle and receipts are not edited. Main directed A to
append this one child to candidate `b9a8db3e`, then request D's exact final-pin
review before a single full final gate. No separate B gate is authorized.
