# C safety: first-fault model, not a source verdict

`first-fault.ts` checks the proposed alarm transition independently of the C reader. It is not wired into `extractC` or the CLI. A proof here means something about this explicit model only.

The `gpt-6.2-astra` review identified why importing the old twin would be unsound. The normal reader excludes refusals from its transition relation; it also records some arithmetic refusals without cutting the source path. A later refusal can mask an earlier fault, and removing a matching reason by text cannot repair that. Clang constant folding and table rewriting lose sites; the shared executor does not always retain the promoted operation type and does not model exact C-width arithmetic at all widths. C also does not impose the executor's ordering on all operands.

The first-fault construction needs a typed, exhaustive site inventory before lowering and guards over defined prefixes in every permitted evaluation order. Its fault edge must take precedence over later program outcomes, without admitting values outside the request types. On that edge the abstract model stutters all ordinary state and outputs; this does not imply that native C rolls back writes. Unsupported operations on a live path are unchecked, not terminating steps. A bounds law is about a known live array, not general pointer provenance or lifetime.

`first-fault.test.ts` checks ordering, framing, absorption, and successor existence across a finite abstract model. It also checks the 0.51 fixed-width `TRAP` primitives for promoted arithmetic, zero division, and quotient overflow for both quotient and remainder. None of these cases executes undefined C or establishes source coverage. The guarded cursor model (not a certificate for a C translation unit) can be separately exported to Lean:

```sh
bun test research/c-safety/first-fault.test.ts
bun research/c-safety/first-fault.ts /path/to/project
(cd /path/to/project && lake build)
```
