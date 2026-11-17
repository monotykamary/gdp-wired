# Independent kernel review

Reviewer: `pi --provider openai --model gpt-6.1-terra --thinking high`,
launched with `env -u OPENAI_API_KEY`, read-only tools, no extensions/skills.
Scope: actual kernel implementation and final untrusted prover diff only.
No reader/release approval requested or granted.

Earlier findings addressed: accessor TOCTOU in spec validation; omitted invalid
operand receipts; reserved-name aliases; step-law readonly-function scope;
generated-fact/final-conclusion ordering.

## Continuation round9 verdict

**APPROVE** — actual kernel/prover diff after the checked u64 repair, performance
negative memo and shared-budget fix. Launched exactly as above with
`env -u OPENAI_API_KEY`, OpenAI Terra high, read/grep/find/ls only, no extensions
or skills. Full output retained `/tmp/kp2-kernel-review9.txt`; round8 output at
`/tmp/kp2-kernel-review8.txt`.

The reviewer independently accepted guarded `c_n=0`, both-direction local
carry-cut refutations, certificate widening/final replay, reserved namespace
validation, negative-only caching, and unchanged safe-integer boundaries.
Round8's nonblocking resource caution was addressed: local grow calls now share
outer deadline/node budgets. Round9 found no blocking soundness issue.

This is NOT certification of generic Lean export or release readiness. The
restricted helper-digit machine lane and the generic SMachine bridge are
explicitly different. Native tests/Lean receipts are reported by Main, not
asserted to have been executed by the reviewer.

## Original checkpoint round7 verdict (superseded by continuation round9)

**APPROVE** — kernel/prover-only, on soundness and collisions.

The new preflight accepts only a proof tree for the existing kernel checker; otherwise it falls through to the existing search paths. I found no soundness or namespace-collision issue in the provided diff.

This approval does not assert completeness: the u64 identity candidate remains unchecked, and full-machine Lean support is explicitly refused.


Native final gates: `20261117-175918-qbxv36`, all five jobs PASS. This does NOT
resolve the rejected u64 identity certificate or the missing universal actual
Lean export bridge; see STATUS.md. The public DSL admission guard and its
regression are outside this kernel-only review scope and pass the final tests.
