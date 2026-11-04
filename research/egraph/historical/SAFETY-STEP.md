# Historical safety @step — checked counted proof

**The original `one value decided @step` obligation has a complete counted proof
under its original six-law inductive context.** It is not a proof of every
start/step obligation, a full M2/native gate acceptance, or permission to merge
or push. Coordinator independently accepted the step in batch `20261104-131511-nm55yw`,
worker 0, with no prover imported; see coordinator record
`runs/coord-reviews/SAFETY-BRIDGE-v19/ACCEPT.md`. Search and proof artifacts are frozen.

## Exact preserved obligation

- Original 202-row goal SHA256:
  `58496db30029729c33954d6cc01f61673dbe5bc0c52c4f64b1b4126c0dcc20ca`.
- Full 242-row proof context SHA256:
  `6c361c5022bd5cabfecb7c76aacf992e58459c992c6873c461a001145ce9d354`.
- All original 202 rows, 15 count reads, 46 count instances and eight picks remain.
- The 24 earlier nonduplicate focus-law tuples remain. Eight additional tuples
  instantiate existing P1/P2/P5 laws; total new law tuples stays at the 32 cap.
- Two additional reads and six existing count-schema instances give 17 reads
  and 52 instances. No inequality is supplied as an axiom.

Every added law tuple and count instance is mapped to its source law/declaration
and bindings in `recovery/safety-v16-provenance.json.gz` (SHA256
`775913b6637bd2f98bcf42751bf7eb09ccb0fb708709339893a5e5d7b6bccc30`).

## Why the successful search differs

`mcGoal` appends count lemmas after the original negated goal, while the prover's
root slicing and goal-directed atom ordering treat the last row as the goal.
The research adapter moves that original negated row to the end **without
removing any row**, then remaps the returned tree to the original counted order.
Earlier explicit action/count cuts bypassed the native root pipeline. V19 lets
unchanged `grow` run from an empty path and zero nodes on the focused full view.

No prior partial tree or conditional bundle is loaded by proof search. Every
branch of each complete tree was generated inside that case's single 25-second
outer deadline and additional shared 2m work guard, including remapping. Both
v19 modes used about 510,278 work units. No wall-speedup claim is made.

## Actual controls and verification

Native batch `20261104-131040-wllibq`, uploaded tree `c8c3f600601e`, worker 0.

| Mode/control | Result |
|---|---|
| Native root, without optional protocol-pattern wrapper | complete proof |
| Native root, with public single-query protocol-pattern wrapper | identical proof |
| Original counted-order `checkMC` | accepts both |
| Fresh process, no prover import | accepts both |
| Remove direct package, retaining original + prior 24 tuples | certificate rejected |

The wrapper uses the public `withModels` entry only to obtain pattern scope;
`modelOf` always returns undefined, exactly one query is required, and instance
identity must remain unchanged. V19 did not log the resolved `eprScope`; V20
adds explicit runtime scope and native-root-hook observations. No claim that
pattern scope was necessary follows from the two identical certificates.

The v20 runtime audit (`20261104-131258-4sw8jr`, worker 0) observes actual
pattern scope **off/on**, empty paths, zero initial nodes and two native root
entries through the public query hook. Both full roots and focused search-view
hashes match; both return the same retained proof and pass cold/deletion checks.
Audit receipt: `runs/astra-safety-root-v20/receipt.json`, SHA256
`3e1074af21a341ed090192294ad62e281c3ac74cb2aa31d0572fa2f4c9b88d44`.

Both scoped TypeScript checks, full research type-aware lint, and commitlint
pass. The final integration run (`20261104-131321-cmocea`, worker 0) passes
**53 tests / 264 assertions** across all 17 research test files. The earlier negative
results and the v13/v18 adapter failures remain retained as recorded.

## Retained certificate

`proofs/safety-direct-step.json` — 45,386 bytes, SHA256:
`24313e871cc918c83ac3508f295fe19d810d6ec886abf91924a0fadab005b7c3`.

Native receipt: `runs/astra-safety-root-v19/receipt.json`, SHA256:
`34b99c920d8e8c8e8f82ee4e8dede2ea0de48cb028f71b746063f2711ec35654`.

Kernel and prover pins remain respectively:
`596eaaea9a44a11330178ac37b55377f5747a4ed08a8dd010c26b393c69521e2`,
`5e4232da2abe25c1153edf790af4b339d2be8482c5630b0740315c79f60ce708`.

Together with the independently accepted `P3-STEP.md` certificate, both formerly
open historical step obligations now have retained kernel-checked proofs. This
statement deliberately does not promote either to full native/frontier admission.
