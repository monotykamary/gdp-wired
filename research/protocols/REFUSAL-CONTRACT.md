# Unresolved protocol proof: the refusal contract

`consensus_wo_decide` remains an unresolved positive proof obligation. The original
`lean-protocols-wo` job still requires a checked proof, a successful Lean export,
and a successful Lean kernel check. Its command and known-failure entry have not
been changed. An unknown result is not a proof and does not retire that failure.

A separate required job, `protocol-refusal-contract`, runs
`core/protocol-refusal.test.ts`. The test is also explicitly included in the quick
roster. It drives the real `research/protocols/lean10.ts` entrypoint in isolated
child processes, replacing only the prover result and spying on the exporter.
It checks these producer-boundary inputs:

| Prover result | Required report and effect |
| --- | --- |
| `proven: false, checked: false` | `unknown`; no export attempt or artifact |
| `proven: true, checked: false` | `unknown`; no export attempt or artifact |
| `proven: false, checked: true` | `unknown`; no export attempt or artifact |
| Partial candidate laws, not proven or checked | `unknown`; no export attempt or artifact |

The spy fails the assertion if export is attempted, even if the exporter throws.
The controls retain the real protocol ID and the configured two tries. Every
child has a finite timeout and an isolated temporary output path.

**These are injected negative controls, not successful protocol searches.** Their
passing result means that incomplete evidence is refused at the export boundary.
It does not establish protocol safety, prove the missing invariant, increase a
claimed verification size, or substitute for the original positive job.

A future counted `discover`/`inferLaws` investigation may find the missing support.
Only a real successful run of the unchanged positive job, including its Lean
check, can justify retiring the corresponding known failure.
