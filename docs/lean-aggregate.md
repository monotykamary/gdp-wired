# Opt-in aggregate proofs in Lean

`gdp-wired/lean-aggregate` is a separate, experimental entry for aggregate invariants. It is off by default. Neither `proveRule`, the standard CLI, nor the default corpus scores use it. There is no new gdp-wired kernel rule for aggregate closure in this release.

Install the official Lean **4.34.0** toolchain and put `lean` on `PATH` (with elan: `elan toolchain install leanprover/lean4:v4.34.0`). No Lake project or separate proof library is needed: the npm package ships the Lean sources used by this entry. Use this API from Node:

```ts
import {proveLeanAggregate} from 'gdp-wired/lean-aggregate'

const result = await proveLeanAggregate(rule.machine, invariant)
if (result.kind === 'lean-checked') {
  console.log(result.verdict) // checked in Lean, not by the kernel
  console.log(result.receipt.inputSha256, result.receipt.sourceSha256)
} else {
  console.log(result.reason, result.detail) // not checked; not a refutation
}
```

Pass one invariant over reachable states, not a step or a liveness law. The adapter checks **unmarked symbolic models only**: it refuses source-bound machines or laws even if native translation evidence is available. Pass plain records and dense arrays of own enumerable data (ordinary DSL output or parsed JSON); omit absent optional fields instead of writing `undefined`. Proxies, accessors, serialization hooks (including inherited `toJSON`), custom prototypes, and extra fields outside the supported AST are refused. The adapter snapshots the data without calling hooks and applies the ordinary kernel scope check to that exact source before looking for either proof shape:


- **Finite fold:** counters over disjoint classes in a bounded table, maintained by a point update and a broadcast reset. The gdp-wired kernel checks local sequents. Lean checks those trees and composes them into the full original invariant.
- **Weighted sum:** an account-like accumulator updated by adding or removing weights associated with a key. The adapter proposes an instrumented row, an exact weighted equality, and the supporting invariants. Lean transports the checked instrumented family to the caller's original machine and original universally quantified invariant.

This route is intended for both etcd Raft tally invariants and TigerBeetle transfer limit invariants #0 and #1 in the repository corpus. The claims are about the corpus models, not equivalence with the upstream implementations. No special case in the prover matches those names or law indices. Other shapes, including custom functions, finite binders, and existing count/sum instrumentation, can be refused.

Success is **checked in Lean, not by the kernel**. There is no `checked: true` (or `proven` boolean) to mix with a native verdict. The receipt identifies the exact input (SHA-256 of the UTF-8 JSON snapshot of `[machine, law]`), the emitted `.lean` source and its digest, each used library's digest, the Lean version, and the axiom report for `aggregate_claim`. The adapter builds the packaged libraries in a fresh directory, runs Lean on the emitted theorem, and permits only `propext`, `Classical.choice`, and `Quot.sound`. It refuses incomplete reports, unexpected axioms, wrong toolchains, failures and timeouts. The receipt records local execution, not a signed attestation: trust the installed package and the local Lean executable as you would when running Lean yourself.

Imports do not start Lean or search. Calling the function starts an isolated search worker; only a retained candidate starts Lean. `{searchMs, leanMs}` sets separate deadlines (defaults: 60 s for search, with a small worker/serialization allowance; 180 s for compiling and checking in Lean). A refusal does not change the ordinary prover's result.
