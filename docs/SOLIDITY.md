# Solidity: a concrete deployment of the original source

`extractSolidity` from `gdp-wired/extract-sol` compiles Solidity with `solc`, reads its AST and
checks the resulting rule against the same bytecode on Anvil. The [reader design](../research/sol/DESIGN.md)
describes integer widths, storage, calls, re-entrancy and the remaining subset boundaries.

## Abstract contracts and libraries

An abstract declaration is not deployable. The reader does **not** remove `abstract` or replace
its functions with a simplified contract. Before lowering, it chooses a concrete deployment:

1. Search the project for a concrete repository contract that inherits the requested declaration.
   For a library, require an actual reference to the library from the caller or its bases.
   Solidity's compiled AST establishes identity and inheritance, not a matching class name.
2. Prefer the unique conventional `<Target>Mock`, `<Target>Harness` or `<Target>Test` when present;
   otherwise require a unique concrete candidate. Ambiguity is a refusal, not an arbitrary choice.
3. With no concrete repository candidate, an abstract contract can receive a new source unit
   containing a subclass with **only a constructor**. It forwards the original, unbound constructor
   arguments as parameters. It does not implement abstract functions or override inherited bodies.
   Constructor parameters are bound by declaration identity before the original bodies execute base-first;
   forwarding arguments that call code remain refused rather than guessing their initialization order.
4. A library can receive a concrete caller with forwarding functions for its internal functions.
   A library cannot be inherited. This does not invent storage for library storage-reference
   parameters, or silently substitute internal calls for deployed/linked public library calls.
   Those cases require an explicit suitable repository harness, or are refused.

The original source units are never rewritten. Every generated unit is available in
`extraction.harness.generatedSource`. Repository harnesses are compiled as they are, including
constructor guards, hook implementations and any additional methods.

```ts
import {extractSolidity, type SolidityHarness} from 'gdp-wired/extract-sol'

const x = extractSolidity('contracts/Policy.sol', {
  root: '.',
  entry: 'Policy',
  harness: {file: 'contracts/mocks/PolicyMock.sol', entry: 'PolicyMock'},
  methods: ['authorize'],
})
const deployment: SolidityHarness | undefined = x.harness
console.log(deployment, x.notes, x.refusals)
```

`harness` defaults to `'auto'`. Set `harness: false` to require the requested declaration itself
to be deployable. Search is bounded (4,096 Solidity files, 64 candidate files); select a harness
explicitly for a larger project. Dependency, output and hidden directories are not auto-searched.
The same option is accepted in CLI configuration:

```toml
[rules.Policy]
entry = "Policy"
methods = ["authorize"]

[rules.Policy.harness]
file = "contracts/mocks/PolicyMock.sol"
entry = "PolicyMock"
```

Explicit `methods` also permits selecting a public `view` or `pure` function. Unselected
methods are not entry points; internal calls from a selected method are still read normally.
With no `methods`, an ordinary concrete contract retains its existing state-changing entry points.

## What the harness assumes

**A proof or replay is about the chosen concrete deployment, not all possible subclasses or
all library callers.** The extraction's `harness` record and notes identify:

- the original source and target declaration;
- the concrete source, entry and kind of harness;
- the exact constructor definitions, whose arguments are rule parameters subject to their guards;
- overridden function signatures and where those implementations come from;
- additional public entry points supplied by the harness;
- the full generated source, if there is one.

A repository mock's authorization hook, constructor or wrapper may be important to the policy.
Review them; a mock is not evidence of a production deployment simply because it inherits the
same base. A later subset refusal retains the selected harness and its assumptions. Unsupported
operations remain refusals, never successful extractions or evidence that a contract is safe.

For security recall, retain the pinned original hashes, review the policy and deployment context,
require a vulnerable-side run replayed on that bytecode, and require the corresponding fixed
revision not to refute the policy. Merely making an abstract declaration deployable is not a finding.
`research/security/solidity-harness.ts` audits the paired original OpenZeppelin revisions and records
harness provenance separately from that strict finding criterion.
