# Published policy-vulnerability recall — 2026-11-03

## Complete corpus baseline

Measured tree committed as `7db037f`, integrating main `927a521`; original foundation `cae3559`.
This is a targeted seed, not population recall. All 37 original source hashes match retained evidence.
The additional allauth, Flask-Security and MLflow cases are published, fixed policy defects, not
unfixed targets or synthetic stand-ins.

| Measure | Result |
| --- | --- |
| Published, fixed advisories attempted | 18 |
| Published cases extracted on both original revisions | 0/18 |
| Strict CLI findings with reviewed law, original replay and checked fix | **0/18** |
| Upstream Juice Shop training findings | **0/1** |
| Original revisions fetched and source-hash verified | 37/37 |
| Fetch/check pipeline errors | 0 |

All 37 baseline revisions were refused. A refusal is not a security finding or a safe-program verdict.
No source was rewritten and no security candidate was counted. `measurement.json` records this
baseline; the later Solidity experiment below has separate provenance and must not be mistaken for
an 18-case rerun on its frontend.

### Baseline cases and first blockers

Exact commits, paths and policies are in `cases.json`; per-side hashes and diagnostics are in
`measurement.json`. Fix revisions are paired with their vulnerable first parents.

| Case | Published advisory | First blocker on original code |
| --- | --- | --- |
| Authlib client configuration | GHSA-c73q-w75p-j82v | Python nonempty list of claim classes in the constructor |
| Kubeflow run logs | GHSA-wg5q-x4j9-qm54 | Go `http.ResponseWriter` interface argument |
| OpenWISP organization CRLs | GHSA-9gh4-xw24-9xh5 | Django runtime configuration/inherited handler boundary |
| OpenZeppelin Timelock | GHSA-fg47-3c2x-m2wr | Solidity `keccak256` role constant |
| OpenZeppelin UUPS | GHSA-5vp3-v4hc-gx76 | Abstract contract |
| OpenZeppelin Initializable | GHSA-9c22-pwxw-p6hx | Abstract contract |
| OpenZeppelin ERC1155Supply | GHSA-wmpv-c2jp-j2xg | Abstract contract |
| OpenZeppelin quorum history | GHSA-xrc4-737v-9q75 | Abstract contract |
| OpenZeppelin Arbitrum caller | GHSA-9j3m-g383-29qr | Solidity library rather than deployed contract |
| OpenZeppelin duplicate Multicall | GHSA-699g-q6qh-q4v8 | Abstract contract |
| OAuthlib client credentials | GHSA-7984-qgvg-3j9c | Inherited `response_types` state not constructor-bound |
| Doorkeeper serialized secret | GHSA-j7vx-8mqj-cqp9 | Ruby module/mixin is not a supported entry |
| Doorkeeper revocation | GHSA-3m6r-39p3-jq25 | Inherited token state; fixed side also uses instance-variable `||=` |
| Doorkeeper public-client revocation | GHSA-694m-jhr9-pf77 | Instance-variable `||=` |
| Doorkeeper public-client consent | GHSA-7w2c-w47h-789w | Inherited `skip_authorization?` state |
| django-allauth inactive tokens | GHSA-qhmc-3mvr-f2j4 | Untyped token argument |
| Flask-Security OAuth freshness | GHSA-97r5-pg8x-p63p | Flask proxy returns a non-scalar provider object |
| MLflow trace authorization | GHSA-2cm6-r77w-6g96 | Heterogeneous `Authorization | Response` result |
| Juice Shop training, separate denominator | OWASP Juice Shop | Express handler does not take state first |

Selection excludes parser, memory-corruption, injection and signature-verification defects. Duplicate
CVE aliases are not counted twice; empty advisory searches are not negative-security evidence.

## Solidity through concrete original-repository contexts

`solidity-harness-measurement.json` records a separate six-case experiment on frontend snapshot
`ad2b8da56c21` (before integration of `afd977d`). Every original revision and source hash is unchanged.
The frontend adds a source unit only when no suitable repository harness is selected; it never
removes `abstract`, changes an inherited body, or fabricates an abstract implementation.
See [the deployment boundary](../../docs/SOLIDITY.md).

| Measure | Result |
| --- | --- |
| Original revisions/hash checks | 12/12 |
| Concrete contexts selected, with assumptions recorded | 12/12 |
| Individual revisions extracted | 1/12 |
| Cases extracted on both sides | 0/6 |
| Strict findings (reviewed law, original replay, checked fix) | **0/6** |

| Case | Concrete context | Vulnerable / fixed outcome |
| --- | --- | --- |
| UUPS | Repository `UUPSUpgradeableMock` in `contracts/mocks/UUPS/TestInProd.sol` | Both refuse a 256-bit storage-slot constant |
| Initializable | Repository `InitializableMock` | Vulnerable extracts; fixed refuses `extcodesize` inline assembly in `Address.sol` |
| ERC1155Supply | Repository `ERC1155SupplyMock` | Vulnerable refuses dynamic-array construction; fixed refuses the supply-update loop |
| Quorum history | Explicit repository `GovernorMock` | Both refuse EIP-712 immutable state |
| Arbitrum caller | Generated forwarding caller of unchanged internal `LibArbitrumL2.isCrossChain` | Both refuse a call to the external Arbitrum system contract |
| Multicall | Repository `ERC2771ContextMock` | Both refuse immutable trusted-forwarder state |

The measurement records the full constructor definitions, override signatures, additional entry
points, and generated source for **each** selected context. These choices are assumptions, not a
claim about every possible deployment. For example, the UUPS mock implements `_authorizeUpgrade`;
the Governor mock supplies governance hooks and parameters; the ERC2771 mock supplies a trusted
forwarder. A missing body is never invented for a constructor-only subclass. The generated library
caller supplies no invented Arbitrum behavior. Its external system call remains a refusal.

The vulnerable Initializable extraction is progress in reader coverage, **not a reproduced security
finding**: no reviewed policy has been refuted and replayed, and its fixed side is not yet readable.
No fixed refusal is called safe. The original abstract/library refusal has been passed in all twelve
selected contexts; subsequent subset boundaries remain explicit.

Reproduce on boat with `bun research/security/solidity-harness.ts <id>`. For the ambiguous Governor
family add `--harness-file contracts/mocks/GovernorMock.sol --harness-entry GovernorMock`.
Collect receipts with `collect-solidity-harness.ts <log-dir> <frontend-snapshot>`.

## Separate runtime corroboration — not CLI recall

The pinned original OAuthlib `ClientCredentialsGrant` runs with a standard application validator
that authenticates client `low`. A `low`/`read` control succeeds on both versions. A request carrying
`client_id=high` and scope `admin` succeeds on the vulnerable version: callbacks receive `high`
although the authenticated principal is `low`. The fixed version rejects it with `ServerError`.
Both assertion-checked runs passed; no live endpoint or secret was used.

This supports the advisory, not a generated policy proof or discovery. Its strict CLI count remains
zero. Reproduce with `oauth-client-replay.py <original-checkout> <vulnerable|fixed>`.

Baseline receipts: `runs/sec-orm-recall/refresh/`; original entry-file bytes:
`runs/sec-orm-recall/refresh-sources/`; summary: `runs/sec-orm-recall/REFRESH-SUMMARY.json`.
Solidity receipts: `runs/sec-sol-concrete/current-recall/`. The retained runtime-only evidence has
its original measurement provenance in `measurement.json`; it was not reclassified as a finding.
The next inherited-state work must bind real ancestors/class state, not substitute toy handlers.
