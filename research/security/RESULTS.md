# Published policy-vulnerability recall — 2026-11-03

Refresh: `483d849`, based on main `3d7bae1`; original foundation: `cae3559` on `6bdeb95`.
This is the same targeted seed, not population recall. All 31 source hashes match the earlier measurement.

| Measure | Result |
| --- | --- |
| Published, fixed advisories attempted | 15 |
| Published cases extracted on both original revisions | 0/15 |
| Strict CLI findings with reviewed law, original replay and checked fix | **0/15** |
| Upstream Juice Shop training findings | **0/1** |
| Original revisions fetched and source-hash verified | 31/31 |
| Fetch/check pipeline errors | 0 |

All 31 revisions were refused. A refusal is not a security finding or a safe-program verdict.
The library-focused selection increased the attempted corpus, **not actual extraction coverage**.
The subsequent generic Python inheritance/coverage improvements did not make these original targets readable.
There was no readable target on which to continue with a reviewed policy. No source was rewritten,
no abstract contract was replaced with a toy deployed contract, and no security candidate counted.

## Cases and first blockers

Exact commits, paths and policies are in `cases.json`; per-side SHA-256 and full refusal diagnostics
are in `measurement.json`. Fix revisions are paired with their vulnerable first parents.

| Case | Published advisory | First blocker on original code |
| --- | --- | --- |
| Authlib client configuration | GHSA-c73q-w75p-j82v | Python nonempty list of claim classes in the constructor |
| Kubeflow run logs | GHSA-wg5q-x4j9-qm54 | Go `http.ResponseWriter` interface argument |
| OpenWISP organization CRLs | GHSA-9gh4-xw24-9xh5 | Unconfigured Django runtime/inherited `get_object`; handler/ORM boundary |
| OpenZeppelin Timelock | GHSA-fg47-3c2x-m2wr | Solidity `keccak256` role constant |
| OpenZeppelin UUPS | GHSA-5vp3-v4hc-gx76 | Abstract contract |
| OpenZeppelin Initializable | GHSA-9c22-pwxw-p6hx | Abstract contract |
| OpenZeppelin ERC1155Supply | GHSA-wmpv-c2jp-j2xg | Abstract contract |
| OpenZeppelin quorum history | GHSA-xrc4-737v-9q75 | Abstract contract |
| OpenZeppelin Arbitrum caller | GHSA-9j3m-g383-29qr | Solidity library rather than deployed contract |
| OpenZeppelin duplicate Multicall | GHSA-699g-q6qh-q4v8 | Abstract contract |
| OAuthlib client credentials | GHSA-7984-qgvg-3j9c | Inherited `response_types` state not constructor-bound |
| Doorkeeper serialized secret | GHSA-j7vx-8mqj-cqp9 | Ruby module/mixin is not a supported class/function entry |
| Doorkeeper revocation | GHSA-3m6r-39p3-jq25 | Inherited token state; fixed side also uses instance-variable `||=` |
| Doorkeeper public-client revocation | GHSA-694m-jhr9-pf77 | Instance-variable `||=` |
| Doorkeeper public-client consent | GHSA-7w2c-w47h-789w | Inherited `skip_authorization?` state |
| Juice Shop training, separate denominator | OWASP Juice Shop | Express handler does not take state first |

Selection excludes parser, memory-corruption, injection and signature-verification defects; duplicate
CVE aliases are not counted twice. Empty advisory searches are not negative-security evidence.
These cases are in the policy/logic scope, but the result shows they are not yet in the reader subset.

## Separate runtime corroboration — not CLI recall

The pinned original OAuthlib `ClientCredentialsGrant` is invoked with a standard application validator
that authenticates client `low`. A control request for `low`/`read` succeeds on both versions. A request
carrying `client_id=high` and scope `admin` succeeds on the vulnerable version: authorization callbacks
receive `high` even though the authenticated principal is `low`. The fixed version rejects it with
`ServerError`. Both assertion-checked runs passed. No live endpoint or secret was used.

This supports the published advisory, but it is not a generated policy proof or discovery. Its count
in strict CLI recall is **zero**. Reproduce with `oauth-client-replay.py <original-checkout> <vulnerable|fixed>`.

Latest CLI execution: `runs/sec-recall-refresh/receipts/*.log`; original entry-file bytes:
`runs/sec-recall-refresh/sources/`; compact summary: `runs/sec-recall-refresh/SUMMARY.json`.
The earlier separate runtime corroboration remains in `measurement.json` with its original source
measurement identified, and in `runs/sec-expanded/summary.json`; it was not
reclassified as a CLI finding. Every original entry-file SHA-256 was recomputed from the retained bytes
and matched the earlier measurement. The runner uses unmodified
pinned full checkouts, and records both revisions even when one refuses. Follow-up reader work should
first support genuine inherited state/mixins and reviewed deployment contexts, not count stand-ins.
