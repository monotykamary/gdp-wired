# Metadata-only repository and legacy evidence inventory

`inventory.ts` inventories **existing declarative metadata**. It does not audit target code, run a reader or prover, install a target's dependencies, execute `setup`/`repro`/`edits`, clone repositories, contact maintainers, or access the network. It is independent of the older audit runners in this directory.

## Private snapshot and outputs

Prepare an explicitly selected JSON snapshot (do not commit it):

```json
{
  "readerExports": ["./extract", "./extract-py"],
  "catalogs": [{"path": "catalog.json", "text": "[{\"repo\":\"example/widget\",\"commit\":\"main\",\"licence\":\"MIT\",\"path\":\"state.py\"}]"}],
  "documents": [{"path": "private/disclosure/widget.md", "text": "Historical report text"}],
  "sent": {"path": "private/disclosure/SENT.md", "text": "Historical send register"}
}
```

`readerExports` should come from the pinned checkout's `package.json` export keys; a declared reader is only a hint, **not successful extraction, conformance or library acceptance**. Catalogs can be arrays or individual objects. Only `repo`, `commit`, `licence`/`license`, `path`/`target`/`check`/`files`, `entry`/`export`, `file`, `language`/`lang` are consumed. Arbitrary nested execution instructions are ignored. Do not import a catalog as executable code.

Run on boat using a jobs file and a private snapshot data payload:

```sh
supercomputer run --jobs runs/inventory-jobs.json --out runs/inventory-gate --class interactive --data runs/private/disclosure/input:runs/private/disclosure/input
```

The job's metadata-only command is:

```sh
bun research/audit/inventory.ts --snapshot runs/private/disclosure/input/snapshot.json --out runs/private/disclosure/result
```

Supercomputer collects job logs, not arbitrary result directories. Have the job archive the generated packet into its private log, or use an explicitly configured private artifact-recovery workflow; verify the recovered checksums before accepting it. A local log alone is not a recovered result directory. The CLI only writes to a **new directory under `runs/`**, refuses symlink ancestors and existing evidence directories, and creates outputs with directory mode 0700/file mode 0600. Keep the input and parent directories private too. Never commit a real snapshot, generated CSV, report, or sensitive path list. For this program put them in `runs/private/disclosure/`, already gitignored. The coordinator alone writes the canonical ledger, approval register and private Sheet. This tool has no Sheet, mail, GitHub or approval integration.

## Outputs and limits

- `inventory.json`: source records, distinct repository rollup, rejected rows, all provenance hashes, legacy document hashes and historical send summaries.
- `SOURCES.csv`, `REPOSITORIES.csv`: declared immutable pins and licenses, unresolved pins, source paths and registered reader hints. GitHub names are case-normalized. Full 40/64-digit hashes are classified as immutable declarations, **not checked against a clone**. Tag case is preserved; no ref is resolved.
- `LEGACY-REPORTS.csv`: one row per document, always `historical-unverified` / `not-assessed`. A document is not a finding. Mentioned commits/repos are just mentions, not evidence bindings.
- `LEDGER.proposed.csv`: **header only**. No new finding-level rows can be justified by metadata inspection alone. No historical wording can promote a row to verified, approved, sent, acknowledged or fixed.
- `REPORT.md` and `SHA256SUMS`: scope/limitations and content hashes of the generated packet.

Dedupe uses repository, ref, complete source-path set and entry. All contributing input hashes/row numbers survive. Multiple license strings at one pin are flagged for review (they may be legitimate dual licensing, not a defect). Missing fields and rejected repository rows are counted, not guessed. The target of 300 is measured by distinct repository identity, not files, versions or catalog rows.

`SENT.md` reconciliation matches only the exact case-normalized filename stem against a level-two heading, ignoring a trailing parenthetical repository name. Date-prefixed entries and negative notes are independent history facts; both can exist in one section. These are unconfirmed historical claims, never current send authority. Unmatched files/sections remain explicit for manual review. Duplicate stems in different directories can be related to one section but do not imply one finding or one send per document. No private channel or external status is probed.

CSV cells are always quoted and formula-like cells are prefixed with an apostrophe. Use the JSON artifact when exact unescaped strings are needed.

## Checks

Research-only tier: `bun run check` plus `bun test research/audit/inventory.test.ts` on boat. Tests are registered in `scripts/test-shards.ts`. The tests use fabricated catalog/report data, exercise evidence non-promotion, deduplication, conflicting/missing declarations, history ambiguity, CSV injection, hashes and output safety; they never execute audited repositories. No quick bar or trusted-code gate is needed for this isolated metadata utility.
