# Strict-W originals — required non-MLDR gates PASS

Base commit: `f81c2c50810052de0a33e50f18900ab12a6a1cc2`.
Source commit: `d00ad74f526337c0c2f46e6548b83bc1b6688ced`.
Exact candidate tree: `8e367451ea30ed075d2f95e92660fb02e45ba459`.
Branch/worktree: `claude/strict-w-originals`, `../gdp-wired-integ-strict-originals`.

`complete.patch` reconstructs the candidate from the base (five runtime files and two test files). `runtime.patch` contains only runtime changes. `CHANGED.tree` records their exact Git blob IDs; `PROTECTED.tree` records all181 baseline protected blobs, unchanged by the candidate. Hashes are in `SHA256SUMS`.

## Gates

- Active28: PASS, all121 fetched file hashes verified. All16 former cap negatives are now at or under15M; the other12 cases remain exactly equal. 11 checked /17 unknown. No raw bucket increased, no price/law/custody change. Maximum is paxos_epr at exactly15M. See `../CAP28-AUDIT.json` and `../CAP28-FETCHED.sha256`.
- Admission/native/static: PASS. Full mode25 tests /311 assertions; off mode9 tests /60 assertions (16 skipped). TypeScript and type-aware lint passed with zero warnings/errors. All8 logged file hashes match.
- Flags-off29: PASS,29 exact pairs,27checked/2unknown, including the strict28 subset (27checked/1unknown). All125 final census file hashes verified;181 protected blobs unchanged. The extra legacy MLDR control is unchanged UNKNOWN, not a strict-W or full-mode MLDR result.
- Both commitlint configurations: PASS for the exact source commit message.

No whole-line promotion or Lean acceptance is claimed. The earlier failed v1 unit run is retained separately; its import-cycle design is not this tree. A's Main-authorized1G diagnostic still runs on frozen f81c/d105/archive45f, not on this candidate. No root, tier, price or protected-file edit is present.
