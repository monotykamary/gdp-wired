# Strict-W original protocols — completed scoped gates

Runtime commit: `d00ad74f526337c0c2f46e6548b83bc1b6688ced`.
Parent: `f81c2c50810052de0a33e50f18900ab12a6a1cc2`.
Exact tested tree: `8e367451ea30ed075d2f95e92660fb02e45ba459`.
Branch: `claude/strict-w-originals` in `../gdp-wired-integ-strict-originals`.

All16 original non-MLDR cap failures now stop at or below15M. The other12 active controls remain exact. The full flags-off census passed29/29 exact pairs (27checked/2unknown), including the strict28 subset (27checked/1unknown). All181 protected blobs are unchanged; no price, root, tier or native acceptance edit was made.

Native/static controls:25 full tests/311 assertions and9 off tests/60 assertions; TypeScript and type-aware lint passed. Both source-commit lint configurations passed. All254 recorded gate files match their hashes (121cap,125off,8unit).

`RESULT.md` contains the before/after table. `review-packet/README.md` links the reconstructible complete/runtime patches and exact blob inventories. `*-AUDIT.json` and `*-FETCHED.sha256` record the gates. Collected raw artifacts are retained under the original integration worktree's `runs/lane-i/strict-originals-*`; run those hash manifests from that integration root.

The initial queue and first observed check-site map remain in `QUEUED.json`, `FIRST-CROSSINGS.json` and `PROBE-RESULT.md`. They identify budget-check observations, not exact first over-budget AST nodes. The initial probe's absolute/relative finalizer error and the v1 runtime import-cycle failure remain separate failed evidence; neither was silently rewritten into a success.

This is finite scoped evidence, not a universal full-W theorem or Lean promotion. The extra legacy MLDR case is unchanged UNKNOWN and proves only flags-off compatibility. A's frozen f81c1G diagnostic and subsequent isolated Section42 work are separate; these gates do not transfer to a new composed runtime.
