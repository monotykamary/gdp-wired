# Frozen F cut-free family library

These two embedded-library snapshots are byte-for-byte from `lean-kernel/library.ts` at `41ffd98b34a9d57bb30624356c93ef5246ecd0c3`. The emitted strings, rather than an assumed correspondence with adjacent standalone files, are the compatibility authority. The frozen input is hashed before and after generation so a shared input inode cannot silently change the oracle. They preserve the complete emitted project for families without frame, monotone or linear cuts. They are not imported as extra Lean modules.

The current `CountMachine.lean` and `QAlpha.lean` contain the cut-carrying family checker. `scripts/gen-lean-library.ts` generates the current `leanLibrary`. `lean-kernel/gen-legacy-family-library.ts` generates the two legacy overrides and checks their frozen hashes. `leanProject` selects the current sources only when a generated `List CEntryF` definition is present; other project files and insertion order stay unchanged.

Do not edit these snapshots to make a regression pass. A new compatibility baseline needs an explicit release decision. Validate both generators with `--check`; compare complete cut-free projects to frozen-F hashes, not just the theorem file.
