# Lane E paired diagnostic contract, version 2

**The v1 pass flags are withdrawn.** V1 counted files but did not enforce the
exact roster, allowed side identity to change, and did not bind the candidate
revision. Its old logs/JSON are diagnostic history, not acceptance evidence.
The coordinator uses **Lane D's one-command final gate** for merge acceptance.

The repaired local helper fixes the roster independently in `gate-evidence.ts`:
29 exact IC3Syn IDs × repeats 1/2/3; ten exact DuoAI IDs × repeat 1; and the same
29 broken IDs × repeat 1. It rejects missing/extra/duplicate log names and
receipt names, mismatched protocol or repeat between sides, duplicate results,
incomplete pairs, wrong result IDs, and wrong or absent source bindings.

Every source manifest binds full base/candidate Git SHAs and SHA-256 hashes of
their `git archive` files. The worker verifies **both archive hashes and both
embedded Git commit IDs**, extracts both into private directories, and runs
neither side from the mutable upload tree. Vendor gitlink revisions are checked
in preparation and after setup. Begin/end markers bind both SHAs, suite, ID and
repeat; the analyzer also requires the two independently requested full SHAs.

For a diagnostic rerun (not a substitute for the final gate):

```sh
BASE=$(git rev-parse main)
CAND=$(git rev-parse HEAD)
bun research/mldr-incl/prepare-gates.ts "$BASE" "$CAND" runs/mldr-incl-gates-v2
bun research/mldr-incl/make-gates.ts runs/mldr-incl-gates-v2/manifest.json
```

Submit `ic3syn-jobs.json`, `duoai-jobs.json` and `broken-jobs.json` from that
output root **in parallel** through `supercomputer run`, each with
`--data runs/mldr-incl-gates-v2/input:gate-input --class gate --vm-type large --timing`,
to the matching `ic3syn/`, `duoai/` and `broken/` output directories. Then:

```sh
bun research/mldr-incl/analyze-gates.ts runs/mldr-incl-gates-v2 "$BASE" "$CAND"
```

A partial scope can append `duoai`, `broken`, or a comma-separated subset; its
`complete` and overall `pass` are false. Legacy logs cannot pass version 2.

`gate-evidence.test.ts` includes the requested regression: replace a protocol's
log with another protocol's log **under its original filename**, keeping all 87
files and receipts. It must fail. Other tests cover a renamed duplicate,
cross-side IDs/repeats, missing/forged SHAs, wrong archive hashes, repeated
receipts/results, incomplete pairs, wrong result IDs, strict-budget violations,
and false proofs of broken cases.
