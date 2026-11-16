#!/usr/bin/env bash
set -euo pipefail
# One serial job is intentional: paired order on one exclusive --timing worker.
ROOT=$(pwd)
OUT=${SUPERCOMPUTER_OUTPUT_DIR:?supercomputer output directory required}
TMP=$(mktemp -d)
HISTORY="$TMP/history"
TREES=()
cleanup() {
  for tree in "${TREES[@]:-}"; do git -C "$HISTORY" worktree remove --force "$tree" >/dev/null 2>&1 || true; done
  rm -rf "$TMP"
}
trap cleanup EXIT
mkdir -p "$OUT"
bun install --frozen-lockfile
# Supercomputer source capsules deliberately omit .git. Fetch only the four immutable
# read-only controls; this creates no archive and makes no GitHub write.
git init -q "$HISTORY"
git -C "$HISTORY" remote add origin https://github.com/monotykamary/gdp-wired.git
for sha in 70b6604435910194a91ed2749f4f03cb2e116d62 c149b540bc28f9ec752cf9e5f6f299d69613d885 96bf476ed811081ba3d3084ab11ebe19351cd27d c08bb385bbb1afc8dbf6ce1fc8aa8d838b9eb3a5; do
  git -C "$HISTORY" fetch --quiet --no-tags origin "$sha"
done
make_tree() {
  local name=$1 sha=$2
  TREE="$TMP/$name"
  git -C "$HISTORY" worktree add --detach "$TREE" "$sha" >/dev/null
  ln -s "$ROOT/node_modules" "$TREE/node_modules"
  mkdir -p "$TREE/research/bapa/0502-slowdown"
  cp "$ROOT/research/bapa/0502-slowdown/runner.ts" "$ROOT/research/bapa/0502-slowdown/instrument-binders.ts" "$TREE/research/bapa/0502-slowdown/"
  TREES+=("$TREE")
}
make_tree r70 70b6604435910194a91ed2749f4f03cb2e116d62; T70=$TREE
make_tree r149 c149b540bc28f9ec752cf9e5f6f299d69613d885; T149=$TREE
make_tree r96 96bf476ed811081ba3d3084ab11ebe19351cd27d; T96=$TREE
make_tree r08 c08bb385bbb1afc8dbf6ce1fc8aa8d838b9eb3a5; T08=$TREE
run_one() { local tree=$1 mode=$2 label=$3 phase=$4; (cd "$tree" && SLOWDOWN_OUTPUT="$OUT" bun research/bapa/0502-slowdown/runner.ts "$mode" "$label" "$phase" "$OUT"); }
# Three AB/BA/AB or BA/AB/BA pairs for every control. No warmups are discarded.
for control in c149 c96 c08; do
  case "$control" in
    c149) C="$T149"; ORDER=("$T70" "$C" "$C" "$T70" "$T70" "$C");;
    c96) C="$T96"; ORDER=("$C" "$T70" "$T70" "$C" "$C" "$T70");;
    c08) C="$T08"; ORDER=("$C" "$T70" "$T70" "$C" "$C" "$T70");;
  esac
  n=0
  for tree in "${ORDER[@]}"; do n=$((n+1)); run_one "$tree" policy "policy-${control}-${n}" timing; done
done
# Representative larger quantified/provenance case, preserving its per-revision assertion and search cap.
for spec in "$T70 exists exists-c149-1" "$T149 exists exists-c149-2" "$T149 exists exists-c149-3" "$T70 exists exists-c149-4" "$T70 exists exists-c149-5" "$T149 exists exists-c149-6"; do
  read -r tree mode label <<<"$spec"; run_one "$tree" "$mode" "$label" timing
done
# Causal count pass after timings: temporary worktree-only instrumentation, excluded from timing statistics.
for spec in "$T149 c149-count" "$T70 r70-count"; do
  read -r tree label <<<"$spec"; (cd "$tree" && bun research/bapa/0502-slowdown/instrument-binders.ts); run_one "$tree" count-policy "$label" counts
done
{
  echo "commit=$(git rev-parse HEAD)"
  echo "bun=$(bun --version)"
  echo "cpu=$(grep -m1 'model name' /proc/cpuinfo || true)"
  for t in "$T70" "$T149" "$T96" "$T08"; do git -C "$t" rev-parse HEAD; sha256sum "$t/research/security/policy-identity.test.ts" "$t/core/exists-support.test.ts"; done
} > "$OUT/environment.txt"
bun "$ROOT/research/bapa/0502-slowdown/summarize.ts" "$OUT/observations.jsonl" "$OUT/SUMMARY.json"
