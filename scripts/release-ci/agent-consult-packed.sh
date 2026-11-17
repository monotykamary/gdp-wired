#!/usr/bin/env bash
# Parent admission only. Builds/packs locally on the admitted VM; never publishes.
set -euo pipefail
repo=$(cd "$(dirname "$0")/../.." && pwd)
out=${SUPERCOMPUTER_OUTPUT_DIR:?set an absolute, fresh artifact directory}
case "$out" in /*) ;; *) echo 'absolute output directory required' >&2; exit 2;; esac
mkdir "$out/packed"
fixture=$(mktemp -d /tmp/gdp-agent-packed-XXXXXXXX)
trap 'rm -rf "$fixture"' EXIT
cd "$repo"
# Boat transports a hash-bound source tree without Git administration files.
# A local run still requires a clean Git tree; a transported run records the
# parent-supplied identity without claiming an independent Git attestation.
if [ -e "$repo/.git" ]; then
  git rev-parse HEAD > "$out/source-head.txt"
  git diff --exit-code
  printf '%s\n' git-worktree > "$out/source-identity-mode.txt"
else
  node -e 'const fs=require("fs");const s=JSON.parse(fs.readFileSync("VALIDATION-SOURCE.json","utf8")).sourceCommit;if(typeof s!=="string"||!/^[0-9a-f]{40}$/.test(s))throw Error("missing full source identity");console.log(s)' > "$out/source-head.txt"
  cp VALIDATION-SOURCE.json "$out/source-identity.json"
  printf '%s\n' transport-bound-parent-identity > "$out/source-identity-mode.txt"
fi
node --version > "$out/node.txt"
python3 --version > "$out/python.txt" 2>&1
npm --version > "$out/npm.txt"
timeout -k 10s 180s node --check scripts/release-ci/agent-consult-packed-fixture.mjs > "$out/fixture-syntax.log" 2>&1
bun install --frozen-lockfile > "$out/install.log" 2>&1
timeout -k 10s 240s bun scripts/build.ts > "$out/build.log" 2>&1
# Actual npm-packed bytes, not direct dist imports or symlinks back to the checkout.
timeout -k 10s 120s npm pack --ignore-scripts --pack-destination "$out/packed" --json > "$out/pack-library.json"
(cd packages/cli && timeout -k 10s 120s npm pack --ignore-scripts --pack-destination "$out/packed" --json) > "$out/pack-cli.json"
sha256sum "$out"/packed/*.tgz > "$out/tarballs.sha256"
version=$(node -p 'JSON.parse(require("fs").readFileSync("package.json","utf8")).version')
cp scripts/release-ci/agent-consult-packed-fixture.mjs "$fixture/consumer.mjs"
printf '%s\n' '{"private":true,"type":"module"}' > "$fixture/package.json"
cd "$fixture"
# Both paired tarballs are explicit install inputs: wrapper must not fetch a registry gdp-wired.
timeout -k 10s 180s npm install --ignore-scripts --no-audit --no-fund "$out/packed/gdp-wired-$version.tgz" "$out/packed/gdp-wired-cli-$version.tgz" typescript@5.9.3 > "$out/consumer-install.log" 2>&1
timeout -k 10s 30s npm ls --all > "$out/consumer-tree.txt" 2>&1
cat > consumer.ts <<'EOF'
import {createConsultation,toolNames} from 'gdp-wired/agent-consult'
const session=createConsultation({workspaceRoots:[]})
void session.call(toolNames[0],{}).then(()=>session.close())
EOF
timeout -k 10s 30s ./node_modules/.bin/tsc --noEmit --module NodeNext --moduleResolution NodeNext --target ES2022 --skipLibCheck consumer.ts > "$out/consumer-types.log" 2>&1
# Public CLI wrapper must also resolve its local paired dependency.
timeout -k 10s 30s ./node_modules/.bin/gdp-wired-cli --help > "$out/cli-help.txt" 2>&1
# No inherited preload/resolution hooks. Fixture has only installed package, TS and authored inputs.
unset NODE_PATH NODE_OPTIONS GDP_AGENT_CONSULT_ROOTS
GDP_EXPECT_VERSION="$version" timeout -k 10s 300s node consumer.mjs > "$out/packed-consult-transcript.jsonl" 2> "$out/packed-consult.stderr.log"
printf '%s\n' 'PASS: installed tarball library/bin, six tools, edited Python/TS, refusals, no fallback, paired versions' > "$out/packed-consult-result.txt"
