#!/usr/bin/env bash
set -euo pipefail
input=$1
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
printf '{"private":true}\n' > "$scratch/package.json"
(cd "$scratch" && bun add --dev @commitlint/cli@19.8.1 @commitlint/config-conventional@19.8.1)
printf "module.exports={extends:['@commitlint/config-conventional']};\n" > "$scratch/commitlint.config.cjs"
sha256sum "$input/commit-message.txt"
"$scratch/node_modules/.bin/commitlint" --cwd "$scratch" --config "$scratch/commitlint.config.cjs" < "$input/commit-message.txt"
"$scratch/node_modules/.bin/commitlint" --config "$PWD/research/egraph/historical/commitlint.config.cjs" < "$input/commit-message.txt"
printf 'COMBINED_BOTH_COMMITLINT_PASS\n'
