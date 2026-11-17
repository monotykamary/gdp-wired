#!/usr/bin/env bash
# Mandatory native regression against the actual upstream unit, not a copied model.
set -euo pipefail
R=$PWD
O=${SUPERCOMPUTER_OUTPUT_DIR:?native output directory required}
W=$(mktemp -d /tmp/gdp-litellm-XXXXXXXX)
trap 'rm -rf "$W"' EXIT
bun test core/extract-py-decorator.test.ts core/extract-step-native.test.ts > "$O/python-decorator-tests.log" 2>&1
timeout -k 10 180 git clone -q --filter=blob:none --no-checkout --depth 1 --branch v1.106.6 https://github.com/BerriAI/litellm "$W/litellm" > "$O/litellm-clone.log" 2>&1
git -C "$W/litellm" sparse-checkout set litellm enterprise litellm-proxy-extras >> "$O/litellm-clone.log" 2>&1
timeout -k 10 180 git -C "$W/litellm" checkout -q >> "$O/litellm-clone.log" 2>&1
PIN=61c6ab78393ef45683dd7d963d2a315bd845e20b
test "$(git -C "$W/litellm" rev-parse HEAD)" = "$PIN"
printf '%s\n' "$PIN" > "$O/litellm-commit.txt"
python3 -m venv "$W/venv"
if command -v uv >/dev/null; then
  timeout -k 10 600 uv pip install --python "$W/venv/bin/python" -q -e "$W/litellm[proxy]" > "$O/litellm-install.log" 2>&1
else
  timeout -k 10 600 "$W/venv/bin/pip" install -q -e "$W/litellm[proxy]" > "$O/litellm-install.log" 2>&1
fi
export LITELLM_SRC="$W/litellm" LITELLM_PYTHON="$W/venv/bin/python"
export GDP_LITELLM_RESULT="$O/litellm-native-result.json"
timeout -k 10 180 bun test research/langs/litellm/max-iterations-native.test.ts > "$O/litellm-native-tests.log" 2>&1
cd "$R"
