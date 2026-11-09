#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "$0")" && pwd)
check() { printf '%s  %s\n' "$1" "$2" | sha256sum -c -; }
replace() {
  local file=$1 old=$2 new=$3 from=$4
  if test "$old" = absent; then test ! -f "$file"; else check "$old" "$file"; fi
  check "$new" "$here/$from"
  cp "$here/$from" "$file"
  check "$new" "$file"
}
replace core/counts.ts dd70a44ea0c9b97361e9c48884a2817a16e218bf8bf3b0732a56e09668a5193c d9a1f9dcbb376161708d8bda8854e75f4d8c61cc009d03cefc0a2e528bbe865b counts.txt
replace core/count-ranges.ts 497aa7d44694b6f202e82ce5c45d491fa8bd4f6b54f8e948bf2d25ebbfe61417 d7053784d22e19806a57b912905cbbfc050b4ccca0929a72a3ba77db4af08cbb count-ranges.txt
replace core/count-ranges.test.ts 736cb7965aa45853605e7daf6e4a6cc837facebbf71696c65ecd5b3b6e8a9493 2c51121f9029236e97fbafa166660dd87da3cd01a76fc131c72225073105f7ae count-ranges.test.txt
replace research/mldr-incl/range-regression-input.ts absent f781e0b8fcd676b9f57c189ad1760678620fc96f7473ef203a8623a09a74d040 range-regression-input.txt
replace research/mldr-incl/range-regression-input.test.ts absent 73f8165803004b052b560c9e2163dfa7f3d0839861c550d077e8bb6617c41f4a range-regression-input.test.txt
replace research/mldr-incl/install-range-switch.ts absent d6a08521a70669e448ed44e602e94362dc17c185627456f0d22e4a03566149ec install-range-switch.txt
printf '%s\n' 'LANE_E_DEMAND_SOURCE=ac7eacfeeb17677fb58d588a4f5dee6b666294c8; frozen 84a7a672 + checked preflight fixes + hash-checked demand-range sources'
