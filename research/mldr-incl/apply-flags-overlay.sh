#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "$0")" && pwd)
check() { printf '%s  %s\n' "$1" "$2" | sha256sum -c -; }
replace() {
 local file=$1 old=$2 new=$3 from=$4
 if test "$old" = absent; then test ! -f "$file"; else check "$old" "$file"; fi
 check "$new" "$here/$from"; cp "$here/$from" "$file"; check "$new" "$file"
}
replace core/counts.ts d9a1f9dcbb376161708d8bda8854e75f4d8c61cc009d03cefc0a2e528bbe865b f9fd534aa3fd8489046c6add197171176eab866374acb0656023e6e3a8f62305 counts.txt
replace core/count-recovery/member-premises.ts 4e63043f1ae2ba6417d5571a194b06b181b9fa84ed3ed99bf791f6a66e645b2e 134320639aad5112ccd5cbec37d3eaa9c1096f5bb3d54524f289410058eee47e member-premises.txt
replace core/count-recovery/member-premises.test.ts d4bfc0ac682b6807605007b17eb53ee5163fe8c04c468feb9588a32998ff6b2d 28bb855a2249f0dbe53acc00a84680aabe5881457636b4097b4c0351693e33f8 member-premises.test.txt
replace research/mldr-incl/install-member-source-rank.ts absent bdf09d367805cc0b00bf64a90d46af4162204c06e962e5046cdea80bec40495b install-member-source-rank.txt
replace research/mldr-incl/install-member-source-rank.test.ts absent 5e305cd05435aa1b19626048a94afb95e3732eb01f68c00502835a17ee3042f7 install-member-source-rank.test.txt
printf '%s\n' 'LANE_E_FLAGS_SOURCE=9124348d5d313ab7e89082b0146a72d6a7c8bf66; checked demand-range base plus hash-checked flags-first source'
