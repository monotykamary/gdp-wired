#!/usr/bin/env bash
# gdp-wired's "term" image (`supercomputer image build term`, on the repo's image): TermComp's integer transition
# systems (TPDB-ARI at compare/term's pinned commit) at /its and /bench, with LoAT and KoAT2, the tools compare/term and
# research/table's term jobs run. What compare/term/modal_term.py's Modal image had (retired with Modal, in git history).
set -euo pipefail
ARI_COMMIT=183f29db5ec7702215c6aabe12732bf3e836fced
LOAT=v0.9.10
KOAT=v2.7.0

curl -fsSL -o /tmp/loat "https://github.com/LoAT-developers/LoAT/releases/download/$LOAT/loat-static" && sudo install -m 755 /tmp/loat /usr/local/bin/loat
curl -fsSL "https://github.com/aprove-developers/KoAT2-Releases/releases/download/$KOAT/koat2_static.zst" | zstd -d > /tmp/koat2 && sudo install -m 755 /tmp/koat2 /usr/local/bin/koat2
rm -f /tmp/loat /tmp/koat2
B=/opt/gdpw/term/bench
sudo rm -rf "$B" && sudo mkdir -p "$B" && sudo chown "$(id -un)" /opt/gdpw /opt/gdpw/term "$B"
curl -fsSL "https://codeload.github.com/TermCOMP/TPDB-ARI/tar.gz/$ARI_COMMIT" | tar xz -C "$B" --strip-components 1 "TPDB-ARI-$ARI_COMMIT/Integer_Transition_Systems"
for d in /its /bench; do sudo rm -rf "$d" && sudo ln -s "$B" "$d"; done
find "$B" -name '*.ari' | wc -l
