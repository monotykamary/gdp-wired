#!/usr/bin/env bash
# gdp-wired's "chc" image (`supercomputer image build chc`, on the repo's image): the CHC-COMP'26 LIA-Lin benchmarks at
# compare/chc's pinned commit at /chc and /bench, the CHC solvers the compare and research jobs run (z3, cvc5, Golem,
# Eldarica), and, as the image's data (supercomputer.toml), research/dag's dumped step goals at /goals, the table's at
# /goals223 and Spacer's models at /data/spacer-models.jsonl. What compare/chc/modal_chc.py's and research/dag's,
# research/step's and research/query's Modal images had (retired with Modal, in git history).
set -euo pipefail
BENCH_COMMIT=b4fa7a708e5863bbcdb5de50d692ead3a67cbedc

curl -fsSL -o /tmp/z3.zip https://github.com/Z3Prover/z3/releases/download/z3-5.3.1/z3-5.3.1-x64-glibc-2.39.zip
sudo unzip -q -o /tmp/z3.zip -d /opt && sudo ln -sf /opt/z3-5.3.1-x64-glibc-2.39/bin/z3 /usr/local/bin/z3 && z3 --version
curl -fsSL -o /tmp/cvc5.zip https://github.com/cvc5/cvc5/releases/download/cvc5-1.4.1/cvc5-Linux-x86_64-static.zip
sudo rm -rf /opt/cvc5 && sudo unzip -q -o /tmp/cvc5.zip -d /opt/cvc5 && sudo ln -sf "$(find /opt/cvc5 -name cvc5 -type f | head -1)" /usr/local/bin/cvc5 && cvc5 --version | head -1
curl -fsSL https://github.com/usi-verification-and-security/golem/releases/download/v0.9.0/golem-x64-linux.tar.bz2 | sudo tar xj -C /opt
sudo ln -sf "$(find /opt -name golem -type f | head -1)" /usr/local/bin/golem && golem --version
curl -fsSL https://github.com/uuverifiers/eldarica/releases/download/v2.3/eldarica-x86-linux-static.gz | gunzip | sudo tee /usr/local/bin/eld > /dev/null
sudo chmod +x /usr/local/bin/eld && eld -h | head -3
rm -f /tmp/z3.zip /tmp/cvc5.zip

# the benchmarks: only LIA-Lin's tasks and the files they name
B=/opt/gdpw/chc/bench
sudo rm -rf "$B" && sudo mkdir -p "$B" && sudo chown "$(id -un)" /opt/gdpw /opt/gdpw/chc "$B"
curl -fsSL "https://codeload.github.com/chc-comp/chc-comp26-benchmarks/tar.gz/$BENCH_COMMIT" | tar xz -C "$B" --strip-components 1
python3 - "$B" <<'PY'
import pathlib, re, sys
root = pathlib.Path(sys.argv[1])
keep = set()
for y in (root / 'LIA-Lin.set').read_text().split():
    y = root / y
    keep.add(y)
    keep.add(y.parent / re.search(r'^input_files:\s*(\S+)', y.read_text(), re.M).group(1))
for p in sorted(root.rglob('*'), reverse=True):
    if p.is_file() and p not in keep and p.name != 'LIA-Lin.set':
        p.unlink()
    elif p.is_dir() and not any(p.iterdir()):
        p.rmdir()
PY
for d in /chc /bench; do sudo rm -rf "$d" && sudo ln -s "$B" "$d"; done
du -sh "$B"; find "$B" -name '*.yml' | wc -l
for d in /goals /goals223; do ls "$d" | wc -l; done
wc -l /data/spacer-models.jsonl
