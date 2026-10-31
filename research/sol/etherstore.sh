# Solidity by Example's EtherStore (the DAO's re-entrancy shape; solidity-by-example.github.io, MIT), pinned: its law
# inserted above the contract as a comment, then `gdp-wired check` on the code as it is (vulnerable), with the balance
# cleared before the call (checks-effects-interactions), and with the page's own ReEntrancyGuard on withdraw.
#   . research/sol/sol-setup.sh; sh research/sol/etherstore.sh [ms]
set -e
SBE=${SBE:-/tmp/sbe}
REV=5bcdca0239409d7336a07b66a6fca8d0bcc710e6
if [ ! -d "$SBE" ]; then git init -q "$SBE" && git -C "$SBE" fetch -q --depth 1 https://github.com/solidity-by-example/solidity-by-example.github.io "$REV" && git -C "$SBE" checkout -q FETCH_HEAD; fi
git -C "$SBE" rev-parse HEAD
D=/tmp/etherstore; mkdir -p $D/vulnerable $D/cei $D/guard
SRC="$SBE/contracts/src/hacks/re-entrancy"
LAW='/// gdp: law the store holds what it owes: balance >= sum(balances)'
for v in vulnerable cei guard; do cp "$SRC/ReEntrancy.sol" $D/$v/EtherStore.sol; perl -0pi -e "s|(\ncontract EtherStore \\{)|\n$LAW\$1|" $D/$v/EtherStore.sol; done
# checks-effects-interactions: the balance cleared before the value is sent
perl -0pi -e 's/(require\(bal > 0\);\n)/$1        balances[msg.sender] = 0;\n/; s/(require\(sent, "Failed to send Ether"\);\n)\s*balances\[msg.sender\] = 0;\n/$1/' $D/cei/EtherStore.sol
# the guard: Solidity by Example's ReEntrancyGuard, its noReentrant on withdraw
{ sed -n '1,2p' $D/guard/EtherStore.sol; grep -v -E '^(// SPDX|pragma)' "$SRC/ReEntrancyGuard.sol"; sed '1,2d' $D/guard/EtherStore.sol; } > $D/guard/g.sol && mv $D/guard/g.sol $D/guard/EtherStore.sol
perl -0pi -e 's/contract EtherStore \{/contract EtherStore is ReEntrancyGuard {/; s/function withdraw\(\) public \{/function withdraw() public noReentrant {/' $D/guard/EtherStore.sol
for v in vulnerable cei guard; do echo "=== $v"; diff "$SRC/ReEntrancy.sol" $D/$v/EtherStore.sol || true; GDP_CYCLIC_LOG= bun core/cli.ts check $D/$v/EtherStore.sol --entry EtherStore --ms "${1:-60000}" --no-propose 2>&1 | grep -v '^cyclic:'; done
