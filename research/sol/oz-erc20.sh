# OpenZeppelin Contracts' ERC20Mock (v5.1.0, MIT) read with nothing written beyond its laws as comments: the laws are
# inserted above the contract in a copy pinned at the release's commit, then `gdp-wired check` proves or breaks them.
#   . research/sol/sol-setup.sh; sh research/sol/oz-erc20.sh [ms]
set -e
OZ=${OZ:-/tmp/oz5}
REV=69c8def5f222ff96f2b5beff05dfba996368aa79
if [ ! -d "$OZ" ]; then git init -q "$OZ" && git -C "$OZ" fetch -q --depth 1 https://github.com/OpenZeppelin/openzeppelin-contracts "$REV" && git -C "$OZ" checkout -q FETCH_HEAD; fi
git -C "$OZ" rev-parse HEAD
F="$OZ/contracts/mocks/token/ERC20Mock.sol"
grep -q 'gdp: law' "$F" || perl -0pi -e 's/(contract ERC20Mock is ERC20 \{)/\/\/\/ gdp: law the balances sum to the supply: sum(_balances) == _totalSupply\n\/\/\/ gdp: law no balance exceeds the supply: forall a in _balances: _balances[a] <= _totalSupply\n\/\/\/ gdp: law transfer never mints: method == "transfer" implies _totalSupply == old(_totalSupply)\n\/\/\/ gdp: law transferFrom never mints: method == "transferFrom" implies _totalSupply == old(_totalSupply)\n$1/' "$F"
grep -n 'gdp: law' "$F"
GDP_CYCLIC_LOG= bun core/cli.ts check "$F" --ms "${1:-60000}" --no-propose 2>&1 | grep -v '^cyclic:'
