# solc and foundry's anvil for the Solidity front end's jobs (core/extract-sol.ts), once per container: solc 0.8.28's
# static Linux build (ethereum/solidity's release) and foundry's stable release (anvil, the EVM the check runs the
# bytecode on), unless the image has them. Source it (`. research/sol/sol-setup.sh`): it puts both on the PATH.
SOLC_VERSION=${SOLC_VERSION:-0.8.28}
if ! command -v solc >/dev/null 2>&1 || ! solc --version | grep -q "$SOLC_VERSION"; then
  mkdir -p /opt/sol
  [ -x /opt/sol/solc ] || timeout -s KILL 120 curl -fsSL -o /opt/sol/solc "https://github.com/ethereum/solidity/releases/download/v$SOLC_VERSION/solc-static-linux" && chmod +x /opt/sol/solc || echo "sol-setup: solc failed"
  export PATH="/opt/sol:$PATH"
fi
if ! command -v anvil >/dev/null 2>&1; then
  mkdir -p /opt/foundry
  [ -x /opt/foundry/anvil ] || timeout -s KILL 180 sh -c 'curl -fsSL https://github.com/foundry-rs/foundry/releases/download/stable/foundry_stable_linux_amd64.tar.gz | tar xz -C /opt/foundry' || echo "sol-setup: foundry failed"
  export PATH="/opt/foundry:$PATH"
fi
solc --version | tail -1; anvil --version | head -1
