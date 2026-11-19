# Sourced, never mutates the worker's shared npm cache.
node_sha256=e32e2d16081cf644f88392934288086e7662529d0d43277c34f7aad2207cfafb
pinned_node() {
  [[ -x $1 && $(sha256sum -- "$1" | cut -d ' ' -f 1) == "$node_sha256" ]]
}
NODE=''
for candidate in /opt/node-v24.22.1/bin/node /usr/local/bin/node "$(type -P node || true)"; do
  if pinned_node "$candidate"; then NODE=$candidate; break; fi
done
if [[ -z ${NODE:-} ]]; then
  node_cache=$(mktemp -d)
  trap 'rm -rf "$node_cache"' EXIT
  npm_config_cache="$node_cache/npm" npm install --ignore-scripts --no-audit --no-fund --prefix "$node_cache" node-linux-x64@24.22.1 >&2
  NODE="$node_cache/node_modules/node-linux-x64/bin/node"
fi
pinned_node "$NODE" || return 1
"$NODE" --version
test "$("$NODE" --version)" = v24.22.1
