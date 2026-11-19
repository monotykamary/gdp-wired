# Sourced, never mutates the worker's shared npm cache.
for candidate in /opt/node-v24.22.1/bin/node /usr/local/bin/node "$(type -P node || true)"; do
  if [[ -x $candidate && $("$candidate" --version) = v24.22.1 ]]; then NODE=$candidate; break; fi
done
if [[ -z ${NODE:-} ]]; then
  node_cache=$(mktemp -d)
  trap 'rm -rf "$node_cache"' EXIT
  NODE=$(npm_config_cache="$node_cache" npm exec --yes --package=node@24.22.1 -- which node)
fi
"$NODE" --version
test "$("$NODE" --version)" = v24.22.1
