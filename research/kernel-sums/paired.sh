#!/usr/bin/env bash
set -euo pipefail
source research/kernel-sums/pin-node.sh
stock=$(mktemp -d)
cleanup() { rm -rf "$stock"; if [[ -n ${node_cache:-} ]]; then rm -rf "$node_cache"; fi; }
trap cleanup EXIT
sha256sum -c lane-data/stock.sha256
export KERNEL_SUMS_STOCK=$stock
tar -xzf lane-data/stock.tar.gz -C "$stock"
"$NODE" --experimental-transform-types --disable-warning=ExperimentalWarning research/kernel-sums/paired.mjs "$@"
