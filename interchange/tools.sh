#!/bin/sh
# The two tools the WebAssembly checker needs on an x86_64 Linux host (a Modal container, a boat VM), fetched into $1
# (default /tmp/gdp-tools) and checked against their pinned SHA-256: Javy 9.1.0, which builds the module, and Wasmtime
# 49.0.1, which runs it (any WASI preview 1 host does: wasmer, node:wasi). Prints the two paths. On a Mac: Javy's
# javy-arm-macos-v9.1.0.gz from the same release, and `wasmer run` or node's WASI (interchange/wasm-run.ts).
set -e
dir=${1:-/tmp/gdp-tools}
mkdir -p "$dir"
fetch() { # url sha256 file
  [ -f "$dir/$3" ] && echo "$2  $dir/$3" | sha256sum -c - >/dev/null 2>&1 && return 0
  curl -fsSL -o "$dir/$3" "$1"
  echo "$2  $dir/$3" | sha256sum -c - >/dev/null || { echo "checksum mismatch: $3" >&2; exit 1; }
}
fetch https://github.com/bytecodealliance/javy/releases/download/v9.1.0/javy-x86_64-linux-v9.1.0.gz a68b122d48eb3dfc1b801d4e14c39271fde3638243d3272d206e376ac9189e39 javy.gz
fetch https://github.com/bytecodealliance/wasmtime/releases/download/v49.0.1/wasmtime-v49.0.1-x86_64-linux.tar.xz c71f7e0d30a92e418f0d17db7c6d8f6664c1ad764340a1278678f4209deab534 wasmtime.tar.xz
[ -x "$dir/javy" ] || { gunzip -c "$dir/javy.gz" > "$dir/javy"; chmod +x "$dir/javy"; }
[ -x "$dir/wasmtime" ] || { tar -xJf "$dir/wasmtime.tar.xz" -C "$dir"; cp "$dir"/wasmtime-v49.0.1-x86_64-linux/wasmtime "$dir/wasmtime"; }
echo "$dir/javy"
echo "$dir/wasmtime"
