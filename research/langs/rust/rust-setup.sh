# Rust for the Rust front end's jobs (core/extract-rs.ts): a minimal stable toolchain under $HOME once per container
# where the image has none. Source it (`. research/langs/rust/rust-setup.sh`) so PATH keeps it.
if ! cargo --version >/dev/null 2>&1; then
  if [ ! -x "$HOME/.cargo/bin/cargo" ]; then
    timeout -s KILL 300 sh -c 'curl -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal --default-toolchain stable >/dev/null 2>&1' || echo "rust-setup: the install failed"
  fi
  export PATH="$HOME/.cargo/bin:$PATH"
fi
cargo --version
