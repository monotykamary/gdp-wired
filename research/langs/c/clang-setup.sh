# clang for the C and C++ front ends' jobs (core/extract-c.ts): Debian's, once per container. Source it
# (`. research/langs/c/clang-setup.sh`).
if ! command -v clang >/dev/null 2>&1; then
  timeout -s KILL 300 sh -c 'apt-get update -qq >/dev/null 2>&1 && apt-get install -y -qq clang libc6-dev >/dev/null 2>&1' || echo "clang-setup: the install failed"
fi
clang --version | head -1
