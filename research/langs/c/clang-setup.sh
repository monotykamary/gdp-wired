# clang for the C and C++ front ends' jobs (core/extract-c.ts), once per container: LLVM's clang 19 for the image's
# Debian (apt.llvm.org; Debian 12's own clang 14 has no -fstrict-flex-arrays, so a fixed array last in a struct isn't
# bounds-checked by the sanitizer), else Debian's. Source it (`. research/langs/c/clang-setup.sh`).
if ! command -v clang >/dev/null 2>&1; then
  timeout -s KILL 400 sh -c '. /etc/os-release; curl -fsSL https://apt.llvm.org/llvm-snapshot.gpg.key -o /etc/apt/trusted.gpg.d/apt.llvm.org.asc && echo "deb http://apt.llvm.org/$VERSION_CODENAME/ llvm-toolchain-$VERSION_CODENAME-19 main" > /etc/apt/sources.list.d/llvm.list && apt-get update -qq >/dev/null 2>&1 && apt-get install -y -qq clang-19 libc6-dev >/dev/null 2>&1 && ln -sf /usr/bin/clang-19 /usr/local/bin/clang' \
    || { rm -f /etc/apt/sources.list.d/llvm.list; timeout -s KILL 300 sh -c 'apt-get update -qq >/dev/null 2>&1 && apt-get install -y -qq clang libc6-dev >/dev/null 2>&1' || echo "clang-setup: the install failed"; }
fi
clang --version | head -1
