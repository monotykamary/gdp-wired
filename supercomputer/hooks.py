"""gdp-wired's hooks for the supercomputer (~/.local/share/supercomputer; its config is ../supercomputer.toml): the
boat image's layers. Everything else this repo needs (its tree's ignore patterns, the Lean library's build cache, the
runner image's PATH on boat, the GPU pods' setup) is plain config there.
"""
import pathlib

# bun and Lean 4.34.0 by elan, as run.py's Modal image has them
TOOLS = r"""
sudo apt-get update -y -q
sudo DEBIAN_FRONTEND=noninteractive apt-get install -y -q curl unzip git ca-certificates xz-utils zstd bzip2 coreutils python3-pip
# as modal/run.py's image: bun (the version that image has) and Lean 4.34.0 by elan
curl -fsSL https://bun.sh/install | bash -s bun-v1.4.3
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.34.0
~/.elan/bin/lean --version
~/.bun/bin/bun --version
sudo mkdir -p /work /src/gdp-wired /bench /smt /vamp /sv /opt/gdpw
sudo chown "$(id -un)" /smt /vamp /sv /opt/gdpw
"""
# The toolchains the lanes' jobs install at their start on Modal (as root, which a boat item isn't): the language
# sweep's (research/langs/*/*-setup.sh: Ruby and Prism, Elixir, clang 19, a JDK 21 and kotlinc 2.4.21, Swift, Rust),
# LiteLLM's Python (uv, its pinned dependencies, a site directory the user installs into), Solidity's solc and anvil
# (research/sol), and the runner image's own (supercomputer/run.py's runner_image: clang 18, GCC 14's libstdc++, Temurin 17), so
# "image": "runner" jobs run on boat too. Each setup script then finds its tool and installs nothing.
LANGS = r"""
export DEBIAN_FRONTEND=noninteractive
get() { curl -fsSL --retry 6 --retry-all-errors --retry-delay 5 -o "$2" "$1"; }  # (a large download whole, or again)
sudo apt-get update -y -q
sudo -E apt-get install -y -q ruby ruby-dev build-essential elixir clang-18 clang g++-14 libstdc++-14-dev libc6-dev unzip pkg-config binutils \
  libcurl4-openssl-dev libedit2 libncurses-dev libpython3-dev libsqlite3-0 libxml2-dev libz3-dev zlib1g-dev tzdata python3-venv
sudo gem install -q --no-document prism
ruby -e 'require "prism"; puts Prism::VERSION'
# clang 19 for the C and C++ front ends (clang-setup.sh's), first on the PATH; the runner image's clang 18 in /usr/lib/llvm-18/bin
. /etc/os-release
curl -fsSL https://apt.llvm.org/llvm-snapshot.gpg.key | sudo tee /etc/apt/trusted.gpg.d/apt.llvm.org.asc > /dev/null
echo "deb http://apt.llvm.org/$VERSION_CODENAME/ llvm-toolchain-$VERSION_CODENAME-19 main" | sudo tee /etc/apt/sources.list.d/llvm.list
sudo apt-get update -y -q && sudo -E apt-get install -y -q clang-19
sudo ln -sf /usr/bin/clang-19 /usr/local/bin/clang && sudo ln -sf /usr/bin/clang++-19 /usr/local/bin/clang++
clang --version | head -1; /usr/lib/llvm-18/bin/clang --version | head -1
# JDK 21 and kotlinc 2.4.21 (jvm-setup.sh's), Temurin 17 (the runner image's)
sudo mkdir -p /opt/jdk /usr/lib/jvm/temurin-17 && sudo chown "$(id -un)" /opt/jdk /usr/lib/jvm/temurin-17
get "https://api.adoptium.net/v3/binary/latest/21/ga/linux/x64/jdk/hotspot/normal/eclipse" /tmp/jdk21.tgz && tar xzf /tmp/jdk21.tgz -C /opt/jdk --strip-components=1
get "https://api.adoptium.net/v3/binary/latest/17/ga/linux/x64/jdk/hotspot/normal/eclipse" /tmp/jdk17.tgz && tar xzf /tmp/jdk17.tgz -C /usr/lib/jvm/temurin-17 --strip-components=1
get https://github.com/JetBrains/kotlin/releases/download/v2.4.21/kotlin-compiler-2.4.21.zip /tmp/kotlinc.zip && sudo unzip -q -o /tmp/kotlinc.zip -d /opt
rm -f /tmp/jdk21.tgz /tmp/jdk17.tgz /tmp/kotlinc.zip
sudo ln -sf /opt/kotlinc/bin/kotlinc /usr/local/bin/kotlinc
/opt/jdk/bin/javac -version; /usr/lib/jvm/temurin-17/bin/javac -version
# Swift 6.3.3 for this Ubuntu (swift-setup.sh's, which names Debian 12's)
sudo mkdir -p /opt/swift && sudo chown "$(id -un)" /opt/swift
get "https://download.swift.org/swift-6.3.3-release/ubuntu2404/swift-6.3.3-RELEASE/swift-6.3.3-RELEASE-ubuntu24.04.tar.gz" /tmp/swift.tgz && tar xzf /tmp/swift.tgz -C /opt/swift --strip-components=1 && rm /tmp/swift.tgz
/opt/swift/usr/bin/swift --version 2>&1 | head -1
# Rust, minimal stable, for every user: the toolchain's own cargo, rustc and rustdoc linked into /usr/local/bin (rustup's
# proxies answered as rustup outside the installing user's home); rust-setup.sh then finds cargo
sudo mkdir -p /opt/rustup /opt/cargo && sudo chown "$(id -un)" /opt/rustup /opt/cargo
curl -sSf https://sh.rustup.rs | RUSTUP_HOME=/opt/rustup CARGO_HOME=/opt/cargo sh -s -- -y --no-modify-path --profile minimal --default-toolchain stable
for b in cargo rustc rustdoc; do sudo ln -sf "$(ls -d /opt/rustup/toolchains/stable-*/bin)/$b" /usr/local/bin/$b; done
rm -rf ~/.cargo ~/.rustup
env -i HOME=/tmp PATH=/usr/local/bin:/usr/bin:/bin cargo --version | grep '^cargo '
# solc 0.8.28 and anvil 1.5.1 (research/sol/sol-setup.sh's, pinned as research/sol/DESIGN.md measured them on Modal), so
# core/extract-sol.test.ts, core/sol/harness.py and the Solidity measure jobs run on boat
sudo mkdir -p /opt/sol /opt/foundry && sudo chown "$(id -un)" /opt/sol /opt/foundry
get https://github.com/ethereum/solidity/releases/download/v0.8.28/solc-static-linux /opt/sol/solc && chmod +x /opt/sol/solc
get https://github.com/foundry-rs/foundry/releases/download/v1.5.1/foundry_v1.5.1_linux_amd64.tar.gz /tmp/foundry.tgz && tar xzf /tmp/foundry.tgz -C /opt/foundry && rm /tmp/foundry.tgz
/opt/sol/solc --version | tail -1; /opt/foundry/anvil --version | head -1
# LiteLLM's Python: uv, its pinned dependencies, and the system site directory the user installs into (uv pip install --system)
sudo pip install --break-system-packages -q uv
for d in $(python3 -c 'import site; print(" ".join(site.getsitepackages()))') /usr/local/bin; do sudo mkdir -p "$d"; sudo chown -R "$(id -un)" "$d"; done
uv pip install --system --break-system-packages -q 'litellm[proxy]==1.106.6'
python3 -c 'import litellm.proxy.auth.auth_checks; print("litellm deps ok")'
"""
# the compare runners' solvers, a layer each (their BOAT_SETUP, next to their Modal image), the slowest to build first
RUNNERS = ["compare/tip/modal_tip.py", "compare/chc/modal_chc.py", "compare/term/modal_term.py", "compare/term/modal_sv.py"]


def runner_boat(root: pathlib.Path, path: str) -> dict:
    """A compare runner's boat setting (its BOAT_SETUP and BOAT), read under the Modal stub (the real client, if this
    process has it, is put back after)."""
    import sys
    from supercomputer import agent
    had = sys.modules.get("modal")
    sys.modules["modal"] = agent.modal_stub()
    try:
        mod = agent.import_runner(str(root / path))
    finally:
        if had is not None:
            sys.modules["modal"] = had
        else:
            sys.modules.pop("modal", None)
    return {"setup": getattr(mod, "BOAT_SETUP", ""), **getattr(mod, "BOAT", {})}


def layers(root: pathlib.Path) -> list[tuple[str, str]]:
    """The image's layers, bottom first: the tools, each compare runner's solvers and benchmarks (its BOAT_SETUP, the
    slowest to build first), the languages. The names and scripts hash into each layer's snapshot name, so these are
    the image Lane P built (sc-f0d8daeee6c3 at 6c934c9)."""
    return [("tools", TOOLS), *[(pathlib.Path(r).stem.removeprefix("modal_"), runner_boat(root, r)["setup"]) for r in RUNNERS], ("langs", LANGS)]
