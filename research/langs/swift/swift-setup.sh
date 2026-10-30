# A Swift toolchain for the Swift front end's jobs (core/extract-swift.ts) in the suite's Debian 12 image, once per
# container: swift.org's 6.3.3 release for Debian 12 and the system libraries it links with, unless swift is there.
# Source it (`. research/langs/swift/swift-setup.sh`): it puts /opt/swift/usr/bin on the PATH.
if ! command -v swift >/dev/null 2>&1; then
  if [ ! -x /opt/swift/usr/bin/swift ]; then
    timeout -s KILL 300 sh -c 'apt-get -qq update >/dev/null && DEBIAN_FRONTEND=noninteractive apt-get -qq install -y binutils libc6-dev libcurl4-openssl-dev libedit2 libgcc-12-dev libncurses-dev libpython3-dev libsqlite3-0 libstdc++-12-dev libxml2-dev libz3-dev pkg-config tzdata unzip zlib1g-dev git >/dev/null' || echo "swift-setup: the system libraries failed"
    mkdir -p /opt/swift && timeout -s KILL 400 sh -c 'curl -fsSL https://download.swift.org/swift-6.3.3-release/debian12/swift-6.3.3-RELEASE/swift-6.3.3-RELEASE-debian12.tar.gz | tar xz -C /opt/swift --strip-components=1' || echo "swift-setup: the toolchain failed"
  fi
  export PATH="/opt/swift/usr/bin:$PATH"
fi
swift --version 2>&1 | head -1
