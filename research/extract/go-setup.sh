# Go for the Go front end's jobs (core/extract-go.ts): the release the local runs used, unpacked under /tmp once per
# container where the image has another (or none). Source it (`. research/extract/go-setup.sh`) so PATH keeps it.
GDP_GO=1.27.1
if ! go version 2>/dev/null | grep -q "go$GDP_GO "; then
  GDP_ARCH=$(uname -m | sed 's/x86_64/amd64/;s/aarch64/arm64/')
  if [ ! -x /tmp/go/bin/go ]; then
    timeout -s KILL 300 sh -c "curl -fsSL https://go.dev/dl/go$GDP_GO.linux-$GDP_ARCH.tar.gz | tar -C /tmp -xz" || echo "go-setup: the download failed"
  fi
  export PATH=/tmp/go/bin:$HOME/go/bin:$PATH
fi
export GOTOOLCHAIN=local GOFLAGS=-mod=mod
go version
