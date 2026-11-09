#!/usr/bin/env bash
# The production command is unchanged; installation, identity and hashing are outside its 60 s wall.
set -eu
suite=$1; id=$2; repeat=$3; mode=$4
bun install --frozen-lockfile >/dev/null
script=research/protocols/ic3syn/run.ts
skip=broken
if [ "$suite" = duoai ]; then script=research/protocols/run.ts; skip=given,broken; fi
if [ "$mode" = broken ]; then skip=search; fi
cpus=$(python3 -c 'import os; print(",".join(map(str,sorted(os.sched_getaffinity(0))[:4])))')
echo "VERIFY suite=$suite id=$id repeat=$repeat mode=$mode baseline=$(<research/verify-all/BASELINE)"
echo "PIN cpus=$cpus"
lscpu | grep -E 'Architecture:|CPU\(s\):|Model name:|Thread\(s\) per core:|Core\(s\) per socket:'
bun --version
sha256sum kernel/kernel.ts kernel/prove.ts core/dsl.ts research/protocols/ic3syn/run.ts research/protocols/ic3syn/models.ts research/protocols/run.ts research/protocols/models.ts
find core kernel lean-kernel -type f \( -name '*.ts' -o -name '*.lean' \) -print0 | LC_ALL=C sort -z | xargs -0 sha256sum > /tmp/verify-source-manifest.sha256
sha256sum /tmp/verify-source-manifest.sha256
echo "COMMAND taskset -c $cpus timeout -s KILL 60 bun $script --ms 60000 --only $id --skip $skip"
set +e
/usr/bin/time -f 'WALL seconds=%e user=%U sys=%S maxrss_kb=%M exit=%x' taskset -c "$cpus" timeout -s KILL 60 bun "$script" --ms 60000 --only "$id" --skip "$skip"
status=$?
set -e
echo "RESULT exit=$status"
exit "$status"
