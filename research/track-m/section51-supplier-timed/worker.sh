#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.local/bin:$HOME/.bun/bin:$HOME/.elan/bin:$PATH" SUPERCOMPUTER_CONTROLLER=1
input="$PWD/closure-input"
out=${SUPERCOMPUTER_OUTPUT_DIR:?native output protocol required}
mode=${MLDR_MODE:?}
export MLDR_WORKER_PID=$$
[[ "$mode" == timed || "$mode" == instrumented ]]
bun=/home/user/.bun/bin/bun
mkdir -p "$out"
[[ $("$bun" --version) == 1.4.3 ]]
[[ $(sha256sum "$bun" | cut -d ' ' -f 1) == 7ce7d6b654eddeec20afddf2396317fba6dc19ab52788a27e894e1806bf8f24b ]]
"$bun" "$input/harness/guard.ts" authorize "$input" > "$out/authorization.json"
for key in ${!GDP_@}; do unset "$key"; done
unset NODE_OPTIONS BUN_OPTIONS
scratch=$(mktemp -d /tmp/mldr-9eb-3g.XXXXXX)
memory_stop="$scratch/memory-stop"
source "$input/harness/driver-owner.sh"
driver_owner_init
sampler_pid=''
sampler_code=0
stop_sampler(){
 if [[ -n "$sampler_pid" ]]; then
  : > "$memory_stop"
  wait "$sampler_pid" || sampler_code=$?
  sampler_pid=''
  printf '%s\n' "$sampler_code" > "$out/memory-sampler-exit-code.txt"
 fi
}
cleanup(){
 local code=$?
 trap - EXIT
 trap '' TERM INT HUP
 local driver_terminal=false
 if driver_owner_retire; then driver_terminal=true; fi
 stop_sampler
 driver_owner_receipt > "$out/driver-retirement.json"
 if [[ "$driver_terminal" == true ]]; then rm -rf -- "$scratch"; fi
 printf '{"workerPid":%s,"driverTerminal":%s,"scratchRemoved":%s,"exitCode":%s}\n' "$$" "$driver_terminal" "$([[ ! -e "$scratch" ]] && echo true || echo false)" "$code" > "$out/worker-cleanup.json"
 (cd "$out" && find . -type f ! -name ARTIFACTS.sha256 -print0 | sort -z | xargs -0 sha256sum > ARTIFACTS.sha256)
 exit "$code"
}
trap cleanup EXIT
trap 'exit 143' TERM
trap 'exit 130' INT
trap 'exit 129' HUP
# Instantaneous capacity observations, NOT disk reservations or enforcement claims.
df -Pk "$scratch" "$out" > "$out/disk-before.txt"
[[ $(df -Pk "$scratch" | awk 'NR==2 {print $4}') -ge 25165824 ]]
[[ $(df -Pk "$out" | awk 'NR==2 {print $4}') -ge 25165824 ]]
lscpu > "$out/lscpu.txt"
grep -m1 '^model name' /proc/cpuinfo > "$out/cpu-model.txt"
[[ $(nproc) -ge 16 ]]
grep '^MemTotal:' /proc/meminfo > "$out/memory-total.txt"
[[ $(awk '{print $2}' "$out/memory-total.txt") -ge 29360128 ]]
for f in /sys/fs/cgroup/cpu.max /sys/fs/cgroup/memory.max /proc/sys/kernel/random/boot_id; do
 if [[ -r "$f" ]]; then printf '%s ' "$f"; tr '\n' ' ' < "$f"; printf '\n'; fi
done > "$out/cgroup-boot.txt"
taskset -pc $$ > "$out/affinity.txt"
printf '%s\n' "$$" > "$out/worker-pid.txt"
mkdir "$scratch/target" "$scratch/driver"
tar -xf "$input/source.tar" -C "$scratch/target"
tar -xf "$input/gdp-ts.tar" -C "$scratch/target"
tar -xf "$input/handwired.tar" -C "$scratch/target"
mkdir -p "$scratch/driver/research/track-m/closure-9eb-measurement-v4"
cp "$input/harness/"* "$scratch/driver/research/track-m/closure-9eb-measurement-v4/"
ln -s "$scratch/target/core" "$scratch/driver/core"
ln -s "$scratch/target/kernel" "$scratch/driver/kernel"
ln -s "$scratch/target/research/protocols" "$scratch/driver/research/protocols"
entry="$scratch/driver/research/track-m/closure-9eb-measurement-v4"
export MLDR_TARGET="$scratch/target"
"$bun" "$input/harness/guard.ts" source "$input" "$scratch/target" > "$out/source-before.json"
(cd "$scratch/target" && timeout --foreground --signal=TERM --kill-after=5s 120s "$bun" install --frozen-lockfile) > "$out/install.log" 2>&1
# Recheck protected source AFTER install and BEFORE any prover/model imports.
"$bun" "$input/harness/guard.ts" source "$input" "$scratch/target" > "$out/source-postinstall.json"
# Vendor archives are sealed inputs; no network fetch or fallback.
[[ -f "$scratch/target/vendor/gdp-ts/src/index.ts" && -f "$scratch/target/vendor/handwired/src/json-search/loop-program.ts" ]]
"$bun" "$input/harness/guard.ts" profile "$input" > "$out/profile.env"
while IFS='=' read -r key value; do export "$key=$value"; done < "$out/profile.env"
cp "$input/CONFIG.json" "$input/active-flags.json" "$input/weights.json" "$input/INPUTS.sha256" "$input/SEAL.json" "$input/AUTHORIZATION.json" "$out/"
env | LC_ALL=C sort | grep '^GDP_' > "$out/effective-flags.env"
ulimit -f 65536 # 64MiB per output/log file; trace shards are at most 32MiB
before_code=0
"$bun" "$entry/capture-resources.ts" before > "$out/resource-before.log" 2>&1 || before_code=$?
printf '{"before":%s,"after":null}\n' "$before_code" > "$out/resource-exits.json"
[[ "$before_code" == 0 ]] || exit 68
start=$(date +%s%N)
code=0
bash "$entry/driver-owner.sh" exec "$scratch/driver-owner.identity" "$bun" "$entry/driver.ts" "$input" "$out" "$mode" > "$out/driver.log" 2>&1 &
driver_owner_bind "$!" "$scratch/driver-owner.identity" || exit 69
printf '%s\n' "$driver_pid" > "$out/driver-pid.txt"
printf '%s\n' "$driver_start_ticks" > "$out/driver-start-ticks.txt"
bash "$entry/memory-sampler.sh" "$driver_pid" "$out" "$memory_stop" /proc 2 "$driver_start_ticks" > "$out/memory-sampler.log" 2>&1 &
sampler_pid=$!
driver_owner_wait || code=$?
end=$(date +%s%N)
stop_sampler
replay_code=0
if [[ "$mode" == instrumented && "$code" == 0 ]]; then
 timeout --foreground --signal=TERM --kill-after=5s 240s "$bun" "$entry/replay-trace.ts" "$input" "$out" > "$out/trace-replay.log" 2>&1 || replay_code=$?
fi
after_code=0
"$bun" "$entry/capture-resources.ts" after > "$out/resource-after.log" 2>&1 || after_code=$?
printf '{"before":%s,"after":%s}\n' "$before_code" "$after_code" > "$out/resource-exits.json"
printf '%s\n' "$replay_code" > "$out/trace-replay-exit-code.txt"
printf '%s\n' "$code" > "$out/driver-exit-code.txt"
printf '%s\n' "$((end-start))" > "$out/driver-process-wall-ns.txt"
source_code=0
"$bun" "$input/harness/guard.ts" source "$input" "$scratch/target" > "$out/source-after.json" 2>&1 || source_code=$?
printf '%s\n' "$source_code" > "$out/source-exit-code.txt"
df -Pk "$scratch" "$out" > "$out/disk-after.txt"
if [[ "$code" != 0 || "$source_code" != 0 || "$replay_code" != 0 || "$after_code" != 0 ]]; then exit 1; fi
printf 'DIAGNOSTIC complete mode=%s; pair comparison and native cleanup join still required\n' "$mode"
