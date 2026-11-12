#!/usr/bin/env bash
# External observation only. Never signals the driver or changes proof budgets.
set -uo pipefail
pid=${1:?driver pid}; out=${2:?native output}; stop=${3:?stop marker}
proc=${4:-/proc}; interval=${5:-2}; expected_ticks=${6:-}; max_samples=40000
[[ "$pid" =~ ^[1-9][0-9]{0,9}$ && "$interval" =~ ^(0|[1-9][0-9]{0,2})([.][0-9]{1,3})?$ ]] || exit 64
awk -v n="$interval" 'BEGIN { exit !(n > 0 && n <= 60) }' || exit 64
samples=0; errors=0; peak_rss=null; peak_hwm=null; start_ticks=''; reason=starting
phase=unavailable; phase_seq=null; phase_ns=null; complete=false
get_ticks(){
 local raw rest
 local -a fields
 IFS= read -r raw < "$proc/$pid/stat" || return 1
 rest=${raw##*) }; read -r -a fields <<< "$rest"
 [[ ${fields[19]:-} =~ ^[0-9]+$ ]] || return 1
 printf '%s' "${fields[19]}"
}
read_phase(){
 local p='' seq='' name='' ns=''
 phase=unavailable; phase_seq=null; phase_ns=null
 if [[ -r "$out/phase-marker.tsv" ]]; then
  IFS=$'\t' read -r p seq name ns < "$out/phase-marker.tsv" || true
  if [[ "$p" == "$pid" && "$seq" =~ ^[1-9][0-9]*$ && "$name" =~ ^[a-z][a-z0-9-]{0,63}$ && "$ns" =~ ^[0-9]+$ ]]; then
   phase=$name; phase_seq=$seq; phase_ns=\"$ns\"
  fi
 fi
}
summary(){
 local ticks_json=null
 [[ -n "$start_ticks" ]] && ticks_json=\"$start_ticks\"
 printf '{"schema":"mldr-peak-memory/v1","driverPid":%s,"driverStartTicks":%s,"sampleIntervalSeconds":%s,"sampleLimit":%s,"sampleCount":%s,"readErrors":%s,"sampledPeakRssKiB":%s,"sampledPeakVmHwmKiB":%s,"finalProcessPeakExact":false,"meaning":"maximum observed /proc driver VmHWM; lower bound on final process high-water","lastObservedPhase":"%s","phaseSequence":%s,"phaseDriverHrtimeNs":%s,"complete":%s,"stopReason":"%s"}\n' "$pid" "$ticks_json" "$interval" "$max_samples" "$samples" "$errors" "$peak_rss" "$peak_hwm" "$phase" "$phase_seq" "$phase_ns" "$complete" "$reason" > "$out/peak-memory.json.tmp" && mv -f -- "$out/peak-memory.json.tmp" "$out/peak-memory.json"
}
finish(){ read_phase; summary || true; }
trap finish EXIT
trap 'reason=sampler-signal; exit 0' TERM INT
[[ "$expected_ticks" =~ ^[0-9]+$ ]] || { reason=missing-owner-start-identity; exit 64; }
start_ticks=$expected_ticks
observed_ticks=$(get_ticks 2>/dev/null) || { reason=driver-unavailable-before-first-sample; exit 0; }
[[ "$observed_ticks" == "$expected_ticks" ]] || { reason=pid-identity-changed-before-first-sample; exit 0; }
reason=sampling
while [[ ! -e "$stop" && $samples -lt $max_samples ]]; do
 ticks=$(get_ticks 2>/dev/null) || { reason=driver-gone; complete=true; break; }
 [[ "$ticks" == "$start_ticks" ]] || { reason=pid-identity-changed; break; }
 rss=null; hwm=null; size=null
 if [[ -r "$proc/$pid/status" ]]; then
  while IFS=: read -r key value; do
   read -r amount unit <<< "$value"
   [[ "${amount:-}" =~ ^(0|[1-9][0-9]{0,15})$ && "${unit:-}" == kB ]] || continue
   case "$key" in VmRSS) rss=$amount;; VmHWM) hwm=$amount;; VmSize) size=$amount;; esac
  done < "$proc/$pid/status"
 else errors=$((errors+1)); fi
 # Refuse attribution if the PID disappeared or changed during sampling.
 after=$(get_ticks 2>/dev/null) || { reason=driver-gone-during-sample; complete=true; break; }
 [[ "$after" == "$start_ticks" ]] || { reason=pid-identity-changed; break; }
 [[ "$rss" != null || "$hwm" != null ]] || errors=$((errors+1))
 if [[ "$rss" != null && ( "$peak_rss" == null || "$rss" -gt "$peak_rss" ) ]]; then peak_rss=$rss; fi
 if [[ "$hwm" != null && ( "$peak_hwm" == null || "$hwm" -gt "$peak_hwm" ) ]]; then peak_hwm=$hwm; fi
 read_phase
 utc=$(date -u +%Y-%m-%dT%H:%M:%S.%NZ)
 uptime=''; IFS=' ' read -r uptime _ < "$proc/uptime" || true
 [[ "$uptime" =~ ^[0-9]+([.][0-9]+)?$ ]] || uptime=unavailable
 samples=$((samples+1))
 printf '{"schema":"mldr-memory-sample/v1","sample":%s,"capturedAt":"%s","uptimeSeconds":"%s","driverPid":%s,"driverStartTicks":"%s","rssKiB":%s,"vmHwmKiB":%s,"vmSizeKiB":%s,"phase":"%s","phaseSequence":%s,"phaseDriverHrtimeNs":%s}\n' "$samples" "$utc" "$uptime" "$pid" "$start_ticks" "$rss" "$hwm" "$size" "$phase" "$phase_seq" "$phase_ns" >> "$out/memory-samples.jsonl" || { reason=sample-write-failed; exit 1; }
 summary || { reason=summary-write-failed; exit 1; }
 sleep "$interval" || { reason=sleep-failed; exit 1; }
done
if [[ "$reason" == sampling ]]; then
 if [[ -e "$stop" ]]; then reason=worker-requested-stop; complete=true; else reason=sample-limit; fi
fi
