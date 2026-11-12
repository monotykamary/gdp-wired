#!/usr/bin/env bash
# Source for one owned child, or exec a payload after publishing its birth ID.
# No process-name/group signaling. No scratch retirement before terminal join.
driver_owner_stat(){
 local raw rest; local -a fields
 IFS= read -r raw < "/proc/$1/stat" 2>/dev/null || return 1
 rest=${raw##*) }; read -r -a fields <<< "$rest"
 [[ ${fields[19]:-} =~ ^[0-9]+$ ]] || return 1
 printf '%s %s\n' "${fields[0]}" "${fields[19]}"
}
driver_owner_init(){
 driver_pid=''; driver_start_ticks=''; driver_joined=true; driver_exit_code=null
 driver_term_sent=false; driver_kill_sent=false; driver_disposition=not-started
}
driver_owner_bind(){
 driver_pid=$1; driver_joined=false; driver_disposition=awaiting-identity
 local file=$2 owner='' ticks='' i
 for ((i=0;i<40;i++)); do
  if [[ -r "$file" ]]; then
   read -r owner ticks < "$file" || true
   if [[ "$owner" == "$driver_pid" && "$ticks" =~ ^[0-9]+$ ]]; then
    driver_start_ticks=$ticks; driver_disposition=owned; return 0
   fi
  fi
  [[ -e "/proc/$driver_pid/stat" ]] || break
  sleep 0.05
 done
 driver_disposition=identity-unavailable; return 1
}
driver_owner_live(){
 [[ -n "$driver_start_ticks" ]] || return 2
 local state ticks row
 row=$(driver_owner_stat "$driver_pid") || return 1
 read -r state ticks <<< "$row"
 [[ "$ticks" == "$driver_start_ticks" && "$state" != Z && "$state" != X ]]
}
driver_owner_wait(){
 [[ "$driver_joined" == false ]] || return 0
 local code=0
 wait "$driver_pid" || code=$?
 driver_exit_code=$code; driver_joined=true
 if [[ "$driver_disposition" == owned ]]; then driver_disposition=normal-wait; fi
 return "$code"
}
driver_owner_retire(){
 [[ -n "$driver_pid" && "$driver_joined" == false ]] || return 0
 local status i
 if driver_owner_live; then status=0; else status=$?; fi
 if [[ "$status" == 2 ]]; then driver_disposition=identity-unavailable-scratch-retained; return 1; fi
 if [[ "$status" == 0 ]]; then
  if kill -TERM "$driver_pid" 2>/dev/null; then driver_term_sent=true; fi
  driver_disposition=term-sent
  for ((i=0;i<40;i++)); do if ! driver_owner_live; then break; fi; sleep 0.05; done
  if driver_owner_live; then
   if kill -KILL "$driver_pid" 2>/dev/null; then driver_kill_sent=true; fi
   driver_disposition=kill-sent
   for ((i=0;i<40;i++)); do if ! driver_owner_live; then break; fi; sleep 0.05; done
  fi
  if driver_owner_live; then driver_disposition=unreaped-scratch-retained; return 1; fi
 fi
 # A dead/zombie/replaced birth identity cannot still be the live owned child.
 # This is the sole terminal join after a normal wait was interrupted.
 driver_owner_wait || true
 driver_disposition=terminal-joined
 return 0
}
driver_owner_receipt(){
 local pid=null ticks=null
 [[ -z "$driver_pid" ]] || pid=$driver_pid
 [[ -z "$driver_start_ticks" ]] || ticks=\"$driver_start_ticks\"
 printf '{"pid":%s,"startTicks":%s,"joined":%s,"exitCode":%s,"termSent":%s,"killSent":%s,"disposition":"%s"}\n' "$pid" "$ticks" "$driver_joined" "$driver_exit_code" "$driver_term_sent" "$driver_kill_sent" "$driver_disposition"
}
if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
 set -euo pipefail
 [[ ${1:-} == exec && $# -ge 4 ]] || exit 64
 identity=$2; shift 2
 read -r state ticks < <(driver_owner_stat "$$")
 printf '%s %s\n' "$$" "$ticks" > "$identity.tmp"
 mv -f -- "$identity.tmp" "$identity"
 exec "$@"
fi
