import {readFileSync,readlinkSync,existsSync} from 'node:fs'
import {execFileSync} from 'node:child_process'
const cpu0=process.cpuUsage(),t0=performance.now();let n=0
while(performance.now()-t0<300)n++
const cpu=process.cpuUsage(cpu0)
console.log(JSON.stringify({test:'vm-health',wallMs:performance.now()-t0,cpuMs:(cpu.user+cpu.system)/1000,n,load:readFileSync('/proc/loadavg','utf8').trim(),pressure:readFileSync('/proc/pressure/cpu','utf8').trim()}))
const rows=execFileSync('ps',['-eo','pid,ppid,pcpu,pmem,etimes,args','--sort=-pcpu'],{encoding:'utf8'}).trim().split('\n').slice(0,26)
for(const row of rows){if(!/bun|node|tsc|oxlint/.test(row))continue;const pid=row.trim().split(/\s+/)[0]!;let cwd='';try{cwd=readlinkSync(`/proc/${pid}/cwd`)}catch{};console.log(JSON.stringify({process:row,cwd,hasTA:!!cwd&&existsSync(cwd+'/research/track-m/section8-ta-observer.ts')}))}
