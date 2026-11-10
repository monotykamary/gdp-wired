// Observation only: original 60s benchmark default, measured host/cgroup counters and child PIDs.
import {readFileSync,openSync,closeSync,unlinkSync} from 'node:fs'
import {join} from 'node:path'
import {spawn,spawnSync} from 'node:child_process'
const read=(path:string)=>{try{return readFileSync(path,'utf8')}catch{return''}}
export const parseResourceValues=(text:string)=>Object.fromEntries(text.trim().split('\n').flatMap(line=>{const [key,value]=line.trim().replace(':',' ').split(/\s+/);return key&&value&&/^[0-9]+$/.test(value)?[[key,Number(value)]]:[]}))
const values=parseResourceValues
function snapshot(){
 const cgroup=read('/proc/self/cgroup').split('\n').find(line=>line.startsWith('0::'))?.slice(3)??''
 const root=join('/sys/fs/cgroup',cgroup)
 return {at:new Date().toISOString(),uptime:read('/proc/uptime').trim(),memory:values(read('/proc/meminfo')),vmstat:values(read('/proc/vmstat')),cgroup,events:values(read(join(root,'memory.events'))),memoryMax:read(join(root,'memory.max')).trim(),memoryCurrent:read(join(root,'memory.current')).trim()}
}
function descendants(pid:number):number[]{
 const out=[pid]
 for(let i=0;i<out.length&&out.length<128;i++)for(const word of read(`/proc/${out[i]}/task/${out[i]}/children`).trim().split(/\s+/)){const child=Number(word);if(child>0&&!out.includes(child))out.push(child)}
 return out
}
export function resourceLimits(seconds=60){
 if(!Number.isSafeInteger(seconds)||seconds<1||seconds>3600)throw Error('invalid resource observation deadline')
 return{seconds:String(seconds),watchdogMs:(seconds+30)*1000}
}
export async function runResourceMeasured(bun:string,args:string[],cwd:string,label:string,seconds=60){
 const limits=resourceLimits(seconds)
 const outPath=join(cwd,`.resource-${label}.out`),errPath=join(cwd,`.resource-${label}.err`),outFd=openSync(outPath,'w'),errFd=openSync(errPath,'w'),before=snapshot(),start=performance.now()
 const child=spawn('timeout',['-k','5',limits.seconds,bun,...args],{cwd,stdio:['ignore',outFd,errFd],env:{...process.env,CI:'1',GIT_TERMINAL_PROMPT:'0'}})
 const seen=new Set<number>(),starts=new Map<number,string>(),peaks:Record<string,number>={},samples:{elapsedMs:number,rssKiB:number,pids:number[],availableKiB:number}[]=[]
 let peakRssKiB=0,minAvailableKiB=Infinity,watchdog=false,error:Error|undefined
 const sample=()=>{
  const pids=child.pid?descendants(child.pid):[],mem=values(read('/proc/meminfo'));let rss=0
  for(const pid of pids){seen.add(pid);const stat=read(`/proc/${pid}/stat`);if(stat)starts.set(pid,stat.slice(stat.lastIndexOf(')')+2).split(' ')[19]??'');const k=values(read(`/proc/${pid}/status`)).VmRSS??0;rss+=k;peaks[pid]=Math.max(peaks[pid]??0,k)}
  peakRssKiB=Math.max(peakRssKiB,rss);minAvailableKiB=Math.min(minAvailableKiB,mem.MemAvailable??Infinity)
  if(samples.length<400)samples.push({elapsedMs:Math.round(performance.now()-start),rssKiB:rss,pids,availableKiB:mem.MemAvailable??-1})
 }
 sample();console.log('BAR_RESOURCE_BEGIN '+JSON.stringify({label,pid:child.pid,at:before.at,cgroup:before.cgroup,memoryMax:before.memoryMax}))
 const interval=setInterval(sample,250),timer=setTimeout(()=>{
  watchdog=true
  for(const pid of child.pid?descendants(child.pid).reverse():[]){const stat=read(`/proc/${pid}/stat`),born=stat.slice(stat.lastIndexOf(')')+2).split(' ')[19]??'';if(starts.get(pid)===born)try{process.kill(pid,'SIGKILL')}catch{/* exited */}}
 },limits.watchdogMs)
 const exit=await new Promise<{code:number|null,signal:NodeJS.Signals|null}>(resolve=>{child.once('error',e=>{error=e;resolve({code:null,signal:null})});child.once('close',(code,signal)=>resolve({code,signal}))})
 clearInterval(interval);clearTimeout(timer);closeSync(outFd);closeSync(errFd)
 const wallMs=performance.now()-start,after=snapshot(),stdout=read(outPath),stderr=read(errPath)
 const journal=spawnSync('sudo',['-n','journalctl','-k','--no-pager','-o','short-iso','--since',before.at,'--until',after.at],{encoding:'utf8',timeout:5000,maxBuffer:4*1024*1024})
 const lines=(journal.stdout??'').split('\n'),matches:number[]=[]
 lines.forEach((line,i)=>{if([...seen].some(pid=>line.includes('Killed process '+pid+' ')||line.includes('pid='+pid+',')))matches.push(i)})
 const indexes=new Set(matches.flatMap(i=>Array.from({length:7},(_,n)=>i-3+n).filter(j=>j>=0&&j<lines.length))),kernel=[...indexes].sort((a,b)=>a-b).map(i=>lines[i]).join('\n').slice(-16000)
 const oomDelta=(after.vmstat.oom_kill??0)-(before.vmstat.oom_kill??0),kernelPidOom=matches.length>0&&/oom|Out of memory|Killed process/.test(kernel)
 const classification=exit.code===0?'completed':exit.code===124?'strict-timeout':watchdog?'outer-watchdog':kernelPidOom?'confirmed-kernel-oom':(exit.signal==='SIGKILL'||exit.code===137)&&oomDelta>0?'oom-correlated-pid-unconfirmed':exit.signal==='SIGKILL'||exit.code===137?'unattributed-sigkill':error?'launcher-error':'nonzero'
 const resources={telemetryVersion:2,label,strictSeconds:seconds,before,after,pid:child.pid,seenPids:[...seen],peakRssKiB,minAvailableKiB,pidPeaksKiB:peaks,samples,oomDelta,kernelPidOom,kernel,journalExit:journal.status,journalError:journal.stderr?.slice(-1000),watchdog,classification,capture:'files, not bounded spawn buffers'}
 console.log('BAR_RESOURCE_END '+JSON.stringify({label,status:exit.code,signal:exit.signal,classification,wallMs,oomDelta,peakRssKiB,minAvailableKiB,pids:[...seen]}))
 unlinkSync(outPath);unlinkSync(errPath)
 return {status:exit.code,signal:exit.signal,error,wallMs,stdout,stderr,resources}
}
