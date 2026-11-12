// Read-only native resource observations; no candidate imports or resource setters.
import {closeSync,openSync,readSync,readlinkSync,writeFileSync} from 'node:fs'
import {posix,resolve} from 'node:path'

type Observation<T>={status:'OBSERVED';value:T}|{status:'UNKNOWN';reason:string}
const observe=<T>(f:()=>T):Observation<T>=>{try{return {status:'OBSERVED',value:f()}}catch(e){return {status:'UNKNOWN',reason:e instanceof Error?e.message:String(e)}}}
const read=(path:string,max=65536):string=>{
 const fd=openSync(path,'r'),buffer=Buffer.alloc(max+1);let size=0
 try{while(size<buffer.length){const n=readSync(fd,buffer,size,buffer.length-size,null);if(n===0)break;size+=n}}finally{closeSync(fd)}
 if(size>max)throw Error('resource file exceeds bound: '+path)
 return buffer.subarray(0,size).toString('utf8')
}
const cpuList=(text:string):number[]=>{
 const values:number[]=[]
 for(const part of text.split(',')){
  const m=/^(\d+)(?:-(\d+))?$/.exec(part);if(!m)throw Error('invalid kernel CPU list')
  const first=Number(m[1]),last=Number(m[2]??m[1]);if(last<first||last>65535||values.length+last-first+1>4096)throw Error('CPU list exceeds bound')
  for(let n=first;n<=last;n++)values.push(n)
 }
 if(new Set(values).size!==values.length||values.length===0)throw Error('duplicate/empty CPU list')
 return values
}
const decode=(s:string)=>s.replace(/\\([0-7]{3})/g,(_,octal:string)=>String.fromCharCode(parseInt(octal,8)))
const beneath=(path:string,root:string)=>root==='/'?path.startsWith('/'):path===root||path.startsWith(root+'/')
const cgroup=()=>{
 const membershipText=read('/proc/self/cgroup'),mountText=read('/proc/self/mountinfo',1048576)
 const members=membershipText.trim().split('\n').map(line=>{const m=/^(\d+):([^:]*):(.*)$/.exec(line);if(!m)throw Error('invalid cgroup membership');return {line,controllers:m[2]!.split(','),path:m[3]!}})
 const v1=members.find(m=>m.controllers.includes('memory')),member=v1??members.find(m=>m.controllers.length===1&&m.controllers[0]==='')
 if(!member)throw Error('no visible memory cgroup membership')
 const version=v1?1:2
 const mounts=mountText.trim().split('\n').flatMap(line=>{
  const [left,right]=line.split(' - ');if(!left||!right)return []
  const a=left.split(' '),b=right.split(' '),root=decode(a[3]??''),point=decode(a[4]??'')
  if((version===2?b[0]==='cgroup2':b[0]==='cgroup'&&(b[2]??'').split(',').includes('memory'))&&beneath(member.path,root))return [{root,point,line}]
  return []
 }).sort((a,b)=>b.root.length-a.root.length)
 const mount=mounts[0];if(!mount||!posix.isAbsolute(mount.point)||!posix.isAbsolute(member.path)||posix.normalize(member.path)!==member.path)throw Error('cgroup mount/membership cannot be resolved')
 const suffix=mount.root==='/'?member.path.slice(1):member.path.slice(mount.root.length).replace(/^\//,'')
 let current=posix.join(mount.point,suffix),done=false
 const limits:{directory:string;path:string;raw:string|null;kind:'NUMERIC'|'UNLIMITED'|'ROOT_NO_LIMIT_INTERFACE';bytes:string|null}[]=[]
 for(let depth=0;depth<64;depth++){
  if(!beneath(current,mount.point))throw Error('cgroup path escaped mount')
  const path=posix.join(current,version===2?'memory.max':'memory.limit_in_bytes')
  let raw:string|null
  try{raw=read(path).trim()}catch(e){
   if(version===2&&current===mount.point&&mount.root==='/'&&(e as NodeJS.ErrnoException).code==='ENOENT')raw=null
   else throw e
  }
  if(raw!==null&&raw!=='max'&&!/^(0|[1-9]\d*)$/.test(raw))throw Error('invalid cgroup memory limit')
  if(version===1&&raw==='max')throw Error('invalid v1 limit')
  limits.push({directory:current,path,raw,kind:raw===null?'ROOT_NO_LIMIT_INTERFACE':raw==='max'?'UNLIMITED':'NUMERIC',bytes:raw!==null&&raw!=='max'?raw:null})
  if(current===mount.point){done=true;break}current=posix.dirname(current)
 }
 if(!done)throw Error('cgroup ancestor depth exceeds bound')
 const finite=limits.flatMap(l=>l.bytes===null?[]:[BigInt(l.bytes)])
 return {version,membershipSource:'/proc/self/cgroup',membership:member.line,membershipPath:member.path,mountSource:'/proc/self/mountinfo',mount,limits,
  minimumVisibleNumericBytes:finite.length?finite.reduce((a,b)=>a<b?a:b).toString():null,
  numericMeaning:version===1?'raw v1 values; unlimited sentinels not decoded':'numeric memory.max ceiling',outsideVisibleMount:'UNKNOWN' as const}
}
const phase=process.argv[2],out=process.env.SUPERCOMPUTER_OUTPUT_DIR
if((phase!=='before'&&phase!=='after')||!out||!posix.isAbsolute(out))throw Error('native output directory and before/after phase required')
const affinity=observe(()=>{
 const raw=read('/proc/self/status').match(/^Cpus_allowed_list:\s*(.+)$/m)?.[1]?.trim();if(!raw)throw Error('kernel affinity list absent')
 const cpuIds=cpuList(raw);return {source:'/proc/self/status',field:'Cpus_allowed_list',raw,cpuIds,count:cpuIds.length}
})
const rlimits=observe(()=>{
 const raw=read('/proc/self/limits')
 const one=(name:string)=>{const line=raw.split('\n').find(l=>l.startsWith(name+' '));if(!line)throw Error('rlimit absent: '+name)
  const values=line.slice(name.length).trim().split(/\s+/),[soft,hard,units]=values
  if(values.length!==3||units!=='bytes'||![soft,hard].every(v=>v!==undefined&&(/^(0|[1-9]\d*)$/.test(v)||v==='unlimited')))throw Error('invalid rlimit: '+name)
  return {raw:line,soft,hard,units}
 }
 return {source:'/proc/self/limits',addressSpace:one('Max address space'),dataSize:one('Max data size'),residentSet:one('Max resident set')}
})
const memoryCgroup=observe(cgroup),pidNamespace=observe(()=>readlinkSync('/proc/self/ns/pid'))
const hostMemory=observe(()=>{const line=read('/proc/meminfo').match(/^MemTotal:\s+(\d+) kB$/m);if(!line)throw Error('MemTotal absent');return {source:'/proc/meminfo',totalKiB:line[1]!,scope:'host context, not job limit'}})
const valid=process.platform==='linux'&&affinity.status==='OBSERVED'&&affinity.value.count===16&&rlimits.status==='OBSERVED'&&memoryCgroup.status==='OBSERVED'&&pidNamespace.status==='OBSERVED'
const mode=process.env.MLDR_MODE,workerPid=Number(process.env.MLDR_WORKER_PID)
if(!['timed','instrumented'].includes(mode??'')||!Number.isSafeInteger(workerPid)||workerPid<=0)throw Error('missing worker identity')
const receipt={mode,workerPid,format:'mldr-3g-resource-observation/v1',phase,capturedAt:new Date().toISOString(),pid:process.pid,platform:process.platform,pidNamespace,
 affinity,memory:{requestedMiB:28672,requestedMeaning:'scheduler placement request, not an observed hard cap',perJobEnforcement:false,rlimits,cgroup:memoryCgroup,host:hostMemory},
 valid,observationOnly:true,sourceConformance:'UNKNOWN',collectorInvokedCandidateCode:false}
writeFileSync(resolve(out,'resources-'+phase+'.json'),JSON.stringify(receipt,null,2)+'\n')
console.log(JSON.stringify({phase,valid,affinity:affinity.status,memoryCgroup:memoryCgroup.status,rlimits:rlimits.status}))
if(!valid)process.exitCode=68
