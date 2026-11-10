// One sequential VM: exact A/B controls, reverse-order repeat, then crossovers.
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
const [work,input,out,planFile]=process.argv.slice(2);if(!work||!input||!out)throw new Error('WORK INPUT OUTPUT [PLAN] required')
const read=(p:string)=>{try{return readFileSync(p,'utf8').trim()}catch{return null}}
const health=()=>{
 const status=read('/proc/self/status')??'',cpu=read('/proc/cpuinfo')??''
 const mhz=[...cpu.matchAll(/^cpu MHz\s*:\s*([\d.]+)/gm)].map(m=>Number(m[1]))
 return {at:new Date().toISOString(),load:read('/proc/loadavg'),cpuPressure:read('/proc/pressure/cpu'),memoryPressure:read('/proc/pressure/memory'),cpuMax:read('/sys/fs/cgroup/cpu.max'),cpuStat:read('/sys/fs/cgroup/cpu.stat'),cpuset:read('/sys/fs/cgroup/cpuset.cpus.effective'),allowed:status.match(/^Cpus_allowed_list:\s*(.+)$/m)?.[1],mhz:mhz.length?{min:Math.min(...mhz),max:Math.max(...mhz),mean:mhz.reduce((a,b)=>a+b,0)/mhz.length}:null}
}
const buffer=Buffer.alloc(1024*1024,0xa5)
const calibrate=()=>{const before=process.cpuUsage(),start=performance.now();let sum='';for(let i=0;i<64;i++)sum=createHash('sha256').update(buffer).digest('hex');const used=process.cpuUsage(before);return {wallMs:performance.now()-start,cpuMs:(used.user+used.system)/1000,sha256:sum,bytes:64*buffer.length}}
type Step={id:string,variant:string,env?:Record<string,string>,bunArgs?:string[]}
const defaultPlan=[['a1','census-profile'],['b1','tf1-profile'],['b2','tf1-profile'],['a2','census-profile'],['n1','tf1-minimal'],['x1','census-extras'],['u1','census-plain'],['u2','tf1-plain']].map(([id,variant])=>({id:id!,variant:variant!}))
const plan:Step[]=planFile?JSON.parse(readFileSync(planFile,'utf8')):defaultPlan
const report:any[]=[],started=performance.now()
calibrate()
for(const step of plan){
 const {id,variant}=step
 if(!/^[-\w]+$/.test(id)||!/^[-\w]+$/.test(variant))throw new Error('invalid case path')
 if(performance.now()-started>600000&&report.length>=4){report.push({id,variant,skipped:'outer measurement deadline; not a proof result'});continue}
 const cwd=join(work,variant),stdout=join(out,id+'.log'),stderr=join(out,id+'.stderr.log'),resource=join(out,id+'.time.txt')
 const before={health:health(),calibration:calibrate()},samples:ReturnType<typeof health>[]=[]
 console.log(JSON.stringify({event:'start',id,variant,before}))
 const start=performance.now()
 const child=Bun.spawn(['/usr/bin/timeout','-s','KILL','180','/usr/bin/time','-v','-o',resource,process.execPath,...(step.bunArgs??[]).map(s=>s.replaceAll('{out}',out)),'research/track-m/run-phase-census.ts','focused',input,id],{cwd,env:{...process.env,...step.env,TRACK_M_PHASE_CENSUS:variant.endsWith('-plain')?'0':'1',LAB_SECTION7_T1:'0',LAB_SECTION7_FOLLOWUP:'0',LAB_PROFILE_LIMIT_PROVED:'1'},stdout:Bun.file(stdout),stderr:Bun.file(stderr)})
 const timer=setInterval(()=>samples.push(health()),1000)
 let code:number
 try{code=await child.exited}finally{clearInterval(timer)}
 const after={health:health(),calibration:calibrate()},records=readFileSync(stdout,'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l)).filter(r=>r.mode==='phase-census')
 const summary={id,variant,runtimeControls:step.env??{},bunArgs:step.bunArgs??[],exitCode:code,wallMs:performance.now()-start,before,after,samples,resource:read(resource),laws:records.map(r=>({law:r.law,proven:r.proven,checked:r.checked,wallMs:r.wallMs,countedUnits:r.countedUnits,kernelMs:r.phases.kernel,sites:r.sites,checkCalls:r.checkCalls}))}
 report.push(summary);writeFileSync(join(out,'measurements.json'),JSON.stringify(report,null,2)+'\n')
 console.log(JSON.stringify({event:'end',id,variant,exitCode:code,laws:summary.laws.map(r=>({law:r.law,checked:r.checked,units:r.countedUnits,wallMs:r.wallMs,kernelMs:r.kernelMs})),resource:summary.resource}))
 if(code!==0||records.length!==3)throw new Error('incomplete control '+id)
}
const metadata={bun:Bun.version,bunRevision:Bun.revision,execPath:process.execPath,architecture:process.arch,inputSha256:createHash('sha256').update(readFileSync(input)).digest('hex'),environment:Object.fromEntries(['NODE_OPTIONS','BUN_OPTIONS','JSC_useJIT','JSC_useDFGJIT','JSC_useFTLJIT','JSC_useConcurrentJIT','GDP_ROWS_SHARED','GDP_ROWS_UNWEIGHTED','GDP_COUNTS_FOCUS'].map(k=>[k,process.env[k]??null])),runs:report.length}
writeFileSync(join(out,'runtime.json'),JSON.stringify(metadata,null,2)+'\n')
