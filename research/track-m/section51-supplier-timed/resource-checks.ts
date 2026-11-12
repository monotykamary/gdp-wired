// Observation validation, not a memory setter or enforcement certificate.
const stable=(x:any):string=>JSON.stringify(x,(_k,v)=>v&&typeof v==='object'&&!Array.isArray(v)?Object.fromEntries(Object.keys(v).sort().map(k=>[k,v[k]])):v)
function need(ok:unknown,s:string):asserts ok{if(!ok)throw Error(s)}
export function validateResourcePair(before:any,after:any,mode:string,workerPid:number){
 for(const [phase,r] of [['before',before],['after',after]] as const){
  need(r.format==='mldr-3g-resource-observation/v1'&&r.phase===phase&&r.mode===mode&&r.workerPid===workerPid&&Number.isSafeInteger(workerPid)&&workerPid>0&&r.valid===true&&r.observationOnly===true&&r.collectorInvokedCandidateCode===false&&r.platform==='linux','invalid resource identity: '+phase)
  need(r.affinity?.status==='OBSERVED'&&r.affinity.value?.count===16&&r.memory?.requestedMiB===28672&&r.memory.perJobEnforcement===false&&r.memory.requestedMeaning==='scheduler placement request, not an observed hard cap','invalid observed placement: '+phase)
  const cpus=r.affinity.value.cpuIds
  need(Array.isArray(cpus)&&cpus.length===16&&new Set(cpus).size===16&&cpus.every((n:any)=>Number.isSafeInteger(n)&&n>=0&&n<=65535),'invalid observed affinity')
  need(r.memory.rlimits?.status==='OBSERVED'&&r.memory.cgroup?.status==='OBSERVED'&&r.pidNamespace?.status==='OBSERVED','missing actual-limit observation')
  for(const k of ['addressSpace','dataSize','residentSet']){
   const limit=r.memory.rlimits.value?.[k]
   need(limit?.units==='bytes'&&typeof limit.raw==='string'&&[limit.soft,limit.hard].every((v:any)=>typeof v==='string'&&(/^(0|[1-9]\d*)$/.test(v)||v==='unlimited')),'invalid memory rlimit')
  }
  const cg=r.memory.cgroup.value
  need([1,2].includes(cg?.version)&&cg.outsideVisibleMount==='UNKNOWN'&&Array.isArray(cg.limits)&&cg.limits.length>0&&cg.limits.length<=64,'invalid visible cgroup observation')
  for(const l of cg.limits)need(typeof l.path==='string'&&(l.raw===null||l.raw==='max'||typeof l.raw==='string'&&/^(0|[1-9]\d*)$/.test(l.raw)),'invalid raw cgroup limit')
 }
 for(const get of [(r:any)=>r.pidNamespace.value,(r:any)=>r.affinity.value,(r:any)=>r.memory.rlimits.value,(r:any)=>r.memory.cgroup.value])need(stable(get(before))===stable(get(after)),'observed resource identity changed')
 return {before,after,perJobMemoryEnforcement:false,memoryRequestMeaning:'placement-only',outsideVisibleMount:'UNKNOWN'}
}
