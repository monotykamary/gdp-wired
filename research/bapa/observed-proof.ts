// Research-only supervisor: durable progress continues while synchronous proof
// work occupies a separate thread. No production search/checker instrumentation.
import {Worker} from 'node:worker_threads'
import {appendFileSync, mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
export type ObservedOptions={out:string,model:'minimal'|'naive',units:number,wallMs:number,progressMs?:number,backupMs?:number}
export async function observeProof(o:ObservedOptions) {
  for(const [name,n] of Object.entries({units:o.units,wallMs:o.wallMs,progressMs:o.progressMs??10_000,backupMs:o.backupMs??o.wallMs+60_000})) if(!Number.isSafeInteger(n)||n<1) throw Error(`invalid ${name}`)
  mkdirSync(o.out,{recursive:true})
  const shared=new SharedArrayBuffer(14*8), counters=new BigInt64Array(shared), sites=new Map<number,string>([[0,'startup']])
  const started=Date.now(), env:NodeJS.ProcessEnv={...process.env,GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0'}
  delete env.GDP_WORK_WEIGHTS
  const worker=new Worker(new URL('./observed-proof-worker.ts',import.meta.url),{workerData:{...o,shared,started},env})
  let terminal:Record<string,unknown>|undefined, goal:{name:string,hyps:number}|undefined
  const snapshot=(event:string)=>({event,elapsedMs:Date.now()-started,phase:sites.get(Number(Atomics.load(counters,0)))??'pending-site-label',goal,
    candidates:String(Atomics.load(counters,1)),instancesGenerated:String(Atomics.load(counters,2)+Atomics.load(counters,3)),instancesCartesian:String(Atomics.load(counters,2)),instancesMatched:String(Atomics.load(counters,3)),functionWork:String(Atomics.load(counters,4)),
    kernelCalls:String(Atomics.load(counters,5)),kernelCallsCoverage:'existing metered kernel choiceFree/linear/termId/truth/facts entry sites only; not all checker calls',
    kernelCheckSteps:String(Atomics.load(counters,6)),rawWorkFloor:String(Atomics.load(counters,7)),meterEvents:String(Atomics.load(counters,8)),solverCalls:String(Atomics.load(counters,9)),searchNodes:String(Atomics.load(counters,10)),
    lastCheckpointAgeMs:Atomics.load(counters,11)===0n?null:Date.now()-Number(Atomics.load(counters,11)),profile:'raw-work-v1 diagnostic fixture; not canonical or calibrated'})
  const flush=(event:string)=>{const line=JSON.stringify(snapshot(event));appendFileSync(join(o.out,'progress.jsonl'),line+'\n');console.log(line)}
  flush('start')
  const timer=setInterval(()=>flush('progress'),o.progressMs??10_000)
  let forced=false
  const backup=setTimeout(()=>{
    forced=true
    writeFileSync(join(o.out,'proof-report.json'),JSON.stringify({terminal:'supervisor-backup-stop',verdictReturned:false,proven:false,checked:false,cleanup:'termination-requested',lastProgress:snapshot('backup'),counted:false,accepted:false},null,2)+'\n')
    void worker.terminate()
  },o.backupMs??o.wallMs+60_000)
  worker.on('message',(m:{event:string,id?:number,site?:string,goal?:{name:string,hyps:number},report?:Record<string,unknown>})=>{
    if(m.event==='site'&&m.id!==undefined&&m.site!==undefined) sites.set(m.id,m.site)
    if(m.event==='goal'&&m.goal){goal=m.goal;appendFileSync(join(o.out,'goals.jsonl'),JSON.stringify(m.goal)+'\n')}
    if(m.event==='terminal'&&m.report) terminal=m.report
  })
  worker.on('error',(e:unknown)=>{terminal={terminal:'worker-error',verdictReturned:false,proven:false,checked:false,error:e instanceof Error?e.message:String(e)}})
  const exit=await new Promise<number>(resolve=>worker.once('exit',resolve))
  clearInterval(timer);clearTimeout(backup)
  const report:Record<string,unknown>={...(terminal??{terminal:forced?'supervisor-backup-stop':'worker-exit-without-report',verdictReturned:false,proven:false,checked:false}),workerExit:exit,supervisorBackupStop:forced,budgets:{units:o.units,wallMs:o.wallMs,backupMs:o.backupMs??o.wallMs+60_000},lastProgress:snapshot('terminal'),counted:false,accepted:false}
  // Parent owns the final fallback too: even a worker startup error or backup
  // stop leaves an explicit non-verdict, not an absent report or fake refutation.
  writeFileSync(join(o.out,'proof-report.json'),JSON.stringify(report,null,2)+'\n')
  flush('terminal')
  return report
}
if(import.meta.main){
  const model=process.env.BAPA_OBSERVED_MODEL??'naive'
  if(model!=='naive'&&model!=='minimal')throw Error('invalid observed model')
  const report=await observeProof({out:process.env.SUPERCOMPUTER_OUTPUT_DIR!,model,units:1_000_000,wallMs:180_000,backupMs:240_000})
  console.log(JSON.stringify({terminal:report.terminal,proven:report.proven,checked:report.checked}))
  if(report.proven!==true||report.checked!==true) process.exitCode=2
}
