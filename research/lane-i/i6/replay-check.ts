// A completed-check measurement, not an admission policy or strategy run.
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {cpus} from 'node:os'
const [root,tag,...files]=process.argv.slice(2)
const {checkMC}=await import(join(root!,'kernel/kernel.ts'))
const {rawWork,fullWork}=await import(join(root!,'core/work-meter.ts'))
const sha=(bytes:string|Buffer)=>createHash('sha256').update(bytes).digest('hex')
const checker={kernel:sha(readFileSync(join(root!,'kernel/kernel.ts'))),arithmetic:sha(readFileSync(join(root!,'core/check.ts')))}
console.log('I6_REPLAY_HOST '+JSON.stringify({tag,checker,models:[...new Set(cpus().map(c=>c.model))],bootId:readFileSync('/proc/sys/kernel/random/boot_id','utf8').trim()}))
for(const file of files){
 const bytes=readFileSync(file),value=JSON.parse(bytes.toString())
 if(value.format!=='raw-final-count-check-v1'||!['step','init'].includes(value.phase)||!Array.isArray(value.hyps)||!Array.isArray(value.decls)||!value.cert)throw Error('invalid raw checker payload')
 const before=rawWork(),u0=fullWork(),start=performance.now()
 const checked=checkMC(value.hyps,value.decls,value.cert),wallMs=performance.now()-start,after=rawWork(),units=fullWork()-u0
 const raw=Object.fromEntries(Object.keys(after).map(k=>[k,after[k]-before[k]]))
 console.log('I6_CHECK '+JSON.stringify({tag,target:value.target,phase:value.phase,inputSha:sha(bytes),checked,wallMs,units,raw}))
 if(!checked)throw Error('captured original certificate failed to replay')
 const bad=structuredClone(value.cert),breakLeaves=(t:any)=>{if('leaf'in t)t.leaf=[];else {breakLeaves(t.yes);breakLeaves(t.no)}};breakLeaves(bad.tree)
 if(checkMC(value.hyps,value.decls,bad))throw Error('empty-derivation mutant accepted')
 console.log('I6_EMPTY_DERIVATION_REJECTED '+value.phase)
}
