// A completed-check measurement, not an admission policy or strategy run.
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {cpus} from 'node:os'
const [root,tag,...files]=process.argv.slice(2)
const {checkMC,termColumn}=await import(join(root!,'kernel/kernel.ts'))
const {rawWork,fullWork}=await import(join(root!,'core/work-meter.ts'))
const sha=(bytes:string|Buffer)=>createHash('sha256').update(bytes).digest('hex')
const checker={kernel:sha(readFileSync(join(root!,'kernel/kernel.ts'))),arithmetic:sha(readFileSync(join(root!,'core/check.ts')))}
console.log('I6_REPLAY_HOST '+JSON.stringify({tag,checker,models:[...new Set(cpus().map(c=>c.model))],bootId:readFileSync('/proc/sys/kernel/random/boot_id','utf8').trim()}))
// B capture cace38bc: serialized term-column IDs are process-local. Rebind saved
// expressions before either native checker call; never treat captured IDs as authority.
function rebind(cert:any,terms:Record<string,any>={}){
 const names=new Map<string,string>(),pattern=/⟦[0-9]+⟧/g
 const text=(value:string)=>value.replace(pattern,name=>{if(!names.has(name)){if(!Object.hasOwn(terms,name))throw Error('missing term column '+name);names.set(name,termColumn(terms[name]))}return names.get(name)!})
 const visit=(value:any):any=>{if(typeof value==='string')return text(value);if(Array.isArray(value))return value.map(visit);if(!value||typeof value!=='object')return value;const out:Record<string,any>=Object.create(null);for(const [key,child]of Object.entries(value)){const name=text(key),next=visit(child);if(Object.hasOwn(out,name)){if(typeof out[name]!=='number'||typeof next!=='number')throw Error('term-column collision');out[name]+=next}else out[name]=next}return out}
 return visit(cert)
}
for(const file of files){
 const bytes=readFileSync(file),value=JSON.parse(bytes.toString())
 if(value.format!=='raw-final-count-check-v1'||!['step','init'].includes(value.phase)||!Array.isArray(value.hyps)||!Array.isArray(value.decls)||!value.cert)throw Error('invalid raw checker payload')
 const cert=rebind(value.cert,value.termColumns)
 const before=rawWork(),u0=fullWork(),start=performance.now()
 const checked=checkMC(value.hyps,value.decls,cert),wallMs=performance.now()-start,after=rawWork(),units=fullWork()-u0
 const raw=Object.fromEntries(Object.keys(after).map(k=>[k,after[k]-before[k]]))
 console.log('I6_CHECK '+JSON.stringify({tag,target:value.target,phase:value.phase,inputSha:sha(bytes),checked,wallMs,units,raw}))
 if(!checked)throw Error('captured original certificate failed to replay')
 const bad=structuredClone(cert),breakLeaves=(t:any)=>{if('leaf'in t)t.leaf=[];else {breakLeaves(t.yes);breakLeaves(t.no)}};breakLeaves(bad.tree)
 if(checkMC(value.hyps,value.decls,bad))throw Error('empty-derivation mutant accepted')
 console.log('I6_EMPTY_DERIVATION_REJECTED '+value.phase)
}
