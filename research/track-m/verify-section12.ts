// Independent artifact audit: no deadline override or search instrumentation.
import {readFileSync,existsSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {brokenOf} from '../../kernel/prove.ts'
import {checkMC,countedObligations,linear,termColumn,type Path} from '../../kernel/kernel.ts'
const [folder,input]=process.argv.slice(2);if(!folder||!input)throw new Error('FOLDER INPUT required')
const read=(p:string)=>JSON.parse(readFileSync(p,'utf8')),r=read(join(folder,'result.json')),{m,laws}=read(input),before=read(join(folder,'source-before.json')),close=(a:number,b:number)=>Math.abs(a-b)<1e-5,assert=(ok:unknown,message:string)=>{if(!ok)throw new Error(message)}
for(const [p,h]of Object.entries(before))if(p.startsWith('kernel/'))assert(createHash('sha256').update(readFileSync(p)).digest('hex')===h,`kernel changed: ${p}`)
for(let i=0;i<r.columns.length;i++)assert(termColumn(r.columns[i])===`⟦${i}⟧`,`column order ${i}`)
const fs:any[]=r.trace.frames,es:any[]=r.trace.events,childSums=new Map<number,number>(),rootActions=fs.filter(f=>f.kind==='action'&&f.meta.selector==='op'&&!hasActionParent(f)),groups=new Map<string,number>()
function hasActionParent(f:any):boolean{for(let n=f.parent;n!==undefined;n=fs[n]?.parent)if(fs[n]?.kind==='action'&&fs[n]?.meta.selector==='op')return true;return false}
for(const f of fs)if(f.parent!==undefined)childSums.set(f.parent,(childSums.get(f.parent)??0)+f.units)
for(const f of fs){assert(f.end!==undefined&&close(f.units,f.end-f.start),`frame ${f.id} incomplete`);const children=childSums.get(f.id)??0;assert(close(children,f.children)&&close(f.exclusive,f.units-children),`frame ${f.id} ledger`)}
for(const a of rootActions){const op=a.meta.value===null?'else':String(a.meta.value);groups.set(op,(groups.get(op)??0)+a.units)}
for(const row of r.ledger)assert(close(row.units,groups.get(row.op)??0),`op ${row.op} units`)
assert(close(r.totalUnits,r.outsideActions+r.ledger.reduce((s:number,a:any)=>s+a.units,0)),'total conservation')
let point:any=null
const c=r.firstFailure?.capture
if(c?.model){
 const broken=brokenOf(c.numeric)(c.model);assert(broken.length===0,`numeric model breaks ${broken.join(',')}`)
 const value=(lin:Record<string,number>)=>Object.entries(lin).reduce((s,[k,z])=>s+z*(k==='1'?1:c.model[k]??0),0),path=new Map(c.path) as Path
 for(const [,p]of path)assert(p.holds?value(p.lin)<=0:value(p.lin)>0,'path model mismatch')
 const violated=c.pool.filter((i:number)=>{const inst=c.cert.insts[i],below=linear(inst.below,path);assert(below,`below ${i}`);return inst.terms.reduce((s:number,[z,id]:[number,string])=>s+z*(c.model[id]??0),0)+inst.unit*value(below!)>0})
 assert(JSON.stringify(violated)===JSON.stringify(c.violated),'violated set mismatch')
 point={numericModel:true,path:true,violated:violated.length}
}
let certificate:any=null
if(existsSync(join(folder,'proof.json'))){const p=read(join(folder,'proof.json')),index=laws.findIndex((l:any)=>l.name===p.law),checks=countedObligations(m,laws,{[p.law]:p.proof.instances},index).map(({goal,decls})=>!!p.proof.certs[goal.name]&&checkMC(goal.hyps,decls,p.proof.certs[goal.name]));assert(checks.every(Boolean),'fresh kernel rejected certificate');certificate={goals:checks.length,checked:true}}
assert(r.checked===!!certificate,'certificate/result mismatch')
const actionByFrame=new Map<number,any>();for(const f of fs){const parent=actionByFrame.get(f.parent);actionByFrame.set(f.id,parent??(f.kind==='action'&&f.meta.selector==='op'?f:undefined))}
const ledger=r.ledger.map((row:any)=>({op:row.op,units:row.units,actionAttempts:row.actionAttempts,leafVisits:row.leafVisits,leaves:row.leaves,cuts:0,sat:0,checked:0,unknown:0,reusedModels:0,cachedChecked:0,cachedSat:0,cachedUnknown:0,rawSat:0,rawRefuted:0,rawUnknown:0}))
const byOp=new Map(ledger.map((x:any)=>[x.op,x])) as Map<string,any>
for(const e of es){const a=actionByFrame.get(e.frame);if(!a)continue;const row=byOp.get(a.meta.value===null?'else':String(a.meta.value));if(e.kind==='cut')row.cuts++;if(e.kind==='source-result')row[e.outcome==='reused-model'?'reusedModels':e.outcome==='checked'?'checked':e.outcome==='sat'?'sat':'unknown']++;if(e.kind==='source-cached')row[e.outcome==='checked'?'cachedChecked':e.outcome==='sat'?'cachedSat':'cachedUnknown']++;if(e.kind==='source-query-result')row[e.query?.tree||e.query?.why==='refuted, not unfolded'?'rawRefuted':e.query?.stuck==='sat'?'rawSat':'rawUnknown']++}
const summary={law:r.law,kernelIdentical:true,frames:fs.length,events:es.length,ledgerConserved:true,totalUnits:r.totalUnits,wallMs:r.wallMs,ratioToProductionAllowance:r.totalUnits/5000,outsideActions:r.outsideActions,ledger,point,certificate,finalUnresolved:r.finalUnresolved}
writeFileSync(join(folder,'audited-summary.json'),JSON.stringify(summary,null,2)+'\n')
writeFileSync(join(folder,'first-failure.json'),JSON.stringify({law:r.law,firstFailure:r.firstFailure,columns:r.columns},null,2)+'\n')
console.log(JSON.stringify(summary))
