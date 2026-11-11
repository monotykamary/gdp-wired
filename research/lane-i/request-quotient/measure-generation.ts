import {createHash} from 'node:crypto'
import {join} from 'node:path'
const [root,id,kind]=process.argv.slice(2)
const {protocols}=await import(join(root!,'research/protocols/ic3syn/models.ts'))
const {rawWork,fullWork,workKeys}=await import(join(root!,'core/work-meter.ts'))
const {withBudget,counted,fullRate}=await import(join(root!,'kernel/prove.ts'))
const {smallOf}=await import(join(root!,'core/exists.ts'))
const {countsDump,searchCounted}=await import(join(root!,'core/counts.ts'))
const {requestQuotient}=await import(join(root!,'core/request-quotient.ts'))
const protocol=protocols.find((p:any)=>p.id===id)
if(!protocol)throw Error('unknown original '+id)
const rule=protocol.make(),laws=protocol.laws(rule),machine=rule.machine
const hash=(value:unknown)=>createHash('sha256').update(JSON.stringify(value)).digest('hex')
const raw0=rawWork(),units0=fullWork(),t0=performance.now()
let detail:any
if(kind==='classes'){
 const atoms=(c:any):any[]=>(c.op==='and'||c.op==='or')?c.xs.flatMap(atoms):c.op==='not'?atoms(c.x):[c]
 let requests:any[]=[{}]
 for(const name of machine.inputs){const below=Math.max(3,...(machine.assume?atoms(machine.assume):[]).flatMap((c:any)=>c.op==='<'&&c.a.op==='var'&&c.a.name===name&&c.b.op==='const'&&c.b.value<=8?[c.b.value]:[]));requests=requests.flatMap(r=>Array.from({length:below},(_,v)=>({...r,[name]:v})))}
 const subsets=Array.from({length:8},(_,s)=>new Map(Array.from({length:3},(_,i)=>i).filter(i=>(s>>i)&1).map(i=>[i,1])))
 for(const name of machine.inputMaps??[])requests=requests.flatMap(r=>subsets.map(s=>({...r,[name]:s})))
 const quotientStart=performance.now(),quotientUnits=fullWork()
 const quotient=withBudget(1e12,()=>requestQuotient(machine,requests))
 const quotientWallMs=performance.now()-quotientStart,quotientWorkUnits=fullWork()-quotientUnits
 detail={quotientWallMs,quotientWorkUnits,requests:requests.length,classes:quotient?.count,selector:quotient?.selector,reads:quotient?[...quotient.reads]:undefined,classHash:quotient?hash([...quotient.classes]):undefined}
}else if(kind==='samples'){
 const rows=withBudget(1e12,()=>smallOf(machine))
 detail={samples:rows.map(({p,sts}:any)=>({params:p,count:sts.length,hash:hash(sts.map((s:any)=>({scalars:s.scalars,maps:Object.fromEntries(Object.entries(s.maps).map(([n,c]:any)=>[n,[...c].filter(([,v]:any)=>v!==0).sort((a:any,b:any)=>a[0]-b[0])])),defaults:s.defaults})))}))}
}else if(kind==='generation'){
 const done=new Error('captured completed candidate generation')
 countsDump.on=(event:any)=>{if(event.phase==='candidates'){detail={candidateCount:event.laws.length,candidateHash:hash(event.laws),candidateNames:event.laws.map((l:any)=>l.name)};throw done}}
 try{const result=counted(fullRate,()=>searchCounted(machine,laws,1e12),true);throw Error('generation did not reach candidate boundary: '+JSON.stringify(result))}catch(e){if(e!==done)throw e}finally{countsDump.on=undefined}
}else throw Error('invalid measurement kind '+kind)
const wallMs=performance.now()-t0,raw1=rawWork()
console.log('QUOTIENT_MEASUREMENT '+JSON.stringify({id,kind,quotient:process.env.GDP_REQUEST_QUOTIENT,wallMs,units:fullWork()-units0,raw:Object.fromEntries(workKeys.map((k:string)=>[k,raw1[k]-raw0[k]])),...detail}))
