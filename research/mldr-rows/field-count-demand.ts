// Untrusted scheduling only. A primitive field claim can demand the existing
// pre-counts whose declared bodies read that exact cell, plus their already
// proposed coupled counts. This never adds a hypothesis or a count instance.
import {type C,walkOnce} from '../../core/machine.ts'
import {type CountCert,type CountDecl} from '../../kernel/kernel.ts'
import {countsForReads} from '../../core/count-facts.ts'
import {bounded} from '../../core/count-recovery/scalar-guards.ts'
export function fieldCountDemand(ds:CountDecl[],cert:Pick<CountCert,'reads'|'insts'>,claim:C|undefined,cap=12):Set<string>{
 const out=new Set<string>()
 if(!claim||!Number.isSafeInteger(cap)||cap<=0||!bounded([ds,cert,claim]))return out
 cap=Math.min(cap,32)
 const countMaps=new Set(ds.map(d=>d.map)),cells=new Set<string>(),ids=new Set(cert.reads.map(r=>r[0]))
 walkOnce(claim,(o:any)=>{if(o.op==='get'&&!countMaps.has(o.map))cells.add(JSON.stringify(o))})
 if(!cells.size)return out
 for(const read of cert.reads){
  if(out.size>=cap)break
  if(read[1].endsWith('#'))continue
  const count=countsForReads(ds,[read])?.[0]
  if(!count)continue
  let relevant=false
  walkOnce(count.body,(o:any)=>{if(o.op==='get'&&cells.has(JSON.stringify(o)))relevant=true})
  if(!relevant)continue
  out.add(read[0])
  for(const inst of cert.insts){
   if(!inst.terms.some(([k,id])=>k!==0&&id===read[0]))continue
   for(const [k,id]of inst.terms)if(k!==0&&ids.has(id)&&out.size<cap)out.add(id)
  }
 }
 return out
}
