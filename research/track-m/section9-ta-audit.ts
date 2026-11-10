// Audit recorded outcomes only; never turn an unresolved query into a gap/proof.
import {createHash} from 'node:crypto'
export const packetHash=(g:unknown,cert:unknown,path:unknown)=>createHash('sha256').update(JSON.stringify({g,cert,path})).digest('hex')
export function supportsNamedGap(branch:any):boolean{
 const q=branch.queries?.at(-1)
 if(branch.name!=='complement'||!q?.validModel||q.outcome!=='sat'||!Array.isArray(q.violated))return false
 const sat=new Set<number>((branch.attempts??[]).filter((a:any)=>a.outcome==='sat'&&a.sourceAndScopeValid===true).map((a:any)=>a.originalIndex))
 return [27,32,...q.violated].every(i=>sat.has(i))
}
export function auditT9A(records:any[],referenceHash?:string){
 if(records.length!==6)throw new Error('six A/B results required')
 const ids=records.map(r=>r.side+r.repeat)
 if(JSON.stringify(ids)!==JSON.stringify(['A1','B1','A2','B2','A3','B3']))throw new Error('wrong interleaving')
 const expected=referenceHash??records[0].packetHash
 for(const r of records){
  if(r.packetHash!==expected||r.packetHash!==packetHash(r.packet.g,r.packet.cert,r.packet.scope))throw new Error('packet mismatch')
  if(r.unitLimit!==400)throw new Error('allowance changed')
  for(const b of r.branches){
   if(b.outcome==='generator-gap'&&!supportsNamedGap(b))throw new Error('unsupported generator gap')
   if(b.outcome==='checked'&&!b.queries.some((q:any)=>q.numericChecked&&q.conditionalChecked))throw new Error('unchecked branch')
   for(const a of b.attempts){
    if(a.coreLimit!==8)throw new Error('source core cap changed')
    if(a.outcome==='sat'&&(!a.sourceAndScopeValid||!a.model))throw new Error('unvalidated SAT source')
    if(a.outcome==='checked'&&(!a.saved?.lemma||!a.tree))throw new Error('unadmitted proof')
   }
  }
  const pass=r.side==='B'&&r.generated&&r.branches.length===2&&r.branches.every((b:any)=>b.outcome==='checked')&&r.countedUnits<=400
  if(r.pass!==pass)throw new Error('pass classification mismatch')
 }
 const summary=Object.fromEntries(['A','B'].map(side=>{const rows=records.filter(r=>r.side===side),walls=rows.map(r=>r.wallMs).sort((a,b)=>a-b);return [side,{countedUnits:rows.map(r=>r.countedUnits),wallMedianMs:walls[1],wallMaxMs:walls[2],pass:rows.every(r=>r.pass),generatorGap:rows.every(r=>r.generatorGap)}]}))
 return {packetHash:expected,summary,decision:summary.B!.pass?'pass':summary.B!.generatorGap?'generator-gap':'failed-or-inconsistent'}
}
