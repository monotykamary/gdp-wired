// T-A data-first inventory. Evaluate only the captured scalar count vectors.
import {readFileSync} from 'node:fs'
import type {CountCert} from '../../kernel/kernel.ts'
const [log,prior]=process.argv.slice(2);if(!log||!prior)throw new Error('T2_LOG T0_PACKET required')
const rows=readFileSync(log,'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l))
const star=rows.find(r=>r.law?.startsWith('Inv*')&&!r.targetScope),overlap=rows.find(r=>r.law?.startsWith('Inv2973')&&!r.targetScope)
if(!star?.selection?.witnessCleanup||!overlap?.selection?.witnessCleanup)throw new Error('hygienic active traversals required')
const packet=(JSON.parse(readFileSync(prior,'utf8')) as {packet:Pick<CountCert,'reads'|'insts'>}).packet
const final=star.closureSteps.findLast((e:any)=>e.stage==='closure-final'&&e.outcome==='sat')
if(!final?.model||!final.path)throw new Error('missing Inv* SAT leaf')
const selected=new Set<number>(star.selection.originalIndices),full:number[]=[],unbound:number[]=[]
for(const [index,q]of packet.insts.entries()){
 if(q.terms.length>5)continue
 if(q.below.op!=='var'||q.below.name!=='size')throw new Error('unexpected captured vector bound')
 const names=[...q.terms.map((t:any)=>t[1]),...(q.unit?['size']:[])]
 if(names.some(name=>!Object.hasOwn(final.model,name))){unbound.push(index);continue}
 const value=q.terms.reduce((n:number,[z,id]:[number,string])=>n+z*final.model[id],q.unit*final.model.size)
 if(value>0)full.push(index)
}
console.log(JSON.stringify({test:'T-A-data',law:star.law,origin:'section7-followup-v3 hygienic active traversal',path:final.path,model:final.model,activeCuts:final.cuts,activeOriginalIndices:final.closedIndices.map((i:number)=>star.selection.originalIndices[i]),restrictedPool:star.selection.originalIndices,restrictedViolated:full.filter(i=>selected.has(i)),fullPoolSize:packet.insts.length,fullViolated:full,unbound,empty:full.filter(i=>selected.has(i)).length===0}))
const finals=overlap.closureSteps.filter((e:any)=>e.stage==='closure-final'),last=finals.at(-1)
if(finals.length!==14||last.outcome!=='unknown'||last.reason!=='time')throw new Error('unexpected Inv2973 target')
console.log(JSON.stringify({test:'T-A-data',law:overlap.law,leafOrdinal:14,origin:'section7-followup-v3 hygienic active traversal',last,activeOriginalIndices:last.closedIndices.map((i:number)=>overlap.selection.originalIndices[i]),restrictedPool:overlap.selection.originalIndices,needsQuery:true}))
