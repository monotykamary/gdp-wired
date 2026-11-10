// No search: replay a retained branch certificate and reconcile demand ledgers.
import {readFileSync} from 'node:fs'
import {strict as assert} from 'node:assert'
import {termColumn} from '../../kernel/kernel.ts'
import {checkConditionalProof,markConditionalProof} from '../../core/count-recovery/conditional-proof.ts'
import {unpack} from './section18-codec.ts'
const x=unpack(readFileSync(process.argv[2]!,'utf8')),near=(a:number,b:number)=>Math.abs(a-b)<1e-6*Math.max(1,Math.abs(a),Math.abs(b))
assert.equal(x.allowance,5000);assert.equal(x.wallAllowance,4800)
const attempts=x.attempts as any[],byId=new Map(attempts.map(a=>[a.id,a])),sum=(xs:any[],f:(a:any)=>number)=>xs.reduce((n,a)=>n+f(a),0)
for(const a of attempts){
 assert(near(a.inclusiveUnits,a.end-a.start));const children=attempts.filter(c=>c.parent===a.id)
 assert(near(a.units,Math.max(0,a.inclusiveUnits-sum(children,c=>c.inclusiveUnits))))
 if(a.parent!==undefined)assert(byId.has(a.parent))
 const demand=a.demand,known=!!demand&&(demand.modelKnown||demand.coreKnown)&&(demand.scope===undefined||demand.scope===a.scope),cols=new Set([...(demand?.coreColumns??[]),...(demand?.modelColumns??[])])
 assert.equal(a.requested,known?a.cellColumns.some((c:string)=>cols.has(c)):undefined)
}
let proofChecked=false
if(x.checked){
 assert(x.proof&&x.columns,'checked result missing portable proof')
 for(const [i,t]of x.columns.entries())assert.equal(termColumn(t),`⟦${i}⟧`)
 for(const mark of x.proof.marks){let tree=x.proof.tree;for(const part of mark.path)tree=tree[part];markConditionalProof(mark.goal,tree,mark.lemmas)}
 proofChecked=checkConditionalProof(x.proof.goal,x.proof.tree,new Map(x.proof.path));assert(proofChecked)
}
const measured=sum(attempts,a=>a.units),unknown=attempts.filter(a=>a.requested===undefined),unrequested=attempts.filter(a=>a.requested===false)
assert(measured<=x.searchUnits+1e-5)
console.log(JSON.stringify({law:x.law,op:x.op,proofChecked,recordedChecked:x.checked,searchUnits:x.searchUnits,attempts:attempts.length,attemptUnits:measured,unknownDemand:unknown.length,unknownDemandUnits:sum(unknown,a=>a.units),unrequested:unrequested.length,potentialFixedPrefixSaving:sum(unrequested,a=>a.units),potentialFailedOnlySaving:sum(unrequested.filter(a=>!a.emitted),a=>a.units),notAPolicyReplay:true}))
