// Fresh-process validation of every preserved SAT valuation and stop decision.
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {brokenOf} from '../../kernel/prove.ts'
import {columnTerm} from '../../kernel/kernel.ts'
import {auditT9A,packetHash} from './section9-ta-audit.ts'
const [strict,complement,reference]=process.argv.slice(2);if(!strict||!complement||!reference)throw new Error('STRICT COMPLEMENT REFERENCE required')
const prior=JSON.parse(readFileSync(reference,'utf8')),expected=packetHash(prior.g,prior.cert,prior.path)
let sourceModels=0,numericModels=0,scopeChecks=0,admissions=0
const cuts=(xs:any[])=>xs.map(s=>({good:s.good,lemma:s.lemma,index:s.index}))
const pathValid=(path:any[],model:Record<string,number>)=>path.every(([,a])=>{if(Object.keys(a.lin).some(k=>k!=='1'&&!Object.hasOwn(model,k)))return false;const n=Object.entries(a.lin).reduce((s,[k,v])=>s+Number(v)*(k==='1'?1:model[k]!),0);return Number.isFinite(n)&&(a.holds?n<=0:n>0)})
const checkModel=(goal:any,path:any[],model:Record<string,number>)=>{
 if(Object.keys(model).some(k=>k.startsWith('⟦')&&columnTerm(k)!==undefined))throw new Error('stale opaque registry')
 const broken=brokenOf(goal)(model)
 if(broken.length||!pathValid(path,model))throw new Error('invalid replay: '+goal.name+' broken '+JSON.stringify(broken))
 scopeChecks++
}
const audits=[]
for(const dir of [strict,complement]){
 const records=['A1','B1','A2','B2','A3','B3'].map(id=>JSON.parse(readFileSync(join(dir,id+'.json'),'utf8')))
 audits.push(auditT9A(records,expected))
 for(const r of records){
  for(const key of ['numeric','fullCert','indices'])if(JSON.stringify(r.packet[key])!==JSON.stringify(prior[key]))throw new Error('packet mismatch: '+key)
  if(JSON.stringify(cuts(r.packet.available))!==JSON.stringify(cuts(prior.available)))throw new Error('active cuts changed')
  if(!prior.available.every((s:any)=>r.packet.indices[s.index]===s.originalIndex))throw new Error('active cut original index mismatch')
 }
 for(const r of records)for(const b of r.branches){
  for(const q of b.queries)if(q.validModel){checkModel(q.goal,q.path,q.model);numericModels++}
  for(const a of b.attempts){
   if(a.outcome==='sat'){checkModel(a.source,a.path,a.model);sourceModels++}
   if(a.outcome==='checked')admissions++
  }
 }
}
if(audits[0]!.decision==='pass'||audits[1]!.decision!=='generator-gap')throw new Error('unexpected stop outcome')
console.log(JSON.stringify({test:'T-9A-final-validation',packetHash:expected,records:12,packetComponentsChecked:['goal','certificate','path','numeric','fullCert','indices','24 active cuts and original-index mapping'],sourceModels,numericModels,scopeChecks,recordedAdmissions:admissions,strictDecision:audits[0]!.decision,complementDecision:audits[1]!.decision,sourceReplay:'brokenOf + every original path atom; fresh empty opaque registry',noProtocolCounterexampleClaim:true,laterTestsRun:false},null,2))
